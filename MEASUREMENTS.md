# Definitional-equality step counts

Produced by `src/stepcount.rs` (a measurement probe on upstream nanoda; see
`DECISIONS.md`). Reproduce with:

```sh
cargo build --release --features stepcount
./target/release/nanoda_bin <config.json>   # report goes to stderr
```

The question these numbers exist to answer: **is a proof-carrying checker
affordable?** Every reduction step below is a step the eventual
Tarski–Grothendieck backend must discharge as a genuine derivation, so the total
is a lower bound on the kernel's work, and the mix says which rules the kernel
API should be optimised for.

## Results, 2026-07-30

Upstream nanoda at `ddfac2b`, `nat_extension` and `string_extension` on.

| step kind | `init-prelude` (2059 decls) | `grind-ring-5` | `app-lam` | `shift-cascade` |
| --- | ---: | ---: | ---: | ---: |
| `def_eq` calls | 65,347 | 389,543 | 32,403 | 5,085 |
| `def_eq` cache hits | 57,800 | 343,442 | 24,352 | 4,075 |
| beta | 35,140 | 1,511,694 | 51 | 0 |
| zeta (let) | 0 | 853 | 0 | 0 |
| delta | 5,402 | 161,046 | 12 | 0 |
| iota (rec) | 1,757 | 169,511 | 3 | 0 |
| quot | 0 | 2 | 0 | 0 |
| proj | 814 | 24,275 | 0 | 0 |
| nat literal arith | 340 | 19,692 | 0 | 0 |
| string literal | 0 | 0 | 0 | 0 |
| proof irrelevance | 7 | 55 | 0 | 0 |
| eta | 0 | 23 | 0 | 0 |
| eta struct | 3 | 18 | 0 | 0 |
| **total reduction steps** | **43,463** | **1,887,169** | **66** | **0** |

## What this says

**The cache is doing most of the work — 88% of `def_eq` calls are answered from
it**, and strikingly consistently: 88.5% on `init-prelude`, 88.2% on
`grind-ring-5`, 75% on `app-lam`, 80% on `shift-cascade`. This is direct
evidence for the design bet in `CLAUDE.md` that global cacheability is the
single largest performance lever. It also raises the stakes on the context-free
certificate discipline: a context-relative certificate would make this cache
per-declaration and turn 88% hits into a small fraction of that.

**Beta dominates the reduction mix — 81% on `init-prelude`, 80% on
`grind-ring-5`.** Delta and iota are each roughly 9% on `grind-ring-5` and
together 16% on `init-prelude`. Everything else is noise by comparison. So the
kernel's beta rule is the hot path, and the certificate representation for beta
is the one worth optimising; proof irrelevance, eta and quotient reduction are
rare enough that a slow path for them costs nothing.

**Literal arithmetic is real but not dominant** — 19,692 steps on
`grind-ring-5`, about 1% of reductions. That is small in count and enormous in
consequence: these are precisely the steps that have no feasible-length Peano
derivation, which is why milestone 4 makes them primitive kernel rules rather
than deriving them. A 1% step count that would otherwise be unbounded is exactly
the shape of problem native bignum arithmetic exists to solve.

**Caveat on scale.** These are arena workloads, not mathlib. `grind-ring-5` at
1.9M reduction steps is the largest thing measured here and it is still tiny
next to a full mathlib check. The headline question — what the number looks like
at mathlib scale — needs a mathlib export, which is not yet available in this
environment. The mix, though, has been stable across two very different
workloads, and the mix is what the kernel API design depends on.

**Caveat on counting.** `app-lam` and `shift-cascade` report ~0 reduction steps
against tens of thousands of `def_eq` calls: they are structural-comparison
workloads that the quick-check and cache paths settle without ever reducing.
This is a property of those tests, not a gap in the instrumentation.

## Certificate provenance, 2026-07-30

Once `def_eq` threads certificates, the same probe reports where each
definitional-equality conclusion came from. `init-prelude`, 2059 declarations:

| provenance | count |
| --- | ---: |
| certified by a real backend rule | 58,694 |
| admit `def_eq_binder` | 4,978 |
| admit `lazy_delta` | 1,126 |
| admit `eq_cache` | 687 |
| admit `def_eq_app` | 470 |
| admit `def_eq_proj` | 16 |
| admit `proof_irrel` | 7 |
| admit `eta_struct` | 3 |
| admit `def_eq_local`, `string_lit`, `unit_like`, `bool_true` | 0 |
| **total admitted** | **7,287 (11%)** |

Reproduce with `cargo build --release --features stepcount`.

**This number must reach zero before the TG backend can be trusted.** It is the
honest measure of how much of milestone 3 remains: every admit is a place the
checker concludes an equality it cannot yet justify.

Two observations worth carrying forward:

**The union-find cache is a much smaller job than the hit rate suggests.** 57,800
`def_eq` calls are answered from cache, but only 687 become `eq_cache` admits —
the rest are settled by pointer equality, which on a hash-consed representation
*is* alpha equality and discharges as reflexivity. So the proof-producing
union-find (explain-paths over a proof forest) has to serve roughly 1% of cache
hits, not all of them.

**Binder comparison is the largest single hole** at 4,978, which matches where
the design risk is: descending under a binder is exactly where a context-free
certificate has to universally quantify over the local's interpretation rather
than assume a local context. That is the `lam_cong`/`pi_cong` work, and it is
the one to do first.

### After real congruence certificates

Folding `lam_cong`/`pi_cong`/`app_cong` instead of admitting, and composing the
whnf reduction legs onto the result:

| provenance | before | after congruence | after leg composition |
| --- | ---: | ---: | ---: |
| certified | 58,694 | 70,545 | 70,830 |
| admit `def_eq_binder` | 4,978 | 0 | 0 |
| admit `def_eq_app` | 470 | 0 | 0 |
| admit `whnf` | — | — | 2,681 |
| admit `lazy_delta` | 1,126 | 1,126 | 1,126 |
| admit `eq_cache` | 687 | 687 | 687 |
| admit other | 26 | 26 | 26 |
| **total admitted** | **7,287** | **1,839** | **4,520** |

The rise in the last column is deliberate. `def_eq` compares weak-head-normalised
terms, so its certificate justified `x_n ≡ y_n` rather than the `x ≡ y` it
claimed; the 2,681 `whnf` admits are those previously unrecorded reduction legs,
now named and composed in with real `trans`/`symm`. The count went up because the
accounting became honest, not because anything regressed.

## Tutorial gap ledger, 2026-07-31

538 gaps across 91 tutorial files; 64 files report zero. Measured with
`--features tg`, aggregated by reason:

| count | reason |
| ---: | --- |
| 141 | `pi congruence over an admitted body premise` |
| **134** | **`undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary`** |
| 80 | `trans over an admitted premise` |
| 36 | `congruence over an admitted premise` |
| 34 | `pi congruence: dependent and non-dependent Π interpret differently` |
| 24 | `pi congruence: the domain certificate is not about the binder types` |
| 21 | `iota` |
| 19 | `pi congruence: the body certificate is not about the binder bodies` |
| 10 | `symm over an admitted premise` |
| 4 | `lam congruence over an admitted premise` |
| ≤7 each | `whnf`, `eq_cache`, `nat_eq`, `proof_irrel`, `unit_like`, `quot`, `eta`, `proj_reduce`, `eta_struct`, … |

### What this says

**One root cause accounts for roughly 73%.** The 134 undischarged typing
assumptions, plus the 261 gaps that are explicitly *cascades over an admitted
premise* (141 + 80 + 36 + 4), come to ~395 of 538. Everything else is a long
tail.

`iota`, `quot`, `proj_reduce` and `eta_struct` concern inductive types,
recursors and structures — **out of scope** for the inductive-free fragment, and
they total 25.

## Lean's typing judgement, 2026-07-31

`has_type` is now a family of clauses over the typing rules, including the
**lambda** rule (`lam_in_funspace_n`, `lam_in_dprod_n` — the prefix-threaded
ports of `derived::ext`'s unary originals) and the two delta steps a Lean type
usually needs before a `Π` is visible. An obligation it cannot discharge outright
is *reduced* to the typing of the locals the argument mentions, which is the
shape a `λ` binder discharges, rather than assumed whole.

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 545 | **528** |
| tutorial files at 0 gaps | 65 | **67** |
| tutorial escapes | 134 | 133 |
| `028_peano2` gaps | 8 | **0** |
| `029_peano3` gaps | 9 | **0** |
| `init-prelude` gaps | 15953 | 15937 |
| `init-prelude` obligations discharged (of ~17.5k) | 486 | **1451** |
| `init-prelude` runtime | 8.5 s | 9.1 s |
| `init-prelude` peak RSS | 124 MB | 133 MB |

**The inductive-free fragment is complete.** Tutorial exports 001–032 — all 27
of them, everything before `033_empty` introduces the first `inductive` — now
report zero gaps *and* zero escaped assumptions. `checker/tests/tg_tutorial.rs`
asserts it.

Corpus-wide movement is small, and the ledger says why rather than leaving it a
guess. Of `init-prelude`'s 17537 obligations, 5186 are about a **local at the top
level**, where nothing is assumed and nothing is derivable, and 3959 are about an
**opaque constant or an application of one** — an inductive type, constructor or
recursor, which carries no axioms at all. Those 8919 are not reachable by any
typing rule; the interpretation of inductives is what the second half needs, and
it is out of scope for this fragment.

The clause split on `init-prelude` after the change: 5183 by the binder's own
assumption, 1001 by `lam_in_funspace_n`, 702 by `x ∈ U(x)`, 26 by
`lam_in_dprod_n`, 8 by the constant rule, 3 by the application rule, 2 by
`fs(a,a) ∈ U(a)`.

### Why the root is now tractable

The assumption is `⟦a⟧ ∈ ⟦A⟧` where `a` is a **constant or an application** —
never a variable, which is why it cannot be discharged at a binder. But once
`Π` is interpreted as `ext::DProd`'s `dprod` rather than an opaque symbol, each
case has a route:

* **application** `f a` — `dprod`'s characteristic property *is*
  `∀x ∈ A. app(f,x) ∈ b(x)`, so `⟦f a⟧ ∈ ⟦B[a]⟧` follows from `⟦f⟧ ∈ ⟦Π A B⟧`
  and `⟦a⟧ ∈ ⟦A⟧`;
* **constant** `c` — `⟦c⟧` is *defined* as `⟦value⟧`, so it reduces to the
  declaration's own typing, recursively;
* **lambda** — the graph is a section of the fibres, which is what `dprod`
  membership asks for;
* **sort** — `x ∈ U(x)`, already available;
* **local** — the carried hypothesis, already handled.

So the "full type-directed interpretation" is not an open-ended milestone any
more: it is a `has_type` family on `Certifier` with one clause per Lean typing
rule, and the `dprod` interpretation is its enabler. That interpretation is the
change currently in flight for the encoding-mismatch gaps, which means it
unblocks both.

## Beta-reducing the *target* type, 2026-07-31 — a measured negative

`has_type` unfolds a target along its defining equation (`HtClause::TypeDelta`)
but never beta-reduced one. A Lean type like a motive `C xs` interprets to a
set-*application* `app(⟦C⟧, ⟦xs⟧)`, so an obligation stated at it matched no
clause at all. `HtClause::TargetBeta` is the type-level analogue: reduce the
target one head step — beta when the head is a lambda graph, delta when it is a
defined constant, the head first when the application is curried — settle the
obligation against the reduct, and carry the membership back by Leibniz. Beta's
own premise `x ∈ A` is discharged by `target_mem`, which recovers the Lean node
`x` was interpreted from and runs the whole `has_type` recursion on it, so the
premise is derived or *acquired as an antecedent* — never assumed.

**It works, and it changes nothing.** Every gap, escape and derivation count in
the corpus is byte-identical before and after, per file:

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 509 | 509 |
| tutorial escapes | 115 | 115 |
| tutorial `derived (real kernel Thm)` | 7514 | 7514 |
| tutorial files at 0 gaps | 67 | 67 |
| inductive-free fragment | 0 gaps, 0 escapes | 0 gaps, 0 escapes |
| `073` / `075` / `076` / `077` gaps | 12 / 72 / 87 / 187 | 12 / 72 / 87 / 187 |
| `init-prelude` gaps | 15646 | 15646 |
| `init-prelude` escapes | 2486 | 2486 |
| `init-prelude` runtime | 9.6 s | 9.7 s |

What *did* move is the shape of what is carried. Corpus-wide the clause fires 24
times on the tutorials and 8 on `init-prelude`, and the **raw fallback** — the
obligations that end in the bare assumption `⟦a⟧ ∈ ⟦dom⟧`, the one form that
blocks generalisation at a binder — drops from 143 to 119 over the tutorials:

| raw fallback, by target shape | before | after |
| --- | ---: | ---: |
| `app(lam(…), x)` — a redex | 25 | **1** |
| `app(app(…), x)` — curried | 44 | 44 |
| `app(c, x)` for a defined constant `c` | 3 | 3 |
| something else | 71 | 71 |
| **total** | **143** | **119** |

(The 44 curried ones are 40 with an opaque spine head and 4 with a lambda graph
at the bottom of the spine; the split is measured on the *after* build, and is
the same before because the clause never fires on any of them.)

By subject shape the 24 are 18 locals — that category falls from 20 to 2 — and 6
lambdas. Unconditional discharges rise 104 → 110, and
`076_listRecReduction` alone accounts for 12 of the 24 uses — exactly the 12
obligations about a bare local whose declared type interprets to `⟦List α⟧`
while the obligation is stated at `⟦C xs⟧`.

### Why it does not convert

Because **only a closed argument can close a gap**, and these do not become
closed — they become conditional on `⟦xs⟧ ∈ ⟦List α⟧`, which is already among
the assumptions those certificates carry. The escape ledger therefore does not
grow either (`076` stays at 21 escaped of 50 conditional derivations made), and
the ledger balances on every file in the corpus: `made == accounted + escaped`.

### Where the lever runs out

`app(lam(…), x)` targets are nearly exhausted: 25 of 25 minus one over the
tutorials. On `init-prelude` there are 1254 of them and only 8 reduce, and the
new `TbMiss` counters say why — of 5786 redexes reached, 3436 fail beta's own
domain premise and 2686 reduce fine but leave an obligation that is still not
derivable at the reduct. So on the big corpus the binding constraint is not the
missing reduction, and adding it does not expose one.

The 40 curried targets with an **opaque spine head** are the largest remaining
block, and they are not a reduction problem at all: `⟦RBNode α β⟧` has nothing
to reduce, only an inductive that is not interpreted. That is the same wall
`INDUCTIVES.md` describes, not a new one.

## Iota for `Bool.rec`, and a dropped reduction leg, 2026-07-31

Two changes, measured separately and then together.

**Iota became a rule.** `Certifier` gained an `iota` method — the only change to
`kernel/`, 628 → 631 non-comment lines, no new axiom and no new way to build a
`Thm`, with a default implementation delegating to `admit` so every other
backend is unchanged. `TgBackend::iota` derives it for a two-constructor
enumeration: `⟦Bool.rec.{u}⟧` becomes a nest of four lambda graphs
(`RecNest`) over `derived::wbool_rec`'s W-recursor, whose two computation rules
are unconditional in the minor premises.

**A reduction leg was being dropped.** `def_eq` compares weak-head-normalised
terms and must compose the two reduction legs back on. The quick check on the
*reduced* pair returned early and skipped that, so when one side reduced to the
other it returned **reflexivity as the certificate for `x ≡ y`**. The backend's
congruence guard caught it where the caller was a congruence — the nine
`congruence: derived equation does not match the claim` gaps below — and nothing
caught it where the caller was the top-level judgement.

| | before | iota only | both |
| --- | ---: | ---: | ---: |
| tutorial gaps (91 files) | 509 | 502 | **358** |
| tutorial escapes | 115 | 117 | **47** |
| tutorial `derived (real kernel Thm)` | 7514 | 7523 | **7764** |
| tutorial files at 0 gaps | 67 | 67 | **68** |
| `073_boolRecEqns` | 12 | 10 | **0** |
| `075_nRecReduction` | 72 | 72 | **54** |
| `076_listRecReduction` | 87 | 87 | **63** |
| `077_RBTree.id_spec` | 187 | 187 | **101** |
| `116_rtreeRecReduction` | 23 | 18 | **10** |
| `init-prelude` gaps | 15646 | — | **11570** |
| `init-prelude` escapes | 2486 | — | **812** |
| `init-prelude` runtime | 17.6 s | — | **10.3 s** |
| inductive-free fragment | 0 gaps, 0 escapes | unchanged | unchanged |
| arena | 152/0/2 | 152/0/2 | 152/0/2 |

`073_boolRecEqns` is at **zero gaps and zero escapes** — the first file in the
corpus where a recursor meets a constructor and every step is a real kernel
theorem. The ledger balances on all 91 files (`made == accounted + escaped`).

Three files got *worse*, and that is the accounting becoming honest:
`094_ruleK` 8 → 10, `124_quotLiftReduction` 8 → 9, `125_quotIndReduction`
7 → 8. Each reduces through a step this backend cannot justify (`Eq.rec`'s
`is_k` iota, `Quot.lift`) and each was previously getting a dropped leg and a
reflexivity certificate instead of a reported gap.

### The gap ledger, before and after

| before | after | reason |
| ---: | ---: | --- |
| 161 | 109 | `pi congruence over an admitted body premise` |
| 115 | 47 | `undischarged assumption … survived to the boundary` |
| 76 | 81 | `trans over an admitted premise` |
| 35 | 42 | `congruence over an admitted premise` |
| 35 | **0** | `pi congruence: the domain certificate is not about the binder types` |
| 21 | 18 | `iota` (now split by why: 17 "not four arguments", 1 "no curried interpretation") |
| 9 | **0** | `congruence: derived equation does not match the claim` |
| 10 | 13 | `symm over an admitted premise` |
| 6 | 6 | `eq_cache` |
| ≤7 each | ≤10 each | the tail |

The two categories that went to zero are the dropped leg: a certificate about
the reduced pair, handed to a rule that then compared it against the unreduced
claim. The `iota` row is now *diagnostic* rather than a single bucket, which is
what says where the next rung is — every remaining one is a recursor whose
arity is not four, i.e. `N.rec`, `List.rec`, `Eq.rec`, `Acc.rec`, `prod.rec`.

### Why the conditional certificate closed the gap this time

`073`'s iota certificate is **conditional**: `Bool.rec`'s motive and two minor
premises are context locals, so it rests on `⟦motive⟧ ∈ ⟦Bool → Sort u⟧` and the
two minors' typings. It still closes the gap. `073` makes 16 conditional
derivations and accounts for all 16, because with nothing admitted below them
the binder discharge in `pi_cong`/`lam_cong` reaches them.

So the rule recorded in `INDUCTIVES.md` — **"only a closed argument can close a
gap"** — is too strong, and the corrected form is: *a conditional certificate
closes a gap exactly when no admitted step sits below it.* An admit poisons
every rule above it one at a time; it is the poison, not the conditionality,
that strands the assumptions. The four earlier measured negatives all added
derivations underneath an unrepaired admit, which is why none of them converted.

## Iota for `N.rec`, and two older bugs it uncovered, 2026-07-31

`N.rec` is wired end to end: `nat_recursor()` on a `RecCore` shared with
`bool_recursor()`, `rec_nest`'s bottom made pluggable and its depth read off
`major_idx`, `derive_iota` generalised to a recursor applied past its major
premise and to a major premise applied to its constructor fields, and
`derived::wnat_rec`'s two ι rules discharged at the point of use with `HYP`
supplied from the recursor's own domain obligations. No change to `kernel/`.

Two bugs older than any of this surfaced the moment an ι certificate reached
them, and both are measured separately below.

**`derive_beta` over-reduced.** It counted its contractions on the
*substituted* head rather than on the syntactic lambda nesting. `075`'s zero
rule is `(λ motive zero succ. zero) C z s m`: the checker peels three lambdas
and re-applies `m`, but after three substitutions the head is `fun m => m`, so
the backend took a fourth contraction and derived a *different* equation. Its
own guard caught it every time — the three
`beta: derived equation does not match the reduction` gaps — so nothing false
was ever claimed; the derivation was simply not being found.

**A memoised reduct with no certificate.** `whnf` is called both for its answer
and for its evidence, and the answer is memoised the first time. When the first
call did not want evidence, a later certified call found the reduct and nothing
justifying it, and `recall_reduction` could only admit. The fix measured below
re-ran the reduction and used the certificate **only if it landed on the
memoised reduct**. That fix has since been **replaced**: re-running a memoised
computation on a cache hit gives back the work the memo exists to avoid, and the
memo's value type now carries the evidence instead — see *Memoise a result,
memoise why* below. The numbers in this table are the ones the re-running
version measured, and are kept as the record of that step.

| | before | ι only | + `derive_beta` | + `whnf` recall |
| --- | ---: | ---: | ---: | ---: |
| tutorial gaps (91 files) | 358 | — | 316 | **296** |
| tutorial escapes | 47 | — | 48 | **48** |
| tutorial `derived (real kernel Thm)` | 7764 | — | — | **7827** |
| tutorial files at 0 gaps | 68 | — | 68 | **68** |
| `073_boolRecEqns` | 0 | 0 | 0 | **0** |
| `075_nRecReduction` | 54 | 33 | 12 | **4** |
| `101_proofIrrelevanceWhnf` | 10 | — | 10 | **6** |
| `113_reduceCtorParamRefl.mk` | 5 | — | 5 | **1** |
| `114_reduceCtorParamRefl2.mk` | 6 | — | 6 | **2** |
| `076_listRecReduction` | 63 | — | 63 | **63** |
| `init-prelude` gaps | 11570 | — | — | **10919** |
| `init-prelude` escapes | 812 | — | — | **834** |
| `init-prelude` `derived` | — | — | — | **85987** |
| inductive-free fragment | 0 gaps, 0 escapes | — | unchanged | **unchanged** |
| arena | 152/0/2 | — | 152/0/2 | **152/0/2** |
| `derived` tests | 370 | 370 | 370 | **370** |

A dash is "not measured at that stage", not "unchanged": only `075` was run
after the ι wiring alone.

Nothing else in the tutorial corpus moved by a single gap or a single escape.
`init-prelude`'s runtime is unchanged within noise (~48 s in this debug build,
measured against the same build with the `whnf` recall reverted).

### `075`'s remaining four, and why they are not the recursor

`gap: iota …` is **gone** — all six. What is left is two
`pi congruence: the body certificate is not the fibres' pointwise equation`
(the `dprod_ext` route; 283 occurrences on `init-prelude`, a pre-existing
weakness that an admit was previously hiding), one congruence above them, and
**one** escaping certificate.

That certificate carries three assumptions and is worth one gap, not three:
`⟦motive⟧ ∈ ⟦N → Sort 1⟧` — the closed-motive obstruction, wanting
`fs(N,N) ∈ U(⟦Sort 0⟧)` over an opaque `⟦Sort 0⟧` and dischargeable at no
binder — plus the `succ` minor premise's typing at the dependent `doms[2]` and
at its beta-reduced form `fs(⟦N⟧, fs(T,T))`. `INDUCTIVES.md` predicted the
first of the three and predicted that the cascade would largely *become*
escapes. It did not: an admit poisons every rule above it one at a time,
whereas a conditional certificate is one gap however far it travels.

## `List.rec` wired — 2026-07-31

The corpus's only `List` file, and the milestone the inductives push was aimed
at. `derived/src/wlist_rec.rs` packs Lean's two minor premises into the
W-recursor's single step for a constructor carrying a **field** as well as a
recursive argument; `checker/src/tg.rs` gained `RecBottom::List`,
`list_rec_shape`, `list_recursor()`, `fire_list` and `mem_along_c`, and
`derive_iota_core` stopped rejecting a constructor with parameters.

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 296 | **265** |
| tutorial escapes | 48 | **49** |
| tutorial files at 0 gaps | 68 | 68 |
| `073_boolRecEqns` | 0 gaps, 0 escapes | 0, 0 |
| `075_nRecReduction` | 4 gaps, 1 escape | 4, 1 |
| `076_listRecReduction` | 63 gaps, 15 escapes | **32, 16** |
| `076` ι gaps | 5 | **0** |
| `077_RBTree.id_spec` | 101 gaps, 19 escapes | 101, 19 |
| `116_rtreeRecReduction` | 10 | 10 |
| `init-prelude` gaps | 10919 | **10771** |
| `init-prelude` escapes | 834 | **843** |
| `init-prelude` `derived (real kernel Thm)` | 85987 | **86144** |
| `init-prelude` runtime | 10.3 s | 12.4 s |
| inductive-free fragment (27 files) | 0 gaps, 0 escapes | unchanged |
| arena | 152/0/2 | 152/0/2 |
| `derived` tests | 376 | **384** |

Nothing else in the tutorial corpus moved by a single gap or escape: the whole
31-gap improvement is `076`. The `derived` count needs one word of explanation:
the handover's baseline of 370 was right, and a *concurrent* session added
`derived/{src,tests}/choice.rs` — six tests — while this work was in progress,
so the tree measured 376 immediately before these eight landed.

### `076`'s remaining 32, and why none of them is the recursor

32 = **16 escapes** + **3 primary gaps** + **13 cascade** over those three.
The three primaries are two `eq_cache` and one
`pi congruence: the body certificate is not the fibres' pointwise equation` —
the `dprod_ext` route, 283 occurrences on `init-prelude`, and also two of
`075`'s remaining four. The cascade is 6 `congruence over an admitted premise`,
4 `trans over an admitted premise` and 3 `pi congruence over an admitted body
premise`.

The escapes are the interesting half, because the handover predicted zero of
them. **They are not the recursor's**, and the measurement that settles it is
that `076` had 15 escaping certificates *before* any ι certificate existed and
has 16 after: closing five ι gaps and 26 cascade gaps beneath them moved the
escapes by one. Probing what those certificates assume gives, by occurrence:

| assumption | occurrences | dischargeable at a binder? |
| --- | ---: | --- |
| `⟦α⟧ ∈ ⟦Type 0⟧` | 15 | yes — but the `pi_cong` above it admitted |
| `⟦xs⟧ ∈ ⟦List α⟧` | 4 | yes, same |
| `⟦h⟧ ∈ ⟦α⟧` | 2 | yes, same |
| `⟦fun _ : List α => List α⟧ ∈ ⟦List α → Sort 1⟧` | 1 | **no** — wants `⟦List α⟧ ∈ ⟦Sort 1⟧` |
| the cons minor premise's typing | 2 | **no** — wants the motive beta-reduced in the fibre |

The last two rows are the obstructions already on record from `075`: `wlist.rs`
records `lt(α) ∈ ⟦Sort u⟧` as underivable with this `Sort` encoding, since
nothing relates `W(1+α,fam,U(1+α))` to `U(⟦Sort 0⟧)` over an opaque `⟦Sort 0⟧`.
The first three are *locals*, and they escape only because a `pi_cong` above
them admitted and so could no longer peel their guards.

So the corrected rule gains a third clause: an admit poisons every rule above it
one at a time; a conditional certificate is one gap however far it travels; and
a conditional certificate whose binder-discharge is blocked by an admit above it
escapes **even though its assumption is a local's**. `073` reaches zero because
nothing above its certificates admits. `pi_cong`'s extensionality route remains
the single cheapest change that would move `075`, `076` and `077` together.

## Memoise a result, memoise why — 2026-07-31

Two memos handed back answers without the evidence for them. Both now carry the
certificate in the memo's own value type, so a hit returns it; neither re-derives
anything on a hit.

**The reduct memo** (`whnf_cache`, `whnf_no_unfolding_cache`). Its value was an
`ExprPtr`, with certificates in a parallel `(input, reduct) -> cert` table that
only certified calls ever filled. A reduct memoised by an uncertified call — most
of them, since most `whnf` calls come from type inference — therefore had nothing
to hand a later certified one, which admitted `Admit::Whnf` or, in the previous
fix, **re-ran the reduction**. The value type is now `reduct + reduction`
(`checker/src/reduct.rs`): the reduction always records the rules it applied and
their endpoints — a few words a step, no backend call — and the first caller that
wants a certificate builds one *from that record*, without reducing again, and
stores it in the same entry.

**The equality cache** (`eq_cache`). A union-find hit was an `Admit::Cache`: the
certificates that justified the unions were discarded at the point of union. Each
edge now carries the certificate for the pair it was created from, and a hit is
answered by composing along the explain path with real `trans`/`symm`
(`checker/src/union_find.rs`).

| | before | + reduct memo | + `eq_cache` |
| --- | ---: | ---: | ---: |
| tutorial gaps (91 files) | 265 | 265 | **263** |
| tutorial escapes | 49 | 49 | **49** |
| tutorial files at 0 gaps *and* 0 escapes | 68 | 68 | **68** |
| tutorial `derived (real kernel Thm)` | 7859 | 7856 | **7856** |
| tutorial `eq_cache` gaps | 6 | 6 | **4** |
| `init-prelude` gaps | 10771 | 10733 | **10219** |
| `init-prelude` escapes | 843 | 804 | **804** |
| `init-prelude` `derived` | 86144 | 86146 | **86245** |
| `init-prelude` `eq_cache` gaps | 687 | 687 | **272** |
| `init-prelude` `whnf` gaps | 2 | **0** | **0** |
| `init-prelude` runtime | 11.55–11.79 s | — | **11.50–11.55 s** |
| `init-prelude` peak RSS | 168.1–169.0 MB | — | **169.0–169.1 MB** |
| inductive-free fragment (27 files) | 0 gaps, 0 escapes | unchanged | unchanged |
| `073` / `075` / `076` / `116` | 0/0, 4/1, 32/16, 10/1 | unchanged | unchanged |
| arena | 152/0/2 | 152/0/2 | 152/0/2 |

`101_proofIrrelevanceWhnf` moved 6 → 5 and `114_reduceCtorParamRefl2.mk` 2 → 1
with the reduct memo; nothing else in the tutorial corpus moved by a gap or an
escape. Three tutorial derivations disappeared (7859 → 7856, all in `075`)
because a certificate that used to be built twice is now built once.

**Memory is the point of the exercise, and it barely moved: +0.3% peak RSS.**
Three runs each. The traces are `Rc`-shared trees, so a reduction's steps are
stored once however many memo entries contain that reduction; storing them flat
would have been quadratic. Without the TG backend (`NullCertifier`, what the
arena runs) `init-prelude` goes 6976 KB → ~6996 KB and 0.08 s → 0.08 s.

### Two measured negatives, both load-bearing

**Flattening the trace cost 971 gaps.** The first version of the reduct memo
stored a flat list of steps and folded a certificate over it. That loses the
sharing the old parallel table had: a sub-reduction that already had a
certificate used to contribute *that certificate* and one `trans`, and flattening
made it contribute its `n` steps and `n` `trans`. Since a `trans` over an
admitted premise is itself a reported gap, one gap became `n`:
`init-prelude`'s `trans over an admitted premise` went 4716 → 5687 and its
`proj_reduce` 547 → 566, for 11720 gaps against a baseline of 10771. The tree
form is not an optimisation.

**Caching *conditional* certificates on union edges cost 47 escapes and four
files.** A certificate parked in a cache is a second copy, and for a conditional
derivation that is a second undischarged obligation which no binder will ever
reach — the escape ledger counts it, correctly. Caching every certificate took
the tutorial corpus to 291 gaps and 96 escapes and knocked `028_peano2` (0 → 2),
`029_peano3` (0 → 5), `073_boolRecEqns` (0 → 2) and `081_PSigma.snd` (0 → 2) off
zero, on `init-prelude` 804 → 1243 escapes. Caching only the certificates that
rest on nothing (`certify::is_unconditional`) keeps 415 of the 687 closed
`eq_cache` gaps on `init-prelude` and costs no escapes at all. The union still
happens for a conditional verdict — the checker's decisions must not depend on
what the backend could prove — the edge simply carries no certificate, and a path
through it still admits. That is what the 272 remaining `eq_cache` gaps are.

The same argument explains why the reduct memo stores a certificate only into a
trace the memo is actually holding: `whnf`'s cheap-projection variant builds a
trace per call and memoises nothing, and parking a conditional certificate in a
node about to be dropped cost 843 → 5037 escapes on `init-prelude` before the
test for it was added.

### Not eviction

An earlier note in `checker/src/tg.rs` recommended that cache eviction, when it
came to be written, be a high-water-mark LRU over `lam_infos`. **That
recommendation is withdrawn and the note is corrected in place.** Eviction is a
change to how nanoda works, and this crate instruments nanoda rather than
restructuring it; it would also make what the checker can hand back depend on how
much memory it has used, which is precisely the property a certificate-carrying
checker must not acquire. Paying memory to keep a certificate beside every
memoised result is the intended trade. Measuring the memory stays worthwhile — it
is information — and the measurement above is what it says: 0.3%.

## `pi_cong`'s extensionality route: one refusal, 1249 gaps — 2026-07-31

The measured next lever was `pi_cong`'s extensionality route, on the reading that
its two failing categories were about the *fibre's construction* or about what
the body certificate was proving. **Both readings were wrong, and the third
attempt at reading them from the outside was wrong too.** What was actually
happening was found by instrumenting, not by arguing.

### The diagnosis

A temporary probe classified every failure of
`TgBackend::pointwise_premise` by how far it got, over the whole of
`good/init-prelude.ndjson`:

| where the route stopped | count |
| --- | ---: |
| the fibre skeleton did not instantiate | 0 |
| the unfolded skeletons did not match the certificate | 0 |
| a transitivity step failed | 0 |
| **`guard_and_generalise` refused** | **216** |

That is the whole distribution: **216 of 216**. In every one, the two fibre
definitions unfolded at the binder's variable to exactly the certificate's two
sides — the certificate *was* the fibres' pointwise equation, which is what the
gap's own wording denied.

What refused was the generalisation. `guard_and_generalise_at` turns
`⊢ conj(hyps) → φ(w)` into `⊢ conj(rest) → ∀w. (w ∈ A → φ(w))` with
`Thm::ax_dist`, and the kernel checks `ax_dist`'s side condition: `w` must not be
free in `conj(rest)`. Probing the leftover assumptions:

| leftover assumptions mentioning `w` | count |
| --- | ---: |
| shape `t ∈ s` with `w` free in `t` | 216 (every case) |
| the binder's own guard `w ∈ A` present too | 17 |
| the binder's own guard absent | 199 |

So the blocker is uniform: the certificate carries a **beta typing obligation
about an argument that depends on the binder**, and that obligation is stated at
a variable which is about to be bound. `ax_dist` is right to refuse. Nothing was
wrong with the fibre, the skeleton, the certificate's provenance, or any guard.

### The fix

Re-state such an assumption at every point of the domain at once, before
generalising:

```text
φ(w)      becomes      ∀w. (w ∈ A → φ(w))
```

which is `w`-free, and which — instantiated at this `w`, under this guard —
gives `φ(w)` back. It is a weakening of the assumption set: strictly more is
assumed than is used, the assumption stays in the returned list, and it is still
owed. It is also a shape a discharge can *reach*, being literally what the lambda
typing rule proves; `φ(w)` was not.

Twenty lines in `guard_and_generalise_at`, no new lemma, no change to `derived/`,
no change to `kernel/`.

### Before and after

| | before | after |
| --- | ---: | ---: |
| `init-prelude` TOTAL gaps | 10219 | **9650** |
| … `pi congruence: the body certificate is not the fibres' pointwise equation` | 214 | **0** |
| … `pi congruence: the body certificate does not make the fibre constant` | 465 | **0** |
| … `pi congruence over an admitted body premise` (the cascade) | 1293 | 743 |
| … `lam congruence over an admitted premise` | 179 | 177 |
| … escaped assumptions | 804 | **1484** |
| `init-prelude` derived (real kernel Thm) | 86245 | 87494 |
| tutorial corpus TOTAL gaps | 263 | **210** |
| tutorial escapes | 49 | 68 |
| tutorial files at zero gaps | 68 | 68 |
| tutorial files at zero escapes | 79 | 79 |

Per file, and only six moved in the whole corpus:

| file | gaps | escapes |
| --- | ---: | ---: |
| `073_boolRecEqns` | 0 → 0 | 0 → 0 |
| `074_prodRecEqns` | 16 → 14 | 2 → 4 |
| `075_nRecReduction` | 4 → **3** | 1 → 3 |
| `076_listRecReduction` | 32 → **31** | 16 → **17** |
| `077_RBTree.id_spec` | 101 → **53** | 19 → 31 |
| `116_rtreeRecReduction` | 10 → 10 | 1 → 2 |
| `118_accRecReduction` | 13 → 12 | 2 → 3 |

The 27-file inductive-free fragment stays at zero gaps and zero escapes; the
arena stays 152 / 0 / 2; `cargo test -p derived` stays at 384.

### What this bought, stated honestly

**Primary gaps fell by 1249 on `init-prelude`; 680 of that came straight back as
escapes.** The net is 569. The whole of the `pi_cong` extensionality and bridge
categories is gone, and so is 550 of their cascade — but the assumption those
routes were stumbling over did not disappear, it moved: `pi_cong` now succeeds
*conditionally*, the hoisted obligation rides up, and nothing yet discharges it.
That is the honest accounting and it is why the headline files move by so much
less than the category counts do.

### The hypothesis under test, and what happened to it

The handover's belief was that this single change moves `075`, `076` and `077`
**together**, on the evidence that `076`'s sixteen escapes were blocked by a
`pi_cong` above them that could no longer peel their guards.

- `077_RBTree.id_spec` **halved**, 101 → 53. That is the real result, and it was
  not the file the hypothesis was built on.
- `075_nRecReduction` moved 4 → 3: both its `pi_cong` gaps closed, and the
  congruence above them, but two new escapes appeared under them.
- `076_listRecReduction`'s sixteen escapes **did not fall. They rose to
  seventeen.** The file moved 32 → 31.

So the specific prediction is refuted: `076`'s escapes are not `pi_cong`'s. This
is now the *third* independent line of evidence about those sixteen — they
predate `List.rec`, they survived closing 31 gaps beneath them, and they survive
closing the `pi_cong` gap above them. Whatever holds them, it is not a
congruence rule, and the next agent should stop attributing them to one.

The general belief behind the lever — that this is where the measured mass is —
held: 1249 primary gaps is the largest single move recorded in this file.

### The next lever

It is now unambiguous, and it is the *same* obligation in both halves of the
ledger: **discharge a guarded family of typing obligations**
`∀x. (x ∈ A → ⟦a(x)⟧ ∈ ⟦A(x)⟧)`. That is what 680 of the new escapes are, it is
what most of the remaining 1484 are, and it is the antecedent of every conditional
certificate that reaches a boundary. The machinery for the shape already exists —
`has_type_lam` proves exactly it — and what is missing is a consumer: a rule that,
handed a conditional certificate whose assumption is a guarded universal, tries
`has_type` under the binder's own assumption and peels it. The hoisting done here
was deliberately chosen to produce that shape rather than any other.

## The consumer for the guarded family: built, and it fires zero times — 2026-07-31

The lever above was built. `TgBackend::discharge_families`/`peel_family`, hooked
at `TgBackend::cert` — the one funnel every conditional certificate this backend
hands back passes through — takes an assumption of the hoisted shape
`∀w. (w ∈ A → φ(w))`, re-opens it at the variable it was closed over, asks
`has_type` for `φ` with `w ∈ A` in force, re-closes what comes back through the
*same* `guard_and_generalise_at`, compares the result against the very assumption
being removed, and peels it by modus ponens. Nothing is dropped: `reassume`,
`hyp_mp` and `CondEq::new` each refuse a mismatch, and `peel_off` — the algebra,
factored out so it is testable — has a unit test asserting that a proof of the
*wrong* assumption, or of the right one under the wrong hypotheses, peels
nothing.

**Every number in the corpus is unchanged.** Tutorial 210 gaps / 68 escapes,
68 files at zero gaps *and* zero escapes; `init-prelude` 9650 / 1484, derived
87494; `073` 0/0, `075` 3/3, `076` 31/17, `077` 53/31, `116` 10/1, `118` 12/3;
the 27-file fragment at zero and zero; arena 152/0/2; `cargo test -p derived`
384; `./ci/check.sh` all checks passed. `init-prelude` 11.59–11.68 s and
169.0–169.7 MB before against 11.59–11.61 s and 169.5–169.7 MB after, three runs
each — no measurable cost.

### Why it fires zero times, measured rather than argued

A ladder counting how far each attempt gets is now printed on every run. On
`init-prelude`:

| stage | count |
| --- | ---: |
| a hoisted guarded family was offered | 1378 |
| …its binder is free in no other assumption | 1378 |
| …the obligation is a membership (the rest are **nested** families) | 825 |
| …its subject has a Lean node | 825 |
| …**`has_type` derived it under the guard** | **0** |

Nothing refuses on the way in. The typing call fails, and it fails for a reason
that was there before the consumer was written: a hoisted assumption is a beta
obligation that reached `domain_obligation`'s **raw fallback**, and that fallback
fires only after `has_type` has already failed *both* with no assumptions *and*
under `local_premises` — the typings of every local the argument mentions, which
is a superset of the single guard the consumer has to offer. The consumer's
retry is the same failing call, weakened. The premise that "the machinery for
the shape already exists" was true of the *shape* and false of the *subjects*.

Probing the subjects by head symbol settles what they are, and the answer is the
same on `init-prelude` and on the tutorials: **constructor applications of
inductives this backend does not interpret**, plus recursor applications.
`init-prelude`'s top heads are `Decidable.isFalse` (39), `Decidable.isTrue` (35),
`Lean.Name.num` (24), `Lean.Name.str` (23), `Option.some` (21),
`Lean.Syntax.node` (20), `Or.inl`/`Or.inr` (16 each), `List.cons` (13); the
tutorials' are `RBTree.red`/`RBTree.black` (6 each on `077`), `Prod.mk` (`074`),
`RTree.node` (`116`), `Acc.intro` (`118`), `N.rec` (`075`), `List.rec` (`076`).
An uninterpreted inductive has no membership fact to derive *from*.

### What the escapes are — all of them, not just the hoisted ones

Since the guarded family turned out to be a wrapper rather than a cause, the
whole escape population was probed: every certificate that reached a boundary
still conditional, classified by what it assumes, family wrappers unwrapped.

| the escaping certificate assumes | tutorial | `init-prelude` |
| --- | ---: | ---: |
| only context locals' own typings `⟦w⟧ ∈ ⟦A⟧` | 26 | 413 |
| those plus a lambda's typing | 2 | 29 |
| at least one constructor/recursor obligation | 40 | 1042 |
| **total escaping certificates** | **68** | **1484** |

| assumption atom | tutorial | `init-prelude` |
| --- | ---: | ---: |
| a context local's own typing | 64 | 713 |
| a lambda's typing (the `Sort`-encoding obstruction) | 15 | 193 |
| everything else — constructors, recursors, opaque heads | 40 | 1183 |
| **total atoms** | **119** | **2089** |

19 of the tutorial's 68 certificates and 721 of `init-prelude`'s 2089 atoms are
wrapped in at least one guarded family, nested up to **six** deep on `077`
(`FAMILY[FAMILY[FAMILY[FAMILY[FAMILY[FAMILY[⟦RBTree.black …⟧ ∈ …]]]]]]`) — one
obligation re-hoisted at each successive binder. So the hoisting did not create
escapes so much as *wrap* obligations that were already undischargeable, and the
"680 new escapes are guarded families" reading is, at tutorial scale, 19 of 68.

### `076`'s escapes, finally probed rather than attributed

Asked for directly, and they are not what any of the four hypotheses said. The
seventeen are:

| what escapes | count |
| --- | ---: |
| a single `⟦w⟧ ∈ ⟦A⟧` for a context local, and nothing else | 13 |
| three such | 2 |
| context locals plus the motive lambdas' typings | 1 |
| the same, plus `FAMILY[⟦List.rec …⟧ ∈ …]` | 1 |

**Fifteen of the seventeen assume nothing but the typings of context locals.**
That is why they predate `List.rec`, why closing 31 gaps beneath them did not
move them, and why closing the `pi_cong` gap above them did not either: no rule
in the backend was ever going to touch them. `076` states its theorem under
`∀ α (xs : List α)`, the checker's `infer` opens those binders and then asks
`def_eq` about the bodies, and the binder that would discharge `⟦α⟧ ∈ ⟦Type 0⟧`
is *above the query*, not inside it. A congruence rule discharges a guard only
when the binder is part of the equation it is proving.

### The next lever, and it is a decision before it is a derivation

`⟦w⟧ ∈ ⟦A⟧` for a context local is not a step taken on trust. Carneiro's
Theorem 6.7 (thesis §6.3) reads `Γ ⊢ e ≡ e'` as *for all `γ ∈ ⟦Γ⟧`,
`⟦Γ ⊢ e⟧γ = ⟦Γ ⊢ e'⟧γ`*, so a certificate conditional on exactly the ambient
context's typings **is** the judgement's statement. The bare equation the ledger
compares it against is strictly stronger than what the thesis proves, and false
in general off `⟦Γ⟧` — at `⟦A⟧ = ∅` there is no `γ` at all. On that reading 413
of `init-prelude`'s 1484 escapes and 26 of the tutorial's 68 are complete
derivations of the right statement.

What stops this being a one-line change is a distinction the backend cannot make
today: a local introduced by the checker's `infer`, *above* the `def_eq` query,
is ambient and entitled to the reading; a local the query opened itself is not —
its guard should have been discharged at the binder that opened it, and an
escape there is a real failure. Making the ambient context visible to the
backend is the work; deciding that a context-relative claim is what a top-level
certificate asserts is the call that has to be made first, and it changes what
every headline number in this file means. It should not be made by inference
from a gap count.

The other two rows are unchanged as levers and both are old news: a membership
theorem for constructors of an arbitrary inductive (1183 atoms on
`init-prelude`, 40 in the tutorials), and `⟦T⟧ ∈ ⟦Sort u⟧` for an interpreted
inductive (193 and 15) — the `Sort`-encoding obstruction `wlist.rs` already
records.

## A constant's typing, derived once — and why it cannot be a lookup, 2026-07-31

`check_declar` established `val : ty` and threw the fact away; `has_type_const`
re-derived it at every use by recursing into the constant's *value*, and down
the delta graph beneath it. `TgBackend::MAX_TYPE_DEPTH = 16` existed only to
stop that recursion. The declaration's typing is now formed and stored where it
is established (`Certifier::declar_checked` → `TgBackend::store_declar_typing`),
the depth bound is **gone**, and `has_type_const` consults the store before
deriving.

### What the store can hold

| | `init-prelude` |
| --- | ---: |
| declarations with a value | 1645 |
| …whose typing `⟦val⟧ ∈ ⟦T⟧` is derivable | **12** |
| …derived only under antecedents (never stored) | 0 |
| uses answered from the store | 49 |

The twelve are `id`, `Function.comp`, `Function.const`, `letFun`, `optParam`,
`outParam`, `semiOutParam`, `namedPattern`, `inferInstance`, `inferInstanceAs`,
`instInhabitedBool.default`, `EStateM.dummyRestore`. The ceiling is not the
storage: it is what `has_type` can type at all, and the wall is the
`Sort`-encoding obstruction.

### The lookup cannot replace the derivation — the level-instantiation answer

A stored typing is **one** theorem, `⊢ ⟦c.{us}⟧ ∈ ⟦T_c⟧`, at the declared type
and at the declaration's own universe parameters. Two things vary at a use site
and neither can be absorbed:

* **the target.** An obligation about `c` arrives at whatever target the
  surrounding derivation produced, which is usually not `⟦T_c⟧`.
* **the levels.** `⟦c.{u}⟧` and `⟦c.{0}⟧` are definitions of *different bodies* —
  the value is level-substituted before it is interpreted — so they are
  different symbols and different theorems.

The theorem is therefore **not level-generalised, and cannot be**: this kernel
has no quantifier over universe levels, and a level parameter interprets to an
opaque nullary *constant*, which `gen` cannot abstract and `ax_inst` cannot
instantiate. Level-generalising would mean interpreting parameters as free
variables and every constant as `c(u⃗)` rather than a nullary symbol — a change
to the denotation of everything. So the store is keyed by `(name, interpreted
levels)` and a use at other levels misses, honestly.

**Measured, when `has_type_const` was made a pure lookup:** `028_peano2` lost its
last derivation and the inductive-free fragment went off 27/27. Its `Const` rule
fired 25 times before and 5 after, and every one of the twenty losses was *the
same constant at another universe instantiation* — `PN.lit0`, `PN.lit1`,
`PN.add` used at levels other than the ones `PN.lit0` was declared at. So the
store is a shortcut in front of the derivation, not a replacement for it.

### `MAX_TYPE_DEPTH` is gone, replaced by visited sets

Not lowered — removed, with each edge given a real argument:

* the delta edge is guarded by `const_active`, the constant *instantiations*
  being unfolded on the current path; a repeat is exactly a cycle in the delta
  graph, and the walk is bounded by the size of the environment. This is what
  `ht_active` could not do — it keys on `(e, ty, assms)`, and every step of a
  delta chain is a fresh triple.
* `unfolds_to` and `expose_pi` stop on a term/name already visited, so each runs
  at most once per `abbrev_defs` key / per declaration.
* `typeable_shape` carries the names it has unfolded; `target_head_step` is
  structural on the application spine.
* the target-beta edge keeps only `ht_active`'s cycle cut. Its termination
  argument is weaker than the others' and is written down as such in `tg.rs`.
  Measured: no divergence over `good/**`; deepest successful recursion 9 without
  the store and 17 with it, against the 16 the bound used to allow.

### The cost, and a verdict that turned out to be wrong

Load-matched A/B on the same binary, `init-prelude`, min user time of 5 runs:

| | store off | store on |
| --- | ---: | ---: |
| gaps | 9650 | 9650 |
| escaped assumptions | 1484 | 1484 |
| `derived (real kernel Thm)` | 87494 | 87494 |
| obligations settled `by Const` | 13 | 49 |
| user time | 11.79 s | 16.03 s |
| peak RSS | 171 MB | 194 MB |

The store changes no gap, no escape and no certificate count anywhere in the
corpus, and it looked as though it cost 36% of the runtime. **That reading was
wrong, and the switch that made it possible to act on it has been removed.**

The 36% was never the cost of *storing*. It was the cost of 1645 typing
searches, of which 1633 failed — searches that existed only because `infer`
returned a type and discarded the derivation that justified it. Storing a
constant's typing is not optional: it is the only way to use the fact that
`f : T` when `f` is later applied. There is no `bool` for it any more, and the
`in_declar_typing` flag that existed only to keep the search from re-walking
the delta graph beneath itself is gone with it.

The measurement that replaces this one is *Inference carries its evidence*
below: with the search removed and the typing handed in by `check_declar`, the
same 12 typings are stored and `init-prelude` runs in 11.87 s — faster than with
the store turned off.

### Why the store answers 49 uses and not more

A theorem stored while checking one declaration is about the terms *that*
declaration's backend built, and a `TgBackend` is created and dropped per
declaration. So the constant symbols, the opaque symbols, the universe-parameter
symbols and the de Bruijn-index symbols all moved into the per-thread `Shared`,
keyed by what the Lean side names. Where a shared symbol's defining equation
turns out to be about a *different* body than the backend just interpreted, the
backend mints its own and the event is counted (`shared symbols declined: body
not canonical`).

That counter is **13406** on `init-prelude`, over 557 distinct constants, and it
is the ceiling on how far a stored typing can travel. One cause was found and
fixed: `idx_term` minted a fresh nullary symbol per de Bruijn index *per
backend*, so `⟦#0⟧` — and hence the interpretation of every value with a binder
in it — differed between consecutive declarations. Sharing it took the counter
from 15439 to 13406 and moved no other number. The rest is not diagnosed;
`ind_syms`, `rec_nests`, `let` abbreviations and the per-backend level
representative table (`level_reps`) are all still per-backend and are the places
to look.

### Lean's standard axioms are not what the opaque misses are

`propext`, `Classical.choice` and `Quot.sound` head **zero** typing obligations
in `init-prelude`. The 3848 misses about an opaque constant are, by head:
`Nat` 519, `Nat.succ` 453, `PULift` 166, `Nat.rec` 122, `Eq` 113, `List.cons`
99, `List.nil` 91, `PUnit` 81, `False` 64 — inductive types, constructors and
recursors, without exception. Hand-built typing proofs for the three axioms
would move nothing; these misses ask for more inductives.

## Inference carries its evidence, 2026-07-31

`TypeChecker::infer` returned an `ExprPtr` and nothing that justified it. That is
the same defect as a `bool`-returning `def_eq`, one judgement up: the fact
`⟦e⟧ ∈ ⟦T⟧` is established by the very recursion that computes `T`, and
returning only `T` throws the reason away — after which the only way to get it
back is to search for it. `infer` now returns `Inferred { ty, cert }`, with a
typing certificate threaded through every rule, and `check_declar` composes it
with the (previously discarded) `⟦T'⟧ = ⟦T⟧` certificate to hand
`⊢ ⟦val⟧ ∈ ⟦T⟧` straight to the backend.

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 210 | **210** |
| tutorial escapes | 68 | **68** |
| tutorial `derived (real kernel Thm)` | 7928 | **7928** |
| tutorial files at 0 gaps / 0 escapes | 68 / 79 | **68 / 79** |
| `073` / `075` / `076` / `077` gaps | 0 / 3 / 31 / 53 | **0 / 3 / 31 / 53** |
| `init-prelude` gaps | 9650 | **9650** |
| `init-prelude` escapes | 1484 | **1484** |
| `init-prelude` `derived` | 87494 | **87494** |
| `init-prelude` declarations with a stored typing | 12 of 1645 | **12 of 1645** |
| `init-prelude` user time (min of 5) | 16.00 s | **11.87 s** |
| `init-prelude` peak RSS | 198 MB | **175 MB** |
| arena | 152 / 0 / 2 | 152 / 0 / 2 |

**Every gap, escape and derivation count in the corpus is byte-identical, per
file.** Instrumentation may not change what the checker decides, and it did not.

**The runtime fell 24% and the peak RSS 11%.** The typing store used to cost 36%
of `init-prelude` (11.79 s → 16.03 s), and that was read as the price of
storing. It was not: it was 1645 typing searches, 1633 of which failed, looking
for what inference had just worked out. `TgBackend::store_declar_typing` no
longer searches at all — it reads the certificate `check_declar` hands it — and
the same 12 typings come out, all 12 now `carried out of inference, not searched
for`. Carrying a certificate through every inference node is *cheaper* than the
search it replaces, memo included.

### What inference can and cannot justify

`init-prelude`, per node of the inference recursion:

| typings carried | count |
| --- | ---: |
| derived outright | 4375 |
| conditional on the ambient locals | 16345 |
| no evidence | 24022 |

| by rule | count | | no evidence | count |
| --- | ---: | --- | --- | ---: |
| `ty_local` | 13248 | | `ty_const` | 12768 |
| `ty_sort` | 4019 | | `ty_pi` | 5801 |
| `ty_app` | 2390 | | `ty_premise_missing` | 4503 |
| `ty_lam` | 997 | | `ty_lit` | 553 |
| `ty_const` | 49 | | `ty_proj` | 260 |
| `ty_conv` | 17 | | `ty_infer_only` | 92 |
| `ty_let` | 0 | | `ty_app` | 45 |

`ty_not_the_claim` — a rule that built a derivation of something other than the
judgement claimed — is **0**, and should stay there: it is a bug report, not a
missing rule.

The two blocking rows are the ones already known. `ty_const` is 12768 uses of a
constant whose typing was never stored, and 1633 of 1645 are not stored because
`ty_pi` has no rule: `⟦Π A B⟧ ∈ ⟦Sort (imax u v)⟧` is the `Sort`-encoding
obstruction, and no premise inference could supply would give it. `ty_lam`,
`ty_let`, `ty_conv`, `ty_local` and `ty_sort` never decline at all — every time
they were asked with premises in hand they answered. So the ceiling on the
typing store is exactly where `INDUCTIVES.md` says it is, and it is now visible
one rule at a time instead of as a single failed search.

### The ledger of what is still discarded

`assert_def_eq` returns its certificate now instead of asserting one exists, and
the places that still drop one are named and counted rather than found by
grepping: `certificates obtained and discarded` in the `--features stepcount`
report, split into the quotient shape checks, the inductive telescope checks,
the side conditions inside definitional-equality rules whose own conclusion is
an `admit`, and the binder domains checked to be types.

`init-prelude`: 33587 binder domains, 4804 def-eq side conditions, 950
inductive telescope checks, 6 quotient shape checks. The 4804 are the ones with
a route: each sits under an `admit` (`def_eq_proj`, `def_eq_local`,
`proof_irrel`, `unit_like`, `eta_struct`, `string_lit`, `nat_eq`) that has no
rule to compose them into yet. The other two groups establish a *different*
judgement — that a binder domain is a type, that a declaration has the expected
shape — and there is nothing for a membership derivation to do with them.

## The universe tower reaches `interp_sort`, 2026-07-31

`⟦Sort 0⟧` was `syms.sort0`, an opaque nullary symbol. It is now
`derived::tower`'s `U₀ = {0,1}`; `⟦Sort 1⟧` is `U(ω)`, and `⟦Sort (l+1)⟧` is
`U(⟦Sort l⟧)` for `l ≥ 1`. `Tower::new` replaces the prelude's hand-assembled
`Apply`/`Space`/product/function-space chain outright.

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 210 | **210** |
| tutorial escapes | 68 | **68** |
| tutorial `derived (real kernel Thm)` | 7928 | **7928** |
| tutorial files at 0 gaps / 0 escapes | 68 / 79 | **68 / 79** |
| `073` / `075` / `076` / `077` gaps | 0 / 3 / 31 / 53 | **0 / 3 / 31 / 53** |
| `init-prelude` gaps | 9650 | **9650** |
| `init-prelude` escapes | 1484 | **1484** |
| `init-prelude` `derived` | 87494 | **87494** |
| `init-prelude` user time (min of 5) | 11.91 s | **12.25 s** |
| `init-prelude` peak RSS | 175 MB | **177 MB** |
| arena | 152 / 0 / 2 | **152 / 0 / 2** |

**Every gap and escape count in the corpus is byte-identical, per file.** The
tower costs 0.3 s and 2 MB on `init-prelude` — it is built once per thread and
`Tower::new` is not the expensive part of `derived`.

### Two theorems the tower had to supply, and why

Seeding level 1 at `ω` rather than at `U₀` is mandatory (`U(U₀) ⊆ V_ω`, whose
every member is finite, while `⟦N⟧` is not), and it costs exactly two instances
of `⊢ ∀x. x ∈ U(x)` that used to hold definitionally:

* `⟦Prop⟧ ∈ ⟦Type 0⟧` — `U₀ ∈ U(ω)`, not `x ∈ U(x)`. `Tower::at(1).u0_mem`.
  Fires **17** times on `init-prelude`.
* `⟦Prop → Prop⟧ ∈ ⟦Type 0⟧` — `fs(U₀,U₀) ∈ U(ω)`, not `fs(a,a) ∈ U(a)`.
  `Tower::fs_u0_in_u1`. Without it `006`, `007` and `015` each gained a gap and
  an escape and the inductive-free fragment fell to 24/27; with it the corpus is
  identical to baseline. It was measured as a regression first and fixed second.

### `⟦False⟧` is tied to a backend term

`ind_const` gained an arm: a `Prop`-valued inductive with no constructors is
`⟦False⟧ := ∅`, introduced by `ind_abbrev` with `⊢ ⟦False⟧ = ∅`, and
`derived::anchor::uninhabited_along` carries `⊢ ∀x. ¬(x ∈ ∅)` across it. The
result is checked by instantiation to be about the symbol just introduced, and
reported: `init-prelude` derives the anchor **169** times.

`⊢ ⟦False⟧ ∈ ⟦Prop⟧` is registered alongside it — available only because
`⟦Prop⟧` is now `U₀` — and typing obligations discharged on `init-prelude` go
2022 → 2074, with opaque-constant misses 905 → 853.

## `ty_pi` is 92% `Π` and 8% `∀`, 2026-07-31

`infer_pi` now splits its gap by whether `imax u v` simplified to zero, because
the thesis (§6.2) gives `∀` and `Π` two *different* interpretations — a
conditional singleton `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧] ⊆ {•}` for `Prop`, a dependent
function space for `Type` — and `interp_pi` implements only the second, for every
`Expr::Pi` unconditionally. For a `Prop`-valued `Π` the obligation is therefore
not merely unproved but **unprovable as stated**: the target is `U₀ = {0,1}` and
a `dprod` is not a subset of `{•}`.

| | `init-prelude` | tutorial |
| --- | ---: | ---: |
| `ty_pi` (into `Type`) | 5269 | 523 |
| `ty_pi_prop` (into `Prop`) | 449 | 137 |
| `ty_pi` derived | 83 | 10 |

**The `Prop` clause is 8% of the wall, not the wall.** That is the correction
this measurement exists to make: fixing `⟦∀⟧` is necessary for soundness of the
rule and will not by itself move `ty_pi`. The other 92% want
`dprod_in_universe`'s n-ary port and cumulativity, and they are unaffected by the
Prop/Type question.

`ty_pi` is now a rule that declines rather than a gap with no rule: it asks
`domain_premise`, which is closed and non-recursive, and gets 83. It deliberately
does *not* run the `has_type` search — interpreting a `Π` builds a Replacement
derivation per skeleton, and 5801 searches is the shape of mistake that cost
`store_declar_typing` 36% of a run for 12 hits. Cost of the rule as written: 0.1 s
on `init-prelude`, no change to gaps, escapes or `ty_const`.

## `⟦∀⟧` and `⟦Π⟧` are two clauses, and there is a third case — 2026-07-31

`interp_pi` built the dependent-product clause for every `Expr::Pi`. It now
dispatches on the body's sort, three ways.

```text
⟦∀x : α. β⟧ = {•} ∩ ⋂_{x∈⟦α⟧} ⟦β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — β : Prop
⟦Π x : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧                              — β : Type
                                        neither, at a universe parameter
```

The `Prop` clause is one `define_abbrev` for the fibre `b(h⃗,x) := ⟦β⟧` and one
`derived::prop::conditional_singleton` over `∀x. (x ∈ A → • ∈ b(h⃗,x))`, keyed
per body skeleton exactly as the `Π` clause's fibre is.

### The interpretation-side number, which is the point

| | `init-prelude` | tutorial |
| --- | ---: | ---: |
| `ty_pi_prop` sites, before | 449, none discharged | 137, none discharged |
| `ty_pi_prop` sites, after | **446 derived**, 3 not shown | **136 derived**, 1 not shown |

Those 449 and 137 terms were previously interpreted as something they are not,
and their typing obligation was unprovable as stated. It is now
`Tower::cond_in_u0` at the skeleton — a theorem, not a search — derived lazily
once per skeleton and instantiated thereafter.

### The third case, and how large it is

`Π A B : Sort (imax u v)` with `v` a universe parameter does not simplify
(`level.rs`: `IMax` reduces only when the left side is `0`/`1` or the right is
`Zero`/`Succ`; `Max` of two parameters likewise). So the sort is `0` when the
parameter is instantiated at `0` and `max(u,v)` otherwise, and the two clauses
name **different sets** — a subset of `{•}` against a function space. Choosing
either is choosing wrongly on some instantiation, so the backend chooses
neither: an axiom-free symbol of the right shape, and `TyGap::PiUndet`.

| | `init-prelude` | tutorial |
| --- | ---: | ---: |
| `ty_pi` (definitely into a `Type`) | 2903 | 187 |
| `ty_pi_prop` (definitely into `Prop`) | 449 | 137 |
| **`ty_pi_undet` (neither)** | **2366** | **336** |
| share of all `Π` typing sites | **41%** | **51%** |
| …expressions: a universe parameter | 9005 | 1830 |
| …expressions: the sort walk gave up | 429 | 1 |

The last two rows separate "undecidable here" from "this approximation could not
tell", and the ratio is the finding: **95% of the undetermined population on
`init-prelude` and 99.9% on the tutorials is a genuine universe parameter.** A
better syntactic walk closes almost none of it. What closes it is running the
backend per level-instantiation instead of once at the declaration's own
parameters — a design change, not a lemma.

### Corpus movement

| | before | after |
| --- | ---: | ---: |
| tutorial gaps / escapes | 210 / 68 | 218 / 69 |
| tutorial files at zero gaps / zero escapes | 68 / 79 | 65 / 77 |
| inductive-free fragment at zero and zero | 27 of 27 | 25 of 27 |
| `073` / `075` / `076` / `077` gaps | 0 / 3 / 31 / 53 | 0 / 3 / 31 / 53 |
| `init-prelude` gaps / escapes | 9650 / 1484 | 10346 / 1259 |
| `init-prelude` runtime / peak RSS | 12.6 s / 178 MB | 11.9 s / 193 MB |
| arena | 152 / 0 / 2 | 152 / 0 / 2 |

The `Prop` clause alone is corpus-neutral: with it and `∀`-extensionality in
place and the undetermined case still taking the `Type` branch, every number
above is *identical* to the baseline — 210/68, 9650/1484, 87494 derived, the
same gap ledger row for row — while 446 + 136 typing obligations moved from
"no evidence" to "derived". That is the measurement the task asked for: the
interpretation changed on 586 terms and the corpus did not move at all.

The movement is entirely the third case. `init-prelude` gains 748 gaps of
"two Πs of undetermined sort over differently shaped bodies" — two axiom-free
symbols, nothing to relate them — and loses 225 escapes, because obligations
that used to be acquired against a function space are no longer acquired at all.
`028_peano2` and `029_peano3` leave the fragment for exactly this reason:
`two.{u} : Π (α : Sort u). (α → α) → α → α` is a proposition when `u := 0`, so
its type is not a function space, and the one and two *escaped* assumptions left
in those files are obligations `lam_in_funspace_n` used to discharge at a domain
the backend no longer claims is one. Every definitional-equality step in both is
still derived outright.

### `⟦·⟧` stays a function, and that is tested

Three classifications means three ways to disagree, and a disagreement between
two `def_eq`-related `Π`s makes the interpretation not a function of the Lean
term. `derive_pi_cong` names each mixed pairing as its own gap, so the
population is visible: **0 over the tutorials, 2 on `init-prelude`** (one
four-argument application whose head's type does not reach a `Sort` by delta
alone, and one redex the walk declines). `tg_tutorial.rs` holds the tutorial
figure at zero and is mutation-verified three ways — dropping either exit of
`interp_pi` makes it fire 4 times, and weakening the classifier to `syn_type`
alone makes it fire 30.

### `∀`-extensionality

Two `∀`s over differently shaped bodies are built over different conditional
singletons and congruence relates nothing. `cond_ext_n` is the
`dprod_ext_n` of this clause:
`⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x∈A → b(p⃗,x) = b'(q⃗,x))) → chi(p⃗,A) = chi'(q⃗,A')))`,
by `φ ↔ φ'` and Extensionality. Without it the tutorial corpus is at 254 gaps
and the fragment at 4; with it, at the baseline. It is written against
`derived::hyp`, which is documented as superseded — nothing else depends on it,
it is derived once per skeleton pair and memoised, and the alternative was a
hundred lines of `hyp_syl`/`a1i` plumbing.

## The level-instantiation pre-pass, 2026-07-31

`checker/src/instantiations.rs`. The previous section ends by saying the third
case "is not a gap a lemma closes… what closes it is running the backend per
level-instantiation". This is that change, measured.

A worklist fixpoint over the export file computes, before any checking starts,
every `(declaration, ground universe levels)` pair the run will need. Demand
propagates: a required pair `(d, σ)` requires `(c, σ')` for every constant `c`
that `d`'s type, value or recursor rules mention, at the level arguments
*evaluated under σ*. A ground level is always `succ^n(zero)`, so an
instantiation is just a vector of naturals. Each declaration is then checked once
per instantiation, with `TcCtx::sigma` telling the backend which one it is under;
`infer`, `whnf` and `def_eq` never read it.

### The fixpoint

| | tutorials (91 files) | `init-prelude` |
| --- | ---: | ---: |
| declarations | 514 | 2059 |
| …monomorphic (the seed) | — | 610 |
| pairs after propagating from the seed | 291, in **7 rounds** | 1116, in **7 rounds** |
| declarations nothing demands (checked at the default) | 224 | 1007 |
| **pairs in total** | **557**, in 13 rounds | **2652**, in 13 rounds |

Seven rounds is the number that says a single sweep would not do: a pair found
late feeds a pair found early. The totals are 1.08× and 1.29× the declaration
count, so this is not a combinatorial explosion — most declarations are used at
one instantiation or none.

`Inductive` and `Quot` are checked once, at their own parameters, and take no σ:
neither goes through `with_tc_and_declar`, an inductive's check runs over a whole
mutual block and mints a fresh eliminator universe that is by construction not
one of the declaration's. Their *uses* are unaffected — a use of `Foo.{0}` is
interpreted under the using declaration's σ.

### The third case collapses

| | before | after |
| --- | ---: | ---: |
| `ty_pi_undet` typing sites, `init-prelude` | 2366 | **12** |
| `ty_pi_undet` typing sites, tutorials | 336 | **36** |
| undetermined-by-parameter expressions, `init-prelude` | 9005 | 2796 |
| undetermined-by-parameter expressions, tutorials | 1830 | 1394 |
| store lookups answered, `init-prelude` | 111 | 813 |
| stored typings that are level-polymorphic | 5 | 13 |

What is left of the expression population is dominated by the passes that take
no σ — every pass that checks an inductive block.

### Corpus movement

| | before | after |
| --- | ---: | ---: |
| tutorial gaps / escapes | 218 / 69 | **210 / 68** |
| tutorial files at zero gaps / zero escapes | 65 / 77 | **68 / 79** |
| inductive-free fragment at zero and zero | 25 of 27 | **27 of 27** |
| `073` / `075` / `076` / `077` gaps | 0 / 3 / 31 / 53 | 0 / 3 / 31 / 53 |
| `028` / `029` gaps and escapes | 1/1 and 2/2 | **0/0 and 0/0** |
| `init-prelude` gaps / escapes | 10346 / 1259 | 11315 / 1579 |
| `init-prelude` derived (real kernel `Thm`) | 86573 | 100613 |
| `init-prelude` runtime / peak RSS | 12.08 s / 193 MB | 13.75 s / 204 MB |
| arena | 152 / 0 / 2 | 152 / 0 / 2 |

Only four tutorial files moved: `028_peano2` (1 → 0), `029_peano3` (2 → 0),
`081_PSigma.snd` (3 → 0) and `074_prodRecEqns` (16 → 14 gaps, 2 → 4 escapes).
The other 87 are unchanged to the gap and to the escape.

**`init-prelude`'s gap total goes up, and that is not a coverage regression — it
is a change of denominator.** The gap ledger counts *sites*, and there are now
2652 declaration-checks where there were 2059. Per check the count falls from
5.02 to 4.27. The rows that moved say the same thing: "pi congruence: two Πs of
undetermined sort over differently shaped bodies" 748 → 60 and "the body
certificate is not about the binder bodies" 261 → 19, against `trans over an
admitted premise` 4798 → 5759, which is the cascade over 1.29× as many sites.

**Cost: 1.14× wall-clock, 1.16× kernel derivations, 1.06× peak RSS**, against
the design study's estimate of 1.11× and 1.14×. Instantiations run sequentially,
so memory stays flat. Verified inert: with the schedule computed but ignored,
`init-prelude` reproduces the baseline exactly — 10346 gaps, 1259 escapes, 86573
derived — which is what says σ is the only lever this change pulls.

### The pre-pass is complete, and that is counted rather than argued

The prediction is syntactic — it walks the expression DAG for `Const` nodes — and
the checker mints instantiations that are in no expression: literal expansion
builds `List.nil.{0} Char`, `Char.ofNat` and `String.ofList`, and `inductive.rs`
mints temporary declarations for nested inductives. The first is handled by a
fixed seed list of the `NameCache` names at all-zeros, which is a *claim*.

So the backend audits it. Every constant instantiation it interprets is
evaluated under σ and looked up in the schedule:

| | tutorials | `init-prelude` |
| --- | ---: | ---: |
| interpreted at a scheduled instantiation | 935 | 29772 |
| **at an instantiation the pre-pass did NOT predict** | **0** | **0** |
| at levels still mentioning a parameter (no σ in force) | 191 | 325 |
| of a temporary declaration, which has no stable name | 0 | 2 |

The third row is the inductive passes, which take no σ by design; the fourth is
the nested-inductive temporaries, whose names live in a per-declaration arena.
The second row is the finding, and it is zero.
`the_pre_pass_predicts_every_instantiation_the_backend_interprets` holds it
there, and asserts the audit ran at all — a zero miss row proves nothing if
nothing was audited.

### The default instantiation is a choice, and it was measured both ways

1007 of `init-prelude`'s 2059 declarations are demanded by nothing. They are
still checked, at `instantiations::DEFAULT_LEVEL` in every parameter.

| tutorials | gaps | escapes | files at zero gaps |
| --- | ---: | ---: | ---: |
| `DEFAULT_LEVEL = 0` (`Prop`) | 213 | 71 | 66 |
| `DEFAULT_LEVEL = 1` (`Type 0`) | **210** | **68** | **68** |

The two files that decide it are the Church numerals, which use `two.{u}` at no
level at all and are therefore checked entirely at the default. At `u := 0`
their `Π` is a proposition and one obligation escapes in each; at `u := 1` it is
a function space and both derive end to end. Since 27/27 on the fragment is the
acceptance criterion for this design, the default is 1. On `init-prelude` the
ordering goes the other way (11030 gaps at 0 against 11315 at 1) — worth
recording, and not what the choice turns on, since those are counts over
different numbers of sites.

## `⟦T⟧ ∈ ⟦Type 0⟧` wired into the checker — 2026-08-01

`derived::cumul` proved `⊢ W(1+1,B,U(1+1)) ∈ U(ω)` and nothing consumed it.
`checker/src/tg.rs` now does, through a table `has_type` consults beside
`ind_mems`: the constructor rule puts an *element* in its inductive type, this
one puts the *type* in a sort. Four entries — `N`, `Bool`, `Unit`, `Empty` —
each derived once per thread at closed terms, carried onto the declaration's own
abbreviation by one Leibniz step, and **registered only if its conclusion is
literally the membership being claimed**.

Two things in `derived/` had to move, both plumbing:
`cumul::Chain::over` (new file `cumul/ambient.rs`) builds the chain over a
caller-supplied `Tower`, `Wtype` and `Bound` instead of minting its own — which
needed `Clone` on `Sums`, `Wtype`, `Bound`, `Space`, `Peano` and `OmegaCore`,
where a clone copies the *same* symbols; and `cumul::NatMem::over` is
`NatUniverse::new` minus the `Nat` it used to build, because `Cases::new` mints a
fresh `rec₊` and a second `Nat` would be a different `W`. `cumul/enums.rs` is the
same argument where the fibres are empty — no case analysis, seed `S := A`, and
`Bool`'s `(1+1) ∈ U₁` taken off `NatMem` rather than proved twice.

### `N` alone, measured on the clean tree

| | before | after |
| --- | ---: | ---: |
| tutorial gaps (91 files) | 210 | **210** |
| tutorial escapes | 68 | **68** |
| tutorial files at zero gaps / zero escapes | 68 / 79 | 68 / 79 |
| tutorial `derived (real kernel Thm)` | 8014 | 8014 |
| inductive-free fragment (27 files) | 0 gaps, 0 escapes | unchanged |
| `073` / `075` / `076` / `077` | 0/0, 3/3, 31/17, 53/31 | unchanged |
| `init-prelude` gaps | 11315 | **11309** |
| `init-prelude` escapes | 1579 | **1573** |
| `init-prelude` `derived` | 100613 | 100613 |
| `init-prelude` runtime | 13.73 s | 13.69 s |
| `init-prelude` peak RSS | 203.7 MB | 205.1 MB |
| arena | 152/0/2 | 152/0/2 |
| `cargo test -p kernel` / `-p derived` | 50 / 507 | 50 / **509** |

**The corpus barely moves, and the interesting number is why.** On
`init-prelude` the clause fires **559 times** off **135** distinct
`(subject, target)` pairs, and closes **six** gaps. The discharges are real and
visible in the ledger:

| `init-prelude` | before | after |
| --- | ---: | ---: |
| by `IndTy` | — | **559** |
| not shown: an opaque constant | 930 | **433** |
| not shown: a lambda whose typing rule did not apply | 6590 | **6322** |
| by `Lam: a graph is a function into any codomain` | 1414 | **1687** |
| by `Local` | 7104 | 7111 |
| by `CtorApp` | 310 | 314 |
| by `App: a function's values lie in its codomain` | 529 | 531 |
| by `App: the dependent product's sections` | 0 | 3 |
| by `Const: along the defining equation` | 13 | 16 |

So 268 of the `ty_lam` miss population — "a lambda whose typing rule did not
apply" — converted, and 497 of the opaque-constant misses (`Nat : Type 0`, the
single commonest head in that bucket) went away. What did **not** move is the
`ty_*` ledger: `by ty_lam` 1381, `no evidence: ty_const` 14420 and every other
row are byte-identical before and after, on `init-prelude` and on the tutorial
corpus alike. The tutorial corpus does not move by a single gap, escape or
derivation, and the counter says why rather than leaving it a guess: the clause
is consulted **zero** times there. `075`'s `N` obligations are stated at
`⟦Sort u⟧` for a *parameter* `u`, which interprets to the opaque `sort` symbol,
not to `U(ω)`; `076`'s are about `List`.

This is the recorded rule again — *a conditional certificate closes a gap
exactly when no admitted step sits below it* — seen from the other side: 559
obligations stopped being assumed, and six of them were the last thing standing
between a certificate and its discharge.

### The enumerations, A/B on one base

`Bool`, `Unit` and `Empty` were added on top and measured against the same
build with the table restricted, and against the same build with the clause
disabled outright:

| | clause off | `N` only | `N` + enumerations |
| --- | ---: | ---: | ---: |
| `init-prelude` gaps | 10970 | 10964 | **10828** |
| `init-prelude` escapes | 1514 | 1508 | **1470** |
| `init-prelude` `derived` | 96158 | 96158 | 96215 |
| distinct pairs matched / derived | 0 | 131 / 131 | **194 / 194** |
| `IndTy` clause uses | 0 | 543 | **626** |
| tutorial gaps / escapes | 250 / 68 | 250 / 68 | 250 / 68 |
| arena | — | — | 152/0/2 |

**The enumerations are worth more than `N` was**: a further 136 gaps and 38
escapes against `N`'s six and six, for a derivation that is strictly shorter.
The reason is the one `cumul/enums.rs` records — with empty fibres the seed can
be the tag set itself and `Fin(A,∅)` needs no case analysis — plus the fact that
`Bool` heads far more *lambda domains* in `init-prelude` than it does bare
typing obligations, which is exactly the population `⟦T⟧ ∈ ⟦Sort u⟧` was
supposed to unblock.

**Caveat on this table, stated because it matters.** Its three columns are one
build tree and are comparable with each other; their absolute values are **not**
comparable with the table above it, because at the time it was taken a
concurrent session had unrelated in-flight edits to `checker/src/tg.rs` (they are
what put the fragment at 39 gaps and `073` at 18 in that tree, in all three
columns alike). The `N`-only delta measured there, −6 gaps and −6 escapes, is
the same as the one measured on the clean tree, which is the evidence that the
base does not distort the deltas.

### `List` is not done, and the reason is arithmetic rather than difficulty

The closing note of `cumul` said `wlist` needs "the same three obligations" with
`α ∈ U(c)` becoming a hypothesis, and that is still true. What the measurement
adds is the size of the prize. Three things have to be built: closure of `U₁`
under `+` (`A,B ∈ U₁ → A+B ∈ U₁`, from `sum_def` as in `NatMem`), a conditional
`Fin(1+α, fam(α))` whose right branch quantifies over `a ∈ α` rather than over
the point, and a checker clause that carries `⟦α⟧ ∈ ⟦Type 0⟧` as an antecedent
and moves the membership across `app(⟦List⟧,α) = lt(α)`. It is available at
level 0 only: `⟦Type u⟧` for a parameter `u` is the opaque `sort` symbol and the
chain's `ω ∈ U(d)` antecedent cannot be met there.

Against that, what it buys, from the ledger already on record: `076`'s escape
table has exactly **one** assumption blocked on `⟦List α⟧ ∈ ⟦Sort 1⟧`, and
`init-prelude`'s `List.nil`/`List.cons` misses (91 + 99) are `CtorApp`-shaped,
not `⟦List α⟧ ∈ ⟦Type 0⟧`-shaped. The certificate would also be **conditional**,
and this file's own rule says a conditional certificate converts only where
nothing below it admits. So it is an afternoon for something between one and a
few dozen gaps, and it is the wrong next afternoon.

### The tree as it stands with everything in it

A concurrent session landed unrelated work in `checker/src/tg.rs` while this was
being measured, and it has since settled. The combined tree, with `IndTy` on:

| | value |
| --- | ---: |
| tutorial gaps / escapes (91 files) | 197 / 68 |
| tutorial files at zero gaps / zero escapes | 70 / 79 |
| tutorial `derived (real kernel Thm)` | 8027 |
| inductive-free fragment (27 files) | **0 gaps, 0 escapes** |
| `073` / `075` / `076` / `077` | 0/0, 3/3, 31/17, 53/31 |
| `init-prelude` gaps / escapes | 11125 / 1536 |
| `init-prelude` `derived` | 100718 |
| `init-prelude` runtime / peak RSS | 12.90 s / 239.0 MB |
| `IndTy`: distinct pairs matched / derived, clause uses | 199 / 199, **643** |
| arena | **152 / 0 / 2** |
| `cargo test -p kernel` / `-p derived` | 50 / 509 |

The tutorial improvement from 210 to 197 and the two extra zero-gap files are
the concurrent session's, not this change's: `IndTy` is consulted **zero** times
over the whole tutorial corpus, before and after.

## §6.2's proof split for `λ` and application, 2026-08-01

The project owner: *"Clearly both default levels should work, else we have a
bug. Let's sharpen it: when a constant is unused and has level parameters, treat
it like it's used at level 0 **and** level 1, and make that work."*

The two defaults did not agree because **only one of §6.2's three splits was
implemented**. The thesis gives two clauses each for three constructors:

```text
⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]      ⟦Πx : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧
⟦λx : α. e⟧ = •                          ⟦Λx : α. e⟧ = (x ∈ ⟦α⟧ ↦ ⟦e⟧)
⟦e₁ e₂⟧     = •                          ⟦e₁ · e₂⟧   = ⟦e₁⟧(⟦e₂⟧)
```

`interp_pi` split the first. `interp_lambda` built a graph unconditionally and
application built `app(f,x)` unconditionally, so at `u := 0` a Church numeral's
`Π` correctly became a conditional singleton while its `λ` still built a graph —
and `lam_in_funspace_n`, the *`Type`*-clause lambda rule, had nothing to apply
to. That was the escaping obligation in `028_peano2` and `029_peano3`.

### What was built

`TgBackend::term_clause` is the classifier for the two new splits. It is **not**
a second classifier: `sort(e) = lvl(type of e)`, so every case either settles the
question from the level algebra (`Sort` and `Π` are never proofs; a `λ` is one
exactly when its body is) or hands the term's *type* to the existing
`body_clause`. `Undet` takes the `Type` clause here, deliberately and unlike
`Π`: the `Type` clause builds a fresh graph symbol, which identifies nothing,
while the `Prop` clause collapses the term to `•`, which identifies it with
every other proof — so guessing `Type` costs gaps and guessing `Prop` would be
the one direction that could make the checker accept what it should not.

Four rules came with it:

* **`cond_intro` as the `Prop` lambda's typing rule** — `⊢ φ → • ∈ [φ]`,
  generalised over an `∀` skeleton's parameters, taking the same pointwise
  premise `lam_in_dprod_n` takes. `TgBackend::prop_lam_close`.
* **`point_of_proof`** — `⊢ H → ⟦e⟧ = •` for a proof that took *neither* split
  clause. §6.2 sends a variable to `πᵢ(γ)` and it is `•` only because `γ` ranges
  over `⟦Γ⟧`; this kernel has no `γ`, so the equation is conditional on the
  ambient assumptions, and that is what comes back. Two premises — `⟦e⟧ ∈ ⟦α⟧`
  and `⟦α⟧ ∈ U₀`, both from `has_type` — plus `Tower::u0_subsingleton`. A
  defined constant standing for a proof takes a shorter route: its abbreviation
  already unfolds to `•`.
* **`proof_eq`**, which is `point_of_proof` on both sides of an admitted or
  reduced step. Proof irrelevance stops being an admission: `099_proofIrrelevance`
  goes 5 → 0.
* **`syn_type_proj`** — a delta-only transcription of `infer_proj`, because
  without a projection's type `PSigma.fst α β s` is a proof at `u := 0` while
  the projection it delta-reduces to is undetermined.

### The three default sets, measured

`DEFAULT_LEVELS` is now a list. Each entry is closed over exactly as a demanded
pair is.

| | tutorial gaps | escapes | zero-gap | zero-escape | `derived` | `init-prelude` gaps / escapes | pairs | ip runtime |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline (no split, `[1]`) | 210 | 68 | 68 | 79 | 8014 | 11171 / 1534 | 2652 | 13.8 s |
| split, `[0]` | **186** | 68 | 70 | 79 | 8041 | 10785 / 1471 | 2414 | 12.8 s |
| split, `[1]` | **197** | 68 | 70 | 79 | 8027 | 11114 / 1536 | 2652 | 13.2 s |
| split, `[0, 1]` | **222** | 77 | 69 | 79 | 10063 | 16422 / 2288 | 3861 | 21.4 s |

The baseline row is this same tree with `term_clause` forced to `Clause::Type`,
which reproduces the recorded 210 / 68 / 68 / 79 exactly.

**The inductive-free fragment is 27/27 at zero gaps and zero escapes under all
three**, which is the acceptance test. `073_boolRecEqns` is 0/0 under all three
as well; `075`/`076`/`077` are 3/3, 31/17, 53/31 unchanged.

The `[0, 1]` row is *more checking*, not worse checking. A defaulted declaration
is checked once per entry, so a file's one gap is reported twice —
`113_reduceCtorParamRefl.mk` and `114` go 1 → 2 for exactly that reason and
their budgets moved with them. The honest cost is the pair count: **2652 → 3861,
+46%**, for 13.2 s → 21.4 s and 239 MB → 250 MB on `init-prelude`.

### Do `[0]` and `[1]` agree? No — and precisely where

Three files differ, and none of the three differences is a classification
disagreement:

| file | `[0]` | `[1]` | why |
| --- | ---: | ---: | --- |
| `074_prodRecEqns` | 4 | 14 | at `u := 0` the recursor's motive and minors are proofs and ten cascade gaps collapse to `•` |
| `124_quotLiftReduction` | 0 | 9 | the same, for `Quot.lift` |
| `081_PSigma.snd` | **8** | 0 | named below |

`081_PSigma.snd` is the one that is a defect rather than a difference in the
amount of work. `PSigma.{u,v} : Sort (max 1 u v)`, so at `u := v := 0` the
structure is **not** a proof but its first field is: `PSigma.fst α β s : α` with
`α : Prop`. The redex `(λ α β s. s.0) α β s` is therefore a proof and interprets
to `•`, while its reduct `s.0` is a proof that took neither split clause and
interprets to a projection term. `point_of_proof` cannot bridge them because its
first premise is `⟦s.0⟧ ∈ ⟦α⟧` — **a typing obligation about a projection, for
which this backend has no rule at all** (`ty_proj`, 16 gaps corpus-wide before
this change). So the beta step reports a gap and five congruence steps cascade
over it. Closing it means a projection typing rule, not another classifier case.

### What this unblocks, and what it does not

| | baseline | `[0, 1]` |
| --- | ---: | ---: |
| `by ty_lam` (inference typed a `λ`) | 82 | **104** |
| `no evidence: ty_lam` | 4 | **0** |
| "a lambda whose typing rule did not apply" | 131 | 129 |
| typing obligations asked / discharged | 720 / 138 | 754 / **162** |
| `λ` interpreted as `•` | — | 88 |
| application interpreted as `•` | — | 962 |

**The `Prop` lambda's typing rule fires 17 times, all of them through
inference's `ty_lam`, and zero times through `has_type`** — no domain obligation
in the tutorial corpus is about a proof `λ`. The "lambda whose typing rule did
not apply" population barely moves (131 → 129), so the reading that the split
would unblock *that* population is wrong: those are `Type`-clause lambdas whose
target is neither a function space nor a dependent product, and they are
untouched by anything here. On `init-prelude` the split fires much harder — 378
proof lambdas and 3074 proof applications — and `by ty_lam` is 2162.

### `⟦·⟧` is still a function

`the_two_clauses_of_the_interpretation_never_disagree` now asserts four
disagreement rows at zero (the two `Π` ones and `lam congruence: one proof λ and
one Λ`, `congruence: one proof application and one`) plus three population
ratchets. Each new branch was **deleted in turn** and the test confirmed to
fire: `interp_lambda`'s `Prop` branch (λ 88 → 0), `interp_app`'s (application
962 → 0), `ty_lam`'s `Prop` route (λ 88 → 68, `by ty_lam` 104 → 87), and
`term_clause`'s redex case (222 → 282 gaps, fragment off 27/27).

One negative worth recording: the two *new* disagreement rows stay at zero even
under the mutation that produces a genuine disagreement, because `delta` and
`beta` meet the two terms before any congruence does and report it as their own
gap. The rows are still asserted — the case they name is one nothing else would
report — but on this corpus the population ratchets are what catch a regression.

Arena is **152 / 0 / 2** with both the plain and the `--features tg` binary. The
escape ledger balances exactly at every default set: 77 escaped certificates, 77
counted in the gap row.

## The general inductive translation, wired after the recognisers — 2026-08-01

Task #26 **step one** (`WIRING-DESIGN.md` §8): `derived::inductive`'s general
carrier and recursor are reachable from the checker, **after** `enum_arity`,
`nat_shape` and `list_shape`, which stay exactly where they were. No cutover —
that is step two and it is blocked on `derived::cumul` accepting `finord(m)`
fibres (`cumul.rs:252` demands `B(a) ∈ ω` on the nose, and `finord(1) ≠ 1`).

### The corpus does not move

| | `[0]` | `[1]` | `[0, 1]` |
| --- | ---: | ---: | ---: |
| tutorial gaps, before | 179 | 197 | 215 |
| tutorial gaps, after | **179** | **197** | **215** |
| tutorial escapes, before / after | 69 / **69** | 68 / **68** | 78 / **78** |
| files at zero gaps | 70 | 70 | 69 |
| `derived (real kernel Thm)` | 8049 | 8027 | 10071 |

Arena **152 / 0 / 2**, unchanged. The inductive-free fragment is 27/27 at 0/0
under all three, unchanged. `before` is the same binary with
`TgBackend::ind_const`'s general arm returning `None` and
`interpreted_shape`'s general gate returning `false`, so the two rows are the
same tree and the same `derived/`.

**All 91 tutorial reports are byte-identical between the two**, save the new
ledger rows — checked line by line, not by totals. That covers the four files
whose stillness is the scope assertion (`042`, `068`, `077`, `116`) and the
three the recogniser order exists to protect (`073`, `075`, `076`).

### What the path did on the tutorials

| | |
| --- | ---: |
| declarations translated | 15 |
| constructors given a term and a typing rule | 32 |
| recursors given a general nest | 0 |
| cached specs declined: `βⱼ` bodies not canonical | 0 |
| declined: indices | 106 |
| declined: sort-ambiguous or `Prop` (class S/P) | 45 |
| declined: parameters (Lean-facing nest not wired) | 35 |
| declined: constructors not yet in the environment | 14 |
| declined (recursor): `T`-policy 2/3, `HYP` not dischargeable | 9 |
| declined: function-typed recursive argument | 2 |

The two function-typed declines are `116`'s `RTree.node : (Bool → RTree) → RTree`
and the indices declines are `RBTree`'s, which is what the acceptance assertion
asks for: those four files are declined *by reason*, not merely unreached.

The shape the path covers that no recogniser could, in this corpus, is the
**multi-field single-constructor structure** in `035_twoBool`/`061_twoBoolRec`
— `Σy₀:β₀. Σy₁:β₁(y₀). 1` over a one-summand tag set. `enum_arity` refuses any
constructor with a field and any third constructor; `nat_shape` and
`list_shape` match one declaration each, field by field.

### `init-prelude`: 43 gaps close, and the run takes twice as long

| | before | after |
| --- | ---: | ---: |
| gaps | 16384 | **16341** |
| escaped certificates | 2298 | **2261** |
| unpredicted instantiations | 0 | **0** |
| wall clock | 21.0 s | **41.9 s** |
| declarations translated | — | 3803 |
| constructors given a term and a typing rule | — | 3662 |
| cached specs declined: `βⱼ` bodies not canonical | — | **3783** |

**The cost is one number and it names its own cause.** A `GenInd` is cached per
*thread* while a `TgBackend` is per *declaration*, so `WIRING-DESIGN.md` §3.4
moves `ind_syms` to `Shared` to make the `βⱼ` bodies stable across backends —
and then guards every hit by re-walking the declaration and re-interpreting the
field types. On the tutorials the guard never misses. On `init-prelude` it
misses 3783 times out of 3803, i.e. **essentially always across backends**, so
`Inductive::build` runs once per (declaration, inductive) pair rather than once
per inductive, and that is the 21 extra seconds.

The design expected the `ind_syms` move to be sufficient. It is not, and the
binding constraint is one row above it in the same report: **`shared symbols
declined: body not canonical` is 7922** on `init-prelude` — the *constant*
interpretation already fails to agree across declarations that often, so a
field type mentioning any such constant interprets to a different symbol in the
next backend and the whole cached carrier is about the wrong sets. Rebuilding is
then the correct answer, not a missed optimisation.

So the lever for the general path's cost is **canonical constant
interpretation**, not anything in the wiring. Until that moves, the guard is
doing exactly its job — refusing a package of true theorems about somebody
else's symbols — and the price is visible rather than silent. Nothing here is
trusted from the cache: a stale entry costs a rebuild, never a wrong theorem.

## The general ι rule, at `T`-policy 2 — 2026-08-01

Task #26 step one **rung 3, completed**: `RECURSOR-DESIGN.md` §8 rung 5, the
wiring of `derived::inductive::GenRecursor`'s packed-W ι rules into `⟦T.rec⟧`.
Rung 3 as first landed wired `T`-policy 1 only and, as its own record says,
built **zero** general nests on both corpora. This is the policy-2 half.

Both sides of every A/B below are built from **one frozen snapshot** of
`derived/`, `kernel/` and `mini/`, taken before any of this work, with only
`checker/` differing — five agents were committing to `derived/` during the
session and it did not compile for part of it. Runs are interleaved
base/variant and the wall clocks are medians of three.

### The tutorials do not move, at any instantiation set

| | `[0]` | `[1]` | `[0, 1]` |
| --- | ---: | ---: | ---: |
| gaps, before → after | 179 → **179** | 197 → **197** | 215 → **215** |
| escapes, before → after | 69 → **69** | 68 → **68** | 78 → **78** |
| files at zero gaps | 70 | 70 | 69 |
| `derived (real kernel Thm)` | 8049 | 8027 | 10071 |

Identical in every column, and per file: the 91-row gap/escape/derived table is
byte-identical between the two binaries. Arena **152 / 0 / 2** with both. The
inductive-free fragment is 27/27 at 0/0 under all three.

The *reports* differ on 60 of the 91, in the general path's own ledger rows
only. `073`/`075`/`076` and `042`/`068`/`077`/`116` are byte-identical **save**
those rows, with one substantive difference worth naming: `042`, `068`, `075`
and `077` now build **one general recursor nest** each where they previously
recorded a `T`-policy decline, and each reports one more
`a universe parameter: neither clause` query as a result — a nest walks the
recursor's type and interprets every binder. No gap, escape or derivation count
moves on any of the four, and `RBTree` and `RTree` are still declined by reason
(`indices`, `function-typed recursive argument`).

### `init-prelude`: 769 gaps close, at no cost in time

| | before | after |
| --- | ---: | ---: |
| gaps | 16341 | **15572** |
| escaped certificates | 2261 | **2145** |
| recursors given a general nest | 0 | **74** |
| **ι sites the general rule computed** | 0 | **80** |
| constructors given a term and a typing rule | 3662 | **1911** |
| `shared inductive symbols declined: body not canonical` | 12310 | **8875** |
| declined (recursor): `T`-policy 2/3 | 567 | **393** |
| unpredicted instantiations | 0 | **0** |
| wall clock (median of 3, interleaved) | 28.58 s | 28.69 s |

The 80 sites are all of `Lean.Name` (`anonymous` 11, `str` 13, `num` 13),
`Lean.SourceInfo` (`none` 9, `original` 11, `synthetic` 11) and
`Lean.Macro.Exception` (`unsupportedSyntax` 6, `error` 6) — three declarations
no recogniser can reach, with an interleaved mask (`Name.str`/`num` are
`Rec, Plain`), a four-plain-field constructor (`SourceInfo.original`) and live
recursive calls. `Lean.Name.str` is the target `WIRING-DESIGN.md` §8 names.

### Where the 769 come from — three measured steps

| | gaps | escapes | nests | ι sites |
| --- | ---: | ---: | ---: | ---: |
| before | 16341 | 2261 | 0 | 0 |
| + per-backend `⟦cᵢ⟧` memo and the `Rc::ptr_eq` recursor guard | **16077** | **2075** | 0 | 0 |
| + `T`-policy 2, ι at nullary constructors only | **15923** | **2095** | 74 | 26 |
| + ι at constructors with fields (rung 5 proper) | **15572** | **2145** | 74 | 80 |

**Two thirds of the gap movement is the ι rule and one third is
canonicality** — and the canonicality third had to come first, because without
it 54 of the 80 sites were about the wrong symbols. Two caches were the
problem, neither of them the one `WIRING-DESIGN.md` §3.4 identified:

* **The constructor nest was built more than once per backend.**
  `gen_ctor_nest` mints a fresh graph symbol per level, so a second build gives
  a second `⟦cᵢ⟧` with the same meaning; `ind_abbrev` then sees a changed body,
  re-mints, and the second nest's `CtorRule` and ι bridge overwrite the first's
  while `interp`'s `ExprPtr` cache still hands out the first. The ι rule is
  then stated about a set the redex does not mention. A memo on
  `(name, levels)` closes it — and the same memo is why
  `constructors given a term and a typing rule` halves for unchanged coverage.
* **The per-thread `GenRecursor` outlived the carrier it was built over.**
  `gen_inds`' guard rebuilds the carrier when the `βⱼ` bodies did not survive
  (3783 times of 3803); the recursor cached beside it was not re-checked.
  `Rc::ptr_eq` on the `GenInd` is the whole test, it misses **70** of 74 times,
  and rebuilding costs nothing measurable at this scale.

The escape column is the recorded `076` pattern at prelude scale: closing gaps
beneath a conditional certificate lets it escape. Net it is −116, and the two
halves pull opposite ways — canonicality −186, the ι rule +70.

### The dependent-motive census — zero

`RECURSOR-DESIGN.md` §9.2 and `WIRING-DESIGN.md` §12.8, open since the designs
were written, asked whether any in-scope ι site has a genuinely dependent
Type-level motive, since those are a permanent escape by design. Over the 80
sites: **none**. Every one discharged `HYP` from the minor's curried
`fs`-membership at the beta-reduced Lean type, which is what §5.1 predicts for
"every recursor used to define a plain function". The dedicated reason string
`iota: HYP undischargeable — dependent motive` exists, is reachable, and is
emitted **zero** times on either corpus.

What *is* the large population is `T`-policy 3 — a declaration with no nullary
constructor, so no canonical closed point for the motive: 393 recursor
declines, led by `Lean.ParserDescr` with 169 ι sites. Widening the gate to
admit it was measured: 150 more `GenRecursor::build`s and **zero** gaps closed,
because `t_policy` then returns `None` inside `rec_nest` instead. The decline
is the right answer and the gate stays.

### What still declines the ι rule on `init-prelude`

`iota: this recursor has no curried interpretation` is 884 before and **804**
after; the residue is policy 3 (`ParserDescr`, `String`, the `UInt*`s),
`Decidable`/`Option`/`Except` and the rest of the parameterised declarations
(`Decline::Params`, 267 — the Lean-facing type-former nest for `np > 0` is
still unwired), the indexed families, and `is_k`. No general-path ι site fails
for any *other* reason: after this change the report has no
`gap: iota: …` row attributable to `fire_general` at all.

## The type former's parameter nest — `np > 0` wired, 2026-08-01

`INDEXED-DESIGN.md` §8's **C0**, the named prerequisite of the indexed families
work and independent of it: `Decline::Params` — "the Lean-facing nest for
`np > 0` is not wired", the second-largest decline row on `init-prelude` at
**267** — is lifted. Measured **on its own**, before any indexed work, which is
what §8 asks. Nothing about indices is wired; `RBTree` still declines.

What landed: the type former is a nest of `np` lambda graphs with `ind(p⃗)` at
the bottom (`tg.rs::gen_ty_nest`, kept as a `GenTyNest` with its conditional
beta chain `H_p → app-spine(⟦T⟧,p⃗) = ind(p⃗)`); every constructor's nest and
`CtorRule` runs over `np + k + m` levels with the parameters first; the general
ι rule takes `p⃗` from `ta[..np]`; and `gen_rec_bottom` no longer restricts to
monomorphic declarations. `np = 0` is the same code with an empty nest — not a
separate branch — which is why the parameterless results below are identical
rather than merely equal in total.

Both binaries are built from **one frozen snapshot** of `derived/`, `kernel/`
and `mini/`, taken before any of this work, back to back, before either runs;
only `checker/` differs. Prelude runs are interleaved base/variant, medians of
three. The four published baselines reproduce exactly on this machine, which is
the precondition for reporting a delta at all.

### The tutorials do not move, at any instantiation set

| | `[0]` | `[1]` | `[0, 1]` |
| --- | ---: | ---: | ---: |
| gaps, before → after | 179 → **179** | 197 → **197** | 215 → **215** |
| escapes, before → after | 69 → **69** | 68 → **68** | 78 → **78** |
| files at zero gaps | 70 | 70 | 69 |
| `derived (real kernel Thm)` | 8049 | 8027 | 10071 |

The 91-row gap/escape/derived table is **byte-identical** between the two
binaries at all three settings — including `042`, `068` and `077`, which is the
scope assertion (they are indexed and nothing here touches indices), and the
inductive-free fragment, which is 27/27 at 0/0 throughout. Arena **152 / 0 / 2**.

The *reports* differ on 47 of the 91, in the general path's ledger rows only.
The substantive one is `074_prodRecEqns`: **8 typing obligations move from
`raw fallback, about: an application of an opaque constant` to `by CtorApp: an
applied constructor, by its conditional rule`**, because `Prod.mk` now has a
`CtorRule`. That is C0's whole observable on the tutorials, and it is pinned by
`a_parameterised_declaration_reaches_the_general_path`. Fourteen tutorials now
translate a declaration where none did (`Prod`, `PProd`, `PSigma`, the
two-field structures); **none** builds a general recursor nest, where nine used
to — see the second finding below, because those nine were a bug.

One row moves the other way and it is worth naming: the corpus's
`a universe parameter: neither clause` total goes **4962 → 4953**. Nine of those
queries were the binders of the nine spurious nests; the `np > 0` type former
adds one of its own. Answers, not queries: nothing moved.

### `init-prelude`: 80 gaps close, and the run costs half again as long

| | before | after |
| --- | ---: | ---: |
| gaps | 15572 | **15492** |
| escaped certificates | 2145 | **2153** |
| declarations translated | 3803 | **8376** |
| constructors given a term and a typing rule | 1911 | **10204** |
| recursors given a general nest | 74 | **77** |
| **ι sites the general rule computed** | 80 | **92** |
| `by CtorApp` typing discharges | 1420 | **2584** |
| `by IndTy` (`⟦T⟧ ∈ ⟦Type 0⟧`) | 702 | **1093** |
| `gap: iota: this recursor has no curried interpretation` | 804 | **792** |
| `…declined: parameters` | 267 | **0** |
| `…declined (recursor): T-policy 2/3` | 393 | **1104** |
| unpredicted instantiations | 0 | **0** |
| wall clock (median of 3, interleaved) | 28.92 s | **40.82 s** |

**The gain is small and the cost is not.** Twelve more ι sites and 1164 more
`CtorApp` discharges buy 80 gaps; the price is +41% wall clock, and it names its
own cause in the same report: `shared inductive symbols declined: body not
canonical` goes **8875 → 32157** and `declarations translated` 3803 → 8376. Every
parameterised declaration a use site touches now gets an `Inductive::build` per
backend, and the per-thread cache's guard refuses essentially every hit for the
reason already recorded above — the *constant* interpretation is not canonical
across declarations, so a field type's `βⱼ` body is a different term in the next
backend. The lever is unchanged and is not in this wiring.

Whether that trade is worth keeping is a judgement, and the argument for keeping
it is not the 80 gaps: it is that `np > 0` is a hard prerequisite for indexed
families (`RBTree` has `np = 1`), for the `Decidable`/`Option`/`Except` family
of ι sites, and for step two's cutover. As a gap-closing change on its own it
would not pay.

### Three things the plan did not say

1. **A declaration a recogniser owns must never fall through to the general
   path**, and saying so takes two guards, not one. `ind_const_recognised`
   returns `None` both for "not my shape" and for "my shape, but I cannot serve
   this use", and `ind_const` treated the second as the first; with `np > 0`
   unwired that was unreachable, and with it wired `076_listRecReduction` built
   a **second** `List` carrier and a second `List.rec` nest beside the
   hand-written ones — the seam `WIRING-DESIGN.md` §8 forbids. Nothing unsound
   followed (every theorem is guarded, and the file's 31 gaps did not move), but
   `ind_abbrev` re-minted `⟦List⟧`, which is the recorded failure mode that cost
   54 ι sites last time.

   A shape-only `recognised_ind` gate in `ind_const` and `gen_rec_bottom` was
   the obvious fix and it **did not work**, for a reason worth recording: while
   an inductive is being *checked*, the checker installs a temporary
   `InductiveData` with `is_recursive: false` and only asserts the export's real
   value afterwards (`inductive.rs:115`, `:30`). For the length of `List`'s own
   declaration check, `list_shape` therefore refuses `List`; so does the gate
   built on it, and the general path serves the declaration anyway. So the gate
   asks the two recursive shape tests **without** that clause — which loses
   nothing, because in both of them the recursion is already implied by the
   field checks (`succ`'s field, `cons`'s tail) and the flag was a restatement.

   Both halves were **found by reading one ledger row** —
   `shared inductive symbols declined: body not canonical`, 0 → 1 on `076` — not
   by a test, and the second half only because the first did not move it.

   Closing the window has a consequence worth stating on its own, because it
   retracts a previously recorded result: **the nine general recursor nests the
   tutorials used to build were all inside it.** `042`, `068`, `075`, `077`,
   `041`, `067`, `090`, `097` and `098` each built one, and every one was for
   `N` or `Color` — declarations `nat_shape`/`enum_arity` own — during those
   declarations' own checks. The previous rung's record ("`042`, `068`, `075`
   and `077` now build one general recursor nest each where they previously
   recorded a `T`-policy decline") is therefore **the bug, not the feature**;
   the nests were about a carrier nothing else in those files used, which is
   why no gap, escape or derivation count moved when they appeared and none
   moves now that they are gone. `T`-policy 2's reachability is real, and it is
   `init-prelude`'s **5** general nests and 92 ι sites that show it. Eleventh
   and twelfth claim-matching bugs, both found by reading.

   **The nest half of that number read 77 when this entry was written, and it
   was counting rebuilds.** There were always five distinct nests; each was
   rebuilt roughly once per declaration that reached it, first because the `βⱼ`
   guard missed (`Shared::gen_ctor_nests`, 75 → 5) and then because
   `Shared::rec_nests` refused to store a `RecBottom::General` at all (the
   remaining rebuilds, now shared). The ι site count — which is what the
   reachability claim is about — is 92 throughout and did not move at either
   step.
2. **`rec.levelParams` is `[motive, ind…]`** — the motive's level comes
   **first**, so a declaration's own instantiation is the *tail* of its
   recursor's **[decoded**: `042`'s `RBTree.rec` is `[35, 5]` against `RBTree`'s
   `[5]`; `076`'s `List.rec` is `[9, 2]` against `List`'s `[2]`**]**.
   `WIRING-DESIGN.md` §6.1 left this as "an export-format convention this has
   not been checked against" and declined every polymorphic declaration rather
   than guess. It is checked now.
3. **A `βⱼ` body is unusable at a use site once `np > 0`.** It is stated over
   the *walk's* parameter variables and the kernel has no `Term::subst`, so the
   body at actual parameters must be read off `βⱼ`'s **instantiated** defining
   equation. Getting this wrong is not silent: the first cut produced 12 sites
   reporting `iota: a field type's definition is not about this domain` and
   exactly 0 net gaps, which is what sent me looking. The same applies to the
   raw carrier, so `fire_general` uses `recursor::carrier_at` at `p⃗` and checks
   it against `ind.ty_ax` instead of using `ind.wty`.

### A census that came free: there is no class-(T) indexed family on `init-prelude`

`gen_scope` now tests the eliminator trichotomy **before** `num_indices`, so
`…declined: indices` counts only the class-(T) families — the ones
`INDEXED-DESIGN.md` §5.2's `good` subset would serve. On `init-prelude` that row
goes **14 → 0**, and `…declined: sort-ambiguous or Prop (class S/P)` goes
13 → 27: every indexed declaration the path reaches there is `Prop`-valued.
`RBTree` in `042`/`068`/`077` remains the corpus's **only** witness for §5.2's
indexed branch, exactly as the design's tutorial census said — now checked at
prelude scale too, where the demand is entirely for §5.3 and the truncation
clause.

## Canonical constant interpretation: `⟦c⟧` was re-minted per declaration — 2026-08-01

Task #33. `checker/` only. Both binaries built from **one frozen snapshot** of
`derived/`/`kernel/`/`mini/` at `4f9dfa4` (a clean tree; other agents' in-flight
edits to `derived/` and `mini/` are *not* in either side), runs interleaved,
medians of three, `init-prelude` at `DEFAULT_LEVELS = [0, 1]`.

| | before | after |
|---|---|---|
| `shared symbols declined: body not canonical` | 24122 | **14443** |
| `shared inductive symbols declined: body not canonical` | 28148 | **15495** |
| `init-prelude` wall clock (median of 3) | 40.84 s | **35.89 s** |
| `init-prelude` gaps / escapes | 15492 / 2153 | 15492 / 2153 |
| tutorial `[0]` / `[1]` / `[0,1]` | 179/69, 197/68, 215/78 | unchanged, **per file** |
| arena | 152 / 0 / 2 | 152 / 0 / 2 |
| inductive-free fragment | 27/27 at 0/0 | 27/27 at 0/0 |

### What made a body non-canonical, and why the tutorials escape it

The guard was not stale and it was not weakened. The diagnostic that localised
this was a temporary instrumented build counting, per `ind_abbrev` **call
site**, whether the per-thread store hit or drifted, and counting per
`(name, levels)` key how many distinct bodies `const_abbrev` ever saw.

The distribution is the finding, and it is extremely lopsided. Of the 868
constants with a value that `init-prelude` interprets, **576 keep exactly one
interpretation** for the whole run. 233 ever drift. Twenty of them acquire
**more than five hundred distinct bodies each** — `Nat.below` 1077,
`Nat.casesOn` 1056, `Nat.brecOn` 1050, `OfNat.ofNat` 1047, `LT.lt` 1046,
`Nat.add` 979, `Nat.mul`/`Nat.pow`/`HPow.hPow`/`NatPow.pow` ~951 — against 2059
declarations. That is not drift; that is **a fresh symbol roughly every second
declaration**, which is what the owner's reading predicted.

Three minting sites had no per-thread store at all, and everything else was
downstream of them by cascade — a definition mentioning a re-minted constant is
itself re-minted, and a *constructor field type* mentioning one makes the `βⱼ`
guard on the next declaration miss, which rebuilds that declaration's carrier
and re-mints `⟦T⟧` too.

1. **The type former nest** (`gen_ty_nest`). `⟦T⟧` for every declaration the
   general path translates is the head of a nest of `np` lambda graphs, each a
   fresh `define_abbrev`. Per backend, so `⟦T⟧` was a different symbol in every
   declaration: **15840** of the 28148 inductive re-mints, and the first
   canonicity failure in the run, before any constant drifts.
2. **The general constructor nest**, built over the type former's variables:
   **9780** more.
3. **The recursor nest** (`rec_nest`). `rec_nests` was a per-backend `HashMap`
   and the nest is rebuilt with fresh symbols each time: **2528**. This is what
   the `Nat` arithmetic family above is downstream of — every one of those
   definitions mentions `Nat.rec`.

The tutorials escape it because they are single-declaration files: a constant
interpreted once cannot disagree with itself. `Drift` is **0** on all 91 of
them, and that zero is not the guard being satisfied — it is the store never
being consulted twice. `IndDrift` is nonzero on exactly four
(`074`, `081`, `093`, `105`), which is the same defect at the only scale the
tutorials can show it.

### The fix: store the symbol, and check the store rather than rebuild

Three per-thread stores, all on the `const_syms` key discipline
(`(NamePtr::raw, interpreted levels)`, export-file names only) and all
hint-not-trust:

* `Shared::rec_nests`, guarded by `reuse_rec_nest`: same bottom by
  `Rc::ptr_eq`, same variables, same domains, right arities, and the stored
  `head_def` about the term *this* walk builds. Reuse rate is total —
  `shared nests declined` is **0** for recursor nests over the whole run.
* `Shared::gen_ty_nests`, guarded by `Rc::ptr_eq` on the `GenInd`. That test is
  exact rather than approximate: a `GenTyNest` is built entirely out of its
  `GenInd`'s `param_vars`, `param_doms` and `ind.ty_of(p⃗)`, so the same `Rc`
  means the cached nest's theorems are about precisely the terms this backend
  would have built. A reusing backend still has to re-register `⟦T⟧` through
  `mk` (for its own `parts`) and in `abbrev_defs` — `adopt_ty_nest`.
* `Shared::lit_syms`, one symbol per literal **value**.

The constructor nests (item 2) are not stored yet; they fall out partly anyway,
because they are built over the now-shared type former's variables.

### A measured negative: literals are not the cause

Sharing literal symbols by value was measured **twice**, before and after the
nest work, and moved `body not canonical` by **22 out of 21231** — 0.1%. The
first diagnostic had flagged them because the `literal` bit co-occurred with
4510 drifts, which is a good illustration of why a co-occurring reason is not a
cause. The change is kept because it is correct and free, not because it paid.

A second negative: making `Shared::gen_ty_nests` track the *current* translation
(`insert`) rather than the first (`or_insert`) changes **nothing at all** —
24122/28148 identical to the digit. The ratchet is the `βⱼ` guard, not the
store: `gen_ind` mints a new `Rc` on every rebuild, so the stored translation is
always one step behind whatever the next backend computes.

### What is left, and it is now the whole of it

`shared nests declined: not over this walk/translation` is **5630**, and
`cached specs declined: βⱼ bodies not canonical` is **5630**. The two are the
same number because they are the same event: whenever `gen_ind`'s `βⱼ` guard
misses, the translation is rebuilt, its `Rc` changes, and the type former nest
above it is stale by construction. Closing that guard is the remaining lever and
it is worth the rest of the regression — 14443 constant re-mints and 15495
inductive ones are all downstream of those 5630.

## The general recursor nest, shared — the inductive re-mint row closes, 2026-08-01

Fourth and last of the minting sites the previous three entries chased.
`Shared::rec_nests` stored a nest only when its bottom was one of the three
hand-written W-recursors; `RecBottom::General` was excluded, on the recorded
ground that it carries a `GenTyNest`, which was per backend. **That ground had
lapsed one commit earlier**: `Shared::gen_ty_nests` (42a0dee) made the type
former per thread, and `adopt_ty_nest` hands a later backend the *same* `Rc` it
stored — so `same_bottom` can ask `Rc::ptr_eq` of it exactly as it asks it of
`Shared::nat_rec` and friends. Verified before building on it: `GenRec` (carrier,
`GenRecursor`, `RecCore`) is per thread behind `Shared::gen_recs`, `Machine` is
per thread, and nothing else in a general bottom is per backend.

Measured on `init-prelude`, median of three (five for the wall clock),
interleaved, both binaries built back to back from one frozen snapshot of
`derived/`/`kernel/`/`mini/` at 311ead8:

| row | before | after |
|---|---|---|
| `shared inductive symbols declined: body not canonical` | 85 | **0** |
| `shared symbols declined: body not canonical` | 173 | **15** |
| `shared nests declined: not over this walk/translation` | 0 | 0 |
| `shared constructor nests declined: not over this translation` | 0 | 0 |
| `cached specs declined: βⱼ bodies not canonical` | 0 | 0 |
| `cached recursors declined: not over this carrier` | 0 | 0 |
| wall clock | 13.87 s | 13.76 s |

Everything else in the report is **byte-identical**: 15492 gaps, 2153 escapes, 5
general nests, 92 ι sites, 283 declarations translated, 10200 constructors.
Tutorials byte-identical per file over all 91 exports, 215/78; arena 152/0/2;
inductive-free fragment 27/27 at 0/0.

**The wall clock did not move, and that is the expected shape.** The previous
pass removed 5630 guard misses and with them thousands of rebuilt translations;
this one removes 85 nest rebuilds. The row it closes is a canonicity row, not a
cost row — 85 recursor symbols with two denotations each — and −0.8% is what 85
rebuilds are worth. Reported rather than rounded up.

### The residue is 15, and it is two causes, neither of them a store

Instrumented build, first-occurrence order, then the two bodies at the first
drift of each constant:

| constant | events | cause |
|---|---|---|
| `String.utf8EncodeChar` | 6 | `Expr::Let` |
| `List.utf8Encode` | 6 | downstream — its value mentions the first |
| `outParam` | 3 | a non-ground universe level |

The first two are one lever. `String.utf8EncodeChar`'s stored and fresh bodies
are `f4593(f2609)` and `f4607(f2609)` — the same argument under a *different*
lambda-graph symbol, so `Shared::lam_infos` missed, so its skeleton differed.
The two skeletons are `f4591(v)` and `f4605(v)`, and neither `f4591` nor `f4605`
is in *any* per-thread table — not `lam_by_lam`, `pi_by_dprod`, `prop_by_chi`,
`undet_syms`, `opaque_syms`, `lit_syms` or `idx_syms`. They are **let**
abbreviations: `TgBackend::interp`'s `Expr::Let` arm calls `define_abbrev` with
no store at all, one fresh symbol per occurrence per backend. Confirmed
directly — the run mints nine let symbols and `4591` and `4605` are two of them.
That is the fifth minting site, and it is the same shape of fix a fifth time.

`outParam` is different and should not be folded in with them. Its stored and
fresh bodies have the **same** head symbol (`f263`, the lambda graph) and differ
in the argument: `⟦Sort u⟧` reads `imax(0, max(u, succ …))` in one backend and
`max(max(succ …, 0), u)` in the other. It is interpreted at an instantiation
still mentioning a universe parameter — the report's
`…at levels still mentioning a parameter (no σ in force)` row, 327 — and the
level *term* built for it is not canonical across backends. `const_key` keys on
the interpreted levels, so the key matches while the body does not. A lever of
its own, in `interp_levels`/`level_canon` rather than in any symbol store.

## Projection reduction is a rule, and the σ layer is why it took two tries — 2026-08-01

*Threading stage 0's follow-on, task #29. `checker/` only. Measured on frozen
snapshots of `HEAD` and `HEAD` + the change, built separately, `init-prelude`
interleaved, medians of three; `derived/` and `kernel/` pinned at `4f9dfa4` for
both, because the live `derived/` did not compile during this session (a
concurrent agent mid-edit: `hyp_eq_trans` had grown an `&mut Env` parameter and
`le_prop_rec.rs` had not followed).*

`whnf` recorded a projection contraction as `Rule::Admitted(Admit::ProjRed)`, so
the only thing that ever saw the step was `Certifier::admit`. While `admit` had
an optimistic fall-through it rediscovered for itself that both endpoints were
proofs and passed 20 steps a run off as derived. Deleting the fall-through made
those 20 visible as `gap: proj_reduce` 630 → 650. They are answered now, by a
rule: `Certifier::proj_red`, `Rule::ProjRed`, and `TypeChecker::proj_red_step`
inferring both endpoints and handing over Carneiro's Theorem 6.7 premises.

| row | before | after |
|---|---|---|
| `gap: proj_reduce` | 650 | **630** |
| TOTAL gaps | 15455 | **15423** |
| escapes | 2102 | **2138** |
| derived (real kernel `Thm`) | 149614 | 149682 |
| `…threaded, asked by projection reduction` | — | **11** |
| `…asked by a reduction rule's proof shortcut` | 34 | 34 |
| `…asked by a proof λ's body clause` | 41 | 41 |
| `…asked by the admit fall-through` | 0 | 0 |
| wall clock | 13.76 s | 13.73 s |

Tutorials **byte-identical per file** over all 91 exports (213 gaps, 78 at zero
escapes, 69 at zero gaps); arena 152 matched / 0 mismatched / 2 declined. Only
one tutorial export has a `proj_reduce` gap at all — `093_projRed`, at 1 — so
the whole of this measurement is on `init-prelude`.

**Which mechanism the numbers show: evidence arriving, not callers
disappearing.** The three `has_type` search rows do not move by one. What moved
is that a new asker exists and is fed. The 20 close by three routes, and the
split is worth keeping: `already •` 35 → 53, `answered from the memo` 2 → 22,
and 11 fresh threaded derivations.

### The first implementation closed nothing, and that is the finding

Handing `proof_witness` to the new rule scored **zero**: `gap: proj_reduce`
stayed at 650 and the report was indistinguishable from no change. Probed with
temporary distinct admission reason strings — the cheapest instrument in this
codebase, since `note_admit` tallies by string, so a hypothesis becomes a row —
all 650 came back "neither endpoint is a proof". Re-probed against the deleted
fall-through's own predicate: **20 of the 650 have `term_clause == Prop` on both
sides and the old route rescued exactly those 20**, and the checker's `is_proof`
says no at all 650.

Both are right. They answer different questions:

* A declaration is checked **once, at its own universe parameters**. σ is applied
  in exactly one place, `TcCtx::under_sigma`, and everything the backend reads
  goes through it; nothing the checker reads does.
* The 20 are `Nat.brecOn.go` and `Lean.ParserDescr.brecOn.go` shapes, whose
  endpoints have type `motive t` with `motive : Π t. Sort u`. At the parameters
  `Sort u` is not `Sort 0`, so `sort_zero_leg` declines and inference says "not
  a proof" — correctly, because a step licensed only at `u := 0` would let the
  checker accept a declaration that is ill-typed at `u := 1`.
* `⟦Sort u⟧` is built through `interp_level`, which substitutes σ first, so at
  the σ in force it *is* `U₀` — and `⟦α⟧ ∈ U₀` is exactly Theorem 6.7's premise.

So `TypeChecker::PropAt` writes the split down: `Params` gates a checker verdict,
`Sigma` produces evidence for the backend. `proof_irrel_eq` keeps `Params`, so
what the checker accepts is unchanged (arena 152/0/2 confirms). `proj_red_step`
uses `Sigma`, and the 20 close.

**This is a place `mini`'s answer does not transfer.** `MINI-DESIGN.md` §0.1
argues there is only one classifier, because two that could disagree would make
`⟦·⟧` fail to be a function. That is right in mini, which checks one
instantiation and whose `is_prop` is exact — the two questions coincide there and
the rule is free. In nanoda they are different questions and the rule is not
free: asking the *checker's* one to produce the *model's* evidence closes
nothing at all.

### Escapes rise by 36, and it is the same trade run backwards

The derivations are conditional on the ambient locals, exactly as the rescue's
were — stage 0 recorded 2138 → 2102 when the rescue went, and this is 2102 →
2138 coming back. Bought by 32 gaps (20 primary + 12 cascade). Both rows are
gaps; the difference is that the equation now has a derivation attached and the
assumption it rests on is named.

## The declaration-typing ledger, read as a completeness measure — 2026-08-01

*Same session and same snapshots. Instrumentation only: gaps, escapes, tutorials
and arena are unchanged by everything in this section.*

`Shared::declar_typings` is not a cache. The claim this project exists to
establish is that a Lean declaration `c : T` becomes a target-theory theorem
`⊢ ⟦c⟧ ∈ ⟦T⟧`, and that store is where such a theorem lives — so a declaration
with no entry is a declaration that **has not been translated**. Read that way,
`init-prelude`'s headline is not its 15423 definitional-equality gaps, which
count steps inside checking, but this:

| row | `init-prelude` |
|---|---:|
| (declaration, σ) pairs with a value | 2891 |
| …**stored as `⊢ ⟦c⟧ ∈ ⟦T⟧`** | **19** |
| …no certificate at all (`Gap`) | 2674 |
| …derived and discarded as conditional | 198 |
| …temporary, no store can key it (`NoKey`) | 0 |
| …derived, refused by the store's own checks | 0 |
| uses answered from the store | 1308 |
| uses with no entry | 31256 |
| …against a typing that was derived and discarded | 1161 |

`mini`'s counterpart is **121 of 223**. Nanoda's is **19 of 2891**, 0.66 %. A run
with zero definitional-equality gaps and this store would still have proved
nothing about any declaration, and that has not been said plainly before.

### `Gap` and `Conditional` were one number, and they call for opposite work

The residue used to be arithmetic — `Seen` minus `FromInfer` minus `Conditional`
— which conflated three things. Split, and the identity
`Seen = NoKey + Gap + Conditional + FromInfer` is now asserted by a test:

* **`Gap`, 2674 (92.5 %).** Inference produced no certificate, because the
  declaration's own check gapped. Genuine absence and cascade; interpretation
  scope, not threading debt. **This is the story**, and it is where the answer to
  "how much of the prelude is translated" is.
* **`Conditional`, 198 (6.8 %).** Inference *established* the typing and it was
  thrown away. A certificate computed and discarded is threading debt by
  definition, and the stage-0 report's "interpretation-scope residue, not
  threading debt" was right about the `Gap` half and wrong about this one.

### Storing conditional typings: `Sealed` does not forbid it, and it would not pay

Two different things are spelled `hyps`. `TgTyping::Derived { hyps }` is a list
of **formula-level antecedents** on `⊢ conj(hyps) → ⟦val⟧ ∈ ⟦ty⟧`; `Sealed`
tests `Thm::hyps()`, the **kernel sequent**. Measured over all 198: the kernel
sequent is empty in every case, so `Sealed::new` would accept every one. The
persistence discipline is not the obstacle, and the suspicion that the two were
conflated is confirmed.

What the antecedents actually are decides it, and they are not ambient locals'
typings. Measured over the same 198: every antecedent is a **hoisted guarded
family**, `∀x. (x ∈ ⟦A⟧ → …)`, 196 pairs carrying exactly one and 2 carrying
two. They are already generalised past the binder that produced them, so no
binder is left to discharge them — and none is discharged: the
`discharge_families` ledger reads 1150 offered and **0** derived under the
guard, corpus-wide.

So storing them would move 1161 `ty_const` store misses into the escape ledger,
one undischargeable family per use, and both rows count as gaps. The lever is
not widening the store; it is discharging the family — which is the census's
"strongest single empirical argument for the target design", still measured at
zero.

## The schedule already knew what the store needed — 2026-08-04

Zone B, mini's inductive interpretation, was called from one place: the
checker's constant clause, **on a store miss**. Nothing else called it, and it
never read the schedule that the level-instantiation pre-pass computes and that
`mini/src/convert.rs` hands to the ledger.

The pre-pass covers inductives. `checker/src/instantiations.rs`'s worklist
fixpoint has explicit arms for `Declar::Inductive`, `Declar::Constructor` and
`Declar::Recursor`; the inductive arm walks its **constructors' types** and
attributes their edges to the inductive's node, with a comment saying it does so
because *this* checker interprets them whenever the inductive is interpreted.
`convert::load` writes a schedule entry for every declaration where
`insts.for_name` is `Some` — before it matches on the declaration kind, so
inductives are in it. `MINI-DESIGN.md` §9 nevertheless said zone B interprets
"on demand", citing `WIRING-DESIGN.md` §7.1's *inductives excluded from σ
scheduling*. That exclusion is **nanoda's** decision; mini inherited the shape
and not the premise.

### The question, and why a counter could not answer it

Filling eagerly is only sound if the fixpoint's `(name, σ)` set contains every
key a lookup can arrive at. A key it does not predict leaves a miss, and a miss
that sinks no declaration prints no row — so the instrument was to fill
eagerly, make the miss path `panic!`, and run the corpus.

Two rounds, because the first instrument was wrong in an instructive way.
Registering the *whole* schedule up front and panicking on anything outside it
reported three misses — `Bool` at `071`/`072`, `True` at `090` — which turned
out to be **`zoneb::elim_audit` running before the declaration walk**. The audit
infers constructor field types, so it reads the store; running it first made it
a second, unscheduled entry point into zone B. It runs after the pass now.

### The result

Registering each key **as `fill_declaration` attempts it** — so the panic
catches a lookup that arrives *before* its fill as well as one the schedule
never predicted — and running all 91 `good/tutorial` exports:

| | misses |
| --- | ---: |
| all 91 exports, eager fill on | **0** |
| all 91 exports, eager fill deleted | 61 exports |
| all 91 exports, recursor dropped from the fill | 25 exports |
| all 91 exports, constructors dropped from the fill | 0 exports |

Zero. Not "zero unpredicted" — zero *misses*: after the eager fill, the store
lookup in `Checker::const_evidence` and `Checker::delta_evidence` never has
anything to do. Widened to the nine designed fixtures and the bad corpus, the
entire residual miss population is two keys, and both are builds that were
attempted and declined: `Squash` (`ind-spec(Squash: class (P) above Prop)`) and
`VoidProp.rec` (`recursor(VoidProp: class (S) eliminator: no constructors)`).

The constructor row is a guard that fails nothing, and it is kept with that
recorded: `ensure(T, σ)` stores every `⟦T.ctorᵢ.{σ}⟧` alongside `⟦T.{σ}⟧`, and
a constructor's schedule entry cannot outrun the declaration's because its type
mentions the declaration at the declaration's own parameters.

### What eager filling found that no run had asked

`mini/tests/dump.rs` asserted that **zero** declarations in the tutorial corpus
decline, and concluded "every declaration the tutorial corpus contains now
translates". The measurement was real and the conclusion did not follow: a
declaration nothing used at a ground level was never asked. Three declined —
`reduceCtorParam`, `reduceCtorParamRefl`, `reduceCtorParamRefl2`, all as
`ind-spec(…: nested occurrence)`.

Nothing else moved: `pairs`/`constEv`/`typeEv` 218, `unsealed` 0, conversion
`gapped` 0, 89 accepted / 2 declined, no exit 4, no export blocks.

### The nested occurrence was not one, and one of the three now translates

Those three exports write a constructor's recursive field as
`constType (T α) (T α)`, an application of a definition that *reduces* to
`T α`. `zoneb`'s spec walk tested the recursive-argument shape syntactically,
deliberately ahead of any interpretation: `Checker::infer_type` on a
self-mentioning type reaches `const_evidence` → `miss_reason` →
`zoneb::ensure` on the declaration being built, whose carrier does not exist
yet. **Measured** by replacing the decline with `c.infer_type(ty)`: the three
exports do not terminate.

The reduct is taken with the **acceptance-only** `Checker::whnf`, which is
handed no `⟦e⟧`; `delta_evidence` and `beta_evidence` both return on a `None`
endpoint before they consult the store, so nothing on the reduction path is
interpreted and `ensure` is not re-entered. Same measurement with `c.whnf(ty)`
in place of the decline: all three print their reduct and finish.
`zoneb::rec_field` now peels and reduces alternately — `Checker::whnf` at every
level, each binder opened as it goes — which is `open_forall_eager_push`'s own
loop, i.e. the one zone A's `check_ctor_param` and `build_rec_type` already run.
`113`'s field needs the reduction *under* the binder and would survive an
outermost-only whnf, because a `Π` is already in weak head normal form.

Reading the spine through a reduction makes two Lean-facing bridges necessary
that the syntactic walk never needed, and both are in `zoneb::ctor_bottom`,
where `⟦T⟧` exists and the threaded `whnf_conv` can certify them:

* the **recursive field**'s scope assumption is at `⟦constType (T p⃗) (T p⃗)⟧`
  while `Ctor::mem` speaks about `⟦T⟧ p⃗`;
* the **parameter**'s is at `⟦id.{3} Type Type⟧` — `052` declares its
  constructor's parameter at a redex too, which is what its name is about —
  while `⟦T⟧`'s own λ is over `⟦Sort 1⟧`. `Interp::beta_spine` *checks* the
  premise it consumes, so a reduct landing anywhere else is the same decline it
  always was.

`052_reduceCtorParam.mk` translates completely: 2 stored → **5**, 3 groups → 7,
and its row is gone from the decline table. `113` and `114` do not, and the
reason is neither of the above:

| export | declaration | reason (at the time) |
| --- | --- | --- |
| `113_reduceCtorParamRefl.mk` | `reduceCtorParamRefl` | `ind-spec(…: carrier)` |
| `114_reduceCtorParamRefl2.mk` | `reduceCtorParamRefl2` | same |

Their fields reduce to `α → T α`, a **function-typed** recursive argument whose
domain is the declaration's own parameter, so the constructor's fibre value is
`Sum₁(Σ(z::γ(p⃗)))` — a term mentioning `p⃗`. `derived`'s `Fibre::new`
abbreviates each fibre value over **one** fresh variable
(`derived/src/fibre.rs`: `define_abbrev(env, &[yv], &values[i])`), since the
constant branch it builds is a 1-ary graph symbol through `funcs::lambda`,
`beta_conditional` and `Dispatch` alike. Located by instrumenting every `?` in
`Inductive::build`: it stops at stage 6, `Fibre::new`, and at no earlier one.
`RTree.node`'s `γ` is `Bool`, closed, which is why the corpus's only other
function-typed recursive argument passes. Generalising it is `derived/`-side
work and is what these two are now owed.

*(That generalisation landed on 2026-08-05 and the two reasons moved rather
than went; the section at the end of this file is the re-measurement, and the
table above is kept as it was measured.)*

### What is left of the miss path, and what keeps it

`Checker::miss_reason` reads the reason from a table and builds nothing. Three
tables answer it, and the third is new: the **eliminator's** reason had no memo
at all (`IndApparatus::deprec_failed` is a `HashSet`), so it was recomputed by
re-entering `recursor::ensure` at every use. It is attempted once, at the
declaration, and recorded in `IndApparatus::rec_declined`.

The construction itself stays, behind a `Gap::NoInterpretation` fallback that
`Interp::lazy_fills` counts and `tutorial_evidence_ledger` pins at **0** — 197
fills across 61 exports with the eager fill removed. Its remaining caller is not
the checker: 52 of `mini/src`'s unit tests build a `Checker` over an ad-hoc
`Environment` with no ledger and no schedule, and infer a constant occurrence
directly. Deleting the branch would not remove a production path; it would move
the fill into 52 test bodies, each of which would have to name the
`(declaration, σ)` its environment needs **and the order to build them in** —
which is the schedule, restated by hand.

## The fibre takes the parameter telescope — 2026-08-05

`derived::fibre::Fibre::new` abbreviated each fibre value over **one** fresh
variable, `define_abbrev(env, &[yv], &values[i])`, so a value mentioning the
declaration's parameters was refused by `kernel::thm::define`'s free-variable
guard. It now takes the parameter telescope and mints `coᵢ(p⃗,y) = vᵢ`, through
`funcs::lambda_n`, `funcs::beta_conditional_n` and `ext::lam_in_funspace_n` —
the arity-`k+1` siblings, which is the route `fibre.rs`'s own header named while
it was undone. At `np = 0` the three are line-for-line the unary ones with an
empty prefix, so nothing closed moves.

### The `?` census, before and after

The instrument is a `Tr` extension trait on `Option`, applied to every `?` in
`Inductive::build` by rewriting the function body (29 sites), printing
`carrier.rs:<line>` on `None`. Run over all 91 tutorial exports:

| | sites returning `None`, whole corpus |
| --- | --- |
| before | **one**, at `Fibre::new`, on `113` and `114` and on nothing else |
| after | **none**, on any export |

So `Fibre::new` was the only place the one-variable assumption was baked into
`Inductive::build`, and the carrier now builds for both.

### What mini had to bring, and it was not what the scope said

Nothing in `mini` — but `derived::inductive::carrier_at` did, and it was found
by the corpus panicking rather than by reading. That function re-states the
carrier at caller-supplied parameters, and it rebuilt the fibre's branches as
`Term::apply(lamᵢ, [Aᵢ])`: a **1-ary** application of what is now an
`np+1`-ary symbol, so `Term::apply`'s arity assertion fired on **15** of the 91
exports (every `np ≥ 1` declaration reaching a recursor). The repair is two
things and the second is the one no arity check would have caught:

* the branch is `lamᵢ(q⃗, Aᵢ(q⃗))` — the symbol *is* the substitution, since the
  kernel has none;
* the **codomain** must be re-stated too. `ind.fibre.target` is `{v₀} ∪ (…)` at
  the declaration's *own* parameter variables, and a value `Sum_m(Σ(z::γ(p⃗)))`
  mentions them. It happened to be closed for every declaration that reached
  `carrier_at` before, which is why the difference was invisible. It is now
  `Inductive::fibre_at`, a `&Machine` reader over `Inductive::rec_telescopes`.

### The stop moved, and it moved to two different places

The corner walk that pinned the old frontier — `mini`'s
`the_fibre_summand_frontier_splits_by_domain_at_np_one`, four synthetic cells —
re-measured:

| `np` | `γ` | before | after |
| ---: | --- | --- | --- |
| 0 | `A`, closed | **Ok** | **Ok** |
| 1 | `A`, closed | `ind-spec(T: carrier)` | `ind-spec(T: ctor abbreviation)` |
| 1 | `α`, a parameter | `ind-spec(T: carrier)` | `ind-fibre-value(T)` |
| 1 | `∅`, plain | **Ok** | **Ok** |

**Cells 2 and 3 used to agree and no longer do**, which retires the old
conclusion ("the refusal is about the pair `(np, γ)`, not what `γ` means"): it
held only while one blocker sat in front of two.

* Cell 2 is the *same shape* of gap one construction later and on mini's side —
  `zoneb::constructor` abbreviates the constructor term over the **fields
  alone**, and at `np ≥ 1` a function-typed recursive argument makes that term
  mention `p⃗` through `RecArg::of_general`'s summands. `rec_slot_terms`'s
  header had named this and said no cell could reach it; a cell reaches it now.
* Cell 3 is not a wiring gap. `Σ(z::α)`'s `bnd` is **refutable** — take
  `α := ⟦Nat⟧` — so `zoneb::fibre_facts` refuses it, and `cumul::sum_bnd` would
  refuse it under any `H`. *(**Superseded twice, and the cell is now `Ok`.**
  `bnd` came off the placement path, which killed the refutability argument;
  what replaced it — "`isum::isum_in_universe` refuses an input carrying a
  hypothesis or an antecedent, where the fact is spent" — was a description of
  a library that had not been asked, and `isum_in_universe_under` carries the
  antecedent. It was also only half the mini-side obstacle: the row was stated
  at the walk's scope variable rather than the carrier's parameters, so the
  guard's **other** disjunct fired too. See the 2026-08-05 entry "A
  recursive-argument domain that is a parameter".)*

### `113` and `114`: the carrier builds, the placement declines

Both still **accept**, both still certify, and their counters do not move —
`pairs = typeEv = constEv = 2`, `unsealed = gapped = lazyFills = 0` on each —
because the inductive is not one of their scheduled pairs (their dump's "also
stored (no scheduled pair)" section is empty, and the two pairs are `id` and
`constType`). What moved is the decline row:

```text
reduceCtorParamRefl σ=[]  (declined: ind-spec(reduceCtorParamRefl: carrier))
reduceCtorParamRefl σ=[]  (declined: ind-fibre-value(reduceCtorParamRefl))
```

Measured at the line: `CtorEvidence::rec_dom_sort`'s row for `γ = α` has
`hyps().len() == 1` and **the hypothesis is the conclusion** —
`α ∈ ⟦Sort ℓ⟧ ⊢ α ∈ ⟦Sort ℓ⟧` — while `115_rTreeRec`'s closed `γ = Bool` has
`hyps().len() == 0` and passes. That is the first live site of a predicate
`rec_dom_sort` had carried for two rounds without one, and the key it acquired
is `fibre_facts`'s own `Gap::IndFibreValue` rather than a new variant: the
refusal is per **summand**, which is the grain `FibreFacts` is stated at.
*(**One thing this measurement did not print, and it mattered.** The guard is a
disjunction and only the first disjunct was measured. The second — the row's
conclusion against `Formula::mem(interp, rung.set)` — was **also** false, because
`interp` is read off `rec_dom_abbrev` at `Inductive::params` while the row is
stated at the walk's own scope variable. The 2026-08-05 entry below is where
that was printed.)*

**The corpus is unchanged**: `accept=89 decline=2 reject=0 uncertified=0`,
`pairs=218 constEv=218 typeEv=218`, `unsealed=0 gapped=0 lazyFills=0`.

### Mutations, and one guard measured weaker than its comment

| mutation | killed by |
| --- | --- |
| `args_at` reverses `p⃗` at instantiation | the new `a_fibre_value_over_the_parameters_is_expressible` alone, plus 4 suites; a **1-parameter** fixture would not have seen it |
| `args_at` clamps the parameter index to `min(j,1)` | the same test; a **2-parameter** fixture would not have seen it, since the clamp is the identity on `{0,1}` |
| `fibre_summands_at` clamps the slot index | 4 suites with the agreement check; **1 test** without it |
| `fibre_summands_at` reverses the constructor list | 11 tests across 6 suites, **with the check removed** |
| `carrier_at` reuses `ind.fibre.target` | **nothing**, until `carrier_at_restates_the_codomain_and_not_only_the_summands` was written; that test now kills it |
| `carrier_at` applies `lamᵢ` at the declaration's own `p⃗` | 6 tests across 2 suites |

The fifth row is the finding: re-stating the codomain was correct and
**unexercised**, because no declaration that currently reaches `carrier_at` has
an open one — `113`/`114` decline before the recursor. The test is a
three-parameter direct call with distinguishable parameter terms and a rotation
control; it is the only thing standing between that line and a silent revert.
The third and fourth rows say the agreement check in `Inductive::build` moves
a wrong-term outcome forward into a clean decline rather than catching something
otherwise invisible, and its comment now says so at that strength.

## The constructor abbreviation takes the parameter telescope — 2026-08-05

The same defect as the entry above, one construction later and on mini's side.
`zoneb::constructor` minted its constructor-term symbol over the **fields
alone**, `define_abbrev(kenv, &fvs, &raw)`, while under `RecArg::of_general` the
term's dispatcher is stated over the fibre summands `Σ(z::γⱼ(p⃗))` and therefore
mentions the declaration's parameters. It mints over `p⃗ ++ f⃗` now. At `np = 0`
the prefix is empty and nothing closed moves; at `np ≥ 1` with only plain
constructors the extra arguments are inert, and the equality check in
`ctor_bottom` is what says so at every call.

### Localising the stop, before scoping on it

Not a `?` census this time: the gap label `ind-spec(T: ctor abbreviation)` has
exactly one site (`grep -n "ctor abbreviation" mini/src/zoneb.rs`, one match
outside doc comments), so the first stop needed no instrument. The **second**
did — widening the abstraction moved the frontier's cell 2 to
`ind-spec(T: ctor abbreviation instance)`, which has two sites returning the
same label. One `eprintln!` at the equality check, dumping the axiom's
right-hand side beside the term just built, answered it in one run: the two
`Term`s agree everywhere except the dispatcher's first argument, which reads
`Σ(z::γ(p_nest))` in the axiom instance and `Σ(z::γ(p_decl))` in the freshly
built term.

### The half no arity assertion sees, and this time it is in `derived/`

`Inductive::ctor_term` is a function of its arguments **except for the
summands**, which live on `RecArg::summands` at the declaration's own parameter
variables. `zoneb::ctor_bottom` builds its recursive slots at the *nest's*
parameters, so the term it assembled was half at one set of variables and half
at another — a constructor application of nothing. No arity check can see that:
both spellings have the same shape.

`Inductive::ctor_term_at(mach, i, y⃗, r⃗, p⃗)` is the repair, with
`Inductive::recfun_of_at` under it reading `Inductive::fibre_summands_at`'s row
`i` instead of `RecArg::summands`. **`ctor_term` and `recfun_of` delegate to
them at `Inductive::param_terms()`** rather than keeping a second body, so their
agreement is a consequence rather than a check — and, measured below, every
existing `derived/` test of the public term-builder now exercises the new row
lookup for free.

### Consumers, and the arity assertion that did find them

`Translated::ctor_abbrev` is now `∀p⃗ ∀f⃗`, so its four consumers instantiate at
`p⃗ ++ f⃗`: `zoneb::ctor_bottom`, `rec_dep` (`sp_args`), `iota_dep` (`ctor_tms`)
and `proj_data` at both of its sites (`arg_tms`). Each already had the full list
in hand under another name and was slicing `[np..]` off it. The **indexed**
twin, `ctor_ix::ctor_abbrevs`, deliberately did **not** move: nothing indexed
reaches the general dispatcher today, so there is no witness to widen against,
and its failure mode if one arrives is a decline (`define_abbrev`'s
free-variable guard, then `retarget_subject`) rather than a wrong term. Its
header now says so.

### The frontier walk, re-measured

| `np` | `γ` | before | after |
| ---: | --- | --- | --- |
| 0 | `A`, closed | **Ok** | **Ok** |
| 1 | `A`, closed | `ind-spec(T: ctor abbreviation)` | **Ok** |
| 1 | `α`, a parameter | `ind-fibre-value(T)` | `ind-fibre-value(T)` |
| 1 | `∅`, plain | **Ok** | **Ok** |

**Cell 3 is now the whole frontier.** Three controls at the same `np` — a closed
domain at `np = 0` and `np = 1`, and no domain at `np = 1` — now surround it,
and all three translate. `113_reduceCtorParamRefl` and
`114_reduceCtorParamRefl2` sit behind that cell.

*(This paragraph used to add "and it is not a wiring gap", on the ground that
`bnd(Σ(z::α))` is refutable at `α := ⟦Nat⟧`; then, after `bnd` came off the
placement path, that what refuses it is `isum::isum_in_universe`'s requirement
that the membership arrive without a hypothesis or an antecedent. **Both are
superseded and the cell is `Ok`** — see the 2026-08-05 entry "A
recursive-argument domain that is a parameter". `113`/`114` did **not** close
with it: their carrier is placed and they stop one construction later, at
`ctor(…: recursive field codomain)`.)*

### Corpus

**Byte-identical.** `diff` of `mini --verbose` over all 91 tutorial exports,
before and after, is **empty** — not merely the counters but every line:
`accept=89 decline=2 reject=0 uncertified=0`, `pairs=218 constEv=218
typeEv=218`, `unsealed=0 gapped=0 lazyFills=0`, and the two decline rows
unchanged. `ci/check.sh` green, twelve steps.

### Mutations

Every mutation was run against the **whole** workspace suite with
`--no-fail-fast`; without it `cargo test` stops after the first failing binary
and the corpus rows below do not appear at all (three of the nine were first
measured that way and under-reported).

| mutation | killed by |
| --- | --- |
| `constructor` abbreviates over `f⃗` again | 17 tests, corpus included — the consumers now pass `np` more arguments than the axiom binds |
| `constructor` abbreviates over `f⃗ ++ p⃗` (order swapped) | the same 17; the two ends are checked against each other |
| `ctor_bottom` instantiates and applies at `f⃗` alone | the same 17 |
| **`ctor_bottom` uses `ctor_term` instead of `ctor_term_at`** | **2 tests, both new-shaped**: the frontier's cell 2 and `three_constructors_…_at_np_one`. The whole corpus, every `derived/` suite and every other mini test pass under it |
| `rec_dep` instantiates at `f⃗` alone | 8, corpus included |
| `iota_dep` instantiates at `f⃗` alone | 5, corpus included |
| `proj_data` instantiates at `f⃗` alone (both sites) | 4, corpus only |
| `recfun_of_at` clamps the constructor row to `min(i,1)` | 6 — five `derived/` tests plus the new mini one; a **two**-constructor fixture sees neither, since the clamp is the identity on `{0,1}` |
| `recfun_of_at` reads the rows in reverse | 20 across 6 suites, corpus included |

The fourth row is the finding, and it is the same shape as the previous entry's
fifth: the parameter-threading half of this repair is **invisible to everything
that existed before it**. It is not that the corpus is insensitive to
constructor terms — the other eight rows show it is exquisitely sensitive — but
that no declaration mini has ever accepted takes a function-typed recursive
argument at `np ≥ 1`, so the two spellings coincide everywhere the corpus looks.
The two tests in that row are the only thing standing between `ctor_term_at` and
a silent revert.

The eighth row is why the new test has **three** constructors rather than two,
and it is also the argument for delegation over duplication: five of its six
killers are pre-existing `derived/` tests that reach `recfun_of_at` only because
`recfun_of` was rewritten to call it. A second body would have left those five
testing the old path.

## A recursive-argument domain that is a parameter — 2026-08-05

`inductive Tree (α) | node : (α → Tree α) → Tree α`. The obstacle was never that
the statement is false: a Lean declaration is always closed, so a parameterised
one's placement is `⊢ ∀p⃗. (H → ind(p⃗) ∈ Uₙ)` and the fibre summand `Σ(z::α)`
is in `Uₙ` under `α ∈ Uₙ` and under nothing weaker — a `Tree α` over a non-small
`α` has no W-type in `Uₙ` at all. The pipeline that spent it demanded an
unconditional input.

### The `?`-census, before and after

Over `zoneb::fibre_facts`, `cumul::decl::over_at_general`,
`cumul::sigma::unary_telescope_at` and `isum::isum_in_universe` — extension
trait on `Option`/`Result` printing `file:line` at every `?`, plus the explicit
early returns — run on the new fixture:

| | sites firing |
| --- | --- |
| before | `zoneb.rs`'s `!sort_th.hyps().is_empty() \|\| concl ≠ …` guard, **twice** (`PTree`, `MTree`), and nothing else |
| after | **silent** |

Every other `?` in all four functions already passed before the change,
including `unary_telescope_at` and the whole of `over_at_general`.

### What the census did not say, and a print beside it did

The guard is a **disjunction**, and a `?`-census names the line, not the
disjunct. A one-line `eprintln!` of `sort_th.hyps()`, `sort_th.concl()`, the
`Formula::mem(interp, rung.set)` it is compared against and `ind.params`, at the
same line, printed two facts where the brief predicted one:

```text
PTree  hyps  = [ Free(27079) ∈ U₁ ]
       concl =   Free(27079) ∈ U₁
       want  =   Free(27084) ∈ U₁        params = [ 27084 ]
```

The row's hypothesis set was one obstacle. Its **variable** was the other: the
walk states `⟦γ⟧`'s typing at the scope variable it opened, while `interp` comes
off `rec_dom_abbrev` instantiated at `Inductive::params`. Deleting the
hypothesis check would have left the conclusion check failing.

**One discharge fixes both**, which is why the repair is small: `Closed::discharge`
is `implies_intr` then `gen`, so it moves the hypothesis into the conclusion
*and* abstracts the scope variable; `summand_obligation` then collapses the
prenex and `inst_all` at `Inductive::params` lands the theorem on the carrier's
own variables. That is exactly the route every summand **leg** was already
taking, and the change is to run `CtorEvidence::rec_dom_sort` through it in
`spec_of`'s step 3.

### Where `H` comes from when there is no plain field

`decl_universe` read `H` off the legs. `Tree (α) | node : (α → Tree α) → Tree α`
has **no plain field**, hence no leg, hence `hyp = None` — while its fibre
summand needed `α ∈ Uₙ`. So the antecedent had to come from the `γ` typings
themselves, and `decl_universe` now reads it off both families with the same
agreement check. That is not an extra guard: they were discharged through the
same parameter scopes, so agreement is a consequence, and checking it is what
makes it one.

### `derived/`

`isum::isum_in_universe_under` — the same fold under `ctx::Ctx`;
`isum_in_universe` is it at `None`. In `over_at_general`, `T ∈ Uₙ` and
`⋃T ∈ Uₙ` move from the unconditional group to the conditional one; `fin` and
`S ∈ U({A,T})` stay, and the two are asserted **equal across the two contexts**
rather than merely non-implication-shaped, since a conjunction is spelled with
implications in this kernel. `decl.rs`'s unconditionality requirement was
**threaded, not relaxed**: every input is still checked for an empty sequent
hypothesis set on the way in and on the way out.

### The fixture

`mini/tests/fixtures/parameter_domain_branching.lean` — four trees at one shape
and four recursive-argument domains:

| declaration | `np` | domains | before | after |
| --- | ---: | --- | --- | --- |
| `CTree.node : (B2 → CTree) → CTree` | 0 | one, closed | certifies | certifies |
| `KTree.node : (B2 → KTree α) → KTree α` | 1 | one, closed | certifies | certifies |
| `PTree.node : (α → PTree α) → PTree α` | 1 | one, **the parameter** | declined | **certifies** |
| `MTree.node : (B2 → MTree α) → (α → MTree α) → MTree α` | 1 | **two, mixed** | declined | **certifies** |

**`constEv = 8`**, up from 4; `typeEv` 6 → 8; `waiting` empty;
`untranslated declarations = 0`; `unsealed = gapped = 0`.

**Where the mixed constructor's two rows are made uniform is not the fold**, and
the obvious answer was wrong. Both of `MTree`'s rows already carry `H` when
`isum_in_universe_under` sees them, because the walk discharges *every* domain
typing through the parameter scopes whether the domain needs it or not. The
fold's own lifting is at each tree's `leaf`, which contributes no summand and
whose `Sum_0()` rests on `∅ ∈ Uₙ`.

Three untranslated eliminators remain, and they are a different axis:
`KTree.rec` reported `recursor(…: dependent recursor: a minor premise does not
transport)` **before** any of this, at `np = 1` with a closed `γ`, and
`CTree.rec` at `np = 0` translates.

### `113`/`114` advanced and did not close

Their carrier **is** placed. Their untranslated reason moved from
`ind-fibre-value(…)` to `ctor(…: recursive field codomain)`: the field's Lean
codomain is `constType (T α) (T α)`, whose interpretation is an application
term, while the constructor's spine is `⟦T⟧(p⃗)`. The two are definitionally
equal — `rec_field` classifies the field by its reduct, which is why the
declaration is accepted at all — but `⟦·⟧` is a function of the term, so the
membership arrives about one and is owed about the other. One δ/β conversion,
SCOPING.md §4's calibration entry exactly, and the next work on this row.

*The prediction in the brief was that `113`/`114` "should follow". They moved
one construction. A shape that is obfuscated in the corpus and stated in a
fixture is not the same declaration to a checker that reads terms.*

### Corpus

`accept=89 decline=2 reject=0`, `constEv=218 typeEv=218`, `unsealed=0
gapped=0`, `untranslated: 1 declaration` at `113` and `114` and
`1 eliminator` at `052` — the column-granularity ratchet in
`tutorial.rs`'s `UNTRANSLATED_ON_THE_CORPUS` is unchanged. The reason strings in
`mini/tests/dump.rs` moved for `113`/`114` and are corrected in place.
