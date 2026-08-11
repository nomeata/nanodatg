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

**How to read the numbers in this file — and in `PROFILE.md`, `MONOMORPH.md`,
`MODELGEN.md` and `CACHING-DESIGN.md`.** The counters are evidence; the wall
clocks are commentary. This is a shared machine that has carried six seats in a
day and whose wall times swing **2.1× on load alone**, so no decision should
rest on a clock, and no two clocks should be divided to make a ratio — *not
even back-to-back ones on the same binary*, which control for the code and not
for the load. Any comparison a decision rests on is taken with
`perf stat -e instructions`; see `DECISIONS.md`, 2026-08-08. The section
"Which recorded numbers carry weight: counters against clocks" at the end of
this file classifies every recorded headline, and names the ones whose claim
survives on a counter even though the figure quoted for it does not.

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
   The wiring design left this as an export-format convention nobody had
   checked, and declined every polymorphic declaration rather than guess. It is
   checked now. *(The quoted phrase was attributed to `WIRING-DESIGN.md` §6.1;
   it does not occur in that document. `INDEXED-DESIGN.md` §8.1 note 2 inherited
   the same attribution and is corrected there too. The decode is independent
   and is not in doubt.)*
3. **A `βⱼ` body is unusable at a use site once `np > 0`.** It is stated over
   the *walk's* parameter variables, so the body at actual parameters must be
   read off `βⱼ`'s **instantiated** defining equation. *(The reason given here
   was "the kernel has no `Term::subst`". **Void** — `Formula::subst` is public
   and `derived::subst_term` derives term substitution; DECISIONS.md 2026-08-06.
   The conclusion is unaffected: what a use site wants is the equation, which is
   the seam between `βⱼ` and the caller's own term.)* Getting this wrong is not silent: the first cut produced 12 sites
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

**Two corrections to the framing above, 2026-08-10 (task #147); the figures
themselves stand as taken.** First, "2891" is not the size of `init-prelude`
and 19-of-2891 is not "how much of the prelude is translated": 2891 counts
**(declaration, σ) pairs whose declaration carries a value**, and the file has
2059 declarations scheduled at 3861 pairs, of which 968 belong to inductives,
constructors, recursors, `quot` and axioms and are in no row of this table.
Second, `19` and `26` are pair counts, not declaration counts. See "How far
along the goal is: the four denominators, and the row that states one" at the
end of this file for all four populations, the numerator re-measured at **26**,
and the specification of the row that will stop a bare count being quoted
again.

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

## The indexed function-typed recursive argument — two layers, 2026-08-05

`inductive IxT (α) : N → Type | node : {n} → (B2 → IxT α n) → IxT α (N.s n)`.
Witness `mini/tests/fixtures/indexed_infinitary_ctor.{lean,ndjson}`, target
`constEv = 4`. **Reached 0.** Two layers lifted and the third is `derived/`'s.

| round | the stop | owner |
| --- | --- | --- |
| as exported | `ind-spec(IxT: indexed function-typed recursive argument)` | `zoneb::ctor_spec`, a blanket `ni != 0` |
| lift 1 | `ind-spec(IxT: naming a constructor's term)` | `ctor_ix::ctor_abbrevs` |
| lift 2 | `ind-spec(IxT: indexed carrier)` | **`derived/`** |

### Lift 1 was a de Bruijn frame, and the stated reason was about something else

The refusal's ground was that a function-typed recursive argument's index
expressions may mention the bound `z⃗`, which `index_syms` abstracts over the
parameters and the plain fields alone. That is true in general and **is not this
declaration**: `IxT.node`'s recursive occurrence is indexed by the *plain field*
`n`.

What had to change: `rec_field` peels `∀z⃗` to find the spine, so it hands back
index expressions stated at binder depth `d + |γ⃗|` while the checker has
`np + d` open. Read at the shallower depth, `n` resolves to the **parameter**
`α` — which is *also* in the abstraction list, so `define_abbrev` succeeds and
mints `d⃗₀₀ = α`. **A wrong symbol, silently**, and nothing downstream compares
it against the declaration's syntax. The arm now opens the `γ⃗` binders for the
one `index_syms` call.

A `z`-dependent index stays declined and is **unrepresentable** rather than
unbuilt: `IndexedDeclSpec` fixes `d⃗ᵢⱼ`'s arity at `np + plains_before(i,j)`,
the thesis's own restriction (`thesis.txt:1798-1801`).

**The binders are opened *interpreted*, and the first attempt opened them
uninterpreted.** Both decline a `z`-dependent index and neither mints a symbol,
but uninterpreted the decline arrives as `Gap::SymbolicLevel` out of
`typing_of_bvar`, whose own doc says it "cannot arise from a well-formed
expression". The expression is well formed. Measured by the frontier test's cell
B before the shape was settled — *the key was wrong before the code was*.

`zoneb::tests::a_function_typed_recursive_arguments_indices_are_read_inside_its_own_binders`,
three cells: the index is the plain field (Ok, and the defining axiom is
instantiated at **two distinct terms** so that "the parameter" and "the plain
field" are distinguishable — one argument could not); the index is `z`
(`ind-spec(D: recursive argument index)`); the index is closed (Ok, and it is
the control that passes under every wrong reading of the frame).

### Lift 2 was predicted exactly; its consumers were not

`ctor_ix::ctor_abbrevs`' header said "the day there is a witness, this takes
`p⃗` and `ctor_bottom` takes `Inductive::ctor_term_at`, exactly as `crate::zoneb`
did." The witness arrived, and it did.

What the header did not name is that **three** readers instantiate that axiom,
not one: `ctor_ix::build`, `iota_ix_dep` and `minor_ix`. Widening the mint alone
took ten tests red — four indexed-eliminator unit tests and the whole corpus
(`tutorial_evidence_ledger`, `tutorial_the_whole_corpus_certifies`,
`tutorial_first_blocker`, `tutorial_conversion_split`, and two dump tests). The
non-indexed twin had caught the same omission as a 15-of-91 arity blow-up; here
it was a loud test failure, which is a **better** alarm than the one the brief
warned would be absent.

### The third layer, located

`?`-census over `IndexedInductive::build` and the five constructions under it
(`family/carrier.rs`, `good.rs`, `goodstep.rs`, `gval.rs`, `index.rs`):
`good.rs:247` once and `family.rs:187` one frame up, **and nowhere else**.

`good.rs:247` is the ι rebuild — `rec(ctorᵢ(…))` against `GoodValues::of(i,…)`.
The shape is `gval.rs::matrix_atoms`:

```rust
for j in 0..ctor.recs {
    let child = IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, ps, &comps)?);
    let slot = ap.apply(r.clone(), mach.syms.inj(j, s.point())?);
    atoms.push(Formula::mem(child, slot));
}
```

`r(Inj_j(•))` is the `j`-th recursive child at a **single point** — the
`finord(mᵢ)` fibre spelling. Under `RecArg::general` the summand is `Σ(z::γⱼ)`
and the slot holds a family, so the atom has to become
`∀z ∈ γⱼ. tup(d⃗ᵢⱼ) ∈ r(Inj_j(⟨z,•⟩))`: a quantified obligation, not a
membership. That changes `matrix_atoms`, the inversion rule in
`family/carrier.rs` that projects out of exactly that list, and `good.rs`'s
rebuild. **A construction, and `derived/`'s.**

### Corpus

Unchanged: `accept=89 decline=2 reject=0`, `constEv=218 typeEv=218`,
`unsealed=0 gapped=0`. `RBTree` is the corpus's indexed witness and it goes
through `ctor_abbrevs` at `np = 1` — with every `Slot::Rec` a *plain* recursive
occurrence, which is why it never saw either gap.

### The pattern, third instance

`113`/`114` moved twice as layers lifted; this fixture has moved twice. Both say
the same thing: **a decline's stated reason describes the layer that is
refusing, not the obstacle** — and the layer under it has never once been the
one the refusing layer named.

### A process finding: mutation testing in a shared tree is visible to other seats

Another seat sampled the shared working tree during this round and reported a
regression — `constEv 214`, `ctor(RBTree.leaf: naming the constructor's term)`,
and a failing frontier test. Both symptoms are **mine and transient**, and the
diagnosis is exact: `214` and the `RBTree.leaf` string are byte-for-byte what
this round's first intermediate state produced, the window in which
`ctor_ix::ctor_abbrevs` and `ctor_ix::build` had been widened to `p⃗ ++ f⃗` and
the other two consumers had not; the next commit-candidate state is green. The
`ctor-bottom-fields-only` and `abbrev-fields-only` **mutants** reproduce the
same state on disk, as do `shallow-frame` and `uninterpreted-z` for the frontier
test.

So a mutation run is indistinguishable, from outside, from a regression — it
puts deliberately broken code on disk for minutes at a time and the suite it
runs is the suite another seat would run. **Mutation runs belong in a worktree**
when the tree is shared. The cost this time was one seat's investigation; it
would have been the same investigation with a real regression, which is why the
report was the right thing to send.

*(The recursor oracle the other seat landed — `Loaded::export_recs`, 191
recursors compared against Lean's — is now one of exactly **two** tests that
kill the `shallow-frame` mutation, the one that mints a wrong index symbol in
silence. It earned its place on this round's work within an hour of landing.)*

## `Good`'s ι hypothesis was rebuilt with the wrong helper — 2026-08-06

Scoping #73 (`gval::matrix_atoms` for a `Σ(z::γ)` fibre). **`constEv` on
`indexed_infinitary_ctor` is still 0**; what this entry records is that the
layer had *two* stops and the first was a one-line misalignment hiding the
second.

### Measured

`?`-census over `Good::build`, on the fixture:

| | site |
| --- | --- |
| before | `good.rs:247` — the ι **statement** rebuild, `*eq.concl() != want` |
| after the alignment | `good.rs:285` — `ih_eqs: core.ih_eqs?` |

`iota_core` builds its ambient with `ctor_atoms_at(…, &rec_sets(s, ra, carrier))`
(`iota.rs:229`), which spells a function-typed slot `gⱼ ∈ fs(Aⱼ, W)`.
`Good::build` rebuilt the same conjunction with the plain `ctor_atoms` wrapper,
which spells every slot `rⱼ ∈ W`. The two agree **exactly when every recursive
slot is plain**, so the mismatch was invisible to all 91 corpus exports and to
every fixture until one had a function-typed slot at `ni ≥ 1`.

Fixed by using the pair `iota.rs` uses. At an all-plain constructor `rec_sets`
returns `carrier` for every slot and the atoms are term-identical, so the
corpus does not move — `accept=89 decline=2 reject=0`, `constEv=218
typeEv=218`, suite green.

*Two `?`s in a row in one function, and the first was not the obstacle. The
subagent survey that mapped this layer read the `ih_eqs` comment and reported
**it** as the stop; the census said otherwise, and both were right about a
different `?`. A comment that documents a decline is evidence that the decline
exists, not that it is the one being taken.*

### The real obstacle, now measured rather than inferred

`GoodIota::ih_eqs[j]` is `⊢ app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)`,
**unconditional**, and `crate::inductive::iota` returns `ih_eqs: None` under
`RecArg::general` — deliberately, with the reason written at `iota.rs:97-109`:
the general computation rule is conditional on the branches being functions,
and `good.rs` has no ambient to carry it under.

So #73 is not "change one atom". The pieces:

1. **`gval::matrix_atoms`** — atom `1+j` becomes
   `∀z. (z ∈ Aⱼ → tup(d⃗ᵢⱼ) ∈ app(r, Injⱼ(z)))`. Still **one** atom, so the
   `conj_proj` positions do not move. `d⃗ᵢⱼ` does not depend on `z` (`spec.rs`
   fixes its arity at `np + plains_before`), so `z` enters only in the slot.
   The degenerate slot keeps its present spelling — the house pattern
   `fibre_values` already uses for `Σ(z::∅)`, and what keeps `RBTree`'s terms
   unmoved.
2. **A conditional, `z`-indexed ih identity** to replace `ih_eqs[j]`. This is
   the new derivation; `iota.rs` already computes the general case's `sub_at`
   and `ih_at`, so the material exists and only the *unconditional* vector
   `GoodIota` exposes does not.
3. **Four consumers, not three.** The brief named `matrix_atoms`,
   `carrier.rs`'s inversion projection and `good.rs`'s rebuild. The survey
   found two more: `carrier.rs:605-646`, the membership rule's hand-built
   **forward mirror** of the same atom list which never calls `matrix_atoms`;
   and `carrier.rs:742`, a hand-respelled `app(cmp, Injⱼ(•))` beside the
   projection that must stay literally equal to the atom's slot term. Plus
   `prop_rec.rs:846-865`, which re-derives the inversion's `1+m` conclusion
   shape and will fail its equality check if that conclusion gains a
   quantifier.

`vacuous.rs` reads atom `0` only and `goodstep.rs` is shape-agnostic in `ψᵢ`;
neither moves.

## A constructor spelled through an abbreviation — two silences, 2026-08-06

`mutual_aux_encoding`'s `constEv` **11 → 23**, `typeEv` 17 → 23, `gapped` 6 → 0.
Every recursor and every rule theorem in the aux encoding now carries
`⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, at both σ.

The brief bisected the shape to constructor abbreviations in a minor's type and
named two suspects, `kernel.rs:2589`'s `is_prop_or_unit_ev` placeholder and
`conv.rs:81`. **Neither was the cause and both were worth fixing**: they were
what made the trail unreadable, and reading the trail is how the two real
causes were found. That is the §0.4 route the brief predicted, run twice.

### The `?`-census, before

`--block` on the fixture, first blocked pair `Arec` at `v := 0`, reason
`no-endpoint`. Some thirty mints in the trail, at four distinct lines:

| site | what it is | mints |
| --- | ---: | --- |
| `conv.rs:81` | `Conv::gap`, one line every `whnf` step routes through | ~20 |
| `kernel.rs:2589` / `2581` | `is_prop_or_unit_ev`'s negative-answer placeholder | 7 |
| `kernel.rs:1223` / `1263` | `delta_evidence` / `beta_evidence` at `cur_tm = None` | 4 |
| — | plus `unit-like(Tag)`, `unit-like(Aux)` under "other gaps" | 2 |

Not one of those lines is where anything was lost.

* **`Conv::gap` is a function, not a closure** — the module header's "one
  imprecision" applies to it and it was not listed. `#[track_caller]` on it
  moved the whole column to `kernel.rs:721`, which is `whnf_conv`'s `acc` when
  the caller handed in no endpoint. And *that* is not a mint either: `why` is
  the caller's own reason, already chosen. It is built with `Ev::Gap` now.
* **`is_prop_or_unit_ev` answered a question and filed a gap for it.** Every
  negative answer — head not a constant, constant not an inductive, inductive
  not unit-like — paired its `false` with an `Ev::missing` no caller reads.
  "This is not a proof" is an answer. It returns `Option<Ev>` now, so the
  negative branch has no slot to fill, and `Gap::UnitLike` is minted only when
  the inductive *is* unit-like.

### The census, after

The same pair blocks at three mints, all `kernel.rs:1042`, all
`Gap::Iota(Aux.rec)` — and the reason on the ledger row changed with them.
Nothing about the counters moved at that step; the *reason* became true, which
is exactly the `iota(Quot.lift)` → `recursor(Quot.lift: quotient iota: …)` shape
from the earlier round.

### Cause 1 — a congruence builds terms and did not record them

`derived::congr` states `⊢ app(⟦f⟧,⟦a⟧) = app(⟦f'⟧,⟦a'⟧)` and builds both sides
with `Term::apply` **inside the kernel**, so neither passes through
`Interp::mk` and neither reaches the `parts` table. A term's applicative
structure is only ever a recorded hint — the kernel exposes no destructor — so
an unrecorded endpoint is one `Checker::split_app` cannot take apart.

The fixture's conversion is `Mot m₁ m₂ m₃ Tag.ta Aux.a0 =?= m₁ Amk0` under ten
binders. Both `whnf` legs certify; both endpoints are present. `def_eq_struct`'s
`App` branch then splits them — and `⟦m₁ Aux.a0⟧`, which the ι/δ chain *built*
by lifting its leg over the argument stack, splits to `(None, None)` while
`⟦m₁ Amk0⟧`, which came from `infer_type` through `Interp::app`, splits fine.
The instrument that showed it was one `eprintln!` at the split, counting the
three cells: 33 395 decision-only calls with neither side present, 22 122 with
both, and **6** with the left side unsplittable — the fixture's `gapped = 6`,
exactly.

`conv::app_cong` records both endpoints now. `constEv` 11 → **20**.

### Cause 2 — the ι site refused every major that had to reduce

With the attribution repaired the residue named itself: `iota(Aux.rec)` on the
three rule theorems at `v := 1`, minted at the ι site's `Err(None)` arm. Its
comment said what it was doing — *"a major that had to reduce to reach its
constructor owes a conversion this route does not hold"* — and each of the four
route arms carried `major2 == major` to enforce it.

`Arec … Amk0` reaches `Aux.a0` only by δ. So the underlying constructor
certified and its abbreviation did not, and that is not a spelling the encoding
can avoid: an installed `A.rec`'s minors **must** mention `A.aB`, or the
constant is the wrong one.

The major is reduced with `whnf_conv` now, the rule is stated at the reduct on
both axes, and `Checker::spine_cong` — `lift_over_stack` with one argument
allowed to move — puts the major's own conversion in front of the rule.
`constEv` 20 → **23**. `MINI-HANDOFF.md`'s construction-2 note, which recorded
the guard as correct, is corrected in place.

### The new fixture, and the four numbers that separate the two causes

`ctor_abbrev_major.lean` — the mechanism with the mutual recursion taken out.
`constEv` out of 32:

| `app_cong` records | ι reduces the major | `constEv` |
| --- | --- | ---: |
| no | no | 21 |
| no | yes | 26 |
| yes | no | 25 |
| yes | yes | **32** |

Neither fix subsumes the other. `nrec` hands its motive in directly, so only the
major half fails there; `nrec2` computes the motive with `Tag.rec` at the
**middle** tag, which is what makes the minor's expected type reach `m₂ N.z` by
reduction and puts an unrecorded term on one side; `irec` is indexed and reaches
`iota_ix_dep` rather than `iota_dep`, a separate arm of the same match.

### Corpus

**Unchanged**, measured in a worktree carrying only these two files:
`accept=89 decline=2 reject=0`, `constEv=218 typeEv=218`, `unsealed=0 gapped=0`,
both decline rows byte-identical. `diff` of `mini --verbose` over all 91 exports
before and after is **eight lines**, all of the form `convs proved=… sealed=…`
and all upward by 3–59: the extra certified conversions where a major reduced.
`moved`, `movedSealed` and `gapped` do not move on any file. A release sweep of
the corpus takes 89.4 s against 89.0 s before — the certificate is only built
where one was already being tracked.

### Mutations

Whole workspace, `--no-fail-fast`, in a worktree.

| mutation | killed by |
| --- | --- |
| `app_cong` records the LHS endpoint only | **1** — the new fixture, and nothing else |
| `app_cong` records the RHS endpoint only | **nothing** |
| `app_cong` records the RHS with its arguments swapped | 1 |
| the rule is stated at the major's original **term** | 1 |
| the rule is stated at the major's original **expression** | 1 |
| the major's conversion is dropped in front of the rule | 1 |
| `spine_cong` puts the conversion at position 0 | 1 |
| the **indexed** arm keeps `major2 == major` | 1 |
| the **plain** arm keeps `major2 == major` | 1 |
| both attribution repairs reverted | **nothing**, until the two unit pins below; then 2 |

Two findings. **The second row**: only the reduct's record is ever read, because
every call site takes its left endpoint from a term the caller already held. The
line stays — it costs one insert of a term already present, and it is the
difference between recording what the function builds and recording what this
year's consumers happen to read — and its doc comment now says it is
unexercised.

**The last row**: an attribution repair is invisible to a suite that asserts on
counters, because it moves no counter by construction. `kernel::tests::`
`deciding_that_something_is_not_a_proof_mints_no_gap` and the second half of
`an_uncertified_whnf_reports_a_named_absence` are the pins, and they are the
first tests in the tree that assert on the *trail* rather than on a gap's
identity. That is the same hole the `Gap::Iota` attribution round left open.

### What the mutual thread should know

The residue is zero and it is zero for a general reason, not a special-cased
one: nothing in either fix knows what a mutual block is. `mini/tests/mutual.rs`
declines to pin `mutual_aux_encoding`'s `constEv` on the grounds that it belonged
to another seat's live work — it no longer does, and `23` is the number to pin.

## The good-set matrix learns a fibre with more than one point — 2026-08-06

`indexed_infinitary_ctor`'s `constEv` **0 → 2**, `typeEv` 1 → 4, `untranslated
declarations` 1 → 0. `IxT`'s carrier is placed and `IxT.leaf` lands; the two
branching constructors are the residue, and the layer that owns them is
`mini/`'s, not `derived/`'s. Scoping #73, landed, and a fourth layer located.

### The census, before and after

| | site | reason |
| --- | --- | --- |
| before | `good.rs`'s `ih_eqs: core.ih_eqs?` | `ind-spec(IxT: indexed carrier)`, 4 waiting |
| after | `ctor_ix::ctor_bottom`'s `ind_spine` on the recursive field's binder type, **twice and nowhere else** | `ctor(IxT.node/wide: a recursive argument's indices)`, 2 waiting |

The "after" row is a `?`-census with one `eprintln!` per `REC_ARG` site, not an
inference: `local_type` and `infer_indices` never fire. The binder type is
`∀z::γ. IxT α n` and `ind_spine` wants the family's spine, so a function-typed
field's `d⃗ᵢⱼ` cannot be read at all yet.

### What the conditional ih identity actually needed

Not what #73 predicted. The prediction was that "`iota.rs` already computes the
general case's `sub_at` and `ih_at`, so the material exists". `ih_at` is the
*function* identification `cmp|ⱼ = comp(grec, tⱼ, Aⱼ)` — what a minor premise's
ih slot receives — and the matrix needs the composite's value **at one point of
the fibre**, which is a different statement. What did exist was the pointwise
chain `c1 ∘ c2 ∘ c3 ∘ c4` buried inside the function-typed arm; the new row is
its middle two steps,

```text
⊢ P → ∀z. (z ∈ Aⱼ → app(cmp, Injⱼ z) = app(grec, app(tⱼ, z)))
```

hoisted out and *reused* by that arm, so `cmp|ⱼ`'s chain now runs through the
ih row's own equation and the two cannot say different things about
`app(cmp, Injⱼ z)`.

Two things the prediction did not say, and both are the same point:

* **The row exists at every slot of a general constructor, degenerate ones
  included.** `RecArg::general`'s computation rule dispatches over every summand
  alike, so a `γⱼ = ∅` slot inside a mixed constructor has the conditional rule
  and no other. `IotaCore` therefore hands back `IhRow`, keyed on the
  constructor: `Point` (unconditional, `m` of them) at a plain constructor and
  `Fibre` at a general one, never a mix.
* **"The degenerate slot keeps its spelling" is refuted.** At a *mixed*
  constructor the degenerate slot's atom becomes the bounded universal too,
  because that is the only rule available there. What keeps `RBTree` unmoved is
  that a **plain constructor** keeps its spelling — a different statement, and
  the reason `matrix_atoms` keys on `ctor_slot_domains` and not
  `rec_slot_domains`.

The ambient is `Hᵢ^ctor`, the constructor's own argument typings — which
`good.rs` always had and which its header said it did not. That header is
corrected in place.

### The consumers: four predicted, one did not move, two were not predicted

| consumer | moved | what |
| --- | --- | --- |
| `gval::matrix_atoms` | yes | the bounded universal; **one** conjunct, so no `conj_proj` position moves |
| `carrier.rs`'s membership rule | yes | the forward mirror — a function-typed field is stated at `fs(Aⱼ, ind(p⃗,d⃗ᵢⱼ))`, weakened to the skeleton by `fs_mono` over a generalised `subset_w`, and the matrix discharged **pointwise** |
| `carrier.rs`'s inversion projection | yes | reads the same universal out and puts the function back together with `funspace_retarget` — the exact converse of the `fs_mono` step |
| `carrier.rs`'s hand-respelled `app(cmp, Injⱼ(•))` | yes | it is `Injⱼ(z)` in the general arm; the `let _ = &cmp_c;` dead line went with it |
| `prop_rec.rs`'s `1+m` conclusion rebuild | **no** | it fails *closed* — nothing routes a general indexed constructor to it, and the shape check declines rather than mis-states. Predicted to move; it does not have to |
| `carrier.rs`'s `Hᵢ^skel` | **unpredicted** | the *second* instance of the `ctor_atoms` / `ctor_atoms_at`-at-`rec_sets` misalignment `Good::build` had last round, in the file last round did not look at |
| `mini/src/ctor_ix.rs`'s `ctor_abbrevs` | **unpredicted** | it minted a wrong-but-well-formed symbol in silence: `ctor_term` at the **raw** Lean field builds a dispatcher over a branch that is not a function on `Σ(z::γⱼ)`. It goes through `zoneb::rec_slot_terms` now, and the mutation restoring it survived the whole suite until a pin was written for it |
| `vacuous.rs`, `goodstep.rs` | no | as predicted — atom `0` only, and shape-agnostic in `ψᵢ` |

**Three of this row's four layers have now been a wrong-but-well-formed term
minted in silence**: lift 1's `d⃗₀₀ = α`, lift 2's abstraction over the fields
alone, and this round's constructor abbreviation. None of the three was found by
a failing assertion about the term; each was found by a decline one construction
downstream, or by looking.

### The witness, and the two axes it started degenerate

`derived/tests/family_infinitary.rs`, five constructors:

| | shape | what it is for |
| --- | --- | --- |
| `leaf` | `α → IxT α zero` | a plain constructor in the same declaration, and the value everything else hangs its children on |
| `node` | `(B2 → IxT α n) → …` | the two-element fibre |
| `wide` | `(T3 → IxT α n) → …` | a *third* row, so a clamp `i ↦ min(i,1)` cannot hide — identical to `node` in every other respect |
| `pair` | two function-typed slots, **different** fibres | the slot index `j`; at `m = 1` a swap `j ↦ 0` is invisible |
| `mixed` | one plain recursive field beside a function-typed one | the one shape at which `ctor_slot_domains` and `rec_slot_domains` disagree |

`pair` and `mixed` were added after the first three passed, because the first
three leave `j` and the mixed constructor degenerate — the failure mode two
sibling threads hit in the last three rounds. Both build.

Both polarities: `node` fires over a genuinely two-element fibre at a constant
function whose value is a `leaf` (one `lambda_n`, typed by `lam_in_funspace_n` —
a one-point graph cannot inhabit a two-element domain), and the carrier is
provably **empty** at a height no constructor produces, quantified over every
element of the skeleton and refuting all five constructors.

### Mutations

Whole workspace, `--no-fail-fast`, **in a worktree** (`/home/joachim/nd-mut73`,
its own target dir, `vendor/arena-tests` symlinked in) — because a mutation run
puts deliberately broken code on disk for minutes at a time and another seat
sampling the shared tree cannot tell that from a regression. That cost one
seat's investigation last round.

| mutation | killed by |
| --- | ---: |
| `matrix_atoms` keys on the **slot** grain (`rec_slot_domains`) | 5 |
| the fibre summand **row** is read at `min(i,1)` | 19 |
| the bounded universal loses its bound — `∀z. tup(d⃗ᵢⱼ) ∈ app(r, Injⱼ z)` | 6 |
| it quantifies but keeps the point slot `Injⱼ(•)` | 6 |
| the ih row stops one step short, at `app(grec, app(recfun, Injⱼ z))` | 19 |
| the ih row is read at slot `0` whatever `j` is | 5 |
| only the **summand** is read at `min(i,1)`, the row length kept | 6 |
| (M) states a function-typed field at the family, not at `fs(Aⱼ, ·)` | 6 |
| the trivial `∅ = ∅` is not stripped from the fibre row | 6 |
| `ctor_abbrevs` names the **raw** Lean field | **0** — then **1** |

Five findings.

**The corpus is blind to every one of them, and that was measured once rather
than assumed.** The first mutation was run against the whole suite including
`tutorial`: zero corpus failures. Every mutation's diff is inside a
general-fibre branch and no corpus export is indexed *and* general, so the
remaining runs skip `tutorial_` — which is also what makes them affordable,
since `077_RBTree.id_spec` alone is ten million conversions in a debug build.

**The `min(i,1)` clamp is caught twice over, and only one of the two is about
the third constructor.** Clamping the whole *row* trips the
`doms.len() != ctor.recs` guard at any indexed declaration with three
constructors of differing recursive arity — 19 tests, most of them `RBTree`'s.
Clamping only the *summand*, keeping the row length, is the honest form of the
question, and it is killed by 6: `family_infinitary`'s five and the fixture's
own pin. `wide` is what kills it; with `leaf` and `node` alone `min(i,1)` is the
identity.

**The ih row is shared with the non-indexed dependent recursor, and that shows
up as a kill.** `row-unrewritten` takes down three tests that predate this round
— `the_dependent_recursor_at_a_function_typed_argument`, `…at_a_mixed_
constructor` and `the_dependent_premises_are_satisfiable_at_a_function_typed_
argument` — because the pointwise fact was *hoisted out of* the function-typed
arm rather than duplicated beside it, so `cmp|ⱼ`'s chain now runs through the
row's own equation. Duplicating it would have cost those three kills.

**`row-slot-zero` is the case for `pair`.** Reading the ih row at slot `0`
whatever `j` is, is killed by `family_infinitary` and by **nothing else** — not
even by the fixture, whose two branching constructors each have `m = 1`, where
`j` is `0` anyway. Had `pair` not been added after the first three constructors
passed, this mutation would have survived the entire tree.

**`abbrev-raw-slots` survived everything.** `ctor_ix::ctor_abbrevs` minting the
dispatcher over Lean's own function — a well-formed term that is not the
constructor — is invisible to the whole suite, because `⟦G.g⟧`'s nest declines
one construction later, at `ind_spine`, before anything reads the symbol at all.
`ctor_ix::tests::the_constructor_abbreviation_is_not_the_raw_lean_field` is the
pin, on a general indexed family built for it, and it kills the mutation **1**
and nothing else does. It is the negative half deliberately — that the mint is
*not* the raw-field term — because the positive half would be the same call
under a different name. This is the third round running in which the thing that
was wrong was a term nothing compared against anything.

### Corpus

**Unchanged**: `accept=89 decline=2 reject=0`, `constEv=218 typeEv=218`,
`unsealed=0 gapped=0`, `moved − movedSealed = 8979`. `RBTree` is the corpus's
indexed witness and every one of its recursive slots is a plain occurrence, so
`ctor_slot_domains` is all-`None` there and every atom is term-identical to what
it was.

*A process note, and it is the same one as last round in the other direction:
`ci/check.sh` failed once during this round with nine `tutorial` tests reporting
`mini exited with None` on `077_RBTree.id_spec` — no exit code, i.e. a signal.
That file alone runs ten million conversions in a debug build, and nine test
threads were running it at once beside another seat's `--features stepcount`
sweep. `--test-threads=2` is green, and the file is green standalone. A
resource kill and a regression are the same symptom from outside; the
distinguishing measurement is one run of the one file.*

### The fourth layer, shaped

`ctor_ix` needs what `zoneb::ctor_bottom` already has for the non-indexed twin,
at an indexed codomain:

1. **Peel the `γ⃗` binders off the recursive field's `local_type` before
   `ind_spine`, and shift the frame.** This is lift 1's hazard one construction
   over: the index expressions come back stated `|γ⃗|` binders deeper than the
   nest's bottom has open, and read shallow they resolve to a parameter.
2. **Carry the field's typing** `dprod(b,⟦γ⟧) → fs(⟦γ⟧,⟦T p⃗ d⃗⟧) →
   fs(β₀ⱼ(p⃗), ind(p⃗,d⃗ᵢⱼ))` and then through `sigma::reindex_in_funspace` —
   `zoneb`'s five steps with `ind(p⃗)` replaced by the family at that slot's own
   index vector.

The third half is already closed: the constructor *term* is built at the
transported slots, because `ctor_abbrevs` goes through `rec_slot_terms` now.

## The `lazyFills` residue was a declaration order — 2026-08-06

**`lazyFills` 1 → 0 on `mutual_iota_reduction`, 2 → 0 on `mutual_parameters`,
1 → 0 on `mutual_index_sorts`.** Those three were the only place the design's
`lazyFills = 0` did not hold. `pairs`, `constEv`, `typeEv` and every other
column on all ten mutual fixtures are unchanged.

### What it counted, by `panic!`

The technique that settled #57 at zero, applied to the residue: the
`Gap::NoInterpretation` arm of `Checker::miss_reason` was made to `panic!`, and
the declaration walk was made to print the pair it was on. One run answered it.

```text
PAIR A.rec._auxRule0 σ=[1]
LAZY FILL MISS: Eq at σ=[1]
```

Every miss, on all three files, is `Eq`, and every one is at the **first rule
theorem** of the first encoded block. Printing the whole walk said why:

```text
DECL A._auxTag … DECL A.rec._auxRule0   ← the miss
DECL N   DECL aSize …   DECL Eq  FILL Eq σs=[[0],[1]]
```

`Eq` is declared **after** the block. The export's declaration list is in
dependency order and a block that never mentions equality has no reason to
precede it; `mutual_aux::expand` was emitting the rule theorems *at the block*,
so a statement naming `Eq` was checked before `Eq`'s own declaration had filled
the store.

So it was neither of the two hypotheses on the table. It was **not** the
fixpoint having a blind spot at the generated declarations — `Eq`'s σ were in
the schedule the whole time, `[[0], [1]]`, put there by the file's own pre-pass
— and it was **not** the counter over-reporting: an interpretation really was
being built off-schedule. It was the one thing the σ walk cannot express,
*when*. That is also why widening the walk to follow the file's constants
changed nothing, the measurement `mutual_aux::demand`'s header already carried
and which was read as "nothing to find here".

The count is the number of `(Eq, σ)` the first rule theorem needs:
`mutual_parameters` has two because its recursors are scheduled at `σ = [0]`
and `σ = [1]`, and its rule theorems inherit both.

### The fix

`expand` holds every block's rule theorems back and appends them after the
whole file. It is correct rather than merely sufficient: nothing can depend on
a rule theorem, because nothing uses one, and everything a rule theorem depends
on — the encoding's own definitions, and the file's `Eq` — is declared before
the end of the list. Nine lines.

### Mutation

Whole workspace, `--no-fail-fast`, in a worktree.

| mutation | killed by |
| --- | --- |
| the rule theorems are emitted at the block again | 1 — the `lazyFills` columns |
| only the **first** member's rules are held back | 1 — the same |
| the rules are appended **per block** rather than after the file | 1 — the same |

The second and third are the axes the fix could have been written wrong on and
still passed a one-fixture check: *which* members' rules move, and *how far*.
`mutual_iota_reduction` has six rules at three members and
`mutual_index_sorts` has three blocks, so both are separated. Only
`mutual_parameters` reports, because the table's loop stops at its first
mismatch; all three rows carry the number.

### The scope line's own doc was the thing that made this findable

`Checker::miss_reason`'s header enumerated "all 91 tutorial exports and all
nine designed fixtures" and was true; the mutual fixtures are neither, and were
outside the sentence. The enumeration now says which population it is over.

## #76's shape, checked before it is built — 2026-08-06

The unequal-index-telescope scope line was recorded, in three places, as
needing "an `Ix : Tag → Type` computed by recursion on the tag". That was
written as a guess and never measured. The measurement says the shape is
something else, and cheaper: **the indices move into the tag**.

```text
inductive Tag (p⃗) : Sort W          -- Tag.i : ∀p⃗ ix⃗ᵢ, Tag p⃗
inductive Aux (p⃗) : Tag p⃗ → Sort u  -- no index telescope at all
def Tᵢ  := fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.i p⃗ ix⃗ᵢ)
def Mot := fun p⃗ m⃗ => Tag.rec p⃗ (fun t => Aux p⃗ t → Sort v) m⃗
def Tᵢ.rec := fun p⃗ m⃗ k⃗ ix⃗ᵢ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ (Tag.i p⃗ ix⃗ᵢ) t
```

Today's encoding is that shape with every `Tag` constructor nullary, so it is
one path with nothing branching on whether the telescopes agree.

### The probe

Six blocks, written out by hand at the kernel's binder discipline (`@`
everywhere), Lean 4.32.2. Chosen so that no two of them are degenerate on the
same axis.

| block | the axis it holds | verdict |
| --- | --- | --- |
| `HA : N → Type`, `HB : Type` | **arity** differs, 1 vs 0, two members | rules `rfl` |
| `MA, MB : N → _`, `MC : _` | two members **share**, one differs, at three | rules `rfl` |
| `DA : N → _`, `DB : Bit → _` | equal arity, index **type** differs | rules `rfl` |
| `SA/SB/SC` | `Prop`-valued, 2 params, 2 indices, one at `Type 1` | accepted |
| `VA/VB` | index type mentions the **parameter** (`Pair α`) | rules `rfl` |
| `AA/AB`, parameterised, no indices | the **degeneracy**: every tag ctor nullary | accepted |

`#print axioms` on every rule theorem: *does not depend on any axioms*. The
only diagnostics in the whole probe are `noncomputable`/`defProp` linter
warnings, both of which the real fixtures already carry.

`Mot (Tag.i p⃗ ix⃗ᵢ)` ι-reduces to `mᵢ ix⃗ᵢ`, which is the reduction step 5 rests
on, and it does so for the same reason `Mot Tag.i` reduces to `mᵢ` today:
`Tag.rec`'s minor for a constructor with fields is applied to those fields, and
the motive in hand, `mᵢ : ∀ix⃗ᵢ, Tᵢ p⃗ ix⃗ᵢ → Sort v`, is δ-equal to the minor
type `∀ix⃗ᵢ, Aux p⃗ (Tag.i p⃗ ix⃗ᵢ) → Sort v` without an η wrapper.

### The level moves; it does not go away

`Tag` now carries index *values*, so it lives at
`W = max(1, s₁ … s_k)` over **every member's** index types, and that is still
`kernel::sort_under`'s question — an index of type `N` is at `Sort 1` only
because `N` says so. What becomes pure syntax is the level `Tag.rec` runs at:
the packed motive body loses its index telescope, so it is `max(u, v+1)`.

The trap the owner predicted is the same trap in a new address, with the same
witness. The cheap guess for `W` is `1`, and it is right on every fixture
except a `Prop`-valued family indexed by a large type — `SA`'s `γ : Type 1`,
whose sort is `Sort 3`, forces `W = 3`. `mutual_index_sorts` goes on being the
separating fixture, and its `.lean` header's `Sort 3`/`Sort 1` section survives
the lift verbatim apart from which declaration the number lands on.

An over-approximation of `W` is safe in a way the old `w` was not required to
be: `assertLevelLe sⱼ ≤ W` holds a fortiori, and nothing constrains an index
type's sort from above.

### What it cost

Estimated here as "all seven steps of `encode`, and two axes with no fixture",
and that is what it was. The section below it — *"Unequal index telescopes, and
the tag that carries them"* — is the landing.

## Unequal index telescopes, and the tag that carries them — 2026-08-06

**`mutual_index_sorts` exit 4 → 0**, `pairs` 42 → 56 with `constEv` 39 → **56**
and `typeEv` 41 → **56**; `mutualEncoded` 2 → 3, `mutualRules` 8 → 10;
`untranslated` 0/0/0 and `lazyFills` 0. `Reason::IndicesDiffer` is retired. The
corpus is where it was — `accept=89 decline=2 reject=0`,
`constEv=typeEv=218`, `unsealed=0 gapped=0`.

`Aux` had one index telescope, so a block's members had to share theirs. It has
none now: the telescopes are in the **tag**.

```text
inductive Tag (p⃗)  : Sort W            -- Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗
inductive Aux (p⃗)  : Tag p⃗ → Sort u    -- exactly one index, at every block
def Tᵢ      := fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ)
def Mot     := fun p⃗ m⃗ => Tag.rec p⃗ (fun t => Aux p⃗ t → Sort v) m⃗
def Tᵢ.rec  := fun p⃗ m⃗ k⃗ ix⃗ᵢ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) t
```

### One path, and the eight fixtures are the proof

A block whose members are unindexed is the case where every tag constructor is
nullary. Nothing branches on whether the telescopes agree, and the check that
this is true rather than merely intended is that **the eight fixtures that
predate the generalisation did not move by one counter** — `pairs`, `constEv`,
`typeEv`, `lazyFills`, `mutualBlocks`, `mutualEncoded`, `mutualRules`, exit
code. `Tag` gains parameters and level parameters on every one of them and none
of that is visible, because an `Inductive` opens no `(declaration, σ)` pair.

`the_generated_recursors_are_the_ones_lean_exports` — the oracle that is not
mini — still passes over every fixture and the whole corpus.

### The level moved and kept its witness

`W`, the sort `Tag` is declared at, is now the one number not readable off the
declaration: `max(1, s₁ … s_k)` over **every member's** index types.
`Tag.rec` runs at `max(u, v+1)`, which is pure syntax — the packed motive body
lost its index telescope. The index sorts did not stop mattering; they moved
from a recursor's instantiation to an inductive's declared universe.

The `1` is a floor and not padding: `Tag.rec` must eliminate into
`Sort (max u (v+1))` and a `Prop`-valued `Tag` could not. An
over-approximation is safe in a way the old `w` was not required to be — the
kernel checks `sⱼ ≤ W` and nothing bounds an index type's sort from above — and
`sort_under` is still handed `∀ix₁…ix_{j-1}, Iⱼ`, an `imax` above `sⱼ`.

### Mutations

Whole `mini`, `--no-fail-fast`, in a worktree. **Seven, all killed.**

| # | mutation | killed by |
| --- | --- | ---: |
| 1 | `W = 1` — the cheap guess, no `sort_under` at all | 2 |
| 2 | `W` over the **first member's** index types only | 2 |
| 3 | `to_aux` builds `Tag.t_k ix⃗` without the parameters | 2 |
| 4 | `Tᵢ.rec` passes `Tag.t₀`'s arity instead of `Tag.tᵢ`'s | 3 |
| 5 | every motive's type gets member 0's telescope | 2 |
| 6 | every `Tag` constructor gets member 0's telescope | 2 |
| 7 | the surviving index shift, past the motives before it, deleted | 2 |

**Row 2 is the one the round nearly shipped without.** With one shared
telescope, "over every member" and "over member 0" were the same set, and they
still are on every fixture that predates this round: `mutual_index_sorts` is
**green under the mutation** — its `SA`/`SB`/`SC` members all carry the same
two indices, so member 0 already sees the `Type 1` that forces `Sort 3`. The
only thing that separates them is a block whose *first* member has no indices
and whose second is indexed by a large type, which could not be written down at
all before this round, because the members had to agree.

| | `mutual_index_sorts` | `mutual_index_telescopes` |
| --- | --- | --- |
| unmutated | encoded 3, `constEv` 56 | encoded 3, `constEv` 72 |
| row 1 (`W = 1`) | encoded **2**, `constEv` 32 | encoded **2**, `constEv` 56 |
| row 2 (member 0) | encoded 3, `constEv` 56 | encoded **2**, `constEv` 56 |

Row 1 is `mutual_index_sorts` doing the job it was built for, at the new
address. Row 2 has exactly one witness and it is new.

### The new fixture, and the axes it holds apart

`mutual_index_telescopes.lean`, three blocks, `pairs = constEv = typeEv = 72`,
`mutualEncoded = 3`, `mutualRules = 13`, exit 0.

| block | axis |
| --- | --- |
| `MA : N → _`, `MB : _`, `MC : N → _` | two members share, one differs — **and the odd one is in the middle**, so clamping to the first *or* the last member is wrong on `MB` and nothing else |
| `DA : N → _`, `DB : Bit → _` | equal arity, different index **type** |
| `EA : Prop`, `EB : Type 1 → Prop` | the member that fixes `W` is **not** member 0 |

`mutual_index_sorts`' `HA : N → Type` / `HB : Type` is the **arity** axis at
two members, and it became that without being regenerated: the same `.ndjson`
went from exit 4 to exit 0.

Five of the first block's six constructors hold a member whose index arity
differs from the one they build, so the ι rule's induction hypothesis is at a
*different* telescope from the rule's own — in both directions. `maSize`,
`mbSize` and `mcSize` apply the three recursors over one shared motive and
minor list whose **motives are at two different telescopes**, and four
hand-written `Eq.refl` theorems fire the rules across the boundary. Those were
checked by Lean at export time, so they are an oracle that is not mini.

### What did not need to change

`kernel/`, zone A (`kernel::add_block` never required the telescopes to agree
— this was the encoding's line, not the kernel's), `demand`, `expand`, the
black-box allowlist, and `ci/check-mutual-blackbox.sh`, which still licenses
`kernel::{add, sort_under}` and nothing else. `sort_under` is asked a different
question and is asked it in the same way.

## Nested inductives: specialise, check, restore — 2026-08-06

**Zone A takes a nested declaration**, and the recursors it generates are the
ones Lean exports — by the oracle, at every nested fixture. `nested_shapes`
goes from `decline` (exit 2) to `accept`; `nested_iota` is a new fixture whose
**fourteen** `rfl` theorems are the ι rules of seven nested recursors, and mini
reduces every one of them. The corpus does not move: `--nested` is a gate and
nothing sets it there.

### The construction

```text
inductive Tree | leaf | node : List Tree → Tree          -- what the export declares

specialise    {Tree, Tree._nested.1}                     -- a mutual block, mimic copy of List
              Tree.node : Tree._nested.1 → Tree
              Tree._nested.1.nil  : Tree._nested.1
              Tree._nested.1.cons : Tree → Tree._nested.1 → Tree._nested.1
check         kernel::add, unchanged — the block is an ordinary mutual one
restore       Tree._nested.1      ↦ List Tree
              Tree._nested.1.nil  ↦ List.nil Tree
              Tree._nested.1.cons ↦ List.cons Tree
              Tree._nested.1.rec  ↦ Tree.rec_1
```

`mini/src/nested.rs`, 620 lines including the header. The mimics are checked in
a scratch environment and never installed; the whole checker interaction is one
`kernel::add` on a `Declaration::Mutual`, which is why the file inherits the
black-box allowlist (`ci/check-mutual-blackbox.sh` now scans both encoders, with
the same self-test).

### The oracle, and it is not vacuous on this path

`the_generated_recursors_are_the_ones_lean_exports` compares mini's **generated**
recursor against the export's own — level parameters, type, `(params, motives,
minors, indices)`, K-likeness, rule count, rule order and every rule's
right-hand side. Both nested fixtures are in its sweep now; `nested_shapes` was
the one fixture it could not see and the skipped set is empty.

The recursors are generated and not read: `Loaded::export_recs` stays a test-only
table and `parseRecInfo` stays a stub. **The alternative — taking the export's
recursor as the specification — would have made this comparison trivially
satisfied**, and the acceptance axis would then have no check at all on this
path. It costs about eighty lines of restoration to keep it, and the
specialisation it rests on is needed for the model anyway.

| shape | fixture | recursors compared |
| --- | --- | --- |
| `numNested = 1`, recursive container | `Tree` (both fixtures) | 2 |
| `numNested = 1`, non-recursive container | `PTree : Pair PTree` | 2 |
| `numNested = 1`, two positions in one constructor | `BTree : Pair _ → Pair _` (`shapes`) | 2 |
| `numNested = 2`, **one** container twice | `DTree : List (List DTree)` | 3 |
| `numNested = 2`, **two different** containers | `BTree : Box BTree`, `Box` a structure over `List` (`iota`) | 3 |
| a nested type with **parameters of its own** | `PT (α) : List (PT α)` | 2 |

The last two are `Lean.Syntax`'s shape and the axis every other fixture is
degenerate on. `DTree` alone would have passed a treatment keyed on the
container's *name*; `Tree`/`BTree` alone would have passed one that dropped the
block's parameter telescope.

### One reduction rule changed

Mini's ι step took a constructor application's fields by dropping the
**recursor's** parameter count. That is the constructor's own for every recursor
whose rules are its own type's constructors, and wrong for a nested one:
`Tree.rec_1` has `numParams = 0` and reduces on `List.cons`, whose first
argument is `List`'s parameter. It reads the owner's count now, which is Lean's
`RecursorRule.nfields` reached by another route. The same off-by-one was in
`mini/tests/mutual.rs`'s own `num_fields` helper and produced the only five
complaints the oracle made on first contact.

### The nested path can only widen what is accepted

`plan`'s test for an occurrence is syntactic — a foreign inductive applied to
parameters that mention a member — and syntactic is *wider* than `numNested`.
So `add_maybe_nested` tries the ordinary path **first**, on a scratch
environment, and specialises only if it fails. A declaration mini accepted
before is checked by exactly the code that accepted it. That makes the
invariant mechanical rather than a claim about the detector, and the corpus's
191 compared recursors are the evidence that it holds.

### What is **not** checked, and it is the whole obligation

The block that is checked is the specialised one; the declarations installed are
the restored ones, and the restoration is a **rewrite, not a derivation**.
`List Tree` and the mimic are isomorphic and not equal — `nested_roundtrip.lean`
plus `mini/tests/nested.rs` is that as a theorem the kernel *rejects*, with two
closed instances accepted as the controls. So `Tree.rec_1`'s ι rule on
`List.cons` enters the environment as an assumption transported along an
isomorphism nothing on the acceptance axis checks. The oracle says mini's rule
is the rule Lean declares; it does not say either is sound.

`--nested` is therefore a gate the corpus never sets, and zone B declines every
such declaration with `ind-spec(T: nested occurrence)`.

| file | `pairs` | `constEv` | `typeEv` | verdict |
| --- | --- | --- | --- | --- |
| `nested_shapes` (`--nested`) | 10 | **2** | 6 | accept, exit 4, 4 untranslated |
| `nested_iota` (`--nested`) | 16 | **1** | 1 | accept, exit 4, 3 untranslated |
| corpus | 218 | **218** | 218 | `accept=89 decline=2 reject=0`, unchanged |

`constEv` on a nested fixture is the count of `def`s whose value interprets, and
every one that mentions a nested type is `ind-spec(T: nested occurrence)` —
`nested_shapes`' 2 are `listOfN` and `pairOfN`, the containers used *un-nested*.
Those two are the whole of the evidence axis on this path today, and that is the
honest figure. The model has since been **written out and checked** — see
"Nested inductives: the model, written out" below — but it is not *wired*, so
this table is unchanged by it.

### Mutations

Run in a worktree with its own target directory (`--no-fail-fast`; a shared tree
has twice made a mutation look like another seat's regression). Baseline there:
`nested` 7/7, `mutual` 9/9.

| mutation | killed by |
| --- | --- |
| the ι step drops the **recursor's** parameter count again | `nested`, 5 of 7 — every ι theorem, at every nested declaration |
| the mimic members come out in the **reverse** of discovery order | `nested`, 5 of 7 |
| **every** container application is specialised, not only the ones that mention a member | `nested`, 5 of 7 — `listOfN` and `BTree.tag : List N → BTree` are what see it |
| a mimic is reused when the container's **name** matches, not the whole occurrence | `nested`'s `the_recursor_count_is_one_per_specialised_member` **and**, separately, the export oracle — `DTree`'s two copies of `List` collapse into one |
| restoring a mimic consumes **no** parameters | `nested`, 5 of 7 — and `PT α` is the only fixture that sees it; on `Tree` and `BTree` the mutation is the identity |
| `add_maybe_nested` specialises without trying the ordinary path first | **nothing.** `nested` 7/7, `designed` 13/13, `dump` 9/9, `mutual` 9/9 (oracle included), `tutorial` 12/12 |

**The last row is the finding.** The "try the ordinary path first" guard exists
because the occurrence detector is *syntactically wider* than `numNested` —
`Eq T a b` mentions `T` in `Eq`'s parameter and is not nesting — and it makes
"the nested path can only widen what is accepted" mechanical rather than
empirical. But **no declaration in any designed fixture or in the tutorial
corpus makes the detector fire spuriously**, so the guard has no measured
occupant and removing it changes nothing observable today. It is kept for the
argument, not for a fixture; anyone tempted to delete it should first write the
declaration that needs it.

The corpus this is measured over is the **91 tutorial exports plus the designed
fixtures**. `init-prelude` is not in it: it declines at a nat literal above ten
during the frontend walk, so none of its inductives — `Lean.Syntax` included —
ever reaches the kernel, with or without `--nested`.

### How far this is from `Lean.Syntax`

`Lean.Syntax` specialises to `{Syntax, Array Syntax, List Syntax}` — three
motives, seven minors, `Syntax.rec`/`rec_1`/`rec_2` — read off `init-prelude`'s
own export. That is `nested_iota`'s `BTree` shape exactly:
`{BTree, Box BTree, List BTree}`, `Box` a one-field structure over `List`, three
motives, `rec`/`rec_1`/`rec_2`, and `BTree.tag : List N → BTree` standing in for
`Lean.Syntax.ident`'s `List Lean.Syntax.Preresolved` — a container at a type
that has nothing to do with the one being declared.

So **on the acceptance axis the distance is: the shape is covered and the
declaration itself is unmeasured**, because `init-prelude` declines on large
`Nat` long before it. Nothing about nesting blocks it.

**On the evidence axis the distance is the whole of it.** `⟦Tree⟧` is not built,
so `⟦Lean.Syntax⟧` is not either. Sizing route (b) of
`LEAN3-INDUCTIVE-COMPILER.md` §8 on `Tree`, which is the smallest case:

| step | what it needs | definitional? |
| --- | --- | --- |
| `Tree := Aux (Tag.t0)`, `Tree.leaf`, `Tree.node := fun l => Aux.node (pack l)` | `mutual_aux` on the specialised block, plus `pack`/`unpack` | yes |
| `pack : List Tree → LT` by `List.rec`, `unpack : LT → List Tree` by `Aux.rec` at the tag-packed motive | synthesised, no proofs | yes |
| `Tree.rec`'s minor for `node` | `∀ a : LT, m2 (unpack a) → m1 (Aux.node a)` from `nd : ∀ a : List Tree, m2 a → m1 (Tree.node a)` — needs `pack (unpack a) = a` to **typecheck** | no, transport |
| `Tree.rec`'s minor for `cons` | `unpack (Aux.cons a b) ≡ List.cons Tree a (unpack b)` by ι | yes |
| `Tree.rec_1 := fun … t => Eq.rec (Aux.rec … (pack t)) (unpack_pack t)` | `unpack (pack l) = l` | no, transport |
| ι at `Tree.leaf` | δι | **yes** |
| ι at `Tree.rec_1`/`List.nil` | `unpack_pack nil ≡ Eq.refl` by ι, so the transport fires | **yes** |
| ι at `Tree.node` | relates `pack_unpack (pack l)` to `congrArg pack (unpack_pack l)` — a **triangle identity** | no |
| ι at `Tree.rec_1`/`List.cons` | `unpack_pack (cons a b)` is `congrArg` at a variable, so the `Eq.rec` is stuck; the transport has to be pushed through | no |

Two of the four rules come out definitionally; two are genuine synthesised
proofs, and one of those is the triangle identity of the adjoint equivalence.
Lean 3 never meets either, because it has no `rec_1` and its `Tree.rec` rule is
propositional from the start (§4 of the archaeology). Each proof then has to be
*cashed* into a TG equation, which §0 of that document says works and caveats
with "only as available as the proof's own typing" — so the synthesised
development's own interpretability, `Eq.rec` at a `Type`-valued motive included,
is the risk and is unmeasured.

**Every row of that table is measured now**, and the "unmeasured risk" in the
last sentence is measured too. See the next section: the sizing was right on all
four rules and wrong about the triangle identity, which costs nothing, and the
interpretability risk is real and has a name.

## Nested inductives: the model, written out — 2026-08-06

`mini/tests/fixtures/nested_model.lean` is route (b) built at `Tree`, as an
export. It declares **no nested inductive**: the specialised block is an
ordinary `mutual`, `Tree`/`treeLeaf`/`treeNode` are `def`s over it,
`pack`/`unpack` and both round trips are there, `treeRec` and `treeRec1` are
`def`s **at the types the export declares for `Tree.rec` and `Tree.rec_1`**, and
all four ι rules are theorems with proofs. Lean checks it at export time;
`mini/tests/nested.rs`'s `the_model_of_a_nested_recursor_is_checked` adds every
declaration of it through `kernel::add`, in about three seconds.

So the rule `mini/src/nested.rs` installs is **satisfiable**: a `Tree.rec_1` at
that type, ι-reducing on the *real* `List.nil` and `List.cons`, exists and is
built from `List.rec` and the block's own recursor. That is not the same as
being mini's interpretation of it, and the next section says what is left.

### The sizing, measured

`two_of_the_four_model_iota_rules_are_definitional_and_two_are_not` re-proves
each rule by `Eq.refl` at the fixture's own declared statement and compares the
kernel's answer against a table:

| rule | `Eq.refl` | cost |
| --- | --- | --- |
| `Tree.rec` on `leaf` | accepted | — |
| `Tree.rec_1` on `List.nil` | accepted | — |
| `Tree.rec` on `Tree.node` | rejected by the conversion check | `transportNode` |
| `Tree.rec_1` on `List.cons` | rejected by the conversion check | `transportCons` |

Two lemmas and no more, each `Eq.rec` on the round trip landing at `Eq.refl`.

**The triangle identity costs nothing, and that was not predicted.** The
transport `treeRec`'s `node` minor performs is along `packUnpack (pack a)`;
`transportNode` is stated along `congrPack (unpackPack a)`. Those are two proofs
of the same `Prop`, so **proof irrelevance** identifies them and no equation
between proofs is ever built. Lean 3 had to rewrite that stuck `eq.rec` with a
simp set (`prove_eq_rec_invertible`, archaeology §4); mini does not.

### `Gap::StuckRecursor` gets its first occupant, and it is the round trip

`mini --mutual` on the export:

```text
accept 25 declarations   uncertified: 13 const typings, 4 type typings, 3214 conversions
evidence  pairs=41  typeEv=37  constEv=28
convs     proved=46457589  gapped=3214
          convGap:stuck-recursor(S0._auxCarrier.rec)=2475
          convGap:stuck-recursor(List.rec)=709
          convGap:stuck-recursor(Eq.rec)=26
```

All thirteen missing constant typings and all 3 214 gapped conversions are
`Gap::StuckRecursor`, a variant that minted **0** over all 91 corpus exports and
whose doc comment said so and has been corrected. `unpack (pack l)` at an open
`l` is a recursor whose major premise is *another stuck recursor*: the major
δ-reduces underneath without the outer redex firing, so the expression changes
and the certificate owes a congruence over that change — which `whnf` performs
acceptance-only and does not thread. Nothing is owed to `derived/` and nothing
is a clause of §6.2.

This is the answer to the previous section's "unmeasured risk". The risk was not
`Eq.rec` at a `Type`-valued motive as such. It is that **the round trip's own
shape is the one shape the traversal does not thread**.

### Which thirteen, and the sequencing that follows

`mini --mutual --dump-theorems` names every pair. The split is not scattered:

| certified (28) | uncertified (13), all `stuck-recursor` |
| --- | --- |
| the whole block — `S0`, `S1`, their constructors, both recursors at both σ, all four `_auxRule` theorems | `treeRec`, `treeRec1`, `blockRec1`, `ndMinor` |
| `Tree`, `treeLeaf`, `treeNode` | `unpackPack`, `packUnpack` |
| `pack`, `unpack` | `iotaLeaf`, `iota1Nil`, `iotaNode`, `iota1Cons` |
| `congrPack`, `congrCons`, **`csMinor`** | `transportNode`, `transportCons`, **`treeSize`** |

**`csMinor` certifies and `ndMinor` does not**, and that pair is the diagnosis in
miniature: `csMinor`'s `unpack (S1.cons a b)` has a *constructor* major, so ι
fires and the certificate composes; `ndMinor`'s `pack (unpack b)` has a major
that is itself a stuck `S1.rec`, so it reduces underneath `List.rec` without the
outer redex firing. Ten of the thirteen name `List.rec`, two name `Eq.rec`, one
names `S0._auxCarrier.rec`.

**`treeSize` is uncertified, and that decides the order of the remaining work.**
`treeSize` is an ordinary `def` applying the model's recursor at a closed
motive — the analogue of `nested_iota`'s own `treeSize`, and the one pair on
that file which keying alone might have been expected to certify. It does not.
So **keying `⟦Tree⟧` to the model buys `0` on `nested_iota` until
`Gap::StuckRecursor` is threaded**, and building the generator first buys
nothing measurable either. The gate is the congruence, and everything else
queues behind it.

### The congruence, as a shape for the seat that owns it

`mini/src/kernel.rs`, `whnf`'s recursor arm, the branch that mints
`Gap::StuckRecursor(name)` when `stack2[major_pos] != stack[major_pos]`. The
major was reduced by the **acceptance-only** `self.whnf(…)` a few lines above,
so no certificate for `⟦m⟧ = ⟦m'⟧` exists to compose with. What is owed is that
same reduction performed by the *threaded* `whnf_conv`, and its equation lifted
through the application by congruence at the major's position — one `congr`, or
`Interp::beta_spine`'s internal lifting in one leg, so that no `ConvCompose` is
manufactured at the call site. `nested_model.ndjson` is the regression: it is
the only export in the repository that reaches the branch, and it reaches it
3 214 times.

The run costs 46 million conversions and tens of minutes, inside a 4 GB
`ulimit -v`. No test runs the binary on this fixture.

### What is discharged and what is not

Discharged: that the installed rule set is satisfiable; that the isomorphism's
price is exactly two transport lemmas; that the triangle identity is free.

Not discharged: **the keying**. `zoneb::ensure` still answers
`ind-spec(T: nested occurrence)`, so `⟦Tree⟧` is unbuilt and nothing says mini's
interpretation of the *primitive* `Tree.rec_1` is this `treeRec1`. `constEv` on
`nested_iota` is **1/16**, unchanged.

Not discharged: **generality**. The model is written out for `Tree` — depth 1,
one container, no parameters of its own. `BTree` (two *different* containers,
one of them a structure), `PT` (a parameter telescope) and `DTree` (depth 2, and
**two** packed positions in one constructor, which needs the transport lemma
folded rather than applied once) are not modelled. The construction generalises
— the motive vector is `fun _ => Sⱼ` at the root and `fun _ => occⱼ` at each
mimic, the mimic minors need no transport at all, and only a root constructor
with a packed field does — but it is not built and not measured.

### What the evidence axis still owes `Lean.Syntax`, listed

The acceptance-axis answer is unchanged: the shape is covered exactly and
`init-prelude`'s blocker is `Nat`, not nesting. The evidence axis owes five
things, and only the last is a size problem rather than a missing piece.

**They are listed in dependency order and item 4 is first in time**, by the
`treeSize` measurement above: until the `StuckRecursor` congruence lands, items
1–3 move no counter.

1. **The generator.** `nested_model` is written by hand at `Tree`;
   `Lean.Syntax` will not be. A `nested_ev.rs` emitting the tower from
   `nested::Plan` and asking `kernel::add` — the same black box `mutual_aux` is
   — with a named decline for every shape it cannot express. **Specified** in
   `MINI-DESIGN.md` §9, "The generator, specified", including the two facts the
   hand-written model taught: that the model may not reuse the export's own `T`
   and must declare `T._model.self` instead, and that `unpack`'s motive vector
   is the identity at the root and the occurrence at each mimic.
2. **The generalisations that generator needs**: several mimics of *different*
   containers, a *structure* container behind a projection, a parameter
   telescope, depth 2, and a constructor with **two** packed positions, where
   the transport lemma is folded rather than applied once.
3. **The keying.** `zoneb::ensure` answering for `T`, its constructors and each
   `T.rec_k` out of the model's own store entries instead of
   `ind-spec(T: nested occurrence)`. *This item said "a rename in the store, not
   a derivation". **That is half right and the other half is a new route** —
   traced and corrected in "The keying is a rename for typing and a new route
   for reduction" below.*
4. **`Gap::StuckRecursor`'s congruence** in the conversion path, without which
   the model certifies 28 of its own 41 pairs and no more.
5. **Cost.** 46 million conversions for the smallest model there is. Whatever
   the model of `{Syntax, Array Syntax, List Syntax}` costs, it is not that
   divided by anything.

### Mutations

The landing is a fixture, two tests and doc corrections; no source logic
changed, so the mutation table of the previous section stands unaltered. The one
new mutation is the claim the fixture's header rests on — run in a copy of the
tree with its own target directory:

| mutation | killed by |
| --- | --- |
| `Checker::is_prop_or_unit_ev` returns `None` — **proof irrelevance disabled** | `nested`, 1 of 9: `the_model_of_a_nested_recursor_is_checked`, on `iotaNode`, with `Expected definitional equality between (S1.rec.{0} …) and Eq.rec.{0 (0+1)}` |

That message *is* the triangle identity: the `S1.rec` term is
`packUnpack (pack a)`, the `Eq.rec` term is `congrPack (unpackPack a)`, and what
identifies them is irrelevance and nothing else.

**`two_of_the_four_model_iota_rules_are_definitional_and_two_are_not` survives
that mutation**, and that is the right answer rather than a hole: it measures
which rules `Eq.refl` closes, and neither of the two that do needs irrelevance.
The two tests are complementary and the mutation says which is which.

## Nested inductives: the isomorphism, generated — 2026-08-07

`mini/src/nested_ev.rs` emits the half of `nested_model.lean` that is pure
construction — the renamed block, the carrier `T._model.self`, and per mimic
`pack`, `unpack`, `unpackPack` and `packUnpack` — from `nested::Plan`, and asks
`kernel::add` about every one. **A proof it builds and the checker rejects is an
`Err`, never a declaration**; `nested.cpp:370-383`'s silent axiomatisation is the
specific thing not reproduced, and there is no path in the module where a failed
proof becomes an assumption.

This is what the restoration in `mini/src/nested.rs` stands on. That module
rewrites the mimic back to `List Tree` and its constructors back to `List`'s,
and its own header calls the rewrite *not a derivation*. The two round trips are
now theorems with proofs for every declaration the generator accepts — which is
not yet soundness, because the interpretation is not keyed to this development,
but it is no longer "isomorphic, we believe".

### What it produces, per fixture

| fixture | declaration | result |
| --- | --- | --- |
| `nested_iota` | `Tree` — one container | **6 declarations** |
| `nested_iota` | `BTree` — `Box BTree` over `List BTree`, **two different** containers, one a structure | **10 declarations** |
| `nested_iota` | `PT α` | declines, `nested model with parameters` |
| `nested_deep` | `DTree` — `List (List DTree)`, one container at two depths | **10 declarations** |
| `nested_shapes` | all four | decline, `nested model without Eq` |

Six is one block, one carrier and four for the single mimic; ten is the same at
two mimics. **`BTree` is `Lean.Syntax`'s shape** — `{Syntax, Array Syntax,
List Syntax}` against `{BTree, Box BTree, List BTree}` — and the generator
writes its isomorphism whole, including the `Box`/`List` dependency, which forces
the emission order: deeper mimics first, because `pack₀` for `Box` calls `pack₁`
for `List`.

**`PT` is the one shape here the generator does not write**, and the reason is
mechanical rather than deep: everything is written at an empty parameter
telescope, and a parameter telescope means a `p⃗` prefix on every declaration and
a shift on every occurrence. It is the named decline rather than a silent
partial.

**`nested_shapes` declines for a different reason and that is the right answer.**
It declares no `Eq`, and the round trips are equations. `nested_ev` refuses to
mint an `Eq` the export never wrote, exactly as `mutual_aux` refuses to, so all
four of its nested declarations come back with that one reason.

### `nested_deep.lean`, and the fold that had no occupant

`nested_ev`'s congruence fold transports one constructor argument at a time, and
**every nested constructor in the fixture directory moved at most one**:
`List.cons`'s head is at the root and needs no transport, `Box.mk` has a single
field. So the loop ran at most once wherever it was tested, and a fold that
handled the first position and dropped the rest would have passed everything.
`nested_shapes`' `DTree` is the shape that distinguishes them and it declines on
`Eq` before reaching the fold.

`mini/tests/fixtures/nested_deep.lean` is that shape at the smallest size, with
an `Eq`: `DTree.node : List (List DTree) → DTree`, whose inner copy's
`cons : M₁ → M₀ → M₀` has **both** fields at a mimic. It is the third-element
rule one construction along — two moving positions is the first arity that can
tell a fold from a single transport.

### Mutation

| mutation | killed by |
| --- | --- |
| `fold_congr` `break`s after the first moving position | `nested`, 1 of 10: `the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`, on **`nested_deep/DTree` alone** — `nested_iota`'s three rows and `nested_shapes`' four are unmoved |

That is the fixture doing exactly the job it was added for, and it is why the
row above is a measurement rather than a claim that the fold generalises.

### One boundary finding, self-reported

`nested_ev.rs`'s header claims the black-box rule — it emits Lean-world syntax,
asks `kernel::add`, and never names a certificate — and
`ci/check-mutual-blackbox.sh` scanned a list of **two** files by name, so for the
length of one commit that claim was unchecked. The list is three now, and the
script carries the sentence: *a new encoder is added here or its header's
boundary claim is unchecked*. The check passes on all three.

### What this does not do

It does not move a counter. `nested_iota` is `constEv` **1/16** and
`nested_shapes` **2/10**, unchanged, for the reason the previous section
measured: `treeSize` is uncertified in the hand-written model, so keying buys
`0` until `Gap::StuckRecursor` is threaded. The generator is item (2) in that
dependency order and is built ahead of item (1) so that when the congruence
lands the counters move in one step. The recursors and the ι rules on top of the
isomorphism are the rest of item (2) and are not built.

## Nested inductives: both declines closed — 2026-08-07

The generator's two named declines are gone, and neither needed the
`StuckRecursor` congruence.

### `nested_shapes` declared no `Eq`, so the fixture grew one

`mini::nested_ev` will not mint an `Eq` the export never wrote — the round trips
are equations and a fabricated `Eq` is a declaration Lean never made. That is
the module's rule and it stays. The fix was in the fixture:
`nested_shapes.lean` now declares `Eq` exactly as the other three nested
fixtures do, with a doc comment saying it is there so the four declarations
*reach* the generator. Nothing else in the file uses it.

That takes the generator from three shapes to **seven**.

| fixture | declaration | result |
| --- | --- | --- |
| `nested_iota` | `Tree` | 6 declarations |
| `nested_iota` | `BTree` — two *different* containers, one a structure | 10 |
| `nested_iota` | `PT α` — **a parameter telescope of its own** | 6 |
| `nested_deep` | `DTree` — one container at two depths | 10 |
| `nested_shapes` | `Tree` | 6 |
| `nested_shapes` | `PTree` — container **not recursive** | 6 |
| `nested_shapes` | `DTree` | 10 |
| `nested_shapes` | `BTree` — one container at **two positions in one constructor** | 6 |

`nested_shapes`' `BTree` is six and not ten on purpose: two positions at the
*same* occurrence are one mimic, because `nested::plan` keys reuse on the whole
occurrence and not on the container's name.

### The parameter telescope, and the three depth errors it cost

Every generated declaration is now `∀p⃗, …` and every value `fun p⃗ => …`. Three
depth errors were made putting it in, and **the kernel caught all three**:

1. a field type compared against the occurrence at the *telescope's* depth, when
   field `k` sits under the `k` fields before it — so `List.cons`'s tail was not
   recognised as recursive at `np = 1`;
2. the same comparison for a field at another mimic;
3. field types handed to the congruence fold at their own binder's depth instead
   of the minor's body depth.

All three are the identity at `np = 0`, which is why the whole module passed
seven shapes without them. `Gen` now names every depth — `ps`, `occ_at`,
`mem_at`, `call`, `fields_at` — and no use site writes a bare shift.

### The statement oracle, and the kill it did not make

`the_generated_round_trips_state_the_isomorphism` rebuilds all four declared
types from `nested::Plan` and compares them syntactically, and it was written
**before** the telescope for the reason above. Measured honestly: it has **no
occupant the kernel misses**. All three errors above were kernel rejections
first, and a deliberate mutation putting the `Eq`'s own type argument one depth
out is a kernel rejection too — `iso` returns `Err` and the oracle never sees
the statement.

What it did catch is **its own** depth error. Written at `np = 0`, where a
parameter is `#0` at every depth, it was wrong the first time it met `PT` and
the assertion said so. That is worth recording as the shape of the risk rather
than as a kill: it is kept for what it pins — that these four are *the
isomorphism* and not four other well-typed equations — and the header says so.

### What is left

`nested_ev` now declines only [`Reason::Indexed`], [`Reason::DependentFields`],
[`Reason::NoEq`], [`Reason::NameTaken`] and [`Reason::Polymorphic`] — and
**`Polymorphic` has no occupant**: no nested fixture is universe-polymorphic, and
the guard is there because every generated level list is written at the block's
own, which for a polymorphic declaration is not closed. It is named rather than
silently unhandled.

"Generality past an empty parameter telescope", one of the three things the
previous section lists as still assumed, is closed. The other two — the keying,
and the recursors and ι rules on top of the isomorphism — are not, and no
counter moves: `nested_iota` is `constEv` **1/16** and `nested_shapes` **2/10**
for the reason already measured, that `treeSize` is uncertified in the model and
so keying buys `0` until `Gap::StuckRecursor` is threaded.

## The keying is a rename for typing and a new route for reduction — 2026-08-07

*Corrected in place: item (3) of "What the evidence axis still owes" called the
keying "a rename in the store, not a derivation", on the strength of the model's
`def`s carrying the export's declared types verbatim. That is true of **half**
of what the keying has to do, and the half it is not true of is the half that
matters. Traced against the code rather than reasoned about.*

### Occurrence typing: a rename, and nothing more

`Checker::const_evidence` (`mini/src/kernel.rs:2629-2651`) is **name-agnostic**:
it grounds the levels, calls `miss_reason`, then `Interp::get_const(&key)` and
returns `(term, Ev::Proved(typing))`. It never looks at the `ConstantInfo` kind
and never at the `IndApparatus`. And `miss_reason` (`kernel.rs:2608-2613`)
returns `None` the moment `get_const` hits, so **an aliased entry stops any
build being attempted at all**.

`ConstInterp` is three fields (`interp.rs:64-72`) and `zoneb::store`
(`zoneb.rs:3544-3562`) is zone B's only `put_const`. So for every `def` or
theorem that merely *mentions* `T`, `T.ctorᵢ` or `T.rec_k`, keying really is
`put_const((T.rec_k, σ), get_const((T._model.rec_k, σ)).clone())`.

`T.rec` does get a first-class `ConstInterp`, contrary to what one might guess
from `deprecs` existing: `stored_or_reason_after` (`zoneb.rs:246`) routes a
`ConstantInfo::Recursor` to `recursor::ensure` (`zoneb.rs:262`), and every arm
of that ends in `zoneb::store` (e.g. `rec_dep.rs:287`, `recursor.rs:309`). The
`deprecs`/`dep_elims` tables are the *side* structures the ι rule needs, not the
interpretation.

### ι reduction: not a rename, and this is the finding

`kernel.rs`'s conversion path routes a `Recursor` head to `iota_dep::fire`, and
`iota_dep` (`iota_dep.rs:239-246`) demands `IndApparatus::dep_elims[(rec,
σ_rec)]` — the specific `define_abbrev` symbol the eliminator nest's bottom was
bound to, **with its defining axiom** — together with `stored_term` on `⟦T⟧` and
every `⟦T.ctorᵢ⟧` (`iota_dep.rs:218,233,236`) that must be *literally the same
terms the nest was built over* (`iota_dep.rs:222` and `:267` compare by
equality).

An aliased recursor has no such nest.

*This paragraph continued: "…and both `decls` and `deprecs` document themselves
as **identity, not memoisation**, so a second build mints a second family of
Replacement symbols whose theorems cannot be chained with the first's." **That
is a misreading and it is retracted.** "Identity, not memoisation"
(`interp.rs:406-414`) states the tables' *purpose* — one symbol family per
`(name, σ)` — not that they re-mint. `Interp::dep_recursor`
(`interp.rs:1004-1032`) is lookup-first, insert-once, and caches the failure
too, and `const_evidence` only calls `zoneb::ensure` on a `get_const` miss, so
`dep_elims.insert` fires once per key and a second build never happens. Checked
by the seat that owns the conversion path.*

**What is owed is a fourth arm** — the dispatch in `kernel.rs` is a fixed match
on `quot::prim_for` / `direct::clause_for` / `num_indices`, and `quot_iota` and
`rec_acc_iota` are the precedents for a route that is not `iota_dep` — **but it
is not the gate, and this is the correction that matters.**

`zoneb.rs:1960` refuses `⟦Tree⟧` outright for a nested declaration, so there is
no `Translated`, no `DepRec` and no `DepElim`, and `cur_tm`/`all_tms` are `None`
at a nested redex: it takes the existing `_ => Err(None)` arm long before any
new guard could fire. **A fourth arm buys nothing until that decline is lifted**,
and lifting it is the keying — zone B, and this seat's.

`rcompat_at` is `pub(crate)` (`quot_classes.rs:504`) and a sibling module can
call it, but it takes `qc: &QuotClause`, peels `PiShape::Prop` exactly three
times, and uses `graph_pair`/`compat_closure`. **The technique transfers; the
function does not.** *This sentence used to read "which is already one function
… and already runs on corpus rows `122` and `124`" — half right, and the wrong
half would have cost a round.* What a nested route composes is
`Interp::beta_spine` (`interp.rs:1842`, `pub`), `Interp::cond_app`
(`interp.rs:2472`, `pub`), `derived::prop::cond_elim` and
`Scopes::close(..).discharge`, all of which are general and reachable. A module
that assembles them names `Thm`, so it sits on the **evidence** side beside
`iota_dep.rs` and is *not* a black box like `nested_ev.rs`.

**And there is no way to recognise a model-backed recursor at the ι site.**
`Environment` carries only `consts`/`owners`, `nested::add` is deliberately
traceless and `Plan` is dropped; the one sound discriminator already computed
there, `owner(&cname) != owner(name)` (`kernel.rs:955-965`), **does not catch
`Tree.rec` itself**. So if the site has to know, that has to survive from
`nested::add`, and what carries it is a decision to take deliberately rather
than to discover — "traceless" was itself a choice.

### What the keying asserts, and what it must not be allowed to assert

This is the last place "isomorphic, we believe" can get back in, so it is worth
being exact.

Setting `⟦T⟧ := ⟦T._model.self⟧` does **not** say that `T` and `T._model.self`
are the same Lean constant, nor that they are convertible: they are not, and
`nested_roundtrip.lean` is the kernel refusing to identify them. What it says is
that **the primitive declarations `nested::add` installed for `T` are
interpreted by this model**. Soundness then needs exactly two things:

* every *typing* mini's kernel relies on holds of the model — which transfers
  for free **only because** the model's `def`s carry the export's declared types
  verbatim; and
* every *ι rule* mini's kernel fires holds of the model — which does **not**
  transfer for free and is the cashed theorem above.

So the keying has a soundness condition it must **assert rather than assume**:
the model constant's declared type must be syntactically the export's. That is
exactly what `the_generated_round_trips_state_the_isomorphism` checks today for
the four isomorphism declarations, and the keying site should run the same
comparison for the constructors and the recursors rather than trusting the
generator. A keying that aliased a constant whose type merely *happened* to fit
would be asserting an unproved coincidence — which is the original sin this
whole arc exists to remove.

### What it discharges, written now so only the measurement is missing

When the `StuckRecursor` congruence lands and the model certifies its own 41
pairs, the keying discharges, for every nested declaration the generator
accepts:

> `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` for `c` ∈ {`T`, every `T.ctorᵢ`, every `T.rec_k`} — the
> headline obligation `pairs − constEv`, for every pair that mentions one of
> them.

It does **not** discharge that mini's kernel's ι rule for `T.rec_k` is a rule the
model satisfies. That is one cashed theorem per rule, through the fourth arm, and
it is a separate claim with a separate certificate.

### What is still missing before the keying can be written at all

`nested_ev` builds the **isomorphism** — block, carrier, `pack`/`unpack`, both
round trips. It does not yet build `T._model.ctorᵢ` or `T._model.rec_k`, so for
the constructors and the recursors there is at present **nothing to rename to**.
That is the remainder of item (2), and it is the next thing to build: the motive
vector is `m₁` at the root and `fun b => m₂ (unpack b)` at each mimic, the mimic
minors pass through untransported, and only a root constructor with a packed
field transports — all of which the hand-written `nested_model.lean` already
spells out at `Tree`.

## Nested inductives: the constructors and the recursors — 2026-08-07

`nested_ev` now emits the whole model except the ι theorems: the block, the
carrier, `pack`/`unpack` and both round trips per mimic, **`T._model.ctorᵢ`**,
and **`T._model.rec_k` per member**. Every one goes through `kernel::add`.

| fixture | declaration | declarations emitted |
| --- | --- | --- |
| `nested_iota` | `Tree` / `BTree` / `PT α` | 10 / 16 / 10 |
| `nested_deep` | `DTree` | 15 |
| `nested_shapes` | `Tree` / `PTree` / `DTree` / `BTree` | 10 / 10 / 15 / 10 |

One block, one carrier, four per mimic, one per constructor, one per member's
recursor.

### The statements are zone A's own, by an oracle rather than by inspection

`check_recursors` compares `T._model.rec_k`'s declared type against the
`T.rec_k` that **`nested::add` installed** — after the declaration is added,
with the export's names rewritten to the model's and nothing else. It is
therefore not a restatement of the generator: a generator that produced a
well-typed recursor of some *other* type passes `kernel::add` and fails here.
All seven shapes pass, `Tree`, `BTree` and `PT` included; with the constructors
and the four isomorphism statements that is **54 statements compared**.

This is the keying's soundness condition, in place before the keying:
`⟦T.rec_k⟧ := ⟦T._model.rec_k⟧` is an alias exactly when the two are the same
statement about different constants.

### Two bugs, both named by the kernel

The major at a mimic moves along the **retraction** `unpack (pack l) = l`, not
the section — using `packUnpack` there is a type error the kernel reports as
`Bₖ` against `occₖ`. And `Mimic::ctors`' real constructors carry the *export's*
`T` in their own parameters, because they are built before the model exists, so
they need the same `T ↦ T._model.self` rewrite as every other occurrence.

### Cost

**No measured run changes.** `nested_ev`'s output is not spliced into any
pipeline yet, so nothing in the corpus or the fixtures reduces it. When the
keying splices it, the cost is the model's, and `nested_model.ndjson` is the
proxy: 3.6 GB and 30.6 M conversions, which **aborts at the 4 GB cap** once the
certificate is actually built.

*This paragraph ended "the generated tower is larger than the hand-written one
… so that figure is a floor and not a ceiling". **Measured, and it is not larger
— yet.*** Generating and `kernel::add`-ing the whole tower, expression nodes
summed over every emitted declaration:

| tower | declarations | expression nodes | generate + check |
| --- | --- | --- | --- |
| `Tree` | 10 | 896 | 0.16 s |
| `BTree` | 16 | 2 005 | 0.64 s |
| `PT α` | 10 | 1 392 | 0.45 s |
| `nested_model.lean`, hand-written | 25 | 2 954 | — |

So the generated `Tree` tower is **under a third** of the hand-written model,
and `BTree`'s is two thirds of it. The difference is exactly what is not emitted
yet: `nested_model.lean` carries the four ι theorems, the two transport lemmas,
two `congr` lemmas and a use site, and the generator carries none of them. It
does carry what the hand-written file does not — every mimic and every
constructor — and that is already counted above.

The honest reading is therefore: **`nested_model`'s 3.6 GB is a floor for `Tree`
and nothing is yet known about `BTree`.** `BTree` has three recursors to
`Tree`'s two, two mimics to its one, and its ι theorems will need a transport at
`Box.mk` as well as at `List.cons`, so the ι half will not be a constant factor.
The number to watch when the theorems land is `BTree`'s, and it should be taken
before anything splices it.

### What is left

Only the ι theorems, and then `zoneb.rs:1960`.

### The ι theorems, specified — and where the cashing may not go

What is left in `nested_ev` is one theorem per rule of each `T._model.rec_k`,
stated exactly as `nested_model.lean` states its four:

```text
∀ p⃗ M⃗ S⃗ f⃗,  Eq (Mₖ (c f⃗))  (rec_k p⃗ M⃗ S⃗ (c f⃗))  (rhs p⃗ M⃗ S⃗ f⃗)
```

with the rule's constructor and right-hand side read off `Bₖ.rec`'s own
`ConstantInfo::Recursor::rules` and restored through the table the recursors
already use. The statements are therefore free; **the proofs are the work**, and
they split the way the hand-written file splits:

* a rule whose constructor has **no packed field** is `Eq.refl` — `leaf`, and
  `List.nil` because `unpackPack List.nil` ι-reduces to `Eq.refl` and the
  transport in `rec_k` disappears;
* a rule whose constructor **has** one is a transport commutation, one per
  packed position, proved by `Eq.rec` on the round trip landing at `Eq.refl`,
  with **proof irrelevance** closing the mismatch between the `packUnpack (pack
  f)` the recursor transports along and the `congr pack (unpackPack f)` the
  lemma is stated along.

The second kind is a *nested* fold — the equation's two sides each contain
transports, and each position has to move both the value and its induction
hypothesis — so it is `fold_value` and `fold_congr` composed rather than either
alone. That is the piece to size carefully rather than start late.

**The boundary holds through all of it.** A rule is a Lean theorem proved by a
Lean proof term, so emitting it names no `Thm` and
`ci/check-mutual-blackbox.sh`'s allowlist does not move. Turning it into
`⊢ ⟦lhs⟧ = ⟦rhs⟧` is a different module — evidence-side, beside `iota_dep.rs`,
composing `beta_spine`, `cond_app`, `cond_elim` and `discharge` — and
`nested_ev.rs`'s header now says so, because the temptation to cash where the
proof term already sits is the obvious way to lose the invariant.

## Nested inductives: the ι theorems, one lemma in and the shape of the rest — 2026-08-07

`congrPack_i : ∀p⃗ l₀ l, Eq l₀ l → Eq (packᵢ l₀) (packᵢ l)` is emitted per mimic
and typechecks, for all seven shapes. It is small and it is not decoration: the
ι rule of a **root** constructor with a packed field has, on its left, the
transport `recₖ`'s minor performs — along `packUnpack (pack f)` — and proving it
means `Eq.rec` on `unpackPack f`, whose motive has to name a proof of
`Eq (pack (unpack (pack f))) (pack x)` for the abstracted `x`. Only a
*congruence of `pack`* is that. Proof irrelevance then identifies the two at
`x := f`, which is where the triangle identity would otherwise have to be proved
as an equation between proofs.

| tower | declarations | expression nodes | generate + check |
| --- | --- | --- | --- |
| `Tree` | 11 | 988 | 0.17 s |
| **`BTree`** | **18** | **2 189** | **0.64 s** |
| `PT α` | 11 | 1 522 | 0.46 s |

`BTree` is `Lean.Syntax`'s shape and that is the number to watch. Against the
hand-written `nested_model.lean` (25 declarations, 2 954 nodes, one mimic, no
constructors, but *with* its four ι theorems and two transport lemmas) the
generated `BTree` tower is 74 % of the size with none of the ι half written.

### The finding: the ι proof cannot be a standalone lemma applied

The obvious shape — state one helper per rule with `l₀ l h u⃗` as binders, prove
it by `Eq.rec` landing at `Eq.refl`, and apply it — **does not avoid the hard
part**, and this is worth knowing before starting.

Instantiating the helper needs the induction hypotheses `u⃗`, and at position `x`
the hypothesis is `Bᵢ.rec p⃗ M''⃗ S''⃗ (packᵢ f_x)` — the *block's* recursor at the
**composed** motive vector. **No model constant denotes it.** `T._model.rec_i`
is that term already transported (`Eq.rec … (Bᵢ.rec … (pack major)) …`), so it
has the wrong type: `Mᵢ f_x` where the helper wants `Mᵢ (unpackᵢ (packᵢ f_x))`.

So the ι builder needs `M''⃗` and `S''⃗` **at the ι theorem's own binder depth**,
which today are built inline inside `Gen::rec_decl` over closures on *its* depth.
The remaining work is therefore, in order:

1. factor `rec_decl`'s motive vector and minor vector into depth-parameterised
   helpers, shared with the ι builder — mechanical, and the only reason it is
   not already done is that `rec_decl` was the only caller;
2. `congrCtor` per mimic rule with a packed position — congruence of the *real*
   container constructor, the same lemma one level out, needed because a
   mimic's rule transports along `unpackPack (c f⃗)` rather than along `pack`;
3. the rules themselves: `Eq.refl` where the constructor has no packed field
   (`leaf`, and `List.nil` because `unpackPack List.nil` ι-reduces to `Eq.refl`
   and the transport in `recₖ` disappears), and otherwise `Eq.rec` on
   `unpackPack f_x` at a motive written in the **reduced** form — the kernel
   converts it against the declared statement, which is what lets the proof be
   built without reducing the recursor by hand.

`DTree`'s inner `cons : M₁ → M₀ → M₀` has **two** packed positions and will need
(3) folded rather than applied once; it is the same axis `nested_deep.lean` was
added for, and it is the one shape that will decline if the fold is written for
one position only.

## Nested inductives: the ι half, and the one declaration that does not finish — 2026-08-07

*Supersedes the first version of this section, which reported the ι half as a
pass/fail abort. Re-taken on `0550b67`, and with `MINI_CONV_TRACE` the abort is
now a number and a name. **No bisection was needed** — one instrumented run gives
the whole profile, which is what `#107` was for.*

### The two rows, on `0550b67`

| `Tree` tower | verdict | `constEv` | `gapped` | conversions | wall |
| --- | --- | --- | --- | --- | --- |
| isomorphism + both recursors | `accept` | **32/32** | **0** | 3 235 984 | 48 s |
| + the ι half | **abort at the 4 GiB cap** | — | — | **> 6 607 199** | 439 s |

The proof-irrelevance fix moved the first row **−24.7 %** (4 299 788 → 3 235 984)
and **−18.6 %** in wall — more than the corpus-wide −19.9 %, which is the right
direction for a tower that is almost entirely equations.

### It jumps, and it jumps at one declaration

Conversions charged to each declaration of the hand-written model, from the
trace:

| declaration | conversions |
| --- | --- |
| everything up to `treeNode` (block, carrier, `pack`, `unpack`) | < 14 000 each |
| `unpackPack` | 503 708 |
| `packUnpack` | 664 212 |
| `congrPack` | 18 796 |
| `congrCons` | 10 518 |
| **`transportNode`** | **1 653 987** |
| `transportCons` | 583 898 |
| `ndMinor` | 612 324 |
| `csMinor` | 77 777 |
| `treeRec` | 110 000 |
| `blockRec1` | 129 233 |
| `treeRec1` | 610 494 |
| `iotaLeaf` | 774 186 |
| `iota1Nil` | 822 843 |
| **`iotaNode`** | **does not finish** |

**The growth is not smooth and the culprit is named.** `iotaLeaf` and
`iota1Nil` are the two rules whose constructors have **no packed field** — their
proofs are `Eq.refl` — and each completes at about 0.8 M. `iotaNode` is the
first rule **with** a packed field, whose proof is `transportNode` applied, and
it exhausts 4 GiB on its own.

### Two things that follow, and the second is the more useful

**An `Eq.refl` ι rule is not cheap.** `iotaLeaf` costs 774 K conversions to
check a proof that is one constant. The cost is not the proof term; it is the
kernel *converting the two sides of the stated equation*, which is the whole ι
computation. So the ι half was never going to be free even where the proof is
trivial, and a generator emitting them cannot avoid this by being clever about
proofs.

**`#102` is the live hypothesis and the shape fits.** `transportNode` is
`Eq.rec` over a round trip, and a round trip is a recursor whose subject is
another recursor — the compounding shape. And this tower reaches
`whnf_conv`'s `Proj` arm by construction: `mutual_aux` encodes the block with an
`_auxCarrier`, so the members are projected out, and every reduction through a
member goes through a projection whose subject is itself being reduced. That is
exactly the arm where the subject is reduced twice, guarded so the doubling
fires **when the reduction is non-trivial**. It is a hypothesis, not a
conclusion — but it is testable by re-taking `iotaNode`'s row after `#102`, and
that is one run rather than nine.

### What is not yet known

Whether the cost scales with **nesting depth**, which is what would distinguish
`#102`'s 2^depth from ordinary bulk. `nested_deep`'s `DTree` gives a depth-2
comparison, but only for the *generated* tower — the hand-written model exists
at `Tree` only, so the comparison needs the ι theorems emitted first. Recording
it as the measurement that decides the question rather than guessing at it.

### `#102` was the wrong hypothesis, and the export says so in one grep — 2026-08-07

I argued that this tower reaches `whnf_conv`'s doubled `Proj` arm by
construction, on the reasoning that `mutual_aux` encodes the block behind an
`_auxCarrier`, so members are projected out and every reduction through one
goes through a projection whose subject is itself being reduced. **That is
wrong, and the one-run test after `f683e6a` is a flat line.**

| row | on `0550b67` | on `f683e6a` (`#102` fixed) |
| --- | --- | --- |
| isomorphism half | 3 235 984 convs, 48 s, 32/32 | **3 235 984 convs**, 47 s, 32/32 |
| ι half, at `iotaNode` | > 6 607 199, abort at 439 s | **> 6 607 199, abort at 439 s** |

Not a large drop that still exceeds the cap — **identical to the digit**, on
both rows.

The reason is that `nested_model.ndjson` contains **no `proj` node at all**:

```text
app 507, ie 199, forallE 163, in 146, const 43, bvar 12, def 11, thm 10, …
```

`S0._auxCarrier` is a definition by recursion, not a structure field, so the
encoding never builds an `Expr::Proj` and the arm `#102` repaired is never
entered. **The check that would have caught this before I proposed the
hypothesis is one grep of the export for `proj`**, and I did not run it — the
name `_auxCarrier` was allowed to stand in for evidence about the term shape.

### So the ι half's cost is still unexplained, and one suspect is left

Of the three super-linear defects, two are now measured against this tower.
Proof irrelevance (`0550b67`) moved the isomorphism half **−24.7 %**; `#102`
moved **nothing**. What remains is **`#101`** — `infer_type` re-entering itself
from `beta_premise` and `def_eq_ev`, measured at 84 % of conversions with 151×
duplication of α-canonical judgements on `proj_reduced_carrier`. That is the
only remaining candidate that is *known* to be super-linear, and it is untested
here.

The shape of the profile is at least consistent with it: an `Eq.refl` ι rule
costs 774 K conversions to check a proof that is one constant, which means the
cost is the kernel converting the two sides — many inferences over the same
subterms, which is exactly the duplication `#101` describes.

**But that is a hypothesis again, and this section is the reason to say so
plainly rather than assert it.** The test is the same one run, after `#101`
lands.

## Nested inductives: the ι rules, generated and proved — 2026-08-07

`nested_ev` emits **one theorem per rule of every `T._model.rec_k`**, with a
proof, through `kernel::add`. **Nothing declines**: all eight nested
declarations in the fixture directory get all thirty-six of their rules, and
`Reason`'s five guards keep their arguments and gain no occupant.

| fixture / declaration | mimics | rules | declarations | expression nodes | generate + check |
| --- | --- | --- | --- | --- | --- |
| `nested_iota` / `Tree` | 1 | 4 | 11 → **15** | 988 → **2 712** | 0.17 s → **10.3 s** |
| `nested_iota` / **`BTree`** | 2 | 6 | 18 → **24** | 2 189 → **5 531** | 0.64 s → **38.0 s** |
| `nested_iota` / `PT α` | 1 | 4 | 11 → **15** | 1 522 → **3 940** | 0.46 s → **26.5 s** |
| `nested_deep` / `DTree` | 2 | 6 | 17 → **23** | — → **7 765** | — → **91.1 s** |
| `nested_shapes` / `Tree` | 1 | 4 | 11 → 15 | 2 712 | 10.4 s |
| `nested_shapes` / `PTree` | 1 | 3 | 11 → **14** | 1 713 | 2.8 s |
| `nested_shapes` / `DTree` | 2 | 6 | 17 → 23 | 7 583 | 89.3 s |
| `nested_shapes` / `BTree` | 1 | 3 | 11 → **14** | 3 339 | 16.6 s |

`BTree` is `Lean.Syntax`'s shape and **38.0 s is the number that had never been
taken** — 59× the isomorphism half alone, for 2.5× the expression nodes. The
`test` profile, `opt-level = 1`, and the machine was shared; the node counts are
exact and the seconds are the right order of magnitude and not more.

### The proof, and the two shapes it takes

The statement is free, as specified: the rule `Bₖ.rec` obeys is
`minor f⃗ ih⃗` with one hypothesis per field at a member, and the theorem binds
the recursor's own `p⃗ M⃗ S⃗` with the constructor's **export-side** fields on the
end. The proof splits exactly where the hand-written `nested_model.lean` splits:

* **no packed field → `Eq.refl`.** `pack`/`unpack` never appear, the block's own
  ι rule fires and the two sides are one term. **Nineteen** of the thirty-six —
  every constructor with no field at a mimic — counted off the fixtures rather
  than instrumented: `Tree` 2 of 4 (twice), `BTree` 3 of 6, `PT` 2 of 4,
  `DTree` 3 of 6 (twice), `nested_shapes`' `PTree` 2 of 3 and its `BTree` 2 of
  3.
* **a packed field → a fold**, one `Eq.rec` on `unpackPackᵢ f_x` per packed
  position, from a base at which every position is still at
  `unpackᵢ (packᵢ f_x)` and both sides are the same term. Each step moves the
  position **twice**: the field value, and the induction hypothesis for it from
  `Bₘ.rec p⃗ M''⃗ S''⃗ (packᵢ f_x)` to `T._model.rec_m p⃗ M⃗ S⃗ f_x`, which is that
  term already transported.

The motives hold both sides in their **reduced** form — the recursor unfolded,
the block's rule fired, the minor β-reduced — so the kernel converts that
against the declared statement rather than this module reducing a recursor by
hand.

### `congrCtor` was specified as a declaration and is inline instead

Step (2) of the previous section's plan was `congrCtor` per mimic rule with a
packed position, the congruence of the *real* container's constructor. It is
needed and it is exactly where predicted — a mimic's rule transports along
`unpackPackᵢ (c f⃗)`, and abstracting `f_x` leaves the reduct's own proof at the
wrong type — but it is **not a declaration**. Each step of the fold moves a
*different* position of the same constructor, so a named lemma would need one
per position; `Gen::fold_congr` already builds precisely that congruence and is
called inline. `congrPack_i` stays a declaration because the root's fold moves
`pack` and not the constructor, and one lemma covers every position.

Proof irrelevance closes both, as at `nested_model.lean`: the fold's congruence
and the `packUnpack (pack f)` / `unpackPack (c f⃗)` the reduct carries are two
proofs of one `Prop`, and the triangle identity is never built.

### The cost, and what it is not

`generate + check` above is the **acceptance** axis — `nested_ev::iso` building
the tower and `kernel::add` checking every declaration of it. It is not the
evidence axis: `nested_ev`'s output never reaches the binary, so no conversion
certificate is asked for and `MINI_CONV_TRACE` has nothing to say about it.

Re-taken on `5d8b9a5` for the hand-written model, which *is* on the evidence
axis, and the ι half now finishes:

```text
nested_model.ndjson  accept 25 declarations  uncertified: 4 const typings, 30 conversions
```

against the 13 const typings / 4 type typings / 3 214 conversions recorded when
`Gap::StuckRecursor` was first found. The per-declaration trace says where the
7.22 M conversions go:

| declaration | conversions | running total |
| --- | --- | --- |
| `iotaLeaf` | 137 066 | 1 018 881 |
| `iota1Nil` | 150 270 | 1 169 151 |
| `iotaNode` | 161 424 | 1 330 575 |
| **`iota1Cons`** | **2 506 538** | 3 837 113 |
| **`treeSize`** | **3 282 145** | 7 119 258 |

The two `Eq.refl` rules cost 137 K and 150 K each — **an ι rule whose proof is
one constant still costs six figures**, because the cost is the kernel
converting the two sides and not the proof term. `iota1Cons`, the rule with a
packed position at a mimic, is 16× either of them, and the single *use* site
`treeSize` is larger than all four rules together.

### The parameter telescope costs more than the second mimic

`PT α` has one mimic and four rules, the same as `Tree`, and **2.6×** the
acceptance-axis cost. The difference is its one parameter: every occurrence,
every `pack`, every `unpack` and every recursor application carries `p⃗`, and
every one of them is a shift. That is the axis `PT` was added for showing up in
the cost and not only in the correctness.

### Mutations

Five, on `mini/src/nested_ev.rs`'s ι half, `--no-fail-fast`, executed-test
counts read rather than exit codes:

| mutation | killed by |
| --- | --- |
| the fold stops after the **first** packed position | `nested`, 2 of 11 — see below |
| the induction hypothesis at a packed field is `T._model.rec_0` instead of `T._model.rec_m` | `nested`, 2 of 11: `nested_iota/Tree` is `Err("nested model shape")` at once |
| the minor index drops the block-wide member offset (`j`, not `minor_base + j`) | `nested`, 2 of 11 |
| the occurrence's arguments un-shifted at a mimic rule's constructor — **the identity at `np = 0`** | `nested`, 2 of 11: `nested_iota/PT` **alone**, 116 statements → 104 |
| the fold step's motive binds `Eq y x` with `y` un-shifted past its own binder | `nested`, 2 of 11: `nested_iota/Tree` at once |

**The fold's kill names both sides of its case split**, and that is the row
worth reading. `the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`
stops at the first bad row — `nested_deep/DTree` — but
`the_generated_round_trips_state_the_isomorphism` skips a tower that declined
and counts what is left: **116 statements → 67**, and 116 − 67 = 49 is exactly
`nested_deep/DTree` (19) + `nested_shapes/DTree` (19) + `nested_shapes/BTree`
(11). The first two are the *mimic*-side occupant, `M₀.cons : M₁ → M₀ → M₀`; the
third is the **root**-side one, `BTree.node : Pair BTree → Pair BTree → BTree`.
`nested_iota`'s three towers are untouched, which is the sentence
`nested_deep.lean`'s header makes: every other nested constructor in the
directory moves at most one argument.

**The `np = 0` row is the same measurement on the depth axis.** Dropping the
shift on the occurrence's arguments is the identity on `Tree`, `BTree` and
`DTree`, whose occurrences are closed; only `PT α` sees it, and it is the only
row of the sweep that kills at one tower and leaves the other seven standing.
Three of this project's silent wrong terms were shifts of exactly that
description, and it is why every depth in this module is named.

### The statement oracle, extended

`mini/tests/nested.rs`'s `check_iotas` rebuilds every emitted ι statement from
the rule the **installed** `T.rec_k` carries — restored to the model's names,
with the constructor's field telescope read off the recursor's own major type
rather than off the plan — and compares it syntactically. The argument is
`check_recursors`' one level down: `kernel::add` says the proof proves the
statement, and a generator stating a different well-typed equation would satisfy
it.

**It has no kill of its own, and that is reported rather than assumed.** Every
mutation in the table is killed by `kernel::add` first — the ι theorem's
statement and its proof are built from the same `Rule`, so a mutation that moves
one moves the other and the two stop agreeing before the comparison is reached.
That is the same answer `check_iso_statements` gives about itself, and it is
kept for the same reason: what it pins is that these are *the export's rules*
and not thirty-six other well-typed equations, which no amount of typechecking
says.

One thing the extension had to fix in the table it shares with
`check_recursors`: a recursor's *type* never mentions another recursor, so
rewriting `T.rec_m` to a constant **at no levels** was invisible; a rule's
right-hand side names `T.rec_m` at the motive universe on every recursive field,
and the table now carries the level list.

### What this does not move

`nested_iota` is `constEv` **1/16** and `nested_shapes` **2/10**, `unsealed = 0`,
`gapped = 0` — unchanged, and unchanged for the reason three sections ago
measured rather than for a new one. `nested_ev::iso` has no caller outside
`mini/tests/nested.rs`; the binary never builds a tower, so the corpus and both
nested fixtures cannot move until the keying lands. The remaining work is
`zoneb.rs:1960` and, behind it, `Gap::StuckRecursor`.

## Nested inductives: the keying and the splice — 2026-08-07

**`⟦T⟧` is the generated model's carrier**, and it is that because a side table
says so. `mini/src/nested_splice.rs` runs immediately before
`mutual_aux::expand`, puts `nested_ev::iso`'s development into the declaration
list ahead of the declaration it models, and fills
`IndApparatus::model_of : (Name, σ) ↦ Name`. `zoneb::ensure` reads it before the
store test and before `build`.

### The two counters, against the prediction on record

| fixture | before | predicted | after |
| --- | --- | --- | --- |
| `nested_shapes` | `constEv 2 / pairs 10` | 10/10 | **`constEv 81 / pairs 81`** |
| `nested_iota` | `constEv 1 / pairs 16` | 16/16 | **`constEv 103 / pairs 117`** |

`unsealed = 0`, `lazyFills = 0`, `untranslated declarations = 0` on both.

**The denominator moved, and that is not a cheat.** `Ledger::run` opens a pair
for every `Def` in the list, and the model's declarations are `Def`s; the ten
and the sixteen are still there and now certify. `nested_shapes` is complete —
its `waiting` set is empty.

**`nested_iota` is fourteen short and the fourteen are named.** They are exactly
the file's fourteen `rfl` theorems, and each waits on
`recursor(T.rec_k: iota: the recursor's arity or its declaration disagree)` —
the **ι dispatch arm**, which is a separate piece and was never this one's.
`iota_dep::fire`'s first check is `args.len() != np + 1 + n + 1`, and a nested
recursor fails it before anything else: `Tree.rec` binds two motives and four
minors, so a redex has seven arguments where that arity expects four. Nothing
about the fourteen is the keying's: `⟦T.rec_k⟧` is in the store for all seven
recursors, `untranslated eliminators = 0`, and both endpoints of every redex
interpret.

So the prediction was right about `nested_shapes` and wrong about `nested_iota`,
in the direction the brief said to report: the residual is one named piece, and
it is the fourth.

### Why the keying is a table and cannot be a name

`nested_keying.lean` is the new fixture and it is the discriminator: two nested
declarations of one shape, and the file itself declares `UTree._model.self` at a
type that has nothing to do with `UTree`. `nested_ev::iso` answers `NameTaken`,
nothing is keyed, and `⟦UTree⟧` waits on
`ind-spec(UTree: nested model name taken)`. Under `⟦T⟧ := ⟦T._model.self⟧`
spelled as a name rule the file's own definition is in the store, `⟦UTree⟧`
resolves to `⟦N⟧`, `utreeTy` certifies against a model nobody built, and every
counter reads as if it worked. That is the `_auxCarrier` failure one level up.

The fixture is also the fast inner loop: 9 s and 68 000 conversions against
`nested_shapes`' 1m40 and `nested_iota`'s 2m18.

### Three measurements decided the shape, and each refuted a first attempt

**1. Spliced *is* interpreted.** `Ledger::run` gives a `Def` with no schedule
entry a pair at the all-zero σ, so "splice the model and let the schedule decide
what to interpret" is not a thing. The model is spliced only as far as
`mutual_aux::demand_over`'s fixpoint reaches from the keyed constants.

**2. The pre-pass pads, and keying off the padding is what blew the memory.**
`checker::instantiations::compute` closes its demand and then defaults: *"a
declaration nothing demands is still checked, once per entry of
`DEFAULT_LEVELS`"*. So `T.rec` is scheduled at `[0]` and `[1]` in every file
that declares a nested type, whether or not anything eliminates one. Seeding the
model from the schedule therefore pulled in the whole ι tower, twice, in a file
whose two `def`s never mention a recursor: `nested_keying` was past 950 000
conversions and out of 4 GB after nine minutes. The σ are read off the file's
own declarations instead (`applied_at`, one sweep, no closure and no padding),
and the same file is 68 000 conversions in nine seconds.

*That padding is right where it is.* It exists so that a declaration nothing
reaches is still **checked**; a model exists so that a use site can **read** it,
and a σ no use site names is a model nobody will read.

**3. The ι theorems cost more than the rest of the arc put together, and they
are not seeded.** With them in, `nested_iota` was at **43.7 million conversions
and 6 GB after fifteen minutes**, still at declaration 65 of about 80; without
them the same file is **6.0 million and 2m18s**. Inside `Tree`'s four rules the
split is sharp:

| rule | proof | conversions |
| --- | --- | --- |
| `iota_0_0` (`Tree.leaf`) | `Eq.refl` | ~150 000 |
| `iota_0_1` (`Tree.node`) | transport | 5 000 000 |
| `iota_1_0` (`List.nil`) | `Eq.refl` | ~150 000 |
| `iota_1_1` (`List.cons`) | transport | 13 700 000 |

and `gapped` goes 0 → 30 → 109 across exactly those two. **The expensive
conversions are the ones that fail**, at `eq_cash`'s own recorded residual —
#90(b), a transport that must be *reduced* rather than compared, whose small
witness is `transport_through_eq_rec.lean` at 21 509 conversions. Paying tens of
millions of conversions to produce gaps, before the consumer that would read
them exists, is a cost with no counter behind it, so the seeding is three lines
left for whoever wires the arm. This is #110 with a number.

### What `zoneb.rs:1960` was protecting, and why it stays

The `nested occurrence` arm of `ctor_spec` is the only thing between zone B and
a recursion with no bottom: `Checker::infer_type` on a self-mentioning field
type reaches `const_evidence` → `miss_reason` → `zoneb::ensure` on the
declaration whose carrier is being built. It was **not** lifted and must not be.
What changed is that a nested declaration no longer reaches it — `ensure` routes
to the model first — and the model route is safe from that recursion for a
*different* reason: it reads a constant already in the store and builds no
carrier, so there is no half-built declaration to come back to. Two arguments,
not one restated.

The arm still has an occupant: `constType β (T p⃗)`, the field whose occurrence
reduces away. `nested::plan` answers `Ok(None)` for it — it is not nested — so
it never had a model to be keyed onto.

### Two lazy fills per model, and one more, both closed

`lazyFills` went to 2 per model and then to 1 on `nested_iota` before the two
loops that close it, and both were the splice failing to predict a σ:

* `_auxTag.rec` and `_auxCarrier.rec`, inside the block's own `mutual_aux`
  encoding. `expand` emits a `def` for every member recursor whether or not
  anything demands it, and the demand walk reaches them only through `rec_k`.
  **Everything spliced is scheduled**, at the all-zero σ if nothing else.
* `Eq.rec.{0,1}` — `Gen::rec_decl`'s transport is an `Eq.rec` at the motive
  level over the occurrence's, and no declaration of the file uses that pair.
  `mutual_aux::demand`'s rule that "a constant from the surrounding file is
  already scheduled by the file's own pre-pass" does not survive here: the term
  that needs the σ did not exist when the pre-pass ran. The model's foreign
  demands are added too, and `mentioned_after` is what makes that safe — every
  constant the model names is already settled strictly before the declaration it
  models, so the entry is discharged ahead of the model.

### What did not change

The corpus: no tutorial export declares a nested inductive, `splice` finds
nothing, `Spliced::nested` is empty and the apparatus is not even built for it.
`kernel/`, `derived/`, the black-box allowlist's rule and its self-test.
`nested_splice.rs` joins that allowlist — it is the file that *produces* the
keying, so if any file in the pipeline were going to need to read a `Term` it
would be that one; it does not, and `zoneb::model_alias` is where a certificate
is first touched.

### The mutations

Eight, against the two fast tests (`nested_keying` at 9 s, `nested_shapes` at
1m40). The executed test count is read out of the harness's own summary rather
than classified from the log: `cargo test` prints `error: test failed` at line
start, and a `^error:` classifier reads every kill as a compile error.

```text
KILLED   a missing `model_of` entry falls through to the class-(T) walk
KILLED   key on the name `T._model.self` instead of on the table
KILLED   never recognise a nested declaration, so nothing is keyed
KILLED   splice the model *after* the declaration it models
KILLED   let `fill_declaration` use its own name list, losing `T.rec_1`
KILLED   drop the σ from a recursor's key
SURVIVED carry the model's defining equation onto the export's constant
SURVIVED drop the dependency-order check
```

The first is the one that decides whether the discriminator is real. Both
survivors are recorded with their reason in `nested_splice.rs`'s header: the
`defeq` one is unreachable by construction (a primitive inductive and a
primitive recursor have no δ step, so the equation is never consulted), and the
order check has no occupant in the fixture set but is what the foreign-demand
loop's safety argument is stated in terms of.

## Nested inductives: the fourth ι dispatch arm — 2026-08-07

**The rules fire with a certificate.** `mini/src/iota_model.rs` is the arm
`MINI-DESIGN.md` §"the keying is a rename for typing and a new route for
reduction" owed: a sibling of `iota_dep::fire` at the same site in
`Checker::whnf_conv`, selected on `IndApparatus::nested` — the same membership
`zoneb::ensure` routes the declaration's *interpretation* on — and answering out
of a second table, `IndApparatus::model_iota : ((T.rec_k, σ), ctor) ↦ theorem`,
that `nested_splice::splice` fills beside `model_of` and from the same source.

### The counters

| fixture | before | after |
| --- | --- | --- |
| `nested_shapes` | `constEv 81 / pairs 81` | **81 / 81**, unmoved |
| `nested_keying` | `constEv 20 / pairs 22` | **20 / 22**, unmoved |
| `nested_iota` | `constEv 103 / pairs 117` | **`constEv 117 / pairs 124`** |
| `nested_iota_arm` *(new)* | — | **`constEv 34 / pairs 36`** |

`unsealed = 0`, `lazyFills = 0`, `untranslated declarations = eliminators = 0`
throughout. `nested_iota` is **8.1 M conversions in 3m30** against 6.0 M and
2m18, with `gapped = 112` — fourteen to eighteen conversions per declining rule
and nothing else. The denominator moved by the seven ι theorems the splice now
seeds, and all seven certify, which is the other half of saying the seeding is
sound.

### What the obvious arm did, measured, before the one that works

The plan on record was "`eq_cash::cash` applied to the rule theorem at the
redex's own arguments". **It does not type-check, and the failure is not
incidental.** Written that way the arm produced

```text
waiting:classifier = 7      mini-bug = 7      convGap:classifier = 104
```

every one of them `eq_cash.rs:236`, `c.infer_type(proof)`. The model's theorem
binds `M₀ : T._model.self → Sort v` and the redex's motive is `m1 : T → Sort v`;
`T` is a primitive `ConstantInfo::Inductive` and `T._model.self` a `def` over the
specialised block, so Lean has no conversion between them — which is exactly the
separation `nested_splice.rs`'s header keeps *on purpose*. "The model's `rec_k`
and the export's are the same statement about different constants" is true of
the statement and false of the type, and `eq_cash`'s own tests never saw it:
they run over `nested_model.lean`, a hand-written model with **no** nested
declaration, where there is one world and no export/model split.

In set world there is nothing to convert: `zoneb::model_alias` stores one term
under both keys, so `⟦T⟧` **is** `⟦T._model.self⟧` and the redex's motive is
already a member of the domain the theorem's nest asks for. So the arm walks the
nest at the interpretation — `Interp::cond_app` once per argument, which is
`Checker`'s own `App` clause with its Lean `assert_def_eq_as` replaced by the
**stronger** demand that the two interpretations be equal on the nose. That
demand is the keying, stated as a check; a declaration where it fails declines at
`DOMAIN`.

`eq_cash` is split for it: `cash_stmt` is `cash` without step 1, taking a
membership the caller already holds and the statement it is about. The arm hands
it the same equation spelled in the **export's** constants — the redex on the
left, `whnf`'s own right-hand side on the right — and nothing is assumed by the
substitution, because step 4's `retarget_set` refuses unless the `Eq` nest those
build *is* the membership's own set.

### Seven rules fire and seven decline, and the split is not the fixture's

All fourteen of `nested_iota`'s theorems are `rfl` and Lean's kernel checked all
fourteen. What differs is the **model's** proof of the corresponding rule:
`nested_ev`'s `Rule::value` is `Eq.refl` wrapped in one `Eq.rec` per field the
pack/unpack fold has to move, so a constructor with no field at a mimic gets a
reflexivity proof and one with a field gets a transport.

| rule | model's proof | seeded | fires |
| --- | --- | --- | --- |
| `Tree.leaf`, `List.nil`, `BTree.leaf`, `BTree.tag`, `List.nil`, `PT.leaf`, `List.nil` | `Eq.refl` | yes | **yes** |
| `Tree.node`, `List.cons`, `BTree.node`, `Box.mk`, `List.cons`, `PT.node`, `List.cons` | transport | no | no, by name |

The seeding is that split and it is a **cost decision with a number**. Seeding
all fourteen was measured from `nested_splice` at **43.7 M conversions and 6 GB
after fifteen minutes**, still at declaration 65 of about 80, with `gapped`
0 → 30 → 109 across the two transporting `Tree` rules alone (5.0 M and 13.7 M).
Seeding the seven reflexive ones costs **2.1 M** (6.0 M → 8.1 M) and 1m12.

**And the seven left out could not have fired anyway.** Their proofs go through
`#90(b)` — a transport that must be *reduced* rather than compared, witnessed
minimally by `transport_through_eq_rec.lean` at 21 509 conversions — so their own
constant typings are `no-endpoint` and there is nothing for `eq_cash` to read.
`eq_cash`'s `MODEL_IOTA` table is that fact on the hand-written model, already
asserted: `iotaLeaf` and `iota1Nil` cash, `iotaNode` and `iota1Cons` do not. So
the seeding leaves out exactly the rules the arm could not serve, and it buys no
conversion that would have certified.

`refl_proved` is the discriminator, read off the **value** of the declaration
this pass built and not off its name — `iota_k_j` says which rule it is and
nothing about whether it transports. When `#90(b)` lands that guard is the one
line to widen, and the number to re-measure is the 5.0/13.7 M above.

### `nested_iota_arm`, and why a fourteenth fixture

`nested_iota` is three and a half minutes. The arm's two answers are separated
by one nested declaration: `nested_iota_arm.lean` is `Tree`, its two recursors
and all four of its rules — two the model proves by `Eq.refl` and two it
transports — in **28 seconds**. It is the mutation vehicle and it is the only
input where "fired" and "declined" are both pinned cheaply.

The discriminating assertion is not the count. `waiting` reads **one** entry per
recursor; an arm that never fired would read `2` and `2` under the same two keys
with the same total, and a reading of `constEv < pairs` would be equally
satisfied by it.

### The mutations

Thirteen, against `the_iota_dispatch_arm_fires_the_rules_its_model_proved`,
`--no-fail-fast`. The executed test count is read out of the harness's own
summary: `cargo test` prints `error: test failed` at line start, and a `^error:`
classifier reads every kill as a compile error. The mutant binary is run under
`ulimit -v 8388608` so that the seeding mutation dies at a cap as a result; the
cap cannot go on `cargo` itself, because rustc at two jobs needs more than the
checker does. The baseline is re-run after the last restore, so a green column
is not a column about a file that was never put back.

```text
KILLED   a missing rule returns some other gap instead of declining
KILLED   …and the faithful form: it borrows `iota_dep`'s own reason string
KILLED   select on the rule table, so an unseeded rule takes iota_dep's route
KILLED   answer a constructor from another constructor's rule
KILLED   drop the σ from the rule key
KILLED   the major's own parameters are fields
KILLED   instantiate the rule at the major as well as the shared telescope
KILLED   seed every rule, not only the ones proved by reflexivity
KILLED   `refl_proved` stops reading the proof
SURVIVED drop the check that the composite is about *this* redex
SURVIVED drop the check that it lands on the Lean right-hand side
SURVIVED drop the check that an argument is in the nest's own domain
SURVIVED select on `model_of` instead of on `nested`
```

**The first three are the must-kill and they are one error three times**: a
discriminator whose missing case answers from somewhere else reports a working
model when there is none. None of them moves a *count* — `iota_dep::fire`
declines for a nested recursor too — so all three are killed by the reason
string, which is why the test asserts the `waiting` map and not its total.

**Four survivors, and one of them was acted on.** *Dropping the right-hand-side
check* survives because the statement handed to `cash_stmt` was built with `rhs`
as its third argument, so `cashed.rhs` **is** the inference the check compared
against — the guard, the second `infer_type(rhs)` behind it, and a duplicate of
`cash_stmt`'s own conclusion check were **deleted** rather than excused, which
also removes one inference of the whole right-hand side per firing.
`eq_cash`'s header makes the same argument about three guards it removed.

The other three are reported and kept:

* *the left endpoint* is `infer_type`'s interpretation of the redex against
  `whnf`'s accumulator — the same term by two code paths, and the only statement
  in the arm that relates them. `iota_dep` keeps the identical comparison at the
  identical place, and a certificate about a term `whnf` is not tracking is the
  failure it exists for;
* *the domain check* is the keying stated as a check, and it is what the whole
  interpretation-level walk rests on. Without it `cond_app` gets a membership in
  the wrong set and fails at `WALK`, one step later and less informatively;
* *`model_of` versus `nested`* has **no witness in the fixture set**: every
  nested recursor that is ever applied is also keyed. `nested` is kept because it
  is the membership `zoneb::ensure` routes the *interpretation* on, so the two
  axes cannot disagree about which declarations are modelled — but the
  distinction is unmeasured and is recorded as such.

### What did not change

The corpus: no tutorial export declares a nested inductive, so `splice` finds
nothing, `model_iota` is empty and `iota_model::selects` answers `false` off
`Interp::ind_built` without building an apparatus the file would never otherwise
have had. `kernel/`, `derived/`, `nested_ev.rs`, and the black-box allowlist —
`nested_splice.rs` gained a seeding loop and a syntactic `Eq.refl` test, and
still names no `Term`, `Thm` or `Interp`.

## The `modelgen` hookup — the model comes from the export now (#112)

`mini/src/nested_ev.rs` is **deleted**, 2117 lines. `modelgen/` generates the
model of a nested inductive as an export filter (`MODELGEN.md` §1) and
`mini/src/nested_splice.rs` — `splice` → `recognise` — reads it out of the
environment, checks each statement against the export's own, and keys `⟦T⟧`,
`⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧` onto it. `mini` runs the filter itself
(`mini/src/modelgen.rs`, on by default, `--no-modelgen` off).

### What it bought, and what it cost

| fixture | before | after |
| --- | --- | --- |
| `nested_keying` | 22 pairs, `constEv` 20, `untranslated eliminators` 4; 28 570 conversions, 11.7 s | **45 pairs, `constEv` 43, eliminators 0**; 9 775 526 conversions, 5m21 |
| `nested_iota_arm` | 39 / 39, 6 031 316 conversions, ~5m | **45 / 45**, 9 818 364 conversions, 5m24 |
| `nested_shapes` | 81 / 81, 1m40 | **does not complete** — 33m20, then OOM at a 12 GB cap |

Both remaining declines on `nested_keying` are `UTree`, which is the fixture's
point. `gapped 0`, `unsealed 0`, `lazyFills 0` throughout. The corpus does not
move: `numNested > 0` occurs in **three** files of `vendor/arena-tests` and
none of them is in `good/tutorial`.

**The cost is on the certification axis and it is structural.** The old splice
pruned the model to what the file demanded — `nested_keying` applies no nested
recursor, so `pack`, `unpack`, both round trips, both recursors and the four ι
theorems were never interpreted. A filtered export has no such half: the model
is 15 declarations of the *file*, `Ledger::run` opens a pair for every `Def`,
and every one is interpreted. 342× the conversions for 2× the pairs. Acceptance
is **not** where it goes: load plus `kernel::add` of the whole filtered
`nested_iota_arm`, model included, is ~10 s of that file's 324 s.

*(`--acceptance-only` cannot be used to measure that split: it governs the exit
code only, and `run::Options` has no such field. A first attempt at this table
read 5m0 "acceptance" against 5m20 "full" and was measuring the same run
twice.)*

**The level schedule is not the lever here either, and the reading that it was
is corrected in place.** `mini/src/nested_splice.rs`'s header used to report
that `T._model.rec_k` and every `T._model.iota_k_j` are "mentioned by nothing"
and so padded to `[0]` and `[1]` by `checker::instantiations`' `DEFAULT_LEVELS`,
and that suppressing it needed the other crate to learn the model's naming
convention. Counting the scheduled `(name, σ)` pairs on `nested_keying` — no
behaviour changed — refutes both halves:

* `T._model.rec_k` **is** mentioned, by `T._model.iota_k_j`; it is demanded at
  both σ, not defaulted there.
* `T._model.iota_k_j` is defaulted, but `nested_splice::recognise` then demands
  it at the σ it keys `T.rec_k` at, and `T.rec` / `T.rec_1` are at `[0]` and
  `[1]` by the **same** default, on an *ordinary* declaration. The σ set is
  unchanged either way.

`post == pre` for all 48 scheduled names: the propagation is wholly subsumed by
the pre-pass, and no model-side suppression can move this file. Nor is the
doubling where the cost is — 15 of the 23 model-tower names are monomorphic and
already scheduled once (31 pairs against 23; 65 against 48 file-wide).
Truncating *every* declaration to one σ, which is unreachable because it also
drops demanded instantiations, gives **9 775 526 → 4 101 470 conversions and
5m22 → 2m17, with `constEv` 43 → 23 and `lazyFills` 0 → 71**. So **2.38× bounds
every scheduling-side fix together**, against the 342× above: that 342× is the
model being in the file, not the model being scheduled twice.

**And `nested_shapes` is not blocked on the schedule either.** Under the same
one-σ truncation it **completes** — 23m46, 42 305 813 conversions, inside the
12 GB cap it OOMs against at 33m20 today. That is the *optimistic* bound and it
is not a fix: the truncation drops demanded σ, so the run certifies less
(`pairs` 126, `constEv` 96, `lazyFills` 363, and nine
`waiting:no-interp(X._model.k.rec)` rows) while still costing 4× the whole of
`nested_keying`'s baseline. Any real narrowing does *more* work than this, so
**42 M conversions is a floor on the post-monomorphization cost of this
fixture**: the schedule is what stands between it and the memory cap, and it is
not what stands between it and being affordable. Re-measure before un-ignoring;
do not expect the schedule alone to buy it back.

The standing fix is `MONOMORPH.md` §8 — delete the schedule, not narrow it —
with mono run **before** `modelgen` so no pass needs the convention.

**`CACHING-DESIGN.md`'s narrowing is not the lever here, measured.** With
`frame_put`'s `Gap` gate removed *entirely* — strictly more than the narrowing —
`nested_keying` went **5m20 → 5m14**, while the frame cache went 11.6% → 32.7%
hit rate and 51.6 M → 20.7 M lookups. The gate is not this workload's cost.
`PROFILE.md`'s 91.9 s → 8.8 s figure was measured on the `tower` probe, which
times `nested_ev::iso` — the generator this change deletes.

The lever that *is* available and was not pulled: `checker::instantiations`
defaults every undemanded declaration at `[0]` **and** `[1]`, and
`T._model.rec_k` and every `T._model.iota_k_j` are mentioned by nothing, so each
is interpreted twice. Suppressing that needs the checker crate to learn the
`_model` convention.

### Two corrections to `MODELGEN.md` §1, from its first consumer

1. **§1.1 property 1's "on the nose" needs "up to a positional renaming of the
   level parameters".** mini does not use the export's recursors: it mints its
   own in `kernel::add_block`, where `fresh_level_name` calls the motive
   universe `v` while every export writes `u`. Comparing the model's `rec_k`
   type against mini's `T.rec_k` by name fails at every `Sort` occurrence.
2. **§1.1 property 2's "check the key by name" needs the rewriting applied to
   the key.** At the root the ι theorem's major is headed by
   `T._model.ctor_j`, not by `T.node` — the §1 rewriting reaches into the rule
   statement. At a mimic it is `List.cons`, unrewritten. A consumer reading the
   key off the statement maps it back through ρ.

Nothing else in §1 was insufficient, and the consumer's surface turned out to be
**four of the nine name families** — `self`, `ctor_j`, `rec_k`, `iota_k_j`.
`pack`, `unpack`, the two round trips and `congrPack` are never read, which is
why §1's later index-telescope change did not reach mini at all.

### The mutations, and two traps in the harness

Seven, all **KILLED**, against the fourteen fast tests of `mini/tests/nested.rs`:
a missing model not recorded so `zoneb` falls through (the must-kill); the ι key
taken from the index rather than read off the statement; the recursor statement
not compared; the position check dropped; level parameters compared by name;
a recursor keyed at the empty σ; a failing `modelgen` falling back to the
unfiltered input.

Two traps, both paid for:

* **`shutil.move` restores the original mtime**, so cargo skips the rebuild and
  the *next* run measures the previous mutant. One verdict was read off a stale
  binary and reported SURVIVED.
* **A survivor found a vacuous test.** `a_modelgen_that_fails_declines_and_names_it`
  spawned through the file's `run` helper, which prepends `--no-modelgen`, so
  the filter was never reached; and it looked for `/bin/false`, which does not
  exist under Nix, so it *skipped*. Both were invisible until the mutation
  survived.

## Which recorded numbers carry weight: counters against clocks — 2026-08-08

Every headline in `MEASUREMENTS.md`, `PROFILE.md`, `MONOMORPH.md`,
`MODELGEN.md` and `CACHING-DESIGN.md` was censused and classified. The axis is
**not** "was this an A/B on one binary" — it is **deterministic counter against
wall clock**.

**Adjacency buys nothing.** A back-to-back A/B on one build controls for the
binary and the code; it does not control for the load. Two twelve-minute runs
can straddle another seat starting or finishing, and this machine has carried
six seats in a day. So a back-to-back wall pair is *just as suspect* as a
cross-day one.

**This repo already measured its own load envelope, twice.** §4.1 of
`MODELGEN.md` records the whole tree at **28.9 s against a recorded 13.7 s** —
"the difference is the machine and not the filter — three other seats were
saturating it". That is a **2.1× swing from load alone**. §6.6's phase split
moved 65/11/24 → 56/7/37 between two sittings on the same file while the RSS
column held to 0.3 %, and the file draws the right conclusion: *"only the peak
column is stable across sittings"*. **Any wall claim under about 2× is inside
that envelope and is not evidence.**

### The classification

**Sound, regardless of load** — deterministic properties of the computation:
instruction counts; the project's own counters (`conversions`, `proved`,
`sealed`, `moved`, `gapped`, `constEv`/`pairs`, `INFER_ENTRIES`, `HASH_NODES`);
declaration, group and expression-node counts; distinct-versus-total from an
intern table and the duplication factors derived from it; cache hit rates;
scheduled `(name, σ)` pairs; and pass/fail and abort-to-the-byte facts.

**Probably sound, and it should be said rather than asserted** — **peak RSS**.
Per-process and reproducible to a fraction of a percent across sittings here,
but allocator behaviour shifts under memory pressure and the cgroup ceiling is
shared.

**Suspect** — every wall-clock figure and every `N×` derived from one.

### The suspect headlines, named

* **The monomorph amortization triangle**, `MONOMORPH.md` §9.5 — 3011.42 s /
  741.14 s / 1188.76 s, and the **2.53×**, **2.03×** and **1.6×** read off them.
  The most decision-bearing wall ratio in the corpus; re-taken with
  `perf stat` in the entry below.
* **`PROFILE.md` §2's `DTree` 91.9 s → 8.8 s (10.5×)**, and 12.7× / 14.5×.
* **`PROFILE.md` §1's "~400× nanoda, ~80× Lean"** — cross-implementation wall
  ratios over sub-0.1 s denominators, and it sets the document's whole framing.
* **`PROFILE.md` §5's experiment grid**, including **B (whnf memo) at 0.63×**,
  which `CACHING-DESIGN.md` cites as the reason not to build it.
* **`PROFILE.md`'s hash-consing "14 % regression"** (91.86 → 105.15 s), a
  decision-bearing negative with no counter twin.
* **`MODELGEN.md` §4.1's "roughly 800×"**.
* **`MONOMORPH.md` §5.2's nanoda 0.152 s → 0.109 s** — a 43 ms difference
  between two ~0.1 s runs, carrying "levels are not free even in a kernel that
  keeps them".
* **`MONOMORPH.md` §9.5's "the grouping fix is not a cost"** (815.42 → 741.14 s)
  and the phase split that assigns serialisation **166.2 s (22 %)**.
* **`MEASUREMENTS.md`'s own** 17.6 → 10.3 s, 16.00 → 11.87 s (−24 %),
  21.0 → 41.9 s, 28.92 → 40.82 s (+41 %), and the eight-tower second column.

### Where the claim survives its number: counter twins

For much of the above **the real evidence is already a counter and the wall time
is decoration** — the claim stands, the figure quoted for it does not. These
should be re-cited to their counters rather than re-measured:

| claim | the number to quote instead |
| --- | --- |
| `DTree` 10.5× — "memoising `infer_type` is the lever" | `INFER_ENTRIES` **285,922,406 → 20,266,178** = 14.1× |
| the `n^2.20 → n^1.98` exponent | the same fits on entry counts: **2.18** (R²=0.973) → **1.99** (R²=0.981) |
| "the narrowed gate reproduces experiment A" | `INFER_ENTRIES` **20,266,178**, the same count to the digit |
| ι seeding costs 2 m 27 → 25 m 52 | conversions **3,878,982 → 51,830,194** (13×) |
| the `#102` refutation | **3,235,984 conversions on both sides**, identical to the digit |
| `−18.6 %` in wall | **−24.7 %** conversions (4,299,788 → 3,235,984) |
| the scheduling bound 5m22 → 2m17 | conversions **9,775,526 → 4,101,470** = **2.38×** |
| the hookup cost | **342× the conversions for 2× the pairs** |
| gate removal "changes nothing" | frame cache **11.6 % → 32.7 %** hit rate, **51.6 M → 20.7 M** lookups |
| variant B rejected | duplication **2.264 → 2.048** and RSS **+12.6 %**, not its 1 % wall column |
| the amortization triangle's real content | peak RSS **10,711,008 → 10,761,796 KB, +0.5 %** on 15.8 % more declarations |

### Two chains that should be broken

1. **`MEASUREMENTS.md`'s eight-tower seconds are disclaimed at source** — *"the
   machine was shared; the node counts are exact and the seconds are the right
   order of magnitude and not more"* — and are nonetheless the numerator of
   `MODELGEN.md` §4.1's **"roughly 800×"** and the thing `PROFILE.md` reproduces
   "row for row" to argue its probe is cheap.
2. **`MODELGEN.md` §6's "2.99× faster"** divides by `MONOMORPH.md` §9.5's
   **815.42 s**, a row that same table has since **superseded with 741.14 s**.
   Recomputed it is 2.72× — but both sides are clocks, so the ratio should be
   dropped rather than re-divided. Corrected in place.

### The house already does this right in six places

Worth preserving as the pattern: `MEASUREMENTS.md`'s *"the honest cost is the
pair count"*; the `#102` verdict resting wholly on identical conversion counts;
`MODELGEN.md` §6.7 keeping the RSS delta and **explicitly refusing** the 6.7 %
wall delta because *"the two runs were made hours apart on a machine with other
seats on it"*; §6.6's *"only the peak column is stable"*; `CACHING-DESIGN.md`'s
byte-identical `INFER_ENTRIES`; and `MONOMORPH.md`'s variant B rejected on
duplication and RSS rather than on its wall column.

## The monomorph amortization triangle, re-taken with `perf` — 2026-08-08

The claim under test: monomorphizing a Lean export before checking it **pays for
itself on a single check**. It rested on three wall clocks taken hours apart —
3011.42 s direct, 741.14 s for the pass, 1188.76 s for the check of the output —
which is exactly the shape the section above classifies as suspect. Re-taken
with `perf stat -e instructions,cycles,task-clock,page-faults`.

**Method.** Both binaries were **copied into the measuring worktree and used
from there**, so that another seat rebuilding mid-series could not change them:
`nanoda_pinned` (sha256 `bba36086…`, the shared `target/release/nanoda_bin`) for
both checks, `monomorph_pinned` (sha256 `7fc99d17…`, `mono-group`'s binary at
`1463750`, the one §9.5's row was taken with) for the pass. Every run is
`perf stat` around `/run/current-system/sw/bin/time -f` around the binary, in a
subshell with `ulimit -v`. **Nothing waited for a quiet machine**: instruction
counts are near-immune to contention, which is the entire reason for using them.
The only gate was the session memory ceiling — `monomorph` peaks at 35 GB and
this user's processes together may not pass ~50 GB without the machine killing
every seat at once.

| run | declarations | **instructions** | cycles | IPC | wall | peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `nanoda` on `mathlib.ndjson` | 670,630 | **22,822,856,168,440** | 12,107,394,522,045 | 1.885 | 2758.08 s | 10,715,200 KB |
| `monomorph` mode A, `-o` | — | **5,305,931,509,798** | 3,346,397,993,873 | 1.586 | 757.45 s | 35,292,700 KB |
| `nanoda` on that output | 776,723 | **9,759,549,740,309** | 5,375,258,774,159 | 1.816 | 1211.37 s | 10,759,940 KB |

### It still amortizes, and the figure is smaller

**Pass plus check is 15.066 T against 22.823 T direct: 1.51×.** The pass costs
5.306 T; each check saves 13.063 T; **break-even is 0.41 of a check.** So the
conclusion survives — it pays for itself the *first* time, with room to spare —
and the number that was being quoted for it does not. **The checker alone is
2.34×, not 2.53×.**

**Both figures are at `monomorph --default 0`, and the default is load-bearing —
through duplication, not through `Prop`.** A quarter of Mathlib's groups are
demanded by nothing and take that default (164,481 of 654,504), so the question
of whether `Sort 0` was buying the checker proof irrelevance had to be settled
rather than assumed. `MONOMORPH.md` §9.13 settles it against: at `--default 1`
the checker ratio is **1.763×** and pass-plus-check **1.231×**, and the whole of
the gap decomposes as **1.2932× more declarations × 1.0289× per declaration** —
90 % duplication. **Per declaration 97.2 % of the speedup survives the change of
level** (2.7163× against 2.6399×), and a step-counting build puts proof
irrelevance at 0.2801 % of reduction steps on the `[0]` output against 0.2983 %
on the input — *lower*, where the hypothesis needs it higher. So quote these
numbers as "at the default", not as "at `Prop`"; what monomorphization removes
is level machinery, uniformly across every conversion rule.

### Wall against instructions: they agree on direction, not on magnitude

Three wall-derived answers to one question — 2.53× recorded, 2.28× from the very
runs above, against **2.34×** in instructions — span **11 %**, and the two
bracket the instruction count from opposite sides. The recorded clock overstated
the checker ratio by 8 %; these runs' own clocks understate it by 3 %. **This is
the useful calibration: the corpus of recorded wall ratios is not worthless, it
is accurate to roughly ±10 %.** A claim that survives a 10 % swing is safe to
keep; the several claims in this repo that turn on 1–5 % differences are not.

**Peak RSS came out better than "probably sound".** 10,715,200 KB here against
10,711,008 KB recorded on a different day for the same work — **0.04 %**. The
pass reproduced its own recorded peak to **0.005 %** (35,292,700 against
35,294,528 KB) and wrote a **byte-identical** output, 5,816,542,757 bytes, the
same count to the digit. Where a decision here rests on RSS, it stands.

**IPC is the load meter, and it moved.** 1.885 / 1.586 / 1.816 across the three.
The check of the monomorphized file ran at *lower* IPC than the check of the
input, which is why its wall ratio understates its instruction saving: the
monomorphized file is a smaller amount of work per unit of memory traffic.

### Mode B: the pass is measurable, the check is not, and that is structural

Mode B — `--mono-recursors`, what `mini` actually wants — cannot complete this
triangle, and not for want of a quiet machine. On `init-prelude`'s mode B output
`nanoda` panics at `checker/src/inductive.rs:1269`, `Expected (Declar::Recursor,
Declar::Recursor)`, exit 101, after **371,105,688 instructions** against the
**1,532,217,667** a full check of that export costs — it dies roughly a quarter
of the way in, because it mints `T._at.σ.rec` and mode B renamed it. Same
pinned binary, same export, mode A of which checks clean in **987,231,746**
instructions for 2,244 declarations against the input's 2,059: **1.55×**, the
counter that replaces §5.2's 43 ms stopwatch.

So **the amortization figure is measured on the mode we are not adopting.**
Whether it carries to mode B is an argument, not a measurement: mode B is
+0.63 % declarations over mode A (781,601 against 776,723) and is *by
construction* a pure post-pass over mode A's output, so its check would very
likely land within a percent of mode A's 9.760 T — **if a checker existed that
did not regenerate recursors by name.** None does. That is a checker change,
not a measurement, and it should be booked as one.

**Mode B's *pass* is measurable, and it is much cheaper than the clock said.**
The full-Mathlib mode B pass with `-o` has never been run by anyone and could
not be run in this window either — it needs ~39 GB and another seat held 14–21 GB
throughout, which together would cross the ~50 GB ceiling that kills every seat
at once. That is a scheduling limit and not a structural one, and it is the one
number here still owed. But the **A-against-B ratio** is measurable at a size
where the memory is safe, and both modes were run back to back on the 20 M-line
prefix with the same pinned binary:

| 20 M prefix | instructions | cycles | IPC | wall | peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| mode A pass, `-o` | 762,754,348,322 | 359,518,303,545 | 2.122 | 81.26 s | 6,425,736 KB |
| mode B pass, `-o` | 865,036,777,646 | 484,357,920,287 | 1.786 | 109.39 s | 6,983,276 KB |
| **B / A** | **1.134×** | 1.347× | — | **1.346×** | 1.087× |

**Mode B costs 13 % more instructions and 35 % more wall.** That gap is the
sharpest case in this file of the two quantities measuring different things, and
it is not noise — the two runs are adjacent and the cause is visible in the
counters: mode B's IPC is **1.786 against 2.122**, so it is markedly more
memory-bound per instruction. §9.5's recorded 20 M pair (86.87 s against
138.60 s, **1.60×**) is a clock and overstates the work ratio by two fifths.

**So the amortization very probably carries to mode B, at about 1.44× — as a
projection, clearly labelled.** Scaling mode A's 5.306 T pass by 1.134 gives
≈6.02 T, and scaling its 9.760 T check by mode B's +0.63 % declarations gives
≈9.82 T, for ≈15.84 T against the 22.823 T direct check: **≈1.44×, still paying
for itself on one check.** Two things keep this a projection rather than a
result: the pass ratio is measured at 20 M and assumed to hold at 100 M, and the
check figure assumes a checker that does not exist.

### What the machine was doing

Deliberately not controlled, and recorded only so the wall column can be read.
Run 1 began at loadavg 5.61 with 4.0 GB anon and ran **concurrently with another
seat's `monomorph` prefix ladder** throughout, finishing with 21.7 GB anon on the
box; run 2 began at loadavg 5.03 / 2.3 GB; run 3 at loadavg 3.40 / 0.9 GB. Run 1
was therefore the most contended of the three and still came in **8.4 % faster
than the uncontended figure on record** — which is the clearest single
demonstration in this file that a wall clock on this machine is not measuring
what it is being asked to measure.

## `nested.rs` and `init-prelude`, in instructions — 2026-08-08

Two counters that had never been taken, both on `origin/master` at `9120294`,
both `perf stat -e instructions` per `47b262b`. The machine carried two other
seats throughout; that is why the wall columns are here only as commentary.

### The CI long pole, `mini/tests/nested.rs` (#110)

```text
perf stat -e instructions  cargo test --test nested -- --test-threads=1
  17 760 968 447 568 instructions      20 passed, 2 ignored, 1 207.27 s serial
```

`ci/check.sh` ran the workspace three times when this was taken — plain,
`--features stepcount`, `--features tg` — so this **one file was 53.3 T
instructions per check run**. It is 17.76 T now: the two feature runs are
`-p nanoda_lib`, and `mini` is not in them (2026-08-09, below).

Every wall figure previously attached to it is uncomparable and must not be
chained: 285.7 s (`6b11c94`), 309.50 s (`9a8702f`, PROFILE §5, at 15 tests),
336 s (the file's own header). None records the load and the file has grown to
22 tests across them. The count above is the first figure a later one can be
compared against.

Two tests are essentially the whole file. Each spawns one `mini` subprocess;
measured against the **test-profile** binary (`target/debug/deps/mini-<hash>`,
not `target/debug/mini` — see below), `--no-modelgen --verbose --nested`:

| fixture | test | instructions | conversions |
| --- | --- | ---: | ---: |
| `nested_keying` | `the_nested_declarations_interpretation_is_its_models` | 9.931 T | 9 857 800 |
| `nested_iota_arm` | `the_iota_dispatch_arm_fires_the_rules_its_model_proved` | 9.945 T | 9 900 638 |

Both `gapped 0`. They are different fixtures asserting different axes — keying
against ι-arm firing — so they cannot be merged, which is why `#110`'s recorded
"merge the two tower tests" fix does not transfer (the tests it named went with
`mini/src/nested_ev.rs` at `#112`).

**The arithmetic does not close, and that is recorded rather than smoothed.**
9.931 + 9.945 = 19.88 T against the containing binary's 17.76 T — the two rows
sum to 12 % *more* than the thing that contains them. They were taken later,
under different memory pressure and under `ulimit -v 8 GB`, and `perf stat`
counts kernel instructions too. Read them as "each heavy test is about 10 T",
not as a decomposition; re-take all three in one sitting if the split has to be
exact.

**A profile trap that corrupted two runs before it was noticed — closed
2026-08-09.** `cargo build` uplifted an **opt-level 0** `mini` to
`target/debug/mini` (54 389 712 bytes; no `-C opt-level` in the `dev` profile),
`cargo test` built an **opt-level 1** one (45 041 256 bytes, `-C opt-level=1`),
and both uplifted to the *same path*. `CARGO_BIN_EXE_mini` is that path —
confirmed by `strings` on any mini test binary — so every subprocess test ran
whichever of the two the last cargo command happened to leave there.

Re-derived on `f68890c` before the fix, the two files were 44 859 744 and
61 052 224 bytes with different inodes. **Cargo itself is consistent**: after
`cargo build --bin mini`, `cargo test --test dump --no-run` re-uplifted in
0.01 s, so the earlier "it does not re-uplift" reading does not reproduce and is
not what bit. What bites is the artefact that outlives the command — a test
binary in `target/debug/deps/`, which is what a measuring seat points `perf` at.
That reads the path, and a `cargo build` in another window is enough to change
what the path means.

**The fix is that there is now only one binary.** Cargo compares profiles by
their settings and not by their name, precisely so `dev` and `test` can be one
unit when they agree, so the root `Cargo.toml` gives the two tables identical
contents. `ci/check-uplift.sh` builds a throwaway crate carrying those two
sections verbatim and fails if `cargo build` and `cargo test` land different
inodes at the one path; its self-test feeds it the pre-fix pair and requires the
red. Measured: same inode after both commands, 0.6 s for the check.

A second, milder collision on the same path remains and is *cost*, not
correctness: `nanoda_lib`'s dev-dependencies are in the graph whenever its own
test targets are, which under resolver 2 changes `num-bigint`'s features and so
`mini`'s bytes (61 238 368 with them, 61 056 280 without). Both binaries are the
same source at the same opt-level. `ci/check.sh` keeps its build and test halves
on the same side of that line so nothing is compiled twice.

### `init-prelude`, past its first three blockers (#87, #121)

`scripts/nat-reach.py` closes the declarations reaching a nat literal above
mini's cap of 10 forward under `const`: **77 carry one directly and 529 of
1 777 (29.8 %) fall with them**. Run against the complement, mini gets
**1 459 declarations and 3 078 scheduled pairs** through `convert::load` —
against `declars=0` on the unfiltered file — and used to decline on
`non-standard axiom: sorryAx`, which is a **leaf** (removing it drops exactly
one declaration of 1 248).

**`sorryAx` is no longer a blocker, and the leaf reading is now computed rather
than inferred.** `#121` narrowed the axiom rule to the axioms something in the
file refers to (`mini/src/unused_axiom.rs`), and on the residue
`unused_axiom::classify` reports `used = []`, `unused = ["sorryAx"]` over all
1 245 mini declarations — one non-standard axiom in the file and nothing
anywhere refers to it. Mini ignores it, names it on the verdict line, and goes
on.

**What is behind it is `Nat`, again, and it is cost.** Measured on the *release*
profile at `f8d7dc2` (which is `82e2df9` plus `#121`, so it is **after** the
arena port and after `#115`), `perf stat -e instructions`, `ulimit -v` 10 GB,
`MINI_CONV_TRACE=1` for per-declaration progress:

| | |
| --- | --- |
| kernel pass (`kernel::add`, the acceptance axis) | **1 245 of 1 245**, complete |
| interpretation pass completed | **231** declarations of 1 245; it died inside the 232nd, `Nat.mod_lt` |
| conversions at that point | `proved` 30 347 733, `sealed` 29 029 789, **`gapped` 0** |
| instructions | **20 848 572 753 087** (20.85 T) |
| task-clock | 1 555 s |
| how it ended | **`SIGABRT` — the allocator hit the 10 GB `ulimit -v`**, not a timeout |

Three things in that table were not known before and none is a guess.
**The whole file type-checks**: every declaration of the residue passes
`kernel::add`. *That was inferable from the trace alone at the time, because
`MINI_CONV_TRACE`'s rows came from `Ledger::run`, which did not start until the
whole-file kernel loop had finished. **The inference no longer holds** and is
recorded here only as what it was: `mini/src/decl_pass.rs` interleaves the two,
so a trace row now says the kernel reached that declaration and nothing about
the ones after it. The fact itself stands — it was measured on this run — but
re-measuring it needs the verdict line, not the trace.* **`gapped` is 0 at 231
declarations** — nothing mini reached is
unrepresentable; it is slow, and the slow part is `Nat`. And **the wall is
memory rather than time**: the run ended by itself.

The trace says where the cost is. Declarations 197–199 (`Nat.sub_le`,
`Nat.succ_sub_succ_eq_sub`, `Nat.sub_lt`) each cost tens of thousands of
conversions; `Nat.modCore_lt` alone takes the count from 7.8 M to 20.2 M, and
`Nat.mod_lt` from 20.2 M to 30.3 M and then off the cliff.

The 3 000 s / **14.8 GB RSS with no verdict** on record above this line was
taken before both the arena port and `#115` and is **superseded**. The shape of
the answer changed: it is not "no output in fifty minutes" any more, it is "231
declarations, 20.85 T, and then 10 GB is not enough". A run under a larger cap
would go further and the next number to take is where 14.8 GB now lands. `Nat`
remains 29.8 % of the file and is a separate problem, and there is still no
cheap split: `--acceptance-only` changes the exit code, not the work.

**Both halves of that measurement are deterministic and were seen twice.** An
earlier run of the same command on `8e2e45b` — before `#115` — stopped at
*exactly* the same declaration with *exactly* the same `proved`/`sealed`
figures, and differed only in taking 1 800 s to get there instead of 1 555 s.
The stopping point is a property of the file; the wall clock is a property of
the tree.

## `ci/check.sh` end to end, and what the feature matrix cost — 2026-08-09

The whole script had been "~45 min" all day and nobody had counted it. Both runs
below are `perf stat -e instructions -- <script>` on the same warm tree in one
sitting, `CARGO_BUILD_JOBS=12`, with `modelgen` and the release profile
pre-warmed so neither run pays a cold `lake build` or a cold `lto` link the
other does not. Another seat's `mini` corpus runs were on the box for part of
the first; that moves the wall column and not the instruction column, which is
the whole reason `47b262b` says counters decide.

| | instructions | wall | test invocations |
| --- | ---: | ---: | ---: |
| three `cargo test --workspace` sweeps (before) | **107 901 091 763 823** | 2 824 s | 3 911 |
| plain sweep + two `-p nanoda_lib` sweeps (after) | **36 722 573 641 991** | 986 s | 1 431 |

**71.18 T saved, 66.0 %**, and 47.1 min → 16.4 min. Both runs ended
`all checks passed`.

Re-run after rebasing onto `0b7fa3b`, which is three arena-expression commits
further on and is therefore *not* comparable with the pair above: **39.29 T,
1 142 s (19.0 min)**, `all checks passed`, no step SKIPped.

Re-run again at CACHING-DESIGN.md's steps 1 and 2 — the narrowed `Gap` gate
with the pointer key, and `opt-level = 3` in `dev` and `test` — warm tree,
`CARGO_BUILD_JOBS=12`, same shape of run as the row above and comparable with
it: **19 271 833 029 935 instructions (19.27 T), 1 532 s**,
`all checks passed`, no step SKIPped. **51.0 % of the script gone, 2.04×.**
Quote *this* one for "how long is `ci/check.sh`", the 39.29 T for what the
steps were worth to it, and the pair above for "what did the matrix cost".

Two things this row is not. It is **not** an attribution between the two
steps: that is CACHING-DESIGN.md §6.1's four rows, taken on
`mini/tests/nested.rs` and the tutorial corpus, where the split is 2.13× for
step 1 and a further 1.08× for step 2. And its **wall column is worthless
here** — 1 532 s against the previous row's 1 142 s, on a box carrying
another seat's `monomorph` run at 14.8 GB RSS for the whole of it, while the
instruction column fell by half. That is `47b262b` exactly: counters decide,
clocks comment.

**The coverage is the same set of tests, and that is checked rather than
argued.** `Running …` on stderr and libtest's results on stdout are both ordered
and 1:1, so they zip into an inventory of (test target, test name, outcome). The
two runs produce **1 343 such triples each and the sorted inventories are
identical** — same targets, same names, same outcomes. Only the multiplicities
move:

* **1 240** triples go from three executions to one. Not one of them belongs to
  the checker: 108 test targets are affected and none is `nanoda_lib`,
  `corpus.rs` or `tg_tutorial.rs`.
* **44** stay at three — `nanoda_lib`'s own unit tests (38) and `corpus.rs` (6),
  which are what the two features can actually change.
* **59** stay at one: the `tg`-only tests, 31 in `nanoda_lib`'s unit tests
  behind `cfg(all(test, feature = "tg"))` and 28 in `tg_tutorial.rs`, which
  exist in the `tg` build alone and always did.

**Why it was safe to narrow.** `cargo tree -e all` over the whole 135-node graph
differs in exactly one node between the plain resolution and each feature
resolution — `nanoda_lib` — so no dependency's `cfg` can carry either feature
anywhere else. `kernel` and `derived` do not link `nanoda_lib` at all. `mini`
does, for the export parser and the level pre-pass, and every item the two
features gate is reachable only through a `TypeChecker`, which builds its
backend in its constructor: `certify::new_backend` is the single door. That is
now enforced rather than asserted — `ci/check.sh` runs everything except the
checker under `NANODATG_ASSERT_FEATURE_INERT`, which makes that constructor
panic, and `ci/check-feature-inert.sh` watches the panic happen against a
process that certainly does build one.

## `Interp::parts` deleted: the kernel grew a term reader — 2026-08-09

*The memory half of "the checker handles `init-prelude` at reasonable time and
memory costs". `PRELUDE-COST.md` §3.2 measured one table at **54.4 % of the live
heap** and **80 % of the live kernel `Term` nodes**, and §3.3 measured the naive
prune — clearing it per declaration — at **−60.2 % heap and 213 new gaps**. This
is what replaced it. Baseline `origin/master` at `0260925`; both binaries `test`
profile (`opt-level = 3`, no LTO), `perf stat -e instructions` per `47b262b`,
each run under its own `ulimit -v`.*

### What the table was

`derived::skeleton::Parts` was `HashMap<Term, (FnSym, Vec<Term>)>`, written by
`Interp::mk` and read by the skeleton decomposition. **It is neither identity
nor memoisation: the value is the key's own contents.** `Term` is
`Rc<TermData>`, `TermData::App(FnSym, Vec<Term>)` is one of its three
constructors, and `parts[Term::apply(f, args)]` was `(f, args)` — a second copy
of the argument vector the node already holds. The table existed because
`kernel::Term` had constructors and no reader (`data()` is `pub(crate)`).

So the change is a reader: `Term::as_app(&self) -> Option<(FnSym, &[Term])>`,
six lines, the exact analogue of the `Formula::as_eq` that has always been
there. It exposes only `TermData::App`, so the constructor discipline that makes
dangling de Bruijn indices unconstructible is untouched, and an `App`'s
arguments are locally closed whenever the whole term is — it hands back nothing
a client could not already hold. `ci/check-boundary.sh` is green; the kernel
goes from 676 to 682 non-comment lines against a budget of 700.

With it: `derived::skeleton::skeleton` reads structure off the term and is
**total** (returns `Term`, not `Option<Term>`), `Interp::parts_of` is
`t.as_app()`, `Interp::mk` is `Term::apply`, and the field is deleted. Two
`rebuild` calls whose results were discarded — beta's and the fibre's second
legs, there only to file the contractum's nodes in the table — go with it, as do
`conv::app_cong`'s two endpoint-recording `mk` calls and `proj_data`'s
`term_recorded`, which hand-rebuilt `proj_of`'s four layers through `mk` and is
now `proj_of`.

### What the 213 gaps were

**Recordedness was standing in for decomposability**, and it was wrong in both
directions. Wrong on the read side: a term the *kernel* built — a substitution
instance, or either endpoint of a `derived::congr` — never passed through
`Interp::mk` and read back as structureless, which is `mini/src/conv.rs`'s six
conversions lost on `mutual_aux_encoding` and, at scale, §3.3's 108
`not-decomposable` and 69 `no-endpoint`. Wrong on the write side: keeping the
proxy true meant remembering every term ever built, forever. **Clearing the
table breaks the proxy; deleting it removes the thing being approximated**, and
the decomposition can no longer fail.

### The numbers

Instructions and peak RSS, separately.

| workload | | baseline | reader | |
| --- | --- | ---: | ---: | ---: |
| 91 good tutorial exports | instructions | 405 375 599 994 | 402 689 993 069 | **−0.66 %** |
| | peak RSS | 178 540 kB | **33 808 kB** | **−81.1 %** |
| `Nat.ble_eq_true_of_le` closure, 47 decls | instructions | 2 251 144 138 254 | 2 232 215 740 074 | **−0.84 %** |
| | peak RSS | 1 049 824 kB | **46 524 kB** | **−95.6 %** |

Peak RSS on the corpus is the same file in both, `077_RBTree.id_spec`.

**And the two declarations that stop `init-prelude` today, cut out with
`scripts/decl-closure.py` and run alone.**

| closure | | baseline | reader |
| --- | --- | ---: | ---: |
| **`Nat.mod_lt`, 159 decls** — the `Nat.mod*` cluster the file dies inside | outcome | **`SIGABRT` at a 12 GB `ulimit -v`**: `memory allocation of 3 825 205 264 bytes failed`, at 1 992 s | **completes**, 159 of 159, **66 569 578 conversions, `gapped 0`** |
| | peak RSS | **11 142 200 kB** | **501 984 kB** |
| | instructions | 26 461 224 027 620, to the abort | 38 790 399 776 432, 2 825 s |
| **`BitVec.decEq` + `BitVec.noConfusion`, 83 decls** | outcome | §4.2: killed by a 25-minute timeout **inside declaration 81 of 83**, 17 242 524 conversions | **completes**, 83 of 83, **25 335 661 conversions, `gapped 0`** |
| | peak RSS | ≥ 3 841 600 kB | **106 172 kB** |
| | instructions | — | 15 071 153 293 830, 1 096 s |

**That is the memory half of the goal, answered, and the `Nat.mod_lt` row is
the sharpest form of it.** That closure runs **66 569 578 conversions** — more
than twice the 30 347 733 at which the whole file died — and peaks at 490 MB.
At §3.1's measured 241 B per conversion it would have needed **16 GB**; it
needs **7.5 B**, and the figure is *flat* rather than a slope, because what was
growing was the table and not the work. Both walls this document found are
memory-free now: the `Nat.mod*` cluster completes, and §4.2's `BitVec` pair,
which no run had ever finished, completes.

What stops `init-prelude` is **time** — `List.get.match_1` alone is 11.00 T
instructions (§4.2) and this change moves none of it.

**Time is unchanged and that is the expected sign.** §3.3's clear-per-declaration
row *saved* 3.1 %, because clearing is 33 431 conversions that stop happening;
removing the table changes no conversion at all, and the ≈0.7 % it returns is
431 598 hash inserts and their `Vec` clones per 60 declarations.

### The strong check

**All 91 exports' `--verbose` output is byte-identical across the change** —
every `facts`, `clauses`, `ledger`, `evidence`, `convs` and `untranslated` row,
`accept 89 / decline 2 / reject 0`, `constEv 218/218`, `unsealed 0`,
**`gapped 0`**, and the conversion counters to the digit. Two baseline runs were
diffed against each other first, to establish that the output is deterministic
at all: they agree on all 1 002 lines and differ by 0.02 % in instructions. The
`Nat.ble_eq_true_of_le` closure's report is byte-identical too, at
`proved=3 750 820  gapped=0`.

`cargo test --workspace --exclude nanoda_lib`: **1 265 passed, 0 failed**.
`cargo test -p nanoda_lib --features tg`: 28 + 72 + 6 passed, 0 failed.

### The mutation, seen red first

`mini/src/interp.rs`'s `skeleton_refuses_an_unrecorded_term` asserted that a
term mentioning the binder that had not been built through `Interp::mk`
decomposes to `None` — "an unrecorded term mentioning the binder must fail, not
be papered over". It is now
`skeleton_decomposes_a_term_the_interpretation_did_not_build`, and it asserts
the opposite: the term decomposes to exactly the skeleton a recorded one would
give. Run against `origin/master`'s code it panics —
`MUTATION: must decompose` — which is the point. **Restore the table and any
prune of it — clearing per declaration, bounding it, evicting from it — turns
that term back into an atom and this test goes red**, which is precisely the
213-gap failure in one assertion.

### What did not change, and why

`checker/src/tg.rs` keeps its own `parts` table and a private
`skeleton_recorded`, **deliberately**. Pointing tg's wrapper at the total
decomposition moves five of `checker/tests/tg_tutorial.rs`'s counter assertions
— the projection clause is reached 3 times instead of 5, because a
decomposition that used to fail now succeeds and an earlier rule fires instead.
Those counters are tg's frontier record and re-baselining them is a change to
make on purpose, not a side effect of a memory fix in another crate. The same
one-line replacement is available there whenever somebody wants it.

## Beta domain obligations arrive from the application's own check — 2026-08-10

*Task #126, the census's largest bucket-(i) row (`THREADING-CENSUS.md` §1.3,
§3). Baseline `origin/master` at `a7b0c6a`; `release`, `--features
tg,stepcount`, the `scripts/arena.sh` config over
`good/init-prelude.ndjson`; `perf stat -e instructions` throughout.*

### The claim under test, and how it fared

The census said the beta rule's domain obligation `⟦a⟧ ∈ ⟦A⟧` should not be
searched for because "`infer` typed this very argument when the application
was checked". Both halves of that sentence were measurable, and they came
apart:

* **Where the checker held the evidence, it was being discarded.** `infer_app`
  composes `⟦arg⟧ ∈ ⟦binder domain⟧` — the argument's own typing converted
  along the `assert_def_eq` certificate — and consumed it only into `ty_app`,
  and only while the *head's* derivation was still alive. With 20 922
  `ty_const` no-evidence heads, the common case built the composition never;
  the beta rule then re-derived the same fact per redex by `has_type`, and
  `local_premises` guessed the context by scanning the argument for `Local`
  nodes.
* **But the majority of the raw-hoisted population was never in inference's
  hands at all.** That is the refutation half, below.

### What landed

`Certifier::app_arg_checked` (default no-op; the null backend pays nothing):
`infer_app` hands every checked argument's composed typing to the backend,
now built even when the head's derivation is dead — the composition gained a
second consumer, so the `live` gate that made it free to skip became wrong.
`TgBackend::arg_mems` stores it keyed `(arg, ⟦binder domain⟧)`, entries
checked at the write to establish exactly their key's claim.
`TgBackend::domain_obligation` reads the store **before any search**, and a
recalled entry is re-checked against the claim being asked
(`derived::establishes`) — a failed recall falls through to the search and is
counted as a bug report (`ArgMem::Mismatch`, 0 on the corpus).

Fixture: `beta_domain_obligation_reads_the_application_checks_handoff`, three
atoms — a checked redex whose certificate must be unconditional, an unchecked
same-shaped redex whose certificate must stay the honest `Conditional` hoist,
and a poisoned store entry (a true theorem under the wrong key) the recall
guard must refuse. Mutations verified: deleting the write turns atom 1 red
with exactly the pre-tranche `Conditional`; skipping `establishes` at the
read turns atom 3 red as `Admitted("trans over an admitted premise")` — the
wrong membership fails `u_mp` against the beta lemma inside the rule, i.e.
the system fails closed, but the *label* moves from an honest hoist to an
admitted gap, which is why the guard is load-bearing.

### The numbers (`init-prelude`, 2 059 declarations, 3 861 (decl, σ) pairs)

| | `a7b0c6a` | with the handoff |
| --- | ---: | ---: |
| instructions | 193.83 G | 194.01 G (**+0.09 %**) |
| gaps | 15 542 | **15 532** |
| escapes | 2 257 | **2 247** |
| obligations asked / discharged | 39 951 / 5 373 | 39 951 / 5 373 |
| answered from the handoff | — | **10 300** (102 outright + 10 198 under antecedents) |
| entries stored | — | 26 724 |
| recalls failing their claim | — | **0** |
| `has_type` miss "a local" | 11 310 | **1 132** |
| `by Local` (context acquired by the search) | 15 648 | 5 447 |
| raw hoists | 20 338 | 20 328 |

Reading it: the handoff did not change *what* is discharged outright (the 102
were derivable by search too) — it changed **where the conditional answers
come from**. 10 198 obligations that used to be settled by the search
re-acquiring ambient-local typings (`has_type_local`, the census's 11 211-row
"context guessed, not read") now arrive with their antecedents from the
application check. The ten escapes closed are obligations about applications
of locals (`w x`): the raw hoist assumed the whole membership, which no
binder discharges; the handoff carries per-local antecedents, which binders
do discharge. The ledger is unchanged row-for-row everywhere else.

### The refutation: the raw population, attributed

The new permanent ledger row (`raw hoists by cause`) splits the 20 328
survivors:

* **32** — handed off at another domain term (a conversion the store does not
  carry). Negligible.
* **1 640** — checked, and the argument's typing was already a hole at the
  check: the `ty_const` cascade seen from the beta rule, §3 bucket (ii).
  These convert into handoff entries *by themselves* the day the shared
  constant store lands: the write site is already there.
* **18 656** — **no application check ever visited the term.** Probe-sampled
  (40 subjects): `Eq.refl α a` / `HEq.refl x y` constructor applications
  built by `to_ctor_when_k`'s K-shortcut, and minor premises out of *other
  declarations' values* (`Fin.casesOn` wrappers, `Nat.below`'s
  `fun n n_ih => PProd …`) entering by delta unfolding, instantiated at the
  current declaration's locals. For these, "the typing arrives with the whnf
  call" can only mean stage-2-proper subject-reduction threading or
  cross-declaration evidence (task #125) — no recall of this declaration's
  inference can serve them, because it never held them.

So the census's beta row was **two problems and a third wearing its coat**:
a threading debt (now paid where it existed), a cascade face (bucket (ii),
delivery mechanism now in place), and a reduction-built residue that is the
honest remaining case for stage 2's signature change.

## One per-declaration loop: what the certified prefix costs and buys — 2026-08-10

The pipeline was a whole-file kernel pass and then a whole-file interpretation
pass. The kernel pass early-returns at the first rejection, so **a file with one
bad declaration produced no certificate for any of the others.**
`mini/src/decl_pass.rs` fuses them: parse, schedule, drop the unused axioms, then
one loop that checks a declaration, interprets it and adds it to the environment.

Instructions with `perf stat -e instructions` over the sweep in
`scripts/oneloop-sweep.sh` (`--no-modelgen --verbose --mutual`, one process per
file), the `dev` profile, `origin/master` at `893206c` against `joachim/oneloop`.
Both binaries built in their own worktree from their own source, because the main
checkout's `target/debug/mini` was a day older than `HEAD` and would have priced
the wrong code.

| population | files | before | after | |
| --- | --- | --- | --- | --- |
| `good/tutorial` | 91, all accepted | 406.39 G | **397.25 G** | −2.2 % |
| `good/*.ndjson` | 4, none accepted whole | 2.98 G | **2.91 G** | −2.4 % |
| `bad/**` | 55, all rejected or declined | 36.45 G | **114.23 G** | +213 % |
| `good/undecidability` | 4, two rejected | 48.39 G | **120.70 G** | +149 % |
| whole sweep | 154 | 494.03 G | **635.18 G** | +28.6 % |

**The two halves of that table are different facts and must not be averaged.**
On the accepted population the run does the same work and is 2.2 % *cheaper* —
the whole-file `env.clone()` the expansion took per file, and the `positions`
sweep the nested recognition took per file, are both gone. Everywhere the number
rises, it rises because the run is now doing something it did not do at all: on
a stopped file the prefix before the stop is interpreted and certified, and
before this it was not.

What that buys, per file, on the two populations where a stop is the norm:

| export | verdict | declarations before the stop | certificates: before → after |
| --- | --- | --- | --- |
| `good/undecidability/subject-reduction-redex` | reject | 40 | 0 → **22** |
| `good/undecidability/alg-conv-trans-acc-left` | reject | 39 | 0 → **21** |
| `bad/ctor-num-fields` | reject | 23 | 0 → **17** |
| `bad/constlevels` | reject | 11 | 0 → **8** |
| `bad/tutorial/002_badDef` | reject | 0 | 0 → 0 |

The last row is not a failure: `002_badDef`'s first declaration is the bad one,
and a prefix of nothing certifies nothing. It is in the table because a
capability measured only where it fires is a capability nobody has bounded.

**The verdicts did not move.** The 154-file sweep is byte-identical between the
two binaries — verdict, tag, exit code, `facts`, `clauses`, `elim`, `ledger`,
`evidence`, `untranslated`, `convs` and `framecache` rows — apart from the new
`prefix` row. Over `mini/tests/fixtures` (every non-nested fixture, so all ten
`mutual` ones) it is byte-identical too, apart from five rows that are all the
one waived property: an unused non-standard axiom is no longer kernel-checked,
so `unused_axiom_ignored` reads `3 declarations` where it read 5,
`route_unused_axiom` reads 1 where it read 2, those two files' `framecache`
rows lose the misses of the type checks that no longer happen (188 → 184 and
6 → 5), and `unused_axiom_illtyped` — a fixture added for this — is accepted
where it was rejected.

*The first version of this claim was weaker than it reads, and the reason is
worth keeping: `scripts/oneloop-sweep.sh` filtered rows with `conv\b|frame\b`,
which matches neither `convs` nor `framecache` — so the two rows carrying the
conversion census were silently outside the comparison. The regex is
`convs|framecache` now and the numbers above are the re-taken ones.*

### `init-prelude`: 0 → at least 265, and the wall moved

The headline case, and the one that motivated the restructure. Run on the
`modelgen`-filtered export (cached once, so both binaries see the same bytes),
`--no-modelgen --verbose --mutual --nested`, `MINI_CONV_TRACE=1`,
`ulimit -v` 20 GB.

**Before**: `decline` — a budget refusal in the recursor type of
`ByteArray.IsValidUTF8` — after 2 005 s and 26.75 T instructions, with
`facts declars=2131`. `MINI_CONV_TRACE` emitted **zero rows**. That zero is the
measurement and it is direct rather than inferred: the interpretation pass is
downstream of a completed acceptance pass, and the acceptance pass never
completed, so **not one declaration of the file was certified**.

**After**: the trace runs from the first declaration. At the point the run was
stopped externally at ~85 minutes it was at declaration **265**
(`List.utf8Encode`), with `proved` 77 019 756, `sealed` 73 555 792 and
**`gapped` 0**. So the certified prefix is 0 → **≥ 265**, and every conversion
in it is closed.

**The wall moved and it moved onto a known one.** The run no longer stops where
`ByteArray.IsValidUTF8` is; it stops where `Nat.mod_lt` is — the same cliff §"
`nested.rs` and `init-prelude`, in instructions" already prices (the trace
crosses 30.3 M conversions inside `Nat.mod_lt`). **This is a real cost
regression on this file and should be read as one**: the *verdict* on
`init-prelude` used to be available in 33 minutes and now is not, because
reaching it means interpreting 2 000-odd declarations first. The verdict itself
is unchanged. What would restore the fast path is a switch for the evidence
half — `decl_pass::Pass::new` already takes one, and the used-axiom decline is
its only caller today — but it is a flag with its own contract and its own
fixtures and is deliberately not part of this change.

The `good/tutorial` aggregate, which is the standing ratchet, is unchanged to
the last digit:

```
pairs=218  constEv=218  unsealed=0  lazyFills=0
proved=829683  sealed=827106  gapped=0  moved=3461  movedSealed=915
moved − movedSealed = 2546
```

## How far along the goal is: the four denominators, and the row that states one — 2026-08-10

*Task #147. `origin/master` at `c2c68c5`, `--release --features tg`,
`vendor/arena-tests/good/init-prelude.ndjson`, `perf stat -e instructions`. The
numerator was **re-measured, not inherited**. Three temporary instruments were
used and reverted in the same session: a `Sealed::new` ok/err tally
(`checker/src/sealed.rs`), a print of `export_file.declars.len()`
(`checker/src/main.rs`), and a static per-kind pair census in the level
pre-pass (`checker/src/instantiations.rs`). Nothing in the tree retains them.*

The project's stated thrust is *"all declarations of prelude-init (except
skipped non-standard axioms) checked, accepted and with their typing relation
having a fully proven theorem in the environment."* Nobody could quote a ratio
for it, because **four different populations were all being called
"declarations of `init-prelude`"** and two of them had been published against
each other. They are all measured here, together, so that no future number can
be quoted without one.

| population | count | what it is |
|---|---:|---|
| declaration **records** in the export file | 1 777 | `def` 1479, `thm` 156, `inductive` 126, `opaque` 10, `quot` 4, `axiom` 2 — one JSON line each |
| **declarations** (named constants) | **2 059** | the 126 `inductive` records expand to 126 type formers + 154 constructors + 128 recursors; this is `export_file.declars.len()`, and the checker's own "Checked 2059 declarations" |
| scheduled **(declaration, σ) pairs** | 3 861 | the level-instantiation pre-pass's schedule; the unit the checker actually runs on |
| (declaration, σ) pairs **with a value** | **2 891** | `def` 2687 + `thm` 194 + `opaque` 10 — the declaration-typing ledger's denominator |

**The 1 777-vs-2 674 disagreement was neither corpus nor double counting: it
was a category error in a sentence.** `THREADING-CENSUS.md`'s cascade root is
2 674 *of the 2 891 (declaration, σ) pairs with a value* — the census's own
§1.2 row says so — but §3 item 3 called the same figure "2 674 declarations
whose own check gapped", and a declaration count larger than the file is what a
reader then had to reconcile. Corrected in place. The mechanism behind the
expansion is **universe-level instantiation, not monomorphisation of types**:
1 645 value-carrying declarations are scheduled at 2 891 ground σ.

### The exclusion, measured exactly

`init-prelude` contains **two** `axiom` records: `Classical.choice` — standard
per `mini::convert::is_standard_axiom` — and **`sorryAx`**, which is not. So
*"except skipped non-standard axioms"* removes **exactly one declaration**.
Measured both ways:

* Statically: no `def`, `thm`, `opaque` or `axiom` in the file contains a
  `Const` node for `sorryAx` — **zero references**, so `mini::unused_axiom`
  drops it as unused rather than declining the file.
* Dynamically: running the checker with `permitted_axioms` set to exactly
  Lean's three moves the verdict from "Checked 2059 declarations" to
  **"Checked 2058"**, and the schedule from 3 861 pairs to 3 859. The
  declaration-typing ledger does not move at all, because `sorryAx` carries no
  value and was never in its denominator.

Neither `propext` nor `Quot.sound` appears in `init-prelude` at all; the four
`quot` records are `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`.

So the goal's population is **2 058 declarations / 3 859 (declaration, σ)
pairs**, and 1 of 2 059 is skipped.

### The numerator, re-measured

| row | value |
|---|---:|
| `Dt::Seen` — (declaration, σ) pairs with a value | 2 891 |
| `Dt::Stored` — **…carrying `⊢ ⟦c⟧ ∈ ⟦T⟧`, sealed** | **26** |
| `Dt::Gap` — no certificate at all | 2 667 |
| `Dt::Conditional` — derived, discarded as conditional | 198 |
| `Dt::NoKey` / `Dt::Refused` | 0 / 0 |
| `Dt::Poly` — of the 26, level-polymorphic | 25 |
| uses answered from the store / missing | 1 325 / 28 060 |
| instructions | 194.23 G |

**26 of 2 891 is 0.90 %. 26 of 3 859 — every scheduled pair of every
non-skipped declaration, which is what the goal's sentence says — is 0.67 %.**
The checked-and-accepted half of the goal is at 2 059 / 2 059; the
fully-proven-theorem half is the number above.

### Three things the row is not saying, and all three matter

1. **A quarter of the goal's population is outside the denominator.**
   `Dt::Seen` counts only value-carrying declarations. Every inductive type
   former, constructor, recursor, `quot` constant and axiom — **413
   declarations / 968 pairs after the exclusion**, 20.1 % and 25.1 % — is not
   in it, and has no ledger row of its own. A ledger reading 2 891 / 2 891
   would still leave a quarter of the prelude's typing obligations unmeasured.
   Per-kind, `(declarations, pairs)`: `def` (1479, 2687), `thm` (156, 194),
   `opaque` (10, 10), `recursor` (128, 471), `ctor` (154, 261), `inductive`
   (126, 230), `quot` (4, 4), `axiom` (2, 4).

2. **26 is a count of pairs, not of declarations, and the two differ by
   roughly half.** Perturbing `DEFAULT_LEVELS` from `[0, 1]` to `[0, 1, 2]`
   moves the value denominator 2 891 → 3 959 and `Dt::Stored` 26 → 35, with
   `Dt::Poly` 25 → 34: **+9 stored pairs are additional σ of declarations
   already counted**. Those nine therefore contribute at least 18 of the 26, so
   the distinct Lean declarations behind the numerator are **at most 17, and at
   least 10** — against 2 058, between **0.5 % and 0.8 %**. The exact figure
   needs a field the ledger does not have; it is `distinct` in the
   specification below.

3. **`Dt::Seen` is a walk counter, not a denominator.** `note_dt(Dt::Seen)`
   is the first line of `TgBackend::store_declar_typing`, so a run that reaches
   fewer declarations reports a smaller denominator and a *better-looking*
   ratio. Today it is not vacuous, and that is now a measurement rather than an
   assumption: the pre-pass's **static** count of value-carrying scheduled
   pairs is **2 891**, equal to `Dt::Seen` to the digit. Nothing asserts it.

`Dt::Stored` is also bumped one line **before** `Sealed::new`, exactly as
`FALSE_ANCHORS` is — so the numerator is a count of sealed theorems only if the
seal never refuses. Instrumented: **5 229 `Sealed::new` calls on this file,
0 refusals**. True today, unasserted.

### The permanent row, specified

For whoever lands #126. Not landed here: every field needs
`checker/src/tg.rs`, which #125 holds.

**Landed 2026-08-10 (task #126), with three corrections to this
specification** — each measured, each noted at its field below. The row prints
as its own block after `level instantiations`; the CI test is
`the_translated_row_measures_the_goals_population_and_may_not_narrow`.

**Name:** `translated`, printed as its own block, not inside the `Dt` table —
the `Dt` rows are a breakdown of one population, and the point of this row is
that the population is not the goal's.

**Fields**, each a `u64`, each printed with its denominator on the same line:

| field | definition | today |
|---|---|---:|
| `scheduled` | (declaration, σ) pairs the pre-pass scheduled, **all kinds**, computed in `instantiations::compute_in` before any checking | 3 861 |
| `skipped` | pairs dropped as non-standard axioms, named in the line | 2 (`sorryAx`) |
| `population` | `scheduled − skipped` — **the denominator, printed inline** | 3 859 |
| `reached` | pairs the walk actually entered; a separate counter incremented at the top of the per-pair check, **not** derived from any `Dt` row | 3 861 |
| `eligible` | of `population`, the pairs whose declaration carries a value — today's `Dt::Seen` | 2 891 |
| `sealed` | pairs with a `Sealed` typing **published** — incremented *after* `Sealed::new` and after `publish`, never before | 26 |
| `distinct` | distinct `NameKey`s among `sealed` — the count the goal's sentence asks for | unmeasured, ≤ 17 |
| `sealed_by_kind` | `sealed` split over the eight `Declar` variants | `def`/`thm` only, today |

**Two assertions the row must carry, both in the report and in the test:**

* `reached == scheduled`, and `eligible ==` the pre-pass's static count of
  value-carrying scheduled pairs. This is the non-vacuity guard. Without it a
  run that reaches half the file reports `13/1445` and reads as honest.
* `sealed` is counted after the seal and the publish. If they are ever split,
  the report prints a bug-report line the way the `⟦False⟧` anchor already does
  (`"…but the thread is holding no sealed anchor"`), rather than a silent
  overcount.

**CI floor**, in `checker/tests/tg_tutorial.rs` beside
`the_declaration_typing_ledger_accounts_for_every_declaration`:

```text
assert_eq!(reached, scheduled);          // vacuity: not a ratchet, an identity
assert_eq!(eligible, static_value_pairs);// vacuity: ditto
assert!(population >= 3859);             // the denominator may not shrink
assert!(sealed >= 26);                   // ratchet, may only rise
assert!(distinct >= <first measurement>);// ratchet, may only rise
```

`population >= 3859` is the field that makes the eleventh instance of
"reporting success having done nothing" fail red: a change that narrows what is
scheduled improves `sealed / population` for free, and only a floor under the
denominator catches it. The two `assert_eq!`s are deliberately not ratchets —
a ratchet on a vacuity guard is a vacuity guard that can be loosened.

### The row as landed, and the three places the specification was wrong

```
  translated — the goal's own population, and how much of it is proved:
    0.67% of the population proved; 0.90% of the pairs that carry a value; 17 distinct declarations of 2059
    scheduled (declaration, σ) pairs, all kinds                          3861
    …skipped as non-standard axioms (sorryAx)                               2
    POPULATION (scheduled − skipped)                                     3859
    …pairs the walk entered                                              3757
    …scheduled pairs absorbed by Inductive/Quot (checked once)            104
    …of the population, carrying a value (eligible today)                2891
    SEALED AND PUBLISHED ⊢ ⟦c⟧ ∈ ⟦T⟧                                       26
    …distinct declarations behind them                                     17
      sealed def (of 2687 scheduled)                                       26
      sealed thm (of 194 scheduled)                                         0
      sealed opaque (of 10 scheduled)                                       0
      sealed axiom (of 4 scheduled)                                         0
      sealed inductive (of 230 scheduled)                                   0
      sealed ctor (of 261 scheduled)                                        0
      sealed recursor (of 471 scheduled)                                    0
      sealed quot (of 4 scheduled)                                          0
```

Every figure the specification predicted independently is reproduced to the
digit — 3 861 scheduled, 2 891 value-carrying, 26 sealed, 2 059 declarations —
which is the calibration that lets the three disagreements be read as findings
rather than as wiring faults.

1. **`reached == scheduled` is false, and the difference is 104.**
   `ExportFile::check_declar_all` checks an `Inductive` or `Quot` **once**, at
   the empty instantiation, however many σ the schedule lists for it — by
   design, since neither goes through `with_tc_and_declar` and neither has
   anywhere to put a σ. The walk therefore enters 3 757 of the 3 861 scheduled
   pairs. The identity is kept, and kept able to fail, by naming the absorbed
   pairs in a counter of their own: **`reached + collapsed == scheduled`**. Had
   the specified identity been asserted as written it would have failed on the
   first run and the natural repair — deriving `reached` from the schedule —
   would have destroyed the guard.

2. **`skipped` cannot be read off the parser's drop list, and must not be.**
   Whether `sorryAx` reaches the schedule at all depends on `permitted_axioms`:
   under `unsafe_permit_all_axioms` it is scheduled at 2 pairs, under Lean's
   three it never reaches the pre-pass and `scheduled` is 3 859 already. A
   denominator that moves with a config flag is not a denominator, so `skipped`
   is computed **from the schedule**, as the scheduled pairs of any axiom that
   is not one of Lean's three (the predicate is reimplemented in
   `checker/src/instantiations.rs`; `checker` does not depend on `mini`). The
   consequence is the one that matters: **`population` is 3 859 under either
   config.**

3. **`distinct` is 17 — the top of the bound, not the middle.** The
   perturbation argument bounded it at ≥ 10 and ≤ 17. Measured, all 26 sealed
   pairs belong to 17 distinct declarations, so 9 declarations contribute two σ
   each and 8 contribute one. **17 of 2 058 is 0.83 %**, and that is the figure
   the goal's sentence asks for.

`eligible` and `Dt::Seen` agree at 2 891 without an adjustment, and the
declaration-typing store's `Sealed::new` refused **0** times, so `sealed` and
`Dt::Stored` agree at 26 — but they now agree for a reason: the new counter is
bumped after the seal *and* after the publish, and a refusal both decrements
the numerator and prints a bug-report line.

Both non-vacuity guards were mutation-verified. Reporting `value_pairs` as
`scheduled` (a narrowed population that reads as a better ratio — the exact
failure the row exists to catch) fails on `population >= 3859`. Dropping the
`collapsed` accounting fails on the identity, and fails *first* through the
report's own bug-report line, which the test also asserts is absent — so a run
read without CI still says when its arithmetic does not close.

Cost: the pre-pass gains one pass over the demand map (2 059 entries) and the
walk gains three atomics per pair; unmeasurable against 194 G instructions.

## Where the lambda typing rule actually declines, and what the raw hoists are about — 2026-08-10

*Task #126, stage 2. Baseline `origin/master` at `d772b16`; `release`,
`--features tg,stepcount`, `vendor/arena-tests/good/init-prelude.ndjson`;
`perf stat -e instructions`. Two permanent ledger rows landed here. The ledger
is otherwise unchanged: 15 532 gaps, 2 247 escapes, 20 328 raw hoists
(32 / 1 640 / 18 656 by cause) before and after.*

### Why this was measured before anything was threaded

`THREADING-CENSUS.md` §2 names stage 2's largest named shape: **10 538 of the
20 328 raw hoists are about "a λ whose typing rule did not apply"
(`HtMiss::Lam`), against 2 970 the same rule does discharge — first place to
look.** `HtMiss` records the *subject's shape*, so that row says a lambda was
the thing being typed. It does not say the rule failed to apply, and it turns
out not to.

### `lambda typing declines, by cause` — the rule applies; the recursion runs out

Every `?` in `TgBackend::has_type_lam` and `has_type_lam_prop` is now
attributed. **35 321 declines on `init-prelude`:**

| cause | count |
|---|---:|
| the rule applied; the **BODY** has no typing | **32 831** |
| the target is not a function type at all | 1 019 |
| the target has no readable head | 545 |
| the target is a Π over a different domain | 372 |
| the discharge left unexpected assumptions | 294 |
| proof λ: the BODY has no typing | 259 |
| proof λ: the target is not `⟦∀x:A. β⟧` | 1 |
| *everything else* — no graph, no skeleton, skeleton shape, no fibre, fibre mismatch, retarget, discharge, lemma, `→` over a different domain | **0** |

**93 % of the declines are the recursion, not the rule.** The nine structural
ways the rule can fail — the graph, the skeleton, the fibre, the lemma
application — fire zero times between them on the whole prelude. The typing
rule for lambdas is not the missing piece and no work on it will move the
10 538. This refutes the census's "first place to look" as a direction while
confirming its count.

### What the untypeable bodies are, and what they are typed at

The cross-cut of the 33 090 `BODY has no typing` declines:

| the body was | count | | stated at | count |
|---|---:|---|---|---:|
| **a lambda** | **21 263** | | something else | 21 773 |
| an application of a defined constant | 4 218 | | `app(lam(…), x)` — beta-reduces | **8 496** |
| an application of a lambda | 3 782 | | `app(w, x)` for a context local | 2 030 |
| an application of an opaque constant | 2 209 | | a defined constant | 291 |
| a Π — needs `dprod_in_universe` | 690 | | `app(c, x)` for a defined `c` | 104 |
| a let, projection or literal | 435 | | curried, spine head a lambda graph | 101 |
| a local / an opaque constant / other | 234 | | curried, other | 36 |

Two readings, both actionable and neither about lambdas:

* **The decline is a nested-λ cascade.** 21 263 of the untypeable bodies are
  themselves lambdas, so one failure deep in a λ-chain is counted once per
  enclosing binder. The genuine leaves are **applications** — 10 209 of them,
  split over defined-constant, lambda and opaque heads — plus 690 Πs. The rule
  the residue wants is the *application* rule (and behind it `ty_const`), not
  the lambda rule.
* **8 496 of these obligations are stated at a target that beta-reduces**,
  while `HtClause::TargetBeta` discharges **125** obligations in the whole run.
  The existing ledger explains the shortfall: `has_type_target_beta` reaches
  12 874 redexes and loses 6 004 to *its own* `x ∈ A` premise and 8 624 to the
  reduct still not being typeable. The target-side reduction is a second front
  with the same shape as the subject-side one.

### The subject-only reach probe: splitting the census's 18 622

`Shared::typed_at` is keyed on the **pair** `(subject, target)`, so its
headline — 18 622 of the 18 656 never-checked raw hoists were "never a typing
rule's conclusion anywhere on the thread" — conflates a missing *fact* with a
missing *conversion*: a subject some declaration typed at a definitionally
equal target that interprets apart would count as never concluded. The new
subject-only index `Shared::typed_subj` separates them, cross-cut by whether
the subject is closed:

| of the 18 622 | count |
|---|---:|
| subject typed at some **other** target, closed, in an earlier declaration | 455 |
| subject typed at some other target, open, in this declaration | 5 |
| **closed subject no typing rule anywhere ever spoke about** | **7 717** |
| **open subject (free variables) no typing rule anywhere ever spoke about** | **10 445** |

**The census's refutation survives the sharper question.** A conversion-carrying
cross-declaration store reaches 460 (2.5 %), not the population — the same
order as the 34 the pair-keyed probe found. But the split of the remainder is
the new information, and it says the two halves need *different* mechanisms:

* **7 717 closed subjects.** A closed term no typing rule anywhere ever
  concluded anything about. Nothing can be transported to these, from any
  declaration, generalised or not; only a rule firing where none fires today
  produces the fact. These are not reachable by threading.
* **10 445 open subjects.** These carry the current declaration's free
  variables, so they are *substitution instances*: the term is a subterm of
  another declaration's value, entering by delta and instantiated at the
  current locals. The ground fact is absent by construction — it is about
  variables that did not exist when the other declaration was checked — but its
  **generalised** form (`∀w. w ∈ D → ⟦m⟧(w) ∈ ⟦B⟧(w)`) was concluded there,
  under that declaration's own binders. This is the only half of the residue a
  typing threaded down the reduction can reach, and reaching it means
  *instantiation of a generalised fact*, not recall of a ground one.

### What this says about stage 2's target signature

The census's mechanism — `whnf(e, ⊢⟦e⟧∈⟦T⟧)`, a typing carried alongside the
cursor and re-established by Leibniz at each step — is sound and cheap, but it
**does not by itself pay the beta rule's debt**, and the reason is structural:
`⟦(λx:A.b) a⟧ ∈ ⟦T⟧` says nothing about `⟦a⟧ ∈ ⟦A⟧`. Set-theoretic membership
of an application is not a statement about the argument. The cursor's typing is
transported correctly and consumed by nothing that owes a domain obligation.

What the measurement says the 10 445 need instead is a **generalised** typing
threaded through *delta*, not through beta: when `whnf` unfolds `c` to `v`, the
typings inference concluded about `v`'s subterms under `v`'s own binders are
available, and the reduction's own substitution is exactly the instantiation
that turns them into the facts the later beta steps ask for — with `⟦u⟧ ∈ D`
for each instantiated binder supplied by the *enclosing* beta step's own
obligation, which is where the chaining lives. That is a different signature
from the one §2 specifies, and it is the finding, not a plan.

### Cost

194.01 G → **194.39 G instructions (+0.20 %)**, ledger identical row for row.
The `LamDecline` bumps are atomics; the cost is the 33 090 `ht_shape`/
`ht_target` calls at the body cross-cut. `typed_subj` and the subject probe are
`stepcount`-gated and cost nothing in the default build.

### The target side reads the same handoff, and it is the same wall — 2026-08-10

*Same run and configuration. A **null result**, recorded as one.*

`TgBackend::arg_mems` — the store `infer_app` fills with every checked
argument's typing — had one consumer, `domain_obligation`, on the *subject*
side of the beta rule. `target_mem` owes the identical premise on the *target*
side (`app(lam(…), x) = t(x)` holds only for `x ∈ A`) and went straight to the
search. That asymmetry is now removed: `target_mem` reads the store first, with
the same `establishes` re-check, restating the entry over `assms ++ (its own,
less what is already there)` by `reassume`, since the caller here already holds
assumptions where `domain_obligation` asks with none.

| | |
|---|---:|
| premises that reached the handoff read | **2 119** |
| …answered from it, free of antecedents | 0 |
| …answered from it, under the check's own antecedents | **145** |
| `target beta: premise x ∈ A not settled` | 6 004 → **6 004** |
| `HtClause::TargetBeta` (obligations the clause discharges) | 125 → **125** |
| gaps / escapes / raw hoists | 15 532 / 2 247 / 20 328 — **all unchanged** |
| instructions | 194.39 G → 194.33 G |

**145 premises changed provenance and nothing closed.** Every one of them the
search settled anyway, from the same ambient-local antecedents; the 6 004 that
fail are premises for which the store has no entry at all, which is the same
population as the subject side's 18 656 seen from the other end. The
denominator is printed beside the numerator, and both handoff rows print even
at zero, precisely so the null is legible: a zero over an unstated denominator
is the shape of a probe that never ran, and this one ran 2 119 times.

The wire is kept rather than reverted for two reasons, neither of which is that
it helped: one store with two consumers is the state the census asks for, and
the 1 640 raw hoists that are the `ty_const` cascade convert into store entries
the day the shared constant store lands — at which point this read is where the
target side collects them. It is instrumented so that day is visible.

## The delta route, refuted before it was built — 2026-08-10

*Task #126. Same run and configuration. The coordinator's directive was to
build the mechanism named at the end of the previous section: a **generalised**
typing threaded through `delta`, instantiated by the reduction's own
substitution, targeting the 10 445 open subjects. It was measured first,
because the claim "the generalised fact exists" was mine, unmeasured, and
load-bearing. **It is false**, and the tranche was not built.*

### The probe

`Shared::typed_at` keys on the ground pair `(subject, target)`. For an **open**
subject — one carrying the current declaration's locals — a ground miss is
guaranteed and means nothing: the pair is about variables that did not exist
when the declaration the term came from was checked. The question that can be
asked is the abstracted one, and `Shared::typed_skel` asks it: every membership
any typing rule concludes is also filed with its free variables closed over, in
first-occurrence order.

Canonical without minting anything. `Formula::forall` closes a free variable
into a de Bruijn binder, so folding it over the pair's free variables gives a
form that depends only on the term's shape and compares across declarations and
across `Env`s — no fresh-variable pool, no ordering convention to get wrong.

**Calibrated on the closed subjects.** For a closed subject the skeleton *is*
the pair, so the closed rows of the skeleton probe must agree with the ground
probe. They do: 0 closed skeleton hits against 0 closed ground hits over 8 172
closed subjects. A skeleton hit where the pair missed would have meant the two
keys measure different things and the open rows could not be read.

### The result

| of the 18 622 never concluded at their pair | |
|---|---:|
| **open** subject, generalised membership concluded in an **earlier** declaration | **133** |
| open subject, generalised membership concluded in this declaration | 1 |
| **open subject, never concluded at any generality** | **10 316** |
| closed subject, skeleton concluded earlier / here | 0 / 0 |
| closed subject, never concluded at any generality | 8 172 |

**The delta route's population is 134, not 10 445.** 1.3 % of the open
subjects, 0.7 % of the 18 622. Building the transport — generalising at the
handoff write, matching the reduction's substitution, chaining each binder's
`⟦u⟧ ∈ D` from the enclosing beta step — would have been the largest machine in
this file for 134 obligations, and it would have measured clean.

Read together with the two earlier keys, the population has now been asked for
at four:

| the question | the key | reached |
|---|---|---:|
| was this very membership concluded anywhere? | `(subject, target)` | 34 |
| was the subject typed at *some other* target? | `subject` | 460 |
| was the **generalised** membership concluded? | `∀w⃗. subject ∈ target` | **134** |
| does the target-side twin find it in the same store? | `arg_mems` at `target_mem` | 145, closing **0** |

**The residue is not a transport problem at any level of generality.** The
facts were never derived, anywhere, by anyone, in any form. What is missing is
derivational power — and the decline ledger says where: the leaves of the
lambda cascade are applications (10 209) and Πs (690), and the 8 496 body
obligations stated at a beta-reducible target against 125 discharges are the
same wall seen from the target side. That is bucket (ii) by §3's own
classification, so §3's split has been corrected in place: the 18 656 were
filed under bucket (i) on the assumption that the facts existed and were being
dropped.

### The 7 717 closed subjects: 407 distinct terms, and what stands in the way

Asked as a separate question, because "closed" is a strong property: such a
term's typing needs no transporting and no generalising, it can simply be
concluded. **7 717 obligations, 407 distinct terms** — 223 lambdas, 88
applications of a defined constant, 44 Πs, 17 let/projection/literal, 14
applications of an opaque constant, 12 constants, 9 applications of a lambda.
So the cost of typing them on demand is 407 inferences, not 7 717, and the
arithmetic is not the obstacle. Two things are:

* **Not at the obligation site.** `domain_obligation` runs inside `TgBackend`,
  which is a *field* of the `TypeChecker` — the call is
  `tc.certifier.beta(tc.ctx, …)`, with the backend mutably borrowed and the
  context passed beside it. There is no path from the backend back to `infer`,
  and giving it one means restructuring the ownership.
* **At the construction site, with a risk to bound first.** These terms are
  built by the reduction, inside `whnf`, where `self` *is* a `TypeChecker` and
  `infer` is in hand. So the correct reading of "the typing arrives with the
  whnf call" is not a cursor-carried typing — which pays nothing, proved above
  — but **inference invoked at each beta contraction on the argument, handed
  to the backend through the existing `Certifier::app_arg_checked` store.**
  The risk is re-entrancy: `infer` calls `ensure_pi` calls `whnf`, and beta is
  81 % of all reduction steps, so this is the hot path calling itself. Measure
  the bound before building.

Ledger unchanged throughout: 15 532 gaps, 2 247 escapes, 20 328 raw hoists.
The probes are `stepcount`-gated and cost nothing in the default build.

## Typing the reduction's own arguments — the fifth route, and the one that pays — 2026-08-10

*Task #126. Baseline `origin/master` at `f791e3f`; `release`, `--features
tg,stepcount`, `good/init-prelude.ndjson`; `perf stat -e instructions`.
**Three ratchets moved, with the trade written below.** Escapes did not move.*

### Why deriving, after four transports failed

The census's residue — 18 656 raw hoists about terms no application check ever
visited — was asked for at four keys and none of them reaches it: the ground
pair 34, the subject at another target 460, the **generalised** membership 134,
the target-side twin 145 closing nothing. The fact was never derived anywhere,
at any generality, so nothing can carry it. The only thing that produces it is
a typing rule firing, and `TgBackend` cannot fire one — it is a *field* of the
`TypeChecker`, so `domain_obligation` has no path back to `infer`.

`whnf` does. `TypeChecker::beta_arg_typing` runs at the beta contraction in
`whnf_no_unfolding_reduce`, where the redex's argument and a `TypeChecker` are
in the same hand: infer the argument, convert its typing along `def_eq` to the
binder's domain, and hand it to the existing `Certifier::app_arg_checked`
store, which `domain_obligation` already reads. **This is the correct reading of
"the typing arrives with the whnf call"** — not the cursor-carried typing §2
specified, which was proved to pay nothing.

### Three restrictions, each measured rather than assumed

| restriction | why | measured |
|---|---|---|
| **closed arguments only** (`has_fvars`) | inference *reduces*, so it drives more `whnf`, which raises more obligations | unrestricted: obligations asked 39 951 → 52 862, **+16.8 % instructions, escapes 2 247 → 3 033**. Closed-only: obligations asked 40 060 (flat), +0.47 %, escapes unmoved |
| **`Check`, not `InferOnly`** | the argument's sub-derivations are what make its typing derivable | `InferOnly` on the same population: **+32** discharged. `Check`: **+977** |
| **outermost argument only** | `derive_beta` peels one binder at a time, so `a₁`'s domain is `lam`'s own and needs no instantiation; the inner ones would mean rebuilding the intermediate lambdas the composite `inst` exists to avoid | the outermost alone reaches 3 313 redexes |

Plus two safety properties. The backend is **asked first**
(`Certifier::wants_arg_typing`, default `false`, so the null backend pays
nothing), and the conversion uses **`def_eq`, not `assert_def_eq`** — a redex
the reduction built need not be well-typed, and a hard failure would turn an
accepted file into a rejected one. The corpus confirms it: 152 matched, 0
mismatched, no `good/` file newly rejected.

### What it bought

| | `f791e3f` | with `beta_arg_typing` |
| --- | ---: | ---: |
| closed arguments asked / typed | — | **3 313 / 3 313** |
| typing obligations discharged | 5 373 | **6 350** (+977) |
| handoff answers, **outright** | 102 | **3 266** (32×) |
| handoff answers, under antecedents | 10 198 | 10 200 |
| raw hoists, total | 20 328 | **19 460** (−868) |
| …**never checked at an application** | 18 656 | **16 502** (−2 154) |
| …a hole at their own check | 1 640 | 2 926 (+1 286) |
| **escapes** | 2 247 | **2 247** — unmoved |
| gaps | 15 532 | 15 761 (+229) |
| instructions | 194.39 G | 195.32 G (**+0.47 %**) |

**3 313 asked, 3 313 typed** — every closed argument the backend wanted,
inference typed and `def_eq` matched, with no declines. The 2 154 fall in the
census's own residue row splits honestly: **868** obligations are now answered
that were raw-hoisted before, and **1 286** moved into "a hole at their own
check" — the on-demand inference visited them and *its* typing was a hole, so
they are re-attributed from "nobody ever looked" into the `ty_const` cascade,
which is bucket (ii). That re-attribution is a gain in knowledge, not in
proving, and it is stated separately for exactly that reason.

### The trade: three ratchets moved, and why each

`gaps <= 15542 → 15761`, `proj_reduce <= 630 → 661`, `miss_cond <= 1214 →
1244`. **The +229 gaps are not a new kind of gap.** Row by row, and these six
rows are the whole of it:

| row | Δ | what it is |
|---|---:|---|
| `trans over an admitted premise` | +78 | composition downstream of the two below |
| `congruence over an admitted premise` | +40 | ditto |
| `symm over an admitted premise` | +29 | ditto |
| `eq_cache` | +27 | ditto |
| `proj_reduce` | +31 | interpreted structures — named bucket (ii) |
| `nat_reduce` | +24 | milestone 4 primitives — named bucket (ii) |

The on-demand inference performs reductions the run did not perform before, and
they land on rules that were **already admitting**. Nothing that was derived
before is admitted now. In particular **the ι path is flat** — no `iota` row
moved — so `the_general_iota_rule_computes_on_the_prelude`, whose guard is a
total-gap count, is being re-based by a neighbour's traffic and not by its own
subject regressing. That is recorded at the assertion, not only here, because a
guard re-based silently is a guard that has stopped guarding.

The escape ratchet is the one that did **not** move, and it is the one the
standing rule is about: 2 247 before and after. The +229 gaps are accounted, not
escaping.

### The fixture

`beta_domain_obligation_reads_the_application_checks_handoff` grew from three
atoms to four. Its `unchecked` atom pinned the honest `Conditional` hoist for a
closed argument nobody inferred — which is precisely what this tranche closes —
so that atom is **restated** (now: `Proved` and unconditional) rather than
deleted, and a new `unchecked, open` atom takes over the falsifier it used to
carry. Mutation-verified: deleting the `has_fvars` guard turns `unchecked,
open` red.

### The inner binders of a nested redex — built, measured, removed — 2026-08-10

*The named successor to the tranche above. It works, it reaches 2.5× as many
arguments, and it is not shippable. Recorded so nobody rebuilds it.*

`derive_beta` peels a lambda nest one binder at a time, so the domain it keys
`aₖ` at is the *k*-th lambda's — instantiated for `k > 0`, and reachable only by
rebuilding the intermediate lambdas the composite `inst` exists to avoid. The
walk advances `cur = inst(body, [aₖ])`, exactly as `derive_beta` does, so the
keys line up; the intermediate lambdas are only built when an O(1) scan says
some inner argument is closed and unstored.

| | typed | never-checked hoists | **escapes** | gaps | instr. |
| --- | ---: | ---: | ---: | ---: | ---: |
| baseline (`f791e3f`) | — | 18 656 | **2 247** | 15 532 | — |
| **outermost only (shipped)** | 3 313 | **16 502** | **2 247** | 15 761 | +0.47 % |
| + inner binders | 8 281 | 12 347 | **5 909** | 20 869 | +5.7 % |
| + inner binders, closed nests only | 6 442 | 16 688 | **5 661** | 20 561 | +4.6 % |

**Escapes 2.6×. That is not a trade, it is a regression**, and the standing
rule is absolute about this counter for the reason the run demonstrates: the
walk doubles the inference volume, inference *reduces*, reduction raises new
obligations (40 060 → 62 199 asked), and those escape. It is the same mechanism
that disqualified the open arguments, at a different scale.

Two things make the verdict clean rather than a judgement call:

* **The restriction that saved the outermost tranche does not save this one.**
  Requiring the nest to be closed *throughout* — so every intermediate lambda
  is closed and none mentions a local — still escapes 5 661.
* **The middle row's 12 347 is not a win.** It comes with 22 139 more
  obligations asked; the population shrank by being outrun, not by being
  answered. And the closed-nest row leaves that population at **16 688,
  actively worse than the 16 502 the shipped code reaches by doing less.** A
  measurable that moves the right way while its own denominator moves further
  is why this stage reports raw hoists beside obligations asked.

What it would take is a way to type an argument that does not go through
`infer` — which is the same research question the open arguments raise, and not
this tranche's. The finding is recorded at
`TypeChecker::beta_arg_typing` so the next reader meets it before the idea.

### Can the type be read off instead of inferred? — 4 119 of 16 502, and the obstacle that remains — 2026-08-10

*The research question the previous five results converged on was "a way to
type an argument that does not go through `infer`". A fully applied
constructor is the candidate: its type is its declared type,
level-substituted and instantiated at its own arguments — a substitution into
something the environment already holds, no reduction, no new obligations.
Measured before anything was built.*

`TgBackend::declared_type_shape` runs at every raw hoist about a term no
application check visited, and measures the **whole** claim rather than the
shape: for a saturated head it builds the instantiated declared type,
interprets it, and compares it to the domain actually being asked.

| of the 16 468 | |
|---|---:|
| **constructor, saturated, instantiated type *is* the domain** | **906** |
| constructor, saturated, type is not the domain | 153 |
| **constant, saturated, instantiated type *is* the domain** | **3 213** |
| constant, saturated, type is not the domain | 450 |
| constant, partially applied | 3 |
| not an application of a constant at all | 11 743 |

**4 119 — 25 % of the residue — have a target the declared type hits exactly.**
No conversion, so no `def_eq`, so no reduction: the cost that disqualified the
open arguments, the inner binders and the two inference-flag variants is simply
absent for this population. That is the first route measured this session whose
cost is structurally zero rather than merely small.

**But the type is not the membership, and that distinction is the whole of the
remaining work.** Reading `Eq.refl a : a = a` off the environment gives the
*type*; the certificate `⊢ ⟦Eq.refl a⟧ ∈ ⟦a = a⟧` still has to be derived, and
the constructor rule that derives it (`HtClause::CtorApp`, already firing 3 291
times a run) needs `⟦aᵢ⟧ ∈ ⟦Aᵢ⟧` for each argument. So these 4 119 are cases
where the rule *applies* and its recursion did not complete — the same
untypeable-argument cascade, met one level up.

That is not a dead end, and the reason is the shape of the debt rather than its
size. The rule is **conditional**: `⊢ (a₁ ∈ A₁ ∧ …) → c a⃗ ∈ T[a⃗]`. Hoisting
those per-argument antecedents instead of the whole membership is strictly
better debt, and this project has already measured why — the 2026-08-10 handoff
closed ten escapes for exactly this reason: *"the raw hoist assumed the whole
membership, which no binder discharges; the handoff carries per-local
antecedents, which binders do discharge."* The named next tranche is therefore
not "type these 4 119" but **"stop hoisting the whole membership where the
constructor rule can decompose it"**, and its measurable is escapes, which is
the counter every other route moved the wrong way.

The 11 743 remainder — dominated by the 223 distinct closed lambdas — is not
reachable this way and stays where §2 leaves it.

### Decomposing the hoist into per-argument antecedents — built, measured, removed — 2026-08-10

*The named successor to the entry above, and its refutation. The tranche was
"stop hoisting the whole membership where the constructor rule can decompose
it", resting on one claim: that per-argument antecedents are debt a binder can
discharge while a whole hoisted membership is not. **The claim is false of this
population**, and the census that shows why is shipped.*

`HtClause::CtorApp` is conditional — `⊢ (a₁ ∈ A₁ ∧ …) → c a⃗ ∈ T[a⃗]` — but
`has_type_ctor_app` declines the *whole* clause when any premise cannot be
settled, sending the caller to the raw hoist. Acquiring the unsettled premise as
an antecedent instead is one line, and the same move `has_type_local` already
makes for a context local's own typing.

**Measured before it was built.** A decline census at the rule itself, counted
only from the rule lookup onwards (the clause is tried at every application, so
"the head is not an interpreted inductive" is the whole traffic of the checker
and says nothing):

| where the ctor rule was found | |
|---|---:|
| fired | 1 739 |
| **a premise unsettled** | **3 066** |
| no rule at these levels | 2 441 |
| wrong arity — a partial or over-application | 2 911 |
| instantiate / premise shape / assemble | 0 / 0 / 0 |

Of the 3 066, 2 664 premises had already settled before the one that did not, so
the debt really is concentrated: most of each declined clause was paid for. And
**1 376 — 45 % — are premises about a context local**, which is exactly the
shape the tranche wanted.

#### The refutation, in one row

A binder introduces `⟦w⟧ ∈ ⟦A⟧` at the local's *declared* `A`, and nothing else.
So the premise's domain has to be that, or the acquired antecedent is stated
where no binder ever discharges it. Bucketed rather than argued:

| of the 1 376 local premises, the rule's domain was | |
|---|---:|
| the local's own type | **0** |
| its type, up to a delta chain | **0** |
| the other unfolding direction | **0** |
| unrelated — and a **set application** `app(⟦T⟧, p⃗)` | **1 376** |
| unrelated, anything else | 0 |

The first two rows are 0 *by construction* — `assumed` would have matched them —
and are counted anyway so that the finding reads as evidence rather than as an
absent measurement: a positive `SameDomain` would mean `assumed` is failing to
match what it should. **The population is 100 % the un-contracted Lean-facing
curried spine**: the rule states its premise at `app(⟦T⟧, p⃗)` while the local's
type interprets to `U(…)` or `⟦Bool⟧`. What is missing is the *contraction* —
`has_type_target_beta`'s job — not a decomposition.

#### Built anyway, and measured five ways

Obligations asked stayed flat at **40 060** in every variant — the first route
this session that does not outrun its own denominator — and the goal's own
counter (**26 sealed, 17 distinct declarations**) is identical to the digit
throughout.

| | escapes | gaps | raw hoists | asked |
| --- | ---: | ---: | ---: | ---: |
| declining (shipped) | **2 247** | 15 761 | 16 502 | 40 060 |
| acquire every unsettled premise | 2 252 | 15 736 | 15 745 | 40 060 |
| …at most one per clause | 2 252 | 15 736 | 16 027 | 40 060 |
| …only a local argument | 2 249 | 15 751 | 15 977 | 40 060 |
| …only a non-local argument | 2 250 | 15 746 | 16 270 | 40 060 |
| …only at the outermost obligation | **2 247** | 15 761 | 15 881 | 40 060 |

**Escapes do not fall in any variant**, so the standing rule applies and the
route is removed. The restriction that saved the outermost tranche does not save
this one either, and it fails in a new way worth naming: the outermost-only row
is free because it is **inert**. Escapes, gaps and the sealed count are
unchanged to the digit; the only number that moves is the raw-hoist
attribution, and −621 there is knowledge and not proving — the same distinction
`ArgMem::RawGapAtCheck`'s doc draws about its own row. **A variant whose sole
effect is to relabel 621 hoists is the "skip is not pass" failure wearing the
shape of a win**, and reading it as one is precisely what two-sided reporting
exists to stop.

#### What is kept

The decomposition is gone; the census is not. `CtorDecline`, `CTOR_PREM_SHAPE`
and `LocalPrem` ship, print zero when nothing reaches them, and were verified
side-effect free — the whole `init-prelude` ledger is byte-identical to the
baseline with them in. The verdict table is at `TgBackend::has_type_ctor_app`,
so the next reader meets it before the idea.

**The edge this localises.** The standing rule says a stage that does not move
escapes has left a specific edge unthreaded, and here the per-clause counters
name it: the general inductive's constructor rule states its premises at the
curried spine `app(⟦T⟧, p⃗)`, and `has_type` reaches that only through
`has_type_target_beta`. The next question is therefore not about hoisting at all
but about why the target-beta clause does not contract these 1 376 — which is a
question about `target_head_step` and its own domain premise, not about the
constructor rule.

### The head reduction that never reached its delta branch — escapes 2 247 → 2 232 — 2026-08-10

*The edge the refutation above localised, measured at the clause and then
closed. **The first fall of the escape ratchet this stage**, after seven routes
that could only trade it away.*

The entry above ended by naming a question rather than a route: the general
inductive's constructor rule states its premises at the curried spine
`app(⟦T⟧, p⃗)`, `has_type` reaches that only through `has_type_target_beta`, and
that clause was not firing on the 1 376. So: why not.

#### Measured at the clause, in the shape that worked at the rule

A decline census over every exit of `target_head_step`, all rows printed
including the ones expected to be zero. 97 307 invocations, recursive calls
included (`CurriedOk`/`CurriedHeadMiss` are the rows to subtract if a count of
obligations served is wanted — said in the doc, because a census with an
ambiguous denominator is the thing it exists to avoid):

| one head reduction of a type | |
|---|---:|
| the target is not a set application — never this clause's business | 67 869 |
| contracted a redex / reduced a curried head / unfolded a defined head | 6 870 / 1 081 / 1 854 |
| **beta's own premise `x ∈ A` not settled** | 6 004 |
| the curried head's own reduction declined | 2 810 |
| **the head's shape is not recorded** | 4 955 |
| **the target's shape is not recorded** | 5 195 |
| the head is opaque | 669 |
| no graph / did not assemble / wrong target | 0 / 0 / 0 |

The two "not recorded" rows together are **larger than the domain-premise row**,
which is not what a reduction-cost story predicts. Splitting them by whether the
*term* is an application, when the table says it is not:

| | |
|---|---:|
| head unrecorded, and not an application either | 2 032 |
| **head IS an application; the table was not told** | **2 923** |
| target unrecorded, and not an application either | 4 945 |
| **target IS an application; the table was not told** | **250** |

**3 173 declines caused by the side table rather than by the term.** And on the
1 376 themselves, asked both ways:

| of the 1 376, could target-beta start | via `parts` | via the term |
|---|---:|---:|
| head is a λ graph | 0 | 0 |
| head is curried | 394 | 394 |
| head is a defined constant | **0** | **982** |
| head shape unknown | **982** | **0** |

All 982 flip. `TgBackend::parts`' own header already said this would happen —
the table is "redundant, and retained only because retiring it moves this
backend's frontier counters", and its misses are "the silent kind: a term the
kernel itself built read back as structureless".

#### The defect, and the one-line shape of the fix

`target_head_step` looked the head's shape up in `parts` and returned `None`
when it was absent — **before considering any of its three branches**. Two of
those branches read the shape. The third does not: `app(c, x)` for a defined
constant unfolds `c` out of `abbrev_defs`, and never touches `hsym`/`hargs`. So
the clause was refusing a delta step it could perform, on terms it had every
means to reduce.

The lookup is now optional and gates only the two branches that use it. Nothing
else changed: no new rule, no new obligation, `parts` still in place, the
existing `l != *ty || r != ty2` check still deciding what comes out.

#### What it bought

| | before | after |
| --- | ---: | ---: |
| **escapes** | **2 247** | **2 232** |
| gaps | 15 761 | 15 734 |
| **derived (real kernel `Thm`)** | 159 791 | **159 803** |
| obligations asked | 40 060 | **40 060** |
| raw hoists, never checked | 16 502 | 16 233 |
| unsettled ctor premises about a local | 1 376 | 798 |
| instructions | — | +0.67 % |

**Obligations asked did not move.** That is the whole difference between this
and the seven refuted routes, every one of which paid for its answers with new
obligations that escaped: this one contracts redexes that were already there, so
the debt is discharged where a binder can see it rather than manufactured
elsewhere. Every row of the gap ledger moved down or stayed — `trans over an
admitted premise` −4, `symm` −4, `proj_reduce` −2, `beta: the lambda has no
function-graph interpretation` −2 — and **nothing that was derived before is
admitted now**. +0.67 % instructions, against +0.47 % for the one other shipped
route and +5.7 % for the rejected inner binders.

#### The ratchets

Both are **tightened**, not bought: gaps 15 761 → 15 734 and escapes 2 257 →
2 232. A ratchet that only ever loosens has stopped measuring, and this is the
first chance this stage has had to move one in the right direction.

One reach ratchet is **re-based with a written trade**:
`projection_reduction_is_a_rule_fed_by_inference` asserts that at least 11
projection reductions reach the threaded derivation, and 9 now do. Two
reductions *lost* and two *not attempted* read identically in that row, so the
distinction is checked rather than assumed — `gap: proj_reduce` fell 661 → 659
in lockstep, the three search rows are unmoved at 34/41/0, and no ledger row
rose. It is the population, not the rate, exactly as that test's own 630 → 661
move was. The trade is at the assertion as well as here.

#### Still uncounted

The **3 213 `ConstMatches`** half of the 4 119 remains unmeasured: the census
covers the constructor rule, and a constant application has no conditional rule
to decompose. It is also now the *older* question — the 2 923 + 250
table-caused declines outside the constructor population are closed by this
change wherever the delta branch serves them, and what remains of them is
`ThStep`'s business rather than `CtorReach`'s.

### Beta's own domain premise: 6 170, and it is a missing fact — 2026-08-10

*The largest genuine decline left by the census above, asked the same way. The
suspicion going in was that it would be the second instance of the
`target_head_step` pattern — a component reading a cache's absence as a fact
about the world. **It is not**, and the rows that say so are mostly zeros.*

`target_mem` derives beta's premise `x ∈ A` or declines; it never assumes it. So
the question is not why it refuses but where the premise could legitimately come
from. Census at the clause, every exit, zeros included, partition exact:

| beta's own domain premise `x ∈ A` | 13 856 |
|---|---:|
| an assumption in force said so | 293 |
| a term-level fact about the operators | 409 |
| a constructor's membership | 5 265 |
| an inductive type in its universe | 223 |
| the application check's handoff held it | 245 |
| the `has_type` recursion derived it | 1 251 |
| **no Lean node interprets to the subject** | **5 250** |
| a node was found; the recursion still declined | 920 |
| a node was found that reinterprets to something else | **0** |

The rows sum to the denominator. They did not on the first run — the handoff
return was uninstrumented and 245 went missing — which is the whole reason a
census states its total.

#### Four rows, three of them zeros

| | |
|---|---:|
| declines where the subject was **already assumed at another domain** | **0** |
| …and nothing in scope mentioned it at all | 6 170 |
| no-node subjects that are open set **applications** | 5 250 / 5 250 |
| …whose head is a **λ graph** (so the subject is itself a redex) | **0** |
| …that **this backend built** — in `parts`, absent from `exprs_rev` | **5 250 / 5 250** |
| a node found that reinterprets to something else | **0** |

Read together these close every cheap route and identify the expensive one:

* **Not a conversion.** 0 of 6 170 have the subject assumed at another domain.
  This is the sharpest contrast with the constructor-premise result above, where
  the answer was 1 376 of 1 376 and the debt *was* a conversion. The same
  question, asked at two clauses, gets opposite answers — which is why it is
  asked rather than assumed.
* **Not a contraction.** 0 have a λ graph at the head.
* **Not a cache.** Every one of the 5 250 is a term the *derivation* assembled
  and the *interpretation* never produced — a reduct, living only in the target
  theory. `exprs_rev` is right to have no node, and `NodeMismatch = 0` says it
  is not lying. This is exactly what `target_head_step` was **not**: there the
  term carried the structure and the table had merely not been told; here there
  is no node to find.

#### The verdict, and what it would take

**The eighth measured dead end.** What is missing is a term-level route to
`app(f,a) ∈ dom` that does not pass through an `ExprPtr`. The prelude has the
shape of one — `fs_app_mem`, "a function's values lie in its codomain" — but
using it needs `f ∈ fs(A, dom)` for a head that is a partially reduced spine
(4 438 curried, 812 a defined constant), and nothing on the thread holds a
function-space membership for those. `has_type_app` derives the analogous fact,
but reads the `Π` off the head's *syntactic Lean type*, which is precisely what
a reduct does not have.

**Both halves of that reading are wrong, and the next section is the
measurement that refutes them.** The subject has no node; its *leaves* all do,
and the composite is one `foldl_apps` away, so the route does not need a new
derivation. And closing the clause completely moves the ledger by exactly zero.
The paragraph that used to stand here — "not reachable by threading, by
transport, or by another lookup … a derivation question for `derived/`" — was a
diagnosis from the consumer's side that never asked whether the premise was
*binding*, and it is corrected rather than deleted because it is what the
`derived/` tranche was briefed from.

The residual 920 do have a node; 638 are applications of an **opaque** constant,
the uninterpreted-inductive obstruction, which is a named bucket and not this
clause's problem.

Ledger unchanged with the census in: escapes 2 232, gaps 15 734, 159 803 derived
— byte-identical, so the measurement is side-effect free.

### The 3 213 `ConstMatches` are the goal counter seen from the inside — 2026-08-10

*The oldest open item of this stage, and it closes as a verdict rather than as
work. Census at the clause, zeros included, total stated — the method's ninth
answer at a measurement each.*

A quarter of the raw-hoist residue is a saturated constant application whose
instantiated declared type **is** the domain. The *type* is readable off the
environment with no reduction; that is what the original 4 119 measured. The
*membership* needs `has_type_app`, once per argument, and each use needs the
head's own typing — so a spine `c a₁ … aₙ` needs `⊢ ⟦c⟧ ∈ ⟦T_c⟧` for the head
**constant**.

Asked as a store lookup, not a derivation:

| of the 3 213, the head constant's own typing is in the store | |
|---|---:|
| **yes** | **3** |
| no | 3 210 |
| no key, or not a constant head | 0 |

And the clause's own census, every exit:

| `app(f,a) ∈ ty` | 47 617 |
|---|---:|
| concluded by the dependent product | 492 |
| concluded by the function space | **0** |
| the head could not conceivably be typed (shape screen) | 3 939 |
| the head has no syntactic type | 9 970 |
| its type is not a `Π` | 514 |
| **the head's own typing at that `Π` is not available** | **32 553** |
| …and the spine's head is a **constant** | **32 553** |
| …and it is not | **0** |
| the argument's typing is not available | 149 |
| no `Π` site / wrong domain / no fibre / did not assemble | **0 / 0 / 0 / 0** |

**68 % of every failure of this clause is one step, and that step is a constant
head, 32 553 out of 32 553.** Nothing else fails at all: the dependent-product
machinery — sites, domains, fibres, assembly — is a clean four zeros. There is
no defect here to find.

#### The verdict

This population is not reachable by plumbing, and it is not an eighth or ninth
dead end in the sense the others were. **It is the goal counter seen from the
inside.** `⊢ ⟦c⟧ ∈ ⟦T_c⟧` is precisely the theorem the `translated` row counts,
and it stands at **26 sealed of 2 059 declarations**. Only 3 of the 3 213 have
one. The recursion is topological — a declaration's typing needs the typings of
the declarations its own type is built from — and with 26 sealed there is almost
no base for it to stand on.

That also explains the asymmetry with the constructor rule, which fires 3 291
times a run against this clause's 492. **A constructor's base case is
supplied**: `CtorRule` is a derived theorem about the constructor, built in
`derived`. An ordinary constant has no such supply, and the only way to get one
is to have checked the declaration.

**So the lever for this quarter of the residue is the coverage and the order of
declaration typings — the `translated` row — and not any clause of `has_type`.**
That is a different kind of item from everything this stage has produced, and it
is the one the goal statement was always about.

#### Two nulls recorded as nulls

* **`HtClause::AppFs` fires 0 times** on this corpus. The function-space branch
  exists for typings that `derived`'s ι minor-premise chains state at `fs`, and
  none of them reaches this clause. Its lemma, `fs_app_mem`, is the same one the
  `target_mem` entry above identifies as the shape of what that population
  needs — so the branch is not dead code so much as *not yet reachable*.
* The `fs` branch's shape test was switched from [`TgBackend::parts`] to
  `Term::as_app`, applying the `target_head_step` lesson. **It changed
  nothing**: the whole `init-prelude` ledger is byte-identical, and the
  diagnostic counter for "the `Π` is an application only the term knows" is
  **0**. The defect does not recur here, and that is measured rather than
  assumed.

### Why 26: it is a wall, not a bootstrap — 2026-08-10

*The framing the entry above produced was that the goal is one recursion needing
a base. **Measured, that is wrong**, and being wrong about it is the most useful
thing this stage has established: it redirects the work from ordering to a
single missing capability.*

The hypothesis was testable and this is the test. If the goal were a
bootstrapping problem, the declarations that fail should be blocked by *other
declarations*, and sealing a few heavily-named ones should unblock many.

Aggregate counters cannot answer it — they say how many fail, not which, and
"is the next failure blocked by the last" is a question about individual
declarations in walk order. So: one line per declaration with a value (outcome,
gap tag, name, and the constants its **value** mentions), env-gated, analysed by
`scripts/decl-frontier.py`.

#### One tag

| declarations with a value | 2 891 |
|---|---:|
| sealed | 26 (17 distinct names) |
| derived only under antecedents | 198 |
| **no certificate at all** | **2 667** |
| …by tag: **`ty_premise_missing`** | **2 667** |

**One tag, 2 667 of 2 667.** One blocker repeated, not a long tail — the two
possibilities the census was built to separate, separated on the first run.

#### And it is not the dependency graph

A dependency blocks only if it is **itself a value-carrying declaration that is
not sealed**. A reference to an inductive, a constructor or a recursor is not a
blocker: `derived`'s own theorems serve those, which is why `CtorApp` fires
3 291 times against `has_type_app`'s 492. Counting them as blockers is the easy
mistake and the first cut of this analysis made it — it collapsed the ready set
to 20 and would have "confirmed" the bootstrap story.

| unsealed (2 865), by number of blocking declarations | |
|---|---:|
| **0** | **1 040** |
| 1 / 2 / 3 / 4 / 5 / 6+ | 591 / 408 / 263 / 273 / 99 / 191 |

**1 040 declarations — 36 % — have nothing blocking them and fail anyway**,
every one tagged `ty_premise_missing`. In walk order they are `Eq.ndrec`,
`cast`, `rfl`, `Nat.lt`, `Pow.casesOn`, `HPow.hPow`. And the cascade is flat:
sealing the ten most-named blockers (`Eq.ndrec`, `OfNat.ofNat`, `instOfNatNat`,
`eq_of_heq`, `Unit`, …) moves the ready set from 1 040 to **1 126**. Eighty-six,
for ten base cases.

**The dependency graph is not the constraint.** The base is not missing; the
declarations at the base fail for the same reason as everything else.

#### What the reason actually is

`TyGap::Premise` means "a rule was asked and one of its premises was already a
hole", which is true of every cascade and identifies nothing. Split across the
five sites that raise it:

| which rule found its own premise a hole | 12 982 |
|---|---:|
| **`ty_conv`: the subject's own typing** | **8 045** |
| **`ty_app`: the argument's** | **4 693** |
| `ty_conv`: the typing was there, the *equality* was admitted | 244 |
| `ty_app`: the **function's** typing | **0** |
| `ty_app`: both | **0** |
| `ty_lam`: the body's, under the binder | **0** |
| `ty_let`: the body's | **0** |

Four zeros, and they are the finding. The structural rules never lack their
premise: a lambda's body is always typed, a `let`'s body is always typed, and a
function's typing is present at **every one** of the 4 693 applications whose
*argument* is missing. The entire within-declaration cascade is two things —
**a conversion whose subject has no typing, and an application's argument**.

That is the same population this stage has been measuring all along, arriving
from the other end: `domain_obligation`'s raw hoists are arguments without
typings, and here they are again as the reason 2 667 declarations are not
translated. It is one obstacle seen at two layers, not two.

#### What this changes

The goal is **not** approached by ordering the declarations better or by
hand-sealing base cases; both were plausible before this measurement and neither
survives it. It is approached by typing **arguments** and **conversion
subjects** — and the honest position after nine measurements is that the eight
refuted routes were all attempts at exactly that, seven of which paid for their
answers in escapes. The one that worked, `target_head_step`, worked because it
made an existing clause reach terms it was already shaped for.

The lead this section named — a function-space membership for reduced spines,
to give `has_type` a way to type an application without an `ExprPtr`, 4 693 of
these being applications — **is closed as a dead end by the section below**,
which measured its supply at 0 of 5 250 and its value at zero rows of the
ledger. It is corrected here rather than deleted because it is what the
`derived/` tranche was briefed from.

## Beta's own domain premise is not a blocker — 2026-08-10

*The `derived/` tranche the section above briefed, which measured its own brief
before building and found nothing left to build. Instrument:
`scripts/spine-probe.diff`, worktree-only. Two load-bearing claims were tested
and both failed, so no construction was written; "0 of 5 250" below is why
writing one would have been the twelfth recorded "skip is not pass".*

### The brief

Every `init-prelude` declaration is to carry a fully proven typing theorem, and
the census above named beta's own domain premise `x ∈ A` (13 856 firings,
6 170 declines) as the largest single blocker in the way. Its reading was that
5 250 of those declines need `app(f,a) ∈ dom` derived **without** an `ExprPtr`,
that `fs_app_mem` is the shape of the answer, and that supplying its antecedent
`f ∈ fs(A, dom)` for a partially reduced spine is a `derived/` question.

Two claims, asked in order: *is the antecedent suppliable?* and, before any of
it, *is the premise binding?*

### The population, split before anything was built

The probe peels each no-node subject's application spine to its atom head and
counts what is there. Denominator 5 250, exact.

| | |
|---|---:|
| spine length 1 / 2 / 3 / 4 / 5 / 6 / 7+ | 812 / 1 682 / 1 527 / 1 045 / 136 / 32 / 16 |
| atom head is a **defined constant** (equation in `abbrev_defs`) | 5 073 |
| atom head is an opaque symbol | 177 |
| atom head is a λ graph | **0** |
| atom head is a free variable | **0** |
| **atom head has a Lean node** | **5 250 / 5 250** |
| **every spine argument has a Lean node** | **5 250 / 5 250** |
| the domain `dom` is a nullary symbol / another application | 3 594 / 1 656 |
| the domain is `fs(_,_)` or a dependent product | **0** |

Spine length 1 is exactly the 812 the earlier census called "head is a defined
constant", and 4 438 of length ≥ 2 are its "head is curried": the same
partition, read off the term instead of one level of the table.

### Claim 1 refuted: the antecedent has zero supply

`typed_at`/`typed_subj` record every `(subject, target)` any typing rule has
ever concluded, across the whole run. Asked of these 5 250:

| | |
|---|---:|
| this very membership `x ∈ dom` concluded anywhere | **0** |
| the subject typed at *some* target, ever | **0** |
| the **immediate head** typed at some target, ever | **0** |
| the **atom head** typed at some target, ever | **0** |
| every spine argument typed at some target | 816 |
| the immediate head's target is `fs(A, dom)` — `fs_app_mem` closes it | **0** |

There is no `f ∈ fs(A, B)` to retarget because there is **no typing for `f` at
all**, at any target, from any declaration. A `derived/` lemma whose antecedent
is a function-space membership for the head would have had a supply of 0 of
5 250 — a proof no consumer shape can feed. (The wider figure it is an instance
of: 26 constant typings stored of 2 891 declarations with a value, and 6 389
typing obligations discharged of 40 060.)

### Claim 2 refuted: the node is one call away, and closing the clause is worth nothing

Every leaf has a node, so the composite the index lacks can simply be rebuilt —
`ctx.foldl_apps(atom_head_node, arg_nodes)` — and the ordinary, unchanged
`has_type_app` then applies to it. Measured:

| | |
|---|---:|
| rebuilt node produced, interpreting back to the subject | **740 / 740** |
| …a leaf had no node, or the rebuild interpreted elsewhere | **0** |
| …and the recursion **derived** the membership | **618** (83.5 %) |
| ……outright, acquiring no assumption | 433 |
| …and the recursion still declined | 122 |

740 rather than 5 250 because `interp` fills `exprs_rev` on the way: after the
first encounter the subject *has* a node and the clause never reaches this exit
again. Returned rather than discarded, the effect on the clause is large:

| row | before | after |
|---|---:|---:|
| target beta: premise `x ∈ A` not settled | 6 170 | **1 703** |
| target beta: reduct still not typeable | 9 306 | **14 021** |
| `target_mem`: NO LEAN NODE interprets to the subject | 5 250 | **740** |
| `target_mem`: the `has_type` recursion derived it | 1 251 | **5 705** |
| one head reduction of a type: contracted a redex | 7 686 | **11 795** |

And the effect on the outcome is **nil**. The whole ledger is byte-identical
with the fix returning its derivations:

| | before | after |
|---|---:|---:|
| gaps | 15 734 | 15 734 |
| escapes | 2 232 | 2 232 |
| derived (real kernel `Thm`) | 159 803 | 159 803 |
| obligations asked / discharged | 40 060 / 6 389 | 40 060 / 6 389 |
| admitted | 369 | 369 |

The two moved rows say where it went: `TbMiss::Domain` falls by 4 467 and
`TbMiss::Reduct` rises by 4 715. The redex now contracts, and the contracted
target has no typing either, so every decline the clause stops making is made
one step later by the clause after it.

### The verdict

**Beta's own domain premise is a counted obstruction, not a binding one**, and
`derived/` is not missing a construction. Every rule the successful 618 used is
one `derived/` already exports; what stood in the way was this clause asking
the reverse index for a term the *interpretation* had no reason to build, while
the *derivation* had built it out of pieces the index knows.

Three consequences worth carrying:

* **A census of a clause cannot say whether the clause matters.** Eight routes
  were measured at this frontier and each was judged by the size of its own
  residue; this is the first to be judged by removing the residue and reading
  the ledger, and it is the first to come out at zero. The ledger diff is
  cheap — a run with the candidate wired in and discarded — and it should
  precede the tranche, not follow it.
* **"Nothing on the thread holds it" is two claims.** The head has no
  function-space membership *and* no membership of any kind; the first sounds
  like a missing conversion and the second is a missing typing. Asking
  `typed_subj` costs one lookup and separates them.
* **The frontier is the reduct's own typing** (`TbMiss::Reduct`, 9 306 rising
  to 14 021 the moment the premise above stops absorbing them), not anything a
  function-space lemma reaches.

## The target-beta clause is worth fifteen gaps — 2026-08-10

*The method from the section above, turned on the frontier that section found.
`TbMiss::Reduct` was the row that absorbed every decline the domain premise
stopped making, so the question is the same one: delete it and read the whole
ledger. Instrument: `scripts/spine-probe.diff`, `NANODA_REDUCT_ASSUME=1`.*

### How a typing row is deleted without admitting anything

`reduct_assumed` **acquires** the reduct's own typing as a new antecedent
instead of declining — [`has_type_local`]'s move, applied one clause along. No
admission and no kernel rule: the theorem is `conj_proj`, `⊢ conj(used) →
used[i]`, a real projection out of the assumption list, and the antecedent is
returned to the caller, where a binder discharges it or the escape ledger counts
it. So the experiment is not "pretend the fact holds"; it is "hoist the fact and
let the ledger charge for it", which is what makes the ledger reading honest.

### Three runs

| | A: baseline | B: reduct acquired | C: B + the node rebuild |
|---|---:|---:|---:|
| **gaps** | 15 734 | **15 719** | **15 719** |
| **escapes** | 2 232 | **2 235** | **2 235** |
| **derived (real kernel `Thm`)** | 159 803 | **159 821** | **159 821** |
| obligations asked / discharged | 40 060 / 6 389 | 40 060 / 6 389 | 40 060 / 6 389 |
| `TbMiss::Reduct` | 9 306 | **0** | **0** |
| `TbMiss::Domain` | 6 170 | 5 474 | **405** |
| reduct typings acquired | — | 4 753 | 9 958 |
| raw hoists, all causes | 19 144 | 13 067 | 13 067 |
| deepest derivation | 20 | 23 | 23 |

**B and C are identical on every ledger row.** Stacking the node rebuild on top
— which more than doubles the acquisitions, 4 753 → 9 958, and takes the domain
premise from 6 170 declines to 405 — changes **not one number**. Two independent
closures of the two frontier rows of one clause, and the second is free of
effect given the first.

The whole movement, gap row by gap row:

| row | A | B |
|---|---:|---:|
| trans over an admitted premise | 8 457 | 8 451 |
| symm over an admitted premise | 487 | 481 |
| proj_reduce | 659 | 656 |
| beta: the lambda has no function-graph interpretation | 7 | 4 |
| undischarged assumption survived to the boundary (= escapes) | 2 232 | 2 235 |

−6 −6 −3 −3 +3 = **−15**.

### What absorbs it: not a third row, a cascade

The coordinator's question was whether a third row absorbs the residue, which
would make the frontier deeper than two layers. It is worse and simpler than
that: **no single row absorbs it, because the gap ledger is not made of
originating failures.** In the baseline,

| | |
|---|---:|
| trans over an admitted premise | 8 457 |
| pi congruence over an admitted body premise | 1 147 |
| congruence over an admitted premise | 636 |
| symm over an admitted premise | 487 |
| lam congruence over an admitted premise | 179 |
| pi congruence over an admitted domain premise | 137 |
| **"over an admitted premise", by row name** | **11 043 of 15 734 (70 %)** |

*Corrected: this table first read 10 228 (65 %), having missed the `congruence`
and `lam congruence` rows. Counting by **row name** is in any case an
approximation of the real partition — the next section measures it off the
premises instead and gets 11 111, because 68 gaps whose reason string reads like
an origin are relays.*

Two thirds of the ledger is a rule that received a gap as a premise and reported
one in turn. Closing a clause that originates gaps therefore buys, at best, the
sub-tree of the cascade it feeds — and this clause feeds fifteen of it. The
6 077 raw hoists the acquisition removes (19 144 → 13 067) are real work that
the ledger, correctly, does not credit: they were never what the ledger counted.

### The verdict

**`has_type_target_beta` is not on `init-prelude`'s critical path.** 13 856
firings, two frontier rows, 9 958 acquisitions when both are deleted, and a
ledger that moves 15 gaps of 15 734 (**0.1 %**) and three escapes the wrong way.
The goal counter — 40 060 obligations asked, 6 389 discharged — does not move at
all.

This converges with what the `checker/` seat established independently in the
same window: the within-declaration cascade is `ty_conv`'s subject (8 045) plus
`ty_app`'s argument (4 693), with four zeros saying the structural rules never
lack their premise; and it is a **wall, not a bootstrap** — 1 040 declarations
have nothing blocking them and fail anyway, and ten base cases move the ready
set by 86. Two routes, arriving from opposite ends, at the same statement: the
constraint is upstream of every clause that has been measured at this frontier,
and it is the supply of *originating* typings, not the reach of any rule that
consumes them.

**Practical consequence for briefing.** The three cheap deletions run in about
fourteen seconds each and answered, between them, two tranches' worth of design
questions. The ordering that works is: split the population, delete it, read the
whole ledger, *then* decide whether there is a construction to write. Judged by
residue size, the domain premise (6 170) and the reduct row (9 306) were the two
largest items at this frontier; judged by the ledger they are worth zero and
fifteen.

## Which clause originates the gap, and the sub-tree it feeds — 2026-08-10

*The ranking the thrust has been missing. Every census this stage has counted a
clause's own declines; none has asked which clauses **originate** and how large
a sub-tree each one's closure removes. Instrument:
`scripts/gap-provenance.diff`. It ends with the first tranche this stage has
produced that has a measured payoff.*

### Provenance, not row names

`TgCert::Admitted` carries a bitmask. A rule that fails on its own merits mints
a bit — it **originates**. A rule that fails because a premise was already a gap
inherits the union of its premises' bits — it **relays**. A relayed gap naming
exactly one origin is charged to that origin's sub-tree; one naming two or more
is charged to a `MULTI` bucket, because closing either alone would not remove
it. `origin_mask` reads that off the premises' certificates *before* `consume`,
so the partition is a fact about the derivation rather than about the reason
string — which matters, because **68 gaps whose reason string reads like an
origin are in fact relays**.

### The partition, exact and total

| | | |
|---|---:|---:|
| **originated** — a rule failed on its own merits | **2 391** | 15.2 % |
| **relayed**, attributable to exactly one origin | 10 366 | 65.9 % |
| **relayed**, naming two or more origins | 745 | 4.7 % |
| **escaped** — an assumption survived to the boundary | 2 232 | 14.2 % |
| **total** | **15 734** | |

Only one gap in seven is an originating failure. The ledger is a list of
reports, and six of every seven relay someone else's.

### The ranking

`sub-tree = own + solely-attributed relays`, ordered by sub-tree. This is the
column a tranche should be chosen on, and no census before this one produced it.

| origin | own | relayed | **sub-tree** |
|---|---:|---:|---:|
| **iota: this recursor has no curried interpretation** | 792 | 4 725 | **5 517** |
| **iota: the major premise is not a constructor** | 486 | 2 800 | **3 286** |
| **proj_reduce** | 659 | 1 808 | **2 467** |
| eq_cache | 287 | 562 | 849 |
| pi congruence: the body certificate is not about the binder bodies | 33 | 258 | 291 |
| nat_reduce | 32 | 79 | 111 |
| nat_eq | 44 | 22 | 66 |
| pi congruence: two Πs of undetermined sort over differently shaped bodies | 22 | 33 | 55 |
| lam congruence: the body certificate is not the graphs' pointwise equation | 19 | 30 | 49 |
| eta_struct | 6 | 18 | 24 |
| beta: the lambda has no function-graph interpretation | 7 | 14 | 21 |
| proof_irrel | 3 | 14 | 17 |
| def_eq_proj | 1 | 3 | 4 |

**Three origins account for 11 270 of 15 734 — 71.6 % of the ledger**, and only
745 relays (4.7 %) need more than one closure. The ranking is nothing like the
ranking by row size: `trans over an admitted premise` is the largest row in the
ledger at 8 457 and originates **nothing**.

### The ranking, validated by deletion

Acquiring the ι equation as an antecedent — `⊢ (⟦r⟧ = ⟦r'⟧) → (⟦r⟧ = ⟦r'⟧)`, a
real `imp_refl`, with the antecedent going into the certificate where the escape
ledger charges for it — deletes the top two origins:

| | baseline | ι acquired |
|---|---:|---:|
| **gaps** | 15 734 | **7 654** |
| escapes | 2 232 | 2 952 |
| derived (real kernel `Thm`) | 159 803 | **168 603** |
| obligations asked / discharged | 40 060 / 6 389 | 40 060 / 6 389 |
| trans over an admitted premise | 8 457 | 1 800 |
| pi congruence over an admitted body premise | 1 147 | 667 |
| congruence over an admitted premise | 636 | 464 |
| symm over an admitted premise | 487 | 337 |
| relays naming two or more origins | 745 | 454 |

**Gaps fall by 8 080 — 51.4 % of the entire ledger — and 8 800 more real kernel
theorems appear.** Predicted 8 803, measured 8 080; the 723 difference is relays
re-attributing one place down, `proj_reduce`'s sub-tree growing 2 467 → 2 754 as
ι stops claiming them. **So the provenance column predicts a deletion to within
8 % from a single side-effect-free run**, and the ranking can be trusted without
one deletion per origin.

Two honest caveats. The +720 escapes are the acquisition's own cost and a real ι
derivation would not pay them. And the typing counter — 40 060 asked, 6 389
discharged — does **not** move: this is half the def-eq certificate ledger, not
a typing win.

### Is the top origin reachable? Bounded, and named

The 792 are **109 distinct recursors**, which is a list, not a phenomenon:

| recursor | firings |
|---|---:|
| `Lean.ParserDescr.rec` | 169 |
| `Decidable.rec` | 81 |
| `Lean.Syntax.rec` | 66 |
| `Lean.Syntax.rec_1` | 22 |
| `EStateM.Result.rec`, `Except.rec`, `Lean.Syntax.Preresolved.rec`, `Lean.Syntax.rec_2` | 12 each |
| `Eq.rec` | 6 |
| ~100 more (`Add.rec`, `AndOp.rec`, `Append.rec`, `Array.rec`, `BEq.rec`, …) | 4 each |

The head is mutual and nested families (`Lean.Syntax` and its three companion
recursors, `Lean.ParserDescr`) plus large elimination (`Decidable.rec`,
`Eq.rec`); the tail is ~100 **structure** recursors at four firings each,
one-constructor classes that should be the easiest case there is.

The second origin is even sharper: of its 486, **485 are a major premise whose
head is a constant that is not a constructor** — it did not reduce — and exactly
1 is a projection. No lambdas, no literals, no locals. One delta step short of
the rule firing.

**This is the tenth measured verdict and the first that is not a dead end.**
Eight routes were chosen by residue size and two frontier rows were deleted for
zero and fifteen; this one is worth 8 080 gaps and is a bounded list of names.

### The convergence, stated as one finding

Two routes, neither derived from the other, arrived in the same window at one
statement: **the constraint is the supply of originating facts, not the reach of
any rule that consumes them.**

* *This route.* Two frontier rows of `has_type_target_beta` — beta's own domain
  premise (6 170 declines) and the reduct's typing (9 306) — deleted outright,
  worth zero and fifteen gaps between them. Then the ledger partitioned: 15.2 %
  originated, 70.6 % relayed, and three originating clauses carrying 71.6 % of
  the total.
* *The `checker/` seat's route.* The within-declaration cascade is `ty_conv`'s
  subject (8 045) plus `ty_app`'s argument (4 693), with **four zeros** saying
  the structural rules never lack their premise; `ty_premise_missing` 2 667 of
  2 667; and it is a **wall, not a bootstrap** — 1 040 declarations have nothing
  blocking them and fail anyway, and ten base cases move the ready set by 86.

A later reader meeting either half alone will underrate it. The first says every
*consuming* rule measured at this frontier is worth nothing when unblocked; the
second says the *producing* side has no supply and cannot be bootstrapped from
within a declaration. Together they say the work is on the supply side and
nowhere else — and the ranking above is the first thing produced this stage that
names where on the supply side to start.

## Origin 2 priced, and it is the `Nat` literal question — 2026-08-11

*The ranking's second entry, taken before the first because it was the sharp
one. Measured before anything was built, per the rule; what the measurement
found was that the brief it was taken from — including my own wording of it —
was wrong about the cause.*

### The sub-tree is real, and the column is validated per origin

`NANODA_IOTA_ASSUME` now names **one** origin, so a prediction can be checked
against its own deletion rather than against a combined run:

| deleted | acquisitions | gaps | fall | **predicted sub-tree** |
|---|---:|---:|---:|---:|
| — (baseline) | — | 15 734 | — | — |
| `iota: the major premise is not a constructor` | 486 | **12 668** | **3 066** | 3 286 |
| `iota: this recursor has no curried interpretation` | 792 | **10 720** | **5 014** | 5 517 |
| both | 1 278 | 7 654 | 8 080 | 8 803 |

Two things worth having. Each prediction lands within **7–9 %** of its own
deletion, so the provenance column is calibrated per origin and not just in
aggregate. And **3 066 + 5 014 = 8 080 exactly**: the two sub-trees are
disjoint and additive, which is what the single-origin attribution rule claimed
and had not yet been made to prove.

### The cause: three constants, and 466 of them are one

Origin 2 is 486 firings. One is a projection. The other 485 are a major premise
whose head is a constant that is not a constructor, and the census of *which*
constant is the whole finding:

| kind | constant | firings |
|---|---|---:|
| definition | **`Nat.ble`** | **466** |
| definition | `Nat.beq` | 14 |
| definition | `OfNat.ofNat` | 5 |

**Three distinct constants — 96 % of them one — carrying 3 066 gaps, 19.5 % of
the whole ledger.**

### Which corrects the brief, including my own wording of it

The census that produced this origin recorded "a constant that is not a
constructor — **it did not reduce**", and the tranche was briefed as *one delta
step short of the rule firing*. That reading is wrong, and `Nat.ble` is why.

`Nat.ble` and `Nat.beq` are not unfolded by the checker at all. They are
**GMP-accelerated literal operations**: `try_reduce_nat` (`checker/src/tc.rs:587`)
matches the head against `NameCache`'s cached pointers and computes the answer
natively, and `reduce_rec`'s internal `self.whnf(major)` takes that path with
**no certificate requested**. So the ι rule's major premise becomes
`Bool.true`/`Bool.false` by arithmetic the backend never saw and could not
have derived: the certifier's own route for it is `Admit::NatRed`, an admission,
not a rule.

The step this origin is short of is therefore not a delta step and not
plumbing. It is **`⟦Nat.ble a b⟧ = ⟦Bool.true⟧` for literal operands**, a fact
about numerals in the target theory.

### The third route to the same place

`NAT-BRIDGE-FEASIBILITY.md` §1 already answered the question this lands on, from
the opposite end and before this ledger existed: *"`init-prelude` needs
computation, not only representation … conversion checks that are decided only
because the checker evaluates `Nat.beq` and `Nat.ble` on literals — at operands
as large as 2⁶⁴ — and it contains no route to those checks that does not
compute."* It established that by renaming the operations out of `NameCache` and
watching the checker fail.

That document named the two operations. This one **prices** them: `Nat.ble` and
`Nat.beq` are 480 of 486 firings at the second-largest origin in the gap ledger,
and closing that origin is worth **3 066 gaps**. The nat-computation work has
had a feasibility argument since; it now has a payoff number, which is the thing
it was missing.

So the convergence is three routes, not two:

* the target-beta route — every *consuming* rule measured at this frontier is
  worth nothing when unblocked (0 and 15 gaps);
* the `checker/` seat's route — the *producing* side has no supply and cannot be
  bootstrapped inside a declaration (a wall, not a bootstrap);
* and this one — of the supply that is missing, the second-largest single piece
  is literal `Nat` arithmetic, which was independently shown to be unavoidable.

### What is left of the ranking

Origin 1, `iota: this recursor has no curried interpretation`, is now measured
at **5 014 gaps** (31.9 %) and remains the largest single item anywhere in this
ledger. It is 109 distinct recursors: a head of mutual and nested families
(`Lean.ParserDescr.rec` 169, `Decidable.rec` 81, `Lean.Syntax.rec` 66 and three
companions) and a tail of roughly a hundred **one-constructor structure
recursors at four firings each**. The tail is the untested hypothesis worth
taking next: if one shape covers it, it is a large fraction of 5 014 for a
single construction. Unlike origin 2 it is a genuine construction question and
not a representation one.

## Origin 1's tail is one shape: 100 structure recursors, 2 480 gaps — 2026-08-11

*The tail-is-uniform hypothesis, tested. It holds, and more tightly than
proposed: the shape is exactly half the origin, every member of it fires exactly
four times, and all 400 decline at the same line for the same reason.*

### The origin is now four origins

`iota: this recursor has no curried interpretation` was one row. It is split by
the gates `gen_rec_bottom` actually applies, and because the origin mask mints a
bit per *reason*, that yields **four sub-trees from one side-effect-free run**:

| origin | own | relayed | sub-tree |
|---|---:|---:|---:|
| iota: no interpretation — **a ONE-CONSTRUCTOR STRUCTURE** | **400** | 2 280 | **2 680** |
| iota: no interpretation — several constructors | 286 | 1 858 | 2 144 |
| iota: no interpretation — a mutual block | 100 | 493 | 593 |
| iota: no interpretation — an indexed family | 6 | 54 | 60 |

The split is not cosmetic and it is the point of having put the mask on the
certificate: a construction that covers one shape now has its payoff priced
before it is written. Ledger byte-identical with the split in: 15 734 / 2 232 /
159 803.

### The shape, and how uniform it is

**400 firings, 100 distinct recursors, exactly four firings each.** No indices,
no mutual block, no nesting, no hand-written recogniser, `np` 0 or 1. The list
is what it looks like:

```
ctors=1 np=0   ByteArray  Char  String  String.Pos.Raw  Substring.Raw
               UInt8 UInt16 UInt32 UInt64 USize
               Lean.Macro.Context  Lean.Macro.Methods  Lean.Macro.State  …
ctors=1 np=1   Add  AndOp  AndThen  Append  Applicative  Array  BEq  Bind
               BitVec  Complement  Div  Dvd  Fin  Functor  Hashable
               HomogeneousPow  Inhabited  …
```

These are **type classes and wrapper structures**. That matters for §*Beyond
this corpus* below.

### Why they decline: 400 of 400 at one line

`t_policy` (`tg.rs:8219`) sites the motive's canonical point at a **nullary**
constructor — `ctors.iter().position(nullary)?` — and returns `None` when there
is none. That is policy 3. Measured, rather than inferred:

| | |
|---|---:|
| structures whose single constructor is **nullary** | 0 |
| structures whose single constructor **takes fields** — policy 3 | **400** |

(The census's six nullary rows are `Eq.rec`, which is counted in the *indexed*
bucket.) So all 400 decline at the same line, for the same reason, and the
reason is a property of the shape rather than of any individual declaration.

### The deletion, and what it is worth

| | gaps | fall | predicted |
|---|---:|---:|---:|
| baseline | 15 734 | — | — |
| the structures alone deleted | **13 254** | **2 480** | 2 680 |
| all four ι-interpretation causes deleted | 10 720 | 5 014 | 5 517 |

**2 480 gaps — 15.8 % of the whole ledger — for one shape**, and within 7.5 % of
the prediction, which is the fourth time the provenance column has landed inside
9 %. The structures are 2 480 of 5 014, i.e. 49.5 % of origin 1, matching their
50.5 % share of its firings almost exactly: the sub-tree per firing is flat
across the origin, which is another way of saying the population is uniform.

### What the construction is, and where it belongs

A one-constructor inductive **has no case analysis**. Its ι rule is

```text
S.rec C f (S.mk a⃗)  ≡  f a⃗
```

— a single rule, nothing to branch on, and no choice of target to make. The
entire apparatus `t_policy` exists to serve — a canonical closed point at which
to site the motive so the W-type's branching has a target — is needed only
because the general construction branches over constructors. **At one
constructor there is nothing to branch over, so there is nothing for the policy
to decide.** The eliminator is simply the inverse of the constructor.

This also repairs a reading that would otherwise bury the population.
`gen_rec_bottom`'s header records that "widening the gate to admit [policy 3]
was measured and closes zero gaps, because `t_policy` then refuses inside
`rec_nest` instead". That is true and it is not a verdict on this shape: it
measured *widening the gate*, which lets the same policy fail one level later.
What these 400 want is not a wider gate but **no policy at all**.

**This is a `derived/` construction, not a `checker/` one** — a degenerate
recursor in `derived::inductive`, beside `GenRecursor` rather than inside it. Per
standing instruction it is named here rather than built.

### Beyond this corpus

`init-prelude`'s counts are `init-prelude`'s. The shape this construction covers
is *type classes and wrapper structures* — `Add`, `Functor`, `BEq`, `Inhabited`,
`Fin`, `Array`, the `UInt` family — and a corpus like Mathlib is built out of
them at a density this file cannot represent. The 2 480 is a floor for what the
construction is worth and almost certainly a low one; that cannot be measured
here, and is recorded so the number is not read as a ceiling.

## Origin 3, `proj_reduce`: 1 618 not 2 467, and it is origin 1's construction — 2026-08-11

*The third of the three that carry 71.6 %. Two results: the sub-tree column
missed for the first time, and the miss is structural and worth more than the
origin; and the origin turns out not to be a tranche at all, because what it
needs is the construction origin 1's structures already sent to `derived/`.*

### The history, read and not re-derived

`#102` proposed that the ι tower reaches `whnf_conv`'s doubled `Proj` arm and
was **disproved** at `f5dab4d` — `nested_model.ndjson` contains no `proj` node at
all. `#105` found a real parameter hole in `index_congr` that was **not
exploitable**, both mutations dying at the consumer. Both looked at the
projection path, one for cost and one for soundness; **neither asked what it
originates**, which is why the row survived two passes.

### What it originates, by exit

| exit | |
|---|---:|
| the checker handed over no proof pair — the endpoints are not proofs | **652** |
| the redex is not a proof | 7 |
| the reduct is not a proof / the two `•` equations did not compose | 0 |

659 exactly. **99 % is one cause**, and it is the one `proj_red`'s own header
states: the rule's only derivation is Carneiro 6.7 — both endpoints are proofs,
so both interpret to `•` — and where they are not proofs there is no rule at
all, because *"this backend has no interpretation of structures, so it has no
axiom about `mk`, none about `proj` beyond its being a function symbol"*.

### The deletion: 1 618, against a predicted 2 467

| | gaps | fall | predicted |
|---|---:|---:|---:|
| baseline | 15 734 | — | — |
| `proj_reduce` deleted | **14 116** | **1 618** | 2 467 |

**A 34 % over-prediction — the first outside 9 % in six deletions**, and the
cause is visible row by row in the after-ranking rather than being noise:

| row | before | after |
|---|---:|---:|
| nat_eq | 66 | **391** |
| nat_reduce | 111 | 190 |
| iota: several constructors | 2 144 | 2 340 |
| iota: the major premise is not a constructor | 3 286 | 3 329 |
| eq_cache | 849 | 890 |
| relays naming two or more origins | 785 | **78** |

The relays did not disappear; **they re-originated**. A third of the predicted
sub-tree moved to literal arithmetic, `nat_eq` going up nearly sixfold.

### The calibration this buys, which is the durable part

`SUBTREE` assumes a relay vanishes when its sole origin closes. That is true for
a **terminal** origin — one where the derivation stops and nothing past it is
attempted — and every ι row is terminal, because a recursor with no curried
interpretation blocks the whole reduction. Predicted/measured for those:
3 286/3 066, 5 517/5 014, 2 680/2 480.

It is false for a **mid-chain** origin. Certifying a projection does not end the
conversion the projection sits in; it lets the derivation run on to the next
wall, and the next wall bills someone else.

So the column is a **ceiling**, and any origin worth building against should be
confirmed by deleting it. That is cheap, because **measured deletions compose**:

| deleted | gaps | fall |
|---|---:|---:|
| one-constructor structures | 13 254 | 2 480 |
| `proj_reduce` | 14 116 | 1 618 |
| **both** | **11 636** | **4 098** |

2 480 + 1 618 = 4 098, to the digit. Additivity survives even where the
prediction does not, so confirmation is needed once per origin, never once per
combination.

### And origin 3 is not a tranche — it is origin 1's construction, again

Every structure whose projection reduces without a certificate is
**one-constructor**, and there are only eight of them:

| structure | firings |
|---|---:|
| `PProd` | 114 |
| `OfNat` | 37 |
| `PULift` | 8 |
| `Fin` | 7 |
| `Char` | 6 |
| `Array`, `PLift`, `ULift` | 2 each |

`(mk a⃗).i ⟶ aᵢ` and `S.rec C f (S.mk a⃗) ⟶ f a⃗` are the same eliminator of the
same one-constructor inductive. A degenerate recursor in `derived::inductive`
supplies both: the projection rule is that recursor at the projection motive.

**So the construction already assigned for origin 1's structures is worth
4 098 gaps — 26.0 % of the ledger — not 2 480**, provided it is built to serve
the projection rule as well as the ι rule. That is a design constraint on that
task, and it is the reason this tranche ends in a note to another seat rather
than in a construction of its own.

(Only 178 of the 659 declines have a literal `Expr::Proj` at the redex's head;
the rest carry the projection deeper in a spine, so the eight names are the
distinct structures seen at the head and not a partition of the 659.)

### What is left on the board

| origin | own | predicted sub-tree | measured |
|---|---:|---:|---:|
| iota: the major premise is not a constructor (`Nat.ble`) | 486 | 3 286 | 3 066 — *assigned* |
| iota: a ONE-CONSTRUCTOR STRUCTURE | 400 | 2 680 | 2 480 — *assigned* |
| `proj_reduce` | 659 | 2 467 | **1 618** — *same construction as above* |
| iota: several constructors | 286 | 2 144 | unmeasured |
| eq_cache | 287 | 849 | unmeasured |
| iota: a mutual block | 100 | 593 | unmeasured |
| iota: an indexed family | 6 | 60 | unmeasured |

`several constructors` is the largest unassigned item; it is terminal, so its
2 144 should hold to within 9 %.
