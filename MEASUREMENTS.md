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
