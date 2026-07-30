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
