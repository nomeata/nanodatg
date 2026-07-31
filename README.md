# nanodatg

A proof-carrying Lean checker: a fork of
[`nanoda_lib`](https://github.com/ammkrn/nanoda_lib) that turns Lean's export
format into derivations in a small LCF-style kernel for **Tarski–Grothendieck
set theory**, rather than into a trusted `true`/`false` verdict.

Today an external Lean checker is trusted: you believe its ~10k lines of
inference and definitional-equality code. Here the type checker itself is
**untrusted**, and the only trusted component is `kernel/`.

## The threat model determines everything

The single threat is: **a bug in Lean's kernel lets someone derive `False`.**

We are *not* showing that translated theorems mean what the Lean originals mean.
Only this: if a development translates and the kernel accepts every step, the
development proves no contradiction. That holds as long as the translation of
`False` is genuinely refutable in the target.

So a translation bug is **not** a soundness bug — it yields a rejection, never a
false theorem. The translator may be liberal and clever. The kernel may not.

## Layout

| path | trusted? | what |
| --- | --- | --- |
| `kernel/` | **yes — the entire TCB** | FOL-with-∈ kernel for TG set theory, and the proof-backend boundary |
| `derived/` | no | derived inference rules and conservative constructions |
| `checker/` | no | fork of nanoda_lib: parser, `Expr`, inference, defeq, reduction |
| `ci/` | — | boundary enforcement, and a self-test for it |
| `scripts/` | — | corpus harness |

`checker/` is imported with full upstream history, so the instrumentation diff
is exactly:

```sh
git diff nanoda-upstream/master -- checker/
```

## Getting started

```sh
direnv allow          # or: nix develop
./ci/check.sh         # everything CI runs
```

The corpus tests want the Lean Kernel Arena suite, which is gitignored for size:

```sh
mkdir -p vendor/arena-tests
curl -sSL https://arena.lean-lang.org/lean-arena-tests.tar.gz \
  | tar xz -C vendor/arena-tests
./scripts/arena.sh    # 102 good + 55 bad export files
```

Without it, `cargo test` still runs the committed fixtures in
`checker/tests/fixtures/{good,bad}`, so there is always negative coverage.

## Where the project is

**The fork changes the shape of the roadmap.** Because `checker/` inherits
nanoda, the untrusted side — inductives, recursors, `Prop`, proof irrelevance,
quotients, mutual and nested inductives, literals — is *already implemented and
passing*. The remaining frontier is the interpretation and the kernel.

### The trusted base

`kernel/` is **624 non-comment lines**, no `unsafe`, no dependencies,
CI-enforced. Eight set axioms — extensionality, empty set, pairing, union,
power, regularity, replacement (a scheme), and Tarski's Axiom A — plus five
logic axioms and the rules (modus ponens, generalisation, reflexivity, Leibniz)
and conservative definitional extension.

That is **two fewer than the brief's ten**, because *singleton* and *ordered
pair* are constructed rather than assumed. The empty set is the one that went
the other way, deliberately: Separation at a refutable condition *is* the
empty-set axiom, and deriving it from Tarski needs the recursion theorem and a
transitive closure. `kernel/README.md` states the trade.

**Five soundness bugs have been found and fixed in the trusted base, none of
them by the test suite.** All were found by reading with intent to break — see
`DECISIONS.md`. That practice is now standing policy for any change to
`kernel/`, *including fixes*: bug #5 existed only because of the fix for #4.

### What is derived, not assumed

`derived/` (4,800 lines, untrusted, 175 tests) builds on the kernel: a
propositional and quantifier toolkit, "reasoning under a fixed hypothesis" (the
nearest a Hilbert system gets to a deduction theorem), Separation from
Replacement, unordered pairs, singletons and Kuratowski ordered pairs with
injectivity, union, power set, Cartesian products, function spaces, the
least-universe operator `U(x)`, lambda graphs, application, **beta reduction**,
graph and image extensionality, dependent products, and the bridge showing a
constant-fibre dependent product *is* the function space.

### Coverage

With `--features tg`, **65 of 91** tutorial exports check with *every*
definitional-equality step discharged by a real kernel derivation — zero gaps.
Acceptance across the whole arena corpus is unchanged with the backend active
(152 matched, 0 mismatched), so the backend adds evidence without changing
verdicts.

`MEASUREMENTS.md` carries the gap ledger. The dominant remaining cause is a
single one: the typing obligation `⟦a⟧ ∈ ⟦A⟧` that beta carries, which is
undischargeable when the argument is a constant or an application. It and its
cascades are roughly 73% of what is left.

### Remaining work, in order

1. **Give every rule the terms it concludes about.** `lam_cong` and `pi_cong`
   have them and guard correctly; `app_cong`, `trans` and `symm` do not, so
   they cannot check what they prove. Measured cost: ~500 gaps.
2. **A `has_type` family on `Certifier`** — the type-directed interpretation.
   Now tractable rather than open-ended: with `Π` interpreted as a dependent
   product, application typing follows from its characteristic property,
   constant typing reduces to the declaration's own, and lambda typing is the
   graph being a section.
3. Complete Tarski's inaccessibility clause (needs Cantor–Schröder–Bernstein),
   which would in turn let the empty-set axiom be retired.
4. A proof-producing union-find for the equality cache.
5. Primitive `ℕ` with native bignum arithmetic — deliberately shelved; the
   inductive-free fragment does not need it.

## The honest progress metric

`cargo build --release --features stepcount` makes the checker report where every
definitional-equality conclusion came from — a real backend rule, or an `admit`
naming a hole still to be closed:

```
definitional-equality certificate provenance
  certified (real rule)           70830
  admit whnf                       2681
  admit lazy_delta                 1126
  admit eq_cache                    687
  ...
  TOTAL admitted                   4520
```

**This number must reach zero before the backend can be trusted.** Admits are an
enum, not scattered strings, so a new hole cannot be introduced without naming
it. See `MEASUREMENTS.md` for the full data and `DECISIONS.md` for the reasoning.

## Licence

`checker/` derives from nanoda_lib, Apache-2.0; see `checker/LICENSE` and
`NOTICE`.
