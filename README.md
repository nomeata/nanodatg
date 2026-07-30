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
passing*. The remaining frontier is almost entirely kernel-side: build the TG
kernel and close the gap between "the checker concluded these are equal" and
"the backend can justify it".

Done:

- **A real Tarski–Grothendieck kernel** (`kernel/`, 511 non-comment lines):
  terms and formulas, an opaque `Thm`, Hilbert-style FOL inference rules,
  derived equality rules, and the set axioms. Hilbert style because `Thm` must
  be a formula with no context — which also means generalisation needs no side
  condition, shrinking the trusted surface.
- **Capture designed away rather than checked.** The representation is locally
  nameless *and* `Bound` is unconstructible from outside: the only way to make
  one is `Formula::forall`, closing over a named variable. The adversarial
  substitution tests were mutation-tested to confirm they actually catch depth
  bugs.
- An interpretation of Lean into the kernel language (`checker/src/tg.rs`) using
  symbols introduced by pure signature extension — no axioms, so unconditionally
  conservative and no growth of the TCB.
- The `Certifier` proof-backend trait and `NullCertifier`.
- Boundary rules enforced by `ci/check-boundary.sh`, which has its own self-test
  (`ci/test-boundary.sh`) — that self-test found four real bugs in the first
  version of the check.
- Every definitional-equality path returns `Option<Cert>` rather than `bool`.
- Reflexivity, sort equality, constant equality, eta, and full
  congruence (`app_cong`, `lam_cong`, `pi_cong`) discharged by real rules.
- Step counting and certificate-provenance reporting (`--features stepcount`).
- Corpus regression net: 152 matched, 0 mismatched.

### Checked with real derivations

With `--features tg` the checker uses the TG kernel, and reports per run whether
every definitional-equality step was actually derived:

| tutorial export | result |
| --- | --- |
| `001_basicDef` | fully derived, 0 gaps |
| `003_arrowType` | fully derived, 0 gaps |
| `004_dependentType` | fully derived, 0 gaps |
| `005_constType` | fully derived, 0 gaps |
| `008_forallSortWhnf` | fully derived, 0 gaps |
| `006_betaReduction`, `007_betaReduction2` | accepted; beta gap reported |

Acceptance across the whole arena corpus is unchanged with the backend active:
152 matched, 0 mismatched. The backend adds evidence; it does not change
verdicts.

Next, in order of value:

1. **Defining axioms for `lam`/`app`**, by conservative definitional extension,
   so beta becomes a derivation rather than a reported gap. This is what
   unblocks 006/007 and most of the rest of the corpus.
2. **Make `whnf` return evidence.** The largest remaining hole, and the only one
   that was a genuine correctness bug rather than missing plumbing — see
   `DECISIONS.md`.
3. `lazy_delta`, which composes from `delta` plus `trans`.
4. A **proof-producing union-find** for the equality cache. Smaller than the 88%
   cache-hit rate suggests, because most hits are pointer equality and discharge
   as reflexivity.
5. Complete Tarski's Axiom A (the surjection clause needs ordered pairs).
6. Primitive `ℕ` with native bignum arithmetic in the kernel.

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
