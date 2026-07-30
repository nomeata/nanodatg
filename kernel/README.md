# `kernel` — the trusted computing base

Everything in this crate must be correct. Nothing outside it does.

## Threat model

The single threat is: **a bug in Lean's kernel lets someone derive `False`.**

We are not trying to show that a translated theorem *means* what the Lean
original means. The claim is narrower and cheaper: if a whole development
translates and this kernel accepts every step, then the development proves no
contradiction. That holds as long as the translation of `False` is genuinely
refutable in the target.

So a translation bug is **not** a soundness bug — it produces a rejection, never
a false theorem. The translator may be liberal, ugly and clever. This crate may
not.

## The trusted base, itemised

Everything below has to be right. Nothing else does.

1. The ten axioms of Tarski–Grothendieck set theory (milestone 3).
2. The first-order proof system, including — especially — the free-variable and
   distinct-variable side conditions on substitution and generalisation.
3. *(from milestone 4)* The claim that the host's bignum operations correctly
   implement the intended interpretation of the primitive arithmetic symbols.

Item 3 is a deliberate, eyes-open addition to the TCB. See below.

## Current contents (milestone 1)

The set-theoretic kernel does not exist yet. Today the crate contains only the
proof-backend boundary:

* `Certifier` — the trait every definitional-equality conclusion must go
  through. It is generic over the term representation, so the TCB contains no
  knowledge of Lean's syntax; the dependency points untrusted → trusted only.
* `NullCertifier` — `type Cert = ()`. Makes the checker behave like an ordinary
  trusted checker while the real backend is built.

**`NullCertifier` must be unreachable in a release build once the real backend
exists.** It currently sits behind the default-on `null-certifier` cargo
feature so that gate is a one-line change.

## Boundary rules

Enforced by `ci/check-boundary.sh`, which is itself tested by
`ci/test-boundary.sh`:

| Rule | Also enforced by |
| --- | --- |
| No `unsafe` | `#![forbid(unsafe_code)]` |
| No external crate dependencies | empty `[dependencies]` in `Cargo.toml` |
| `Thm` has no public fields and no public constructor | — |
| No I/O, no serialization, no printing of derivations | — |
| ≤ 1000 non-comment lines | — |

The grep duplicates the compiler- and Cargo-level enforcements on purpose: those
can be removed in the very commit that violates them, and the duplication makes
that show up as a CI failure rather than as nothing at all.

### Why no derivation printing

`Thm` carries its **conclusion only**. Derivations exist transiently, as the
history of API calls, and are dropped immediately. Memory is O(live theorems),
not O(proof size), and no proof file is ever written. This is what makes the
approach affordable, and a kernel that could serialize a derivation would invite
a workflow that gives it up.

## Dependency policy

The crate is dependency-free. There is exactly one sanctioned future exception:

> **`num-bigint` (or a hand-rolled equivalent) for native numeral arithmetic,
> arriving in milestone 4.**

This is not yet a dependency — the line above exists so `ci/check-boundary.sh`
can distinguish "the sanctioned exception, documented" from "someone added a
crate". When it is actually added it must be pinned and vetted, and this section
must record the version and the vetting.

Anything else is a boundary violation.

## Milestone 4 note: built-in arithmetic

`ℕ` will be a **primitive sort** with primitive numeral syntax and native
bignum-backed rule schemas (`+`, `-` truncated, `*`, `/`, `%`, `^`, `=`, `≤`,
`<`, `gcd`, and the bitwise/shift operations), mirroring what Lean's kernel
accelerates.

These are not derived from the Peano axioms, and must not be. Lean's kernel
short-circuits `Nat.mul` to GMP rather than unfolding its recursion, so there is
no feasible-length derivation corresponding to `2^64 * 3`; deriving arithmetic
would make `decide`-heavy developments uncheckable regardless of constant
factors. Numerals are stored as bignums, never as `S(S(...))` towers.

Why this is safe to trust: every such rule is valid in the standard model
(`ℕ ↦ ω`, symbols to the usual ordinal operations), so consistency is preserved
*provided the computation is correct*. Correctness of the computation is the
whole risk, and it is a testable one — which is precisely why `ℕ` is primitive
rather than defined as von Neumann ordinals. A primitive sort with a canonical
intended meaning has no defined encoding for the rules to disagree with, which
removes the only failure mode that would be invisible to differential testing.

Differential-test against an independent implementation, including: zero,
truncated subtraction below zero, division and modulo by zero (Lean returns
`0`), and values straddling word boundaries.
