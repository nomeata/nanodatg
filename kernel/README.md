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

1. The axioms of Tarski–Grothendieck set theory. **Tarski's Axiom A is
   currently incomplete** — the "no surjection from `y` onto `u`" clause needs
   ordered pairs and is stubbed to a weaker disjunct. It is named
   `ax_tarski_incomplete`, nothing in the checker path uses it, and it must be
   finished before any claim that depends on inaccessibles.
2. The first-order proof system, including — especially — the free-variable and
   distinct-variable side conditions on substitution and generalisation.
3. *(from milestone 4)* The claim that the host's bignum operations correctly
   implement the intended interpretation of the primitive arithmetic symbols.

Item 3 is a deliberate, eyes-open addition to the TCB. See below.

## Current contents

* `term.rs` — terms and formulas of first-order logic with `∈`. Locally
  nameless, and `Bound` is **unconstructible from outside**: the only way to make
  one is `Formula::forall`, which closes over a named variable. So dangling
  indices cannot be built, every `Term` handed out is locally closed, and the
  classic "substitutable for" side condition on instantiation is *removed*
  rather than checked. Adversarially tested in `tests/substitution.rs`, and
  those tests are mutation-verified to actually catch depth bugs.
* `thm.rs` — the opaque `Thm`, Hilbert-style primitive rules (Łukasiewicz
  propositional axioms, instantiation, distribution, modus ponens,
  generalisation, reflexivity, Leibniz), derived rules built on top of them
  (symmetry, transitivity, congruence, and the propositional combinators), the
  TG set axioms, and conservative definitional extension via `define`.
* `Certifier` — the trait every definitional-equality conclusion must go
  through. Generic over the term representation, so the TCB contains no
  knowledge of Lean's syntax; the dependency points untrusted → trusted only.
* `NullCertifier` — `type Cert = ()`. Makes the checker behave like an ordinary
  trusted checker; the real backend lives in `checker/src/tg.rs`.

Hilbert style rather than natural deduction because `Thm` must be a formula with
no context. That has a concrete payoff in the trusted surface: **generalisation
needs no side condition**, since the usual `x ∉ FV(Γ)` is vacuous when there is
no `Γ`. The one genuinely necessary side condition, `x ∉ FV(φ)` on the
distribution axiom, is checked and tested.

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

## Why beta is not yet derivable

The set-theoretic function corresponding to a Lean lambda *can* be constructed —
this is Carneiro's interpretation, and it is not in doubt:

    ⟦λx:A. b⟧ = { ⟨x, ⟦b⟧⟩ : x ∈ ⟦A⟧ }        (by Replacement)
    ⟦f a⟧     = ⋃ { y : ⟨a, y⟩ ∈ ⟦f⟧ }

Two things stand between that and a derivable beta rule.

**1. Definitional extension.** `lam` and `app` have to *mean* something, which
means defining axioms rather than the bare signature extension the checker
currently uses. `thm::define` now provides this: given `⊢ ∀x⃗. ∃!y. φ(x⃗, y)` it
introduces a fresh symbol and returns `⊢ ∀x⃗. φ(x⃗, f(x⃗))`. The `∃!` premise is
required as a *theorem*, because uniqueness is exactly what makes a model's
expansion unique and hence the extension conservative. Demonstrated end to end
in `tests/define.rs`, which derives `⊢ ∀x. ∃!y. y = x` from the primitives and
uses it to obtain `⊢ ∀x. f(x) = x`.

Note also that `lam` is not one symbol but a *family*: the body of a lambda is a
term with a free variable, i.e. a scheme, so each Lean lambda induces its own
definitional extension parameterised by the lambda's free variables. That is
routine, just not free.

**2. A typing premise — the real obstruction.** A set-theoretic function has a
*set* domain, so beta is not unconditional. If `a ∉ A` then

    app(lam_b(A), a) = ⋃∅ = ∅

while `⟦b[a/x]⟧` is generally something else. The derivable statement is

    ⊢ a ∈ A → app(lam_b(A), a) = b[a/x]

and discharging that antecedent requires `⊢ ⟦a⟧ ∈ ⟦A⟧` — a *typing* fact. This
is why Carneiro's interpretation is type-directed: its soundness theorem is
"if `Γ ⊢ a : A` then `⟦a⟧ ∈ ⟦A⟧`", and the interpretation is only defined
relative to a typing derivation.

So closing beta means extending the `Certifier` boundary beyond equality to
carry typing judgements, and threading those through the checker's `infer`
alongside the existing equality certificates. That is the substance of the
remaining milestone-3 work, and it is a larger job than "add some axioms" —
which is what an earlier version of this note implied.

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
