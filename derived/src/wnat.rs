//! **The natural numbers as a W-type** — Lean's
//! `inductive N | zero | succ (n : N)`, the first *recursive* inductive this
//! development interprets.
//!
//! # The construction
//!
//! ```text
//! A  := 1 + 1                 the tag set: one tag per constructor
//! 2  := {0, 1}                a codomain for the fibre family
//! B  := rec₊(λ_. 0, λ_. 1)    zero has no recursive argument, succ has one
//! N  := W(A, B, U(A))
//! zero   := ⟨inl •, ∅⟩        the empty function out of the empty fibre
//! succ n := ⟨inr •, {⟨•,n⟩}⟩  the one-point function out of `1`
//! ```
//!
//! The two "constant functions" are one-point graphs, because their domain `1`
//! is a singleton: `λ_. 0` on `1` **is** `{⟨•,0⟩}`. So the whole family is
//! [`crate::sums::Cases`] over two [`crate::point_fun`] graphs, and
//! [`crate::sums::Cases::beta_left`]/[`beta_right`](crate::sums::Cases::beta_right)
//! compute it.
//!
//! # Interface
//!
//! Every statement below is at **closed terms** — `N`, `zero` and `succ` have
//! no parameters — except where a natural number is quantified:
//!
//! ```text
//! ⊢ app(B, inl •) = 0                             [Nat::fibre_zero]
//! ⊢ app(B, inr •) = 1                             [Nat::fibre_succ]
//! ⊢ closed(A, B, U(A))                            [Nat::closed]
//! ⊢ ⟨inl •, ∅⟩ ∈ N                                [Nat::zero]
//! ⊢ ∀n. (n ∈ N → ⟨inr •, {⟨•,n⟩}⟩ ∈ N)            [Nat::succ]
//! ⊢ ∀n. ¬(⟨inl •,∅⟩ = ⟨inr •,{⟨•,n⟩}⟩)            [Nat::zero_ne_succ]
//! ⊢ ∀m ∀n. (⟨inr •,{⟨•,m⟩}⟩ = ⟨inr •,{⟨•,n⟩}⟩ → m = n)   [Nat::succ_inj]
//! ```
//!
//! and, for the *constructor as a function* — which is what an interpretation of
//! Lean needs, since `N.succ` is applied rather than being a term-former —
//! a unary symbol `sc` with `⊢ ∀x. sc(x) = ⟨inr •, {⟨•,x⟩}⟩` and its graph:
//!
//! ```text
//! ⊢ succ_fun ∈ fs(N, N)                           [Nat::succ_in_funspace]
//! ⊢ ∀n. (n ∈ N → app(succ_fun, n) = sc(n))        [Nat::succ_beta]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # The bound is still `U(A)`, and the ω-tower is not needed
//!
//! `INDUCTIVES.md` recorded a *prediction* that `N` would need "a bound that is
//! no longer the tag set — i.e. the ω-tower", because the fibres stop being
//! empty. **Measured, that is wrong.** [`crate::bound::least_universe_closed`]
//! asks only for `A ∈ U(c)` and `∀a ∈ A. app(B,a) ∈ U(c)`, and at `c := A` all
//! three obligations are already available:
//!
//! * `A ∈ U(A)` — [`crate::universe::mem_least_universe`];
//! * `0 = ∅ ∈ U(A)` — [`crate::enums::empty_in_least_universe`], the subset
//!   clause `C₂` at `∅ ⊆ A`;
//! * `1 = {∅} ∈ U(A)` — [`crate::bound::Bound::least_pairing`] at `a = b = ∅`,
//!   since `{∅,∅}` *is* the term `1`.
//!
//! So the bound is `U(A)` exactly as for [`crate::enums`], and the real work is
//! the **case analysis**: computing `app(B,a)` for `a ∈ 1 + 1`, which is
//! [`crate::sums::Sums::sum_cases`] plus [`crate::sums::Sums::unit_eta`] plus
//! the two `rec₊` computation rules. No ω-tower, no recursion theorem, no new
//! axiom.
//!
//! # Non-vacuity
//!
//! Three memberships about one set say nothing if that set could be a
//! singleton, so both distinctness statements are derived and both are pinned
//! in `tests/wnat.rs`:
//!
//! * [`Nat::zero_ne_succ`] comes from [`crate::sums::Sums::disjoint`] — the two
//!   *tags* differ — through the Kuratowski pair's injectivity;
//! * [`Nat::succ_inj`] comes from that same injectivity twice over, once for
//!   the W-type pair and once inside the one-point fibre function.
//!
//! Together they make `zero`, `succ zero`, `succ (succ zero)`, … pairwise
//! distinct, so `N` is provably infinite — which is what stops every membership
//! theorem above from being satisfied by a one-element set.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wnat::…` all still resolve. The layout matches [`crate::wlist`]
//! file for file, because `List α` is this construction with a parameter.
//!
//! | file | what it holds |
//! |---|---|
//! | [`apparatus`] | [`Nat`] — the symbol `N`, the term builders, and the constructor |
//! | [`typing`] | the two constructors' typing rules, and which hypotheses are real |
//! | [`distinct`] | distinctness and injectivity — the non-vacuity witness |

pub mod apparatus;
pub mod distinct;
pub mod typing;

pub use apparatus::Nat;
