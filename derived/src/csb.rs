//! **Cantor–Schröder–Bernstein**: two injections make a bijection.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::csb::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`clauses`] | the four clauses of an injection as formulas, and the Knaster–Tarski operator as a condition |
//! | [`fixpoint`] | the operator is monotone, and it has a fixed point — **no hypothesis on either injection** |
//! | [`bijection`] | the bijection built at that fixed point, and the theorem as a scheme |
//! | [`graph`] | [`schroeder_bernstein`] — the scheme at two set relations |
//! | [`sandwich`] | [`equinumerous_sandwich`] — `a ⊆ b ⊆ c` and `a ≈ c` give `a ≈ b` |
//!
//! `shared` holds the private readers and `H → …` combinators several of them
//! need; it exports no theorem and is not re-exported.
//!
//! # Interface
//!
//! Write `INJECTION(f,a,b)` for [`injection`] — `kernel::thm::equinumerous`'s
//! body with the *onto* clause deleted, same spelling and same described pairs —
//! and `≈` for `kernel::thm::equinumerous`. Then
//!
//! ```text
//! ⊢ ∀a ∀b ∀f ∀g. ((INJECTION(f,a,b) ∧ INJECTION(g,b,a)) → a ≈ b)
//!                                                        [schroeder_bernstein]
//! ⊢ ∀a ∀b ∀c. (((a ⊆ b ∧ b ⊆ c) ∧ a ≈ c) → a ≈ b)      [equinumerous_sandwich]
//! ```
//!
//! plus the scheme both are instances of, [`csb_scheme`], which takes the eight
//! clauses at two arbitrary two-variable *formulas* rather than at two sets.
//! Callers need none of the derivations.
//!
//! # Where the notes this was built from were wrong
//!
//! `crate::universe::inaccessibility` predicted the cost: "the back-and-forth
//! construction needs the recursion theorem, hence `ω` and function graphs". The
//! second half is right and the first half is **not**. The iterative
//! construction — `C₀ = a ∖ g[b]`, `C_{n+1} = g[f[Cₙ]]`, `C = ⋃ₙ Cₙ` — does need
//! `ω`; the Knaster–Tarski construction computes the same set with **one
//! Separation and no recursion at all**, and it needs no power set either
//! because the intersection of all pre-fixed points can be written as a
//! separation *condition* rather than as an intersection of a set of sets. So
//! [`crate::recursion`] — 4 911 lines of `ω`-recursion, and the reason this was
//! scheduled as expensive — is not on the path and was never consulted. See
//! [`fixpoint`].
//!
//! The other half of the prediction is right, and it is where the cost actually
//! went: `equinumerous` is a first-order formula about a bijection **set**, so
//! the conclusion has to be an explicit graph. That graph is
//!
//! ```text
//! φ  :=  { p ∈ a × b : ∃x ∃y. (p = ⟨x,y⟩ ∧ ((x ∈ c ∧ F(x,y))
//!                            ∨ (¬(x ∈ c) ∧ ((y ∈ b ∧ ¬(y ∈ F[c])) ∧ G(y,x))))) }
//! ```
//!
//! — one Separation over `crate::funspace`'s Cartesian product — and proving its
//! five clauses is most of [`bijection`].
//!
//! # Why a scheme in two formulas, and not just two sets
//!
//! The consumer is `crate::universe::inaccessibility`, and what it holds is
//! `y ⊆ U(x) ⊆ u` together with a bijection `y ≈ u`. Neither of the two
//! injections it needs — the *inclusion* `y ↪ U(x)`, and the converse of that
//! bijection *restricted* to `U(x)` — exists as a set in its hands; building
//! them would be two more Replacements and eight more clauses to prove about
//! them. As formulas they are `x = y` and `⟨x,y⟩ ∈ e`, and their eight clauses
//! are one projection each off what the caller already has. So the scheme is
//! not a generalisation ahead of a consumer; it is what the consumer wanted.
//! [`equinumerous_sandwich`] is that instance and [`schroeder_bernstein`] is the
//! set-graph one.
//!
//! # No choice
//!
//! Knaster–Tarski is the choice-free argument, and nothing here calls
//! [`crate::choice`]. `Thm::ax_choice` is ambient in this kernel, so that is a
//! statement about this derivation and not about the theory.

pub mod bijection;
pub mod clauses;
pub mod fixpoint;
pub mod prereq;
mod shared;

pub use clauses::{
    fixed, in_image, inj_dom, inj_inj, inj_sv, inj_total, injection, injection_clauses, pre_fixed,
    step, stopper,
};
pub use bijection::{csb_clauses, csb_scheme};
pub use fixpoint::{csb_fixpoint, step_monotone};
pub use prereq::Csb;
