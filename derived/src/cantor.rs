//! Cantor's theorem, and the regularity of a universe.
//!
//! # Interface
//!
//! Write `R(x,b)` for an arbitrary two-variable formula and `⟨x,b⟩ ∈ k` for
//! `kernel::thm::pair_in`, i.e. `∃p. (p ∈ k ∧ is_opair(p,x,b))` — the notion
//! `kernel::thm::equinumerous` is written with, so the bijection `C₄` hands over
//! plugs straight in with no translation layer. Then, with
//!
//! ```text
//! DOM (R,I)  :=  ∀x ∀b. (R(x,b) → x ∈ I)
//! SV  (R)    :=  ∀x ∀b ∀c. ((R(x,b) ∧ R(x,c)) → b = c)
//! ONTO(R,S)  :=  ∀b. (b ∈ S → ∃x. R(x,b))
//! ONTO⊆(R,I) :=  ∀b. (b ⊆ I → ∃x. R(x,b))
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ ¬(DOM(R,I) ∧ (SV(R) ∧ ONTO⊆(R,I)))                    [no_diagonal_surjection]
//! ⊢ ∀I ∀k. ¬(DOM ∧ (SV ∧ ONTO⊆)) at R(x,b) := ⟨x,b⟩ ∈ k   [no_surjection_onto_subsets]
//! ⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → ¬(y ≈ u))          [member_not_equinumerous]
//! ⊢ ((is_universe(u) ∧ (I ∈ u ∧ S ⊆ u))
//!      ∧ (DOM(R,I) ∧ (SV(R) ∧ ONTO(R,S))))  →  S ∈ u      [image_in_universe]
//! ```
//!
//! Callers need none of the derivations; the four statements above are the whole
//! contract. [`image_in_universe`] is the one the rest of the development wants:
//! it is **regularity**, the fact that turns `C₄`'s disjunction into a closure
//! property.
//!
//! # What this needs from the axiom
//!
//! `C₂` and `C₄`. **Not the transitivity clause `C₁`** — which is worth saying,
//! because the plan this module was written to execute expected
//! [`member_not_equinumerous`] to go through `𝒫y ∈ u` and transitivity. It does
//! not have to: `C₂` says directly that a subset of a member is a member, which
//! is all the diagonal argument needs. So both universe theorems here were
//! available before 2026-07-31 and simply had not been proved. `C₁` becomes
//! indispensable one step further on, where a *function set* has to be shown to
//! be a subset of `u`; see the countermodels at the end of `crate::universe`.
//!
//! # Why the surjective form, and why `b ⊆ I` rather than `b ∈ 𝒫I`
//!
//! The usual Cantor statement is about injections `𝒫I ↪ I`, and getting from
//! "injection both ways" to "equinumerous" is Cantor–Schröder–Bernstein
//! ([`crate::csb`], which did not exist when this was written). The
//! **surjective** form needs none of that: the diagonal set is built directly
//! from the relation, and the contradiction is one biconditional. It is also
//! strictly more useful here, because the objects `C₄` produces are surjections
//! onto `u`, not injections into it.
//!
//! Three clauses are asked of `k` and no more: its pairs start in `I`, it is
//! single-valued, and every subset of `I` is hit. **Totality and injectivity
//! are not used** — the diagonal argument does not need them, and leaving them
//! out is what lets a bijection be *restricted* to a subset of its codomain and
//! still qualify, which is exactly the move [`member_not_equinumerous`] makes.
//! Phrasing the target as `b ⊆ I` rather than `b ∈ 𝒫I` keeps the power-set
//! symbol out of the statement altogether.
//!
//! # The diagonal
//!
//! `D := { x ∈ I : ∀b. (⟨x,b⟩ ∈ k → ¬(x ∈ b)) }`, one
//! [`crate::funcs::separation_full`]. `D ⊆ I`, so some `j` has `⟨j,D⟩ ∈ k`, and
//! `j ∈ I`. Then `j ∈ D` unfolds to `j ∈ I ∧ φ(j)`, and `φ(j)` is equivalent to
//! `¬(j ∈ D)`: forwards by instantiating `φ(j)` at `D` itself, backwards because
//! single-valuedness makes `D` the *only* `b` with `⟨j,b⟩ ∈ k`. So
//! `j ∈ D ↔ ¬(j ∈ D)`.
//!
//! Note where each clause is spent: `DOM` supplies `j ∈ I` (without it `j ∈ D`
//! would not follow from `φ(j)`), `ONTO` supplies `j`, and `SV` supplies the
//! backward direction. Dropping any one of the three makes the statement false.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::cantor::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`clauses`] | `DOM`, `SV`, `ONTO` and `ONTO⊆` as formulas, for the scheme and for a set relation |
//! | [`diagonal`] | Cantor's theorem: [`no_diagonal_surjection`] and its set instance |
//! | [`equinumerous`] | [`member_not_equinumerous`] — what refutes `C₄`'s second disjunct |
//! | [`image`] | [`image_in_universe`] — **regularity**, the export the rest wants |
//!
//! `shared` holds the private formula readers and `H → …` combinators more than
//! one of them needs; it exports no theorem and is not re-exported.

pub mod clauses;
pub mod diagonal;
pub mod equinumerous;
pub mod image;
mod shared;

pub use clauses::{
    onto_subsets, pairs_start_in, r_dom, r_onto, r_onto_subsets, r_sv, single_valued,
    surjects_onto_subsets,
};
pub use diagonal::{no_diagonal_surjection, no_surjection_onto_subsets};
pub use equinumerous::member_not_equinumerous;
pub use image::{image_in_universe, surjects_onto};
