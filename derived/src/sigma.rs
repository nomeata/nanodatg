//! The dependent sum `Σ`, at one level and iterated over a telescope — §5.2's
//! rule for a constructor's non-recursive arguments.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::sigma::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`pair_parts`] | `q ∈ A × B → (π₁q ∈ A ∧ π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)` — the bridge from [`crate::proj`]'s rules "at a literal pair" to an elimination rule handed a bare element |
//! | [`dsum`] | [`DSum`] — one `Σ` level over a domain and a fibre symbol, with intro, both projections and η |
//! | [`telescope`] | [`Telescope`] — `k` levels nested, with the packing rule, the `k` typed projections and η |
//!
//! `shared` holds the private implication-form rewrite combinators more than
//! one of them needs; it exports no theorem and is not re-exported.
//!
//! # Why this exists
//!
//! `thesis.txt:1795–1797`:
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ ∀y : β. τ ctor ⇒ Σy' : β. A[y'/y];
//!                                        p'. B[π₁p'/y][π₂p'/p];  …
//! ```
//!
//! `derived/` had no `Σ` at all before this module — [`crate::funspace`] has
//! the *Cartesian* product and [`crate::ext::dprod`] the dependent
//! **product**, neither of which is a dependent sum — and it had the
//! projections ([`crate::proj`]) only at terms already written as pairs. Those
//! two gaps are what [`dsum`] and [`pair_parts`] fill; [`telescope`] is the
//! iteration, and it is what turns a constructor's argument list into one tag
//! summand for [`crate::isum`].
//!
//! # Nothing here is an axiom
//!
//! One Replacement and one Separation per `Σ` level, both unconditional, plus
//! one [`crate::define_abbrev`] naming the innermost `1`. No new axiom.

pub mod dsum;
pub mod pair_parts;
mod shared;
pub mod telescope;

pub use dsum::{dsum, DSum};
pub use pair_parts::product_parts;
pub use telescope::Telescope;
