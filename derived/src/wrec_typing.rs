//! Typing for the recursor's composite: `comp(g,f,d) ∈ fs(d,T)`.
//!
//! # What this is for
//!
//! Step 4 of `INDUCTIVES.md`'s recipe — totality of the recursor — extends an
//! attempt by one point, and an attempt is *by definition* a subset of
//! `W × T`. So the new value `app(e, ⟨a,⟨f, comp(wrec,f,B(a))⟩⟩)` has to be
//! shown to lie in `T`, and `e` is an arbitrary set: the only way is to
//! hypothesise the step's typing,
//!
//! ```text
//! step_typed(A,B,u,T,e) := ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) →
//!                             ∀r. (r ∈ fs(B(a), T) → app(e, ⟨a,⟨f,r⟩⟩) ∈ T)))
//! ```
//!
//! and then *discharge its third premise* by showing that the composite really
//! is a function from the fibre to `T`. That last part is what this file
//! proves, and it is independent of the induction that uses it. That induction
//! now exists — [`crate::wrec_extend`] — and
//! [`wrec_composite_typed`]'s antecedent is *literally* its induction
//! hypothesis, so it drops in with no adaptation.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀f ∀d ∀x ∀y. (⟨x,y⟩ ∈ comp(g,f,d) → y = app(g, app(f,x)))
//!                                                          [composite_value]
//! ⊢ ∀g ∀f ∀d. sv(comp(g,f,d))                     [composite_single_valued]
//! ⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d), b) = app(g, app(f,b)))
//!                                                            [composite_app]
//! ⊢ ∀g ∀f ∀d ∀T. ((∀b. (b ∈ d → app(g, app(f,b)) ∈ T)) → comp(g,f,d) ∈ fs(d,T))
//!                                                          [composite_typed]
//! ```
//!
//! [`composite_app`] is the one an inductive with a **non-empty fibre** needs.
//! `Bool.rec` never asked for it: every fibre of an enumeration is `∅`, so
//! [`crate::wrec_unit::comp_empty_domain`] collapses the composite and the ι
//! rule's right-hand side loses its recursive call. `N.rec` cannot avoid it —
//! the `succ` fibre is `1`, the subterm family is the one-point graph
//! `{⟨•,n⟩}`, and the recursive call *is* `app(comp(wrec,{⟨•,n⟩},1), •)`.
//!
//! All are unconditional in `g` and `f`: neither needs `f` to be a function,
//! nor `g`, nor `d` to be `f`'s domain. `comp` is a Replacement image along
//! `b ↦ ⟨b, app(g,app(f,b))⟩` ([`crate::wrec::compose`]), so it is a function
//! on `d` whatever it composes — single-valuedness is injectivity of the
//! Kuratowski pair and nothing else. Only the *codomain* needs a hypothesis,
//! and [`composite_typed`]'s is the weakest one that names `T`.
//!
//! # Non-vacuity
//!
//! The hypothesis of [`composite_typed`] is not one no set satisfies:
//! `tests/wrec.rs` discharges it at `d := ∅`, where it is vacuous, and reads
//! off `⊢ comp(g,f,∅) ∈ fs(∅,T)` for arbitrary `g`, `f` and `T`.
//!
//! # Layout
//!
//! This module is a **hub**: both constructions live in their own file with
//! their own interface header, and everything is re-exported here, so the paths
//! `crate::wrec_typing::…` all still resolve.
//!
//! | file | what it exports |
//! |---|---|
//! | [`composite`] | the composite is a function into `T`, unconditionally in `g` and `f` |
//! | [`values`] | the recursor's values are in `T`, and hence so are its composites' |

pub mod composite;
pub mod values;

pub use composite::{
    composite_app, composite_single_valued, composite_typed, composite_value,
};
pub use values::{wrec_composite_typed, wrec_value_typed};
