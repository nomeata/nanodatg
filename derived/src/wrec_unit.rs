//! **ι fires.** The recursor of [`crate::wrec`], computed at a concrete
//! instance.
//!
//! # Why this file exists
//!
//! Everything [`crate::wrec`] proves about `wrec(A,B,u,T,e)` — including
//! [`crate::wrec::iota_on_domain`] — is **vacuously true of an empty
//! recursor**. `⊢ ∅ ∈ Att` says the attempt condition is satisfiable; it says
//! nothing about `wrec` having a single member, and every ι statement is
//! guarded by `indom(wrec, ⟨a,f⟩)`. Until that guard is discharged *somewhere*,
//! the module is a set of statements about a set that might be `∅`.
//!
//! This file discharges it, at the smallest instance there is, and **without
//! needing totality**:
//!
//! ```text
//! A := {c}      B := ∅      u := U(c)      V := app(e, ⟨c,⟨∅,∅⟩⟩)      T := {V}
//! ```
//!
//! The sole element of `W({c},∅,U(c))` is `⟨c,∅⟩` ([`crate::bound`] builds it),
//! and the one-point graph `g := {⟨⟨c,∅⟩, V⟩}` is an attempt. The recursion
//! condition is not circular, because the fibre is `B(c) = app(∅,c) = ∅`
//! ([`crate::wtype::app_of_empty`]) and a composite over an empty domain is
//! empty whatever it composes ([`comp_empty_domain`]) — so `V` is a **closed**
//! term, not a fixed point equation.
//!
//! # Interface
//!
//! Writing `W` for `W({c},∅,U(c))`, `V` for `app(e, ⟨c,⟨∅,∅⟩⟩)`, `T` for `{V}`
//! and `g` for `{⟨⟨c,∅⟩, V⟩}`:
//!
//! ```text
//! ⊢ ∀g ∀f. comp(g,f,∅) = ∅                                   [comp_empty_domain]
//! ⊢ closed({c}, ∅, U(c))                              [unit_wtype → UnitWtype::closed]
//! ⊢ ⟨c,∅⟩ ∈ W                                         [unit_wtype → UnitWtype::sup]
//! ⊢ g ∈ Att({c}, ∅, U(c), T, e)                [singleton_attempt → UnitAttempt::att]
//! ⊢ app(g, ⟨c,∅⟩) = V                        [singleton_attempt → UnitAttempt::value]
//! ⊢ app(wrec({c}, ∅, U(c), T, e), ⟨c,∅⟩) = app(e, ⟨c,⟨∅,∅⟩⟩)        [iota_fires]
//! ```
//!
//! That line is the first point of the file: **both sides are computed**, the
//! left-hand side really is an application of the recursor, and the two sides
//! are visibly different terms — `tests/wrec.rs` asserts that they are, so the
//! equation cannot be reflexivity in disguise.
//!
//! # The second point: `step_typed`, discharged
//!
//! [`crate::wrec_total`]'s three theorems all carry
//! `closed(A,B,u) ∧ step_typed(A,B,u,T,e)`, and `step_typed` is a hypothesis
//! the construction cannot discharge — `e` is an arbitrary set. A theorem whose
//! antecedent no five sets satisfy proves nothing, so this file satisfies it,
//! at the same instance:
//!
//! ```text
//! ⊢ step_typed({c}, ∅, U(c), T, e)                          [unit_step_typed]
//! ⊢ wrec({c}, ∅, U(c), T, e) ∈ fs(W, T)                       [unit_funspace]
//! ⊢ app(wrec({c}, ∅, U(c), T, e), ⟨c,∅⟩) = app(e, ⟨c,⟨∅,∅⟩⟩)      [unit_iota]
//! ```
//!
//! The second has **no antecedent left**: both hypotheses of
//! [`crate::wrec_total::wrec_funspace`] are gone. The third is the *general* ι
//! rule fired here, and `tests/wrec_total.rs` checks it is literally the same
//! formula [`iota_fires`] proves by hand — two independent routes, one
//! equation.
//!
//! `step_typed` holds here for a reason that does not generalise, which is
//! exactly what makes it cheap: the fibre is `∅`, and [`crate::wtype::empty_funspace`]
//! makes `∅` the only function out of `∅`, so the step's arguments are forced
//! and its value is the closed term `V`.
//!
//! `c` and `e` are the caller's: nothing here is special about them, so the
//! statement is not about one hand-picked set. In the tests they are fresh
//! constants.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wrec_unit::…` all still resolve. Read the header of the one file you
//! need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`composite`] | [`comp_empty_domain`] — what stops the recursion being circular |
//! | [`instance`] | the unit W-type: `closed({c},∅,U(c))` and `⟨c,∅⟩ ∈ W` |
//! | [`attempt`] | the one-point graph, and that it is an attempt |
//! | [`fires`] | [`wrec_member`] and [`iota_fires`] — the guard discharged |
//! | [`typing`] | `step_typed` discharged, and with it `wrec ∈ fs(W,T)` and the general ι |
//!
//! `shared` holds the two private equational moves both halves need; it exports
//! no theorem and is not re-exported.

pub mod attempt;
pub mod composite;
pub mod fires;
pub mod instance;
mod shared;
pub mod typing;

pub use attempt::{singleton_attempt, unit_graph, unit_target, unit_value, UnitAttempt};
pub use composite::comp_empty_domain;
pub use fires::{iota_fires, wrec_member};
pub use instance::{unit_wtype, UnitWtype};
pub use typing::{unit_funspace, unit_iota, unit_step_typed};
