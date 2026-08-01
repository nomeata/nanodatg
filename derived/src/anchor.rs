//! **The anchor of the threat model**: the translations of `Empty` and `False`
//! are genuinely empty.
//!
//! # Why this module exists
//!
//! The project's `README.md` states the whole guarantee as
//!
//! > if a development translates and the kernel accepts every step, the
//! > development proves no contradiction. **That holds as long as the
//! > translation of `False` is genuinely refutable in the target.**
//!
//! Every other claim about the interpretation is deliberately weak — we do not
//! claim our `List` is really a list. This one cannot be weak, because it is the
//! clause the guarantee rests on. Nothing in the crate proved it before this
//! module; each of `⟦Empty⟧` and `⟦False⟧` could have been an arbitrary
//! non-empty set and no test would have noticed.
//!
//! # Interface
//!
//! Writing `enum(0)` for the term [`crate::enums::enum0`] hands back, `0` for
//! `∅` and `{0,1}` for the two-element set of truth values:
//!
//! ```text
//! ── the W-type side (Empty) ──
//! ⊢ ∀B. closed(∅, B, ∅)                              [wtype::empty_closed]
//! ⊢ ∀B ∀u ∀x. ¬(x ∈ W(∅, B, u))                      [wtype::empty_wtype_uninhabited]
//! ⊢ ∀B ∀u. W(∅, B, u) = ∅                            [wtype::empty_wtype_eq]
//! ⊢ ∀x. ¬(x ∈ enum(0))                               [wtype::enum0_uninhabited]
//! ⊢ enum(0) = ∅                                      [wtype::enum0_eq]
//! ⊢ ∀T. ∅ ∈ fs(enum(0), T)                           [wtype::enum0_rec]
//! from ⊢ c = X and ⊢ ∀x. ¬(x ∈ X)  infer  ⊢ ∀x. ¬(x ∈ c)   [wtype::uninhabited_along]
//!
//! ── the Prop side (False) ──
//! ⊢ ∀x. ¬(x ∈ ⟦False⟧)                               [falsity::false_uninhabited]
//! ⊢ t ∈ ⟦False⟧ → ψ,  for any term t and formula ψ    [falsity::false_absurd]
//! ⊢ ⟦False⟧ ∈ ⟦Prop⟧                                 [falsity::false_in_prop]
//! ⊢ ⟦True⟧ ∈ ⟦Prop⟧                                  [falsity::true_in_prop]
//! ⊢ ¬(⟦False⟧ = ⟦True⟧)                              [falsity::prop_two_valued]
//! ⊢ [φ] ∈ ⟦Prop⟧                                     [falsity::cond_in_prop]
//! ⊢ [⊥] = ⟦False⟧                                    [falsity::bot_is_false]
//! ⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)            [falsity::prop_subsingleton]
//! ```
//!
//! # Which formulation of the `False` anchor, and why
//!
//! Three statements were on the table: `∀x. ¬(x ∈ ⟦False⟧)`, `⟦False⟧ = ∅`, and
//! "from `t ∈ ⟦False⟧` every formula follows". In *this* kernel the first two
//! are one step apart and the first **is** the third: negation is not primitive,
//! `Formula::not(φ)` is literally `φ → ⊥`, so
//!
//! ```text
//! ⊢ ∀x. ¬(x ∈ ⟦False⟧)      is      ⊢ ∀x. (x ∈ ⟦False⟧ → ⊥)
//! ```
//!
//! and a derivation of `⊢ t ∈ ⟦False⟧` yields `⊢ ⊥` by one instantiation and one
//! modus ponens, hence any `ψ` by [`crate::ex_falso`]. So the uninhabitedness
//! statement is the primary one; [`falsity::false_absurd`] packages the second
//! step for callers, and `= ∅` is kept because it is the thesis's own clause
//! (§6.2: `⟦Γ ⊢ ⊥⟧γ = ∅`) and because the W-type side needs it anyway.
//!
//! # `Prop` is `{0, 1}`, and that is where `False` comes from
//!
//! Carneiro's *The Type Theory of Lean* identifies `Prop` with the zeroth
//! universe: `P := U₀` and `U₀ = {∅, {•}}` with `• = ∅`. A proposition *is* a
//! subset of `{•}`, which is why proof irrelevance needs no axiom — that is
//! [`falsity::prop_subsingleton`], derived here for **every** member of
//! `⟦Prop⟧`, not just for the conditional singletons [`crate::prop`] builds.
//! `⊥` is the empty `Prop`-inductive, so `⟦False⟧ = 0`, and the anchor is then
//! [`crate::empty`]'s `⊢ ∀z. ¬(z ∈ ∅)` read at that term.
//!
//! # Non-vacuity
//!
//! An emptiness theorem is the one shape that *cannot* be vacuous by being
//! about nothing — but it can be vacuous by being about the **wrong term**.
//! `⊢ ∀x. ¬(x ∈ S)` says nothing about the interpretation unless `S` is the term
//! the backend actually produces. So:
//!
//! * [`wtype::enum0_uninhabited`] and [`wtype::enum0_eq`] are stated at the term
//!   [`crate::enums::enum0`] builds — the function calls it rather than
//!   re-spelling `W(∅,∅,U(∅))`, and refuses to return a theorem whose subject is
//!   any other term. `checker/src/tg.rs`'s `Inductives::ty(0)` hands back exactly
//!   that term for a zero-constructor enumeration, which is what `⟦Empty⟧`
//!   abbreviates.
//! * [`falsity`] is **not** yet tied to a backend term: `⟦Sort 0⟧` is an opaque
//!   nullary symbol in `checker/src/tg.rs` (`interp_sort`), and a `Prop`-valued
//!   inductive with no value — which `False` is — falls through to an opaque
//!   nullary symbol too. The statements here are about the term the backend
//!   *should* produce. See this crate's `tests/anchor.rs` and the module note in
//!   [`falsity`].
//!
//! And in the other direction, a development in which `1 = 0` would make every
//! statement here true and none of them informative, so
//! [`falsity::prop_two_valued`] is derived as well: the two truth values are
//! different sets.

pub mod falsity;
pub mod wtype;

pub use falsity::{
    bot_is_false, cond_in_prop, false_absurd, false_in_prop, false_set, false_uninhabited,
    prop_subsingleton, prop_two_valued, true_in_prop, true_set, truth_values,
};
pub use wtype::{
    empty_closed, empty_wtype_eq, empty_wtype_uninhabited, enum0_eq, enum0_rec, enum0_uninhabited,
    uninhabited_along,
};
