//! Propositions as subsets of `1`: the conditional singleton `[φ]`, and the
//! interpretations of Lean's `Eq` and `And`.
//!
//! Following Carneiro's *The Type Theory of Lean*, a `Prop` denotes a **subset
//! of `{•}`**: it is true when its denotation is `1 = {•}` and false when it is
//! `0 = ∅`. Proof irrelevance is then not an axiom but a triviality — every
//! inhabitant of such a set *is* `•` — and that is exactly what
//! [`cond_subsingleton`] records.
//!
//! Nothing here is an axiom. The whole module is **one Separation on the unit
//! set**:
//!
//! ```text
//! [φ]  :=  { x ∈ 1 : φ }
//! ```
//!
//! and everything else is a corollary of its defining biconditional plus
//! [`crate::sums::unit_mem`] and [`crate::sums::unit_eta`], which is why the
//! `Sums` built by [`Props::new`] is threaded through rather than rebuilt: two
//! `Sums` would mean two different `1`s and none of the theorems would compose.
//!
//! # `[·]` takes a formula, not a set
//!
//! `φ` is an arbitrary formula, so `[·]` cannot be a function symbol applied to
//! a set — a first-order signature has no way to quantify over formulas. It is a
//! *construction taking a formula*, exactly as [`crate::separation::separation`]
//! is, and [`conditional_singleton`] has the same shape: hand it a formula and
//! the parameters its free variables live in, get back a fresh symbol together
//! with its characteristic theorem. `Eq`, `And` and propositional truncation
//! `‖·‖` are then three instances.
//!
//! # The shape of the development
//!
//! | fact | lemma |
//! |---|---|
//! | `∀x. (x ∈ [φ] ↔ (x ∈ 1 ∧ φ))` | [`conditional_singleton`] |
//! | `φ → • ∈ [φ]` | [`cond_intro`] |
//! | `• ∈ [φ] → φ` | [`cond_elim`] |
//! | `¬φ → [φ] = 0` | [`cond_false`] |
//! | `φ → [φ] = 1` | [`cond_true`] |
//! | `∀x ∀y. ((x ∈ [φ] ∧ y ∈ [φ]) → x = y)` | [`cond_subsingleton`] |
//! | `[φ] ⊆ 1` | [`cond_subset_unit`] |
//! | `‖a‖ = [∃x. x ∈ a]`, with intro, elim and both polarities | [`Trunc`] |
//!
//! # Non-vacuity
//!
//! A subsingleton development is precisely where a vacuous result hides: if
//! `[φ]` came out always-empty, or always-`1`, every lemma above would still be
//! provable and none of them would say anything. So both polarities are pinned
//! on concrete instances. [`Props::eq_distinct`] is the load-bearing one:
//!
//! ```text
//! ⊢ ∀a ∀b. (¬(a = b) → ¬(eq_set(a,a) = eq_set(a,b)))
//! ```
//!
//! Discharged at the two sets [`crate::sums::tags_distinct`] separates, `∅` and
//! `1`, it gives `⊢ ¬(eq_set(∅,∅) = eq_set(∅,1))` — the denotation of a true
//! equation is *not* the denotation of a false one. The tests pin that, together
//! with `⊢ • ∈ eq_set(∅,∅)` and `⊢ ¬(• ∈ eq_set(∅,1))`, and the same pair for
//! `And` at `and_set(1,1)` and `and_set(1,0)`.
//!
//! # Scope
//!
//! Only the **typing** of `Eq.refl` and `And.intro` is built here — enough for
//! the tutorial tests, in which every computing recursor states its result as an
//! equation. The recursors of `Eq` and `And` themselves, indexed families in
//! general, and subsingleton elimination are all out of scope.
//!
//! # Layout
//!
//! This module is a **hub**: both constructions live in their own file with
//! their own interface header, and everything is re-exported here, so the paths
//! `crate::prop::…` all still resolve.
//!
//! | file | what it exports |
//! |---|---|
//! | [`cond`] | the conditional singleton `χ = { x ∈ 1 : φ }`, and the lemmas that use it |
//! | [`cond_ext_n`] | two such singletons over pointwise-equal families are equal — `∀`-extensionality |
//! | [`apparatus`] | [`Props`] — `U₀`, the typing rules over it, and the non-vacuity check |
//! | [`trunc`] | [`Trunc`] — propositional truncation `‖a‖ = [∃x. x ∈ a]`, the third instance |

pub mod apparatus;
pub mod cond;
pub mod cond_ext_n;
pub mod trunc;

pub use apparatus::Props;
pub use cond::{
    cond_elim, cond_false, cond_intro, cond_subset_unit, cond_subsingleton, cond_true,
    conditional_singleton,
};
pub use cond_ext_n::cond_ext_n;
pub use trunc::Trunc;
