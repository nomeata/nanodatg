//! The empty set, **derived** from Tarski's Axiom A and Regularity.
//!
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::empty::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`readers`] | the five syntax readers the rest of the crate shares |
//! | [`irreflexive`] | `⊢ ∀x. ¬(x ∈ x)`, from Regularity at a singleton |
//! | [`two_cycle`] | `⊢ ∀a ∀b. ¬(a ∈ b ∧ b ∈ a)`, from Regularity at a pair |
//! | [`tarski`] | [`Universe`], `𝒫y ∈ u`, and "`u` has no `∈`-maximal element" |
//! | [`set`] | the symbol `∅`, and Separation from one non-empty transitive set |
//! | [`induction`] | `Ind`, `Least`, and their existence — Infinity, derived |
//! [`empty`] is the working symbol, `∅` with `⊢ ∀z. ¬(z ∈ ∅)`, which
//! [`crate::separation::separation`], [`crate::funcs::separation_full`] and
//! everything downstream of them consume. It rests on no empty-set axiom:
//! `Thm::ax_empty` was **deleted on 2026-07-31**, taking the trusted set axioms
//! from eight to seven. What follows is what replaced it.
//!
//! # The derivation
//!
//! [`empty_existence`] proves `⊢ ∃e ∀z. ¬(z ∈ e)` in three moves, and
//! [`empty_of_exists`] turns that into the symbol, uniqueness coming from
//! Extensionality via [`crate::define_by_membership`].
//!
//! 1. **A non-empty set.** [`tarski_at`] puts an arbitrary `x` inside a universe
//!    `u`, so `x` itself witnesses `∃w. w ∈ u`. Nothing stronger is needed —
//!    [`crate::universe::universe_three_members`] would also serve, and costs
//!    considerably more.
//! 2. **A transitive one.** Tarski's clause `C₁`, `∀y ∈ u. ∀z ∈ y. z ∈ u`, says
//!    exactly that `u` is transitive. It is stated curried and guarded, while
//!    [`transitive`] is uncurried and conjunctive; [`transitive_of_clause`] is
//!    the shuffle between the two shapes, and the only fiddly step in the whole
//!    derivation.
//! 3. **Regularity.** [`empty_from_transitive`] proves
//!    `⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)`: an `∈`-minimal member
//!    of a transitive set shares no member with it, but all of its own members
//!    *are* members of it, so it has none.
//!
//! The universe variable is then discharged by [`crate::exists_elim`], which it may be
//! because the conclusion does not mention it. No `Thm` anywhere in this module
//! is produced other than through the kernel's rules.
//!
//! # Why this was not possible before
//!
//! `separation.rs` records why an empty set is not derivable from
//! Extensionality, Pairing, Union, Power, Replacement and Regularity: those are
//! all modelled by the sets generated from a `ℤ`-indexed membership chain, in
//! which nothing bottoms out. That model does *not* satisfy Tarski (see
//! [`universe_no_maximal`]), so the independence argument stops applying once
//! `ax_tarski` is in play — but until 2026-07-31 `ax_tarski` had no transitivity
//! clause, and step 2 above was unavailable. Its second clause closed `u` only
//! under *subsets* of members, so from `w ∈ y ∈ u` one got `{w} ⊆ y`, hence
//! `{w} ∈ u` — the singleton, never `w` itself. Every attempt to apply
//! Regularity (to `u`, to `⋃u`, to `𝒫m`, to `u ∪ ⋃u`) yielded a minimal element
//! not known to be a subset of the set it was minimal in, and stalled in the
//! same place each time.
//!
//! The route then planned was much longer: the recursion theorem, the iterates
//! `⋃ⁿx`, and their union as the transitive closure of `x`. `C₁` removes the
//! obstruction outright — `w ∈ y ∈ u` now gives `w ∈ u` — so a universe *is*
//! transitive and the closure is not needed. That machinery is not wasted; it is
//! what [`crate::recursion`] is built on.
//!
//! # What else Tarski gives, on the way
//!
//! The `𝒫`-tower results below are independent of the `∅` derivation and are
//! kept because they are what makes induction available.
//!
//! * [`universe_power_closed`] derives `∀y ∈ u. 𝒫y ∈ u`, by taking the
//!   `p ⊇ 𝒫y` that Tarski's third clause supplies inside `u` and pushing
//!   `𝒫y ⊆ p` back into `u` with the second.
//! * Hence [`inductive_set_exists`]: `⊢ ∀x ∃u. (x ∈ u ∧ ∀y ∈ u. 𝒫y ∈ u)` — an
//!   **inductive set**, which is to say Tarski gives Infinity.
//! * And [`least_inductive_set_exists`]: `⊢ ∀x ∃n. Least(x, n)`, an `ω`
//!   contained in every inductive set, **so induction is available**. It is
//!   carved out of `u` by Separation at "lies in every `𝒫`-inductive set", which
//!   is [`crate::separation::separation_nonvacuous`] — the *non-vacuous* form,
//!   needing no empty set, because `x` itself satisfies the condition. That is
//!   what kept the argument non-circular back when `∅` was still downstream of
//!   it.
//!
//! [`separation_from_transitive`] remains the sharpest statement of the general
//! fact: full Separation costs one non-empty transitive set and nothing else.
//! [`empty_existence`] is that statement cashed in at Tarski's universe.

pub mod induction;
pub mod irreflexive;
pub mod readers;
pub mod set;
pub mod tarski;
pub mod two_cycle;

pub use induction::{
    inductive, inductive_set_exists, least_inductive, least_inductive_set_exists,
};
pub use irreflexive::no_self_mem;
pub use two_cycle::no_two_cycle;
pub use readers::{curry, hyp_contract, open_exists, open_forall, split_and};
pub use set::{
    empty, empty_existence, empty_from_transitive, empty_of_exists, separation_from_transitive,
    transitive, transitive_of_clause,
};
pub use tarski::{
    tarski_at, tarski_at_term, universe_no_maximal, universe_power_closed, Universe,
};
