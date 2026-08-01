//! Set-theoretic function application, and beta reduction.
//!
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::funcs::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`logic`] | disjunction introduction, case analysis, and the `⊢ H → φ` forms of MP and syllogism |
//! | [`sets`] | [`Sets`], and the two Union lemmas everything about `app` starts from |
//! | [`separation`] | Separation from Replacement: conditionally, then outright |
//! | [`coll`] | the symbol `coll(f,a) = { y : ⟨a,y⟩ ∈ f }` |
//! | [`apply`] | [`Apply`], `app`'s membership condition, and `app` off the domain |
//! | [`beta`] | lambda graphs, and beta reduction |
//! `app(f, a)` is `⋃ { y : ⟨a,y⟩ ∈ f }`, so the construction climbs four rungs:
//!
//! 1. every such `y` lies in `⋃⋃f` ([`snd_in_union2`]), which gives Separation
//!    a superset to cut the collection out of;
//! 2. Separation itself, derived from the Replacement scheme
//!    ([`separation_nonempty`] for an inhabited result, [`separation_full`] for
//!    any result at all);
//! 3. the collection as a function symbol ([`collection`]), and `app` as the
//!    union of it ([`Apply`], [`app_members`]);
//! 4. beta reduction for the graph `{ ⟨x,t(x)⟩ : x ∈ A }` ([`lambda`],
//!    [`beta_conditional`]), and its off-domain complement
//!    ([`app_off_domain`]).
//!
//! # The empty set, and what it removed
//!
//! Replacement gives Separation directly only for an *inhabited* result: the
//! choice relation needs a default value, and the only harmless default is an
//! element of the answer. The vacuous case produces a set with no members, so
//! it needs `∅` — and for as long as `∅` was not available, [`collection`] had
//! to be made total by falling back on an arbitrary default when there was
//! nothing to collect, with an inhabitation antecedent on its characteristic
//! theorem to hide the default away.
//!
//! `crate::empty::empty` supplies `∅` ([`crate::empty::empty`]), [`separation_full`]
//! glues the two cases, and the fallback is gone. `coll(f,a)` *is*
//! `{ y : ⟨a,y⟩ ∈ f }`, empty or not, and
//!
//! ```text
//! ⊢ ∀f ∀a ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f)
//! ⊢ ∀f ∀a ∀w. (w ∈ app(f,a) ↔ ∃y. (⟨a,y⟩ ∈ f ∧ w ∈ y))
//! ```
//!
//! hold outright. Beta reduction never paid for the antecedent anyway — what
//! had to be inhabited was the *collection*, not the value, and on the domain
//! the collection contains `t(a)` whatever `t(a)` is — so
//! [`beta_conditional`] is unchanged. What *is* new is the other half:
//! [`app_off_domain`] proves `⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)`,
//! which was previously not even statable.

pub mod apply;
pub mod beta;
pub mod coll;
pub mod logic;
pub mod separation;
pub mod sets;

pub use apply::{app_members, app_off_domain, Apply};
pub use beta::{beta_conditional, beta_conditional_n, lambda, lambda_n};
pub use coll::{collection, collection_conditional, value_collection};
pub use logic::{cases, hyp_mp2, hyp_syl, or_intro_left, or_intro_right};
pub use separation::{cond_relation_unique, separation_full, separation_nonempty};
pub use sets::{snd_in_union2, union_intro, Sets};
