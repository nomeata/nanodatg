//! [`Csb`]: the four constructions the bijection is assembled out of, bundled.
//!
//! # Interface
//!
//! ```text
//! Csb::new(env)             -> DResult<Csb>   // mints its own pairing
//! Csb::with_apply(env, &ap) -> DResult<Csb>   // shares a caller's pairing
//! ```
//!
//! A [`Csb`] carries
//!
//! ```text
//! ap             crate::funcs::Apply     — pairing, ∅, and the pair's injectivity
//! prod           crate::funspace::Product — the Cartesian product a × b
//! ⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))              [pair_in_prod]
//! ⊢ ∀f ∀a ∀b. ((∃p. (p ∈ f ∧ is_opair(p,a,b))) ↔ ⟨a,b⟩ ∈ f)     [pair_in_bridge]
//! ```
//!
//! and nothing else. Bundled rather than passed one at a time because
//! [`super::bijection`] needs all four and threading them individually makes the
//! signature unreadable.
//!
//! # How this fails
//!
//! Nothing here declines. Each of the four prerequisites is a construction in a
//! module that has not moved to [`crate::err::DResult`] yet, so each call goes
//! through [`crate::err::imported`] and a refusal arrives as a
//! [`crate::err::DerErr::Assembly`] naming the construction that refused and the
//! line here that asked for it. That is the honest amount of information
//! available, and it says which module to migrate next.
//!
//! Neither entry carries `#[track_caller]`: which of the four prerequisites
//! failed is precisely what a reader needs, and moving the site out to the
//! caller would throw it away.
//!
//! # Why the product, and why the bridge
//!
//! The **product** is the superset the bijection is separated out of.
//! `crate::funspace::cartesian` builds it from Replacement, so its membership
//! condition is unconditional and no inhabitation antecedent survives — which
//! matters, because the bijection between two empty sets is empty.
//!
//! The **bridge** is what lets the finished graph be *described*.
//! `kernel::thm::equinumerous` speaks of `∃p. (p ∈ f ∧ is_opair(p,a,b))`, a
//! condition in the signature `{∈,=}`; the graph is built out of the *term*
//! `⟨a,b⟩ = {{a},{a,b}}`, which exists only because `upair` is a definitional
//! extension. `crate::choice::pair_in_bridge` is the translation, and this is
//! the second consumer of it — `crate::choice`'s header predicted that
//! "`ax_tarski`'s equinumerosity clause will want the same bridge the day anyone
//! tries to use it", and that day is this file.
//!
//! **Everything must be built over one pairing.** Two calls to
//! `crate::funcs::Apply::new` mint two unrelated ordered pairs whose terms do
//! not compose, and the bridge would then translate the wrong one.
//! [`Csb::with_apply`] is what a caller that already has an `Apply` — the
//! `crate::prelude`, for instance — should use.

use kernel::{Env, Thm};

use crate::err::{imported, DResult};
use crate::funcs::Apply;
use crate::funspace::{product, Product};

/// The prerequisites of [`super::bijection`], over one shared pairing.
pub struct Csb {
    /// Pairing, `∅`, `{a}`'s members, and `⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d)`.
    pub ap: Apply,
    /// The Cartesian product the bijection is separated out of.
    pub prod: Product,
    /// `⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))`.
    pub pair_in_prod: Thm,
    /// `⊢ ∀f ∀a ∀b. ((∃p. (p ∈ f ∧ is_opair(p,a,b))) ↔ ⟨a,b⟩ ∈ f)` — the
    /// described pair meets the constructed one.
    pub pair_in_bridge: Thm,
}

impl Csb {
    /// Build everything from the axioms up, over a freshly minted pairing.
    pub fn new(env: &mut Env) -> DResult<Csb> {
        let ap = Apply::new(env)?;
        Csb::with_apply(env, &ap)
    }

    /// Build everything over the caller's pairing, which is what a caller that
    /// already has an [`Apply`] must do: the ordered pair the bijection is made
    /// of has to be the one the caller's other lemmas speak of.
    pub fn with_apply(env: &mut Env, ap: &Apply) -> DResult<Csb> {
        let prod = imported("crate::funspace::product", product(env, &ap.sets))?;
        let pair_in_prod = imported(
            "crate::sums::pair_in_product",
            crate::sums::pair_in_product(env, ap, &prod),
        )?;
        let described = imported(
            "crate::choice::opair_described",
            crate::choice::opair_described(env, &ap.sets, &ap.mem_sing),
        )?;
        let pair_in_bridge = imported(
            "crate::choice::pair_in_bridge",
            crate::choice::pair_in_bridge(env, &ap.sets, &described),
        )?;
        Ok(Csb { ap: ap.clone(), prod, pair_in_prod, pair_in_bridge })
    }
}
