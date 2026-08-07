//! [`Rec`]: application and `ω` over a **single** chain of definitional
//! extensions.
//!
//! # Interface
//!
//! [`Rec::new`] builds, from the axioms up, one stack in which
//! [`crate::funcs::Apply`] and [`crate::recursion::Peano`] share their symbols,
//! and exposes [`crate::recursion::app_of_graph`]'s theorem over it. There is no
//! new theorem here — this file exists so that the ones there are compose.
//!
//! # Why it has to be one chain
//!
//! `Apply` and `Peano` each mint their own `∅` when built independently
//! ([`crate::empty::empty`] calls `kernel::thm::define`, which creates a *new*
//! symbol every time), and a theorem about one says nothing about the other.
//! Recursion talks about `app(f, 0)`, so the `0` of `ω` and the `∅` that `app`
//! returns off a domain must be the *same symbol* — otherwise `app(f,0) = c` and
//! `0 ∈ ω` would be statements about two unrelated constants.
//!
//! `Rec` builds the `Apply` first and threads its pairing, its singleton lemma
//! and its empty set into `OmegaCore::with_parts`, so `zero()` is simultaneously
//! `∅`, `0 ∈ ω`, and the value `app` takes off a domain.

use kernel::{Env, Term, Thm};

use crate::funcs::Sets;
use super::naturals::OmegaCore;
use super::peano::Peano;
use super::graph::app_of_graph;

/// Application and `ω` over a single chain of definitional extensions.
///
/// [`crate::funcs::Apply`] and [`Peano`] each mint their own `∅` when built
/// independently ([`crate::empty::empty`] calls `kernel::thm::define`, which
/// creates a *new* symbol every time), and a theorem about one says nothing
/// about the other. `Rec` builds the `Apply` first and threads its pairing,
/// its singleton lemma and its empty set into [`OmegaCore::with_parts`], so
/// `zero()` below is simultaneously `∅`, `0 ∈ ω`, and the value `app` takes off
/// a domain.
pub struct Rec {
    /// Pairing, union, `∅`, `coll` and `app`.
    pub ap: crate::funcs::Apply,
    /// `ω` with the Peano properties, over `ap`'s `∅` and `ap`'s pairing.
    pub peano: Peano,
    /// `⊢ ∀f ∀a ∀b. ((SingleValued(f) ∧ ⟨a,b⟩ ∈ f) → app(f,a) = b)`.
    pub app_of_graph: Thm,
}

impl Rec {
    /// Build the lot, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Rec> {
        let sets = Sets::new(env);
        let ap = crate::funcs::Apply::with_sets(env, sets.clone()).ok()?;
        let core = OmegaCore::with_parts(
            env,
            sets,
            ap.mem_sing.clone(),
            ap.empty,
            ap.empty_ax.clone(),
        )?;
        let peano = Peano::over(env, core)?;
        let app_of_graph = app_of_graph(env, &ap)?;
        Some(Rec { ap, peano, app_of_graph })
    }

    /// The shared `ω` apparatus.
    pub fn core(&self) -> &OmegaCore { &self.peano.core }

    /// The term `0`, which is `∅`.
    pub fn zero(&self) -> Term { self.core().zero() }

    /// The term `ω`.
    pub fn omega(&self) -> Term { self.core().set() }

    /// The term `succ(t)`.
    pub fn succ_of(&self, t: Term) -> Term { self.core().succ_of(t) }

    /// The term `⟨a,b⟩`.
    pub fn pair(&self, a: Term, b: Term) -> Term { self.ap.sets.pair(a, b) }

    /// The term `app(f,a)`.
    pub fn apply(&self, f: Term, a: Term) -> Term { self.ap.apply(f, a) }
}
