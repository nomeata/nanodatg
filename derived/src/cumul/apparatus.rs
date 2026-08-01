//! **One signature carrying both halves** — the general inductive translation
//! ([`crate::inductive::Machine`]) and the cumulative hierarchy
//! ([`super::Chain`]) over the *same* pairing, `∅`, `𝒫`, `ω`, `U(·)` and `W`.
//!
//! # Interface
//!
//! ```text
//! IndChain::new(env)                  -> Option<IndChain>
//! IndChain::over(env, tower, wt, bnd) -> Option<IndChain>
//! IndChain::build(env, spec)          -> Option<Inductive>
//! ```
//!
//! and the four fields [`IndChain::tower`], [`IndChain::chain`],
//! [`IndChain::mach`], [`IndChain::clo`]. Nothing here is new mathematics: it
//! is the assembly, and it exists for the reason [`super::ambient`] exists —
//! getting it wrong is *silent*.
//!
//! # Why an assembly step is needed at all
//!
//! [`crate::inductive::Machine::new`] mints its own [`Wtype`] and [`Bound`],
//! and so does [`super::Chain::new`] (by way of its own [`Tower`]). Two of
//! either in one `Env` are two different `W`, two different `U(·)` and two
//! different `⟨·,·⟩`, and a theorem about one says **nothing** about the other.
//! The composition in [`super::decl`] multiplies a theorem from each, so they
//! have to come from one signature or the multiplication is a category error
//! that no type checks.
//!
//! The order is forced, and it is the one [`super::Chain::over`]'s header
//! gives:
//!
//! 1. build the [`Tower`] — it owns the [`crate::funspace::in_universe::Space`],
//!    the [`Sums`] over that `Space`'s power set, and `ω` over the same pairing;
//! 2. build the [`Wtype`] over a **clone** of `tower.sums`, and the [`Bound`]
//!    over that `Wtype` and the tower's own `U(·)`;
//! 3. [`super::Chain::over`] and [`crate::inductive::Machine::over`] on the
//!    same two, each cloning rather than minting.
//!
//! [`SumClosure`] comes last because it needs the tower's four `∀c` closure
//! theorems, which [`super::Chain`] does not keep (it keeps only the five the
//! stages need). It is built once here rather than per declaration.
//!
//! # What is checked
//!
//! [`super::Chain::over`]'s five symbol comparisons, plus
//! [`IndChain::is_one_signature`], which additionally compares the `Machine`'s
//! W-type and pairing against the `Chain`'s. They are *necessary and not
//! sufficient* — they compare symbols, not statements — and the sufficient
//! check stays where it belongs: [`super::decl::DeclUniverse::over`] pins the
//! conclusion of the theorem it finally returns.

use kernel::Env;

use crate::bound::Bound;
use crate::inductive::{DeclSpec, Inductive, Machine};
use crate::isum::SumClosure;
use crate::sums::Sums;
use crate::tower::Tower;
use crate::wtype::Wtype;

use super::chain::Chain;

/// The translation apparatus and the cumulative hierarchy, over one signature.
pub struct IndChain {
    /// The universe tower: `ω`, `U(·)`, `U₁`, and the `∀c` closure theorems.
    pub tower: Tower,
    /// The cumulative hierarchy over the tower's signature.
    pub chain: Chain,
    /// The inductive translation apparatus over the same signature.
    pub mach: Machine,
    /// `U(c)`'s closure under `+`, and `∅ ∈ U(c)`, `1 ∈ U(c)` — derived once,
    /// used by [`super::tags`].
    pub clo: SumClosure,
}

impl IndChain {
    /// Build every symbol and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<IndChain> {
        let tower = Tower::new(env)?;
        let sums: Sums = tower.sums.clone();
        let wt = Wtype::over(env, sums)?;
        let bound = Bound::over(env, &wt, tower.space.lu, tower.space.lu_ax.clone())?;
        IndChain::over(env, tower, &wt, &bound)
    }

    /// The same over a caller-supplied [`Tower`], [`Wtype`] and [`Bound`], so
    /// that every conclusion is about the caller's own symbols.
    ///
    /// `None` unless the three came from one signature, as far as
    /// [`Chain::over`]'s comparisons and [`IndChain::is_one_signature`] can
    /// tell.
    pub fn over(env: &mut Env, tower: Tower, wt: &Wtype, bound: &Bound) -> Option<IndChain> {
        let chain = Chain::over(env, &tower, wt, bound)?;
        let mach = Machine::over(env, wt.clone(), bound.clone())?;
        let clo = SumClosure::new(
            env,
            &mach.wt.sums,
            tower.space.lu,
            &tower.empty_in,
            &tower.pairing,
            &tower.product,
            &tower.bin_union,
        )?;
        let out = IndChain { tower, chain, mach, clo };
        out.is_one_signature().then_some(out)
    }

    /// Whether the `Machine` and the `Chain` really are over one signature.
    ///
    /// Four symbols: the pairing (hence `⟨·,·⟩`, `sup` and every tuple), the
    /// W-type, `U(·)` and `+`. A `Machine` built over a second `Wtype` would
    /// answer every question with a true theorem about a `W` the chain's
    /// `w_in_universe_bnd` does not speak of.
    pub fn is_one_signature(&self) -> bool {
        self.mach.wt.sums.ap.sets.up == self.chain.wt.sums.ap.sets.up
            && self.mach.wt.w == self.chain.wt.w
            && self.mach.bnd.lu == self.chain.lu()
            && self.clo.lu == self.chain.lu()
            && self.clo.is_over(&self.mach.wt.sums)
            && self.mach.wt.sums.sum == self.chain.wt.sums.sum
    }

    /// Translate a declaration over this apparatus.
    pub fn build(&mut self, env: &mut Env, spec: &DeclSpec) -> Option<Inductive> {
        Inductive::build(env, &mut self.mach, spec)
    }
}
