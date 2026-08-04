//! **The chain-side apparatus the composition needs**, over a signature the
//! caller's [`crate::inductive::Machine`] already lives on.
//!
//! # Interface
//!
//! ```text
//! IndChain::over(env, tower, wt, bound) -> Option<IndChain>
//! IndChain::is_over(&self, mach)        -> bool
//! ```
//!
//! and the three fields [`IndChain::chain`], [`IndChain::clo`] and
//! [`IndChain::bnd_sum`]. Nothing here
//! is new mathematics: it is the assembly, and it exists for the reason
//! [`super::ambient`] exists — getting it wrong is *silent*.
//!
//! # Why the `Machine` is **not** a field
//!
//! It was, for one revision, and that was wrong. A client that already
//! translates declarations — `checker/src/tg.rs`, which holds one
//! `Rc<RefCell<Machine>>` per thread — would then have a *second* `Machine`
//! built over the same [`Wtype`] and [`Bound`], and a second `Machine` mints a
//! second [`crate::sums::Cases`] and a second [`crate::proj::Proj`], hence a
//! different [`crate::inductive::MachineId`]. Every
//! [`Inductive::is_over`](crate::inductive::Inductive::is_over) guard
//! downstream would then refuse the client's own declarations. So the `Machine`
//! is passed in at each call, and [`IndChain::is_over`] checks it is one
//! signature with the chain.
//!
//! # Why an assembly step is needed at all
//!
//! [`crate::inductive::Machine::new`] mints its own [`Wtype`] and [`Bound`],
//! and so does [`super::Chain::new`] (by way of its own [`Tower`]). Two of
//! either in one `Env` are two different `W`, two different `U(·)` and two
//! different `⟨·,·⟩`, and a theorem about one says **nothing** about the other.
//! [`super::decl`] multiplies a theorem from each, so they have to come from
//! one signature or the multiplication is a category error that no type checks.
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
//! stages need). It is built once here rather than per declaration, and
//! [`super::sum_bnd::bnd_sum`] is here for the stronger version of the same
//! reason: it does not merely cost work to repeat, it **mints symbols**.
//!
//! # What is checked
//!
//! [`super::Chain::over`]'s five symbol comparisons, plus [`IndChain::is_over`]:
//! the pairing, the W-type, `U(·)` and `+`. They are *necessary and not
//! sufficient* — they compare symbols, not statements — and the sufficient
//! check stays where it belongs, on the conclusion
//! [`super::decl::DeclUniverse::over`] finally returns.

use kernel::{Env, Thm};

use crate::bound::Bound;
use crate::inductive::Machine;
use crate::isum::SumClosure;
use crate::sums::Sums;
use crate::tower::Tower;
use crate::wtype::Wtype;

use super::chain::Chain;

/// The cumulative hierarchy and the sum-closure apparatus, over one signature.
pub struct IndChain {
    /// The cumulative hierarchy: the stages, `Fin⁺`, and `W ∈ U(d)`.
    pub chain: Chain,
    /// `U(c)`'s closure under `+`, and `∅ ∈ U(c)`, `1 ∈ U(c)` — derived once,
    /// used by [`super::tags`].
    pub clo: SumClosure,
    /// `⊢ ∀a ∀b. ((bnd(a) ∧ bnd(b)) → bnd(a + b))` — the tower-side twin of
    /// [`SumClosure::sum`], derived once **because it mints symbols**.
    ///
    /// [`super::bnd_tagged_copy`], which it goes through, introduces a
    /// `define_abbrev` body and its lambda graph — one Replacement instance. A
    /// client that derived it per declaration would leave a redundant pair in
    /// the signature for every declaration after the first, which is the same
    /// hazard [`super::decl`]'s header records for `image_symbol_n`.
    pub bnd_sum: Thm,
}

impl IndChain {
    /// Build every symbol and derive every theorem, from the axioms up, and
    /// return the [`Machine`] over the same signature alongside.
    ///
    /// For a client that does *not* already hold a translation apparatus. One
    /// that does — see the module header — builds its own and calls
    /// [`IndChain::over`].
    pub fn new(env: &mut Env) -> Option<(IndChain, Machine)> {
        let tower = Tower::new(env)?;
        let sums: Sums = tower.sums.clone();
        let wt = Wtype::over(env, sums)?;
        let bound = Bound::over(env, &wt, tower.space.lu, tower.space.lu_ax.clone())?;
        let ic = IndChain::over(env, &tower, &wt, &bound)?;
        let mach = Machine::over(env, wt, bound)?;
        ic.is_over(&mach).then_some((ic, mach))
    }

    /// The chain and the closure apparatus over a caller-supplied [`Tower`],
    /// [`Wtype`] and [`Bound`], so that every conclusion is about the caller's
    /// own symbols.
    ///
    /// `None` unless the three came from one signature, as far as
    /// [`Chain::over`]'s comparisons can tell.
    pub fn over(env: &mut Env, tower: &Tower, wt: &Wtype, bound: &Bound) -> Option<IndChain> {
        let chain = Chain::over(env, tower, wt, bound)?;
        let clo = SumClosure::new(
            env,
            &chain.wt.sums,
            tower.space.lu,
            &tower.empty_in,
            &tower.pairing,
            &tower.product,
            &tower.bin_union,
        )?;
        let sums = chain.wt.sums.clone();
        let bnd_sum = super::sum_bnd::bnd_sum(env, &chain.r, &chain.st, &sums)?;
        let out = IndChain { chain, clo, bnd_sum };
        (out.clo.lu == out.chain.lu() && out.clo.is_over(&out.chain.wt.sums)).then_some(out)
    }

    /// Whether `mach` really is over this chain's signature.
    ///
    /// Four symbols: the pairing (hence `⟨·,·⟩`, `sup` and every tuple), the
    /// W-type, `U(·)` and `+`. A `Machine` built over a second [`Wtype`] would
    /// answer every question with a true theorem about a `W` this chain's
    /// `w_in_universe_bnd` does not speak of.
    pub fn is_over(&self, mach: &Machine) -> bool {
        mach.wt.sums.ap.sets.up == self.chain.wt.sums.ap.sets.up
            && mach.wt.w == self.chain.wt.w
            && mach.bnd.lu == self.chain.lu()
            && mach.wt.sums.sum == self.chain.wt.sums.sum
            && self.clo.is_over(&mach.wt.sums)
    }
}
