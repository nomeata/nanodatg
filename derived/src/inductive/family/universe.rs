//! **`⊢ ∀p⃗ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ Uₙ)`** — the indexed carrier is small, at one
//! `C₂` step over the unchanged non-indexed chain, at **any rung of the
//! tower**.
//!
//! # The claim, and it holds
//!
//! `INDEXED-DESIGN.md` §8 (D4) predicted "`DeclUniverse`'s `wty_in_u1` plus one
//! `C₂`, `∀`-closed over `x⃗` with **no new antecedent** — the list stays
//! exactly `A ∈ U₁`". Checked, and that is what it is:
//!
//! ```text
//! ind(p⃗,x⃗) ⊆ W        [IndexedCarrier::subset_w]   — a Separation, for every x⃗
//! W ∈ Uₙ              [DeclUniverse::wty_in_u1]    — carries whatever H the tags carried
//! ───────────────────────────────────────────── C₂  [Rung::sub]
//! ind(p⃗,x⃗) ∈ Uₙ
//! ```
//!
//! Three things are worth being explicit about, because each could have gone
//! the other way:
//!
//! * **No index-typing antecedent.** `ind(p⃗,x⃗) ⊆ W` holds for *junk* index
//!   vectors too — a Separation is a subset no matter what is asked of it — so
//!   the `∀x⃗` closure is free. Contrast [`super::carrier`]'s membership rule,
//!   which does need `tup(e⃗ᵢ) ∈ Idx(p⃗)`: putting something *into* the carrier
//!   is where the index typing is spent.
//! * **Nothing about `Idx(p⃗)` is needed.** `𝒫(Idx(p⃗)) ∈ Uₙ` would follow from
//!   `ιₖ ∈ Uₙ` by the tower's product and power closures, and it is never
//!   asked: the size argument runs on the skeleton, and `goodrec` appears only
//!   inside a Separation condition.
//! * **The antecedent list is unchanged.** Whatever `H` the caller's
//!   `⊢ [H →] A ∈ Uₙ` carried is what comes out; this file adds none and
//!   removes none.
//!
//! # Why the rung is a parameter
//!
//! `⟦Sort ℓ⟧ = U_ℓ`, so the rung a declaration is placed at is read off its
//! **resultant sort** and is not a property of this construction.
//! `RBTree : Πα:Sort u+1. Color → N → Sort u+1` lands in `U₂` at the
//! instantiation `u := 1`, which is the second of the two pairs `042` schedules
//! (`DEFAULT_LEVELS = [0,1]`), and the whole of the rest of the size pipeline —
//! [`crate::cumul::summand_at`], [`crate::cumul::tags_at`],
//! [`crate::cumul::arg_obligations_at`], [`crate::cumul::nullary_summands_at`]
//! and [`DeclUniverse::over_at`] — is already stated at an arbitrary [`Rung`].
//!
//! Nothing about the derivation changes with `n`: the one step is `C₂`
//! ([`Rung::sub`]), which every rung has, and the subset half
//! ([`IndexedCarrier::subset_w`]) does not mention a universe at all. So
//! [`IndexedUniverse::over_at`] is a rung parameter and two guards, and
//! [`IndexedUniverse::over`] is `over_at` at `ic.chain.u1`, i.e. `n = 1`, for
//! which an existing caller pays nothing.
//!
//! **Where the rung has to come from** is the same as for
//! [`DeclUniverse::over_at`], and is checked here rather than assumed:
//! `Uₙ` must be *this* chain's `U(·)` applied to the rung's own seed
//! ([`crate::tower::Tower::at`] on the tower [`crate::cumul::IndChain::over`]
//! was built over), and `du` must have been built at the same rung —
//! [`DeclUniverse::universe`] carries which one that was, so a `du` at `U₁`
//! handed in with a request for `U₂` is refused rather than composed into a
//! statement about the wrong universe.
//!
//! # Interface
//!
//! ```text
//! ⊢ [H →] ind(p⃗,x⃗) ∈ Uₙ          at the working variables   [IndexedUniverse::at_vars]
//! ⊢ ∀p⃗ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ Uₙ)                            [IndexedUniverse::ty_in_u1]
//! ```

use kernel::{Env, Formula, Term, Thm};

use crate::cumul::{DeclUniverse, IndChain};
use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::tower::Rung;
use crate::{all_unconditional, gen_all, inst_all};

use super::carrier::IndexedCarrier;

/// The indexed carrier, placed in `Uₙ`.
pub struct IndexedUniverse {
    /// The term `Uₙ` both memberships below are in — [`Rung::set`] of the rung
    /// [`IndexedUniverse::over_at`] was called at, and `U₁` for
    /// [`IndexedUniverse::over`]. Carried so that a caller checks the rung it
    /// got rather than the one it meant to ask for.
    pub universe: Term,
    /// `⊢ [H →] ind(p⃗,x⃗) ∈ Uₙ`, at the declaration's parameters and
    /// [`IndexedCarrier::xvs`].
    pub at_vars: Thm,
    /// `⊢ ∀p⃗ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ Uₙ)` — the statement a checker consumes.
    pub ty_in_u1: Thm,
}

impl IndexedUniverse {
    /// One `C₂` over [`DeclUniverse::wty_in_u1`], at `U₁`.
    ///
    /// [`IndexedUniverse::over_at`] at `ic.chain.u1`, and nothing else.
    pub fn over(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        ixc: &IndexedCarrier,
        du: &DeclUniverse,
        hyp: Option<&Formula>,
    ) -> Option<IndexedUniverse> {
        IndexedUniverse::over_at(env, ic, mach, ind, ixc, du, hyp, &ic.chain.u1)
    }

    /// One `C₂` over [`DeclUniverse::wty_in_u1`], at any rung of the tower.
    ///
    /// `du` must be [`DeclUniverse::over_at`] at the same `ic`, `mach`, `ind`
    /// **and `rung`**, with the same optional `hyp`; `ixc` must be
    /// [`IndexedCarrier::build`] over that same `ind`. Both the conclusion and
    /// the **empty hypothesis set** of the caller's theorem are checked, on the
    /// way in and on the way out.
    ///
    /// `rung` must be a rung of the same tower the chain was built over —
    /// `Uₙ` is compared against this chain's `U(·)` at the rung's own seed —
    /// and [`Rung::sub`], the one theorem of the rung this file spends, is
    /// checked to rest on nothing. See the module header.
    #[allow(clippy::too_many_arguments)]
    pub fn over_at(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        ixc: &IndexedCarrier,
        du: &DeclUniverse,
        hyp: Option<&Formula>,
        rung: &Rung,
    ) -> Option<IndexedUniverse> {
        if !ic.is_over(mach)
            || !ind.is_over(mach)
            || !all_unconditional(&[&du.wty_in_u1, &rung.sub])
        {
            return None
        }
        let un = rung;
        // The rung is this chain's own, and `du` was built at *it* rather than
        // at whatever rung its caller defaulted to.
        if un.set != Term::apply(ic.chain.lu(), vec![un.seed.clone()]) || du.universe != un.set {
            return None
        }
        let wrap = |c: Formula| match hyp {
            Some(h) => Formula::imp(h.clone(), c),
            None => c,
        };
        if *du.wty_in_u1.concl() != wrap(Formula::mem(ind.wty.clone(), un.set.clone())) {
            return None
        }

        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let xs: Vec<Term> = ixc.xvs.iter().map(|v| Term::var(*v)).collect();
        let carrier = ixc.ty_of(&ps, &xs)?;

        // `ind(p⃗,x⃗) ⊆ W`, from the Separation.
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let mut sa = ps.clone();
        sa.extend(xs.iter().cloned());
        sa.push(tz.clone());
        let sub = Thm::gen(zv, &inst_all(&ixc.subset_w, &sa)?);
        if *sub.concl() != kernel::thm::subset(env, carrier.clone(), ind.wty.clone()) {
            return None
        }

        // `C₂`: a subset of a member of `Uₙ` is a member of `Uₙ`.
        let c2 = inst_all(&un.sub, std::slice::from_ref(&ind.wty))?;
        let at_vars = match hyp {
            None => {
                let step = Thm::mp(&c2, &du.wty_in_u1)?;
                Thm::mp(&inst_all(&step, std::slice::from_ref(&carrier))?, &sub)?
            }
            Some(h) => {
                let step = crate::syl(&du.wty_in_u1, &c2)?;
                let inst = crate::syl(
                    &step,
                    &Thm::ax_inst(step.concl().as_imp()?.1, carrier.clone())?,
                )?;
                crate::hyp_mp(&inst, &crate::a1i(&sub, h.clone()))?
            }
        };
        if *at_vars.concl() != wrap(Formula::mem(carrier, un.set.clone()))
            || !at_vars.hyps().is_empty()
        {
            return None
        }

        let mut quant = ind.params.clone();
        quant.extend(ixc.xvs.iter().copied());
        Some(IndexedUniverse {
            universe: un.set.clone(),
            ty_in_u1: gen_all(&quant, &at_vars),
            at_vars,
        })
    }
}
