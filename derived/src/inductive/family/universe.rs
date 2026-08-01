//! **`⊢ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ U₁)`** — the indexed carrier is small, at one
//! `C₂` step over the unchanged non-indexed chain.
//!
//! # The claim, and it holds
//!
//! `INDEXED-DESIGN.md` §8 (D4) predicted "`DeclUniverse`'s `wty_in_u1` plus one
//! `C₂`, `∀`-closed over `x⃗` with **no new antecedent** — the list stays
//! exactly `A ∈ U₁`". Checked, and that is what it is:
//!
//! ```text
//! ind(p⃗,x⃗) ⊆ W        [IndexedCarrier::subset_w]   — a Separation, for every x⃗
//! W ∈ U₁              [DeclUniverse::wty_in_u1]    — carries whatever H the tags carried
//! ───────────────────────────────────────────── C₂  [Rung::sub]
//! ind(p⃗,x⃗) ∈ U₁
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
//! * **Nothing about `Idx(p⃗)` is needed.** `𝒫(Idx(p⃗)) ∈ U₁` would follow from
//!   `ιₖ ∈ U₁` by the tower's product and power closures, and it is never
//!   asked: the size argument runs on the skeleton, and `goodrec` appears only
//!   inside a Separation condition.
//! * **The antecedent list is unchanged.** Whatever `H` the caller's
//!   `⊢ [H →] A ∈ U₁` carried is what comes out; this file adds none and
//!   removes none.
//!
//! # Interface
//!
//! ```text
//! ⊢ [H →] ind(p⃗,x⃗) ∈ U₁          at the working variables   [IndexedUniverse::at_vars]
//! ⊢ ∀p⃗ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ U₁)                            [IndexedUniverse::ty_in_u1]
//! ```

use kernel::{Env, Formula, Term, Thm};

use crate::cumul::{DeclUniverse, IndChain};
use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::{gen_all, inst_all};

use super::carrier::IndexedCarrier;

/// The indexed carrier, placed in `U₁`.
pub struct IndexedUniverse {
    /// `⊢ [H →] ind(p⃗,x⃗) ∈ U₁`, at the declaration's parameters and
    /// [`IndexedCarrier::xvs`].
    pub at_vars: Thm,
    /// `⊢ ∀p⃗ ∀x⃗. ([H →] ind(p⃗,x⃗) ∈ U₁)` — the statement a checker consumes.
    pub ty_in_u1: Thm,
}

impl IndexedUniverse {
    /// One `C₂` over [`DeclUniverse::wty_in_u1`].
    ///
    /// `du` must be [`DeclUniverse::over`] at the same `ic`, `mach` and `ind`,
    /// with the same optional `hyp`; `ixc` must be
    /// [`IndexedCarrier::build`] over that same `ind`. Both the conclusion and
    /// the **empty hypothesis set** of the caller's theorem are checked, on the
    /// way in and on the way out.
    pub fn over(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        ixc: &IndexedCarrier,
        du: &DeclUniverse,
        hyp: Option<&Formula>,
    ) -> Option<IndexedUniverse> {
        if !ic.is_over(mach) || !ind.is_over(mach) || !du.wty_in_u1.hyps().is_empty() {
            return None
        }
        let u1 = &ic.chain.u1;
        let wrap = |c: Formula| match hyp {
            Some(h) => Formula::imp(h.clone(), c),
            None => c,
        };
        if *du.wty_in_u1.concl() != wrap(Formula::mem(ind.wty.clone(), u1.set.clone())) {
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

        // `C₂`: a subset of a member of `U₁` is a member of `U₁`.
        let c2 = inst_all(&u1.sub, std::slice::from_ref(&ind.wty))?;
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
        if *at_vars.concl() != wrap(Formula::mem(carrier, u1.set.clone()))
            || !at_vars.hyps().is_empty()
        {
            return None
        }

        let mut quant = ind.params.clone();
        quant.extend(ixc.xvs.iter().copied());
        Some(IndexedUniverse { ty_in_u1: gen_all(&quant, &at_vars), at_vars })
    }
}
