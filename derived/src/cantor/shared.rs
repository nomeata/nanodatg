//! Internal readers and combinators shared by the constructions in
//! [`crate::cantor`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`split_and`], [`open_forall`] and [`open_exists`] take formulas apart —
//! `φ ∧ ψ` is `¬(φ → ¬ψ)` and `∃v. φ` is `¬∀v. ¬φ`, so reading either back
//! needs an explicit reader. The rest are the `H → …` forms of contraction,
//! existential discharge and instantiation, which have to exist separately
//! because every step of the diagonal argument runs under the ambient
//! hypothesis `DOM ∧ (SV ∧ ONTO)` and there is no deduction theorem.
//!
//! Reading a formula apart produces no `Thm`, so a bug in one of these can only
//! cause a rejection, never a wrong theorem.

use kernel::{Formula, FreeVar, Term, Thm};
use crate::{com12, exists_elim_imp, syl, uncurry};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub(super) fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// Instantiate the body of `∀v. φ` at `t`, as a *formula* operation.
pub(super) fn open_forall(phi: &Formula, t: &Term) -> Option<Formula> {
    let (_, body) = Thm::ax_inst(phi.clone(), t.clone())?.concl().as_imp()?;
    Some(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (body, fls2) = open_forall(&all_not, t)?.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub(super) fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    Thm::mp(&Thm::mp(&s, t)?, &crate::imp_refl(h))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging `v`.
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — instantiation in implication form, for a quantified
/// formula that is only available under a hypothesis.
pub(super) fn inst_all_imp(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = Thm::ax_inst(phi.clone(), ts.first()?.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}
