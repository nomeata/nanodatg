//! Propositional and quantifier combinators this module needs and the crate
//! does not already have.
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** The
//! bridge in [`super::bridge`] rewrites one side of a biconditional inside a
//! conjunction inside a disjunction inside an existential, all under an ambient
//! hypothesis, and the crate's toolkit consumes *proved* formulas rather than
//! hypothetical ones. These are the congruences and movers that gap needs:
//! symmetry and transitivity of `↔` in both the plain and the `H → …` form,
//! congruence of `∧` and `∨` under implication, instantiation, Leibniz,
//! existential discharge and generalisation.
//!
//! Each one reads its premises apart, so a bug here can cause a rejection but
//! never a wrong theorem.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::{
    a1i, and_intro, and_left, and_right, com12, contrapos, eq_symm_imp, exists_elim_imp, hyp_and,
    hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp, iff_mpr, imp_mono_r, syl, syl_imp,
    uncurry,
};

/// From `⊢ φ ↔ ψ` infer `⊢ ψ ↔ φ`.
pub(super) fn iff_symm(t: &Thm) -> Option<Thm> { Some(and_intro(&iff_mpr(t)?, &iff_mp(t)?)) }

/// From `⊢ φ ↔ ψ` and `⊢ ψ ↔ χ` infer `⊢ φ ↔ χ`.
pub(super) fn iff_trans(ab: &Thm, bc: &Thm) -> Option<Thm> {
    Some(and_intro(&syl(&iff_mp(ab)?, &iff_mp(bc)?)?, &syl(&iff_mpr(bc)?, &iff_mpr(ab)?)?))
}

/// From `⊢ H → (P ↔ A)` and `⊢ A ↔ B` infer `⊢ H → (P ↔ B)`.
pub(super) fn hyp_iff_trans(h_iff: &Thm, ab: &Thm) -> Option<Thm> {
    let h_pa = hyp_iff_mp(h_iff)?;
    let h_ap = hyp_iff_mpr(h_iff)?;
    let (_, p_to_a) = h_pa.concl().as_imp()?;
    let (p, a) = p_to_a.as_imp()?;
    let (a2, b) = iff_mp(ab)?.concl().as_imp()?;
    if a != a2 {
        return None
    }
    let h_pb = syl(&h_pa, &imp_mono_r(&iff_mp(ab)?, p.clone())?)?;
    let bridge = Thm::mp(&syl_imp(b, a, p), &iff_mpr(ab)?)?;
    let h_bp = syl(&h_ap, &bridge)?;
    hyp_and(&h_pb, &h_bp)
}

/// From `⊢ A → A'` and `⊢ B → B'` infer `⊢ (A ∧ B) → (A' ∧ B')`.
pub(super) fn and_cong_imp(l: &Thm, r: &Thm) -> Option<Thm> {
    let (a, _) = l.concl().as_imp()?;
    let (b, _) = r.concl().as_imp()?;
    let h_a = syl(&and_left(a.clone(), b.clone()), l)?;
    let h_b = syl(&and_right(a, b), r)?;
    hyp_and(&h_a, &h_b)
}

/// From `⊢ A → A'` and `⊢ B → B'` infer `⊢ (A ∨ B) → (A' ∨ B')`.
///
/// `A ∨ B` is `¬A → B`, so the left half runs backwards: to weaken the
/// disjunction one has to *strengthen* `¬A`, which is contraposition.
fn or_cong_imp(l: &Thm, r: &Thm) -> Option<Thm> {
    let (a, a2) = l.concl().as_imp()?;
    let (b, _) = r.concl().as_imp()?;
    let contra = contrapos(l)?; // ⊢ ¬A' → ¬A
    let na2 = Formula::not(a2);
    let step = Thm::mp(&syl_imp(na2.clone(), Formula::not(a), b), &contra)?;
    syl(&step, &imp_mono_r(r, na2)?)
}

/// From `⊢ A ↔ A'` and `⊢ B ↔ B'` infer `⊢ (A ∨ B) ↔ (A' ∨ B')`.
pub(super) fn or_cong(l: &Thm, r: &Thm) -> Option<Thm> {
    let fwd = or_cong_imp(&iff_mp(l)?, &iff_mp(r)?)?;
    let bwd = or_cong_imp(&iff_mpr(l)?, &iff_mpr(r)?)?;
    Some(and_intro(&fwd, &bwd))
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — [`crate::inst_all`] in implication form, for a
/// quantified formula only available under a hypothesis.
///
/// A private copy of the combinator [`crate::ext`] keeps privately, on the same
/// reasoning: reading formulas apart produces no `Thm`.
pub(super) fn inst_all_imp(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = Thm::ax_inst(phi.clone(), ts.first()?.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → a = b` infer `⊢ H → b = a`.
pub(super) fn hyp_eq_symm(env: &mut Env, h_eq: &Thm) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    syl(h_eq, &eq_symm_imp(env, a, b))
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])`.
pub(super) fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must occur free in neither `H` nor `φ`).
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    crate::empty::hyp_contract(&syl(h_ex, &elim)?)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for each `v` in turn (innermost first).
///
/// Each step is the distribution axiom, whose side condition — `v` not free in
/// `H` — is *checked* by [`Thm::ax_dist`] rather than assumed; a violation
/// returns `None`.
pub(super) fn hyp_gen_all(vs: &[FreeVar], t: &Thm) -> Option<Thm> {
    let mut acc = t.clone();
    for v in vs {
        let (h, body) = acc.concl().as_imp()?;
        acc = Thm::mp(&Thm::ax_dist(*v, h, body)?, &Thm::gen(*v, &acc))?;
    }
    Some(acc)
}
