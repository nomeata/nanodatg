//! Private readers and `H → …` combinators for [`crate::csb`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Deliberately private copies rather than imports from a neighbouring module,
//! on the reasoning `crate::universe::shared` gives: reading a formula apart is
//! untrusted and safe — no `Thm` is produced by any of it, so a helper here can
//! fail to build a theorem but never build a wrong one.

use kernel::{Formula, FreeVar, Term, Thm};

use crate::{com12, contrapos_imp, exists_elim_imp, forall_mono, imp_refl, syl, uncurry};

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub(super) fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    Thm::mp(&Thm::mp(&s, t)?, &imp_refl(h))
}

/// Generalisation under a hypothesis: from `⊢ H → φ` infer `⊢ H → ∀v. φ`.
///
/// `v` must not occur free in `H`; `Thm::ax_dist` is what enforces it.
pub(super) fn hyp_gen(v: FreeVar, t: &Thm) -> Option<Thm> {
    let (h, phi) = t.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h, phi)?, &Thm::gen(v, t))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
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

/// `⊢ (∀x.(φ → ψ)) → (∀x. φ → ∀x. ψ)` — [`crate::forall_mono`] in *implication*
/// form, which is what a step under a hypothesis needs.
///
/// The body is [`crate::forall_mono`]'s, stopped one line before it discharges
/// its own antecedent.
pub(super) fn forall_mono_imp(x: FreeVar, phi: &Formula, psi: &Formula) -> Option<Thm> {
    let a = Formula::forall(x, Formula::imp(phi.clone(), psi.clone()));
    let a_to_body = Thm::ax_inst(a.clone(), Term::var(x))?;
    let b = Formula::forall(x, phi.clone());
    let b_to_phi = Thm::ax_inst(b.clone(), Term::var(x))?;

    let a_to_bpsi = com12(&syl(&b_to_phi, &com12(&a_to_body)?)?)?;
    let dist1 = Thm::ax_dist(x, a, Formula::imp(b.clone(), psi.clone()))?;
    let a_to_all = Thm::mp(&dist1, &Thm::gen(x, &a_to_bpsi))?;
    syl(&a_to_all, &Thm::ax_dist(x, b, psi.clone())?)
}

/// `⊢ (∀x.(φ → ψ)) → (∃x. φ → ∃x. ψ)` — [`crate::exists_mono`] in *implication*
/// form.
pub(super) fn exists_mono_imp(x: FreeVar, phi: &Formula, psi: &Formula) -> Option<Thm> {
    let contra_all = forall_mono(x, &Thm::gen(x, &contrapos_imp(phi.clone(), psi.clone())))?;
    let (np, nq) = (Formula::not(psi.clone()), Formula::not(phi.clone()));
    let chain = syl(&contra_all, &forall_mono_imp(x, &np, &nq)?)?;
    syl(&chain, &contrapos_imp(Formula::forall(x, np), Formula::forall(x, nq)))
}

/// From `⊢ H → (φ → ψ)` with `x` not free in `H`, infer
/// `⊢ H → (∃x. φ → ∃x. ψ)`.
pub(super) fn hyp_exists_mono(x: FreeVar, t: &Thm) -> Option<Thm> {
    let (_, imp) = t.concl().as_imp()?;
    let (phi, psi) = imp.as_imp()?;
    syl(&hyp_gen(x, t)?, &exists_mono_imp(x, &phi, &psi)?)
}

/// From `⊢ H → (φ → ψ)` infer `⊢ H → (¬ψ → ¬φ)`.
pub(super) fn hyp_contrapos(t: &Thm) -> Option<Thm> {
    let (_, imp) = t.concl().as_imp()?;
    let (phi, psi) = imp.as_imp()?;
    syl(t, &contrapos_imp(phi, psi))
}

/// From `⊢ H → (l ∨ r)` and `⊢ H → ¬r` infer `⊢ H → l`.
///
/// `l ∨ r` is `¬l → r`, so refuting `r` makes `¬l` absurd.
pub(super) fn or_left_of_not_right(h_disj: &Thm, h_notr: &Thm) -> Option<Thm> {
    let (_, disj) = h_disj.concl().as_imp()?;
    let (nl, _) = disj.as_imp()?;
    let (l, _) = nl.as_imp()?;
    // `¬l → r` chained with `r → ⊥` is `¬l → ⊥`, i.e. `¬¬l`.
    let nn = crate::separation::hyp_syl(h_disj, h_notr)?;
    syl(&nn, &crate::notnot_elim(l))
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (_, body) = Thm::ax_inst(all_not, t.clone())?.concl().as_imp()?;
    let (inner, fls2) = body.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(inner)
}
