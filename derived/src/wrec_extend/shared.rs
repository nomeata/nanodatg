//! Small movers, in implication form, shared by the constructions in
//! [`crate::wrec_extend`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** Each
//! one only reads its premises apart, so a bug here can cause a rejection but
//! never a wrong theorem.
//!
//! Everything in this module is derived under the ambient hypothesis bundle
//! [`super::hypothesis`], and there is no deduction theorem, so generalisation
//! ([`gen_under`]), instantiation ([`hyp_inst`]), Leibniz ([`hyp_leibniz`]) and
//! conjunction-splitting ([`hyp_split`]) all have to exist in the `H → …` form.
//! [`gen_under`] alone appears eight times.

use kernel::{Formula, FreeVar, Term, Thm};
use crate::{a1i, and_intro, and_left, and_right, hyp_mp, iff_mp, iff_mpr, imp_mono_r, syl};

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
pub(super) fn gen_under(v: FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])`.
pub(super) fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ φ ↔ ψ` and `⊢ ψ ↔ χ` infer `⊢ φ ↔ χ`.
pub(super) fn iff_trans(ab: &Thm, bc: &Thm) -> Option<Thm> {
    Some(and_intro(
        &syl(&iff_mp(ab)?, &iff_mp(bc)?)?,
        &syl(&iff_mpr(bc)?, &iff_mpr(ab)?)?,
    ))
}

/// From `⊢ ψ ↔ ψ′` infer `⊢ (φ ∨ ψ) ↔ (φ ∨ ψ′)`. A disjunction is an
/// implication out of a negation, so this is monotonicity in the consequent,
/// twice.
pub(super) fn or_right_cong(iff: &Thm, l: &Formula) -> Option<Thm> {
    let n = Formula::not(l.clone());
    Some(and_intro(
        &imp_mono_r(&iff_mp(iff)?, n.clone())?,
        &imp_mono_r(&iff_mpr(iff)?, n)?,
    ))
}

/// Split `φ ∧ ψ` into its conjuncts.
pub(super) fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, _) = f.as_imp()?;
    let (phi, npsi) = inner.as_imp()?;
    let (psi, _) = npsi.as_imp()?;
    Some((phi, psi))
}

/// From `⊢ H → (φ ∧ ψ)` infer the two halves.
pub(super) fn hyp_split(h: &Thm) -> Option<(Thm, Thm)> {
    let (_, conj) = h.concl().as_imp()?;
    let (phi, psi) = split_and(&conj)?;
    Some((
        syl(h, &and_left(phi.clone(), psi.clone()))?,
        syl(h, &and_right(phi, psi))?,
    ))
}
