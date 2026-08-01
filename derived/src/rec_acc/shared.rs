//! The private plumbing more than one file in [`crate::rec_acc`] needs.
//!
//! **Nothing here is a theorem about sets and nothing is derived.** These are
//! the `H → …` forms of instantiation and conjunction elimination, plus the two
//! formula readers — `φ ∧ ψ` is `¬(φ → ¬ψ)` and `φ ↔ ψ` is a conjunction of
//! implications, so reading either back needs an explicit reader. Every one can
//! only fail to build a theorem, never build a wrong one.
//!
//! They are private copies of [`crate::wrec`]'s identically-named helpers rather
//! than shared exports, for the same reason `crate::acc::shared` copies
//! `hyp_inst_mp`: those are `pub(super)` inside `wrec`, and promoting them would
//! enlarge that module's interface for no gain here. The four that `wrec` does
//! re-export `pub(crate)` — `hyp_eq_symm`, `hyp_eq_trans`, `hyp_congr`,
//! `hyp_exists_elim` — are imported, not copied.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{and_left, and_right, syl, uncurry};

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

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

/// Read `φ ↔ ψ` apart, which is `(φ → ψ) ∧ (ψ → φ)`.
pub(super) fn as_iff(f: &Formula) -> Option<(Formula, Formula)> {
    split_and(f)?.0.as_imp()
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

/// From `⊢ H → ∀v. (φ → ψ)` infer `⊢ H → (∃v. φ → ∃v. ψ)`.
///
/// `∃v. φ` is `¬∀v. ¬φ`, so this is the contrapositive of `∀v. ¬ψ → ∀v. ¬φ`,
/// proved pointwise under the extra hypothesis `∀v. ¬ψ` and then generalised.
pub(super) fn hyp_exists_mono(v: FreeVar, h_all: &Thm) -> Option<Thm> {
    let (h, all) = h_all.concl().as_imp()?;
    let tv = Term::var(v);
    let (_, body) = Thm::ax_inst(all.clone(), tv.clone())?.concl().as_imp()?;
    let (phi, psi) = body.as_imp()?;

    let all_not_psi = Formula::forall(v, Formula::not(psi));
    let all_not_phi = Formula::forall(v, Formula::not(phi.clone()));
    let j = Formula::and(h.clone(), all_not_psi.clone());

    let j_h = and_left(h.clone(), all_not_psi.clone());
    let j_all = and_right(h, all_not_psi.clone());
    let j_imp = syl(&syl(&j_h, h_all)?, &Thm::ax_inst(all, tv.clone())?)?;
    let j_npsi = syl(&j_all, &Thm::ax_inst(all_not_psi.clone(), tv)?)?;
    let j_nphi = crate::funcs::hyp_syl(&j_imp, &j_npsi)?;

    let j_gen = Thm::mp(&Thm::ax_dist(v, j, Formula::not(phi))?, &Thm::gen(v, &j_nphi))?;
    syl(
        &uncurry(&j_gen)?,
        &crate::contrapos_imp(all_not_psi, all_not_phi),
    )
}

/// From `⊢ φ ↔ ψ` and `⊢ ψ ↔ χ` infer `⊢ φ ↔ χ`.
pub(super) fn iff_trans(ab: &Thm, bc: &Thm) -> Option<Thm> {
    Some(crate::and_intro(
        &syl(&crate::iff_mp(ab)?, &crate::iff_mp(bc)?)?,
        &syl(&crate::iff_mpr(bc)?, &crate::iff_mpr(ab)?)?,
    ))
}

/// From `⊢ ψ ↔ ψ′` infer `⊢ (φ ∨ ψ) ↔ (φ ∨ ψ′)`. A disjunction is an
/// implication out of a negation, so this is monotonicity in the consequent,
/// twice.
pub(super) fn or_right_cong(iff: &Thm, l: &Formula) -> Option<Thm> {
    let n = Formula::not(l.clone());
    Some(crate::and_intro(
        &crate::imp_mono_r(&crate::iff_mp(iff)?, n.clone())?,
        &crate::imp_mono_r(&crate::iff_mpr(iff)?, n)?,
    ))
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, when `v` is not free in `H`.
pub(super) fn gen_under(v: FreeVar, h: &Thm) -> Option<Thm> {
    let (hyp, phi) = h.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, hyp, phi)?, &Thm::gen(v, h))
}

/// From `⊢ H → x = y` infer `⊢ H → (φ(x) → φ(y))`, for a formula context given
/// as a closure over a hole variable.
pub(super) fn hyp_leibniz<F: Fn(Term) -> Formula>(
    env: &mut Env,
    h_eq: &Thm,
    ctx: F,
) -> Option<Thm> {
    let (k, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    crate::hyp_mp(&crate::a1i(&leib, k), h_eq)
}
