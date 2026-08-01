//! Equational plumbing under a hypothesis, and the private formula readers.
//!
//! **Nothing here is a theorem about sets and nothing is derived.** Every
//! equation in the recursion argument is derived *under* an ambient hypothesis,
//! and there is no deduction theorem, so instantiation, symmetry, transitivity,
//! congruence and existential elimination all have to exist in the `H → …`
//! form. These are the private copies: they read their premises apart and can
//! only fail to build a theorem, never build a wrong one.
//!
//! [`hyp_eq_symm`], [`hyp_eq_trans`], [`hyp_congr`] and [`hyp_exists_elim`] are
//! re-exported `pub(crate)` from [`crate::wrec`], because eight other modules in
//! this crate import them; the rest are private to the sibling files here.
//!
//! [`split_and`], [`as_iff`] and [`hyp_split`] take formulas apart —
//! `φ ∧ ψ` is `¬(φ → ¬ψ)` and `φ ↔ ψ` is a conjunction of implications, so
//! reading either back needs an explicit reader. Taking a formula apart
//! produces no `Thm`, so a bug in one can only cause a rejection.

use kernel::{Env, Formula, Term, Thm};
use crate::{a1i, and_left, and_right, eq_symm_imp, hyp_mp, syl, uncurry};

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → x = y` infer `⊢ H → y = x`.
pub(crate) fn hyp_eq_symm(env: &mut Env, h: &Thm) -> Option<Thm> {
    let (_, eq) = h.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    syl(h, &eq_symm_imp(env, x, y))
}

/// From `⊢ H → x = y` and `⊢ H → y = z` infer `⊢ H → x = z`.
pub(crate) fn hyp_eq_trans(env: &mut Env, xy: &Thm, yz: &Thm) -> Option<Thm> {
    let (k, e1) = xy.concl().as_imp()?;
    let (_, e2) = yz.concl().as_imp()?;
    let (x, y) = e1.as_eq()?;
    let (y2, z) = e2.as_eq()?;
    if y != y2 {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(y, z, hole, Formula::eq(x, Term::var(hole)));
    hyp_mp(&hyp_mp(&a1i(&leib, k), yz)?, xy)
}

/// From `⊢ H → x = y` infer `⊢ H → ctx(x) = ctx(y)`, for a term context given
/// as a closure. One Leibniz with a fresh hole, discharged against reflexivity.
pub(crate) fn hyp_congr<F: Fn(Term) -> Term>(env: &mut Env, h_eq: &Thm, ctx: F) -> Option<Thm> {
    let (k, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let phi = Formula::eq(lhs.clone(), ctx(Term::var(hole)));
    let leib = Thm::eq_leibniz(x, y, hole, phi);
    hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), h_eq)?, &a1i(&Thm::eq_refl(lhs), k))
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts. A private reader:
/// taking a formula apart produces no `Thm`, so a bug here can only cause a
/// rejection.
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

/// From `⊢ (H ∧ φ) → ψ` and `⊢ H → ∃v. φ`, with `v` free in neither `H` nor
/// `ψ`, infer `⊢ H → ψ` — existential elimination under a hypothesis.
///
/// The one move the union argument is made of: "some attempt contains this
/// pair" has to be used twice over, and there is no deduction theorem to
/// discharge the witness with.
pub(crate) fn hyp_exists_elim(v: kernel::FreeVar, h_body: &Thm, h_ex: &Thm) -> Option<Thm> {
    let (hphi, psi) = h_body.concl().as_imp()?;
    let (h, _) = split_and(&hphi)?;
    let per = crate::com12(&uncurry(h_body)?)?; // φ → (H → ψ)
    let target = Formula::imp(h, psi);
    let elim = crate::exists_elim_imp(v, &Thm::gen(v, &per), &target)?;
    hyp_mp(&crate::com12(&elim)?, h_ex)
}
