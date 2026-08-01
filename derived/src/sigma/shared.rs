//! Internal helpers shared by the constructions in [`crate::sigma`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Every equation in these derivations is hypothetical — the hypothesis being
//! `q ∈ Σ(p⃗)`, which is what a `Σ`-elimination is always under — so the
//! equality toolkit in [`crate`], which consumes *proved* equations, does not
//! apply and each rewrite is wanted in implication form instead. Reading
//! formulas apart produces no `Thm`, so a helper here can fail to build a
//! theorem but never build a wrong one.

use kernel::{Env, Formula, Term, Thm};

use crate::{a1i, eq_symm_imp, hyp_mp, mpd_const, syl};

/// From `⊢ H → u = v` infer `⊢ H → ctx(u) = ctx(v)`.
pub(super) fn hyp_congr<F: Fn(Term) -> Term>(env: &mut Env, h_eq: &Thm, ctx: F) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (u, v) = eq.as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(u.clone());
    let leib = Thm::eq_leibniz(u, v, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    syl(h_eq, &mpd_const(&leib, &Thm::eq_refl(lhs))?)
}

/// From `⊢ H → u = v` infer `⊢ H → v = u`.
pub(super) fn hyp_eq_symm(env: &mut Env, h_eq: &Thm) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (u, v) = eq.as_eq()?;
    syl(h_eq, &eq_symm_imp(env, u, v))
}

/// From `⊢ H → u = v` and `⊢ H → φ(u)` infer `⊢ H → φ(v)`.
pub(super) fn hyp_transport<F: Fn(Term) -> Formula>(
    env: &mut Env,
    h_eq: &Thm,
    h_phi: &Thm,
    phi: F,
) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (u, v) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(u.clone(), v, hole, phi(Term::var(hole)));
    debug_assert_eq!(*h_phi.concl(), Formula::imp(h.clone(), phi(u)));
    hyp_mp(&hyp_mp(&a1i(&leib, h), h_eq)?, h_phi)
}
