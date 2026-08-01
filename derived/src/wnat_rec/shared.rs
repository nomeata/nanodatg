//! Two combinators shared by the constructions in [`crate::wnat_rec`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`congr_ctx`] rewrites one occurrence of a term inside a context given as a
//! closure, and [`gen_under`] generalises under a fixed hypothesis. Both exist
//! because there is no deduction theorem: every equation in this module is
//! derived under the ambient `HYP`, and the ordinary equality toolkit consumes
//! *proved* equations.

use kernel::{Env, Formula, FreeVar, Term, Thm};

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
pub(super) fn congr_ctx<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
pub(super) fn gen_under(v: FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}
