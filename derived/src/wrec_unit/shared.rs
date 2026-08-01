//! Two unconditional equational moves, shared by the constructions in
//! [`crate::wrec_unit`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`congr`] rewrites one occurrence of a term inside a context given as a
//! closure, and [`eq_trans`] chains two proved equations. They read their
//! premises apart and can only fail to build a theorem, never build a wrong
//! one.
//!
//! Unlike the `H → …` helpers elsewhere in this crate these are
//! *unconditional*, because at this instance there is no ambient hypothesis
//! left to carry — which is the whole point of the file.

use kernel::{Env, Formula, Term, Thm};

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`, for a term context given as a
/// closure. The hypothesis-free companion of [`crate::wrec::hyp_congr`].
pub(super) fn congr<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// From `⊢ x = y` and `⊢ y = z` infer `⊢ x = z`.
pub(super) fn eq_trans(env: &mut Env, xy: &Thm, yz: &Thm) -> Option<Thm> {
    let (x, y) = xy.concl().as_eq()?;
    let (y2, z) = yz.concl().as_eq()?;
    if y != y2 {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(y, z, hole, Formula::eq(x, Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, yz)?, xy)
}
