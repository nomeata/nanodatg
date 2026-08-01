//! Small rewriting steps, in implication form, shared by the constructions in
//! [`crate::wlist_rec`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** Every
//! equation in this module is derived under the ambient `HYP`, and there is no
//! deduction theorem, so congruence ([`congr_ctx`]), transport
//! ([`carry_under`], [`rewrite_under`]), generalisation ([`gen_under`]) and
//! instantiation ([`hyp_inst`]) all have to exist in the `H → …` form.
//!
//! [`split_pair`] takes an equation between Kuratowski pairs apart into its two
//! components; it is what turns [`super::members`]'s case analysis into usable
//! equations on `head` and `tail` separately.
//!
//! Reading a formula apart produces no `Thm`, so a helper here can fail to build
//! a theorem but never build a wrong one.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::funcs::Apply;
use crate::{and_left, and_right, hyp_mp, inst_all, syl};

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
pub(super) fn congr_ctx<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// From `⊢ x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
pub(super) fn carry_under<F: Fn(Term) -> Formula>(
    env: &mut Env,
    eq: &Thm,
    ctx: F,
    prev: &Thm,
) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    syl(prev, &Thm::mp(&leib, eq)?)
}

/// From `⊢ H → x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
pub(super) fn rewrite_under<F: Fn(Term) -> Formula>(
    env: &mut Env,
    h_eq: &Thm,
    ctx: F,
    h_prev: &Thm,
) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    hyp_mp(&syl(h_eq, &leib)?, h_prev)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
pub(super) fn gen_under(v: FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → ⟨a,b⟩ = ⟨c,d⟩` infer `⊢ H → a = c` and `⊢ H → b = d`.
pub(super) fn split_pair(ap: &Apply, h_eq: &Thm, a: &Term, b: &Term, c: &Term, d: &Term) -> Option<(Thm, Thm)> {
    let inj = inst_all(&ap.pair_inj, &[a.clone(), b.clone(), c.clone(), d.clone()])?;
    let (l, r) = (Formula::eq(a.clone(), c.clone()), Formula::eq(b.clone(), d.clone()));
    let both = syl(h_eq, &inj)?;
    Some((
        syl(&both, &and_left(l.clone(), r.clone()))?,
        syl(&both, &and_right(l, r))?,
    ))
}
