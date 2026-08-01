//! Internal helpers shared by the constructions in [`crate::ext`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** These
//! are the combinators that more than one sibling module needs: equational
//! reasoning under a fixed hypothesis, discharge of an existential, universal
//! instantiation in implication form, and the decomposition of `isfun` into its
//! three clauses.
//!
//! The `⊢ H → φ` idiom has no equality toolkit of its own — `eq_trans`,
//! `eq_symm` and `congr_arg` all consume a *proved* equation, and the equations
//! in these derivations are only ever available under `H` — so [`hyp_leibniz`],
//! [`hyp_congr`], [`hyp_eq_trans`] and [`hyp_eq_symm`] are the missing half,
//! each a single Leibniz step plus plumbing. Reading a formula apart produces
//! no `Thm`, so a helper here can fail to build a theorem but never build a
//! wrong one.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{is_function, is_single_valued, is_total, Product};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, hyp_mp, inst_all, mpd_const,
    syl, uncurry,
};

/// From `⊢ P → (Q → R)` infer `⊢ (P ∧ Q) → R` — the converse of
/// [`crate::uncurry`].
pub(super) fn curry(t: &Thm) -> Option<Thm> {
    let (p, rest) = t.concl().as_imp()?;
    let (q, _) = rest.as_imp()?;
    let h = Formula::and(p.clone(), q.clone());
    let hp = and_left(p.clone(), q.clone());
    let hq = and_right(p, q);
    hyp_mp(&hyp_mp(&a1i(t, h), &hp)?, &hq)
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])` — Leibniz under a
/// hypothesis.
pub(super) fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ H → a = b` infer `⊢ H → c[a/w] = c[b/w]` — congruence under a
/// hypothesis, for a term `c` with the hole `w`.
///
/// `lhs` must be `c[a/w]`; that is checked rather than assumed, since a term
/// cannot be substituted into from outside the kernel and the caller therefore
/// has to supply the substituted form itself. Returns `None` if it does not
/// match, which is exactly the case where the hole is in the wrong place.
pub(super) fn hyp_congr(h_eq: &Thm, w: FreeVar, lhs: &Term, c: &Term) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    let leib = Thm::eq_leibniz(a, b, w, Formula::eq(lhs.clone(), c.clone()));
    let (ante, _) = leib.concl().as_imp()?.1.as_imp()?;
    if ante != Formula::eq(lhs.clone(), lhs.clone()) {
        return None
    }
    syl(h_eq, &mpd_const(&leib, &Thm::eq_refl(lhs.clone()))?)
}

/// From `⊢ H → a = b` and `⊢ H → b = c` infer `⊢ H → a = c`.
pub(super) fn hyp_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
    let (h, e1) = ab.concl().as_imp()?;
    let (_, e2) = bc.concl().as_imp()?;
    let (a, b1) = e1.as_eq()?;
    let (b2, c) = e2.as_eq()?;
    if b1 != b2 {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(b1, c, w, Formula::eq(a, Term::var(w)));
    hyp_mp(&hyp_mp(&a1i(&leib, h), bc)?, ab)
}

/// From `⊢ H → a = b` infer `⊢ H → b = a`.
pub(super) fn hyp_eq_symm(env: &mut Env, h_eq: &Thm) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    syl(h_eq, &eq_symm_imp(env, a, b))
}

/// `⊢ ∀A. (P(A, A) → f(A) = g(A))`, from `⊢ ∀A ∀A'. (A = A' → (P(A,A') → …))`.
///
/// Shared by [`lam_ext_same_domain`] and [`dprod_ext_same_domain`], which
/// differ only in what the theorem handed in says.
pub(super) fn same_domain(env: &mut Env, thm: &Thm) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let inst = inst_all(thm, &[ta.clone(), ta.clone()])?;
    let (ante, _) = inst.concl().as_imp()?;
    // The antecedent must be the reflexive equation the instantiation created;
    // anything else means this is not a conclusion of the expected shape.
    if ante != Formula::eq(ta.clone(), ta.clone()) {
        return None
    }
    let out = Thm::mp(&inst, &Thm::eq_refl(ta))?;
    debug_assert!(out.concl().as_imp().is_some(), "same_domain: unexpected shape");
    Some(Thm::gen(a, &out))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
///
/// A private copy of the combinator [`crate::funspace`] keeps privately too, on
/// the same reasoning it gives: reading formulas apart produces no `Thm`, so a
/// duplicate is safe, and a derivation this long should not break when a
/// neighbouring module reshapes its own helpers.
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    crate::empty::hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — [`crate::inst_all`] in implication form, for a
/// quantified formula that is only available under a hypothesis.
pub(super) fn inst_all_imp(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = Thm::ax_inst(phi.clone(), ts.first()?.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}

/// The three clauses of `isfun(f)`, as the formulas this module reasons with,
/// checked against [`crate::funspace::is_function`]'s own assembly of them.
///
/// Returns `None` if they do not agree — which would mean the function space is
/// characterised by something other than what is taken apart below, and the
/// projections would then be about the wrong conjuncts.
pub(super) fn isfun_parts(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    a: &Term,
    b: &Term,
    f: &Term,
) -> Option<(Formula, Formula, Formula, Formula)> {
    let sub = kernel::thm::subset(env, f.clone(), p.of(a.clone(), b.clone()));
    let total = is_total(env, &ap.sets, a, b, f);
    let sv = is_single_valued(env, &ap.sets, f);
    let isfun = is_function(env, &ap.sets, p, a, b, f);
    if isfun != Formula::and(sub.clone(), Formula::and(total.clone(), sv.clone())) {
        return None
    }
    Some((isfun, sub, total, sv))
}
