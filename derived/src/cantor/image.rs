//! **Regularity**: a subset of a universe that is the surjective image of a
//! member is a member.
//!
//! # Interface
//!
//! ```text
//! ⊢ ((is_universe(u) ∧ (I ∈ u ∧ S ⊆ u))
//!      ∧ (DOM(R,I) ∧ (SV(R) ∧ ONTO(R,S))))  →  S ∈ u          [image_in_universe]
//! ```
//!
//! a **scheme** in the two-variable formula `R`, with
//! [`surjects_onto`] building the second conjunct. Callers need none of the
//! derivation below.
//!
//! # Why this is the export the rest of the development wants
//!
//! It is what turns `C₄`'s disjunction into a closure property. `C₄` says
//! `S ∈ u` or `S ≈ u`; [`super::member_not_equinumerous`] refutes the second
//! disjunct whenever `S` is a member, but `S` being a member is what was to be
//! proved. The way round is to refute it from `S` being an *image*: if `S ≈ u`
//! then composing the bijection with `R` surjects `I` onto every subset of `I`,
//! which [`super::no_diagonal_surjection`] forbids.
//!
//! `R` is a formula and not a set, so no product and no Separation instance is
//! needed to carry the relation, which is what keeps this usable in
//! [`crate::bound`] — where the relation is
//! `R(q,p) := (p ∈ f ∧ ∃r. p = ⟨q,r⟩)` and building it as a set would need
//! product closure.
//!
//! Product closure is *proved* now
//! ([`crate::funspace::product_in_universe`]) — this note used to say it "is not
//! available", full stop, and that is no longer the reason. The reason is
//! **layering**: `product_in_universe` is derived *through*
//! [`super::image_in_universe`] (via `crate::universe::union`, which imports
//! this module), so using it here would be circular. Keeping `R` a formula is
//! what avoids the cycle, not what avoids an open problem.
//!
//! This is the longest derivation in [`crate::cantor`] and it is one
//! construction: the composite relation, the three clauses it has to satisfy,
//! and the contradiction are a single argument with no separable parts.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::{a1i, and_left, and_right, com12, exists_elim_imp, hyp_and, hyp_mp, syl, uncurry};

use super::shared::{discharge, inst_all_imp, open_exists, split_and};
use super::clauses::{r_dom, r_onto, r_onto_subsets, r_sv};
use super::diagonal::no_diagonal_surjection;
use super::equinumerous::subsets_of_member;

/// `DOM ∧ (SV ∧ ONTO)` at a target *set* `s` — the package
/// [`image_in_universe`] consumes.
///
/// `cv` must be fresh for `r`; it is bound in the result, so the choice does not
/// show up in the formula.
pub fn surjects_onto(
    r: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    cv: FreeVar,
    i: &Term,
    s: &Term,
) -> Option<Formula> {
    let dom = r_dom(r, xv, bv, i);
    let sv = r_sv(r, xv, bv, cv)?;
    let onto = r_onto(r, xv, bv, s);
    Some(Formula::and(dom, Formula::and(sv, onto)))
}

/// `⊢ ((is_universe(u) ∧ (i ∈ u ∧ s ⊆ u)) ∧ surjects_onto(R, i, s)) → s ∈ u`
///
/// **Regularity: a subset of `u` that is the image of a member of `u` is itself
/// a member.** This is what turns `C₄` from a statement about cardinality into a
/// closure property, and it is the step every remaining closure property for a
/// universe goes through.
///
/// The argument. `C₄` offers `s ≈ u` or `s ∈ u`, so it is enough to refute the
/// first. A bijection `f : s → u` composes with `R` to give a relation
/// `R'(x,b) := ∃r. (R(x,r) ∧ ⟨r,b⟩ ∈ f)` from `i` onto `u` — and in particular
/// onto every subset of `i`, since a subset of the member `i` is a member of `u`
/// by `C₂`. [`no_diagonal_surjection`] refutes that. The composite is used as a
/// *formula*: nothing here builds `prod(i, 𝒫i)`, and no Separation beyond the
/// diagonal's own is needed.
///
/// Note that the composite is single-valued because `R` and `f` both are, and
/// that `f`'s totality and injectivity are never used — so the same proof works
/// for a mere surjection `s ↠ u`.
///
/// **What this does and does not need from the axiom.** `C₂` and `C₄` only; the
/// transitivity clause `C₁` is not used. Where `C₁` is unavoidable is one step
/// further on, in showing that a *function set* `f ∈ fs(X, u)` is a subset of
/// `u` — that needs the members of `X ∈ u` to be members of `u` — and
/// countermodel B in `crate::universe` refutes that without `C₁`.
///
/// `cv` is allocated internally; rebuild the statement with any fresh variable,
/// since it is bound. Returns `None` if the variables collide.
#[allow(clippy::too_many_arguments)]
pub fn image_in_universe(
    env: &mut Env,
    empty: &Thm,
    u: &Term,
    i: &Term,
    s: &Term,
    xv: FreeVar,
    bv: FreeVar,
    r: &Formula,
) -> Option<Thm> {
    if xv == bv {
        return None
    }
    for t in [u, i, s] {
        if t.occurs_free(xv) || t.occurs_free(bv) {
            return None
        }
    }
    let (cv, rv, rv2, fv, x2v, wv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    for v in [cv, rv, rv2, fv, x2v, wv] {
        if v == xv || v == bv || r.occurs_free(v) {
            return None
        }
        for t in [u, i, s] {
            if t.occurs_free(v) {
                return None
            }
        }
    }
    let (tx, tb, tc) = (Term::var(xv), Term::var(bv), Term::var(cv));
    let (tr, tr2, tf, tx2) = (Term::var(rv), Term::var(rv2), Term::var(fv), Term::var(x2v));

    // ── The hypothesis, taken apart once ─────────────────────────────────────
    let dom = r_dom(r, xv, bv, i);
    let sv = r_sv(r, xv, bv, cv)?;
    let onto = r_onto(r, xv, bv, s);
    let sv_onto = Formula::and(sv.clone(), onto.clone());
    let surj = Formula::and(dom.clone(), sv_onto.clone());

    let univ_u = crate::universe::is_universe(env, u);
    let i_in_u = Formula::mem(i.clone(), u.clone());
    let s_sub_u = kernel::thm::subset(env, s.clone(), u.clone());
    let mems = Formula::and(i_in_u.clone(), s_sub_u.clone());
    let base = Formula::and(univ_u.clone(), mems.clone());
    let h = Formula::and(base.clone(), surj.clone());

    let h_base = and_left(base.clone(), surj.clone());
    let h_surj = and_right(base.clone(), surj.clone());
    let h_univ = syl(&h_base, &and_left(univ_u.clone(), mems.clone()))?;
    let h_mems = syl(&h_base, &and_right(univ_u.clone(), mems))?;
    let h_i = syl(&h_mems, &and_left(i_in_u.clone(), s_sub_u.clone()))?;
    let h_ssub = syl(&h_mems, &and_right(i_in_u, s_sub_u))?;
    let h_dom = syl(&h_surj, &and_left(dom.clone(), sv_onto.clone()))?;
    let h_tail = syl(&h_surj, &and_right(dom.clone(), sv_onto))?;
    let h_sv = syl(&h_tail, &and_left(sv.clone(), onto.clone()))?;
    let h_onto = syl(&h_tail, &and_right(sv.clone(), onto.clone()))?;

    // A subset of the member `i` is a member of `u` — `C₂`, and the only place
    // the universe's own clauses enter before `C₄`.
    let h_subs_in_u = subsets_of_member(env, u, i, &h_univ, &h_i)?;
    let all_subs_in_u = h_subs_in_u.concl().as_imp()?.1;

    // ── The bijection `f : s → u`, and the three clauses of it this uses ─────
    let equi = kernel::thm::equinumerous(env, s.clone(), u.clone());
    let fbody = open_exists(&equi, &tf)?;
    debug_assert_eq!(equi, Formula::exists(fv, fbody.clone()), "the ∃f did not reopen");
    let (in_su, q1) = split_and(&fbody)?;
    let (total, q2) = split_and(&q1)?;
    let (onto_u, q3) = split_and(&q2)?;
    let (sv_f, inj) = split_and(&q3)?;

    let n = Formula::and(h.clone(), fbody.clone());
    let n_h = and_left(h.clone(), fbody.clone());
    let n_f = and_right(h.clone(), fbody.clone());
    let n_in_su = syl(&n_f, &and_left(in_su.clone(), q1.clone()))?;
    let n_q2 = syl(&syl(&n_f, &and_right(in_su.clone(), q1))?, &and_right(total, q2))?;
    let n_onto_u = syl(&n_q2, &and_left(onto_u.clone(), q3.clone()))?;
    let n_sv_f = syl(&syl(&n_q2, &and_right(onto_u.clone(), q3))?, &and_left(sv_f.clone(), inj))?;

    // ── The composite `R'(x,b) := ∃r. (R(x,r) ∧ ⟨r,b⟩ ∈ f)` ──────────────────
    let r_xr = r.subst(bv, &tr);
    let p_rb = kernel::thm::pair_in(env, tf.clone(), tr.clone(), tb.clone());
    let e1 = Formula::and(r_xr.clone(), p_rb.clone());
    let rprime = Formula::exists(rv, e1.clone());
    let rprime_c = rprime.subst(bv, &tc);

    // ── DOM': the composite still starts in `i` ──────────────────────────────
    let m = Formula::and(n.clone(), rprime.clone());
    let m_n = and_left(n.clone(), rprime.clone());
    let m_rp = and_right(n.clone(), rprime.clone());
    let m2 = Formula::and(m.clone(), e1.clone());
    let m2_m = and_left(m.clone(), e1.clone());
    let m2_e = and_right(m.clone(), e1.clone());
    let m2_rxr = syl(&m2_e, &and_left(r_xr.clone(), p_rb.clone()))?;
    let dom_at = inst_all_imp(&dom, &[tx.clone(), tr.clone()])?;
    let m2_in_i = hyp_mp(
        &syl(&syl(&m2_m, &syl(&m_n, &syl(&n_h, &h_dom)?)?)?, &dom_at)?,
        &m2_rxr,
    )?;
    debug_assert_eq!(
        *m2_in_i.concl(),
        Formula::imp(m2, Formula::mem(tx.clone(), i.clone())),
        "DOM' did not reduce to R's own domain clause"
    );
    let n_dom_step = uncurry(&discharge(rv, &m_rp, &m2_in_i)?)?;
    let dom_inner = Formula::imp(rprime.clone(), Formula::mem(tx.clone(), i.clone()));
    let n_dom_b =
        Thm::mp(&Thm::ax_dist(bv, n.clone(), dom_inner)?, &Thm::gen(bv, &n_dom_step))?;
    let n_dom = Thm::mp(
        &Thm::ax_dist(xv, n.clone(), n_dom_b.concl().as_imp()?.1)?,
        &Thm::gen(xv, &n_dom_b),
    )?;
    debug_assert_eq!(
        *n_dom.concl(),
        Formula::imp(n.clone(), r_dom(&rprime, xv, bv, i)),
        "DOM' has the wrong shape"
    );

    // ── SV': `R` pins `r`, then `f` pins the value ───────────────────────────
    let both_rp = Formula::and(rprime.clone(), rprime_c.clone());
    let k = Formula::and(n.clone(), both_rp.clone());
    let k_n = and_left(n.clone(), both_rp.clone());
    let k_both = and_right(n.clone(), both_rp.clone());
    let k_p1 = syl(&k_both, &and_left(rprime.clone(), rprime_c.clone()))?;
    let k_p2 = syl(&k_both, &and_right(rprime.clone(), rprime_c.clone()))?;

    let e2_left = r.subst(bv, &tr2);
    let e2_right = kernel::thm::pair_in(env, tf.clone(), tr2.clone(), tc.clone());
    let e2 = Formula::and(e2_left.clone(), e2_right.clone());
    debug_assert_eq!(
        rprime_c,
        Formula::exists(rv2, e2.clone()),
        "the second composite did not reopen at a fresh witness"
    );

    let k1 = Formula::and(k.clone(), e1.clone());
    let k1_k = and_left(k.clone(), e1.clone());
    let k1_e1 = and_right(k.clone(), e1.clone());
    let k2 = Formula::and(k1.clone(), e2.clone());
    let k2_k1 = and_left(k1.clone(), e2.clone());
    let k2_e2 = and_right(k1.clone(), e2.clone());
    let k2_k = syl(&k2_k1, &k1_k)?;
    let k2_e1 = syl(&k2_k1, &k1_e1)?;
    let k2_n = syl(&k2_k, &k_n)?;

    let k2_rxr = syl(&k2_e1, &and_left(r_xr.clone(), p_rb.clone()))?;
    let k2_prb = syl(&k2_e1, &and_right(r_xr, p_rb.clone()))?;
    let k2_rxr2 = syl(&k2_e2, &and_left(e2_left, e2_right.clone()))?;
    let k2_pr2c = syl(&k2_e2, &and_right(k2_rxr2.concl().as_imp()?.1, e2_right))?;

    let sv_at = inst_all_imp(&sv, &[tx.clone(), tr.clone(), tr2.clone()])?;
    let k2_eq_r = hyp_mp(
        &syl(&syl(&k2_n, &syl(&n_h, &h_sv)?)?, &sv_at)?,
        &hyp_and(&k2_rxr, &k2_rxr2)?,
    )?;
    let carry = Thm::eq_leibniz(
        tr.clone(),
        tr2.clone(),
        wv,
        kernel::thm::pair_in(env, tf.clone(), Term::var(wv), tb.clone()),
    );
    let k2_pr2b = hyp_mp(&hyp_mp(&a1i(&carry, k2.clone()), &k2_eq_r)?, &k2_prb)?;
    let sv_f_at = inst_all_imp(&sv_f, &[tr2.clone(), tb.clone(), tc.clone()])?;
    let k2_eq_bc = hyp_mp(
        &syl(&syl(&k2_n, &n_sv_f)?, &sv_f_at)?,
        &hyp_and(&k2_pr2b, &k2_pr2c)?,
    )?;
    debug_assert_eq!(
        *k2_eq_bc.concl(),
        Formula::imp(k2, Formula::eq(tb.clone(), tc.clone())),
        "SV' did not reach the equation"
    );

    let k1_eq = discharge(rv2, &syl(&k1_k, &k_p2)?, &k2_eq_bc)?;
    let k_eq = discharge(rv, &k_p1, &k1_eq)?;
    let n_sv_step = uncurry(&k_eq)?;
    let n_sv_c = Thm::mp(
        &Thm::ax_dist(cv, n.clone(), n_sv_step.concl().as_imp()?.1)?,
        &Thm::gen(cv, &n_sv_step),
    )?;
    let n_sv_b = Thm::mp(
        &Thm::ax_dist(bv, n.clone(), n_sv_c.concl().as_imp()?.1)?,
        &Thm::gen(bv, &n_sv_c),
    )?;
    let n_sv_r = Thm::mp(
        &Thm::ax_dist(xv, n.clone(), n_sv_b.concl().as_imp()?.1)?,
        &Thm::gen(xv, &n_sv_b),
    )?;
    debug_assert_eq!(
        *n_sv_r.concl(),
        Formula::imp(n.clone(), r_sv(&rprime, xv, bv, cv)?),
        "SV' has the wrong shape"
    );

    // ── ONTO': every subset of `i` is a member of `u`, and `f` is onto `u` ───
    let b_sub_i = kernel::thm::subset(env, tb.clone(), i.clone());
    let p = Formula::and(n.clone(), b_sub_i.clone());
    let p_n = and_left(n.clone(), b_sub_i.clone());
    let p_sub = and_right(n.clone(), b_sub_i.clone());
    let p_b_in_u = hyp_mp(
        &syl(&syl(&p_n, &syl(&n_h, &h_subs_in_u)?)?, &Thm::ax_inst(all_subs_in_u, tb.clone())?)?,
        &p_sub,
    )?;
    let p_ex_r = hyp_mp(
        &syl(&syl(&p_n, &n_onto_u)?, &Thm::ax_inst(onto_u.clone(), tb.clone())?)?,
        &p_b_in_u,
    )?;
    debug_assert_eq!(
        p_ex_r.concl().as_imp()?.1,
        Formula::exists(rv, p_rb.clone()),
        "f's onto clause does not produce a preimage of b"
    );

    let p1 = Formula::and(p.clone(), p_rb.clone());
    let p1_p = and_left(p.clone(), p_rb.clone());
    let p1_pr = and_right(p.clone(), p_rb.clone());
    let in_su_at = inst_all_imp(&in_su, &[tr.clone(), tb.clone()])?;
    let p1_r_in_s = syl(
        &hyp_mp(&syl(&syl(&p1_p, &syl(&p_n, &n_in_su)?)?, &in_su_at)?, &p1_pr)?,
        &and_left(Formula::mem(tr.clone(), s.clone()), Formula::mem(tb.clone(), u.clone())),
    )?;
    let p1_ex_x = hyp_mp(
        &syl(&syl(&p1_p, &syl(&p_n, &syl(&n_h, &h_onto)?)?)?, &Thm::ax_inst(onto.clone(), tr.clone())?)?,
        &p1_r_in_s,
    )?;
    let r_x2r = r.subst(bv, &tr).subst(xv, &tx2);
    debug_assert_eq!(
        p1_ex_x.concl().as_imp()?.1,
        Formula::exists(x2v, r_x2r.clone()),
        "R's onto clause does not produce a preimage of r"
    );

    let p2 = Formula::and(p1.clone(), r_x2r.clone());
    let p2_p1 = and_left(p1.clone(), r_x2r.clone());
    let p2_r = and_right(p1.clone(), r_x2r.clone());
    let e1_x2 = e1.subst(xv, &tx2);
    let rprime_x2 = rprime.subst(xv, &tx2);
    let p2_pair = hyp_and(&p2_r, &syl(&p2_p1, &p1_pr)?)?;
    let p2_rp_x2 = syl(&p2_pair, &crate::exists_intro_imp(rv, e1_x2, tr.clone())?)?;
    debug_assert_eq!(
        *p2_rp_x2.concl(),
        Formula::imp(p2.clone(), rprime_x2.clone()),
        "the composite was not introduced at the witness"
    );
    let p2_goal = syl(&p2_rp_x2, &crate::exists_intro_imp(xv, rprime.clone(), tx2)?)?;

    let p1_goal = discharge(x2v, &p1_ex_x, &p2_goal)?;
    let p_goal = discharge(rv, &p_ex_r, &p1_goal)?;
    let n_onto_r = Thm::mp(
        &Thm::ax_dist(bv, n.clone(), uncurry(&p_goal)?.concl().as_imp()?.1)?,
        &Thm::gen(bv, &uncurry(&p_goal)?),
    )?;
    debug_assert_eq!(
        *n_onto_r.concl(),
        Formula::imp(n.clone(), r_onto_subsets(env, &rprime, xv, bv, i)),
        "ONTO' has the wrong shape"
    );

    // ── Cantor refutes the composite, so `s ≉ u` ─────────────────────────────
    let cantor = no_diagonal_surjection(env, empty, i, xv, bv, &rprime)?;
    let n_false = hyp_mp(
        &a1i(&cantor, n.clone()),
        &hyp_and(&n_dom, &hyp_and(&n_sv_r, &n_onto_r)?)?,
    )?;
    let h_not_equi = com12(&exists_elim_imp(
        fv,
        &Thm::gen(fv, &com12(&uncurry(&n_false)?)?),
        &Formula::imp(h.clone(), Formula::false_()),
    )?)?;
    debug_assert_eq!(
        *h_not_equi.concl(),
        Formula::imp(h.clone(), Formula::not(equi.clone())),
        "the refutation of s ≈ u has the wrong shape"
    );

    // ── `C₄`, with the equinumerosity disjunct gone ──────────────────────────
    let cl = crate::universe::universe_clauses(env, u).ok()?;
    let c4_at_s = Thm::ax_inst(cl.c4, s.clone())?;
    let h_disj = hyp_mp(&syl(&h_univ, &syl(&cl.to_c4, &c4_at_s)?)?, &h_ssub)?;
    let goal = Formula::mem(s.clone(), u.clone());
    debug_assert_eq!(
        *h_disj.concl(),
        Formula::imp(h.clone(), Formula::or(equi, goal.clone())),
        "C₄ did not instantiate to the expected disjunction"
    );
    let out = hyp_mp(&h_disj, &h_not_equi)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal), "image_in_universe: wrong shape");
    Some(out)
}
