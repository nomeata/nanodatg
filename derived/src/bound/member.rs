//! **Step 3** — a function into a universe is a *member* of it.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ∈ u)
//!                                                       [funspace_mem_universe]
//! ```
//!
//! Callers need none of the derivation below. It is the longest single
//! derivation in [`crate::bound`], and it is one construction: the three clauses
//! it assembles are the three hypotheses of a single lemma and have no
//! independent life.
//!
//! # The route, and why no Separation
//!
//! [`super::funspace_subset_universe`] makes `f` a *subset* of `u`; turning that
//! into membership is [`crate::cantor::image_in_universe`] — regularity, which
//! is what makes `C₄`'s disjunction a closure property — applied at `I := x`,
//! `S := f`, and the relation **scheme**
//!
//! ```text
//! R(q,p) := (p ∈ f ∧ ∃r. p = ⟨q,r⟩)
//! ```
//!
//! `R` is a formula, not a set, so no second product and no Separation instance
//! are needed anywhere. Its three obligations are discharged from material
//! already to hand:
//!
//! * **`ONTO`** — every `p ∈ f` has a first component in `x`, from the product
//!   membership condition, i.e. [`super::funspace_pairs`];
//! * **`DOM`** — every `q ∈ x` is related to something, from totality of `f`;
//! * **`SV`** — `R` is single-valued, from `f`'s own single-valuedness together
//!   with [`crate::pairs::opair_inj`].

use kernel::{Env, Formula, Term, Thm};
use crate::cantor::{r_dom, r_onto, r_sv};
use crate::funspace::is_single_valued;
use crate::sums::Sums;
use crate::universe::is_universe;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp,
    inst_all, opair, syl, uncurry,
};

use super::shared::{hyp_inst, hyp_inst_mp, hyp_leibniz, open_exists, split_and};
use super::subset::funspace_pairs_at;

/// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ∈ u)`.
///
/// [`crate::cantor::image_in_universe`] at `I := x`, `S := f` and the relation
/// scheme
///
/// ```text
/// R(q,p)  :=  (p ∈ f ∧ ∃y. p = ⟨q,y⟩)
/// ```
///
/// with `f ⊆ u` supplied by [`crate::bound::funspace_subset_universe`]. The three clauses:
///
/// * **ONTO** — a member `p` of `f` is `⟨q,r⟩` with `q ∈ x` ([`crate::bound::funspace_pairs`]),
///   and that `q` is the witness;
/// * **DOM** — if `R(q,p)` then `p` is *both* `⟨q,y⟩` and the `⟨q′,r⟩` the
///   product condition supplies, so `q = q′ ∈ x` by
///   [`crate::pairs::opair_inj`];
/// * **SV** — if `R(q,p)` and `R(q,c)` then `⟨q,y⟩ ∈ f` and `⟨q,y′⟩ ∈ f`, so
///   `y = y′` because `f` is single-valued, and `p = ⟨q,y⟩ = ⟨q,y′⟩ = c`.
///
/// Note what is *not* needed: `f` need not be total, and `x` need not be
/// anything but a member of `u`. `empty` is consumed by the diagonal Separation
/// inside `image_in_universe` and appears in no result.
pub fn funspace_mem_universe(
    env: &mut Env,
    s: &Sums,
    empty: &Thm,
    pairs: &Thm,
    subset: &Thm,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let (uv, xv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tx, tf) = (Term::var(uv), Term::var(xv), Term::var(fv));

    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let f_in_fs = Formula::mem(tf.clone(), s.fs.of(tx.clone(), tu.clone()));
    let mems = Formula::and(x_in_u.clone(), f_in_fs.clone());
    let h = Formula::and(univ_u.clone(), mems.clone());

    let h_univ = and_left(univ_u.clone(), mems.clone());
    let h_mems = and_right(univ_u, mems);
    let h_x = syl(&h_mems, &and_left(x_in_u.clone(), f_in_fs.clone()))?;
    let h_f = syl(&h_mems, &and_right(x_in_u, f_in_fs))?;

    // ── `f ⊆ u`, and the two ways of reading `f` apart ───────────────────────
    let h_fsub = inst_all(subset, &[tu.clone(), tx.clone(), tf.clone()])?;
    let sub_f_u = kernel::thm::subset(env, tf.clone(), tu.clone());
    if *h_fsub.concl() != Formula::imp(h.clone(), sub_f_u.clone()) {
        return None
    }
    let pairs_at = funspace_pairs_at(env, pairs, s, &tx, &tu, &tf)?;
    let h_pairs = syl(&h_f, &pairs_at)?;

    let fs_at = inst_all(&s.fs.fs_ax, &[tx.clone(), tu.clone(), tf.clone()])?;
    let h_isfun = syl(&h_f, &iff_mp(&fs_at)?)?;
    let isfun = h_isfun.concl().as_imp()?.1;
    let (sub_prod, graph) = split_and(&isfun)?;
    let (total, single) = split_and(&graph)?;
    if single != is_single_valued(env, &s.ap.sets, &tf) {
        return None
    }
    let h_graph = syl(&h_isfun, &and_right(sub_prod, graph.clone()))?;
    let h_single = syl(&h_graph, &and_right(total, single))?;

    // ── The relation scheme `R(q,p)` ────────────────────────────────────────
    let (qv, pv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tq, tp, ty) = (Term::var(qv), Term::var(pv), Term::var(yv));
    let p_in_f = Formula::mem(tp.clone(), tf.clone());
    let ex_y = Formula::exists(yv, Formula::eq(tp.clone(), opair(up, tq.clone(), ty.clone())));
    let r = Formula::and(p_in_f.clone(), ex_y.clone());

    // ── ONTO: every member of `f` is hit ────────────────────────────────────
    let l = Formula::and(h.clone(), p_in_f.clone());
    let l_h = and_left(h.clone(), p_in_f.clone());
    let l_p = and_right(h.clone(), p_in_f.clone());
    let l_ex = hyp_inst_mp(&syl(&l_h, &h_pairs)?, &tp, &l_p)?;
    let ex_outer = l_ex.concl().as_imp()?.1;

    let (q1v, r1v) = (env.fresh_var(), env.fresh_var());
    let (tq1, tr1) = (Term::var(q1v), Term::var(r1v));
    let e1 = open_exists(&ex_outer, &tq1)?;
    let m = Formula::and(l.clone(), e1.clone());
    let m_l = and_left(l.clone(), e1.clone());
    let m_e1 = and_right(l.clone(), e1.clone());
    let (q1_in_x, ex_inner) = split_and(&e1)?;
    let m_ex = syl(&m_e1, &and_right(q1_in_x.clone(), ex_inner.clone()))?;

    let e2 = open_exists(&ex_inner, &tr1)?;
    let n = Formula::and(m.clone(), e2.clone());
    let n_m = and_left(m.clone(), e2.clone());
    let n_e2 = and_right(m.clone(), e2.clone());
    let (r1_in_u, p_eq) = split_and(&e2)?;
    if p_eq != Formula::eq(tp.clone(), opair(up, tq1.clone(), tr1.clone())) {
        return None
    }
    let n_eq = syl(&n_e2, &and_right(r1_in_u, p_eq))?;

    let body_at_q1 = Formula::eq(tp.clone(), opair(up, tq1.clone(), ty.clone()));
    let n_ey = syl(&n_eq, &exists_intro_imp(yv, body_at_q1, tr1.clone())?)?;
    let n_pf = syl(&syl(&n_m, &m_l)?, &l_p)?;
    let n_r = hyp_and(&n_pf, &n_ey)?;
    if *n_r.concl() != Formula::imp(n.clone(), r.subst(qv, &tq1)) {
        return None
    }
    let ex_q = Formula::exists(qv, r.clone());
    let n_ex_q = syl(&n_r, &exists_intro_imp(qv, r.clone(), tq1)?)?;

    let m_goal = crate::funspace::discharge(r1v, &m_ex, &n_ex_q)?;
    let l_goal = crate::funspace::discharge(q1v, &l_ex, &m_goal)?;
    let h_onto = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::imp(p_in_f.clone(), ex_q))?,
        &Thm::gen(pv, &uncurry(&l_goal)?),
    )?;
    if *h_onto.concl() != Formula::imp(h.clone(), r_onto(&r, qv, pv, &tf)) {
        return None
    }

    // ── DOM: the relation starts in `x` ─────────────────────────────────────
    let k = Formula::and(h.clone(), r.clone());
    let k_h = and_left(h.clone(), r.clone());
    let k_r = and_right(h.clone(), r.clone());
    let k_pf = syl(&k_r, &and_left(p_in_f.clone(), ex_y.clone()))?;
    let k_ex_y = syl(&k_r, &and_right(p_in_f.clone(), ex_y.clone()))?;

    let y1v = env.fresh_var();
    let ty1 = Term::var(y1v);
    let ey1 = open_exists(&ex_y, &ty1)?;
    let k1 = Formula::and(k.clone(), ey1.clone());
    let k1_k = and_left(k.clone(), ey1.clone());
    let k1_ey = and_right(k.clone(), ey1.clone());
    if ey1 != Formula::eq(tp.clone(), opair(up, tq.clone(), ty1.clone())) {
        return None
    }

    let k1_ex = hyp_inst_mp(
        &syl(&syl(&k1_k, &k_h)?, &h_pairs)?,
        &tp,
        &syl(&k1_k, &k_pf)?,
    )?;
    let (q2v, r2v) = (env.fresh_var(), env.fresh_var());
    let (tq2, tr2) = (Term::var(q2v), Term::var(r2v));
    let d1 = open_exists(&ex_outer, &tq2)?;
    let k2 = Formula::and(k1.clone(), d1.clone());
    let k2_k1 = and_left(k1.clone(), d1.clone());
    let k2_d1 = and_right(k1.clone(), d1.clone());
    let (q2_in_x, ex_inner2) = split_and(&d1)?;
    let k2_q2 = syl(&k2_d1, &and_left(q2_in_x.clone(), ex_inner2.clone()))?;
    let k2_ex = syl(&k2_d1, &and_right(q2_in_x, ex_inner2.clone()))?;

    let d2 = open_exists(&ex_inner2, &tr2)?;
    let k3_k2 = and_left(k2.clone(), d2.clone());
    let k3_d2 = and_right(k2.clone(), d2.clone());
    let (r2_in_u, p_eq2) = split_and(&d2)?;
    let k3_eq2 = syl(&k3_d2, &and_right(r2_in_u, p_eq2))?;

    // `⟨q,y₁⟩ = ⟨q₂,r₂⟩`, then `q = q₂` and so `q ∈ x`.
    let kur2 = opair(up, tq2.clone(), tr2.clone());
    let k3_ey = syl(&syl(&k3_k2, &k2_k1)?, &k1_ey)?;
    let w1 = env.fresh_var();
    let k3_pairs_eq = hyp_mp(
        &hyp_leibniz(&k3_ey, w1, &Formula::eq(Term::var(w1), kur2.clone()))?,
        &k3_eq2,
    )?;
    let inj = inst_all(&s.ap.pair_inj, &[tq.clone(), ty1.clone(), tq2.clone(), tr2.clone()])?;
    let kur1 = opair(up, tq.clone(), ty1.clone());
    if *inj.concl()
        != Formula::imp(
            Formula::eq(kur1, kur2),
            Formula::and(
                Formula::eq(tq.clone(), tq2.clone()),
                Formula::eq(ty1.clone(), tr2.clone()),
            ),
        )
    {
        return None
    }
    let k3_q_eq = syl(
        &syl(&k3_pairs_eq, &inj)?,
        &and_left(Formula::eq(tq.clone(), tq2.clone()), Formula::eq(ty1.clone(), tr2.clone())),
    )?;
    let k3_q_eq_sym = syl(&k3_q_eq, &eq_symm_imp(env, tq.clone(), tq2.clone()))?;
    let w2 = env.fresh_var();
    let k3_q_in_x = hyp_mp(
        &hyp_leibniz(&k3_q_eq_sym, w2, &Formula::mem(Term::var(w2), tx.clone()))?,
        &syl(&k3_k2, &k2_q2)?,
    )?;

    let k2_goal = crate::funspace::discharge(r2v, &k2_ex, &k3_q_in_x)?;
    let k1_goal = crate::funspace::discharge(q2v, &k1_ex, &k2_goal)?;
    let k_goal = crate::funspace::discharge(y1v, &k_ex_y, &k1_goal)?;
    let q_in_x = Formula::mem(tq.clone(), tx.clone());
    let h_dom_inner = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::imp(r.clone(), q_in_x.clone()))?,
        &Thm::gen(pv, &uncurry(&k_goal)?),
    )?;
    let h_dom = Thm::mp(
        &Thm::ax_dist(qv, h.clone(), h_dom_inner.concl().as_imp()?.1)?,
        &Thm::gen(qv, &h_dom_inner),
    )?;
    if *h_dom.concl() != Formula::imp(h.clone(), r_dom(&r, qv, pv, &tx)) {
        return None
    }

    // ── SV: the relation is single-valued ───────────────────────────────────
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let rc = r.subst(pv, &tc);
    let both_r = Formula::and(r.clone(), rc.clone());
    let g = Formula::and(h.clone(), both_r.clone());
    let g_h = and_left(h.clone(), both_r.clone());
    let g_r = syl(&and_right(h.clone(), both_r.clone()), &and_left(r.clone(), rc.clone()))?;
    let g_rc = syl(&and_right(h.clone(), both_r.clone()), &and_right(r.clone(), rc.clone()))?;
    let (c_in_f, ex_y_c) = split_and(&rc)?;
    let g_pf = syl(&g_r, &and_left(p_in_f.clone(), ex_y.clone()))?;
    let g_ex_y = syl(&g_r, &and_right(p_in_f.clone(), ex_y.clone()))?;
    let g_cf = syl(&g_rc, &and_left(c_in_f.clone(), ex_y_c.clone()))?;
    let g_ex_yc = syl(&g_rc, &and_right(c_in_f, ex_y_c.clone()))?;

    let (z1v, z2v) = (env.fresh_var(), env.fresh_var());
    let (tz1, tz2) = (Term::var(z1v), Term::var(z2v));
    let f1 = open_exists(&ex_y, &tz1)?;
    let g1 = Formula::and(g.clone(), f1.clone());
    let g1_g = and_left(g.clone(), f1.clone());
    let g1_f1 = and_right(g.clone(), f1.clone());
    let f2 = open_exists(&ex_y_c, &tz2)?;
    let g2 = Formula::and(g1.clone(), f2.clone());
    let g2_g1 = and_left(g1.clone(), f2.clone());
    let g2_f2 = and_right(g1.clone(), f2.clone());
    if f1 != Formula::eq(tp.clone(), opair(up, tq.clone(), tz1.clone()))
        || f2 != Formula::eq(tc.clone(), opair(up, tq.clone(), tz2.clone()))
    {
        return None
    }

    // `⟨q,z₁⟩ ∈ f` and `⟨q,z₂⟩ ∈ f`, by moving `p` and `c` across.
    let g2_ep = syl(&g2_g1, &g1_f1)?;
    let g2_ec = g2_f2.clone();
    let kc = opair(up, tq.clone(), tz2.clone());
    let (w3, w4) = (env.fresh_var(), env.fresh_var());
    let g2_kp_in_f = hyp_mp(
        &hyp_leibniz(&g2_ep, w3, &Formula::mem(Term::var(w3), tf.clone()))?,
        &syl(&syl(&g2_g1, &g1_g)?, &g_pf)?,
    )?;
    let g2_kc_in_f = hyp_mp(
        &hyp_leibniz(&g2_ec, w4, &Formula::mem(Term::var(w4), tf.clone()))?,
        &syl(&syl(&g2_g1, &g1_g)?, &g_cf)?,
    )?;

    let g2_g = syl(&g2_g1, &g1_g)?;
    let g2_single = syl(&syl(&g2_g, &g_h)?, &h_single)?;
    let g2_sv = hyp_inst(&g2_single, &[tq.clone(), tz1.clone(), tz2.clone()])?;
    let g2_z = hyp_mp(&g2_sv, &hyp_and(&g2_kp_in_f, &g2_kc_in_f)?)?;
    if *g2_z.concl() != Formula::imp(g2.clone(), Formula::eq(tz1.clone(), tz2.clone())) {
        return None
    }

    // `p = ⟨q,z₁⟩ = ⟨q,z₂⟩ = c`.
    let w5 = env.fresh_var();
    let g2_p_kc = hyp_mp(
        &hyp_leibniz(
            &g2_z,
            w5,
            &Formula::eq(tp.clone(), opair(up, tq.clone(), Term::var(w5))),
        )?,
        &g2_ep,
    )?;
    let w6 = env.fresh_var();
    let g2_kc_c = syl(&g2_ec, &eq_symm_imp(env, tc.clone(), kc.clone()))?;
    let g2_pc = hyp_mp(
        &hyp_leibniz(&g2_kc_c, w6, &Formula::eq(tp.clone(), Term::var(w6)))?,
        &g2_p_kc,
    )?;

    let g1_goal = crate::funspace::discharge(z2v, &syl(&g1_g, &g_ex_yc)?, &g2_pc)?;
    let g_goal = crate::funspace::discharge(z1v, &g_ex_y, &g1_goal)?;
    let p_eq_c = Formula::eq(tp.clone(), tc.clone());
    let h_sv_c = Thm::mp(
        &Thm::ax_dist(cv, h.clone(), Formula::imp(both_r.clone(), p_eq_c.clone()))?,
        &Thm::gen(cv, &uncurry(&g_goal)?),
    )?;
    let h_sv_p = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), h_sv_c.concl().as_imp()?.1)?,
        &Thm::gen(pv, &h_sv_c),
    )?;
    let h_sv = Thm::mp(
        &Thm::ax_dist(qv, h.clone(), h_sv_p.concl().as_imp()?.1)?,
        &Thm::gen(qv, &h_sv_p),
    )?;
    if *h_sv.concl() != Formula::imp(h.clone(), r_sv(&r, qv, pv, cv).ok()?) {
        return None
    }

    // ── Regularity ──────────────────────────────────────────────────────────
    let img = crate::cantor::image_in_universe(env, empty, &tu, &tx, &tf, qv, pv, &r).ok()?;
    let surj = crate::cantor::surjects_onto(&r, qv, pv, cv, &tx, &tf).ok()?;
    let base = Formula::and(
        is_universe(env, &tu),
        Formula::and(Formula::mem(tx.clone(), tu.clone()), sub_f_u),
    );
    if *img.concl()
        != Formula::imp(Formula::and(base, surj), Formula::mem(tf.clone(), tu.clone()))
    {
        return None
    }
    let h_base = hyp_and(&h_univ, &hyp_and(&h_x, &h_fsub)?)?;
    let h_surj = hyp_and(&h_dom, &hyp_and(&h_sv, &h_onto)?)?;
    let out = hyp_mp(&a1i(&img, h.clone()), &hyp_and(&h_base, &h_surj)?)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tf, tu)),
        "funspace_mem_universe: wrong shape"
    );
    Some(gen_all(&[uv, xv, fv], &out))
}
