//! There is at most one recursion: agreement, then inclusion, then equality.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀n. (n ∈ ω → ∀f₁ ∀f₂. ((RecFn(f₁) ∧ RecFn(f₂)) → app(f₁,n) = app(f₂,n)))  [rec_agree]
//! ⊢ ∀f₁ ∀f₂ ∀p. ((RecFn(f₁) ∧ RecFn(f₂)) → (p ∈ f₁ → p ∈ f₂))                [rec_subset]
//! ⊢ ∀f₁ ∀f₂. ((RecFn(f₁) ∧ RecFn(f₂)) → f₁ = f₂)                             [rec_unique]
//! ```
//!
//! Callers need only the last. `RecFn` is [`crate::recursion::rec_fn`]'s five
//! conjuncts.
//!
//! # Why this is not [`crate::recursion::approx_unique`] again
//!
//! It is the same *shape* of argument — agree at every point, then upgrade
//! agreement to equality through the graph conjuncts — but it is a different
//! argument, and much shorter, because the recursion is stated with `app` rather
//! than with membership. [`rec_agree`]'s induction never opens a graph: the base
//! is R4 at both functions and the step is R5 at both, with the induction
//! hypothesis equating the two arguments of `G`. The approximation version had
//! to read each value off a pair first, which is where its length came from.
//!
//! [`crate::recursion::approx_unique`] is also unusable here on its own terms:
//! its domain hypothesis is `m ∈ ω`, and the domain in question is `ω` itself.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_intro, and_left, and_right, gen_all, hyp_and, hyp_mp, inst_all, mpd_const, syl,
    uncurry,
};
use crate::funspace::discharge;
use super::hyp::{hyp_eq_symm, hyp_eq_trans, inst_chain};
use super::induction::induction_scheme;
use super::iterate::{rec_fn, RecFn};
use super::rec::Rec;

/// `⊢ ∀n. (n ∈ ω → ∀f₁ ∀f₂. ((RecFn(f₁) ∧ RecFn(f₂)) → app(f₁,n) = app(f₂,n)))`
/// — **two recursions take the same value at every natural**.
///
/// An induction that never opens a graph: the base is R4 at both functions and
/// the step is R5 at both, with the induction hypothesis equating the two
/// arguments of `G`.
pub fn rec_agree(env: &mut Env, r: &Rec, g: FnSym, c: &Term) -> Option<Thm> {
    let (x, f1, f2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tf1, tf2) = (Term::var(x), Term::var(f1), Term::var(f2));
    let s1 = rec_fn(env, r, g, c, &tf1)?;
    let s2 = rec_fn(env, r, g, c, &tf2)?;
    let (p1, p2) = (s1.formula(), s2.formula());
    let h = Formula::and(p1.clone(), p2.clone());

    let goal_at =
        |t: &Term| Formula::eq(r.apply(tf1.clone(), t.clone()), r.apply(tf2.clone(), t.clone()));
    let phi_at = |t: &Term| {
        Formula::forall(f1, Formula::forall(f2, Formula::imp(h.clone(), goal_at(t))))
    };
    let phi = phi_at(&tx);

    // ── Base: both functions take the value `c` at `0` ───────────────────────
    let zero = r.zero();
    let h_b1 = syl(&and_left(p1.clone(), p2.clone()), &s1.proj(3)?)?;
    let h_b2 = syl(&and_right(p1.clone(), p2.clone()), &s2.proj(3)?)?;
    let h_b2s = hyp_eq_symm(env, &h_b2)?;
    let base_body = hyp_eq_trans(env, &h_b1, &h_b2s)?;
    let base = gen_all(&[f1, f2], &base_body);
    debug_assert_eq!(*base.concl(), phi.subst(x, &zero), "rec_agree: the base case drifted");

    // ── Step: both step by `G`, and the arguments agree ──────────────────────
    let sx = r.succ_of(tx.clone());
    let x_om = Formula::mem(tx.clone(), r.omega());
    let k = Formula::and(x_om.clone(), phi.clone());
    let j = Formula::and(k.clone(), h.clone());
    let j_k = and_left(k.clone(), h.clone());
    let j_h = and_right(k.clone(), h.clone());
    let j_xom = syl(&j_k, &and_left(x_om.clone(), phi.clone()))?;
    let j_phi = syl(&j_k, &and_right(x_om.clone(), phi.clone()))?;

    let equation = |j_s: &Thm, s: &RecFn| -> Option<Thm> {
        let r5 = syl(j_s, &s.proj(4)?)?;
        hyp_mp(&syl(&r5, &Thm::ax_inst(s.step.clone(), tx.clone())?)?, &j_xom)
    };
    let j_e1 = equation(&syl(&j_h, &and_left(p1.clone(), p2.clone()))?, &s1)?;
    let j_e2 = equation(&syl(&j_h, &and_right(p1.clone(), p2.clone()))?, &s2)?;

    let ic = inst_chain(&phi, &[tf1.clone(), tf2.clone()])?;
    let j_ih = hyp_mp(&syl(&j_phi, &ic)?, &j_h)?;

    let (v1, v2) = (r.apply(tf1.clone(), tx.clone()), r.apply(tf2.clone(), tx.clone()));
    let w = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(
            v1.clone(),
            v2,
            w,
            Formula::eq(
                Term::apply(g, vec![v1.clone()]),
                Term::apply(g, vec![Term::var(w)]),
            ),
        ),
        &Thm::eq_refl(Term::apply(g, vec![v1])),
    )?;
    let j_gg = syl(&j_ih, &congr)?;
    let j_left = hyp_eq_trans(env, &j_e1, &j_gg)?;
    let j_e2s = hyp_eq_symm(env, &j_e2)?;
    let j_goal = hyp_eq_trans(env, &j_left, &j_e2s)?;
    debug_assert_eq!(*j_goal.concl(), Formula::imp(j, goal_at(&sx)));

    let mut cur = uncurry(&j_goal)?;
    let mut inner = Formula::imp(h, goal_at(&sx));
    for v in [f2, f1] {
        cur = Thm::mp(&Thm::ax_dist(v, k.clone(), inner.clone())?, &Thm::gen(v, &cur))?;
        inner = Formula::forall(v, inner);
    }
    debug_assert_eq!(
        *cur.concl(),
        Formula::imp(Formula::and(x_om.clone(), phi.clone()), phi.subst(x, &sx)),
        "rec_agree: the step case drifted"
    );

    let scheme = induction_scheme(env, r.core(), x, &phi)?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(x, &cur)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, Formula::imp(x_om, phi)),
        "rec_agree: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀f₁ ∀f₂ ∀p. ((RecFn(f₁) ∧ RecFn(f₂)) → (p ∈ f₁ → p ∈ f₂))`.
///
/// One inclusion; [`rec_unique`] runs it in both directions. A member of `f₁` is
/// a pair `⟨a,b⟩` with `a ∈ ω` (R1), and single-valuedness reads `app(f₁,a) = b`
/// off it. `agree` then gives `app(f₂,a) = b`, and totality of `f₂` on `ω` (R3)
/// produces *some* pair `⟨a,b′⟩ ∈ f₂`, whose value must therefore be `b`.
///
/// `agree` must be [`rec_agree`]'s theorem at the same `g` and `c`.
pub fn rec_subset(env: &mut Env, r: &Rec, g: FnSym, c: &Term, agree: &Thm) -> Option<Thm> {
    let (f1, f2, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (a, b, b2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf1, tf2, tp) = (Term::var(f1), Term::var(f2), Term::var(p));
    let (ta, tb, tb2) = (Term::var(a), Term::var(b), Term::var(b2));

    let s1 = rec_fn(env, r, g, c, &tf1)?;
    let s2 = rec_fn(env, r, g, c, &tf2)?;
    let (q1, q2) = (s1.formula(), s2.formula());
    let h = Formula::and(q1.clone(), q2.clone());

    let p_f1 = Formula::mem(tp.clone(), tf1.clone());
    let p_f2 = Formula::mem(tp.clone(), tf2.clone());
    let j = Formula::and(h.clone(), p_f1.clone());
    let j_h = and_left(h.clone(), p_f1.clone());
    let j_p1 = and_right(h.clone(), p_f1.clone());
    let j_s1 = syl(&j_h, &and_left(q1.clone(), q2.clone()))?;
    let j_s2 = syl(&j_h, &and_right(q1, q2))?;

    // ── `p` is a pair `⟨a,b⟩` with `a ∈ ω` ───────────────────────────────────
    let pair_ab = r.pair(ta.clone(), tb.clone());
    let a_om = Formula::mem(ta.clone(), r.omega());
    let e_inner = Formula::exists(b, Formula::eq(tp.clone(), pair_ab.clone()));
    let e_a = Formula::and(a_om.clone(), e_inner.clone());
    let bounded_at_p = Thm::ax_inst(s1.bounded.clone(), tp.clone())?;
    debug_assert_eq!(
        bounded_at_p.concl().as_imp()?.1,
        Formula::imp(p_f1.clone(), Formula::exists(a, e_a.clone())),
        "rec_subset: conjunct R1 has an unexpected shape"
    );
    let j_ex_a = hyp_mp(&syl(&syl(&j_s1, &s1.proj(0)?)?, &bounded_at_p)?, &j_p1)?;

    let j2 = Formula::and(j.clone(), e_a.clone());
    let j2_j = and_left(j.clone(), e_a.clone());
    let j2_e = and_right(j.clone(), e_a.clone());
    let j2_am = syl(&j2_e, &and_left(a_om.clone(), e_inner.clone()))?;
    let j2_ex_b = syl(&j2_e, &and_right(a_om.clone(), e_inner))?;

    let eq_p = Formula::eq(tp.clone(), pair_ab.clone());
    let j3 = Formula::and(j2.clone(), eq_p.clone());
    let j3_j2 = and_left(j2.clone(), eq_p.clone());
    let j3_eq = and_right(j2.clone(), eq_p.clone());
    let j3_j = syl(&j3_j2, &j2_j)?;
    let j3_p1 = syl(&j3_j, &j_p1)?;
    let j3_h = syl(&j3_j, &j_h)?;
    let j3_s1 = syl(&j3_j, &j_s1)?;
    let j3_s2 = syl(&j3_j, &j_s2)?;
    let j3_am = syl(&j3_j2, &j2_am)?;

    // ── `app(f₁,a) = b`, then agreement, then `app(f₂,a) = b` ────────────────
    let w1 = env.fresh_var();
    let carry1 =
        Thm::eq_leibniz(tp.clone(), pair_ab.clone(), w1, Formula::mem(Term::var(w1), tf1.clone()));
    let j3_pair1 = hyp_mp(&hyp_mp(&a1i(&carry1, j3.clone()), &j3_eq)?, &j3_p1)?;
    let j3_sv1 = syl(&j3_s1, &s1.proj(1)?)?;
    let aog1 = inst_all(&r.app_of_graph, &[tf1.clone(), ta.clone(), tb.clone()])?;
    let j3_v1 = hyp_mp(&a1i(&aog1, j3.clone()), &hyp_and(&j3_sv1, &j3_pair1)?)?;

    let agree_body = Thm::mp(&Thm::ax_inst(agree.concl().clone(), ta.clone())?, agree)?;
    let (_, agree_all) = agree_body.concl().as_imp()?;
    let agree_inst = syl(&agree_body, &inst_chain(&agree_all, &[tf1.clone(), tf2.clone()])?)?;
    let j3_agree = hyp_mp(&hyp_mp(&a1i(&agree_inst, j3.clone()), &j3_am)?, &j3_h)?;
    let j3_agrees = hyp_eq_symm(env, &j3_agree)?;
    let j3_v2 = hyp_eq_trans(env, &j3_agrees, &j3_v1)?;

    // ── Totality of `f₂` supplies a pair there, and its value must be `b` ────
    let mem_ab2 = Formula::mem(r.pair(ta.clone(), tb2.clone()), tf2.clone());
    let total2_at = Thm::ax_inst(s2.total.clone(), ta.clone())?;
    debug_assert_eq!(
        total2_at.concl().as_imp()?.1,
        Formula::imp(a_om, Formula::exists(b2, mem_ab2.clone())),
        "rec_subset: conjunct R3 has an unexpected shape"
    );
    let j3_ex_b2 = hyp_mp(&syl(&syl(&j3_s2, &s2.proj(2)?)?, &total2_at)?, &j3_am)?;

    let j4 = Formula::and(j3.clone(), mem_ab2.clone());
    let j4_j3 = and_left(j3.clone(), mem_ab2.clone());
    let j4_mem = and_right(j3.clone(), mem_ab2);
    let j4_sv2 = syl(&j4_j3, &syl(&j3_s2, &s2.proj(1)?)?)?;
    let aog2 = inst_all(&r.app_of_graph, &[tf2.clone(), ta.clone(), tb2.clone()])?;
    let j4_v2b = hyp_mp(&a1i(&aog2, j4.clone()), &hyp_and(&j4_sv2, &j4_mem)?)?;
    let j4_v2bs = hyp_eq_symm(env, &j4_v2b)?;
    let j4_rhs = syl(&j4_j3, &j3_v2)?;
    let j4_b2b = hyp_eq_trans(env, &j4_v2bs, &j4_rhs)?;

    let w2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(
        tb2,
        tb,
        w2,
        Formula::mem(r.pair(ta, Term::var(w2)), tf2.clone()),
    );
    let j4_pair2 = hyp_mp(&hyp_mp(&a1i(&carry2, j4.clone()), &j4_b2b)?, &j4_mem)?;

    let j4_eqs = hyp_eq_symm(env, &syl(&j4_j3, &j3_eq)?)?;
    let w3 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(pair_ab, tp, w3, Formula::mem(Term::var(w3), tf2));
    let j4_goal = hyp_mp(&hyp_mp(&a1i(&carry3, j4), &j4_eqs)?, &j4_pair2)?;

    let j3_goal = discharge(b2, &j3_ex_b2, &j4_goal)?;
    let j2_goal = discharge(b, &j2_ex_b, &j3_goal)?;
    let j_goal = discharge(a, &j_ex_a, &j2_goal)?;

    let out = uncurry(&j_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::imp(p_f1, p_f2)),
        "rec_subset: unexpected shape"
    );
    Some(gen_all(&[f1, f2, p], &out))
}

/// `⊢ ∀f₁ ∀f₂. ((RecFn(f₁) ∧ RecFn(f₂)) → f₁ = f₂)` — **the recursion is
/// unique**.
///
/// [`rec_subset`] in both directions, then Extensionality. `subset` must be
/// [`rec_subset`]'s theorem at the same `g` and `c`.
pub fn rec_unique(env: &mut Env, r: &Rec, g: FnSym, c: &Term, subset: &Thm) -> Option<Thm> {
    let (f1, f2, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf1, tf2, tp) = (Term::var(f1), Term::var(f2), Term::var(p));
    let s1 = rec_fn(env, r, g, c, &tf1)?;
    let s2 = rec_fn(env, r, g, c, &tf2)?;
    let (q1, q2) = (s1.formula(), s2.formula());
    let h = Formula::and(q1.clone(), q2.clone());

    let swapped = hyp_and(
        &and_right(q1.clone(), q2.clone()),
        &and_left(q1.clone(), q2.clone()),
    )?;
    let fwd = inst_all(subset, &[tf1.clone(), tf2.clone(), tp.clone()])?;
    let bwd = syl(&swapped, &inst_all(subset, &[tf2.clone(), tf1.clone(), tp.clone()])?)?;
    debug_assert_eq!(
        fwd.concl().as_imp()?.0,
        h,
        "rec_unique: rec_subset has an unexpected hypothesis"
    );

    let (p_f1, p_f2) =
        (Formula::mem(tp.clone(), tf1.clone()), Formula::mem(tp, tf2.clone()));
    let h_all = Thm::mp(
        &Thm::ax_dist(p, h.clone(), Formula::iff(p_f1, p_f2))?,
        &Thm::gen(p, &hyp_and(&fwd, &bwd)?),
    )?;
    let ext = Thm::ax_extensionality(env);
    let out = syl(&h_all, &inst_all(&ext, &[tf1.clone(), tf2.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(tf1, tf2)),
        "rec_unique: unexpected shape"
    );
    Some(gen_all(&[f1, f2], &out))
}
