//! Two approximations over the same domain are equal: agreement, then
//! inclusion.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀k. (k ∈ ω → ∀m₁ ∀h₁ ∀m₂ ∀h₂.
//!          ((m₁ ∈ ω ∧ (Approx(m₁,h₁) ∧ (m₂ ∈ ω ∧ (Approx(m₂,h₂)
//!             ∧ (k ∈ m₁ ∧ k ∈ m₂)))))
//!          → app(h₁,k) = app(h₂,k)))                              [approx_agree]
//! ⊢ ∀n. (n ∈ ω → ∀a. (a ∈ n → a ∈ ω))                             [omega_is_transitive]
//! ⊢ ∀m ∀h₁ ∀h₂ ∀p. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂)))
//!          → (p ∈ h₁ → p ∈ h₂))                                   [approx_subset]
//! ⊢ ∀m ∀h₁ ∀h₂. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂))) → h₁ = h₂)  [approx_unique]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why the three are one construction
//!
//! [`approx_subset`] **consumes the other two as arguments** — they are
//! instantiated, never rebuilt, so a mismatch surfaces as `None` — and neither
//! has any other consumer. Agreeing at every point is not yet being equal: a
//! graph could carry junk that is not a pair, or a pair over a point outside the
//! domain, and conjunct A1 of [`crate::recursion::Approx`] is what rules that
//! out. So the file is the step from "same values" to "same set", and splitting
//! it would put a lemma in one place and its only use in another.
//!
//! [`approx_agree`] is the half that carries the content, and is itself an
//! induction. The base case never touches the domain: both graphs contain
//! `⟨0,c⟩` by A4 and are single-valued by A2, so
//! [`crate::recursion::app_of_graph`] reads `c` off each. The step case is where
//! the domain is used — `succ(k) ∈ m` gives `k ∈ m`
//! ([`crate::recursion::pred_in_omega_member`]), the induction hypothesis
//! equates the two values there, and A5 turns that into equality of `G` of them.
//!
//! [`omega_is_transitive`] is distinct from
//! [`crate::recursion::omega_trans`], which says every *member* of `ω` is
//! transitive; this says `ω` itself is, and it is what lets the agreement
//! lemma — stated for `k ∈ ω` — be applied at a point of some natural `m`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_intro, and_left, and_right, com12, eq_symm_imp, gen_all, hyp_and, hyp_mp,
    hyp_or_elim, iff_mp, inst_all, mpd_const, syl, uncurry,
};
use super::induction::induction_scheme;
use super::rec::Rec;
use super::approximation::{approx, conj, conj_proj, pred_in_omega_member, Approx};
use super::hyp::{hyp_eq_symm, hyp_eq_trans, inst_chain};

/// `⊢ ∀k. (k ∈ ω → ∀m₁ ∀h₁ ∀m₂ ∀h₂. ((m₁ ∈ ω ∧ (Approx(m₁,h₁) ∧ (m₂ ∈ ω ∧
/// (Approx(m₂,h₂) ∧ (k ∈ m₁ ∧ k ∈ m₂))))) → app(h₁,k) = app(h₂,k)))` — **any two
/// approximations take the same value at every point common to their domains**.
///
/// The two domains are kept apart because the union step needs exactly that:
/// `app(f,n)` is read off the approximation with domain `succ n` and
/// `app(f,succ n)` off the one with domain `succ(succ n)`, and the step equation
/// relates them at the single point `n`. Nothing in the argument below uses the
/// domains for anything but transitivity, so separating them costs only the
/// bookkeeping.
///
/// This is the half of the uniqueness argument that carries the content, and it
/// is itself an induction. The base case never touches the domain: both graphs
/// contain `⟨0,c⟩` by A4 and are single-valued by A2, so
/// [`crate::recursion::app_of_graph`] reads `c` off each. The step case is where the domain is
/// used — `succ(k) ∈ m` gives `k ∈ m` ([`pred_in_omega_member`]), the induction
/// hypothesis then equates the two values there, and A5 turns that into
/// equality of `G` of them, which is what each graph's value at `succ(k)` is.
///
/// The hypothesis is a four-fold conjunction, associated to the right, so
/// `m ∈ ω` and the two `Approx`es are all available where the argument needs
/// them; `m ∈ ω` is what supplies transitivity.
pub fn approx_agree(env: &mut Env, r: &Rec, g: FnSym, c: &Term) -> Option<Thm> {
    let x = env.fresh_var();
    let (m1, h1, m2, h2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tm1, th1, tm2, th2) =
        (Term::var(x), Term::var(m1), Term::var(h1), Term::var(m2), Term::var(h2));

    let ax1 = approx(env, r, g, c, &tm1, &th1)?;
    let ax2 = approx(env, r, g, c, &tm2, &th2)?;
    let m1_om = Formula::mem(tm1.clone(), r.omega());
    let m2_om = Formula::mem(tm2.clone(), r.omega());
    let (f1, f2) = (ax1.formula(), ax2.formula());

    let parts_at = |t: &Term| {
        [
            m1_om.clone(),
            f1.clone(),
            m2_om.clone(),
            f2.clone(),
            Formula::mem(t.clone(), tm1.clone()),
            Formula::mem(t.clone(), tm2.clone()),
        ]
    };
    let hyp_at = |t: &Term| conj(&parts_at(t));
    let goal_at =
        |t: &Term| Formula::eq(r.apply(th1.clone(), t.clone()), r.apply(th2.clone(), t.clone()));
    let phi_at = |t: &Term| {
        Formula::forall(
            m1,
            Formula::forall(
                h1,
                Formula::forall(
                    m2,
                    Formula::forall(h2, Formula::imp(hyp_at(t), goal_at(t))),
                ),
            ),
        )
    };
    let phi = phi_at(&tx);

    // ── Base: both graphs contain `⟨0,c⟩`, so both read back `c` ─────────────
    let zero = r.zero();
    let hz = hyp_at(&zero);
    let pz = parts_at(&zero);
    let value_at = |env: &mut Env, ha: &Thm, ax: &Approx, th: &Term, pt: &Term, val: &Term| -> Option<Thm> {
        // `⊢ H → app(h, pt) = val`, given `⊢ H → Approx(m,h)` and `⊢ H → ⟨pt,val⟩ ∈ h`.
        let _ = env;
        let hyp = ha.concl().as_imp()?.0;
        let sv = syl(ha, &ax.proj(1)?)?;
        let aog = inst_all(&r.app_of_graph, &[th.clone(), pt.clone(), val.clone()])?;
        let mem = syl(ha, &ax.proj(3)?)?;
        hyp_mp(&a1i(&aog, hyp), &hyp_and(&sv, &mem)?)
    };
    let hz_ax1 = conj_proj(&pz, 1)?;
    let hz_ax2 = conj_proj(&pz, 3)?;
    let hz_app1 = value_at(env, &hz_ax1, &ax1, &th1, &zero, c)?;
    let hz_app2 = value_at(env, &hz_ax2, &ax2, &th2, &zero, c)?;
    let base_body = {
        let sym = hyp_eq_symm(env, &hz_app2)?;
        hyp_eq_trans(env, &hz_app1, &sym)?
    };
    debug_assert_eq!(*base_body.concl(), Formula::imp(hz, goal_at(&zero)));
    let base = gen_all(&[m1, h1, m2, h2], &base_body);
    debug_assert_eq!(*base.concl(), phi.subst(x, &zero), "approx_agree: the base case drifted");

    // ── Step ─────────────────────────────────────────────────────────────────
    let sx = r.succ_of(tx.clone());
    let x_om = Formula::mem(tx.clone(), r.omega());
    let k = Formula::and(x_om.clone(), phi.clone());
    let hs = hyp_at(&sx);
    let ps = parts_at(&sx);
    let j = Formula::and(k.clone(), hs.clone());

    let j_k = and_left(k.clone(), hs.clone());
    let j_hs = and_right(k.clone(), hs.clone());
    let j_phi = syl(&j_k, &and_right(x_om.clone(), phi.clone()))?;
    let j_mom1 = syl(&j_hs, &conj_proj(&ps, 0)?)?;
    let j_ax1 = syl(&j_hs, &conj_proj(&ps, 1)?)?;
    let j_mom2 = syl(&j_hs, &conj_proj(&ps, 2)?)?;
    let j_ax2 = syl(&j_hs, &conj_proj(&ps, 3)?)?;
    let j_sx_m1 = syl(&j_hs, &conj_proj(&ps, 4)?)?;
    let j_sx_m2 = syl(&j_hs, &conj_proj(&ps, 5)?)?;

    // `x ∈ m₁` and `x ∈ m₂`, from transitivity of each domain.
    let pim = pred_in_omega_member(env, r)?;
    let pred_at = |tm: &Term, j_mom: &Thm, j_sx_m: &Thm| -> Option<Thm> {
        let pim_at = inst_all(&pim, std::slice::from_ref(tm))?;
        let (_, pim_all) = pim_at.concl().as_imp()?;
        let pim_k = syl(&pim_at, &Thm::ax_inst(pim_all, tx.clone())?)?;
        hyp_mp(&hyp_mp(&a1i(&pim_k, j.clone()), j_mom)?, j_sx_m)
    };
    let j_x_m1 = pred_at(&tm1, &j_mom1, &j_sx_m1)?;
    let j_x_m2 = pred_at(&tm2, &j_mom2, &j_sx_m2)?;

    // The induction hypothesis, at this `m₁`, `h₁`, `m₂`, `h₂`.
    let j_hx = hyp_and(
        &j_mom1,
        &hyp_and(
            &j_ax1,
            &hyp_and(&j_mom2, &hyp_and(&j_ax2, &hyp_and(&j_x_m1, &j_x_m2)?)?)?,
        )?,
    )?;
    debug_assert_eq!(*j_hx.concl(), Formula::imp(j.clone(), hyp_at(&tx)));
    let ic = inst_chain(&phi, &[tm1.clone(), th1.clone(), tm2.clone(), th2.clone()])?;
    let j_ih = hyp_mp(&syl(&j_phi, &ic)?, &j_hx)?;

    // Each graph's value at `succ x` is `G` of its value at `x`.
    let v1 = Term::apply(g, vec![r.apply(th1.clone(), tx.clone())]);
    let v2 = Term::apply(g, vec![r.apply(th2.clone(), tx.clone())]);
    let succ_value = |ha: &Thm, ax: &Approx, th: &Term, val: &Term, j_sx_m: &Thm| -> Option<Thm> {
        let a5 = syl(ha, &ax.proj(4)?)?;
        let at_x = Thm::ax_inst(ax.step.clone(), tx.clone())?;
        let mem = hyp_mp(&syl(&a5, &at_x)?, j_sx_m)?;
        let sv = syl(ha, &ax.proj(1)?)?;
        let aog = inst_all(&r.app_of_graph, &[th.clone(), sx.clone(), val.clone()])?;
        hyp_mp(&a1i(&aog, j.clone()), &hyp_and(&sv, &mem)?)
    };
    let j_app1 = succ_value(&j_ax1, &ax1, &th1, &v1, &j_sx_m1)?;
    let j_app2 = succ_value(&j_ax2, &ax2, &th2, &v2, &j_sx_m2)?;

    // `G` is a function symbol, so the induction hypothesis transports.
    let w = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(
            r.apply(th1.clone(), tx.clone()),
            r.apply(th2.clone(), tx.clone()),
            w,
            Formula::eq(v1.clone(), Term::apply(g, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(v1.clone()),
    )?;
    let j_gg = syl(&j_ih, &congr)?;
    debug_assert_eq!(*j_gg.concl(), Formula::imp(j.clone(), Formula::eq(v1, v2)));

    let j_goal = {
        let left = hyp_eq_trans(env, &j_app1, &j_gg)?;
        let right = hyp_eq_symm(env, &j_app2)?;
        hyp_eq_trans(env, &left, &right)?
    };
    debug_assert_eq!(*j_goal.concl(), Formula::imp(j, goal_at(&sx)));

    // Quantify `m₁`, `h₁`, `m₂`, `h₂` back in; none of them is free in `K`.
    let step_body = uncurry(&j_goal)?;
    let mut cur = step_body;
    let mut inner = Formula::imp(hs, goal_at(&sx));
    for v in [h2, m2, h1, m1] {
        cur = Thm::mp(&Thm::ax_dist(v, k.clone(), inner.clone())?, &Thm::gen(v, &cur))?;
        inner = Formula::forall(v, inner);
    }
    let g_m = cur;
    debug_assert_eq!(
        *g_m.concl(),
        Formula::imp(Formula::and(x_om.clone(), phi.clone()), phi.subst(x, &sx)),
        "approx_agree: the step case drifted"
    );

    let scheme = induction_scheme(env, r.core(), x, &phi)?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(x, &g_m)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, Formula::imp(x_om, phi)),
        "approx_agree: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → ∀a. (a ∈ n → a ∈ ω))` — **`ω` is transitive**.
///
/// Distinct from [`crate::recursion::omega_trans`], which says every *member* of `ω` is
/// transitive; this says `ω` itself is, and it is what lets the agreement
/// lemma — stated for `k ∈ ω` — be applied at a point of some natural `m`.
/// Induction: `∅` has no members, and a member of `succ(x)` is a member of `x`
/// (induction hypothesis) or is `x` itself (which is in `ω` by the step's own
/// antecedent).
pub fn omega_is_transitive(env: &mut Env, r: &Rec) -> Option<Thm> {
    let core = r.core();
    let (x, a) = (env.fresh_var(), env.fresh_var());
    let (tx, ta) = (Term::var(x), Term::var(a));
    let om = r.omega();
    let a_om = Formula::mem(ta.clone(), om.clone());
    let phi = Formula::forall(a, Formula::imp(Formula::mem(ta.clone(), tx.clone()), a_om.clone()));

    // ── Base: nothing is in `∅` ──────────────────────────────────────────────
    let zero = r.zero();
    let not_mem = inst_all(&core.empty_ax, std::slice::from_ref(&ta))?;
    let base = Thm::gen(a, &syl(&not_mem, &crate::ex_falso(a_om.clone()))?);
    debug_assert_eq!(*base.concl(), phi.subst(x, &zero), "omega_is_transitive: base drifted");

    // ── Step ─────────────────────────────────────────────────────────────────
    let sx = r.succ_of(tx.clone());
    let x_om = Formula::mem(tx.clone(), om.clone());
    let k = Formula::and(x_om.clone(), phi.clone());
    let a_sx = Formula::mem(ta.clone(), sx.clone());
    let l = Formula::and(k.clone(), a_sx.clone());
    let l_k = and_left(k.clone(), a_sx.clone());
    let l_mem = and_right(k.clone(), a_sx.clone());

    let succ_at = inst_all(&core.succ_ax, &[tx.clone(), ta.clone()])?;
    let l_disj = syl(&l_mem, &iff_mp(&succ_at)?)?;

    let l_phi = syl(&l_k, &and_right(x_om.clone(), phi.clone()))?;
    let case_mem = syl(&l_phi, &Thm::ax_inst(phi.clone(), ta.clone())?)?;

    let l_xom = syl(&l_k, &and_left(x_om.clone(), phi.clone()))?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(tx.clone(), ta.clone(), hole, Formula::mem(Term::var(hole), om.clone()));
    let from_eq = syl(&eq_symm_imp(env, ta.clone(), tx.clone()), &leib)?;
    let case_eq = hyp_mp(&a1i(&com12(&from_eq)?, l.clone()), &l_xom)?;

    let l_goal = hyp_or_elim(&l_disj, &case_mem, &case_eq)?;
    let step_body = uncurry(&l_goal)?;
    let step = Thm::mp(&Thm::ax_dist(a, k, Formula::imp(a_sx, a_om))?, &Thm::gen(a, &step_body))?;
    debug_assert_eq!(
        *step.concl(),
        Formula::imp(Formula::and(x_om.clone(), phi.clone()), phi.subst(x, &sx)),
        "omega_is_transitive: step drifted"
    );

    let scheme = induction_scheme(env, r.core(), x, &phi)?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(x, &step)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, Formula::imp(x_om, phi)),
        "omega_is_transitive: unexpected shape"
    );
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 3b: agreement upgraded to equality.
//
// Agreeing at every point is not yet being equal: a graph could carry junk that
// is not a pair, or a pair over a point outside the domain. Conjunct A1 of
// [`Approx`] is what rules that out, and it is the only place it is used.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀m ∀h₁ ∀h₂ ∀p. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂))) → (p ∈ h₁ → p ∈ h₂))`.
///
/// One inclusion; [`approx_unique`] runs it in both directions. A member of
/// `h₁` is a pair `⟨a,b⟩` with `a ∈ m` (A1), and single-valuedness reads
/// `app(h₁,a) = b` off it. `a ∈ m ⊆ ω` ([`omega_is_transitive`]), so `agree`
/// applies and gives `app(h₂,a) = b` as well. Totality of `h₂` on `m` (A3)
/// produces *some* pair `⟨a,b′⟩ ∈ h₂`, whose value must then be `b` — so the
/// pair is `⟨a,b⟩`, which is `p`.
///
/// `agree` must be [`approx_agree`]'s theorem and `om_trans`
/// [`omega_is_transitive`]'s, at the same `g` and `c`; both are instantiated,
/// never rebuilt, so a mismatch surfaces as `None`.
pub fn approx_subset(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    agree: &Thm,
    om_trans: &Thm,
) -> Option<Thm> {
    let (m, h1, h2, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (a, b, b2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, th1, th2, tp) = (Term::var(m), Term::var(h1), Term::var(h2), Term::var(p));
    let (ta, tb, tb2) = (Term::var(a), Term::var(b), Term::var(b2));

    let ax1 = approx(env, r, g, c, &tm, &th1)?;
    let ax2 = approx(env, r, g, c, &tm, &th2)?;
    let m_om = Formula::mem(tm.clone(), r.omega());
    let hparts = [m_om.clone(), ax1.formula(), ax2.formula()];
    let h = conj(&hparts);

    let p_h1 = Formula::mem(tp.clone(), th1.clone());
    let p_h2 = Formula::mem(tp.clone(), th2.clone());
    let j = Formula::and(h.clone(), p_h1.clone());
    let j_h = and_left(h.clone(), p_h1.clone());
    let j_p1 = and_right(h.clone(), p_h1.clone());
    let j_mom = syl(&j_h, &conj_proj(&hparts, 0)?)?;
    let j_ax1 = syl(&j_h, &conj_proj(&hparts, 1)?)?;
    let j_ax2 = syl(&j_h, &conj_proj(&hparts, 2)?)?;

    // ── `p` is a pair `⟨a,b⟩` with `a ∈ m` ───────────────────────────────────
    let pair_ab = r.pair(ta.clone(), tb.clone());
    let a_m = Formula::mem(ta.clone(), tm.clone());
    let e_inner = Formula::exists(b, Formula::eq(tp.clone(), pair_ab.clone()));
    let e_a = Formula::and(a_m.clone(), e_inner.clone());
    let bounded_at_p = Thm::ax_inst(ax1.bounded.clone(), tp.clone())?;
    debug_assert_eq!(
        bounded_at_p.concl().as_imp()?.1,
        Formula::imp(p_h1.clone(), Formula::exists(a, e_a.clone())),
        "approx_subset: conjunct A1 has an unexpected shape"
    );
    let j_ex_a = hyp_mp(&syl(&syl(&j_ax1, &ax1.proj(0)?)?, &bounded_at_p)?, &j_p1)?;

    let j2 = Formula::and(j.clone(), e_a.clone());
    let j2_j = and_left(j.clone(), e_a.clone());
    let j2_e = and_right(j.clone(), e_a.clone());
    let j2_am = syl(&j2_e, &and_left(a_m.clone(), e_inner.clone()))?;
    let j2_ex_b = syl(&j2_e, &and_right(a_m.clone(), e_inner.clone()))?;

    let eq_p = Formula::eq(tp.clone(), pair_ab.clone());
    let j3 = Formula::and(j2.clone(), eq_p.clone());
    let j3_j2 = and_left(j2.clone(), eq_p.clone());
    let j3_eq = and_right(j2.clone(), eq_p.clone());
    let j3_j = syl(&j3_j2, &j2_j)?;
    let j3_p1 = syl(&j3_j, &j_p1)?;
    let j3_ax1 = syl(&j3_j, &j_ax1)?;
    let j3_ax2 = syl(&j3_j, &j_ax2)?;
    let j3_mom = syl(&j3_j, &j_mom)?;
    let j3_am = syl(&j3_j2, &j2_am)?;

    // ── `app(h₁,a) = b` ──────────────────────────────────────────────────────
    let w1 = env.fresh_var();
    let carry1 =
        Thm::eq_leibniz(tp.clone(), pair_ab.clone(), w1, Formula::mem(Term::var(w1), th1.clone()));
    let j3_pair1 = hyp_mp(&hyp_mp(&a1i(&carry1, j3.clone()), &j3_eq)?, &j3_p1)?;
    let j3_sv1 = syl(&j3_ax1, &ax1.proj(1)?)?;
    let aog1 = inst_all(&r.app_of_graph, &[th1.clone(), ta.clone(), tb.clone()])?;
    let j3_v1 = hyp_mp(&a1i(&aog1, j3.clone()), &hyp_and(&j3_sv1, &j3_pair1)?)?;

    // ── `a ∈ ω`, then agreement, then `app(h₂,a) = b` ────────────────────────
    let omt_at = inst_all(om_trans, std::slice::from_ref(&tm))?;
    let (_, omt_all) = omt_at.concl().as_imp()?;
    let omt_a = syl(&omt_at, &Thm::ax_inst(omt_all, ta.clone())?)?;
    let j3_aom = hyp_mp(&hyp_mp(&a1i(&omt_a, j3.clone()), &j3_mom)?, &j3_am)?;

    let agree_body = Thm::mp(&Thm::ax_inst(agree.concl().clone(), ta.clone())?, agree)?;
    let (_, agree_all) = agree_body.concl().as_imp()?;
    let agree_inst = syl(
        &agree_body,
        &inst_chain(&agree_all, &[tm.clone(), th1.clone(), tm.clone(), th2.clone()])?,
    )?;
    let j3_hagree = hyp_and(
        &j3_mom,
        &hyp_and(
            &j3_ax1,
            &hyp_and(&j3_mom, &hyp_and(&j3_ax2, &hyp_and(&j3_am, &j3_am)?)?)?,
        )?,
    )?;
    let j3_agree = hyp_mp(&hyp_mp(&a1i(&agree_inst, j3.clone()), &j3_aom)?, &j3_hagree)?;
    let j3_v2 = {
        let sym = hyp_eq_symm(env, &j3_agree)?;
        hyp_eq_trans(env, &sym, &j3_v1)?
    };
    debug_assert_eq!(
        *j3_v2.concl(),
        Formula::imp(j3.clone(), Formula::eq(r.apply(th2.clone(), ta.clone()), tb.clone())),
        "approx_subset: the transported value has an unexpected shape"
    );

    // ── Totality of `h₂` supplies a pair there, and its value must be `b` ────
    let mem_ab2 = Formula::mem(r.pair(ta.clone(), tb2.clone()), th2.clone());
    let total2_at = Thm::ax_inst(ax2.total.clone(), ta.clone())?;
    debug_assert_eq!(
        total2_at.concl().as_imp()?.1,
        Formula::imp(a_m.clone(), Formula::exists(b2, mem_ab2.clone())),
        "approx_subset: conjunct A3 has an unexpected shape"
    );
    let j3_ex_b2 = hyp_mp(&syl(&syl(&j3_ax2, &ax2.proj(2)?)?, &total2_at)?, &j3_am)?;

    let j4 = Formula::and(j3.clone(), mem_ab2.clone());
    let j4_j3 = and_left(j3.clone(), mem_ab2.clone());
    let j4_mem = and_right(j3.clone(), mem_ab2.clone());
    let j4_sv2 = syl(&j4_j3, &syl(&j3_ax2, &ax2.proj(1)?)?)?;
    let aog2 = inst_all(&r.app_of_graph, &[th2.clone(), ta.clone(), tb2.clone()])?;
    let j4_v2b = hyp_mp(&a1i(&aog2, j4.clone()), &hyp_and(&j4_sv2, &j4_mem)?)?;
    let j4_b2b = {
        let sym = hyp_eq_symm(env, &j4_v2b)?;
        hyp_eq_trans(env, &sym, &syl(&j4_j3, &j3_v2)?)?
    };

    let w2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(
        tb2.clone(),
        tb.clone(),
        w2,
        Formula::mem(r.pair(ta.clone(), Term::var(w2)), th2.clone()),
    );
    let j4_pair2 = hyp_mp(&hyp_mp(&a1i(&carry2, j4.clone()), &j4_b2b)?, &j4_mem)?;

    let j4_eqs = hyp_eq_symm(env, &syl(&j4_j3, &j3_eq)?)?;
    let w3 = env.fresh_var();
    let carry3 =
        Thm::eq_leibniz(pair_ab, tp.clone(), w3, Formula::mem(Term::var(w3), th2.clone()));
    let j4_goal = hyp_mp(&hyp_mp(&a1i(&carry3, j4), &j4_eqs)?, &j4_pair2)?;

    // ── Discharge the three witnesses, innermost first ───────────────────────
    let j3_goal = crate::funspace::discharge(b2, &j3_ex_b2, &j4_goal)?;
    let j2_goal = crate::funspace::discharge(b, &j2_ex_b, &j3_goal)?;
    let j_goal = crate::funspace::discharge(a, &j_ex_a, &j2_goal)?;

    let out = uncurry(&j_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::imp(p_h1, p_h2)),
        "approx_subset: unexpected shape"
    );
    Some(gen_all(&[m, h1, h2, p], &out))
}

/// `⊢ ∀m ∀h₁ ∀h₂. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂))) → h₁ = h₂)` — **an
/// approximation is determined by its domain**.
///
/// [`approx_subset`] run in both directions, which is all Extensionality needs:
/// the hypothesis is symmetric in the two graphs up to the order of two
/// conjuncts, so the second direction is the same theorem with them swapped.
///
/// `subset` must be [`approx_subset`]'s theorem at the same `g` and `c`; it is
/// instantiated, never rebuilt, so a mismatch surfaces as `None`.
pub fn approx_unique(env: &mut Env, r: &Rec, g: FnSym, c: &Term, subset: &Thm) -> Option<Thm> {
    let (m, h1, h2, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, th1, th2, tp) = (Term::var(m), Term::var(h1), Term::var(h2), Term::var(p));

    let ax1 = approx(env, r, g, c, &tm, &th1)?;
    let ax2 = approx(env, r, g, c, &tm, &th2)?;
    let (f1, f2) = (ax1.formula(), ax2.formula());
    let m_om = Formula::mem(tm.clone(), r.omega());
    let both = Formula::and(f1.clone(), f2.clone());
    let h = Formula::and(m_om.clone(), both.clone());

    // `H → (m ∈ ω ∧ (Approx(m,h₂) ∧ Approx(m,h₁)))` — the same hypothesis with
    // the two graphs exchanged, which is what the reverse inclusion wants.
    let h_mom = and_left(m_om.clone(), both.clone());
    let h_both = and_right(m_om.clone(), both.clone());
    let swapped = hyp_and(
        &h_mom,
        &hyp_and(
            &syl(&h_both, &and_right(f1.clone(), f2.clone()))?,
            &syl(&h_both, &and_left(f1.clone(), f2.clone()))?,
        )?,
    )?;

    let fwd = inst_all(subset, &[tm.clone(), th1.clone(), th2.clone(), tp.clone()])?;
    let bwd = syl(&swapped, &inst_all(subset, &[tm, th2.clone(), th1.clone(), tp])?)?;
    debug_assert_eq!(fwd.concl().as_imp()?.0, h, "approx_unique: approx_subset has an unexpected hypothesis");

    let (p_h1, p_h2) =
        (Formula::mem(Term::var(p), th1.clone()), Formula::mem(Term::var(p), th2.clone()));
    let h_iff = hyp_and(&fwd, &bwd)?;
    let h_all = Thm::mp(
        &Thm::ax_dist(p, h.clone(), Formula::iff(p_h1, p_h2))?,
        &Thm::gen(p, &h_iff),
    )?;
    let ext = Thm::ax_extensionality(env);
    let out = syl(&h_all, &inst_all(&ext, &[th1.clone(), th2.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(th1, th2)),
        "approx_unique: unexpected shape"
    );
    Some(gen_all(&[m, h1, h2], &out))
}
