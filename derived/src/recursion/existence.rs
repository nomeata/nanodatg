//! For every natural `n` there is an approximation with domain `succ n`.
//!
//! # Interface
//!
//! ```text
//! ⊢ Approx(succ 0, {⟨0,c⟩})                                    [approx_one]
//! ⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n, h))
//!            → Approx(succ(succ n), h ∪ {⟨succ n, G(app(h,n))⟩}))   [approx_extend]
//! ⊢ ∀n. (n ∈ ω → ∃h. Approx(succ n, h))                        [approx_exists]
//! ```
//!
//! Callers need only the last; the two before it are the base and the step of
//! its induction, exported because each is worth pinning on its own.
//!
//! # Why the family is indexed by `succ n` rather than `n`
//!
//! Conjunct A4 of [`crate::recursion::Approx`] asserts `⟨0,c⟩ ∈ h`
//! *unconditionally*, so `Approx(0,h)` is contradictory: A1 would put `0` in the
//! empty domain. Running the induction one step up removes the empty
//! approximation from the family altogether, and with it the case split that
//! would otherwise appear in every clause below.
//!
//! # What the step actually costs
//!
//! Extending `h` by the single pair `⟨succ n, G(app(h,n))⟩` re-establishes all
//! five conjuncts, and only two of them are bookkeeping:
//!
//! * **A2**, single-valuedness, is where `succ(n) ∉ succ(n)`
//!   ([`crate::recursion::Peano::no_self_mem`]) is spent: the new point must be
//!   absent from the old graph, and what is known about it is that it is not in
//!   the old *domain* — [`crate::recursion::approx_dom`] is the bridge;
//! * **A5** needs the extension to take the *same values as `h`* below the new
//!   point — the value lemma inside [`approx_extend`] — without which the step
//!   equation of the extension would not follow from the step equation of `h`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{hyp_syl, or_intro_left, or_intro_right};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, ex_falso, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, inst_all, mpd_const, singleton, syl,
    uncurry,
};
use super::adjoin::{adjoin, mem_adjoin};
use super::approximation::{approx, pred_in_omega_member};
use super::hyp::{hyp_eq_symm, hyp_eq_trans, inst_chain};
use super::peano::mem_succ_self;
use super::rec::Rec;

/// `⊢ Approx(succ 0, {⟨0,c⟩})` — the one-point graph is an approximation over
/// the one-point domain.
///
/// A1 and A3 both come down to `succ 0` having `0` as its only member, A2 to
/// injectivity of the pair, and A4 to reflexivity. A5 is *vacuous*: a successor
/// in `succ 0` would have to be `0`, and `succ k = 0` puts `k` in `∅`.
pub fn approx_one(env: &mut Env, r: &Rec, g: FnSym, c: &Term) -> Option<Thm> {
    let core = r.core();
    let (zero, s0) = (r.zero(), r.succ_of(r.zero()));
    let p0 = r.pair(zero.clone(), c.clone());
    let h0 = singleton(r.ap.sets.up, p0.clone());
    let ax = approx(env, r, g, c, &s0, &h0)?;

    let mem_h0 = |t: &Term| inst_all(&r.ap.mem_sing, &[p0.clone(), t.clone()]);
    let zero_in_s0 = mem_succ_self(core, &zero)?;

    // ── A4: `⟨0,c⟩ ∈ {⟨0,c⟩}` ────────────────────────────────────────────────
    let base = Thm::mp(&iff_mpr(&mem_h0(&p0)?)?, &Thm::eq_refl(p0.clone()))?;
    debug_assert_eq!(*base.concl(), ax.base, "approx_one: A4 drifted");

    // ── A1: the only member is a pair over `0`, and `0 ∈ succ 0` ─────────────
    let (p, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, ta, tb) = (Term::var(p), Term::var(a), Term::var(b));
    let e_b = Formula::eq(tp.clone(), r.pair(ta.clone(), tb.clone()));
    let e_a = Formula::and(Formula::mem(ta, s0.clone()), Formula::exists(b, e_b));
    let eq_p0 = Formula::eq(tp.clone(), p0.clone());
    let ex_b = exists_intro_imp(b, Formula::eq(tp.clone(), r.pair(zero.clone(), tb)), c.clone())?;
    let witnessed = hyp_and(&a1i(&zero_in_s0, eq_p0.clone()), &ex_b)?;
    let ex_a = exists_intro_imp(a, e_a, zero.clone())?;
    let bounded_body = syl(&iff_mp(&mem_h0(&tp)?)?, &syl(&witnessed, &ex_a)?)?;
    let bounded = Thm::gen(p, &bounded_body);
    debug_assert_eq!(*bounded.concl(), ax.bounded, "approx_one: A1 drifted");

    // ── A2: both pairs are `⟨0,c⟩`, so both second components are `c` ────────
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));
    let mem1 = Formula::mem(r.pair(tx.clone(), ty.clone()), h0.clone());
    let mem2 = Formula::mem(r.pair(tx.clone(), ty2.clone()), h0.clone());
    let hy = Formula::and(mem1.clone(), mem2.clone());
    let second = |proj: &Thm, t: &Term| -> Option<Thm> {
        let pinj = inst_all(&r.ap.pair_inj, &[tx.clone(), t.clone(), zero.clone(), c.clone()])?;
        let components = syl(&iff_mp(&mem_h0(&r.pair(tx.clone(), t.clone()))?)?, &pinj)?;
        let value = syl(
            &components,
            &and_right(Formula::eq(tx.clone(), zero.clone()), Formula::eq(t.clone(), c.clone())),
        )?;
        syl(proj, &value)
    };
    let y_c = second(&and_left(mem1.clone(), mem2.clone()), &ty)?;
    let y2_c = second(&and_right(mem1, mem2), &ty2)?;
    let y2_sym = hyp_eq_symm(env, &y2_c)?;
    let single_body = hyp_eq_trans(env, &y_c, &y2_sym)?;
    debug_assert_eq!(*single_body.concl(), Formula::imp(hy, Formula::eq(ty, ty2)));
    let single = gen_all(&[x, y, y2], &single_body);
    debug_assert_eq!(*single.concl(), ax.single, "approx_one: A2 drifted");

    // ── A3: the only member of `succ 0` is `0`, and `⟨0,c⟩` is there ─────────
    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let (ta3, tb3) = (Term::var(a3), Term::var(b3));
    let a_s0 = Formula::mem(ta3.clone(), s0.clone());
    let goal3 = Formula::exists(b3, Formula::mem(r.pair(ta3.clone(), tb3.clone()), h0.clone()));
    let disj3 = iff_mp(&inst_all(&core.succ_ax, &[zero.clone(), ta3.clone()])?)?;
    let case_in_zero = a1i(
        &syl(&inst_all(&core.empty_ax, std::slice::from_ref(&ta3))?, &ex_falso(goal3.clone()))?,
        a_s0.clone(),
    );
    let w3 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(
        zero.clone(),
        ta3.clone(),
        w3,
        Formula::mem(r.pair(Term::var(w3), c.clone()), h0.clone()),
    );
    let from_eq = syl(
        &eq_symm_imp(env, ta3.clone(), zero.clone()),
        &syl(&carry3, &crate::imp_mono_r(&exists_intro_imp(b3, Formula::mem(r.pair(ta3.clone(), tb3), h0.clone()), c.clone())?, ax.base.clone())?)?,
    )?;
    let case_eq = a1i(&mpd_const(&from_eq, &base)?, a_s0.clone());
    let total_body = hyp_or_elim(&disj3, &case_in_zero, &case_eq)?;
    debug_assert_eq!(*total_body.concl(), Formula::imp(a_s0, goal3));
    let total = Thm::gen(a3, &total_body);
    debug_assert_eq!(*total.concl(), ax.total, "approx_one: A3 drifted");

    // ── A5: no successor lies in `succ 0` ────────────────────────────────────
    let k = env.fresh_var();
    let tk = Term::var(k);
    let sk = r.succ_of(tk.clone());
    let sk_s0 = Formula::mem(sk.clone(), s0.clone());
    let goal5 = Formula::mem(
        r.pair(sk.clone(), Term::apply(g, vec![r.apply(h0.clone(), tk.clone())])),
        h0.clone(),
    );
    let disj5 = iff_mp(&inst_all(&core.succ_ax, &[zero.clone(), sk.clone()])?)?;
    let empty5 = |t: &Term| -> Option<Thm> {
        syl(&inst_all(&core.empty_ax, std::slice::from_ref(t))?, &ex_falso(goal5.clone()))
    };
    let case5_mem = a1i(&empty5(&sk)?, sk_s0.clone());
    let w5 = env.fresh_var();
    let carry5 =
        Thm::eq_leibniz(sk.clone(), zero.clone(), w5, Formula::mem(tk.clone(), Term::var(w5)));
    let case5_eq = a1i(
        &syl(&mpd_const(&carry5, &mem_succ_self(core, &tk)?)?, &empty5(&tk)?)?,
        sk_s0.clone(),
    );
    let step_body = hyp_or_elim(&disj5, &case5_mem, &case5_eq)?;
    debug_assert_eq!(*step_body.concl(), Formula::imp(sk_s0, goal5));
    let step = Thm::gen(k, &step_body);
    debug_assert_eq!(*step.concl(), ax.step, "approx_one: A5 drifted");

    let out = and_intro(
        &bounded,
        &and_intro(&single, &and_intro(&total, &and_intro(&base, &step))),
    );
    debug_assert_eq!(*out.concl(), ax.formula(), "approx_one: unexpected shape");
    Some(out)
}

/// The graph the base case runs on: `{⟨0,c⟩}`.
pub fn one_point_graph(r: &Rec, c: &Term) -> Term {
    singleton(r.ap.sets.up, r.pair(r.zero(), c.clone()))
}

/// The extension of `h` at `succ n`: `h ∪ {⟨succ n, G(app(h,n))⟩}`.
pub fn extension(r: &Rec, g: FnSym, n: &Term, h: &Term) -> Term {
    let value = Term::apply(g, vec![r.apply(h.clone(), n.clone())]);
    adjoin(&r.ap.sets, h.clone(), r.pair(r.succ_of(n.clone()), value))
}

/// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n, h)) → Approx(succ(succ n), h ∪ {⟨succ n, G(app(h,n))⟩}))`
/// — **one more step of the recursion extends an approximation**.
///
/// `dom` must be [`crate::recursion::approx_dom`]'s theorem and `om_trans`
/// [`crate::recursion::omega_is_transitive`]'s, both at the same `g` and `c`;
/// they are instantiated, never rebuilt, so a mismatch surfaces as `None`.
///
/// The five conjuncts are re-established in the order A1, A2, A3, A4, A5,
/// because A5 needs A2 twice over: once for the value lemma below, which says
/// the extension agrees with `h` below the new point, and once to read the new
/// value back off the graph.
pub fn approx_extend(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    dom: &Thm,
    om_trans: &Thm,
) -> Option<Thm> {
    let core = r.core();
    let sets = r.ap.sets.clone();
    let (n, h) = (env.fresh_var(), env.fresh_var());
    let (tn, th) = (Term::var(n), Term::var(h));
    let sn = r.succ_of(tn.clone());
    let ssn = r.succ_of(sn.clone());
    let val = Term::apply(g, vec![r.apply(th.clone(), tn.clone())]);
    let e = r.pair(sn.clone(), val.clone());
    let hp = adjoin(&sets, th.clone(), e.clone());

    let axh = approx(env, r, g, c, &sn, &th)?;
    let axp = approx(env, r, g, c, &ssn, &hp)?;
    let n_om = Formula::mem(tn.clone(), r.omega());
    let fh = axh.formula();
    let hyp = Formula::and(n_om.clone(), fh.clone());

    let h_n = and_left(n_om.clone(), fh.clone());
    let h_ax = and_right(n_om.clone(), fh.clone());
    let h_a1 = syl(&h_ax, &axh.proj(0)?)?;
    let h_a2 = syl(&h_ax, &axh.proj(1)?)?;
    let h_a3 = syl(&h_ax, &axh.proj(2)?)?;
    let h_a4 = syl(&h_ax, &axh.proj(3)?)?;
    let h_a5 = syl(&h_ax, &axh.proj(4)?)?;
    let succ_om = |t: &Term| inst_all(&core.succ_closed, std::slice::from_ref(t));
    let h_sn_om = hyp_mp(&a1i(&succ_om(&tn)?, hyp.clone()), &h_n)?;
    let h_ssn_om = hyp_mp(&a1i(&succ_om(&sn)?, hyp.clone()), &h_sn_om)?;

    // ── The two membership splits everything below runs on ───────────────────
    let ma = mem_adjoin(env, &sets, &r.ap.mem_sing)?;
    let ma_at = |z: &Term| inst_all(&ma, &[th.clone(), e.clone(), z.clone()]);
    let into_h = |z: &Term| -> Option<Thm> {
        syl(
            &or_intro_left(Formula::mem(z.clone(), th.clone()), Formula::eq(z.clone(), e.clone())),
            &iff_mpr(&ma_at(z)?)?,
        )
    };
    let e_in_hp = {
        let disj = Thm::mp(
            &or_intro_right(Formula::mem(e.clone(), th.clone()), Formula::eq(e.clone(), e.clone())),
            &Thm::eq_refl(e.clone()),
        )?;
        Thm::mp(&iff_mpr(&ma_at(&e)?)?, &disj)?
    };
    let succ_in = |m: &Term, z: &Term| -> Option<Thm> {
        syl(
            &or_intro_left(Formula::mem(z.clone(), m.clone()), Formula::eq(z.clone(), m.clone())),
            &iff_mpr(&inst_all(&core.succ_ax, &[m.clone(), z.clone()])?)?,
        )
    };
    let succ_out = |m: &Term, z: &Term| iff_mp(&inst_all(&core.succ_ax, &[m.clone(), z.clone()])?);

    // ── A1: every member is a pair over `succ(succ n)` ───────────────────────
    let (vp, va, vb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, ta, tb) = (Term::var(vp), Term::var(va), Term::var(vb));
    let ex_b_of = |first: &Term| Formula::exists(vb, Formula::eq(tp.clone(), r.pair(first.clone(), tb.clone())));
    let inner_ssn = Formula::and(Formula::mem(ta.clone(), ssn.clone()), ex_b_of(&ta));
    let goal1 = Formula::exists(va, inner_ssn.clone());
    let p_hp = Formula::mem(tp.clone(), hp.clone());

    let weaken_body = hyp_and(
        &syl(&and_left(Formula::mem(ta.clone(), sn.clone()), ex_b_of(&ta)), &succ_in(&sn, &ta)?)?,
        &and_right(Formula::mem(ta.clone(), sn.clone()), ex_b_of(&ta)),
    )?;
    let weaken = crate::exists_mono(va, &Thm::gen(va, &weaken_body))?;
    let bh_at = Thm::ax_inst(axh.bounded.clone(), tp.clone())?;
    let from_a1 = syl(
        &bh_at,
        &crate::imp_mono_r(&weaken, Formula::mem(tp.clone(), th.clone()))?,
    )?;

    let j1 = Formula::and(hyp.clone(), p_hp.clone());
    let j1_h = and_left(hyp.clone(), p_hp.clone());
    let j1_disj = syl(&and_right(hyp.clone(), p_hp.clone()), &iff_mp(&ma_at(&tp)?)?)?;
    let j1_case_h = syl(&j1_h, &syl(&h_a1, &from_a1)?)?;
    let eq_pe = Formula::eq(tp.clone(), e.clone());
    let witnessed = hyp_and(
        &a1i(&mem_succ_self(core, &sn)?, eq_pe.clone()),
        &exists_intro_imp(vb, Formula::eq(tp.clone(), r.pair(sn.clone(), tb.clone())), val.clone())?,
    )?;
    let j1_case_e = a1i(
        &syl(&witnessed, &exists_intro_imp(va, inner_ssn.clone(), sn.clone())?)?,
        j1.clone(),
    );
    let j1_goal = hyp_or_elim(&j1_disj, &j1_case_h, &j1_case_e)?;
    let h_bounded = Thm::mp(
        &Thm::ax_dist(vp, hyp.clone(), Formula::imp(p_hp, goal1))?,
        &Thm::gen(vp, &uncurry(&j1_goal)?),
    )?;
    debug_assert_eq!(
        *h_bounded.concl(),
        Formula::imp(hyp.clone(), axp.bounded.clone()),
        "approx_extend: A1 drifted"
    );

    // ── A2: single-valued, which is where `succ n ∉ succ n` is spent ─────────
    let (vx, vy, vy2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(vx), Term::var(vy), Term::var(vy2));
    let pxy = r.pair(tx.clone(), ty.clone());
    let pxy2 = r.pair(tx.clone(), ty2.clone());
    let m1 = Formula::mem(pxy.clone(), hp.clone());
    let m2 = Formula::mem(pxy2.clone(), hp.clone());
    let mm = Formula::and(m1.clone(), m2.clone());
    let goal2 = Formula::eq(ty.clone(), ty2.clone());
    let in1 = Formula::mem(pxy.clone(), th.clone());
    let eq1 = Formula::eq(pxy.clone(), e.clone());
    let in2 = Formula::mem(pxy2.clone(), th.clone());
    let eq2 = Formula::eq(pxy2.clone(), e.clone());

    let jj = Formula::and(hyp.clone(), mm.clone());
    let jj_hyp = and_left(hyp.clone(), mm.clone());
    let jj_mm = and_right(hyp.clone(), mm.clone());
    let jj_d1 = syl(&syl(&jj_mm, &and_left(m1.clone(), m2.clone()))?, &iff_mp(&ma_at(&pxy)?)?)?;
    let jj_d2 = syl(&syl(&jj_mm, &and_right(m1.clone(), m2.clone()))?, &iff_mp(&ma_at(&pxy2)?)?)?;

    let components = |t: &Term| inst_all(&r.ap.pair_inj, &[tx.clone(), t.clone(), sn.clone(), val.clone()]);
    let fst_sn = |t: &Term| -> Option<Thm> {
        syl(
            &components(t)?,
            &and_left(Formula::eq(tx.clone(), sn.clone()), Formula::eq(t.clone(), val.clone())),
        )
    };
    let snd_val = |t: &Term| -> Option<Thm> {
        syl(
            &components(t)?,
            &and_right(Formula::eq(tx.clone(), sn.clone()), Formula::eq(t.clone(), val.clone())),
        )
    };

    // `L → ⊥` from `L → x = succ n` together with `L → ⟨x,t⟩ ∈ h`: the domain
    // of `h` is `succ n`, and `succ n ∉ succ n`.
    let clash = |env: &mut Env, l: &Formula, l_eq: &Thm, l_axh: &Thm, l_mem: &Thm, t: &Term| -> Option<Thm> {
        let dom_at = inst_all(dom, &[sn.clone(), th.clone(), tx.clone(), t.clone()])?;
        let l_xsn = hyp_mp(&a1i(&dom_at, l.clone()), &hyp_and(l_axh, l_mem)?)?;
        let w = env.fresh_var();
        let leib = Thm::eq_leibniz(
            tx.clone(),
            sn.clone(),
            w,
            Formula::mem(Term::var(w), sn.clone()),
        );
        let l_ss = hyp_mp(&hyp_mp(&a1i(&leib, l.clone()), l_eq)?, &l_xsn)?;
        let l_false = hyp_mp(
            &a1i(&inst_all(&r.peano.no_self_mem, std::slice::from_ref(&sn))?, l.clone()),
            &l_ss,
        )?;
        syl(&l_false, &ex_falso(goal2.clone()))
    };

    // Left branch: the first pair was already in `h`.
    let l1 = Formula::and(jj.clone(), in1.clone());
    let l1_jj = and_left(jj.clone(), in1.clone());
    let l1_in1 = and_right(jj.clone(), in1.clone());
    let l1_hyp = syl(&l1_jj, &jj_hyp)?;
    let l1_axh = syl(&l1_hyp, &h_ax)?;
    let sv_at = inst_chain(&axh.single, &[tx.clone(), ty.clone(), ty2.clone()])?;
    let l1_sv = syl(&l1_hyp, &syl(&h_a2, &sv_at)?)?;
    let l1_pair = hyp_mp(&a1i(&crate::and_intro_imp(in1.clone(), in2.clone()), l1.clone()), &l1_in1)?;
    let l1_case_h = hyp_syl(&l1_pair, &l1_sv)?;

    let l1e = Formula::and(l1.clone(), eq2.clone());
    let l1e_l1 = and_left(l1.clone(), eq2.clone());
    let l1e_eq = syl(&and_right(l1.clone(), eq2.clone()), &fst_sn(&ty2)?)?;
    let l1e_axh = syl(&l1e_l1, &l1_axh)?;
    let l1e_mem = syl(&l1e_l1, &l1_in1)?;
    let l1e_goal = clash(env, &l1e, &l1e_eq, &l1e_axh, &l1e_mem, &ty)?;
    let l1_case_e = uncurry(&l1e_goal)?;
    let l1_goal = hyp_or_elim(&syl(&l1_jj, &jj_d2)?, &l1_case_h, &l1_case_e)?;
    let jj_case_in1 = uncurry(&l1_goal)?;

    // Right branch: the first pair is the new one, so `x = succ n`.
    let l2 = Formula::and(jj.clone(), eq1.clone());
    let l2_jj = and_left(jj.clone(), eq1.clone());
    let l2_eq1 = and_right(jj.clone(), eq1.clone());
    let l2_xsn = syl(&l2_eq1, &fst_sn(&ty)?)?;
    let l2_yval = syl(&l2_eq1, &snd_val(&ty)?)?;
    let l2_hyp = syl(&l2_jj, &jj_hyp)?;
    let l2_axh = syl(&l2_hyp, &h_ax)?;

    let l2i = Formula::and(l2.clone(), in2.clone());
    let l2i_l2 = and_left(l2.clone(), in2.clone());
    let l2i_eq = syl(&l2i_l2, &l2_xsn)?;
    let l2i_axh = syl(&l2i_l2, &l2_axh)?;
    let l2i_mem = and_right(l2.clone(), in2.clone());
    let l2i_goal = clash(env, &l2i, &l2i_eq, &l2i_axh, &l2i_mem, &ty2)?;
    let l2_case_h = uncurry(&l2i_goal)?;

    let l2e_y = syl(&and_left(l2.clone(), eq2.clone()), &l2_yval)?;
    let l2e_y2 = syl(&and_right(l2.clone(), eq2.clone()), &snd_val(&ty2)?)?;
    let l2e_y2s = hyp_eq_symm(env, &l2e_y2)?;
    let l2e_goal = hyp_eq_trans(env, &l2e_y, &l2e_y2s)?;
    let l2_case_e = uncurry(&l2e_goal)?;
    let l2_goal = hyp_or_elim(&syl(&l2_jj, &jj_d2)?, &l2_case_h, &l2_case_e)?;
    let jj_case_eq1 = uncurry(&l2_goal)?;

    let jj_goal = hyp_or_elim(&jj_d1, &jj_case_in1, &jj_case_eq1)?;
    let mut cur = uncurry(&jj_goal)?;
    let mut inner = Formula::imp(mm.clone(), goal2.clone());
    for v in [vy2, vy, vx] {
        cur = Thm::mp(&Thm::ax_dist(v, hyp.clone(), inner.clone())?, &Thm::gen(v, &cur))?;
        inner = Formula::forall(v, inner);
    }
    let h_single = cur;
    debug_assert_eq!(
        *h_single.concl(),
        Formula::imp(hyp.clone(), axp.single.clone()),
        "approx_extend: A2 drifted"
    );

    // ── The extension takes the same values as `h` below the new point ───────
    let (vk, vbv) = (env.fresh_var(), env.fresh_var());
    let (tk, tbv) = (Term::var(vk), Term::var(vbv));
    let k_sn = Formula::mem(tk.clone(), sn.clone());
    let q = Formula::and(hyp.clone(), k_sn.clone());
    let q_hyp = and_left(hyp.clone(), k_sn.clone());
    let q_ksn = and_right(hyp.clone(), k_sn.clone());
    let a3_at_k = Thm::ax_inst(axh.total.clone(), tk.clone())?;
    let q_ex = hyp_mp(&syl(&q_hyp, &syl(&h_a3, &a3_at_k)?)?, &q_ksn)?;

    let mem_kb = Formula::mem(r.pair(tk.clone(), tbv.clone()), th.clone());
    let sq = Formula::and(q.clone(), mem_kb.clone());
    let sq_q = and_left(q.clone(), mem_kb.clone());
    let sq_mem = and_right(q.clone(), mem_kb.clone());
    let sq_hyp = syl(&sq_q, &q_hyp)?;
    let aog_h = inst_all(&r.app_of_graph, &[th.clone(), tk.clone(), tbv.clone()])?;
    let sq_v_h = hyp_mp(
        &a1i(&aog_h, sq.clone()),
        &hyp_and(&syl(&sq_hyp, &h_a2)?, &sq_mem)?,
    )?;
    let aog_hp = inst_all(&r.app_of_graph, &[hp.clone(), tk.clone(), tbv.clone()])?;
    let sq_v_hp = hyp_mp(
        &a1i(&aog_hp, sq.clone()),
        &hyp_and(&syl(&sq_hyp, &h_single)?, &syl(&sq_mem, &into_h(&r.pair(tk.clone(), tbv.clone()))?)?)?,
    )?;
    let sq_v_hs = hyp_eq_symm(env, &sq_v_h)?;
    let sq_goal = hyp_eq_trans(env, &sq_v_hp, &sq_v_hs)?;
    let q_goal = crate::funspace::discharge(vbv, &q_ex, &sq_goal)?;
    debug_assert_eq!(
        *q_goal.concl(),
        Formula::imp(q, Formula::eq(r.apply(hp.clone(), tk.clone()), r.apply(th.clone(), tk.clone()))),
        "approx_extend: the value lemma drifted"
    );
    let value_all = Thm::gen(vk, &q_goal);

    // ── A3: total on `succ(succ n)` ──────────────────────────────────────────
    let (va3, vb3) = (env.fresh_var(), env.fresh_var());
    let (ta3, tb3) = (Term::var(va3), Term::var(vb3));
    let a_ssn = Formula::mem(ta3.clone(), ssn.clone());
    let goal3 = Formula::exists(vb3, Formula::mem(r.pair(ta3.clone(), tb3.clone()), hp.clone()));
    let j3 = Formula::and(hyp.clone(), a_ssn.clone());
    let j3_disj = syl(&and_right(hyp.clone(), a_ssn.clone()), &succ_out(&sn, &ta3)?)?;
    let lift = crate::exists_mono(vb3, &Thm::gen(vb3, &into_h(&r.pair(ta3.clone(), tb3.clone()))?))?;
    let a3_at = Thm::ax_inst(axh.total.clone(), ta3.clone())?;
    let j3_case_in = syl(
        &and_left(hyp.clone(), a_ssn.clone()),
        &syl(
            &h_a3,
            &syl(&a3_at, &crate::imp_mono_r(&lift, Formula::mem(ta3.clone(), sn.clone()))?)?,
        )?,
    )?;
    let w3 = env.fresh_var();
    let leib3 = Thm::eq_leibniz(
        sn.clone(),
        ta3.clone(),
        w3,
        Formula::mem(r.pair(Term::var(w3), val.clone()), hp.clone()),
    );
    let from_eq3 = syl(&eq_symm_imp(env, ta3.clone(), sn.clone()), &leib3)?;
    let intro3 = exists_intro_imp(
        vb3,
        Formula::mem(r.pair(ta3.clone(), tb3.clone()), hp.clone()),
        val.clone(),
    )?;
    let j3_case_eq = a1i(&syl(&mpd_const(&from_eq3, &e_in_hp)?, &intro3)?, j3.clone());
    let j3_goal = hyp_or_elim(&j3_disj, &j3_case_in, &j3_case_eq)?;
    let h_total = Thm::mp(
        &Thm::ax_dist(va3, hyp.clone(), Formula::imp(a_ssn, goal3))?,
        &Thm::gen(va3, &uncurry(&j3_goal)?),
    )?;
    debug_assert_eq!(
        *h_total.concl(),
        Formula::imp(hyp.clone(), axp.total.clone()),
        "approx_extend: A3 drifted"
    );

    // ── A4: the base pair survives the extension ─────────────────────────────
    let h_base = syl(&h_a4, &into_h(&r.pair(r.zero(), c.clone()))?)?;
    debug_assert_eq!(
        *h_base.concl(),
        Formula::imp(hyp.clone(), axp.base.clone()),
        "approx_extend: A4 drifted"
    );

    // ── A5: the step equation, at the old points and at the new one ──────────
    let (vk5, w5) = (env.fresh_var(), env.fresh_var());
    let tk5 = Term::var(vk5);
    let sk5 = r.succ_of(tk5.clone());
    let g_of = |t: Term| Term::apply(g, vec![t]);
    let goal5 = Formula::mem(r.pair(sk5.clone(), g_of(r.apply(hp.clone(), tk5.clone()))), hp.clone());
    let sk_ssn = Formula::mem(sk5.clone(), ssn.clone());
    let j5 = Formula::and(hyp.clone(), sk_ssn.clone());
    let j5_hyp = and_left(hyp.clone(), sk_ssn.clone());
    let j5_mem = and_right(hyp.clone(), sk_ssn.clone());
    let j5_disj = syl(&j5_mem, &succ_out(&sn, &sk5)?)?;

    let pim = pred_in_omega_member(env, r)?;
    let pred_in = |m: &Term| -> Option<Thm> {
        let at_m = inst_all(&pim, std::slice::from_ref(m))?;
        let (_, body) = at_m.concl().as_imp()?;
        syl(&at_m, &Thm::ax_inst(body, tk5.clone())?)
    };
    let congr = |env: &mut Env, u: &Term, v: &Term| -> Option<Thm> {
        let w = env.fresh_var();
        mpd_const(
            &Thm::eq_leibniz(u.clone(), v.clone(), w, Formula::eq(g_of(u.clone()), g_of(Term::var(w)))),
            &Thm::eq_refl(g_of(u.clone())),
        )
    };

    // Case `succ k ∈ succ n`: the pair is already in `h`, at the same value.
    let sk_sn = Formula::mem(sk5.clone(), sn.clone());
    let l5 = Formula::and(j5.clone(), sk_sn.clone());
    let l5_j5 = and_left(j5.clone(), sk_sn.clone());
    let l5_mem = and_right(j5.clone(), sk_sn.clone());
    let l5_hyp = syl(&l5_j5, &j5_hyp)?;
    let l5_ksn = hyp_mp(
        &hyp_mp(&a1i(&pred_in(&sn)?, l5.clone()), &syl(&l5_hyp, &h_sn_om)?)?,
        &l5_mem,
    )?;
    let value_at_k = Thm::mp(&Thm::ax_inst(value_all.concl().clone(), tk5.clone())?, &value_all)?;
    let l5_v = hyp_mp(&a1i(&value_at_k, l5.clone()), &hyp_and(&l5_hyp, &l5_ksn)?)?;
    let cg = congr(env, &r.apply(hp.clone(), tk5.clone()), &r.apply(th.clone(), tk5.clone()))?;
    let l5_gg = syl(&l5_v, &cg)?;
    let l5_ggs = hyp_eq_symm(env, &l5_gg)?;
    let a5_at = Thm::ax_inst(axh.step.clone(), tk5.clone())?;
    let old_pair = r.pair(sk5.clone(), g_of(r.apply(th.clone(), tk5.clone())));
    let l5_pair = hyp_mp(&syl(&l5_hyp, &syl(&h_a5, &a5_at)?)?, &l5_mem)?;
    let l5_pair_hp = syl(&l5_pair, &into_h(&old_pair)?)?;
    let leib5 = Thm::eq_leibniz(
        g_of(r.apply(th.clone(), tk5.clone())),
        g_of(r.apply(hp.clone(), tk5.clone())),
        w5,
        Formula::mem(r.pair(sk5.clone(), Term::var(w5)), hp.clone()),
    );
    let l5_goal = hyp_mp(&hyp_mp(&a1i(&leib5, l5.clone()), &l5_ggs)?, &l5_pair_hp)?;
    let j5_case_in = uncurry(&l5_goal)?;

    // Case `succ k = succ n`: `k = n`, and the new pair is exactly the value.
    let sk_eq = Formula::eq(sk5.clone(), sn.clone());
    let l6 = Formula::and(j5.clone(), sk_eq.clone());
    let l6_j5 = and_left(j5.clone(), sk_eq.clone());
    let l6_eq = and_right(j5.clone(), sk_eq.clone());
    let l6_hyp = syl(&l6_j5, &j5_hyp)?;
    let l6_ssn_om = syl(&l6_hyp, &h_ssn_om)?;
    let l6_k_ssn = hyp_mp(
        &hyp_mp(&a1i(&pred_in(&ssn)?, l6.clone()), &l6_ssn_om)?,
        &syl(&l6_j5, &j5_mem)?,
    )?;
    let omt_at = inst_all(om_trans, std::slice::from_ref(&ssn))?;
    let (_, omt_body) = omt_at.concl().as_imp()?;
    let omt_k = syl(&omt_at, &Thm::ax_inst(omt_body, tk5.clone())?)?;
    let l6_k_om = hyp_mp(&hyp_mp(&a1i(&omt_k, l6.clone()), &l6_ssn_om)?, &l6_k_ssn)?;
    let inj_at = inst_all(&r.peano.succ_inj, &[tk5.clone(), tn.clone()])?;
    let l6_kn = hyp_mp(
        &hyp_mp(&a1i(&inj_at, l6.clone()), &hyp_and(&l6_k_om, &syl(&l6_hyp, &h_n)?)?)?,
        &l6_eq,
    )?;
    let value_at_n = Thm::mp(&Thm::ax_inst(value_all.concl().clone(), tn.clone())?, &value_all)?;
    let l6_vn = hyp_mp(
        &a1i(&value_at_n, l6.clone()),
        &hyp_and(&l6_hyp, &a1i(&mem_succ_self(core, &tn)?, l6.clone()))?,
    )?;
    let l6_vns = hyp_eq_symm(env, &l6_vn)?;
    let w6 = env.fresh_var();
    let leib6 = Thm::eq_leibniz(
        r.apply(th.clone(), tn.clone()),
        r.apply(hp.clone(), tn.clone()),
        w6,
        Formula::mem(r.pair(sn.clone(), g_of(Term::var(w6))), hp.clone()),
    );
    let l6_at_n = hyp_mp(&hyp_mp(&a1i(&leib6, l6.clone()), &l6_vns)?, &a1i(&e_in_hp, l6.clone()))?;
    let l6_nk = hyp_eq_symm(env, &l6_kn)?;
    let w7 = env.fresh_var();
    let leib7 = Thm::eq_leibniz(
        tn.clone(),
        tk5.clone(),
        w7,
        Formula::mem(
            r.pair(r.succ_of(Term::var(w7)), g_of(r.apply(hp.clone(), Term::var(w7)))),
            hp.clone(),
        ),
    );
    let l6_goal = hyp_mp(&hyp_mp(&a1i(&leib7, l6.clone()), &l6_nk)?, &l6_at_n)?;
    let j5_case_eq = uncurry(&l6_goal)?;

    let j5_goal = hyp_or_elim(&j5_disj, &j5_case_in, &j5_case_eq)?;
    let h_step = Thm::mp(
        &Thm::ax_dist(vk5, hyp.clone(), Formula::imp(sk_ssn, goal5))?,
        &Thm::gen(vk5, &uncurry(&j5_goal)?),
    )?;
    debug_assert_eq!(
        *h_step.concl(),
        Formula::imp(hyp.clone(), axp.step.clone()),
        "approx_extend: A5 drifted"
    );

    let out = hyp_and(
        &h_bounded,
        &hyp_and(&h_single, &hyp_and(&h_total, &hyp_and(&h_base, &h_step)?)?)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, axp.formula()),
        "approx_extend: unexpected shape"
    );
    Some(gen_all(&[n, h], &out))
}

/// `⊢ ∀n. (n ∈ ω → ∃h. Approx(succ n, h))` — **every one-step-longer domain has
/// an approximation**.
///
/// [`approx_one`] is the base and [`approx_extend`] the step; the induction adds
/// only the discharge of the witness, which is why it is short. `dom` and
/// `om_trans` are passed straight through to [`approx_extend`].
pub fn approx_exists(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    dom: &Thm,
    om_trans: &Thm,
) -> Option<Thm> {
    let (x, vh) = (env.fresh_var(), env.fresh_var());
    let (tx, tvh) = (Term::var(x), Term::var(vh));
    let sx = r.succ_of(tx.clone());
    let ssx = r.succ_of(sx.clone());
    let axx = approx(env, r, g, c, &sx, &tvh)?;
    let phi = Formula::exists(vh, axx.formula());

    // ── Base ─────────────────────────────────────────────────────────────────
    let one = approx_one(env, r, g, c)?;
    let s0 = r.succ_of(r.zero());
    let ax0 = approx(env, r, g, c, &s0, &tvh)?;
    let base = crate::exists_intro(vh, ax0.formula(), one_point_graph(r, c), &one)?;
    debug_assert_eq!(*base.concl(), phi.subst(x, &r.zero()), "approx_exists: base drifted");

    // ── Step ─────────────────────────────────────────────────────────────────
    let ext = approx_extend(env, r, g, c, dom, om_trans)?;
    let x_om = Formula::mem(tx.clone(), r.omega());
    let k = Formula::and(x_om.clone(), phi.clone());
    let hp = extension(r, g, &tx, &tvh);
    let axnew = approx(env, r, g, c, &ssx, &tvh)?;

    let ext_at = inst_all(&ext, &[tx.clone(), tvh.clone()])?;
    let kk = Formula::and(k.clone(), axx.formula());
    let kk_xom = syl(
        &and_left(k.clone(), axx.formula()),
        &and_left(x_om.clone(), phi.clone()),
    )?;
    let kk_ext = hyp_mp(
        &a1i(&ext_at, kk.clone()),
        &hyp_and(&kk_xom, &and_right(k.clone(), axx.formula()))?,
    )?;
    let kk_goal = syl(&kk_ext, &exists_intro_imp(vh, axnew.formula(), hp)?)?;
    let step_body =
        crate::funspace::discharge(vh, &and_right(x_om.clone(), phi.clone()), &kk_goal)?;
    debug_assert_eq!(
        *step_body.concl(),
        Formula::imp(k, phi.subst(x, &sx)),
        "approx_exists: step drifted"
    );

    let scheme = super::induction::induction_scheme(env, r.core(), x, &phi)?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(x, &step_body)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, Formula::imp(x_om, phi)),
        "approx_exists: unexpected shape"
    );
    Some(out)
}
