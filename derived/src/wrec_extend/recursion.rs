//! **Clause 3 of the attempt condition**: the recursion condition. The long
//! half.
//!
//! # Interface
//!
//! Private to [`crate::wrec_extend`]. `extension_recursion_condition` is the
//! third and hardest of the three clauses [`super::assemble`] needs.
//!
//! # Why it is the long half
//!
//! The recursion condition is a statement about *every* point of the domain, so
//! it has to be re-established at the new point **and** preserved at every old
//! one — and preserving it is not free, because the condition mentions
//! `comp(G, f, B(a))`, the composite of the *whole* graph, which has changed.
//!
//! `composite_transfer` is the lemma that makes it go through: on the old
//! points' fibres `G` and `g` agree, so their composites are equal
//! ([`crate::wrec::compose_ext`]), and the old recursion equation carries across.
//! `agreement` is that agreement, and `into_domain` is what puts a subterm of an
//! old point back into `g`'s domain so the induction has something to stand on.
//!
//! At the new point the condition is the definition of `v` and the value
//! equation from [`super::value`] — but stated at a substitution instance, which
//! is why `super::terms::Cx` carries the body as a closure.

use kernel::{Env, Formula, Term, Thm};
use crate::wrec;
use crate::separation::hyp_syl;
use crate::sums::Sums;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim, indom, step_at};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, hyp_and, hyp_mp, hyp_or_elim, iff_mp, inst_all,
    syl, uncurry,
};

use super::shared::{gen_under, hyp_inst, hyp_leibniz, hyp_split};
use super::terms::Cx;

/// `⊢ indom(wrec, x) → indom(G, x)` — the extension's domain contains the
/// recursor's. Unconditional: it is `wrec ⊆ G` under an existential.
fn into_domain(env: &mut Env, s: &Sums, cx: &Cx, x: &Term) -> Option<Thm> {
    let yv = env.fresh_var();
    let p = s.ap.sets.pair(x.clone(), Term::var(yv));
    let out = crate::exists_mono(yv, &Thm::gen(yv, &cx.embed(s, &p)?))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            indom(env, &s.ap, &cx.rec_t, x),
            indom(env, &s.ap, &cx.g, x)
        ),
        "into_domain: the implication has the wrong shape"
    );
    Some(out)
}

/// **`G` takes `wrec`'s value everywhere `wrec` is defined.**
///
/// ```text
/// ⊢ K → ∀x. (indom(wrec,x) → app(wrec,x) = app(G,x))
/// ```
///
/// A pair of `wrec` over `x` is a pair of `G` over `x`, and each of the two is
/// single-valued — `wrec` under `closed(A,B,u)`, `G` by
/// [`extension_single_valued`] — so each takes that pair's second component as
/// its value. This is what [`crate::wrec::compose_ext`]'s premise is made of.
pub(super) fn agreement(env: &mut Env, wt: &Wtype, r: &Recursor, cx: &Cx, sv_g: &Thm) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let ind = indom(env, ap, &cx.rec_t, &tx);
    let h = Formula::and(cx.k.clone(), ind.clone());
    let h_k = and_left(cx.k.clone(), ind.clone());
    let h_ind = and_right(cx.k.clone(), ind);

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let pxy = ap.sets.pair(tx.clone(), ty.clone());
    let phi = Formula::mem(pxy.clone(), cx.rec_t.clone());
    let n = Formula::and(h.clone(), phi.clone());
    let n_h = and_left(h.clone(), phi.clone());
    let n_mem = and_right(h, phi);
    let n_k = syl(&n_h, &h_k)?;
    let n_cl = syl(&n_k, &cx.cl)?;

    let sv_rec = syl(&n_cl, &inst_all(&r.sv, &cx.ps)?)?;
    let v1 = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[cx.rec_t.clone(), tx.clone(), ty.clone()])?,
            n.clone(),
        ),
        &hyp_and(&sv_rec, &n_mem)?,
    )?;
    let in_g = syl(&n_mem, &cx.embed(s, &pxy)?)?;
    let v2 = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[cx.g.clone(), tx.clone(), ty])?,
            n,
        ),
        &hyp_and(&syl(&n_k, sv_g)?, &in_g)?,
    )?;
    let flip = hyp_eq_symm(env, &v2)?;
    let body = hyp_eq_trans(env, &v1, &flip)?;
    let out = uncurry(&hyp_exists_elim(yv, &body, &h_ind)?)?;
    gen_under(xv, &cx.k, &out)
}

/// From `⊢ H → K` and `⊢ H → ∀b. (b ∈ d → indom(wrec, app(f′,b)))` infer
/// `⊢ H → comp(wrec,f′,d) = comp(G,f′,d)`.
///
/// [`crate::wrec::compose_ext`] against [`agreement`], pointwise. The premise
/// it needs is *exactly* the subterm clause of a recursion condition, which is
/// why both cases below have one to hand.
#[allow(clippy::too_many_arguments)]
fn composite_transfer(
    env: &mut Env,
    wt: &Wtype,
    r: &Recursor,
    cx: &Cx,
    agree: &Thm,
    h_k: &Thm,
    h_sub: &Thm,
    f2: &Term,
    d: &Term,
) -> Option<Thm> {
    let ap = &wt.sums.ap;
    let (h, _) = h_k.concl().as_imp()?;
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let fb = ap.apply(f2.clone(), tb.clone());
    let at_b = hyp_inst(h_sub, std::slice::from_ref(&tb))?;
    let ag = hyp_inst(&syl(h_k, agree)?, std::slice::from_ref(&fb))?;
    let all = gen_under(bv, &h, &hyp_syl(&at_b, &ag)?)?;
    debug_assert_eq!(
        *all.concl(),
        Formula::imp(
            h.clone(),
            wrec::agree_on(env, ap, &cx.rec_t, &cx.g, f2, d)
        ),
        "composite_transfer: the agreement has the wrong shape"
    );
    syl(
        &all,
        &inst_all(
            &r.ext,
            &[cx.rec_t.clone(), cx.g.clone(), f2.clone(), d.clone()],
        )?,
    )
}

/// **The extension satisfies the recursion condition.** `⊢ K → rec_cond(B,e,G)`
///
/// Two cases, from the union's membership condition. At an **old** point,
/// [`crate::wrec::wrec_rec_cond`] gives both clauses for `wrec` and
/// [`agreement`] plus [`composite_transfer`] move them to `G`. At `⟨a,f⟩`
/// itself, [`crate::pairs::opair_inj`] recovers `a` and `f` from the new pair,
/// the subterm clause is the induction hypothesis, and the equation is `V`'s
/// own definition with the composite moved across.
pub(super) fn extension_recursion_condition(
    env: &mut Env,
    wt: &Wtype,
    r: &Recursor,
    cx: &Cx,
    sv_g: &Thm,
    agree: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let te = cx.ps[4].clone();
    let tbf = cx.ps[1].clone();
    let (pa2, pf2, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (a2, f2, ty) = (Term::var(pa2), Term::var(pf2), Term::var(yv));
    let w1 = ap.sets.pair(a2.clone(), f2.clone());
    let fib2 = ap.apply(tbf.clone(), a2.clone());

    // The recursion condition's body, as a function of the constructor and the
    // subterm family — so that the new-point case can be proved at `a` and `f`
    // and then carried across the two equations `a′ = a` and `f′ = f`.
    let goal_at = |env: &mut Env, aa: &Term, ff: &Term| -> Formula {
        let fib = ap.apply(tbf.clone(), aa.clone());
        let bv = env.fresh_var();
        let tb = Term::var(bv);
        let sub = Formula::forall(
            bv,
            Formula::imp(
                Formula::mem(tb.clone(), fib.clone()),
                indom(env, ap, &cx.g, &ap.apply(ff.clone(), tb)),
            ),
        );
        let eqn = Formula::eq(
            ap.apply(cx.g.clone(), ap.sets.pair(aa.clone(), ff.clone())),
            step_at(ap, r.comp, &te, &cx.g, aa, ff, &fib),
        );
        Formula::and(sub, eqn)
    };

    let head = indom(env, ap, &cx.g, &w1);
    let h0 = Formula::and(cx.k.clone(), head.clone());
    let h0_k = and_left(cx.k.clone(), head.clone());
    let h0_head = and_right(cx.k.clone(), head);

    let pair1 = ap.sets.pair(w1.clone(), ty.clone());
    let phi = Formula::mem(pair1.clone(), cx.g.clone());
    let h1 = Formula::and(h0.clone(), phi.clone());
    let h1_h0 = and_left(h0.clone(), phi.clone());
    let h1_phi = and_right(h0, phi);
    let h1_k = syl(&h1_h0, &h0_k)?;
    let disj = syl(&h1_phi, &iff_mp(&cx.mem(s, &pair1)?)?)?;

    // ── An old point ────────────────────────────────────────────────────────
    let old = Formula::mem(pair1.clone(), cx.rec_t.clone());
    let n = Formula::and(h1.clone(), old.clone());
    let n_h1 = and_left(h1.clone(), old.clone());
    let n_old = and_right(h1.clone(), old);
    let n_k = syl(&n_h1, &h1_k)?;
    let n_cl = syl(&n_k, &cx.cl)?;

    let y2 = env.fresh_var();
    let n_ind = syl(
        &n_old,
        &exists_intro_imp(
            y2,
            Formula::mem(
                ap.sets.pair(w1.clone(), Term::var(y2)),
                cx.rec_t.clone(),
            ),
            ty.clone(),
        )?,
    )?;
    let rc = hyp_mp(
        &hyp_inst(
            &syl(&n_cl, &inst_all(&r.rec_cond, &cx.ps)?)?,
            &[a2.clone(), f2.clone()],
        )?,
        &n_ind,
    )?;
    let (n_sub, n_eqn) = hyp_split(&rc)?;

    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let fb2 = ap.apply(f2.clone(), tb.clone());
    let into = into_domain(env, s, cx, &fb2)?;
    let n_subg = gen_under(
        bv,
        &n,
        &hyp_syl(&hyp_inst(&n_sub, std::slice::from_ref(&tb))?, &a1i(&into, n.clone()))?,
    )?;

    let n_agree = hyp_mp(
        &hyp_inst(&syl(&n_k, agree)?, std::slice::from_ref(&w1))?,
        &n_ind,
    )?;
    let n_ct = composite_transfer(env, wt, r, cx, agree, &n_k, &n_sub, &f2, &fib2)?;
    let n_step = hyp_congr(env, &n_ct, |t| {
        ap.apply(
            te.clone(),
            ap.sets.pair(a2.clone(), ap.sets.pair(f2.clone(), t)),
        )
    })?;
    let n_lhs = hyp_eq_symm(env, &n_agree)?;
    let n_mid = hyp_eq_trans(env, &n_lhs, &n_eqn)?;
    let n_eq_g = hyp_eq_trans(env, &n_mid, &n_step)?;
    let case_old = uncurry(&hyp_and(&n_subg, &n_eq_g)?)?;

    // ── The new point ───────────────────────────────────────────────────────
    let is_new = Formula::eq(pair1, cx.q.clone());
    let nn_h1 = and_left(h1.clone(), is_new.clone());
    let nn_new = and_right(h1, is_new);
    let nn_k = syl(&nn_h1, &h1_k)?;

    let inj1 = syl(
        &nn_new,
        &inst_all(
            &ap.pair_inj,
            &[w1.clone(), ty, cx.w0.clone(), cx.v.clone()],
        )?,
    )?;
    let eq_w = syl(
        &inj1,
        &and_left(
            Formula::eq(w1.clone(), cx.w0.clone()),
            Formula::eq(Term::var(yv), cx.v.clone()),
        ),
    )?;
    let inj2 = syl(
        &eq_w,
        &inst_all(
            &ap.pair_inj,
            &[a2.clone(), f2.clone(), cx.a.clone(), cx.f.clone()],
        )?,
    )?;
    let eq_a2 = Formula::eq(a2.clone(), cx.a.clone());
    let eq_f2 = Formula::eq(f2.clone(), cx.f.clone());
    let nn_a = syl(&inj2, &and_left(eq_a2.clone(), eq_f2.clone()))?;
    let nn_f = syl(&inj2, &and_right(eq_a2, eq_f2))?;

    // The goal at `a` and `f`, under `K` alone.
    let bv2 = env.fresh_var();
    let tb2 = Term::var(bv2);
    let fb = ap.apply(cx.f.clone(), tb2.clone());
    let into_af = into_domain(env, s, cx, &fb)?;
    let k_subg = gen_under(
        bv2,
        &cx.k,
        &hyp_syl(
            &hyp_inst(&cx.ih, std::slice::from_ref(&tb2))?,
            &a1i(&into_af, cx.k.clone()),
        )?,
    )?;
    let k_val = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[cx.g.clone(), cx.w0.clone(), cx.v.clone()])?,
            cx.k.clone(),
        ),
        &hyp_and(sv_g, &a1i(&cx.new_pair(s)?, cx.k.clone()))?,
    )?;
    let k_ct = composite_transfer(
        env,
        wt,
        r,
        cx,
        agree,
        &crate::imp_refl(cx.k.clone()),
        &cx.ih,
        &cx.f.clone(),
        &cx.fibre.clone(),
    )?;
    let k_step = hyp_congr(env, &k_ct, |t| {
        ap.apply(
            te.clone(),
            ap.sets.pair(cx.a.clone(), ap.sets.pair(cx.f.clone(), t)),
        )
    })?;
    let k_eqn = hyp_eq_trans(env, &k_val, &k_step)?;
    let k_goal = hyp_and(&k_subg, &k_eqn)?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(cx.k.clone(), goal_at(env, &cx.a.clone(), &cx.f.clone())),
        "extension_recursion_condition: the new point's goal has the wrong shape"
    );

    // …carried back along `a′ = a` and `f′ = f`.
    let nn_goal_af = syl(&nn_k, &k_goal)?;
    let hole = env.fresh_var();
    let phi_a = goal_at(env, &Term::var(hole), &cx.f.clone());
    let a_back = hyp_eq_symm(env, &nn_a)?;
    let at_a2 = hyp_mp(&hyp_leibniz(&a_back, hole, &phi_a)?, &nn_goal_af)?;
    let hole2 = env.fresh_var();
    let phi_f = goal_at(env, &a2, &Term::var(hole2));
    let f_back = hyp_eq_symm(env, &nn_f)?;
    let case_new = uncurry(&hyp_mp(&hyp_leibniz(&f_back, hole2, &phi_f)?, &at_a2)?)?;

    // ── The two cases, then the two quantifiers ─────────────────────────────
    let body = hyp_or_elim(&disj, &case_old, &case_new)?;
    let inner = uncurry(&hyp_exists_elim(yv, &body, &h0_head)?)?;
    let out = gen_under(pa2, &cx.k, &gen_under(pf2, &cx.k, &inner)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            cx.k.clone(),
            wrec::rec_cond(env, ap, r.comp, &tbf, &te, &cx.g)
        ),
        "extension_recursion_condition: rec_cond(G) has the wrong shape"
    );
    Some(out)
}
