//! The two ι rules.
//!
//! # Interface
//!
//! Private to [`crate::wlist_rec`]; surfaced as
//! [`crate::wlist_rec::ListRec::iota_nil`] and
//! [`crate::wlist_rec::ListRec::iota_cons`].
//!
//! # What makes these the payoff
//!
//! [`crate::wrec_total`] supplies the general ι rule — the recursor's value at
//! `⟨a,f⟩` is the step applied to `⟨a,⟨f, comp(rec,f,B(a))⟩⟩` — and everything
//! here is the work of specialising it at the two constructors: computing the
//! composite `comp` at a one-point fibre, and rewriting the step's argument into
//! the form [`super::computes`] evaluated.
//!
//! `iota_cons_at` is the one that matters. Its right-hand side mentions the
//! recursor again, so it is not an equation two constant terms could satisfy by
//! accident; `tests/wlist_rec.rs` checks that its two sides are different terms
//! and that the recursive occurrence is really there.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::point_fun::PointFun;
use crate::sums::Cases;
use crate::wlist::WList;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, and_left, and_right, hyp_and, hyp_mp, inst_all, syl, uncurry};

use super::shared::{congr_ctx, gen_under, hyp_inst, rewrite_under};

/// `⊢ HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z` — **ι at `List.nil`**.
///
/// Line for line the deleted `wnat_rec`'s zero rule: the fibre `fam(α)(inl •)` is
/// `0`, so the composite is over an empty domain and
/// [`crate::wrec_unit::comp_empty_domain`] collapses it, leaving the step applied
/// to `k₀`.
#[allow(clippy::too_many_arguments)]
pub(super) fn iota_nil_at(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    cases_s: &Cases,
    r: &Recursor,
    dis: &Thm,
    app_nil: &Thm,
    lrec: &Term,
    step: &Term,
    alpha: &Term,
    z: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, zero_s) = (s.unit(), s.point(), s.zero());
    let fam = wl.fam_of(s, cases_s, alpha.clone());
    let tag = s.inl(point.clone());
    let (hyp, _) = dis.concl().as_imp()?;
    let lt_w = inst_all(&wl.lt_ax, std::slice::from_ref(alpha))?;
    let w_t = {
        let (_, rhs) = lt_w.concl().as_eq()?;
        rhs
    };
    let fibre_nil = inst_all(&wl.fibre_nil, std::slice::from_ref(alpha))?;

    // `inl • ∈ 1+α`, and `∅ ∈ fs(fam(α)(inl •), W)`.
    let tag_mem = Thm::mp(
        &inst_all(&s.inl_mem, &[one.clone(), alpha.clone(), point.clone()])?,
        &s.unit_mem,
    )?;
    let hole = env.fresh_var();
    let f_in = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                zero_s.clone(),
                wt.fibre(fam.clone(), tag.clone()),
                hole,
                Formula::mem(zero_s.clone(), s.fs.of(Term::var(hole), w_t.clone())),
            ),
            &crate::eq_symm(env, &fibre_nil)?,
        )?,
        &inst_all(&wt.empty_fun, std::slice::from_ref(&w_t))?,
    )?;
    let fired = hyp_mp(
        &hyp_inst(dis, &[tag.clone(), zero_s.clone()])?,
        &a1i(&and_intro(&tag_mem, &f_in), hyp.clone()),
    )?;

    // The composite over the empty fibre is `∅`, so the step's argument is `k₀`.
    let fib = wt.fibre(fam.clone(), tag.clone());
    let coll = crate::congr_arg(env, r.comp, &[lrec.clone(), zero_s.clone(), fib], 2, &fibre_nil)?;
    let empty = inst_all(
        &crate::wrec_unit::comp_empty_domain(env, ap, r.comp, &r.comp_ax)?,
        &[lrec.clone(), zero_s.clone()],
    )?;
    let to_empty = crate::eq_trans(env, &coll, &empty)?;
    let rhs = congr_ctx(env, &to_empty, |q| {
        ap.apply(
            step.clone(),
            ap.sets.pair(tag.clone(), ap.sets.pair(zero_s.clone(), q)),
        )
    })?;
    let at_key = crate::eq_trans(env, &rhs, app_nil)?;
    let out = hyp_eq_trans(env, &fired, &a1i(&at_key, hyp.clone()))?;
    if *out.concl()
        != Formula::imp(
            hyp,
            Formula::eq(ap.apply(lrec.clone(), wt.sup(tag, zero_s)), z.clone()),
        )
    {
        return None
    }
    Some(out)
}

/// `⊢ (HYP ∧ (h ∈ α ∧ t ∈ lt(α))) → app(lrec, ⟨inr h,{⟨•,t⟩}⟩)
///        = app(app(app(s,h),t), app(lrec, t))` — **ι at `List.cons`, with both
/// the field and the recursive call live**.
///
/// The fibre `fam(α)(inr h)` is `1`, so nothing collapses. Everything
/// the deleted `wnat_rec`'s successor rule needed is needed again — the one-point
/// subterm family, the composite's typing, and
/// [`crate::wrec_typing::composite_app`] to read the recursive value back out —
/// with one difference: the fibre equation is itself *conditional* on `h ∈ α`,
/// because `α` is arbitrary.
#[allow(clippy::too_many_arguments)]
pub(super) fn iota_cons_at(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    cases_s: &Cases,
    r: &Recursor,
    pf: &PointFun,
    dis: &Thm,
    fs_thm: &Thm,
    app_cons: &Thm,
    lrec: &Term,
    step: &Term,
    alpha: &Term,
    su: &Term,
    t: &Term,
    hv: FreeVar,
    tv: FreeVar,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point) = (s.unit(), s.point());
    let fam = wl.fam_of(s, cases_s, alpha.clone());
    let lt = wl.ty_of(alpha.clone());
    let lt_w = inst_all(&wl.lt_ax, std::slice::from_ref(alpha))?;
    let w_t = {
        let (_, rhs) = lt_w.concl().as_eq()?;
        rhs
    };
    let (th, tl) = (Term::var(hv), Term::var(tv));
    let tag = s.inr(th.clone());
    let pfn = PointFun::of(s, point.clone(), tl.clone());
    let (hyp, _) = dis.concl().as_imp()?;
    let mem_h = Formula::mem(th.clone(), alpha.clone());
    let mem_t = Formula::mem(tl.clone(), lt.clone());
    let inner = Formula::and(mem_h.clone(), mem_t.clone());
    let p = Formula::and(hyp.clone(), inner.clone());
    let p_hyp = and_left(hyp.clone(), inner.clone());
    let p_rest = and_right(hyp.clone(), inner.clone());
    let p_h = syl(&p_rest, &and_left(mem_h.clone(), mem_t.clone()))?;
    let p_t = syl(&p_rest, &and_right(mem_h.clone(), mem_t.clone()))?;

    // `t ∈ W`, the same membership stated at the raw W-type.
    let tl_c = tl.clone();
    let p_t_w = rewrite_under(
        env,
        &a1i(&lt_w, p.clone()),
        move |w| Formula::mem(tl_c.clone(), w),
        &p_t,
    )?;

    // ── `{⟨•,t⟩} ∈ fs(1,W)`, and the same at the fibre `fam(α)(inr h)` ──────
    let in_fs_1 = syl(
        &p_t_w,
        &inst_all(&pf.in_fs, &[point.clone(), tl.clone(), w_t.clone()])?,
    )?;
    let fibre_cons = syl(&p_h, &inst_all(&wl.fibre_cons, &[alpha.clone(), th.clone()])?)?;
    let back_fib = hyp_eq_symm(env, &fibre_cons)?;
    let (pfn_c, w_c) = (pfn.clone(), w_t.clone());
    let p_f_fib = rewrite_under(
        env,
        &back_fib,
        move |w| Formula::mem(pfn_c.clone(), Term::apply(s.fs.fs, vec![w, w_c.clone()])),
        &in_fs_1,
    )?;

    let tag_mem = syl(
        &p_h,
        &inst_all(&s.inr_mem, &[one.clone(), alpha.clone(), th.clone()])?,
    )?;
    let fired = hyp_mp(
        &syl(&p_hyp, &hyp_inst(dis, &[tag.clone(), pfn.clone()])?)?,
        &hyp_and(&tag_mem, &p_f_fib)?,
    )?;

    // ── The fibre is `1`, so the composite has domain `1` ───────────────────
    let fib = wt.fibre(fam.clone(), tag.clone());
    let cmp = comp_of(r.comp, lrec.clone(), pfn.clone(), one.clone());
    let (lrec_c, pfn_c2) = (lrec.clone(), pfn.clone());
    let coll = hyp_congr(env, &fibre_cons, move |q| {
        comp_of(r.comp, lrec_c.clone(), pfn_c2.clone(), q)
    })?;
    let _ = fib;
    let rhs = hyp_congr(env, &coll, |q| {
        ap.apply(
            step.clone(),
            ap.sets.pair(tag.clone(), ap.sets.pair(pfn.clone(), q)),
        )
    })?;
    let at_one = hyp_eq_trans(env, &fired, &rhs)?;

    // ── `comp(lrec,{⟨•,t⟩},1) ∈ fs(1,T)` ────────────────────────────────────
    let p_lrec = syl(&p_hyp, fs_thm)?;
    let p_val = {
        let bv = env.fresh_var();
        let tb = Term::var(bv);
        let mem_b = Formula::mem(tb.clone(), one.clone());
        let k = Formula::and(p.clone(), mem_b.clone());
        let k_b = and_right(p.clone(), mem_b.clone());
        let k_p = and_left(p.clone(), mem_b.clone());
        let k_pt = syl(&k_b, &inst_all(&s.unit_eta, std::slice::from_ref(&tb))?)?;
        let k_cong = hyp_congr(env, &k_pt, |q| ap.apply(pfn.clone(), q))?;
        let k_app = hyp_eq_trans(
            env,
            &k_cong,
            &a1i(&inst_all(&pf.app, &[point.clone(), tl.clone()])?, k.clone()),
        )?;
        let k_in_t = hyp_mp(
            &a1i(
                &inst_all(&wt.app_mem, &[w_t.clone(), t.clone(), lrec.clone(), tl.clone()])?,
                k.clone(),
            ),
            &hyp_and(&syl(&k_p, &p_lrec)?, &syl(&k_p, &p_t_w)?)?,
        )?;
        let k_back = hyp_eq_symm(env, &k_app)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            tl.clone(),
            ap.apply(pfn.clone(), tb.clone()),
            hole,
            Formula::mem(ap.apply(lrec.clone(), Term::var(hole)), t.clone()),
        );
        let k_goal = hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &k_back)?, &k_in_t)?;
        gen_under(bv, &p, &uncurry(&k_goal)?)?
    };
    let ct = inst_all(
        &crate::wrec_typing::composite_typed(env, s, r.comp, &r.comp_ax)?,
        &[lrec.clone(), pfn.clone(), one.clone(), t.clone()],
    )?;
    let p_cmp_fs = hyp_mp(&a1i(&ct, p.clone()), &p_val)?;

    // ── …and all three arguments are where the step's Replacement ranges ────
    let sub = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[one.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };
    let in_fs_lt = syl(
        &p_t,
        &inst_all(&pf.in_fs, &[point.clone(), tl.clone(), lt.clone()])?,
    )?;
    let p_fw = sub(&in_fs_lt, &lt, &pfn)?;
    let p_ft = sub(&p_cmp_fs, t, &cmp)?;
    let p_step = hyp_mp(
        &a1i(
            &inst_all(app_cons, &[th.clone(), pfn.clone(), cmp.clone()])?,
            p.clone(),
        ),
        &hyp_and(&p_h, &hyp_and(&p_fw, &p_ft)?)?,
    )?;
    let at_val = hyp_eq_trans(env, &at_one, &p_step)?;

    // ── The value: `app(f,•) = t` and `app(cmp,•) = app(lrec,t)` ────────────
    let f_at = inst_all(&pf.app, &[point.clone(), tl.clone()])?;
    let comp_app = Thm::mp(
        &inst_all(
            &crate::wrec_typing::composite_app(env, ap, r.comp, &r.comp_ax)?,
            &[lrec.clone(), pfn.clone(), one.clone(), point.clone()],
        )?,
        &s.unit_mem,
    )?;
    let f_lift = congr_ctx(env, &f_at, |q| ap.apply(lrec.clone(), q))?;
    let c_at = crate::eq_trans(env, &comp_app, &f_lift)?;
    let sh = ap.apply(su.clone(), th.clone());
    let v1 = congr_ctx(env, &f_at, |q| {
        ap.apply(ap.apply(sh.clone(), q), ap.apply(cmp.clone(), point.clone()))
    })?;
    let v2 = congr_ctx(env, &c_at, |q| {
        ap.apply(ap.apply(sh.clone(), tl.clone()), q)
    })?;
    let value = crate::eq_trans(env, &v1, &v2)?;
    let out = hyp_eq_trans(env, &at_val, &a1i(&value, p.clone()))?;
    if *out.concl()
        != Formula::imp(
            p,
            Formula::eq(
                ap.apply(lrec.clone(), wt.sup(tag, pfn)),
                ap.apply(
                    ap.apply(sh.clone(), tl.clone()),
                    ap.apply(lrec.clone(), tl.clone()),
                ),
            ),
        )
    {
        return None
    }
    Some(out)
}
