//! The step is typed.
//!
//! # Interface
//!
//! [`premise`] is the hypothesis `HYP` every theorem in this module carries;
//! `step_typed_at` derives `step_typed(…)` from it, surfaced as
//! [`crate::wlist_rec::ListRec::step_typed`].
//!
//! Callers need none of the derivation below, but they do need [`premise`]: a
//! caller has to build the same formula to discharge the hypothesis.
//!
//! # Why `HYP` is not free
//!
//! [`crate::wbool_rec`] gets its `step_typed` for nothing, because `T` there is a
//! two-element set and the step's value is always one of them. No such trick
//! survives once the step's value is an *application*: the only thing that puts
//! `app(app(app(s,h),t),r)` in `T` is `s` being typed.
//!
//! This is not new work either — the typing conditions on `z` and `s` are
//! exactly what a caller applying Lean's `List.rec` is already paying, with `T`
//! the motive at `List.nil`. It is the longest derivation in this module because
//! the `cons` branch has to be typed under three nested function-space
//! memberships at once.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::sums::{Cases, Sums};
use crate::wlist::WList;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, hyp_and, hyp_mp, hyp_or_elim, inst_all, syl, uncurry};

use super::shared::{carry_under, gen_under};
use super::step::StepSyms;

/// The hypothesis both ι rules carry: `z ∈ T ∧ s ∈ fs(α, fs(lt(α), fs(T,T)))`.
///
/// Lean's own typing of a `List.rec` application, and nothing more: `T` is the
/// motive at `List.nil α`, `z` the nil minor premise, and `s` the cons one,
/// whose type `∀ h, ∀ t, motive t → motive (cons h t)` becomes
/// `fs(α, fs(lt(α), fs(T,T)))` once the motive is constant.
pub fn premise(s: &Sums, wl: &WList, alpha: &Term, z: &Term, su: &Term, t: &Term) -> Formula {
    Formula::and(
        Formula::mem(z.clone(), t.clone()),
        Formula::mem(
            su.clone(),
            s.fs.of(
                alpha.clone(),
                s.fs.of(wl.ty_of(alpha.clone()), s.fs.of(t.clone(), t.clone())),
            ),
        ),
    )
}

/// `⊢ HYP → step_typed(1+α, fam(α), U(1+α), T, e(α,z,s,T))`.
///
/// [`crate::wlist`]'s case analysis once more, now on the step's own tag
/// argument. At `inl •` the fibre is `0`, so `f` and `r` are forced to `∅`
/// ([`crate::wtype::empty_funspace`]), the triple is `k₀` and the value is `z`.
/// At `inr h` — with `h ∈ α`, which the case analysis supplies — the fibre is
/// `1`, so `f ∈ fs(1,lt(α))` and `r ∈ fs(1,T)`, both inside the power sets the
/// Replacement ranges over; the triple is `key_cons(h,f,r)` and the value is
/// typed by **five** applications of [`crate::wtype::funspace_app_mem`], one more
/// than `N` needed, for the extra field.
///
/// This is where `HYP` is used and the *only* place.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_typed_at(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    wl: &WList,
    cases_s: &Cases,
    sy: &StepSyms,
    app_nil: &Thm,
    app_cons: &Thm,
    alpha: &Term,
    z: &Term,
    su: &Term,
    t: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, zero_s) = (s.unit(), s.point(), s.zero());
    let tags = WList::tags_of(s, alpha.clone());
    let fam = wl.fam_of(s, cases_s, alpha.clone());
    let u = bnd.universe_of(tags.clone());
    let lt = wl.ty_of(alpha.clone());
    let w_t = wt.of(tags.clone(), fam.clone(), u.clone());
    let lt_w = inst_all(&wl.lt_ax, std::slice::from_ref(alpha))?;
    let step = sy.step_of(wt, alpha, z, su, t);
    let hyp = premise(s, wl, alpha, z, su, t);
    let fs_inner = s.fs.of(lt.clone(), s.fs.of(t.clone(), t.clone()));

    let prod_empty = crate::wtype::empty_product(env, s)?;
    let empty_fs = crate::wtype::empty_funspace(env, s, &prod_empty)?;

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre = wt.fibre(fam.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), w_t.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre.clone(), t.clone()));
    let hm = Formula::and(hyp.clone(), ma.clone());
    let front = Formula::and(hm.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());

    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr.clone());
    let p_hm = syl(&p_front, &and_left(hm.clone(), mf.clone()))?;
    let p_mf_w = syl(&p_front, &and_right(hm.clone(), mf.clone()))?;
    let p_hyp = syl(&p_hm, &and_left(hyp.clone(), ma.clone()))?;
    let p_ma = syl(&p_hm, &and_right(hyp.clone(), ma.clone()))?;
    let p_z = syl(
        &p_hyp,
        &and_left(
            Formula::mem(z.clone(), t.clone()),
            Formula::mem(su.clone(), s.fs.of(alpha.clone(), fs_inner.clone())),
        ),
    )?;
    let p_su = syl(
        &p_hyp,
        &and_right(
            Formula::mem(z.clone(), t.clone()),
            Formula::mem(su.clone(), s.fs.of(alpha.clone(), fs_inner.clone())),
        ),
    )?;

    // The subterm family is stated at the raw W-type; `lt(α)` is what everything
    // else here speaks of, so it is moved across the abbreviation once.
    let w_lt = crate::eq_symm(env, &lt_w)?;
    let (tf_c, fibre_c) = (tf.clone(), fibre.clone());
    let p_mf = carry_under(
        env,
        &w_lt,
        move |w| Formula::mem(tf_c.clone(), Term::apply(s.fs.fs, vec![fibre_c.clone(), w])),
        &p_mf_w,
    )?;

    let triple = |x: &Term, y: &Term, w: &Term| {
        ap.apply(
            step.clone(),
            ap.sets.pair(x.clone(), ap.sets.pair(y.clone(), w.clone())),
        )
    };
    let goal = Formula::mem(triple(&ta, &tf, &tr), t.clone());

    // `K → app(f,x) ∈ b`, from `K → f ∈ fs(a,b)` and `K → x ∈ a`.
    let applied = |k_fun: &Thm, k_arg: &Thm, a: &Term, b: &Term, g: &Term, x: &Term| -> Option<Thm> {
        let rule = inst_all(&wt.app_mem, &[a.clone(), b.clone(), g.clone(), x.clone()])?;
        let (k, _) = k_fun.concl().as_imp()?;
        hyp_mp(&a1i(&rule, k), &hyp_and(k_fun, k_arg)?)
    };
    // `K → g ∈ fs(D, cod)`, the fibre having been computed to `D`.
    let retype = |env: &mut Env,
                  k: &Formula,
                  k_fib: &Thm,
                  prem: &Thm,
                  dom: &Term,
                  cod: &Term,
                  g: &Term|
     -> Option<Thm> {
        let cong = hyp_congr(env, k_fib, |q| s.fs.of(q, cod.clone()))?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            s.fs.of(fibre.clone(), cod.clone()),
            s.fs.of(dom.clone(), cod.clone()),
            hole,
            Formula::mem(g.clone(), Term::var(hole)),
        );
        hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &cong)?, prem)
    };
    // `K → g ∈ 𝒫(prod(1,cod))`, from `K → g ∈ fs(1,cod)`.
    let sub = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[one.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };
    // `K → app(e,⟨a,⟨f,r⟩⟩) ∈ T`, the value carried back along its computation.
    let carry_back = |env: &mut Env, k: &Formula, k_val: &Thm, k_in_t: &Thm| -> Option<Thm> {
        let (_, veq) = k_val.concl().as_imp()?;
        let (lhs, rhs) = veq.as_eq()?;
        let back = hyp_eq_symm(env, k_val)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(Term::var(hole), t.clone()));
        hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &back)?, k_in_t)
    };

    // ── The nil branch: the tag is `inl x` with `x ∈ 1` ─────────────────────
    let left = {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let k_body = Formula::and(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), s.inl(tx.clone())),
        );
        let k = Formula::and(p.clone(), k_body.clone());
        let k_p = and_left(p.clone(), k_body.clone());
        let k_case = and_right(p.clone(), k_body.clone());
        let k_x = syl(
            &k_case,
            &and_left(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), s.inl(tx.clone())),
            ),
        )?;
        let k_eq = syl(
            &k_case,
            &and_right(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), s.inl(tx.clone())),
            ),
        )?;
        let k_pt = syl(&k_x, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let k_inj = hyp_congr(env, &k_pt, |q| s.inl(q))?;
        let k_a = hyp_eq_trans(env, &k_eq, &k_inj)?;
        let k_cong = hyp_congr(env, &k_a, |q| wt.fibre(fam.clone(), q))?;
        let fibre_nil = inst_all(&wl.fibre_nil, std::slice::from_ref(alpha))?;
        let k_fib = hyp_eq_trans(env, &k_cong, &a1i(&fibre_nil, k.clone()))?;

        let k_mf = syl(&k_p, &p_mf)?;
        let k_mr = syl(&k_p, &p_mr)?;
        let k_f = retype(env, &k, &k_fib, &k_mf, &zero_s, &lt, &tf)?;
        let k_r = retype(env, &k, &k_fib, &k_mr, &zero_s, t, &tr)?;

        let k_tag = hyp_congr(env, &k_a, |q| triple(&q, &tf, &tr))?;
        let forced = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
            syl(prem, &inst_all(&empty_fs, &[cod.clone(), g.clone()])?)
        };
        let k_f0 = forced(&k_f, &lt, &tf)?;
        let k_r0 = forced(&k_r, t, &tr)?;
        let e1 = hyp_congr(env, &k_f0, |q| triple(&s.inl(point.clone()), &q, &tr))?;
        let e2 = hyp_congr(env, &k_r0, |q| triple(&s.inl(point.clone()), &zero_s, &q))?;
        let collapse = hyp_eq_trans(env, &e1, &e2)?;
        let to_key = hyp_eq_trans(env, &k_tag, &collapse)?;
        let k_val = hyp_eq_trans(env, &to_key, &a1i(app_nil, k.clone()))?;
        let k_in_t = syl(&k_p, &p_z)?;
        let k_goal = carry_back(env, &k, &k_val, &k_in_t)?;

        let per = crate::exists_elim_imp(
            xv,
            &Thm::gen(xv, &crate::com12(&uncurry(&k_goal)?)?),
            &Formula::imp(p.clone(), goal.clone()),
        )?;
        crate::com12(&per)?
    };

    // ── The cons branch: the tag is `inr h` with `h ∈ α` ────────────────────
    let right = {
        let hv = env.fresh_var();
        let th = Term::var(hv);
        let k_body = Formula::and(
            Formula::mem(th.clone(), alpha.clone()),
            Formula::eq(ta.clone(), s.inr(th.clone())),
        );
        let k = Formula::and(p.clone(), k_body.clone());
        let k_p = and_left(p.clone(), k_body.clone());
        let k_case = and_right(p.clone(), k_body.clone());
        let k_h = syl(
            &k_case,
            &and_left(
                Formula::mem(th.clone(), alpha.clone()),
                Formula::eq(ta.clone(), s.inr(th.clone())),
            ),
        )?;
        let k_a = syl(
            &k_case,
            &and_right(
                Formula::mem(th.clone(), alpha.clone()),
                Formula::eq(ta.clone(), s.inr(th.clone())),
            ),
        )?;
        let k_cong = hyp_congr(env, &k_a, |q| wt.fibre(fam.clone(), q))?;
        let fibre_cons = inst_all(&wl.fibre_cons, &[alpha.clone(), th.clone()])?;
        let k_fib = hyp_eq_trans(env, &k_cong, &syl(&k_h, &fibre_cons)?)?;

        let k_mf = syl(&k_p, &p_mf)?;
        let k_mr = syl(&k_p, &p_mr)?;
        let k_f = retype(env, &k, &k_fib, &k_mf, &one, &lt, &tf)?;
        let k_r = retype(env, &k, &k_fib, &k_mr, &one, t, &tr)?;

        let k_tag = hyp_congr(env, &k_a, |q| triple(&q, &tf, &tr))?;
        let k_fw = sub(&k_f, &lt, &tf)?;
        let k_ft = sub(&k_r, t, &tr)?;
        let k_app = hyp_mp(
            &a1i(
                &inst_all(app_cons, &[th.clone(), tf.clone(), tr.clone()])?,
                k.clone(),
            ),
            &hyp_and(&k_h, &hyp_and(&k_fw, &k_ft)?)?,
        )?;
        let k_val = hyp_eq_trans(env, &k_tag, &k_app)?;

        // `app(app(app(s,h), app(f,•)), app(r,•)) ∈ T`, five applications.
        let k_pt_mem = a1i(&s.unit_mem, k.clone());
        let fx = ap.apply(tf.clone(), point.clone());
        let k_fx = applied(&k_f, &k_pt_mem, &one, &lt, &tf, &point)?;
        let k_rx = applied(&k_r, &k_pt_mem, &one, t, &tr, &point)?;
        let k_su = syl(&k_p, &p_su)?;
        let k_sh = applied(&k_su, &k_h, alpha, &fs_inner, su, &th)?;
        let sh = ap.apply(su.clone(), th.clone());
        let tt = s.fs.of(t.clone(), t.clone());
        let k_sht = applied(&k_sh, &k_fx, &lt, &tt, &sh, &fx)?;
        let k_in_t = applied(
            &k_sht,
            &k_rx,
            t,
            t,
            &ap.apply(sh.clone(), fx.clone()),
            &ap.apply(tr.clone(), point.clone()),
        )?;
        let k_goal = carry_back(env, &k, &k_val, &k_in_t)?;

        let per = crate::exists_elim_imp(
            hv,
            &Thm::gen(hv, &crate::com12(&uncurry(&k_goal)?)?),
            &Formula::imp(p.clone(), goal.clone()),
        )?;
        crate::com12(&per)?
    };

    let cases = syl(
        &p_ma,
        &inst_all(&s.sum_cases, &[one.clone(), alpha.clone(), ta.clone()])?,
    )?;
    let body = hyp_or_elim(&cases, &left, &right)?;

    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let over_f = gen_under(fv, &hm, &uncurry(&over_r)?)?;
    let out = gen_under(av, &hyp, &uncurry(&over_f)?)?;
    if *out.concl()
        != Formula::imp(
            hyp,
            crate::wrec_total::step_typed(env, s, wt, &tags, &fam, &u, t, &step),
        )
    {
        return None
    }
    Some(out)
}
