//! The step is typed.
//!
//! # Interface
//!
//! ```text
//! HYP := z ∈ T ∧ s ∈ fs(N, fs(T,T))                                  [premise]
//!
//! ⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))   [step_typed_at]
//! ```
//!
//! surfaced as [`crate::wnat_rec::NatRec::step_typed`]. Callers need none of the
//! derivation below, but they do need [`premise`]: it is the hypothesis every
//! other theorem in this module carries, and a caller has to build the same
//! formula to discharge it.
//!
//! # Why `HYP` is not free, unlike `Bool`'s
//!
//! [`crate::wbool_rec`] gets its `step_typed` for nothing, because `T` there is
//! the two-element set `{fls,tru}` and the step's value is always one of them.
//! No such trick survives once the step's value is an *application*
//! `app(app(s,n),r)`: the only thing that puts it in `T` is `s` being typed.
//!
//! But this is not new work either. `z ∈ T` and `s ∈ fs(N, fs(T,T))` are exactly
//! the typing obligations a caller applying Lean's `N.rec` to `z` and `s` is
//! already paying, with `T` the motive at `N.zero`. See the `N.rec` feasibility
//! entry in `INDUCTIVES.md`.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::sums::Sums;
use crate::wnat::Nat;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, hyp_and, hyp_mp, hyp_or_elim, inst_all, syl, uncurry};

use super::shared::gen_under;
use super::step::StepSyms;

/// The hypothesis both ι rules carry: `z ∈ T ∧ s ∈ fs(N, fs(T,T))`.
///
/// Lean's own typing of a `N.rec` application, and nothing more: `T` is the
/// motive at `N.zero`, `z` the zero minor premise, and `s` the `succ` one,
/// whose type `∀ n, C n → C (succ n)` becomes `fs(N, fs(T,T))` once the motive
/// is constant. See the `N.rec` feasibility entry in `INDUCTIVES.md` for why a
/// constant motive is what `075_nRecReduction` actually has.
pub fn premise(s: &Sums, nat: &Nat, z: &Term, su: &Term, t: &Term) -> Formula {
    Formula::and(
        Formula::mem(z.clone(), t.clone()),
        Formula::mem(
            su.clone(),
            s.fs.of(nat.ty.clone(), s.fs.of(t.clone(), t.clone())),
        ),
    )
}

/// `⊢ HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T))`.
///
/// [`crate::wnat`]'s case analysis once more, now on the step's own tag
/// argument. At `inl •` the fibre is `0`, so `f` and `r` are forced to `∅`
/// ([`crate::wtype::empty_funspace`]), the triple is `k₀` and the value is `z`.
/// At `inr •` the fibre is `1`, so `f ∈ fs(1,N)` and `r ∈ fs(1,T)` — both inside
/// the power sets the Replacement ranges over, by
/// [`crate::funspace::funspace_subset_pow_prod`] — the triple is `key(f,r)` and
/// the value is `app(app(s,app(f,•)),app(r,•))`, typed by four applications of
/// [`crate::ext::funspace_app_mem`].
///
/// This is where `HYP` is used and the *only* place: `z ∈ T` types the zero
/// branch and `s ∈ fs(N,fs(T,T))` types the `succ` one. `Bool` needed neither,
/// because `T := {fls,tru}` contained the step's only two values by
/// construction; once the value is an application no such target exists.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_typed_at(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    nat: &Nat,
    sy: &StepSyms,
    app_zero: &Thm,
    app_succ: &Thm,
    z: &Term,
    su: &Term,
    t: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, zero_s) = (s.unit(), s.point(), s.zero());
    let u = bnd.universe_of(nat.tags.clone());
    let step = sy.step_of(wt, z, su, t);
    let hyp = premise(s, nat, z, su, t);

    let prod_empty = crate::wtype::empty_product(env, s)?;
    let empty_fs = crate::wtype::empty_funspace(env, s, &prod_empty)?;

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre = wt.fibre(nat.fam.clone(), ta.clone());

    let app_at = inst_all(app_succ, &[tf.clone(), tr.clone()])?;

    let ma = Formula::mem(ta.clone(), nat.tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), nat.ty.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre.clone(), t.clone()));
    let hm = Formula::and(hyp.clone(), ma.clone());
    let front = Formula::and(hm.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());

    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr.clone());
    let p_hm = syl(&p_front, &and_left(hm.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(hm.clone(), mf.clone()))?;
    let p_hyp = syl(&p_hm, &and_left(hyp.clone(), ma.clone()))?;
    let p_ma = syl(&p_hm, &and_right(hyp.clone(), ma.clone()))?;
    let p_z = syl(
        &p_hyp,
        &and_left(
            Formula::mem(z.clone(), t.clone()),
            Formula::mem(su.clone(), s.fs.of(nat.ty.clone(), s.fs.of(t.clone(), t.clone()))),
        ),
    )?;
    let p_su = syl(
        &p_hyp,
        &and_right(
            Formula::mem(z.clone(), t.clone()),
            Formula::mem(su.clone(), s.fs.of(nat.ty.clone(), s.fs.of(t.clone(), t.clone()))),
        ),
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

    let branch = |env: &mut Env, second: bool| -> Option<Thm> {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let inj = |q: Term| if second { s.inr(q) } else { s.inl(q) };
        let k_body = Formula::and(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), inj(tx.clone())),
        );
        let k = Formula::and(p.clone(), k_body.clone());
        let k_p = and_left(p.clone(), k_body.clone());
        let k_case = and_right(p.clone(), k_body.clone());
        let k_x = syl(
            &k_case,
            &and_left(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), inj(tx.clone())),
            ),
        )?;
        let k_eq = syl(
            &k_case,
            &and_right(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), inj(tx.clone())),
            ),
        )?;
        // `K → a = inj(•)`, hence `K → app(B,a) = 0` (or `= 1`).
        let k_pt = syl(&k_x, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let k_inj = hyp_congr(env, &k_pt, inj)?;
        let k_a = hyp_eq_trans(env, &k_eq, &k_inj)?;
        let fibre_eq = if second { &nat.fibre_succ } else { &nat.fibre_zero };
        let k_cong = hyp_congr(env, &k_a, |q| wt.fibre(nat.fam.clone(), q))?;
        let k_fib = hyp_eq_trans(env, &k_cong, &a1i(fibre_eq, k.clone()))?;
        let dom = if second { one.clone() } else { zero_s.clone() };

        let k_mf = syl(&k_p, &p_mf)?;
        let k_mr = syl(&k_p, &p_mr)?;

        // `K → g ∈ fs(D, cod)`, the fibre having been computed.
        let retype = |env: &mut Env, prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
            let cong = hyp_congr(env, &k_fib, |q| s.fs.of(q, cod.clone()))?;
            let hole = env.fresh_var();
            let leib = Thm::eq_leibniz(
                s.fs.of(fibre.clone(), cod.clone()),
                s.fs.of(dom.clone(), cod.clone()),
                hole,
                Formula::mem(g.clone(), Term::var(hole)),
            );
            hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &cong)?, prem)
        };
        let k_f = retype(env, &k_mf, &nat.ty, &tf)?;
        let k_r = retype(env, &k_mr, t, &tr)?;

        // `K → app(e, ⟨a,⟨f,r⟩⟩) = app(e, ⟨inj •, ⟨f',r'⟩⟩)`, the tag rewritten.
        let k_tag = hyp_congr(env, &k_a, |q| triple(&q, &tf, &tr))?;

        let (k_val, k_in_t) = if second {
            // ── `succ`: the step computes, and the value is typed ────────────
            let sub = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
                let inc = inst_all(&s.fs.fs_sub, &[one.clone(), cod.clone()])?;
                let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
                syl(prem, &at)
            };
            let k_fw = sub(&k_f, &nat.ty, &tf)?;
            let k_ft = sub(&k_r, t, &tr)?;
            let k_app = hyp_mp(&a1i(&app_at, k.clone()), &hyp_and(&k_fw, &k_ft)?)?;
            let k_val = hyp_eq_trans(env, &k_tag, &k_app)?;

            let k_pt_mem = a1i(&s.unit_mem, k.clone());
            let fx = ap.apply(tf.clone(), point.clone());
            let k_fx = applied(&k_f, &k_pt_mem, &one, &nat.ty, &tf, &point)?;
            let k_rx = applied(&k_r, &k_pt_mem, &one, t, &tr, &point)?;
            let k_su = syl(&k_p, &p_su)?;
            let fst = s.fs.of(t.clone(), t.clone());
            let k_sfx = applied(&k_su, &k_fx, &nat.ty, &fst, su, &fx)?;
            let k_in_t = applied(
                &k_sfx,
                &k_rx,
                t,
                t,
                &ap.apply(su.clone(), fx.clone()),
                &ap.apply(tr.clone(), point.clone()),
            )?;
            (k_val, k_in_t)
        } else {
            // ── zero: both families are forced to `∅` ────────────────────────
            let forced = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
                syl(prem, &inst_all(&empty_fs, &[cod.clone(), g.clone()])?)
            };
            let k_f0 = forced(&k_f, &nat.ty, &tf)?;
            let k_r0 = forced(&k_r, t, &tr)?;
            let e1 = hyp_congr(env, &k_f0, |q| triple(&inj(point.clone()), &q, &tr))?;
            let e2 = hyp_congr(env, &k_r0, |q| {
                triple(&inj(point.clone()), &zero_s, &q)
            })?;
            let collapse = hyp_eq_trans(env, &e1, &e2)?;
            let to_key = hyp_eq_trans(env, &k_tag, &collapse)?;
            let k_val = hyp_eq_trans(env, &to_key, &a1i(app_zero, k.clone()))?;
            (k_val, syl(&k_p, &p_z)?)
        };

        // `K → app(e,⟨a,⟨f,r⟩⟩) ∈ T`, the value carried back.
        let (_, veq) = k_val.concl().as_imp()?;
        let (lhs, rhs) = veq.as_eq()?;
        let back = hyp_eq_symm(env, &k_val)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            rhs,
            lhs,
            hole,
            Formula::mem(Term::var(hole), t.clone()),
        );
        let k_goal = hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &back)?, &k_in_t)?;

        let per = crate::exists_elim_imp(
            xv,
            &Thm::gen(xv, &crate::com12(&uncurry(&k_goal)?)?),
            &Formula::imp(p.clone(), goal.clone()),
        )?;
        crate::com12(&per)
    };

    let cases = syl(
        &p_ma,
        &inst_all(&s.sum_cases, &[one.clone(), one.clone(), ta.clone()])?,
    )?;
    let left = branch(env, false)?;
    let right = branch(env, true)?;
    let body = hyp_or_elim(&cases, &left, &right)?;

    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let over_f = gen_under(fv, &hm, &uncurry(&over_r)?)?;
    let out = gen_under(av, &hyp, &uncurry(&over_f)?)?;
    if *out.concl()
        != Formula::imp(
            hyp,
            crate::wrec_total::step_typed(env, s, wt, &nat.tags, &nat.fam, &u, t, &step),
        )
    {
        return None
    }
    Some(out)
}
