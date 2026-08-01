//! The step's typing hypothesis, discharged — and with it, the whole recursor.
//!
//! # Interface
//!
//! ```text
//! ⊢ step_typed({c}, ∅, U(c), T, e)                          [unit_step_typed]
//! ⊢ wrec({c}, ∅, U(c), T, e) ∈ fs(W, T)                       [unit_funspace]
//! ⊢ app(wrec({c}, ∅, U(c), T, e), ⟨c,∅⟩) = app(e, ⟨c,⟨∅,∅⟩⟩)      [unit_iota]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why this is the second point of the module
//!
//! [`crate::wrec_total`]'s three theorems all carry
//! `closed(A,B,u) ∧ step_typed(A,B,u,T,e)`, and `step_typed` is a hypothesis the
//! general construction cannot discharge — `e` is an arbitrary set. A theorem
//! whose antecedent no five sets satisfy proves nothing. This file satisfies it.
//!
//! [`unit_funspace`] then has **no antecedent left**: both hypotheses of
//! [`crate::wrec_total::wrec_funspace`] are gone.
//!
//! [`unit_iota`] is the *general* ι rule fired at this instance, and
//! `tests/wrec_total.rs` checks it is literally the same formula
//! [`super::iota_fires`] proves by hand — two independent routes, one equation.
//!
//! # Why `step_typed` is cheap here, and why that does not generalise
//!
//! The fibre is `∅`, and [`crate::wtype::empty_funspace`] makes `∅` the only
//! function out of `∅`, so the step's two function arguments are *forced* and
//! its value is the closed term `V`. `T` is `{V}`, so the value is in the motive
//! by reflexivity. Nothing about that survives a constructor with a non-empty
//! fibre — which is exactly why the general theorems carry the hypothesis.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::bound::Bound;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, hyp_mp, iff_mp, iff_mpr, inst_all, singleton, syl,
    uncurry,
};

use super::shared::{congr, eq_trans};
use super::composite::comp_empty_domain;
use super::instance::unit_wtype;
use super::attempt::{unit_target, unit_value};

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
fn gen_under(v: kernel::FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// **The step is typed, here.**
///
/// ```text
/// ⊢ step_typed({c}, ∅, U(c), {V}, e)     with  V := app(e, ⟨c,⟨∅,∅⟩⟩)
/// ```
///
/// [`crate::wrec_total`]'s hypothesis on the step, **satisfied by a concrete
/// five-tuple** — which is what stops [`crate::wrec_total::totality`] and
/// [`crate::wrec_total::iota`] from being statements about an antecedent no
/// sets fulfil.
///
/// It holds for a reason that does not generalise, and that is the point of
/// this instance: the fibre `B(a) = app(∅,a)` is `∅`
/// ([`crate::wtype::app_of_empty`]), and `∅` is the *only* function out of `∅`
/// ([`crate::wtype::empty_funspace`]), so `f` and `r` are forced to be `∅` and
/// `a` is forced to be `c`. The step's value is then the closed term `V`, and
/// the target `{V}` contains it by reflexivity.
pub fn unit_step_typed(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    c: &Term,
    e: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let up = ap.sets.up;
    let u = Term::apply(bnd.lu, vec![c.clone()]);
    let z = wt.empty();
    let sing_c = singleton(up, c.clone());
    let w_t = wt.of(sing_c.clone(), z.clone(), u.clone());
    let v = unit_value(ap, c, e);
    let t_t = unit_target(ap, c, e);

    let prod_empty = crate::wtype::empty_product(env, s)?;
    let empty_fs = crate::wtype::empty_funspace(env, s, &prod_empty)?;

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre = wt.fibre(z.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), sing_c.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), w_t.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre.clone(), t_t.clone()));
    let front = Formula::and(ma.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());
    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr);
    let p_ma = syl(&p_front, &and_left(ma.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(ma.clone(), mf))?;

    // `a = c`, and the fibre collapses to `∅`.
    let p_a = syl(
        &p_ma,
        &iff_mp(&inst_all(&ap.mem_sing, &[c.clone(), ta.clone()])?)?,
    )?;
    let app_empty = inst_all(&wt.app_empty, std::slice::from_ref(&ta))?;

    let cong_w = congr(env, &app_empty, |t| s.fs.of(t, w_t.clone()))?;
    let hole_w = env.fresh_var();
    let f_into = Thm::mp(
        &Thm::eq_leibniz(
            s.fs.of(fibre.clone(), w_t.clone()),
            s.fs.of(z.clone(), w_t.clone()),
            hole_w,
            Formula::mem(tf.clone(), Term::var(hole_w)),
        ),
        &cong_w,
    )?;
    let p_f = syl(
        &p_mf,
        &syl(&f_into, &inst_all(&empty_fs, &[w_t.clone(), tf.clone()])?)?,
    )?;

    let cong_t = congr(env, &app_empty, |t| s.fs.of(t, t_t.clone()))?;
    let hole_t = env.fresh_var();
    let r_into = Thm::mp(
        &Thm::eq_leibniz(
            s.fs.of(fibre, t_t.clone()),
            s.fs.of(z.clone(), t_t.clone()),
            hole_t,
            Formula::mem(tr.clone(), Term::var(hole_t)),
        ),
        &cong_t,
    )?;
    let p_r = syl(
        &p_mr,
        &syl(&r_into, &inst_all(&empty_fs, &[t_t.clone(), tr.clone()])?)?,
    )?;

    // `app(e, ⟨a,⟨f,r⟩⟩) = app(e, ⟨c,⟨∅,∅⟩⟩) = V`, one component at a time.
    let step = |x: &Term, y: &Term, w: &Term| {
        ap.apply(
            e.clone(),
            ap.sets.pair(x.clone(), ap.sets.pair(y.clone(), w.clone())),
        )
    };
    let e1 = hyp_congr(env, &p_a, |t| step(&t, &tf, &tr))?;
    let e2 = hyp_congr(env, &p_f, |t| step(c, &t, &tr))?;
    let e3 = hyp_congr(env, &p_r, |t| step(c, &z, &t))?;
    let e12 = hyp_eq_trans(env, &e1, &e2)?;
    let chain = hyp_eq_trans(env, &e12, &e3)?;
    debug_assert_eq!(
        *chain.concl(),
        Formula::imp(p.clone(), Formula::eq(step(&ta, &tf, &tr), v.clone())),
        "unit_step_typed: the value does not collapse to V"
    );

    // …so it is in `{V}`.
    let v_in_t = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[v.clone(), v.clone()])?)?,
        &Thm::eq_refl(v.clone()),
    )?;
    let back = hyp_eq_symm(env, &chain)?;
    let hole = env.fresh_var();
    let lift = hyp_mp(
        &a1i(
            &Thm::eq_leibniz(
                v.clone(),
                step(&ta, &tf, &tr),
                hole,
                Formula::mem(Term::var(hole), t_t.clone()),
            ),
            p.clone(),
        ),
        &back,
    )?;
    let body = hyp_mp(&lift, &a1i(&v_in_t, p))?;

    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let over_f = gen_under(fv, &ma, &uncurry(&over_r)?)?;
    let out = Thm::gen(av, &over_f);
    debug_assert_eq!(
        *out.concl(),
        crate::wrec_total::step_typed(env, s, wt, &sing_c, &z, &u, &t_t, e),
        "unit_step_typed: the hypothesis has the wrong shape"
    );
    Some(out)
}

/// **The recursor is a function, unconditionally, at the unit instance.**
///
/// ```text
/// ⊢ wrec({c}, ∅, U(c), {V}, e) ∈ fs(W({c}, ∅, U(c)), {V})
/// ```
///
/// [`crate::wrec_total::wrec_funspace`] with **both** of its hypotheses
/// discharged: `closed({c},∅,U(c))` by [`unit_wtype`] and
/// `step_typed({c},∅,U(c),{V},e)` by [`unit_step_typed`]. No antecedent
/// survives, so the general theorem is not vacuous — some five sets satisfy
/// its premise, and at them the recursor really is a function into the target.
///
/// `funspace` is [`crate::wrec_total::wrec_funspace`] and `rec` the symbol
/// [`crate::wrec::wrec_symbol`] introduced.
#[allow(clippy::too_many_arguments)]
pub fn unit_funspace(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    rec: FnSym,
    funspace: &Thm,
    c: &Term,
    e: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let up = s.ap.sets.up;
    let u = Term::apply(bnd.lu, vec![c.clone()]);
    let z = wt.empty();
    let sing_c = singleton(up, c.clone());
    let t_t = unit_target(&s.ap, c, e);

    let uw = unit_wtype(env, wt, bnd, c)?;
    let st = unit_step_typed(env, wt, bnd, c, e)?;
    let at = inst_all(
        funspace,
        &[sing_c.clone(), z.clone(), u.clone(), t_t.clone(), e.clone()],
    )?;
    let out = Thm::mp(&at, &and_intro(&uw.closed, &st))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(
            Term::apply(
                rec,
                vec![sing_c.clone(), z.clone(), u.clone(), t_t.clone(), e.clone()]
            ),
            s.fs.of(wt.of(sing_c, z, u), t_t)
        ),
        "unit_funspace: the conclusion has the wrong shape"
    );
    Some(out)
}

/// **The general ι rule computes, at the unit instance.**
///
/// ```text
/// ⊢ app(wrec({c}, ∅, U(c), {V}, e), ⟨c,∅⟩) = app(e, ⟨c, ⟨∅,∅⟩⟩)
/// ```
///
/// — the *same statement* `iota_fires` proves, but reached the other way
/// round: through [`crate::wrec_total::iota`], with both of its hypotheses
/// discharged and its two premises `c ∈ {c}` and `∅ ∈ fs(B(c), W)` supplied,
/// and then with the composite `comp(wrec, ∅, app(∅,c))` collapsed by
/// [`comp_empty_domain`].
///
/// `tests/wrec_total.rs` checks the two conclusions are literally equal. That
/// is the cross-check the general development most wants: `iota_fires` builds
/// a one-point attempt by hand and reads the value off it, while this goes
/// through totality, the one-point extension and structural induction. If the
/// two ever disagreed, one of them would be about a different recursor.
#[allow(clippy::too_many_arguments)]
pub fn unit_iota(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    comp: FnSym,
    comp_ax: &Thm,
    rec: FnSym,
    iota: &Thm,
    c: &Term,
    e: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let up = ap.sets.up;
    let u = Term::apply(bnd.lu, vec![c.clone()]);
    let z = wt.empty();
    let sing_c = singleton(up, c.clone());
    let w_t = wt.of(sing_c.clone(), z.clone(), u.clone());
    let t_t = unit_target(ap, c, e);
    let v = unit_value(ap, c, e);
    let w0 = wt.sup(c.clone(), z.clone());
    let rec_t = Term::apply(rec, vec![sing_c.clone(), z.clone(), u.clone(), t_t.clone(), e.clone()]);

    let uw = unit_wtype(env, wt, bnd, c)?;
    let st = unit_step_typed(env, wt, bnd, c, e)?;
    let dis = Thm::mp(
        &inst_all(iota, &[sing_c, z.clone(), u, t_t, e.clone()])?,
        &and_intro(&uw.closed, &st),
    )?;
    let at_cf = inst_all(&dis, &[c.clone(), z.clone()])?;

    // `c ∈ {c}` and `∅ ∈ fs(app(∅,c), W)`.
    let c_in = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[c.clone(), c.clone()])?)?,
        &Thm::eq_refl(c.clone()),
    )?;
    let app_empty = inst_all(&wt.app_empty, std::slice::from_ref(c))?;
    let back = crate::eq_symm(env, &app_empty)?;
    let cong = congr(env, &back, |t| s.fs.of(t, w_t.clone()))?;
    let hole = env.fresh_var();
    let f_in = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                s.fs.of(z.clone(), w_t.clone()),
                s.fs.of(ap.apply(z.clone(), c.clone()), w_t.clone()),
                hole,
                Formula::mem(z.clone(), Term::var(hole)),
            ),
            &cong,
        )?,
        &inst_all(&wt.empty_fun, std::slice::from_ref(&w_t))?,
    )?;
    let fired = Thm::mp(&at_cf, &and_intro(&c_in, &f_in))?;

    // The composite over an empty fibre collapses, so the value is closed.
    let coll = congr(env, &app_empty, |t| comp_of(comp, rec_t.clone(), z.clone(), t))?;
    let empty = inst_all(
        &comp_empty_domain(env, ap, comp, comp_ax)?,
        &[rec_t.clone(), z.clone()],
    )?;
    let to_empty = eq_trans(env, &coll, &empty)?;
    let rhs = congr(env, &to_empty, |t| {
        ap.apply(e.clone(), ap.sets.pair(c.clone(), ap.sets.pair(z.clone(), t)))
    })?;
    let out = eq_trans(env, &fired, &rhs)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(ap.apply(rec_t, w0), v),
        "unit_iota: the computed equation has the wrong shape"
    );
    Some(out)
}
