//! Four facts about `∅`, and why they are load-bearing.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀S. ∅ ∈ fs(∅, S)                                       [empty_is_a_function]
//! ⊢ ∀a. app(∅, a) = ∅                                             [app_of_empty]
//! ⊢ ∀x. prod(∅, x) = ∅                                           [empty_product]
//! ⊢ ∀x ∀f. (f ∈ fs(∅,x) → f = ∅)                                 [empty_funspace]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What they are for
//!
//! These are not incidental: they are what makes the whole of [`crate::wtype`]
//! non-vacuous, and what makes every one-point instance in the development
//! compute.
//!
//! [`super::unit_wtype_inhabited`] needs a family `B` with empty fibres and a
//! function out of an empty domain. `∅` serves as **both**: [`app_of_empty`]
//! gives `app(∅,a) = ∅` for *every* `a`, which is all `closed` ever asks of a
//! family, and [`empty_is_a_function`] gives `∅ ∈ fs(∅,S)` for every `S`. So the
//! unit W-type needs no new symbol at all.
//!
//! [`empty_funspace`] is the converse and is what makes the recursors compute:
//! at a fibre-free constructor the function and the recursive-value argument are
//! *forced* to be `∅`, so the step term reduces to a closed term with nothing
//! left to case on. [`crate::wbool_rec`], [`crate::wnat_rec`] and
//! [`crate::wrec_unit`] all turn on it. [`empty_product`] is the lemma it runs
//! through: a function into `fs(∅,x)` is a subset of `prod(∅,x)`, and that is
//! `∅`.

use kernel::{Env, Formula, Term, Thm};
use crate::funspace::{is_function, is_single_valued, is_total};
use crate::sums::Sums;
use crate::separation::{hyp_ex_falso, hyp_syl};
use crate::{
    a1i, and_intro, and_left, contrapos, ex_falso, gen_all, hyp_and, iff_mp, iff_mpr, inst_all,
    notnot_intro, syl,
};


/// `⊢ ∀S. ∅ ∈ fs(∅, S)` — the empty set is the empty function, into anything.
///
/// All three clauses of `isfun` are vacuous: `∅` has no members, so it is a
/// subset of the product, it is total on `∅`, and it is single-valued. Each
/// falls straight out of `⊢ ∀z. ¬(z ∈ ∅)` by ex falso.
///
/// This is what makes the W-type's base case reachable: a constructor with no
/// recursive arguments is `⟨a, ∅⟩`, and its typing rule asks exactly for
/// `∅ ∈ fs(0, S)`.
pub fn empty_is_a_function(env: &mut Env, s: &Sums) -> Option<Thm> {
    let sv = env.fresh_var();
    let ts = Term::var(sv);
    let e = Term::apply(s.ap.empty, vec![]);

    let isfun = is_function(env, &s.ap.sets, &s.prod, &e, &ts, &e);
    let sub = kernel::thm::subset(env, e.clone(), s.prod.of(e.clone(), ts.clone()));
    let total = is_total(env, &s.ap.sets, &e, &ts, &e);
    let single = is_single_valued(env, &s.ap.sets, &e);
    if isfun != Formula::and(sub.clone(), Formula::and(total.clone(), single.clone())) {
        return None
    }

    // ── ∅ ⊆ prod(∅,S) ────────────────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let not_z = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?;
    let sub_thm = Thm::gen(
        zv,
        &syl(&not_z, &ex_falso(Formula::mem(tz.clone(), s.prod.of(e.clone(), ts.clone()))))?,
    );
    if *sub_thm.concl() != sub {
        return None
    }

    // ── total on ∅ ───────────────────────────────────────────────────────────
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let body = Formula::and(
        Formula::mem(ty.clone(), ts.clone()),
        Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), e.clone()),
    );
    let not_x = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tx))?;
    let total_thm = Thm::gen(xv, &syl(&not_x, &ex_falso(Formula::exists(yv, body)))?);
    if *total_thm.concl() != total {
        return None
    }

    // ── single-valued ────────────────────────────────────────────────────────
    let y2v = env.fresh_var();
    let ty2 = Term::var(y2v);
    let p1 = Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), e.clone());
    let p2 = Formula::mem(s.ap.sets.pair(tx.clone(), ty2.clone()), e.clone());
    let not_p1 = inst_all(&s.ap.empty_ax, &[s.ap.sets.pair(tx, ty.clone())])?;
    let sv_thm = gen_all(
        &[xv, yv, y2v],
        &syl(
            &syl(&and_left(p1, p2), &not_p1)?,
            &ex_falso(Formula::eq(ty, ty2)),
        )?,
    );
    if *sv_thm.concl() != single {
        return None
    }

    let fs_at = inst_all(&s.fs.fs_ax, &[e.clone(), ts.clone(), e.clone()])?;
    let mem = Formula::mem(e.clone(), s.fs.of(e.clone(), ts.clone()));
    if *fs_at.concl() != Formula::iff(mem.clone(), isfun) {
        return None
    }
    let out = Thm::mp(
        &iff_mpr(&fs_at)?,
        &and_intro(&sub_thm, &and_intro(&total_thm, &sv_thm)),
    )?;
    debug_assert_eq!(*out.concl(), mem, "empty_is_a_function: unexpected shape");
    Some(Thm::gen(sv, &out))
}

/// `⊢ ∀a. app(∅, a) = ∅` — `∅` is the constant-empty family.
///
/// Nothing is a pair in `∅`, so `∅` has empty domain and
/// [`crate::funcs::app_off_domain`] applies at every argument. This is what
/// lets the non-vacuity witness take `B := ∅` rather than building a lambda:
/// `closed` only ever mentions `B` through `app(B,a)`, and here that is `∅`
/// unconditionally.
pub fn app_of_empty(env: &mut Env, s: &Sums) -> Option<Thm> {
    let off = crate::funcs::app_off_domain(env, &s.ap)?;
    let (av, yv) = (env.fresh_var(), env.fresh_var());
    let (ta, ty) = (Term::var(av), Term::var(yv));
    let e = Term::apply(s.ap.empty, vec![]);

    let pair = s.ap.sets.pair(ta.clone(), ty.clone());
    let l = Formula::mem(pair.clone(), e.clone());
    let all_not = Thm::gen(yv, &inst_all(&s.ap.empty_ax, std::slice::from_ref(&pair))?);
    // `¬∃y. l` *is* `¬¬∀y. ¬l`, so double-negation introduction closes it.
    let no_pair = Thm::mp(&notnot_intro(Formula::forall(yv, Formula::not(l.clone()))), &all_not)?;

    let at = inst_all(&off, &[e.clone(), ta.clone()])?;
    if *at.concl()
        != Formula::imp(
            Formula::not(Formula::exists(yv, l)),
            Formula::eq(s.ap.apply(e.clone(), ta.clone()), e.clone()),
        )
    {
        return None
    }
    let out = Thm::mp(&at, &no_pair)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(s.ap.apply(e.clone(), ta), e),
        "app_of_empty: unexpected shape"
    );
    Some(Thm::gen(av, &out))
}

/// `⊢ ∀T ∀z. ¬(z ∈ prod(∅,T))` — a product with an empty factor is empty.
///
/// Immediate from the product's characteristic property: its membership
/// condition opens with `∃x. (x ∈ ∅ ∧ …)`, and nothing is in `∅`.
pub fn empty_product(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (tv, zv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, tz, tx, ty) = (Term::var(tv), Term::var(zv), Term::var(xv), Term::var(yv));
    let e = Term::apply(s.ap.empty, vec![]);

    let inner = Formula::exists(
        yv,
        Formula::and(
            Formula::mem(ty.clone(), tt.clone()),
            Formula::eq(tz.clone(), s.ap.sets.pair(tx.clone(), ty)),
        ),
    );
    let mem_xe = Formula::mem(tx.clone(), e.clone());
    let body = Formula::and(mem_xe.clone(), inner.clone());
    let cond = Formula::exists(xv, body.clone());

    let prod_t = s.prod.of(e.clone(), tt.clone());
    let at = inst_all(&s.prod.prod_ax, &[e.clone(), tt.clone(), tz.clone()])?;
    if *at.concl() != Formula::iff(Formula::mem(tz.clone(), prod_t.clone()), cond) {
        return None
    }

    let not_x = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tx))?;
    let body_false = syl(&and_left(mem_xe, inner), &not_x)?;
    let no_body = Thm::mp(
        &notnot_intro(Formula::forall(xv, Formula::not(body))),
        &Thm::gen(xv, &body_false),
    )?;
    let out = Thm::mp(&contrapos(&iff_mp(&at)?)?, &no_body)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::mem(tz, prod_t)),
        "empty_product: unexpected shape"
    );
    Some(gen_all(&[tv, zv], &out))
}

/// `⊢ ∀T ∀f. (f ∈ fs(∅,T) → f = ∅)` — the empty function is the *only*
/// function out of `∅`.
///
/// The converse of [`empty_is_a_function`], and the half that makes the
/// concrete bound below closed: a function out of `∅` is a subset of
/// `prod(∅,T)`, which [`empty_product`] shows is empty, so it has no members
/// and Extensionality identifies it with `∅`.
pub fn empty_funspace(env: &mut Env, s: &Sums, prod_empty: &Thm) -> Option<Thm> {
    let (tv, fv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, tf, tz) = (Term::var(tv), Term::var(fv), Term::var(zv));
    let e = Term::apply(s.ap.empty, vec![]);

    let isfun = is_function(env, &s.ap.sets, &s.prod, &e, &tt, &tf);
    let sub = kernel::thm::subset(env, tf.clone(), s.prod.of(e.clone(), tt.clone()));
    let rest = Formula::and(
        is_total(env, &s.ap.sets, &e, &tt, &tf),
        is_single_valued(env, &s.ap.sets, &tf),
    );
    if isfun != Formula::and(sub.clone(), rest.clone()) {
        return None
    }

    let mem_fs = Formula::mem(tf.clone(), s.fs.of(e.clone(), tt.clone()));
    let fs_at = inst_all(&s.fs.fs_ax, &[e.clone(), tt.clone(), tf.clone()])?;
    if *fs_at.concl() != Formula::iff(mem_fs.clone(), isfun) {
        return None
    }
    let h_sub = syl(&iff_mp(&fs_at)?, &and_left(sub.clone(), rest))?;

    let pe = inst_all(prod_empty, &[tt, tz.clone()])?;
    let h_not = hyp_syl(
        &syl(&h_sub, &Thm::ax_inst(sub, tz.clone())?)?,
        &a1i(&pe, mem_fs.clone()),
    )?;

    let mem_zf = Formula::mem(tz.clone(), tf.clone());
    let mem_ze = Formula::mem(tz.clone(), e.clone());
    let not_ze = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?;
    let fwd = hyp_ex_falso(&h_not, mem_ze.clone())?;
    let bwd = hyp_ex_falso(&a1i(&not_ze, mem_fs.clone()), mem_zf.clone())?;
    let h_all = Thm::mp(
        &Thm::ax_dist(zv, mem_fs.clone(), Formula::iff(mem_zf, mem_ze))?,
        &Thm::gen(zv, &hyp_and(&fwd, &bwd)?),
    )?;
    let ext = inst_all(&Thm::ax_extensionality(env), &[tf.clone(), e.clone()])?;
    let out = syl(&h_all, &ext)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(mem_fs, Formula::eq(tf, e)),
        "empty_funspace: unexpected shape"
    );
    Some(gen_all(&[tv, fv], &out))
}
