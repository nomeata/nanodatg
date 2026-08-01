//! Reading a value off a function: `app` against a graph, and against a member
//! of a function space.
//!
//! # Interface
//!
//! Writing `sv(f)` for [`crate::funspace::is_single_valued`] and `app(f,x)` for
//! [`crate::funcs::Apply`]'s application, the exports are
//!
//! ```text
//! ⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)        [app_of_pair]
//! ⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)   [funspace_app_mem]
//! ```
//!
//! Callers need neither derivation.
//!
//! [`app_of_pair`] is what connects the *graph* a function space talks about to
//! the `app` everything else talks about. It is the same argument
//! [`crate::funcs::beta_conditional`] runs for lambda graphs, with
//! single-valuedness in place of injectivity of the Kuratowski pair — and,
//! unlike beta reduction, it needs no membership antecedent, since `⟨x,y⟩ ∈ f`
//! already says `x` is in the domain. That is what makes it usable against a
//! function given only as a member of a function space, which is exactly what
//! [`funspace_app_mem`] does with it.
//!
//! The membership antecedent on [`funspace_app_mem`] is genuine: off the domain
//! `app(f,x)` is `∅` (see [`crate::funcs::app_off_domain`]), which need not be
//! in `b`.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::funspace::{is_single_valued, Funspace, Product};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, mpd_const, syl, uncurry,
};
use super::shared::{discharge, hyp_eq_symm, hyp_leibniz, inst_all_imp, isfun_parts};

/// `⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)` — the value of a
/// single-valued graph at a point it relates.
///
/// `app(f,x)` is `⋃{ y' : ⟨x,y'⟩ ∈ f }`, so this is the same argument
/// [`crate::funcs::beta_conditional`] runs for lambda graphs, with
/// single-valuedness in place of injectivity of the Kuratowski pair: the
/// collection has `y` as a member, single-valuedness forces every member to
/// equal `y`, so the collection is `{y}` and the union strips it off.
///
/// Unlike beta reduction this needs no membership antecedent — `⟨x,y⟩ ∈ f` is
/// already the statement that `x` is in the domain — which is what makes it
/// usable against a function given only as a member of a function space.
pub fn app_of_pair(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (f, x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tx, ty, tz) = (Term::var(f), Term::var(x), Term::var(y), Term::var(z));

    let sv = is_single_valued(env, &ap.sets, &tf);
    let mem_pair = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), tf.clone());
    let h = Formula::and(sv.clone(), mem_pair.clone());
    let h_sv = and_left(sv.clone(), mem_pair.clone());
    let h_pair = and_right(sv.clone(), mem_pair.clone());

    let coll_t = ap.coll_of(tf.clone(), tx.clone());
    let sing = crate::singleton(ap.sets.up, ty.clone());
    let mem_zc = Formula::mem(tz.clone(), coll_t.clone());
    let mem_zs = Formula::mem(tz.clone(), sing.clone());
    let mem_pair_z = Formula::mem(ap.sets.pair(tx.clone(), tz.clone()), tf.clone());
    let eq_zy = Formula::eq(tz.clone(), ty.clone());

    // The two characterisations this rests on, checked rather than assumed.
    let coll_at = inst_all(&ap.coll_members, &[tf.clone(), tx.clone(), tz.clone()])?;
    if *coll_at.concl() != Formula::iff(mem_zc.clone(), mem_pair_z.clone()) {
        return None
    }
    let ms = inst_all(&ap.mem_sing, &[ty.clone(), tz.clone()])?;
    if *ms.concl() != Formula::iff(mem_zs.clone(), eq_zy.clone()) {
        return None
    }

    // ── H → (⟨x,z⟩ ∈ f → z = y), single-valuedness at ⟨x,z⟩ and ⟨x,y⟩ ────────
    let sv_at = inst_all_imp(&sv, &[tx.clone(), tz.clone(), ty.clone()])?;
    let sv_body = Formula::imp(Formula::and(mem_pair_z.clone(), mem_pair.clone()), eq_zy.clone());
    if *sv_at.concl() != Formula::imp(sv.clone(), sv_body) {
        return None
    }
    let k_h = and_left(h.clone(), mem_pair_z.clone());
    let k_pz = and_right(h.clone(), mem_pair_z.clone());
    let k_conj = hyp_and(&k_pz, &syl(&k_h, &h_pair)?)?;
    let h_z_eq = uncurry(&hyp_mp(&syl(&syl(&k_h, &h_sv)?, &sv_at)?, &k_conj)?)?;

    // ── coll(f,x) and {y} have the same members ──────────────────────────────
    let fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&coll_at)?, h.clone()), &h_z_eq)?,
        &a1i(&iff_mpr(&ms)?, h.clone()),
    )?;

    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        ty.clone(),
        tz.clone(),
        w,
        Formula::mem(ap.sets.pair(tx.clone(), Term::var(w)), tf.clone()),
    );
    let h_eq_pair =
        syl(&h_pair, &com12(&syl(&eq_symm_imp(env, tz.clone(), ty.clone()), &carry)?)?)?;
    let bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &h_eq_pair)?,
        &a1i(&iff_mpr(&coll_at)?, h.clone()),
    )?;

    let h_all = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::iff(mem_zc, mem_zs))?,
        &Thm::gen(z, &hyp_and(&fwd, &bwd)?),
    )?;
    let h_coll_eq = syl(&h_all, &inst_all(&ext, &[coll_t.clone(), sing.clone()])?)?;

    // ── app(f,x) = ⋃coll(f,x) = ⋃{y} = y ─────────────────────────────────────
    let ucoll = ap.sets.union_of(coll_t.clone());
    let using = ap.sets.union_of(sing.clone());
    let app_t = ap.apply(tf.clone(), tx.clone());

    let w2 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(
            coll_t,
            sing,
            w2,
            Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w2))),
        ),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_def = inst_all(&ap.app_ax, &[tf, tx])?;
    let w3 = env.fresh_var();
    let carry3 =
        Thm::eq_leibniz(ucoll, using.clone(), w3, Formula::eq(app_t.clone(), Term::var(w3)));
    let h_app_using =
        hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w4 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, ty.clone(), w4, Formula::eq(app_t.clone(), Term::var(w4))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&ty))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_t, ty)),
        "app_of_pair: unexpected shape"
    );
    Some(gen_all(&[f, x, y], &out))
}

/// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)` — a function's
/// values lie in its codomain.
///
/// Totality supplies *some* `y ∈ b` with `⟨x,y⟩ ∈ f`, and [`app_of_pair`] —
/// single-valuedness being the other clause of `isfun` — identifies that `y` as
/// `app(f,x)`. The membership antecedent is genuine: off the domain `app(f,x)`
/// is `∅` (see [`crate::funcs::app_off_domain`]), which need not be in `b`.
///
/// `p` and `fsp` must be the product and function space `fs` was built from,
/// and `ap` the application apparatus over the same [`crate::funcs::Sets`];
/// `app_pair` must be what [`app_of_pair`] produces for that `ap`. All of that
/// is checked rather than assumed.
pub fn funspace_app_mem(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    app_pair: &Thm,
) -> Option<Thm> {
    let (av, bv, f, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tx) = (Term::var(av), Term::var(bv), Term::var(f), Term::var(x));

    let mem_fs = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::and(mem_fs.clone(), mem_xa.clone());

    let (isfun, sub, total, sv) = isfun_parts(env, ap, p, &ta, &tb, &tf)?;
    let fs_at = inst_all(&fsp.fs_ax, &[ta.clone(), tb.clone(), tf.clone()])?;
    if *fs_at.concl() != Formula::iff(mem_fs.clone(), isfun) {
        return None
    }

    let rest = Formula::and(total.clone(), sv.clone());
    let h_isfun = syl(&and_left(mem_fs.clone(), mem_xa.clone()), &iff_mp(&fs_at)?)?;
    let h_rest = syl(&h_isfun, &and_right(sub, rest))?;
    let h_total = syl(&h_rest, &and_left(total.clone(), sv.clone()))?;
    let h_sv = syl(&h_rest, &and_right(total.clone(), sv.clone()))?;
    let h_xa = and_right(mem_fs, mem_xa);

    // ── H → ∃y. (y ∈ b ∧ ⟨x,y⟩ ∈ f), totality at this `x` ────────────────────
    let y = env.fresh_var();
    let ty = Term::var(y);
    let mem_yb = Formula::mem(ty.clone(), tb.clone());
    let mem_pair = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), tf.clone());
    let body = Formula::and(mem_yb.clone(), mem_pair.clone());
    let h_ex = hyp_mp(&syl(&h_total, &Thm::ax_inst(total, tx.clone())?)?, &h_xa)?;
    debug_assert_eq!(
        *h_ex.concl(),
        Formula::imp(h.clone(), Formula::exists(y, body.clone())),
        "funspace_app_mem: the totality clause has an unexpected shape"
    );

    // ── That `y` is `app(f,x)`, so `app(f,x) ∈ b` ────────────────────────────
    let j = Formula::and(h.clone(), body.clone());
    let j_h = and_left(h.clone(), body.clone());
    let j_body = and_right(h.clone(), body);
    let j_yb = syl(&j_body, &and_left(mem_yb.clone(), mem_pair.clone()))?;
    let j_pair = syl(&j_body, &and_right(mem_yb, mem_pair.clone()))?;
    let j_sv = syl(&j_h, &h_sv)?;

    let app_t = ap.apply(tf.clone(), tx.clone());
    let ap_at = inst_all(app_pair, &[tf, tx, ty.clone()])?;
    if *ap_at.concl()
        != Formula::imp(Formula::and(sv, mem_pair), Formula::eq(app_t.clone(), ty.clone()))
    {
        return None
    }
    let j_eq = hyp_mp(&a1i(&ap_at, j), &hyp_and(&j_sv, &j_pair)?)?;
    let w = env.fresh_var();
    let j_goal = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &j_eq)?, w, &Formula::mem(Term::var(w), tb.clone()))?,
        &j_yb,
    )?;

    let out = discharge(y, &h_ex, &j_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(app_t, tb)),
        "funspace_app_mem: unexpected shape"
    );
    Some(gen_all(&[av, bv, f, x], &out))
}
