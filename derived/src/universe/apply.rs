//! Closure under **application**: `app(f,x) ∈ u` whenever `f ∈ u`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀f ∀x. ((is_universe(u) ∧ f ∈ u) → coll(f,x) ∈ u)  [universe_coll_closed]
//! ⊢ ∀u ∀f ∀x. ((is_universe(u) ∧ f ∈ u) → app(f,x) ∈ u)   [universe_app_closed]
//! ⊢ ∀c ∀f ∀x. (f ∈ U(c) → app(f,x) ∈ U(c))                [least_universe_app]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What is and is not assumed about `f`
//!
//! **Nothing.** `f` need not be a function, need not be single-valued, and `x`
//! need not be in its domain; `app(f,x)` is `⋃{ y : ⟨x,y⟩ ∈ f }` whatever `f`
//! is, and off the domain it is `∅` ([`crate::funcs::app_off_domain`]). An
//! earlier note wanted this lemma with `sv(f)` as an extra hypothesis; it is
//! not needed, because the argument never looks at *which* values `f` takes,
//! only at where they live.
//!
//! # The route
//!
//! Three rungs, and the only universe facts used are `⋃`-closure and `C₂`:
//!
//! 1. `⋃f ∈ u` and then `⋃⋃f ∈ u`, by [`super::universe_union_closed`] twice;
//! 2. `coll(f,x) ⊆ ⋃⋃f` — [`crate::funcs::snd_in_union2`], the same superset
//!    lemma that made `coll` a legitimate instance of Separation in the first
//!    place — so `coll(f,x) ∈ u` by `C₂` ([`super::universe_sub_mem`]);
//! 3. `app(f,x) = ⋃coll(f,x)`, so one more `⋃`-closure.
//!
//! Note that step 2 is where the whole thing would fail without `C₁`: `⋃f ∈ u`
//! is `⋃`-closure, and `⋃`-closure is what the transitivity clause bought.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{snd_in_union2, Apply};
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};

use super::closure::least_universe_transfer;
use super::least::{in_all_universes, least_universe_mem};
use super::predicate::is_universe;

/// `⊢ ∀f ∀x. coll(f,x) ⊆ ⋃⋃f` — every value `f` could take at `x` lies two
/// unions up.
///
/// [`crate::funcs::snd_in_union2`] composed with `coll`'s membership condition.
/// This is the inclusion that made `coll` a legitimate instance of Separation,
/// re-used here as the inclusion `C₂` needs.
fn coll_subset_union2(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let (fv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tx, ty) = (Term::var(fv), Term::var(xv), Term::var(yv));
    let uuf = ap.sets.union_of(ap.sets.union_of(tf.clone()));
    let coll_t = ap.coll_of(tf.clone(), tx.clone());

    let members = inst_all(&ap.coll_members, &[tf.clone(), tx.clone(), ty.clone()])?;
    if *members.concl()
        != Formula::iff(
            Formula::mem(ty.clone(), coll_t.clone()),
            Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), tf.clone()),
        )
    {
        return None
    }
    let siu = inst_all(&snd_in_union2(env, &ap.sets)?, &[tf.clone(), tx.clone(), ty.clone()])?;
    let step = syl(&iff_mp(&members)?, &siu)?;
    let out = Thm::gen(yv, &step);
    if *out.concl() != kernel::thm::subset(env, coll_t, uuf) {
        return None
    }
    Some(gen_all(&[fv, xv], &out))
}

/// `⊢ ∀u ∀f ∀x. ((is_universe(u) ∧ f ∈ u) → coll(f,x) ∈ u)` — the collection of
/// `f`'s values at `x` is a member of any universe `f` is a member of.
///
/// `coll(f,x) ⊆ ⋃⋃f ∈ u`, so `C₂`. Two applications of
/// [`super::universe_union_closed`] and one of [`super::universe_sub_mem`], and
/// nothing about `f` beyond its membership.
pub fn universe_coll_closed(
    env: &mut Env,
    ap: &Apply,
    union_closed: &Thm,
    sub_mem: &Thm,
) -> Option<Thm> {
    let (uv, fv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tf, tx) = (Term::var(uv), Term::var(fv), Term::var(xv));
    let uf = ap.sets.union_of(tf.clone());
    let uuf = ap.sets.union_of(uf.clone());
    let coll_t = ap.coll_of(tf.clone(), tx.clone());

    let univ_u = is_universe(env, &tu);
    let f_in_u = Formula::mem(tf.clone(), tu.clone());
    let h = Formula::and(univ_u.clone(), f_in_u.clone());
    let h_univ = and_left(univ_u.clone(), f_in_u.clone());
    let h_f = and_right(univ_u, f_in_u);

    // `⊢ (is_universe(u) ∧ t ∈ u) → ⋃t ∈ u`, checked against our own rebuild.
    let union_at = |env: &mut Env, t: &Term| -> Option<Thm> {
        let at = inst_all(union_closed, &[tu.clone(), t.clone()])?;
        let want = Formula::imp(
            Formula::and(is_universe(env, &tu), Formula::mem(t.clone(), tu.clone())),
            Formula::mem(ap.sets.union_of(t.clone()), tu.clone()),
        );
        if *at.concl() != want {
            return None
        }
        Some(at)
    };
    let h_uf = hyp_mp(&a1i(&union_at(env, &tf)?, h.clone()), &hyp_and(&h_univ, &h_f)?)?;
    let h_uuf = hyp_mp(&a1i(&union_at(env, &uf)?, h.clone()), &hyp_and(&h_univ, &h_uf)?)?;

    let sm = inst_all(sub_mem, &[tu.clone(), uuf.clone(), coll_t.clone()])?;
    if *sm.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(uuf.clone(), tu.clone()),
                    kernel::thm::subset(env, coll_t.clone(), uuf.clone()),
                ),
            ),
            Formula::mem(coll_t.clone(), tu.clone()),
        )
    {
        return None
    }
    let sub = inst_all(&coll_subset_union2(env, ap)?, &[tf.clone(), tx.clone()])?;
    let out = hyp_mp(
        &a1i(&sm, h.clone()),
        &hyp_and(&h_univ, &hyp_and(&h_uuf, &a1i(&sub, h.clone()))?)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(coll_t, tu)),
        "universe_coll_closed: wrong shape"
    );
    Some(gen_all(&[uv, fv, xv], &out))
}

/// `⊢ ∀u ∀f ∀x. ((is_universe(u) ∧ f ∈ u) → app(f,x) ∈ u)` — **a universe is
/// closed under application**, with no hypothesis on `f` beyond membership.
///
/// `app(f,x)` is `⋃coll(f,x)`, so this is [`universe_coll_closed`] followed by
/// one more [`super::universe_union_closed`], with the defining equation moved
/// across by Leibniz. In particular `f` need not be single-valued and `x` need
/// not be in its domain.
pub fn universe_app_closed(
    env: &mut Env,
    ap: &Apply,
    union_closed: &Thm,
    coll_closed: &Thm,
) -> Option<Thm> {
    let (uv, fv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tf, tx) = (Term::var(uv), Term::var(fv), Term::var(xv));
    let coll_t = ap.coll_of(tf.clone(), tx.clone());
    let ucoll = ap.sets.union_of(coll_t.clone());
    let app_t = ap.apply(tf.clone(), tx.clone());

    let univ_u = is_universe(env, &tu);
    let f_in_u = Formula::mem(tf.clone(), tu.clone());
    let h = Formula::and(univ_u.clone(), f_in_u.clone());
    let h_univ = and_left(univ_u.clone(), f_in_u.clone());

    let cc = inst_all(coll_closed, &[tu.clone(), tf.clone(), tx.clone()])?;
    if *cc.concl() != Formula::imp(h.clone(), Formula::mem(coll_t.clone(), tu.clone())) {
        return None
    }
    let uc = inst_all(union_closed, &[tu.clone(), coll_t.clone()])?;
    if *uc.concl()
        != Formula::imp(
            Formula::and(is_universe(env, &tu), Formula::mem(coll_t.clone(), tu.clone())),
            Formula::mem(ucoll.clone(), tu.clone()),
        )
    {
        return None
    }
    let h_ucoll = hyp_mp(&a1i(&uc, h.clone()), &hyp_and(&h_univ, &cc)?)?;

    // `app(f,x) = ⋃coll(f,x)` carries the membership back to `app`.
    let app_def = inst_all(&ap.app_ax, &[tf.clone(), tx.clone()])?;
    if *app_def.concl() != Formula::eq(app_t.clone(), ucoll.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ucoll,
        app_t.clone(),
        hole,
        Formula::mem(Term::var(hole), tu.clone()),
    );
    let out = hyp_mp(
        &hyp_mp(&a1i(&leib, h.clone()), &a1i(&crate::eq_symm(env, &app_def)?, h.clone()))?,
        &h_ucoll,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(app_t, tu)),
        "universe_app_closed: wrong shape"
    );
    Some(gen_all(&[uv, fv, xv], &out))
}

/// `⊢ ∀c ∀f ∀x. (f ∈ U(c) → app(f,x) ∈ U(c))` — **`U(c)` is closed under
/// application**, with no hypothesis at all.
///
/// The transfer through the intersection that
/// [`super::least_universe_pairing`] uses: a closure property holding in every
/// universe holds in `U(c)`, so `is_universe(U(c))` is not needed.
pub fn least_universe_app(
    env: &mut Env,
    ap: &Apply,
    lu: FnSym,
    lu_ax: &Thm,
    app_closed: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (cv, fv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tf, tx) = (Term::var(cv), Term::var(fv), Term::var(xv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let app_t = ap.apply(tf.clone(), tx.clone());

    let h = Formula::mem(tf.clone(), w.clone());

    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), c_in_u.clone());

    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());
    let n_univ = syl(&n_a, &and_left(univ_u, c_in_u))?;

    let transfer = least_universe_transfer(env, lu_ax, &tc, &tf, &tu)?;
    let n_f_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_h)?, &n_a)?;

    let at = inst_all(app_closed, &[tu.clone(), tf.clone(), tx.clone()])?;
    if *at.concl()
        != Formula::imp(
            Formula::and(is_universe(env, &tu), Formula::mem(tf.clone(), tu.clone())),
            Formula::mem(app_t.clone(), tu.clone()),
        )
    {
        return None
    }
    let n_app_in_u = hyp_mp(&a1i(&at, n.clone()), &hyp_and(&n_univ, &n_f_in_u)?)?;

    let h_phi = Thm::mp(
        &Thm::ax_dist(uv, h.clone(), Formula::imp(a, Formula::mem(app_t.clone(), tu)))?,
        &Thm::gen(uv, &uncurry(&n_app_in_u)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tc, &app_t)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let out = syl(&h_phi, &crate::iff_mpr(&least_universe_mem(lu_ax, &tc, &app_t)?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(app_t, w)),
        "least_universe_app: wrong shape"
    );
    Some(gen_all(&[cv, fv, xv], &out))
}
