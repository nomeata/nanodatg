//! The **conditional value** `cval(c,v) = c × {v}` — the function `h ∈ c ↦ v`.
//!
//! # Interface
//!
//! ```text
//! cval(c,v) := prod(c, {v})                                          [cval_of]
//!
//! ⊢ ∀c ∀w ∀z. (z ∈ prod(c,w) → ∃x. x ∈ c)                    [prod_inhabited]
//! ⊢ ∀c ∀v ∀p ∀q. (⟨p,q⟩ ∈ cval(c,v) → q = v)             [prod_snd_singleton]
//! ⊢ ∀c ∀v. sv(cval(c,v))                                 [cval_single_valued]
//! ⊢ ∀c ∀v. (• ∈ c → app(cval(c,v), •) = v)                          [cval_app]
//! ⊢ ∀c ∀u ∀v. ((∀h. (h ∈ c → u = v)) → cval(c,u) = cval(c,v))       [cval_ext]
//! ⊢ ∀c ∀u ∀d ∀t. ((∀h. (h ∈ c → (h ∈ d ∧ u ∈ t))) →
//!       cval(c,u) ⊆ prod(d,t))                                    [cval_bound]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why this is the interpretation of `h ∈ [φ] ↦ e`
//!
//! Carneiro's *The Type Theory of Lean* §6.2.2 defines the accessibility
//! recursor with two nested proof-indexed abstractions:
//!
//! ```text
//! rec_acc(A,R,e) = (x ∈ A ↦ (h ∈ [x ∈ acc(A,R)] ↦ F(x)))
//! F(x)           = e(x)(•)(y ∈ A ↦ (h ∈ [⟨y,x⟩ ∈ R] ↦ F(y)))
//! ```
//!
//! Both inner abstractions have the shape "a function on a *proposition* — a
//! subset of `1` — that is constant", and a constant function on `c` with value
//! `v` is exactly the Cartesian product `c × {v}`:
//!
//! ```text
//! z ∈ prod(c,{v})  ↔  ∃x. (x ∈ c ∧ ∃y. (y ∈ {v} ∧ z = ⟨x,y⟩))
//!                  ↔  ∃x. (x ∈ c ∧ z = ⟨x,v⟩)
//! ```
//!
//! So **no new symbol is minted here at all**: `cval` is a term built from
//! [`crate::funspace::Product`], whose membership condition is already
//! unconditional, and the lemmas the recursor needs — extensionality in `v`, a
//! bound, and a beta rule — are theorems about arbitrary sets `c`, not schemes
//! over a formula. The `[φ]`-ness of `c` is used nowhere below; it enters only
//! when a caller instantiates `c` at a [`crate::prop::conditional_singleton`],
//! which is what [`crate::rec_acc::ih`] does.
//!
//! # Why the two premises are guarded by `h ∈ c`
//!
//! The recursor compares `cval([⟨y,x⟩ ∈ R], app(g,y))` with the same at another
//! attempt `h`, and it can only know `app(g,y) = app(h,y)` when `⟨y,x⟩ ∈ R` —
//! off the relation two attempts need not agree at all, and there the
//! conditional value is empty so the disagreement is invisible. Guarding the
//! premise by `h ∈ c` makes exactly that available and **needs no case analysis
//! on the proposition**: when `c` is empty the premise is vacuous and both
//! products are empty, and one derivation covers both cases. Asking for `u = v`
//! outright would be false; asking for `¬φ ∨ u = v` would need excluded middle
//! and a split at every use.
//!
//! [`cval_bound`] is shaped the same way: `v ∈ t` is required only under
//! `h ∈ c`, so an empty proposition imposes no typing obligation at all. That is
//! what keeps `step_typed` free of any condition on the values off the relation.

use kernel::{Env, Formula, Term, Thm};

use crate::sums::Sums;
use crate::wrec::hyp_eq_trans;
use crate::{
    a1i, and_left, and_right, com12, curry, eq_symm_imp, exists_elim_imp, exists_intro_imp,
    exists_mono, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, singleton, syl,
    uncurry,
};

/// The term `cval(c,v) = prod(c,{v})` — the constant function `h ∈ c ↦ v`.
pub fn cval_of(s: &Sums, c: Term, v: Term) -> Term {
    s.prod.of(c, singleton(s.ap.sets.up, v))
}

/// `⊢ ∀c ∀w ∀z. (z ∈ prod(c,w) → ∃x. x ∈ c)` — a product with a member has an
/// inhabited left factor.
///
/// This is what lets [`cval_ext`] and [`cval_bound`] spend their guarded
/// premises: a member of `cval(c,v)` witnesses `c`'s inhabitation, and `h ∈ c`
/// is the only thing those premises are guarded by.
pub fn prod_inhabited(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (cv, wv, zv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tw, tz, tx, ty) = (
        Term::var(cv),
        Term::var(wv),
        Term::var(zv),
        Term::var(xv),
        Term::var(yv),
    );

    let at = inst_all(&s.prod.prod_ax, &[tc.clone(), tw.clone(), tz.clone()])?;
    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    let inner = Formula::exists(
        yv,
        Formula::and(
            Formula::mem(ty.clone(), tw.clone()),
            Formula::eq(tz.clone(), s.ap.sets.pair(tx.clone(), ty)),
        ),
    );
    if *at.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), s.prod.of(tc.clone(), tw.clone())),
            Formula::exists(xv, Formula::and(mem_xc.clone(), inner.clone())),
        )
    {
        return None
    }

    let mono = exists_mono(xv, &Thm::gen(xv, &and_left(mem_xc.clone(), inner)))?;
    let out = syl(&iff_mp(&at)?, &mono)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::mem(tz, s.prod.of(tc, tw)),
            Formula::exists(xv, mem_xc)
        ),
        "prod_inhabited: unexpected shape"
    );
    Some(gen_all(&[cv, wv, zv], &out))
}

/// `⊢ ∀c ∀v ∀p ∀q. (⟨p,q⟩ ∈ cval(c,v) → q = v)` — the value of a conditional
/// value is *the* value.
///
/// Two existential eliminations and [`crate::funcs::Apply::pair_inj`]; the
/// singleton on the right of the product is what pins `q`.
pub fn prod_snd_singleton(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (cv, vv, pv, qv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tv, tp, tq, tx, ty) = (
        Term::var(cv),
        Term::var(vv),
        Term::var(pv),
        Term::var(qv),
        Term::var(xv),
        Term::var(yv),
    );

    let sing = singleton(s.ap.sets.up, tv.clone());
    let pq = s.ap.sets.pair(tp.clone(), tq.clone());
    let at = inst_all(&s.prod.prod_ax, &[tc.clone(), sing.clone(), pq.clone()])?;

    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let eq_pair = Formula::eq(pq.clone(), s.ap.sets.pair(tx.clone(), ty.clone()));
    let ib = Formula::and(mem_ys.clone(), eq_pair.clone());
    let goal = Formula::eq(tq.clone(), tv.clone());

    // `y ∈ {v} → y = v`, and `⟨p,q⟩ = ⟨x,y⟩ → q = y`.
    let ms = inst_all(&s.ap.mem_sing, &[tv.clone(), ty.clone()])?;
    let t_yv = syl(&and_left(mem_ys.clone(), eq_pair.clone()), &iff_mp(&ms)?)?;
    let pi = inst_all(
        &s.ap.pair_inj,
        &[tp.clone(), tq.clone(), tx.clone(), ty.clone()],
    )?;
    let t_qy = syl(
        &syl(&and_right(mem_ys.clone(), eq_pair.clone()), &pi)?,
        &and_right(
            Formula::eq(tp.clone(), tx.clone()),
            Formula::eq(tq.clone(), ty.clone()),
        ),
    )?;
    let t_qv = hyp_eq_trans(env, &t_qy, &t_yv)?;
    if *t_qv.concl() != Formula::imp(ib.clone(), goal.clone()) {
        return None
    }

    let inner_ex = exists_elim_imp(yv, &Thm::gen(yv, &t_qv), &goal)?;
    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    let ex_ib = Formula::exists(yv, ib);
    let outer = syl(&and_right(mem_xc.clone(), ex_ib.clone()), &inner_ex)?;
    let outer_ex = exists_elim_imp(xv, &Thm::gen(xv, &outer), &goal)?;
    if *at.concl()
        != Formula::iff(
            Formula::mem(pq.clone(), s.prod.of(tc.clone(), sing.clone())),
            Formula::exists(xv, Formula::and(mem_xc, ex_ib)),
        )
    {
        return None
    }
    let out = syl(&iff_mp(&at)?, &outer_ex)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(pq, s.prod.of(tc, sing)), goal),
        "prod_snd_singleton: unexpected shape"
    );
    Some(gen_all(&[cv, vv, pv, qv], &out))
}

/// `⊢ ∀c ∀v. sv(cval(c,v))` — a conditional value is a function.
///
/// Immediate from [`prod_snd_singleton`]: both values are `v`.
pub fn cval_single_valued(env: &mut Env, s: &Sums, snd: &Thm) -> Option<Thm> {
    let (cv, vv, xv, yv, y2v) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tv, tx, ty, ty2) = (
        Term::var(cv),
        Term::var(vv),
        Term::var(xv),
        Term::var(yv),
        Term::var(y2v),
    );
    let cval = cval_of(s, tc.clone(), tv.clone());

    let m1 = Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), cval.clone());
    let m2 = Formula::mem(s.ap.sets.pair(tx.clone(), ty2.clone()), cval.clone());
    let h = Formula::and(m1.clone(), m2.clone());

    let s1 = syl(
        &and_left(m1.clone(), m2.clone()),
        &inst_all(snd, &[tc.clone(), tv.clone(), tx.clone(), ty.clone()])?,
    )?;
    let s2 = syl(
        &and_right(m1, m2),
        &inst_all(snd, &[tc.clone(), tv.clone(), tx.clone(), ty2.clone()])?,
    )?;
    let s2r = syl(&s2, &eq_symm_imp(env, ty2.clone(), tv.clone()))?;
    let out = hyp_eq_trans(env, &s1, &s2r)?;
    if *out.concl() != Formula::imp(h, Formula::eq(ty, ty2)) {
        return None
    }

    let body = gen_all(&[xv, yv, y2v], &out);
    if *body.concl() != crate::funspace::is_single_valued(env, &s.ap.sets, &cval) {
        return None
    }
    Some(gen_all(&[cv, vv], &body))
}

/// `⊢ ∀c ∀v. (• ∈ c → app(cval(c,v), •) = v)` — **the beta rule**.
///
/// When the proposition `c` holds — that is, when `•` inhabits it — applying the
/// conditional value at the proof gives the value back. This is what makes the
/// interpretation of `h ∈ [φ] ↦ e` compute, and hence what lets the recursion
/// equation of [`crate::rec_acc`] be read as Carneiro writes it rather than as a
/// statement about an opaque set.
///
/// `app_of_graph` must be [`crate::recursion::app_of_graph`].
pub fn cval_app(env: &mut Env, s: &Sums, sv: &Thm, app_of_graph: &Thm) -> Option<Thm> {
    let (cv, vv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tv, tx, ty) = (
        Term::var(cv),
        Term::var(vv),
        Term::var(xv),
        Term::var(yv),
    );
    let pt = s.point();
    let cval = cval_of(s, tc.clone(), tv.clone());
    let sing = singleton(s.ap.sets.up, tv.clone());
    let pair = s.ap.sets.pair(pt.clone(), tv.clone());
    let mem_pc = Formula::mem(pt.clone(), tc.clone());

    // `• ∈ c → ⟨•,v⟩ ∈ cval(c,v)`, through the product's membership condition.
    let inner_body = Formula::and(
        Formula::mem(ty.clone(), sing.clone()),
        Formula::eq(pair.clone(), s.ap.sets.pair(tx.clone(), ty.clone())),
    );
    let body_x = Formula::and(
        Formula::mem(tx.clone(), tc.clone()),
        Formula::exists(yv, inner_body.clone()),
    );

    let ms = inst_all(&s.ap.mem_sing, &[tv.clone(), tv.clone()])?;
    let v_in_sing = Thm::mp(&iff_mpr(&ms)?, &Thm::eq_refl(tv.clone()))?;
    let inner_at_v = crate::and_intro(&v_in_sing, &Thm::eq_refl(pair.clone()));
    let inner_pt = inner_body.subst(xv, &pt);
    let ex_inner = Thm::mp(&exists_intro_imp(yv, inner_pt, tv.clone())?, &inner_at_v)?;
    let body_at_pt = hyp_and(
        &imp_refl(mem_pc.clone()),
        &a1i(&ex_inner, mem_pc.clone()),
    )?;
    let ex_outer = syl(
        &body_at_pt,
        &exists_intro_imp(xv, body_x.clone(), pt.clone())?,
    )?;
    let at = inst_all(&s.prod.prod_ax, &[tc.clone(), sing, pair.clone()])?;
    if *at.concl()
        != Formula::iff(
            Formula::mem(pair, cval.clone()),
            Formula::exists(xv, body_x),
        )
    {
        return None
    }
    let mem_pair = syl(&ex_outer, &iff_mpr(&at)?)?;

    // `app_of_graph` at `(cval(c,v), •, v)`, with single-valuedness supplied.
    let aog = inst_all(app_of_graph, &[cval.clone(), pt.clone(), tv.clone()])?;
    let sv_at = inst_all(sv, &[tc.clone(), tv.clone()])?;
    let out = syl(&hyp_and(&a1i(&sv_at, mem_pc.clone()), &mem_pair)?, &aog)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(mem_pc, Formula::eq(s.ap.apply(cval, pt), tv)),
        "cval_app: unexpected shape"
    );
    Some(gen_all(&[cv, vv], &out))
}

/// `∀h. (h ∈ c → u = v)` — the guarded premise of [`cval_ext`], as a formula.
pub fn agree_on_cond(env: &mut Env, c: &Term, u: &Term, v: &Term) -> Formula {
    let hv = env.fresh_var();
    Formula::forall(
        hv,
        Formula::imp(
            Formula::mem(Term::var(hv), c.clone()),
            Formula::eq(u.clone(), v.clone()),
        ),
    )
}

/// `⊢ ∀c ∀u ∀v. ((∀h. (h ∈ c → u = v)) → cval(c,u) = cval(c,v))` — **the
/// extensionality the recursor's agreement argument runs on**.
///
/// See the module header for why the premise is guarded. `inhab` must be
/// [`prod_inhabited`].
pub fn cval_ext(env: &mut Env, s: &Sums, inhab: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (cv, uv, vv, zv, xv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tu, tvv, tz, tx) = (
        Term::var(cv),
        Term::var(uv),
        Term::var(vv),
        Term::var(zv),
        Term::var(xv),
    );
    let hyp = agree_on_cond(env, &tc, &tu, &tvv);
    let cu = cval_of(s, tc.clone(), tu.clone());
    let cvv = cval_of(s, tc.clone(), tvv.clone());

    // `H → ((∃x. x ∈ c) → u = v)` — the premise with its guard existentially
    // packed, which is the form a membership hands over.
    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    let eq_uv = Formula::eq(tu.clone(), tvv.clone());
    let per_x = com12(&Thm::ax_inst(hyp.clone(), tx.clone())?)?;
    let packed = com12(&exists_elim_imp(
        xv,
        &Thm::gen(xv, &per_x),
        &Formula::imp(hyp.clone(), eq_uv.clone()),
    )?)?;
    if *packed.concl()
        != Formula::imp(
            hyp.clone(),
            Formula::imp(Formula::exists(xv, mem_xc), eq_uv),
        )
    {
        return None
    }

    // One inclusion, run twice; the second with the equation reversed.
    let mut incl = |from: &Term, to: &Term| -> Option<Thm> {
        let sing_from = singleton(s.ap.sets.up, from.clone());
        let cf = s.prod.of(tc.clone(), sing_from.clone());
        let mem_from = Formula::mem(tz.clone(), cf);
        let k = Formula::and(hyp.clone(), mem_from.clone());
        let k_h = and_left(hyp.clone(), mem_from.clone());
        let k_m = and_right(hyp.clone(), mem_from);
        let k_inh = syl(
            &k_m,
            &inst_all(inhab, &[tc.clone(), sing_from, tz.clone()])?,
        )?;
        let k_eq0 = hyp_mp(&syl(&k_h, &packed)?, &k_inh)?;
        let k_eq = if *from == tu {
            k_eq0
        } else {
            syl(&k_eq0, &eq_symm_imp(env, tu.clone(), tvv.clone()))?
        };
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            from.clone(),
            to.clone(),
            hole,
            Formula::mem(
                tz.clone(),
                s.prod.of(tc.clone(), singleton(s.ap.sets.up, Term::var(hole))),
            ),
        );
        uncurry(&hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &k_eq)?, &k_m)?)
    };

    let fwd = incl(&tu, &tvv)?;
    let bwd = incl(&tvv, &tu)?;
    let both = hyp_and(&fwd, &bwd)?;
    let iff = Formula::iff(
        Formula::mem(tz.clone(), cu.clone()),
        Formula::mem(tz, cvv.clone()),
    );
    if *both.concl() != Formula::imp(hyp.clone(), iff.clone()) {
        return None
    }
    let h_all = Thm::mp(&Thm::ax_dist(zv, hyp.clone(), iff)?, &Thm::gen(zv, &both))?;
    let out = syl(&h_all, &inst_all(&ext, &[cu.clone(), cvv.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::eq(cu, cvv)),
        "cval_ext: unexpected shape"
    );
    Some(gen_all(&[cv, uv, vv], &out))
}

/// `∀h. (h ∈ c → (h ∈ d ∧ u ∈ t))` — the guarded premise of [`cval_bound`], as
/// a formula.
pub fn bound_cond(env: &mut Env, c: &Term, u: &Term, d: &Term, t: &Term) -> Formula {
    let hv = env.fresh_var();
    let th = Term::var(hv);
    Formula::forall(
        hv,
        Formula::imp(
            Formula::mem(th.clone(), c.clone()),
            Formula::and(
                Formula::mem(th, d.clone()),
                Formula::mem(u.clone(), t.clone()),
            ),
        ),
    )
}

/// `⊢ ∀c ∀u ∀d ∀t. ((∀h. (h ∈ c → (h ∈ d ∧ u ∈ t))) → cval(c,u) ⊆ prod(d,t))` —
/// **the typing the recursor's totality argument runs on**.
///
/// Guarded exactly as [`cval_ext`] is; see the module header.
pub fn cval_bound(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (cv, uv, dv, tv, zv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tu, td, tt, tz, tx, ty) = (
        Term::var(cv),
        Term::var(uv),
        Term::var(dv),
        Term::var(tv),
        Term::var(zv),
        Term::var(xv),
        Term::var(yv),
    );
    let hyp = bound_cond(env, &tc, &tu, &td, &tt);
    let sing = singleton(s.ap.sets.up, tu.clone());
    let cu = s.prod.of(tc.clone(), sing.clone());
    let goal = Formula::mem(tz.clone(), s.prod.of(td.clone(), tt.clone()));

    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let eq_z = Formula::eq(tz.clone(), s.ap.sets.pair(tx.clone(), ty.clone()));
    let ib = Formula::and(mem_ys.clone(), eq_z.clone());
    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    let ex_ib = Formula::exists(yv, ib.clone());
    let body_x = Formula::and(mem_xc.clone(), ex_ib.clone());

    // ── Under `K := (H ∧ x ∈ c) ∧ (y ∈ {u} ∧ z = ⟨x,y⟩)` ────────────────────
    let front = Formula::and(hyp.clone(), mem_xc.clone());
    let k = Formula::and(front.clone(), ib.clone());
    let k_front = and_left(front.clone(), ib.clone());
    let k_h = syl(&k_front, &and_left(hyp.clone(), mem_xc.clone()))?;
    let k_xc = syl(&k_front, &and_right(hyp.clone(), mem_xc.clone()))?;
    let k_ib = and_right(front.clone(), ib);

    let k_both = hyp_mp(&syl(&k_h, &Thm::ax_inst(hyp.clone(), tx.clone())?)?, &k_xc)?;
    let mem_xd = Formula::mem(tx.clone(), td.clone());
    let mem_ut = Formula::mem(tu.clone(), tt.clone());
    let k_xd = syl(&k_both, &and_left(mem_xd.clone(), mem_ut.clone()))?;
    let k_ut = syl(&k_both, &and_right(mem_xd, mem_ut))?;

    // `y = u`, hence `y ∈ t`.
    let ms = inst_all(&s.ap.mem_sing, &[tu.clone(), ty.clone()])?;
    let k_yu = syl(
        &syl(&k_ib, &and_left(mem_ys.clone(), eq_z.clone()))?,
        &iff_mp(&ms)?,
    )?;
    let k_uy = syl(&k_yu, &eq_symm_imp(env, ty.clone(), tu.clone()))?;
    let hole = env.fresh_var();
    let leib_yt = Thm::eq_leibniz(
        tu.clone(),
        ty.clone(),
        hole,
        Formula::mem(Term::var(hole), tt.clone()),
    );
    let k_yt = hyp_mp(&hyp_mp(&a1i(&leib_yt, k.clone()), &k_uy)?, &k_ut)?;

    // `⟨x,y⟩ ∈ prod(d,t)`, then carried back along `z = ⟨x,y⟩`.
    let pip = inst_all(
        &s.pair_in_prod,
        &[td.clone(), tt.clone(), tx.clone(), ty.clone()],
    )?;
    let k_pair = syl(&hyp_and(&k_xd, &k_yt)?, &iff_mpr(&pip)?)?;
    let k_zx = syl(
        &syl(&k_ib, &and_right(mem_ys, eq_z))?,
        &eq_symm_imp(env, tz.clone(), s.ap.sets.pair(tx.clone(), ty.clone())),
    )?;
    let hole2 = env.fresh_var();
    let leib_z = Thm::eq_leibniz(
        s.ap.sets.pair(tx.clone(), ty),
        tz.clone(),
        hole2,
        Formula::mem(Term::var(hole2), s.prod.of(td.clone(), tt.clone())),
    );
    let k_goal = hyp_mp(&hyp_mp(&a1i(&leib_z, k.clone()), &k_zx)?, &k_pair)?;
    if *k_goal.concl() != Formula::imp(k, goal.clone()) {
        return None
    }

    // ── Discharge both witnesses ────────────────────────────────────────────
    let per_y = com12(&uncurry(&k_goal)?)?; // ib → (front → goal)
    let elim_y = exists_elim_imp(
        yv,
        &Thm::gen(yv, &per_y),
        &Formula::imp(front.clone(), goal.clone()),
    )?; // (∃y. ib) → (front → goal)
    let unc = curry(&com12(&elim_y)?)?; // (front ∧ ∃y. ib) → goal

    let hb = Formula::and(hyp.clone(), body_x.clone());
    let hb_h = and_left(hyp.clone(), body_x.clone());
    let hb_body = and_right(hyp.clone(), body_x.clone());
    let hb_xc = syl(&hb_body, &and_left(mem_xc.clone(), ex_ib.clone()))?;
    let hb_ex = syl(&hb_body, &and_right(mem_xc, ex_ib))?;
    let hb_goal = syl(&hyp_and(&hyp_and(&hb_h, &hb_xc)?, &hb_ex)?, &unc)?;
    if *hb_goal.concl() != Formula::imp(hb, goal.clone()) {
        return None
    }

    let per_x = com12(&uncurry(&hb_goal)?)?; // body_x → (H → goal)
    let elim_x = exists_elim_imp(
        xv,
        &Thm::gen(xv, &per_x),
        &Formula::imp(hyp.clone(), goal.clone()),
    )?;
    let h_ex = com12(&elim_x)?; // H → ((∃x. body_x) → goal)

    let at = inst_all(&s.prod.prod_ax, &[tc.clone(), sing, tz.clone()])?;
    if *at.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), cu.clone()),
            Formula::exists(xv, body_x),
        )
    {
        return None
    }
    let body = crate::funcs::hyp_syl(&a1i(&iff_mp(&at)?, hyp.clone()), &h_ex)?;
    let out = Thm::mp(
        &Thm::ax_dist(
            zv,
            hyp.clone(),
            Formula::imp(Formula::mem(tz, cu.clone()), goal),
        )?,
        &Thm::gen(zv, &body),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, kernel::thm::subset(env, cu, s.prod.of(td, tt))),
        "cval_bound: unexpected shape"
    );
    Some(gen_all(&[cv, uv, dv, tv], &out))
}
