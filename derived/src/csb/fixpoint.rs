//! Knaster–Tarski: the set the Cantor–Schröder–Bernstein bijection switches on.
//!
//! # Interface
//!
//! With `F`, `G`, `a`, `b` as in [`super::clauses`], and `Φ(s)` the operator
//! written there as [`step`](super::clauses::step),
//!
//! ```text
//! Φ(s)  =  a ∖ G[b ∖ F[s]]
//! ```
//!
//! this file proves
//!
//! ```text
//! ⊢ (s ⊆ t) → (Φ(s)(d) → Φ(t)(d))                            [step_monotone]
//! ⊢ ∃c. ∀d. (d ∈ c ↔ Φ(c)(d))                                 [csb_fixpoint]
//! ```
//!
//! — a **fixed point** of `Φ`, proved with **no hypothesis on `F` or `G`
//! whatsoever**. Not one of the eight injection clauses is used: `Φ` is monotone
//! whatever `F` and `G` are, because `s` occurs in it under two negations, and
//! monotonicity is all Knaster–Tarski needs. Everything the injections are for
//! happens in [`super::bijection`], on the other side of this statement.
//!
//! # What it costs, and what it does not
//!
//! [`crate::funcs::separation_full`] twice, and nothing else. In particular:
//!
//! * **no `ω`, no recursion theorem, no back-and-forth.** The `C₀ = a ∖ G[b]`,
//!   `C_{n+1} = G[F[C_n]]`, `C = ⋃ₙ Cₙ` construction — which is what needs
//!   [`crate::recursion`], and what `crate::universe::inaccessibility` predicted
//!   would be needed — computes the *same* set by iteration. Knaster–Tarski
//!   reaches it in one Separation instead, so the `ω`-recursion this development
//!   already has is **not on this path at all**;
//! * **no power set.** The least fixed point is usually `⋂{s ∈ 𝒫a : Φ(s) ⊆ s}`,
//!   which needs `𝒫a` to quantify over. Writing the same intersection as a
//!   *separation condition* — `c ∈ a` together with `∀s. (Φ(s) ⊆ s → c ∈ s)`,
//!   an unbounded quantifier inside the condition — needs no bounding set,
//!   because the Replacement scheme Separation comes from admits an arbitrary
//!   formula. **This is not a new trick here.** It is exactly
//!   [`crate::acc`]'s `acc(A,R) := { z ∈ A : ∀C. ((C ⊆ A ∧ step_closed) → z ∈ C) }`,
//!   which says the same thing in the same words, and
//!   [`crate::wtype`]'s least-closed-set pattern before it. The technique that
//!   makes this construction cheap was already in the library, twice, while the
//!   estimate that scheduled it as expensive stood;
//! * **no set `Φ(s)`.** `Φ(s) ⊆ s` is spelled out as
//!   [`pre_fixed`](super::clauses::pre_fixed), a formula, so the operator is
//!   never applied to anything. Only two sets are ever built: `c` itself and
//!   the auxiliary `d` of the post-fixed half.
//!
//! # The argument
//!
//! `c := { z ∈ a : ∀s. (PRE(s) → z ∈ s) }`, the intersection of every pre-fixed
//! point, cut down to `a`.
//!
//! * `c` is **pre-fixed**: given `Φ(c)(z)`, take any pre-fixed `s`. Every member
//!   of `c` is in `s` by `c`'s own definition, so `c ⊆ s`, so `Φ(c)(z)` gives
//!   `Φ(s)(z)` by monotonicity, so `z ∈ s`. That holds for every pre-fixed `s`,
//!   which is exactly the defining condition of `c` — and `z ∈ a` comes free
//!   with `Φ`. So `z ∈ c`.
//! * `c` is **post-fixed**: let `d := { z ∈ a : Φ(c)(z) }`, the one place a
//!   second Separation is spent. `d ⊆ c` is the previous bullet, so
//!   monotonicity turns `Φ(d)(z)` into `Φ(c)(z)`, i.e. into `z ∈ d` — so `d` is
//!   itself pre-fixed, so `c ⊆ d` by `c`'s defining condition, so every `z ∈ c`
//!   has `Φ(c)(z)`.
//!
//! `d` is discharged before the conclusion is stated, and `c` with it.
//!
//! # Why the fixed point and not just the pre-fixed point
//!
//! Both halves are spent, in different clauses of the finished bijection.
//! Pre-fixedness is what turns `¬(z ∈ c)` into a `G`-preimage — it is the
//! *totality* of the bijection off `c`. Post-fixedness is what stops a `z ∈ c`
//! from also being a `G`-preimage of something outside `F[c]` — it is the
//! *ontoness*. Dropping either leaves a relation that is still single-valued and
//! injective and is no longer a bijection; `tests/csb.rs` pins both.
//!
//! # How this fails
//!
//! [`csb_fixpoint`] declines exactly twice, and both refusals happen before any
//! derivation starts: `xv` and `bv` must be distinct, and the seven variables
//! the function mints for its own use must occur in none of `F`, `G`, `a`,
//! `codom`. That pair is the whole of the entry's contract. Everything after
//! them is this file checking its own work — the `debug_assert_eq!`s, and the
//! kernel calls behind [`crate::prim`] — so a failure from there is a
//! [`crate::err::DerErr::Assembly`] and a bug here rather than in the caller.
//! [`step_monotone`] has no contract at all: it assumes nothing about `F` or
//! `G`, so every way it can stop is an assembly failure.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::decline;
use crate::err::DResult;
use crate::funcs::separation_full;
use crate::prim::{self, Shape};
use crate::rules::{
    exists_mono, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_syl, syl, uncurry,
};
use crate::{a1i, and_left, and_right};

use super::clauses::{in_image, pre_fixed, step, stopper};
use super::shared::{discharge, hyp_contrapos, hyp_exists_mono, hyp_gen};

/// `⊢ (s ⊆ t) → (Φ(s)(d) → Φ(t)(d))` — **the operator is monotone**, with no
/// hypothesis on `F` or `G`.
///
/// `s` occurs in `Φ` under two negations: growing `s` grows the image `F[s]`,
/// shrinks the complement `b ∖ F[s]`, shrinks its `G`-preimage, and hence grows
/// `a` minus that preimage. This is the only property of `Φ` Knaster–Tarski
/// uses, and it is why the fixed point is available before any injection clause
/// is assumed.
///
/// `wv` must be fresh for `F`, `s` and `t`; `bv` is `F`'s codomain variable and
/// `G`'s argument variable, `dv` the value `Φ` is being evaluated at.
#[allow(clippy::too_many_arguments)]
pub fn step_monotone(
    env: &mut Env,
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    dv: FreeVar,
    wv: FreeVar,
    s: &Term,
    t: &Term,
    a: &Term,
    codom: &Term,
) -> DResult<Thm> {
    let sub = kernel::thm::subset(env, s.clone(), t.clone());
    let (tw, tb, td) = (Term::var(wv), Term::var(bv), Term::var(dv));

    // ── `sub → (IMG(s,b) → IMG(t,b))` ────────────────────────────────────────
    //
    // The image's witness `w` moves across the inclusion and takes `F(w,b)`
    // with it.
    let f_at_w = f.subst(xv, &tw);
    let mem_ws = Formula::mem(tw.clone(), s.clone());
    let body_s = Formula::and(mem_ws.clone(), f_at_w.clone());
    let k_sub = and_left(sub.clone(), body_s.clone());
    let k_body = and_right(sub.clone(), body_s.clone());
    let k_mem_s = syl(&k_body, &and_left(mem_ws.clone(), f_at_w.clone()))?;
    let k_f = syl(&k_body, &and_right(mem_ws.clone(), f_at_w.clone()))?;
    let k_mem_t = hyp_mp(&syl(&k_sub, &prim::ax_inst(sub.clone(), tw.clone())?)?, &k_mem_s)?;
    let body_moves = uncurry(&hyp_and(&k_mem_t, &k_f)?)?;
    let img_moves = hyp_exists_mono(wv, &body_moves)?;
    debug_assert_eq!(
        *img_moves.concl(),
        Formula::imp(sub.clone(), Formula::imp(in_image(f, xv, wv, s)?, in_image(f, xv, wv, t)?)),
        "step_monotone: the image inclusion has the wrong shape"
    );

    // ── `sub → (∃b.(…t…) → ∃b.(…s…))`, the *reverse* direction ───────────────
    //
    // The complement shrinks where the image grows, so the `G`-preimage of the
    // complement shrinks too — and this is the step that flips the inclusion.
    let img_t = in_image(f, xv, wv, t)?;
    let g_at_d = g.subst(xv, &td);
    let mem_b = Formula::mem(tb.clone(), codom.clone());
    let left_t = Formula::and(mem_b.clone(), Formula::not(img_t.clone()));
    let wit_t = Formula::and(left_t.clone(), g_at_d.clone());

    let k2_sub = and_left(sub.clone(), wit_t.clone());
    let k2_wit = and_right(sub.clone(), wit_t.clone());
    let k2_left = syl(&k2_wit, &and_left(left_t.clone(), g_at_d.clone()))?;
    let k2_g = syl(&k2_wit, &and_right(left_t.clone(), g_at_d.clone()))?;
    let k2_mem_b = syl(&k2_left, &and_left(mem_b.clone(), Formula::not(img_t.clone())))?;
    let k2_not_t = syl(&k2_left, &and_right(mem_b.clone(), Formula::not(img_t.clone())))?;
    let k2_not_s = hyp_mp(&hyp_contrapos(&syl(&k2_sub, &img_moves)?)?, &k2_not_t)?;
    let k2_out = hyp_and(&hyp_and(&k2_mem_b, &k2_not_s)?, &k2_g)?;
    let wit_moves = uncurry(&k2_out)?;
    let ex_moves = hyp_exists_mono(bv, &wit_moves)?;

    // ── Contrapose, and put `d ∈ a` back on ──────────────────────────────────
    let stop_moves = hyp_contrapos(&ex_moves)?;
    let stop_s = stopper(f, g, xv, bv, dv, wv, s, codom)?;
    let stop_t = stopper(f, g, xv, bv, dv, wv, t, codom)?;
    debug_assert_eq!(
        *stop_moves.concl(),
        Formula::imp(sub.clone(), Formula::imp(stop_s.clone(), stop_t.clone())),
        "step_monotone: the stopper condition has the wrong shape"
    );

    let step_s = step(f, g, xv, bv, dv, wv, s, a, codom)?;
    let mem_d_a = Formula::mem(td.clone(), a.clone());
    let k3_sub = and_left(sub.clone(), step_s.clone());
    let k3_step = and_right(sub.clone(), step_s.clone());
    let k3_mem = syl(&k3_step, &and_left(mem_d_a.clone(), stop_s.clone()))?;
    let k3_stop = syl(&k3_step, &and_right(mem_d_a.clone(), stop_s.clone()))?;
    let k3_out = hyp_and(&k3_mem, &hyp_mp(&syl(&k3_sub, &stop_moves)?, &k3_stop)?)?;
    let out = uncurry(&k3_out)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(sub, Formula::imp(step_s, step(f, g, xv, bv, dv, wv, t, a, codom)?)),
        "step_monotone: wrong shape"
    );
    Ok(out)
}

/// `⊢ ∃c. ∀d. (d ∈ c ↔ Φ(c)(d))` — the Knaster–Tarski fixed point.
///
/// `xv` and `bv` are `F`'s two distinguished variables (`F(x,b)`), and `G`'s the
/// other way round (`G(b,x)`). `a` and `codom` must mention neither. `empty`
/// must be a proof `⊢ ∀z. ¬(z ∈ e)`; it is consumed by the two Separations and
/// does not appear in the conclusion.
///
/// The conclusion is not generalised over anything — `F` and `G` may have
/// arbitrary further parameters, and it is the caller's business what to do with
/// them. It is also independent of every variable this function mints: the
/// witness, the working subset and `Φ`'s own `d`, `w` and `b` are all bound in
/// the result, so a caller may rebuild the statement with
/// [`fixed`](super::clauses::fixed) at variables of its own choosing.
#[allow(clippy::too_many_arguments)]
pub fn csb_fixpoint(
    env: &mut Env,
    empty: &Thm,
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    a: &Term,
    codom: &Term,
) -> DResult<Thm> {
    if xv == bv {
        return Err(decline!("F's two distinguished variables are the same variable"))
    }
    let (dv, wv, cv, sv, tv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (cset, dset) = (env.fresh_var(), env.fresh_var());
    for v in [dv, wv, cv, sv, tv, cset, dset] {
        if f.occurs_free(v)
            || g.occurs_free(v)
            || a.occurs_free(v)
            || codom.occurs_free(v)
            || v == xv
            || v == bv
        {
            return Err(decline!(
                "a working variable freshly minted here already occurs in F, G, the domain or the codomain"
            ))
        }
    }
    let (td, tc, ts, tt) = (Term::var(dv), Term::var(cv), Term::var(sv), Term::var(tv));
    let (tcs, tds) = (Term::var(cset), Term::var(dset));

    // ── `c := { z ∈ a : ∀s. (PRE(s) → z ∈ s) }` ──────────────────────────────
    let pre_s = pre_fixed(f, g, xv, bv, dv, wv, &ts, a, codom)?;
    let pre_t = pre_fixed(f, g, xv, bv, dv, wv, &tt, a, codom)?;
    let min = Formula::forall(sv, Formula::imp(pre_s, Formula::mem(tc.clone(), ts.clone())));

    let sep = separation_full(env, cv, &min, a, empty)?;
    let mem_c_a = Formula::mem(tc.clone(), a.clone());
    let carved = Formula::and(mem_c_a.clone(), min.clone());
    let q = Formula::forall(cv, Formula::iff(Formula::mem(tc.clone(), tcs.clone()), carved.clone()));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(cset, q.clone()),
        "csb_fixpoint: separation_full did not produce c's characteristic property"
    );

    // ── `Q → ∀t. (PRE(t) → c ⊆ t)` — `c` is below every pre-fixed point ──────
    let q_at_c = prim::ax_inst(q.clone(), tc.clone())?;
    let q_min = hyp_syl(
        &hyp_iff_mp(&q_at_c)?,
        &a1i(&and_right(mem_c_a.clone(), min.clone()), q.clone()),
    )?;
    let min_at_t = prim::ax_inst(min.clone(), tt.clone())?;
    let q_c_pre = hyp_syl(&q_min, &a1i(&min_at_t, q.clone()))?;

    let mem_c_cs = Formula::mem(tc.clone(), tcs.clone());
    let k = Formula::and(q.clone(), pre_t.clone());
    let k_q = and_left(q.clone(), pre_t.clone());
    let k_pre = and_right(q.clone(), pre_t.clone());
    let k_c_pre = syl(&k_q, &q_c_pre)?;
    let k_c_t = crate::funcs::hyp_mp2(
        &k_c_pre,
        &syl(&k_pre, &Thm::ax_k(pre_t.clone(), mem_c_cs.clone()))?,
    )?;
    let k_sub = hyp_gen(cv, &k_c_t)?;
    let sub_c_t = kernel::thm::subset(env, tcs.clone(), tt.clone());
    debug_assert_eq!(
        *k_sub.concl(),
        Formula::imp(k.clone(), sub_c_t.clone()),
        "csb_fixpoint: c ⊆ t is not the subset formula monotonicity expects"
    );
    let q_below = hyp_gen(tv, &uncurry(&k_sub)?)?;
    let below_all = q_below.concl().imp_parts()?.1;

    // ── `Q → ∀d. (Φ(c)(d) → d ∈ c)` — `c` is pre-fixed ───────────────────────
    let step_c = step(f, g, xv, bv, dv, wv, &tcs, a, codom)?;
    let mem_d_a = Formula::mem(td.clone(), a.clone());
    let stop_c = stopper(f, g, xv, bv, dv, wv, &tcs, codom)?;

    let m = Formula::and(q.clone(), step_c.clone());
    let m_q = and_left(q.clone(), step_c.clone());
    let m_step = and_right(q.clone(), step_c.clone());
    let m_mem_a = syl(&m_step, &and_left(mem_d_a.clone(), stop_c.clone()))?;

    // Under `M ∧ PRE(t)`: `c ⊆ t`, so monotonicity sends `Φ(c)(d)` to `Φ(t)(d)`,
    // and `PRE(t)` reads off `d ∈ t`.
    let n = Formula::and(m.clone(), pre_t.clone());
    let n_m = and_left(m.clone(), pre_t.clone());
    let n_pre = and_right(m.clone(), pre_t.clone());
    let n_q = syl(&n_m, &m_q)?;
    let n_step_c = syl(&n_m, &m_step)?;
    let n_below_t = syl(&n_q, &q_below)?; // N → ∀t.(PRE(t) → c ⊆ t)
    let n_pre_sub = syl(&n_below_t, &prim::ax_inst(below_all.clone(), tt.clone())?)?;
    let n_sub = hyp_mp(&n_pre_sub, &n_pre)?; // N → c ⊆ t
    let mono = step_monotone(env, f, g, xv, bv, dv, wv, &tcs, &tt, a, codom)?;
    let n_step_t = hyp_mp(&hyp_mp(&a1i(&mono, n.clone()), &n_sub)?, &n_step_c)?;
    let pre_t_at_d = prim::ax_inst(pre_t.clone(), td.clone())?;
    let n_mem_t = hyp_mp(&hyp_mp(&a1i(&pre_t_at_d, n.clone()), &n_pre)?, &n_step_t)?;

    let m_min_d = hyp_gen(tv, &uncurry(&n_mem_t)?)?;
    debug_assert_eq!(
        *m_min_d.concl(),
        Formula::imp(m.clone(), min.subst(cv, &td)),
        "csb_fixpoint: the minimality condition at d has the wrong shape"
    );
    let m_carved = hyp_and(&m_mem_a, &m_min_d)?;
    let q_at_d = prim::ax_inst(q.clone(), td.clone())?;
    let m_in_c = hyp_mp(&syl(&m_q, &hyp_iff_mpr(&q_at_d)?)?, &m_carved)?;
    let q_prefixed = hyp_gen(dv, &uncurry(&m_in_c)?)?;
    debug_assert_eq!(
        *q_prefixed.concl(),
        Formula::imp(q.clone(), pre_fixed(f, g, xv, bv, dv, wv, &tcs, a, codom)?),
        "csb_fixpoint: c's pre-fixedness has the wrong shape"
    );

    // ── `d := { z ∈ a : Φ(c)(z) }`, and `c` is post-fixed ────────────────────
    let sep_d = separation_full(env, dv, &stop_c, a, empty)?;
    let qd = Formula::forall(
        dv,
        Formula::iff(Formula::mem(td.clone(), tds.clone()), step_c.clone()),
    );
    debug_assert_eq!(
        *sep_d.concl(),
        Formula::exists(dset, qd.clone()),
        "csb_fixpoint: separation_full did not produce d's characteristic property"
    );

    let p = Formula::and(q.clone(), qd.clone());
    let p_q = and_left(q.clone(), qd.clone());
    let p_qd = and_right(q.clone(), qd.clone());
    let qd_at_d = prim::ax_inst(qd.clone(), td.clone())?;
    let p_d_fwd = hyp_iff_mp(&syl(&p_qd, &qd_at_d)?)?; // P → (d ∈ D → Φ(c)(d))
    let p_d_bwd = hyp_iff_mpr(&syl(&p_qd, &qd_at_d)?)?; // P → (Φ(c)(d) → d ∈ D)
    let p_pre_c = syl(&p_q, &q_prefixed)?;
    let prefixed_c = pre_fixed(f, g, xv, bv, dv, wv, &tcs, a, codom)?;
    let p_step_to_c = syl(&p_pre_c, &prim::ax_inst(prefixed_c.clone(), td.clone())?)?;
    // `P → d ⊆ c`
    let p_d_sub_c = hyp_gen(dv, &hyp_syl(&p_d_fwd, &p_step_to_c)?)?;
    let sub_d_c = kernel::thm::subset(env, tds.clone(), tcs.clone());
    debug_assert_eq!(
        *p_d_sub_c.concl(),
        Formula::imp(p.clone(), sub_d_c.clone()),
        "csb_fixpoint: d ⊆ c is not the subset formula monotonicity expects"
    );

    // `P → PRE(d)`: monotonicity along `d ⊆ c` turns `Φ(d)(z)` into `Φ(c)(z)`.
    let mono_dc = step_monotone(env, f, g, xv, bv, dv, wv, &tds, &tcs, a, codom)?;
    let p_mono = hyp_mp(&a1i(&mono_dc, p.clone()), &p_d_sub_c)?;
    let p_pre_d = hyp_gen(dv, &hyp_syl(&p_mono, &p_d_bwd)?)?;
    debug_assert_eq!(
        *p_pre_d.concl(),
        Formula::imp(p.clone(), pre_fixed(f, g, xv, bv, dv, wv, &tds, a, codom)?),
        "csb_fixpoint: d's pre-fixedness has the wrong shape"
    );

    // `P → c ⊆ d`, hence `P → ∀d. (d ∈ c → Φ(c)(d))`.
    let below_at_d = prim::ax_inst(below_all, tds.clone())?;
    let p_c_sub_d = hyp_mp(&syl(&syl(&p_q, &q_below)?, &below_at_d)?, &p_pre_d)?;
    let sub_c_d = kernel::thm::subset(env, tcs.clone(), tds.clone());
    debug_assert_eq!(
        *p_c_sub_d.concl(),
        Formula::imp(p.clone(), sub_c_d.clone()),
        "csb_fixpoint: c ⊆ d has the wrong shape"
    );
    let p_c_to_d = hyp_mp(&a1i(&prim::ax_inst(sub_c_d, td.clone())?, p.clone()), &p_c_sub_d)?;
    let p_postfixed = hyp_syl(&p_c_to_d, &p_d_fwd)?;

    // ── The biconditional, then discharge `d`, then discharge `c` ────────────
    let p_pre_at = syl(&p_pre_c, &prim::ax_inst(prefixed_c, td.clone())?)?;
    let p_iff = hyp_gen(dv, &hyp_and(&p_postfixed, &p_pre_at)?)?;
    let fixed_form = super::clauses::fixed(f, g, xv, bv, dv, wv, &tcs, a, codom)?;
    debug_assert_eq!(
        *p_iff.concl(),
        Formula::imp(p.clone(), fixed_form.clone()),
        "csb_fixpoint: the fixed-point equation has the wrong shape"
    );

    let q_fixed = discharge(dset, &a1i(&sep_d, q.clone()), &p_iff)?;
    let out = prim::mp(&exists_mono(cset, &Thm::gen(cset, &q_fixed))?, &sep)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::exists(cset, fixed_form),
        "csb_fixpoint: wrong shape"
    );
    Ok(out)
}
