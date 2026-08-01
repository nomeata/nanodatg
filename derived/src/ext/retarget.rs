//! Swapping the codomain of a function space for any set the values land in.
//!
//! # Interface
//!
//! With `values_in(a,c,f) := ∀x. (x ∈ a → app(f,x) ∈ c)`, which is
//! [`values_in`], the export is
//!
//! ```text
//! ⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ values_in(a,c,f)) → f ∈ fs(a,c))   [funspace_retarget]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! All three clauses of `isfun` move across. Single-valuedness does not mention
//! the codomain at all. Totality does, and needs the value the old codomain
//! supplies to be recognised as `app(f,x)`, which is
//! [`crate::ext::app_of_pair`]. The subset clause is the same step once more.
//!
//! **No inhabitation anywhere**, and that is the point: on an empty domain the
//! hypothesis is vacuous and so is every clause, so this says `fs(∅,b)` and
//! `fs(∅,c)` have the same members for *any* `b` and `c` — the degenerate case
//! that a route through an equation between the codomains would have lost. It
//! is what makes [`crate::ext::dprod_const_fibre`] unconditional.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{Funspace, Product};
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};
use super::shared::{discharge, hyp_leibniz, isfun_parts};

/// `∀x. (x ∈ a → app(f,x) ∈ c)` — every value `f` takes on `a` lies in `c`.
///
/// The constant-fibre counterpart of [`crate::ext::is_section`], and the hypothesis
/// [`funspace_retarget`] swaps a codomain under.
pub fn values_in(env: &mut Env, ap: &Apply, a: &Term, c: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx), c.clone()),
        ),
    )
}

/// `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ (∀x. (x ∈ a → app(f,x) ∈ c))) → f ∈ fs(a,c))`
/// — the codomain of a function space may be replaced by any set the function's
/// values lie in.
///
/// All three clauses of `isfun` move across. Single-valuedness does not mention
/// the codomain at all. Totality does, and needs the value the old codomain
/// supplies to be recognised as `app(f,x)`, which is [`crate::ext::app_of_pair`]. The subset
/// clause is the same step once more: a member of `f` is a pair `⟨x,y⟩` with
/// `x ∈ a` and `y ∈ b`, and `y` is again `app(f,x)`, so it is in `c` and the
/// pair is in `prod(a,c)`.
///
/// **No inhabitation anywhere**, and that is the point: on an empty domain the
/// hypothesis is vacuous and so is every clause, so this says `fs(∅,b)` and
/// `fs(∅,c)` have the same members for *any* `b` and `c` — which is exactly the
/// degenerate case that a route through `⋃img(A) = B` would have lost.
pub fn funspace_retarget(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    app_pair: &Thm,
) -> Option<Thm> {
    let (av, bv, cv, f) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, tf) = (Term::var(av), Term::var(bv), Term::var(cv), Term::var(f));
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));

    // The hypothesis, rebuilt at our own `x` so that it can be opened.
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let app_t = ap.apply(tf.clone(), tx.clone());
    let vi_body = Formula::imp(mem_xa.clone(), Formula::mem(app_t.clone(), tc.clone()));
    let vi = Formula::forall(x, vi_body.clone());
    debug_assert_eq!(vi, values_in(env, ap, &ta, &tc, &tf), "funspace_retarget: shape drift");

    let mem_fs_b = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));
    let mem_fs_c = Formula::mem(tf.clone(), fsp.of(ta.clone(), tc.clone()));
    let h = Formula::and(mem_fs_b.clone(), vi.clone());

    let (isfun_b, sub_b, total_b, sv) = isfun_parts(env, ap, p, &ta, &tb, &tf)?;
    let (isfun_c, sub_c, total_c, sv_c) = isfun_parts(env, ap, p, &ta, &tc, &tf)?;
    if sv != sv_c {
        return None
    }
    let fs_at_b = inst_all(&fsp.fs_ax, &[ta.clone(), tb.clone(), tf.clone()])?;
    if *fs_at_b.concl() != Formula::iff(mem_fs_b.clone(), isfun_b) {
        return None
    }
    let fs_at_c = inst_all(&fsp.fs_ax, &[ta.clone(), tc.clone(), tf.clone()])?;
    if *fs_at_c.concl() != Formula::iff(mem_fs_c, isfun_c) {
        return None
    }

    let rest_b = Formula::and(total_b.clone(), sv.clone());
    let h_isfun = syl(&and_left(mem_fs_b.clone(), vi.clone()), &iff_mp(&fs_at_b)?)?;
    let h_sub_b = syl(&h_isfun, &and_left(sub_b.clone(), rest_b.clone()))?;
    let h_rest = syl(&h_isfun, &and_right(sub_b.clone(), rest_b))?;
    let h_total_b = syl(&h_rest, &and_left(total_b.clone(), sv.clone()))?;
    let h_sv = syl(&h_rest, &and_right(total_b.clone(), sv.clone()))?;
    let h_vi = and_right(mem_fs_b, vi.clone());

    // The instance of [`app_of_pair`] every clause below cashes in.
    let pair_xy = ap.sets.pair(tx.clone(), ty.clone());
    let mem_pair = Formula::mem(pair_xy.clone(), tf.clone());
    let ap_at = inst_all(app_pair, &[tf.clone(), tx.clone(), ty.clone()])?;
    if *ap_at.concl()
        != Formula::imp(
            Formula::and(sv.clone(), mem_pair.clone()),
            Formula::eq(app_t.clone(), ty.clone()),
        )
    {
        return None
    }

    // ── Totality, with the value moved into `c` ──────────────────────────────
    let mem_yb = Formula::mem(ty.clone(), tb.clone());
    let mem_yc = Formula::mem(ty.clone(), tc.clone());
    let body_b = Formula::and(mem_yb.clone(), mem_pair.clone());
    let body_c = Formula::and(mem_yc.clone(), mem_pair.clone());

    let k = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_ex_b = hyp_mp(
        &syl(&syl(&k_h, &h_total_b)?, &Thm::ax_inst(total_b, tx.clone())?)?,
        &k_xa,
    )?;
    debug_assert_eq!(
        *k_ex_b.concl(),
        Formula::imp(k.clone(), Formula::exists(y, body_b.clone())),
        "funspace_retarget: the totality clause has an unexpected shape"
    );
    let k_app_c =
        hyp_mp(&syl(&syl(&k_h, &h_vi)?, &Thm::ax_inst(vi.clone(), tx.clone())?)?, &k_xa)?;

    let j = Formula::and(k.clone(), body_b.clone());
    let j_k = and_left(k.clone(), body_b.clone());
    let j_body = and_right(k.clone(), body_b.clone());
    let j_pair = syl(&j_body, &and_right(mem_yb.clone(), mem_pair.clone()))?;
    let j_sv = syl(&j_k, &syl(&k_h, &h_sv)?)?;
    let j_eq = hyp_mp(&a1i(&ap_at, j), &hyp_and(&j_sv, &j_pair)?)?;
    let w1 = env.fresh_var();
    let j_yc = hyp_mp(
        &hyp_leibniz(&j_eq, w1, &Formula::mem(Term::var(w1), tc.clone()))?,
        &syl(&j_k, &k_app_c)?,
    )?;
    let j_ex_c = syl(
        &hyp_and(&j_yc, &j_pair)?,
        &exists_intro_imp(y, body_c.clone(), ty.clone())?,
    )?;
    let k_ex_c = discharge(y, &k_ex_b, &j_ex_c)?;
    let h_total_c = Thm::mp(
        &Thm::ax_dist(x, h.clone(), Formula::imp(mem_xa.clone(), Formula::exists(y, body_c)))?,
        &Thm::gen(x, &uncurry(&k_ex_c)?),
    )?;
    debug_assert_eq!(
        *h_total_c.concl(),
        Formula::imp(h.clone(), total_c),
        "funspace_retarget: the new totality clause has an unexpected shape"
    );

    // ── The graph sits inside `prod(a,c)` ────────────────────────────────────
    let mem_zf = Formula::mem(tz.clone(), tf.clone());
    let mem_z_prod_c = Formula::mem(tz.clone(), p.of(ta.clone(), tc.clone()));
    let eq_z_pair = Formula::eq(tz.clone(), pair_xy);

    let m = Formula::and(h.clone(), mem_zf.clone());
    let m_h = and_left(h.clone(), mem_zf.clone());
    let m_zf = and_right(h.clone(), mem_zf.clone());
    let m_zprod =
        hyp_mp(&syl(&syl(&m_h, &h_sub_b)?, &Thm::ax_inst(sub_b, tz.clone())?)?, &m_zf)?;
    let prod_at_b = inst_all(&p.prod_ax, &[ta.clone(), tb.clone(), tz.clone()])?;
    let inner_b = Formula::exists(y, Formula::and(mem_yb.clone(), eq_z_pair.clone()));
    let outer_b = Formula::and(mem_xa.clone(), inner_b.clone());
    if *prod_at_b.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), p.of(ta.clone(), tb.clone())),
            Formula::exists(x, outer_b.clone()),
        )
    {
        return None
    }
    let m_ex = syl(&m_zprod, &iff_mp(&prod_at_b)?)?;

    let n = Formula::and(m.clone(), outer_b.clone());
    let n_m = and_left(m.clone(), outer_b.clone());
    let n_outer = and_right(m.clone(), outer_b.clone());
    let n_xa = syl(&n_outer, &and_left(mem_xa.clone(), inner_b.clone()))?;
    let n_inner = syl(&n_outer, &and_right(mem_xa.clone(), inner_b))?;

    let body_pair_b = Formula::and(mem_yb.clone(), eq_z_pair.clone());
    let pf = Formula::and(n.clone(), body_pair_b.clone());
    let p_n = and_left(n.clone(), body_pair_b.clone());
    let p_body = and_right(n, body_pair_b);
    let p_zeq = syl(&p_body, &and_right(mem_yb, eq_z_pair.clone()))?;
    let p_zf = syl(&p_n, &syl(&n_m, &m_zf)?)?;
    let w2 = env.fresh_var();
    let p_pair_f = hyp_mp(
        &hyp_leibniz(&p_zeq, w2, &Formula::mem(Term::var(w2), tf.clone()))?,
        &p_zf,
    )?;
    let p_sv = syl(&p_n, &syl(&n_m, &syl(&m_h, &h_sv)?)?)?;
    let p_eq = hyp_mp(&a1i(&ap_at, pf), &hyp_and(&p_sv, &p_pair_f)?)?;

    let p_xa = syl(&p_n, &n_xa)?;
    let p_vi = syl(&p_n, &syl(&n_m, &syl(&m_h, &h_vi)?)?)?;
    let p_app_c = hyp_mp(&syl(&p_vi, &Thm::ax_inst(vi, tx.clone())?)?, &p_xa)?;
    let w3 = env.fresh_var();
    let p_yc =
        hyp_mp(&hyp_leibniz(&p_eq, w3, &Formula::mem(Term::var(w3), tc.clone()))?, &p_app_c)?;

    let body_pair_c = Formula::and(mem_yc.clone(), eq_z_pair);
    let inner_c = Formula::exists(y, body_pair_c.clone());
    let outer_c = Formula::and(mem_xa, inner_c.clone());
    let p_inner_c =
        syl(&hyp_and(&p_yc, &p_zeq)?, &exists_intro_imp(y, body_pair_c, ty)?)?;
    let p_outer_c = syl(
        &hyp_and(&p_xa, &p_inner_c)?,
        &exists_intro_imp(x, outer_c.clone(), tx)?,
    )?;
    let prod_at_c = inst_all(&p.prod_ax, &[ta.clone(), tc.clone(), tz.clone()])?;
    if *prod_at_c.concl() != Formula::iff(mem_z_prod_c.clone(), Formula::exists(x, outer_c)) {
        return None
    }
    let p_goal = syl(&p_outer_c, &iff_mpr(&prod_at_c)?)?;

    let n_goal = discharge(y, &n_inner, &p_goal)?;
    let m_goal = discharge(x, &m_ex, &n_goal)?;
    let h_sub_c = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_zf, mem_z_prod_c))?,
        &Thm::gen(z, &uncurry(&m_goal)?),
    )?;
    debug_assert_eq!(
        *h_sub_c.concl(),
        Formula::imp(h.clone(), sub_c),
        "funspace_retarget: the new subset clause has an unexpected shape"
    );

    // ── The three clauses, reassembled ───────────────────────────────────────
    let out = syl(&hyp_and(&h_sub_c, &hyp_and(&h_total_c, &h_sv)?)?, &iff_mpr(&fs_at_c)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tf, fsp.of(ta, tc))),
        "funspace_retarget: unexpected shape"
    );
    Some(gen_all(&[av, bv, cv, f], &out))
}
