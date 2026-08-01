//! The value at the new point.
//!
//! # Interface
//!
//! Private to [`crate::wrec_extend`]. `value_at_new_point` derives
//! `app(G, ⟨a,f⟩) = v` for the extended graph `G` — that the new pair really is
//! what `app` reads off at the new point, and not something the old graph `g`
//! already had there.
//!
//! # Why it needs the hypothesis
//!
//! `app` is `⋃ coll(G, x)`, so pinning it down at `⟨a,f⟩` means showing the new
//! pair is the *only* pair of `G` over that point. The old graph could in
//! principle contain one too — and the hypothesis that it does not is exactly
//! `¬indom(g, ⟨a,f⟩)`, which is the clause of [`super::hypothesis`] this file
//! spends. Everything downstream that computes with the extension goes through
//! this equation.

use kernel::{Env, Formula, Term, Thm};
use crate::wrec::{hyp_eq_symm, hyp_eq_trans, indom};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, hyp_and, hyp_mp, hyp_or_elim, iff_mp, inst_all,
    syl, uncurry,
};

use super::shared::{gen_under, hyp_inst, hyp_split};
use super::terms::Cx;

/// **Whatever `G` holds at `⟨a,f⟩`, it is `V`.**
///
/// ```text
/// ⊢ K → ∀y. (⟨⟨a,f⟩, y⟩ ∈ G → y = V)
/// ```
///
/// Two cases. If the pair is the new one, [`crate::pairs::opair_inj`] reads
/// `y = V` straight off. If it came from `wrec`, then `⟨a,f⟩` was already in
/// the recursor's domain, so [`crate::wrec::wrec_rec_cond`] gives
/// `app(wrec,⟨a,f⟩) = V` — the recursion equation at that very point — while
/// single-valuedness gives `app(wrec,⟨a,f⟩) = y`.
///
/// **This is what makes the union single-valued without a case analysis on
/// whether `⟨a,f⟩` is already in `dom wrec`.** The old value, if there is one,
/// is not merely compatible with `V`: it *is* `V`.
pub(super) fn value_at_new_point(env: &mut Env, wt: &Wtype, r: &Recursor, cx: &Cx) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let pair = ap.sets.pair(cx.w0.clone(), ty.clone());

    let m = Formula::and(cx.k.clone(), Formula::mem(pair.clone(), cx.g.clone()));
    let m_k = and_left(cx.k.clone(), Formula::mem(pair.clone(), cx.g.clone()));
    let m_g = and_right(cx.k.clone(), Formula::mem(pair.clone(), cx.g.clone()));
    let m_disj = syl(&m_g, &iff_mp(&cx.mem(s, &pair)?)?)?;

    // ── The pair came from `wrec` ───────────────────────────────────────────
    let mem_rec = Formula::mem(pair.clone(), cx.rec_t.clone());
    let n = Formula::and(m.clone(), mem_rec.clone());
    let n_m = and_left(m.clone(), mem_rec.clone());
    let n_rec = and_right(m.clone(), mem_rec);
    let n_k = syl(&n_m, &m_k)?;
    let n_cl = syl(&n_k, &cx.cl)?;

    // `indom(wrec, ⟨a,f⟩)`.
    let y2 = env.fresh_var();
    let n_indom = syl(
        &n_rec,
        &exists_intro_imp(
            y2,
            Formula::mem(ap.sets.pair(cx.w0.clone(), Term::var(y2)), cx.rec_t.clone()),
            ty.clone(),
        )?,
    )?;
    debug_assert_eq!(
        *n_indom.concl(),
        Formula::imp(n.clone(), indom(env, ap, &cx.rec_t, &cx.w0)),
        "value_at_new_point: indom drifted"
    );

    // `app(wrec,⟨a,f⟩) = V`, from the recursion equation on `wrec`'s own domain.
    let rc_at = hyp_inst(
        &syl(&n_cl, &inst_all(&r.rec_cond, &cx.ps)?)?,
        &[cx.a.clone(), cx.f.clone()],
    )?;
    let n_pair = hyp_mp(&rc_at, &n_indom)?;
    let (_, n_eq) = hyp_split(&n_pair)?;

    // `app(wrec,⟨a,f⟩) = y`, from single-valuedness.
    let n_sv = syl(&n_cl, &inst_all(&r.sv, &cx.ps)?)?;
    let n_app = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[cx.rec_t.clone(), cx.w0.clone(), ty.clone()])?,
            n.clone(),
        ),
        &hyp_and(&n_sv, &n_rec)?,
    )?;
    let n_flip = hyp_eq_symm(env, &n_app)?;
    let n_out = hyp_eq_trans(env, &n_flip, &n_eq)?;
    let left = uncurry(&n_out)?;

    // ── The pair is the new one ─────────────────────────────────────────────
    let right = a1i(
        &syl(
            &inst_all(
                &ap.pair_inj,
                &[cx.w0.clone(), ty.clone(), cx.w0.clone(), cx.v.clone()],
            )?,
            &and_right(
                Formula::eq(cx.w0.clone(), cx.w0.clone()),
                Formula::eq(ty.clone(), cx.v.clone()),
            ),
        )?,
        m.clone(),
    );

    let body = uncurry(&hyp_or_elim(&m_disj, &left, &right)?)?;
    gen_under(yv, &cx.k, &body)
}
