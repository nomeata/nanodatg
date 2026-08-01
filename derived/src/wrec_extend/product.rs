//! **Clause 2 of the attempt condition**: the extension is a set of pairs over
//! the W-type.
//!
//! # Interface
//!
//! Private to [`crate::wrec_extend`]. `extension_in_product` is the second of
//! the three clauses [`super::assemble`] needs.
//!
//! # What has to be checked
//!
//! `g ⊆ prod(W,T)` comes with `g` being an attempt, so the only new obligation
//! is the new pair: `⟨a,f⟩ ∈ W` — which is `sup`'s typing rule
//! [`crate::wtype::sup_mem`] — and `v ∈ T`, which is `new_value_typed` and is
//! where the step's typing side condition
//! [`crate::wrec_total::step_typed`] is spent. That side condition cannot be
//! removed, and this is the file that shows why: without it there is nothing
//! whatsoever putting the step's value in the motive.

use kernel::{Env, Formula, Term, Thm};
use crate::wrec::comp_of;
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, inst_all, syl,
    uncurry,
};

use super::shared::{gen_under, hyp_inst};
use super::terms::Cx;

/// `⊢ K → V ∈ T` — **the new value is in the target**.
///
/// [`crate::wrec_total::step_typed`] at `a`, `f` and `r := comp(wrec,f,B(a))`.
/// Its first two premises are the induction step's own `a ∈ A` and
/// `f ∈ fs(B(a),W)`; the third is
/// [`crate::wrec_typing::wrec_composite_typed`] applied to the induction
/// hypothesis, and is the whole reason that lemma exists.
fn new_value_typed(r: &Recursor, cx: &Cx) -> Option<Thm> {
    let cmp = comp_of(r.comp, cx.rec_t.clone(), cx.f.clone(), cx.fibre.clone());
    let typed = hyp_mp(
        &hyp_inst(
            &syl(&cx.cl, &inst_all(&r.comp_typed, &cx.ps)?)?,
            &[cx.a.clone(), cx.f.clone()],
        )?,
        &cx.ih,
    )?;
    let at_a = hyp_mp(&hyp_inst(&cx.st, std::slice::from_ref(&cx.a))?, &cx.ma)?;
    let at_f = hyp_mp(&hyp_inst(&at_a, std::slice::from_ref(&cx.f))?, &cx.mf)?;
    hyp_mp(&hyp_inst(&at_f, std::slice::from_ref(&cmp))?, &typed)
}

/// `⊢ K → ⟨⟨a,f⟩, V⟩ ∈ prod(W,T)` — the new pair is a legal one.
fn new_pair_typed(wt: &Wtype, r: &Recursor, cx: &Cx) -> Option<Thm> {
    let s = &wt.sums;
    let in_w = hyp_mp(
        &hyp_inst(
            &hyp_mp(
                &hyp_inst(
                    &syl(&cx.cl, &inst_all(&wt.sup_mem, &cx.ps[0..3])?)?,
                    std::slice::from_ref(&cx.a),
                )?,
                &cx.ma,
            )?,
            std::slice::from_ref(&cx.f),
        )?,
        &cx.mf,
    )?;
    let in_t = new_value_typed(r, cx)?;
    let iff = inst_all(
        &s.pair_in_prod,
        &[cx.w_t.clone(), cx.ps[3].clone(), cx.w0.clone(), cx.v.clone()],
    )?;
    syl(&hyp_and(&in_w, &in_t)?, &iff_mpr(&iff)?)
}

/// **The extension is a set of pairs over `W` with values in `T`.**
///
/// ```text
/// ⊢ K → G ∈ 𝒫(prod(W(A,B,u), T))
/// ```
///
/// An old pair is in the product because `wrec` is
/// ([`crate::wrec::wrec_subset_prod`], which needs no hypothesis at all); the
/// new pair is because of [`new_pair_typed`].
pub(super) fn extension_in_product(env: &mut Env, wt: &Wtype, r: &Recursor, cx: &Cx) -> Option<Thm> {
    let s = &wt.sums;
    let prod_t = s.prod.of(cx.w_t.clone(), cx.ps[3].clone());
    let pv = env.fresh_var();
    let tp = Term::var(pv);

    let in_g = Formula::mem(tp.clone(), cx.g.clone());
    let m = Formula::and(cx.k.clone(), in_g.clone());
    let m_k = and_left(cx.k.clone(), in_g.clone());
    let m_g = and_right(cx.k.clone(), in_g);
    let m_disj = syl(&m_g, &iff_mp(&cx.mem(s, &tp)?)?)?;

    let sp = inst_all(&r.subset_prod, &cx.ps)?;
    let old = a1i(
        &Thm::mp(&Thm::ax_inst(sp.concl().clone(), tp.clone())?, &sp)?,
        m.clone(),
    );

    let hole = env.fresh_var();
    let carry = syl(
        &crate::eq_symm_imp(env, tp.clone(), cx.q.clone()),
        &Thm::eq_leibniz(
            cx.q.clone(),
            tp.clone(),
            hole,
            Formula::mem(Term::var(hole), prod_t.clone()),
        ),
    )?;
    let new = syl(
        &syl(&m_k, &new_pair_typed(wt, r, cx)?)?,
        &crate::com12(&carry)?,
    )?;

    let body = uncurry(&hyp_or_elim(&m_disj, &old, &new)?)?;
    let sub = gen_under(pv, &cx.k, &body)?;
    debug_assert_eq!(
        *sub.concl(),
        Formula::imp(cx.k.clone(), kernel::thm::subset(env, cx.g.clone(), prod_t.clone())),
        "extension_in_product: the inclusion has the wrong shape"
    );
    syl(&sub, &iff_mpr(&inst_all(&s.pow_ax, &[prod_t, cx.g.clone()])?)?)
}
