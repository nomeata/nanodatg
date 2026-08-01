//! The step computes.
//!
//! # Interface
//!
//! Private to [`crate::wlist_rec`]; surfaced as
//! [`crate::wlist_rec::ListRec::app_nil`] and
//! [`crate::wlist_rec::ListRec::app_cons`]. The two equations evaluate the step
//! at the `nil` key and at a packed `cons` row.
//!
//! # Why these are stated at all
//!
//! They are the **non-vacuity** witness for the step. Everything else in this
//! module would still be provable if `e` were a constant function, and these two
//! equations rule that out: the first returns the caller's own `z`, the second a
//! term built out of the caller's own `s` applied to the head and to the
//! recursive value, at fresh variables. No degenerate step satisfies both.

use kernel::{Env, Formula, Term, Thm};
use crate::proj::Proj;
use crate::wlist::WList;
use crate::wrec::hyp_eq_trans;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, and_left, and_right, hyp_and, hyp_mp, iff_mpr, inst_all, syl};

use super::shared::carry_under;
use super::step::{StepSyms, key_cons, key_nil, payload, pow_prod, unpack, unpack_row, value_cons, value_packed};
use super::members::{nil_in_step, row_in_step};

/// `⊢ app(e(α,z,s,T), k₀) = z` and
/// `⊢ (h ∈ α ∧ (f ∈ FW(α) ∧ r ∈ FT(T))) → app(e, ⟨inr h,⟨f,r⟩⟩) = app(app(app(s,h),app(f,•)),app(r,•))`.
///
/// [`crate::ext::app_of_pair`] at the two memberships, with
/// [`step_single_valued`] supplying its single-valuedness premise, and
/// [`unpack`] turning the packed value into the one Lean's minor premise takes.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_apps(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    pj: &Proj,
    sy: &StepSyms,
    sv: &Thm,
    alpha: &Term,
    z: &Term,
    su: &Term,
    t: &Term,
    h: &Term,
    f: &Term,
    r: &Term,
) -> Option<(Thm, Thm)> {
    let s = &wt.sums;
    let ap = &s.ap;
    let step = sy.step_of(wt, alpha, z, su, t);

    let nil_mem = nil_in_step(env, wt, sy, alpha, z, su, t)?;
    let at_nil = Thm::mp(
        &inst_all(&wt.app_pair, &[step.clone(), key_nil(wt), z.clone()])?,
        &and_intro(sv, &nil_mem),
    )?;
    if *at_nil.concl() != Formula::eq(ap.apply(step.clone(), key_nil(wt)), z.clone()) {
        return None
    }

    // `H := h ∈ α ∧ (f ∈ FW ∧ r ∈ FT)`, which is exactly `⟨h,⟨f,r⟩⟩ ∈ Q(α,T)`.
    let lt = wl.ty_of(alpha.clone());
    let (fw, ft) = (pow_prod(s, &lt), pow_prod(s, t));
    let inner = Formula::and(
        Formula::mem(f.clone(), fw.clone()),
        Formula::mem(r.clone(), ft.clone()),
    );
    let hh = Formula::mem(h.clone(), alpha.clone());
    let hyp = Formula::and(hh.clone(), inner.clone());
    let p = ap.sets.pair(f.clone(), r.clone());
    let q = ap.sets.pair(h.clone(), p.clone());

    let into_pay = iff_mpr(&inst_all(&s.pair_in_prod, &[fw, ft, f.clone(), r.clone()])?)?;
    let into_dom = iff_mpr(&inst_all(
        &s.pair_in_prod,
        &[alpha.clone(), payload(s, wl, alpha, t), h.clone(), p.clone()],
    )?)?;
    let h_pay = syl(&and_right(hh.clone(), inner.clone()), &into_pay)?;
    let h_dom = syl(&hyp_and(&and_left(hh.clone(), inner.clone()), &h_pay)?, &into_dom)?;

    let row_mem = row_in_step(env, wt, wl, pj, sy, alpha, z, su, t, &q)?;
    let h_row_at = syl(&h_dom, &row_mem)?;

    // The row at an explicit pair is the row at its components.
    let ur = unpack_row(env, wt, pj, su, h, &p)?;
    let step_c = step.clone();
    let h_row = carry_under(env, &ur, move |w| Formula::mem(w, step_c.clone()), &h_row_at)?;

    let key = key_cons(wt, h, f, r);
    let packed = value_packed(ap, pj, su, h, &p);
    let at = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[step.clone(), key.clone(), packed.clone()])?,
            hyp.clone(),
        ),
        &hyp_and(&a1i(sv, hyp.clone()), &h_row)?,
    )?;
    let unp = unpack(env, ap, pj, su, h, f, r)?;
    let at_cons = hyp_eq_trans(env, &at, &a1i(&unp, hyp.clone()))?;
    if *at_cons.concl()
        != Formula::imp(
            hyp,
            Formula::eq(ap.apply(step, key), value_cons(ap, su, h, f, r)),
        )
    {
        return None
    }
    Some((at_nil, at_cons))
}
