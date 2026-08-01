//! The step computes.
//!
//! # Interface
//!
//! Private to [`crate::wnat_rec`]. `step_apps` is the pair of equations
//!
//! ```text
//! ⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z
//! ⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) →
//!       app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩) = app(app(s,app(f,•)),app(r,•)))
//! ```
//!
//! surfaced as [`crate::wnat_rec::NatRec::app_zero`] and
//! [`crate::wnat_rec::NatRec::app_succ`].
//!
//! # Why these are stated at all
//!
//! They are the **non-vacuity** witness for the step. Everything else in this
//! module would still be provable if `e` were a constant function, and these two
//! equations rule that out: the first returns the caller's `z`, the second
//! returns a term built out of the caller's own `s`, at fresh variables. No
//! degenerate step satisfies both.

use kernel::{Env, Formula, Term, Thm};
use crate::wnat::Nat;
use crate::proj::Proj;
use crate::wrec::hyp_eq_trans;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, hyp_and, hyp_mp, iff_mpr, inst_all, syl};

use super::step::{StepSyms, key_succ, key_zero, pow_prod, unpack, value_packed, value_succ};
use super::members::{row_in_step, zero_in_step};

/// `⊢ app(e(z,s,T), k₀) = z` and
/// `⊢ (f ∈ FW ∧ r ∈ FT(T)) → app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩) = app(app(s,app(f,•)),app(r,•))`.
///
/// [`crate::ext::app_of_pair`] at the two memberships, with
/// [`step_single_valued`] supplying its single-valuedness premise, and
/// [`unpack`] turning the packed value into the one Lean's minor premise takes.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_apps(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    pj: &Proj,
    sy: &StepSyms,
    sv: &Thm,
    z: &Term,
    su: &Term,
    t: &Term,
    f: &Term,
    r: &Term,
) -> Option<(Thm, Thm)> {
    let s = &wt.sums;
    let ap = &s.ap;
    let step = sy.step_of(wt, z, su, t);

    let zero_mem = zero_in_step(env, wt, sy, z, su, t)?;
    let at_zero = Thm::mp(
        &inst_all(&wt.app_pair, &[step.clone(), key_zero(wt), z.clone()])?,
        &and_intro(sv, &zero_mem),
    )?;
    if *at_zero.concl() != Formula::eq(ap.apply(step.clone(), key_zero(wt)), z.clone()) {
        return None
    }

    // `H := f ∈ FW ∧ r ∈ FT(T)`, which is exactly `⟨f,r⟩ ∈ prod(FW, FT(T))`.
    let (fw, ft) = (pow_prod(s, &nat.ty), pow_prod(s, t));
    let h = Formula::and(
        Formula::mem(f.clone(), fw.clone()),
        Formula::mem(r.clone(), ft.clone()),
    );
    let p = ap.sets.pair(f.clone(), r.clone());
    let into_prod = iff_mpr(&inst_all(&s.pair_in_prod, &[fw, ft, f.clone(), r.clone()])?)?;
    let row_mem = row_in_step(env, wt, nat, pj, sy, z, su, t, &p)?;
    let h_row = syl(&into_prod, &row_mem)?;

    let key = key_succ(wt, f, r);
    let packed = value_packed(ap, pj, su, &p);
    let at = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[step.clone(), key.clone(), packed.clone()])?,
            h.clone(),
        ),
        &hyp_and(&a1i(sv, h.clone()), &h_row)?,
    )?;
    let unp = unpack(env, ap, pj, su, f, r)?;
    let at_succ = hyp_eq_trans(env, &at, &a1i(&unp, h.clone()))?;
    if *at_succ.concl()
        != Formula::imp(
            h,
            Formula::eq(ap.apply(step, key), value_succ(ap, su, f, r)),
        )
    {
        return None
    }
    Some((at_zero, at_succ))
}
