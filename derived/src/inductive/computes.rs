//! The general step computes — (S1), one rule per constructor.
//!
//! # Interface
//!
//! Private to [`crate::inductive`]; surfaced, generalised, as
//! [`super::recursor::GenRecursor::computes`]. The `i`-th rule evaluates the
//! step at an `i`-branch key built from explicit components:
//!
//! ```text
//! ⊢ (σ ∈ Aᵢ ∧ (f ∈ FWᵢ ∧ r ∈ FTᵢ))
//!       → app(e(p⃗,s⃗,T), ⟨Injᵢ(σ), ⟨f,r⟩⟩) = valᵢ(σ, f, r)
//! ```
//!
//! # Why these are stated at all
//!
//! They are the **non-vacuity witness for the step**: everything else in this
//! module would still be provable if `e` were a constant function, and these
//! rules rule that out — the value is built out of the caller's own `sᵢ`
//! applied to the key's own components, at fresh variables, at every
//! constructor. They are also the working form everything downstream
//! consumes: [`super::typed`] fires them at the no-junk decomposition of an
//! arbitrary tag, and [`super::iota`] at a constructor term.

use kernel::{Env, Formula, Term, Thm};

use crate::wrec::hyp_eq_trans;
use crate::{a1i, and_left, and_right, hyp_and, hyp_mp, iff_mpr, inst_all, syl};

use super::members::row_in_step;
use super::rec_shared::carry_under;
use super::step::{unpack, unpack_row, Rx, StepSym};

/// The `i`-th computation rule, at caller-supplied `σ`, `f`, `r` (normally
/// fresh variables). `sv` is [`super::values::step_single_valued`]'s theorem.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_app(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    sv: &Thm,
    i: usize,
    sigma: &Term,
    f: &Term,
    r: &Term,
) -> Option<Thm> {
    let s = cx.s();
    let ap = cx.ap();
    let step = cx.step(syms);

    // `H := σ ∈ Aᵢ ∧ (f ∈ FWᵢ ∧ r ∈ FTᵢ)`, which is exactly `⟨σ,⟨f,r⟩⟩ ∈ Qᵢ`.
    let (fw, ft) = (cx.fw(i)?, cx.ft(i)?);
    let m_sig = Formula::mem(sigma.clone(), cx.summand(i));
    let inner = Formula::and(
        Formula::mem(f.clone(), fw.clone()),
        Formula::mem(r.clone(), ft.clone()),
    );
    let hyp = Formula::and(m_sig.clone(), inner.clone());
    let p = ap.sets.pair(f.clone(), r.clone());
    let q = ap.sets.pair(sigma.clone(), p.clone());

    let into_pay = iff_mpr(&inst_all(
        &s.pair_in_prod,
        &[fw, ft, f.clone(), r.clone()],
    )?)?;
    let into_dom = iff_mpr(&inst_all(
        &s.pair_in_prod,
        &[cx.summand(i), cx.payload(i)?, sigma.clone(), p.clone()],
    )?)?;
    let h_pay = syl(&and_right(m_sig.clone(), inner.clone()), &into_pay)?;
    let h_dom = syl(
        &hyp_and(&and_left(m_sig.clone(), inner.clone()), &h_pay)?,
        &into_dom,
    )?;

    // The row is in the step, and a row at an explicit pair is the row at
    // its components.
    let h_row_at = syl(&h_dom, &row_in_step(env, cx, syms, i, &q)?)?;
    let ur = unpack_row(env, cx, i, sigma, &p)?;
    let step_c = step.clone();
    let h_row = carry_under(env, &ur, move |w| Formula::mem(w, step_c.clone()), &h_row_at)?;

    // Single-valuedness reads the value off the pair.
    let key = cx.key(i, sigma, &p)?;
    let packed = cx.val_packed(i, sigma, &p)?;
    let at = hyp_mp(
        &a1i(
            &inst_all(&cx.mach.wt.app_pair, &[step.clone(), key.clone(), packed.clone()])?,
            hyp.clone(),
        ),
        &hyp_and(&a1i(sv, hyp.clone()), &h_row)?,
    )?;
    let unp = unpack(env, cx, i, sigma, f, r)?;
    let out = hyp_eq_trans(env, &at, &a1i(&unp, hyp.clone()))?;
    if *out.concl()
        != Formula::imp(
            hyp,
            Formula::eq(ap.apply(step, key), cx.val(i, sigma, f, r)?),
        )
    {
        return None
    }
    Some(out)
}
