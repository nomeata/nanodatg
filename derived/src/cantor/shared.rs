//! Internal readers and combinators shared by the constructions in
//! [`crate::cantor`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`split_and`], [`open_forall`] and [`open_exists`] take formulas apart —
//! `φ ∧ ψ` is `¬(φ → ¬ψ)` and `∃v. φ` is `¬∀v. ¬φ`, so reading either back
//! needs an explicit reader. The rest are the `H → …` forms of contraction,
//! existential discharge and instantiation, which have to exist separately
//! because every step of the diagonal argument runs under the ambient
//! hypothesis `DOM ∧ (SV ∧ ONTO)` and there is no deduction theorem.
//!
//! Reading a formula apart produces no `Thm`, so a bug in one of these can only
//! cause a rejection, never a wrong theorem.
//!
//! # How these fail
//!
//! Every explicit refusal below is a [`crate::err::DerErr::Assembly`], never a
//! decline. The module is private to [`crate::cantor`], so the caller of
//! everything here *is* that module: a formula that is not the connective its
//! parameter's name claims was built by a `cantor` derivation, and that
//! derivation is the bug. Nothing here has a contract an outside caller could
//! legitimately fail to meet.
//!
//! The **thin combinators** — [`hyp_contract`], [`discharge`] and
//! [`inst_all_imp`] — carry `#[track_caller]`. Each is called from every step of
//! the derivations in [`super::diagonal`], [`super::equinumerous`] and
//! [`super::image`], so a failure sited on its own line names this file, which
//! the reader already knew; annotated, the site is the line of the construction
//! that composed the call. The three **readers** are deliberately *not*
//! annotated: each peels several connectives off a single formula, and which of
//! them did not come apart is exactly what a site inside this file says.

use kernel::{Formula, FreeVar, Term, Thm};

use crate::err::{DResult, Operand};
use crate::prim::{self, Shape};
use crate::rules::{com12, exists_elim_imp, syl, uncurry};
use crate::{assembly, imp_refl};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub(super) fn split_and(f: &Formula) -> DResult<(Formula, Formula)> {
    let (inner, fls) = f.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!(
            "split_and: the conjunction is not a negation",
            Operand::formula("f", f),
        ))
    }
    let (phi, not_psi) = inner.imp_parts()?;
    let (psi, fls2) = not_psi.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!(
            "split_and: the second conjunct is not negated",
            Operand::formula("not_psi", &not_psi),
        ))
    }
    Ok((phi, psi))
}

/// Instantiate the body of `∀v. φ` at `t`, as a *formula* operation.
pub(super) fn open_forall(phi: &Formula, t: &Term) -> DResult<Formula> {
    let (_, body) = prim::ax_inst(phi.clone(), t.clone())?.concl().imp_parts()?;
    Ok(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> DResult<Formula> {
    let (all_not, fls) = phi.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!(
            "open_exists: the existential is not a negated universal",
            Operand::formula("phi", phi),
        ))
    }
    let (body, fls2) = open_forall(&all_not, t)?.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!(
            "open_exists: the opened body is not a negation",
            Operand::formula("phi", phi),
            Operand::term("t", t),
        ))
    }
    Ok(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
#[track_caller]
pub(super) fn hyp_contract(t: &Thm) -> DResult<Thm> {
    let (h, rest) = t.concl().imp_parts()?;
    let (h2, phi) = rest.imp_parts()?;
    if h != h2 {
        return Err(assembly!("hyp_contract: the two antecedents differ", Operand::thm("t", t)))
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    prim::mp(&prim::mp(&s, t)?, &imp_refl(h))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging `v`.
#[track_caller]
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> DResult<Thm> {
    let (_, goal) = he_goal.concl().imp_parts()?;
    let (h, _) = h_ex.concl().imp_parts()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — instantiation in implication form, for a quantified
/// formula that is only available under a hypothesis.
#[track_caller]
pub(super) fn inst_all_imp(phi: &Formula, ts: &[Term]) -> DResult<Thm> {
    let first = match ts.first() {
        Some(t) => t,
        None =>
            return Err(assembly!(
                "inst_all_imp: there is nothing to instantiate at",
                Operand::formula("phi", phi),
            )),
    };
    let mut cur = prim::ax_inst(phi.clone(), first.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().imp_parts()?;
        cur = syl(&cur, &prim::ax_inst(body, t.clone())?)?;
    }
    Ok(cur)
}
