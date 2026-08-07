//! Local readers and small combinators, private to [`crate::universe`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Deliberately private copies rather than imports from [`crate::empty`]: this
//! module should not break when a neighbouring derivation is reshaped. Reading a
//! formula apart is untrusted and safe — no `Thm` is produced by any of it, so a
//! helper here can fail to build a theorem but never build a wrong one.
//!
//! # How these fail
//!
//! Every refusal below is a [`crate::err::DerErr::Assembly`], never a decline.
//! These are *readers*: each is handed a formula the derivation above it built
//! and asked to take apart the connective it is named for, so a refusal means
//! the formula is not the shape its builder thought — a bug in that builder.
//! Nothing here has a contract a caller can legitimately fail to meet.

use kernel::{Formula, Term, Thm};

use crate::err::{DResult, Operand};
use crate::prim::{self, Shape};
use crate::rules::hyp_and;
use crate::{and_left, and_right, assembly, imp_refl};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub(super) fn split_and(f: &Formula) -> DResult<(Formula, Formula)> {
    let (inner, fls) = f.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!("split_and: the outer implication is not a negation", Operand::formula("f", f)))
    }
    let (phi, not_psi) = inner.imp_parts()?;
    let (psi, fls2) = not_psi.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!(
            "split_and: the right conjunct's negation is not one",
            Operand::formula("f", f),
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
        return Err(assembly!("open_exists: the existential is not a negated universal", Operand::formula("phi", phi)))
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
pub(super) fn hyp_contract(t: &Thm) -> DResult<Thm> {
    let (h, rest) = t.concl().imp_parts()?;
    let (h2, phi) = rest.imp_parts()?;
    if h != h2 {
        return Err(assembly!("hyp_contract: the two antecedents differ", Operand::thm("t", t)))
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    prim::mp(&prim::mp(&s, t)?, &imp_refl(h))
}

/// `⊢ (a ∧ b) → (b ∧ a)`.
pub(super) fn and_comm_imp(a: Formula, b: Formula) -> Thm {
    hyp_and(&and_right(a.clone(), b.clone()), &and_left(a, b)).expect("and_comm_imp: shapes line up")
}
