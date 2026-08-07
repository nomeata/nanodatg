//! Reading formulas back apart.
//!
//! # Interface
//!
//! Five readers, all total functions on syntax and **none of them a theorem**:
//!
//! ```text
//! φ ∧ ψ                  ↦  (φ, ψ)                       [split_and]
//! ∀x. φ, t               ↦  φ[t/x]                       [open_forall]
//! ∃x. φ, t               ↦  φ[t/x]                       [open_exists]
//! ⊢ H → (H → φ)          ↦  ⊢ H → φ                      [hyp_contract]
//! ⊢ (φ ∧ ψ) → χ          ↦  ⊢ φ → (ψ → χ)                [curry]
//! ```
//!
//! Public because [`crate::recursion`], [`crate::sums`] and the checker all use
//! them; they are the shared vocabulary for taking a kernel-built formula apart.
//!
//! The axioms are built by the kernel with the kernel's own fresh variables. A
//! derivation outside it either rebuilds each subformula (and hopes the shapes
//! agree) or *reads* them off, which is what these do. Reading is untrusted and
//! safe: no `Thm` is produced by the first three at all, and the last two are
//! ordinary combinator compositions, so a mistake here yields a rejected
//! derivation, never a wrong theorem.

use kernel::{Formula, Term, Thm};

use crate::err::{DResult, Operand};
use crate::prim::{self, Shape};
use crate::rules::{hyp_mp, syl};
use crate::{and_left, and_right, assembly, imp_refl};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub fn split_and(f: &Formula) -> DResult<(Formula, Formula)> {
    let (inner, fls) = f.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!("split_and: the conjunction is not a negation", Operand::formula("f", f)))
    }
    let (phi, not_psi) = inner.imp_parts()?;
    let (psi, fls2) = not_psi.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!("split_and: the second conjunct is not negated", Operand::formula("f", f)))
    }
    Ok((phi, psi))
}

/// Instantiate the body of `∀v. φ` at `t`, as a *formula* operation.
///
/// `Thm::ax_inst` is a theorem whatever `φ` is, so its conclusion can be mined
/// for the instance without `φ` being proved.
pub fn open_forall(phi: &Formula, t: &Term) -> DResult<Formula> {
    let inst = prim::ax_inst(phi.clone(), t.clone())?;
    let (_, body) = inst.concl().imp_parts()?;
    Ok(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`, so this unwraps two
/// negations around [`open_forall`].
pub fn open_exists(phi: &Formula, t: &Term) -> DResult<Formula> {
    let (all_not, fls) = phi.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!("open_exists: the existential is not a negated universal", Operand::formula("phi", phi)))
    }
    let not_body = open_forall(&all_not, t)?;
    let (body, fls2) = not_body.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!("open_exists: the opened body is not a negation", Operand::formula("phi", phi)))
    }
    Ok(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub fn hyp_contract(t: &Thm) -> DResult<Thm> {
    let (h, rest) = t.concl().imp_parts()?;
    let (h2, phi) = rest.imp_parts()?;
    if h != h2 {
        return Err(assembly!("hyp_contract: the two antecedents differ", Operand::thm("t", t)))
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    let step = prim::mp(&s, t)?;
    prim::mp(&step, &imp_refl(h))
}

/// From `⊢ A → (B → χ)` infer `⊢ (A ∧ B) → χ` — the converse of
/// [`crate::uncurry`].
pub fn curry(t: &Thm) -> DResult<Thm> {
    let (a, rest) = t.concl().imp_parts()?;
    let (b, _) = rest.imp_parts()?;
    // Under `A ∧ B`: apply the theorem to the left conjunct, then to the right.
    let via_a = syl(&and_left(a.clone(), b.clone()), t)?;
    hyp_mp(&via_a, &and_right(a, b))
}
