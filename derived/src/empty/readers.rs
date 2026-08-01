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

use crate::{and_left, and_right, hyp_mp, imp_refl, syl};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// Instantiate the body of `∀v. φ` at `t`, as a *formula* operation.
///
/// `Thm::ax_inst` is a theorem whatever `φ` is, so its conclusion can be mined
/// for the instance without `φ` being proved.
pub fn open_forall(phi: &Formula, t: &Term) -> Option<Formula> {
    let inst = Thm::ax_inst(phi.clone(), t.clone())?;
    let (_, body) = inst.concl().as_imp()?;
    Some(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`, so this unwraps two
/// negations around [`open_forall`].
pub fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let not_body = open_forall(&all_not, t)?;
    let (body, fls2) = not_body.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    let step = Thm::mp(&s, t)?;
    Thm::mp(&step, &imp_refl(h))
}

/// From `⊢ A → (B → χ)` infer `⊢ (A ∧ B) → χ` — the converse of
/// [`crate::uncurry`].
pub fn curry(t: &Thm) -> Option<Thm> {
    let (a, rest) = t.concl().as_imp()?;
    let (b, _) = rest.as_imp()?;
    // Under `A ∧ B`: apply the theorem to the left conjunct, then to the right.
    let via_a = syl(&and_left(a.clone(), b.clone()), t)?;
    hyp_mp(&via_a, &and_right(a, b))
}
