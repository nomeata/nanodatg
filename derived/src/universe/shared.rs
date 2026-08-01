//! Local readers and small combinators, private to [`crate::universe`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Deliberately private copies rather than imports from [`crate::empty`]: this
//! module should not break when a neighbouring derivation is reshaped. Reading a
//! formula apart is untrusted and safe — no `Thm` is produced by any of it, so a
//! helper here can fail to build a theorem but never build a wrong one.

use kernel::{Formula, Term, Thm};

use crate::{and_left, and_right, hyp_and, imp_refl};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub(super) fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
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
pub(super) fn open_forall(phi: &Formula, t: &Term) -> Option<Formula> {
    let (_, body) = Thm::ax_inst(phi.clone(), t.clone())?.concl().as_imp()?;
    Some(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (body, fls2) = open_forall(&all_not, t)?.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub(super) fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    Thm::mp(&Thm::mp(&s, t)?, &imp_refl(h))
}

/// `⊢ (a ∧ b) → (b ∧ a)`.
pub(super) fn and_comm_imp(a: Formula, b: Formula) -> Thm {
    hyp_and(&and_right(a.clone(), b.clone()), &and_left(a, b)).expect("and_comm_imp: shapes line up")
}
