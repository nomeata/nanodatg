//! Private combinators for a derivation carried out under an **optional**
//! hypothesis. Exports no theorem and is not re-exported.
//!
//! A constructor's typing rule is stated under the conjunction of its
//! arguments' typings — and a *nullary* constructor has none, so the rule must
//! come out as `⊢ ctor ∈ carrier` and not `⊢ ⊤ → ctor ∈ carrier`. That
//! distinction is not cosmetic: `INDUCTIVES.md`'s `Bool` measurement turns on
//! `⟦Bool.true⟧ ∈ ⟦Bool⟧` being an **unconditional** closed theorem, because
//! only an unconditional theorem closes a gap at the boundary.
//!
//! [`Ctx`] is therefore an `Option<Formula>`, and every step of the derivation
//! goes through it: with `Some(H)` each combinator is the implication-form rule
//! from `crate::lib`, with `None` it is the ordinary one.

use kernel::{Env, Formula, Term, Thm};

use crate::{a1i, conj_sub, eq_symm, hyp_mp, inst_all, syl};
use crate::recursion::hyp::hyp_eq_symm;

/// An optional antecedent. `Ctx(None)` means every theorem below is stated
/// outright.
pub(super) struct Ctx(pub Option<Formula>);

impl Ctx {
    /// From `⊢ φ` infer `⊢ H → φ`.
    pub(super) fn lift(&self, t: &Thm) -> Thm {
        match &self.0 {
            Some(h) => a1i(t, h.clone()),
            None => t.clone(),
        }
    }

    /// From `⊢ H → φ` and `⊢ φ → ψ` infer `⊢ H → ψ`.
    pub(super) fn syl(&self, hp: &Thm, imp: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => syl(hp, imp),
            None => Thm::mp(imp, hp),
        }
    }

    /// From `⊢ H → (φ → ψ)` and `⊢ H → φ` infer `⊢ H → ψ`.
    pub(super) fn mp(&self, hf: &Thm, ha: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_mp(hf, ha),
            None => Thm::mp(hf, ha),
        }
    }

    /// From `⊢ H → ∀v. φ` infer `⊢ H → φ[t/v]`.
    pub(super) fn inst(&self, hall: &Thm, t: Term) -> Option<Thm> {
        match &self.0 {
            Some(_) => {
                let (_, all) = hall.concl().as_imp()?;
                syl(hall, &Thm::ax_inst(all, t)?)
            }
            None => inst_all(hall, std::slice::from_ref(&t)),
        }
    }

    /// From `⊢ H → a = b` infer `⊢ H → b = a`.
    pub(super) fn eq_symm(&self, env: &mut Env, heq: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_eq_symm(env, heq),
            None => eq_symm(env, heq),
        }
    }

    /// `⊢ H → conj(atoms[start..end])`, for a run that is genuinely present.
    pub(super) fn sub(&self, atoms: &[Formula], start: usize, end: usize) -> Option<Thm> {
        conj_sub(atoms, start, end)
    }
}
