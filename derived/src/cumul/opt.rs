//! Private combinators for a derivation carried out under an **optional**
//! hypothesis. Exports no theorem and is not re-exported.
//!
//! The same device as `crate::inductive::shared`, and it is here for the same
//! reason. A closed declaration's `⊢ ⟦T⟧ ∈ U₁` must be **unconditional** —
//! `⊢ ⊤ → ⟦T⟧ ∈ U₁` does not close a gap at the checker's boundary — while a
//! parameterised one genuinely owes something about its parameters
//! (`⊢ α ∈ U₁ → ⟦List α⟧ ∈ U₁`, since a `List` over a proper-class-sized `α`
//! is no member of any universe). One derivation has to produce both shapes.
//!
//! The antecedent is carried in the **conclusion**, never as a sequent
//! hypothesis: `Thm::gen` over a declaration's parameters is the last step of
//! [`super::decl`], and generalising a variable that a `Γ` mentions is exactly
//! what that would forbid.

use kernel::{Formula, FreeVar, Term, Thm};

use crate::{a1i, and_intro, hyp_and, hyp_mp, inst_all, syl};

/// An optional antecedent. `Ctx(None)` means every theorem is stated outright.
pub(super) struct Ctx(pub Option<Formula>);

impl Ctx {
    /// From `⊢ φ` infer `⊢ H → φ`.
    pub(super) fn lift(&self, t: &Thm) -> Thm {
        match &self.0 {
            Some(h) => a1i(t, h.clone()),
            None => t.clone(),
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

    /// From `⊢ H → φ` and `⊢ H → ψ` infer `⊢ H → (φ ∧ ψ)`.
    pub(super) fn and(&self, hp: &Thm, hq: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_and(hp, hq),
            None => Some(and_intro(hp, hq)),
        }
    }

    /// From `⊢ H → (φ → ψ)` and `⊢ H → (ψ → χ)` infer `⊢ H → (φ → χ)`.
    pub(super) fn syl(&self, hf: &Thm, hg: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => crate::separation::hyp_syl(hf, hg),
            None => syl(hf, hg),
        }
    }

    /// From `⊢ H → φ` infer `⊢ H → ∀v. φ`.
    ///
    /// `v` must not occur free in `H` — at every use here `v` is `env`-fresh
    /// and `H` is the declaration's parameter scope, so it cannot.
    pub(super) fn gen(&self, v: FreeVar, body: &Formula, t: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(h) => Thm::mp(&Thm::ax_dist(v, h.clone(), body.clone())?, &Thm::gen(v, t)),
            None => Some(Thm::gen(v, t)),
        }
    }

    /// The formula this context's theorems have, given the bare conclusion.
    pub(super) fn wrap(&self, concl: Formula) -> Formula {
        match &self.0 {
            Some(h) => Formula::imp(h.clone(), concl),
            None => concl,
        }
    }
}
