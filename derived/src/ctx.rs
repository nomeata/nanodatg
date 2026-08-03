//! **A derivation carried out under an *optional* hypothesis.** Exports no
//! theorem; it is the glue that lets one derivation serve both the conditional
//! and the unconditional case.
//!
//! # Why it is an `Option` and not a `Formula`
//!
//! Two constructions in this crate come in exactly two flavours, and the
//! difference between them is *only* whether an antecedent is present:
//!
//! * a constructor's typing rule is stated under the conjunction of its
//!   arguments' typings, and a **nullary** constructor has none — the rule must
//!   come out as `⊢ ctor ∈ carrier`, not `⊢ ⊤ → ctor ∈ carrier`. That is not
//!   cosmetic: `INDUCTIVES.md`'s `Bool` measurement turns on
//!   `⟦Bool.true⟧ ∈ ⟦Bool⟧` being an unconditional closed theorem, because only
//!   an unconditional theorem closes a gap at the boundary.
//! * [`crate::isum::Dispatch`] over branches that are **constructed** has
//!   unconditional branch typings; over branches that are **variables** the
//!   typings are the caller's hypothesis and cannot be recovered. Both are the
//!   same nest of `case`s and the same fold, so they are one derivation with two
//!   contexts.
//!
//! Writing the derivation once against `Ctx` is what keeps the two from
//! drifting apart, and it is why the degenerate spelling stays **term-identical**
//! rather than merely provably equal.
//!
//! # Interface
//!
//! [`Ctx`] wraps an `Option<Formula>`. With `Some(H)` every combinator is the
//! implication-form rule from `crate::lib`; with `None` it is the ordinary one.
//! [`Ctx::under`] is the shape a caller should compare a result against.

use kernel::{Env, Formula, Term, Thm};

use crate::recursion::hyp::hyp_eq_symm;
use crate::{a1i, and_intro, conj_sub, eq_symm, hyp_and, hyp_mp, inst_all, syl};

/// An optional antecedent. `Ctx(None)` means every theorem below is stated
/// outright.
pub struct Ctx(pub Option<Formula>);

impl Ctx {
    /// The statement `⊢ H → φ`, or `⊢ φ` when there is no hypothesis — what a
    /// caller checking a result's shape should build.
    pub fn under(&self, phi: Formula) -> Formula {
        match &self.0 {
            Some(h) => Formula::imp(h.clone(), phi),
            None => phi,
        }
    }

    /// From `⊢ φ` infer `⊢ H → φ`.
    pub fn lift(&self, t: &Thm) -> Thm {
        match &self.0 {
            Some(h) => a1i(t, h.clone()),
            None => t.clone(),
        }
    }

    /// From `⊢ H → φ` and `⊢ φ → ψ` infer `⊢ H → ψ`.
    pub fn syl(&self, hp: &Thm, imp: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => syl(hp, imp),
            None => Thm::mp(imp, hp),
        }
    }

    /// From `⊢ H → (φ → ψ)` and `⊢ H → φ` infer `⊢ H → ψ`.
    pub fn mp(&self, hf: &Thm, ha: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_mp(hf, ha),
            None => Thm::mp(hf, ha),
        }
    }

    /// From `⊢ H → φ` and `⊢ H → ψ` infer `⊢ H → (φ ∧ ψ)`.
    pub fn and(&self, a: &Thm, b: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_and(a, b),
            None => Some(and_intro(a, b)),
        }
    }

    /// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, which needs `v` not free in `H`.
    pub fn gen(&self, v: kernel::FreeVar, t: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(h) => {
                let (_, phi) = t.concl().as_imp()?;
                Thm::mp(&Thm::ax_dist(v, h.clone(), phi)?, &Thm::gen(v, t))
            }
            None => Some(Thm::gen(v, t)),
        }
    }

    /// From `⊢ H → ∀v. φ` infer `⊢ H → φ[t/v]`.
    pub fn inst(&self, hall: &Thm, t: Term) -> Option<Thm> {
        match &self.0 {
            Some(_) => {
                let (_, all) = hall.concl().as_imp()?;
                syl(hall, &Thm::ax_inst(all, t)?)
            }
            None => inst_all(hall, std::slice::from_ref(&t)),
        }
    }

    /// From `⊢ H → a = b` infer `⊢ H → b = a`.
    pub fn eq_symm(&self, env: &mut Env, heq: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_eq_symm(env, heq),
            None => eq_symm(env, heq),
        }
    }

    /// `⊢ H → conj(atoms[start..end])`, for a run that is genuinely present.
    pub fn sub(&self, atoms: &[Formula], start: usize, end: usize) -> Option<Thm> {
        conj_sub(atoms, start, end)
    }
}
