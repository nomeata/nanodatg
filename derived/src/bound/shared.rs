//! Internal readers and combinators shared by the constructions in
//! [`crate::bound`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Every step of the chain is derived under an ambient hypothesis — the
//! conjunction `is_universe(u) ∧ …` — and there is no deduction theorem, so
//! instantiation, modus ponens and Leibniz all have to exist in the `H → …`
//! form; that is [`hyp_inst`], [`hyp_inst_mp`] and [`hyp_leibniz`].
//!
//! [`split_and`], [`open_forall`] and [`open_exists`] take formulas apart:
//! `φ ∧ ψ` is `¬(φ → ¬ψ)` and `∃v. φ` is `¬∀v. ¬φ`, so reading either back
//! needs an explicit reader, and instantiating a quantifier whose body is only
//! available as a formula needs the substituted body built by hand. Taking a
//! formula apart produces no `Thm`, so a bug in one can only cause a rejection.

use kernel::{Formula, FreeVar, Term, Thm};
use crate::{a1i, hyp_mp, syl};

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

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])` — Leibniz under a
/// hypothesis.
pub(super) fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ H → ∀v. (P → Q)` and `⊢ H → P[t/v]` infer `⊢ H → Q[t/v]` — instantiate
/// a universal that sits under a hypothesis, and detach.
pub(super) fn hyp_inst_mp(h_all: &Thm, t: &Term, h_arg: &Thm) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    let at = Thm::ax_inst(all, t.clone())?;
    hyp_mp(&syl(h_all, &at)?, h_arg)
}

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}
