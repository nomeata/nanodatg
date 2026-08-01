//! Internal helpers shared by the constructions in [`crate::sums`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** Two
//! kinds of thing live here: the term constructors that name `0`, `1`, `inl`,
//! `inr` and the body of `A + B`, and the small implication-form inference
//! steps that more than one sibling module needs.
//!
//! The term constructors are here rather than in [`super::sum`] because
//! [`super::cases`] builds `inl(u)` and `inr(u)` inside the Separation
//! condition that carves out `rec₊`, so both files must spell the tags exactly
//! the same way or nothing composes.
//!
//! Every equation in these derivations is hypothetical, so the equality
//! toolkit in [`crate`] — which consumes *proved* equations — does not apply,
//! and each rewrite is wanted in implication form instead. Reading formulas
//! apart produces no `Thm`, so a helper here can fail to build a theorem but
//! never build a wrong one.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::funspace::{bin_union, Product};
use crate::{
    a1i, and_intro, com12, contrapos, exists_elim_imp, iff_mp, iff_mpr, imp_refl, opair, singleton,
    syl, uncurry,
};

/// `⊢ u = v → (t ∈ u → t ∈ v)` — carry a membership across an equation.
pub(super) fn carry_mem(env: &mut Env, t: Term, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::mem(t, Term::var(w)))
}

/// `⊢ u = v → (u ∈ t → v ∈ t)` — carry an element across an equation.
pub(super) fn carry_elem(env: &mut Env, u: Term, v: Term, t: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::mem(Term::var(w), t))
}

/// `⊢ u = v → (t = u → t = v)` — rewrite the right-hand side of an equation.
pub(super) fn carry_eq_rhs(env: &mut Env, t: Term, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::eq(t, Term::var(w)))
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

/// From `⊢ φ ↔ ψ` and `⊢ ψ ↔ χ` infer `⊢ φ ↔ χ`.
pub(super) fn iff_trans(ab: &Thm, bc: &Thm) -> Option<Thm> {
    let fwd = syl(&iff_mp(ab)?, &iff_mp(bc)?)?;
    let bwd = syl(&iff_mpr(bc)?, &iff_mpr(ab)?)?;
    Some(and_intro(&fwd, &bwd))
}

/// From `⊢ p₁ → p₂` and `⊢ q₁ → q₂` infer `⊢ (p₁ ∨ q₁) → (p₂ ∨ q₂)`.
///
/// `a ∨ b` is `¬a → b`, so monotonicity in the *left* disjunct runs backwards:
/// it is the contraposition of `p₁ → p₂` that composes.
pub(super) fn or_mono(p12: &Thm, q12: &Thm) -> Option<Thm> {
    let (p1, _) = p12.concl().as_imp()?;
    let (q1, _) = q12.concl().as_imp()?;
    let h = Formula::imp(Formula::not(p1), q1); // p₁ ∨ q₁
    let h_np2_np1 = a1i(&contrapos(p12)?, h.clone());
    let h_np1_q1 = imp_refl(h.clone());
    let h_np2_q1 = hyp_syl(&h_np2_np1, &h_np1_q1)?;
    hyp_syl(&h_np2_q1, &a1i(q12, h))
}

/// From `⊢ p₁ ↔ p₂` and `⊢ q₁ ↔ q₂` infer `⊢ (p₁ ∨ q₁) ↔ (p₂ ∨ q₂)`.
pub(super) fn or_iff(p: &Thm, q: &Thm) -> Option<Thm> {
    let fwd = or_mono(&iff_mp(p)?, &iff_mp(q)?)?;
    let bwd = or_mono(&iff_mpr(p)?, &iff_mpr(q)?)?;
    Some(and_intro(&fwd, &bwd))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// The term `∅` — both `0` and the point `•`.
pub(super) fn zero_of(ap: &Apply) -> Term { Term::apply(ap.empty, vec![]) }

/// The term `1 = {∅}`.
pub(super) fn unit_of(ap: &Apply) -> Term { singleton(ap.sets.up, zero_of(ap)) }

/// `inl(a) = ⟨∅, a⟩`.
pub(super) fn inl_of(ap: &Apply, a: Term) -> Term { opair(ap.sets.up, zero_of(ap), a) }

/// `inr(b) = ⟨1, b⟩`.
pub(super) fn inr_of(ap: &Apply, b: Term) -> Term { opair(ap.sets.up, unit_of(ap), b) }

/// `({∅} × A) ∪ ({1} × B)`, the term the symbol `sum` abbreviates.
pub(super) fn sum_body(ap: &Apply, p: &Product, a: Term, b: Term) -> Term {
    bin_union(
        &ap.sets,
        p.of(singleton(ap.sets.up, zero_of(ap)), a),
        p.of(singleton(ap.sets.up, unit_of(ap)), b),
    )
}
