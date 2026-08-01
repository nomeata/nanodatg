//! Private combinators more than one file in [`crate::quot`] needs.
//!
//! Exports no theorem and is not re-exported from the hub. Everything here is
//! pure formula plumbing: instantiating a nest of universal quantifiers, taking
//! a conjunction apart, and rewriting one side of a membership along an
//! equation. The quotient files are long enough without three copies of each.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{exists_elim_imp, com12, imp_refl, syl};

/// `⊢ (∀x₁ … ∀xₙ. φ) → φ[t₁/x₁, …, tₙ/xₙ]` — instantiate a nest of universal
/// quantifiers, given the formula rather than a theorem.
///
/// [`crate::inst_all`] does the same to a *proved* `∀`; this is the implication
/// form, which is what a clause read off a guard needs.
pub(super) fn inst_formula(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let (first, rest) = ts.split_first()?;
    let mut th = Thm::ax_inst(phi.clone(), first.clone())?;
    for t in rest {
        let (_, body) = th.concl().as_imp()?;
        th = syl(&th, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(th)
}

/// Take `φ ∧ ψ` apart. `Formula::and` is `¬(φ → ¬ψ)`, so this is two
/// [`Formula::as_imp`] steps and a discard.
pub(super) fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, _) = f.as_imp()?;
    let (a, nb) = inner.as_imp()?;
    let (b, _) = nb.as_imp()?;
    Some((a, b))
}

/// `⊢ a = b → (u ∈ a → u ∈ b)` — carry a membership across an equation between
/// the two *sets*.
pub(super) fn carry_mem(env: &mut Env, u: Term, a: Term, b: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(a, b, w, Formula::mem(u, Term::var(w)))
}

/// `⊢ a = b → (a ∈ S → b ∈ S)` — carry a membership across an equation between
/// the two *elements*.
///
/// The mirror of [`carry_mem`], which rewrites the set. Getting these two the
/// wrong way round type-checks and then silently fails to compose, so they are
/// named for the side they move.
pub(super) fn carry_elem(env: &mut Env, a: Term, b: Term, set: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(a, b, w, Formula::mem(Term::var(w), set))
}

/// `⊢ b = c → (a = b → a = c)` — transitivity of equality, in the
/// hypothesis-composable implication form.
pub(super) fn eq_chain(env: &mut Env, a: Term, b: Term, c: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(b, c, w, Formula::eq(a, Term::var(w)))
}

/// From `⊢ H → φ` infer `⊢ H → ∀x. φ`, provided `x` is not free in `H`.
///
/// The generalisation rule lifted into the hypothesis-form discipline of
/// `crate::lib`'s "reasoning under a fixed hypothesis" section. `None` when
/// `Thm::ax_dist`'s side condition fails, i.e. exactly when `x` *is* free in
/// `H` and the inference would be unsound.
pub(super) fn hyp_gen(x: FreeVar, t: &Thm) -> Option<Thm> {
    let (h, phi) = t.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(x, h, phi)?, &Thm::gen(x, t))
}

/// Existential elimination under a fixed hypothesis: from
/// `⊢ H → ∃x. E(x)` and `⊢ H → (E(x) → K)` infer `⊢ H → K`.
///
/// `x` must be free in neither `H` nor `K`; the first is enforced by
/// `Thm::ax_dist` inside [`exists_elim_imp`], the second by that function's own
/// side condition. This is the "obtain a witness" step, and without it every
/// derivation over [`super::lift`]'s Replacement image would have to open the
/// existential by hand.
///
/// The last move is a **contraction**: eliminating the existential produces
/// `⊢ H → (H → K)`, because `H` is used twice — once to supply the witness and
/// once inside the body — and `S` collapses that back to `⊢ H → K`.
pub(super) fn hyp_obtain(x: FreeVar, ex: &Thm, body: &Thm) -> Option<Thm> {
    let (h, _) = ex.concl().as_imp()?;
    let (h2, rest) = body.concl().as_imp()?;
    if h != h2 {
        return None
    }
    let (_, k) = rest.as_imp()?;
    let all = Thm::gen(x, &com12(body)?);
    let elim = exists_elim_imp(x, &all, &Formula::imp(h.clone(), k.clone()))?;
    let doubled = syl(ex, &elim)?;
    let s = Thm::ax_s(h.clone(), h.clone(), k);
    Thm::mp(&Thm::mp(&s, &doubled)?, &imp_refl(h))
}
