//! Small combinators, private to [`crate::funspace`] except for one.
//!
//! # Interface
//!
//! ```text
//! from ⊢ (H ∧ E) → φ and ⊢ H → ∃v. E    infer ⊢ H → φ     [discharge]
//! ```
//!
//! discharging the witness `v`, which must not occur free in `H` or `φ`. That
//! side condition is the whole content: drop it and a witness escapes its scope.
//!
//! [`discharge`] is public because [`crate::recursion`] and [`crate::bound`] run
//! the same move several deep — the approximation argument opens a pair, then
//! its second component, then the value of the other graph at the same point —
//! and duplicating it there would mean several copies of the one place where the
//! side condition matters.
//!
//! Everything else here is private and is a *reader*: it takes a formula apart
//! or shuffles a conjunction. Private copies rather than imports, because the
//! neighbouring modules keep theirs private too and a derivation this long
//! should not break when one of them is reshaped. Reading formulas apart is
//! untrusted and safe — no `Thm` is produced by any of it.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{com12, exists_elim_imp, imp_refl, syl, uncurry};

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

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
///
/// Public because [`crate::recursion`] runs the same move three deep — the
/// approximation argument opens a pair, then its second component, then the
/// value of the other graph at the same point — and duplicating it there would
/// mean two copies of the one place where a witness escapes its scope if the
/// side condition is dropped.
pub fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

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

/// Instantiate the body of `∃v. φ` at `t`, as a *formula* operation. `∃` is
/// `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (_, body) = Thm::ax_inst(all_not, t.clone())?.concl().as_imp()?;
    let (body, fls2) = body.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

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
