//! Equational glue under a fixed hypothesis.
//!
//! # Interface
//!
//! ```text
//! from ⊢ H → a = b                    infer ⊢ H → b = a          [hyp_eq_symm]
//! from ⊢ H → a = b and ⊢ H → b = c    infer ⊢ H → a = c          [hyp_eq_trans]
//! ⊢ (∀x⃗. φ) → φ[t⃗/x⃗]                                             [inst_chain]
//! ```
//!
//! The approximation argument is a chain of equations assembled under an
//! ever-present hypothesis, and without a deduction theorem every link costs a
//! Leibniz instance and every instantiation an `ax_inst` chain. These three turn
//! that into one call each. No `Thm` is built here that is not built by the
//! kernel's own rules.

use kernel::{Env, Formula, Term, Thm};

use crate::{a1i, eq_symm_imp, hyp_mp, imp_refl, syl};

/// From `⊢ H → a = b` infer `⊢ H → b = a`.
pub fn hyp_eq_symm(env: &mut Env, h_ab: &Thm) -> Option<Thm> {
    let (_, ab) = h_ab.concl().as_imp()?;
    let (a, b) = ab.as_eq()?;
    syl(h_ab, &eq_symm_imp(env, a, b))
}

/// From `⊢ H → a = b` and `⊢ H → b = c` infer `⊢ H → a = c`.
pub fn hyp_eq_trans(env: &mut Env, h_ab: &Thm, h_bc: &Thm) -> Option<Thm> {
    let (h, ab) = h_ab.concl().as_imp()?;
    let (a, b) = ab.as_eq()?;
    let (h2, bc) = h_bc.concl().as_imp()?;
    let (b2, cc) = bc.as_eq()?;
    if h != h2 || b != b2 {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(b, cc, w, Formula::eq(a, Term::var(w)));
    hyp_mp(&hyp_mp(&a1i(&leib, h), h_bc)?, h_ab)
}

/// `⊢ φ → ψ`, where `ψ` is `φ` with its leading `∀`s instantiated at `ts`.
///
/// The implication form of [`crate::inst_all`], for use when the universally
/// quantified formula is only available under a hypothesis.
pub fn inst_chain(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = imp_refl(phi.clone());
    for t in ts {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}
