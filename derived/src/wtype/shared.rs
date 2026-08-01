//! Internal helpers shared by the constructions in [`crate::wtype`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`apply_closed`] is the one move every use of the bound hypothesis makes —
//! `closed(A,B,S)` is a doubly-quantified implication, and cashing it at a
//! particular `a` and `f` under an ambient hypothesis takes two instantiations
//! and two modus ponens steps; [`hyp_inst_mp`] is that step in the `H → …`
//! form, which is needed because there is no deduction theorem.

use kernel::{Formula, Term, Thm};
use crate::{hyp_mp, syl};

/// From `⊢ H → closed(A,B,S)`, `⊢ H → a ∈ A` and `⊢ H → f ∈ fs(B(a), S)`,
/// infer `⊢ H → ⟨a,f⟩ ∈ S`.
///
/// The one move `closed` exists for, and it happens three times below, so it is
/// factored out. `cl` must be the very formula the first premise concludes,
/// which is checked by the instantiation failing otherwise.
pub(super) fn apply_closed(
    h_cl: &Thm,
    h_mem_a: &Thm,
    h_mem_f: &Thm,
    cl: &Formula,
    a: &Term,
    f: &Term,
) -> Option<Thm> {
    let at_a = Thm::ax_inst(cl.clone(), a.clone())?;
    let h_inner = hyp_mp(&syl(h_cl, &at_a)?, h_mem_a)?;
    hyp_inst_mp(&h_inner, f, h_mem_f)
}

/// From `⊢ H → ∀x. (P → Q)` and `⊢ H → P[t/x]` infer `⊢ H → Q[t/x]`.
///
/// Instantiating a universal that sits under a hypothesis is the single most
/// repeated move below — `closed`, `sup_mem` and the induction step all have
/// that shape — and doing it by hand each time is where the shapes drift.
pub(super) fn hyp_inst_mp(h_all: &Thm, t: &Term, h_arg: &Thm) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    let at = Thm::ax_inst(all, t.clone())?;
    hyp_mp(&syl(h_all, &at)?, h_arg)
}
