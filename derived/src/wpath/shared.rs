//! The three internal helpers shared by the constructions in [`crate::wpath`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** The
//! kernel is Hilbert style and has no deduction theorem, so every derivation in
//! this module runs as `H → …`; these are the three moves that shape makes
//! repetitive, and doing them by hand each time is where the formulas drift.

use kernel::{Formula, FreeVar, Term, Thm};

use crate::{hyp_mp, syl};

/// From `⊢ H → ∀x. φ` infer `⊢ H → φ[t/x]`.
pub(super) fn hyp_inst(h_all: &Thm, t: &Term) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    syl(h_all, &Thm::ax_inst(all, t.clone())?)
}

/// From `⊢ H → ∀x. (P → Q)` and `⊢ H → P[t/x]` infer `⊢ H → Q[t/x]`.
pub(super) fn hyp_inst_mp(h_all: &Thm, t: &Term, h_arg: &Thm) -> Option<Thm> {
    hyp_mp(&hyp_inst(h_all, t)?, h_arg)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, given that `v` is not free in `H`.
///
/// The `∀`-distribution axiom, with the generalisation already applied — the
/// move that closes every `∀`-quantified conclusion in this module.
pub(super) fn gen_under(v: FreeVar, h: &Formula, body: &Formula, thm: &Thm) -> Option<Thm> {
    Thm::mp(&Thm::ax_dist(v, h.clone(), body.clone())?, &Thm::gen(v, thm))
}
