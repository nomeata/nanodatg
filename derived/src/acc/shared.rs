//! One internal helper shared by the constructions in [`crate::acc`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! [`hyp_inst_mp`] is the single most repeated move in the module —
//! instantiating a universal that sits under an ambient hypothesis — and doing
//! it by hand each time is where the shapes drift. It is needed in this form
//! because the kernel is Hilbert style and there is no deduction theorem, so
//! everything runs as `H → …`.
//!
//! It is a copy of `crate::wtype`'s private helper of the same name rather than
//! a shared export, because that one is `pub(super)` inside `wtype` and
//! promoting it would enlarge `crate::wtype`'s interface for no gain here.

use kernel::{Term, Thm};
use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{hyp_mp, syl};

/// From `⊢ H → ∀x. (P → Q)` and `⊢ H → P[t/x]` infer `⊢ H → Q[t/x]`.
pub(super) fn hyp_inst_mp(h_all: &Thm, t: &Term, h_arg: &Thm) -> DResult<Thm> {
    let (_, all) = h_all.concl().imp_parts()?;
    let at = prim::ax_inst(all, t.clone())?;
    hyp_mp(&syl(h_all, &at)?, h_arg)
}
