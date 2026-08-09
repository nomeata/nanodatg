//! **B0 prototype (ENV-UNIFY.md §3.5, task #125)** — dump shapes for the
//! cross-engine skeleton-key comparison.
//!
//! ENV-UNIFY.md's one prototype-gated unknown is whether mini's and the
//! checker's dispatches produce the same skeleton key for the same shape,
//! over one shared kernel `Env`. This module is the *data shape* of the
//! measurement; `mini/tests/b0_env_unify.rs` (feature `b0`) is the
//! measurement itself. Nothing here is consumed by any derivation, and the
//! module is expected to be deleted or replaced when track B5 is scoped.

use kernel::{FnSym, Term};

/// One engine's skeleton-site tables: for each distinct skeleton, the key
/// `Term` and the symbols the engine minted for it, in a fixed role order
/// (documented at the two `b0_sites` producers).
pub struct SiteDump {
    /// λ body shapes — mini's `lams` / checker's `lam_infos`.
    pub lams: Vec<(Term, Vec<FnSym>)>,
    /// Dependent-`Π` fibre shapes — mini's `fibres` / checker's `pi_infos`.
    pub fibres: Vec<(Term, Vec<FnSym>)>,
    /// `Prop`-valued `∀` shapes — mini's `conds` / checker's `prop_infos`.
    pub conds: Vec<(Term, Vec<FnSym>)>,
}
