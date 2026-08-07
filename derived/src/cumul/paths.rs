//! **The path-code apparatus, over this chain's signature** — the eight
//! [`crate::wpath`] theorems and the one bridge that makes them usable at the
//! `ω`-tower, derived once and carried by [`super::Chain`].
//!
//! # Interface
//!
//! ```text
//! Paths::new(env, r, st, wt, space, product_all, pow_all,
//!            mem_tower, sub_in_stage, pair_in_stage) -> Option<Paths>
//! ```
//!
//! and the fields, each at the statement its own module header gives. The two a
//! consumer reads are
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀Q ∀d. ( ((closed(A,B,u) ∧ amb(A,B,Q))
//!                      ∧ ((W(A,B,u) ⊆ U(d) ∧ Q ∈ U(d)) ∧ A ∈ U(d)))
//!                        → W(A,B,u) ∈ U(d) )              [Paths::w_in_universe]
//! ⊢ ∀A ∀B. ((∀a. (a ∈ A → B(a) ⊆ S)) → amb(A,B,T))        [Paths::tower_amb]
//! ```
//!
//! **Neither mentions the fibres.** That is the whole content of this file's
//! existence: [`super::WMem::w_in_universe_bnd`], the theorem it displaces at
//! [`super::DeclUniverse::over_at_general`]'s step (f), asks for
//! [`super::bnd`] at every fibre value, and `bnd` is *refutable* at an infinite
//! one.
//!
//! # Why an assembly step, and why here
//!
//! For [`super::chain`]'s reason exactly. [`crate::wpath::paths_symbol`] mints a
//! Separation over **a** [`Wtype`], and every theorem downstream of it is about
//! that `W` and that `paths`. A second `paths` over the same `W` is a second
//! symbol that no equation relates to the first, and
//! [`crate::wpath::w_in_universe_paths`] built over it would be a true theorem
//! about a relation this chain's `tower_amb` says nothing about. So the symbol is
//! minted once, beside the tower, and travels with it.
//!
//! `Chain::over` gives the same guarantee for a caller with its own signature:
//! the `Wtype` it is handed is the caller's, so `paths` is over the caller's `W`.
//!
//! # The one input that is not the chain's own
//!
//! [`crate::universe::least_universe_is_universe`] — `⊢ ∀x. is_universe(U(x))` —
//! needs a [`crate::csb::Csb`], and the chain has none. It is built here over the
//! chain's **own** [`Apply`](crate::funcs::Apply), which is what
//! [`crate::csb::Csb::with_apply`] is for; the alternative, `Csb::new`, mints a
//! second pairing. The `Csb` is not kept: it appears nowhere in the conclusion
//! (`is_universe` is a formula over `∈`, `⊆` and `≈` and mentions no symbol at
//! all), so nothing downstream can need it.
//!
//! # Cost
//!
//! One Separation for `paths`, one [`crate::wtype::w_rect`] inside
//! [`crate::wpath::paths_injective`], and one product symbol inside the `Csb`.
//! Measured at 0.1 s in a debug build for the whole chain — this is not where the
//! time goes, and it is derived eagerly rather than memoised because
//! [`super::DeclUniverse::over_at_general`] takes a `&IndChain` and could not
//! fill a memo if it wanted to.

use kernel::{Env, FnSym, Thm};

use crate::funspace::in_universe::Space;
use crate::recursion::Rec;
use crate::wtype::Wtype;

use super::stages::Stages;

/// The path relation over one chain's `W`, and the two theorems a consumer
/// reads.
pub struct Paths {
    /// The relation symbol `paths(A,B,u,Q)`, of arity 4.
    pub sym: FnSym,
    /// `⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths ↔ (p ∈ Bnd ∧ ∀C. …))` — the Separation.
    pub ax: Thm,
    /// `⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths → p ∈ prod(W, prod(Q,A)))`.
    pub subset: Thm,
    /// **P2** — `paths` is the least closed subset of the ambient.
    pub induction: Thm,
    /// **P1** — the two rules hold of `paths`.
    pub intro: Thm,
    /// **P3** — every member of `paths` arises from a rule.
    pub inversion: Thm,
    /// **P4** — the code determines the tree.
    pub injective: Thm,
    /// `⊢ ∀x. is_universe(U(x))`, kept because
    /// [`crate::cantor::image_in_universe`] wants it and a second derivation
    /// would want a second [`crate::csb::Csb`].
    pub is_universe: Thm,
    /// **`⊢ ∀A ∀B ∀u ∀Q ∀d. (… → W(A,B,u) ∈ U(d))`** — the theorem, at an
    /// arbitrary fibre family. See the module header.
    pub w_in_universe: Thm,
    /// `⊢ ∀A ∀B. ((∀a. (a ∈ A → B(a) ⊆ S)) → amb(A,B,T))` — the tower is a
    /// legal path ambient, from the half of `Fin⁺` that survives.
    pub tower_amb: Thm,
    /// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) → is_sup(z))` — W3, derived here because
    /// [`crate::wpath::paths_injective`] needs it and it mints a `w_rect`.
    pub w_inversion: Thm,
}

impl Paths {
    /// Mint `paths` over `wt`'s `W` and derive the lot.
    ///
    /// `space`, `product_all` and `pow_all` must be the tower's — `U(·)` and its
    /// product and power-set closures at `∀c`; `mem_tower`, `sub_in_stage` and
    /// `pair_in_stage` [`super::closure`]'s, over `st`. Every one of them is
    /// required hypothesis-free by the lemmas below, which check it.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        env: &mut Env,
        r: &Rec,
        st: &Stages,
        wt: &Wtype,
        space: &Space,
        product_all: &Thm,
        pow_all: &Thm,
        mem_tower: &Thm,
        sub_in_stage: &Thm,
        pair_in_stage: &Thm,
    ) -> Option<Paths> {
        let (sym, ax) = crate::wpath::paths_symbol(env, wt)?;
        let subset = crate::wpath::paths_subset(env, wt, sym, &ax)?;
        let induction = crate::wpath::paths_induction(env, wt, sym, &ax)?;
        let intro = crate::wpath::paths_intro(env, wt, sym, &ax, &induction, &subset)?;
        let inversion = crate::wpath::paths_inversion(env, wt, sym, &induction, &subset, &intro)?;
        let root_label = crate::wpath::root_label(env, wt, sym, &inversion)?;
        let step_premise = crate::wpath::step_premise(env, wt, sym, &inversion)?;
        let w_inversion = crate::wtype::w_inversion(env, wt)?;
        let injective = crate::wpath::paths_injective(
            env,
            wt,
            sym,
            &subset,
            &intro,
            &w_inversion,
            &root_label,
            &step_premise,
        )?;

        let csb = crate::csb::Csb::with_apply(env, &wt.sums.ap)?;
        let is_universe = crate::universe::least_universe_is_universe(
            env,
            &csb,
            space.lu,
            &space.lu_ax,
            space.pow,
            &space.pow_ax,
        ).ok()?;

        let w_in_universe = crate::wpath::w_in_universe_paths(
            env,
            wt,
            sym,
            &subset,
            &injective,
            space.lu,
            &is_universe,
            product_all,
            pow_all,
        )?;

        let tower_amb =
            super::wpaths::tower_amb_over(env, r, st, wt, mem_tower, sub_in_stage, pair_in_stage)?;

        Some(Paths {
            sym,
            ax,
            subset,
            induction,
            intro,
            inversion,
            injective,
            is_universe,
            w_in_universe,
            tower_amb,
            w_inversion,
        })
    }
}
