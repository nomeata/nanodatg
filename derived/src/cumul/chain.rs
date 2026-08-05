//! **One chain of definitional extensions**, carrying the universe tower and
//! the cumulative hierarchy over the *same* pairing, `∅`, `𝒫`, `ω` and `app`.
//!
//! # Interface
//!
//! [`Chain::new`] builds everything and returns it; the fields are the theorems
//! the rest of [`crate::cumul`] consumes, each at the statement its own module
//! header gives. Nothing here is new mathematics — it is the assembly, and it
//! exists because getting it wrong is silent.
//!
//! # Why an assembly step is needed at all
//!
//! [`crate::tower::Tower::new`] and [`crate::recursion::Rec::new`] each mint
//! their own `∅`, `ω` and `𝒫`, and a theorem about one says nothing about the
//! other: they are different `FnSym`s and no rule relates them. [`crate::recursion::Peano`] is
//! not `Clone`, so the tower's `ω` cannot simply be copied into a `Rec`.
//!
//! The assembly that works, and the only one:
//!
//! 1. build the [`Tower`] — it constructs the [`Space`] over the [`Apply`], the
//!    [`crate::sums::Sums`] over the `Space`'s power set, and `ω` over the same pairing and
//!    the same `∅`;
//! 2. take [`Tower::at`] `(1)` **before** anything is moved out;
//! 3. destructure, keeping `sums`, `space`, `peano` and the `∀c` closure
//!    theorems;
//! 4. rebuild [`crate::recursion::Rec`] from the tower's own `Apply` and
//!    `Peano`;
//! 5. build the [`Step`] with `space.pow` — **not** with a fresh
//!    [`crate::power`] and **not** with `peano.core.pow`, which
//!    [`crate::recursion::OmegaCore`] mints as a third power-set symbol that
//!    looks identical and composes with nothing.
//!
//! Every syntactic comparison downstream fails if any of these is skipped, and
//! fails by returning `None` from a lemma that looks unrelated, which is why
//! this is written down once here rather than repeated per test.

use kernel::{Env, FnSym, Thm};

use crate::bound::Bound;
use crate::funcs::Apply;
use crate::funspace::in_universe::Space;
use crate::recursion::{app_of_graph, Rec};
use crate::tower::{Rung, Tower};
use crate::wtype::Wtype;

// `Chain::over`, the constructor that reuses a caller's ambient signature,
// lives in [`super::ambient`]; the assembly both constructors share is
// [`Chain::assemble`] below.

use super::inside::Inside;
use super::paths::Paths;
use super::stages::Stages;
use super::wmem::WMem;
use super::step::Step;

/// The universe tower and the cumulative hierarchy, over one chain.
pub struct Chain {
    /// The W-type apparatus, and inside it the one [`crate::sums::Sums`]
    /// everything is built over.
    pub wt: Wtype,
    /// The W-type's bound theory: `closed(A,B,U(c))`, W1, W3, and
    /// `f ∈ fs(x,U(c)) → f ∈ U(c)`.
    pub bound: Bound,
    /// The power set, `U(·)` and the two clause transfers.
    pub space: Space,
    /// `ω`, the recursion apparatus and `app_of_graph`.
    pub r: Rec,
    /// Rung 1 of the tower — the `U₁` that `⟦N⟧ ∈ ⟦Type 0⟧` is a membership
    /// in, and the only rung with `ω ∈ Uₙ` spelled at a closed term.
    pub u1: Rung,
    /// The step operator `G(x) = x ∪ 𝒫x`, the recursion at it, and the tower
    /// `T(S) = ⋃ₙ Vₙ`.
    pub st: Stages,

    // ── the `∀c` closure theorems, kept because `Rung` fixes `c` ────────────
    /// `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))`.
    pub pow_all: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))`.
    pub product_all: Thm,
    /// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))`.
    pub union_all: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))`.
    pub bin_union_all: Thm,
    /// `⊢ ∀c ∀y. (y ∈ U(c) → ∀z. (z ∈ y → z ∈ U(c)))` — `C₁`.
    pub transitive_all: Thm,
    /// `⊢ ∀c ∀y. (y ∈ U(c) → ∀z. (z ⊆ y → z ∈ U(c)))` — `C₂`.
    pub sub_all: Thm,

    // ── the cumulative-hierarchy lemmas ──────────────────────────────────────
    /// `⊢ ∀k. (k ∈ ω → bnd(k))` — [`mod@super::bounded`].
    pub bounded: Thm,
    /// `⊢ ∀p. (p ∈ ω → ∀z. (z ∈ Vₚ → z ∈ T))`.
    pub mem_tower: Thm,
    /// `⊢ ∀p. (p ∈ ω → ∀z. (z ⊆ Vₚ → z ∈ V₍succ p₎))`.
    pub sub_in_stage: Thm,
    /// `⊢ ∀p. (p ∈ ω → ∀x ∀y. ((x ∈ Vₚ ∧ y ∈ Vₚ) → ⟨x,y⟩ ∈ V₍succ² p₎))`.
    pub pair_in_stage: Thm,
    /// `⊢ ∀c ∀n. (n ∈ ω → (S ∈ U(c) → Vₙ ∈ U(c)))`.
    pub stages_in_universe: Thm,
    /// `⊢ ∀A ∀B. ((A ⊆ S ∧ ∀a ∈ A. (B(a) ⊆ S ∧ B(a) ∈ ω)) → closed(A,B,T))`.
    pub tower_closed: Thm,
    /// `⊢ ∀A ∀B. ((A ⊆ S ∧ ∀a ∈ A. (B(a) ⊆ S ∧ bnd(B(a)))) → closed(A,B,T))` —
    /// the same at the general fibre condition, which `tower_closed` is an
    /// instance of.
    pub tower_closed_bnd: Thm,
    /// `T ⊆ U(c)` and `T ∈ U(c)` — [`super::Inside`].
    pub inside: Inside,
    /// `W ⊆ T` and `W ∈ U(d)` — [`super::WMem`].
    pub wmem: WMem,
    /// **The path route** — `W ∈ U(d)` at an arbitrary fibre family, and the
    /// tower as its ambient. [`super::Paths`], and what
    /// [`super::DeclUniverse::over_at_general`]'s step (f) actually spends.
    pub paths: Paths,
}

/// The tower's five `∀c` closure theorems, which [`Chain::assemble`] needs and
/// which a caller who already has a [`Tower`] already has.
pub(super) struct Closures {
    pub pow_all: Thm,
    pub product_all: Thm,
    pub union_all: Thm,
    pub bin_union_all: Thm,
    pub transitive_all: Thm,
    pub sub_all: Thm,
}

impl Chain {
    /// Build the lot. See the module header for why the order is what it is.
    pub fn new(env: &mut Env) -> Option<Chain> {
        let t = Tower::new(env)?;
        let u1 = t.at(1)?;
        let ap: Apply = t.sums.ap.clone();
        let cl = Closures {
            pow_all: t.pow.clone(),
            product_all: t.product.clone(),
            union_all: t.union.clone(),
            bin_union_all: t.bin_union.clone(),
            transitive_all: t.transitive.clone(),
            sub_all: t.sub.clone(),
        };
        let Tower { sums, space, peano, .. } = t;

        let app_of_graph = app_of_graph(env, &ap)?;
        let r = Rec { ap, peano, app_of_graph };

        let wt = Wtype::over(env, sums)?;
        let bound = Bound::over(env, &wt, space.lu, space.lu_ax.clone())?;

        Chain::assemble(env, r, u1, space, wt, bound, cl)
    }

    /// Everything downstream of the ambient signature: the step operator, the
    /// stage recursion, and the six lemmas the W-type membership rests on.
    ///
    /// Split out of [`Chain::new`] so that [`Chain::over`](super::ambient) can
    /// reach it with a `Wtype` and a `Bound` the *caller* already built. Nothing
    /// here inspects where its arguments came from; the guards that they came
    /// from one signature are in the two constructors.
    pub(super) fn assemble(
        env: &mut Env,
        r: Rec,
        u1: crate::tower::Rung,
        space: Space,
        wt: Wtype,
        bound: Bound,
        cl: Closures,
    ) -> Option<Chain> {
        let Closures { pow_all, product_all, union_all, bin_union_all, transitive_all, sub_all } =
            cl;

        let step = Step::new(env, &r.ap.sets, space.pow, &space.pow_ax)?;
        let st = Stages::new(env, &r, step)?;

        let bounded = super::bounded::bounded(env, &r, &st)?;
        let mem_tower = super::closure::mem_tower(env, &r, &st)?;
        let sub_in_stage = super::closure::sub_in_stage(env, &r, &st)?;
        let pair_in_stage = super::closure::pair_in_stage(env, &r, &st, &sub_in_stage)?;
        let stages_in_universe = super::universe::stages_in_universe(
            env,
            &r,
            &st,
            space.lu,
            space.pow,
            &pow_all,
            &bin_union_all,
        )?;
        let tower_closed_bnd = super::closed::tower_closed_bnd(
            env,
            &r,
            &wt.sums,
            &st,
            &mem_tower,
            &sub_in_stage,
            &pair_in_stage,
        )?;
        let tower_closed =
            super::closed::tower_closed(env, &r, &wt.sums, &st, &tower_closed_bnd, &bounded)?;

        let inside = Inside::new(
            env,
            &r,
            &wt.sums,
            &st,
            space.lu,
            &stages_in_universe,
            &transitive_all,
            &union_all,
            &sub_all,
            &bound.funspace_mem_lu,
        )?;

        let wmem = WMem::new(
            env,
            &wt,
            &st,
            space.lu,
            &r.omega(),
            &tower_closed,
            &tower_closed_bnd,
            &inside.tower_subset,
            &inside.tower_mem,
            &sub_all,
        )?;

        let paths = Paths::new(
            env,
            &r,
            &st,
            &wt,
            &space,
            &product_all,
            &pow_all,
            &mem_tower,
            &sub_in_stage,
            &pair_in_stage,
        )?;

        Some(Chain {
            wt,
            bound,
            space,
            r,
            u1,
            st,
            pow_all,
            product_all,
            union_all,
            bin_union_all,
            transitive_all,
            sub_all,
            bounded,
            mem_tower,
            sub_in_stage,
            pair_in_stage,
            stages_in_universe,
            tower_closed,
            tower_closed_bnd,
            inside,
            wmem,
            paths,
        })
    }

    /// The least-universe symbol `U(·)`.
    pub fn lu(&self) -> FnSym { self.space.lu }
}
