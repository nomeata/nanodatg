//! The whole chain, assembled once.
//!
//! # Interface
//!
//! [`Bound::new`] builds every symbol and derives every theorem from the axioms
//! up; [`Bound::over`] does the same over a caller-supplied [`crate::wtype::Wtype`],
//! so that a client already holding one gets a bound whose terms compose with
//! everything else built over it. The fields are the theorems of steps 1–7, so a
//! caller reads them off the struct and never calls the functions in the sibling
//! files directly.
//!
//! # Why it is a struct and not a set of free functions
//!
//! Every theorem in [`crate::bound`] is about *the* universe symbol, *the*
//! function space and *the* pairing of one definitional extension. Building any
//! of them twice would mint a second `upair`, and then `⟨a,b⟩` would name two
//! different terms and none of the theorems would compose. Threading one
//! `Bound` is what makes the chain a chain.

use kernel::{Env, FnSym, Term, Thm};
use crate::wtype::Wtype;

use super::opair::universe_opair;
use super::subset::{funspace_pairs, funspace_subset_universe};
use super::member::funspace_mem_universe;
use super::closure::universe_closed;
use super::least::least_universe_closed;
use super::rules::{sup_mem_at, w_inversion_at};
use super::funspace_universe::{funspace_subset_least_universe, least_universe_funspace_mem};

/// Every theorem this module proves, over one [`Wtype`] and one universe
/// operator.
///
/// Assembled in a struct because each step consumes the previous one and
/// because `U(x)` is a *definitional extension*: building it twice would mint
/// two symbols and none of the theorems would compose. A caller that already
/// has a `U(x)` — from [`crate::funspace::Space`], say — should use
/// [`Bound::over`] and hand it in.
#[derive(Clone)]
pub struct Bound {
    /// `U(x)`, the least universe containing `x`.
    pub lu: FnSym,
    /// **The `W` these theorems are about.** [`Bound::sup_mem`] and
    /// [`Bound::w_inversion`] are W1 and W3 at one particular W-type symbol,
    /// and `lu` alone does not say which: two [`Wtype`]s over the same
    /// [`Sums`](crate::sums::Sums) and the same `U(·)` give two `Bound`s that
    /// are indistinguishable by every other field. A client holding a `Bound`
    /// and a `Wtype` compares this against `wt.w` before treating them as one
    /// signature — see [`crate::cumul::Chain::over`].
    pub w: FnSym,
    /// The pairing the same theorems are over, recorded for the same reason:
    /// `⟨a,f⟩` is a different term under a different `upair`.
    pub up: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
    pub lu_ax: Thm,
    /// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → ⟨a,b⟩ ∈ u)`.
    pub universe_opair: Thm,
    /// `⊢ ∀x ∀u ∀f. (f ∈ fs(x,u) → ∀p. (p ∈ f → ∃q. (q ∈ x ∧ ∃r. (r ∈ u ∧ p = ⟨q,r⟩))))`.
    pub funspace_pairs: Thm,
    /// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ⊆ u)`.
    pub funspace_subset: Thm,
    /// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ∈ u)`.
    pub funspace_mem: Thm,
    /// `⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a ∈ A. B(a) ∈ u)) → closed(A,B,u))`.
    pub universe_closed: Thm,
    /// `⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a ∈ A. B(a) ∈ U(c)) → closed(A,B,U(c)))`.
    pub least_universe_closed: Thm,
    /// **W1, unconditional** — see [`sup_mem_at`].
    pub sup_mem: Thm,
    /// **W3, unconditional** — see [`w_inversion_at`].
    pub w_inversion: Thm,
    /// `⊢ ∀c ∀x ∀f. ((x ∈ U(c) ∧ f ∈ fs(x, U(c))) → f ∈ U(c))`.
    pub funspace_mem_lu: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))`.
    pub funspace_subset_lu: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))` — see
    /// [`crate::universe::least_universe_pairing`]. Kept here because the
    /// derivation it needs, [`crate::universe::universe_pairing`], is one this
    /// struct already runs, and a caller wanting `{a,b} ∈ U(c)` (any singleton,
    /// `1` in particular) should not have to run it a second time.
    pub least_pairing: Thm,
}

impl Bound {
    /// Build everything over a **fresh** `U(x)`.
    pub fn new(env: &mut Env, wt: &Wtype) -> Option<Bound> {
        let (lu, lu_ax) = crate::universe::least_universe(env)?;
        Bound::over(env, wt, lu, lu_ax)
    }

    /// Build everything over a caller-supplied `U(x)`, so that the theorems
    /// compose with whatever else was proved about that symbol.
    pub fn over(env: &mut Env, wt: &Wtype, lu: FnSym, lu_ax: Thm) -> Option<Bound> {
        let s = &wt.sums;
        let pairing = crate::universe::universe_pairing(
            env,
            s.ap.sets.up,
            &s.ap.sets.up_ax,
            s.ap.empty,
            &s.ap.empty_ax,
            s.pow,
            &s.pow_ax,
        )?;
        let mem_mem = crate::universe::universe_mem_mem(env)?;
        let universe_opair = universe_opair(env, s.ap.sets.up, &pairing)?;
        let funspace_pairs = funspace_pairs(env, s)?;
        let funspace_subset =
            funspace_subset_universe(env, s, &funspace_pairs, &mem_mem, &universe_opair)?;
        let funspace_mem = funspace_mem_universe(
            env,
            s,
            &s.ap.empty_ax,
            &funspace_pairs,
            &funspace_subset,
        )?;
        let universe_closed =
            universe_closed(env, s, &mem_mem, &universe_opair, &funspace_mem)?;
        let least_universe_closed =
            least_universe_closed(env, s, lu, &lu_ax, &wt.fs_mono, &universe_closed)?;

        let sup_mem = sup_mem_at(env, wt, lu, &least_universe_closed)?;
        let inversion = wt.inversion(env)?;
        let w_inversion = w_inversion_at(env, wt, lu, &least_universe_closed, &inversion)?;

        let funspace_mem_lu =
            least_universe_funspace_mem(env, s, lu, &lu_ax, &wt.fs_mono, &funspace_mem)?;
        let least_pairing =
            crate::universe::least_universe_pairing(env, lu, &lu_ax, s.ap.sets.up, &pairing)?;
        let c1 = crate::universe::least_universe_transitive(env, lu, &lu_ax)?;
        let funspace_subset_lu =
            funspace_subset_least_universe(env, s, lu, &c1, &wt.fs_mono, &funspace_mem_lu)?;

        Some(Bound {
            lu,
            w: wt.w,
            up: wt.sums.ap.sets.up,
            lu_ax,
            universe_opair,
            funspace_pairs,
            funspace_subset,
            funspace_mem,
            universe_closed,
            least_universe_closed,
            sup_mem,
            w_inversion,
            funspace_mem_lu,
            funspace_subset_lu,
            least_pairing,
        })
    }

    /// The term `U(x)`.
    pub fn universe_of(&self, x: Term) -> Term { Term::apply(self.lu, vec![x]) }
}
