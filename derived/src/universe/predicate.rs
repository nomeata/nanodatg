//! `is_universe(u)`: the clauses of Tarski's Axiom A, rebuilt outside the
//! kernel.
//!
//! # Interface
//!
//! Four formula builders, one per clause, and their conjunction:
//!
//! ```text
//! C₁  transitive(u)   :=  ∀y ∈ u. ∀z ∈ y. z ∈ u          [transitive]
//! C₂  closed_sub(u)   :=  ∀y ∈ u. ∀z ⊆ y. z ∈ u          [closed_sub]
//! C₃  closed_pow(u)   :=  ∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p  [closed_pow]
//! C₄  inaccessible(u) :=  ∀y ⊆ u. (y ≈ u ∨ y ∈ u)        [inaccessible]
//!
//! is_universe(u)    :=  C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))            [is_universe]
//! universe_body(x,u) :=  x ∈ u ∧ is_universe(u)          [universe_body]
//! ```
//!
//! and the one theorem, which is the axiom and nothing more:
//!
//! ```text
//! ⊢ ∃u. (x ∈ u ∧ is_universe(u))    [tarski_at], at a caller-chosen term `x`
//! ```
//!
//! Note `C₁`'s `z ∈ y`, not `z ⊆ y`: the subset form is [`closed_sub`], and the
//! two are independent. `C₁` is what makes `u` a Grothendieck universe rather
//! than merely a Tarski one, and it was added to `ax_tarski` on 2026-07-31 —
//! before that, `U(x)` was closed under neither `⋃`, binary union, products nor
//! function spaces, and all four are *refutable* without it. See the
//! countermodels in [`crate::universe`].
//!
//! # Why this is rebuilt rather than read off the axiom
//!
//! Splitting the axiom's body into `x ∈ u` and `is_universe(u)` is what lets the
//! membership clause be varied (it is what `x` is quantified over) while the
//! universe-hood of `u` stays a property of `u` alone. Each clause is rebuilt
//! exactly as `Thm::ax_tarski` builds it, and that is **checked rather than
//! hoped for**: [`tarski_at`] `debug_assert`s [`universe_body`] against the
//! axiom's own body, and `tests/universe.rs` asserts it independently.
//! Alpha-equivalent formulas are syntactically equal here, so rebuilding with
//! fresh bound variables reproduces the kernel's formula on the nose — and that
//! assert is the reason the 2026-07-31 clause change was caught rather than
//! silently producing a predicate no axiom supports.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inst_all;

/// `∀y ∈ u. ∀z ⊆ y. z ∈ u` — closure under subsets of members.
pub fn closed_sub(env: &mut Env, u: &Term) -> Formula {
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let sub = kernel::thm::subset(env, tz.clone(), ty.clone());
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::forall(z, Formula::imp(sub, Formula::mem(tz, u.clone()))),
        ),
    )
}

/// `∀y ∈ u. ∀z ∈ y. z ∈ u` — transitivity.
///
/// Note `z ∈ y`, not `z ⊆ y`: the subset form is [`closed_sub`], and the two are
/// independent. This clause is what makes `u` a Grothendieck universe rather
/// than merely a Tarski one, and it was added to `ax_tarski` on 2026-07-31 —
/// before that, `U(x)` was closed under neither `⋃`, binary union, products nor
/// function spaces, and all four are *refutable* without it. See the
/// countermodels at the end of this file.
pub fn transitive(env: &mut Env, u: &Term) -> Formula {
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), u.clone()),
            Formula::forall(z, Formula::imp(Formula::mem(tz.clone(), ty), Formula::mem(tz, u.clone()))),
        ),
    )
}

/// `∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p` — power sets stay inside.
pub fn closed_pow(env: &mut Env, u: &Term) -> Formula {
    let (y, z, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tz, tp) = (Term::var(y), Term::var(z), Term::var(p));
    let sub = kernel::thm::subset(env, tz.clone(), ty.clone());
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::exists(
                p,
                Formula::and(
                    Formula::mem(tp.clone(), u.clone()),
                    Formula::forall(z, Formula::imp(sub, Formula::mem(tz, tp))),
                ),
            ),
        ),
    )
}

/// `∀y ⊆ u. (y ≈ u ∨ y ∈ u)` — inaccessibility.
pub fn inaccessible(env: &mut Env, u: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    let sub = kernel::thm::subset(env, ty.clone(), u.clone());
    let equi = kernel::thm::equinumerous(env, ty.clone(), u.clone());
    Formula::forall(y, Formula::imp(sub, Formula::or(equi, Formula::mem(ty, u.clone()))))
}

/// `is_universe(u)` — the four non-membership clauses of the axiom, in the
/// axiom's own nesting: `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`.
///
/// The axiom's body is `x ∈ u ∧ is_universe(u)`, which is [`universe_body`];
/// splitting it that way is what lets the membership clause be varied (it is
/// what `x` is quantified over) while the universe-hood of `u` is a property of
/// `u` alone.
///
/// `C₁` is [`transitive`], added 2026-07-31. Keep this nesting identical to
/// `Thm::ax_tarski`'s — [`tarski_at`]'s `debug_assert` is what enforces that, and
/// it is the reason the clause change here was caught rather than silently
/// producing a predicate no axiom supports.
pub fn is_universe(env: &mut Env, u: &Term) -> Formula {
    let c1 = transitive(env, u);
    let c2 = closed_sub(env, u);
    let c3 = closed_pow(env, u);
    let c4 = inaccessible(env, u);
    Formula::and(c1, Formula::and(c2, Formula::and(c3, c4)))
}

/// `x ∈ u ∧ is_universe(u)` — the body of Tarski's axiom, verbatim.
pub fn universe_body(env: &mut Env, x: &Term, u: &Term) -> Formula {
    let univ = is_universe(env, u);
    Formula::and(Formula::mem(x.clone(), u.clone()), univ)
}

/// Tarski's Axiom A at the term `x`: `⊢ ∃u. (x ∈ u ∧ is_universe(u))`, with the
/// existential's bound variable rebuilt as the caller's `u`.
///
/// This is [`Thm::ax_tarski`] instantiated and nothing more; the point of the
/// function is the **check**, which pins that [`is_universe`] really is what
/// the axiom asserts. It is a run-time check and not an assertion because it
/// is the whole of what the function contributes: a drift between the two
/// spellings is caught downstream by `Thm::mp` eventually, but here it is
/// caught where it can be read.
pub fn tarski_at(env: &mut Env, x: &Term, u: FreeVar) -> Option<Thm> {
    let ax = Thm::ax_tarski(env);
    let ex = inst_all(&ax, std::slice::from_ref(x))?;
    let body = Formula::exists(u, universe_body(env, x, &Term::var(u)));
    (*ex.concl() == body).then_some(ex)
}
