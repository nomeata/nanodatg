//! **The universe tower** `U₀, U₁, U₂, …` — Carneiro's `Uₙ` as a library
//! construction, with the properties the interpretation assumes of it as its
//! interface and Tarski's Axiom A hidden behind that interface.
//!
//! Nothing here is an axiom and the kernel is untouched. `U₀` is one unordered
//! pair, `Uₙ₊₁` is [`crate::universe`]'s least-universe operator applied to a
//! seed, and every closure property below is either assembled from a lemma that
//! was already proved about `U(·)` or derived here in a dozen lines.
//!
//! # Interface
//!
//! Writing `U₀` for [`Tower::u0`], `Uₙ` for [`Tower::level`], `[φ]` for the
//! conditional singleton, `•` for `∅` and `fs(a,b)` for the function space, the
//! exports are — and a caller needs nothing else from this module:
//!
//! ```text
//! ── the terms ────────────────────────────────────────────────────────────
//! U₀ := {0, 1}                                             [Tower::u0]
//! U₁ := U(ω)                                               [Tower::level]
//! U₍ₙ₊₁₎ := U(Uₙ)                     for n ≥ 1            [Tower::level]
//!
//! ── level 0, which is Prop and is NOT a universe ─────────────────────────
//! ⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))                         [Tower::u0_members]
//! ⊢ [φ] ∈ U₀                for any formula φ              [Tower::cond_in_u0]
//! ⊢ 0 ∈ U₀        ⊢ 1 ∈ U₀        ⊢ ¬(0 = 1)               [false_in_u0, true_in_u0, u0_two_valued]
//! ⊢ ∀p ∀x. ((p ∈ U₀ ∧ x ∈ p) → x = •)                      [Tower::u0_subsingleton]
//!
//! ── the tower, at every level n ≥ 1 (`Level`, from `Tower::at`) ──────────
//! ⊢ U₍ₙ₋₁₎ ∈ Uₙ                                            [Level::mem_below]
//! ⊢ ω ∈ Uₙ                                                 [Level::omega_mem]
//! ⊢ U₀ ∈ Uₙ                    ⊢ ∅ ∈ Uₙ                    [Level::u0_mem, Level::empty_mem]
//! ⊢ ∀y. (y ∈ Uₙ → ∀z. (z ∈ y → z ∈ Uₙ))                    [Level::transitive]
//! ⊢ ∀y. (y ∈ Uₙ → ∀z. (z ⊆ y → z ∈ Uₙ))                    [Level::sub]
//! ⊢ ∀y. (y ∈ Uₙ → 𝒫y ∈ Uₙ)                                 [Level::pow]
//! ⊢ ∀s. (s ∈ Uₙ → ⋃s ∈ Uₙ)                                 [Level::union]
//! ⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → {a,b} ∈ Uₙ)                [Level::pairing]
//! ⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → ⟨a,b⟩ ∈ Uₙ)                [Level::opair]
//! ⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → (a ∪ b) ∈ Uₙ)              [Level::bin_union]
//! ⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → prod(a,b) ∈ Uₙ)            [Level::product]
//! ⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → fs(a,b) ∈ Uₙ)              [Level::funspace]
//! ⊢ ∀f ∀x. (f ∈ Uₙ → app(f,x) ∈ Uₙ)                        [Level::app]
//!
//! ── Replacement and Π, per fibre family b (`Family`, from `Tower::family`) ─
//! ⊢ ∀A. ((A ∈ Uₙ ∧ ∀x ∈ A. b(x) ∈ Uₙ) → img(A) ∈ Uₙ)       [Family::at]
//! ⊢ ∀A. ((A ∈ Uₙ ∧ ∀x ∈ A. b(x) ∈ Uₙ) → dprod(A) ∈ Uₙ)     [Family::at]
//!
//! ── cumulativity, for every m ≤ n up to a chosen height (`Cumul`) ────────
//! ⊢ Uₙ ⊆ U₍ₙ₊₁₎                                            [Cumul::step]
//! ⊢ Uₘ ⊆ Uₙ                                                [Cumul::lift]
//! ⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)                                         [Cumul::strict]
//!
//! ── non-vacuity ─────────────────────────────────────────────────────────
//! ⊢ ¬(U₀ = U₁)                                             [Tower::u0_ne_u1]
//! ⊢ fs(U₀,U₀) ∈ U₁                                         [Tower::fs_u0_in_u1]
//! ```
//!
//! Everything above is at closed terms except where a set is quantified, and
//! `Tower::at(n)` returns `None` at `n = 0` — see below for why that is not an
//! omission.
//!
//! # `U₀` is not a universe, and the tower does not start by iterating on it
//!
//! Two facts about level 0, both of which the shape of this module is dictated
//! by.
//!
//! **`U₀` is `Prop`, not a universe.** The thesis puts `P := U₀` (§2.2) and
//! `U₀ = {∅, {•}}` (§6.2); it is a two-element set of *truth values*, and it is
//! not closed under power set — `1 = {0}` is a member and `𝒫1 = {0,1}` is `U₀`
//! itself, which is not one of its own two members. So `U₀` gets the membership
//! condition, the subsingleton property and
//! `[φ] ∈ U₀`, and none of the closure clauses; `Tower::at(0)` is `None` rather
//! than a `Level` whose fields would be unprovable.
//!
//! **`U₁` is `U(ω)`, not `U(U₀)`.** This is the one place the construction
//! departs from the shape one would write down first, and the reason is a
//! countermodel rather than a proof-engineering difficulty:
//!
//! > `V_ω`, the hereditarily finite sets, satisfies **every** clause of
//! > [`crate::universe::is_universe`]. It is transitive; a subset of a
//! > hereditarily finite set is hereditarily finite; `𝒫y` is hereditarily
//! > finite for hereditarily finite `y`; and a subset of `V_ω` is either finite
//! > — hence a member — or countably infinite, hence equinumerous with the
//! > countable `V_ω`, which is `C₄`'s other disjunct.
//!
//! `U₀ = {0,1}` is hereditarily finite, so `V_ω` is a universe containing it,
//! so `U(U₀) ⊆ V_ω` — and **every member of `V_ω` is finite**. Hence
//! `ω ∉ U(U₀)`, and more to the point no infinite set whatsoever is a member of
//! `U(U₀)`. A tower seeded at `U₀` would make `⟦Sort 1⟧` a set with no infinite
//! members, and `⟦N⟧` is infinite; `⊢ ω ∈ U₁` is therefore not an optional
//! extra but the statement that rules this out. It is *refutable* for
//! `U₁ := U(U₀)`, exactly as binary union and function spaces were refutable
//! for `U(c)` before the transitivity clause was added to `ax_tarski` — see the
//! countermodels at the end of [`crate::universe`], of which this is one more.
//!
//! Seeding at `ω` fixes it and costs nothing: `ω ∈ U(ω)` is
//! [`crate::universe::mem_least_universe`], and `ω ∈ Uₙ` for `n > 1` follows by
//! transitivity from `ω ∈ U₍ₙ₋₁₎ ∈ Uₙ`. It is also **closer** to the thesis,
//! not further: §6.2 does not define `U_{n+1}` from `Uₙ` at all. It fixes a
//! sequence `(κₙ)` of strong limit cardinals independently and sets
//! `U_{n+1} = V_{κₙ}`, with `U₀ = {∅,{•}}` as a separate clause. Reading `κₙ`
//! as the `n`-th inaccessible, `U(ω) = V_{κ₀}` and `U(V_{κₙ}) = V_{κₙ₊₁}`, so
//! the iteration below *is* that sequence — and the fact that `U₀` does not
//! appear in it is a feature of the thesis, not an accident of this encoding.
//!
//! # `is_universe(Uₙ)` is not claimed, and is not needed
//!
//! [`crate::universe::inaccessibility_reduction`] reduces `C₄(U(x))` to
//! Cantor–Schröder–Bernstein and gets no further, so `is_universe(U(x))` is
//! unavailable. It is also unnecessary: every closure property above holds in
//! *every* universe, and therefore transfers through the intersection `U(x)` on
//! its own. That is why the interface exposes the closure clauses and not the
//! predicate. Do not try to add `is_universe(Uₙ)`; nothing here wants it.
//!
//! # Levels are syntax, so the iteration is meta-level
//!
//! Lean's levels are `0`, `succ`, `max`, `imax` and parameters. A closed level
//! evaluates to a numeral at interpretation time, so [`Tower::level`] takes a
//! `usize` and iterates in Rust. **No set-theoretic recursion happens and no
//! recursion theorem is needed** — which matters, because
//! [`crate::recursion`] does not have one. Level *variables* stay opaque, as
//! they do in the thesis: §6.1 removes level expressions from terms before the
//! interpretation runs and gives no universe-polymorphic interpretation either.
//!
//! # What is derived here versus assembled
//!
//! Four derivations, all small, in [`levels`]:
//!
//! | statement | why it is not a call |
//! |---|---|
//! | `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))` | [`crate::funspace::pow_closed`] is stated at a *fixed* `u`; this is it at the variable `U(c)`, plus one generalisation |
//! | `⊢ ∀c. ∅ ∈ U(c)` | [`crate::enums::empty_in_least_universe`] is the same statement but takes a `Wtype` and a `Bound`, which the tower needs for nothing else |
//! | `⊢ ∀c. U₀ ∈ U(c)` | new: `1 = {0,0}`, so two applications of [`crate::universe::least_universe_pairing`] over `∅` |
//! | `⊢ ¬(U₀ = U₁)` | new: `U₀ ∈ U₁` and Regularity's `¬(x ∈ x)` |
//!
//! Everything else is *named*, not reproved. `Uₙ ∈ U₍ₙ₊₁₎` is
//! [`crate::universe::mem_least_universe`], transitivity is
//! [`crate::universe::least_universe_transitive`], and the closure clauses are
//! [`crate::universe`]'s `least_universe_{pairing,opair,union,bin_union,
//! replacement,app}`, [`crate::funspace`]'s `product_in_universe` and
//! `funspace_in_universe_pair`, and [`crate::ext::dprod_in_universe_pair`],
//! each instantiated at the level's seed. Level 0 is
//! [`crate::anchor::falsity`] — `truth_values`, `cond_in_prop`,
//! `prop_subsingleton`, `prop_two_valued` — re-exposed rather than rebuilt.
//!
//! # What this tower does *not* give, named precisely
//!
//! * **`⟦N⟧ ∈ U₁`.** `⟦N⟧` is [`crate::wnat`]'s `W(A, B, U(A))` with
//!   `A = 1 + 1`, and its bound is `U(A)`, not a level of this tower. Getting
//!   `⟦N⟧ ∈ U₁` needs a W-type-in-a-universe argument: `W(A,B,u) ⊆ u` is
//!   immediate, but `W(A,B,u) ∈ u` is not, and the rank argument the thesis
//!   uses (§6.3, `cf(κ) > sup_{a∈A}|B(a)|`) is a cofinality computation, not a
//!   transfer through the intersection. `⊢ ω ∈ Uₙ` is the ingredient that
//!   argument needs from *here*, and it is supplied; the argument itself is a
//!   separate job.
//! * **`is_universe(Uₙ)`**, as above.
//! * **`⟦Sort u⟧` for a level variable `u`.** Out of scope by construction, and
//!   nothing here would have to change: an opaque symbol plus the [`Level`]
//!   fields as hypotheses is exactly the shape a polymorphic caller would want.
//!
//! # Layout
//!
//! This module is a **hub**: the construction lives in [`levels`] with its own
//! interface header, and everything is re-exported here.
//!
//! | file | what it exports |
//! |---|---|
//! | [`levels`] | [`Tower`], [`Level`], [`Family`] — the terms, the step, the closure clauses, and the non-vacuity checks |
//! | [`cumulative`] | [`Cumul`] — `Uₘ ⊆ Uₙ` for every level pair, its strictness, and the lift rules `Sort max(u,v)` and `ulift` need |

pub mod cumulative;
pub mod levels;

pub use cumulative::Cumul;
pub use levels::{Family, Level, Tower};
