//! The canonical universe operator `U(x)` — the least Grothendieck universe
//! containing `x`.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::universe::…` all still resolve and no caller has to know which file
//! a theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`predicate`] | the four clauses `C₁`–`C₄`, `is_universe`, and `ax_tarski` at a term |
//! | [`least`] | the membership condition, its existence, and the symbol `U(x)` |
//! | [`closure`] | `𝒫y ∈ u`, and `C₁`, `C₂`, `C₃` transferred to `U(x)` |
//! | [`inaccessibility`] | what `C₄(U(x))` reduces to — and it is Cantor–Schröder–Bernstein |
//! | [`pairing`] | `{a,b} ∈ u`, `{a,b} ∈ U(c)` and `⟨a,b⟩ ∈ U(c)` |
//! | [`union`] | `⋃s ∈ u` and `⋃s ∈ U(c)` — the long one |
//! | [`binary`] | `(a ∪ b) ∈ u` and `(a ∪ b) ∈ U(c)` |
//! | [`replacement`] | `img(A) ∈ u` and `img(A) ∈ U(c)` |
//! | [`replacement_n`] | the same two, for a fibre `b(q⃗,x)` carrying a parameter prefix |
//! | [`apply`] | `coll(f,x) ∈ u` and `app(f,x) ∈ u`, with nothing assumed about `f` |
//!
//! `shared` holds the private readers and combinators several of them need; it
//! exports no theorem and is not re-exported.
//!
//! [`kernel::Thm::ax_tarski`] gives *existence* of a universe around every set, never
//! uniqueness, so it cannot be Skolemised by `kernel::thm::define` directly.
//! What is canonical is the **intersection** of all universes containing `x`:
//!
//! ```text
//! U(x) := { z ∈ u₀ : ∀u. (is_universe(u) ∧ x ∈ u) → z ∈ u }
//! ```
//!
//! for any `u₀` Tarski happens to hand over. Two things have to be said about
//! that description before it defines anything.
//!
//! * **It does not depend on `u₀`.** Under the hypothesis that `u₀` *is* a
//!   universe containing `x`, the side condition `z ∈ u₀` is implied by the
//!   body — instantiate the body at `u₀` — so the separated set satisfies
//!   `∀z. (z ∈ s ↔ ∀u. (is_universe(u) ∧ x ∈ u) → z ∈ u)`, in which `u₀` no
//!   longer occurs. That formula is what [`least_universe_existence`] proves,
//!   and it is why the operator is well defined rather than merely definable.
//! * **`∃!` follows from Extensionality**, via
//!   [`crate::define_by_membership`], which is what [`least_universe`] hands to
//!   the kernel.
//!
//! The separation used is [`crate::separation::separation_nonvacuous`], which
//! needs the separated set to be inhabited and in exchange needs no empty set
//! (none is derivable here; see `crate::separation`). The witness is `x`
//! itself: `x ∈ u` holds for *every* universe containing `x`, trivially, which
//! is [`mem_all_universes_self`] and also the lemma [`mem_least_universe`]
//! wants.
//!
//! # What is proved about `U(x)`
//!
//! | statement | where |
//! |---|---|
//! | `⊢ ∀x ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))` | [`least_universe_existence`] |
//! | `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))` | [`least_universe`] |
//! | `⊢ ∀x ∀u₀. ((x ∈ u₀ ∧ is_universe(u₀)) → ∀z. (z ∈ U(x) ↔ (z ∈ u₀ ∧ …)))` | [`least_universe_independent`] |
//! | `⊢ ∀x. x ∈ U(x)` | [`mem_least_universe`] |
//! | `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → 𝒫y ∈ u)` | [`universe_power_closed`] |
//! | `⊢ ∀x. C₁(U(x))` | [`least_universe_transitive`] |
//! | `⊢ ∀x. C₂(U(x))` | [`least_universe_closed_sub`] |
//! | `⊢ ∀x. C₃(U(x))` | [`least_universe_closed_pow`] |
//! | `⊢ ∀x. (C₂(U(x)) ∧ C₃(U(x)))` | [`least_universe_closure`] |
//! | `⊢ ∀x. U(x) ∈ U(U(x))` | [`tower_step`] |
//! | `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → {a,b} ∈ u)` | [`universe_pairing`] |
//! | `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))` | [`least_universe_pairing`] |
//! | `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))` | [`least_universe_opair`] |
//! | `⊢ ∀u ∀s. ((is_universe(u) ∧ s ∈ u) → ⋃s ∈ u)` | [`universe_union_closed`] |
//! | `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))` | [`least_universe_union`] |
//! | `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → (a ∪ b) ∈ u)` | [`universe_bin_union`] |
//! | `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))` | [`least_universe_bin_union`] |
//! | `⊢ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ ∀x ∈ A. b(x) ∈ u)) → img(A) ∈ u)` | [`universe_replacement`] |
//! | `⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x ∈ A. b(x) ∈ U(c)) → img(A) ∈ U(c))` | [`least_universe_replacement`] |
//! | `⊢ ∀q⃗ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ ∀x ∈ A. b(q⃗,x) ∈ u)) → img(q⃗,A) ∈ u)` | [`universe_replacement_n`] |
//! | `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x ∈ A. b(q⃗,x) ∈ U(c)) → img(q⃗,A) ∈ U(c))` | [`least_universe_replacement_n`] |
//! | `⊢ ∀u ∀f ∀x. ((is_universe(u) ∧ f ∈ u) → app(f,x) ∈ u)` | [`universe_app_closed`] |
//! | `⊢ ∀c ∀f ∀x. (f ∈ U(c) → app(f,x) ∈ U(c))` | [`least_universe_app`] |
//!
//! # What `U(x)` is not closed under
//!
//! Until 2026-07-31 `ax_tarski` had four clauses and no transitivity, and then
//! binary union, `⋃`, Replacement and products were **false** for `U(x)`, not
//! merely unproved — `fs(a,b) ∈ U(c)` from `a, b ∈ U(c)`, the shape Lean's `Π`
//! rule wants, included. The last section of this comment records
//! the countermodels; they are **no longer models**, because the transitivity
//! clause is exactly what they violate, and it is kept there to show what that
//! clause buys. See [`least_universe_transitive`].
//!
//! **Those three are now proved.** `⋃` is [`universe_union_closed`], binary
//! union is [`universe_bin_union`], products are
//! [`crate::funspace::product_in_universe`], and with them the function space
//! ([`crate::funspace::funspace_in_universe_pair`]) and Lean's dependent `Π`
//! rule ([`crate::ext::dprod_in_universe_pair`]). Each reduces, via `C₁` and
//! `C₄`, to exhibiting a surjection onto the target from a member of `u`, and
//! [`crate::cantor::image_in_universe`] turns that into membership; `union`
//! records the surjection the `⋃` case needs, which is the only one of them
//! that is not a one-line composition.
//!
//! The **last** clause of `is_universe` — inaccessibility — is *not* proved
//! for `U(x)`; see [`inaccessibility_reduction`], which derives exactly what
//! remains, and the note there for why the remainder is Cantor–Schröder–
//! Bernstein and not proof engineering. Consequently `is_universe(U(x))` itself
//! is **not** available, and neither is the claim that the tower
//! `x ∈ U(x) ∈ U(U(x)) ∈ ⋯` is a tower of *universes* — only that it is a
//! membership chain whose every link satisfies the three non-inaccessibility
//! clauses. Nothing below needs `is_universe(U(x))`: a closure property that
//! holds in *every* universe transfers through the intersection on its own.
//! The countermodels that made the transitivity clause necessary.
//!
//! **Read the dates. These countermodels refute the FOUR-clause `ax_tarski` that
//! stood until 2026-07-31, not the axiom in the kernel today.** They are kept —
//! not deleted — because they are the whole reason `C₁` exists: without the
//! transitivity clause, `⋃`, binary union, products and function spaces are not
//! merely unproved for `U(c)`, they are **refutable**, and a future reader
//! tempted to "simplify" `ax_tarski` back to four clauses needs to see exactly
//! what that would destroy.
//!
//! Neither model below is a model of the present axiom. `M` has `{ω} ∈ M` and
//! `ω ∉ M`, so it violates `C₁` (`∀y ∈ u. ∀z ∈ y. z ∈ u`) at `y := {ω}`,
//! `z := ω`; `M'` violates it the same way. So they refute nothing about the
//! current theory, and every statement they used to refute is now open at worst
//! — several are proved. What they still establish, permanently, is a *relative*
//! independence: **none of these closure properties is derivable from `C₂`, `C₃`
//! and `C₄` alone.**
//!
//! ## Countermodel A — hereditarily finite over one atom
//!
//! Let `W := ω` and put
//!
//! ```text
//! M₀ := ∅        M_{n+1} := { x : x finite, x ⊆ M_n ∪ {W} }        M := ⋃ₙ Mₙ
//! ```
//!
//! `M` satisfies `C₂`, `C₃` and `C₄` — and **not** `C₁`:
//!
//! * `C₂` — a subset of a member is a finite subset of the same `Mₙ ∪ {W}`.
//! * `C₃` — `𝒫y` for a finite `y` is a finite set of subsets of `y`, all of
//!   which are members; and `W ∉ 𝒫y`, because `W` is infinite and `y` is finite.
//! * `C₄` — `M` is countable, so a subset of it is either finite (hence a
//!   member) or countably infinite (hence equinumerous with `M`).
//! * `C₁` — **fails**: `W ∈ {W} ∈ M` but `W ∉ M`, since every member of `M` is
//!   finite. This is precisely the clause now in the axiom, and it is why `M` is
//!   no longer a model.
//!
//! Under the old axiom `M` was a universe containing `{W}`, so `U({W}) ⊆ M`,
//! and with [`mem_least_universe`]'s `{W} ∈ U({W})` that refuted
//! `∀c ∀a. (a ∈ U(c) → ⋃a ∈ U(c))` — because `⋃{W} = W ∉ U({W})` — and refuted
//! transitivity of `U(x)` outright. **Both statements are now available**:
//! transitivity of `U(x)` is [`least_universe_transitive`], proved by the same
//! transfer through the intersection that [`least_universe_pairing`] uses.
//!
//! ## Countermodel B — two atoms that may not meet
//!
//! Let `W₁ := ω` and `W₂ := ω+1` (both infinite, and `{W₂}` is neither) and put
//!
//! ```text
//! M'_{n+1} := { x : x finite, x ⊆ M'ₙ ∪ {W₁,W₂}, ¬(W₁ ∈ x ∧ {W₂} ∈ x) }
//! ```
//!
//! with `M'₀ := ∅` and `M' := ⋃ₙ M'ₙ`. `C₂`, `C₃` and `C₄` hold exactly as
//! before — the extra constraint is inherited by subsets, and `W₁ ∉ 𝒫y` for
//! finite `y`, so it never obstructs `C₃`. `C₁` fails for the same reason it
//! fails in `M`: `W₁ ∈ {W₁} ∈ M'` and `W₁ ∉ M'`.
//!
//! Under the old axiom, `c := {W₁, W₂} ∈ M'` gave `{W₁}, {W₂} ∈ U(c)` by `C₂`
//! and `𝒫{W₂} = {∅,{W₂}} ∈ U(c)` by [`universe_power_closed`]; with
//! `a := {W₁}` and `b := 𝒫{W₂}` in `U(c) ⊆ M'`,
//!
//! * **binary union was refuted** — `a ∪ b = {W₁, ∅, {W₂}}` holds `W₁` and
//!   `{W₂}` together, so it is not in `M'`;
//! * **the Cartesian product was refuted** — `prod(a,b) ∋ ⟨W₁,{W₂}⟩`, whose
//!   second Kuratowski component is `{W₁,{W₂}}`, again holding both;
//! * **the function space was refuted** — `fs(a,b)` contains the function
//!   `{⟨W₁,{W₂}⟩}`, so it is not in `M'` either.
//!
//! So until 2026-07-31 the statement Lean's `Π` typing rule wants,
//! `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))`, was **false in the
//! standard model** and no proof effort could have reached it. Note what
//! survived even then, and why: the ordered pair `⟨a,b⟩` of two *members* is
//! fine ([`least_universe_opair`]), because `⟨{W₁}, 𝒫{W₂}⟩` never puts `W₁` and
//! `{W₂}` in one set. What broke the products and function spaces is that they
//! reach *inside* their arguments — and "`U(c)` contains the members of its
//! members" is exactly `C₁`.
//!
//! ## What is and is not settled now
//!
//! With `C₁` in the axiom:
//!
//! * **Settled.** `U(x)` is transitive ([`least_universe_transitive`]). Every
//!   member of a member of `U(x)` is a member. The countermodels above cannot be
//!   revived against any statement, because they are not models.
//! * **Settled.** Regularity: a subset of `u` that some member of `u` surjects
//!   onto is a member ([`crate::cantor::image_in_universe`]), and no member of
//!   `u` is equinumerous with `u` ([`crate::cantor::member_not_equinumerous`]).
//!   Both rest on Cantor's theorem in surjective form. Neither actually uses
//!   `C₁` — `C₂` already says a subset of a member is a member — so both were
//!   available before 2026-07-31 and had simply not been proved.
//! * **Settled, as of the `⋃` derivation.** `⋃a ∈ u`, `a ∪ b ∈ u`,
//!   `prod(a,b) ∈ u`, `fs(a,b) ∈ u`, `img(A) ∈ u` and `app(f,x) ∈ u` all hold
//!   for members of a universe `u`, and all transfer to `U(c)`. Each reduces,
//!   via `C₁` (which gives `⋃a ⊆ u` and `a ∪ b ⊆ u`) and regularity, to
//!   exhibiting a member of `u` that surjects onto the target. The `⋃` case is
//!   the one with real content: the surjection is not onto `⋃s` but onto `u`
//!   itself, from the set `S := { img(w) : w ∈ s }` of images of `s`'s members
//!   under the supposed bijection `⋃s ≈ u`, and the contradiction is that
//!   `S ∈ u ⊆ ⋃S` is a membership 2-cycle. See [`union`].
//! * **Inaccessibility for `U(x)`** — [`inaccessibility_reduction`], i.e.
//!   Cantor–Schröder–Bernstein — remains open and is independent of all of the
//!   above. Note that `is_universe(U(x))` is *not* needed for any closure
//!   property proved here: closure properties true in every universe transfer
//!   through the intersection on their own.

pub mod apply;
pub mod binary;
pub mod closure;
pub mod inaccessibility;
pub mod least;
pub mod pairing;
pub mod predicate;
pub mod replacement;
pub mod replacement_n;
pub mod union;
mod shared;

pub use closure::{
    least_universe_closed_pow, least_universe_closed_sub, least_universe_closure,
    least_universe_transfer, least_universe_transitive, universe_clauses, universe_mem_mem,
    universe_power_closed, universe_sub_mem, universe_transitive_clause, UniverseClauses,
};
pub use inaccessibility::{inaccessibility_reduction, tower_step};
pub use least::{
    in_all_universes, least_universe, least_universe_existence, least_universe_existence_at,
    least_universe_independent, least_universe_mem, mem_all_universes_self, mem_least_universe,
};
pub use pairing::{
    least_universe_opair, least_universe_pairing, power_tower_distinct, upair_not_equinumerous,
    universe_pairing, universe_three_members,
};
pub use apply::{least_universe_app, universe_app_closed, universe_coll_closed};
pub use binary::{least_universe_bin_union, universe_bin_union};
pub use replacement::{fibres_in, least_universe_replacement, universe_replacement};
pub use replacement_n::{fibres_in_n, least_universe_replacement_n, universe_replacement_n};
pub use union::{least_universe_union, universe_union_closed};
pub use predicate::{
    closed_pow, closed_sub, inaccessible, is_universe, tarski_at, transitive, universe_body,
};
