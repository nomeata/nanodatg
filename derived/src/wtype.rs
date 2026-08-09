//! The **W-type**, as the intersection of all closed subsets of a bound.
//!
//! Following Carneiro's *The Type Theory of Lean* §6.2.1: given a set `A` and a
//! family `B` indexed by `A`, `W_{x∈A} B(x)` is "the intersection of all sets
//! `W` such that `⟨a,f⟩ ∈ W` whenever `a ∈ A` and `f : B(a) → W`". Writing
//! `B(a)` for `app(B,a)` and `⟨a,f⟩` for the Kuratowski pair, that is
//!
//! ```text
//! closed(A,B,S)  :=  ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), S) → ⟨a,f⟩ ∈ S))
//! W(A,B,u)       :=  { z ∈ u : ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S) }
//! ```
//!
//! **Nothing here is an axiom.** `W` is one Separation on `u`; every theorem
//! below is derived from that plus the pairing, union, power set and function
//! space apparatus already in this crate. Phrasing the intersection as a
//! *condition* rather than as `⋂{S ∈ 𝒫u : closed(S)}` is what keeps it to a
//! single Separation — `𝒫(u)` is never needed.
//!
//! # The bound `u` is a hypothesis
//!
//! `W` is carved out of `u`, and `u` is a **parameter**: this module never
//! builds one. Under the four-clause `ax_tarski` that stood until 2026-07-31 a
//! Tarski universe provably would *not* serve — see the countermodels at the end
//! of [`crate::universe`], which are no longer models now that the axiom has a
//! transitivity clause. `closed(A,B,u)` for a universe `u` is therefore no
//! longer refutable, and the route to it is known:
//!
//! 1. `f ∈ fs(B(a), u)` with `B(a) ∈ u` makes every member of `f` a Kuratowski
//!    pair `⟨x,y⟩` of members of `u` — `x ∈ B(a) ⊆ u` by transitivity, `y ∈ u`
//!    by the codomain — so `f ⊆ u` by pairing closure
//!    ([`crate::universe::universe_pairing`], three times);
//! 2. `f` is the surjective image of `B(a) ∈ u` under
//!    `R(x,p) := (p ∈ f ∧ ∃y. p = ⟨x,y⟩)`, so `f ∈ u` by
//!    [`crate::cantor::image_in_universe`];
//! 3. `⟨a,f⟩ ∈ u` by [`crate::universe::least_universe_opair`]'s argument.
//!
//! **All three steps are now derived**, in [`crate::bound`], which turns them
//! into
//!
//! ```text
//! ⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a. (a ∈ A → B(a) ∈ u)))
//!                  → closed(A,B,u))          [crate::bound::universe_closed]
//! ⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → B(a) ∈ U(c)))
//!                  → closed(A,B,U(c)))       [crate::bound::least_universe_closed]
//! ```
//!
//! the second by transfer through the intersection rather than by instantiating
//! the first at `u := U(c)` — the transfer needs nothing about `U(c)` beyond
//! `U(c) ⊆ u`. (`is_universe(U(c))` is a theorem,
//! [`crate::universe::least_universe_is_universe`]; [`crate::bound`] just does
//! not go through it.) So the antecedent below is **discharged at `U(c)`**, and
//! [`crate::bound::sup_mem_at`], [`crate::bound::w_inversion_at`] and
//! [`crate::bound::w_rect_at`] are W1, W3 and structural induction carrying
//! only the typing conditions on `A` and `B`.
//!
//! What is kept here is the *general* form: `u` is still a parameter, and for
//! an arbitrary parameter `closed(A,B,u)` really is irreducible — a `u` that is
//! not closed under `sup` bounds no W-type. The `ω`-tower remains the
//! alternative source of a bound.
//!
//! # The shape of the development
//!
//! | fact | lemma |
//! |---|---|
//! | `(f ∈ fs(X,Y) ∧ Y ⊆ Z) → f ∈ fs(X,Z)` | [`fs_mono`] |
//! | `z ∈ W(A,B,u) ↔ (z ∈ u ∧ ∀S. …)` | [`w_symbol`] |
//! | `z ∈ W(A,B,u) → z ∈ u` | [`w_subset`] |
//! | `(C ⊆ u ∧ closed(A,B,C)) → W(A,B,u) ⊆ C` — **W2** | [`w_induction`] |
//! | `closed(A,B,u) → …⟨a,f⟩ ∈ W(A,B,u)` — **W1** | [`sup_mem`], unconditionally [`crate::bound::sup_mem_at`] |
//! | `closed(A,B,u) → ∀w ∈ W. ∃a ∃f. w = ⟨a,f⟩` — **W3** | [`w_inversion`], unconditionally [`crate::bound::w_inversion_at`] |
//! | `⟨a,f⟩ = ⟨a',f'⟩ → (a = a' ∧ f = f')` — **W4** | [`Wtype::sup_inj`] |
//! | structural induction over a formula | [`w_rect`], unconditionally [`crate::bound::w_rect_at`] |
//!
//! # Non-vacuity
//!
//! Every lemma above is trivially true when `W(A,B,u)` is empty, so without a
//! witness the module proves nothing at all. The witness is
//! [`unit_wtype_inhabited`]: at `A := 1`, `B := ∅` and `u := {⟨•,∅⟩}` it derives
//!
//! ```text
//! ⊢ ⟨•,∅⟩ ∈ W(1, ∅, {⟨•,∅⟩})
//! ```
//!
//! — the unit type as a W-type, a one-element W-type needing no recursion.
//! `∅` serves as the constant-empty family because [`app_of_empty`] gives
//! `app(∅,a) = ∅` for *every* `a`, which is all `closed` ever asks of `B`; and
//! `∅` serves as the empty function because [`empty_is_a_function`] gives
//! `∅ ∈ fs(∅,S)` for every `S`.
//!
//! There is a second way this development could have said nothing: W1, W3 and
//! [`w_rect`] all carry `closed(A,B,u)` as an antecedent, and an antecedent no
//! set ever satisfies makes a theorem vacuous just as surely as an empty `W`.
//! [`unit_bound_closed`] discharges that too, at the same instance —
//! `⊢ closed(1, ∅, {⟨•,∅⟩})` — so W1 there becomes an unconditional typing rule
//! for `sup`. It has a second use now that [`crate::bound`] proves the general
//! statement: `tests/bound.rs` checks that the general theorem's conclusion,
//! instantiated at `A := 1`, `B := ∅`, `u := {⟨•,∅⟩}`, is literally the formula
//! this hand-built instance proves — so the two cannot have drifted apart.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wtype::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`condition`] | [`closed`], [`w_cond`], the symbol `W(A,B,u)`, and `W ⊆ u` |
//! | [`monotone`] | [`fs_mono`] — the function space is monotone in its target |
//! | [`empty`] | the four facts about `∅` the non-vacuity witness and the recursors run on |
//! | [`induction`] | **W2** — `W` is the least closed subset of `u` |
//! | [`sup`] | **W1** — `sup`'s typing rule |
//! | [`inversion`] | **W3** — [`is_sup`], and no junk |
//! | [`rect`] | structural induction over a formula: [`ind_step`], [`Params`], [`w_rect`] |
//! | [`witness`] | the inhabited unit W-type, and a bound that really is closed |
//! | [`apparatus`] | [`Wtype`] — every symbol and theorem over one definitional extension |
//!
//! `shared` holds the two private combinators more than one of them needs; it
//! exports no theorem and is not re-exported. **W4** — injectivity of `sup` —
//! is [`Wtype::sup_inj`], read straight off the Kuratowski pair.

pub mod apparatus;
pub mod condition;
pub mod empty;
pub mod induction;
pub mod inversion;
pub mod monotone;
pub mod rect;
mod shared;
pub mod sup;
pub mod witness;

pub use apparatus::Wtype;
pub use condition::{closed, w_cond, w_subset, w_symbol};
pub use empty::{app_of_empty, empty_funspace, empty_is_a_function, empty_product};
pub use induction::w_induction;
pub use inversion::{is_sup, w_inversion};
pub use monotone::fs_mono;
pub use rect::{ind_step, w_rect, Params};
pub use sup::sup_mem;
pub use witness::{unit_bound_closed, unit_wtype_inhabited};
