//! Discharging the W-type's bound hypothesis: **a universe is closed under
//! `sup`**.
//!
//! # Interface
//!
//! Write `closed(A,B,S)` for [`crate::wtype::closed`], i.e.
//!
//! ```text
//! closed(A,B,S)  :=  ∀a. (a ∈ A → ∀f. (f ∈ fs(app(B,a), S) → ⟨a,f⟩ ∈ S))
//! ```
//!
//! and `U(c)` for the least universe containing `c`
//! ([`crate::universe::least_universe`]). The exports are
//!
//! ```text
//! ⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → ⟨a,b⟩ ∈ u)   [universe_opair]
//! ⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ⊆ u) [funspace_subset_universe]
//! ⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ∈ u) [funspace_mem_universe]
//! ⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a. (a ∈ A → app(B,a) ∈ u)))
//!                 → closed(A,B,u))                               [universe_closed]
//! ⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c)))
//!                 → closed(A,B,U(c)))                            [least_universe_closed]
//! ⊢ ∀c ∀x ∀f. ((x ∈ U(c) ∧ f ∈ fs(x, U(c))) → f ∈ U(c))          [least_universe_funspace_mem]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))           [funspace_subset_least_universe]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))             [Bound::least_pairing]
//! ```
//!
//! Note the **`⊆`** in the last one. `fs(a,b) ∈ U(c)` does *not* follow from
//! these — the missing step is named exactly on
//! [`funspace_subset_least_universe`] — but it is now proved by a different
//! route, [`crate::funspace::funspace_in_universe_pair`], which goes through
//! `⋃`-closure and iterated power sets rather than through the pairs.
//! [`Bound`] assembles the whole chain in one struct.
//!
//! and, with the last of those, the three W-type rules that used to carry
//! `closed(A,B,u)` as an antecedent, now carrying only the typing side
//! conditions on `A` and `B` that any caller has anyway:
//!
//! ```text
//! ⊢ ∀c ∀A ∀B. (T(A,B,c) → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) → ⟨a,f⟩ ∈ W)))  [sup_mem_at]
//! ⊢ ∀c ∀A ∀B. (T(A,B,c) → ∀w. (w ∈ W → ∃a. (a ∈ A ∧ ∃f. (…))))             [w_inversion_at]
//! ⊢ T(A,B,c) → (ind_step → ∀z. (z ∈ W → φ(z)))                             [w_rect_at]
//! ```
//!
//! writing `W` for `W(A,B,U(c))` and `T(A,B,c)` for
//! `A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c))`. Callers need none of the
//! derivations below; the statements above are the whole contract.
//!
//! # Why this is not circular, and what it needs from the axiom
//!
//! `is_universe(U(c))` is **not** available — its inaccessibility clause is
//! open, see [`crate::universe::inaccessibility_reduction`] — so
//! [`least_universe_closed`] cannot be [`universe_closed`] at `u := U(c)`. It
//! is the same transfer through the intersection that
//! [`crate::universe::least_universe_pairing`] makes: a closure property that
//! holds in *every* universe holds in `U(c)`, because `U(c) ⊆ u` for every
//! universe `u ∋ c` and [`crate::wtype::fs_mono`] moves a function into the
//! larger codomain.
//!
//! Three clauses of `ax_tarski` do the work. `C₁` (transitivity, added
//! 2026-07-31) is what makes `f ⊆ u`: a member of `f ∈ fs(x,u)` is a pair
//! `⟨p,q⟩` with `p ∈ x ∈ u`, and without `C₁` there is nothing putting `p` in
//! `u` — countermodel B at the end of [`crate::universe`] refutes exactly that.
//! `C₂` and `C₄` are spent inside [`crate::cantor::image_in_universe`], which
//! is what turns `f ⊆ u` into `f ∈ u`, and `C₃` inside
//! [`crate::universe::universe_pairing`], which needs three distinct members of
//! `u` to refute `{a,b} ≈ u`. So all four clauses are load-bearing, but only
//! `C₁` is load-bearing *here*: the other three are spent in lemmas that were
//! already proved.
//!
//! # The route
//!
//! For `f ∈ fs(B(a), u)` with `B(a) ∈ u`:
//!
//! 1. **`f ⊆ u`** — [`funspace_subset_universe`]. Every `p ∈ f` is in
//!    `prod(B(a), u)`, hence `p = ⟨x,y⟩` with `x ∈ B(a)` and `y ∈ u`; `x ∈ u`
//!    by `C₁`, and then `⟨x,y⟩ ∈ u` by [`universe_opair`], which is
//!    [`crate::universe::universe_pairing`] three times over the Kuratowski
//!    pair `{{x},{x,y}}`.
//! 2. **`f ∈ u`** — [`funspace_mem_universe`], by
//!    [`crate::cantor::image_in_universe`] at `I := B(a)`, `S := f` and the
//!    relation **scheme** `R(x,p) := (p ∈ f ∧ ∃y. p = ⟨x,y⟩)`. `R` is a
//!    formula, not a set, so no second product and no Separation are needed.
//!    Its three clauses come from the product membership condition
//!    (`ONTO`), from [`crate::pairs::opair_inj`] (`DOM`), and from `f`'s own
//!    single-valuedness together with `opair_inj` (`SV`).
//! 3. **`⟨a,f⟩ ∈ u`** — [`universe_opair`] again, with `a ∈ u` from `a ∈ A ∈ u`
//!    by `C₁`.
//!
//! No closure under `⋃`, binary union or products is used, and none is proved:
//! the route above never builds `prod(a,b)` as a *member*, only reads the
//! membership condition of one that is already there.
//!
//! # Non-vacuity
//!
//! Two checks, both in `tests/bound.rs`.
//!
//! * **Against the worked instance.** [`crate::wtype::unit_bound_closed`]
//!   proves `⊢ closed(1, ∅, {⟨•,∅⟩})` by hand, from the axioms, with no
//!   universe anywhere. The conclusion of [`universe_closed`] instantiated at
//!   those same three terms is checked to be *that formula* — so the general
//!   theorem and the worked instance are about the same predicate, and neither
//!   is a look-alike of the other.
//! * **The antecedents are satisfied, not merely unrefuted.** The test
//!   `a_universe_bounded_wtype_is_inhabited` derives
//!   `⊢ {c} ∈ U(c) ∧ ∀a. (a ∈ {c} → app(∅,a) ∈ U(c))` outright — `c ∈ U(c)`,
//!   pairing, and `∅ ∈ U(c)` by `C₂` — discharges it against
//!   [`least_universe_closed`] to get `⊢ closed({c}, ∅, U(c))`, and cashes
//!   [`sup_mem_at`] in at `a := c`, `f := ∅` for
//!
//!   ```text
//!   ⊢ ⟨c,∅⟩ ∈ W({c}, ∅, U(c))
//!   ```
//!
//!   — the unit W-type again, but bounded by an arbitrary set's canonical
//!   universe rather than by a bound picked to make `closed` true by fiat.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::bound::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need — each restates
//! the part of the Interface block above that it owns.
//!
//! | file | step | what it exports |
//! |---|---|---|
//! | [`opair`] | 1 | `⟨a,b⟩ ∈ u` for members `a`, `b` of a universe |
//! | [`subset`] | 2 | `f ⊆ u` for `f ∈ fs(x,u)`, and [`funspace_pairs`] |
//! | [`member`] | 3 | `f ∈ u` for the same `f` — the long one |
//! | [`closure`] | 4 | [`fibres_in`], and `closed(A,B,u)` for an arbitrary universe |
//! | [`least`] | 5 | the transfer of step 4 to `U(c)`, where `is_universe` is unavailable |
//! | [`rules`] | 6 | [`At`], and the three W-type rules with the bound antecedent gone |
//! | [`funspace_universe`] | 7 | `f ∈ U(c)`, and `fs(a,b) ⊆ U(c)` — note the `⊆` |
//! | [`chain`] | — | [`Bound`], the whole chain assembled once |
//!
//! `shared` holds the private `H → …` combinators and formula readers more than
//! one of them needs; it exports no theorem and is not re-exported.

pub mod chain;
pub mod funspace_universe;
pub mod least;
pub mod member;
pub mod opair;
pub mod rules;
mod shared;
pub mod subset;
pub mod closure;

pub use chain::Bound;
pub use funspace_universe::{funspace_subset_least_universe, least_universe_funspace_mem};
pub use least::{least_universe_closed, least_universe_subset};
pub use member::funspace_mem_universe;
pub use opair::universe_opair;
pub use rules::{discharge_closed, sup_mem_at, w_inversion_at, w_rect_at, At};
pub use subset::{funspace_pairs, funspace_subset_universe};
pub use closure::{fibres_in, universe_closed};
