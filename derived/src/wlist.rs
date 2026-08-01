//! **Lists as a W-type** — Lean's
//! `inductive List (α : Type u) | nil : List α | cons : α → List α → List α`,
//! the first *parameterised* inductive this development interprets.
//!
//! # The construction
//!
//! ```text
//! A(α)   := 1 + α                       one tag per constructor; `cons` carries its head
//! 2      := {0, 1}                       a codomain for the fibre family
//! B(α)   := rec₊(λ_:1. 0, λ_:α. 1)      nil has no recursive argument, cons has one
//! lt(α)  := W(A(α), B(α), U(A(α)))
//! nil       := ⟨inl •, ∅⟩               the empty function out of the empty fibre
//! cons h t  := ⟨inr h, {⟨•,t⟩}⟩         the one-point function out of `1`
//! ```
//!
//! `α` is a **parameter**, not an index, so `INDUCTIVES.md`'s `good` predicate is
//! vacuous and `lt(α)` is the W-type outright, with no subset carving. It stays a
//! free variable of every statement below: `lt` is a *unary* symbol, where
//! [`crate::wnat`]'s `N` was nullary.
//!
//! # Interface
//!
//! Writing `fam(α)` for the fibre family (which is [`WList::fam_of`], a term, not
//! a symbol) and `lt(α)` for the type:
//!
//! ```text
//! ⊢ ∀α. app(fam(α), inl •) = 0                          [WList::fibre_nil]
//! ⊢ ∀α ∀h. (h ∈ α → app(fam(α), inr h) = 1)             [WList::fibre_cons]
//! ⊢ ∀α. closed(1+α, fam(α), U(1+α))                     [WList::closed]
//! ⊢ ∀α. lt(α) = W(1+α, fam(α), U(1+α))                  [WList::lt_ax]
//! ⊢ ∀α. ⟨inl •,∅⟩ ∈ lt(α)                               [WList::nil]
//! ⊢ ∀α ∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → ⟨inr h,{⟨•,t⟩}⟩ ∈ lt(α))   [WList::cons]
//! ```
//!
//! and the two injectivity statements, plus the three-element witness:
//!
//! ```text
//! ⊢ ∀h ∀t. ¬(⟨inl •,∅⟩ = ⟨inr h,{⟨•,t⟩}⟩)               [WList::nil_ne_cons]
//! ⊢ ∀h ∀t ∀h′ ∀t′. (cons h t = cons h′ t′ → (h = h′ ∧ t = t′))  [WList::cons_inj]
//! ⊢ ∀h. (¬(nil = c₁) ∧ (¬(nil = c₂) ∧ ¬(c₁ = c₂)))      [WList::distinct3]
//! ⊢ ∀α ∀h. (h ∈ α → (nil ∈ lt(α) ∧ (c₁ ∈ lt(α) ∧ c₂ ∈ lt(α))))  [WList::three_in]
//! ```
//!
//! where `c₁ = cons h nil` and `c₂ = cons h c₁`. Callers need none of the
//! derivations below.
//!
//! # The memberships are **unconditional in `α`**
//!
//! `INDUCTIVES.md`'s `N` report predicted that "every membership theorem
//! acquires a hypothesis `α ∈ ⟦Sort u⟧` that nothing currently discharges".
//! **Measured, that is wrong**, and the reason is worth recording, because it
//! says which obstructions are about inductives and which are about `Sort`.
//!
//! [`crate::bound::least_universe_closed`] asks only for `A ∈ U(c)` and
//! `∀a ∈ A. app(B,a) ∈ U(c)`, and at `c := A := 1 + α` all three obligations hold
//! with `α` free and no hypothesis at all:
//!
//! * `1 + α ∈ U(1+α)` — [`crate::universe::mem_least_universe`], which is about
//!   an arbitrary set and so does not care that this one mentions `α`;
//! * `0 = ∅ ∈ U(1+α)` — [`crate::enums::empty_in_least_universe`];
//! * `1 = {∅} ∈ U(1+α)` — [`crate::bound::Bound::least_pairing`] at `a = b = ∅`.
//!
//! Nothing there mentions `α`'s own type, so nothing asks for one. The same goes
//! for the two memberships: `sup`'s typing rule needs a tag in `1 + α` and a
//! function out of the fibre, and `h ∈ α` supplies the first for `cons` — a
//! hypothesis about `h`, not about `α`.
//!
//! What genuinely is **not** derivable is `lt(α) ∈ ⟦Sort u⟧`, and that is the
//! obstruction already recorded for `⟦Bool⟧ ∈ ⟦Sort 1⟧`: it comes from the
//! `Sort` encoding, where `⟦Sort u⟧` is an iterated `U` over an opaque
//! `⟦Sort 0⟧`, and not from anything about inductives. The hypothesis
//! `α ∈ ⟦Sort u⟧` *does* reappear one level up, in [`crate::wlist_fun`], but for
//! an unrelated reason: there `⟦List⟧` has to be a **set function**, and a set
//! function only computes on its domain.
//!
//! # What the parameter costs: one constant function on an arbitrary set
//!
//! For `N` both fibre branches were constant functions on `1`, and a constant
//! function on a *singleton* is a one-point graph, so [`crate::point_fun`]
//! covered them. Here the right branch is `λ_ : α. 1` on an **arbitrary** `α`,
//! which is not a one-point graph. It is built instead as a lambda graph
//! ([`crate::funcs::lambda`]) over a constant body symbol `co(y) = 1`, typed by
//! [`crate::ext::lam_in_funspace`] — whose hypothesis `∀y ∈ α. co(y) ∈ 2` is
//! discharged by `1 ∈ 2` alone. That is the one piece of new machinery the
//! parameter costs, and it is four lines.
//!
//! Note the asymmetry this produces: `app(fam(α), inl •) = 0` is
//! unconditional, because the left fibre function lives on `1` and `• ∈ 1` is a
//! theorem, whereas `app(fam(α), inr h) = 1` carries `h ∈ α`, because `α` is
//! arbitrary and `h` might not be in it. `cons`'s membership inherits that
//! hypothesis, which is exactly the one Lean's `cons : α → List α → List α`
//! states.
//!
//! # Non-vacuity
//!
//! Two memberships about one set say nothing if that set could be a singleton,
//! so both distinctness statements are derived and pinned in `tests/wlist.rs`:
//!
//! * [`WList::nil_ne_cons`] comes from [`crate::sums::Sums::disjoint`] — the two
//!   *tags* differ, whatever the head and tail are;
//! * [`WList::cons_inj`] comes from the Kuratowski pair's injectivity three
//!   times over: once for the W-type pair, once through the singleton fibre, and
//!   once inside it. It gives **both** components back, so `cons` is injective in
//!   the head as well as the tail — which is what makes `α`'s elements visible
//!   inside the list and stops `lt(α)` collapsing to `N`.
//!
//! [`WList::distinct3`] cashes them in: for any `h`, the three lists `nil`,
//! `cons h nil`, `cons h (cons h nil)` are pairwise distinct, and
//! [`WList::three_in`] puts all three in `lt(α)` as soon as `α` has an element.
//! So `lt(α)` is provably infinite for inhabited `α`, and every membership above
//! is a statement about a set with many elements.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wlist::…` all still resolve. Read the header of the one file you
//! need.
//!
//! | file | what it holds |
//! |---|---|
//! | [`apparatus`] | [`WList`] — the symbol `lt(α)`, the term builders, and the constructor |
//! | [`typing`] | the two constructors' typing rules, and which hypotheses are real |
//! | [`distinct`] | distinctness, injectivity, and three distinct lists — the non-vacuity witness |

pub mod apparatus;
pub mod distinct;
pub mod typing;

pub use apparatus::WList;
