//! **The recursor for `List`**, and its two computation rules — Lean's
//! `List.rec`, computed, with a field *and* a recursive call live.
//!
//! # What this is
//!
//! [`crate::wlist`] interprets `inductive List (α : Type u) | nil | cons (h : α)
//! (t : List α)` as the W-type `lt(α) = W(1+α, fam(α), U(1+α))` with
//! `fam(α)(inl •) = 0`, `fam(α)(inr h) = 1`, and constructors `⟨inl •, ∅⟩` and
//! `⟨inr h, {⟨•,t⟩}⟩`. [`crate::wrec_total`] builds the W-recursor and proves the
//! **unguarded** ι rule for it. This file is the join: it packs Lean's two minor
//! premises into the single step `e` the W-recursor takes, discharges that rule's
//! `step_typed` hypothesis from the recursor's *own* argument typings, and reads
//! off
//!
//! ```text
//! List.rec z s (List.nil α)        ≡  z
//! List.rec z s (List.cons α h t)   ≡  s h t (List.rec z s t)
//! ```
//!
//! as equations between sets.
//!
//! # What is new here, against [`crate::wnat_rec`]
//!
//! Two things, and only two.
//!
//! *The value has three components.* `N.succ` carries one recursive argument and
//! nothing else, so its step value is `app(app(s, app(f,•)), app(r,•))`.
//! `List.cons` carries a **field** as well, so its value is
//! `app(app(app(s,h), app(f,•)), app(r,•))`. In the packed encoding that is
//! literally **one more application in [`value_packed`] and nothing else** —
//! every lemma between `row_packed` and `unpack` is stated at the packed
//! payload `p` and never names a component. That collapse is the whole reason
//! [`crate::proj`] was built rather than the existential encoding, and it holds:
//! `step_cases`, `value_at_packed`, `value_at_nil` and `step_single_valued` are
//! `wnat_rec`'s proofs with `h` threaded through as an inert extra argument.
//!
//! *The tag carries the field.* `N`'s `succ` tag is the constant `inr •`;
//! `List`'s is `inr h`, which **varies**. So the step's Replacement can no longer
//! range over the fibre payload alone — it ranges over `q ∈ prod(α, P(T))`, and
//! the row reads its two halves back with `π₁`/`π₂` (`row_at`). That is one
//! extra projection *at the Replacement*, not inside the lemmas: everything from
//! `step_cases` downwards sees `π₁ q` and `π₂ q` as opaque terms and never
//! needs the η rule `⟨π₁ q, π₂ q⟩ = q`, which is what would have forced the
//! dropped membership `q ∈ prod(α,P(T))` to be carried through every case
//! analysis.
//!
//! ```text
//! FW(α)   := 𝒫(prod(1, lt(α)))     a superset of fs(1,lt(α)) that also holds ∅
//! FT(T)   := 𝒫(prod(1, T))
//! P(α,T)  := prod(FW(α), FT(T))        the cons branch's fibre payload, packed
//! Q(α,T)  := prod(α, P(α,T))           …together with the head
//! k₀      := ⟨inl •, ⟨∅,∅⟩⟩             the nil branch's whole argument
//! val(s,h,p) := app(app(app(s,h), app(π₁ p, •)), app(π₂ p, •))
//! row(s,h,p) := ⟨⟨inr h, p⟩, val(s,h,p)⟩
//!
//! E(α,s,T)   := { row(s, π₁ q, π₂ q) : q ∈ Q(α,T) }     one Replacement
//! e(α,z,s,T) := E(α,s,T) ∪ {⟨k₀, z⟩}
//! ```
//!
//! # `α` is a parameter, and stays free
//!
//! Everything below is stated with `α` a free variable, exactly as
//! [`crate::wlist`] states its memberships. The only hypotheses about it are the
//! ones Lean's own signature states — `h ∈ α` for a head — plus the recursor's
//! own argument typings. In particular nothing asks for `α ∈ ⟦Sort u⟧`; that
//! hypothesis belongs to [`crate::wlist_fun`], where `⟦List⟧` has to be a set
//! *function*, and not to the inductive.
//!
//! # Interface
//!
//! Writing `lrec(α,z,s,T)` for [`ListRec::of`] and
//! `HYP := z ∈ T ∧ s ∈ fs(α, fs(lt(α), fs(T,T)))`:
//!
//! ```text
//! ⊢ ∀α ∀z ∀s ∀T. app(e(α,z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z             [ListRec::app_nil]
//! ⊢ ∀α ∀z ∀s ∀T ∀h ∀f ∀r. ((h ∈ α ∧ (f ∈ FW(α) ∧ r ∈ FT(T))) →
//!       app(e(α,z,s,T), ⟨inr h,⟨f,r⟩⟩)
//!            = app(app(app(s,h), app(f,•)), app(r,•)))          [ListRec::app_cons]
//! ⊢ ∀α ∀z ∀s ∀T. (HYP → step_typed(1+α, fam(α), U(1+α), T, e))  [ListRec::step_typed]
//! ⊢ ∀α ∀z ∀s ∀T. (HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z)      [ListRec::iota_nil]
//! ⊢ ∀α ∀z ∀s ∀T ∀h ∀t. ((HYP ∧ (h ∈ α ∧ t ∈ lt(α))) →
//!       app(lrec(α,z,s,T), ⟨inr h,{⟨•,t⟩}⟩)
//!            = app(app(app(s,h),t), app(lrec(α,z,s,T), t)))     [ListRec::iota_cons]
//! ```
//!
//! `HYP` is Lean's own typing of a `List.rec` application and nothing more, with
//! `T` the motive at `List.nil α`. It is **not** free — `Bool`'s was, because
//! `T := {fls,tru}` made `step_typed` vacuous there, and no such trick survives a
//! step whose value is an application — but it is also not new work: it is the
//! recursor's own domain obligations, which a caller is already paying for.
//!
//! # Non-vacuity
//!
//! [`ListRec::iota_cons`]'s right-hand side mentions `lrec` again, so it is not
//! an equation two constant terms could satisfy by accident, and it mentions the
//! head `h` as well, so it is not an equation that ignores the field.
//! [`premise_witness`] discharges `HYP` outright at `α := 1`, `T := 1`, `z := •`
//! — a tag set with a *member*, so `h ∈ α` is satisfiable too and the cons rule
//! is not vacuous at that instance. `tests/wlist_rec.rs` pins all of it.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wlist_rec::…` all still resolve. Read the header of the one file you
//! need.
//!
//! | file | what it holds |
//! |---|---|
//! | [`step`] | the terms, and the step symbol as one Replacement over a packed row |
//! | [`members`] | what is in the step, and what is not |
//! | [`values`] | the step's values, and hence that it is a function |
//! | [`computes`] | the step's two computation rules — the non-vacuity witness |
//! | [`typed`] | [`premise`], and that the step lands in the motive |
//! | [`iota`] | the two ι rules, `iota_nil` and `iota_cons` |
//! | [`recursor`] | [`ListRec`] — the whole thing, packaged |
//!
//! `shared` holds the private implication-form rewriting steps more than one of
//! them needs; it exports no theorem and is not re-exported.
//!
//! The layout mirrors [`crate::wnat_rec`] file for file, because the two
//! constructions are the same argument at a different index set — `1 + α`
//! instead of `1 + 1` — and keeping them parallel is what makes the extra cost
//! of the head parameter visible.

pub mod computes;
pub mod iota;
pub mod members;
pub mod recursor;
mod shared;
pub mod step;
pub mod typed;
pub mod values;

pub use recursor::{premise_witness, ListRec};
pub use step::{
    domain, key_cons, key_nil, payload, pow_prod, value_cons, value_packed, StepSyms,
};
pub use typed::premise;

// ─────────────────────────────────────────────────────────────────────────────
// Closing notes — 2026-07-31
//
// ## What is done
//
// The derived side of `List.rec` is complete. `ListRec::over` returns, at fresh
// `α`, `z`, `s`, `T`, `h` and `t`, with `HYP := z ∈ T ∧ s ∈ fs(α, fs(lt(α),
// fs(T,T)))`:
//
//   app_nil     ⊢ ∀α∀z∀s∀T. app(e(α,z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z
//   app_cons    ⊢ ∀α∀z∀s∀T∀h∀f∀r. ((h ∈ α ∧ (f ∈ FW(α) ∧ r ∈ FT(T))) →
//                     app(e(α,z,s,T), ⟨inr h,⟨f,r⟩⟩)
//                        = app(app(app(s,h), app(f,•)), app(r,•)))
//   sv          ⊢ ∀α∀z∀s∀T. sv(e(α,z,s,T))
//   step_typed  ⊢ ∀α∀z∀s∀T. (HYP → step_typed(1+α, fam(α), U(1+α), T, e))
//   iota_nil    ⊢ ∀α∀z∀s∀T. (HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z)
//   iota_cons   ⊢ ∀α∀z∀s∀T∀h∀t. ((HYP ∧ (h ∈ α ∧ t ∈ lt(α))) →
//                     app(lrec(α,z,s,T), ⟨inr h,{⟨•,t⟩}⟩)
//                        = app(app(app(s,h),t), app(lrec(α,z,s,T), t)))
//
// `iota_cons` is the point of the file: its right-hand side mentions `lrec`
// again *and* the constructor's field `h`, which no `N` equation could.
// `premise_witness` discharges `HYP` at `α := 1`, `T := 1`, `z := •`, and
// `tests/wlist_rec.rs` pins all six plus that discharge — including the cons
// rule fired at `h := •`, `t := nil`, which is why the witness takes `α := 1`
// rather than the cheaper `α := 0`.
//
// ## The "one more π" claim, tested
//
// `wnat_rec`'s closing notes justify `crate::proj` by predicting that a
// constructor with a field costs "one more `π` in the value term and nothing
// else, because every lemma between the step's Replacement and `unpack` is
// stated at the packed payload and never names a component". **That held**, and
// it is worth being precise about how far.
//
// * `value_packed` gains one application — `app(su,h)` in place of `su` — and
//   `unpack` gains one congruence. That is the predicted cost, exactly.
// * `step_cases`, `value_at_packed`, `value_at_nil`, `step_single_valued`,
//   `row_in_step` and `nil_in_step` are `wnat_rec`'s proofs with `h` threaded
//   through as an **inert extra argument**. Not one of them changed shape; the
//   fibre payload `p` is still opaque to all of them.
// * What the prediction did *not* cover, and what a reader should expect next
//   time, is that `List`'s **tag varies**: `N`'s cons-side key is the constant
//   `inr •`, `List`'s is `inr h`. So the Replacement can no longer range over
//   the fibre payload alone — it ranges over `q ∈ prod(α, P(α,T))` — and one
//   projection appears *at the Replacement*, in `row_at`.
//
//   That extra projection is confined to `row_at` and does **not** leak, and the
//   reason is worth recording because it was the one real design choice here.
//   Stating `value_at_packed` at `(h,p)` rather than at `q` is what avoids ever
//   needing the η rule `⟨π₁ q, π₂ q⟩ = q` — the case analysis compares
//   `⟨inr h, p⟩` with `⟨inr(π₁ q), π₂ q⟩` and reads off `h = π₁ q` (by
//   `inr_inj`) and `p = π₂ q` separately, never reassembling `q`. Had it been
//   stated at `q`, `step_cases` would have had to *carry* the dropped membership
//   `q ∈ prod(α,P(α,T))` through every case analysis, which is precisely the
//   widening the existential encoding was rejected for.
//
// ## What indexed families would need next
//
// Nothing in this file. `α` is a **parameter** — fixed throughout the
// declaration — so it stays a free variable and `INDUCTIVES.md`'s `good`
// predicate is vacuous; that is what lets `lt(α)` be the W-type outright. An
// *index* varies per constructor, so §5.2's translation carves a subset of the
// W-type by `good`, and `good`'s base case is an **equality** between index
// tuples. `crate::prop` interprets `Eq` as a conditional singleton, which is
// enough to *type* `Eq.refl` and no more; a `good` predicate needs `Eq`'s
// elimination, and for `Eq` specifically that is `is_k` subsingleton elimination
// (§5.3), which abandons W-types for `acc`. So the order is: `acc`, then §5.3,
// then §5.2's `spec` judgment — and only then does a second file beside this one
// make sense. Extending this one would not reach it.
//
// The nearer generalisation, and the cheap one, is a constructor with **two or
// more plain recursive arguments**: that changes only the fibre — `f` and `r`
// are still single sets, over a two-point domain instead of `1` — so neither the
// encoding nor any proof here cares.
//
// `116_rtreeRecReduction` is NOT the corpus test for it, though this comment
// said so until 2026-08-01. `RTree.node` has `numFields: 1` and `RTree` is
// exported with `isReflexive: true`: its one recursive argument is
// function-typed, `children : (Bool → RTree)`. That is the `Σ(z::γ)` fibre
// shape — strictly harder, and its reduct puts a lambda under the minor
// premise. There is no plain `m ≥ 2` test in the tutorial corpus at all
// (`RBTree.red`/`black` are `m ≥ 2` but `RBTree` is an indexed family,
// `numIndices: 2`); the witnesses are `Lean.ParserDescr.{binary, sepBy,
// sepBy1}` in `init-prelude`.
//
// ## The backend, wired — 2026-07-31
//
// `checker/src/tg.rs` gained `RecBottom::List`, `list_rec_shape`,
// `list_recursor()` and `fire_list`, and `076_listRecReduction` went **63 gaps
// / 15 escapes → 32 / 16**, with all five ι gaps closed. Three things the
// wiring needed that `N` did not, all recorded on `RecBottom`:
//
// 1. **Parameter handling.** `derive_iota_core` drops `c.num_params` of the
//    major premise's arguments before taking its fields, mirroring
//    `reduce_rec`'s `num_extra_params_to_major`; and the nest's bottom reads the
//    minors at `vars[np+1]`/`vars[np+2]` and the target at `doms[np+1]`.
// 2. **The type is a redex.** `⟦List α⟧` is `app(⟦List.{u}⟧, ⟦α⟧)`, so the
//    bridge to `lt(α)` is `wlist_fun`'s `l_beta` under `⟦α⟧ ∈ ⟦Type u⟧` — a
//    *conditional* equation, which is why `TgBackend::mem_along` grew the
//    variant `mem_along_c`.
// 3. **The constructors are applied.** `wlist_fun` grew `nil_beta` and
//    `cons_beta`, the *equations* behind the two membership rules it already
//    exported: ι needs `app(Nil(S),α) = ⟨inl •,∅⟩`, not `∈`.
//
// The 32 that remain are **not** the recursor, and are not this file's. Measured
// rather than argued: `076` had 15 escaping certificates *before* the recursor
// was wired and has 16 after, so closing 31 gaps beneath them moved them by one.
// See `INDUCTIVES.md` for the breakdown.
