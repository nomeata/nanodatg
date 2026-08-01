//! **The recursor for `N`**, and its two computation rules — Lean's `N.rec`,
//! computed, with the recursive call live.
//!
//! # What this is
//!
//! [`crate::wnat`] interprets `inductive N | zero | succ (n : N)` as the W-type
//! `N = W(1+1, B, U(1+1))` with `B(inl •) = 0`, `B(inr •) = 1`, and constructors
//! `⟨inl •, ∅⟩` and `⟨inr •, {⟨•,n⟩}⟩`. [`crate::wrec_total`] builds the
//! W-recursor and proves the **unguarded** ι rule for it. This file is the
//! join: it packs Lean's two minor premises into the single step `e` the
//! W-recursor takes, discharges that rule's `step_typed` hypothesis from the
//! recursor's *own* argument typings, and reads off
//!
//! ```text
//! N.rec z s N.zero      ≡  z
//! N.rec z s (N.succ n)  ≡  s n (N.rec z s n)
//! ```
//!
//! as equations between sets. The second is ι **with the recursive call live**,
//! which is what [`crate::wbool_rec`] could not exercise: `Bool`'s fibres are
//! empty, so its composite collapses by
//! [`crate::wrec_unit::comp_empty_domain`] and its ι right-hand side never
//! mentions the recursor again. Here the `succ` fibre is `1`, the composite is
//! the one-point graph `{⟨•, app(nrec,n)⟩}`, and
//! [`crate::wrec_typing::composite_app`] is what reads the recursive value back
//! out of it.
//!
//! # The step, and the projections it is built on
//!
//! The W-recursor applies its step to the **triple** `⟨a, ⟨f, r⟩⟩` — the tag,
//! the subterm family and the family of recursive values. For `Bool` the fibres
//! are empty, `f` and `r` are forced to `∅`, the triple takes exactly two values
//! and the step is a graph on two points ([`crate::twopoint`]). For `N` the
//! `succ` fibre is `1`, so `f` ranges over `fs(1,N)` and `r` over `fs(1,T)`, and
//! the step has to *compute* `app(app(s, app(f,•)), app(r,•))` — it must take
//! its argument apart.
//!
//! [`crate::proj`] is what takes it apart. Writing `π₁`/`π₂` for its
//! projections:
//!
//! ```text
//! FW      := 𝒫(prod(1, N))        a superset of fs(1,N) that also holds ∅
//! FT(T)   := 𝒫(prod(1, T))
//! P(T)    := prod(FW, FT(T))          the succ branch's payload, packed
//! k₀      := ⟨inl •, ⟨∅,∅⟩⟩            the zero branch's whole argument
//! val(s,p):= app(app(s, app(π₁ p, •)), app(π₂ p, •))
//!
//! E(s,T)   := { ⟨⟨inr •, p⟩, val(s,p)⟩ : p ∈ P(T) }     one Replacement
//! e(z,s,T) := E(s,T) ∪ {⟨k₀, z⟩}
//! ```
//!
//! # Why projections, and not an existential — the extend-or-replace test
//!
//! There is a shorter construction, and this file deliberately does not use it.
//! Without projections the components can only be *named* by an existential
//! inside the Replacement's own relation — one Replacement layer per component,
//! `{ ⟨key(f,r), val(s,f,r)⟩ : r ∈ FT }` gathered over `f ∈ FW` — and then every
//! fact about the step is proved by eliminating those existentials in turn.
//! That was built first and it works for `N`.
//!
//! It fails the test that matters, which is **not** "is this the more general
//! construction" but **"when the next constructor shape arrives, do I extend
//! this or replace it?"**:
//!
//! * `List.cons` has a *field* as well as a recursive argument, so its step
//!   value is `app(app(app(s, h), app(f,•)), app(r,•))` — three components, not
//!   two. With the existential encoding that is a **third Replacement layer**,
//!   and `step_cases`, `value_at_packed` and `step_single_valued` all
//!   widen with it: every proof in the file is rewritten. With projections it is
//!   one more `π` in [`value_packed`] and **nothing else changes**, because
//!   every lemma between `row_packed` and `unpack` is stated at the *packed*
//!   payload `p` and never names a component.
//! * A constructor with two recursive arguments changes only the fibre — `f`
//!   and `r` are still single sets — so neither encoding cares.
//!
//! So the projection route extends and the existential route is replaced, which
//! is the same distinction as `enums.rs` → `wnat.rs` → `wlist.rs` (each strictly
//! generalised the last) against `twopoint.rs` (which took `073` to zero gaps
//! and then had to go, because `N`'s fibres are not empty).
//!
//! The thesis agrees, and that is independent evidence rather than the reason:
//! §5.1's menagerie takes `Σx : α. β` with `π₁` and `π₂` as **primitives**, with
//! ι rules `π₁(a,b) ≡ a`, `π₂(a,b) ≡ b` and the η rule `(π₁ x, π₂ x) ≡ x`. It
//! expects to project out of packed tuples everywhere, not only here.
//!
//! **What is *not* built, and why.** The `Σ` *type former* itself. The step's
//! true domain is dependent — at the tag `inl •` the payload lives in
//! `fs(0,N) × fs(0,T)` and at `inr •` in `fs(1,N) × fs(1,T)` — so `Σ` is what it
//! would take to state that domain exactly. It is not needed, because both
//! fibres embed in the *one* non-dependent superset `P(T)`: `fs(0,X) = {∅}` and
//! `∅ ∈ 𝒫(prod(1,X))`, and `fs(1,X) ⊆ 𝒫(prod(1,X))`. That collapse is not
//! special to `N` — it holds whenever the fibres are bounded by a common power
//! set, which covers every non-indexed inductive with finitely many recursive
//! arguments per constructor, `List` included. `Σ` becomes load-bearing only for
//! an unbounded fibre family, which is out of scope for the same reason the
//! ω-tower is. The half of §5.1's `Σ` that *is* needed — the projections — is
//! built.
//!
//! # Interface
//!
//! Writing `nrec(z,s,T)` for [`NatRec::of`] and
//! `HYP := z ∈ T ∧ s ∈ fs(N, fs(T,T))`:
//!
//! ```text
//! ⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z                [NatRec::app_zero]
//! ⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) →
//!       app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩) = app(app(s,app(f,•)),app(r,•)))
//!                                                             [NatRec::app_succ]
//! ⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))
//!                                                           [NatRec::step_typed]
//! ⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)        [NatRec::iota_zero]
//! ⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) →
//!       app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩)
//!            = app(app(s,n), app(nrec(z,s,T), n)))            [NatRec::iota_succ]
//! ```
//!
//! `HYP` is **not** free, unlike `Bool`'s — `T := {fls,tru}` made
//! `step_typed` vacuous there, and no such trick is available once the step's
//! value is an application. But it is also not new work: `z ∈ T` and
//! `s ∈ fs(N, fs(T,T))` are exactly the typing obligations a caller applying
//! Lean's `N.rec` to `z` and `s` is already paying, with `T` the motive at
//! `N.zero`. See the `N.rec` feasibility entry in `INDUCTIVES.md`.
//!
//! # Non-vacuity
//!
//! [`NatRec::iota_succ`]'s right-hand side mentions `nrec` again, so it is not
//! an equation two constant terms could satisfy by accident, and `tests/wnat_rec.rs`
//! checks that its two sides are different terms and that the recursive
//! occurrence is really there. [`NatRec::app_zero`] and [`NatRec::app_succ`] are
//! computations of the *step* at fresh variables, and the second returns a term
//! built out of the caller's own `s`, so no degenerate step satisfies both.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wnat_rec::…` all still resolve. Read the header of the one file you
//! need.
//!
//! | file | what it holds |
//! |---|---|
//! | [`step`] | the terms, and the step symbol `e(z,s,T)` as one Replacement |
//! | [`members`] | what is in the step, and what is not |
//! | [`values`] | the step's values, and hence that it is a function |
//! | [`computes`] | the step's two computation rules — the non-vacuity witness |
//! | [`typed`] | [`premise`], and that the step lands in the motive |
//! | [`iota`] | the two ι rules, `iota_zero` and `iota_succ` |
//! | [`recursor`] | [`NatRec`] — the whole thing, packaged |
//!
//! `shared` holds the two private combinators more than one of them needs; it
//! exports no theorem and is not re-exported.

pub mod computes;
pub mod iota;
pub mod members;
pub mod recursor;
mod shared;
pub mod step;
pub mod typed;
pub mod values;

pub use recursor::{premise_witness, NatRec};
pub use step::{key_succ, key_zero, payload, pow_prod, value_packed, value_succ, StepSyms};
pub use typed::premise;

// ─────────────────────────────────────────────────────────────────────────────
// Closing notes — 2026-07-31
//
// ## What is done
//
// The derived side of `N.rec` is complete. `NatRec::over` returns, at fresh
// `z`, `s`, `T` and `n`, with `HYP := z ∈ T ∧ s ∈ fs(N, fs(T,T))`:
//
//   app_zero    ⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z
//   app_succ    ⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) →
//                     app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩)
//                        = app(app(s, app(f,•)), app(r,•)))
//   sv          ⊢ ∀z ∀s ∀T. sv(e(z,s,T))
//   step_typed  ⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))
//   iota_zero   ⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)
//   iota_succ   ⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) →
//                     app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩)
//                        = app(app(s,n), app(nrec(z,s,T), n)))
//
// `iota_succ` is the point of the file: its right-hand side mentions `nrec`
// again, which no `Bool` equation could. `HYP` is discharged at a concrete
// instance by `premise_witness`, so none of these is a statement about an
// unsatisfiable antecedent, and `tests/wnat_rec.rs` pins all six plus that
// discharge.
//
// ## The backend, wired — 2026-07-31
//
// All four items below are done in `checker/src/tg.rs`, and `075_nRecReduction`
// went **54 gaps / 0 escapes → 4 gaps / 1 escape** with all six ι gaps closed.
//
// 1. **`nat_recursor()` beside `bool_recursor()`.** The shared prefix came out
//    as its own `RecCore` — `Recursor::new` + `wrec_extend::extension` +
//    `totality` + `iota` + `wrec_funspace` — which is the expensive half of
//    `derived` and mentions no tag set at all, so both recursors sit on one
//    copy. `Inductives` gained the `PointFun` field, because `NatRec::over`
//    insists on the very one `Nat` was built over.
//
// 2. **`rec_nest`'s bottom made pluggable**, as `RecBottom`. The depth is now
//    `major_idx + 1` rather than a hand-unrolled four, and every level carries
//    *all* the arguments above it (`prefixes[k] = 0..k`) rather than only the
//    ones its body mentions — `Bool`'s bottom ignores the motive but `N`'s does
//    not, since `T` **is** the motive at `N.zero`. That uniformity is what makes
//    the nest independent of its bottom, and is the whole of what `List.rec`
//    needs from the nest.
//
// 3. **`derive_iota` generalised** on both counts. Trailing arguments are split
//    off first, the equation derived at the *core* — the recursor applied to
//    exactly its own arguments — and lifted back by congruence, with the guard
//    still comparing against the full redex and reduct. The major premise is
//    `unfold_apps`ed, so `N.succ n` is a constructor with a field.
//
// 4. **`HYP` supplied at the point of use.** `⟦z⟧ ∈ T` is literally the
//    level-2 domain obligation, handed back by `nest_chain` rather than asked
//    twice; `⟦s⟧ ∈ fs(⟦N⟧, fs(T,T))` is asked at that kernel term and
//    transported to `fs(W,·)` along `⊢ ⟦N⟧ = W(1+1,B,U(1+1))`, so the
//    *assumption*, if it survives, is still stated at the abbreviation and can
//    still be discharged at a binder. `⟦n⟧ ∈ ⟦N⟧` likewise.
//
// Two things outside `N.rec` had to be fixed on the way, both older than any of
// this and both found by an ι certificate finally reaching them.
// `TgBackend::derive_beta` counted its contractions on the *substituted* head
// rather than on the syntactic lambda nesting, so where the checker stops after
// three (`(λ motive zero succ. zero) C z s m` leaves `fun m => m` in head
// position) the backend took a fourth and proved a different equation — caught
// by its own guard, three times on `075`, and reported as a gap. And
// `TypeChecker::recall_reduction` had nothing to recall when a reduct had been
// memoised by an uncertified `whnf` call; it now re-runs the reduction and uses
// the certificate **only if it lands on the memoised reduct**, so what the
// checker returns is unchanged.
//
// ## The trap, and how it actually landed
//
// `075`'s motive `fun x : N => (∀ _ : N, N)` is a **closed** term whose typing
// wants `fs(N,N) ∈ U(⟦Sort 0⟧)`, underivable with this `Sort` encoding and
// dischargeable at no binder. That did happen: the file's one escaping
// certificate carries exactly `⟦motive⟧ ∈ ⟦N → Sort 1⟧`, together with the succ
// minor's typing at both `doms[2]` and `fs(⟦N⟧,fs(T,T))`.
//
// What did **not** happen is the rest of the prediction. The expectation was
// the `073`-first-stage pattern — most gaps close, several escapes appear.
// Exactly **one** escape appeared, and it absorbed three assumptions rather
// than becoming three gaps, because a conditional certificate with nothing
// admitted beneath it is one gap however far it travels. The corrected rule
// from the `Bool` entry — "an admit poisons every rule above it one at a time;
// conditionality does not" — turns out to be the dominant effect, not a caveat.
//
// Staged, so the credit is honest: the ι wiring alone took `075` **54 → 33**,
// `derive_beta`'s contraction count **33 → 12**, and the `whnf` recall
// **12 → 4**. The last two are not about inductives, and the first two of the
// four that remain are `pi_cong`'s extensionality route.
//
// A second trap, and it is real: `T` must be `doms[1]` *as the nest computes
// it*, not a term rebuilt here. `075`'s motive is constant so `app(⟦C⟧,⟦N.zero⟧)`
// beta-reduces to `fs(⟦N⟧,⟦N⟧)`, but the two sides of the iota equation can only
// share their assumptions if both go through `interp` on the same Lean types —
// which is exactly why `RecNest`'s domains are walked off the recursor's own
// type rather than reconstructed. The nest's bottom therefore names `doms[1]`
// and `fire_nat` reads `T` from the same place.
//
// ## Cost, measured
//
// ~1050 lines here and ~300 in `crate::proj`, for 12 tests
// (`tests/wnat_rec.rs` 7, `tests/proj.rs` 5). `derived` 358 → 370.
//
// The single most useful thing built was `crate::proj`. Every lemma between
// `row_packed` and `unpack` is stated at the **packed** payload and mentions no
// component, so a constructor with an extra field costs one more `π` in
// `value_packed` and changes nothing else. The first version of this file
// projected with nested existentials instead, one Replacement layer per
// component; it worked, and every one of those lemmas would have had to be
// rewritten for `List.cons`. That is the whole argument for the projections,
// and it is recorded in the header under the extend-or-replace test.
//
// **That claim was cashed on 2026-07-31 and it held.** `crate::wlist_rec` is
// this file with `h` threaded through as an inert extra argument: `step_cases`,
// `value_at_packed`, `value_at_zero` and `step_single_valued` did not change
// shape, and `value_packed` gained exactly one application. What the claim did
// not cover is that `List`'s *tag* varies — `inr h` where `N`'s is the constant
// `inr •` — so the Replacement ranges over `prod(α, P(α,T))` and one projection
// appears at the Replacement itself. It stays confined there; see that file'"'"'s
// closing notes for why, which is the one real design decision it contains.
