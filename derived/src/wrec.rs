//! The **W-type recursor**, by union of attempts, and its **ι rule**.
//!
//! # Status: steps 1–6 are derived
//!
//! This file holds steps 1–3 and 6 of `INDUCTIVES.md`'s recipe. **Totality —
//! step 4 — is no longer open**: it is [`crate::wrec_total::totality`], run on
//! the one-point extension of [`crate::wrec_extend`], and with it come
//! `wrec ∈ fs(W,T)` and the **unguarded** ι rule. What survives as a hypothesis
//! there, and cannot be removed, is a typing side condition on the step `e`
//! that the design note does not mention:
//!
//! ```text
//! step_typed := ∀a ∈ A. ∀f ∈ fs(B(a),W). ∀r ∈ fs(B(a),T). app(e,⟨a,⟨f,r⟩⟩) ∈ T
//! ```
//!
//! See the closing notes at the bottom of this file. Step 7 — uniqueness, and
//! hence introducing `wrec` through `define` rather than `define_abbrev` — is
//! the only one left.
//!
//! **ι fires.** Everything in *this* file would still be provable if `wrec`
//! were `∅`. [`crate::wrec_unit`] rules that out, without needing totality: at
//! `A := {c}`, `B := ∅`, `u := U(c)` and `T := {app(e,⟨c,⟨∅,∅⟩⟩)}` it derives
//!
//! ```text
//! ⊢ ⟨⟨c,∅⟩, app(e,⟨c,⟨∅,∅⟩⟩)⟩ ∈ wrec({c},∅,U(c),T,e)   [wrec_unit::wrec_member]
//! ⊢ app(wrec({c},∅,U(c),T,e), ⟨c,∅⟩) = app(e, ⟨c,⟨∅,∅⟩⟩) [wrec_unit::iota_fires]
//! ```
//!
//! — unconditional, both sides computed, the two sides distinct terms. The
//! same instance discharges `step_typed` ([`crate::wrec_unit::unit_step_typed`])
//! and yields the unconditional `⊢ wrec ∈ fs(W,T)` there, so the general
//! theorems are not statements about an unsatisfiable antecedent; and
//! [`crate::wrec_unit::unit_iota`] fires the *general* ι rule at that instance
//! and lands on literally the equation `iota_fires` proves by hand.
//!
//! # Notation
//!
//! `W` is `W(A,B,u)` ([`crate::wtype`]), `⟨x,y⟩` the Kuratowski pair, `app`
//! set-theoretic application ([`crate::funcs`]), `fs(X,Y)` the function space,
//! `prod(X,Y)` the Cartesian product, `B(a)` the fibre `app(B,a)`, and
//! `closed(A,B,u)` the W-type's bound hypothesis ([`crate::wtype::closed`]) —
//! which is *not* irreducible: at `u := U(c)` it is discharged by
//! [`crate::bound::least_universe_closed`], via
//! [`crate::bound::discharge_closed`], leaving only `A ∈ U(c)` and
//! `∀a ∈ A. B(a) ∈ U(c)`.
//!
//! Three abbreviations are used throughout, all built here as formulas so that
//! callers can rebuild and compare them:
//!
//! ```text
//! indom(g,x)       := ∃y. ⟨x,y⟩ ∈ g                             [indom]
//! agree_on(g,h,f,d):= ∀b. (b ∈ d → app(g,app(f,b)) = app(h,app(f,b)))
//!                                                                [agree_on]
//! rec_cond(B,e,g)  := ∀a ∀f. (indom(g,⟨a,f⟩) →
//!                       ((∀b. (b ∈ B(a) → indom(g, app(f,b))))
//!                        ∧ app(g,⟨a,f⟩) = app(e, ⟨a,⟨f, comp(g,f,B(a))⟩⟩)))
//!                                                                [rec_cond]
//! ```
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀f ∀d ∀p. (p ∈ comp(g,f,d) ↔ ∃b. (b ∈ d ∧ p = ⟨b, app(g,app(f,b))⟩))
//!                                                                [compose]
//! ⊢ ∀g ∀h ∀f ∀d. (agree_on(g,h,f,d) → comp(g,f,d) = comp(h,f,d))
//!                                                                [compose_ext]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g.
//!       (g ∈ Att ↔ (g ∈ 𝒫(prod(W,T)) ∧ (sv(g) ∧ rec_cond(B,e,g))))
//!                                                                [attempts]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. ∅ ∈ Att                                      [empty_attempt]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀z. (z ∈ W → ∀g ∀h. ((g ∈ Att ∧ h ∈ Att) →
//!             ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z)))))
//!                                                                [agreement]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. wrec(A,B,u,T,e) = ⋃ Att(A,B,u,T,e)           [wrec_symbol]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀p. (p ∈ wrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))        [wrec_members]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ wrec)  [attempt_subset_wrec]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g. (g ∈ Att →
//!       ∀x. (indom(g,x) → indom(wrec,x)))                 [attempt_indom_wrec]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. wrec ⊆ prod(W,T)                      [wrec_subset_prod]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → sv(wrec))            [wrec_single_valued]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(wrec,x) = app(g,x))))
//!                                                                [wrec_value]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → rec_cond(B,e,wrec))   [wrec_rec_cond]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → wrec ∈ Att)           [wrec_is_attempt]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀a ∀f. (indom(wrec, ⟨a,f⟩) →
//!           app(wrec, ⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩)))
//!                                                                [iota_on_domain]
//! ```
//!
//! `sv(g)` is [`crate::funspace::is_single_valued`]. Callers need none of the
//! derivations below; the statements above are the whole contract.
//!
//! # Why union of attempts, and not rank
//!
//! `INDUCTIVES.md` records the departure: Carneiro defines the recursor by
//! transfinite recursion on rank, which would mean developing ordinals. The
//! union-of-attempts construction lands in the same place and needs only `W2`
//! (structural induction), which [`crate::wtype::w_rect`] already provides.
//! Nothing here is an axiom: one Replacement (for `comp`), one Separation (for
//! `Att`), one union, and two explicit definitions.
//!
//! # Representation, and why
//!
//! **The step is applied flat.** The design note writes the recursion equation
//! as `F(⟨a,f⟩) = e(a)(f)(F ∘ f)`, three curried set-applications. Each `app`
//! in a chain costs a separate beta obligation at the point of use, so the step
//! is instead applied to a single Kuratowski triple:
//!
//! ```text
//! app(e, ⟨a, ⟨f, comp(F,f,B(a))⟩⟩)
//! ```
//!
//! `comp(g,f,d)` is `g ∘ f` restricted to `d`, i.e. `{ ⟨b, g(f b)⟩ : b ∈ d }`,
//! and is a Replacement along `b ↦ ⟨b, app(g,app(f,b))⟩` — the same shape as
//! [`crate::funcs::lambda`], which cannot be reused because it takes a *unary
//! function symbol* and the body here mentions the two parameters `g` and `f`.
//!
//! **The domain is a parameter of the composite, not read off `f`.** There is
//! no domain operator in this crate, and the recursion equation always has
//! `B(a)` to hand, so `comp` takes it. That also keeps `comp` free of any
//! well-definedness side condition: it is a total operation on three arbitrary
//! sets. The only fact about it the recursor needs is [`compose_ext`] — no beta
//! rule, because the recursion equation never *applies* a composite, it only
//! compares two of them.
//!
//! **Attempts are described with `app`, not with graph membership.** An attempt
//! is a set `g` of pairs, and the two natural phrasings of "the recursion
//! equation holds at `w ∈ dom g`" are
//!
//! ```text
//! ∀y. (⟨w,y⟩ ∈ g → y = app(e, …))        and        app(g,w) = app(e, …)
//! ```
//!
//! The second is used. The reason is the agreement proof: it runs by structural
//! induction with the hypothesis *"`g` and `h` agree at every subterm"*, and
//! with the first phrasing that hypothesis has to be destructured — an
//! existential witness for each of `g` and `h`, eliminated under the induction's
//! ambient hypothesis — before the two values can be compared. With the second
//! it is an equation between terms and composes directly. Measured effect: the
//! induction step of [`agreement`] needs *no* existential elimination at all.
//! `dom g` itself stays unnamed: `indom(g,x)` is only ever introduced
//! (`indom_intro`) or passed along, never taken apart inside the induction.
//!
//! Single-valuedness is still part of being an attempt, because the union has
//! to be a function for `app(wrec,·)` to mean anything; it is simply not needed
//! *inside* the induction.
//!
//! **`wrec` is an explicit definition, not a `define` with an `∃!` premise.**
//! `wrec(A,B,u,T,e) := ⋃ Att(A,B,u,T,e)` is a term, so
//! [`crate::define_abbrev`] introduces it for nothing. The unique-existence
//! statement that `INDUCTIVES.md`'s route 2 wants — "the unique function on `W`
//! satisfying ι" — is then a *theorem* about this symbol rather than the
//! premise of its introduction, which is strictly more informative: a caller
//! that prefers the implicit form can feed the theorem to
//! [`kernel::thm::define`]. That theorem is **not yet derived**; see the
//! closing notes.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wrec::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need — the Interface
//! block above is reproduced there, step by step.
//!
//! | file | step | what it exports |
//! |---|---|---|
//! | [`composite`] | 1 | the symbol `comp(g,f,d)`, [`agree_on`], and [`compose_ext`] |
//! | [`attempt`] | 2 | [`indom`], [`rec_cond`], and the symbol `Att(A,B,u,T,e)` |
//! | [`agree`] | 3 | any two attempts agree, by structural induction |
//! | [`union`] | 4 | the symbol `wrec = ⋃ Att`, its members, its values, and that it is a function |
//! | [`is_attempt`] | 5–6 | `wrec ∈ Att`, `∅ ∈ Att`, and ι on the recursor's domain |
//!
//! `hyp` holds the private `H → …` combinators and formula readers that more
//! than one of them needs; four of them are re-exported `pub(crate)` because
//! eight other modules in this crate import them, but it exports no theorem.

pub mod agree;
pub mod attempt;
pub mod composite;
mod hyp;
pub mod is_attempt;
pub mod union;

pub use agree::{agree_formula, agreement};
pub use attempt::{
    att_of, attempt_bound, attempt_cond, attempts, indom, rec_cond, step_at,
};
pub use composite::{agree_on, comp_of, compose, compose_ext};
pub use is_attempt::{empty_attempt, iota_on_domain, wrec_is_attempt, wrec_rec_cond};
pub use union::{
    attempt_indom_wrec, attempt_subset_wrec, wrec_members, wrec_of, wrec_single_valued,
    wrec_subset_prod, wrec_symbol, wrec_value,
};

pub(crate) use hyp::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim};

// ─────────────────────────────────────────────────────────────────────────────
// Closing notes — 2026-07-31, third pass.
//
// Totality landed. What is left is step 7, and it is optional.
// ─────────────────────────────────────────────────────────────────────────────
//
// ## Against `INDUCTIVES.md`'s seven steps
//
// | step | status |
// |---|---|
// | 1. attempts form a set | **done** — `attempts`, one `separation_full` |
// | 2. any two attempts agree | **done** — `agreement`, by `wtype::w_rect` |
// | 3. `F := ⋃Att` is a function, and is an attempt | **done** — `wrec_single_valued`, `wrec_rec_cond`, `wrec_is_attempt` |
// | 4. `F` is total on `W` | **done** — `crate::wrec_total::totality`, on `crate::wrec_extend::extension` |
// | 5. `F ∈ fs(W,T)` | **done** — `crate::wrec_total::wrec_funspace` |
// | 6. ι | **done, unguarded** — `crate::wrec_total::iota`; `iota_on_domain` here is the guarded form it is built on |
// | 7. uniqueness, and the `∃!` | **not done**. `wrec` is still introduced by `define_abbrev`, not by `define` |
//
// Everything in steps 4–6 carries two hypotheses and no others:
// `closed(A,B,u)`, the W-type's own bound condition, discharged at `u := U(c)`
// by `crate::bound`; and `step_typed`, the typing side condition on the step,
// which is **not** a defect of the construction — see below. Both are
// discharged outright at the unit instance. No new axioms, no `admit`, nothing
// added to `kernel/`.
//
// ## The three theorems, exactly
//
// Writing `H` for `closed(A,B,u) ∧ step_typed(A,B,u,T,e)`:
//
// ```text
// ⊢ ∀A ∀B ∀u ∀T ∀e. (H → ∀z. (z ∈ W → indom(wrec, z)))       [wrec_total::totality]
// ⊢ ∀A ∀B ∀u ∀T ∀e. (H → wrec ∈ fs(W, T))               [wrec_total::wrec_funspace]
// ⊢ ∀A ∀B ∀u ∀T ∀e. (H → ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W)) →
//       app(wrec,⟨a,f⟩) = app(e, ⟨a,⟨f, comp(wrec,f,B(a))⟩⟩)))    [wrec_total::iota]
// ```
//
// The last is `iota_on_domain` with its guard discharged, and nothing else:
// `⟨a,f⟩ ∈ W` by W1, then `indom(wrec,⟨a,f⟩)` by totality. That is the whole
// of the ι rule, and it is why `iota_on_domain` was stated separately in the
// first place.
//
// ## Non-vacuity, and why it has teeth here
//
// `step_typed` is a hypothesis nothing in the construction discharges — `e` is
// an arbitrary set — so a totality theorem could have been about an antecedent
// no five sets satisfy. `crate::wrec_unit::unit_step_typed` closes that:
//
// ```text
// ⊢ step_typed({c}, ∅, U(c), {V}, e)                with V := app(e,⟨c,⟨∅,∅⟩⟩)
// ⊢ wrec({c},∅,U(c),{V},e) ∈ fs(W({c},∅,U(c)), {V})    [wrec_unit::unit_funspace]
// ```
//
// The second has **no antecedent at all**. It holds for a reason that does not
// generalise, and that is the point: the fibre `B(a) = app(∅,a)` is `∅`, and
// `∅` is the only function out of `∅` (`wtype::empty_funspace`), so `f` and `r`
// are forced and the step's value is the closed term `V`.
//
// There is a second check, and it is the one worth keeping: `wrec_unit::unit_iota`
// fires the *general* ι rule at that instance — discharging `H`, supplying
// `c ∈ {c}` and `∅ ∈ fs(B(c),W)`, collapsing the composite — and lands on
// **literally the formula** `wrec_unit::iota_fires` proves by hand from a
// one-point attempt. Two independent routes to the same equation; `tests/wrec_total.rs`
// asserts they agree. If they ever stop agreeing, one of them is about a
// different recursor.
//
// ## What step 4 actually cost, and where the trap was
//
// `crate::wrec_extend` is ~1090 lines for one lemma: `G := wrec ∪ {⟨⟨a,f⟩,V⟩}`
// is an attempt. Three clauses, and the cost is not evenly spread.
//
// * **`G ⊆ prod(W,T)`** is short, and is the *only* place `step_typed` is
//   spent. Its third premise, `comp(wrec,f,B(a)) ∈ fs(B(a),T)`, is
//   `wrec_typing::wrec_composite_typed` applied to the induction hypothesis —
//   that lemma exists for no other reason and drops straight in, exactly as the
//   previous pass predicted.
// * **`sv(G)`** is where the design has to be right. The note before last said
//   "no case analysis on whether `⟨a,f⟩` is already in `dom wrec`", and that is
//   correct and load-bearing: `wrec_rec_cond` forces the old value to *be* `V`,
//   not merely to be compatible with it. The note then said a **two-way split
//   on `x = ⟨a,f⟩`** was unavoidable. That turned out to be one framing of the
//   right idea but not the cheapest one. What is actually needed is the lemma
//   `⊢ K → ∀y. (⟨⟨a,f⟩,y⟩ ∈ G → y = V)` (`value_at_new_point`), and with it in
//   hand the four cases collapse to **three** with no excluded-middle split
//   anywhere: if either pair is the new one, `opair_inj` gives `x = ⟨a,f⟩` and
//   that lemma types the *other* value; only when both came from `wrec` is
//   `sv(wrec)` used. So: the correction was right about the mechanism and
//   pessimistic about the shape.
// * **`rec_cond(G)`** is the long half, as predicted. Two cases; both need
//   `compose_ext`, whose `agree_on` premise is `agreement` — `wrec` and `G`
//   agree wherever `wrec` is defined, because `wrec ⊆ G` and `G` is
//   single-valued. The one thing worth writing down: the new-point case proves
//   its goal at `a` and `f` and **carries it back** along `a′ = a`, `f′ = f`
//   with two Leibniz steps. Rewriting the hypotheses forwards instead means
//   rebuilding the goal formula by hand and hoping it matches; carrying it back
//   makes the two instances the same closure applied to two terms, which cannot
//   drift. It went through on the first compile.
//
// The induction itself, once the step exists, is about forty lines:
// `wtype::w_rect` at `φ(z) := indom(wrec,z)`, with the four conjuncts of the
// step's hypothesis peeled off one at a time. That peeling is why
// `wrec_extend::hypothesis` is left-nested in the order it is — `uncurry`
// takes them off in exactly the order `ind_step` wants them back.
//
// ## Step 7: uniqueness, and why it is still worth doing
//
// By `w_rect` at
// `φ(z) := ∀k. ((k ∈ fs(W,T) ∧ ι-holds-for-k) → app(k,z) = app(wrec,z))` —
// structurally the same induction as `agreement`, and every piece of plumbing
// it needs is now in place, including the two facts that were missing when this
// was last written: `wrec ∈ fs(W,T)` and unguarded ι. It is what turns the ι
// rule into a *characterisation*, and hence what would let a caller introduce
// the recursor through `kernel::thm::define` instead of `define_abbrev`.
//
// It is **optional**, and deliberately left. `define_abbrev` is an explicit
// definition and already a conservative extension; `define`'s `∃!` obligation
// would make the symbol a definitional extension in the stronger sense, which
// is a real improvement but not one anything downstream is currently blocked
// on. The checker backend needs ι, and ι is done.
//
// ## Cost, measured
//
// 33 tests across `tests/wrec.rs` (23) and `tests/wrec_total.rs` (10).
// ~1800 lines here for steps 1–3 and 6; ~1090 in `crate::wrec_extend` for the
// induction step; ~470 in `crate::wrec_total` for the induction and its two
// consequences; ~970 in `crate::wrec_unit`, of which ~300 are the new
// `step_typed` discharge and the cross-check; ~520 in `crate::wrec_typing`.
//
// The dominant cost is still assembling implications from combinators, and the
// four helpers `hyp_eq_symm`, `hyp_eq_trans`, `hyp_congr` and `hyp_exists_elim`
// are still what makes it tractable. Two more earned their place this pass and
// are private to `wrec_extend`: `gen_under` (from `⊢ H → φ` infer
// `⊢ H → ∀v. φ`), which appears eleven times, and `hyp_leibniz`, which is what
// carries a goal across an equation under a hypothesis. Anything that has to
// generalise under an ambient hypothesis wants the first; anything that has to
// substitute under one wants the second.
