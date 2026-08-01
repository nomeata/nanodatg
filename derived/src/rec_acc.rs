//! The **accessibility recursor** `rec_acc(A,R,e)`, by union of attempts, and
//! its **ι rule**.
//!
//! # Status: the recursor is total and ι fires, unguarded
//!
//! Carneiro's *The Type Theory of Lean* §6.2.2 (thesis.txt:2160–2166) defines
//!
//! ```text
//! rec_acc(A,R,e) = (x ∈ A ↦ (h ∈ [x ∈ acc(A,R)] ↦ F(x)))
//! F : acc(A,R) → V,  F(x) = e(x)(•)(y ∈ A ↦ (h ∈ [⟨y,x⟩ ∈ R] ↦ F(y)))
//! ```
//!
//! and `⟦rec_acc e⟧ = rec_acc(⟦α⟧,⟦r⟧,⟦e⟧)` (thesis.txt:2129). Both objects are
//! built here: `F` is [`union`]'s `accrec(A,R,T,e)`, the packaging is
//! [`package`]'s `pack(A,R,T,e)`, and [`total::iota`] / [`package::pack_iota`]
//! are the recursion equation at each spelling.
//!
//! **The thesis's `F` has no target set and this one does.** Carneiro defines
//! `F : acc(A,R) → V` by transfinite recursion on rank into the whole universe;
//! this development follows [`crate::wrec`]'s ordinal-free union-of-attempts
//! route, which needs a *set* to bound the attempts, so `T` is a fourth
//! parameter and the step must be typed into it. That is the same correction
//! `INDUCTIVES.md` records for `wrec` — "totality is not free, the step must be
//! typed into `T`" — and it is the **only** hypothesis anywhere in this module.
//! There is no analogue of `wrec`'s second hypothesis `closed(A,B,u)`: `W` needs
//! a bound because `W(A,B,u)` is a subset of nothing already named, whereas
//! `acc(A,R) ⊆ A` by construction. Everything up to and including the guarded ι
//! rule is therefore **unconditional**, where the corresponding `wrec` theorem
//! carries `closed(A,B,u)`.
//!
//! # Notation
//!
//! ```text
//! acc(A,R)             the accessibility carrier (crate::acc)
//! ⟨y,x⟩                the Kuratowski pair; ⟨y,x⟩ ∈ R means "y precedes x"
//! app(f,a), fs, prod   application, function space, product (crate::funcs, crate::funspace)
//! 1, •                 the unit set and its point (crate::sums)
//! [φ]                  the conditional singleton { z ∈ 1 : φ } (crate::prop)
//! sv(g)                crate::funspace::is_single_valued
//! indom(g,x)           ∃y. ⟨x,y⟩ ∈ g  (crate::wrec::indom, shared)
//!
//! cval(c,v)            := prod(c, {v})                   — the function h ∈ c ↦ v
//! ep(R,y,x)            := [⟨y,x⟩ ∈ R]
//! ih(g,A,R,x)          := { ⟨y, cval(ep(R,y,x), app(g,y))⟩ : y ∈ A }
//! step(e,x,i)          := app(app(app(e,x),•), i)        — Carneiro's e(x)(•)(i)
//! ih_bound(A,T)        := 𝒫(prod(A, 𝒫(prod(1,T))))
//!
//! preds_indom(A,R,g,x) := ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → indom(g,y)))
//! rec_cond(A,R,e,g)    := ∀x. (indom(g,x) →
//!                           (preds_indom(A,R,g,x) ∧ app(g,x) = step(e,x,ih(g,A,R,x))))
//! step_typed(A,R,T,e)  := ∀x. (x ∈ acc(A,R) →
//!                           ∀i. (i ∈ ih_bound(A,T) → step(e,x,i) ∈ T))
//!
//! Att(A,R,T,e)         := { g ∈ 𝒫(prod(acc(A,R),T)) : sv(g) ∧ rec_cond(A,R,e,g) }
//! accrec(A,R,T,e)      := ⋃ Att(A,R,T,e)                                    — F
//! accprop(A,R)         := prod(acc(A,R), {•})
//! pack(A,R,T,e)        := ih(accrec(A,R,T,e), A, accprop(A,R), •)  — the thesis's rec_acc
//! ```
//!
//! # Interface
//!
//! Writing `ST` for `step_typed(A,R,T,e)` and eliding the leading
//! `∀A ∀R ∀T ∀e`:
//!
//! ```text
//! ── the pieces ──────────────────────────────────────────────────────────────
//! ⊢ ∀R ∀y ∀x ∀z. (z ∈ ep(R,y,x) ↔ (z ∈ 1 ∧ ⟨y,x⟩ ∈ R))              [edge_prop]
//! ⊢ ∀c ∀v. (• ∈ c → app(cval(c,v), •) = v)                           [cval_app]
//! ⊢ ∀c ∀u ∀v. ((∀h. (h ∈ c → u = v)) → cval(c,u) = cval(c,v))        [cval_ext]
//! ⊢ ∀c ∀u ∀d ∀t. ((∀h. (h ∈ c → (h ∈ d ∧ u ∈ t))) →
//!       cval(c,u) ⊆ prod(d,t))                                     [cval_bound]
//! ⊢ ∀g ∀A ∀R ∀x ∀p. (p ∈ ih(g,A,R,x) ↔
//!       ∃y. (y ∈ A ∧ p = ⟨y, cval(ep(R,y,x), app(g,y))⟩))           [ih_symbol]
//! ⊢ ∀g ∀h ∀A ∀R ∀x. (preds_agree(g,h,A,R,x) → ih(g,A,R,x) = ih(h,A,R,x))
//!                                                                     [ih_ext]
//! ⊢ ∀g ∀A ∀R ∀T ∀x. (preds_typed(g,A,R,T,x) →
//!       ih(g,A,R,x) ∈ ih_bound(A,T))                                [ih_typed]
//! ⊢ ∀g ∀A ∀R ∀x. sv(ih(g,A,R,x))                          [ih_single_valued]
//! ⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) →
//!       app(app(ih(g,A,R,x), y), •) = app(g,y))                       [ih_app]
//!
//! ── the recursor ────────────────────────────────────────────────────────────
//! ⊢ ∀g. (g ∈ Att ↔ (g ∈ 𝒫(prod(acc(A,R),T)) ∧ (sv(g) ∧ rec_cond(A,R,e,g))))
//!                                                                   [attempts]
//! ⊢ ∅ ∈ Att                                                   [empty_attempt]
//! ⊢ ∀z. (z ∈ acc(A,R) → ∀g ∀h. ((g ∈ Att ∧ h ∈ Att) →
//!       ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z))))        [agreement]
//! ⊢ accrec = ⋃ Att                                              [rec_symbol]
//! ⊢ ∀p. (p ∈ accrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))                   [rec_members]
//! ⊢ ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ accrec)             [attempt_subset_rec]
//! ⊢ ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(accrec,x)))   [attempt_indom_rec]
//! ⊢ accrec ⊆ prod(acc(A,R),T)                              [rec_subset_prod]
//! ⊢ sv(accrec)                                           [rec_single_valued]
//! ⊢ ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(accrec,x) = app(g,x)))  [rec_value]
//! ⊢ rec_cond(A,R,e,accrec)                                    [rec_rec_cond]
//! ⊢ accrec ∈ Att                                            [rec_is_attempt]
//! ⊢ ∀x. (indom(accrec,x) → app(accrec,x) = step(e,x,ih(accrec,A,R,x)))
//!                                                           [iota_on_domain]
//!
//! ── what totality costs ─────────────────────────────────────────────────────
//! ⊢ (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))                   [totality]
//! ⊢ (ST → accrec ∈ fs(acc(A,R), T))                           [rec_funspace]
//! ⊢ (ST → ∀x. (x ∈ acc(A,R) →
//!       app(accrec,x) = step(e,x,ih(accrec,A,R,x))))                   [iota]
//!
//! ── the thesis's packaging ──────────────────────────────────────────────────
//! ⊢ ∀x. (x ∈ acc(A,R) → app(app(pack,x),•) = app(accrec,x))       [pack_app]
//! ⊢ (ST → ∀x. (x ∈ acc(A,R) →
//!       app(app(pack,x),•) = step(e,x,ih(accrec,A,R,x))))         [pack_iota]
//! ```
//!
//! [`RecAcc`] bundles every symbol and every theorem; callers read them off the
//! struct and never call the sibling files directly.
//!
//! # Representation, and why
//!
//! **The step is applied curried, with `•` in the middle.** [`crate::wrec`]
//! flattens its step to `app(e, ⟨a,⟨f,r⟩⟩)`, on the grounds that each `app` in a
//! chain costs a beta obligation at the point of use. The trade is different
//! here: `W`'s step is a *packed* object assembled from `n` minor premises, so
//! its argument order is the construction's own choice, whereas `acc` has one
//! introduction rule and `e` **is** Lean's minor premise. Keeping Carneiro's
//! `e(x)(•)(ih)` makes thesis.txt:2129 literally true and matches the curried
//! lambda-nest a checker backend produces anyway. The `•` is
//! `⟦intro_acc x f⟧ = •` (thesis.txt:2127); it carries no information and is
//! deliberately *not* dropped, since dropping it would change `e`'s arity and so
//! derive a true equation about a term no backend produces.
//!
//! **The proof-indexed abstractions are Cartesian products.** A constant
//! function on a proposition `c` with value `v` is exactly `c × {v}`, so
//! [`cval`] mints **no symbol at all** — it is a term over
//! [`crate::funspace::Product`], whose membership condition is already
//! unconditional. Both of the thesis's abstractions (`h ∈ [⟨y,x⟩ ∈ R] ↦ F(y)`
//! and `h ∈ [x ∈ acc(A,R)] ↦ F(x)`) are instances, which is also why
//! [`package`] needs no Replacement: `pack` is [`ih`] at the relation
//! `acc(A,R) × {•}`.
//!
//! **The two lemmas about `cval` are guarded by `h ∈ c`, not by `φ`.** Off the
//! relation two attempts need not agree and the values need not be typed; there
//! the conditional value is empty, so guarding the premises by inhabitation
//! covers both cases in one derivation and **no case analysis on the proposition
//! is performed anywhere in the module**. See [`cval`].
//!
//! **`step_typed` quantifies over a power set, not a function space.**
//! `ih_bound(A,T) = 𝒫(prod(A, 𝒫(prod(1,T))))` contains `∅` as happily as it
//! contains a total function, so no attempt ever has to be proved total to be
//! usable — the `pow_prod` superset trick `RECURSOR-DESIGN.md` §3.2 records for
//! the general W-recursor. It also makes `step_typed` a *weaker* hypothesis than
//! the function-space form, hence the theorems stronger.
//!
//! # Non-vacuity
//!
//! Two independent checks, both in [`witness`] and [`ih`]:
//!
//! ```text
//! ⊢ step_typed(1,∅,1,∅)                                  [unit_step_typed]
//! ⊢ ∃w. ⟨•,w⟩ ∈ accrec(1,∅,1,∅)                     [unit_facts, in_domain]
//! ⊢ app(accrec(1,∅,1,∅), •) = ∅                          [unit_facts, iota]
//! ⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) →
//!       app(app(ih(g,A,R,x), y), •) = app(g,y))                    [ih_app]
//! ```
//!
//! The first three are **closed and unconditional**: `step_typed` is a
//! hypothesis nothing in the construction discharges, so [`total`]'s theorems
//! could have been about an unsatisfiable antecedent, and everything in
//! [`is_attempt`] would still hold with `accrec = ∅`. The fourth is what stops
//! ι from being a statement about an opaque set: at `g := accrec` it says the
//! third argument of the step, applied to a predecessor and to the proof that it
//! *is* one, is the recursive value `app(accrec,y)`.
//!
//! # "No antecedent at all" means the sequent, not just the formula
//!
//! A [`kernel::Thm`] is `Γ ⊢ φ`. Every claim above — "everything up to and
//! including the guarded ι rule is **unconditional**", "`ST` is the only
//! hypothesis in the module", and above all "**every one of these has no
//! antecedent at all**" about the four closed witnesses — is a claim that `Γ` is
//! *empty*. An antecedent spelled out inside `concl()`, as in `ST → …`, is
//! honest; a formula sitting in `hyps()` is not, and [`kernel::Thm::mp`] puts one there
//! silently the moment a premise carries it.
//!
//! So every entry in this module that takes a `&Thm` checks `hyps().is_empty()`
//! as well as pinning what it can of the conclusion, and each apparatus struct
//! offers the same check over the theorems it carries — [`Base::all_unconditional`],
//! [`RecAcc::all_unconditional`], [`is_attempt::UnionFacts::all_unconditional`],
//! [`total::Machinery::all_unconditional`], [`witness::UnitInputs::all_unconditional`]
//! and [`extend::Ext::inputs_unconditional`]. All of those fields are `pub`, so
//! the check belongs at each consumer boundary and not only at construction.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::rec_acc::…` all resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`cval`] | the conditional value `cval(c,v) = c × {v}` — the interpretation of `h ∈ [φ] ↦ v` |
//! | [`ih`] | `ep(R,y,x)`, the induction hypothesis `ih(g,A,R,x)`, and its beta rule |
//! | [`base`] | [`Base`] — the shared apparatus every later file is stated over |
//! | [`attempt`] | `indom`, `rec_cond`, the symbol `Att(A,R,T,e)`, and `∅ ∈ Att` |
//! | [`agree`] | any two attempts agree, by `acc_rect` along `R` |
//! | [`union`] | the symbol `accrec = ⋃Att`, its members, its values, and that it is a function |
//! | [`is_attempt`] | `accrec ∈ Att`, and ι on its domain |
//! | [`extend`] | the one-point extension `accrec ∪ {⟨x,V⟩}`, and that it is an attempt |
//! | [`total`] | totality, `accrec ∈ fs(acc(A,R),T)`, and the unguarded ι rule |
//! | [`bounded`] | `ih(accrec,A,R,x) ∈ ih_bound(A,T)` — what lets a *guarded* step equation be instantiated at the recursion's own ih |
//! | [`package`] | the thesis's `rec_acc(A,R,e)` and its ι rule |
//! | [`witness`] | non-vacuity: ι fired closed at `A := 1`, `R := ∅`, `T := 1`, `e := ∅` |
//! | [`apparatus`] | [`RecAcc`] — every symbol and theorem over one definitional extension |
//!
//! `shared` holds the private `H → …` combinators and formula readers more than
//! one of them needs; it exports no theorem and is not re-exported.
//!
//! # What is not here
//!
//! * **Uniqueness** — "the unique function on `acc(A,R)` satisfying ι", which
//!   would let `accrec` be introduced through [`kernel::thm::define`] rather than
//!   [`crate::define_abbrev`]. Step 7 of `INDUCTIVES.md`'s recipe, optional
//!   there and optional here, by the same argument [`crate::wrec`] gives.
//! * **The `φ`-restricted variant `acc^φ_r`** of thesis.txt:1831–1845, and the
//!   §5.3 subsingleton-eliminator translation that consumes it. Those are
//!   built *from* this, not here.
//! * **Any `tg.rs` wiring.** Nothing in `checker/` consumes this yet; the
//!   corpus gap this closes is closed only once a backend clause exists.

pub mod agree;
pub mod apparatus;
pub mod attempt;
pub mod base;
pub mod bounded;
pub mod cval;
pub mod extend;
pub mod ih;
pub mod is_attempt;
pub mod package;
mod shared;
pub mod total;
pub mod union;
pub mod witness;

pub use agree::{agree_formula, agreement};
pub use apparatus::RecAcc;
pub use attempt::{
    att_of, attempt_bound, attempt_cond, attempts, empty_attempt, preds_indom, rec_cond,
};
pub use base::Base;
pub use bounded::ih_in_bound;
pub use cval::{
    agree_on_cond, bound_cond, cval_app, cval_bound, cval_ext, cval_of, cval_single_valued,
    prod_inhabited, prod_snd_singleton,
};
pub use extend::{step_typed, Ext};
pub use ih::{
    edge_prop, ep_of, ih_app, ih_bound, ih_ext, ih_of, ih_single_valued, ih_symbol, ih_typed,
    ih_value, preds_agree, preds_typed, row_of,
};
pub use is_attempt::{iota_on_domain, rec_is_attempt, rec_rec_cond, Syms, UnionFacts};
pub use package::{accprop_of, pack_app, pack_iota, pack_of};
pub use total::{iota, rec_funspace, totality, Machinery};
pub use union::{
    attempt_indom_rec, attempt_subset_rec, rec_members, rec_of, rec_single_valued, rec_subset_prod,
    rec_symbol, rec_value,
};
pub use witness::{empty_step, unit_accessible, unit_facts, unit_step_typed, UnitInputs};
