//! **The translation of an inductive declaration**, driven by declaration data
//! rather than written out by hand — §5.2's `spec` judgment, as a procedure.
//!
//! # What this replaces
//!
//! `derived/src/enums.rs`, `wnat.rs` and `wlist.rs` each interpret **one**
//! inductive at **one** concrete arity: all-nullary capped at two constructors,
//! `N`, `List`. `inductive RGB | red | green | blue` is the same shape as
//! `Bool` and none of them can express it. This module takes the declaration's
//! data — how many parameters, and per constructor its non-recursive argument
//! types and its recursive-argument count — and builds the carrier, the
//! constructors, their typing rules, their injectivity and their pairwise
//! distinctness, at whatever arity the declaration has.
//!
//! ```text
//! Aᵢ      := Σy₀:β₀. … Σy_{k-1}:β_{k-1}. 1          per constructor
//! A       := Sum_n(A₀ … A_{n-1})
//! B       := rec₊(λ_. finord(m₀), … rec₊(λ_. finord(m_{n-1}), ∅))
//! carrier := W(A, B, U({A, T}))
//! ctor_i(y⃗,r⃗) := ⟨Inj_i⟨y₀,…,⟨y_{k-1},•⟩⟩, f(r⃗)⟩
//! ```
//!
//! `Sum_n`, `Inj_i` and `finord(m) = Sum_m(1,…,1)` are **real symbols**, minted
//! on demand and cached on the [`Machine`] — see [`crate::isum::symbols`] for
//! why, and for which cache is keyed by what. Nothing below states anything
//! over the underlying `A₀ + (A₁ + (… + 0))` nest.
//!
//! # Interface
//!
//! [`Machine::new`] once, then [`Inductive::build`] per declaration:
//!
//! ```text
//! ⊢ closed(A, B, U({A,T}))                                    [Inductive::closed]
//! ⊢ ∀p⃗. ind(p⃗) = W(A, B, U({A,T}))                            [Inductive::ty_ax]
//! ⊢ ∀p⃗ ∀y⃗ ∀r⃗. (H → ctor_i(y⃗,r⃗) ∈ ind(p⃗))                     [Ctor::mem]
//! ⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. (ctor_i(y⃗,r⃗) = ctor_i(y⃗′,r⃗′) → ⋀ eqs)     [Ctor::inj]
//! ⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))            [Inductive::distinct]
//! ```
//!
//! `H` is the right-nested conjunction of `yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1})` and
//! `rⱼ ∈ ind(p⃗)`, and is **absent** for a nullary constructor, so
//! `⊢ ctor ∈ ind` comes out closed exactly when Lean's constructor is.
//!
//! What is **not** here is `⊢ ⟦T⟧ ∈ U₁` — the size statement a checker needs to
//! answer `T : Type 0`. It is not a gap in this module: it is a fact about the
//! cumulative hierarchy, not about the carrier, and it lives in
//! [`crate::cumul::DeclUniverse`], which consumes an [`Inductive`] built here
//! and returns `⊢ ∀p⃗. ([H →] ind(p⃗) ∈ U₁)`.
//!
//! # Layout
//!
//! This module is a **hub**: each construction lives in its own file with its
//! own interface header. Read the header of the one you need.
//!
//! | file | what it holds |
//! |---|---|
//! | [`spec`] | [`DeclSpec`], [`CtorSpec`], [`Slot`] — the declaration data, and why argument types are `FnSym`s |
//! | [`machine`] | [`Machine`] — the apparatus every declaration is built over, once |
//! | [`carrier`] | [`Inductive`] — `A`, `B`, the bound and the definitional extension |
//! | [`ctor`] | [`Ctor`] — a constructor's term and its typing rule |
//! | [`distinct`] | injectivity and pairwise distinctness — the non-vacuity half |
//! | [`step`] | the recursor's packed step: the terms, and one Replacement per constructor |
//! | [`members`] | what is in the step, and what is not |
//! | [`values`] | the step's values, and hence that it is a function — (S2) |
//! | [`computes`] | the step's per-constructor computation rules — (S1) |
//! | [`premise`] | the pointwise hypothesis bundle `HYP` |
//! | [`motive`] | what a **dependent** motive asks for: `COD`, `DEP`, and the target policy |
//! | [`guard`] | the guarded minors that make `HYP` dischargeable at a variable motive |
//! | [`dep`] | [`DepRecursor`] — the eliminator at a **dependent** motive, and its ι rules |
//! | [`decl_fields`] | each `Prop` field of a one-constructor class-(T) structure inhabited by the point — `le_prop_fields`/`trunc_fields`'s third sibling |
//! | [`decl_proj`] | a projection out of a class-(T) structure, typed at an arbitrary carrier element — the structure η rule, and the projection's computation rule at the constructor |
//! | [`degen`] | [`DegenRec`] — **one constructor and no recursive field**: the eliminator is the inverse of the constructor, so there is no target, no `HYP` and no W-recursor |
//! | [`rect`] | structural induction over the carrier, in the declaration's own constructors |
//! | [`typed`] | `HYP → step_typed` — (S3), the first consumer of `no_junk` |
//! | [`iota`] | the per-constructor ι rules — (S4) |
//! | [`recursor`] | [`GenRecursor`] — the whole recursor, packaged |
//! | [`empty_decl`] | [`EmptyDecl`] — **no constructors**: the carrier is `0`, the eliminator is typed by that alone, and there are no ι rules |
//! | [`family`] | indexed families: `good`, the subset carrier, membership and inversion |
//!
//! `shared` holds the optional-hypothesis combinators and `rec_shared` the
//! implication-form rewriting steps; neither exports a theorem.
//!
//! # What is out of scope, and is not a gap in this file
//!
//! **Indices.** §5.2's third output `G` (`good`) exists only to undo the
//! erasure of indices, and for a non-indexed declaration it is vacuous
//! (`INDUCTIVES.md:176`), the subset carving collapses, and the type *is* the
//! W-type. There is no `good` in the files above and there should not be — but
//! it is no longer *absent*: [`family`] builds it, over this module's carrier
//! and this module's step apparatus, and carves `ind(p⃗,x⃗)` out of the W-type
//! by Separation. The retracted half of this note is "needs the equality type
//! first": `good`'s base case is a kernel equality inside a Separation and its
//! elimination is `eq_leibniz` (`INDEXED-DESIGN.md` §2.4). The **non-indexed
//! path is deliberately not routed through the subset**, so nothing in the
//! files above changed.
//!
//! **The wiring.** [`recursor`] derives the recursor and its ι rules at the
//! packed W-type interface; turning that into `⟦T.rec⟧` needs the currying
//! nest, the `T`-policy and the pointwise-`HYP` bridging, which live in the
//! checker and are separate work (`RECURSOR-DESIGN.md` §3.4, §5.2, rung 5).
//!
//! **Dependent Type-level motives** are **in** scope and built —
//! [`dep`], and this note used to say the opposite. The W-recursor here does
//! take one target set, and that turned out not to be the obstacle: `HYP`
//! quantifies the minor premises, so a minor that *tests* its induction
//! hypotheses ([`guard`]) makes `HYP` dischargeable at a variable motive, and
//! [`rect`]'s induction carries the result from the constructors to the whole
//! carrier. `RECURSOR-DESIGN.md` §5.3's Σ-target variant is **not** needed and
//! was not built; §5.1 and §5.3 are corrected there.
//!
//! **Nesting, mutual declarations, `Prop`, small elimination.** Out for the
//! reasons `INDUCTIVES.md`'s Scope section gives; see [`spec`] for which of them
//! this module's input shape actually forecloses.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] per declaration (naming the carrier), plus the
//! `Σ`s, sums, `rec₊`s and lambda graphs the primitives already introduce. The
//! W-type's bound is discharged, not assumed: [`Inductive::closed`] is
//! unconditional at every arity.

pub mod carrier;
pub mod computes;
pub mod ctor;
pub mod decl_fields;
pub mod decl_proj;
pub mod degen;
pub mod dep;
pub mod distinct;
pub mod empty_decl;
pub mod family;
pub mod guard;
pub mod iota;
pub mod machine;
pub mod members;
pub mod motive;
pub mod premise;
mod rec_shared;
pub mod rect;
pub mod recursor;
pub mod spec;
pub mod step;
pub mod typed;
pub mod values;
mod wrec_input;

pub use carrier::Inductive;
pub use family::{IndexedDeclSpec, IndexedInductive};
pub use ctor::Ctor;
pub use machine::{Machine, MachineId};
pub use decl_fields::DeclFields;
pub use decl_proj::{proj_of, DeclProj};
pub use degen::DegenRec;
pub use dep::DepRecursor;
pub use empty_decl::EmptyDecl;
pub use recursor::{carrier_at, GenRecursor};
pub use spec::{CtorSpec, DeclSpec, Slot};
pub use step::{applied_minor, pow_prod, StepSym};
