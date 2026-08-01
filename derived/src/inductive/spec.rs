//! **The declaration spec** — the data a non-indexed inductive declaration is
//! translated from, and nothing else.
//!
//! # What §5.2 needs to see, and what it does not
//!
//! The `spec` judgment (`thesis.txt:1789–1801`) recurses over two lists: the
//! constructor list, and each constructor's argument list. At every step it
//! looks at exactly three things —
//!
//! * whether the constructor list is empty (`0 spec`) or `(c : β) + K`;
//! * whether the next argument is a plain one, `∀y : β. τ`, or a recursive one,
//!   `(∀z :: γ. t e) → τ`;
//! * for a plain argument, the argument's **type** `β`.
//!
//! It never looks at the constructor's *name*, nor at the recursive argument's
//! type (which is `t e`, determined), nor — for a non-indexed declaration — at
//! the index expression `e`. So the spec is
//!
//! ```text
//! DeclSpec { params: np, ctors: [ CtorSpec { args: [β₀ … β_{k-1}], recs: m } … ] }
//! ```
//!
//! and that is the whole input to [`crate::inductive::Inductive::build`].
//!
//! # Why the argument types are `FnSym`s and not `Term`s
//!
//! Because the kernel **has `Formula::subst` but no `Term::subst`**. The
//! thesis's rule
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ ∀y : β. τ ctor ⇒ Σy' : β. A[y'/y];  p'. B[π₁p'/y][π₂p'/p]; …
//! ```
//!
//! substitutes into `A` and `B`, and the only way to express that here is for
//! each argument type to be a **function symbol** applied to the arguments it
//! depends on: substituting is then applying the symbol to different terms.
//! [`crate::sigma::Telescope`] fixes the convention — `βᵢ` has arity `np + i`,
//! taking the declaration's `np` parameters and the `i` earlier arguments — and
//! this struct simply presents it.
//!
//! That is a **restriction on what can be translated**, and it is worth being
//! precise about which one. It is not a restriction on dependency: `βᵢ` may
//! mention every earlier argument, which is exactly the dependent telescope. It
//! is a restriction on *how the caller supplies* the type: a checker holding a
//! Lean expression for the argument's type must first turn it into a symbol,
//! with [`crate::define_abbrev`] over the parameter and argument variables. For
//! `List`'s `cons : α → List α → List α` that symbol is the identity,
//! `β₀(p) = p`, and for a closed argument type it is a constant. Both are one
//! line. So the constraint is real but cheap, and it is discharged at the
//! *boundary*, which is where the checker already builds terms.
//!
//! # What is deliberately absent
//!
//! **Indices.** `good`/`G` is the third output of the `spec` judgment and it
//! exists solely to undo the erasure of indices; for a parameterised,
//! non-indexed declaration it is vacuous (`INDUCTIVES.md:176`) and the type is
//! the W-type outright. There is no field for indices here and adding one would
//! not be an extension of this construction but a different one — it needs the
//! equality type first.
//!
//! **Nesting.** A recursive argument is counted, not described, because
//! `thesis.txt:1800`'s `Σ(z :: γ)` collapses to `1` only for a **non-nested**
//! recursive argument. A nested one contributes a fibre summand that is a
//! genuine telescope, and [`recs`](CtorSpec::recs) being a `usize` is exactly
//! the assumption that it does not.
//!
//! **Universes and `Prop`.** §5.2's small-eliminator clause truncates, and §5.3
//! abandons W-types for `acc`. Neither is representable here, by design.

use kernel::FnSym;

/// One field position of a constructor, in **declared order**.
///
/// The carrier erases order — `A` collects only the non-recursive arguments
/// and `B` only counts the recursive ones — but the *recursor* cannot: Lean's
/// minor premise takes the constructor's fields in declared order, and the
/// corpus demands interleaving: `Lean.ParserDescr.sepBy` and `sepBy1` in
/// `init-prelude` are `Rec, Plain, Rec, Plain`, on a non-indexed,
/// parameter-free declaration — i.e. squarely inside this module's scope.
/// A `Slot::Plain` consumes the next entry of [`CtorSpec::args`]; a
/// `Slot::Rec` consumes the next recursive position.
///
/// This comment used to cite `RBTree.red` as
/// `N → RBTree α → α → RBTree α → RBTree α`. The mask was right, the citation
/// was not: `RBTree` is an **indexed family** (`numIndices: 2`, over `Color` and
/// `N`), the real constructor is
/// `red : ∀ α n, RBTree α Color.b n → α → RBTree α Color.b n → RBTree α Color.r n`,
/// and indexed families are outside this module's scope — the spec builder must
/// decline it. There is no plain `m ≥ 2` constructor in the tutorial corpus at
/// all, which is why the witness above is an `init-prelude` one.
///
/// Note what the mask does **not** change: `βⱼ` still has arity `np + j` —
/// parameters plus the *earlier non-recursive* arguments — so a later argument
/// type never depends on an earlier recursive argument. That matches the
/// thesis exactly (the `ctor` rule for a recursive argument does not extend
/// `Γ`, `thesis.txt:1798–1801`), and it is forced by erasure: the tag telescope
/// holds only the non-recursive arguments, so nothing else is available to
/// substitute. A Lean declaration that violates it cannot be expressed as a
/// [`CtorSpec`] at all and must be declined by the spec builder at the
/// boundary — a counted gap, never a mistranslation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// The next non-recursive argument, `yⱼ : βⱼ(p⃗, y₀ … y_{j-1})`.
    Plain,
    /// The next recursive argument, `rⱼ : ind(p⃗)`.
    Rec,
}

/// One constructor: its non-recursive argument types, how many recursive
/// arguments it takes, and the declared order of the two kinds of field.
#[derive(Clone, Debug)]
pub struct CtorSpec {
    /// `β₀ … β_{k-1}`, the non-recursive argument types. `βᵢ` has arity
    /// `np + i`: the declaration's parameters, then the earlier arguments.
    pub args: Vec<FnSym>,
    /// The number of recursive arguments, `m`. The constructor's fibre is
    /// [`finord(m)`](crate::isum::finord).
    pub recs: usize,
    /// The declared field order — length `k + m`, with `k` [`Slot::Plain`]
    /// entries and `m` [`Slot::Rec`] entries. The carrier ignores it; the
    /// recursor's step value and ι rules read it. [`CtorSpec::new`] defaults
    /// to fields-then-recs; [`CtorSpec::with_order`] takes the real mask.
    pub order: Vec<Slot>,
}

impl CtorSpec {
    /// A constructor with the given argument types and recursive-argument
    /// count, its fields declared **non-recursive first** — the order the
    /// carrier's hypotheses use. For an interleaved declaration use
    /// [`CtorSpec::with_order`].
    pub fn new(args: Vec<FnSym>, recs: usize) -> CtorSpec {
        let mut order = vec![Slot::Plain; args.len()];
        order.extend(std::iter::repeat_n(Slot::Rec, recs));
        CtorSpec { args, recs, order }
    }

    /// A constructor whose fields interleave in the given declared order.
    /// `None` unless the mask has exactly `args.len()` [`Slot::Plain`]s and
    /// `recs` [`Slot::Rec`]s.
    pub fn with_order(args: Vec<FnSym>, recs: usize, order: Vec<Slot>) -> Option<CtorSpec> {
        let c = CtorSpec { args, recs, order };
        if c.order_consistent() { Some(c) } else { None }
    }

    /// A nullary constructor — no arguments of either kind.
    pub fn nullary() -> CtorSpec { CtorSpec::new(Vec::new(), 0) }

    /// The number of non-recursive arguments.
    pub fn arity(&self) -> usize { self.args.len() }

    /// Whether [`CtorSpec::order`] really is a mask for these fields:
    /// `#Plain = k` and `#Rec = m`.
    pub fn order_consistent(&self) -> bool {
        let plains = self.order.iter().filter(|s| **s == Slot::Plain).count();
        let recs = self.order.iter().filter(|s| **s == Slot::Rec).count();
        plains == self.args.len() && recs == self.recs
    }
}

/// A non-indexed, non-mutual, non-nested inductive declaration.
#[derive(Clone, Debug)]
pub struct DeclSpec {
    /// The number of parameters, `np`. Parameters are fixed throughout the
    /// declaration and stay free variables of every theorem derived from it.
    pub params: usize,
    /// The constructors, in declaration order. The empty list is `Empty`.
    pub ctors: Vec<CtorSpec>,
}

impl DeclSpec {
    /// A declaration with `params` parameters and the given constructors.
    pub fn new(params: usize, ctors: Vec<CtorSpec>) -> DeclSpec { DeclSpec { params, ctors } }

    /// The number of constructors, `n`.
    pub fn len(&self) -> usize { self.ctors.len() }

    /// Whether the declaration has no constructors — Lean's `Empty`.
    pub fn is_empty(&self) -> bool { self.ctors.is_empty() }

    /// Whether every argument type has the arity
    /// [`crate::sigma::Telescope`] requires — `βᵢ` of arity `np + i` — and
    /// every constructor's field mask is consistent with its field counts.
    ///
    /// Checked by [`crate::inductive::Inductive::build`], which declines rather
    /// than deriving something about the wrong terms. This is the derived
    /// layer's half of the **positive scope check**: everything a `DeclSpec`
    /// can express is a non-indexed, non-mutual, non-nested declaration with
    /// plain recursive arguments, and a checker-side spec builder must decline
    /// (and count) anything it cannot faithfully express in this shape —
    /// function-typed recursive arguments, indices, mutual blocks — rather
    /// than force a fit.
    pub fn well_formed(&self) -> bool {
        self.ctors.iter().all(|c| {
            c.order_consistent()
                && c.args.iter().enumerate().all(|(i, b)| b.arity() as usize == self.params + i)
        })
    }
}
