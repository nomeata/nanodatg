//! **The indexed declaration spec** — the erased declaration, plus the index
//! data §5.2's `good` needs and nothing else.
//!
//! # A wrapper, not a wider `DeclSpec`
//!
//! `INDEXED-DESIGN.md` §7.2 argues the shape and this file implements it: the
//! erased [`DeclSpec`] is kept **whole and unchanged** as
//! [`IndexedDeclSpec::base`], because it is the identity the shared machinery
//! is keyed on — [`Machine`](crate::inductive::Machine),
//! [`Inductive`](crate::inductive::Inductive) and
//! [`GenRecursor`](crate::inductive::GenRecursor) all consume it, and the
//! `good` recursion of [`super::good`] is *also* the erased declaration's
//! `wrec`, at another target. Growing index fields inside `DeclSpec` would make
//! every existing consumer carry fields it must ignore, and the ignoring would
//! be an invariant rather than a type.
//!
//! The corollary, which is deliberate: **for class (T), the non-indexed path is
//! a special case, not an instance.** [`super::IndexedInductive::build`]
//! declines `indices.is_empty()` outright rather than routing it through a
//! provably-vacuous Separation. Wrapping `Bool`, `N` and `List` in
//! `{s ∈ W : • ∈ …}` would re-derive the whole zero-gap fragment through a
//! subset carving for no benefit. That the collapse *is* a theorem is worth a
//! test (`family.rs`'s `an_unindexed_spec_is_declined`), not a code path.
//!
//! **Class (S) is the other way round.** [`super::le::LeCarrier`] and
//! [`super::index::IndexSpace`] accept `indices.is_empty()`, because a
//! non-indexed subsingleton has no W-type carrier to be a special case *of*:
//! `And`, `PUnit` and `ProjDataIndex` are conditional singletons, and
//! [`super::le_prop`] is where that collapse is cashed. The rule is by
//! eliminator class, not by index count; [`super::index`]'s header states it.
//!
//! # What the index data is
//!
//! With `np` parameters and `ni` indices (`INDEXED-DESIGN.md` §3.1):
//!
//! ```text
//! ι₀ … ι_{ni−1}   the index types;  ι_k of arity np + k
//!                 (parameters, then the earlier indices)
//!
//! per constructor i:
//!   e⃗ᵢ    : ni symbols of arity np + kᵢ    — the RESULT indices, in terms of
//!                                            the parameters and every plain
//!                                            field, in declared plain order
//!   d⃗ᵢⱼ   : ni symbols of arity
//!           np + plains_before(i,j)        — the j-th RECURSIVE argument's
//!                                            indices
//! ```
//!
//! Arities follow the [`crate::sigma::Telescope`] convention for the same
//! reason [`crate::inductive::spec`] gives — the symbol's defining equation is
//! a *seam* to rewrite along and an instantiation is one node — so dependence
//! is expressed by *application*, and a checker-side builder turns each index
//! expression into a symbol with one [`crate::define_abbrev`] over the
//! parameter and field variables. *(That header used to give the reason as "the
//! kernel has `Formula::subst` but no `Term::subst`"; it is void — see
//! [`crate::subst_term`].)*
//!
//! [`plains_before`](IndexedDeclSpec::plains_before) is the restriction that
//! matters: `d⃗ᵢⱼ` may mention only the plain fields that **precede** the `j`-th
//! `Slot::Rec` in the declared mask. That is the thesis's own restriction — the
//! recursive-argument rule does not extend `Γ` (`thesis.txt:1798–1801`) — and
//! it is forced here by erasure, since the tag telescope holds only the plain
//! fields. A Lean declaration whose index expression mentions a *recursive*
//! field is unrepresentable and must be declined at the boundary (a counted
//! gap, `IndexRecFieldDep`), never forced to fit.
//!
//! `RBTree` satisfies it, which is the point of the restriction being stated
//! this way: `red`'s mask is `Plain, Rec, Plain, Rec`, its rec-arg indices are
//! `(Color.b, n)` with `n` the plain field at mask position 0, so
//! `plains_before = 1` for both `Rec` slots' first index and `1`/`2` for the
//! two slots respectively; `black`'s `(c₁,n)`/`(c₂,n)` likewise.
//!
//! # Interface
//!
//! [`IndexedDeclSpec::well_formed`] is [`DeclSpec::well_formed`] plus the arity
//! checks above; it is what [`super::IndexedInductive::build`] gates on. The
//! `*_at` methods are the one spelling of "this index symbol applied to its
//! arguments", so the `Gᵢ` axiom, the membership rule and the inversion rule
//! cannot drift apart.

use kernel::{FnSym, Term};

use crate::inductive::spec::{DeclSpec, Slot};
use crate::sigma::Telescope;
use crate::sums::Sums;

/// One constructor's index data, parallel to its [`CtorSpec`](crate::inductive::CtorSpec).
#[derive(Clone, Debug)]
pub struct CtorIndices {
    /// `e⃗ᵢ` — the result indices: `ni` symbols, each of arity `np + kᵢ`,
    /// taking the parameters and then **all** the constructor's plain fields
    /// in declared plain order.
    pub result: Vec<FnSym>,
    /// `d⃗ᵢⱼ` — per [`Slot::Rec`] position `j`, that recursive argument's
    /// indices: `ni` symbols of arity `np + plains_before(i,j)`.
    pub rec_args: Vec<Vec<FnSym>>,
}

impl CtorIndices {
    /// A constructor whose result indices are `result` and which has no
    /// recursive arguments.
    pub fn nonrecursive(result: Vec<FnSym>) -> CtorIndices {
        CtorIndices { result, rec_args: Vec::new() }
    }
}

/// An indexed inductive family: the **erased** declaration, the index types,
/// and the per-constructor index expressions.
#[derive(Clone, Debug)]
pub struct IndexedDeclSpec {
    /// The erased declaration — what
    /// [`Inductive::build`](crate::inductive::Inductive::build) and
    /// [`GenRecursor::build`](crate::inductive::GenRecursor::build) consume,
    /// unchanged.
    pub base: DeclSpec,
    /// `ι₀ … ι_{ni−1}`, the index types; `ιₖ` has arity `np + k`. Empty
    /// **iff** the declaration is not indexed, in which case the construction
    /// declines and the caller uses the non-indexed path.
    pub indices: Vec<FnSym>,
    /// One entry per constructor of [`IndexedDeclSpec::base`], in the same
    /// order.
    pub ctors_idx: Vec<CtorIndices>,
}

impl IndexedDeclSpec {
    /// An indexed declaration.
    pub fn new(
        base: DeclSpec,
        indices: Vec<FnSym>,
        ctors_idx: Vec<CtorIndices>,
    ) -> IndexedDeclSpec {
        IndexedDeclSpec { base, indices, ctors_idx }
    }

    /// `np`.
    pub fn params(&self) -> usize { self.base.params }
    /// `ni`, the number of indices.
    pub fn num_indices(&self) -> usize { self.indices.len() }
    /// `n`, the number of constructors.
    pub fn len(&self) -> usize { self.base.ctors.len() }
    /// Whether the declaration has no constructors.
    pub fn is_empty(&self) -> bool { self.base.ctors.is_empty() }

    /// How many [`Slot::Plain`] fields precede the `j`-th [`Slot::Rec`] field
    /// of constructor `i` in the declared mask — the arity budget of `d⃗ᵢⱼ`.
    ///
    /// `None` if `i` or `j` is out of range.
    pub fn plains_before(&self, i: usize, j: usize) -> Option<usize> {
        let order = &self.base.ctors.get(i)?.order;
        let mut plains = 0;
        let mut seen = 0;
        for sl in order {
            match sl {
                Slot::Plain => plains += 1,
                Slot::Rec => {
                    if seen == j {
                        return Some(plains)
                    }
                    seen += 1;
                }
            }
        }
        None
    }

    /// Whether every symbol has the arity the construction applies it at.
    ///
    /// [`DeclSpec::well_formed`] for the erased half, and then: `ιₖ` of arity
    /// `np + k`; one [`CtorIndices`] per constructor; `ni` result symbols per
    /// constructor, each of arity `np + kᵢ`; one `d⃗ᵢⱼ` row per recursive
    /// argument, each row `ni` symbols of arity `np + plains_before(i,j)`.
    ///
    /// Checked by [`super::IndexedInductive::build`], which declines rather
    /// than deriving something about the wrong terms. A `well_formed` spec is
    /// *not* thereby a translatable one: `indices.is_empty()` is well formed
    /// and is declined, on the grounds §7.2 gives.
    pub fn well_formed(&self) -> bool {
        let np = self.base.params;
        if !self.base.well_formed() || self.ctors_idx.len() != self.base.ctors.len() {
            return false
        }
        if !self.indices.iter().enumerate().all(|(k, s)| s.arity() as usize == np + k) {
            return false
        }
        let ni = self.indices.len();
        (0..self.base.ctors.len()).all(|i| {
            let c = &self.base.ctors[i];
            let ci = &self.ctors_idx[i];
            ci.result.len() == ni
                && ci.result.iter().all(|s| s.arity() as usize == np + c.args.len())
                && ci.rec_args.len() == c.recs
                && (0..c.recs).all(|j| {
                    let want = match self.plains_before(i, j) {
                        Some(w) => np + w,
                        None => return false,
                    };
                    ci.rec_args[j].len() == ni
                        && ci.rec_args[j].iter().all(|s| s.arity() as usize == want)
                })
        })
    }

    /// `ιₖ(p⃗, x₀ … x_{k−1})` — the `k`-th index type at the parameters and the
    /// earlier index values.
    pub fn index_type_at(&self, k: usize, ps: &[Term], xs: &[Term]) -> Option<Term> {
        let mut a = ps.to_vec();
        a.extend(xs.get(..k)?.iter().cloned());
        Some(Term::apply(*self.indices.get(k)?, a))
    }

    /// `eᵢₖ(p⃗, y⃗)` — constructor `i`'s `k`-th result index at the parameters
    /// and **all** its plain fields.
    pub fn result_at(&self, i: usize, k: usize, ps: &[Term], ys: &[Term]) -> Option<Term> {
        let mut a = ps.to_vec();
        a.extend(ys.iter().cloned());
        Some(Term::apply(*self.ctors_idx.get(i)?.result.get(k)?, a))
    }

    /// `dᵢⱼₖ(p⃗, y₀ … )` — the `j`-th recursive argument's `k`-th index, at the
    /// parameters and the plain fields that precede that `Rec` slot.
    pub fn rec_index_at(
        &self,
        i: usize,
        j: usize,
        k: usize,
        ps: &[Term],
        ys: &[Term],
    ) -> Option<Term> {
        let mut a = ps.to_vec();
        a.extend(ys.get(..self.plains_before(i, j)?)?.iter().cloned());
        Some(Term::apply(*self.ctors_idx.get(i)?.rec_args.get(j)?.get(k)?, a))
    }

    /// `e⃗ᵢ(p⃗,y⃗)` as a list — constructor `i`'s result index vector.
    pub fn result_vec(&self, i: usize, ps: &[Term], ys: &[Term]) -> Option<Vec<Term>> {
        (0..self.num_indices()).map(|k| self.result_at(i, k, ps, ys)).collect()
    }

    /// `d⃗ᵢⱼ(p⃗,y⃗)` as a list.
    pub fn rec_index_vec(&self, i: usize, j: usize, ps: &[Term], ys: &[Term]) -> Option<Vec<Term>> {
        (0..self.num_indices()).map(|k| self.rec_index_at(i, j, k, ps, ys)).collect()
    }

    /// `tup(x⃗) = ⟨x₀, ⟨x₁, … ⟨x_{ni−1}, •⟩…⟩⟩` — the thesis's index tuple, and
    /// exactly [`crate::sigma::Telescope::tuple_of`]'s spelling, so an element
    /// of the index space and an index tuple are the same term.
    pub fn tup(s: &Sums, xs: &[Term]) -> Term { Telescope::tuple_of(s, xs) }
}
