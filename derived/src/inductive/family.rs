//! **Indexed inductive families** — §5.2's `good` predicate and the subset
//! carving it justifies, over the *erased* declaration's machinery.
//!
//! # What this module is, in one paragraph
//!
//! An indexed family `T : Πp⃗. Πx⃗. Sort ℓ` is translated by (1) throwing the
//! indices away and translating the resulting non-indexed declaration with
//! [`crate::inductive`] — that is the **skeleton** `W`; (2) recursing over the
//! skeleton a second time, at the target `𝒫(Idx(p⃗))`, to compute for each
//! skeleton element the set of index tuples at which it is *good*; and (3)
//! carving the family out of the skeleton by Separation:
//!
//! ```text
//! ind(p⃗, x⃗) := { s ∈ W : tup(x⃗) ∈ app(goodrec(p⃗), s) }
//! ```
//!
//! Both recursions are the **same** [`crate::wrec_total::Recursor`] over the
//! **same** [`Machine`](crate::inductive::Machine),
//! [`Inductive`](crate::inductive::Inductive) and tag sum; they differ only in
//! what their step's rows carry ([`crate::inductive::step::Vals`]). Nothing
//! about equality types, `acc` or subsingleton elimination enters: `good`'s
//! base case is a kernel equality of tuple terms inside a Separation, and
//! eliminating it is `eq_leibniz`.
//!
//! # Layout
//!
//! | file | what it holds |
//! |---|---|
//! | [`spec`] | [`IndexedDeclSpec`], [`CtorIndices`] — the index data, and why it wraps `DeclSpec` rather than widening it |
//! | [`index`] | [`IndexSpace`] — `Idx(p⃗)` and `𝒫(Idx(p⃗))`, one telescope |
//! | [`gval`] | [`GoodValues`] — `Gᵢ(p⃗,σ,r)`, one Separation per constructor |
//! | [`goodstep`] | [`GoodStep`] — the packed step, (S1), (S2), and the **unconditional** (S3) |
//! | [`good`] | [`Good`] — `goodrec` and the `good`-ι rules |
//! | [`carrier`] | [`IndexedCarrier`] — the carrier, membership (M), inversion (I), and the D6 bridge |
//! | [`universe`] | [`IndexedUniverse`] — `⊢ ∀p⃗∀x⃗. ([H →] ind(p⃗,x⃗) ∈ Uₙ)`, at any rung |
//! | [`vacuous`] | emptiness at an index no constructor produces |
//! | [`le`] | class (S): the §5.3 `acc`-carrier and its degenerate case, indexed **and** non-indexed |
//! | [`le_prop`] | class (S) at `ni = 0`: the carrier read as a conditional singleton, and the `prop` collapses |
//! | [`le_prop_fields`] | class (S) at `ni = 0`: each field type inhabited by the point, out of the major premise |
//! | [`le_prop_rec`] | class (S) at `ni = 0`: the ι rule — a one-point function, and §5.3's field erasure |
//! | [`le_rec`] | class (S): the recursor — `rec_acc` at `(A_φ,R)`, the edge rule that makes ι fire, and the Lean-shaped ι |
//! | [`trunc`] | class (P): `‖·‖` of the lifted carrier, indexed **and** non-indexed, and ι as proof irrelevance |
//! | [`trunc_rec`] | class (P), non-indexed: the elimination rule, `decl_rect` at a **constant** `φ` |
//!
//! # The non-indexed path is a special case **of class (T)**, deliberately
//!
//! [`IndexedInductive::build`] **declines** a spec with no indices. Routing
//! `ni = 0` through a vacuous Separation would re-derive the whole zero-gap
//! non-indexed fragment through `ind(p⃗) = {s ∈ W : • ∈ …}` — real cost, no
//! benefit, and a fragment-regression risk. `INDEXED-DESIGN.md` §7.2 argues it
//! at length; `derived/tests/family.rs` cashes the collapse as a *theorem*
//! (`good` at a zero-index spec is asked for and refused), which is the right
//! place for it.
//!
//! **That argument is about the `good` route and does not extend to class
//! (S).** It turns on there being another path, and for `Bool`, `N` and `List`
//! there is: [`crate::inductive`]'s W-type carrier. A non-indexed
//! *subsingleton* — `And`, `PUnit`, `ProjDataIndex` — has no W-type carrier to
//! fall back on; its carrier is a conditional singleton. So [`le`] and
//! [`index`] accept `ni = 0`, [`le_prop`] cashes the collapse, and the guard
//! stays where it belongs, on [`IndexedInductive::build`]. The ι rule for those
//! declarations is [`le_prop_rec`] and **not** [`le_rec`] with a relaxed guard:
//! at `ni = 0` the index tuple is `•` for every constructor, so `rec_acc`'s
//! step is addressed by nothing while Lean's minor is still addressed by the
//! constructor's fields — see [`le_prop_rec`]'s header. The `ni = 0` guard
//! that used to sit on [`IndexSpace::build`] was the mistake: it made the
//! *index space* refuse a case that only the class-(T) carrier had a reason to
//! refuse.
//!
//! # What is out of scope here
//!
//! The **wiring**: turning these theorems into `⟦T⟧`, `⟦T.ctor⟧` and
//! `⟦T.rec⟧` needs `ExprPtr`-level work and lives in the checker. In
//! particular, `INDEXED-DESIGN.md` §5.1's finding — that the indexed
//! recursor's engine *is* the erased declaration's
//! [`GenRecursor`](crate::inductive::GenRecursor), with the index arguments
//! dead binders in the nest — needs nothing new from this module beyond
//! [`IndexedCarrier::bridge`], which is what moves a Lean-shaped hypothesis
//! (`rⱼ ∈ ind(p⃗, d⃗ᵢⱼ)`) to the skeleton-shaped one (S4) carries
//! (`rⱼ ∈ skel(p⃗)`).

pub mod carrier;
pub mod good;
pub mod goodstep;
pub mod gval;
pub mod index;
pub mod le;
pub mod le_prop;
pub mod le_prop_fields;
pub mod le_prop_rec;
pub mod le_rec;
pub mod spec;
pub mod trunc;
pub mod trunc_rec;
pub mod universe;
pub mod vacuous;

pub use carrier::{IndexedCarrier, IndexedCtor};
pub use good::{Good, GoodIota};
pub use goodstep::GoodStep;
pub use gval::GoodValues;
pub use index::IndexSpace;
pub use le::{LeCarrier, LeSpec};
pub use le_prop::LeProp;
pub use le_prop_fields::LePropFields;
pub use le_prop_rec::{rec_term, LePropRecursor};
pub use le_rec::{minor_app, minor_eq, slot_at, LeRecursor};
pub use spec::{CtorIndices, IndexedDeclSpec};
pub use trunc::{TruncCarrier, TruncCtor};
pub use trunc_rec::TruncRecursor;
pub use universe::IndexedUniverse;
pub use vacuous::empty_at_index;

use kernel::{Env, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::wrec_total::Recursor;

/// A translated indexed family: the index space, the `good` recursion and the
/// carrier, all over one [`Machine`] and one skeleton.
pub struct IndexedInductive {
    /// The declaration this was built from.
    pub spec: IndexedDeclSpec,
    /// `Idx(p⃗)` and `𝒫(Idx(p⃗))`.
    pub ix: IndexSpace,
    /// The `n` `good` values.
    pub gv: GoodValues,
    /// The `good` recursion's step, and (S1)–(S3).
    pub gs: GoodStep,
    /// `goodrec` and the `good`-ι rules.
    pub good: Good,
    /// The carrier, (M) and (I).
    pub carrier: IndexedCarrier,
}

impl IndexedInductive {
    /// Translate an indexed declaration over an already-translated skeleton.
    ///
    /// `ind` must be [`Inductive::build`] at `spec.base` over `mach`, and
    /// `rc`/`iota`/`funspace` the same W-recursor apparatus used everywhere
    /// else. Returns `None` when the spec is not
    /// [`well_formed`](IndexedDeclSpec::well_formed), when it has **no
    /// indices** (see the header), when it has no constructors, or when any
    /// internal shape check fails.
    pub fn build(
        env: &mut Env,
        mach: &mut Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        rc: &Recursor,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<IndexedInductive> {
        if !spec.well_formed() || spec.indices.is_empty() || spec.is_empty() || !ind.is_over(mach) {
            return None
        }
        // The skeleton must be *this* declaration's erasure, not another's.
        if ind.spec.params != spec.base.params || ind.spec.ctors.len() != spec.base.ctors.len() {
            return None
        }
        let ps: Vec<kernel::Term> = ind.params.iter().map(|v| kernel::Term::var(*v)).collect();
        let ix = IndexSpace::build(env, mach, spec, &ps)?;
        let gv = GoodValues::build(env, mach, ind, spec, &ix)?;
        let gs = GoodStep::build(env, mach, ind, spec, &ix, &gv)?;
        let good = Good::build(env, mach, ind, spec, &ix, &gv, &gs, rc, iota, funspace)?;
        let carrier = IndexedCarrier::build(env, mach, ind, spec, &ix, &gv, &good)?;
        Some(IndexedInductive { spec: spec.clone(), ix, gv, gs, good, carrier })
    }

    /// Whether every theorem this holds is a `⊢` with nothing on the left.
    ///
    /// Checked by `derived/tests/family.rs`: an antecedent belongs in the
    /// conclusion, and a sequent hypothesis would be invisible to the
    /// conclusion comparisons the tests do.
    pub fn rests_on_nothing(&self) -> bool {
        let mut ts: Vec<&Thm> = vec![
            &self.gs.sv,
            &self.gs.step_typed,
            &self.good.funspace,
            &self.good.wrec_iota,
            &self.carrier.ty_ax,
            &self.carrier.subset_w,
            &self.carrier.bridge,
            &self.carrier.good_of,
            &self.carrier.intro,
        ];
        ts.extend(self.gv.axioms.iter());
        ts.extend(self.gv.in_target.iter());
        ts.extend(self.good.iota.iter());
        ts.extend(self.carrier.ctors.iter().flat_map(|c| [&c.mem, &c.inv]));
        ts.into_iter().all(|t| t.hyps().is_empty())
    }
}
