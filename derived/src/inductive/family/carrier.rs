//! **The indexed carrier** `ind(p⃗, x⃗)`, with constructor membership and
//! inversion — `INDEXED-DESIGN.md` §4, and the composition D3 named as the
//! riskiest derived step.
//!
//! # The carrier
//!
//! ```text
//! ind(p⃗, x⃗) := { s ∈ W(A,B,U({A,T′})) : tup(x⃗) ∈ app(goodrec(p⃗), s) }
//! ```
//!
//! — one [`crate::define_by_membership`] of arity `np + ni`, and the thesis's
//! `λx :: α. {s : Wp:A. B p | rec_W (λp. G p) s x}` (`thesis.txt:1784`) with
//! `rec_W … s x` read as "the index tuple is in the good-set of `s`". It is a
//! subset of `W` **for every `x⃗`, junk ones included** — a Separation is a
//! subset no matter what is asked of it — which is what makes
//! [`super::universe`] one `C₂` step and what makes the weakening bridge below
//! unconditional.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) ↔ (z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)))  [IndexedCarrier::ty_ax]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ W)                             [IndexedCarrier::subset_w]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ skel(p⃗))                       [IndexedCarrier::bridge]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → tup(x⃗) ∈ app(goodrec,z))           [IndexedCarrier::good_of]
//! ⊢ ∀p⃗∀x⃗∀z. ((z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)) → z ∈ ind(p⃗,x⃗)) [IndexedCarrier::intro]
//!
//! (M) ⊢ ∀p⃗∀y⃗∀r⃗. ( (Hᵢ^ind ∧ Eᵢ) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)) ) [IndexedCtor::mem]
//! (M′) ⊢ ∀p⃗∀y⃗∀r⃗. ( Hᵢ^ind → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)) )      [IndexedCtor::mem_lean]
//!         — (M) with `Eᵢ` discharged, its antecedent in **Lean field order**
//! (I) ⊢ ∀p⃗∀y⃗∀r⃗∀x⃗. ( ([Hᵢ^skel ∧] ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)) →
//!         ( tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗)) ∧ ⋀ⱼ rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗)) ) ) [IndexedCtor::inv]
//! ```
//!
//! writing `skel(p⃗)` for the erased declaration's carrier (the *skeleton*
//! W-type, [`crate::inductive::Inductive::carrier`]) and `Hᵢ^skel` for its
//! constructor hypotheses.
//!
//! # A recursive argument is a **function into** the family, or an element of it
//!
//! The two `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` above are the plain spelling. At a constructor
//! taking [`RecArg::general`](crate::recarg::RecArg::general) Lean's field is a
//! function and the atom is `rⱼ ∈ fs(Aⱼ, ind(p⃗, d⃗ᵢⱼ))` — at **every** slot of
//! that constructor, the degenerate `Aⱼ = 1` included, because the choice is
//! per constructor ([`Inductive::ctor_slot_domains`]). (M) and (I) both move,
//! and in opposite directions:
//!
//! * (M) has to get from a function into `ind(p⃗,d⃗ᵢⱼ)` to a function into the
//!   skeleton, which is [`Wtype::fs_mono`](crate::wtype::Wtype::fs_mono) over
//!   `subset_w` generalised; and it discharges the good-set matrix's bounded
//!   universal *pointwise*, one `z ∈ Aⱼ` at a time, `app(rⱼ,z)` being the child
//!   there by the function space's application rule.
//! * (I) reads that same bounded universal out and gets the children back
//!   pointwise, so it has to put the function back together:
//!   [`Wtype::retarget`](crate::wtype::Wtype::retarget) — "every value lands in
//!   `ind(p⃗,d⃗ᵢⱼ)`, so the field is a function into it" — is the exact converse
//!   of (M)'s `fs_mono` step.
//!
//! One equation rewrites the matrix's slot in both directions, and it is
//! [`GoodIota::ih`]; `ih_fibre_at` is the single door both rules take it
//! through, so the forward mirror and the inversion projection cannot disagree
//! about what `app(cmp, Injⱼ z)` is.
//!
//! # (M)'s antecedent is longer than the design said — a measured negative
//!
//! `INDEXED-DESIGN.md` §4.2 states (M) with antecedent `Hᵢ^ind` alone: the
//! plain fields at their types and each recursive argument at
//! `ind(p⃗, d⃗ᵢⱼ)`. **That is not enough**, and the gap is structural rather
//! than an oversight in the proof:
//!
//! ```text
//! Eᵢ  :=  ⋀ₖ  eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, eᵢ₀(p⃗,y⃗) … eᵢ_{k−1}(p⃗,y⃗))
//! ```
//!
//! `Gᵢ` is a Separation *out of `Idx(p⃗)`*, so putting `tup(e⃗ᵢ)` into it needs
//! `tup(e⃗ᵢ) ∈ Idx(p⃗)` — and the index expressions are opaque `FnSym`s, by the
//! same convention that makes the whole spec expressible, so nothing in
//! `derived/` can prove it. Dropping the `w ∈ Idx(p⃗)` conjunct from `Gᵢ` is not
//! an escape: that conjunct is exactly what makes
//! [`super::goodstep`]'s `step_typed` unconditional. So `ni` extra antecedents
//! it is, discharged at the checker boundary where the Lean typing derivation
//! lives. For `RBTree.red` they are `Color.r ∈ Color` — closed — and `n ∈ N`,
//! which is the plain field's own typing and is already in hand.
//!
//! Inversion is unaffected: it reads the equality *out*, and never needs the
//! index tuple to be well typed.
//!
//! # `Eᵢ` pre-discharged, and the antecedent that is left is Lean-positional
//!
//! `INDEXED-DESIGN.md` §8.1 left an open question about exactly this: (M)'s
//! `ni` extra antecedents are *not* positional against the constructor's Lean
//! field spine, so they cannot be appended to a positionally-instantiated
//! premise list, and "either the rule grows a second, subject-addressed premise
//! list, or `Eᵢ` is discharged at rule-build time". [`IndexedCtor::mem_lean`]
//! is the second, and it is general rather than an argument about one
//! constructor:
//!
//! ```text
//! given   wₖ : ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ^ind → eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ))   for k < ni
//! yields  ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ^ind → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)))
//! ```
//!
//! **Why `Hᵢ^ind` is always enough to state `wₖ` at.** `eᵢₖ` is a `FnSym` of
//! arity `np + kᵢ`, so it can mention only the parameters and the **plain**
//! fields — an index expression mentioning a recursive field declines
//! automatically, because a recursive field opens no kernel variable and
//! [`crate::define_abbrev`] refuses a body with a free variable outside its
//! parameter list. So `Eᵢ` is a statement about `p⃗` and `y⃗` alone, the facts
//! that could discharge it are the plain typings, and those are a
//! sub-conjunction of `Hᵢ^ind`. There is never a `wₖ` that needs more than
//! (M) itself already assumes.
//!
//! **No new mathematics.** `mem_lean` is `mem` composed with the caller's
//! witnesses; each `wₖ` is checked against the antecedent `mem` carries,
//! rebuilt from [`IndexedCtor::mem_atoms`], so the two cannot drift.
//!
//! What is left, `Hᵢ^ind`, *is* positional against the Lean spine once it is
//! permuted by the constructor's field mask, and
//! [`IndexedCtor::mem_atoms_lean`] does that: entry `q` is the typing
//! obligation of the constructor's `q`-th Lean field, and it is the antecedent
//! `mem_lean`'s conclusion carries. The carrier's own order (all plains, then
//! all recs) is not the declared order whenever the mask interleaves, which for
//! `RBTree.red` it does.
//!
//! # Why this is the composition D3 was worried about
//!
//! (M) chains, under one ambient hypothesis and at every constructor: a
//! Separation unfolding (`ind(p⃗,x⃗)`'s axiom, backwards), a `wrec` ι
//! ([`super::good`]), a second Separation unfolding (`Gᵢ`'s axiom, backwards),
//! `ni` telescope introductions, `k` literal projections `compⱼ(tup y⃗) = yⱼ`
//! and `m` composite computations `app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)` — or,
//! at a general constructor, `m` of them **under a bounded universal**. (I)
//! is the same chain read right to left. Every one of those is an instance of
//! something that existed; what had no ancestor is the *composition*, and the
//! answer is that it goes through with the ambient hypothesis carried in
//! implication form throughout, exactly as (S3) and (S4) do.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms_at, rec_sets, Inductive};
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{
    carry_under, congr_ctx, gen_under, hyp_conj, hyp_inst, rewrite_under, under,
};
use crate::inductive::Slot;
use crate::sigma::Telescope;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conj_sub, eq_symm, eq_trans, establishes,
    gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl, uncurry,
};

use super::good::{Good, GoodIota, IhRow};
use super::gval::GoodValues;
use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// One constructor of an indexed family: its membership rule and its
/// inversion rule.
pub struct IndexedCtor {
    /// Its position in the declaration.
    pub index: usize,
    /// The declaration's `np` parameter variables — [`Inductive::params`], kept
    /// so that [`IndexedCtor::mem_lean`] can instantiate `mem` and its inputs
    /// back at the working variables without being handed the declaration.
    pub pvs: Vec<FreeVar>,
    /// The `k` plain-field variables — the same ones
    /// [`super::good::GoodIota`] is stated at.
    pub yvs: Vec<FreeVar>,
    /// The `m` recursive-argument variables.
    pub tvs: Vec<FreeVar>,
    /// The `ni` index variables that (I) quantifies over.
    pub xvs: Vec<FreeVar>,
    /// (M)'s antecedent, atom by atom, at the working variables: the `k` plain
    /// typings, then the `m` recursive arguments at their *indexed* types, then
    /// the `ni` result-index typings `Eᵢ`. Exported so a caller discharging it
    /// rebuilds exactly what the theorem carries.
    pub mem_atoms: Vec<Formula>,
    /// The constructor's field mask read as a permutation: the Lean field at
    /// position `q` is typed by [`IndexedCtor::mem_atoms`]`[lean_order[q]]`.
    ///
    /// Length `k + m`; a [`Slot::Plain`] entry of the mask consumes the next
    /// plain typing (positions `0..k` of `mem_atoms`) and a [`Slot::Rec`] entry
    /// the next recursive one (positions `k..k+m`). This is the *only* place
    /// the declared order enters the carrier, which otherwise erases it.
    pub lean_order: Vec<usize>,
    /// `⊢ ∀p⃗∀y⃗∀r⃗. ((Hᵢ^ind ∧ Eᵢ) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)))`.
    pub mem: Thm,
    /// (I)'s antecedent atoms: `Hᵢ^skel`'s atoms, then
    /// `ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)`.
    pub inv_atoms: Vec<Formula>,
    /// `⊢ ∀p⃗∀y⃗∀r⃗∀x⃗. (… → (tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗)) ∧ ⋀ⱼ rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)))`.
    pub inv: Thm,
}

impl IndexedCtor {
    /// The number of Lean fields, `k + m`.
    fn fields(&self) -> usize { self.yvs.len() + self.tvs.len() }

    /// **`Hᵢ^ind` alone, positional against the Lean field spine.**
    ///
    /// Entry `q` is the typing obligation of the constructor's `q`-th declared
    /// field: `yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)` for a plain one, `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))` for
    /// a recursive one. The `ni` result-index typings `Eᵢ` are **not** here —
    /// they are what [`IndexedCtor::mem_lean`] discharges, and they have no
    /// field to be positional against.
    ///
    /// This is [`IndexedCtor::mem_atoms`]`[..k+m]` permuted by
    /// [`IndexedCtor::lean_order`], and it is the antecedent of `mem_lean`'s
    /// conclusion, so a consumer that instantiates premises positionally
    /// against the constructor's spine can use the two together unchanged.
    pub fn mem_atoms_lean(&self) -> Vec<Formula> {
        self.lean_order.iter().map(|q| self.mem_atoms[*q].clone()).collect()
    }

    /// **(M) with `Eᵢ` pre-discharged**, its antecedent in Lean field order:
    ///
    /// ```text
    /// given   ws[k] : ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ^ind → eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ))   for k < ni
    /// yields  ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ^ind → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)))
    /// ```
    ///
    /// **`Hᵢ^ind` is the Lean-ordered spelling on both sides** — literally
    /// `conj_of(self.mem_atoms_lean())`, not [`IndexedCtor::mem`]'s
    /// carrier-ordered antecedent. One order across the whole interface: a
    /// consumer holding the constructor's field typings positionally builds the
    /// `wₖ` out of them and reads the result with them, and never sees the
    /// carrier's plains-then-recs order. Permuting to it is this method's job.
    ///
    /// The antecedent is dropped
    /// entirely, on both sides, for a constructor with no fields at all, where
    /// each `ws[k]` is the unconditional `⊢ ∀p⃗. eᵢₖ(p⃗) ∈ ιₖ(p⃗, e⃗<ₖ)` and the
    /// result is the unconditional `⊢ ∀p⃗. ctorᵢ ∈ ind(p⃗, e⃗ᵢ(p⃗))`.
    ///
    /// **No new mathematics**: this is [`IndexedCtor::mem`] composed with the
    /// caller's witnesses. Each `ws[k]` is checked against the antecedent `mem`
    /// already carries, rebuilt here from [`IndexedCtor::mem_atoms`], and for
    /// an empty hypothesis set; `None` on any mismatch, on the wrong number of
    /// witnesses, and on an output whose shape is not the one documented above.
    ///
    /// See the module header for why `Hᵢ^ind` is always a strong enough
    /// antecedent to state the `wₖ` at.
    ///
    /// # What the witness protocol demands, and who can meet it
    ///
    /// Each `wₖ` must be **closed, prenex, and at this build's own working
    /// variables** — `∀p⃗∀y⃗∀r⃗` in that order, over `pvs`/`yvs`/`tvs`, about
    /// *this* `ind(p⃗,x⃗)`. That is not negotiable and it is not incidental: the
    /// derivation instantiates `mem` and every `wₖ` at the same variable list,
    /// so a witness over a second [`IndexedInductive`](super::IndexedInductive)
    /// would be a true theorem about a carrier no equation relates to this one.
    ///
    /// **It has a consumer, and the consumer is not the production path.**
    /// `mini` calls this for real — with witnesses derived from its own store,
    /// since a test cannot fabricate a `Thm` — and writing that call is what
    /// forced `mini` to stop discarding the index abbreviations' defining
    /// axioms: inference hands back `⟦eₖ⟧ ∈ ⟦Iₖ⟧` at the *interpretations*, and
    /// only those axioms relate it to the statement above at the *symbols*.
    /// What is still absent is the constructor nest that would call it in
    /// anger; the type former is a complete obligation on its own, so `042`
    /// closed without it.
    ///
    /// **One sub-case is general here and unexercised everywhere.** `ιₖ` has
    /// arity `np + k`, so an index *type* may depend on the earlier index
    /// *expressions*, and [`IndexedCtor::mem_atoms`] states `Eₖ` at
    /// `ιₖ(p⃗, e⃗<ₖ)` accordingly — this method passes that through and is
    /// general in it. No corpus declaration exercises it: `RBTree`'s index types
    /// are `Color` and `N`, `Acc`'s is a parameter, and every fixture's are
    /// closed. So a `ιₖ` whose body genuinely mentions `x⃗<ₖ` is untested at
    /// *both* ends, and a consumer meeting one owes a **named decline** rather
    /// than code that looks general. Nothing here needs to change for it; what
    /// is missing is a witness, not a theorem.
    pub fn mem_lean(&self, ws: &[Thm]) -> Option<Thm> {
        let nf = self.fields();
        let ni = self.mem_atoms.len().checked_sub(nf)?;
        if ws.len() != ni || self.lean_order.len() != nf {
            return None
        }

        // The working variables `mem` and every `wₖ` are stated at.
        let mut args: Vec<Term> = self.pvs.iter().map(|v| Term::var(*v)).collect();
        args.extend(self.yvs.iter().map(|v| Term::var(*v)));
        args.extend(self.tvs.iter().map(|v| Term::var(*v)));
        let mem_at = inst_all(&self.mem, &args)?;
        let (want_ante, concl) = mem_at.concl().as_imp()?;
        if want_ante != conj_of(&self.mem_atoms)? {
            return None
        }

        let hind = conj_of(&self.mem_atoms[..nf]);
        let lean = self.mem_atoms_lean();
        let hlean = conj_of(&lean);

        // `⊢ [Hᵢ^ind →] Eₖ`, from the caller, checked against what `mem` asks.
        // The antecedent is the **Lean-ordered** spelling, the same one the
        // conclusion carries: one order across the whole interface.
        let mut idx: Vec<Thm> = Vec::with_capacity(ni);
        for (k, w) in ws.iter().enumerate() {
            let at = inst_all(w, &args)?;
            let want = match &hlean {
                Some(h) => Formula::imp(h.clone(), self.mem_atoms[nf + k].clone()),
                None => self.mem_atoms[nf + k].clone(),
            };
            if !establishes(&at, &want) {
                return None
            }
            idx.push(at);
        }

        let body = match (hlean.clone(), &hind) {
            // The general case: permute the field typings out of the
            // Lean-ordered conjunction, then feed the index typings from them.
            (Some(hl), Some(h)) => {
                let mut inv = vec![usize::MAX; nf];
                for (q, j) in self.lean_order.iter().enumerate() {
                    *inv.get_mut(*j)? = q;
                }
                let mut parts: Vec<Thm> = Vec::with_capacity(nf + ni);
                for j in 0..nf {
                    parts.push(conj_proj(&lean, *inv.get(j).filter(|q| **q != usize::MAX)?)?);
                }
                let to_hind = hyp_conj(&parts)?;
                if *to_hind.concl() != Formula::imp(hl.clone(), h.clone()) {
                    return None
                }
                parts.extend(idx.iter().cloned());
                syl(&hyp_conj(&parts)?, &mem_at)?
            }
            // A constructor with no fields: nothing to permute, and the
            // antecedent disappears on both sides.
            (None, None) => {
                let mut acc = idx.last()?.clone();
                for t in idx[..ni - 1].iter().rev() {
                    acc = crate::and_intro(t, &acc);
                }
                Thm::mp(&mem_at, &acc)?
            }
            _ => return None,
        };

        let want = match hlean {
            Some(hl) => Formula::imp(hl, concl),
            None => concl,
        };
        if !establishes(&body, &want) {
            return None
        }
        let mut quant = self.pvs.clone();
        quant.extend(self.yvs.iter().copied());
        quant.extend(self.tvs.iter().copied());
        Some(gen_all(&quant, &body))
    }
}

/// The indexed family's carrier.
pub struct IndexedCarrier {
    /// The type symbol, of arity `np + ni`.
    pub ty: FnSym,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) ↔ (z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)))`.
    pub ty_ax: Thm,
    /// The `ni` index variables [`IndexedCarrier::carrier`] is stated at.
    pub xvs: Vec<FreeVar>,
    /// `ind(p⃗, x⃗)` at the declaration's parameters and [`IndexedCarrier::xvs`].
    pub carrier: Term,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ W)`.
    pub subset_w: Thm,
    /// **The D6 weakening bridge**: `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ skel(p⃗))`,
    /// the same statement one Leibniz step past the abbreviation. This is what
    /// turns Lean-shaped hypotheses (recursive arguments at *indexed* types)
    /// into the skeleton-shaped hypotheses the erased recursor's (S4) carries.
    pub bridge: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → tup(x⃗) ∈ app(goodrec,z))`.
    pub good_of: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. ((z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)) → z ∈ ind(p⃗,x⃗))`.
    pub intro: Thm,
    /// One entry per constructor.
    pub ctors: Vec<IndexedCtor>,
}

impl IndexedCarrier {
    /// `ind(p⃗, x⃗)` at caller-supplied parameters and indices. `None` unless
    /// the two lists have the declaration's own lengths — a shorter list is a
    /// well-formed term that is not this family.
    pub fn ty_of(&self, ps: &[Term], xs: &[Term]) -> Option<Term> {
        if ps.len() + xs.len() != self.ty.arity() as usize {
            return None
        }
        let mut a = ps.to_vec();
        a.extend(xs.iter().cloned());
        Some(Term::apply(self.ty, a))
    }

    /// Carve the carrier out of the skeleton, and derive (M) and (I).
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ix: &IndexSpace,
        gv: &GoodValues,
        good: &Good,
    ) -> Option<IndexedCarrier> {
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ni = spec.num_indices();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        // ── the Separation ──────────────────────────────────────────────────
        let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let tup_x = IndexedDeclSpec::tup(s, &xs);
        let psi = Formula::mem(tup_x.clone(), ap.apply(good.rec.clone(), tz.clone()));
        let cond = Formula::and(Formula::mem(tz.clone(), ind.wty.clone()), psi.clone());
        let existence = crate::funcs::separation_full(env, zv, &psi, &ind.wty, &ap.empty_ax)?;
        let mut params = ind.params.clone();
        params.extend(xvs.iter().copied());
        let (ty, ty_ax) = crate::define_by_membership(env, &params, &existence, zv, &cond)?;

        let carrier = Term::apply(ty, {
            let mut a = ps.clone();
            a.extend(xs.iter().cloned());
            a
        });

        // ── the four one-line consequences ──────────────────────────────────
        let mut ax_args = ps.clone();
        ax_args.extend(xs.iter().cloned());
        ax_args.push(tz.clone());
        let at = inst_all(&ty_ax, &ax_args)?;
        let mem_w = Formula::mem(tz.clone(), ind.wty.clone());
        let quant = {
            let mut q = params.clone();
            q.push(zv);
            q
        };
        let subset_w = gen_all(
            &quant,
            &syl(&iff_mp(&at)?, &and_left(mem_w.clone(), psi.clone()))?,
        );
        let good_of = gen_all(
            &quant,
            &syl(&iff_mp(&at)?, &and_right(mem_w.clone(), psi.clone()))?,
        );
        let intro = gen_all(&quant, &iff_mpr(&at)?);

        // The bridge: `W` is `skel(p⃗)`, one Leibniz along the erased carrier's
        // defining equation.
        let to_skel = eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?; // ⊢ W = skel(p⃗)
        let bridge = {
            let base = syl(&iff_mp(&at)?, &and_left(mem_w, psi.clone()))?;
            let tzc = tz.clone();
            gen_all(
                &quant,
                &carry_under(env, &to_skel, move |t| Formula::mem(tzc.clone(), t), &base)?,
            )
        };

        // ── the per-constructor rules ───────────────────────────────────────
        let mut ctors = Vec::with_capacity(spec.len());
        for i in 0..spec.len() {
            ctors.push(ctor_rules(
                env,
                mach,
                ind,
                spec,
                ix,
                gv,
                good,
                &Handles { ty, subset_w: &subset_w, good_of: &good_of, intro: &intro },
                i,
            )?);
        }

        Some(IndexedCarrier {
            ty,
            ty_ax,
            xvs,
            carrier,
            subset_w,
            bridge,
            good_of,
            intro,
            ctors,
        })
    }
}

/// The carrier-level facts a constructor rule is built from. Private.
struct Handles<'a> {
    ty: FnSym,
    subset_w: &'a Thm,
    good_of: &'a Thm,
    intro: &'a Thm,
}

/// From `⊢ aⱼ = bⱼ` for each `j`, infer `⊢ ctx(a⃗) = ctx(b⃗)`.
///
/// The `a⃗` appear in `ni` places at once (once per index symbol), which is why
/// this is a context-with-a-list rather than [`congr_ctx`] at a single hole.
fn rewrite_args<F>(env: &mut Env, eqs: &[Thm], ctx: F) -> Option<Thm>
where
    F: Fn(&[Term]) -> Term,
{
    let mut olds = Vec::with_capacity(eqs.len());
    let mut news = Vec::with_capacity(eqs.len());
    for e in eqs {
        let (a, b) = e.concl().as_eq()?;
        olds.push(a);
        news.push(b);
    }
    if eqs.is_empty() {
        return Some(Thm::eq_refl(ctx(&[])))
    }
    let mut acc: Option<Thm> = None;
    for pos in 0..eqs.len() {
        let (news_c, olds_c) = (news.clone(), olds.clone());
        let step = congr_ctx(env, &eqs[pos], |x| {
            let mut a = news_c[..pos].to_vec();
            a.push(x);
            a.extend(olds_c[pos + 1..].iter().cloned());
            ctx(&a)
        })?;
        acc = Some(match acc {
            None => step,
            Some(prev) => eq_trans(env, &prev, &step)?,
        });
    }
    acc
}

/// The `j`-th ih equation of a constructor whose recursive arguments are
/// plain: `⊢ app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)`, unconditional.
///
/// `None` at a general constructor — its row is [`IhRow::Fibre`] and there is
/// no point equation to read, which is the whole content of the split.
fn ih_point(gi: &GoodIota, j: usize) -> Option<&Thm> {
    match &gi.ih {
        IhRow::Point(v) => v.get(j),
        IhRow::Fibre(_) => None,
    }
}

/// The `j`-th ih equation of a **general** constructor at one `z`:
/// `⊢ (H ∧ z ∈ Aⱼ) → app(cmp, Injⱼ z) = app(goodrec, app(rⱼ, z))`.
///
/// `to_skel` is `⊢ H → Hᵢ^ctor`, the caller's own bridge onto the ambient the
/// row is stated under; `kz_h`/`kz_z` split `H ∧ z ∈ Aⱼ`. Both (M) and (I) use
/// this one door, so the forward mirror and the inversion projection cannot
/// rewrite the same slot with two different equations.
fn ih_fibre_at(
    gi: &GoodIota,
    j: usize,
    to_skel: &Thm,
    tz: &Term,
    kz_h: &Thm,
    kz_z: &Thm,
) -> Option<Thm> {
    let row = match &gi.ih {
        IhRow::Fibre(v) => v.get(j)?,
        IhRow::Point(_) => return None,
    };
    let at_h = syl(to_skel, row)?;
    hyp_mp(&syl(kz_h, &hyp_inst(&at_h, std::slice::from_ref(tz))?)?, kz_z)
}

/// (M) and (I) at one constructor.
#[allow(clippy::too_many_arguments)]
fn ctor_rules(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ix: &IndexSpace,
    gv: &GoodValues,
    good: &Good,
    h: &Handles<'_>,
    i: usize,
) -> Option<IndexedCtor> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ni = spec.num_indices();
    let (kk, m) = (spec.base.ctors[i].args.len(), spec.base.ctors[i].recs);
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let gi = &good.at[i];
    let (yvs, tvs) = (gi.yvs.clone(), gi.tvs.clone());
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();

    // The comps of the tag payload, and the equations that read them back.
    let comps: Vec<Term> = (0..kk)
        .map(|j| Telescope::comp_of(ap, &mach.proj, j, gi.tuple.clone()))
        .collect();

    // `ind(p⃗, x⃗)` at an arbitrary index vector.
    let fam_at = |xs: &[Term]| -> Term {
        let mut a = ps.clone();
        a.extend(xs.iter().cloned());
        Term::apply(h.ty, a)
    };
    let res = spec.result_vec(i, &ps, &ys)?;
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, &ps, &ys)).collect::<Option<_>>()?;

    // **The recursive slots' stated sets, at the constructor's own grain.**
    // `None` at every slot of a constructor whose recursive arguments are
    // plain, `Some(Aⱼ)` at every slot of one taking
    // [`RecArg::general`](crate::recarg::RecArg::general) — the degenerate
    // `Aⱼ = 1` included, because that choice is per constructor. This is the
    // same grain [`GoodValues::matrix_atoms`] keys the good-set matrix on and
    // the same one [`rec_sets`] states `Hᵢ^ctor` at, and all three have to
    // agree or the ι rebuilt below is about another conjunction.
    let doms = ind.ctor_slot_domains(i);
    if doms.len() != m {
        return None
    }
    let ra = ind.recargs.get(i)?;
    // `tⱼ ∈ ·` at a plain slot, `tⱼ ∈ fs(Aⱼ, ·)` at a function-typed one.
    let rec_stated = |j: usize, set: Term| -> Term {
        match &doms[j] {
            None => set,
            Some(aj) => s.fs.of(aj.clone(), set),
        }
    };

    // ── (M) ─────────────────────────────────────────────────────────────────
    // The antecedent: plain typings, recursive arguments at their indexed
    // types, then the result-index typings the header explains.
    let mut atoms: Vec<Formula> = (0..kk)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(spec.base.ctors[i].args[j], a))
        })
        .collect();
    for j in 0..m {
        atoms.push(Formula::mem(ts[j].clone(), rec_stated(j, fam_at(&childs[j]))));
    }
    for k in 0..ni {
        atoms.push(Formula::mem(res[k].clone(), spec.index_type_at(k, &ps, &res)?));
    }
    let hm = conj_of(&atoms)?; // `ni ≥ 1`, so never empty

    // The skeleton-shaped hypotheses, via the bridge. **`ctor_atoms_at` at
    // `rec_sets`, not the plain `ctor_atoms` wrapper**: this conjunction has to
    // be the one `Good`'s ι carries, and the two agree only when every slot is
    // plain.
    let skel_atoms =
        ctor_atoms_at(&ind.telescopes[i], &ps, &ys, &ts, &rec_sets(s, ra, &ind.carrier));
    let hyp_skel = conj_of(&skel_atoms);
    let m_skel = match &hyp_skel {
        None => None,
        Some(_) => {
            let mut parts: Vec<Thm> = Vec::with_capacity(kk + m);
            for j in 0..kk {
                parts.push(conj_proj(&atoms, j)?);
            }
            for j in 0..m {
                let child_set = fam_at(&childs[j]);
                let at_w = match &doms[j] {
                    // `tⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` weakens to `tⱼ ∈ W` outright.
                    None => {
                        let mut a = ps.clone();
                        a.extend(childs[j].iter().cloned());
                        a.push(ts[j].clone());
                        syl(&conj_proj(&atoms, kk + j)?, &inst_all(h.subset_w, &a)?)?
                    }
                    // A **function into** the family weakens by the function
                    // space being monotone in its codomain, and the inclusion
                    // it needs is `subset_w` generalised over its subject.
                    Some(aj) => {
                        let zv = env.fresh_var();
                        let mut a = ps.clone();
                        a.extend(childs[j].iter().cloned());
                        a.push(Term::var(zv));
                        let sub = Thm::gen(zv, &inst_all(h.subset_w, &a)?);
                        if *sub.concl()
                            != kernel::thm::subset(env, child_set.clone(), ind.wty.clone())
                        {
                            return None
                        }
                        syl(
                            &hyp_and(&conj_proj(&atoms, kk + j)?, &under(&sub, &hm))?,
                            &inst_all(
                                &mach.wt.fs_mono,
                                &[
                                    aj.clone(),
                                    child_set,
                                    ind.wty.clone(),
                                    ts[j].clone(),
                                ],
                            )?,
                        )?
                    }
                };
                let tj = ts[j].clone();
                let dom = doms[j].clone();
                let to_skel = eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?;
                parts.push(carry_under(
                    env,
                    &to_skel,
                    move |t| {
                        let set = match &dom {
                            None => t,
                            Some(aj) => s.fs.of(aj.clone(), t),
                        };
                        Formula::mem(tj.clone(), set)
                    },
                    &at_w,
                )?);
            }
            Some(hyp_conj(&parts)?)
        }
    };

    // `H → app(goodrec, ctorᵢ) = Gᵢ(p⃗, tup(y⃗), cmp)`.
    let m_iota = match &m_skel {
        Some(t) => syl(t, &gi.eq)?,
        None => under(&gi.eq, &hm),
    };

    // `H → tup(e⃗ᵢ(p⃗,y⃗)) ∈ Idx(p⃗)`, from the result-index typings.
    let tup_res = IndexedDeclSpec::tup(s, &res);
    let m_idx = {
        let mut a = ps.clone();
        a.extend(res.iter().cloned());
        syl(&conj_sub(&atoms, kk + m, kk + m + ni)?, &inst_all(ix.intro(), &a)?)?
    };

    // The base-case equality, and the child memberships, at the *comps*.
    let (psc, resc) = (ps.clone(), i);
    let res_eq = rewrite_args(env, &gi.comp_eqs, |a| {
        IndexedDeclSpec::tup(s, &spec.result_vec(resc, &psc, a).expect("arity ensured"))
    })?;
    let m_eq = under(&eq_symm(env, &res_eq)?, &hm);

    let mut child_thms = Vec::with_capacity(m);
    for j in 0..m {
        // The index tuple, at the plain fields and at the payload's comps, and
        // the equation between them.
        let pb = spec.plains_before(i, j)?;
        let (psc, ic) = (ps.clone(), i);
        let arg_eq = rewrite_args(env, &gi.comp_eqs[..pb], |a| {
            IndexedDeclSpec::tup(s, &spec.rec_index_vec(ic, j, &psc, a).expect("arity ensured"))
        })?;
        let arg_back = eq_symm(env, &arg_eq)?;
        let child_c = IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, &ps, &comps)?);

        let step2 = match &doms[j] {
            // ── a plain slot: one child, at one point of the fibre ──────────
            None => {
                let mut a = ps.clone();
                a.extend(childs[j].iter().cloned());
                a.push(ts[j].clone());
                let gd = syl(&conj_proj(&atoms, kk + j)?, &inst_all(h.good_of, &a)?)?;
                let slot = ap.apply(good.rec.clone(), ts[j].clone());
                let step1 =
                    carry_under(env, &arg_back, move |w| Formula::mem(w, slot.clone()), &gd)?;
                let ih_back = eq_symm(env, ih_point(gi, j)?)?;
                carry_under(env, &ih_back, move |v| Formula::mem(child_c.clone(), v), &step1)?
            }
            // ── a function-typed slot: the whole `Aⱼ`-indexed family ────────
            //
            // The obligation is the matrix's own bounded universal, so the
            // whole of it is proved under `H ∧ z ∈ Aⱼ` and generalised at the
            // end. `app(tⱼ,z)` is the child there, reached by the function
            // space's application rule rather than by being the field.
            Some(aj) => {
                let m_skel_j = m_skel.as_ref()?;
                let zv = env.fresh_var();
                let tz = Term::var(zv);
                let mem_z = Formula::mem(tz.clone(), aj.clone());
                let kz = Formula::and(hm.clone(), mem_z.clone());
                let kz_h = and_left(hm.clone(), mem_z.clone());
                let kz_z = and_right(hm.clone(), mem_z);
                let app_tz = ap.apply(ts[j].clone(), tz.clone());

                // `app(tⱼ, z) ∈ ind(p⃗, d⃗ᵢⱼ)`.
                let k_app = hyp_mp(
                    &a1i(
                        &inst_all(
                            &mach.wt.app_mem,
                            &[
                                aj.clone(),
                                fam_at(&childs[j]),
                                ts[j].clone(),
                                tz.clone(),
                            ],
                        )?,
                        kz.clone(),
                    ),
                    &hyp_and(&syl(&kz_h, &conj_proj(&atoms, kk + j)?)?, &kz_z)?,
                )?;
                // …hence `tup(d⃗ᵢⱼ(y⃗)) ∈ app(goodrec, app(tⱼ,z))`.
                let mut a = ps.clone();
                a.extend(childs[j].iter().cloned());
                a.push(app_tz.clone());
                let gd = syl(&k_app, &inst_all(h.good_of, &a)?)?;
                let slot = ap.apply(good.rec.clone(), app_tz);
                let step1 =
                    carry_under(env, &arg_back, move |w| Formula::mem(w, slot.clone()), &gd)?;

                // The ih row at this `z`, carried in from `Hᵢ^ctor`.
                let ih_z = ih_fibre_at(gi, j, m_skel_j, &tz, &kz_h, &kz_z)?;
                let ih_back = crate::recursion::hyp::hyp_eq_symm(env, &ih_z)?;
                let at_z = rewrite_under(
                    env,
                    &ih_back,
                    move |v| Formula::mem(child_c.clone(), v),
                    &step1,
                )?;
                gen_under(zv, &hm, &uncurry(&at_z)?)?
            }
        };
        child_thms.push(step2);
    }

    // `H → tup(e⃗ᵢ) ∈ Gᵢ(p⃗, tup(y⃗), cmp)`, by the `Gᵢ` axiom backwards.
    let mut g_args = ps.clone();
    g_args.push(gi.tuple.clone());
    g_args.push(gi.cmp.clone());
    g_args.push(tup_res.clone());
    let g_at = inst_all(&gv.axioms[i], &g_args)?;
    let mut matrix_thms = vec![m_eq];
    matrix_thms.extend(child_thms.iter().cloned());
    let m_in_g = hyp_mp(
        &a1i(&iff_mpr(&g_at)?, hm.clone()),
        &hyp_and(&m_idx, &hyp_conj(&matrix_thms)?)?,
    )?;

    // Carry it back along the ι, then put the constructor in the carrier.
    let m_in_app = {
        let back = crate::recursion::hyp::hyp_eq_symm(env, &m_iota)?;
        let tr = tup_res.clone();
        rewrite_under(env, &back, move |v| Formula::mem(tr.clone(), v), &m_in_g)?
    };
    let m_ctor_w = {
        let mut a = ps.clone();
        a.extend(ys.iter().cloned());
        a.extend(ts.iter().cloned());
        let at_skel = match &m_skel {
            Some(t) => syl(t, &inst_all(&ind.ctors[i].mem, &a)?)?,
            None => under(&inst_all(&ind.ctors[i].mem, &a)?, &hm),
        };
        let ctor_c = gi.ctor.clone();
        rewrite_under(
            env,
            &under(&inst_all(&ind.ty_ax, &ps)?, &hm),
            move |t| Formula::mem(ctor_c.clone(), t),
            &at_skel,
        )?
    };
    let mut i_args = ps.clone();
    i_args.extend(res.iter().cloned());
    i_args.push(gi.ctor.clone());
    let mem_body = hyp_mp(
        &a1i(&inst_all(h.intro, &i_args)?, hm.clone()),
        &hyp_and(&m_ctor_w, &m_in_app)?,
    )?;
    if *mem_body.concl() != Formula::imp(hm, Formula::mem(gi.ctor.clone(), fam_at(&res))) {
        return None
    }
    let mut mquant = ind.params.clone();
    mquant.extend(yvs.iter().copied());
    mquant.extend(tvs.iter().copied());
    let mem = gen_all(&mquant, &mem_body);

    // ── (I) ─────────────────────────────────────────────────────────────────
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let tup_x = IndexedDeclSpec::tup(s, &xs);
    let mem_at_x = Formula::mem(gi.ctor.clone(), fam_at(&xs));
    let mut inv_atoms = skel_atoms.clone();
    inv_atoms.push(mem_at_x.clone());
    let hk = conj_of(&inv_atoms)?;

    let (k_skel, k_mem) = match &hyp_skel {
        Some(hs) => (
            Some(syl(&conj_sub(&inv_atoms, 0, kk + m)?, &imp_refl(hs.clone()))?),
            conj_proj(&inv_atoms, kk + m)?,
        ),
        None => (None, imp_refl(mem_at_x.clone())),
    };
    let k_iota = match &k_skel {
        Some(t) => syl(t, &gi.eq)?,
        None => under(&gi.eq, &hk),
    };

    // `K → tup(x⃗) ∈ Gᵢ(p⃗, tup(y⃗), cmp)`.
    let mut g_args = ps.clone();
    g_args.extend(xs.iter().cloned());
    g_args.push(gi.ctor.clone());
    let k_good = syl(&k_mem, &inst_all(h.good_of, &g_args)?)?;
    let k_in_g = {
        let tx = tup_x.clone();
        rewrite_under(env, &k_iota, move |v| Formula::mem(tx.clone(), v), &k_good)?
    };

    let mut ga = ps.clone();
    ga.push(gi.tuple.clone());
    ga.push(gi.cmp.clone());
    ga.push(tup_x.clone());
    let matrix = GoodValues::matrix(env, mach, ind, spec, i, &ps, &gi.tuple, &gi.cmp, &tup_x)?;
    let k_matrix = syl(
        &syl(&k_in_g, &iff_mp(&inst_all(&gv.axioms[i], &ga)?)?)?,
        &and_right(Formula::mem(tup_x.clone(), ix.idx.clone()), matrix),
    )?;
    let matrix_atoms =
        GoodValues::matrix_atoms(env, mach, ind, spec, i, &ps, &gi.tuple, &gi.cmp, &tup_x)?;

    // The base-case equality, moved off the comps.
    let k_eq = {
        let base = syl(&k_matrix, &conj_proj(&matrix_atoms, 0)?)?;
        let tx = tup_x.clone();
        carry_under(env, &res_eq, move |v| Formula::eq(tx.clone(), v), &base)?
    };

    // The children, moved off the comps and off the ih row, then re-typed.
    let mut inv_children = Vec::with_capacity(m);
    for j in 0..m {
        let base = syl(&k_matrix, &conj_proj(&matrix_atoms, 1 + j)?)?;
        let pb = spec.plains_before(i, j)?;
        let (psc, ic) = (ps.clone(), i);
        let arg_eq = rewrite_args(env, &gi.comp_eqs[..pb], |a| {
            IndexedDeclSpec::tup(s, &spec.rec_index_vec(ic, j, &psc, a).expect("arity ensured"))
        })?;
        let child = IndexedDeclSpec::tup(s, &childs[j]);
        // `rⱼ ∈ W` (or `rⱼ ∈ fs(Aⱼ, W)`), from the skeleton hypothesis.
        let k_rw = match &hyp_skel {
            Some(_) => {
                let at = syl(&conj_proj(&inv_atoms, kk + j)?, &imp_refl(skel_atoms[kk + j].clone()))?;
                let tj = ts[j].clone();
                let dom = doms[j].clone();
                rewrite_under(
                    env,
                    &under(&inst_all(&ind.ty_ax, &ps)?, &hk),
                    move |t| {
                        let set = match &dom {
                            None => t,
                            Some(aj) => s.fs.of(aj.clone(), t),
                        };
                        Formula::mem(tj.clone(), set)
                    },
                    &at,
                )?
            }
            None => return None, // `m > 0` forces a non-empty `Hᵢ^skel`
        };

        let mut ia = ps.clone();
        ia.extend(childs[j].iter().cloned());
        inv_children.push(match &doms[j] {
            // ── a plain slot ────────────────────────────────────────────────
            None => {
                let cmp_c = ap.apply(gi.cmp.clone(), mach.syms.inj(j, s.point())?);
                let step1 =
                    carry_under(env, &arg_eq, move |w| Formula::mem(w, cmp_c.clone()), &base)?;
                let ch = child.clone();
                let step2 = carry_under(
                    env,
                    ih_point(gi, j)?,
                    move |v| Formula::mem(ch.clone(), v),
                    &step1,
                )?;
                ia.push(ts[j].clone());
                hyp_mp(
                    &a1i(&inst_all(h.intro, &ia)?, hk.clone()),
                    &hyp_and(&k_rw, &step2)?,
                )?
            }
            // ── a function-typed slot ───────────────────────────────────────
            //
            // The atom read out is a bounded universal, so what comes back is
            // the family's membership **pointwise**; `funspace_retarget` is
            // what turns "every value lands in `ind(p⃗,d⃗ᵢⱼ)`" back into the
            // field being a function into it. That is the exact converse of
            // the `fs_mono` step (M) took in the other direction.
            Some(aj) => {
                let k_skel_j = k_skel.as_ref()?;
                let zv = env.fresh_var();
                let tz = Term::var(zv);
                let mem_z = Formula::mem(tz.clone(), aj.clone());
                let kz = Formula::and(hk.clone(), mem_z.clone());
                let kz_h = and_left(hk.clone(), mem_z.clone());
                let kz_z = and_right(hk.clone(), mem_z);
                let app_tz = ap.apply(ts[j].clone(), tz.clone());

                // The atom, instantiated at this `z`.
                let at_z = hyp_mp(
                    &syl(&kz_h, &hyp_inst(&base, std::slice::from_ref(&tz))?)?,
                    &kz_z,
                )?;
                let cmp_c = ap.apply(gi.cmp.clone(), mach.syms.inj(j, tz.clone())?);
                let step1 =
                    carry_under(env, &arg_eq, move |w| Formula::mem(w, cmp_c.clone()), &at_z)?;
                let ih_z = ih_fibre_at(gi, j, k_skel_j, &tz, &kz_h, &kz_z)?;
                let ch = child.clone();
                let step2 =
                    rewrite_under(env, &ih_z, move |v| Formula::mem(ch.clone(), v), &step1)?;

                // `app(rⱼ, z) ∈ W`, then in the family at `d⃗ᵢⱼ`.
                let k_app = hyp_mp(
                    &a1i(
                        &inst_all(
                            &mach.wt.app_mem,
                            &[aj.clone(), ind.wty.clone(), ts[j].clone(), tz.clone()],
                        )?,
                        kz.clone(),
                    ),
                    &hyp_and(&syl(&kz_h, &k_rw)?, &kz_z)?,
                )?;
                let mut ja = ia.clone();
                ja.push(app_tz);
                let in_fam = hyp_mp(
                    &a1i(&inst_all(h.intro, &ja)?, kz.clone()),
                    &hyp_and(&k_app, &step2)?,
                )?;
                let vals = gen_under(zv, &hk, &uncurry(&in_fam)?)?;
                hyp_mp(
                    &a1i(
                        &inst_all(
                            &mach.wt.retarget,
                            &[
                                aj.clone(),
                                ind.wty.clone(),
                                fam_at(&childs[j]),
                                ts[j].clone(),
                            ],
                        )?,
                        hk.clone(),
                    ),
                    &hyp_and(&k_rw, &vals)?,
                )?
            }
        });
    }

    let mut concl_thms = vec![k_eq];
    concl_thms.extend(inv_children);
    let inv_body = hyp_conj(&concl_thms)?;
    let mut want_atoms = vec![Formula::eq(tup_x, tup_res)];
    for j in 0..m {
        want_atoms.push(Formula::mem(ts[j].clone(), rec_stated(j, fam_at(&childs[j]))));
    }
    if *inv_body.concl() != Formula::imp(hk, conj_of(&want_atoms)?) {
        return None
    }
    let mut iquant = mquant.clone();
    iquant.extend(xvs.iter().copied());
    let inv = gen_all(&iquant, &inv_body);

    // The field mask, read as a permutation of the carrier's atom order.
    let mut lean_order = Vec::with_capacity(kk + m);
    let (mut plains, mut recs) = (0usize, 0usize);
    for slot in &spec.base.ctors[i].order {
        match slot {
            Slot::Plain => {
                lean_order.push(plains);
                plains += 1;
            }
            Slot::Rec => {
                lean_order.push(kk + recs);
                recs += 1;
            }
        }
    }
    if plains != kk || recs != m {
        return None
    }

    Some(IndexedCtor {
        index: i,
        pvs: ind.params.clone(),
        yvs,
        tvs,
        xvs,
        mem_atoms: atoms,
        lean_order,
        mem,
        inv_atoms,
        inv,
    })
}
