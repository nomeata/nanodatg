//! **Class (P)** — §5.2's small-eliminator clause, `‖·‖` of the lifted carrier.
//!
//! # The rule, and what is left to do once it is read carefully
//!
//! `thesis.txt:1813–1815`:
//!
//! ```text
//! Γ; t : F ⊢ K spec    ¬(Γ; t : ∀x :: α. U_ℓ ⊢ K LE)
//! ────────────────────────────────────────────────────────────────
//! Γ ⊢ ⟦µt : ∀x :: α. U_ℓ. K⟧ = λx :: α. ulift_ℓ ‖⟦µt : ∀x :: α. U_{ℓ'}. K⟧ x‖
//! ```
//!
//! with `ℓ'` the maximum of `1` and the constructor arguments' levels. Three
//! things sit inside that, and **all three already existed**, which is why this
//! file is composition:
//!
//! 1. `⟦µt : ∀x :: α. U_{ℓ'}. K⟧` — the ordinary §5.2 translation, at the
//!    *lifted* universe. [`super::IndexedCarrier`] for an indexed declaration,
//!    [`Inductive`] for a non-indexed one.
//! 2. `‖·‖` — [`Trunc`], `‖a‖ = [∃x. x ∈ a]`.
//! 3. `ulift_ℓ` — **nothing**. `thesis.txt:2106–2108` gives
//!    `⟦ulift_n^n α⟧ = ⟦α⟧` and `⟦↑e⟧ = ⟦↓e⟧ = ⟦e⟧`: `ulift` is the identity on
//!    interpretations, so raising the target universe to `ℓ'` and lowering the
//!    result back to `ℓ` are both no-ops on the *sets*. Checked against the
//!    thesis rather than assumed, because it is the step that makes this file
//!    short.
//!
//! Point 3 has a corollary worth naming: since the level never enters the
//! carrier — a §5.2 carrier is a Separation out of `W`, and `W`'s definition
//! mentions no universe beyond its own bound — the *same* [`IndexedCarrier`]
//! serves as the translation at `ℓ` and at `ℓ'`. There is no second W-type to
//! build and no re-derivation at another level. The level reappears only in the
//! universe-membership theorem, and there class (P) is *cheaper* than class (T)
//! rather than more expensive: [`TruncCarrier::in_u0`] needs no size argument
//! about `W` at all, because `‖a‖ ⊆ 1` holds whatever `a` is.
//!
//! # The branch decider is the eliminator trichotomy
//!
//! `INDEXED-DESIGN.md` §2.1: class (P) is "resultant level possibly 0, and the
//! recursor **not** large-eliminating — motive `Sort 0`, no extra level
//! parameter". Neither `numIndices` nor `k` nor the constructor count decides
//! it, so this file is deliberately indifferent to all three and offers two
//! entry points that differ only in what is being truncated:
//!
//! * [`TruncCarrier::over_family`] — an indexed declaration, over
//!   [`super::IndexedCarrier`];
//! * [`TruncCarrier::over_declaration`] — a non-indexed one, over
//!   [`Inductive`] directly.
//!
//! That is the opposite of [`super::spec`]'s policy for class (T), where
//! `ni = 0` is declined on the grounds that routing it through a vacuous
//! Separation would re-derive the zero-gap fragment. Here nothing is
//! re-derived: the truncation is one symbol application on top of a carrier
//! that already exists, so the non-indexed case costs a `Vec` and is served.
//!
//! # Corpus demand — decoded, not assumed
//!
//! Decoding every `inductive` record in every export in this repository and
//! classifying by `rec.levelParams` against the declaration's own gives
//! **thirteen** class-(P) declarations, six indexed and seven not:
//!
//! | declaration | np | ni | ctors | rec? | where |
//! |---|---|---|---|---|---|
//! | `SortElimProp2` | 1 | 2 | 1 | no | `072` |
//! | `Nat.le` | 1 | 1 | 2 | yes | `init-prelude`, `grind-ring-5`, `alg-conv-trans-acc-*` |
//! | `Nat.le.below` | 2 | 2 | 2 | yes | `init-prelude`, `grind-ring-5` |
//! | `List.Mem` | 2 | 1 | 2 | yes | `grind-ring-5` |
//! | `Int.NonNeg` | 0 | 1 | 1 | no | `grind-ring-5` |
//! | `Prod.Lex` | 4 | 2 | 2 | no | `grind-ring-5` |
//! | `Or` | 2 | 0 | 2 | no | `init-prelude`, `grind-ring-5` |
//! | `Exists` | 2 | 0 | 1 | no | `070`, `grind-ring-5` |
//! | `Nonempty` | 1 | 0 | 1 | no | `init-prelude`, `grind-ring-5` |
//! | `ByteArray.IsValidUTF8` | 1 | 0 | 1 | no | `init-prelude`, `grind-ring-5` |
//! | `BoolProp` | 0 | 0 | 2 | no | `069` |
//! | `PropStructure` | 0 | 0 | 1 | no | `084`, `086` |
//! | `PredWithTypeField` | 0 | 0 | 1 | no | `055` |
//!
//! Two corrections to what was believed when this file was written:
//!
//! * **"two constructors, therefore not large-eliminating" is not the reason.**
//!   `SortElimProp2`, `Exists`, `Nonempty`, `Int.NonNeg` and
//!   `ByteArray.IsValidUTF8` all have exactly **one** constructor and are still
//!   not LE, while one-constructor `And`, `Eq`, `Acc` and `SortElimProp` *are*.
//!   The constructor count is not the test; `rec.levelParams` is, and it is
//!   read, never recomputed (`INDEXED-DESIGN.md` §2.1's threat model).
//! * **`super::le`'s header undercounts.** It records `Nat.le` and
//!   `Nat.le.below` as the prelude's class-(P) pair; the seven non-indexed
//!   entries above are class (P) too, and `Or` and `Nonempty` are in the
//!   prelude beside them. Corrected there.
//!
//! `Nat.le`, `Nat.le.below` and `List.Mem` are **recursive** class-(P)
//! declarations, which is why [`TruncCtor::trunc_mem`] exists: a recursive
//! argument of a `Prop`-valued family is itself a *proof*, so its Lean-shaped
//! hypothesis is `• ∈ ‖ind(p⃗, d⃗ᵢⱼ)‖`, not `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ)`, and the two are
//! separated by an existential elimination that is the only genuinely new
//! derivation in this file.
//!
//! # Interface
//!
//! Writing `a` for the underlying carrier — `ind(p⃗,x⃗)` or `ind(p⃗)` — and `‖a‖`
//! for [`TruncCarrier::carrier`]:
//!
//! ```text
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ ↔ (z ∈ 1 ∧ ∃w. w ∈ a))                [TruncCarrier::ty_ax]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ → z ∈ 1)                              [TruncCarrier::subset_unit]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ → z = •)                              [TruncCarrier::only_point]
//! ⊢ ∀p⃗∀x⃗∀u∀v. ((u ∈ ‖a‖ ∧ v ∈ ‖a‖) → u = v)                [TruncCarrier::irrel]
//! ⊢ ∀p⃗∀x⃗. (• ∈ ‖a‖ → ∃w. w ∈ a)                            [TruncCarrier::elim]
//! ⊢ ∀p⃗∀x⃗. ‖a‖ ∈ U₀                                          [TruncCarrier::in_u0]
//!
//! per constructor, with Hᵢ the underlying carrier's own antecedent:
//! ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)                        [TruncCtor::mem]
//! ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → ‖ind(p⃗, e⃗ᵢ)‖ = 1)                        [TruncCtor::is_unit]
//! ⊢ ∀p⃗∀y⃗.   (Hᵢ^‖‖ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)                     [TruncCtor::trunc_mem]
//!
//! and, at an index no constructor reaches:
//! ⊢ ∀p⃗. ‖ind(p⃗,x⃗)‖ = 0                                      [TruncCarrier::empty_at]
//! ```
//!
//! `Hᵢ^‖‖` is `Hᵢ` with each recursive atom `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` replaced by
//! `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖`, and the `r⃗` accordingly gone from the quantifier prefix.
//!
//! # The recursor: ι is [`Trunc::irrel`], and that is the whole of it
//!
//! A class-(P) recursor's motive is `Sort 0`, so both sides of its ι live in a
//! `Prop` interpretation, and `thesis.txt:2114` makes the eliminator's value
//! literally `•`. [`TruncCarrier::only_point`] is the set-level content: *every*
//! inhabitant of the carrier is `•`, so `⟦rec … (ctorᵢ …)⟧ = ⟦minorᵢ …⟧` is
//! `• = •` and holds by reflexivity. There is no recursor set to build, no minor
//! nest, and no step function — which is exactly what [`Trunc`]'s own header
//! predicted ("the large eliminator does not exist … there is no recursor set to
//! build"). What a caller needs in order to *type* the ι is
//! [`TruncCarrier::irrel`], and it is one instantiation of [`Trunc::irrel`].
//!
//! # Non-vacuity, and why it has to cut both ways here
//!
//! A truncated carrier is a subset of `{•}`, so a construction that returned the
//! constant `1` and a construction that returned the constant `0` would each
//! satisfy every *membership* theorem the other could not, and a careless test
//! would pass against either. Both polarities are therefore pinned as
//! **equations at concrete sets**, not as memberships:
//! [`TruncCtor::is_unit`] gives `‖ind(p⃗,e⃗ᵢ)‖ = 1` at an index a constructor
//! reaches, [`TruncCarrier::empty_at`] gives `‖ind(p⃗,x⃗)‖ = 0` at one no
//! constructor reaches, and `⊢ ¬(0 = 1)` ([`Sums::tags_distinct`]) turns the
//! pair into "these are different sets". That is stronger than
//! `• ∈ ‖…‖` plus `¬(• ∈ ‖…‖)` and costs the same, because
//! [`crate::prop::cond_true`] and [`crate::prop::cond_false`] apply to `‖·‖`
//! verbatim — it is a conditional singleton.
//!
//! [`Sums::tags_distinct`]: crate::sums::Sums::tags_distinct

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms_at, rec_sets, Inductive};
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{hyp_conj, hyp_ex_branch};
use crate::prop::cond::{cond_false, cond_true};
use crate::prop::trunc::Trunc;
use crate::sums::Sums;
use crate::tower::Tower;
use crate::{
    and_left, and_right, conj_of, conj_proj, exists_intro_imp, gen_all, hyp_mp, inst_all,
    notnot_intro, syl,
};

use super::carrier::IndexedCarrier;

/// One constructor of a class-(P) declaration.
pub struct TruncCtor {
    /// Its position in the declaration.
    pub index: usize,
    /// The `k` plain-field variables.
    pub yvs: Vec<FreeVar>,
    /// The `m` recursive-argument variables. Quantified by [`TruncCtor::mem`]
    /// and [`TruncCtor::is_unit`]; **absent** from [`TruncCtor::trunc_mem`],
    /// which is the point of that theorem.
    pub tvs: Vec<FreeVar>,
    /// `Hᵢ`'s atoms — the underlying carrier's own antecedent, verbatim.
    pub mem_atoms: Vec<Formula>,
    /// `⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)` — the typing of `|ctorᵢ …|`.
    pub mem: Thm,
    /// `⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → ‖ind(p⃗, e⃗ᵢ)‖ = 1)` — **non-vacuity**, positive
    /// polarity, at a concrete set.
    pub is_unit: Thm,
    /// `Hᵢ^‖‖`'s atoms: `Hᵢ` with each recursive atom truncated.
    pub trunc_atoms: Vec<Formula>,
    /// `⊢ ∀p⃗∀y⃗. (Hᵢ^‖‖ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)` — the **Lean-shaped** rule, whose
    /// recursive hypotheses are proofs rather than elements.
    pub trunc_mem: Thm,
}

/// A class-(P) declaration's carrier: `‖·‖` of the §5.2 translation.
pub struct TruncCarrier {
    /// The `ni` index variables the carrier is stated at — empty for a
    /// non-indexed declaration.
    pub xvs: Vec<FreeVar>,
    /// `a` — the underlying §5.2 carrier, `ind(p⃗,x⃗)` or `ind(p⃗)`.
    pub base: Term,
    /// `‖a‖`, the class-(P) carrier.
    pub carrier: Term,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ ↔ (z ∈ 1 ∧ ∃w. w ∈ a))`.
    pub ty_ax: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ → z ∈ 1)` — the carrier is a `Prop`.
    pub subset_unit: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ‖a‖ → z = •)` — every inhabitant is the point, which is
    /// what makes the recursor's ι reflexivity.
    pub only_point: Thm,
    /// `⊢ ∀p⃗∀x⃗∀u∀v. ((u ∈ ‖a‖ ∧ v ∈ ‖a‖) → u = v)` — proof irrelevance.
    pub irrel: Thm,
    /// `⊢ ∀p⃗∀x⃗. (• ∈ ‖a‖ → ∃w. w ∈ a)` — soundness: the truncation is not
    /// vacuously inhabited.
    pub elim: Thm,
    /// `⊢ ∀p⃗∀x⃗. ‖a‖ ∈ U₀`, with **no antecedent and no size argument**.
    pub in_u0: Thm,
    /// One entry per constructor, in declaration order.
    pub ctors: Vec<TruncCtor>,
    /// The parameter variables everything above is stated at.
    params: Vec<FreeVar>,
}

/// One constructor's input to [`build`], read off whichever carrier is being
/// truncated. Private: the two entry points are the interface.
struct CtorInput {
    index: usize,
    yvs: Vec<FreeVar>,
    tvs: Vec<FreeVar>,
    /// `Hᵢ`'s atoms — `k` plain typings, then the `m` recursive ones, then
    /// whatever else the underlying rule carries (`Eᵢ`, for the indexed route).
    atoms: Vec<Formula>,
    /// `⊢ [Hᵢ →] ctorᵢ(y⃗,r⃗) ∈ target`, at the working variables.
    body: Thm,
}

impl TruncCarrier {
    /// Class (P) over an **indexed** declaration.
    ///
    /// `ixc` must be [`IndexedCarrier::build`] over `ind`, and `tr`/`tow` must
    /// be built over the same [`Sums`] as `mach` — otherwise the `1` this
    /// speaks about is not the one [`Trunc`] speaks about, and every shape
    /// check below fails rather than producing a theorem about two different
    /// unit sets.
    pub fn over_family(
        env: &mut Env,
        mach: &Machine,
        tow: &Tower,
        tr: &Trunc,
        ind: &Inductive,
        ixc: &IndexedCarrier,
    ) -> Option<TruncCarrier> {
        if !ind.is_over(mach) || ixc.xvs.is_empty() {
            return None
        }
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let xs: Vec<Term> = ixc.xvs.iter().map(|v| Term::var(*v)).collect();
        let base = ixc.ty_of(&ps, &xs)?;

        let mut inputs = Vec::with_capacity(ixc.ctors.len());
        for c in &ixc.ctors {
            let mut args = ps.clone();
            args.extend(c.yvs.iter().map(|v| Term::var(*v)));
            args.extend(c.tvs.iter().map(|v| Term::var(*v)));
            inputs.push(CtorInput {
                index: c.index,
                yvs: c.yvs.clone(),
                tvs: c.tvs.clone(),
                atoms: c.mem_atoms.clone(),
                body: inst_all(&c.mem, &args)?,
            });
        }
        build(env, mach, tow, tr, &ind.params, &ixc.xvs, base, &inputs)
    }

    /// Class (P) over a **non-indexed** declaration — `Or`, `Exists`,
    /// `Nonempty` and the four one-off tutorial `Prop`s.
    ///
    /// The carrier being truncated is [`Inductive::carrier`] itself, and the
    /// constructor rules are [`crate::inductive::Ctor::mem`]. A nullary
    /// constructor's rule has no antecedent at all; that is carried through
    /// rather than manufactured into a vacuous conjunction.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        tow: &Tower,
        tr: &Trunc,
        ind: &Inductive,
    ) -> Option<TruncCarrier> {
        if !ind.is_over(mach) || ind.ctors.is_empty() {
            return None
        }
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        let mut inputs = Vec::with_capacity(ind.ctors.len());
        for c in &ind.ctors {
            let ys: Vec<Term> = c.args.iter().map(|v| Term::var(*v)).collect();
            let ts: Vec<Term> = c.recs.iter().map(|v| Term::var(*v)).collect();
            let atoms = ctor_atoms_at(
                &ind.telescopes[c.index],
                &ps,
                &ys,
                &ts,
                &rec_sets(&mach.wt.sums, ind.recargs.get(c.index)?, &ind.carrier),
            );
            if conj_of(&atoms) != c.hyp {
                return None
            }
            let mut args = ps.clone();
            args.extend(ys.iter().cloned());
            args.extend(ts.iter().cloned());
            inputs.push(CtorInput {
                index: c.index,
                yvs: c.args.clone(),
                tvs: c.recs.clone(),
                atoms,
                body: inst_all(&c.mem, &args)?,
            });
        }
        build(env, mach, tow, tr, &ind.params, &[], ind.carrier.clone(), &inputs)
    }

    /// `⊢ ∀p⃗. ‖ind(p⃗,x⃗)‖ = 0` — **non-vacuity**, negative polarity.
    ///
    /// `empty` must be [`super::empty_at_index`]'s output at the index terms
    /// `xs`: `⊢ ∀p⃗ ∀z. ¬(z ∈ ind(p⃗,x⃗))`, unconditional. The truncation of an
    /// empty set is the empty set, so the answer is a *different set* from
    /// [`TruncCtor::is_unit`]'s, and `⊢ ¬(0 = 1)` says so.
    ///
    /// `at` is the underlying carrier at those index terms — `ixc.ty_of(p⃗, x⃗)`
    /// — which this cannot rebuild, since it does not hold the
    /// [`IndexedCarrier`].
    pub fn empty_at(
        &self,
        env: &mut Env,
        s: &Sums,
        tr: &Trunc,
        at: &Term,
        empty: &Thm,
    ) -> Option<Thm> {
        if !empty.hyps().is_empty() {
            return None
        }
        let ps: Vec<Term> = self.params.iter().map(|v| Term::var(*v)).collect();
        let all_z = inst_all(empty, &ps)?;
        if !all_z.concl().is_forall() {
            return None
        }
        // `⊢ ∀z. ¬(z ∈ a)` is `⊢ ¬(∃z. z ∈ a)` after one double negation, since
        // `∃` *is* `¬∀¬` and bound-variable names are erased by the kernel.
        let not_phi = Thm::mp(&notnot_intro(all_z.concl().clone()), &all_z)?;
        let phi = condition(env, at);
        if *not_phi.concl() != Formula::not(phi.clone()) {
            return None
        }
        let c = tr.of(at.clone());
        let chi = inst_all(&tr.trunc_ax, std::slice::from_ref(at))?;
        let out = Thm::mp(&cond_false(env, s, &phi, &c, &chi)?, &not_phi)?;
        if *out.concl() != Formula::eq(c, s.zero()) {
            return None
        }
        Some(gen_all(&self.params, &out))
    }
}

/// `∃w. w ∈ a` — [`Trunc`]'s own condition at `a`.
///
/// Rebuilt at a fresh variable rather than read out of [`Trunc::trunc_ax`],
/// which is sound because [`Formula::forall`] abstracts to a de Bruijn index and
/// discards the binder's name: this formula is *identical* to the one `Trunc`
/// was defined with. If it were not, every [`crate::prop::cond`] call below
/// would refuse it — `chi_at` compares the rebuilt guard against the stored
/// characteristic theorem — so the assumption cannot silently hold wrong.
fn condition(env: &mut Env, a: &Term) -> Formula {
    let w = env.fresh_var();
    Formula::exists(w, Formula::mem(Term::var(w), a.clone()))
}

/// The shared core: truncate `base`, and re-derive each constructor rule
/// through [`Trunc::intro`] and (for the recursive ones) [`Trunc::elim`].
#[allow(clippy::too_many_arguments)]
fn build(
    env: &mut Env,
    mach: &Machine,
    tow: &Tower,
    tr: &Trunc,
    params: &[FreeVar],
    xvs: &[FreeVar],
    base: Term,
    inputs: &[CtorInput],
) -> Option<TruncCarrier> {
    let s = &mach.wt.sums;
    let carrier = tr.of(base.clone());
    let (one, pt) = (s.unit(), s.point());

    let mut quant: Vec<FreeVar> = params.to_vec();
    quant.extend(xvs.iter().copied());

    // ── the six one-liners, each one instantiation of a `Trunc` theorem ──────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mut zquant = quant.clone();
    zquant.push(zv);

    let ty_ax = gen_all(&zquant, &inst_all(&tr.trunc_ax, &[base.clone(), tz.clone()])?);
    let sub_at = inst_all(&tr.subset, &[base.clone(), tz.clone()])?;
    if *sub_at.concl() != Formula::imp(
        Formula::mem(tz.clone(), carrier.clone()),
        Formula::mem(tz.clone(), one.clone()),
    ) {
        return None
    }
    let subset_unit = gen_all(&zquant, &sub_at);
    let only_point = gen_all(
        &zquant,
        &syl(&sub_at, &inst_all(&s.unit_eta, std::slice::from_ref(&tz))?)?,
    );

    let (uv, vv) = (env.fresh_var(), env.fresh_var());
    let mut uvquant = quant.clone();
    uvquant.extend([uv, vv]);
    let irrel = gen_all(
        &uvquant,
        &inst_all(&tr.irrel, &[base.clone(), Term::var(uv), Term::var(vv)])?,
    );

    let elim = gen_all(&quant, &inst_all(&tr.elim, std::slice::from_ref(&base))?);

    // `‖a‖ ∈ U₀` — a conditional singleton is a truth value, whatever `a` is.
    // No `W`, no `C₂`, no antecedent: this is where class (P) is *cheaper* than
    // class (T) rather than more expensive.
    let phi = condition(env, &base);
    let chi = inst_all(&tr.trunc_ax, std::slice::from_ref(&base))?;
    let in_u0_body = tow.cond_in_u0(env, &phi, &carrier, &chi)?;
    if *in_u0_body.concl() != Formula::mem(carrier.clone(), tow.u0()) {
        return None
    }
    let in_u0 = gen_all(&quant, &in_u0_body);

    // ── the constructor rules ────────────────────────────────────────────────
    let mut ctors = Vec::with_capacity(inputs.len());
    for inp in inputs {
        ctors.push(ctor_rule(env, s, tr, params, inp, &pt)?);
    }

    Some(TruncCarrier {
        xvs: xvs.to_vec(),
        base,
        carrier,
        ty_ax,
        subset_unit,
        only_point,
        irrel,
        elim,
        in_u0,
        ctors,
        params: params.to_vec(),
    })
}

/// The three rules at one constructor.
fn ctor_rule(
    env: &mut Env,
    s: &Sums,
    tr: &Trunc,
    params: &[FreeVar],
    inp: &CtorInput,
    pt: &Term,
) -> Option<TruncCtor> {
    let hyp = conj_of(&inp.atoms);
    let (kk, m) = (inp.yvs.len(), inp.tvs.len());

    // `⊢ [Hᵢ →] ctorᵢ ∈ target` — the constructor term and the carrier it lands
    // in are *read off* the underlying rule rather than rebuilt, so the index
    // expressions `e⃗ᵢ` never have to be re-applied here.
    let concl = match &hyp {
        Some(h) => {
            let (a, c) = inp.body.concl().as_imp()?;
            if a != *h {
                return None
            }
            c
        }
        None => inp.body.concl().clone(),
    };
    let (ctor, target) = concl.as_mem()?;

    // `⊢ [Hᵢ →] φ`, where `φ = ∃w. w ∈ target`: the constructor is the witness.
    let wv = env.fresh_var();
    let phi = Formula::exists(wv, Formula::mem(Term::var(wv), target.clone()));
    let witness =
        exists_intro_imp(wv, Formula::mem(Term::var(wv), target.clone()), ctor.clone())?;
    let h_phi = match &hyp {
        Some(_) => syl(&inp.body, &witness)?,
        None => Thm::mp(&witness, &inp.body)?,
    };

    let c = tr.of(target.clone());
    let chi = inst_all(&tr.trunc_ax, std::slice::from_ref(&target))?;

    // `mem`: `Trunc::intro` at the constructor.
    let intro_at = inst_all(&tr.intro, &[target.clone(), ctor.clone()])?;
    let mem_body = match &hyp {
        Some(_) => syl(&inp.body, &intro_at)?,
        None => Thm::mp(&intro_at, &inp.body)?,
    };
    let want_mem = Formula::mem(pt.clone(), c.clone());
    if *mem_body.concl() != imp_opt(&hyp, want_mem.clone()) {
        return None
    }

    // `is_unit`: the same witness through `cond_true`. The *equation* is what
    // makes non-vacuity bite; the membership above would survive `‖·‖` being
    // constantly `1`.
    let unit_body = syl_opt(&hyp, &h_phi, &cond_true(env, s, &phi, &c, &chi)?)?;
    if *unit_body.concl() != imp_opt(&hyp, Formula::eq(c.clone(), s.unit())) {
        return None
    }

    let mut mquant = params.to_vec();
    mquant.extend(inp.yvs.iter().copied());
    mquant.extend(inp.tvs.iter().copied());
    let mem = gen_all(&mquant, &mem_body);
    let is_unit = gen_all(&mquant, &unit_body);

    // ── the Lean-shaped rule ────────────────────────────────────────────────
    let (trunc_atoms, trunc_body) =
        truncated_rule(tr, &inp.atoms, &mem_body, &want_mem, kk, m, &inp.tvs, pt)?;
    let mut tquant = params.to_vec();
    tquant.extend(inp.yvs.iter().copied());
    let trunc_mem = gen_all(&tquant, &trunc_body);

    Some(TruncCtor {
        index: inp.index,
        yvs: inp.yvs.clone(),
        tvs: inp.tvs.clone(),
        mem_atoms: inp.atoms.clone(),
        mem,
        is_unit,
        trunc_atoms,
        trunc_mem,
    })
}

/// **The one genuinely new derivation.** From
/// `⊢ (H₀ ∧ … ∧ recⱼ ∧ … ) → • ∈ ‖target‖`, in which each `recⱼ` names an
/// *element* `rⱼ` of the child carrier, infer the rule whose recursive
/// hypotheses are the child carriers' own **truncations**:
///
/// ```text
/// ⊢ (H₀ ∧ … ∧ • ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖ ∧ … ) → • ∈ ‖target‖
/// ```
///
/// with the `r⃗` gone. This is what a `Prop`-valued recursive declaration
/// actually needs: `Nat.le.step`'s recursive argument is a *proof* of
/// `Nat.le n m`, and the only thing a caller can supply about it is that the
/// proposition is inhabited.
///
/// The derivation is `m` nested existential eliminations. `Trunc::elim` turns
/// `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖` into `∃rⱼ. rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)`, and
/// [`hyp_ex_branch`] discharges each witness in turn — legal because `rⱼ` is
/// free in neither the truncated antecedent nor the conclusion, both of which
/// mention only the parameters and the plain fields.
#[allow(clippy::too_many_arguments)]
fn truncated_rule(
    tr: &Trunc,
    atoms: &[Formula],
    mem_body: &Thm,
    want: &Formula,
    kk: usize,
    m: usize,
    tvs: &[FreeVar],
    pt: &Term,
) -> Option<(Vec<Formula>, Thm)> {
    // The truncated antecedent: each recursive atom `rⱼ ∈ cⱼ` becomes
    // `• ∈ ‖cⱼ‖`, everything else is untouched.
    let mut children = Vec::with_capacity(m);
    let mut trunc_atoms = atoms.to_vec();
    for j in 0..m {
        let (r, child) = atoms.get(kk + j)?.as_mem()?;
        if r != Term::var(tvs[j]) {
            return None
        }
        trunc_atoms[kk + j] = Formula::mem(pt.clone(), tr.of(child.clone()));
        children.push(child);
    }
    if m == 0 {
        return Some((trunc_atoms, mem_body.clone()))
    }
    let hmp = conj_of(&trunc_atoms)?;

    // `H_0 = Hᵢ^‖‖`, `H_{t+1} = H_t ∧ recₜ`. The base case is `⊢ H_m → •∈‖…‖`.
    let mut levels = vec![hmp.clone()];
    for j in 0..m {
        levels.push(Formula::and(levels[j].clone(), atoms[kk + j].clone()));
    }
    // `⊢ H_{t+1} → H_t`, one `and_left` each.
    let step: Vec<Thm> = (0..m)
        .map(|t| and_left(levels[t].clone(), atoms[kk + t].clone()))
        .collect();

    // `⊢ H_m → H_t` (`from_m`) and `⊢ H_t → H_0` (`to_base`), both by folding.
    let mut from_m: Vec<Thm> = vec![crate::imp_refl(levels[m].clone()); m + 1];
    for t in (0..m).rev() {
        from_m[t] = syl(&from_m[t + 1], &step[t])?;
    }
    let mut to_base: Vec<Thm> = vec![crate::imp_refl(levels[0].clone()); m + 1];
    for t in 0..m {
        to_base[t + 1] = syl(&step[t], &to_base[t])?;
    }

    // Every atom of `Hᵢ`, under `H_m`: the plain ones and the trailing ones out
    // of `Hᵢ^‖‖`, the recursive ones out of their own `∧` layer.
    let mut parts: Vec<Thm> = Vec::with_capacity(atoms.len());
    for j in 0..kk {
        parts.push(syl(&from_m[0], &conj_proj(&trunc_atoms, j)?)?);
    }
    for t in 0..m {
        let right = and_right(levels[t].clone(), atoms[kk + t].clone());
        parts.push(syl(&from_m[t + 1], &right)?);
    }
    for j in kk + m..atoms.len() {
        parts.push(syl(&from_m[0], &conj_proj(&trunc_atoms, j)?)?);
    }
    let mut acc = syl(&hyp_conj(&parts)?, mem_body)?;
    if *acc.concl() != Formula::imp(levels[m].clone(), want.clone()) {
        return None
    }

    // Eliminate the witnesses, innermost first.
    for t in (0..m).rev() {
        // `⊢ H_t → ((∃rₜ. rₜ ∈ cₜ) → •∈‖…‖)`.
        let branch = hyp_ex_branch(tvs[t], &acc, &levels[t], want)?;
        // `⊢ H_t → • ∈ ‖cₜ‖`, then `Trunc::elim` supplies the existential.
        let h_tr = syl(&to_base[t], &conj_proj(&trunc_atoms, kk + t)?)?;
        let h_ex = syl(&h_tr, &inst_all(&tr.elim, std::slice::from_ref(&children[t]))?)?;
        acc = hyp_mp(&branch, &h_ex)?;
    }
    if *acc.concl() != Formula::imp(hmp, want.clone()) {
        return None
    }
    Some((trunc_atoms, acc))
}

/// `H → φ`, or bare `φ` when there is no antecedent.
fn imp_opt(hyp: &Option<Formula>, phi: Formula) -> Formula {
    match hyp {
        Some(h) => Formula::imp(h.clone(), phi),
        None => phi,
    }
}

/// [`syl`] when there is an antecedent, [`Thm::mp`] when there is not.
fn syl_opt(hyp: &Option<Formula>, a: &Thm, b: &Thm) -> Option<Thm> {
    match hyp {
        Some(_) => syl(a, b),
        None => Thm::mp(b, a),
    }
}
