//! **The class-(P) recursor, indexed** — `‖ind(p⃗,x⃗)‖`'s elimination rule, one
//! theorem per declaration.
//!
//! # Interface
//!
//! Writing `‖ind(p⃗,x⃗)‖` for [`TruncCarrier::carrier`], `m` for a fresh motive
//! variable, `•` for the point, and `app(m, x⃗, t)` for the **curried**
//! application [`motive_app`] — the same spine [`super::prop_rec`] defines, and
//! deliberately not a second one:
//!
//! ```text
//! MINORᵢ(m) := ∀y⃗. ( Aᵢ → • ∈ app(m, e⃗ᵢ(p⃗,y⃗), •) )                  [minors]
//!
//! Aᵢ  :=  the kᵢ + mᵢ FIELD atoms, in DECLARED order:            [minor_atoms]
//!             yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)                    at a Slot::Plain
//!             • ∈ ‖ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))‖            at a Slot::Rec
//!         then the mᵢ induction hypotheses
//!             • ∈ app(m, d⃗ᵢⱼ(p⃗,y⃗), •)
//!
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) →
//!       ∀x⃗ ∀t. ( t ∈ ‖ind(p⃗,x⃗)‖ → • ∈ app(m, x⃗, t) ) )                  [rec]
//! ```
//!
//! **There is no `∀r⃗`**, exactly as in
//! [`TruncRecursor`](super::trunc_rec::TruncRecursor) and
//! [`TruncCtor::trunc_mem`](super::trunc::TruncCtor::trunc_mem): a recursive
//! argument of a `Prop`-valued family is a *proof*, so it contributes an atom
//! and not a variable, and the three theorems can be read side by side.
//!
//! # It sits strictly between two files and takes one half from each
//!
//! The three `φ`s the three eliminators run [`decl_rect`] at:
//!
//! | module | `φ(z)` | `z` in `goodrec` | `z` in the motive |
//! |---|---|---|---|
//! | [`super::trunc_rec`] — class (P), `ni = 0` | `• ∈ app(m,•)` | — | no |
//! | **here** — class (P), `ni ≥ 1` | `∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗),z) → • ∈ app(m,x⃗,•))` | **yes** | **no** |
//! | [`super::prop_rec`] — class (T) at a `Prop` motive | `∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗),z) → • ∈ app(m,x⃗,z))` | yes | yes |
//!
//! Neither sibling's simplification survives here, and that is the whole
//! content of the file:
//!
//! * **[`super::trunc_rec`]'s "one projection" fails.** There, `φ` is constant
//!   in `z`, so `rect_stepᵢ`'s antecedent already contains its own consequent
//!   and a recursive minor is discharged without being read. Here `φ` mentions
//!   `z` in the `goodrec` antecedent, so `φ(tⱼ)` is *not* `φ(ctorᵢ(y⃗,t⃗))`: the
//!   induction hypothesis has to be **fired at the child's own index vector**
//!   `d⃗ᵢⱼ`, and the fact that lets it fire —
//!   `tⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` — comes out of inversion. Every minor carries content.
//! * **[`super::prop_rec`]'s motive transport is unnecessary.** There, `φ`
//!   mentions `z` in `app(m,x⃗,z)` too, so the subject travels through the
//!   motive spine and a minor's conclusion is about `ctorᵢ(y⃗,r⃗)`. Here the
//!   motive's subject is `•` at every position, because
//!   [`TruncCarrier::only_point`] says every inhabitant of the carrier is the
//!   point. The `ni` [`kernel::Thm::eq_leibniz`] steps that move the conclusion
//!   from `e⃗ᵢ` to `x⃗` are still needed; the `ni + 1`-th, at the subject, is not.
//!
//! What is taken whole from each: the **inversion** is
//! [`invert_under`](super::prop_rec) — [`IndexedCtor::inv`](super::IndexedCtor),
//! `pair_inj` componentwise, [`IndexedCarrier::good_of`] — called unchanged,
//! because the `goodrec` antecedent is the same one; and the **two ends** are
//! [`TruncCarrier::only_point`] and [`TruncCarrier::elim`], because the
//! truncation has thrown the member away and eliminating out of it has to go
//! back to the thing truncated. Without `elim` the theorem is unprovable, and
//! that is the honest price of a small eliminator.
//!
//! # The `ulift` class (P) does not pay for
//!
//! `thesis.txt:1811–1819` states this clause **for the indexed case directly** —
//! `⟦µt : ∀x::α. U_ℓ. K⟧ = λx::α. ulift_ℓ ‖⟦µt : ∀x::α. U_{ℓ'}. K⟧ x‖`, with the
//! `λx::α` prefix and the `x` applied — so nothing here is a non-indexed clause
//! being stretched. Carneiro's `ℓ' = max(1, all the constructor arguments)`
//! *lifts the target universe above 1 before truncating*, and **that lift is
//! exactly the step class (P) does not have to pay for**: nothing ever places
//! the base in a universe, only `‖a‖ ∈ U₀`
//! ([`TruncCarrier::in_u0`]), which needs no size argument. So there is no
//! second W-type at `ℓ'`, no [`super::universe`] and no cumulativity chain —
//! `ulift` evaporates at the set level (`:2106`, and `:2284`'s soundness clause
//! is the cumulativity raise). That is the content of [`super::trunc`]'s
//! "cheaper rather than more expensive", said at the place it is spent.
//!
//! `:1893–1901` leaves the introduction rules, the recursor and ι as future
//! work, so the theorem above is **invention** on the same footing as
//! [`super::trunc_rec`]'s and [`super::prop_rec`]'s, both of whose headers say
//! so of themselves.
//!
//! # Symbols versus interpretations — what a consumer has to move, and where
//!
//! Everything is stated at the index **symbols** `e⃗ᵢ`, `d⃗ᵢⱼ` and `βⱼ`, per
//! `crate::inductive::spec`'s convention. A checker's `x⃗` are *interpretations*
//! of Lean index expressions, so every use has to move between the two, and the
//! move splits by the shape of the position exactly as
//! [`super::prop_rec`]'s header sets out:
//!
//! * inside `app(m, …, •)` the spine is a nest of *binary* `app` nodes, and the
//!   fold down it is [`motive_congr_of`](super::prop_rec::motive_congr_of) —
//!   **reused, not redefined**;
//! * at a `mem`-shaped position the term is one `FnSym` applied to `p⃗ ++ x⃗`,
//!   and one congruence over that symbol does it: `mini`'s
//!   `ctor_ix::index_congr`. The truncated recursive atom `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖`
//!   is that case with one extra unary node — `‖·‖` is a single symbol
//!   application, so it is one further [`kernel::Thm::eq_leibniz`] at the hole
//!   and **not** a spine. It needs nothing from here.
//!
//! And the terms that need moving are *enumerable* rather than buried:
//! [`trunc_minor_atoms_at`] and [`trunc_minor_body_at`] rebuild `Aᵢ` and
//! `MINORᵢ`'s body at the consumer's **own** parameter and field terms, so a
//! consumer never has to restate this module's convention to reach it. They are
//! the builders [`IndexedTruncRecursor::over_family`] itself uses, so the
//! accessor and the theorem cannot drift. The conclusion's `x⃗` and `t` need no
//! move at all: they are `∀`-bound, so a consumer instantiates them at its own
//! interpretations directly.
//!
//! # Scope, and which half of it has a witness
//!
//! Class (P), indexed, `ni ≥ 1` — [`TruncCarrier::over_family`]'s scope, since
//! that is the carrier this eliminates out of. Both edges return `None`, and
//! **neither has a guard of its own**, because a guard no test can reach is
//! worse than none: `n = 0` is refused by there being no minors to conjoin (and
//! the true statement at zero constructors is the different one that the
//! carrier is empty), and `ni = 0` by the pin that `tc` is *this* family's
//! truncation — [`TruncCarrier::over_family`] refuses an empty `xvs`, so a `tc`
//! with `ni = 0` is a [`TruncCarrier::over_declaration`] and belongs to
//! [`super::trunc_rec`], which is a different construction and not a relaxed
//! guard on this one. That last refusal is reachable and is tested.
//!
//! **The corpus witnesses one half of that scope and the tests witness the
//! other.** `072_SortElimProp2` — `np = 1`, `ni = 2`, `kᵢ = 2`, result indices
//! the fields permuted — is the only class-(P) indexed row the tutorial corpus
//! asks for, and it has `recs = 0`. So the corpus exercises the non-constant
//! `φ` and the [`IndexedCtor::inv`](super::IndexedCtor) forcing, and **nothing
//! in it exercises the recursive minors** — the branch where the induction
//! hypothesis is fired at `d⃗ᵢⱼ` and actually consumed. `Nat.le`,
//! `Nat.le.below` and `List.Mem` (prelude and `grind-ring-5`, not the
//! tutorials) are the declarations that would. `derived/tests/family_trunc_rec_ix.rs`
//! therefore carries a hand-built `Nat.le`-shaped fixture beside `072`'s, and
//! the recursive half is exercised **there and only there**; a passing corpus
//! run is not evidence for it. A second hand-built fixture there carries an
//! **interleaved** field mask (`Plain, Rec, Plain, Rec`), because `Nat.le`'s own
//! mask is plains-then-recs and so cannot tell the declared order from the
//! carrier's — the `minor_atoms` ordering claim has no other witness.
//!
//! # Nothing here is an axiom
//!
//! One Separation per call, inside [`decl_rect`]'s [`crate::wtype::w_rect`].
//! Everything else is an instance of a theorem [`TruncCarrier`],
//! [`IndexedCarrier`], [`super::good`] or [`crate::inductive::rect`] already
//! proved, and every theorem spent is required to be **unconditional at the
//! door** — a sequent hypothesis is invisible to the `establishes` on the way
//! out, so it has to be refused where it enters.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{gen_under, hyp_conj, hyp_ex_branch, hyp_inst, rewrite_under};
use crate::inductive::rect::{decl_rect, rect_parts};
use crate::prop::trunc::Trunc;
use crate::recursion::hyp::hyp_eq_symm;
use crate::sums::Sums;
use crate::{
    all_unconditional, and_left, and_right, conj_of, conj_proj, establishes, gen_all, hyp_mp,
    imp_refl, inst_all, syl, uncurry,
};

use super::carrier::IndexedCarrier;
use super::prop_rec::{invert_under, lean_order_of, motive_app, Inverted};
use super::spec::IndexedDeclSpec;
use super::trunc::TruncCarrier;
use super::IndexedInductive;

/// **`Aᵢ` at caller-supplied parameter and field terms** — the `kᵢ + mᵢ` field
/// atoms in *declared* order, then the `mᵢ` induction hypotheses:
///
/// ```text
/// yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)                  at a Slot::Plain
/// • ∈ ‖ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))‖          at a Slot::Rec
/// • ∈ app(motive, d⃗ᵢⱼ(p⃗,y⃗), •)     one per recursive field
/// ```
///
/// The sibling of [`minor_atoms_at`](super::prop_rec::minor_atoms_at), and the
/// differences are the two that make this a separate construction: a recursive
/// field contributes a **truncated** atom with no variable of its own, and an
/// induction hypothesis is stated at the point rather than at that variable.
///
/// [`IndexedTruncRecursor::over_family`] calls this at its own fresh variables;
/// a consumer calls it at Lean interpretations, which is the only way to know
/// what it has to prove without restating this module's convention.
///
/// `None` on a length mismatch or an out-of-range constructor.
#[allow(clippy::too_many_arguments)]
pub fn trunc_minor_atoms_at(
    s: &Sums,
    tr: &Trunc,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    i: usize,
    motive: &Term,
    ps: &[Term],
    ys: &[Term],
) -> Option<Vec<Formula>> {
    let c = spec.base.ctors.get(i)?;
    let (k, m) = (c.args.len(), c.recs);
    if ys.len() != k {
        return None
    }
    let pt = s.point();
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, ps, ys)).collect::<Option<_>>()?;

    let plains: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(c.args[j], a))
        })
        .collect();
    let recs: Vec<Formula> = (0..m)
        .map(|j| Some(Formula::mem(pt.clone(), tr.of(ixc.ty_of(ps, &childs[j])?))))
        .collect::<Option<_>>()?;

    let mut atoms = lean_order_of(&c.order, &plains, &recs)?;
    for child in childs.iter().take(m) {
        atoms.push(Formula::mem(pt.clone(), motive_app(s, motive, child, &pt)));
    }
    Some(atoms)
}

/// **`MINORᵢ`'s body at caller-supplied terms** — [`trunc_minor_atoms_at`]
/// implying `• ∈ app(motive, e⃗ᵢ(p⃗,y⃗), •)`, or that conclusion bare when the
/// constructor has no fields at all.
///
/// The `∀y⃗` prefix is *not* included: a consumer discharging the minor supplies
/// its own binders, and [`IndexedTruncRecursor::minors`] is this closed over
/// [`IndexedTruncRecursor::minor_vars`]. One builder for both, so the accessor
/// a consumer reads and the formula the theorem carries cannot drift.
#[allow(clippy::too_many_arguments)]
pub fn trunc_minor_body_at(
    s: &Sums,
    tr: &Trunc,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    i: usize,
    motive: &Term,
    ps: &[Term],
    ys: &[Term],
) -> Option<Formula> {
    let atoms = trunc_minor_atoms_at(s, tr, spec, ixc, i, motive, ps, ys)?;
    let pt = s.point();
    let concl = Formula::mem(
        pt.clone(),
        motive_app(s, motive, &spec.result_vec(i, ps, ys)?, &pt),
    );
    Some(match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    })
}

/// An indexed class-(P) declaration's elimination rule.
pub struct IndexedTruncRecursor {
    /// The motive variable `m`, minted here. Free in
    /// [`IndexedTruncRecursor::minor_atoms`] and
    /// [`IndexedTruncRecursor::minors`], and bound by the outermost `∀` but one
    /// of [`IndexedTruncRecursor::rec`].
    pub motive: FreeVar,
    /// Per constructor, the `kᵢ` **plain**-field variables — the only binders
    /// `MINORᵢ` has. A recursive field contributes an atom and not a variable,
    /// so this is shorter than
    /// [`IndexedPropRecursor::minor_vars`](super::prop_rec::IndexedPropRecursor::minor_vars)
    /// at the same declaration, and the atom list is not.
    pub minor_vars: Vec<Vec<FreeVar>>,
    /// Per constructor, `Aᵢ` atom by atom: the `kᵢ + mᵢ` field atoms in
    /// declared order, then the `mᵢ` induction hypotheses.
    ///
    /// Empty for a constructor with no fields, in which case `MINORᵢ` has no
    /// antecedent at all.
    pub minor_atoms: Vec<Vec<Formula>>,
    /// `MINORᵢ` itself, closed over [`IndexedTruncRecursor::minor_vars`].
    pub minors: Vec<Formula>,
    /// `⋀ᵢ MINORᵢ(m)`, the antecedent of [`IndexedTruncRecursor::rec`].
    pub hyp: Formula,
    /// The `ni` index variables the conclusion quantifies over, outermost
    /// first.
    pub xvs: Vec<FreeVar>,
    /// The major-premise variable `t`, bound **inside** all of
    /// [`IndexedTruncRecursor::xvs`].
    pub major: FreeVar,
    /// **`⊢ ∀p⃗ ∀m. (⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. (t ∈ ‖ind(p⃗,x⃗)‖ → • ∈ app(m,x⃗,t)))`**
    /// — unconditional, checked on the way out.
    pub rec: Thm,
}

/// The context one induction step is built in. Private; every field is either
/// the family's or minted by [`IndexedTruncRecursor::over_family`].
struct Step<'a> {
    mach: &'a Machine,
    ind: &'a Inductive,
    spec: &'a IndexedDeclSpec,
    ixc: &'a IndexedCarrier,
    tr: &'a Trunc,
    /// `goodrec(p⃗)`.
    grec: &'a Term,
    ps: &'a [Term],
    /// The motive term.
    tm: &'a Term,
    zv: FreeVar,
    phi: &'a Formula,
    hyp: &'a Formula,
    minors: &'a [Formula],
}

impl IndexedTruncRecursor {
    /// The elimination rule for an **indexed** class-(P) family.
    ///
    /// `fam` must be [`IndexedInductive::build`] over `ind` and `mach`, and
    /// `tc` must be [`TruncCarrier::over_family`] over that same `fam.carrier`
    /// with `tr` — pinned on `tc.base` and `tc.carrier` rather than assumed, so
    /// a truncation of one family cannot be eliminated into another's
    /// induction.
    ///
    /// `None` for a family whose spec and skeleton disagree, for a `tc` that is
    /// a truncation of some **other** family (or of a non-indexed declaration —
    /// that is [`super::trunc_rec`], a different construction), for a foreign
    /// apparatus, for any theorem spent that carries a hypothesis, and on any
    /// internal shape check. A declaration with no constructors is refused
    /// because it has no minors to conjoin.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, so build this
    /// once per declaration and cache it with the result.
    pub fn over_family(
        env: &mut Env,
        mach: &Machine,
        tr: &Trunc,
        ind: &Inductive,
        fam: &IndexedInductive,
        tc: &TruncCarrier,
    ) -> Option<IndexedTruncRecursor> {
        let spec = &fam.spec;
        let ixc = &fam.carrier;
        let (n, ni) = (spec.len(), spec.num_indices());
        // `n = 0` and `ni = 0` are **not** guarded here, because a guard no
        // test can reach is worse than none: `n = 0` is refused three lines
        // below by `conj_of(&minors)` — there is nothing to conjoin — and
        // `ni = 0` by the `tc.xvs.len() != ni` pin, since
        // `TruncCarrier::over_family` refuses an empty `xvs` and so `tc` can
        // never have one. Both are also outside `IndexedInductive::build`'s own
        // scope, which is where the statement about them belongs.
        if !ind.is_over(mach) || ind.spec.ctors.len() != n
            || ind.spec.params != spec.base.params
            || ind.params.len() != spec.base.params
            || ixc.ctors.len() != n
            || ixc.xvs.len() != ni
            || ixc.ty.arity() as usize != spec.base.params + ni
        {
            return None
        }
        let s = &mach.wt.sums;
        let pt = s.point();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        // **There is no provenance check on `tc`, deliberately.** One was here
        // — `tc.base == ixc.ty_of(p⃗, tc.xvs)` and `tc.carrier == ‖tc.base‖` —
        // and removing it left every test passing, including the one that hands
        // this another family's truncation and a non-indexed one. The refusal
        // is over-determined by the two places `tc` is actually spent: the
        // conclusions of `only_point` and `elim` are compared against `‖·‖` of
        // the carrier **rebuilt here from `ixc`**, so a `tc` about any other set
        // fails there. A pin no mutation can reach is worse than none, and the
        // statement comparison is the better check anyway: it pins what the
        // theorem says rather than where it came from.
        if !all_unconditional(&[
            &ixc.subset_w,
            &ixc.good_of,
            &ixc.intro,
            &ind.ty_ax,
            &tc.only_point,
            &tc.elim,
            &tr.intro,
        ]) || !all_unconditional(&ixc.ctors.iter().map(|c| &c.inv).collect::<Vec<_>>())
            || !all_unconditional(&ind.ctors.iter().map(|c| &c.mem).collect::<Vec<_>>())
        {
            return None
        }

        let ap = &s.ap;
        let grec = fam.good.rec.clone();

        // ── `φ(z) := ∀x⃗. (tup(x⃗) ∈ app(goodrec,z) → • ∈ app(m,x⃗,•))` ────────
        //
        // `z` is in the `goodrec` antecedent and **not** in the motive: that one
        // difference from `prop_rec`'s `φ` is what removes the subject transport
        // and leaves everything else standing.
        let mv = env.fresh_var();
        let tm = Term::var(mv);
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let pxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let pxs: Vec<Term> = pxvs.iter().map(|v| Term::var(*v)).collect();
        let phi = quantify(
            &pxvs,
            Formula::imp(
                Formula::mem(IndexedDeclSpec::tup(s, &pxs), ap.apply(grec.clone(), tz.clone())),
                Formula::mem(pt.clone(), motive_app(s, &tm, &pxs, &pt)),
            ),
        );

        // ── the minors: `∀y⃗` only, and the atoms in Lean field order ────────
        let mut minor_vars: Vec<Vec<FreeVar>> = Vec::with_capacity(n);
        let mut minor_atoms: Vec<Vec<Formula>> = Vec::with_capacity(n);
        let mut minors: Vec<Formula> = Vec::with_capacity(n);
        for i in 0..n {
            let c = &spec.base.ctors[i];
            let (k, m) = (c.args.len(), c.recs);
            let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let atoms = trunc_minor_atoms_at(s, tr, spec, ixc, i, &tm, &ps, &ys)?;
            if atoms.len() != k + 2 * m {
                return None
            }
            let body = trunc_minor_body_at(s, tr, spec, ixc, i, &tm, &ps, &ys)?;
            minors.push(quantify(&yvs, body));
            minor_vars.push(yvs);
            minor_atoms.push(atoms);
        }
        let hyp = conj_of(&minors)?;

        // ── `⊢ HYP → RECT(φ)` ───────────────────────────────────────────────
        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != n {
            return None
        }
        let mut steps: Vec<Thm> = Vec::with_capacity(n);
        for i in 0..n {
            let cx = Step {
                mach,
                ind,
                spec,
                ixc,
                tr,
                grec: &grec,
                ps: &ps,
                tm: &tm,
                zv,
                phi: &phi,
                hyp: &hyp,
                minors: &minors,
            };
            let st = induction_step(env, &cx, i, &minor_vars[i], &minor_atoms[i])?;
            if *st.concl() != Formula::imp(hyp.clone(), parts[i].clone()) {
                return None
            }
            steps.push(st);
        }
        // `⊢ HYP → ∀z. (z ∈ W → φ(z))`.
        let h_all = syl(&hyp_conj(&steps)?, &decl_rect(env, mach, ind, zv, &phi)?)?;

        // ── the two ends: `only_point` and `elim` ───────────────────────────
        let fxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let fxs: Vec<Term> = fxvs.iter().map(|v| Term::var(*v)).collect();
        let base = ixc.ty_of(&ps, &fxs)?;
        let carrier = tr.of(base.clone());
        let tv = env.fresh_var();
        let tt = Term::var(tv);
        let mem_t = Formula::mem(tt.clone(), carrier.clone());
        let kf = Formula::and(hyp.clone(), mem_t.clone());
        let k_h = and_left(hyp.clone(), mem_t.clone());
        let k_m = and_right(hyp.clone(), mem_t.clone());

        // `t = •`, hence `• ∈ ‖ind(p⃗,x⃗)‖`.
        let mut op_args = ps.clone();
        op_args.extend(fxs.iter().cloned());
        op_args.push(tt.clone());
        let op = inst_all(&tc.only_point, &op_args)?;
        if *op.concl() != Formula::imp(mem_t.clone(), Formula::eq(tt.clone(), pt.clone())) {
            return None
        }
        let k_pt = syl(&k_m, &op)?;
        let cc = carrier.clone();
        let k_ptmem = rewrite_under(env, &k_pt, move |q| Formula::mem(q, cc.clone()), &k_m)?;

        // `∃w. w ∈ ind(p⃗,x⃗)` — the member the truncation threw away. Unlike
        // `trunc_rec`'s, this existential is already at the *indexed* carrier,
        // so `subset_w` and `good_of` apply to the witness directly and no
        // `Inductive::ty_ax` step is needed to reach `W`.
        let wv = env.fresh_var();
        let tw = Term::var(wv);
        let mut el_args = ps.clone();
        el_args.extend(fxs.iter().cloned());
        let elim = inst_all(&tc.elim, &el_args)?;
        let mem_w = Formula::mem(tw.clone(), base.clone());
        if *elim.concl()
            != Formula::imp(
                Formula::mem(pt.clone(), carrier.clone()),
                Formula::exists(wv, mem_w.clone()),
            )
        {
            return None
        }
        let k_ex = syl(&k_ptmem, &elim)?;

        // ── under `K3 = kf ∧ (w ∈ ind(p⃗,x⃗))`, run the induction at `w` ─────
        let k3 = Formula::and(kf.clone(), mem_w.clone());
        let k3_f = and_left(kf.clone(), mem_w.clone());
        let k3_w = and_right(kf.clone(), mem_w.clone());

        let mut wa = ps.clone();
        wa.extend(fxs.iter().cloned());
        wa.push(tw.clone());
        let sub = inst_all(&ixc.subset_w, &wa)?;
        if *sub.concl() != Formula::imp(mem_w.clone(), Formula::mem(tw.clone(), ind.wty.clone())) {
            return None
        }
        let gof = inst_all(&ixc.good_of, &wa)?;
        if *gof.concl()
            != Formula::imp(
                mem_w.clone(),
                Formula::mem(
                    IndexedDeclSpec::tup(s, &fxs),
                    ap.apply(grec.clone(), tw.clone()),
                ),
            )
        {
            return None
        }

        let k3_phi = hyp_mp(
            &hyp_inst(&syl(&syl(&k3_f, &k_h)?, &h_all)?, std::slice::from_ref(&tw))?,
            &syl(&k3_w, &sub)?,
        )?;
        let k3_goal = hyp_mp(&hyp_inst(&k3_phi, &fxs)?, &syl(&k3_w, &gof)?)?;

        let at_pt = Formula::mem(pt.clone(), motive_app(s, &tm, &fxs, &pt));
        if *k3_goal.concl() != Formula::imp(k3, at_pt.clone()) {
            return None
        }
        // The witness is free in neither `kf` nor the conclusion.
        let k_goal_pt = hyp_mp(&hyp_ex_branch(wv, &k3_goal, &kf, &at_pt)?, &k_ex)?;

        // ── `t = •` back onto the motive's subject ──────────────────────────
        let back = hyp_eq_symm(env, &k_pt)?;
        let (sc, tmc, fxc, ptc) = (s.clone(), tm.clone(), fxs.clone(), pt.clone());
        let k_goal = rewrite_under(
            env,
            &back,
            move |q| Formula::mem(ptc.clone(), motive_app(&sc, &tmc, &fxc, &q)),
            &k_goal_pt,
        )?;

        let want_body = Formula::mem(pt.clone(), motive_app(s, &tm, &fxs, &tt));
        if *k_goal.concl() != Formula::imp(kf, want_body.clone()) {
            return None
        }
        let mut closed = gen_under(tv, &hyp, &uncurry(&k_goal)?)?;
        for v in fxvs.iter().rev() {
            closed = gen_under(*v, &hyp, &closed)?;
        }

        let mut quant = ind.params.clone();
        quant.push(mv);
        let rec = gen_all(&quant, &closed);
        let want = quantify(
            &quant,
            Formula::imp(
                hyp.clone(),
                quantify(&fxvs, Formula::forall(tv, Formula::imp(mem_t, want_body))),
            ),
        );
        if !establishes(&rec, &want) {
            return None
        }

        Some(IndexedTruncRecursor {
            motive: mv,
            minor_vars,
            minor_atoms,
            minors,
            hyp,
            xvs: fxvs,
            major: tv,
            rec,
        })
    }
}

/// `∀x₀ … ∀x_{n-1}. φ`, outermost first — [`gen_all`] at the formula level.
fn quantify(xs: &[FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}

/// `⊢ HYP → rect_stepᵢ(φ)` — one constructor's induction step, discharged from
/// `MINORᵢ`.
fn induction_step(
    env: &mut Env,
    cx: &Step<'_>,
    i: usize,
    yvs: &[FreeVar],
    atoms: &[Formula],
) -> Option<Thm> {
    let (mach, ind, spec, ixc, tr) = (cx.mach, cx.ind, cx.spec, cx.ixc, cx.tr);
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let pt = s.point();
    let ps = cx.ps;
    let ni = spec.num_indices();
    let c = &spec.base.ctors[i];
    let (k, m) = (c.args.len(), c.recs);
    if yvs.len() != k || atoms.len() != k + 2 * m {
        return None
    }
    // `rect_step` binds a variable per recursive field even though `MINORᵢ`
    // does not; these are its, not the minor's.
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let ctor = ind.ctor_term(mach, i, &ys, &ts)?;
    let res = spec.result_vec(i, ps, &ys)?;
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, ps, &ys)).collect::<Option<_>>()?;

    // ── `rect_stepᵢ`'s own antecedent, in its own order ─────────────────────
    let mut ratoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(c.args[j], a))
        })
        .collect();
    ratoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    ratoms.extend(ts.iter().map(|t| cx.phi.subst(cx.zv, t)));
    let hr = conj_of(&ratoms);
    let kf = match &hr {
        Some(h) => Formula::and(cx.hyp.clone(), h.clone()),
        None => cx.hyp.clone(),
    };
    let (k_hyp, k_rect) = match &hr {
        Some(h) => (
            and_left(cx.hyp.clone(), h.clone()),
            Some(and_right(cx.hyp.clone(), h.clone())),
        ),
        None => (imp_refl(cx.hyp.clone()), None),
    };
    let rect_at = |j: usize| -> Option<Thm> { syl(k_rect.as_ref()?, &conj_proj(&ratoms, j)?) };

    // ── under `K2 = kf ∧ (tup(x⃗) ∈ app(goodrec, ctorᵢ))` ────────────────────
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let mem_g = Formula::mem(
        IndexedDeclSpec::tup(s, &xs),
        ap.apply(cx.grec.clone(), ctor.clone()),
    );
    let k2 = Formula::and(kf.clone(), mem_g.clone());
    let k2_kf = and_left(kf.clone(), mem_g.clone());
    let k2_g = and_right(kf.clone(), mem_g.clone());
    let lift = |t: &Thm| syl(&k2_kf, t);

    // The inversion, shared verbatim with the other two indexed eliminators.
    let plains: Vec<Thm> = (0..k).map(|j| lift(&rect_at(j)?)).collect::<Option<_>>()?;
    let in_w: Vec<Thm> = (0..m).map(|j| lift(&rect_at(k + j)?)).collect::<Option<_>>()?;
    let Inverted { skel: _, idx_eqs, child_mem } = invert_under(
        env, mach, ind, spec, ixc, i, ps, &ys, &ts, &xs, &k2, &plains, &in_w, &k2_g,
    )?;

    // **The truncated recursive atoms.** `MINORᵢ` asks for a *proof* that the
    // child family is inhabited, not for the element inversion produced, so
    // each `tⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` is pushed through `Trunc::intro`. This is where
    // the `∀r⃗` disappears.
    let mut trunc_mems: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        let child = ixc.ty_of(ps, &childs[j])?;
        trunc_mems.push(syl(&child_mem[j], &inst_all(&tr.intro, &[child, ts[j].clone()])?)?);
    }

    // **The induction hypotheses, fired at the child's own indices.** `φ` is not
    // constant, so this is where `trunc_rec`'s one-projection argument fails:
    // `φ(tⱼ)` has to be instantiated at `d⃗ᵢⱼ` and its `goodrec` antecedent
    // discharged from the child's membership.
    let mut ihs: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        let at_child = hyp_inst(&lift(&rect_at(k + m + j)?)?, &childs[j])?;
        let mut ga = ps.to_vec();
        ga.extend(childs[j].iter().cloned());
        ga.push(ts[j].clone());
        ihs.push(hyp_mp(&at_child, &syl(&child_mem[j], &inst_all(&ixc.good_of, &ga)?)?)?);
    }

    // ── `MINORᵢ`, instantiated at the plain fields alone ────────────────────
    let mut lean_thms = lean_order_of(&c.order, &plains, &trunc_mems)?;
    lean_thms.extend(ihs.iter().cloned());
    for (q, th) in lean_thms.iter().enumerate() {
        if *th.concl() != Formula::imp(k2.clone(), atoms[q].clone()) {
            return None
        }
    }
    let minor = hyp_inst(&syl(&lift(&k_hyp)?, &conj_proj(cx.minors, i)?)?, &ys)?;
    let mut cur = match hyp_conj(&lean_thms) {
        Some(p) => hyp_mp(&minor, &p)?,
        None => minor,
    };

    // ── move the conclusion from `e⃗ᵢ` to `x⃗`, one index at a time ──────────
    //
    // `ni` steps and not `ni + 1`: the motive's subject is `•` at both ends, so
    // `prop_rec`'s final transport at the subject has nothing to do.
    let mut spine = res.clone();
    for q in 0..ni {
        let back = hyp_eq_symm(env, &idx_eqs[q])?;
        let (pre, post) = (xs[..q].to_vec(), spine[q + 1..].to_vec());
        let (sc, tmc, ptc) = (s.clone(), cx.tm.clone(), pt.clone());
        cur = rewrite_under(
            env,
            &back,
            move |hole| {
                let mut v = pre.clone();
                v.push(hole);
                v.extend(post.iter().cloned());
                Formula::mem(ptc.clone(), motive_app(&sc, &tmc, &v, &ptc))
            },
            &cur,
        )?;
        spine[q] = xs[q].clone();
    }
    if *cur.concl()
        != Formula::imp(k2, Formula::mem(pt.clone(), motive_app(s, cx.tm, &xs, &pt)))
    {
        return None
    }

    // ── close `∀x⃗`, then `rect_step`'s own binders ──────────────────────────
    let mut acc = uncurry(&cur)?;
    for v in xvs.iter().rev() {
        acc = gen_under(*v, &kf, &acc)?;
    }
    if *acc.concl() != Formula::imp(kf, cx.phi.subst(cx.zv, &ctor)) {
        return None
    }
    match &hr {
        None => Some(acc),
        Some(_) => {
            let mut out = uncurry(&acc)?;
            for v in tvs.iter().rev() {
                out = gen_under(*v, cx.hyp, &out)?;
            }
            for v in yvs.iter().rev() {
                out = gen_under(*v, cx.hyp, &out)?;
            }
            Some(out)
        }
    }
}
