//! **Class (S)** — §5.3's subsingleton eliminators, as `acc` at a Separation.
//!
//! # `acc^φ_r` is an instantiation, not a module
//!
//! `INDEXED-DESIGN.md` §6.1. The thesis (`:1831–1845`) builds `acc^φ_r` over
//! the subtype `{x : α | φ x}` with a projected relation `r′`. At the set level
//! both wrappers evaporate, **because of the two corrections that landed with
//! [`crate::acc`]**:
//!
//! * `step_closed` carries the `x ∈ A` guard the thesis omits, and `preds_in`
//!   carries `y ∈ A` — without the former, `acc(A,R) = A` for every `R`
//!   (`acc/condition.rs`'s header records the collapse);
//! * `R ⊆ A × A` is **not** assumed anywhere — edges leaving `A` are ignored by
//!   the guards, and `acc/witness.rs:226`'s countermodel pins that the `w ∈ A`
//!   conjunct is load-bearing.
//!
//! So with `A_φ := {q ∈ Idx(p⃗) : φ(q)}` a single Separation,
//! `acc^φ_r = acc(A_φ, R)` with `R` passed through **unrestricted**:
//! `preds_in(A_φ,R,C,q)` already quantifies only over predecessors satisfying
//! `φ`, which is precisely the thesis's intent. No projected `r′`, no subtype
//! pairing, no new module.
//!
//! # The two Separations
//!
//! Read off the *same* [`IndexedDeclSpec`] the class-(T) route uses — §5.3's
//! `LE ctor` recursion is at the set level a **formula** builder, not a set
//! builder:
//!
//! ```text
//! A_φ(p⃗) := { q ∈ Idx(p⃗) :
//!               ⋁ᵢ ∃y⃗. ( ⋀ⱼ yⱼ ∈ βⱼ(p⃗,y<ⱼ)  ∧  q = tup(e⃗ᵢ(p⃗,y⃗)) ) }
//!
//! R(p⃗)   := { e ∈ Idx(p⃗) × Idx(p⃗) :
//!               ⋁ᵢ ⋁ⱼ ∃y⃗. ( ⋀ⱼ′ yⱼ′ ∈ βⱼ′(…)
//!                            ∧ e = ⟨tup(d⃗ᵢⱼ(p⃗,y⃗)), tup(e⃗ᵢ(p⃗,y⃗))⟩ ) }
//! ```
//!
//! — the thesis's `[S; R]` accumulator, with the base case contributing φ's
//! matrix and each recursive argument contributing one edge, pointing from the
//! child's index to the result index. An empty disjunction is `⊥`, which is how
//! a declaration with no constructors and a declaration with no recursive
//! arguments are handled without a special case.
//!
//! # The degenerate case is the whole corpus demand
//!
//! `071_SortElimProp` — one parameter, two indices, one non-recursive
//! constructor — is the only class-(S) family in the 91 tutorial files that
//! needs this route at all (`Eq` and `Acc` take direct interpretation clauses).
//! With no recursive arguments the `LE ctor` recursion emits an empty
//! disjunction, so `R` has no members, hence `R = ∅` by Extensionality, hence
//! `acc(A_φ, R) = A_φ` by [`crate::acc::acc_empty_relation`] — a *conditional
//! singleton's* worth of content, and [`LeCarrier::degenerate`] is it.
//!
//! **The same holds on `init-prelude`, which was expected to be different and
//! is not.** Decoding every declaration with `numIndices > 0` in every export in
//! this repository gives four in `init-prelude`: `Eq` and `HEq`, both class (S)
//! and both **non-recursive** (so both degenerate); and `Nat.le` and
//! `Nat.le.below`, both of which are class (P) — the truncation clause
//! ([`super::trunc`]), not this one.
//! Across the whole repository the only *recursive* class-(S) declaration is
//! `Acc` itself, whose recursive argument is function-typed and so is not
//! representable as an [`IndexedDeclSpec`]; `INDEXED-DESIGN.md` §2.2 gives it
//! the direct clause `⟦Acc.rec⟧ = rec_acc::pack`.
//!
//! Two things this paragraph got wrong when it was written, both corrected by
//! decoding rather than by reasoning:
//!
//! * **`Nat.le` and `Nat.le.below` are not class (P) *because* they have two
//!   constructors.** The constructor count is not the test at all: one-ctor
//!   `And`, `Eq`, `Acc` and `SortElimProp` are large-eliminating, and one-ctor
//!   `SortElimProp2`, `Exists`, `Nonempty` and `Int.NonNeg` are not. The test
//!   is the recursor's `levelParams`, which `INDEXED-DESIGN.md` §2.1 reads and
//!   never recomputes.
//! * **`numIndices > 0` is the wrong census.** Class (P) is decided by the same
//!   trichotomy and is indifferent to indices: seven of the thirteen class-(P)
//!   declarations in this repository have none, `Or` and `Nonempty` among them
//!   and both in `init-prelude`. [`super::trunc`]'s header has the full table.
//!
//! So a recursive user-defined subsingleton — the case that needs the full
//! `R ≠ ∅` recursion — has **no witness anywhere**, tutorials and prelude
//! alike. Its carrier is built here anyway (it is one formula recursion and
//! costs nothing extra) and its recursor is [`super::le_rec`], which also covers
//! the degenerate `mᵢ = 0` case uniformly. What stays deferred is §6.2's
//! index-projection minor — the map from an index tuple back to the
//! constructor's fields, `thesis.txt:1866–1870`'s "delayed elimination" — which
//! is a wiring question (which Lean binder ends up in which minor slot) and
//! appears in [`super::le_rec`] as the *hypothesis* a step has to satisfy.
//!
//! # Interface
//!
//! ```text
//! A_φ(p⃗)                                                      [LeCarrier::a_phi]
//! ⊢ ∀p⃗ ∀q. (q ∈ A_φ(p⃗) ↔ (q ∈ Idx(p⃗) ∧ φ(q)))                 [LeCarrier::phi_ax]
//! R(p⃗)                                                        [LeCarrier::rel]
//! ⊢ ∀p⃗ ∀e. (e ∈ R(p⃗) ↔ (e ∈ Idx×Idx ∧ ρ(e)))                  [LeCarrier::rel_ax]
//! acc(A_φ(p⃗), R(p⃗))                                           [LeCarrier::acc_set]
//! ⊢ ∀p⃗ ∀y⃗. ((Hᵢ ∧ Eᵢ) → tup(e⃗ᵢ(p⃗,y⃗)) ∈ A_φ(p⃗))                [LeCarrier::intro]
//! ⊢ ∀p⃗. acc(A_φ(p⃗), R(p⃗)) = A_φ(p⃗)          (no recursion)    [LeCarrier::degenerate]
//! ρ's disjuncts, one per recursive argument             [LeCarrier::rel_disjuncts]
//! φ's disjuncts, one per constructor                    [LeCarrier::phi_disjuncts]
//! ```
//!
//! `Hᵢ` is the constructor's plain-argument typings and `Eᵢ` the `ni`
//! result-index typings — the same antecedent [`super::carrier`]'s membership
//! rule carries, and for the same reason: `Idx(p⃗)` membership cannot be derived
//! about opaque index symbols.
//!
//! # `ni = 0`: the antecedent can be *empty*, and that changes `intro`'s shape
//!
//! A non-indexed subsingleton is built here too — [`super::index`]'s header
//! gives the reason, which is that class (S) has no second path the way class
//! (T) does. Nothing in the two Separations cares: `Idx(p⃗) = 1`, `tup() = •`,
//! and `q = •` is the whole of each φ-disjunct's index equation.
//!
//! What does care is [`LeCarrier::intro`]. `Hᵢ ∧ Eᵢ` is empty exactly when the
//! constructor has no fields **and** the declaration has no indices —
//! `PUnit.unit`, `True.intro` — and there is no `⊤` in this kernel to weaken
//! it to. So at that one constructor the rule is stated **unconditionally**:
//!
//! ```text
//! ⊢ ∀p⃗ ∀y⃗. ((Hᵢ ∧ Eᵢ) → tup(e⃗ᵢ(p⃗,y⃗)) ∈ A_φ(p⃗))     when kᵢ + ni > 0
//! ⊢ ∀p⃗. • ∈ A_φ(p⃗)                                  when kᵢ = ni = 0
//! ```
//!
//! and [`LeCarrier::intro_is_conditional`] is the one-line test, so a consumer
//! reads which shape it has rather than pattern-matching on an implication that
//! might be one of `Hᵢ`'s own conjuncts. At `ni ≥ 1` the antecedent is never
//! empty and the shape is exactly what it always was.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::acc::Acc;
use crate::inductive::machine::Machine;
use crate::{
    conj_of, disj_of, disj_inject, ex_falso, exists_intro_imp, gen_all, hyp_and, iff_mp, iff_mpr,
    imp_refl, inst_all, syl,
};

use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// The class-(S) input. The **same** data as the class-(T) route: the branch
/// is decided per declaration off the export's eliminator trichotomy
/// (`INDEXED-DESIGN.md` §2.1), not off anything in the spec, so there is no
/// second spec type.
pub type LeSpec = IndexedDeclSpec;

/// A subsingleton family's carrier: the domain Separation, the relation
/// Separation, and `acc` of the two.
pub struct LeCarrier {
    /// `A_φ`, of arity `np`.
    pub phi: FnSym,
    /// `⊢ ∀p⃗ ∀q. (q ∈ A_φ(p⃗) ↔ (q ∈ Idx(p⃗) ∧ φ(q)))`.
    pub phi_ax: Thm,
    /// `A_φ(p⃗)`, at the parameters.
    pub a_phi: Term,
    /// `R`, of arity `np`.
    pub rel: FnSym,
    /// `⊢ ∀p⃗ ∀e. (e ∈ R(p⃗) ↔ (e ∈ Idx(p⃗)×Idx(p⃗) ∧ ρ(e)))`.
    pub rel_ax: Thm,
    /// `R(p⃗)`.
    pub r: Term,
    /// `acc(A_φ(p⃗), R(p⃗))` — the carrier `⟦P x⃗⟧ = [tup(x⃗) ∈ ·]` is a
    /// membership in this. [`super::le_index`] mints that conditional
    /// singleton at `ni ≥ 1`; [`super::le_prop`] reads it off `A_φ` directly at
    /// `ni = 0`, where the two coincide.
    pub acc_set: Term,
    /// Per constructor,
    /// `⊢ ∀p⃗ ∀y⃗. ((Hᵢ ∧ Eᵢ) → tup(e⃗ᵢ(p⃗,y⃗)) ∈ A_φ(p⃗))` — or, when the
    /// antecedent is empty (`kᵢ = ni = 0`), the unconditional
    /// `⊢ ∀p⃗. • ∈ A_φ(p⃗)`. [`LeCarrier::intro_is_conditional`] says which.
    pub intro: Vec<Thm>,
    /// `⊢ ∀p⃗. acc(A_φ(p⃗), R(p⃗)) = A_φ(p⃗)` — present **iff** no constructor is
    /// recursive, which is when `R` is provably empty.
    pub degenerate: Option<Thm>,
    /// The variable ρ's matrix speaks about — the edge, ranging over
    /// `Idx × Idx`.
    pub rel_subject: kernel::FreeVar,
    /// The variable φ's matrix speaks about — the index tuple, ranging over
    /// `Idx(p⃗)`.
    pub phi_subject: kernel::FreeVar,
    /// φ's disjuncts, one per **constructor**, in declared order:
    /// `∃y⃗ᵢ. (⋀ⱼ yⱼ ∈ βᵢⱼ(p⃗,y⃗<ⱼ) ∧ q = tup(e⃗ᵢ(p⃗,y⃗)))`, with `q` the
    /// [`LeCarrier::phi_subject`].
    ///
    /// Exported for the reason [`LeCarrier::rel_disjuncts`] is: a consumer that
    /// needs φ's *matrix* — [`super::le_prop`] does — cannot recover it from
    /// [`LeCarrier::phi_ax`], whose binders are de Bruijn, and rebuilding the
    /// recursion there would be a second copy of it.
    pub phi_disjuncts: Vec<Formula>,
    /// ρ's disjuncts, one per **recursive argument**, flat and
    /// constructor-major: `(i,j)` sits at [`LeCarrier::rel_slot`]`(spec,i,j)`.
    ///
    /// Exported because the *recursor* has to inject into one of them —
    /// deriving `⟨tup(d⃗ᵢⱼ), tup(e⃗ᵢ)⟩ ∈ R(p⃗)` is what makes ι fire
    /// ([`super::le_rec`]) — and the disjunct list is not recoverable from
    /// [`LeCarrier::rel_ax`] alone. Rebuilding it there would work (every
    /// binder is closed, so the formulas compare equal whatever fresh variables
    /// a second pass chose), but two copies of one recursion is exactly the
    /// drift this crate's `*_at` methods exist to prevent.
    pub rel_disjuncts: Vec<Formula>,
}

impl LeCarrier {
    /// Build the two Separations and derive the introduction rules.
    ///
    /// `ac` must be [`Acc::with_apply`] over the same pairing as `mach`;
    /// otherwise `⟨y,x⟩` denotes a different term here than in the relation and
    /// nothing composes.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ac: &Acc,
        spec: &LeSpec,
        ix: &IndexSpace,
        params: &[kernel::FreeVar],
    ) -> Option<LeCarrier> {
        if !spec.well_formed()
            || params.len() != spec.params()
            || ix.num_indices() != spec.num_indices()
        {
            return None
        }
        if ac.sets.up != mach.wt.sums.ap.sets.up {
            return None
        }
        let s = &mach.wt.sums;
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let n = spec.len();

        // Per constructor, a fresh field vector and its typings.
        let yvss: Vec<Vec<kernel::FreeVar>> = spec
            .base
            .ctors
            .iter()
            .map(|c| (0..c.args.len()).map(|_| env.fresh_var()).collect())
            .collect();
        let typings = |i: usize, ys: &[Term]| -> Vec<Formula> {
            (0..ys.len())
                .map(|j| {
                    let mut a = ps.clone();
                    a.extend(ys[..j].iter().cloned());
                    Formula::mem(ys[j].clone(), Term::apply(spec.base.ctors[i].args[j], a))
                })
                .collect()
        };

        // ── φ ───────────────────────────────────────────────────────────────
        let qv = env.fresh_var();
        let tq = Term::var(qv);
        let mut phi_disjuncts = Vec::with_capacity(n);
        for (i, yvs) in yvss.iter().enumerate() {
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let mut atoms = typings(i, &ys);
            atoms.push(Formula::eq(
                tq.clone(),
                IndexedDeclSpec::tup(s, &spec.result_vec(i, &ps, &ys)?),
            ));
            let body = conj_of(&atoms)?;
            phi_disjuncts.push(yvs.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc)));
        }
        let phi_matrix = disj_of(&phi_disjuncts).unwrap_or_else(Formula::false_);
        let phi_ex = crate::funcs::separation_full(env, qv, &phi_matrix, &ix.idx, &s.ap.empty_ax)?;
        let (phi, phi_ax) = crate::define_by_membership(
            env,
            params,
            &phi_ex,
            qv,
            &Formula::and(Formula::mem(tq.clone(), ix.idx.clone()), phi_matrix.clone()),
        )?;
        let a_phi = Term::apply(phi, ps.clone());

        // ── R ───────────────────────────────────────────────────────────────
        let ev = env.fresh_var();
        let te = Term::var(ev);
        let sq = s.prod.of(ix.idx.clone(), ix.idx.clone());
        let mut rel_disjuncts = Vec::new();
        for (i, yvs) in yvss.iter().enumerate() {
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            for j in 0..spec.base.ctors[i].recs {
                let mut atoms = typings(i, &ys);
                atoms.push(Formula::eq(
                    te.clone(),
                    ac.edge(
                        IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, &ps, &ys)?),
                        IndexedDeclSpec::tup(s, &spec.result_vec(i, &ps, &ys)?),
                    ),
                ));
                let body = conj_of(&atoms)?;
                rel_disjuncts
                    .push(yvs.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc)));
            }
        }
        let recursive = !rel_disjuncts.is_empty();
        let rel_matrix = disj_of(&rel_disjuncts).unwrap_or_else(Formula::false_);
        let rel_ex = crate::funcs::separation_full(env, ev, &rel_matrix, &sq, &s.ap.empty_ax)?;
        let (rel, rel_ax) = crate::define_by_membership(
            env,
            params,
            &rel_ex,
            ev,
            &Formula::and(Formula::mem(te.clone(), sq.clone()), rel_matrix.clone()),
        )?;
        let r = Term::apply(rel, ps.clone());
        let acc_set = ac.of(a_phi.clone(), r.clone());

        // ── the introduction rules ──────────────────────────────────────────
        let ni = spec.num_indices();
        let mut intro = Vec::with_capacity(n);
        for (i, yvs) in yvss.iter().enumerate() {
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let res = spec.result_vec(i, &ps, &ys)?;
            let tup_res = IndexedDeclSpec::tup(s, &res);
            let plain = typings(i, &ys);
            let mut atoms = plain.clone();
            for k in 0..ni {
                atoms.push(Formula::mem(res[k].clone(), spec.index_type_at(k, &ps, &res)?));
            }
            // `None` exactly when `kᵢ = 0` **and** `ni = 0` — a nullary
            // constructor of a non-indexed subsingleton, `PUnit.unit`. Then the
            // rule is unconditional; see [`Ante`].
            let ante = Ante(conj_of(&atoms));

            // `tup(e⃗ᵢ) ∈ Idx(p⃗)`. At `ni = 0` the index space is the one-point
            // set and `IndexSpace::intro` is the hypothesis-free
            // `⊢ ∀p⃗. • ∈ Idx(p⃗)`, so there is no run of conjuncts to project
            // and the membership is weakened into the context instead.
            let mut ia = ps.clone();
            ia.extend(res.iter().cloned());
            let h_idx = if ni == 0 {
                ante.lift(&inst_all(ix.intro(), &ia)?)
            } else {
                syl(
                    &crate::conj_sub(&atoms, plain.len(), atoms.len())?,
                    &inst_all(ix.intro(), &ia)?,
                )?
            };

            // The `i`-th disjunct of φ, witnessed by the fields themselves.
            let mut wit_atoms = plain.clone();
            wit_atoms.push(Formula::eq(tup_res.clone(), tup_res.clone()));
            let wit_body = conj_of(&wit_atoms)?;
            let mut parts: Vec<Thm> = (0..plain.len())
                .map(|j| crate::conj_proj(&atoms, j))
                .collect::<Option<_>>()?;
            parts.push(ante.lift(&Thm::eq_refl(tup_res.clone())));
            let h_body = fold_conj(&parts)?;
            debug_assert_eq!(*h_body.concl(), ante.wrap(wit_body));

            // Existentially close, one field at a time, then inject.
            //
            // **The witnesses need their own variables.** The disjunct being
            // built is `∃y⃗. (⋀ⱼ yⱼ ∈ βᵢⱼ ∧ tup(e⃗ᵢ(p⃗,y⃗ᵢ)) = tup(e⃗ᵢ(p⃗,y⃗)))`,
            // in which the left of the equation is the *fixed* subject
            // `tup_res` and only the right is under the binders. `tup_res`
            // mentions the very field variables being quantified, so wrapping
            // `Formula::exists(yⱼ, ·)` around a formula that already contains
            // it abstracts the left-hand occurrences too and yields a
            // reflexivity, not an instance — which no `disj_inject` will
            // accept. So the closure runs at a second, fresh vector `w⃗` and
            // instantiates it back at `y⃗` one step at a time; `tup_res` is
            // spelled at `y⃗` throughout and is never in a binder's scope.
            //
            // The two readings coincide exactly when `tup_res` has no field
            // variables in it — no fields (`k = 0`, the loop is empty) or no
            // indices (`ni = 0`, `tup() = •` is closed) — which is why every
            // declaration in this repository's corpus hid it.
            let wvs: Vec<kernel::FreeVar> = yvs.iter().map(|_| env.fresh_var()).collect();
            let mut h_disj = h_body;
            for pos in (0..yvs.len()).rev() {
                // `y₀ … y_{pos−1}` are already discharged; `w_pos … w_{k−1}`
                // are still witnesses, and `w_pos` is the one being bound.
                let mix: Vec<Term> = (0..yvs.len())
                    .map(|j| Term::var(if j < pos { yvs[j] } else { wvs[j] }))
                    .collect();
                let mut a = typings(i, &mix);
                a.push(Formula::eq(
                    tup_res.clone(),
                    IndexedDeclSpec::tup(s, &spec.result_vec(i, &ps, &mix)?),
                ));
                let body = wvs[pos + 1..]
                    .iter()
                    .rev()
                    .fold(conj_of(&a)?, |acc, w| Formula::exists(*w, acc));
                h_disj = syl(&h_disj, &exists_intro_imp(wvs[pos], body, ys[pos].clone())?)?;
            }
            let inj = disj_inject(&phi_disjuncts, i)?;
            let inj = subst_all(&inj, qv, &tup_res);
            let h_phi = ante.syl(&h_disj, &inj)?;

            let mut aa = ps.clone();
            aa.push(tup_res.clone());
            let into = iff_mpr(&inst_all(&phi_ax, &aa)?)?;
            let body = ante.syl(&ante.and(&h_idx, &h_phi)?, &into)?;
            if *body.concl() != ante.wrap(Formula::mem(tup_res, a_phi.clone())) {
                return None
            }
            let mut quant = params.to_vec();
            quant.extend(yvs.iter().copied());
            intro.push(gen_all(&quant, &body));
        }

        // ── the degenerate case: no recursion, so `R = ∅` and `acc = A_φ` ───
        let degenerate = if recursive {
            None
        } else {
            let mut ra = ps.clone();
            ra.push(te.clone());
            let at = inst_all(&rel_ax, &ra)?;
            let no_mem = Thm::gen(
                ev,
                &syl(
                    &syl(
                        &iff_mp(&at)?,
                        &crate::and_right(Formula::mem(te.clone(), sq), Formula::false_()),
                    )?,
                    &imp_refl(Formula::false_()),
                )?,
            );
            // `R = ∅`, by Extensionality against the empty set's own axiom.
            let empty_t = ac.empty_term();
            let same = Thm::gen(ev, &{
                let l = syl(&inst_all(&no_mem, std::slice::from_ref(&te))?, &ex_falso(Formula::mem(te.clone(), empty_t.clone())))?;
                let rr = syl(&inst_all(&ac.empty_ax, std::slice::from_ref(&te))?, &ex_falso(Formula::mem(te.clone(), r.clone())))?;
                crate::and_intro(&l, &rr)
            });
            let eq = Thm::mp(
                &inst_all(&Thm::ax_extensionality(env), &[r.clone(), empty_t.clone()])?,
                &same,
            )?;
            // `acc(A_φ, R) = acc(A_φ, ∅) = A_φ`.
            let hole = env.fresh_var();
            let lift = Thm::mp(
                &Thm::mp(
                    &Thm::eq_leibniz(
                        r.clone(),
                        empty_t.clone(),
                        hole,
                        Formula::eq(acc_set.clone(), ac.of(a_phi.clone(), Term::var(hole))),
                    ),
                    &eq,
                )?,
                &Thm::eq_refl(acc_set.clone()),
            )?;
            let closed = inst_all(&ac.empty_relation, std::slice::from_ref(&a_phi))?;
            let out = crate::eq_trans(env, &lift, &closed)?;
            if *out.concl() != Formula::eq(acc_set.clone(), a_phi.clone()) {
                return None
            }
            Some(gen_all(params, &out))
        };

        Some(LeCarrier {
            phi,
            phi_ax,
            a_phi,
            rel,
            rel_ax,
            r,
            acc_set,
            intro,
            degenerate,
            rel_subject: ev,
            phi_subject: qv,
            rel_disjuncts,
            phi_disjuncts,
        })
    }

    /// Whether [`LeCarrier::intro`]`[i]` is stated with an antecedent.
    ///
    /// `false` exactly when constructor `i` has no fields and the declaration
    /// has no indices, in which case the rule is the unconditional
    /// `⊢ ∀p⃗. • ∈ A_φ(p⃗)`. `None` when `i` is out of range.
    ///
    /// This is a question about the *spec*, decided before any theorem is
    /// built, which is why it is a free function of it rather than something
    /// read back off a conclusion.
    pub fn intro_is_conditional(spec: &LeSpec, i: usize) -> Option<bool> {
        Some(spec.base.ctors.get(i)?.args.len() + spec.num_indices() > 0)
    }

    /// Where constructor `i`'s `j`-th recursive argument's disjunct sits in
    /// [`LeCarrier::rel_disjuncts`] — the constructors' recursive slots
    /// concatenated in declared order.
    pub fn rel_slot(spec: &LeSpec, i: usize, j: usize) -> Option<usize> {
        if j >= spec.base.ctors.get(i)?.recs {
            return None
        }
        Some(spec.base.ctors[..i].iter().map(|c| c.recs).sum::<usize>() + j)
    }
}

/// The introduction rule's **optional** antecedent.
///
/// `Hᵢ ∧ Eᵢ` is the constructor's plain-field typings followed by its `ni`
/// result-index typings, and it is empty exactly when the constructor has no
/// fields *and* the declaration has no indices — `PUnit.unit`, `True.intro`.
/// One derivation has to produce both shapes: `⊢ ⊤ → • ∈ A_φ` is not a thing
/// this kernel can even say, and a caller that has to case-split on whether the
/// theorem it was handed is an implication is a caller that will get it wrong.
///
/// The same device as `crate::cumul`'s `Ctx`, and for the same reason. It is
/// private here rather than shared because the two carry *different* things —
/// there a parameter smallness assumption, here a typing conjunction — and the
/// combinators they need do not coincide.
struct Ante(Option<Formula>);

impl Ante {
    /// From `⊢ φ` infer `⊢ H → φ`.
    fn lift(&self, t: &Thm) -> Thm {
        match &self.0 {
            Some(h) => crate::a1i(t, h.clone()),
            None => t.clone(),
        }
    }

    /// From `⊢ [H →] φ` and `⊢ φ → ψ` infer `⊢ [H →] ψ`.
    fn syl(&self, t: &Thm, imp: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => syl(t, imp),
            None => Thm::mp(imp, t),
        }
    }

    /// From `⊢ [H →] φ` and `⊢ [H →] ψ` infer `⊢ [H →] (φ ∧ ψ)`.
    fn and(&self, p: &Thm, q: &Thm) -> Option<Thm> {
        match &self.0 {
            Some(_) => hyp_and(p, q),
            None => Some(crate::and_intro(p, q)),
        }
    }

    /// The formula a theorem in this context has, given its bare conclusion.
    fn wrap(&self, concl: Formula) -> Formula {
        match &self.0 {
            Some(h) => Formula::imp(h.clone(), concl),
            None => concl,
        }
    }
}

/// Fold `⊢ H → atomᵢ` into `⊢ H → (atom₀ ∧ (atom₁ ∧ …))`, matching
/// [`conj_of`]'s right nesting.
fn fold_conj(thms: &[Thm]) -> Option<Thm> {
    let mut acc = thms.last()?.clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = hyp_and(t, &acc)?;
    }
    Some(acc)
}

/// Substitute a term for a free variable throughout a theorem's conclusion, by
/// generalising and instantiating — the only route the kernel offers.
fn subst_all(t: &Thm, v: kernel::FreeVar, term: &Term) -> Thm {
    inst_all(&Thm::gen(v, t), std::slice::from_ref(term)).expect("one binder, one term")
}
