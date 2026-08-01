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
//! A recursive user-defined subsingleton — the case that needs the full
//! `R ≠ ∅` recursion — has **no witness in the 91 files**. Its carrier is
//! built here anyway (it is one formula recursion and costs nothing extra); its
//! *recursor* is deliberately deferred, per the standing decline-and-count
//! rule, and so is §6.2's index-projection minor, which is a wiring question
//! (which Lean binder ends up in which minor slot) rather than a derived one.
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
//! ```
//!
//! `Hᵢ` is the constructor's plain-argument typings and `Eᵢ` the `ni`
//! result-index typings — the same antecedent [`super::carrier`]'s membership
//! rule carries, and for the same reason: `Idx(p⃗)` membership cannot be derived
//! about opaque index symbols.

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
    /// membership in this.
    pub acc_set: Term,
    /// Per constructor,
    /// `⊢ ∀p⃗ ∀y⃗. ((Hᵢ ∧ Eᵢ) → tup(e⃗ᵢ(p⃗,y⃗)) ∈ A_φ(p⃗))`.
    pub intro: Vec<Thm>,
    /// `⊢ ∀p⃗. acc(A_φ(p⃗), R(p⃗)) = A_φ(p⃗)` — present **iff** no constructor is
    /// recursive, which is when `R` is provably empty.
    pub degenerate: Option<Thm>,
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
        if !spec.well_formed() || spec.indices.is_empty() || params.len() != spec.params() {
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
            let h = conj_of(&atoms)?; // `ni ≥ 1`, so never empty

            // `tup(e⃗ᵢ) ∈ Idx(p⃗)`.
            let mut ia = ps.clone();
            ia.extend(res.iter().cloned());
            let h_idx = syl(
                &crate::conj_sub(&atoms, plain.len(), atoms.len())?,
                &inst_all(ix.intro(), &ia)?,
            )?;

            // The `i`-th disjunct of φ, witnessed by the fields themselves.
            let mut wit_atoms = plain.clone();
            wit_atoms.push(Formula::eq(tup_res.clone(), tup_res.clone()));
            let wit_body = conj_of(&wit_atoms)?;
            let mut parts: Vec<Thm> = (0..plain.len())
                .map(|j| crate::conj_proj(&atoms, j))
                .collect::<Option<_>>()?;
            parts.push(crate::a1i(&Thm::eq_refl(tup_res.clone()), h.clone()));
            let h_body = fold_conj(&parts)?;
            debug_assert_eq!(*h_body.concl(), Formula::imp(h.clone(), wit_body));

            // Existentially close, one field at a time, then inject.
            let mut h_disj = h_body;
            for (pos, v) in yvs.iter().enumerate().rev() {
                let inner_atoms = {
                    let mut a = typings(i, &ys);
                    a.push(Formula::eq(
                        tq.clone(),
                        IndexedDeclSpec::tup(s, &spec.result_vec(i, &ps, &ys)?),
                    ));
                    conj_of(&a)?
                };
                let body = yvs[pos + 1..]
                    .iter()
                    .rev()
                    .fold(inner_atoms, |acc, w| Formula::exists(*w, acc));
                let body = body.subst(qv, &tup_res);
                h_disj = syl(&h_disj, &exists_intro_imp(*v, body, ys[pos].clone())?)?;
            }
            let inj = disj_inject(&phi_disjuncts, i)?;
            let inj = subst_all(&inj, qv, &tup_res);
            let h_phi = syl(&h_disj, &inj)?;

            let mut aa = ps.clone();
            aa.push(tup_res.clone());
            let into = iff_mpr(&inst_all(&phi_ax, &aa)?)?;
            let body = syl(&hyp_and(&h_idx, &h_phi)?, &into)?;
            if *body.concl() != Formula::imp(h, Formula::mem(tup_res, a_phi.clone())) {
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
        })
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
