//! **The guarded minors of an indexed family at a value motive** —
//! [`super::super::guard`]'s construction with the guard testing the *indexed*
//! induction hypothesis.
//!
//! # What differs, and what does not
//!
//! [`super::super::guard`] exists because `HYP` asks each minor to send
//! **arbitrary** `vⱼ ∈ T` into `T`, while Lean's dependent minor only promises
//! that when the `vⱼ` really are values of the motive; the answer is to
//! instantiate `GenRecursor` at a minor that *tests* its own hypothesis and
//! collapses to `∅` when the test fails. All of that is unchanged here. One
//! thing is not:
//!
//! ```text
//! non-indexed  psiᵢ := ⋀ⱼ vⱼ ∈ app(C, tⱼ)
//! indexed      psiᵢ := ⋀ⱼ tⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))  ,  ⋀ⱼ vⱼ ∈ app(m, d⃗ᵢⱼ, tⱼ)
//! ```
//!
//! The extra `mᵢ` conjuncts are **not caution.** `HYP` types a recursive field
//! at the *skeleton*, `tⱼ ∈ W`, while `IDEPᵢ`'s antecedent types it at the
//! *family*, `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` — a strictly stronger fact that
//! `minor_typedᵢ` does not carry, and without which the positive case could not
//! fire Lean's minor at all. It is dischargeable where it matters for exactly
//! the reason D7 works: at the induction step,
//! [`IndexedCtor::inv`](super::IndexedCtor::inv) reads it off
//! `ctorᵢ(y⃗,t⃗) ∈ ind(p⃗,x⃗)`.
//!
//! Everything between — the Separation, the `k + 2m` lambda graphs, the beta
//! chain, the positive/negative split and the regeneralisation — is
//! [`guarded_core`], called with this `psiᵢ` and with a `lands` closure that
//! spends [`super::dep_motive`]'s premises instead of
//! [`super::super::motive`]'s. There is one implementation of that plumbing.
//!
//! # Interface
//!
//! ```text
//! gminᵢ                                        [IndexedGuardedMinors::terms]
//! psiᵢ, atom by atom                     [IndexedGuardedMinors::guard_atoms]
//! ⊢ (ICOD ∧ IDEP) → minor_typedᵢ(gminᵢ, T)     [IndexedGuardedMinors::typed]
//! ⊢ (ICOD ∧ IDEP) → HYP(gmin⃗, T)               [IndexedGuardedMinors::hyp]
//! ⊢ ∀y⃗∀t⃗∀v⃗. ((minor_typedᵢ's antecedent ∧ psiᵢ)
//!        → gminᵢ⟪y⃗,t⃗⟫v⃗ = Sᵢ⟪y⃗,t⃗⟫v⃗)           [IndexedGuardedMinors::fires]
//! ```
//!
//! `minor_typedᵢ` and `HYP` are the **skeleton's** — [`minor_typed`], at
//! `ind.wty` — because the engine is the skeleton's
//! [`GenRecursor`](super::super::GenRecursor) and its hypothesis is not ours to
//! restate. The indices enter only through `psiᵢ` and through `IDEPᵢ`.
//!
//! # Nothing here is an axiom
//!
//! Per guarded constructor, exactly what [`super::super::guard`] mints: one
//! Separation, `k + 2m` Replacements and `2(k + 2m)` abbreviations, plus one
//! Extensionality per case.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::guard::{guarded_core, unguarded_core, union_empty, GuardVars, LandsAt};
use crate::inductive::machine::Machine;
use crate::inductive::motive::cod_parts;
use crate::inductive::premise::minor_typed;
use crate::inductive::rec_shared::{hyp_conj, hyp_inst, rewrite_under, under};
use crate::inductive::step::applied_minor;
use crate::inductive::Slot;
use crate::sums::Sums;
use crate::{a1i, and_left, and_right, conj_of, conj_proj, eq_symm, hyp_mp, inst_all, syl};

use super::carrier::IndexedCarrier;
use super::dep_motive::{icod, idep_parts};
use super::prop_rec::{lean_order_of, minor_atoms_at};
use super::spec::IndexedDeclSpec;

/// **`psiᵢ`, atom by atom** — the `mᵢ` recursive fields at their *indexed*
/// types, then the `mᵢ` induction hypotheses at the motive.
///
/// Exactly the entries of [`minor_atoms_at`] that `minor_typedᵢ`'s antecedent
/// does not already supply, taken from that builder rather than restated, so
/// the guard and `IDEPᵢ`'s antecedent cannot drift. Empty at `mᵢ = 0`, where
/// there is no guard.
#[allow(clippy::too_many_arguments)]
pub fn guard_atoms_of(
    s: &Sums,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    i: usize,
    motive: &Term,
    ps: &[Term],
    ys: &[Term],
    ts: &[Term],
    vs: &[Term],
) -> Option<Vec<Formula>> {
    let c = spec.base.ctors.get(i)?;
    let (k, m) = (c.args.len(), c.recs);
    let a = minor_atoms_at(s, spec, ixc, i, motive, ps, ys, ts, vs)?;
    if a.len() != k + 2 * m {
        return None
    }
    let mut out: Vec<Formula> = (0..m)
        .map(|j| Some(a.get(rec_position(&c.order, j)?)?.clone()))
        .collect::<Option<_>>()?;
    out.extend(a[k + m..].iter().cloned());
    Some(out)
}

/// The position of the `j`-th [`Slot::Rec`] in the declared mask.
fn rec_position(order: &[Slot], j: usize) -> Option<usize> {
    let mut seen = 0;
    for (q, slot) in order.iter().enumerate() {
        if matches!(slot, Slot::Rec) {
            if seen == j {
                return Some(q)
            }
            seen += 1;
        }
    }
    None
}

/// `minor_typedᵢ`'s antecedent, atom by atom, at caller-chosen terms: the `k`
/// plain typings, the `m` carrier memberships at `W`, the `m` values at `T`.
fn typed_atoms(
    ind: &Inductive,
    i: usize,
    ps: &[Term],
    ys: &[Term],
    ts: &[Term],
    vs: &[Term],
    tt: &Term,
) -> Vec<Formula> {
    let c = &ind.spec.ctors[i];
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(c.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    atoms.extend(vs.iter().map(|v| Formula::mem(v.clone(), tt.clone())));
    atoms
}

/// The guarded minors of one indexed declaration at a value-valued motive.
pub struct IndexedGuardedMinors {
    /// The motive variable `m`.
    pub motive: FreeVar,
    /// Lean's dependent minor-premise variables `S₀ … S_{n-1}`.
    pub minors: Vec<FreeVar>,
    /// The target variable `T`.
    pub target: FreeVar,
    /// `gminᵢ`, in constructor order — `Sᵢ` itself where `mᵢ = 0`.
    pub terms: Vec<Term>,
    /// `ICOD(m,T)`.
    pub cod: Formula,
    /// The `IDEPᵢ(m,Sᵢ)` conjuncts, and their conjunction.
    pub dep_parts: Vec<Formula>,
    /// `IDEP(m,S⃗)`.
    pub dep: Formula,
    /// The `kᵢ` plain, `mᵢ` recursive and `mᵢ` value variables each
    /// [`IndexedGuardedMinors::guard_atoms`] and
    /// [`IndexedGuardedMinors::fires`] is stated at.
    pub vars: Vec<(Vec<FreeVar>, Vec<FreeVar>, Vec<FreeVar>)>,
    /// `psiᵢ`, atom by atom, at those variables. Empty where `mᵢ = 0`.
    pub guard_atoms: Vec<Vec<Formula>>,
    /// The skeleton's `minor_typedᵢ(gminᵢ, T)` conjuncts.
    pub minor_typed: Vec<Formula>,
    /// `⊢ (ICOD ∧ IDEP) → minor_typedᵢ(gminᵢ, T)`, per constructor.
    pub typed: Vec<Thm>,
    /// `⊢ (ICOD ∧ IDEP) → HYP(gmin⃗, T)`.
    pub hyp: Thm,
    /// The firing rules; `None` exactly where `mᵢ = 0` and `gminᵢ` **is** `Sᵢ`.
    pub fires: Vec<Option<Thm>>,
}

impl IndexedGuardedMinors {
    /// Build the guarded minors of an indexed family and discharge `HYP`.
    ///
    /// `motive`, `minors` and `target` are the caller's own variables, so the
    /// formulas here and the ones [`super::super::recursor`]'s schemas are
    /// instantiated to are literally the same. `ind` must be the family's
    /// skeleton over `mach`. `None` for a declaration with no constructors or
    /// no indices, on a length mismatch, or on any internal shape check.
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ixc: &IndexedCarrier,
        motive: FreeVar,
        minors: &[FreeVar],
        target: FreeVar,
    ) -> Option<IndexedGuardedMinors> {
        let n = spec.len();
        if n == 0
            || spec.num_indices() == 0
            || minors.len() != n
            || !ind.is_over(mach)
            || ind.spec.ctors.len() != n
            || ind.params.len() != spec.base.params
        {
            return None
        }
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let (tm, tt) = (Term::var(motive), Term::var(target));
        let su: Vec<Term> = minors.iter().map(|v| Term::var(*v)).collect();

        let cod_f = icod(env, s, &ind.wty, spec.num_indices(), &tm, &tt);
        let dep_parts_f = idep_parts(env, mach, ind, spec, ixc, &tm, &su)?;
        let dep_f = conj_of(&dep_parts_f)?;
        let g = Formula::and(cod_f.clone(), dep_f.clone());
        let (covers_f, empty_f) = cod_parts(&cod_f)?;

        // `⊢ g → ∅ ∈ T`, which is all the negative case needs of `ICOD`.
        let empty_in_t = syl(
            &and_left(cod_f.clone(), dep_f.clone()),
            &and_right(covers_f, empty_f),
        )?;
        let un_empty = union_empty(env, ap)?;

        let mut terms = Vec::with_capacity(n);
        let mut typed = Vec::with_capacity(n);
        let mut fires = Vec::with_capacity(n);
        let mut guard_atoms = Vec::with_capacity(n);
        let mut vars = Vec::with_capacity(n);
        for i in 0..n {
            let c = &spec.base.ctors[i];
            let (k, m) = (c.args.len(), c.recs);
            let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
            let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
            let vvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
            let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

            let psi_atoms = guard_atoms_of(s, spec, ixc, i, &tm, &ps, &ys, &ts, &vs)?;
            let land = Landing {
                mach,
                ind,
                spec,
                i,
                cod_f: &cod_f,
                dep_f: &dep_f,
                dep_parts_f: &dep_parts_f,
                a_atoms: minor_atoms_at(s, spec, ixc, i, &tm, &ps, &ys, &ts, &vs)?,
                psi_atoms: psi_atoms.clone(),
                h_atoms: typed_atoms(ind, i, &ps, &ys, &ts, &vs, &tt),
                ps: &ps,
                ys: &ys,
                ts: &ts,
                vs: &vs,
                order: &c.order,
                minor: &su[i],
            };

            let (term, th, fired) = if m == 0 {
                let mut f = |e: &mut Env, at: LandsAt<'_>| land.lands(e, at);
                let th = unguarded_core(env, mach, ind, i, &g, &yvs, &su[i], &tt, &mut f)?;
                (su[i].clone(), th, None)
            } else {
                let psi = conj_of(&psi_atoms)?;
                let mut f = |e: &mut Env, at: LandsAt<'_>| land.lands(e, at);
                let (t, th, fr) = guarded_core(
                    env,
                    mach,
                    ind,
                    i,
                    &g,
                    GuardVars { yvs: &yvs, tvs: &tvs, vvs: &vvs },
                    &psi,
                    &[motive],
                    minors[i],
                    target,
                    &empty_in_t,
                    &un_empty,
                    &mut f,
                )?;
                (t, th, Some(fr))
            };
            terms.push(term);
            typed.push(th);
            fires.push(fired);
            guard_atoms.push(psi_atoms);
            vars.push((yvs, tvs, vvs));
        }

        let mt: Vec<Formula> = (0..n)
            .map(|i| minor_typed(env, s, &ind.spec.ctors[i], &ps, &ind.wty, &terms[i], &tt))
            .collect();
        for i in 0..n {
            if !crate::establishes(&typed[i], &Formula::imp(g.clone(), mt[i].clone())) {
                return None
            }
        }
        let hyp = hyp_conj(&typed)?;
        if !crate::establishes(&hyp, &Formula::imp(g, conj_of(&mt)?)) {
            return None
        }
        // Every field is documented `⊢ …`; a sequent hypothesis would be
        // invisible to the conclusion comparisons above.
        if !crate::all_unconditional(&fires.iter().flatten().collect::<Vec<_>>()) {
            return None
        }

        Some(IndexedGuardedMinors {
            motive,
            minors: minors.to_vec(),
            target,
            terms,
            cod: cod_f,
            dep_parts: dep_parts_f,
            dep: dep_f,
            vars,
            guard_atoms,
            minor_typed: mt,
            typed,
            hyp,
            fires,
        })
    }
}

/// Everything "the minor's value lands in `T`" needs at one constructor.
struct Landing<'a> {
    mach: &'a Machine,
    ind: &'a Inductive,
    spec: &'a IndexedDeclSpec,
    i: usize,
    cod_f: &'a Formula,
    dep_f: &'a Formula,
    dep_parts_f: &'a [Formula],
    /// `Aᵢ`, atom by atom.
    a_atoms: Vec<Formula>,
    /// `psiᵢ`, atom by atom.
    psi_atoms: Vec<Formula>,
    /// `minor_typedᵢ`'s antecedent, atom by atom.
    h_atoms: Vec<Formula>,
    ps: &'a [Term],
    ys: &'a [Term],
    ts: &'a [Term],
    vs: &'a [Term],
    order: &'a [Slot],
    minor: &'a Term,
}

impl Landing<'_> {
    /// `⊢ ctx → Sᵢ⟪y⃗,t⃗⟫v⃗ ∈ T` — the one place `IDEP` and `ICOD` are spent.
    ///
    /// `IDEPᵢ` puts the value in `app(m, e⃗ᵢ, ctorᵢ)`; `ICOV`, at that index
    /// vector and at `ctorᵢ ∈ W`, carries it into the target.
    fn lands(&self, env: &mut Env, at: LandsAt<'_>) -> Option<Thm> {
        let (mach, ind, spec, i) = (self.mach, self.ind, self.spec, self.i);
        let ap = &mach.wt.sums.ap;
        let (k, m) = (self.ys.len(), self.ts.len());
        let ctx = at.ctx;

        // ── `Aᵢ`, atom by atom ──────────────────────────────────────────────
        // The plain typings come out of `minor_typedᵢ`'s own antecedent; the
        // recursive fields at their indexed types and the induction hypotheses
        // come out of the guard, which is the whole reason the guard is longer
        // here than in the non-indexed case.
        let field: Vec<Thm> = (0..k + m)
            .map(|j| syl(at.k_h, &conj_proj(&self.h_atoms, j)?))
            .collect::<Option<_>>()?;
        let psi: Vec<Thm> = match at.k_psi {
            None => Vec::new(),
            Some(kp) => (0..2 * m)
                .map(|j| syl(kp, &conj_proj(&self.psi_atoms, j)?))
                .collect::<Option<_>>()?,
        };
        if psi.len() != 2 * m {
            return None
        }
        let plains: Vec<Thm> = field[..k].to_vec();
        let recs: Vec<Thm> = psi[..m].to_vec();
        let mut a_thms = lean_order_of(self.order, &plains, &recs)?;
        a_thms.extend(psi[m..].iter().cloned());
        for (q, th) in a_thms.iter().enumerate() {
            if *th.concl() != Formula::imp(ctx.clone(), self.a_atoms.get(q)?.clone()) {
                return None
            }
        }

        // ── `IDEPᵢ` at the fields in declared order, then the hypotheses ────
        let k_dep = syl(at.k_g, &and_right(self.cod_f.clone(), self.dep_f.clone()))?;
        let k_dep_i = syl(&k_dep, &conj_proj(self.dep_parts_f, i)?)?;
        let mut insts = lean_order_of(self.order, self.ys, self.ts)?;
        insts.extend(self.vs.iter().cloned());
        let inst = hyp_inst(&k_dep_i, &insts)?;
        let k_val = match hyp_conj(&a_thms) {
            Some(prem) => hyp_mp(&inst, &prem)?,
            None => inst,
        };

        // ── `ctorᵢ(y⃗,t⃗) ∈ W`, through the carrier's abbreviation ────────────
        let ctor_t = ind.ctor_term(mach, i, self.ys, self.ts)?;
        let ty_at = inst_all(&ind.ty_ax, self.ps)?;
        let mut ctor_args = self.ps.to_vec();
        ctor_args.extend(self.ys.iter().cloned());
        ctor_args.extend(self.ts.iter().cloned());
        let mem_rule = inst_all(&ind.ctors[i].mem, &ctor_args)?;
        let k_mem = match &ind.ctors[i].hyp {
            None => under(&mem_rule, ctx),
            Some(_) => {
                // The rule types the recursive fields at `ind(p⃗)`; the ambient
                // has them at `W`.
                let back = eq_symm(env, &ty_at)?;
                let mut atoms: Vec<Thm> = plains.clone();
                for (j, tj) in self.ts.iter().enumerate() {
                    let tc = tj.clone();
                    atoms.push(rewrite_under(
                        env,
                        &under(&back, ctx),
                        move |q| Formula::mem(tc.clone(), q),
                        &field[k + j],
                    )?);
                }
                hyp_mp(&a1i(&mem_rule, ctx.clone()), &hyp_conj(&atoms)?)?
            }
        };
        let ctor_c = ctor_t.clone();
        let k_w = rewrite_under(
            env,
            &under(&ty_at, ctx),
            move |q| Formula::mem(ctor_c.clone(), q),
            &k_mem,
        )?;

        // ── `ICOV` at `(e⃗ᵢ, ctorᵢ)` carries the value into the target ───────
        let (covers, empty_in) = cod_parts(self.cod_f)?;
        let k_cod = syl(at.k_g, &and_left(self.cod_f.clone(), self.dep_f.clone()))?;
        let k_covers = syl(&k_cod, &and_left(covers, empty_in))?;
        let mut ix = spec.result_vec(i, self.ps, self.ys)?;
        ix.push(ctor_t);
        let k_inner = hyp_mp(&hyp_inst(&k_covers, &ix)?, &k_w)?;
        let val = applied_minor(ap, self.order, self.minor, self.ys, self.ts, self.vs);
        hyp_mp(&hyp_inst(&k_inner, std::slice::from_ref(&val))?, &k_val)
    }
}
