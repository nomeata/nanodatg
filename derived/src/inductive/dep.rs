//! **The recursor at a dependent motive** — `RECURSOR-DESIGN.md` §5.3's
//! extension, built.
//!
//! # What this closes
//!
//! [`super::recursor`]'s [`GenRecursor`] is simply typed: `grec(p⃗,s⃗,T)` lands
//! in one target *set*. What a `(declaration, σ)` pair actually asks of
//! `⟦T.rec.{σ}⟧` is
//!
//! ```text
//! ∀t ∈ ⟦T p⃗⟧. rec(t) ∈ app(C, t)
//! ```
//!
//! with the motive `C` **still a bound variable** — a different obligation from
//! the ι *equation* at a use site where `C` has been instantiated, and the one
//! every class-(T) recursor on the tutorial corpus needs, because the corpus's
//! recursor files η-expand the eliminator itself and so never have a constant
//! motive.
//!
//! # Interface
//!
//! Writing `W` for the raw carrier, `C`/`S⃗`/`T` for the motive, Lean's minor
//! premises and the target ([`DepRecursor::motive`] etc.),
//! `drec := grec(p⃗, gmin⃗, T)` for [`DepRecursor::rec`], `COD`/`DEP` for
//! [`super::motive`]'s premises and `PRE := COD ∧ DEP`:
//!
//! ```text
//! ⊢ PRE → ∀z. (z ∈ W → app(drec, z) ∈ app(C, z))          [DepRecursor::typing]
//!
//! ⊢ PRE → ∀y⃗ ∀t⃗. (( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1}) ∧ ⋀ⱼ tⱼ ∈ W )
//!            → app(drec, ctorᵢ(y⃗,t⃗))
//!                = Sᵢ⟪y⃗,t⃗ in declared order⟫
//!                    app(drec,t₀) … app(drec,t_{mᵢ-1}))     [DepRecursor::iota]
//! ```
//!
//! Both are stated at **Lean's own** minor premises `Sᵢ`, not at the guarded
//! ones [`super::guard`] instantiates `GenRecursor` with; the guard is an
//! implementation detail of the term, and [`super::guard::GuardedMinors::fires`]
//! is what removes it from the statements. `PRE` is exactly Lean's own
//! hypotheses: `DEP` is its dependent minor-premise typing pointwise, and `COD`
//! is discharged outright by [`super::motive::cod_at_funspace`] at
//! `T := ⋃V ∪ {∅}` for any `V` the motive is a function into.
//!
//! # How it goes through, and where the work is
//!
//! Not by a new recursion. `drec` **is** `GenRecursor`'s term, at a particular
//! choice of `s⃗` and `T`; all four of (S1)–(S4) are reused by instantiation.
//! The two things that did not exist are:
//!
//! 1. `HYP` at a variable motive — [`super::guard`], which is where the
//!    `⋃img(C)` obstruction is actually dissolved;
//! 2. an induction principle stated in the declaration's own constructors —
//!    [`super::rect`], which is what carries `app(drec, z) ∈ app(C, z)` from the
//!    constructors to the whole carrier, and which needs the two η rules
//!    (`Telescope::eta` and `rect::recarg_eta`) because `φ` is applied to the
//!    carrier element itself.
//!
//! Given those, the induction step is: fire (S4) to get
//! `app(drec, ctorᵢ) = gminᵢ⟪y⃗,t⃗⟫(drec t⃗)`, note that the induction hypotheses
//! `app(drec,tⱼ) ∈ app(C,tⱼ)` are *precisely* the guard, rewrite `gminᵢ` to
//! `Sᵢ`, and apply `DEPᵢ`. The ι rule is the same computation with the
//! induction hypotheses supplied by [`DepRecursor::typing`] instead, which is
//! why it comes second and carries no `φ(tⱼ)`.
//!
//! # Nothing here is an axiom
//!
//! One [`super::rect::decl_rect`] (one Separation) and instances of theorems
//! that already exist; the symbols are [`super::guard`]'s.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::wrec::hyp_eq_trans;
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, eq_symm, hyp_and, hyp_mp, inst_all, syl, uncurry,
};

use super::carrier::{ctor_atoms, Inductive};
use super::guard::GuardedMinors;
use super::machine::Machine;
use super::motive::cod_parts;
use super::rec_shared::{carry_back, gen_under, hyp_conj, hyp_inst, rewrite_under, under};
use super::recursor::GenRecursor;
use super::rect::{decl_rect, rect_parts};
use super::step::applied_minor;

/// The eliminator of one declaration at a **dependent** motive.
pub struct DepRecursor {
    /// The motive variable `C`.
    pub motive: FreeVar,
    /// Lean's dependent minor-premise variables `S₀ … S_{n-1}`.
    pub minors: Vec<FreeVar>,
    /// The target variable `T`.
    pub target: FreeVar,
    /// The guarded minors `GenRecursor` was instantiated at, and everything
    /// derived about them.
    pub guards: GuardedMinors,
    /// `drec = grec(p⃗, gmin⃗, T)` at the declaration's own parameters.
    pub rec: Term,
    /// `PRE = COD(C,T) ∧ DEP(C,S⃗)`.
    pub premise: Formula,
    /// `⊢ PRE → ∀z. (z ∈ W → app(drec,z) ∈ app(C,z))` — **the obligation**.
    pub typing: Thm,
    /// `⊢ PRE → ∀y⃗ ∀t⃗. (Hᵢ → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t⃗))`,
    /// per constructor, with `Hᵢ` the field typings and `tⱼ ∈ W`.
    pub iota: Vec<Thm>,
}

impl DepRecursor {
    /// Derive the whole development over a caller-supplied carrier, general
    /// recursor and W-recursor.
    ///
    /// `gr` must be [`GenRecursor::build`]'s output over *this* `mach`, `ind`
    /// and `rc` ([`GenRecursor::is_over`]), and `rc` the W-recursor it was
    /// built over — every term below splices `gr`'s Replacement symbols into
    /// `ind`'s carrier, and a foreign one would produce a well-formed term that
    /// nothing here is true of. `None` for a declaration with no constructors,
    /// or if any internal shape check fails.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        gr: &GenRecursor,
        rc: &Recursor,
    ) -> Option<DepRecursor> {
        let n = ind.spec.ctors.len();
        if n == 0 || !gr.is_over(mach, ind) {
            return None
        }
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        let motive = env.fresh_var();
        let minors: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
        let target = env.fresh_var();
        let guards = GuardedMinors::build(env, mach, ind, motive, &minors, target)?;
        let (tc, tt) = (Term::var(motive), Term::var(target));
        let drec = gr.rec_of(mach, ind, rc, &ps, &guards.terms, &tt)?;
        let premise = Formula::and(guards.cod.clone(), guards.dep.clone());

        // `φ(z) := app(drec, z) ∈ app(C, z)` — the obligation, pointwise.
        let zv = env.fresh_var();
        let phi = Formula::mem(
            ap.apply(drec.clone(), Term::var(zv)),
            ap.apply(tc.clone(), Term::var(zv)),
        );
        let rect = decl_rect(env, mach, ind, zv, &phi)?;
        let parts = rect_parts(env, mach, ind, zv, &phi)?;

        // ── the induction steps ─────────────────────────────────────────────
        let mut steps = Vec::with_capacity(n);
        for i in 0..n {
            steps.push(induction_step(
                env, mach, ind, gr, &guards, rc, &drec, &premise, &parts, i,
            )?);
        }
        let typing = syl(&hyp_conj(&steps)?, &rect)?;
        let goal_all = Formula::forall(
            zv,
            Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
        );
        if !crate::establishes(&typing, &Formula::imp(premise.clone(), goal_all)) {
            return None
        }

        // ── the dependent ι rules ───────────────────────────────────────────
        let mut iota = Vec::with_capacity(n);
        for i in 0..n {
            iota.push(dep_iota(
                env, mach, ind, gr, &guards, &drec, &premise, &typing, zv, &phi, i,
            )?);
        }

        let mut fields: Vec<&Thm> = vec![&typing];
        fields.extend(iota.iter());
        if !crate::all_unconditional(&fields) {
            return None
        }
        Some(DepRecursor { motive, minors, target, guards, rec: drec, premise, typing, iota })
    }
}

/// The `k + m` typing atoms of `rect_stepᵢ`/`ι`'s antecedent, at caller-chosen
/// field terms: the argument types, then the carrier memberships.
fn field_atoms(ind: &Inductive, i: usize, ps: &[Term], ys: &[Term], ts: &[Term]) -> Vec<Formula> {
    let ctor = &ind.spec.ctors[i];
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    atoms
}

/// `⊢ ctx → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t₀) … ` — **the ι
/// computation**, at Lean's own minor.
///
/// Fires (S4) at the guarded minors, then removes the guard: its condition is
/// `app(drec,tⱼ) ∈ app(C,tⱼ)`, which is exactly what `k_phi` supplies.
#[allow(clippy::too_many_arguments)]
fn fire(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    gr: &GenRecursor,
    guards: &GuardedMinors,
    drec: &Term,
    ctx: &Formula,
    k_cod: &Thm,
    k_hyp: &Thm,
    k_fields: &[Thm],
    k_phi: &[Thm],
    ys: &[Term],
    ts: &[Term],
    i: usize,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let (tc, tt) = (Term::var(guards.motive), Term::var(guards.target));
    let m = ts.len();
    let vs: Vec<Term> = ts.iter().map(|t| ap.apply(drec.clone(), t.clone())).collect();

    // (S4), at the guarded minors and this target.
    let mut args = ps.clone();
    args.extend(guards.terms.iter().cloned());
    args.push(tt.clone());
    args.extend(ys.iter().cloned());
    args.extend(ts.iter().cloned());
    let iota_at = inst_all(&gr.iota[i], &args)?;

    let tel = &ind.telescopes[i];
    let hctor = ctor_atoms(tel, &ps, ys, ts, &ind.carrier);
    let k_iota = match conj_of(&hctor) {
        None => hyp_mp(&a1i(&iota_at, ctx.clone()), k_hyp)?,
        Some(_) => {
            // The rule types the recursive fields at `ind(p⃗)`; `ctx` has `W`.
            let ty_at = inst_all(&ind.ty_ax, &ps)?;
            let back = eq_symm(env, &ty_at)?;
            let mut atoms: Vec<Thm> = k_fields[..ys.len()].to_vec();
            for (j, t) in ts.iter().enumerate() {
                let t_c = t.clone();
                atoms.push(rewrite_under(
                    env,
                    &under(&back, ctx),
                    move |q| Formula::mem(t_c.clone(), q),
                    &k_fields[ys.len() + j],
                )?);
            }
            hyp_mp(&a1i(&iota_at, ctx.clone()), &hyp_and(k_hyp, &hyp_conj(&atoms)?)?)?
        }
    };

    // The guard fires, if there is one.
    match &guards.fires[i] {
        None => Some(k_iota),
        Some(fired) => {
            // `app(drec,tⱼ) ∈ T`, from `COD` at `tⱼ ∈ W` and the hypothesis.
            let (covers, _) = cod_parts(&guards.cod)?;
            let k_covers = syl(k_cod, &and_left(covers, cod_parts(&guards.cod)?.1))?;
            let mut k_in_t = Vec::with_capacity(m);
            for j in 0..m {
                let at = hyp_inst(&k_covers, std::slice::from_ref(&ts[j]))?;
                let inner = hyp_mp(&at, &k_fields[ys.len() + j])?;
                k_in_t.push(hyp_mp(
                    &hyp_inst(&inner, std::slice::from_ref(&vs[j]))?,
                    &k_phi[j],
                )?);
            }
            let mut h_atoms: Vec<Thm> = k_fields.to_vec();
            h_atoms.extend(k_in_t);
            let mut insts = ys.to_vec();
            insts.extend(ts.iter().cloned());
            insts.extend(vs.iter().cloned());
            let at = hyp_inst(&under(fired, ctx), &insts)?;
            let k_eq = hyp_mp(&at, &hyp_and(&hyp_conj(&h_atoms)?, &hyp_conj(k_phi)?)?)?;
            let out = hyp_eq_trans(env, &k_iota, &k_eq)?;
            let want = Formula::eq(
                ap.apply(drec.clone(), ind.ctor_term(mach, i, ys, ts)?),
                applied_minor(ap, &ind.spec.ctors[i].order, &Term::var(guards.minors[i]), ys, ts, &vs),
            );
            let _ = tc;
            if *out.concl() != Formula::imp(ctx.clone(), want) {
                return None
            }
            Some(out)
        }
    }
}

/// `⊢ PRE → rect_stepᵢ(φ)` — the `i`-th induction step of [`super::rect`],
/// discharged from Lean's premises.
#[allow(clippy::too_many_arguments)]
fn induction_step(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    gr: &GenRecursor,
    guards: &GuardedMinors,
    _rc: &Recursor,
    drec: &Term,
    premise: &Formula,
    parts: &[Formula],
    i: usize,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tc = Term::var(guards.motive);
    let (k, m) = (ind.spec.ctors[i].args.len(), ind.spec.ctors[i].recs);

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = ts.iter().map(|t| ap.apply(drec.clone(), t.clone())).collect();

    let mut atoms = field_atoms(ind, i, &ps, &ys, &ts);
    atoms.extend(
        (0..m).map(|j| Formula::mem(vs[j].clone(), ap.apply(tc.clone(), ts[j].clone()))),
    );
    let (ctx, k_prem, k_atom): (Formula, Thm, Vec<Thm>) = match conj_of(&atoms) {
        None => (premise.clone(), crate::imp_refl(premise.clone()), Vec::new()),
        Some(h) => {
            let ctx = Formula::and(premise.clone(), h.clone());
            let rest = and_right(premise.clone(), h.clone());
            let projected = (0..atoms.len())
                .map(|j| syl(&rest, &conj_proj(&atoms, j)?))
                .collect::<Option<Vec<Thm>>>()?;
            (ctx, and_left(premise.clone(), h), projected)
        }
    };

    let k_cod = syl(&k_prem, &and_left(guards.cod.clone(), guards.dep.clone()))?;
    let k_dep = syl(&k_prem, &and_right(guards.cod.clone(), guards.dep.clone()))?;
    let k_hyp = syl(&k_prem, &guards.hyp)?;
    let k_fields = &k_atom[..k + m];
    let k_phi = &k_atom[k + m..];

    let k_eq = fire(
        env, mach, ind, gr, guards, drec, &ctx, &k_cod, &k_hyp, k_fields, k_phi, &ys, &ts, i,
    )?;

    // `DEPᵢ` at the fields and the recursive calls.
    let k_dep_i = syl(&k_dep, &conj_proj(&guards.dep_parts, i)?)?;
    let mut insts = ys.clone();
    insts.extend(ts.iter().cloned());
    insts.extend(vs.iter().cloned());
    let at = hyp_inst(&k_dep_i, &insts)?;
    let k_val = match hyp_conj(&k_atom) {
        Some(prem) => hyp_mp(&at, &prem)?,
        None => at,
    };

    let ctor_t = ind.ctor_term(mach, i, &ys, &ts)?;
    let body = carry_back(env, &k_eq, &k_val, &ap.apply(tc.clone(), ctor_t))?;
    let out = if atoms.is_empty() { body } else { uncurry(&body)? };
    let quantified = yvs
        .iter()
        .chain(tvs.iter())
        .rev()
        .try_fold(out, |acc, v| gen_under(*v, premise, &acc))?;
    if !crate::establishes(&quantified, &Formula::imp(premise.clone(), parts[i].clone())) {
        return None
    }
    Some(quantified)
}

/// `⊢ PRE → ∀y⃗ ∀t⃗. (Hᵢ → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t⃗))`.
///
/// The same computation as [`induction_step`], with the induction hypotheses
/// supplied by [`DepRecursor::typing`] rather than assumed — which is what
/// makes the ι rule's antecedent Lean's constructor typing and nothing more.
#[allow(clippy::too_many_arguments)]
fn dep_iota(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    gr: &GenRecursor,
    guards: &GuardedMinors,
    drec: &Term,
    premise: &Formula,
    typing: &Thm,
    zv: FreeVar,
    phi: &Formula,
    i: usize,
) -> Option<Thm> {
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let (k, m) = (ind.spec.ctors[i].args.len(), ind.spec.ctors[i].recs);

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();

    let atoms = field_atoms(ind, i, &ps, &ys, &ts);
    let (ctx, k_prem, k_atom): (Formula, Thm, Vec<Thm>) = match conj_of(&atoms) {
        None => (premise.clone(), crate::imp_refl(premise.clone()), Vec::new()),
        Some(h) => {
            let ctx = Formula::and(premise.clone(), h.clone());
            let rest = and_right(premise.clone(), h.clone());
            let projected = (0..atoms.len())
                .map(|j| syl(&rest, &conj_proj(&atoms, j)?))
                .collect::<Option<Vec<Thm>>>()?;
            (ctx, and_left(premise.clone(), h), projected)
        }
    };

    let k_cod = syl(&k_prem, &and_left(guards.cod.clone(), guards.dep.clone()))?;
    let k_hyp = syl(&k_prem, &guards.hyp)?;

    // The induction hypotheses, off the typing theorem.
    let k_typing = syl(&k_prem, typing)?;
    let mut k_phi = Vec::with_capacity(m);
    for j in 0..m {
        let at = hyp_inst(&k_typing, std::slice::from_ref(&ts[j]))?;
        k_phi.push(hyp_mp(&at, &k_atom[k + j])?);
    }
    let _ = (zv, phi);

    let body = fire(
        env, mach, ind, gr, guards, drec, &ctx, &k_cod, &k_hyp, &k_atom, &k_phi, &ys, &ts, i,
    )?;
    let out = if atoms.is_empty() { body } else { uncurry(&body)? };
    let quantified = yvs
        .iter()
        .chain(tvs.iter())
        .rev()
        .try_fold(out, |acc, v| gen_under(*v, premise, &acc))?;

    let want = dep_iota_stmt(env, mach, ind, guards, drec, i)?;
    if !crate::establishes(&quantified, &Formula::imp(premise.clone(), want)) {
        return None
    }
    Some(quantified)
}

/// The `i`-th dependent ι rule's own statement, for a caller to rebuild and
/// compare against.
pub fn dep_iota_stmt(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    guards: &GuardedMinors,
    drec: &Term,
    i: usize,
) -> Option<Formula> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let (k, m) = (ind.spec.ctors.get(i)?.args.len(), ind.spec.ctors[i].recs);

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = ts.iter().map(|t| ap.apply(drec.clone(), t.clone())).collect();

    let atoms = field_atoms(ind, i, &ps, &ys, &ts);
    let concl = Formula::eq(
        ap.apply(drec.clone(), ind.ctor_term(mach, i, &ys, &ts)?),
        applied_minor(ap, &ind.spec.ctors[i].order, &Term::var(guards.minors[i]), &ys, &ts, &vs),
    );
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    Some(quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc)))
}
