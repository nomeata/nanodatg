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
//! # A function-typed recursive argument
//!
//! At `RTree = leaf | node (children : Bool → RTree)` the two deliverables are
//!
//! ```text
//! ⊢ PRE → ∀z. (z ∈ W → app(drec,z) ∈ app(C,z))
//! ⊢ PRE → ∀g. (g ∈ fs(A₀,W) → app(drec, node(g)) = app(app(S₁,g), comp(drec,g,A₀)))
//! ```
//!
//! with `PRE`'s `DEP₁` taking the field's own function and a **family** of
//! induction hypotheses:
//!
//! ```text
//! ∀g ∀v. ((g ∈ fs(A₀,W) ∧ ∀z. (z ∈ A₀ → app(v,z) ∈ app(C, app(g,z))))
//!            → app(app(S₁,g),v) ∈ app(C, node(g)))
//! ```
//!
//! Three things carry the widening, and each is a single place:
//!
//! * [`super::motive::ih_at_motive`] — the pointwise shape, used by `DEPᵢ` and
//!   by [`super::guard`]'s guard formula, so that discharging one is not a
//!   coincidence with respect to the other;
//! * [`Inductive::minor_subs`] / [`Inductive::minor_ihs`] — what the minor
//!   premise's recursive and ih slots receive, the *same* funnel
//!   [`super::iota`] builds the value ι rule from, so the two rules cannot
//!   disagree about the right-hand side;
//! * `guard_at_composite` and `typing_pointwise` here — the one step between
//!   `app(drec, app(tⱼ,z))`, which is what [`super::rect`] and
//!   [`DepRecursor::typing`] give, and `app(comp(drec,tⱼ,Aⱼ), z)`, which is
//!   what the guard is stated at.
//!
//! `COD` alone no longer types the induction hypothesis: at a function-typed
//! slot it is a whole function on `Aⱼ`, so it is
//! [`crate::wrec_typing::composite_typed`] over `COD` applied pointwise.
//!
//! # A **mixed** constructor
//!
//! A constructor carrying *both* a plain recursive field and a function-typed
//! one — `γ₀ = ∅`, `γ₁ = [Bool]` — takes
//! [`RecArg::general`](crate::recarg::RecArg::general) as a **whole**, so
//! `ctorᵢ(y⃗,t⃗)`'s first argument is a function out of `1` while Lean's minor
//! premise there still takes an element of the carrier. `DEPᵢ` therefore has to
//! be stated at **both** grains at once, and it is: its recursive binder is the
//! constructor term's argument (`tⱼ ∈ fs(1,W)`, so that `app(C, ctorᵢ(y⃗,t⃗))`
//! is a statement about a real constructor term) while its induction hypothesis
//! and its applied minor are at [`Inductive::minor_subs`]'s `app(tⱼ,•)`. That
//! is [`super::motive::dep_minor`], and it has been written that way since the
//! two grains were named.
//!
//! What was missing was the *proof* side, and it was one site:
//! [`super::guard`]'s `minor_lands` holds the minor premise's grain and needs
//! `DEPᵢ`'s. It instantiates `DEPᵢ` at [`crate::point_fun::PointFun`]'s
//! `{⟨•,tⱼ⟩}` — `point_in_funspace` for the recursive atom, `point_app` for the
//! induction hypothesis and for coming back to `Sᵢ⟪y⃗,t⃗⟫v⃗`, all three at
//! `a := •`, where `fs({a},T)` **is** `fs(1,W)` because `1 = {•}` is the same
//! term. This file then needed exactly three per-slot corrections, each in a
//! place that already branched on a slot: `sub_in_carrier` (the minor
//! premise's `subⱼ ∈ W`, which at a mixed plain slot is the function-space
//! application rule at `• ∈ 1`), `fire`'s antecedent, which is at the minor
//! premise's grain and not the constructor term's, and `k_phi`, which is flat
//! wherever Lean's minor premise takes a carrier element.
//!
//! **Measured, and it is the reason there is no door here any more.** With the
//! `has_mixed_ctor` guard removed and nothing else changed,
//! [`super::rect::decl_rect`] already went through at a mixed constructor and
//! `GuardedMinors::build` was the only thing that stopped — at exactly one
//! `hyp_mp`, on exactly two of `DEPᵢ`'s four antecedent atoms, both at the
//! plain slot and both with the *subject* right and the *set* wrong.
//!
//! # Nothing here is an axiom
//!
//! One [`super::rect::decl_rect`] (one Separation) and instances of theorems
//! that already exist; the symbols are [`super::guard`]'s. Function
//! extensionality, which the function-typed path spends inside
//! [`super::rect::recarg_eta`], is [`Machine::fs_ext`]'s memo — one
//! Extensionality instance per apparatus, not one per declaration.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::wrec::hyp_eq_trans;
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, eq_symm, hyp_and, hyp_mp, inst_all, syl, uncurry,
};

use super::carrier::{ctor_atoms_at, rec_sets, Inductive};
use super::guard::GuardedMinors;
use super::machine::Machine;
use super::motive::cod_parts;
use super::rec_shared::{carry_back, gen_under, hyp_conj, hyp_inst, rewrite_under, under};
use super::recursor::GenRecursor;
use super::rect::{decl_rect, rect_parts};
use super::motive::ih_at_motive;
use super::step::applied_minor;

/// The composite's computation and typing rules, derived once per declaration
/// — the two facts a **function-typed** recursive slot's induction hypothesis
/// needs and a plain one never touches.
///
/// ```text
/// ⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d), b) = app(g, app(f,b)))          [app]
/// ⊢ ∀g ∀f ∀d ∀T. ((∀b. (b ∈ d → app(g,app(f,b)) ∈ T)) → comp(g,f,d) ∈ fs(d,T))
/// ```
struct Comp {
    app: Thm,
    typed: Thm,
}

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
        let comp = Comp {
            app: crate::wrec_typing::composite_app(env, ap, rc.comp, &rc.comp_ax)?,
            typed: crate::wrec_typing::composite_typed(env, s, rc.comp, &rc.comp_ax)?,
        };

        // ── the induction steps ─────────────────────────────────────────────
        let mut steps = Vec::with_capacity(n);
        for i in 0..n {
            steps.push(induction_step(
                env, mach, ind, gr, &guards, rc, &comp, &drec, &premise, &parts, i,
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
                env, mach, ind, gr, &guards, rc, &comp, &drec, &premise, &typing, zv, &phi, i,
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
///
/// The recursive atoms are at the **constructor term's** grain
/// ([`Inductive::ctor_slot_domains`]) — `tⱼ ∈ fs(Aⱼ, W)` at a function-typed
/// field — because `ctorᵢ(y⃗,t⃗)` is what both the induction step and the ι rule
/// conclude about, and `t⃗` are its own arguments.
///
/// **The prediction held, and it was checked by re-running the same
/// mutation.** With the mixed constructor declined this choice failed nothing;
/// the note that recorded it said it would be the first thing to become
/// observable when the door lifted, and that lifting it would be one change
/// and not two. Keying `field_atoms` off [`Inductive::rec_slot_domains`] now
/// fails `deprec.rs`'s `the_dependent_recursor_at_a_mixed_constructor`, and
/// the door lifted without this function being touched.
fn field_atoms(
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    ps: &[Term],
    ys: &[Term],
    ts: &[Term],
) -> Vec<Formula> {
    let ctor = &ind.spec.ctors[i];
    let s = &mach.wt.sums;
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    let doms = ind.ctor_slot_domains(i);
    atoms.extend((0..ts.len()).map(|j| match doms.get(j).and_then(|d| d.as_ref()) {
        None => Formula::mem(ts[j].clone(), ind.wty.clone()),
        Some(a) => Formula::mem(ts[j].clone(), s.fs.of(a.clone(), ind.wty.clone())),
    }));
    atoms
}

/// `⊢ ctx → subⱼ ∈ W` — **what the minor premise's `j`-th recursive slot
/// receives, typed**, from the constructor's own `j`-th argument typed at
/// [`Inductive::ctor_slot_domains`].
///
/// At every slot but a **mixed** constructor's plain one the two grains agree
/// and this is the field atom itself. There they do not: the field is typed
/// `tⱼ ∈ fs(1,W)` because `ctorᵢ`'s argument is a function out of `1`, while
/// [`Inductive::minor_subs`] hands the minor premise `app(tⱼ,•)`, and the step
/// between them is the function-space application rule at `• ∈ 1`.
///
/// `None` at a function-typed slot, where the minor premise receives a whole
/// function and `subⱼ ∈ W` is not a statement about it.
#[allow(clippy::too_many_arguments)]
fn sub_in_carrier(
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    j: usize,
    ctx: &Formula,
    ts: &[Term],
    k_field: &Thm,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let (cd, rd) = (ind.ctor_slot_domains(i), ind.rec_slot_domains(i));
    if rd.get(j)?.is_some() {
        return None
    }
    match cd.get(j)? {
        None => Some(k_field.clone()),
        Some(a) if *a == s.unit() => {
            let rule = inst_all(
                &mach.wt.app_mem,
                &[a.clone(), ind.wty.clone(), ts[j].clone(), s.point()],
            )?;
            hyp_mp(
                &a1i(&rule, ctx.clone()),
                &hyp_and(k_field, &under(&s.unit_mem, ctx))?,
            )
        }
        Some(_) => None,
    }
}

/// `⊢ ctx → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ ih₀ … ` — **the ι computation**,
/// at Lean's own minor.
///
/// Fires (S4) at the guarded minors, then removes the guard: its condition is
/// [`super::motive::ih_at_motive`] at each slot, which is exactly what `k_phi`
/// supplies. What the minor receives in its recursive and its
/// induction-hypothesis slots is [`Inductive::minor_subs`] and
/// [`Inductive::minor_ihs`] — the same funnel `super::iota` builds the general
/// ι rule's right-hand side from, so the two rules cannot disagree.
#[allow(clippy::too_many_arguments)]
fn fire(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    gr: &GenRecursor,
    guards: &GuardedMinors,
    rc: &Recursor,
    comp: &Comp,
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
    // Both grains, because this function holds one of each: `t⃗` are the
    // constructor's own arguments and `subs`/`vs` are the minor premise's.
    let cd = ind.ctor_slot_domains(i);
    let doms = ind.rec_slot_domains(i);
    let subs = ind.minor_subs(mach, i, ts)?;
    let vs = ind.minor_ihs(mach, rc.comp, drec, i, ts)?;
    // `subⱼ ∈ W` at every slot Lean's minor premise takes an element of the
    // carrier at, including a mixed constructor's plain one.
    let k_subs: Vec<Thm> = (0..m)
        .map(|j| match doms.get(j)? {
            None => sub_in_carrier(mach, ind, i, j, ctx, ts, &k_fields[ys.len() + j]),
            Some(_) => Some(k_fields[ys.len() + j].clone()),
        })
        .collect::<Option<_>>()?;

    // (S4), at the guarded minors and this target.
    let mut args = ps.clone();
    args.extend(guards.terms.iter().cloned());
    args.push(tt.clone());
    args.extend(ys.iter().cloned());
    args.extend(ts.iter().cloned());
    let iota_at = inst_all(&gr.iota[i], &args)?;

    let tel = &ind.telescopes[i];
    // **The ι rule's own antecedent is per constructor** — `rec_sets` at the
    // carrier, so a function-typed field is typed at `fs(Aⱼ, ind(p⃗))` — which
    // is the same grain `super::iota` built it at.
    let hctor = ctor_atoms_at(
        tel,
        &ps,
        ys,
        ts,
        &rec_sets(s, &ind.recargs[i], &ind.carrier),
    );
    let k_iota = match conj_of(&hctor) {
        None => hyp_mp(&a1i(&iota_at, ctx.clone()), k_hyp)?,
        Some(_) => {
            // The rule types the recursive fields at `ind(p⃗)`; `ctx` has `W`.
            // At a function-typed slot the rewrite goes **under** the function
            // space, not at the top of the membership.
            let ty_at = inst_all(&ind.ty_ax, &ps)?;
            let back = eq_symm(env, &ty_at)?;
            let mut atoms: Vec<Thm> = k_fields[..ys.len()].to_vec();
            for (j, t) in ts.iter().enumerate() {
                let t_c = t.clone();
                // `rec_sets` is the **constructor term's** grain, so the hole is.
                let d = cd.get(j)?.clone();
                let fs = s.fs.clone();
                atoms.push(rewrite_under(
                    env,
                    &under(&back, ctx),
                    move |q| {
                        Formula::mem(
                            t_c.clone(),
                            match &d {
                                None => q,
                                Some(a) => fs.of(a.clone(), q),
                            },
                        )
                    },
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
            // The induction hypothesis lands in the target: `app(drec,tⱼ) ∈ T`
            // from `COD` at a plain slot, and `comp(drec,tⱼ,Aⱼ) ∈ fs(Aⱼ,T)` by
            // the composite's typing rule at a function-typed one.
            let (covers, _) = cod_parts(&guards.cod)?;
            let k_covers = syl(k_cod, &and_left(covers, cod_parts(&guards.cod)?.1))?;
            let mut k_in_t = Vec::with_capacity(m);
            for j in 0..m {
                k_in_t.push(match doms.get(j)?.as_ref() {
                    None => {
                        let at = hyp_inst(&k_covers, std::slice::from_ref(&subs[j]))?;
                        let inner = hyp_mp(&at, &k_subs[j])?;
                        hyp_mp(&hyp_inst(&inner, std::slice::from_ref(&vs[j]))?, &k_phi[j])?
                    }
                    Some(a) => composite_in_funspace(
                        env,
                        mach,
                        ind,
                        comp,
                        &k_covers,
                        ctx,
                        a,
                        drec,
                        &ts[j],
                        &k_fields[ys.len() + j],
                        &k_phi[j],
                        &tt,
                    )?,
                });
            }
            // The firing rule is stated at the **minor premise's** grain, so its
            // recursive atoms are `k_subs` and not `k_fields`'s; the two differ
            // exactly at a mixed constructor's plain slot.
            let mut h_atoms: Vec<Thm> = k_fields[..ys.len()].to_vec();
            h_atoms.extend(k_subs.iter().cloned());
            h_atoms.extend(k_in_t);
            let mut insts = ys.to_vec();
            insts.extend(subs.iter().cloned());
            insts.extend(vs.iter().cloned());
            let at = hyp_inst(&under(fired, ctx), &insts)?;
            let k_eq = hyp_mp(&at, &hyp_and(&hyp_conj(&h_atoms)?, &hyp_conj(k_phi)?)?)?;
            let out = hyp_eq_trans(env, &k_iota, &k_eq)?;
            let want = Formula::eq(
                ap.apply(drec.clone(), ind.ctor_term(mach, i, ys, ts)?),
                applied_minor(
                    ap,
                    &ind.spec.ctors[i].order,
                    &Term::var(guards.minors[i]),
                    ys,
                    &subs,
                    &vs,
                ),
            );
            let _ = tc;
            if *out.concl() != Formula::imp(ctx.clone(), want) {
                return None
            }
            Some(out)
        }
    }
}

/// `⊢ ctx → comp(drec, t, A) ∈ fs(A, T)` — **the composite lands in the
/// target**, the function-typed slot's counterpart of `COD`'s one step.
///
/// `COD` alone cannot say it: its `covers` clause types *one* value of the
/// motive, and here the induction hypothesis is a whole function on `A`. The
/// composite's typing rule wants the values pointwise, and the two facts that
/// supply them are the field's typing (`app(t,z) ∈ W`, by the function-space
/// application rule) and the guard at `z` (`app(cmp,z) ∈ app(C, app(t,z))`,
/// which `COD` then carries into `T`).
#[allow(clippy::too_many_arguments)]
fn composite_in_funspace(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    comp: &Comp,
    k_covers: &Thm,
    ctx: &Formula,
    a: &Term,
    drec: &Term,
    t: &Term,
    k_t: &Thm,
    k_guard: &Thm,
    tt: &Term,
) -> Option<Thm> {
    let ap = &mach.wt.sums.ap;
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mem_z = Formula::mem(tz.clone(), a.clone());
    let kz = Formula::and(ctx.clone(), mem_z.clone());
    let k_ctx = and_left(ctx.clone(), mem_z.clone());
    let k_z = and_right(ctx.clone(), mem_z);
    let tz_val = ap.apply(t.clone(), tz.clone());

    // `app(t,z) ∈ W`.
    let k_tz = hyp_mp(
        &a1i(
            &inst_all(
                &mach.wt.app_mem,
                &[a.clone(), ind.wty.clone(), t.clone(), tz.clone()],
            )?,
            kz.clone(),
        ),
        &hyp_and(&syl(&k_ctx, k_t)?, &k_z)?,
    )?;

    // The guard at `z`, moved off the composite's spelling onto `drec`'s.
    let k_g_at = hyp_mp(&hyp_inst(&syl(&k_ctx, k_guard)?, std::slice::from_ref(&tz))?, &k_z)?;
    let motive_at = k_g_at.concl().as_imp()?.1.as_mem()?.1;
    let ca = inst_all(&comp.app, &[drec.clone(), t.clone(), a.clone(), tz.clone()])?;
    let k_ca = hyp_mp(&a1i(&ca, kz.clone()), &k_z)?;
    let k_raw = rewrite_under(
        env,
        &k_ca,
        move |q| Formula::mem(q, motive_at.clone()),
        &k_g_at,
    )?;

    // `COD` on top: the value is in the motive's fibre, so it is in `T`.
    let inner = hyp_mp(
        &hyp_inst(&syl(&k_ctx, k_covers)?, std::slice::from_ref(&tz_val))?,
        &k_tz,
    )?;
    let k_in_t = hyp_mp(
        &hyp_inst(
            &inner,
            std::slice::from_ref(&ap.apply(drec.clone(), tz_val.clone())),
        )?,
        &k_raw,
    )?;
    let pw = gen_under(zv, ctx, &uncurry(&k_in_t)?)?;
    hyp_mp(
        &a1i(
            &inst_all(&comp.typed, &[drec.clone(), t.clone(), a.clone(), tt.clone()])?,
            ctx.clone(),
        ),
        &pw,
    )
}

/// The `m` guard atoms say exactly what `DEPᵢ`'s antecedent says.
///
/// Both of `fire`'s callers assemble them from a different source — the
/// induction step from `rect_step`'s hypothesis, the ι rule from
/// [`DepRecursor::typing`] — and both then feed them to `DEPᵢ`. Checking them
/// against [`super::motive::ih_at_motive`] here is what makes that a
/// consequence rather than two coincidences.
///
/// **Measured: this check is redundant for soundness.** Replacing its body
/// with `true` fails no test, and it cannot fail one: a wrong `k_phi` makes
/// `hyp_conj` build a conjunction `DEPᵢ`'s antecedent does not match and the
/// `hyp_mp` below returns `None` anyway.
///
/// **Kept, and this is the third seat's own reason rather than the first's.**
/// The earlier one was "localisation", and that is worth less than it sounds:
/// both call sites turn `false` into a bare `return None` with no message, so
/// nothing is *reported* anywhere. What the check actually is is a
/// **specification pin**, and the only one of its kind here. `fire`'s two
/// callers build the guard atoms from two unrelated sources — the induction
/// step from `rect_step`'s hypothesis, the ι rule from [`DepRecursor::typing`]
/// — and this is the sole place either is compared against the common
/// definition in [`super::motive::ih_at_motive`]. Delete it and their agreement
/// stays true and stops being *stated*: the next widening of
/// [`Inductive::rec_slot_domains`] would change what an induction hypothesis is
/// at a function-typed slot, both assemblies would follow it, and there would
/// be nothing left to notice that one of them had not. A redundant layer that
/// pins a definition is not the same object as a redundant layer that repeats a
/// guard, and the rule that says delete the second does not reach the first.
fn guard_atoms_match(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    guards: &GuardedMinors,
    i: usize,
    ctx: &Formula,
    subs: &[Term],
    vs: &[Term],
    k_phi: &[Thm],
) -> bool {
    let s = &mach.wt.sums;
    let tc = Term::var(guards.motive);
    let doms = ind.rec_slot_domains(i);
    doms.len() == k_phi.len()
        && (0..k_phi.len()).all(|j| {
            let want = ih_at_motive(env, s, &tc, &subs[j], &vs[j], doms[j].as_ref());
            *k_phi[j].concl() == Formula::imp(ctx.clone(), want)
        })
}

/// `⊢ ctx → ∀z. (z ∈ Aⱼ → app(drec, app(tⱼ,z)) ∈ app(C, app(tⱼ,z)))` — the
/// obligation read **pointwise** off [`DepRecursor::typing`].
///
/// The ι rule's induction hypotheses come from the typing theorem rather than
/// from an assumption, and at a function-typed slot the theorem has to be fired
/// once per point of the field's own domain, at `app(tⱼ,z) ∈ W`.
#[allow(clippy::too_many_arguments)]
fn typing_pointwise(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    ctx: &Formula,
    a: &Term,
    k_typing: &Thm,
    t: &Term,
    k_t: &Thm,
) -> Option<Thm> {
    let ap = &mach.wt.sums.ap;
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mem_z = Formula::mem(tz.clone(), a.clone());
    let kz = Formula::and(ctx.clone(), mem_z.clone());
    let k_ctx = and_left(ctx.clone(), mem_z.clone());
    let k_z = and_right(ctx.clone(), mem_z);

    let k_tz = hyp_mp(
        &a1i(
            &inst_all(
                &mach.wt.app_mem,
                &[a.clone(), ind.wty.clone(), t.clone(), tz.clone()],
            )?,
            kz.clone(),
        ),
        &hyp_and(&syl(&k_ctx, k_t)?, &k_z)?,
    )?;
    let at = hyp_inst(
        &syl(&k_ctx, k_typing)?,
        std::slice::from_ref(&ap.apply(t.clone(), tz)),
    )?;
    gen_under(zv, ctx, &uncurry(&hyp_mp(&at, &k_tz)?)?)
}

/// `⊢ ctx → ∀z. (z ∈ Aⱼ → app(comp(drec,tⱼ,Aⱼ), z) ∈ app(C, app(tⱼ,z)))` — the
/// guard atom at a **function-typed** slot, from the same statement about
/// `app(drec, app(tⱼ,z))`.
///
/// The two sides differ by the composite's computation rule alone, and this is
/// the one place that step is taken: both of `fire`'s callers hold the raw form
/// (the induction step off `rect_step`'s hypothesis, the ι rule off
/// [`DepRecursor::typing`]) and the guard is stated at the composite, because
/// that is what the minor premise's slot actually receives.
#[allow(clippy::too_many_arguments)]
fn guard_at_composite(
    env: &mut Env,
    _mach: &Machine,
    comp: &Comp,
    ctx: &Formula,
    a: &Term,
    drec: &Term,
    t: &Term,
    k_raw: &Thm,
) -> Option<Thm> {
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mem_z = Formula::mem(tz.clone(), a.clone());
    let kz = Formula::and(ctx.clone(), mem_z.clone());
    let k_ctx = and_left(ctx.clone(), mem_z.clone());
    let k_z = and_right(ctx.clone(), mem_z);

    let at = hyp_mp(&hyp_inst(&syl(&k_ctx, k_raw)?, std::slice::from_ref(&tz))?, &k_z)?;
    let motive_at = at.concl().as_imp()?.1.as_mem()?.1;
    let ca = inst_all(&comp.app, &[drec.clone(), t.clone(), a.clone(), tz.clone()])?;
    let back = crate::wrec::hyp_eq_symm(env, &hyp_mp(&a1i(&ca, kz.clone()), &k_z)?)?;
    let moved = rewrite_under(env, &back, move |q| Formula::mem(q, motive_at.clone()), &at)?;
    gen_under(zv, ctx, &uncurry(&moved)?)
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
    rc: &Recursor,
    comp: &Comp,
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
    let doms = ind.ctor_slot_domains(i);
    if doms.len() != m {
        return None
    }

    // `rect_stepᵢ`'s own induction hypotheses — `φ(tⱼ)` at a plain slot and the
    // pointwise family `∀z ∈ Aⱼ. φ(app(tⱼ,z))` at a function-typed one. This
    // is `super::rect`'s spelling and not the guard's, and the two are bridged
    // by `guard_at_composite` below.
    let phi_z = |env: &mut Env, j: usize| -> Formula {
        match &doms[j] {
            None => Formula::mem(
                ap.apply(drec.clone(), ts[j].clone()),
                ap.apply(tc.clone(), ts[j].clone()),
            ),
            Some(a) => {
                let zz = env.fresh_var();
                let tzz = Term::var(zz);
                let val = ap.apply(ts[j].clone(), tzz.clone());
                Formula::forall(
                    zz,
                    Formula::imp(
                        Formula::mem(tzz, a.clone()),
                        Formula::mem(
                            ap.apply(drec.clone(), val.clone()),
                            ap.apply(tc.clone(), val),
                        ),
                    ),
                )
            }
        }
    };
    let mut atoms = field_atoms(mach, ind, i, &ps, &ys, &ts);
    for j in 0..m {
        let f = phi_z(env, j);
        atoms.push(f);
    }
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

    // The guard atoms, at the composite spelling the minor premise's slot has.
    let vs = ind.minor_ihs(mach, rc.comp, drec, i, &ts)?;
    let rd = ind.rec_slot_domains(i);
    let mut k_phi = Vec::with_capacity(m);
    for j in 0..m {
        k_phi.push(match (&doms[j], rd.get(j)?) {
            (_, Some(a)) => guard_at_composite(
                env,
                mach,
                comp,
                &ctx,
                a,
                drec,
                &ts[j],
                &k_atom[k + m + j],
            )?,
            (None, None) => k_atom[k + m + j].clone(),
            // A **mixed** constructor's plain slot: `rect_step` states the
            // hypothesis pointwise over the constructor's `1`, and the guard
            // wants the one point of it.
            (Some(_), None) => hyp_mp(
                &hyp_inst(&k_atom[k + m + j], std::slice::from_ref(&s.point()))?,
                &under(&s.unit_mem, &ctx),
            )?,
        });
    }

    let subs = ind.minor_subs(mach, i, &ts)?;
    if !guard_atoms_match(env, mach, ind, guards, i, &ctx, &subs, &vs, &k_phi) {
        return None
    }

    let k_eq = fire(
        env, mach, ind, gr, guards, rc, comp, drec, &ctx, &k_cod, &k_hyp, k_fields, &k_phi,
        &ys, &ts, i,
    )?;

    // `DEPᵢ` at the fields and the recursive calls.
    let k_dep_i = syl(&k_dep, &conj_proj(&guards.dep_parts, i)?)?;
    let mut insts = ys.clone();
    insts.extend(ts.iter().cloned());
    insts.extend(vs.iter().cloned());
    let at = hyp_inst(&k_dep_i, &insts)?;
    let mut dep_atoms: Vec<Thm> = k_fields.to_vec();
    dep_atoms.extend(k_phi.iter().cloned());
    let k_val = match hyp_conj(&dep_atoms) {
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
    rc: &Recursor,
    comp: &Comp,
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

    let atoms = field_atoms(mach, ind, i, &ps, &ys, &ts);
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

    // The induction hypotheses, off the typing theorem. At a function-typed
    // slot the typing theorem is read **pointwise** — once per point of the
    // field's own domain — and then moved onto the composite's spelling.
    let k_typing = syl(&k_prem, typing)?;
    let doms = ind.ctor_slot_domains(i);
    if doms.len() != m {
        return None
    }
    let rd = ind.rec_slot_domains(i);
    let subs = ind.minor_subs(mach, i, &ts)?;
    let mut k_phi = Vec::with_capacity(m);
    for j in 0..m {
        k_phi.push(match rd.get(j)? {
            // The guard atom is flat at whatever the minor premise receives —
            // `tⱼ` at a plain constructor, `app(tⱼ,•)` at a mixed one's plain
            // slot — and the typing theorem is fired there.
            None => {
                let k_sub = sub_in_carrier(mach, ind, i, j, &ctx, &ts, &k_atom[k + j])?;
                let at = hyp_inst(&k_typing, std::slice::from_ref(&subs[j]))?;
                hyp_mp(&at, &k_sub)?
            }
            Some(a) => {
                let raw = typing_pointwise(
                    env, mach, ind, &ctx, a, &k_typing, &ts[j], &k_atom[k + j],
                )?;
                guard_at_composite(env, mach, comp, &ctx, a, drec, &ts[j], &raw)?
            }
        });
    }
    let vs = ind.minor_ihs(mach, rc.comp, drec, i, &ts)?;
    if !guard_atoms_match(env, mach, ind, guards, i, &ctx, &subs, &vs, &k_phi) {
        return None
    }
    let _ = (zv, phi);

    let body = fire(
        env, mach, ind, gr, guards, rc, comp, drec, &ctx, &k_cod, &k_hyp, &k_atom, &k_phi,
        &ys, &ts, i,
    )?;
    let out = if atoms.is_empty() { body } else { uncurry(&body)? };
    let quantified = yvs
        .iter()
        .chain(tvs.iter())
        .rev()
        .try_fold(out, |acc, v| gen_under(*v, premise, &acc))?;

    let want = dep_iota_stmt(env, mach, ind, guards, rc.comp, drec, i)?;
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
    comp: kernel::FnSym,
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
    let subs = ind.minor_subs(mach, i, &ts)?;
    let vs = ind.minor_ihs(mach, comp, drec, i, &ts)?;

    let atoms = field_atoms(mach, ind, i, &ps, &ys, &ts);
    let concl = Formula::eq(
        ap.apply(drec.clone(), ind.ctor_term(mach, i, &ys, &ts)?),
        applied_minor(
            ap,
            &ind.spec.ctors[i].order,
            &Term::var(guards.minors[i]),
            &ys,
            &subs,
            &vs,
        ),
    );
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    Some(quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc)))
}
