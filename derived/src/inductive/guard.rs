//! **The guarded minor premises** — what makes [`super::recursor`]'s `HYP`
//! dischargeable at a *variable* motive.
//!
//! # The obstruction, and the way round it
//!
//! [`super::premise`]'s bundle asks, per constructor,
//!
//! ```text
//! ∀y⃗ ∀t⃗ ∀v⃗. (( ⋀ yⱼ ∈ βⱼ ∧ ⋀ tⱼ ∈ W ∧ ⋀ vⱼ ∈ T ) → sᵢ⟪y⃗,t⃗⟫v⃗ ∈ T)
//! ```
//!
//! and Lean's dependent minor gives `Sᵢ⟪y⃗,t⃗⟫v⃗ ∈ app(C, ctorᵢ(y⃗,t⃗))` only when
//! each `vⱼ ∈ app(C, tⱼ)`. With `T := ⋃img(C)`-shaped targets the hypothesis
//! `vⱼ ∈ T` is **too weak** to supply that — the recorded reason a single `T`
//! was thought not to exist (`RECURSOR-DESIGN.md` §5.1, last bullet).
//!
//! The reading that is wrong is "`sᵢ` must be `Sᵢ`". `HYP` quantifies `sᵢ`, and
//! [`super::recursor`]'s schemas are `∀s⃗`, so `sᵢ` may be **any** term — in
//! particular one that *tests* the hypothesis it was handed. Note that
//! `minor_typedᵢ` gives the minor both `t⃗` and `v⃗`, so the test is expressible:
//!
//! ```text
//! guardᵢ := ⋀ⱼ vⱼ ∈ app(C, tⱼ)
//! gminᵢ  := λy⃗ t⃗ v⃗. ⋃ { x ∈ {Sᵢ⟪y⃗,t⃗⟫v⃗} : guardᵢ }
//! ```
//!
//! — Lean's minor when the induction hypotheses really are values of the
//! motive, and `∅` when they are junk. `HYP` then holds for *arbitrary*
//! `vⱼ ∈ T`: in the first case by Lean's minor and `app(C, ctorᵢ) ⊆ T`, in the
//! second because `⋃∅ = ∅ ∈ T`. Both halves of [`super::motive::cod`] are used
//! exactly once, and nothing about `T` beyond them is ever needed.
//!
//! The guard is *not* what makes the recursor land in the motive — that is
//! [`super::rect`]'s induction, which never sees it. The guard exists only so
//! that (S3) and (S4) can be **instantiated**; the induction then shows the
//! guard fires at every real recursive call, so [`super::dep`]'s ι rule is
//! stated at `Sᵢ`, not at `gminᵢ`.
//!
//! # Interface
//!
//! ```text
//! GuardedMinors::build(env, mach, ind, motive, minors, target)
//!
//! gminᵢ                                                 [GuardedMinors::terms]
//! ⊢ (COD ∧ DEP) → minor_typedᵢ(gminᵢ, T)                [GuardedMinors::typed]
//! ⊢ (COD ∧ DEP) → HYP(gmin⃗, T)                          [GuardedMinors::hyp]
//! ⊢ ⋃∅ = ∅                                              [union_empty]
//! ```
//!
//! with `COD`/`DEP` from [`super::motive`] and `minor_typedᵢ`/`HYP` from
//! [`super::premise`], all rebuilt at the caller's own `C`, `S⃗` and `T`
//! variables so the results compose with [`super::recursor`]'s `∀p⃗ ∀s⃗ ∀T`.
//!
//! # A constructor with no recursive arguments needs no guard
//!
//! There is nothing to test — `minor_typedᵢ` is then `∀y⃗. (⋯ → Sᵢ⟪y⃗⟫ ∈ T)`,
//! and Lean's minor plus `app(C, ctorᵢ(y⃗)) ⊆ T` gives it outright. So
//! `gminᵢ := Sᵢ`, with no lambda graph and no Separation, and every all-nullary
//! declaration (every enumeration, `Bool` included) costs this file nothing at
//! all. The `m ≥ 1` branch is `k + 2m` lambda graphs and one Separation.
//!
//! # Nothing here is an axiom
//!
//! Per guarded constructor: one Separation, `k + 2m` Replacements (the lambda
//! graphs) and `2(k + 2m)` [`crate::define_abbrev`]s, plus one Extensionality
//! per case of the guard. No new axiom, and `RECURSOR-DESIGN.md` §5.3's `Σ`
//! target is not needed: the dependent sum was only ever a way of carrying the
//! recursive argument alongside its value so the two could be compared, and the
//! minor already has both.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{beta_conditional_n, cases, hyp_syl, lambda_n, separation_full};
use crate::wrec::{hyp_congr, hyp_eq_trans};
use crate::{
    a1i, and_left, and_right, com12, conj_of, conj_proj, define_abbrev, define_by_membership,
    ex_falso, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, notnot_intro,
    singleton, syl, uncurry,
};

use super::carrier::Inductive;
use super::machine::Machine;
use super::motive::{cod, cod_parts, dep_parts};
use super::premise::minor_typed;
use super::rec_shared::{carry_back, gen_under, hyp_conj, hyp_inst, rewrite_under, under};
use super::spec::Slot;
use super::step::applied_minor;

/// `⊢ ⋃∅ = ∅`.
///
/// A general fact with exactly one consumer: the guarded minor's fallback
/// value, when the Separation carves nothing out. One Extensionality, both
/// sides refuted from `⊢ ∀z. ¬(z ∈ ∅)`.
pub fn union_empty(env: &mut Env, ap: &crate::funcs::Apply) -> Option<Thm> {
    let zero = Term::apply(ap.empty, vec![]);
    let un = ap.sets.union_of(zero.clone());
    let (zv, yv) = (env.fresh_var(), env.fresh_var());
    let (tz, ty) = (Term::var(zv), Term::var(yv));

    // `¬(z ∈ ⋃∅)`: unfold the union, then refute the witness.
    let members = inst_all(&ap.sets.un_ax, &[zero.clone(), tz.clone()])?;
    let body = Formula::and(
        Formula::mem(ty.clone(), zero.clone()),
        Formula::mem(tz.clone(), ty.clone()),
    );
    let no_wit = syl(
        &and_left(Formula::mem(ty.clone(), zero.clone()), Formula::mem(tz.clone(), ty)),
        &inst_all(&ap.empty_ax, std::slice::from_ref(&Term::var(yv)))?,
    )?;
    let all_not = Thm::gen(yv, &no_wit);
    let not_ex = Thm::mp(&notnot_intro(all_not.concl().clone()), &all_not)?;
    if *not_ex.concl() != Formula::not(Formula::exists(yv, body)) {
        return None
    }
    let not_un = syl(&iff_mp(&members)?, &not_ex)?;
    let not_zero = inst_all(&ap.empty_ax, std::slice::from_ref(&tz))?;

    // Two refuted memberships make an `↔`.
    let (l, r) = (Formula::mem(tz.clone(), un.clone()), Formula::mem(tz, zero.clone()));
    let same = crate::and_intro(
        &syl(&not_un, &ex_falso(r.clone()))?,
        &syl(&not_zero, &ex_falso(l.clone()))?,
    );
    if *same.concl() != Formula::iff(l, r) {
        return None
    }
    let ext = inst_all(&Thm::ax_extensionality(env), &[un.clone(), zero.clone()])?;
    Thm::mp(&ext, &Thm::gen(zv, &same))
}

/// The guarded minors of one declaration, with the discharge of `HYP`.
pub struct GuardedMinors {
    /// The motive variable `C`.
    pub motive: FreeVar,
    /// Lean's dependent minor-premise variables `S₀ … S_{n-1}`.
    pub minors: Vec<FreeVar>,
    /// The target variable `T`.
    pub target: FreeVar,
    /// `gminᵢ`, in constructor order — `Sᵢ` itself where `mᵢ = 0`.
    pub terms: Vec<Term>,
    /// `COD(C,T)`, at those variables.
    pub cod: Formula,
    /// The `DEPᵢ(C,Sᵢ)` conjuncts, and their conjunction.
    pub dep_parts: Vec<Formula>,
    /// `DEP(C,S⃗)`.
    pub dep: Formula,
    /// The `minor_typedᵢ(gminᵢ, T)` conjuncts.
    pub minor_typed: Vec<Formula>,
    /// `⊢ (COD ∧ DEP) → minor_typedᵢ(gminᵢ, T)`, per constructor.
    pub typed: Vec<Thm>,
    /// `⊢ (COD ∧ DEP) → HYP(gmin⃗, T)`.
    pub hyp: Thm,
    /// **The guard fires**, per constructor:
    ///
    /// ```text
    /// ⊢ ∀y⃗ ∀t⃗ ∀v⃗. (( ⋀ⱼ yⱼ ∈ βⱼ ∧ ⋀ⱼ tⱼ ∈ W ∧ ⋀ⱼ vⱼ ∈ T
    ///                  ∧ ⋀ⱼ vⱼ ∈ app(C,tⱼ) )
    ///                → gminᵢ⟪y⃗,t⃗⟫v⃗ = Sᵢ⟪y⃗,t⃗⟫v⃗)
    /// ```
    ///
    /// — the antecedent is `minor_typedᵢ`'s, conjoined with the guard. `None`
    /// exactly where `mᵢ = 0` and `gminᵢ` **is** `Sᵢ`, so there is nothing to
    /// rewrite. This is what lets [`super::dep`]'s ι rule be stated at Lean's
    /// own minor rather than at the guarded one.
    pub fires: Vec<Option<Thm>>,
}

impl GuardedMinors {
    /// Build the guarded minors and discharge `HYP` at them.
    ///
    /// `motive`, `minors` and `target` are the caller's own variables, so that
    /// the formulas here and the ones [`super::recursor`]'s schemas are
    /// instantiated to are literally the same. `None` for a declaration with no
    /// constructors, if `minors` has the wrong length, or if any internal shape
    /// check fails.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        motive: FreeVar,
        minors: &[FreeVar],
        target: FreeVar,
    ) -> Option<GuardedMinors> {
        let n = ind.spec.ctors.len();
        if n == 0 || minors.len() != n || !ind.is_over(mach) {
            return None
        }
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let (tc, tt) = (Term::var(motive), Term::var(target));
        let su: Vec<Term> = minors.iter().map(|v| Term::var(*v)).collect();

        let cod_f = cod(env, s, &ind.wty, &tc, &tt);
        let dep_parts_f = dep_parts(env, mach, ind, &tc, &su)?;
        let dep_f = conj_of(&dep_parts_f)?;
        let g = Formula::and(cod_f.clone(), dep_f.clone());
        let un_empty = union_empty(env, ap)?;

        let mut terms = Vec::with_capacity(n);
        let mut typed = Vec::with_capacity(n);
        let mut fires = Vec::with_capacity(n);
        for i in 0..n {
            let (term, th, fired) = if ind.spec.ctors[i].recs == 0 {
                let th =
                    unguarded(env, mach, ind, i, &g, &cod_f, &dep_f, &dep_parts_f, &su[i], &tt)?;
                (su[i].clone(), th, None)
            } else {
                let (t, th, f) = guarded(
                    env, mach, ind, i, &g, &cod_f, &dep_f, &dep_parts_f, motive, minors[i],
                    target, &un_empty,
                )?;
                (t, th, Some(f))
            };
            terms.push(term);
            typed.push(th);
            fires.push(fired);
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
        // Every field of this struct is documented `⊢ …`, and `Thm::gen` cannot
        // discharge a sequent hypothesis — the firing rules go out the same
        // door as the rest.
        if !crate::all_unconditional(&fires.iter().flatten().collect::<Vec<_>>()) {
            return None
        }

        Some(GuardedMinors {
            motive,
            minors: minors.to_vec(),
            target,
            terms,
            cod: cod_f,
            dep_parts: dep_parts_f,
            dep: dep_f,
            minor_typed: mt,
            typed,
            hyp,
            fires,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The shared core: Lean's minor lands in the target
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ K → Sᵢ⟪y⃗,t⃗⟫v⃗ ∈ T`, given under `K`: the ambient `COD ∧ DEP`, the field
/// typings, the carrier memberships, and the induction hypotheses **at the
/// motive** (`vⱼ ∈ app(C,tⱼ)`).
///
/// The one place `DEP` and `COD` are consumed. Used twice: unguarded when the
/// constructor has no recursive arguments, and inside the guard's positive case
/// when it has.
#[allow(clippy::too_many_arguments)]
fn minor_lands(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    ctx: &Formula,
    cod_f: &Formula,
    dep_f: &Formula,
    dep_parts_f: &[Formula],
    k_g: &Thm,
    ys: &[Term],
    ts: &[Term],
    vs: &[Term],
    k_atoms: &[Thm],
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let _ = &s.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let ctor_t = ind.ctor_term(mach, i, ys, ts)?;

    // `DEPᵢ` at the fields.
    let k_cod = syl(k_g, &and_left(cod_f.clone(), dep_f.clone()))?;
    let k_dep = syl(k_g, &and_right(cod_f.clone(), dep_f.clone()))?;
    let k_dep_i = syl(&k_dep, &conj_proj(dep_parts_f, i)?)?;
    let mut insts = ys.to_vec();
    insts.extend(ts.iter().cloned());
    insts.extend(vs.iter().cloned());
    let at = hyp_inst(&k_dep_i, &insts)?;
    let k_val = match hyp_conj(k_atoms) {
        Some(prem) => hyp_mp(&at, &prem)?,
        None => at,
    };

    // `ctorᵢ(y⃗,t⃗) ∈ W`, through the carrier's abbreviation.
    let ty_at = inst_all(&ind.ty_ax, &ps)?;
    let (ind_t, w_t) = ty_at.concl().as_eq()?;
    let mut ctor_args = ps.clone();
    ctor_args.extend(ys.iter().cloned());
    ctor_args.extend(ts.iter().cloned());
    let mem_rule = inst_all(&ind.ctors[i].mem, &ctor_args)?;
    let k_mem = match &ind.ctors[i].hyp {
        None => under(&mem_rule, ctx),
        Some(_) => {
            // The recursive atoms arrive as `tⱼ ∈ W`; the rule wants `tⱼ ∈ ind(p⃗)`.
            let back = crate::eq_symm(env, &ty_at)?;
            let mut atoms: Vec<Thm> = k_atoms[..ys.len()].to_vec();
            for (j, t) in ts.iter().enumerate() {
                let t_c = t.clone();
                atoms.push(carry_back_mem(env, &back, &k_atoms[ys.len() + j], t_c, ctx)?);
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
    let _ = (ind_t, w_t);

    // `COD` carries it into the target.
    let (covers, empty_in) = cod_parts(cod_f)?;
    let k_covers = syl(&k_cod, &and_left(covers, empty_in))?;
    let k_at_ctor = hyp_inst(&k_covers, std::slice::from_ref(&ctor_t))?;
    let k_inner = hyp_mp(&k_at_ctor, &k_w)?;
    let val = k_val.concl().as_imp()?.1.as_mem()?.0;
    let k_out = hyp_mp(&hyp_inst(&k_inner, std::slice::from_ref(&val))?, &k_val)?;
    Some(k_out)
}

/// From `⊢ ctx → ind(p⃗) = W` reversed and `⊢ ctx → t ∈ W`, infer
/// `⊢ ctx → t ∈ ind(p⃗)`.
fn carry_back_mem(
    env: &mut Env,
    back: &Thm,
    k_mem: &Thm,
    t: Term,
    ctx: &Formula,
) -> Option<Thm> {
    rewrite_under(env, &under(back, ctx), move |q| Formula::mem(t.clone(), q), k_mem)
}

// ─────────────────────────────────────────────────────────────────────────────
// No recursive arguments: no guard
// ─────────────────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn unguarded(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    g: &Formula,
    cod_f: &Formula,
    dep_f: &Formula,
    dep_parts_f: &[Formula],
    su: &Term,
    tt: &Term,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ctor = &ind.spec.ctors[i];
    let k = ctor.args.len();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    let ctx = match conj_of(&atoms) {
        Some(h) => Formula::and(g.clone(), h),
        None => g.clone(),
    };
    let k_g = match conj_of(&atoms) {
        Some(h) => and_left(g.clone(), h),
        None => imp_refl(g.clone()),
    };
    let k_atoms: Vec<Thm> = match conj_of(&atoms) {
        Some(h) => {
            let rest = and_right(g.clone(), h);
            (0..k).map(|j| syl(&rest, &conj_proj(&atoms, j)?)).collect::<Option<_>>()?
        }
        None => Vec::new(),
    };

    let body = minor_lands(
        env, mach, ind, i, &ctx, cod_f, dep_f, dep_parts_f, &k_g, &ys, &[], &[], &k_atoms,
    )?;
    let out = if atoms.is_empty() { body } else { uncurry(&body)? };
    let quantified = yvs.iter().rev().try_fold(out, |acc, v| gen_under(*v, g, &acc))?;
    let want = minor_typed(env, s, ctor, &ps, &ind.wty, su, tt);
    if !crate::establishes(&quantified, &Formula::imp(g.clone(), want)) {
        return None
    }
    Some(quantified)
}

// ─────────────────────────────────────────────────────────────────────────────
// Recursive arguments: the guard
// ─────────────────────────────────────────────────────────────────────────────

/// The `k + 2m` binders of a guarded minor, in **application order**: the
/// declared mask over `(y⃗, t⃗)`, then the induction hypotheses.
struct Binders {
    vars: Vec<FreeVar>,
    /// Which atom of `minor_typedᵢ`'s antecedent types each binder.
    atom: Vec<usize>,
    doms: Vec<Term>,
}

#[allow(clippy::too_many_arguments)]
fn guarded(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    g: &Formula,
    cod_f: &Formula,
    dep_f: &Formula,
    dep_parts_f: &[Formula],
    motive: FreeVar,
    minor: FreeVar,
    target: FreeVar,
    un_empty: &Thm,
) -> Option<(Term, Thm, Thm)> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ctor = &ind.spec.ctors[i];
    let (k, m) = (ctor.args.len(), ctor.recs);
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let (tc, su, tt) = (Term::var(motive), Term::var(minor), Term::var(target));

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    // `minor_typedᵢ`'s antecedent, atom by atom.
    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    atoms.extend(vs.iter().map(|v| Formula::mem(v.clone(), tt.clone())));
    let h = conj_of(&atoms)?;

    // The binders, in application order.
    let mut bd = Binders { vars: Vec::new(), atom: Vec::new(), doms: Vec::new() };
    let (mut pi, mut ri) = (0usize, 0usize);
    for sl in &ctor.order {
        match sl {
            Slot::Plain => {
                let mut a = ps.clone();
                a.extend(ys[..pi].iter().cloned());
                bd.vars.push(yvs[pi]);
                bd.atom.push(pi);
                bd.doms.push(Term::apply(ctor.args[pi], a));
                pi += 1;
            }
            Slot::Rec => {
                bd.vars.push(tvs[ri]);
                bd.atom.push(k + ri);
                bd.doms.push(ind.wty.clone());
                ri += 1;
            }
        }
    }
    for (j, vj) in vvs.iter().enumerate() {
        bd.vars.push(*vj);
        bd.atom.push(k + m + j);
        bd.doms.push(tt.clone());
    }
    let l = bd.vars.len();

    // ── the guard, as a Separation ──────────────────────────────────────────
    let val = applied_minor(ap, &ctor.order, &su, &ys, &ts, &vs);
    let sing = singleton(ap.sets.up, val.clone());
    let psi = conj_of(
        &(0..m)
            .map(|j| Formula::mem(vs[j].clone(), ap.apply(tc.clone(), ts[j].clone())))
            .collect::<Vec<_>>(),
    )?;
    let xv = env.fresh_var();
    let existence = separation_full(env, xv, &psi, &sing, &ap.empty_ax)?;
    let carved = Formula::and(Formula::mem(Term::var(xv), sing.clone()), psi.clone());
    let mut sep_params = vec![motive, minor];
    sep_params.extend(yvs.iter().copied());
    sep_params.extend(tvs.iter().copied());
    sep_params.extend(vvs.iter().copied());
    let (sep_sym, sep_ax) = define_by_membership(env, &sep_params, &existence, xv, &carved)?;
    let sep_args: Vec<Term> = sep_params.iter().map(|v| Term::var(*v)).collect();
    let sep_t = Term::apply(sep_sym, sep_args.clone());
    let guarded_val = ap.sets.union_of(sep_t.clone());

    // ── the lambda nest, innermost first ────────────────────────────────────
    let mut prefix: Vec<FreeVar> = ind.params.clone();
    prefix.extend([motive, minor, target]);
    let prefix_t: Vec<Term> = prefix.iter().map(|v| Term::var(*v)).collect();

    let mut syms: Vec<(FnSym, Thm)> = Vec::new();
    let mut lams: Vec<(FnSym, Thm)> = Vec::new();
    let mut body = guarded_val.clone();
    for level in (0..l).rev() {
        let mut xs: Vec<FreeVar> = prefix.clone();
        xs.extend(bd.vars[..=level].iter().copied());
        let (sym, sym_ax) = define_abbrev(env, &xs, &body)?;
        let (lam, lam_ax) = lambda_n(env, ap, sym)?;
        let beta = beta_conditional_n(env, ap, sym, lam, &lam_ax)?;
        syms.push((sym, sym_ax));
        lams.push((lam, beta));
        if level > 0 {
            let mut args = prefix_t.clone();
            args.extend(bd.vars[..level].iter().map(|v| Term::var(*v)));
            args.push(bd.doms[level].clone());
            body = Term::apply(lam, args);
        }
    }
    syms.reverse();
    lams.reverse();

    let gmin = {
        let mut args = prefix_t.clone();
        args.push(bd.doms[0].clone());
        Term::apply(lams[0].0, args)
    };

    // ── the beta chain, under `minor_typedᵢ`'s own antecedent ───────────────
    let mut chain = under(&Thm::eq_refl(gmin.clone()), &h);
    for level in 0..l {
        let x = Term::var(bd.vars[level]);
        let x_c = x.clone();
        let stepped = hyp_congr(env, &chain, move |q| ap.apply(q, x_c.clone()))?;
        let mut beta_args = prefix_t.clone();
        beta_args.extend(bd.vars[..level].iter().map(|v| Term::var(*v)));
        beta_args.push(bd.doms[level].clone());
        beta_args.push(x.clone());
        let beta_at = inst_all(&lams[level].1, &beta_args)?;
        let k_beta = hyp_mp(&a1i(&beta_at, h.clone()), &conj_proj(&atoms, bd.atom[level])?)?;
        let mut sym_args = prefix_t.clone();
        sym_args.extend(bd.vars[..=level].iter().map(|v| Term::var(*v)));
        let k_unfold = under(&inst_all(&syms[level].1, &sym_args)?, &h);
        let half = hyp_eq_trans(env, &stepped, &k_beta)?;
        chain = hyp_eq_trans(env, &half, &k_unfold)?;
    }
    let applied = applied_minor(ap, &ctor.order, &gmin, &ys, &ts, &vs);
    if *chain.concl() != Formula::imp(h.clone(), Formula::eq(applied.clone(), guarded_val.clone()))
    {
        return None
    }

    // ── the guard fires: `gminᵢ⟪y⃗,t⃗⟫v⃗ = Sᵢ⟪y⃗,t⃗⟫v⃗` whenever it holds ────────
    let sep_iff = {
        let mut a = sep_args.clone();
        a.push(Term::var(xv));
        inst_all(&sep_ax, &a)?
    };
    let hp = Formula::and(h.clone(), psi.clone());
    let mem_sep = Formula::mem(Term::var(xv), sep_t.clone());
    let mem_sing = Formula::mem(Term::var(xv), sing.clone());
    let fires = {
        let p_psi = and_right(h.clone(), psi.clone());
        let fwd = hyp_syl(
            &under(&iff_mp(&sep_iff)?, &hp),
            &under(&and_left(mem_sing.clone(), psi.clone()), &hp),
        )?;
        let bwd = {
            let pair = com12(&crate::and_intro_imp(mem_sing.clone(), psi.clone()))?;
            let with_psi = hyp_mp(&under(&pair, &hp), &p_psi)?;
            hyp_syl(&with_psi, &under(&iff_mpr(&sep_iff)?, &hp))?
        };
        let same = hyp_and(&fwd, &bwd)?;
        if *same.concl()
            != Formula::imp(hp.clone(), Formula::iff(mem_sep.clone(), mem_sing.clone()))
        {
            return None
        }
        let ext = inst_all(&Thm::ax_extensionality(env), &[sep_t.clone(), sing.clone()])?;
        let eq_sets = hyp_mp(&under(&ext, &hp), &gen_under(xv, &hp, &same)?)?;
        let eq_un = hyp_congr(env, &eq_sets, move |q| ap.sets.union_of(q))?;
        let collapse = under(&inst_all(&ap.union_sing, std::slice::from_ref(&val))?, &hp);
        let eq_val = hyp_eq_trans(env, &eq_un, &collapse)?;
        let lifted = syl(&and_left(h.clone(), psi.clone()), &chain)?;
        hyp_eq_trans(env, &lifted, &eq_val)?
    };
    if *fires.concl() != Formula::imp(hp.clone(), Formula::eq(applied.clone(), val.clone())) {
        return None
    }

    // ── the value lands in the target, guard or no guard ────────────────────
    let ctx = Formula::and(g.clone(), h.clone());
    let k_g = and_left(g.clone(), h.clone());
    let k_h = and_right(g.clone(), h.clone());
    let goal = Formula::mem(applied.clone(), tt.clone());

    // The guard holds: Lean's minor, then `COD`.
    let pos_ctx = Formula::and(ctx.clone(), psi.clone());
    let pos = {
        let p_ctx = and_left(ctx.clone(), psi.clone());
        let p_psi = and_right(ctx.clone(), psi.clone());
        let p_h = syl(&p_ctx, &k_h)?;
        let pos_eq = syl(&hyp_and(&p_h, &p_psi)?, &fires)?;
        let mut k_atoms: Vec<Thm> = Vec::with_capacity(k + 2 * m);
        for j in 0..(k + m) {
            k_atoms.push(syl(&p_h, &conj_proj(&atoms, j)?)?);
        }
        let ihs: Vec<Formula> = (0..m)
            .map(|j| Formula::mem(vs[j].clone(), ap.apply(tc.clone(), ts[j].clone())))
            .collect();
        for (j, _) in ihs.iter().enumerate() {
            k_atoms.push(syl(&p_psi, &conj_proj(&ihs, j)?)?);
        }
        let lands = minor_lands(
            env, mach, ind, i, &pos_ctx, cod_f, dep_f, dep_parts_f, &syl(&p_ctx, &k_g)?, &ys,
            &ts, &vs, &k_atoms,
        )?;
        carry_back(env, &pos_eq, &lands, &tt)?
    };

    // The guard fails: nothing is carved out, and `⋃∅ = ∅ ∈ T`.
    let neg_ctx = Formula::and(ctx.clone(), Formula::not(psi.clone()));
    let neg = {
        let n_ctx = and_left(ctx.clone(), Formula::not(psi.clone()));
        let n_psi = and_right(ctx.clone(), Formula::not(psi.clone()));
        let zero = Term::apply(ap.empty, vec![]);
        let refute = hyp_syl(
            &under(&iff_mp(&sep_iff)?, &neg_ctx),
            &hyp_syl(&under(&and_right(mem_sing, psi.clone()), &neg_ctx), &n_psi)?,
        )?;
        let empty_side = under(
            &inst_all(&ap.empty_ax, std::slice::from_ref(&Term::var(xv)))?,
            &neg_ctx,
        );
        let same = hyp_and(
            &hyp_syl(
                &refute,
                &under(&ex_falso(Formula::mem(Term::var(xv), zero.clone())), &neg_ctx),
            )?,
            &hyp_syl(&empty_side, &under(&ex_falso(mem_sep.clone()), &neg_ctx))?,
        )?;
        if *same.concl()
            != Formula::imp(
                neg_ctx.clone(),
                Formula::iff(mem_sep, Formula::mem(Term::var(xv), zero.clone())),
            )
        {
            return None
        }
        let ext = inst_all(&Thm::ax_extensionality(env), &[sep_t.clone(), zero.clone()])?;
        let eq_sets = hyp_mp(&under(&ext, &neg_ctx), &gen_under(xv, &neg_ctx, &same)?)?;
        let eq_un = hyp_congr(env, &eq_sets, move |q| ap.sets.union_of(q))?;
        let eq_zero = hyp_eq_trans(env, &eq_un, &under(un_empty, &neg_ctx))?;
        let chain_neg = syl(&syl(&n_ctx, &k_h)?, &chain)?;
        let full = hyp_eq_trans(env, &chain_neg, &eq_zero)?;

        let (covers, empty_in) = cod_parts(cod_f)?;
        let k_cod = syl(&syl(&n_ctx, &k_g)?, &and_left(cod_f.clone(), dep_f.clone()))?;
        let k_zero = syl(&k_cod, &and_right(covers, empty_in))?;
        carry_back(env, &full, &k_zero, &tt)?
    };

    let body_th = cases(&com12(&uncurry(&pos)?)?, &com12(&uncurry(&neg)?)?)?;
    if *body_th.concl() != Formula::imp(ctx.clone(), goal) {
        return None
    }

    // ── regeneralise into `minor_typedᵢ`, and into the firing rule ──────────
    let mut out = uncurry(&body_th)?;
    for v in vvs.iter().rev().chain(tvs.iter().rev()).chain(yvs.iter().rev()) {
        out = gen_under(*v, g, &out)?;
    }
    let want = minor_typed(env, s, ctor, &ps, &ind.wty, &gmin, &tt);
    if !crate::establishes(&out, &Formula::imp(g.clone(), want)) {
        return None
    }

    let mut quant: Vec<FreeVar> = yvs.clone();
    quant.extend(tvs.iter().copied());
    quant.extend(vvs.iter().copied());
    let fired = gen_all(&quant, &fires);
    Some((gmin, out, fired))
}
