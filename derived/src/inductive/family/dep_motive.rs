//! **The indexed dependent motive's premises** — [`super::super::motive`]'s
//! `COD` and `DEP` at a motive that varies with the *indices*, not only with
//! the tree.
//!
//! # Why these are not `motive.rs`'s at a cleverly chosen `C`
//!
//! [`dep_minor`](super::super::motive::dep_minor) applies the motive to the
//! **tree alone**: `app(C, tⱼ)` at each induction hypothesis and
//! `app(C, ctorᵢ(y⃗,t⃗))` at the conclusion. Lean's *indexed* minor applies it at
//! the constructor's own indices, `app(C, d⃗ᵢⱼ, rⱼ)` and `app(C, e⃗ᵢ, ctorᵢ)`,
//! and those indices are not recoverable from a tree-only motive — the two
//! statements are not instances of one another in either direction:
//!
//! * a tree-only `C'` cannot *state* Lean's premise, because `e⃗ᵢ` does not
//!   appear;
//! * and the obvious repair, `C'(z) := ⋃{ app(m,x⃗,z) : tup(x⃗) ∈ app(goodrec,z) }`,
//!   gives `app(m,e⃗ᵢ,ctorᵢ) ⊆ app(C',ctorᵢ)`, which is the right direction for
//!   the *conclusion* and the wrong one for the *induction hypothesis* — from
//!   `vⱼ ∈ app(C',tⱼ)` nothing recovers `vⱼ ∈ app(m,d⃗ᵢⱼ,tⱼ)`.
//!
//! So the premise is a different formula and this file states it. Everything
//! *below* the premise — the guarded minors, the recursion, ι — is shared;
//! see [`super::dep_guard`].
//!
//! # Interface
//!
//! Writing `W` for the raw skeleton carrier, `m` for the motive, `T` for the
//! target and `app(m, x⃗, z)` for [`super::motive_app`]'s curried spine:
//!
//! ```text
//! ICOV(m,T) := ∀x⃗ ∀z. ( z ∈ W → ∀y. ( y ∈ app(m,x⃗,z) → y ∈ T ) )
//! ICOD(m,T) := ICOV(m,T) ∧ ∅ ∈ T                                    [icod]
//!
//! IDEPᵢ(m,Sᵢ) := ∀f⃗ ∀v⃗. ( Aᵢ → Sᵢ⟪f⃗⟫v⃗ ∈ app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗)) )
//!                                                              [idep_minor]
//! ```
//!
//! `f⃗` is the constructor's `kᵢ + mᵢ` fields **in declared order** and `v⃗` the
//! `mᵢ` induction hypotheses, exactly as Lean's own minor binds them; `Sᵢ⟪f⃗⟫v⃗`
//! is [`applied_minor`] at [`Inductive::minor_args`] — Lean's own grain, since
//! `Sᵢ` is a function on `⟦γⱼ → T p⃗⟧` and not on the fibre `Aⱼ` the antecedent
//! binds. `Aᵢ` is [`super::minor_atoms_general`], which at a constructor with
//! no function-typed recursive field **is** [`super::minor_atoms_at`], the
//! builder [`IndexedPropRecursor`](super::IndexedPropRecursor) uses at `•`
//! instead of at the bound `vⱼ`. Two thirds of the antecedent is therefore
//! literally the `Prop` rule's `minor_atoms` wherever the `Prop` rule applies,
//! which is what lets a consumer transport its existing walk unchanged; it
//! holds only while the order stays Lean's, so the order is not a free choice
//! here.
//!
//! # `ICOD` keeps `COD`'s two-conjunct shape, deliberately
//!
//! [`cod_parts`](super::super::motive::cod_parts) reads any `and` apart, and
//! `ICOD` is an `and` of the same two things in the same order, so the guard's
//! negative case (`⋃∅ = ∅ ∈ T`) and its positive case (the value is covered)
//! are the *same* two projections at both arities. That is why the shared core
//! in [`super::super::guard`] needs to know nothing about indices.
//!
//! The covering conjunct is guarded by `z ∈ W` rather than by
//! `z ∈ ind(p⃗,x⃗)` — the weaker antecedent, hence the *stronger* premise, and
//! the one the caller can actually discharge from the motive's own funspace
//! typing without first proving the constructor lands at its index.
//!
//! # Nothing here is derived
//!
//! Both are formula builders. Every theorem about them lives in
//! [`super::dep_guard`] and [`super::dep_rec`].

use kernel::{Env, Formula, FreeVar, Term};

use crate::conj_of;
use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::inductive::step::applied_minor;
use crate::sums::Sums;

use super::carrier::IndexedCarrier;
use super::prop_rec::{lean_order_of, minor_atoms_general, motive_app};
use super::spec::IndexedDeclSpec;

/// `ICOD(m,T)` — the target holds every value of the motive, at every index
/// vector and every element of the skeleton, and holds `∅`.
///
/// At `ni = 0` this is [`cod`](super::super::motive::cod) on the nose.
pub fn icod(env: &mut Env, s: &Sums, w: &Term, ni: usize, m: &Term, t: &Term) -> Formula {
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let (zv, yv) = (env.fresh_var(), env.fresh_var());
    let (tz, ty) = (Term::var(zv), Term::var(yv));

    let inner = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty, motive_app(s, m, &xs, &tz)),
            Formula::mem(Term::var(yv), t.clone()),
        ),
    );
    let body = Formula::forall(zv, Formula::imp(Formula::mem(tz, w.clone()), inner));
    let covers = xvs.iter().rev().fold(body, |acc, v| Formula::forall(*v, acc));
    Formula::and(covers, Formula::mem(s.zero(), t.clone()))
}

/// `IDEPᵢ(m,Sᵢ)` — Lean's dependent minor premise for one constructor of an
/// indexed family.
///
/// `None` unless `spec`/`ixc` describe one family over `mach`, `ind` is its
/// skeleton and `i` is in range.
#[allow(clippy::too_many_arguments)]
pub fn idep_minor(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    i: usize,
    m: &Term,
    su: &Term,
) -> Option<Formula> {
    let c = spec.base.ctors.get(i)?;
    let (k, mm) = (c.args.len(), c.recs);
    let s = &mach.wt.sums;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..mm).map(|_| env.fresh_var()).collect();
    let vvs: Vec<FreeVar> = (0..mm).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    let atoms = minor_atoms_general(env, mach, ind, spec, ixc, i, m, &ps, &ys, &ts, &vs)?;
    // **The applied minor is at Lean's own grain**, exactly as
    // [`dep_minor`](super::super::motive::dep_minor) states it: `Sᵢ` is a
    // function on `⟦γⱼ → T p⃗⟧`, not on `fs(Aⱼ, ind(p⃗,d⃗ᵢⱼ))`, and the crossing
    // is [`Inductive::minor_args`]. `t⃗` themselves stay the constructor term's
    // arguments, because `ctorᵢ(y⃗,t⃗)` is in the conclusion.
    let subs = ind.minor_subs(mach, i, &ts)?;
    let a_subs = ind.minor_args(env, mach, i, &subs)?;
    let a_vs = ind.minor_args(env, mach, i, &vs)?;
    let concl = Formula::mem(
        applied_minor(&s.ap, &c.order, su, &ys, &a_subs, &a_vs),
        motive_app(s, m, &spec.result_vec(i, &ps, &ys)?, &ind.ctor_term(mach, i, &ys, &ts)?),
    );
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = lean_order_of(&c.order, &yvs, &tvs)?;
    quant.extend(vvs);
    Some(quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc)))
}

/// Every [`idep_minor`], in constructor order. `None` on a length mismatch.
#[allow(clippy::too_many_arguments)]
pub fn idep_parts(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    m: &Term,
    minors: &[Term],
) -> Option<Vec<Formula>> {
    if minors.len() != spec.base.ctors.len() {
        return None
    }
    (0..minors.len())
        .map(|i| idep_minor(env, mach, ind, spec, ixc, i, m, &minors[i]))
        .collect()
}

/// `IDEP(m,S⃗)`, the right-nested conjunction. `None` for a declaration with no
/// constructors.
#[allow(clippy::too_many_arguments)]
pub fn idep_hyp(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ixc: &IndexedCarrier,
    m: &Term,
    minors: &[Term],
) -> Option<Formula> {
    conj_of(&idep_parts(env, mach, ind, spec, ixc, m, minors)?)
}
