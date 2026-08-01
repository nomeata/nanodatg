//! **What a dependent motive asks for** — the two premises [`super::dep`]
//! carries, as formulas, plus the one canonical way to discharge the first.
//!
//! # Interface
//!
//! At the declaration's parameters `p⃗`, a motive `C` (a set-level function on
//! the carrier), the Lean minor-premise variables `S⃗` and a target `T`, writing
//! `W` for the raw carrier and `ctorᵢ(y⃗,t⃗)` for [`Inductive::ctor_term`]:
//!
//! ```text
//! COD(C,T)   := (∀x. (x ∈ W → ∀y. (y ∈ app(C,x) → y ∈ T))) ∧ ∅ ∈ T        [cod]
//!
//! DEPᵢ(C,Sᵢ) := ∀y₀ … y_{k-1} ∀t₀ … t_{m-1} ∀v₀ … v_{m-1}.
//!     (( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1}) ∧ ⋀ⱼ tⱼ ∈ W ∧ ⋀ⱼ vⱼ ∈ app(C,tⱼ) )
//!        → Sᵢ⟪y⃗,t⃗ in declared order⟫ v₀ … v_{m-1} ∈ app(C, ctorᵢ(y⃗,t⃗)))  [dep_minor]
//!
//! DEP(C,S⃗)  := DEP₀ ∧ ( … ∧ DEP_{n-1})                                  [dep_hyp]
//!
//! ⊢ ∀C ∀V. (C ∈ fs(W, V) → COD(C, ⋃V ∪ {∅}))                  [cod_at_funspace]
//! ```
//!
//! # `DEPᵢ` is Lean's minor premise, on the nose
//!
//! It differs from [`super::premise`]'s `minor_typedᵢ` in exactly one place, and
//! that place is the whole of the dependent-motive problem: the induction
//! hypotheses are typed at `app(C,tⱼ)` — the motive **at the recursive argument
//! it belongs to** — rather than at one flat target, and the conclusion lands in
//! `app(C, ctorᵢ(y⃗,t⃗))` rather than in the same flat target. Everything else —
//! the argument order, the `k + 2m` right-nested antecedent, the
//! [`super::step::applied_minor`] spelling, the disappearance of the antecedent
//! at a field-free constructor — is shared verbatim, so the two can be read side
//! by side and a caller that can produce one can see what the other costs.
//!
//! # `COD` is a bookkeeping premise, not a real one
//!
//! [`super::dep`]'s recursor is still `wrec` at one target set; `COD` says only
//! that the target is *big enough* to hold every value the motive can take, and
//! that it holds `∅` (the value the guarded minors of [`super::guard`] fall back
//! on when their induction hypotheses are junk). It never says the target is
//! closed under anything, which is why it is discharged outright:
//! [`cod_at_funspace`] takes `T := ⋃V ∪ {∅}` for **any** `V` the motive is a
//! function into, and in the wiring `V` is `⟦Sort u₁⟧`, which is what the
//! motive's own Lean type gives. So the target policy of `RECURSOR-DESIGN.md`
//! §5.2 has nothing left to choose at a dependent motive.

use kernel::{Env, Formula, Term, Thm};

use crate::funspace::{bin_union, mem_bin_union};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, conj_of, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, singleton, syl,
    uncurry,
};

use super::carrier::Inductive;
use super::machine::Machine;
use super::rec_shared::gen_under;
use super::spec::CtorSpec;
use super::step::applied_minor;

/// `COD(C,T)` — the target holds every value of the motive, and `∅`.
pub fn cod(env: &mut Env, s: &Sums, w: &Term, c: &Term, t: &Term) -> Formula {
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let inner = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty, s.ap.apply(c.clone(), tx.clone())),
            Formula::mem(Term::var(yv), t.clone()),
        ),
    );
    let covers = Formula::forall(xv, Formula::imp(Formula::mem(tx, w.clone()), inner));
    Formula::and(covers, Formula::mem(s.zero(), t.clone()))
}

/// The target [`cod_at_funspace`] discharges `COD` at: `⋃V ∪ {∅}`.
pub fn cod_target(s: &Sums, v: &Term) -> Term {
    bin_union(&s.ap.sets, s.ap.sets.union_of(v.clone()), singleton(s.ap.sets.up, s.zero()))
}

/// `DEPᵢ(C,Sᵢ)` — Lean's dependent minor premise for one constructor.
///
/// `None` unless `ind` was translated over `mach` and `i` is in range.
pub fn dep_minor(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    c: &Term,
    su: &Term,
) -> Option<Formula> {
    let ctor: &CtorSpec = ind.spec.ctors.get(i)?;
    let (k, m) = (ctor.args.len(), ctor.recs);
    let s = &mach.wt.sums;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let yvs: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    atoms.extend(
        (0..m).map(|j| {
            Formula::mem(vs[j].clone(), s.ap.apply(c.clone(), ts[j].clone()))
        }),
    );

    let applied = applied_minor(&s.ap, &ctor.order, su, &ys, &ts, &vs);
    let target = s.ap.apply(c.clone(), ind.ctor_term(mach, i, &ys, &ts)?);
    let concl = Formula::mem(applied, target);
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    quant.extend(vvs);
    Some(quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc)))
}

/// The conjuncts of [`dep_hyp`], for a caller that projects them one at a time.
pub fn dep_parts(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    c: &Term,
    minors: &[Term],
) -> Option<Vec<Formula>> {
    if minors.len() != ind.spec.ctors.len() {
        return None
    }
    (0..minors.len())
        .map(|i| dep_minor(env, mach, ind, i, c, &minors[i]))
        .collect()
}

/// `DEP(C,S⃗)`, the right-nested conjunction of every [`dep_minor`]. `None` for a
/// declaration with no constructors.
pub fn dep_hyp(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    c: &Term,
    minors: &[Term],
) -> Option<Formula> {
    conj_of(&dep_parts(env, mach, ind, c, minors)?)
}

/// `⊢ ∀C ∀V. (C ∈ fs(W, V) → COD(C, ⋃V ∪ {∅}))` — **the target policy, settled**.
///
/// A motive is a function into *some* set (in the wiring, `⟦Sort u₁⟧`), and the
/// union of that set together with `∅` is then a target that satisfies `COD`
/// unconditionally. No constructor, no arity and no nullary-constructor
/// special case is consulted; contrast `RECURSOR-DESIGN.md` §5.2's three-way
/// policy, which only ever had to choose because the target had to make
/// `minor_typedᵢ` *true*, and here it does not.
pub fn cod_at_funspace(env: &mut Env, mach: &Machine, ind: &Inductive) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let w = ind.wty.clone();
    let (cv, vv) = (env.fresh_var(), env.fresh_var());
    let (tc, tv) = (Term::var(cv), Term::var(vv));
    let (uv, sing) = (ap.sets.union_of(tv.clone()), singleton(ap.sets.up, s.zero()));
    let t = cod_target(s, &tv);
    let h = Formula::mem(tc.clone(), s.fs.of(w.clone(), tv.clone()));

    let (inj_l, inj_r) = mem_bin_union(env, &ap.sets)?;

    // `∅ ∈ {∅} ⊆ T`.
    let e_sing = iff_mpr(&inst_all(&ap.mem_sing, &[s.zero(), s.zero()])?)?;
    let e_in_sing = Thm::mp(&e_sing, &Thm::eq_refl(s.zero()))?;
    let right = inst_all(&inj_r, &[uv.clone(), sing.clone(), s.zero()])?;
    let empty_in_t = Thm::mp(&right, &e_in_sing)?;

    // `x ∈ W → y ∈ app(C,x) → y ∈ ⋃V ⊆ T`.
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let mx = Formula::mem(tx.clone(), w.clone());
    let my = Formula::mem(ty.clone(), ap.apply(tc.clone(), tx.clone()));
    let k = Formula::and(h.clone(), Formula::and(mx.clone(), my.clone()));

    let k_h = and_left(h.clone(), Formula::and(mx.clone(), my.clone()));
    let k_rest = and_right(h.clone(), Formula::and(mx.clone(), my.clone()));
    let k_mx = syl(&k_rest, &and_left(mx.clone(), my.clone()))?;
    let k_my = syl(&k_rest, &and_right(mx.clone(), my))?;

    let app_rule = inst_all(&mach.wt.app_mem, &[w.clone(), tv.clone(), tc.clone(), tx.clone()])?;
    let k_cx = hyp_mp(&a1i(&app_rule, k.clone()), &hyp_and(&k_h, &k_mx)?)?;
    let intro = crate::funcs::union_intro(
        env,
        &ap.sets,
        tv.clone(),
        ap.apply(tc.clone(), tx.clone()),
        ty.clone(),
    )?;
    let k_uv = hyp_mp(&a1i(&intro, k.clone()), &hyp_and(&k_cx, &k_my)?)?;
    let left = inst_all(&inj_l, &[uv, sing, ty])?;
    let k_t = syl(&k_uv, &a1i(&left, k.clone()))?;

    // Regeneralise into `COD`'s own shape.
    let inner = gen_under(yv, &Formula::and(h.clone(), mx.clone()), &uncurry(&k_t)?)?;
    let covers = gen_under(xv, &h, &uncurry(&inner)?)?;
    let out = hyp_and(&covers, &a1i(&empty_in_t, h.clone()))?;
    let want = Formula::imp(h, cod(env, s, &w, &tc, &t));
    if !crate::establishes(&out, &want) {
        return None
    }
    Some(gen_all(&[cv, vv], &out))
}
