//! The **dependent** recursor: structural induction over a declaration's
//! carrier ([`derived::inductive::rect`]), the guarded minors that make `HYP`
//! dischargeable at a variable motive, and the recursor's typing and ι rules at
//! a genuinely dependent motive.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::bound::Bound;
use derived::inductive::rect::{decl_rect, rect_step};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{conj_of, define_abbrev, disj_of, inst_all};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

struct Fix {
    mach: Machine,
    #[allow(dead_code)]
    rc: Recursor,
    #[allow(dead_code)]
    iota: Thm,
    #[allow(dead_code)]
    funspace: Thm,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { mach, rc, iota, funspace }
}

/// A constant argument-type symbol of the given arity, with value `1`.
fn const_unit_beta(env: &mut Env, mach: &Machine, arity: usize) -> FnSym {
    let vars: Vec<kernel::FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let one = mach.wt.sums.unit();
    define_abbrev(env, &vars, &one).expect("β").0
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural induction
// ─────────────────────────────────────────────────────────────────────────────

/// The premise's antecedent is one flat right-nested chain of `k + 2m` atoms in
/// the order *arguments, recursive arguments, induction hypotheses* — pinned at
/// an interleaved `Plain, Rec, Plain, Rec` mask, where a "fields then recs"
/// reading and a "grouped" reading both differ from this one.
#[test]
fn the_induction_step_orders_its_atoms_by_role_not_by_declaration() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let b0 = const_unit_beta(env, &mach, 0);
    let b1 = const_unit_beta(env, &mach, 1);
    let spec = DeclSpec {
        params: 0,
        ctors: vec![
            CtorSpec { args: vec![], recs: 0, order: vec![] },
            CtorSpec {
                args: vec![b0, b1],
                recs: 2,
                order: vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
            },
        ],
    };
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");

    let zv = env.fresh_var();
    let phi = Formula::mem(Term::var(zv), mach.wt.sums.unit());
    let step = rect_step(env, &mach, &ind, 1, zv, &phi).expect("step");

    // Rebuilt from the kernel's own constructors: four binders in declaration
    // order, then `y₀ ∈ β₀`, `y₁ ∈ β₁(y₀)`, `t₀ ∈ W`, `t₁ ∈ W`, `φ(t₀)`,
    // `φ(t₁)`, then the conclusion at the constructor.
    let vs: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vs.iter().map(|v| Term::var(*v)).collect();
    let (ys, rs) = (&ts[..2], &ts[2..]);
    let ante = conj_of(&[
        Formula::mem(ys[0].clone(), Term::apply(b0, vec![])),
        Formula::mem(ys[1].clone(), Term::apply(b1, vec![ys[0].clone()])),
        Formula::mem(rs[0].clone(), ind.wty.clone()),
        Formula::mem(rs[1].clone(), ind.wty.clone()),
        phi.subst(zv, &rs[0]),
        phi.subst(zv, &rs[1]),
    ])
    .expect("six atoms");
    let concl = phi.subst(zv, &ind.ctor_term(&mach, 1, ys, rs).expect("constructor"));
    let want = vs
        .iter()
        .rev()
        .fold(Formula::imp(ante, concl), |acc, v| Formula::forall(*v, acc));
    assert_eq!(step, want, "the induction step is not the documented chain");

    // And the principle itself goes through at this shape — which is where the
    // two η rules are actually used: `k = 2` needs the telescope's, `m = 2`
    // needs [`recarg_eta`], and neither fires at the all-nullary declaration.
    let rule = decl_rect(env, &mach, &ind, zv, &phi).expect("induction at k=2, m=2");
    let hyp = conj_of(&[
        rect_step(env, &mach, &ind, 0, zv, &phi).expect("step 0"),
        want,
    ])
    .expect("two steps");
    let goal = Formula::forall(
        zv,
        Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
    );
    assert!(derived::establishes(&rule, &Formula::imp(hyp, goal)));
}

/// **Non-vacuity.** At a three-constructor enumeration the premise is
/// discharged outright and the principle yields a closed, unconditional
/// theorem that says the carrier has *no other members* — something no
/// per-constructor typing rule states and `w_rect` cannot say at all, because
/// it does not know what a constructor is.
#[test]
fn induction_proves_a_three_constructor_enumeration_has_no_junk() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let spec = DeclSpec {
        params: 0,
        ctors: (0..3)
            .map(|_| CtorSpec { args: vec![], recs: 0, order: vec![] })
            .collect(),
    };
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");
    let es: Vec<Term> = (0..3)
        .map(|i| ind.ctor_term(&mach, i, &[], &[]).expect("constructor"))
        .collect();

    let zv = env.fresh_var();
    let phi = disj_of(&es.iter().map(|e| Formula::eq(Term::var(zv), e.clone())).collect::<Vec<_>>())
        .expect("three disjuncts");
    let rule = decl_rect(env, &mach, &ind, zv, &phi).expect("induction");

    // Each step is `eᵢ = e₀ ∨ (eᵢ = e₁ ∨ eᵢ = e₂)`, by reflexivity.
    let steps: Vec<Thm> = (0..3)
        .map(|i| {
            let atoms: Vec<Formula> =
                es.iter().map(|e| Formula::eq(es[i].clone(), e.clone())).collect();
            let mut th = Thm::eq_refl(es[i].clone());
            if let Some(tail) = disj_of(&atoms[i + 1..]) {
                th = Thm::mp(&derived::funcs::or_intro_left(atoms[i].clone(), tail), &th)
                    .expect("left injection");
            }
            for j in (0..i).rev() {
                let tail = disj_of(&atoms[j + 1..]).expect("a non-empty tail");
                th = Thm::mp(&derived::funcs::or_intro_right(atoms[j].clone(), tail), &th)
                    .expect("right injection");
            }
            th
        })
        .collect();

    let hyp = steps
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .expect("the premise");
    let out = Thm::mp(&rule, &hyp).expect("modus ponens");

    let want = Formula::forall(
        zv,
        Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
    );
    assert!(derived::establishes(&out, &want), "no-junk is not what came out");
    assert!(closed(out.concl()), "the no-junk theorem should be closed");

    // …and it is not vacuous: the three constructors are provably distinct, so
    // the carrier it describes has three members, not one.
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let d = ind.distinct(env, &mach, i, j).expect("distinctness");
        assert!(d.hyps().is_empty());
    }
    let _ = inst_all(&out, &[es[2].clone()]).expect("instantiable at a constructor");
}
