//! **SUPERSEDED.** Tests for the above-kernel deduction layer; see the
//! "SUPERSEDED" section of `derived/src/hyp.rs`. They pass and are kept, since
//! they pin what the in-kernel judgement will have to do too.
//!
//! The deduction layer: [`derived::hyp::Hyp`].
//!
//! Every test asserts an **exact** conclusion, at atoms built from freshly
//! declared 0-ary symbols. Constants rather than variables on purpose: a
//! statement about `c₀ ∈ c₁` for opaque constants is provable only if the
//! propositional structure really is there, whereas a formula over free
//! variables can be accidentally satisfiable by a rule that instantiated
//! something. Several tests then check the *negative* — that the layer returns
//! `None` — because a layer whose operations silently succeed on nonsense is
//! worse than no layer.

use derived::hyp::{order, Hyp};
use kernel::{Env, Formula, Term, Thm};

/// `n` distinct atomic formulas `cᵢ ∈ cᵢ'`, over fresh 0-ary symbols.
fn atoms(env: &mut Env, n: usize) -> Vec<Formula> {
    (0..n)
        .map(|_| {
            let a = Term::apply(env.declare(0), vec![]);
            let b = Term::apply(env.declare(0), vec![]);
            Formula::mem(a, b)
        })
        .collect()
}

/// `⊤`, as the layer spells it.
fn top() -> Formula { Formula::not(Formula::false_()) }

#[test]
fn assume_has_the_stated_shape() {
    let mut env = Env::new();
    let a = atoms(&mut env, 1).remove(0);
    let h = Hyp::assume(a.clone());
    assert_eq!(h.hyps(), std::slice::from_ref(&a));
    assert_eq!(*h.concl(), a);
    assert_eq!(*h.thm().concl(), Formula::imp(a.clone(), a), "assume must wrap ⊢ φ → φ");
    assert!(!h.is_closed());
}

#[test]
fn lift_has_the_stated_shape() {
    let mut env = Env::new();
    let t = Thm::eq_refl(Term::apply(env.declare(0), vec![]));
    let h = Hyp::lift(&t);
    assert!(h.hyps().is_empty());
    assert_eq!(h.concl(), t.concl());
    assert_eq!(*h.thm().concl(), Formula::imp(top(), t.concl().clone()), "lift must wrap ⊢ ⊤ → φ");
    // And the `⊤` comes back off.
    assert_eq!(h.into_thm().expect("no hypotheses").concl(), t.concl());
}

#[test]
fn conj_is_right_nested_with_no_padding() {
    let mut env = Env::new();
    let a = atoms(&mut env, 3);
    assert_eq!(order::conj(&[]), top());
    assert_eq!(order::conj(&a[..1]), a[0]);
    assert_eq!(order::conj(&a[..2]), Formula::and(a[0].clone(), a[1].clone()));
    assert_eq!(
        order::conj(&a),
        Formula::and(a[0].clone(), Formula::and(a[1].clone(), a[2].clone()))
    );
}

/// The core claim: a binary operation on two `Hyp`s with *different*
/// hypothesis sets unions them and rebuilds the implication.
#[test]
fn binary_operations_union_merge() {
    let mut env = Env::new();
    let a = atoms(&mut env, 2);
    let (p, q) = (a[0].clone(), a[1].clone());

    let hp = Hyp::assume(p.clone());
    let hq = Hyp::assume(q.clone());
    let both = hp.and_intro(&hq).expect("and_intro merges");

    assert_eq!(both.hyps().len(), 2, "the union of two singletons has two members");
    assert!(both.hyps().contains(&p) && both.hyps().contains(&q));
    assert_eq!(*both.concl(), Formula::and(p.clone(), q.clone()));
    assert_eq!(
        *both.thm().concl(),
        Formula::imp(order::conj(both.hyps()), Formula::and(p.clone(), q.clone())),
        "the invariant must hold on the nose"
    );

    // And the caller can name the nesting it wants at the boundary.
    let closed = both.close(&[p.clone(), q.clone()]).expect("close reorders");
    assert_eq!(
        *closed.concl(),
        Formula::imp(Formula::and(p.clone(), q.clone()), Formula::and(p, q))
    );
}

/// Equal hypothesis sets must produce the *same* theorem however they were
/// assembled — otherwise nothing downstream composes.
#[test]
fn the_order_is_canonical() {
    let mut env = Env::new();
    let a = atoms(&mut env, 3);
    let hs: Vec<Hyp> = a.iter().cloned().map(Hyp::assume).collect();

    let left = hs[0].and_intro(&hs[1]).unwrap().and_intro(&hs[2]).unwrap();
    let right = hs[2].and_intro(&hs[0]).unwrap().and_intro(&hs[1]).unwrap();
    assert_eq!(left.hyps(), right.hyps(), "assembly order must not affect the set");
    assert_eq!(
        left.thm().concl().as_imp().unwrap().0,
        right.thm().concl().as_imp().unwrap().0,
        "assembly order must not affect the antecedent"
    );
}

/// `mp` across differing hypothesis sets, with the exact conclusion pinned.
#[test]
fn mp_merges_and_concludes() {
    let mut env = Env::new();
    let a = atoms(&mut env, 3);
    let (p, q, r) = (a[0].clone(), a[1].clone(), a[2].clone());

    // {p → q} ⊢ p → q  and  {p} ⊢ p  give  {p, p → q} ⊢ q.
    let imp = Hyp::assume(Formula::imp(p.clone(), q.clone()));
    let arg = Hyp::assume(p.clone());
    let out = imp.mp(&arg).expect("mp merges");
    assert_eq!(*out.concl(), q);
    assert_eq!(out.hyps().len(), 2);

    // Applying it to an unrelated hypothesis must not silently succeed.
    assert!(imp.mp(&Hyp::assume(r)).is_none(), "mp must reject a mismatched argument");
}

/// Discharging returns exactly the hypothesis to the formula.
#[test]
fn discharge_moves_a_hypothesis_into_the_conclusion() {
    let mut env = Env::new();
    let a = atoms(&mut env, 2);
    let (p, q) = (a[0].clone(), a[1].clone());

    let h = Hyp::assume(p.clone()).and_intro(&Hyp::assume(q.clone())).expect("merge");
    let d = h.discharge(&q).expect("q is assumed");
    assert_eq!(d.hyps(), std::slice::from_ref(&p));
    assert_eq!(*d.concl(), Formula::imp(q.clone(), Formula::and(p.clone(), q.clone())));

    let d2 = d.discharge(&p).expect("p is assumed");
    assert!(d2.is_closed());
    let t = d2.into_thm().expect("closed");
    assert_eq!(
        *t.concl(),
        Formula::imp(p.clone(), Formula::imp(q.clone(), Formula::and(p, q.clone()))),
        "the fully discharged theorem is the curried conjunction introduction"
    );

    // Discharging something that was never assumed is a rejection.
    assert!(Hyp::assume(q.clone()).discharge(&Formula::false_()).is_none());
}

/// A single `assume` discharged is `⊢ φ → φ` and nothing more.
#[test]
fn discharge_of_an_assumption_is_reflexivity() {
    let mut env = Env::new();
    let p = atoms(&mut env, 1).remove(0);
    let t = Hyp::assume(p.clone()).discharge(&p).unwrap().into_thm().unwrap();
    assert_eq!(*t.concl(), Formula::imp(p.clone(), p));
}

/// Generalisation must be refused while a hypothesis mentions the variable, and
/// allowed once it does not. This is the check callers currently rediscover.
#[test]
fn gen_checks_the_free_variable_against_the_hypotheses() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let c = Term::apply(env.declare(0), vec![]);
    let mem = Formula::mem(Term::var(x), c.clone());

    let h = Hyp::assume(mem.clone());
    assert!(h.gen(x).is_none(), "x is free in the hypothesis — gen must be refused");

    // Discharge it first, and the same generalisation is legitimate.
    let d = h.discharge(&mem).expect("assumed");
    let g = d.gen(x).expect("nothing constrains x any more");
    assert!(g.is_closed());
    assert_eq!(
        *g.into_thm().unwrap().concl(),
        Formula::forall(x, Formula::imp(mem.clone(), mem)),
        "gen must produce exactly ∀x. (x ∈ c → x ∈ c)"
    );

    // A variable free in an *unrelated* hypothesis is refused just the same.
    let y = env.fresh_var();
    let other = Formula::mem(Term::var(y), c);
    let two = Hyp::assume(Formula::false_()).weaken(&[other]).unwrap();
    assert!(two.gen(y).is_none(), "gen must look at every hypothesis, not just the relevant one");
}

/// Instantiation and existential introduction, with exact shapes.
#[test]
fn inst_and_exists_intro() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let (c, d) = (Term::apply(env.declare(0), vec![]), Term::apply(env.declare(0), vec![]));
    let body = Formula::mem(Term::var(x), c.clone());

    let all = Hyp::assume(Formula::forall(x, body.clone()));
    let at_d = all.inst(d.clone()).expect("instantiate");
    assert_eq!(*at_d.concl(), Formula::mem(d.clone(), c.clone()));

    let ex = at_d.exists_intro(x, &body, d.clone()).expect("witness d");
    assert_eq!(*ex.concl(), Formula::exists(x, body.clone()));
    assert_eq!(ex.hyps(), std::slice::from_ref(&Formula::forall(x, body.clone())));

    // The premise must actually be the claimed instance.
    assert!(at_d.exists_intro(x, &Formula::mem(Term::var(x), d.clone()), d).is_none());
}

/// Existential elimination discharges the witness from the hypothesis set,
/// merges what is left, and enforces the escape condition.
#[test]
fn obtain_eliminates_an_existential() {
    let mut env = Env::new();
    let w = env.fresh_var();
    let (c, d) = (Term::apply(env.declare(0), vec![]), Term::apply(env.declare(0), vec![]));
    let tw = Term::var(w);

    // `∃w. (w ∈ c ∧ d ∈ d)`. The right conjunct does not mention the witness,
    // so it may leave the existential's scope; the left one may not.
    let side = atoms(&mut env, 1).remove(0);
    let body = Formula::and(Formula::mem(tw.clone(), c.clone()), Formula::mem(d.clone(), d.clone()));
    let goal = Formula::mem(d.clone(), d.clone());

    let ex = Hyp::assume(Formula::exists(w, body.clone()));
    // {body, side} ⊢ (d ∈ d) ∧ side — a second, witness-free hypothesis rides
    // along, and must survive the elimination untouched.
    let inner = Hyp::assume(body.clone())
        .and_right()
        .expect("split")
        .and_intro(&Hyp::assume(side.clone()))
        .expect("merge");
    assert_eq!(inner.hyps().len(), 2);

    let out = Hyp::obtain(w, &ex, &inner).expect("w escapes nothing");
    assert_eq!(*out.concl(), Formula::and(goal, side.clone()));
    assert_eq!(out.hyps().len(), 2, "the opened body is gone; the existential's own hypothesis is in");
    assert!(out.hyps().contains(&Formula::exists(w, body.clone())));
    assert!(out.hyps().contains(&side));

    // If the conclusion mentions the witness, the rule must refuse.
    let escaping = Hyp::assume(body.clone()).and_left().expect("split");
    assert_eq!(*escaping.concl(), Formula::mem(tw.clone(), c.clone()));
    assert!(Hyp::obtain(w, &ex, &escaping).is_none(), "a witness-dependent conclusion must not escape");

    // And so must a hypothesis that mentions it: the same body, kept as an
    // assumption alongside, keeps `w` alive in the merged set.
    let held = Hyp::assume(body.clone())
        .and_right()
        .expect("split")
        .and_intro(&Hyp::assume(Formula::mem(tw.clone(), c.clone())))
        .expect("merge")
        .and_left()
        .expect("split");
    assert!(
        Hyp::obtain(w, &ex, &held).is_none(),
        "a surviving hypothesis mentioning the witness must block the elimination"
    );
}

/// Case analysis merges three hypothesis sets.
#[test]
fn or_elim_merges_three_ways() {
    let mut env = Env::new();
    let a = atoms(&mut env, 3);
    let (p, q, r) = (a[0].clone(), a[1].clone(), a[2].clone());

    let disj = Hyp::assume(Formula::or(p.clone(), q.clone()));
    let left = Hyp::assume(Formula::imp(p.clone(), r.clone()));
    let right = Hyp::assume(Formula::imp(q.clone(), r.clone()));
    let out = disj.or_elim(&left, &right).expect("case split");
    assert_eq!(*out.concl(), r);
    assert_eq!(out.hyps().len(), 3);
}

/// Equality: symmetry, transitivity and congruence, under hypotheses that are
/// *not* shared between the premises.
#[test]
fn equality_operations_merge() {
    let mut env = Env::new();
    let f = env.declare(1);
    let (a, b, c) = (
        Term::apply(env.declare(0), vec![]),
        Term::apply(env.declare(0), vec![]),
        Term::apply(env.declare(0), vec![]),
    );
    let (e1, e2) = (Formula::eq(a.clone(), b.clone()), Formula::eq(b.clone(), c.clone()));

    let h1 = Hyp::assume(e1.clone());
    let h2 = Hyp::assume(e2.clone());

    let sym = h1.symm(&mut env).expect("symm");
    assert_eq!(*sym.concl(), Formula::eq(b.clone(), a.clone()));
    assert_eq!(sym.hyps(), std::slice::from_ref(&e1));

    let tr = h1.trans(&mut env, &h2).expect("trans");
    assert_eq!(*tr.concl(), Formula::eq(a.clone(), c.clone()));
    assert_eq!(tr.hyps().len(), 2, "transitivity unions the two equations' hypotheses");

    let cg = h1.congr_arg(&mut env, f, std::slice::from_ref(&a), 0).expect("congruence");
    assert_eq!(
        *cg.concl(),
        Formula::eq(Term::apply(f, vec![a.clone()]), Term::apply(f, vec![b.clone()]))
    );

    // Rewriting a hypothesis-borne fact along a hypothesis-borne equation.
    let w = env.fresh_var();
    let phi = Formula::mem(Term::var(w), c.clone());
    let at_a = Hyp::assume(Formula::mem(a.clone(), c.clone()));
    let moved = h1.subst(w, &phi, &at_a).expect("rewrite");
    assert_eq!(*moved.concl(), Formula::mem(b, c));
    assert_eq!(moved.hyps().len(), 2);

    // A non-equation is rejected.
    assert!(Hyp::assume(Formula::false_()).symm(&mut env).is_none());
}

/// `wrap` is the only constructor and it enforces the invariant.
#[test]
fn wrap_rejects_a_mismatched_theorem() {
    let mut env = Env::new();
    let a = atoms(&mut env, 2);
    let (p, q) = (a[0].clone(), a[1].clone());

    // ⊢ p → p is a fine theorem, but not a proof of anything under {q}.
    assert!(Hyp::wrap(vec![q.clone()], derived::imp_refl(p.clone())).is_none());
    // Nor is a non-implication a legal wrapped theorem.
    assert!(Hyp::wrap(vec![], Thm::eq_refl(Term::apply(env.declare(0), vec![]))).is_none());
    // The honest pairing is accepted, and canonicalises its input.
    let h = Hyp::wrap(vec![p.clone(), p.clone()], derived::imp_refl(p.clone())).expect("dedupes");
    assert_eq!(h.hyps(), std::slice::from_ref(&p));
    let _ = q;
}

/// Turning memoisation off must not change a single conclusion.
#[test]
fn memoisation_is_transparent() {
    let mut env = Env::new();
    let a = atoms(&mut env, 3);

    let build = || {
        let hs: Vec<Hyp> = a.iter().cloned().map(Hyp::assume).collect();
        hs[0]
            .and_intro(&hs[1])
            .unwrap()
            .and_intro(&hs[2])
            .unwrap()
            .discharge(&a[1])
            .unwrap()
            .close(&[a[0].clone(), a[2].clone()])
            .unwrap()
    };
    let with = build();
    let was = order::memo_enabled(false);
    let without = build();
    order::memo_enabled(was);
    order::forget();
    assert_eq!(with.concl(), without.concl(), "the memo must not change any conclusion");
}

/// Non-vacuity: the layer must not be able to conclude something it was not
/// given. If `Hyp` could quietly weaken its own hypothesis set, this would pass
/// anyway — so the check is that the *final* theorem is not derivable from
/// nothing, by exhibiting it at opaque constants and checking it is a genuine
/// implication rather than the conclusion alone.
#[test]
fn the_layer_does_not_manufacture_theorems() {
    let mut env = Env::new();
    let a = atoms(&mut env, 2);
    let (p, q) = (a[0].clone(), a[1].clone());

    let out = Hyp::assume(Formula::imp(p.clone(), q.clone()))
        .mp(&Hyp::assume(p.clone()))
        .expect("mp");
    // `q` at an opaque constant is not provable, so the theorem had better still
    // carry both hypotheses.
    assert_eq!(*out.concl(), q);
    assert!(!out.is_closed(), "the hypotheses must not have evaporated");
    assert!(out.clone().into_thm().is_none(), "an open Hyp must not hand over a bare theorem");
    let t = out.close(&[Formula::imp(p.clone(), q.clone()), p.clone()]).expect("close");
    assert_eq!(*t.concl(), Formula::imp(Formula::and(Formula::imp(p, q.clone()), a[0].clone()), q));
}
