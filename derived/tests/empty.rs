//! The empty set: how far Tarski's Axiom A gets us, checked step by step.
//!
//! Every test pins the **exact** conclusion of the lemma it covers, rebuilt
//! independently from the kernel's formula constructors. A lemma that returned
//! a differently-shaped theorem — even an alpha-variant, which cannot happen
//! here, or a weaker one, which can — fails these.

use derived::empty;
use kernel::{Env, Formula, Term, Thm};

/// The pairing symbol and the singleton lemmas every test below needs.
fn singletons(env: &mut Env) -> (kernel::FnSym, Thm) {
    let (up, up_ax) = derived::upair(env);
    let mem_sing = derived::mem_singleton(env, up, &up_ax).expect("membership in a singleton");
    (up, mem_sing)
}

/// `⊢ ∀x. ¬(x ∈ x)`, from Regularity at `{x}`.
#[test]
fn no_set_is_a_member_of_itself() {
    let mut env = Env::new();
    let (up, mem_sing) = singletons(&mut env);
    let thm = empty::no_self_mem(&mut env, up, &mem_sing).expect("no_self_mem");

    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    let x = env.fresh_var();
    let tx = Term::var(x);
    let expected = Formula::forall(x, Formula::not(Formula::mem(tx.clone(), tx)));
    assert_eq!(*thm.concl(), expected, "no_self_mem has the wrong shape");
}

/// The theorem is usable: instantiated at a constant it refutes `c ∈ c`.
#[test]
fn no_self_mem_instantiates() {
    let mut env = Env::new();
    let (up, mem_sing) = singletons(&mut env);
    let thm = empty::no_self_mem(&mut env, up, &mem_sing).expect("no_self_mem");

    let tc = Term::apply(env.declare(0), vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&tc)).expect("instantiate");
    assert_eq!(*inst.concl(), Formula::not(Formula::mem(tc.clone(), tc)));
}

/// `⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)` — Regularity turns a
/// non-empty transitive set into an empty one.
#[test]
fn empty_set_from_any_nonempty_transitive_set() {
    let mut env = Env::new();
    let thm = empty::empty_from_transitive(&mut env).expect("empty_from_transitive");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // Rebuild the statement from scratch.
    let t = env.fresh_var();
    let tt = Term::var(t);
    let w = env.fresh_var();
    let nonempty = Formula::exists(w, Formula::mem(Term::var(w), tt.clone()));
    let trans = empty::transitive(&mut env, &tt);
    let (e, z) = (env.fresh_var(), env.fresh_var());
    let goal = Formula::exists(
        e,
        Formula::forall(z, Formula::not(Formula::mem(Term::var(z), Term::var(e)))),
    );
    let expected = Formula::forall(t, Formula::imp(Formula::and(nonempty, trans), goal));
    assert_eq!(*thm.concl(), expected, "empty_from_transitive has the wrong shape");
}

/// The full Separation scheme follows from a non-empty transitive set:
/// `⊢ ∀t ∀a. ((∃w. w ∈ t) ∧ Trans(t)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ z ∈ c))`.
#[test]
fn separation_needs_only_a_nonempty_transitive_set() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let tc = Term::apply(env.declare(0), vec![]);
    let phi = Formula::mem(Term::var(x), tc.clone());

    let thm = empty::separation_from_transitive(&mut env, x, &phi).expect("conditional separation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (t, a, w, s, z) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tt, ta, tz) = (Term::var(t), Term::var(a), Term::var(z));
    let hyp = Formula::and(
        Formula::exists(w, Formula::mem(Term::var(w), tt.clone())),
        empty::transitive(&mut env, &tt),
    );
    let separated = Formula::and(Formula::mem(tz.clone(), ta), Formula::mem(tz.clone(), tc));
    let goal = Formula::exists(
        s,
        Formula::forall(z, Formula::iff(Formula::mem(tz, Term::var(s)), separated)),
    );
    let expected = Formula::forall(t, Formula::forall(a, Formula::imp(hyp, goal)));
    assert_eq!(*thm.concl(), expected, "conditional separation has the wrong shape");
}

/// `empty_of_exists` refuses anything that is not a proof that some set is
/// empty — the premise cannot be smuggled past it.
#[test]
fn empty_symbol_rejects_a_bogus_premise() {
    let mut env = Env::new();
    let (up, mem_sing) = singletons(&mut env);
    let not_an_existence = empty::no_self_mem(&mut env, up, &mem_sing).expect("no_self_mem");
    assert!(
        empty::empty_of_exists(&mut env, &not_an_existence).is_none(),
        "empty_of_exists accepted a theorem that is not `∃e ∀z. ¬(z ∈ e)`"
    );
}

/// `⊢ ∀z. ¬(z ∈ ∅)` — the empty set symbol, derived from `Thm::ax_empty`.
#[test]
fn the_empty_symbol_has_no_members() {
    let mut env = Env::new();
    let (e, thm) = empty::empty(&mut env);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert_eq!(e.arity(), 0, "∅ should be a constant");

    let z = env.fresh_var();
    let expected =
        Formula::forall(z, Formula::not(Formula::mem(Term::var(z), Term::apply(e, vec![]))));
    assert_eq!(*thm.concl(), expected, "empty has the wrong shape");
}

/// Instantiating it refutes membership at any term.
#[test]
fn nothing_is_a_member_of_the_empty_set() {
    let mut env = Env::new();
    let (e, thm) = empty::empty(&mut env);
    let tc = Term::apply(env.declare(0), vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&tc)).expect("instantiate");
    assert_eq!(*inst.concl(), Formula::not(Formula::mem(tc, Term::apply(e, vec![]))));
}

/// Tarski's axiom decomposes into its four clauses, and the projections out of
/// the conjunction are real theorems.
#[test]
fn tarski_clauses_project() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let (univ, ex) = empty::tarski_at(&mut env, x).expect("Tarski at x");

    assert_eq!(*ex.concl(), Formula::exists(univ.u, univ.body.clone()));
    assert_eq!(univ.mem, Formula::mem(Term::var(x), Term::var(univ.u)));
    // The body is `x ∈ u ∧ (C₂ ∧ (C₃ ∧ C₄))`.
    assert_eq!(
        univ.body,
        Formula::and(
            univ.mem.clone(),
            Formula::and(
                univ.closed_sub.clone(),
                Formula::and(univ.closed_pow.clone(), univ.inaccessible.clone())
            )
        )
    );
    // C₂ is `∀y. (y ∈ u → ∀z. (z ⊆ y → z ∈ u))`, rebuilt independently.
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz, tu) = (Term::var(y), Term::var(z), Term::var(univ.u));
    let sub = kernel::thm::subset(&mut env, tz.clone(), ty.clone());
    let expected_c2 = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), tu.clone()),
            Formula::forall(z, Formula::imp(sub, Formula::mem(tz, tu.clone()))),
        ),
    );
    assert_eq!(univ.closed_sub, expected_c2, "C₂ is not the subset-closure clause");

    assert_eq!(*univ.body_mem().concl(), Formula::imp(univ.body.clone(), univ.mem.clone()));
    assert_eq!(
        *univ.body_closed_sub().concl(),
        Formula::imp(univ.body.clone(), univ.closed_sub.clone())
    );
    assert_eq!(
        *univ.body_closed_pow().concl(),
        Formula::imp(univ.body.clone(), univ.closed_pow.clone())
    );
}

/// `⊢ Body → ∀y. (y ∈ u → 𝒫y ∈ u)` — the universe is closed under power sets.
#[test]
fn universe_is_closed_under_power_sets() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);
    let x = env.fresh_var();
    let (univ, _) = empty::tarski_at(&mut env, x).expect("Tarski at x");
    let thm = empty::universe_power_closed(&mut env, pow, &pow_ax, &univ).expect("power closure");

    let y = env.fresh_var();
    let (ty, tu) = (Term::var(y), Term::var(univ.u));
    let expected = Formula::imp(
        univ.body.clone(),
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(ty.clone(), tu.clone()),
                Formula::mem(Term::apply(pow, vec![ty]), tu),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "power closure has the wrong shape");
}

/// `⊢ Body → ∀y. (y ∈ u → ∃p. (p ∈ u ∧ y ∈ p))` — no member of the universe is
/// `∈`-maximal in it, which is what the hereditarily-finite `ℤ`-chain
/// counter-model cannot satisfy.
#[test]
fn universe_has_no_maximal_member() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let (univ, _) = empty::tarski_at(&mut env, x).expect("Tarski at x");
    let thm = empty::universe_no_maximal(&mut env, &univ).expect("no maximal member");

    let (y, p) = (env.fresh_var(), env.fresh_var());
    let (ty, tp, tu) = (Term::var(y), Term::var(p), Term::var(univ.u));
    let expected = Formula::imp(
        univ.body.clone(),
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(ty.clone(), tu.clone()),
                Formula::exists(
                    p,
                    Formula::and(Formula::mem(tp.clone(), tu), Formula::mem(ty, tp)),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "universe_no_maximal has the wrong shape");
}

/// `⊢ ∀x ∃u. (x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u))` — Tarski gives an inductive set,
/// i.e. Infinity.
#[test]
fn tarski_gives_an_inductive_set() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);
    let thm = empty::inductive_set_exists(&mut env, pow, &pow_ax).expect("inductive set");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (x, u) = (env.fresh_var(), env.fresh_var());
    let ind = empty::inductive(&mut env, pow, &Term::var(x), &Term::var(u));
    let expected = Formula::forall(x, Formula::exists(u, ind));
    assert_eq!(*thm.concl(), expected, "inductive_set_exists has the wrong shape");
}

/// `⊢ ∀x ∃n. (Ind(x,n) ∧ ∀w. (Ind(x,w) → ∀q. (q ∈ n → q ∈ w)))` — the least
/// inductive set, i.e. an `ω` with induction, carved out of Tarski's universe
/// by non-vacuous Separation.
#[test]
fn tarski_gives_a_least_inductive_set() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);
    let thm = empty::least_inductive_set_exists(&mut env, pow, &pow_ax).expect("least inductive");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (x, n) = (env.fresh_var(), env.fresh_var());
    let least = empty::least_inductive(&mut env, pow, &Term::var(x), &Term::var(n));
    let expected = Formula::forall(x, Formula::exists(n, least));
    assert_eq!(*thm.concl(), expected, "least_inductive_set_exists has the wrong shape");
}

/// The `Least` predicate is `Ind` plus containment in every inductive set —
/// spelled out here so the theorem above cannot be quietly weakened.
#[test]
fn least_inductive_predicate_shape() {
    let mut env = Env::new();
    let (pow, _) = derived::power(&mut env);
    let (tx, tn) = (Term::apply(env.declare(0), vec![]), Term::apply(env.declare(0), vec![]));

    let (w, q) = (env.fresh_var(), env.fresh_var());
    let (tw, tq) = (Term::var(w), Term::var(q));
    let contained = Formula::forall(
        q,
        Formula::imp(Formula::mem(tq.clone(), tn.clone()), Formula::mem(tq, tw.clone())),
    );
    let expected = Formula::and(
        empty::inductive(&mut env, pow, &tx, &tn),
        Formula::forall(w, Formula::imp(empty::inductive(&mut env, pow, &tx, &tw), contained)),
    );
    assert_eq!(empty::least_inductive(&mut env, pow, &tx, &tn), expected);
}

/// The transitivity predicate says what it should.
#[test]
fn transitivity_predicate_shape() {
    let mut env = Env::new();
    let tt = Term::apply(env.declare(0), vec![]);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::imp(
                Formula::and(Formula::mem(tb.clone(), ta.clone()), Formula::mem(ta, tt.clone())),
                Formula::mem(tb, tt.clone()),
            ),
        ),
    );
    assert_eq!(empty::transitive(&mut env, &tt), expected);
}
