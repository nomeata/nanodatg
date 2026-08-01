//! Infinity, derived — checked against the statement the literature writes.
//!
//! Every test pins the **exact** conclusion of the theorem it covers, rebuilt
//! from the kernel's `Formula`/`Term` constructors rather than by calling the
//! helper the derivation itself used, and several check that the statement is
//! not satisfied vacuously.

use derived::empty::induction::least_inductive_set_exists;
use derived::funcs::Sets;
use derived::infinity::{self, Infinity};
use derived::recursion;
use kernel::{Env, FnSym, Formula, Term, Thm};

/// `0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I)`, rebuilt by hand.
fn textbook_matrix(env: &mut Env, zero: &Term, succ: FnSym, i: &Term) -> Formula {
    let n = env.fresh_var();
    let tn = Term::var(n);
    Formula::and(
        Formula::mem(zero.clone(), i.clone()),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), i.clone()),
                Formula::mem(Term::apply(succ, vec![tn]), i.clone()),
            ),
        ),
    )
}

/// `∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b)))`, rebuilt by hand.
fn two_members(env: &mut Env, i: &Term) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    Formula::exists(
        a,
        Formula::exists(
            b,
            Formula::and(
                Formula::mem(ta.clone(), i.clone()),
                Formula::and(
                    Formula::mem(tb.clone(), i.clone()),
                    Formula::not(Formula::eq(ta, tb)),
                ),
            ),
        ),
    )
}

/// `⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))` — Jech, *Set Theory* §1
/// (`∃S (∅ ∈ S ∧ (∀x ∈ S)(x ∪ {x} ∈ S))`) and Kunen, *Set Theory* I.2 Axiom 7
/// (`∃x (0 ∈ x ∧ ∀y ∈ x (S(y) ∈ x))`), with the bounded quantifier expanded.
#[test]
fn infinity_is_the_textbook_statement() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");
    assert!(kernel::thm::debug_locally_closed(inf.statement.concl()));
    assert!(inf.statement.hyps().is_empty(), "Infinity must be unconditional");

    let i = env.fresh_var();
    let ti = Term::var(i);
    let matrix = textbook_matrix(&mut env, &inf.zero(), inf.succ, &ti);
    assert_eq!(
        *inf.statement.concl(),
        Formula::exists(i, matrix),
        "infinity has the wrong shape"
    );
}

/// The same sentence with `∅` and `succ` eliminated: no function symbol occurs
/// in it at all.
///
/// The expected formula below is built **only** from `Term::var`, so the
/// `assert_eq!` passing is itself the proof that the theorem mentions no
/// function symbol — it is a sentence of the pure language of `∈`, which is
/// what makes "Infinity needs no axiom" independent of the conservativity of
/// the definitional extensions that introduced `∅` and `succ`.
#[test]
fn the_primitive_form_lives_in_the_language_of_membership() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");
    assert!(kernel::thm::debug_locally_closed(inf.primitive.concl()));
    assert!(inf.primitive.hyps().is_empty());

    let (i, e, n, s) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (z1, z2) = (env.fresh_var(), env.fresh_var());
    let (ti, te, tn, ts) = (Term::var(i), Term::var(e), Term::var(n), Term::var(s));
    let (tz1, tz2) = (Term::var(z1), Term::var(z2));

    // ∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e))
    let has_empty = Formula::exists(
        e,
        Formula::and(
            Formula::mem(te.clone(), ti.clone()),
            Formula::forall(z1, Formula::not(Formula::mem(tz1, te))),
        ),
    );
    // ∀n. (n ∈ I → ∃s. (s ∈ I ∧ ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n))))
    let has_succ = Formula::forall(
        n,
        Formula::imp(
            Formula::mem(tn.clone(), ti.clone()),
            Formula::exists(
                s,
                Formula::and(
                    Formula::mem(ts.clone(), ti.clone()),
                    Formula::forall(
                        z2,
                        Formula::iff(
                            Formula::mem(tz2.clone(), ts),
                            Formula::or(
                                Formula::mem(tz2.clone(), tn.clone()),
                                Formula::eq(tz2, tn),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    let matrix = Formula::and(has_empty, has_succ);
    assert_eq!(
        *inf.primitive.concl(),
        Formula::exists(i, matrix.clone()),
        "infinity_primitive has the wrong shape"
    );

    // The exported reader agrees with the hand-built formula, so quoting
    // `is_inductive_primitive` in a downstream statement quotes this sentence.
    let ti2 = Term::var(env.fresh_var());
    assert_eq!(
        infinity::is_inductive_primitive(&mut env, &ti2),
        matrix.subst(i, &ti2),
        "is_inductive_primitive disagrees with the theorem it describes"
    );
}

/// `⊢ ∀I. (Ind(0,I) → ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))` — non-vacuity, for
/// every inductive set rather than for one chosen witness.
#[test]
fn every_inductive_set_has_two_distinct_members() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");
    assert!(kernel::thm::debug_locally_closed(inf.two_members.concl()));
    assert!(inf.two_members.hyps().is_empty());

    let i = env.fresh_var();
    let ti = Term::var(i);
    let matrix = textbook_matrix(&mut env, &inf.zero(), inf.succ, &ti);
    let concl = two_members(&mut env, &ti);
    assert_eq!(
        *inf.two_members.concl(),
        Formula::forall(i, Formula::imp(matrix, concl)),
        "inductive_two_members has the wrong shape"
    );
}

/// The witness Infinity produces is itself one of those sets: the existential
/// carries the two distinct members inside it, so nothing about the statement
/// can be satisfied by a singleton on which `succ` acts as the identity.
#[test]
fn the_witness_carries_its_own_non_vacuity() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");
    assert!(kernel::thm::debug_locally_closed(inf.nonvacuous.concl()));
    assert!(inf.nonvacuous.hyps().is_empty());

    let i = env.fresh_var();
    let ti = Term::var(i);
    let matrix = textbook_matrix(&mut env, &inf.zero(), inf.succ, &ti);
    let two = two_members(&mut env, &ti);
    assert_eq!(
        *inf.nonvacuous.concl(),
        Formula::exists(i, Formula::and(matrix, two)),
        "infinity_nonvacuous has the wrong shape"
    );

    // And the two members really are different terms: `0` and `succ(0)` are not
    // the same syntax, so the distinctness claim is not `¬(t = t)` in disguise.
    assert_ne!(inf.zero(), inf.succ_of(inf.zero()));
}

/// The weakening step refuses a premise about a *different* successor
/// operation.
///
/// `crate::empty::induction` proves the same `∃m. Least(x, m)` shape with `𝒫`
/// in place of `n ↦ n ∪ {n}`. Fed to `infinity_from_least` at the von Neumann
/// `succ` it must be rejected — otherwise the module would be relabelling the
/// power-set statement as Infinity. Fed at `𝒫` the same premise goes through,
/// which is what shows the guard discriminates on the operation rather than
/// just refusing everything.
#[test]
fn the_weakening_step_checks_which_successor_it_was_given() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, sets.up, &sets.up_ax).expect("mem_singleton");
    let (pow, pow_ax) = derived::power(&mut env);
    let (_empty, empty_ax) = derived::empty::empty(&mut env);
    let (succ, _succ_ax) = recursion::successor(&mut env, &sets, &mem_sing).expect("successor");

    let zero = {
        let z = env.fresh_var();
        let inst = derived::inst_all(&empty_ax, &[Term::var(z)]).expect("inst");
        let (mem, _) = inst.concl().as_imp().expect("imp");
        mem.as_mem().expect("mem").1
    };

    // ⊢ ∀x ∃m. Least_𝒫(x, m), instantiated at `∅`.
    let pow_least = least_inductive_set_exists(&mut env, pow, &pow_ax).expect("least (𝒫)");
    let at_zero = derived::inst_all(&pow_least, std::slice::from_ref(&zero)).expect("inst_all");

    assert!(
        infinity::infinity_from_least(&mut env, succ, &zero, &at_zero).is_none(),
        "the power-set inductive set must not pass as von Neumann Infinity"
    );
    assert!(
        infinity::infinity_from_least(&mut env, pow, &zero, &at_zero).is_some(),
        "at 𝒫 the very same premise must go through"
    );
}

/// The weakening step is independent of the theorem that feeds it: given `ω`'s
/// leastness from `recursion` and nothing else, it produces exactly Infinity.
#[test]
fn infinity_is_omega_leastness_with_the_minimality_dropped() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, sets.up, &sets.up_ax).expect("mem_singleton");
    let (pow, pow_ax) = derived::power(&mut env);
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (succ, succ_ax) = recursion::successor(&mut env, &sets, &mem_sing).expect("successor");
    let zero = Term::apply(empty, vec![]);

    let least = recursion::omega_exists(&mut env, pow, &pow_ax, succ, &succ_ax, &empty_ax)
        .expect("omega_exists");
    let thm = infinity::infinity_from_least(&mut env, succ, &zero, &least).expect("weakening");

    let i = env.fresh_var();
    let ti = Term::var(i);
    let matrix = textbook_matrix(&mut env, &zero, succ, &ti);
    assert_eq!(*thm.concl(), Formula::exists(i, matrix));
}

/// The unabbreviation step refuses a premise that is not the symbol form: a
/// `⊢ ∃I. …` whose left conjunct is not `∅ ∈ I` cannot be dressed up as
/// Infinity.
#[test]
fn the_unabbreviation_step_checks_its_premise() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");

    // A theorem of the right *outer* shape and the wrong inner one: Infinity's
    // own primitive form is an `∃I.(… ∧ …)`, but its left conjunct is an
    // existential rather than `∅ ∈ I`.
    assert!(
        infinity::infinity_primitive(
            &mut env,
            inf.succ,
            &inf.succ_ax,
            &inf.empty_ax,
            &inf.primitive,
        )
        .is_none(),
        "infinity_primitive must reject a premise that is not the symbol form"
    );
}

/// `∅` and `succ` are read off the theorems that characterise them, so a
/// mismatched pair cannot slip through.
#[test]
fn the_empty_set_is_read_off_its_own_theorem() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");

    // `⊢ ∀z. ¬(z ∈ z)` has the right quantifier prefix but its body is not
    // `¬(z ∈ e)` for any `e` free of `z`.
    let bogus = {
        let sets = &inf.sets;
        let mem_sing = derived::mem_singleton(&mut env, sets.up, &sets.up_ax).expect("mem_sing");
        derived::empty::no_self_mem(&mut env, sets.up, &mem_sing).expect("no_self_mem")
    };
    assert!(
        infinity::infinity_primitive(&mut env, inf.succ, &inf.succ_ax, &bogus, &inf.statement)
            .is_none(),
        "a theorem that is not `∀z. ¬(z ∈ ∅)` must be rejected"
    );
    assert!(
        infinity::inductive_two_members(&mut env, inf.succ, &inf.succ_ax, &bogus, &bogus).is_none(),
        "a theorem that is not `∀z. ¬(z ∈ ∅)` must be rejected"
    );
}

/// The whole development is one chain of definitional extensions, so the `∅`
/// in Infinity is the `∅` in `ω` and the `succ` is the same symbol too.
#[test]
fn infinity_shares_its_symbols_with_omega() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let inf = Infinity::with_sets(&mut env, sets).expect("Infinity::with_sets");

    // `succ` is a genuine unary symbol, and `succ(0)` is not the term `0`.
    assert_eq!(inf.succ.arity(), 1);
    assert_ne!(inf.succ_of(inf.zero()), inf.zero());

    // The characteristic theorem of `succ` is the membership condition, at the
    // same symbol Infinity's statement mentions.
    let (n, z) = (env.fresh_var(), env.fresh_var());
    let (tn, tz) = (Term::var(n), Term::var(z));
    let expected = Formula::forall(
        n,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::apply(inf.succ, vec![tn.clone()])),
                Formula::or(Formula::mem(tz.clone(), tn.clone()), Formula::eq(tz, tn)),
            ),
        ),
    );
    assert_eq!(*inf.succ_ax.concl(), expected);
}

/// Nothing in the module is an assumption: every exported theorem has an empty
/// hypothesis list, and none of them is `Thm::assume` in disguise.
#[test]
fn nothing_is_assumed() {
    let mut env = Env::new();
    let inf = Infinity::new(&mut env).expect("Infinity::new");
    for (name, thm) in [
        ("statement", &inf.statement),
        ("primitive", &inf.primitive),
        ("two_members", &inf.two_members),
        ("nonvacuous", &inf.nonvacuous),
    ] {
        assert!(thm.hyps().is_empty(), "{name} carries a hypothesis");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "{name} is not closed");
        assert_ne!(
            *thm.concl(),
            Formula::false_(),
            "{name} must not be trivial"
        );
    }
    // A sanity check on the harness itself: an assumption *would* be visible.
    let phi = Formula::mem(Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    assert!(!Thm::assume(phi).hyps().is_empty());
}
