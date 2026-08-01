//! Tests for the inference rules.
//!
//! The negative tests matter most: a rule that fires when it should not is an
//! unsoundness, whereas a rule that fails to fire is merely a rejection.

use kernel::{Env, Formula, Term, Thm};

/// Modus ponens must refuse premises that do not line up. If it did not, any
/// formula whatsoever could be concluded from an unrelated implication.
#[test]
fn mp_rejects_mismatched_premises() {
    let mut env = Env::new();
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (pa, pb, pc) = (
        Formula::mem(Term::var(a), Term::var(a)),
        Formula::mem(Term::var(b), Term::var(b)),
        Formula::mem(Term::var(c), Term::var(c)),
    );

    // ⊢ pa → (pb → pa)
    let k = Thm::ax_k(pa.clone(), pb.clone());
    // Feeding it a proof of pc — which is not pa — must fail.
    let bogus = Thm::eq_refl(Term::var(c));
    assert!(Thm::mp(&k, &bogus).is_none(), "mp accepted a mismatched antecedent");

    // Also: mp on something that is not an implication at all.
    let refl = Thm::eq_refl(Term::var(a));
    assert!(Thm::mp(&refl, &bogus).is_none(), "mp accepted a non-implication");
    let _ = pc;
}

/// The distribution axiom's side condition is real: `∀x.(φ → ψ) → (φ → ∀x.ψ)`
/// is only valid when `x` is not free in `φ`. Dropping the check would let a
/// still-constrained variable be generalised.
#[test]
fn ax_dist_enforces_side_condition() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), Term::var(x)); // x IS free here
    let psi = Formula::eq(Term::var(x), Term::var(x));

    assert!(Thm::ax_dist(x, phi, psi.clone()).is_none(), "ax_dist ignored its free-variable side condition");

    // With a φ that genuinely does not mention x, it must succeed.
    let y = env.fresh_var();
    let ok_phi = Formula::mem(Term::var(y), Term::var(y));
    assert!(Thm::ax_dist(x, ok_phi, psi).is_some(), "ax_dist rejected a valid instance");
}

/// Instantiation only applies to universally quantified formulas.
#[test]
fn ax_inst_requires_a_quantifier() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let not_forall = Formula::eq(Term::var(x), Term::var(x));
    assert!(Thm::ax_inst(not_forall, Term::var(x)).is_none());
}

/// Instantiating `∀x. x = x` at `t` yields exactly `t = t`.
#[test]
fn ax_inst_substitutes_correctly() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let all = Formula::forall(x, Formula::eq(Term::var(x), Term::var(x)));
    let thm = Thm::ax_inst(all.clone(), Term::var(y)).unwrap();
    let expected = Formula::imp(all, Formula::eq(Term::var(y), Term::var(y)));
    assert_eq!(*thm.concl(), expected);
}

/// A worked derivation exercising the primitives together: `⊢ φ → φ`, the
/// classic Hilbert-system warm-up, from A1 and A2 by modus ponens twice.
#[test]
fn derives_identity_implication() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), Term::var(x));

    // A2 with ψ := (φ → φ), χ := φ
    let step1 = Thm::ax_s(phi.clone(), Formula::imp(phi.clone(), phi.clone()), phi.clone());
    // A1: φ → ((φ → φ) → φ)
    let step2 = Thm::ax_k(phi.clone(), Formula::imp(phi.clone(), phi.clone()));
    let step3 = Thm::mp(&step1, &step2).expect("first mp");
    // A1: φ → (φ → φ)
    let step4 = Thm::ax_k(phi.clone(), phi.clone());
    let result = Thm::mp(&step3, &step4).expect("second mp");

    assert_eq!(*result.concl(), Formula::imp(phi.clone(), phi), "did not derive φ → φ");
}

/// The set axioms are well-formed (locally closed, no dangling indices).
///
/// **This comment used to read "Tarski's Axiom A is absent: it was removed for
/// inconsistency". That was false** — the axiom is present, at
/// `Thm::ax_tarski`. What was removed, in 2026-07, was an *earlier and
/// inconsistent statement* of its inaccessibility clause; the axiom was restored
/// with the `y ≈ u` disjunct and later strengthened with transitivity. See
/// `tarski_regression.rs`.
///
/// The error is worth recording rather than silently deleting: a false comment
/// in the *test file* of the one axiom whose historical bug was itself caused by
/// a false comment.
///
/// What this test pins about `ax_tarski` is only well-formedness plus a
/// non-triviality check on `equinumerous`, which is *not* enough — that gap is
/// now closed by `tarski.rs`, which rebuilds the whole five-clause axiom from
/// the constructors in the style of `choice.rs`, and by `replacement.rs`, which
/// does the same for the other formula-valued axiom. Read those before changing
/// either axiom; this file is the weak guard, not the strong one.
#[test]
fn set_axioms_are_wellformed() {
    let mut env = Env::new();
    let axioms = vec![
        Thm::ax_extensionality(&mut env),
        Thm::ax_pairing(&mut env),
        Thm::ax_union(&mut env),
        Thm::ax_power(&mut env),
        Thm::ax_regularity(&mut env),
    ];
    for ax in &axioms {
        assert!(kernel::thm::debug_locally_closed(ax.concl()), "axiom has a dangling bound variable: {:?}", ax.concl());
    }
}

/// Tarski's Axiom A is well-formed, and — the point of the exercise — its
/// inaccessibility clause is a genuine *disjunction*. The previous version
/// dropped the `y ≈ u` alternative, which made it inconsistent with Regularity.
#[test]
fn tarski_axiom_is_wellformed_and_disjunctive() {
    let mut env = Env::new();
    let ax = Thm::ax_tarski(&mut env);
    assert!(kernel::thm::debug_locally_closed(ax.concl()), "Tarski's axiom has a dangling bound variable");

    // Equinumerosity must be a non-trivial formula mentioning membership, not a
    // placeholder that would collapse the disjunction back to the fatal form.
    let (x, m) = (env.fresh_var(), env.fresh_var());
    let equi = kernel::thm::equinumerous(&mut env, Term::var(x), Term::var(m));
    assert!(kernel::thm::debug_locally_closed(&equi));
    assert_ne!(equi, Formula::false_(), "equinumerosity collapsed to falsity — the disjunct would be vacuous");
    assert!(equi.occurs_free(x) && equi.occurs_free(m), "equinumerosity ignores one of its arguments");
}

/// `⟨a,b⟩` described as a formula really does pin down both components: the
/// description must mention each of them.
#[test]
fn opair_description_mentions_both_components() {
    let mut env = Env::new();
    let (p, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let f = kernel::thm::is_opair(&mut env, Term::var(p), Term::var(a), Term::var(b));
    assert!(kernel::thm::debug_locally_closed(&f));
    assert!(f.occurs_free(p) && f.occurs_free(a) && f.occurs_free(b));
}

/// There is **no** empty-set axiom, and there must not be one again.
///
/// `Thm::ax_empty` was deleted on 2026-07-31 once `ax_tarski`'s transitivity
/// clause made `∃e ∀z. ¬(z ∈ e)` derivable — see the note where it used to sit
/// in `thm.rs`, and `derived::empty::empty_existence` for the derivation. A
/// deleted axiom is only worth deleting if it stays deleted, and the kernel has
/// no way to notice a new `pub fn ax_…` appearing, so this reads the source in
/// the same style as `tarski_regression.rs`.
///
/// The shape check the old test performed — that the axiom was an existential
/// rather than the catastrophic universal "every set is empty" — now lives on
/// the derived theorem, in `derived/tests/empty.rs`.
#[test]
fn there_is_no_empty_set_axiom() {
    let src = include_str!("../src/thm.rs");
    for (n, line) in src.lines().enumerate() {
        let code = line.split("//").next().unwrap_or("");
        assert!(
            !code.contains("fn ax_empty"),
            "kernel/src/thm.rs:{}: the empty-set axiom is back — it is derivable, see \
             derived::empty::empty_existence",
            n + 1
        );
    }
}
