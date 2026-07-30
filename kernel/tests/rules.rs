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

/// Symmetry is derived, not primitive — check it actually produces `b = a`.
#[test]
fn eq_symm_derives() {
    let mut env = Env::new();
    let f = env.declare(1);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));

    // Manufacture a proof of `f(a) = f(a)`, then check symm gives the same
    // thing back (a = b with a syntactically equal to b).
    let refl = Thm::eq_refl(Term::apply(f, vec![ta.clone()]));
    let sym = Thm::eq_symm(&mut env, &refl).expect("symm failed on reflexivity");
    assert_eq!(*sym.concl(), Formula::eq(Term::apply(f, vec![ta]), Term::apply(f, vec![Term::var(a)])));

    // symm must refuse a non-equation.
    let k = Thm::ax_k(Formula::eq(Term::var(a), tb.clone()), Formula::false_());
    assert!(Thm::eq_symm(&mut env, &k).is_none(), "symm accepted a non-equation");
}

/// Transitivity must refuse to chain equations whose middles differ.
#[test]
fn eq_trans_rejects_mismatched_middle() {
    let mut env = Env::new();
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let ra = Thm::eq_refl(Term::var(a));
    let rb = Thm::eq_refl(Term::var(b));
    // a = a and b = b do not compose.
    assert!(Thm::eq_trans(&mut env, &ra, &rb).is_none(), "trans chained mismatched equations");
    // a = a with a = a does.
    assert!(Thm::eq_trans(&mut env, &ra, &ra).is_some());
}

/// Congruence in one argument.
#[test]
fn congr_arg_rewrites_the_named_position() {
    let mut env = Env::new();
    let f = env.declare(2);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));

    let args = vec![ta.clone(), tb.clone()];
    let refl_a = Thm::eq_refl(ta.clone());
    let c = Thm::congr_arg(&mut env, f, &args, 0, &refl_a).expect("congr_arg failed");
    assert_eq!(*c.concl(), Formula::eq(Term::apply(f, args.clone()), Term::apply(f, args.clone())));

    // Rewriting a position whose current argument is not the equation's LHS
    // must be refused — otherwise congruence would rewrite the wrong subterm.
    assert!(Thm::congr_arg(&mut env, f, &args, 1, &refl_a).is_none(), "congr_arg rewrote a non-matching position");
    // Out-of-range index.
    assert!(Thm::congr_arg(&mut env, f, &args, 9, &refl_a).is_none());
}

/// Full congruence over all arguments.
#[test]
fn congr_all_arguments() {
    let mut env = Env::new();
    let f = env.declare(2);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let eqs = vec![Thm::eq_refl(Term::var(a)), Thm::eq_refl(Term::var(b))];
    let c = Thm::congr(&mut env, f, &eqs).expect("congr failed");
    let expected = Term::apply(f, vec![Term::var(a), Term::var(b)]);
    assert_eq!(*c.concl(), Formula::eq(expected.clone(), expected));

    // Wrong arity must be refused.
    let g = env.declare(3);
    assert!(Thm::congr(&mut env, g, &eqs).is_none(), "congr ignored arity");
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
#[test]
fn set_axioms_are_wellformed() {
    let mut env = Env::new();
    let axioms = vec![
        Thm::ax_extensionality(&mut env),
        Thm::ax_pairing(&mut env),
        Thm::ax_union(&mut env),
        Thm::ax_power(&mut env),
        Thm::ax_regularity(&mut env),
        Thm::ax_tarski_incomplete(&mut env),
    ];
    for ax in &axioms {
        assert!(kernel::thm::debug_locally_closed(ax.concl()), "axiom has a dangling bound variable: {:?}", ax.concl());
    }
}
