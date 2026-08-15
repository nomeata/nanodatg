//! Tests for the derived rules.
//!
//! These are not trusted code, but they are load-bearing: every derivation the
//! backend builds goes through them, and a derived rule that silently produces
//! the wrong conclusion would turn into a rejection storm rather than an
//! obvious failure.

use kernel::{Env, Formula, Term, Thm};

#[test]
fn eq_symm_derives() {
    let mut env = Env::new();
    let f = env.declare(1);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));

    // **The equation is asymmetric, and that is what makes this a test of
    // `symm`.** It used to run only at `f(a) = f(a)` — the comment said so
    // outright, "a = b with a syntactically equal to b" — where the conclusion
    // is its own converse, so an `eq_symm` that returned its input untouched
    // passed. `Thm::assume` gives `{a = b} ⊢ a = b` with the two sides
    // syntactically different, and symm must hand back `{a = b} ⊢ b = a`.
    let asym = Thm::assume(Formula::eq(ta.clone(), tb.clone()));
    let sym = derived::eq_symm(&mut env, &asym).expect("symm failed on an assumed equation");
    assert_eq!(*sym.concl(), Formula::eq(tb.clone(), ta.clone()), "symm did not swap the sides");
    assert_eq!(sym.hyps(), asym.hyps(), "symm did not carry the assumption through");

    // …and it still handles the reflexive case, where the converse is the same
    // formula. Kept as a case, not as the whole test.
    let refl = Thm::eq_refl(Term::apply(f, vec![ta.clone()]));
    let sym_refl = derived::eq_symm(&mut env, &refl).expect("symm failed on reflexivity");
    assert_eq!(
        *sym_refl.concl(),
        Formula::eq(Term::apply(f, vec![ta.clone()]), Term::apply(f, vec![ta]))
    );

    // symm must refuse a non-equation.
    let k = Thm::ax_k(Formula::eq(Term::var(a), tb.clone()), Formula::false_());
    assert!(derived::eq_symm(&mut env, &k).is_none(), "symm accepted a non-equation");
}

#[test]
fn eq_trans_rejects_mismatched_middle() {
    let mut env = Env::new();
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let ra = Thm::eq_refl(Term::var(a));
    let rb = Thm::eq_refl(Term::var(b));
    // a = a and b = b do not compose.
    assert!(derived::eq_trans(&mut env, &ra, &rb).is_none(), "trans chained mismatched equations");
    // a = a with a = a does.
    assert!(derived::eq_trans(&mut env, &ra, &ra).is_some());
}

#[test]
fn congr_arg_rewrites_the_named_position() {
    let mut env = Env::new();
    let f = env.declare(2);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));

    let args = vec![ta.clone(), tb.clone()];
    let refl_a = Thm::eq_refl(ta.clone());
    let c = derived::congr_arg(&mut env, f, &args, 0, &refl_a).expect("congr_arg failed");
    assert_eq!(*c.concl(), Formula::eq(Term::apply(f, args.clone()), Term::apply(f, args.clone())));

    // Rewriting a position whose current argument is not the equation's LHS
    // must be refused — otherwise congruence would rewrite the wrong subterm.
    assert!(derived::congr_arg(&mut env, f, &args, 1, &refl_a).is_none(), "congr_arg rewrote a non-matching position");
    // Out-of-range index.
    assert!(derived::congr_arg(&mut env, f, &args, 9, &refl_a).is_none());
}

#[test]
fn congr_all_arguments() {
    let mut env = Env::new();
    let f = env.declare(2);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let eqs = vec![Thm::eq_refl(Term::var(a)), Thm::eq_refl(Term::var(b))];
    let c = derived::congr(&mut env, f, &eqs).expect("congr failed");
    let expected = Term::apply(f, vec![Term::var(a), Term::var(b)]);
    assert_eq!(*c.concl(), Formula::eq(expected.clone(), expected));

    // Wrong arity must be refused.
    let g = env.declare(3);
    assert!(derived::congr(&mut env, g, &eqs).is_none(), "congr ignored arity");
}
