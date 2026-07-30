//! Independent verification of `beta_conditional`, written without reference to
//! the agent's own tests.
//!
//! The type system guarantees a `Thm` is derivable. It does *not* guarantee the
//! statement is the one we want, nor that it is non-vacuous. Both are checked
//! here from scratch.

use kernel::{Env, Formula, Term};

#[test]
fn beta_conditional_is_the_statement_it_claims() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("application");

    // A body: an arbitrary unary function symbol standing for the interpretation
    // of a lambda body with its bound variable abstracted.
    let t = env.declare(1);
    let (lam, lam_ax) = derived::funcs::lambda(&mut env, &ap, t).expect("lambda graph");
    let beta = derived::funcs::beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta");

    // Instantiate at two fresh constants and rebuild the expected statement.
    let (a_dom, a_arg) = (env.declare(0), env.declare(0));
    let (dom, arg) = (Term::apply(a_dom, vec![]), Term::apply(a_arg, vec![]));
    let inst = derived::inst_all(&beta, &[dom.clone(), arg.clone()]).expect("instantiate A and a");

    let expected = Formula::imp(
        Formula::mem(arg.clone(), dom.clone()),
        Formula::eq(
            Term::apply(ap.app, vec![Term::apply(lam, vec![dom.clone()]), arg.clone()]),
            Term::apply(t, vec![arg.clone()]),
        ),
    );
    assert_eq!(*inst.concl(), expected, "beta_conditional is not the statement it claims");

    // Non-vacuity: the antecedent must be a real membership claim, not something
    // trivially false that would make the implication say nothing.
    let (ante, _) = inst.concl().as_imp().unwrap();
    let (m_elem, m_set) = ante.as_mem().expect("antecedent should be a membership");
    assert_eq!(m_elem, arg);
    assert_eq!(m_set, dom);

    // And the two sides of the equation must be genuinely different terms —
    // otherwise the conclusion would be reflexivity in disguise.
    let (_, concl) = inst.concl().as_imp().unwrap();
    let (lhs, rhs) = concl.as_eq().expect("conclusion should be an equation");
    assert_ne!(lhs, rhs, "beta's conclusion is reflexivity in disguise — it proves nothing");
}
