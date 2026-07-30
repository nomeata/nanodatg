//! Independent check of the universe operator's key property.
//!
//! `⊢ ∀x. x ∈ U(x)` is the shape the Lean interpretation needs: taking
//! `⟦Sort (n+1)⟧ := U(⟦Sort n⟧)` makes `⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧` immediate,
//! which is exactly the typing premise beta requires.

use kernel::{Env, Formula, Term};

#[test]
fn membership_in_own_least_universe() {
    let mut env = Env::new();
    let (u_sym, u_ax) = derived::universe::least_universe(&mut env).expect("least_universe");
    let thm = derived::universe::mem_least_universe(&mut env, u_sym, &u_ax).expect("mem_least_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let c = env.declare(0);
    let tc = Term::apply(c, vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&tc)).expect("instantiate");

    let expected = Formula::mem(tc.clone(), Term::apply(u_sym, vec![tc.clone()]));
    assert_eq!(*inst.concl(), expected, "mem_least_universe is not the statement it claims");

    // The tower step the interpretation would rely on: U(x) ∈ U(U(x)).
    let ux = Term::apply(u_sym, vec![tc]);
    let step = derived::inst_all(&thm, std::slice::from_ref(&ux)).expect("instantiate at U(x)");
    assert_eq!(*step.concl(), Formula::mem(ux.clone(), Term::apply(u_sym, vec![ux])));
}
