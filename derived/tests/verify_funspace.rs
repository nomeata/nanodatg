//! Independent check of the payoff lemma, written from scratch.
//!
//! `⊢ ∀a. fs(a,a) ∈ U(a)` is the last set-theoretic fact the tutorial's beta
//! steps need: it is what makes `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` available.

use kernel::{Env, Formula, Term};

#[test]
fn function_space_lands_in_the_universe() {
    let mut env = Env::new();
    let dev = derived::funspace::Development::new(&mut env).expect("build the development");

    let thm = dev.in_universe.clone();
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let c = env.declare(0);
    let tc = Term::apply(c, vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&tc)).expect("instantiate");

    let expected = Formula::mem(
        Term::apply(dev.funspace.fs, vec![tc.clone(), tc.clone()]),
        Term::apply(dev.space.lu, vec![tc]),
    );
    assert_eq!(*inst.concl(), expected, "funspace_in_universe is not the statement it claims");

    // Non-vacuity: the two sides must be genuinely different terms, or the
    // statement would be saying something trivial about one object.
    let (elem, set) = inst.concl().as_mem().expect("should be a membership");
    assert_ne!(elem, set, "membership of a thing in itself — the lemma would be vacuous");
}
