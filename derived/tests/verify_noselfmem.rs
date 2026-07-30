//! Independent check of `no_self_mem`, the one unconditional set-theoretic
//! theorem to come out of the empty-set work.
//!
//! Written from scratch: if `⊢ ∀x. ¬(x ∈ x)` really is derived, it is a genuine
//! consequence of Regularity and worth pinning independently.

use kernel::{Env, Formula, Term};

#[test]
fn no_self_membership_is_derived() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, up, &up_ax).expect("mem_singleton");
    let thm = derived::empty::no_self_mem(&mut env, up, &mem_sing).expect("no_self_mem should derive");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let c = env.declare(0);
    let tc = Term::apply(c, vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&tc)).expect("instantiate");

    // ¬(c ∈ c), i.e. (c ∈ c) → ⊥
    let expected = Formula::not(Formula::mem(tc.clone(), tc));
    assert_eq!(*inst.concl(), expected, "no_self_mem is not the statement it claims");

    // And it must genuinely be a negation, not something vacuous.
    let (ante, conseq) = inst.concl().as_imp().expect("negation is an implication to falsity");
    assert_eq!(conseq, Formula::false_());
    assert!(ante.as_mem().is_some(), "the negated formula should be a membership");
}
