//! Independent check that Separation is now a real, unconditional theorem.
//!
//! Separation is *derived*, not axiomatic — the kernel has Replacement and no
//! Separation. It was uncallable until the empty-set axiom arrived, because
//! Separation at a refutable condition **is** the empty-set axiom.

use kernel::{Env, Formula, Term};

#[test]
fn separation_is_unconditional() {
    let mut env = Env::new();
    let (empty_sym, empty_ax) = derived::empty::empty(&mut env);

    // ∅ really has no members.
    let z0 = env.fresh_var();
    let inst = derived::inst_all(&empty_ax, &[Term::var(z0)]).expect("instantiate emptiness");
    assert_eq!(
        *inst.concl(),
        Formula::not(Formula::mem(Term::var(z0), Term::apply(empty_sym, vec![]))),
        "the empty-set symbol does not have the property it claims"
    );

    // Separate a set by a concrete condition: φ(x) := x ∈ c.
    let x = env.fresh_var();
    let c = env.declare(0);
    let phi = Formula::mem(Term::var(x), Term::apply(c, vec![]));
    let (sep, thm) = derived::separation::separation(&mut env, x, &phi, &empty_ax)
        .expect("separation should now be callable");

    // ⊢ ∀a ∀z. (z ∈ sep(a) ↔ (z ∈ a ∧ φ(z))) — with NO antecedent.
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    let (a, zz) = (env.declare(0), env.declare(0));
    let (ta, tz) = (Term::apply(a, vec![]), Term::apply(zz, vec![]));
    let i = derived::inst_all(&thm, &[ta.clone(), tz.clone()]).expect("instantiate a and z");

    let expected = Formula::iff(
        Formula::mem(tz.clone(), Term::apply(sep, vec![ta.clone()])),
        Formula::and(Formula::mem(tz.clone(), ta), Formula::mem(tz, Term::apply(c, vec![]))),
    );
    assert_eq!(*i.concl(), expected, "separation is not the statement it claims");

    // And it must genuinely be a biconditional, not an implication carrying a
    // hidden antecedent — that was the shape of the old conditional version.
    assert!(i.concl().as_imp().is_some(), "an iff is encoded as a conjunction of implications");
}
