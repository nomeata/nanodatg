//! Independent check of `dprod_ext`, the lemma `pi_cong` will rest on.
//!
//! `⟦Π⟧` is a dependent product whose head symbol depends on the fibre's shape,
//! so plain congruence over sub-terms does not give the claim — the same
//! situation `lam_ext` fixed for lambdas.

use kernel::{Env, Formula, Term};

#[test]
fn dependent_product_extensionality_statement() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("apply");
    let fsp = derived::funspace::Development::new(&mut env).expect("funspace development");

    // Two distinct unary fibre symbols.
    let (b1, b2) = (env.declare(1), env.declare(1));
    let d1 = derived::ext::DProd::new(&mut env, &ap, &fsp.funspace, b1).expect("dprod 1");
    let d2 = derived::ext::DProd::new(&mut env, &ap, &fsp.funspace, b2).expect("dprod 2");

    let thm = derived::ext::dprod_ext(&mut env, &ap, &fsp.funspace, b1, &d1, b2, &d2)
        .expect("dprod_ext should derive");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // Instantiate at two constants and rebuild the expected statement.
    let (a, a2) = (env.declare(0), env.declare(0));
    let (ta, ta2) = (Term::apply(a, vec![]), Term::apply(a2, vec![]));
    let inst = derived::inst_all(&thm, &[ta.clone(), ta2.clone()]).expect("instantiate");

    // ⊢ A = A' → ((∀x. x ∈ A → b(x) = b'(x)) → dprod(A) = dprod'(A'))
    let (eq_dom, rest) = inst.concl().as_imp().expect("outer implication");
    assert_eq!(eq_dom, Formula::eq(ta.clone(), ta2.clone()), "antecedent should be domain equality");
    let (pointwise, concl) = rest.as_imp().expect("inner implication");
    assert!(pointwise.is_forall(), "the second hypothesis should be pointwise, i.e. universally quantified");
    assert_eq!(
        concl,
        Formula::eq(Term::apply(d1.dprod, vec![ta]), Term::apply(d2.dprod, vec![ta2])),
        "conclusion should equate the two dependent products"
    );

    // Non-vacuity: the two products must be different terms, else the lemma
    // would be reflexivity wearing a disguise.
    let (l, r) = concl.as_eq().unwrap();
    assert_ne!(l, r);
}
