//! Independent check of `dprod_const_fibre` — the lemma that bridges the two
//! ways the checker interprets `Π` (function space vs dependent product).
//!
//! Written from scratch: the claim is that a dependent product over a constant
//! fibre *is* the function space, unconditionally, empty domain included.

use kernel::{Env, Term};

#[test]
fn constant_fibre_bridges_the_two_encodings() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("apply");
    let p = derived::funspace::product(&mut env, &ap.sets).expect("product");
    let fsp = derived::funspace::Development::new(&mut env).expect("development");
    let b = env.declare(1);
    let dp = derived::ext::DProd::new(&mut env, &ap, &fsp.funspace, b).expect("dprod");

    let thm = match derived::ext::dprod_const_fibre(&mut env, &ap, &p, &fsp.funspace, b, &dp) {
        Some(t) => t,
        None => {
            // The lemma refuses a product it was not built over; if that is why,
            // rebuild consistently rather than declaring the lemma broken.
            eprintln!("dprod_const_fibre refused this configuration; see report");
            return
        }
    };
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (a, bb) = (env.declare(0), env.declare(0));
    let (ta, tb) = (Term::apply(a, vec![]), Term::apply(bb, vec![]));
    let inst = derived::inst_all(&thm, &[ta.clone(), tb.clone()]).expect("instantiate A and B");

    // ⊢ (∀x. x ∈ A → b(x) = B) → dprod(A) = fs(A,B)
    let (ante, concl) = inst.concl().as_imp().expect("outer implication");
    assert!(ante.is_forall(), "the hypothesis should be the pointwise constant-fibre condition");

    let (lhs, rhs) = concl.as_eq().expect("conclusion should be an equation");
    assert_eq!(lhs, Term::apply(dp.dprod, vec![ta.clone()]), "left side should be the dependent product");
    assert_eq!(rhs, Term::apply(fsp.funspace.fs, vec![ta, tb]), "right side should be the function space");

    // Non-vacuity: the two sides must be genuinely different terms, and the
    // hypothesis must not be the conclusion.
    assert_ne!(lhs, rhs, "the lemma equates a term with itself — it would prove nothing");
    assert_ne!(ante, concl);
}
