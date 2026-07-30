//! Does `fs(a,b)`'s membership condition genuinely depend on `a` and `b`?
//!
//! Written because the summary statement `f ∈ fs(a,b) ↔ isfun(f)` reads as if
//! the right-hand side ignores the parameters. It does not — `isfun` is
//! shorthand for a formula mentioning both — but that is worth checking rather
//! than asserting.

use kernel::{Env, Formula, Term};

#[test]
fn funspace_membership_depends_on_both_parameters() {
    let mut env = Env::new();
    let dev = derived::funspace::Development::new(&mut env).expect("development");

    let (a, b, b2, f) = (env.declare(0), env.declare(0), env.declare(0), env.declare(0));
    let (ta, tb, tb2, tf) =
        (Term::apply(a, vec![]), Term::apply(b, vec![]), Term::apply(b2, vec![]), Term::apply(f, vec![]));

    let at_b = derived::inst_all(&dev.funspace.fs_ax, &[ta.clone(), tb.clone(), tf.clone()]).expect("inst b");
    let at_b2 = derived::inst_all(&dev.funspace.fs_ax, &[ta.clone(), tb2.clone(), tf.clone()]).expect("inst b2");

    // Pull out the right-hand side of each biconditional. `p ↔ q` is
    // `¬((p→q) → ¬(q→p))`, so the forward implication's consequent is the RHS.
    let rhs = |t: &kernel::Thm| -> Formula {
        let (inner, _) = t.concl().as_imp().expect("iff is an implication to falsity");
        let (fwd, _) = inner.as_imp().expect("forward half");
        let (_, q) = fwd.as_imp().expect("p → q");
        q
    };
    let (r1, r2) = (rhs(&at_b), rhs(&at_b2));

    // If the condition ignored `b`, these would be identical.
    assert_ne!(r1, r2, "fs's membership condition does not depend on the codomain — that would be wrong");

    // And it must mention the domain too: swapping `a` changes it as well.
    let at_a2 = derived::inst_all(&dev.funspace.fs_ax, &[tb.clone(), tb.clone(), tf]).expect("inst a2");
    assert_ne!(rhs(&at_a2), r1, "fs's membership condition does not depend on the domain");
}
