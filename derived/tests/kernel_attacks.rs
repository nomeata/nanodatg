//! Regression guards for soundness holes found by adversarial review.
//!
//! Both were demonstrated with a real derivation of `⊥` before being fixed.
//! Neither was found by the test suite — they were found by reading the trusted
//! code with the intent to break it. These tests exist so they stay fixed.

use kernel::{Env, Formula, Term, Thm};

/// **Replacement with `x == y`.**
///
/// The image `∃x. (x ∈ a ∧ φ)` closes over `y` as well when the two variables
/// coincide, so the right-hand side of the `↔` stops mentioning the quantified
/// variable and the conclusion degenerates to `∃b ∀y. (y ∈ b ↔ <y-free>)` — a
/// universal set whenever that formula holds, which Regularity refutes.
#[test]
fn replacement_refuses_a_single_variable_for_both_roles() {
    let mut env = Env::new();
    let (x, w) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::eq(Term::var(x), Term::var(w));

    assert!(
        Thm::ax_replacement(&mut env, x, x, phi.clone()).is_none(),
        "replacement accepted one variable for both roles — that yields a universal set"
    );
    // Distinct variables must still be accepted, so this is a side condition
    // rather than a blanket ban.
    let y = env.fresh_var();
    assert!(Thm::ax_replacement(&mut env, x, y, phi).is_some(), "replacement rejected a valid instance");
}

/// **Cross-environment symbol collision.**
///
/// Two `Env`s each start their symbol counter at zero. Without a brand, symbol
/// `k` from one would compare equal to symbol `k` from another, letting a client
/// hold two *contradictory* defining axioms for what the kernel regards as one
/// symbol — from which `⊢ ⊥` follows.
#[test]
fn symbols_from_different_environments_are_distinct() {
    let mut a = Env::new();
    let mut b = Env::new();
    let (fa, fb) = (a.declare(1), b.declare(1));
    assert_ne!(fa, fb, "symbol 0 of one environment equals symbol 0 of another");

    // Same within a single environment: successive declarations differ.
    let fa2 = a.declare(1);
    assert_ne!(fa, fa2);
}

/// **Cross-environment variable collision.**
///
/// The inference rules generate variables they assume are fresh
/// (`ax_replacement`'s `a`/`b`/`y2`, `exists_unique`'s `y2`). A variable minted
/// by another generator must not be able to alias one of those.
#[test]
fn variables_from_different_environments_are_distinct() {
    let mut a = Env::new();
    let mut b = Env::new();
    assert_ne!(a.fresh_var(), b.fresh_var(), "variable 0 of one environment equals variable 0 of another");
}

/// `VarGen` must not be publicly constructible.
///
/// The sharper form of the collision attack used `VarGen::new()` to mint a
/// variable aliasing one `ax_replacement` was about to generate, defeating a
/// client who was careful to use a single `Env`. Making the generator private
/// removes that route entirely: every `FreeVar` now comes from an `Env` and
/// carries its brand.
///
/// This is a compile-time property, so the guard is a source check.
#[test]
fn vargen_is_not_publicly_constructible() {
    let src = include_str!("../../kernel/src/term.rs");
    assert!(
        src.contains("pub(crate) struct VarGen"),
        "VarGen must stay crate-private — a public generator lets a client mint variables \
         that collide with ones the inference rules assume fresh"
    );
    let lib = include_str!("../../kernel/src/lib.rs");
    assert!(!lib.contains("VarGen"), "VarGen must not be re-exported from the kernel root");
}
