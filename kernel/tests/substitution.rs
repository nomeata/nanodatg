//! Adversarial tests for binding, closing, opening and substitution.
//!
//! Capture-avoiding substitution is the classic soundness hole in an LCF
//! kernel, and Metamath's whole distinct-variable apparatus exists because of
//! it. These tests are deliberately written to *try to induce capture* rather
//! than to confirm the happy path — the negative assertions are the point.

use kernel::{Formula, Term, VarGen};

fn setup() -> (VarGen, kernel::FreeVar, kernel::FreeVar, kernel::FreeVar) {
    let mut g = VarGen::new();
    let (x, y, z) = (g.fresh(), g.fresh(), g.fresh());
    (g, x, y, z)
}

/// The central capture test.
///
/// Take `∀y. x = y` and substitute `y` for `x`. A naive named implementation
/// produces `∀y. y = y` — the substituted `y` has been captured by the binder,
/// turning a contingent statement into a tautology. That is the bug.
#[test]
fn substitution_does_not_capture() {
    let (_g, x, y, _z) = setup();

    // ∀y. x = y
    let f = Formula::forall(y, Formula::eq(Term::var(x), Term::var(y)));
    // [y/x]
    let substituted = f.subst(x, &Term::var(y));

    // The wrong answer: ∀y. y = y.
    let captured = Formula::forall(y, Formula::eq(Term::var(y), Term::var(y)));
    assert_ne!(substituted, captured, "substitution captured the free variable");

    // The right answer keeps the substituted occurrence free. Renaming the
    // binder must not change the formula, so compare against the same shape
    // built with a *different* bound variable.
    let mut g2 = VarGen::new();
    let (_, _, _) = (g2.fresh(), g2.fresh(), g2.fresh());
    let w = g2.fresh();
    let expected = Formula::forall(w, Formula::eq(Term::var(y), Term::var(w)));
    assert_eq!(substituted, expected, "alpha-equivalent results should be identical");
}

/// Substituting for a variable that is shadowed by a binder must leave the
/// bound occurrences alone.
#[test]
fn substitution_respects_shadowing() {
    let (_g, x, _y, z) = setup();

    // ∀x. x = x — the binder shadows the free x entirely.
    let f = Formula::forall(x, Formula::eq(Term::var(x), Term::var(x)));
    let substituted = f.subst(x, &Term::var(z));

    assert_eq!(substituted, f, "substituting a shadowed variable changed the formula");
    assert!(!substituted.occurs_free(z), "shadowed substitution leaked the new variable");
}

/// Closing over a variable that does not occur yields a vacuous quantifier, and
/// must not disturb anything else.
#[test]
fn vacuous_binder() {
    let (_g, x, y, _z) = setup();
    let body = Formula::eq(Term::var(x), Term::var(x));
    let f = Formula::forall(y, body.clone());
    assert!(!f.occurs_free(y));
    assert!(f.occurs_free(x), "unrelated free variable was captured by a vacuous binder");
}

/// Nested binders must get distinct de Bruijn depths. If `close` failed to
/// increment depth under a binder, `∀x.∀y. x = y` would collapse to `∀x.∀y. y = y`.
#[test]
fn nested_binders_get_distinct_indices() {
    let (_g, x, y, _z) = setup();

    let inner = Formula::eq(Term::var(x), Term::var(y));
    // ∀x. ∀y. x = y
    let f = Formula::forall(x, Formula::forall(y, inner));

    // ∀x. ∀y. y = y — what a depth bug would produce.
    let collapsed = Formula::forall(x, Formula::forall(y, Formula::eq(Term::var(y), Term::var(y))));
    assert_ne!(f, collapsed, "nested binders collapsed to the same index");

    // ∀x. ∀y. y = x is a genuinely different formula.
    let swapped = Formula::forall(x, Formula::forall(y, Formula::eq(Term::var(y), Term::var(x))));
    assert_ne!(f, swapped, "binder order was lost");
}

/// Alpha-equivalence: the choice of bound variable name must be invisible.
#[test]
fn alpha_equivalence_is_syntactic_equality() {
    let mut g = VarGen::new();
    let (a, b) = (g.fresh(), g.fresh());
    let fa = Formula::forall(a, Formula::mem(Term::var(a), Term::var(a)));
    let fb = Formula::forall(b, Formula::mem(Term::var(b), Term::var(b)));
    assert_eq!(fa, fb, "alpha-equivalent formulas compared unequal");
}

/// Every formula handed out must be locally closed — no dangling index.
#[test]
fn constructed_formulas_are_locally_closed() {
    let (_g, x, y, z) = setup();
    let f = Formula::forall(x, Formula::forall(y, Formula::imp(
        Formula::mem(Term::var(x), Term::var(y)),
        Formula::eq(Term::var(z), Term::var(x)),
    )));
    // A dangling index would make this false and would be a latent capture bug.
    assert!(kernel::thm::debug_locally_closed(&f));
}

/// Substitution under multiple binders lands the term at the right depth.
#[test]
fn substitution_under_nested_binders() {
    let (_g, x, y, z) = setup();

    // ∀y. ∀z. x = y
    let f = Formula::forall(y, Formula::forall(z, Formula::eq(Term::var(x), Term::var(y))));
    let s = f.subst(x, &Term::var(z));

    // z must remain free; if the two binders were miscounted it would be
    // captured by one of them.
    assert!(s.occurs_free(z), "substituted variable was captured under nested binders");
}

/// A substituted term with several free variables keeps all of them free.
#[test]
fn substitution_of_compound_term_keeps_variables_free() {
    let (_g, x, y, z) = setup();
    // ∀x. x ∈ y   then   [z/y]
    let f = Formula::forall(x, Formula::mem(Term::var(x), Term::var(y)));
    let s = f.subst(y, &Term::var(z));
    assert!(s.occurs_free(z));
    assert!(!s.occurs_free(y));
    // And z must not have been swallowed by the ∀x binder.
    let captured = Formula::forall(z, Formula::mem(Term::var(z), Term::var(z)));
    assert_ne!(s, captured);
}

/// Substituting a variable for itself is the identity.
#[test]
fn self_substitution_is_identity() {
    let (_g, x, y, _z) = setup();
    let f = Formula::forall(y, Formula::mem(Term::var(x), Term::var(y)));
    assert_eq!(f.subst(x, &Term::var(x)), f);
}
