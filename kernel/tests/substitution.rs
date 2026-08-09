//! Adversarial tests for binding, closing, opening and substitution.
//!
//! Capture-avoiding substitution is the classic soundness hole in an LCF
//! kernel, and Metamath's whole distinct-variable apparatus exists because of
//! it. These tests are deliberately written to *try to induce capture* rather
//! than to confirm the happy path — the negative assertions are the point.

use kernel::{Env, Formula, Term};

/// `VarGen` is deliberately not public — every `FreeVar` must come from an
/// `Env`, so that it carries that environment's brand. See `term.rs`.
fn setup() -> (Env, kernel::FreeVar, kernel::FreeVar, kernel::FreeVar) {
    let mut g = Env::new();
    let (x, y, z) = (g.fresh_var(), g.fresh_var(), g.fresh_var());
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
    // A fourth variable from the *same* environment; a different environment
    // would give a differently-branded variable that is not interchangeable.
    let mut g2 = _g;
    let w = g2.fresh_var();
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
    let mut g = Env::new();
    let (a, b) = (g.fresh_var(), g.fresh_var());
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

/// `eq_leibniz` shares one `close` between its two substitutions
/// (`PERF-REVIEW.md` F3). That is only a common subexpression if the shared
/// `close` really is independent of the term being substituted — so pin the
/// rule's conclusion against **two independent `subst` calls**, over a corpus
/// built to hit every way the two could come apart.
///
/// The interesting entries are the ones where the hoist could plausibly change
/// something: `a == b`; `a` mentioning the substituted variable (so that one
/// leg is the identity and the other is not); a `φ` that shadows `x`, where
/// `close` must find nothing; nested binders, where the shared abstraction has
/// to land the term at a *different* depth in each leg; and `x` absent from `φ`
/// entirely, where both legs return `φ`.
#[test]
fn eq_leibniz_agrees_with_two_independent_substitutions() {
    use kernel::Thm;
    let mut g = Env::new();
    let (x, y, z, w) = (g.fresh_var(), g.fresh_var(), g.fresh_var(), g.fresh_var());
    let f2 = g.declare(2);
    let (tx, ty, tz, tw) = (Term::var(x), Term::var(y), Term::var(z), Term::var(w));
    let app = Term::apply(f2, vec![tx.clone(), ty.clone()]);

    let phis = vec![
        // No occurrence at all.
        Formula::false_(),
        Formula::mem(ty.clone(), tz.clone()),
        // One occurrence, two occurrences, both sides.
        Formula::eq(tx.clone(), ty.clone()),
        Formula::eq(tx.clone(), tx.clone()),
        Formula::mem(tx.clone(), Term::apply(f2, vec![tx.clone(), tz.clone()])),
        // Under one binder, and under two, at different depths in each leg.
        Formula::forall(y, Formula::eq(tx.clone(), ty.clone())),
        Formula::forall(y, Formula::forall(z, Formula::mem(tx.clone(), Term::apply(f2, vec![ty.clone(), tz.clone()])))),
        // `x` shadowed by a binder of its own name: `close` must find nothing.
        Formula::forall(x, Formula::eq(tx.clone(), ty.clone())),
        // A free occurrence *outside* a shadowing binder, and a bound one inside.
        Formula::imp(Formula::eq(tx.clone(), tz.clone()), Formula::forall(x, Formula::mem(tx.clone(), ty.clone()))),
        // Deeply nested, so the shared `close` is the expensive one.
        Formula::forall(y, Formula::forall(z, Formula::forall(w, Formula::eq(tx.clone(), tw.clone())))),
    ];
    let terms = vec![tx.clone(), ty.clone(), tw.clone(), app.clone()];

    let mut checked = 0;
    for phi in &phis {
        for a in &terms {
            for b in &terms {
                let thm = Thm::eq_leibniz(a.clone(), b.clone(), x, phi.clone());
                let expected = Formula::imp(
                    Formula::eq(a.clone(), b.clone()),
                    Formula::imp(phi.subst(x, a), phi.subst(x, b)),
                );
                assert_eq!(thm.concl(), &expected, "eq_leibniz diverged from subst∘subst on {phi:?} [{a:?}, {b:?}]");
                assert!(thm.hyps().is_empty(), "eq_leibniz invented a hypothesis");
                checked += 1;
            }
        }
    }
    assert_eq!(checked, phis.len() * terms.len() * terms.len());
}

/// **The term reader is the inverse of the constructor, and it is the only
/// shape it can see.**
///
/// `Term::as_app` exists so that a client does not have to remember how it
/// built a term in order to take it apart again — the side table that used to
/// do that was 54 % of an `init-prelude` run's live heap, storing a second copy
/// of what each node already held (`PRELUDE-COST.md` §3.4). What has to stay
/// true is that reading widens nothing: the reader must answer `None` on
/// everything that is not an application, so that the constructor discipline
/// keeping dangling de Bruijn indices unconstructible is untouched.
#[test]
fn a_term_reads_back_as_it_was_applied_and_nothing_else_reads_back_at_all() {
    let (mut g, x, y, _z) = setup();
    let f = g.declare(2);

    let t = Term::apply(f, vec![Term::var(x), Term::var(y)]);
    let (h, args) = t.as_app().expect("an application reads back");
    assert_eq!(h, f);
    assert_eq!(args, &[Term::var(x), Term::var(y)][..]);

    // The round trip is the identity, so nothing about the term was lost in
    // the constructor and nothing is invented by the reader.
    assert_eq!(Term::apply(h, args.to_vec()), t);

    // A variable is not an application. `Bound` is the case that matters and
    // it cannot be tested from out here — there is no way to build one, which
    // is the property being protected — so the assertion available is that the
    // reader has exactly one `Some` case.
    assert!(Term::var(x).as_app().is_none(), "a free variable is not an application");
}
