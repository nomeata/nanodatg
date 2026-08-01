//! The exact formula of [`Thm::ax_replacement`], rebuilt from the constructors.
//!
//! # Why this shape of test
//!
//! Replacement is the other formula-valued axiom — like `ax_tarski` it is not a
//! fixed sentence but a *scheme* assembled at run time out of a caller's `φ` —
//! and until now nothing compared its conclusion against anything. See
//! `choice.rs` for the argument in full: a test that does not compare against
//! the axiom's actual conclusion pins nothing, and the `ax_tarski` history shows
//! how a clause can be added or lost with a green suite.
//!
//! So every assertion below is against `Thm::ax_replacement(…).concl()`, and the
//! formula it is compared with is built here from `Formula` and `Term`
//! constructors only. In particular it does **not** call
//! `kernel::thm::exists_unique` — the `∃!` spelling is the antecedent's entire
//! strength, and borrowing the kernel's copy of it would make the comparison a
//! tautology exactly where it matters most.
//!
//! # The reference statement
//!
//! Replacement in *functional* form with an **exact** image (Kunen I.12.2,
//! Jech §1):
//!
//! ```text
//! ∀a. (∀x. x ∈ a → ∃!y. φ)  →  ∃b ∀y. (y ∈ b ↔ ∃x. (x ∈ a ∧ φ))
//! ```
//!
//! Two things about that statement are load-bearing and are pinned separately
//! below. The antecedent is `∃!`, not `∃`: with mere existence this is
//! Collection, and the `↔` would then assert that the *whole* image of a
//! possibly class-sized relation is a set. And the consequent is `↔`, not `→`:
//! the image is exactly `b`, not merely contained in it.
//!
//! Being a scheme, this is instantiated per-formula rather than quantified over
//! relations, which first-order logic cannot do; `x` and `y` are the caller's
//! designated variables and both are *bound* in the result, which is why an
//! independent rebuild is syntactically equal despite drawing its own fresh
//! variables.

use kernel::{Env, Formula, FreeVar, Term, Thm};

// ─────────────────────────────────────────────────────────────────────────────
// The scheme, described from scratch.
// ─────────────────────────────────────────────────────────────────────────────

/// `∃!y. φ`, spelled `∃y. (φ ∧ ∀y'. (φ[y'/y] → y' = y))`.
///
/// `y'` is a parameter so that a test can supply a *different* fresh variable
/// from the one the kernel used and check that the choice is invisible — which
/// is precisely the property `ax_replacement`'s freshness checks exist to
/// guarantee.
fn exists_unique(y: FreeVar, y2: FreeVar, phi: &Formula) -> Formula {
    let uniq =
        Formula::forall(y2, Formula::imp(phi.subst(y, &Term::var(y2)), Formula::eq(Term::var(y2), Term::var(y))));
    Formula::exists(y, Formula::and(phi.clone(), uniq))
}

/// How the antecedent states "`φ` is functional on `a`".
///
/// `unique` selects `∃!y. φ` or the strictly weaker `∃y. φ`. The latter is
/// built only so a test can assert the axiom is *not* it.
fn functional_on(a: FreeVar, y2: FreeVar, x: FreeVar, y: FreeVar, phi: &Formula, unique: bool) -> Formula {
    let witness = if unique { exists_unique(y, y2, phi) } else { Formula::exists(y, phi.clone()) };
    Formula::forall(x, Formula::imp(Formula::mem(Term::var(x), Term::var(a)), witness))
}

/// `∀a. (∀x. x ∈ a → ∃!y. φ) → ∃b ∀y. (y ∈ b ↔ ∃x. (x ∈ a ∧ φ))`, rebuilt.
///
/// `unique` and `exact` each select the honest statement or a deliberately
/// weakened one, so that the negative tests compare against something concrete.
fn expected_axiom(env: &mut Env, x: FreeVar, y: FreeVar, phi: &Formula, unique: bool, exact: bool) -> Formula {
    let (a, b, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let hyp = functional_on(a, y2, x, y, phi, unique);

    // ∃x. (x ∈ a ∧ φ) — the image of `a` under `φ`.
    let image = Formula::exists(x, Formula::and(Formula::mem(Term::var(x), Term::var(a)), phi.clone()));
    let member = Formula::mem(Term::var(y), Term::var(b));
    let body = if exact { Formula::iff(member, image) } else { Formula::imp(image, member) };
    let concl = Formula::exists(b, Formula::forall(y, body));

    Formula::forall(a, Formula::imp(hyp, concl))
}

/// `y ∈ x` — a `φ` mentioning both designated variables and nothing else.
fn phi_simple(x: FreeVar, y: FreeVar) -> Formula { Formula::mem(Term::var(y), Term::var(x)) }

/// `∀t. (t ∈ y ↔ (t ∈ x ∧ t ∈ w))` — "`y` is `x ∩ w`": a `φ` that carries its
/// own binder and a spare free parameter `w`, so the test also covers a `φ`
/// which is not an atom and which leaves a free variable in the result.
fn phi_with_parameter(env: &mut Env, x: FreeVar, y: FreeVar, w: FreeVar) -> Formula {
    let t = env.fresh_var();
    let tt = Term::var(t);
    let rhs = Formula::and(Formula::mem(tt.clone(), Term::var(x)), Formula::mem(tt.clone(), Term::var(w)));
    Formula::forall(t, Formula::iff(Formula::mem(tt, Term::var(y)), rhs))
}

// ─────────────────────────────────────────────────────────────────────────────
// The tests.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole formula, for an atomic `φ`.
#[test]
fn ax_replacement_is_exactly_the_reference_statement() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = phi_simple(x, y);
    let ax = Thm::ax_replacement(&mut env, x, y, phi.clone()).expect("a fresh x ≠ y must be accepted");
    let expected = expected_axiom(&mut env, x, y, &phi, true, true);
    assert_eq!(
        *ax.concl(),
        expected,
        "ax_replacement is not the formula this test rebuilt; if the scheme was changed \
         deliberately, change this test in the same commit and say why in the message"
    );
}

/// The same, for a `φ` with its own quantifier and a free parameter.
///
/// `φ` is dropped into three positions — the `∃!` witness, the uniqueness
/// conjunct under a substitution, and the image — so a scheme that mangled it
/// in any one of them would pass the atomic case and fail here.
#[test]
fn ax_replacement_handles_a_compound_phi() {
    let mut env = Env::new();
    let (x, y, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let phi = phi_with_parameter(&mut env, x, y, w);
    let ax = Thm::ax_replacement(&mut env, x, y, phi.clone()).expect("a fresh x ≠ y must be accepted");
    let expected = expected_axiom(&mut env, x, y, &phi, true, true);
    assert_eq!(*ax.concl(), expected, "ax_replacement mishandles a compound φ");

    // `w` is the only free variable left: `x` and `y` are bound by the scheme,
    // and none of the variables it generated for itself may escape.
    let mut fvs = Vec::new();
    ax.concl().free_vars(&mut fvs);
    assert_eq!(fvs, vec![w], "the scheme leaked a variable, or captured one of φ's");
    assert!(kernel::thm::debug_locally_closed(ax.concl()), "the scheme produced a dangling index");
}

/// The antecedent is `∃!y. φ`, **not** `∃y. φ`.
///
/// With bare existence the scheme is Collection with an exact image, which is
/// not what is asserted here and is not what the consequent's `↔` is sound for:
/// the `←` direction would then put every `y` related to some `x ∈ a` into `b`,
/// for a relation with no bound on how many `y` each `x` has.
#[test]
fn ax_replacement_antecedent_requires_uniqueness() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = phi_simple(x, y);
    let ax = Thm::ax_replacement(&mut env, x, y, phi.clone()).expect("a fresh x ≠ y must be accepted");
    let weak = expected_axiom(&mut env, x, y, &phi, false, true);
    assert_ne!(
        *ax.concl(),
        weak,
        "ax_replacement's antecedent has weakened from `∃!y. φ` to `∃y. φ` — that is Collection, \
         and the exact-image consequent is not sound for it"
    );
}

/// The consequent is `y ∈ b ↔ image`, **not** `image → y ∈ b`.
///
/// The `→` form only says `b` *contains* the image, which is Replacement with a
/// superset — true but strictly weaker, and Separation is then no longer
/// derivable from it without further work. The exactness is what `derived`
/// builds Separation on.
#[test]
fn ax_replacement_image_is_exact() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = phi_simple(x, y);
    let ax = Thm::ax_replacement(&mut env, x, y, phi.clone()).expect("a fresh x ≠ y must be accepted");
    let inexact = expected_axiom(&mut env, x, y, &phi, true, false);
    assert_ne!(
        *ax.concl(),
        inexact,
        "ax_replacement's consequent has weakened from `↔` to `→` — `b` would merely contain the \
         image rather than be it, and Separation is derived from the exactness"
    );
}

/// `x == y` must be **refused**, and the reason is soundness, not tidiness.
///
/// With `x == y` the image `∃x. (x ∈ a ∧ φ)` closes over the very variable the
/// consequent's `∀y` is meant to bind, so the right-hand side of the `↔` stops
/// mentioning it and the conclusion degenerates to `∃b ∀y. (y ∈ b ↔ ψ)` for a
/// `ψ` that does not depend on `y` — a universal set whenever `ψ` holds, which
/// Regularity refutes.
///
/// The test checks the rejection, and then exhibits the degeneracy directly.
#[test]
fn ax_replacement_rejects_a_single_designated_variable() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), Term::var(x));
    assert!(
        Thm::ax_replacement(&mut env, x, x, phi.clone()).is_none(),
        "ax_replacement accepted x == y — its conclusion is then a universal-set assertion"
    );

    // Why it must refuse: the image `∃x. (x ∈ a ∧ φ)` has already closed over
    // the variable that the consequent's `∀y` is meant to bind, so with `x == y`
    // the right-hand side of the `↔` does not mention the quantified variable at
    // all and `∃b ∀y. (y ∈ b ↔ image)` asserts a universal set.
    let a = env.fresh_var();
    let image = Formula::exists(x, Formula::and(Formula::mem(Term::var(x), Term::var(a)), phi));
    assert!(
        !image.occurs_free(x),
        "the image is closed in x — that is exactly what makes the x == y instance a universal set"
    );
}

/// The variables the scheme generates for itself are invisible.
///
/// `ax_replacement` checks `a`, `b` and `y2` against `x`, `y` and `FV(φ)`. Those
/// checks are unreachable through the public API — `FreeVar`s are branded, so a
/// variable from another `Env` can never compare equal to one of these, and a
/// variable from *this* `Env` was drawn before them and so cannot equal them.
/// They are the belt to branding's braces, and the right thing to test is the
/// property they exist to preserve: **provided the generated variables are
/// fresh, which ones they are does not affect the result.** Two rebuilds using
/// different fresh `y'` must be the same formula, and both must equal the
/// axiom's; if a generated variable ever escaped or captured, this is where it
/// would show.
#[test]
fn ax_replacement_generated_variables_are_invisible() {
    let mut env = Env::new();
    let (x, y, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let phi = phi_with_parameter(&mut env, x, y, w);
    let ax = Thm::ax_replacement(&mut env, x, y, phi.clone()).expect("a fresh x ≠ y must be accepted");

    let first = expected_axiom(&mut env, x, y, &phi, true, true);
    let second = expected_axiom(&mut env, x, y, &phi, true, true);
    assert_eq!(first, second, "the choice of generated variable is visible in the result");
    assert_eq!(*ax.concl(), first);

    // And the axiom is stable: a second call with the same arguments, drawing
    // three more fresh variables, must produce the identical formula.
    let again = Thm::ax_replacement(&mut env, x, y, phi).expect("a fresh x ≠ y must be accepted");
    assert_eq!(ax.concl(), again.concl(), "ax_replacement is not deterministic in its own fresh variables");
}
