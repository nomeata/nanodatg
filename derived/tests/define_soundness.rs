//! Regression guard for a soundness hole once present in `kernel::thm::define`.
//!
//! Extension by definitions is conservative only when the defined symbol takes
//! every parameter the property depends on. Without that side condition the
//! kernel is **unsound**, and the exploit is short — this file reconstructs it
//! and asserts it is now refused.
//!
//! It lives in `derived/tests` rather than `kernel/tests` so that the kernel's
//! own test suite does not need test-only helpers added to the trusted crate.

use kernel::{Env, Formula, Term};

/// **The exploit.** `φ(y) := (y = v)` for a stray `v`, defined with *no*
/// parameters.
///
/// If `define` accepted it, the axiom would be `⊢ f = v` with `v` free. A free
/// variable in a context-free system is implicitly universally quantified and
/// `gen` makes that explicit, giving `⊢ ∀v. f = v`; instantiating twice yields
/// `c₁ = c₂` for two arbitrary constants, and everything follows from that.
///
/// The underlying error: the witness proves "for each `v` there is a unique
/// `y`", so `y` depends on `v` — but `f()` takes no `v`, so the axiom claims one
/// `f` works for every `v`. Strictly stronger than what was proved.
#[test]
fn define_refuses_a_property_with_a_stray_free_variable() {
    let mut env = Env::new();
    let v = env.fresh_var();
    let tv = Term::var(v);
    let (y, phi, witness) = derived::exists_unique_eq(&mut env, &[], &tv);

    assert!(
        kernel::thm::define(&mut env, &[], y, phi, &witness).is_none(),
        "define accepted a property depending on a variable the symbol does not take — \
         that yields `⊢ ∀v. f = v` and hence equality of arbitrary constants"
    );
}

/// The same property *is* acceptable once `v` is a parameter, so the check is a
/// genuine side condition rather than a blanket ban.
#[test]
fn define_accepts_it_when_the_variable_is_a_parameter() {
    let mut env = Env::new();
    let v = env.fresh_var();
    let tv = Term::var(v);
    let (y, phi, witness) = derived::exists_unique_eq(&mut env, &[v], &tv);

    let (f, axiom) = kernel::thm::define(&mut env, &[v], y, phi, &witness)
        .expect("define should accept a property whose free variable is a parameter");
    assert_eq!(f.arity(), 1);
    assert_eq!(*axiom.concl(), Formula::forall(v, Formula::eq(Term::apply(f, vec![tv.clone()]), tv)));
}

/// `define_abbrev` — the everyday entry point — must be unaffected: it always
/// passes a term built from the parameters, so the side condition never bites.
#[test]
fn define_abbrev_still_works() {
    let mut env = Env::new();
    let g = env.declare(1);
    let x = env.fresh_var();
    let t = Term::apply(g, vec![Term::var(x)]);
    let (f, axiom) = derived::define_abbrev(&mut env, &[x], &t).expect("parameters cover the body");
    assert_eq!(f.arity(), 1);
    assert_eq!(*axiom.concl(), Formula::forall(x, Formula::eq(Term::apply(f, vec![Term::var(x)]), t)));
}
