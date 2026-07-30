//! Set-theoretic constructions, derived rather than assumed.

use kernel::{Env, Formula, Term};

/// The unordered pair is introduced by conservative definitional extension, and
/// comes out with exactly its characteristic property.
///
/// If this test passes, the whole chain worked: Pairing gave existence,
/// Extensionality gave uniqueness, the `∃!` was assembled in a Hilbert system
/// with no deduction theorem, and `define` accepted it. Nothing was assumed.
#[test]
fn upair_has_its_characteristic_property() {
    let mut env = Env::new();
    let (f, axiom) = derived::upair(&mut env);
    assert_eq!(f.arity(), 2, "upair should be binary");

    // ⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))
    let concl = axiom.concl();
    assert!(kernel::thm::debug_locally_closed(concl), "defining axiom has a dangling bound variable");

    // Instantiate at three constants and check the shape precisely.
    let (a, b, c) = (env.declare(0), env.declare(0), env.declare(0));
    let (ta, tb, tc) = (Term::apply(a, vec![]), Term::apply(b, vec![]), Term::apply(c, vec![]));
    let inst = derived::inst_all(&axiom, &[ta.clone(), tb.clone()]).expect("instantiate x, y");
    let inst = derived::inst_all(&inst, std::slice::from_ref(&tc)).expect("instantiate z");

    let expected = Formula::iff(
        Formula::mem(tc.clone(), Term::apply(f, vec![ta.clone(), tb.clone()])),
        Formula::or(Formula::eq(tc.clone(), ta), Formula::eq(tc, tb)),
    );
    assert_eq!(*inst.concl(), expected, "upair's characteristic property has the wrong shape");
}

/// Two calls introduce two *different* symbols — the signature grows, and a
/// second `upair` is not silently the same one.
#[test]
fn upair_is_fresh_each_time() {
    let mut env = Env::new();
    let (f1, _) = derived::upair(&mut env);
    let (f2, _) = derived::upair(&mut env);
    assert_ne!(f1.id(), f2.id());
}

/// Singletons and ordered pairs are *compositions*, not new extensions: the
/// signature must not grow when we build them.
#[test]
fn pairs_add_no_new_symbols() {
    let mut env = Env::new();
    let (up, _) = derived::upair(&mut env);
    let before = env.declare(0).id();

    let (a, b) = (env.declare(0), env.declare(0));
    let (ta, tb) = (Term::apply(a, vec![]), Term::apply(b, vec![]));
    let _ = derived::singleton(up, ta.clone());
    let _ = derived::opair(up, ta.clone(), tb.clone());

    // Only the three `declare` calls above consumed ids; building the pair
    // consumed none.
    let after = env.declare(0).id();
    assert_eq!(after - before, 3, "constructing pairs allocated new symbols");
}

/// `⟨a,b⟩` really is `{{a},{a,b}}`.
#[test]
fn opair_is_kuratowski() {
    let mut env = Env::new();
    let (up, _) = derived::upair(&mut env);
    let (a, b) = (env.declare(0), env.declare(0));
    let (ta, tb) = (Term::apply(a, vec![]), Term::apply(b, vec![]));

    let got = derived::opair(up, ta.clone(), tb.clone());
    let expected = Term::apply(
        up,
        vec![Term::apply(up, vec![ta.clone(), ta.clone()]), Term::apply(up, vec![ta, tb])],
    );
    assert_eq!(got, expected);
}
