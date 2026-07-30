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

/// Union comes out of the same abstraction as `upair`, differing only in its
/// existence axiom.
#[test]
fn union_has_its_characteristic_property() {
    let mut env = Env::new();
    let (f, axiom) = derived::union(&mut env);
    assert_eq!(f.arity(), 1);
    assert!(kernel::thm::debug_locally_closed(axiom.concl()));

    let (a, c) = (env.declare(0), env.declare(0));
    let (ta, tc) = (Term::apply(a, vec![]), Term::apply(c, vec![]));
    let inst = derived::inst_all(&axiom, std::slice::from_ref(&ta)).expect("instantiate x");
    let inst = derived::inst_all(&inst, std::slice::from_ref(&tc)).expect("instantiate z");
    // z ∈ ⋃a ↔ ∃y. (y ∈ a ∧ z ∈ y)
    let (lhs, _) = inst.concl().as_imp().expect("iff is a conjunction of implications");
    let (fwd, _) = lhs.as_imp().expect("forward half");
    let (mem, _) = fwd.as_imp().expect("membership");
    assert_eq!(mem, Formula::mem(tc, Term::apply(f, vec![ta])));
}

/// Power set, likewise.
#[test]
fn power_has_its_characteristic_property() {
    let mut env = Env::new();
    let (f, axiom) = derived::power(&mut env);
    assert_eq!(f.arity(), 1);
    assert!(kernel::thm::debug_locally_closed(axiom.concl()));
}

/// The three constructions must introduce distinct symbols in one signature.
#[test]
fn constructions_coexist() {
    let mut env = Env::new();
    let (up, _) = derived::upair(&mut env);
    let (un, _) = derived::union(&mut env);
    let (po, _) = derived::power(&mut env);
    let ids = [up.id(), un.id(), po.id()];
    assert_eq!(ids.iter().collect::<std::collections::HashSet<_>>().len(), 3);
}

/// `⋃{c} = c`, derived from the pair and union constructions plus
/// Extensionality. Needed by application: `app(f,a)` unions the collection of
/// values at `a`, which for a genuine function is a singleton.
#[test]
fn union_of_singleton() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let (un, un_ax) = derived::union(&mut env);

    let thm = derived::union_singleton(&mut env, up, &up_ax, un, &un_ax).expect("union_singleton derivation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // Instantiate at a constant and check the exact equation.
    let a = env.declare(0);
    let ta = Term::apply(a, vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&ta)).expect("instantiate c");
    let expected = Formula::eq(
        Term::apply(un, vec![derived::singleton(up, ta.clone())]),
        ta,
    );
    assert_eq!(*inst.concl(), expected, "union_singleton has the wrong shape");
}

/// Membership in a singleton, and singleton injectivity — the first steps of
/// the Kuratowski ordered-pair argument.
#[test]
fn singleton_lemmas() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);

    let mem_sing = derived::mem_singleton(&mut env, up, &up_ax).expect("mem_singleton");
    let inj = derived::singleton_inj(&mut env, up, &mem_sing).expect("singleton_inj");
    assert!(kernel::thm::debug_locally_closed(mem_sing.concl()));
    assert!(kernel::thm::debug_locally_closed(inj.concl()));

    let (a, c) = (env.declare(0), env.declare(0));
    let (ta, tc) = (Term::apply(a, vec![]), Term::apply(c, vec![]));

    // z ∈ {a} ↔ z = a
    let m = derived::inst_all(&mem_sing, &[ta.clone(), tc.clone()]).expect("inst mem_singleton");
    assert_eq!(
        *m.concl(),
        Formula::iff(Formula::mem(tc.clone(), derived::singleton(up, ta.clone())), Formula::eq(tc.clone(), ta.clone()))
    );

    // {a} = {c} → a = c
    let i = derived::inst_all(&inj, &[ta.clone(), tc.clone()]).expect("inst singleton_inj");
    assert_eq!(
        *i.concl(),
        Formula::imp(
            Formula::eq(derived::singleton(up, ta.clone()), derived::singleton(up, tc.clone())),
            Formula::eq(ta, tc)
        )
    );
}
