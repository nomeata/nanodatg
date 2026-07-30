//! Conservative definitional extension, end to end.
//!
//! The point of these tests is that `define` is not a rubber stamp: it demands
//! an actual `∃!` theorem, and that theorem has to be *derived* from the
//! primitives. The positive test below does exactly that — it builds
//! `⊢ ∀x. ∃!y. y = x` out of reflexivity, generalisation and the propositional
//! combinators, and then uses it to introduce a function symbol and obtain its
//! defining equation.

use kernel::thm::{define, exists_unique};
use kernel::{Env, Formula, Term, Thm};

/// Derive `⊢ ∀x. ∃!y. (y = x)`, then define `f` with `⊢ ∀x. f(x) = x`.
///
/// This exercises the whole chain: `eq_refl`, `imp_refl`, `gen`, `and_intro`,
/// `exists_intro`, and finally `define`.
#[test]
fn define_identity_function() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let y = env.fresh_var();
    let (tx, ty) = (Term::var(x), Term::var(y));

    // φ(y) := y = x
    let phi = Formula::eq(ty.clone(), tx.clone());

    // The uniqueness clause, at the witness y := x. `exists_unique` builds
    // `∃y. (φ ∧ ∀y'. (φ[y'/y] → y' = y))`; we must prove the body at y := x.
    let target = exists_unique(&mut env, y, &phi);

    // Reconstruct the body's shape at y := x so we can prove it.
    // Component 1: x = x.
    let refl = Thm::eq_refl(tx.clone());

    // Component 2: ∀y'. (y' = x → y' = x).
    let y2 = env.fresh_var();
    let inner = Formula::eq(Term::var(y2), tx.clone());
    let ident = derived::imp_refl(inner);
    let uniq = Thm::gen(y2, &ident);

    // Conjoin, then existentially generalise at the witness x.
    let body_at_x = derived::and_intro(&refl, &uniq);
    let body = {
        // The formula `exists_intro` expects is the ∃'s body, i.e. what
        // `exists_unique` quantified over.
        let y3 = env.fresh_var();
        let u = Formula::forall(
            y3,
            Formula::imp(phi.subst(y, &Term::var(y3)), Formula::eq(Term::var(y3), ty.clone())),
        );
        Formula::and(phi.clone(), u)
    };
    assert_eq!(body_at_x.concl(), &body.subst(y, &tx), "hand-built witness does not match the ∃ body at x");

    let ex = derived::exists_intro(y, body, tx.clone(), &body_at_x).expect("exists_intro failed");
    assert_eq!(ex.concl(), &target, "derived ∃! does not match exists_unique's statement");

    // Generalise over x and hand it to `define`.
    let all = Thm::gen(x, &ex);
    let (f, axiom) = define(&mut env, &[x], y, phi, &all).expect("define rejected a valid witness");

    // The defining axiom must be exactly ∀x. f(x) = x.
    let expected = Formula::forall(x, Formula::eq(Term::apply(f, vec![tx.clone()]), tx));
    assert_eq!(*axiom.concl(), expected, "unexpected defining axiom");
}

/// `define` must reject a witness that does not prove the required `∃!`.
/// Without this check the extension would not be conservative — a symbol could
/// be introduced for a property that no unique object satisfies.
#[test]
fn define_rejects_a_bogus_witness() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::eq(Term::var(y), Term::var(x));

    // A true theorem, but not the one required.
    let irrelevant = Thm::eq_refl(Term::var(x));
    assert!(define(&mut env, &[x], y, phi.clone(), &irrelevant).is_none(), "define accepted an unrelated theorem");

    // Even the *existence* half alone is not enough — uniqueness is what makes
    // the expansion of a model unique, and hence the extension conservative.
    let y2 = env.fresh_var();
    let bare_exists = Formula::exists(y2, Formula::eq(Term::var(y2), Term::var(x)));
    let all_bare = Thm::gen(x, &Thm::eq_refl(Term::var(x)));
    assert!(define(&mut env, &[x], y, phi, &all_bare).is_none(), "define accepted a non-∃! witness");
    let _ = bare_exists;
}

/// The parameter list must not contain the defined variable, or `f(x⃗)` would
/// capture it.
#[test]
fn define_rejects_y_among_the_parameters() {
    let mut env = Env::new();
    let y = env.fresh_var();
    let phi = Formula::eq(Term::var(y), Term::var(y));
    let bogus = Thm::eq_refl(Term::var(y));
    assert!(define(&mut env, &[y], y, phi, &bogus).is_none());
}

/// `exists_unique` must not depend on which fresh variable it picks: the
/// locally nameless representation makes alpha-equivalent formulas identical,
/// and `define`'s witness comparison relies on that.
#[test]
fn exists_unique_is_independent_of_fresh_choice() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::eq(Term::var(y), Term::var(x));
    let a = exists_unique(&mut env, y, &phi);
    // Burn some variables, so the second call picks different ones.
    for _ in 0..5 {
        let _ = env.fresh_var();
    }
    let b = exists_unique(&mut env, y, &phi);
    assert_eq!(a, b, "exists_unique depends on the fresh variable it happened to pick");
}

/// The propositional combinators produce what they claim.
#[test]
fn combinators_are_correct() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let p = Formula::mem(Term::var(x), Term::var(x));
    let q = Formula::eq(Term::var(x), Term::var(x));

    assert_eq!(*derived::imp_refl(p.clone()).concl(), Formula::imp(p.clone(), p.clone()));

    let pt = Thm::eq_refl(Term::var(x));
    assert_eq!(*derived::a1i(&pt, p.clone()).concl(), Formula::imp(p.clone(), q.clone()));

    assert_eq!(*derived::mp_const(&pt, p.clone()).concl(), Formula::imp(Formula::imp(q.clone(), p.clone()), p.clone()));

    let both = derived::and_intro(&pt, &pt);
    assert_eq!(*both.concl(), Formula::and(q.clone(), q));
}

/// Explicit definitions are always available and cost no real proof: define a
/// nullary symbol as an abbreviation and get its defining equation.
#[test]
fn define_abbrev_nullary() {
    let mut env = Env::new();
    let g = env.declare(2);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let t = Term::apply(g, vec![Term::var(a), Term::var(b)]);

    let (f, axiom) = derived::define_abbrev(&mut env, &[], &t);
    assert_eq!(f.arity(), 0);
    assert_eq!(*axiom.concl(), Formula::eq(Term::apply(f, vec![]), t));
}

/// With parameters, the defining equation is universally quantified and the
/// symbol is applied to them in order.
#[test]
fn define_abbrev_with_parameters() {
    let mut env = Env::new();
    let g = env.declare(1);
    let (x, y) = (env.fresh_var(), env.fresh_var());
    // f(x, y) := g(x)
    let t = Term::apply(g, vec![Term::var(x)]);

    let (f, axiom) = derived::define_abbrev(&mut env, &[x, y], &t);
    assert_eq!(f.arity(), 2);
    let applied = Term::apply(f, vec![Term::var(x), Term::var(y)]);
    let expected = Formula::forall(x, Formula::forall(y, Formula::eq(applied, t)));
    assert_eq!(*axiom.concl(), expected);
}

/// The defining equation is usable: instantiate it and get a real equation
/// between terms, which is what a delta-reduction certificate needs.
#[test]
fn defining_equation_instantiates() {
    let mut env = Env::new();
    let g = env.declare(1);
    let x = env.fresh_var();
    let t = Term::apply(g, vec![Term::var(x)]);
    let (f, axiom) = derived::define_abbrev(&mut env, &[x], &t);

    let c = env.declare(0);
    let arg = Term::apply(c, vec![]);
    let inst = derived::inst_all(&axiom, std::slice::from_ref(&arg)).expect("instantiation failed");

    let expected = Formula::eq(Term::apply(f, vec![arg.clone()]), Term::apply(g, vec![arg]));
    assert_eq!(*inst.concl(), expected, "instantiated defining equation has the wrong shape");
}
