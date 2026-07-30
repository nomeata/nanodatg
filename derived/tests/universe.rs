//! The canonical universe operator `U(x)`.

use kernel::{Env, Formula, Term, Thm};

use derived::universe as uni;

/// [`uni::is_universe`] must be exactly the three closure clauses `ax_tarski`
/// asserts — the whole construction is worthless if it is a different predicate
/// that merely looks similar. Compared against the axiom itself.
#[test]
fn is_universe_matches_the_axiom() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let u = env.fresh_var();
    let (tx, tu) = (Term::var(x), Term::var(u));

    let ax = Thm::ax_tarski(&mut env);
    let inst = derived::inst_all(&ax, std::slice::from_ref(&tx)).expect("instantiate x");

    let body = uni::universe_body(&mut env, &tx, &tu);
    assert_eq!(*inst.concl(), Formula::exists(u, body.clone()), "universe_body is not Tarski's body");

    // And the body really is `x ∈ u ∧ is_universe(u)`.
    let expected = Formula::and(Formula::mem(tx.clone(), tu.clone()), uni::is_universe(&mut env, &tu));
    assert_eq!(body, expected);

    // ... with `is_universe` the axiom's own `C₂ ∧ (C₃ ∧ C₄)`.
    let c2 = uni::closed_sub(&mut env, &tu);
    let c3 = uni::closed_pow(&mut env, &tu);
    let c4 = uni::inaccessible(&mut env, &tu);
    assert_eq!(uni::is_universe(&mut env, &tu), Formula::and(c2, Formula::and(c3, c4)));
}

/// The clauses are the formulas their names claim, spelled out independently of
/// the module that builds them.
#[test]
fn clauses_have_the_stated_shapes() {
    let mut env = Env::new();
    let tu = Term::apply(env.declare(0), vec![]);

    let (y, z, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tz, tp) = (Term::var(y), Term::var(z), Term::var(p));

    let sub_zy = kernel::thm::subset(&mut env, tz.clone(), ty.clone());
    let want_c2 = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), tu.clone()),
            Formula::forall(z, Formula::imp(sub_zy.clone(), Formula::mem(tz.clone(), tu.clone()))),
        ),
    );
    assert_eq!(uni::closed_sub(&mut env, &tu), want_c2);

    let want_c3 = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), tu.clone()),
            Formula::exists(
                p,
                Formula::and(
                    Formula::mem(tp.clone(), tu.clone()),
                    Formula::forall(z, Formula::imp(sub_zy, Formula::mem(tz, tp))),
                ),
            ),
        ),
    );
    assert_eq!(uni::closed_pow(&mut env, &tu), want_c3);

    let sub_yu = kernel::thm::subset(&mut env, ty.clone(), tu.clone());
    let equi = kernel::thm::equinumerous(&mut env, ty.clone(), tu.clone());
    let want_c4 = Formula::forall(
        y,
        Formula::imp(sub_yu, Formula::or(equi, Formula::mem(ty, tu.clone()))),
    );
    assert_eq!(uni::inaccessible(&mut env, &tu), want_c4);
}

/// `x` lies in every universe containing `x`: the inhabitation witness, proved
/// outright.
#[test]
fn the_intersection_is_inhabited_by_x() {
    let mut env = Env::new();
    let tx = Term::apply(env.declare(0), vec![]);

    let thm = uni::mem_all_universes_self(&mut env, &tx);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert_eq!(*thm.concl(), uni::in_all_universes(&mut env, &tx, &tx));
}

/// The intersection of all universes containing `x` exists — and its
/// membership condition does not mention the universe Tarski supplied.
#[test]
fn the_intersection_exists() {
    let mut env = Env::new();
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));

    let thm = uni::least_universe_existence_at(&mut env, x, z).expect("existence");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let s = env.fresh_var();
    let expected = Formula::exists(
        s,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::var(s)),
                uni::in_all_universes(&mut env, &tx, &tz),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "existence has the wrong shape");

    let all = uni::least_universe_existence(&mut env).expect("existence, generalised");
    assert_eq!(*all.concl(), Formula::forall(x, expected));
}

/// The operator `U(x)` and its characteristic property.
#[test]
fn least_universe_has_its_characteristic_property() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");
    assert_eq!(lu.arity(), 1);
    assert!(kernel::thm::debug_locally_closed(ax.concl()));

    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let expected = Formula::forall(
        x,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::apply(lu, vec![tx.clone()])),
                uni::in_all_universes(&mut env, &tx, &tz),
            ),
        ),
    );
    assert_eq!(*ax.concl(), expected, "U's defining axiom has the wrong shape");
}

/// `⊢ ∀x. x ∈ U(x)`, and the tower step that follows from it.
#[test]
fn x_is_in_its_least_universe() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::mem_least_universe(&mut env, lu, &ax).expect("x ∈ U(x)");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    let x = env.fresh_var();
    let tx = Term::var(x);
    assert_eq!(
        *thm.concl(),
        Formula::forall(x, Formula::mem(tx.clone(), Term::apply(lu, vec![tx.clone()])))
    );

    let tower = uni::tower_step(&mut env, lu, &thm).expect("U(x) ∈ U(U(x))");
    let ux = Term::apply(lu, vec![tx]);
    assert_eq!(
        *tower.concl(),
        Formula::forall(x, Formula::mem(ux.clone(), Term::apply(lu, vec![ux])))
    );
}

/// A Grothendieck universe is closed under power sets — the two closure
/// clauses between them, neither alone.
#[test]
fn universes_are_closed_under_power_sets() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);

    let thm = uni::universe_power_closed(&mut env, pow, &pow_ax).expect("power closure");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (u, y) = (env.fresh_var(), env.fresh_var());
    let (tu, ty) = (Term::var(u), Term::var(y));
    let expected = Formula::forall(
        u,
        Formula::forall(
            y,
            Formula::imp(
                Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(ty.clone(), tu.clone())),
                Formula::mem(Term::apply(pow, vec![ty]), tu),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "universe_power_closed has the wrong shape");
}

/// `U(x)` satisfies Tarski's second clause: it is closed under subsets of its
/// members. Compared against `is_universe`'s own `C₂`, at the term `U(x)`.
#[test]
fn least_universe_is_closed_under_subsets() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::least_universe_closed_sub(&mut env, lu, &ax).expect("C₂ for U(x)");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let x = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(x)]);
    assert_eq!(*thm.concl(), Formula::forall(x, uni::closed_sub(&mut env, &w)));
}

/// And Tarski's third: power sets stay inside. The witness is `𝒫y`.
#[test]
fn least_universe_keeps_power_sets_inside() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::least_universe_closed_pow(&mut env, lu, &ax, pow, &pow_ax).expect("C₃ for U(x)");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let x = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(x)]);
    assert_eq!(*thm.concl(), Formula::forall(x, uni::closed_pow(&mut env, &w)));
}

/// Both closure clauses together — `is_universe(U(x))` minus inaccessibility.
#[test]
fn least_universe_satisfies_two_of_the_three_clauses() {
    let mut env = Env::new();
    let (pow, pow_ax) = derived::power(&mut env);
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm =
        uni::least_universe_closure(&mut env, lu, &ax, pow, &pow_ax).expect("C₂ ∧ C₃ for U(x)");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let x = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(x)]);
    let c2 = uni::closed_sub(&mut env, &w);
    let c3 = uni::closed_pow(&mut env, &w);
    assert_eq!(*thm.concl(), Formula::forall(x, Formula::and(c2.clone(), c3.clone())));

    // And that really is `is_universe(U(x))` with its third conjunct removed.
    let c4 = uni::inaccessible(&mut env, &w);
    assert_eq!(uni::is_universe(&mut env, &w), Formula::and(c2, Formula::and(c3, c4)));
}

/// The third clause is *not* proved. What is proved is the reduction: a subset
/// of `U(x)` that is not a member of it is equinumerous with some universe
/// containing `x` that misses it — from which `y ≈ U(x)` needs
/// Cantor–Schröder–Bernstein, which is not derived here.
#[test]
fn inaccessibility_reduces_to_schroeder_bernstein() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::inaccessibility_reduction(&mut env, lu, &ax).expect("the reduction");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (x, y, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tu) = (Term::var(x), Term::var(y), Term::var(u));
    let w = Term::apply(lu, vec![tx.clone()]);

    let hyp = Formula::and(
        kernel::thm::subset(&mut env, ty.clone(), w.clone()),
        Formula::not(Formula::mem(ty.clone(), w)),
    );
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let concl = Formula::exists(
        u,
        Formula::and(
            Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(tx, tu.clone())),
            Formula::and(
                kernel::thm::equinumerous(&mut env, ty, tu),
                Formula::not(y_in_u),
            ),
        ),
    );
    assert_eq!(
        *thm.concl(),
        Formula::forall(x, Formula::forall(y, Formula::imp(hyp, concl))),
        "inaccessibility_reduction has the wrong shape"
    );
}

/// Well-definedness: the description does not depend on the universe Tarski
/// supplies. Separating inside *any* universe containing `x` gives `U(x)`.
#[test]
fn the_description_does_not_depend_on_the_ambient_universe() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::least_universe_independent(&mut env, lu, &ax).expect("independence");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (x, u0, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tu0, tz) = (Term::var(x), Term::var(u0), Term::var(z));
    let w = Term::apply(lu, vec![tx.clone()]);

    let expected = Formula::forall(
        x,
        Formula::forall(
            u0,
            Formula::imp(
                uni::universe_body(&mut env, &tx, &tu0),
                Formula::forall(
                    z,
                    Formula::iff(
                        Formula::mem(tz.clone(), w),
                        Formula::and(
                            Formula::mem(tz.clone(), tu0),
                            uni::in_all_universes(&mut env, &tx, &tz),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "independence has the wrong shape");
}

/// The shape checks inside the derivations are `debug_assert`s, which pin the
/// intermediate formulas only if they actually run. They do — but say so, so
/// that a future profile change cannot silently disarm them.
#[test]
fn debug_assertions_are_enabled() {
    let enabled = cfg!(debug_assertions);
    assert!(enabled, "the derivations' shape checks are compiled out");
}
