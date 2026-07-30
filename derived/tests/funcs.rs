//! Set-theoretic function application.
//!
//! As in `tests/pairs.rs`, every assertion pins the *exact* conclusion. A lemma
//! that is merely equivalent to the intended one is useless downstream, because
//! the next derivation matches formulas syntactically.

use derived::funcs::{cond_relation_unique, snd_in_union2, union_intro, Sets};
use kernel::{Env, Formula, Term};

/// A fresh environment with `upair` and `union` available.
fn prelude() -> (Env, Sets) {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    (env, sets)
}

/// A fresh constant, usable to instantiate a quantifier at.
fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

/// The witnessed backward half of the Union axiom.
#[test]
fn union_introduction() {
    let (mut env, sets) = prelude();
    let (s, v, u) = (constant(&mut env), constant(&mut env), constant(&mut env));

    let thm = union_intro(&mut env, &sets, s.clone(), v.clone(), u.clone()).expect("union_intro");
    let expected = Formula::imp(
        Formula::and(Formula::mem(v.clone(), s.clone()), Formula::mem(u.clone(), v)),
        Formula::mem(u, sets.union_of(s)),
    );
    assert_eq!(*thm.concl(), expected, "union_intro has the wrong shape");
}

/// `⟨a,y⟩ ∈ f` puts `y` two unions up.
#[test]
fn second_component_lands_in_the_double_union() {
    let (mut env, sets) = prelude();
    let thm = snd_in_union2(&mut env, &sets).expect("snd_in_union2");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (f, a, y) = (constant(&mut env), constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[f.clone(), a.clone(), y.clone()]).expect("instantiate");

    let expected = Formula::imp(
        Formula::mem(sets.pair(a, y.clone()), f.clone()),
        Formula::mem(y, sets.union_of(sets.union_of(f))),
    );
    assert_eq!(*inst.concl(), expected, "snd_in_union2 has the wrong shape");
}

/// The conditional-value relation Replacement is fed is total and functional.
#[test]
fn conditional_value_is_unique() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let d = constant(&mut env);
    // ψ(x) := x ∈ d, an arbitrary predicate.
    let psi = Formula::mem(Term::var(x), d.clone());

    let thm = cond_relation_unique(&mut env, x, &psi, y, &d).expect("cond_relation_unique");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let phi = Formula::or(
        Formula::and(psi.clone(), Formula::eq(Term::var(y), Term::var(x))),
        Formula::and(Formula::not(psi), Formula::eq(Term::var(y), d)),
    );
    let expected = kernel::thm::exists_unique(&mut env, y, &phi);
    assert_eq!(*thm.concl(), expected, "cond_relation_unique has the wrong shape");
}

/// A predicate mentioning the bound value variable is rejected rather than
/// silently producing a capture-flavoured nonsense statement.
#[test]
fn conditional_value_rejects_a_bad_predicate() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let d = constant(&mut env);
    let psi = Formula::mem(Term::var(x), Term::var(y));
    assert!(cond_relation_unique(&mut env, x, &psi, y, &d).is_none());
}

/// Separation, given a witness that the result is inhabited.
#[test]
fn separation_for_an_inhabited_subset() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let (a, c) = (constant(&mut env), constant(&mut env));
    // ψ(x) := x ∈ c, so the theorem is about `A ∩ c`.
    let psi = Formula::mem(Term::var(x), c);

    let thm = derived::funcs::separation_nonempty(&mut env, x, &psi, &a).expect("separation_nonempty");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let s = env.fresh_var();
    let body = Formula::and(Formula::mem(Term::var(x), a.clone()), psi.clone());
    let expected = Formula::imp(
        Formula::exists(x, body.clone()),
        Formula::exists(s, Formula::forall(x, Formula::iff(Formula::mem(Term::var(x), Term::var(s)), body))),
    );
    assert_eq!(*thm.concl(), expected, "separation_nonempty has the wrong shape");
}

/// `{ y : ⟨a,y⟩ ∈ f }` is a set whenever there is anything in it.
#[test]
fn the_value_collection_is_a_set() {
    let (mut env, sets) = prelude();
    let sni = snd_in_union2(&mut env, &sets).expect("snd_in_union2");
    let vc = derived::funcs::value_collection(&mut env, &sets, &sni).expect("value_collection");
    assert!(kernel::thm::debug_locally_closed(vc.concl()), "dangling bound variable");

    let (f, a) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&vc, &[f.clone(), a.clone()]).expect("instantiate");
    let (y, s) = (env.fresh_var(), env.fresh_var());
    let cond = Formula::mem(sets.pair(a, Term::var(y)), f);
    let expected = Formula::imp(
        Formula::exists(y, cond.clone()),
        Formula::exists(
            s,
            Formula::forall(y, Formula::iff(Formula::mem(Term::var(y), Term::var(s)), cond)),
        ),
    );
    assert_eq!(*inst.concl(), expected, "value_collection has the wrong shape");
}

/// The collection symbol, with its default stripped off.
#[test]
fn collection_symbol_characterisation() {
    let (mut env, sets) = prelude();
    let sni = snd_in_union2(&mut env, &sets).expect("snd_in_union2");
    let vc = derived::funcs::value_collection(&mut env, &sets, &sni).expect("value_collection");
    let (coll, ax) = derived::funcs::collection(&mut env, &sets, &vc).expect("collection");
    assert!(kernel::thm::debug_locally_closed(ax.concl()), "dangling bound variable");
    assert_eq!(coll.arity(), 2);

    let (f, a) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&ax, &[f.clone(), a.clone()]).expect("instantiate");
    let y = env.fresh_var();
    let cond = Formula::mem(sets.pair(a.clone(), Term::var(y)), f.clone());
    let expected = Formula::imp(
        Formula::exists(y, cond.clone()),
        Formula::forall(
            y,
            Formula::iff(Formula::mem(Term::var(y), Term::apply(coll, vec![f, a])), cond),
        ),
    );
    assert_eq!(*inst.concl(), expected, "collection has the wrong shape");
}

/// Beta reduction for a set-theoretic function, on its domain.
#[test]
fn beta_on_the_domain() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply::new");
    // An arbitrary unary body symbol, standing for a lambda body.
    let t = env.declare(1);
    let (lam, lam_ax) = derived::funcs::lambda(&mut env, &ap, t).expect("lambda");
    let beta = derived::funcs::beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");
    assert!(kernel::thm::debug_locally_closed(beta.concl()), "dangling bound variable");

    let (big_a, a) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&beta, &[big_a.clone(), a.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::mem(a.clone(), big_a.clone()),
        Formula::eq(
            ap.apply(Term::apply(lam, vec![big_a]), a.clone()),
            Term::apply(t, vec![a]),
        ),
    );
    assert_eq!(*inst.concl(), expected, "beta_conditional has the wrong shape");
}

/// The membership characterisation of application.
#[test]
fn application_membership() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply::new");
    let thm = derived::funcs::app_members(&mut env, &ap).expect("app_members");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (f, a) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[f.clone(), a.clone()]).expect("instantiate");
    let (w, y) = (env.fresh_var(), env.fresh_var());
    let pair_in_f = Formula::mem(ap.sets.pair(a.clone(), Term::var(y)), f.clone());
    let expected = Formula::imp(
        Formula::exists(y, pair_in_f.clone()),
        Formula::forall(
            w,
            Formula::iff(
                Formula::mem(Term::var(w), ap.apply(f, a)),
                Formula::exists(y, Formula::and(pair_in_f, Formula::mem(Term::var(w), Term::var(y)))),
            ),
        ),
    );
    assert_eq!(*inst.concl(), expected, "app_members has the wrong shape");
}

/// The graph of a unary body symbol is the Replacement image of the domain.
#[test]
fn lambda_graph_characterisation() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply::new");
    let t = env.declare(1);
    let (lam, lam_ax) = derived::funcs::lambda(&mut env, &ap, t).expect("lambda");
    assert!(kernel::thm::debug_locally_closed(lam_ax.concl()));
    assert_eq!(lam.arity(), 1);

    let (big_a, y) = (constant(&mut env), env.fresh_var());
    let inst = derived::inst_all(&lam_ax, &[big_a.clone(), Term::var(y)]).expect("instantiate");
    let x = env.fresh_var();
    let expected = Formula::iff(
        Formula::mem(Term::var(y), Term::apply(lam, vec![big_a.clone()])),
        Formula::exists(
            x,
            Formula::and(
                Formula::mem(Term::var(x), big_a),
                Formula::eq(
                    Term::var(y),
                    ap.sets.pair(Term::var(x), Term::apply(t, vec![Term::var(x)])),
                ),
            ),
        ),
    );
    assert_eq!(*inst.concl(), expected, "lambda has the wrong shape");
}

/// Beta is a genuine `∀A ∀a`, not something that merely instantiates well.
#[test]
fn beta_is_fully_quantified() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply::new");
    let t = env.declare(1);
    let (lam, lam_ax) = derived::funcs::lambda(&mut env, &ap, t).expect("lambda");
    let beta = derived::funcs::beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");

    let mut cur = beta.concl().clone();
    for i in 0..2 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let arg = constant(&mut env);
        cur = kernel::Thm::ax_inst(cur, arg).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    // What is left is the implication `a ∈ A → app(lam(A),a) = t(a)`; in
    // particular the membership antecedent is still there.
    let (ante, concl) = cur.as_imp().expect("an implication");
    assert!(ante.as_mem().is_some(), "the domain hypothesis must survive");
    assert!(concl.as_eq().is_some(), "beta should conclude an equation");
}

/// `app` is the union of the collection, by definition.
#[test]
fn app_is_the_union_of_the_collection() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply::new");
    assert_eq!(ap.app.arity(), 2);
    let (f, a) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&ap.app_ax, &[f.clone(), a.clone()]).expect("instantiate");
    let expected = Formula::eq(
        ap.apply(f.clone(), a.clone()),
        ap.sets.union_of(ap.coll_of(f, a)),
    );
    assert_eq!(*inst.concl(), expected, "app_ax has the wrong shape");
}
