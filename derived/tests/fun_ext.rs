//! Function extensionality for set-functions, and the eta equation derived
//! from it.
//!
//! As in `tests/ext.rs`, every assertion pins the *exact* conclusion. A lemma
//! that is merely equivalent to the intended one is useless downstream, because
//! the next derivation matches formulas syntactically.

use derived::ext::{app_of_pair, funspace_app_mem, funspace_ext, pointwise, Eta};
use derived::funcs::{Apply, Sets};
use derived::funspace::{product, Funspace, Product};
use kernel::{Env, FnSym, Formula, Term, Thm};

/// A fresh constant, usable to instantiate a quantifier at.
fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

/// The whole stack: one `Sets`, one `Apply` over it, one product carved from
/// the same pairing, and the function space over that. A second `Sets` would be
/// a second unrelated pairing, and no lemma here would compose.
struct Stack {
    env: Env,
    ap: Apply,
    p: Product,
    fsp: Funspace,
    app_pair: Thm,
    pow: FnSym,
    pow_ax: Thm,
}

fn stack() -> Stack {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let app_pair = app_of_pair(&mut env, &ap).expect("app_of_pair");
    Stack { env, ap, p, fsp, app_pair, pow, pow_ax }
}

/// Function extensionality, at its exact conclusion.
#[test]
fn functions_agreeing_pointwise_are_equal() {
    let Stack { mut env, ap, p, fsp, app_pair, .. } = stack();
    let thm = funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_ext");
    assert!(thm.hyps().is_empty(), "funspace_ext must be hypothesis-free");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (a, b, f, g) =
        (constant(&mut env), constant(&mut env), constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[a.clone(), b.clone(), f.clone(), g.clone()])
        .expect("instantiate");
    let expected = Formula::imp(
        Formula::and(
            Formula::mem(f.clone(), fsp.of(a.clone(), b.clone())),
            Formula::and(
                Formula::mem(g.clone(), fsp.of(a.clone(), b.clone())),
                pointwise(&mut env, &ap, &a, &f, &g),
            ),
        ),
        Formula::eq(f.clone(), g.clone()),
    );
    assert_eq!(*inst.concl(), expected, "funspace_ext has the wrong shape");

    // Non-vacuous: the two sides of the equation are distinct constants, so the
    // conclusion is not an instance of reflexivity.
    let (_, concl) = inst.concl().as_imp().expect("an implication");
    let (lhs, rhs) = concl.as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "funspace_ext would be vacuous");
}

/// The pointwise hypothesis really is about `app` on both sides, and the two
/// sides of it are different terms.
#[test]
fn the_pointwise_hypothesis_is_about_application() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (a, f, g) = (constant(&mut env), constant(&mut env), constant(&mut env));
    let pw = pointwise(&mut env, &ap, &a, &f, &g);
    // The two sides really are `app(f,·)` and `app(g,·)`: at `g := f` the
    // formula is a different one, so neither side was dropped on the floor.
    assert_ne!(pw, pointwise(&mut env, &ap, &a, &f, &f), "the two sides coincide");
    assert_ne!(pw, pointwise(&mut env, &ap, &a, &g, &g), "the two sides coincide");
    // And it is a statement about `app`, not about the graphs themselves.
    assert_ne!(pw, pointwise(&mut env, &ap, &g, &f, &g), "the domain is not read");
}

/// Extensionality refuses a function space built over a *different* pairing.
///
/// `Apply::new` and a second `Sets` are two unrelated definitional extensions,
/// so `app`'s ordered pair and `fs`'s would be different symbols and the
/// derivation would be relating the wrong things. It must decline rather than
/// produce a true theorem about a set nobody means.
#[test]
fn extensionality_refuses_a_foreign_pairing() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let other = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &other).expect("product");
    let fsp =
        Funspace::new(&mut env, &other, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let app_pair = app_of_pair(&mut env, &ap).expect("app_of_pair");
    assert!(
        funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).is_none(),
        "extensionality accepted a foreign pairing"
    );
}

/// Extensionality refuses a `app_of_pair` that is not one — here `app_members`,
/// a true theorem about the same `app` with the wrong shape.
#[test]
fn extensionality_refuses_a_foreign_theorem() {
    let Stack { mut env, ap, p, fsp, .. } = stack();
    let wrong = derived::funcs::app_members(&mut env, &ap).expect("app_members");
    assert!(
        funspace_ext(&mut env, &ap, &p, &fsp, &wrong).is_none(),
        "extensionality accepted a foreign theorem"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The eta equation.
// ─────────────────────────────────────────────────────────────────────────────

/// The requested statement, at its exact conclusion:
/// `⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))`.
///
/// Non-vacuous as a *statement*: the two sides are `f` and `graph(f,A)`, which
/// are different terms, so this is not reflexivity dressed up.
#[test]
fn a_function_is_the_graph_of_its_own_application() {
    let Stack { mut env, ap, p, fsp, app_pair, .. } = stack();
    let fun_ext = funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_ext");
    let app_mem =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    let eta = Eta::new(&mut env, &ap, &p, &fsp, &fun_ext, &app_mem).expect("Eta::new");
    assert!(eta.eta.hyps().is_empty(), "the eta equation must be hypothesis-free");
    assert!(kernel::thm::debug_locally_closed(eta.eta.concl()), "dangling bound variable");

    let (a, b, f) = (constant(&mut env), constant(&mut env), constant(&mut env));
    let inst =
        derived::inst_all(&eta.eta, &[a.clone(), b.clone(), f.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::mem(f.clone(), fsp.of(a.clone(), b.clone())),
        Formula::eq(f.clone(), eta.of(f.clone(), a.clone())),
    );
    assert_eq!(*inst.concl(), expected, "the eta equation has the wrong shape");

    let (_, concl) = inst.concl().as_imp().expect("an implication");
    let (lhs, rhs) = concl.as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "the eta equation would be reflexivity");
}

/// The graph symbol really is `{ ⟨x, app(f,x)⟩ : x ∈ A }`, and beta reduction
/// over it recovers `app(f,·)` on the domain.
#[test]
fn the_eta_graph_is_the_graph_of_application() {
    let Stack { mut env, ap, p, fsp, app_pair, .. } = stack();
    let fun_ext = funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_ext");
    let app_mem =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    let eta = Eta::new(&mut env, &ap, &p, &fsp, &fun_ext, &app_mem).expect("Eta::new");

    let (a, f) = (constant(&mut env), constant(&mut env));
    let x = env.fresh_var();
    let tx = Term::var(x);
    let z = constant(&mut env);
    let members = derived::inst_all(&eta.graph_ax, &[f.clone(), a.clone(), z.clone()])
        .expect("instantiate");
    assert_eq!(
        *members.concl(),
        Formula::iff(
            Formula::mem(z.clone(), eta.of(f.clone(), a.clone())),
            Formula::exists(
                x,
                Formula::and(
                    Formula::mem(tx.clone(), a.clone()),
                    Formula::eq(z, ap.sets.pair(tx.clone(), ap.apply(f.clone(), tx))),
                ),
            ),
        ),
        "the eta graph is not the graph of application"
    );

    let pt = constant(&mut env);
    let beta = derived::inst_all(&eta.beta, &[f.clone(), a.clone(), pt.clone()])
        .expect("instantiate");
    assert_eq!(
        *beta.concl(),
        Formula::imp(
            Formula::mem(pt.clone(), a.clone()),
            Formula::eq(ap.apply(eta.of(f.clone(), a), pt.clone()), ap.apply(f, pt)),
        ),
        "beta over the eta graph has the wrong shape"
    );
}

/// **Non-vacuity, at a concrete function on a concrete two-element set.**
///
/// The domain is `2 = {∅, {∅}}`, and it really has two members: `∅ ≠ {∅}` is
/// [`derived::sums::Sums`]'s `tags_distinct`, asserted here rather than assumed,
/// so the equation is not secretly about a singleton or the empty set. The
/// function is `id(2)`, which [`derived::funspace::identity_is_function`] puts
/// in `fs(2,2)` — so the antecedent discharges and
///
/// ```text
/// ⊢ id(2) = graph(id(2), 2)
/// ```
///
/// holds outright, with no hypothesis left. The two sides are built by
/// *different symbols* and are different terms, so this is genuine content and
/// not reflexivity dressed up.
#[test]
fn the_identity_on_a_two_element_set_is_its_own_graph() {
    let Stack { mut env, ap, p, fsp, app_pair, pow, pow_ax } = stack();
    let fun_ext = funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_ext");
    let app_mem =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    let eta = Eta::new(&mut env, &ap, &p, &fsp, &fun_ext, &app_mem).expect("Eta::new");

    // `2 = {∅, {∅}}`, with its two members shown to be distinct.
    let sums = derived::sums::Sums::over(&mut env, ap.clone(), pow, pow_ax, p.clone(), fsp.clone())
        .expect("Sums::over");
    let (zero, one) = (sums.zero(), sums.unit());
    assert_eq!(
        *sums.tags_distinct.concl(),
        Formula::not(Formula::eq(zero.clone(), one.clone())),
        "the two points are not known to be distinct"
    );
    let two = Term::apply(ap.sets.up, vec![zero, one]);

    let (id, id_ax) =
        derived::funspace::identity_graph(&mut env, &ap.sets).expect("identity_graph");
    let id_fun =
        derived::funspace::identity_is_function(&mut env, &ap.sets, &p, id, &id_ax, &ap.pair_inj)
            .expect("identity_is_function");

    let id_two = Term::apply(id, vec![two.clone()]);
    // `⊢ isfun(id(2))`, then `⊢ id(2) ∈ fs(2,2)` through the function space's
    // characteristic theorem.
    let isfun = derived::inst_all(&id_fun, std::slice::from_ref(&two)).expect("instantiate");
    let fs_at = derived::inst_all(&fsp.fs_ax, &[two.clone(), two.clone(), id_two.clone()])
        .expect("instantiate");
    let mem = Thm::mp(&derived::iff_mpr(&fs_at).expect("mpr"), &isfun).expect("mp");
    assert_eq!(
        *mem.concl(),
        Formula::mem(id_two.clone(), fsp.of(two.clone(), two.clone())),
        "the identity is not a member of its own function space"
    );

    let inst = derived::inst_all(&eta.eta, &[two.clone(), two.clone(), id_two.clone()])
        .expect("instantiate");
    let eq = Thm::mp(&inst, &mem).expect("mp");
    assert!(eq.hyps().is_empty(), "the instance must be hypothesis-free");
    let rhs = eta.of(id_two.clone(), two);
    assert_eq!(*eq.concl(), Formula::eq(id_two.clone(), rhs.clone()), "wrong instance");
    // The whole point: the equation relates two *different* terms, built by two
    // unrelated symbols. Nothing here is reflexivity.
    assert_ne!(id_two, rhs, "the identity instance would be reflexivity");
}

/// **The empty domain.** `∅ ∈ fs(∅,S)` for every `S`
/// ([`derived::wtype::empty_is_a_function`]), so the antecedent discharges
/// there too and the equation says `∅ = graph(∅,∅)` — true, and again not
/// reflexivity: the right-hand side is a `graph` application, not `∅`.
#[test]
fn the_empty_function_is_its_own_graph() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let app_pair = app_of_pair(&mut env, &ap).expect("app_of_pair");
    let fun_ext = funspace_ext(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_ext");
    let app_mem =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    let eta = Eta::new(&mut env, &ap, &p, &fsp, &fun_ext, &app_mem).expect("Eta::new");

    let sums = derived::sums::Sums::over(&mut env, ap.clone(), pow, pow_ax, p.clone(), fsp.clone())
        .expect("Sums::over");
    let empty_fun = derived::wtype::empty_is_a_function(&mut env, &sums).expect("empty_is_a_function");

    let emp = Term::apply(ap.empty, vec![]);
    let mem = derived::inst_all(&empty_fun, std::slice::from_ref(&emp)).expect("instantiate");
    assert_eq!(
        *mem.concl(),
        Formula::mem(emp.clone(), fsp.of(emp.clone(), emp.clone())),
        "∅ ∈ fs(∅,∅) has the wrong shape"
    );

    let inst = derived::inst_all(&eta.eta, &[emp.clone(), emp.clone(), emp.clone()])
        .expect("instantiate");
    let eq = Thm::mp(&inst, &mem).expect("mp");
    let rhs = eta.of(emp.clone(), emp.clone());
    assert_eq!(*eq.concl(), Formula::eq(emp.clone(), rhs.clone()), "wrong instance");
    assert_ne!(emp, rhs, "the empty instance would be reflexivity");
}

/// The eta construction refuses a `fun_ext` that is not one.
#[test]
fn eta_refuses_a_foreign_extensionality() {
    let Stack { mut env, ap, p, fsp, app_pair, .. } = stack();
    let app_mem =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    // `funspace_retarget` is a true theorem over the same stack, quantified the
    // same number of times, and about `fs` — but it is not extensionality.
    let wrong = derived::ext::funspace_retarget(&mut env, &ap, &p, &fsp, &app_pair)
        .expect("funspace_retarget");
    assert!(
        Eta::new(&mut env, &ap, &p, &fsp, &wrong, &app_mem).is_none(),
        "the eta construction accepted a foreign extensionality"
    );
}
