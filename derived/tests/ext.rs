//! Extensionality for lambda graphs.
//!
//! As in `tests/funcs.rs`, every assertion pins the *exact* conclusion. A lemma
//! that is merely equivalent to the intended one is useless downstream, because
//! the next derivation matches formulas syntactically.

use derived::ext::{is_section, lam_ext, lam_ext_same_domain, DProd};
use derived::funcs::{lambda, Apply};
use derived::funspace::{product, Funspace};
use kernel::{Env, FnSym, Formula, Term, Thm};

/// A fresh constant, usable to instantiate a quantifier at.
fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

/// Everything a lambda-extensionality test needs: the application apparatus and
/// two independent body symbols, each with its graph.
struct Two {
    env: Env,
    ap: Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: Thm,
    t2: FnSym,
    lam2: FnSym,
    lam2_ax: Thm,
}

fn prelude() -> Two {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let t = env.declare(1);
    let t2 = env.declare(1);
    let (lam, lam_ax) = lambda(&mut env, &ap, t).expect("lambda");
    let (lam2, lam2_ax) = lambda(&mut env, &ap, t2).expect("lambda");
    Two { env, ap, t, lam, lam_ax, t2, lam2, lam2_ax }
}

/// `∀x. (x ∈ A → t(x) = t'(x))`, the pointwise hypothesis, rebuilt from scratch.
fn pointwise(env: &mut Env, t: FnSym, t2: FnSym, a: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::eq(Term::apply(t, vec![tx.clone()]), Term::apply(t2, vec![tx])),
        ),
    )
}

/// The main lemma, at its exact conclusion.
#[test]
fn lambda_graph_extensionality() {
    let Two { mut env, ap, t, lam, lam_ax, t2, lam2, lam2_ax } = prelude();
    let thm = lam_ext(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, big_a2) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_a2.clone()]).expect("instantiate");

    let expected = Formula::imp(
        Formula::eq(big_a.clone(), big_a2.clone()),
        Formula::imp(
            pointwise(&mut env, t, t2, &big_a),
            Formula::eq(Term::apply(lam, vec![big_a]), Term::apply(lam2, vec![big_a2])),
        ),
    );
    assert_eq!(*inst.concl(), expected, "lam_ext has the wrong shape");
}

/// Both domain quantifiers are really there, not merely instantiable.
#[test]
fn lambda_extensionality_is_fully_quantified() {
    let Two { mut env, ap, t, lam, lam_ax, t2, lam2, lam2_ax } = prelude();
    let thm = lam_ext(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext");

    let mut cur = thm.concl().clone();
    for i in 0..2 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let arg = constant(&mut env);
        cur = Thm::ax_inst(cur, arg).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    let (ante, rest) = cur.as_imp().expect("the domain equation");
    assert!(ante.as_eq().is_some(), "the domain equation must survive");
    let (ante2, concl) = rest.as_imp().expect("the pointwise hypothesis");
    assert!(ante2.is_forall(), "the pointwise hypothesis must survive");
    assert!(concl.as_eq().is_some(), "lam_ext should conclude an equation");
}

/// The same-domain corollary, at its exact conclusion.
#[test]
fn lambda_graph_extensionality_same_domain() {
    let Two { mut env, ap, t, lam, lam_ax, t2, lam2, lam2_ax } = prelude();
    let thm = lam_ext(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext");
    let same = lam_ext_same_domain(&mut env, &thm).expect("lam_ext_same_domain");
    assert!(kernel::thm::debug_locally_closed(same.concl()), "dangling bound variable");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&same, std::slice::from_ref(&big_a)).expect("instantiate");
    let expected = Formula::imp(
        pointwise(&mut env, t, t2, &big_a),
        Formula::eq(Term::apply(lam, vec![big_a.clone()]), Term::apply(lam2, vec![big_a])),
    );
    assert_eq!(*inst.concl(), expected, "lam_ext_same_domain has the wrong shape");
}

/// A body symbol equal to itself gives the graph symbol back on both sides —
/// the degenerate case the checker hits whenever only the domain moved.
#[test]
fn lambda_extensionality_with_one_body() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let t = env.declare(1);
    let (lam, lam_ax) = lambda(&mut env, &ap, t).expect("lambda");

    let thm = lam_ext(&mut env, &ap, t, lam, &lam_ax, t, lam, &lam_ax).expect("lam_ext");
    let (big_a, big_a2) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_a2.clone()]).expect("instantiate");

    let expected = Formula::imp(
        Formula::eq(big_a.clone(), big_a2.clone()),
        Formula::imp(
            pointwise(&mut env, t, t, &big_a),
            Formula::eq(Term::apply(lam, vec![big_a]), Term::apply(lam, vec![big_a2])),
        ),
    );
    assert_eq!(*inst.concl(), expected, "lam_ext has the wrong shape on the diagonal");
}

/// A non-unary body symbol is rejected rather than producing a malformed term.
#[test]
fn lambda_extensionality_rejects_a_bad_arity() {
    let Two { mut env, ap, t, lam, lam_ax, t2, lam2, lam2_ax } = prelude();
    let binary = env.declare(2);
    assert!(lam_ext(&mut env, &ap, binary, lam, &lam_ax, t2, lam2, &lam2_ax).is_none());
    assert!(lam_ext(&mut env, &ap, t, lam, &lam_ax, binary, lam2, &lam2_ax).is_none());
}

/// The corollary refuses anything that is not a `lam_ext` conclusion.
#[test]
fn same_domain_rejects_a_foreign_theorem() {
    let mut env = Env::new();
    // `⊢ ∀u ∀v. u = u` — two quantifiers, but the wrong antecedent shape.
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let refl = derived::gen_all(&[u, v], &Thm::eq_refl(Term::var(u)));
    assert!(lam_ext_same_domain(&mut env, &refl).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// The dependent product.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole stack the dependent product sits on, plus a fibre symbol.
struct Pi {
    env: Env,
    ap: Apply,
    fsp: Funspace,
    b: FnSym,
    dp: DProd,
}

fn pi_prelude() -> Pi {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp = Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p).expect("Funspace::new");
    let b = env.declare(1);
    let dp = DProd::new(&mut env, &ap, &fsp, b).expect("DProd::new");
    Pi { env, ap, fsp, b, dp }
}

/// The base set `⋃{b(x) : x ∈ A}` the product's functions map into.
fn base(ap: &Apply, dp: &DProd, a: &Term) -> Term {
    ap.sets.union_of(Term::apply(dp.img, vec![a.clone()]))
}

/// `L(f)` — "f is a section of the fibration over A".
fn section_cond(env: &mut Env, ap: &Apply, fsp: &Funspace, dp: &DProd, b: FnSym, a: &Term, f: &Term) -> Formula {
    Formula::and(
        Formula::mem(f.clone(), fsp.of(a.clone(), base(ap, dp, a))),
        is_section(env, ap, b, a, f),
    )
}

/// The Replacement image `{ b(x) : x ∈ A }`.
#[test]
fn fibre_image_characterisation() {
    let Pi { mut env, b, dp, .. } = pi_prelude();
    assert!(kernel::thm::debug_locally_closed(dp.img_ax.concl()), "dangling bound variable");
    assert_eq!(dp.img.arity(), 1);

    let big_a = constant(&mut env);
    let w = env.fresh_var();
    let inst = derived::inst_all(&dp.img_ax, &[big_a.clone(), Term::var(w)]).expect("instantiate");
    let x = env.fresh_var();
    let expected = Formula::iff(
        Formula::mem(Term::var(w), Term::apply(dp.img, vec![big_a.clone()])),
        Formula::exists(
            x,
            Formula::and(
                Formula::mem(Term::var(x), big_a),
                Formula::eq(Term::var(w), Term::apply(b, vec![Term::var(x)])),
            ),
        ),
    );
    assert_eq!(*inst.concl(), expected, "image_symbol has the wrong shape");
}

/// The members of `dprod(A)` are exactly the sections — given there is one.
#[test]
fn dependent_product_members() {
    let Pi { mut env, ap, fsp, b, dp } = pi_prelude();
    assert!(kernel::thm::debug_locally_closed(dp.dprod_ax.concl()), "dangling bound variable");
    assert_eq!(dp.dprod.arity(), 1);

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&dp.dprod_ax, std::slice::from_ref(&big_a)).expect("instantiate");

    let (f, g) = (env.fresh_var(), env.fresh_var());
    let l_f = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(f));
    let l_g = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(g));
    let expected = Formula::imp(
        Formula::exists(g, l_g),
        Formula::forall(f, Formula::iff(Formula::mem(Term::var(f), dp.of(big_a)), l_f)),
    );
    assert_eq!(*inst.concl(), expected, "dprod_members has the wrong shape");
}

/// The unconditional half: the product sits inside the function space.
#[test]
fn dependent_product_is_a_set_of_functions() {
    let Pi { mut env, ap, fsp, dp, .. } = pi_prelude();
    assert!(kernel::thm::debug_locally_closed(dp.dprod_sub.concl()), "dangling bound variable");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&dp.dprod_sub, std::slice::from_ref(&big_a)).expect("instantiate");
    let expected = kernel::thm::subset(
        &mut env,
        dp.of(big_a.clone()),
        fsp.of(big_a.clone(), base(&ap, &dp, &big_a)),
    );
    assert_eq!(*inst.concl(), expected, "dprod_subset_funspace has the wrong shape");
}

/// The raw defining axiom really does carry the default disjunct — the symbol
/// is total, which is what `kernel::thm::define` requires.
#[test]
fn dependent_product_definition_is_total() {
    let Pi { mut env, ap, fsp, b, dp } = pi_prelude();
    let big_a = constant(&mut env);
    let f = env.fresh_var();
    let inst = derived::inst_all(&dp.dprod_def, &[big_a.clone(), Term::var(f)]).expect("instantiate");

    let g = env.fresh_var();
    let l_f = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(f));
    let l_g = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(g));
    let default = Formula::and(
        Formula::not(Formula::exists(g, l_g)),
        Formula::mem(Term::var(f), fsp.of(big_a.clone(), base(&ap, &dp, &big_a))),
    );
    let expected = Formula::iff(
        Formula::mem(Term::var(f), dp.of(big_a)),
        Formula::or(l_f, default),
    );
    assert_eq!(*inst.concl(), expected, "dprod's defining axiom has the wrong shape");
}

/// A non-unary fibre symbol is rejected.
#[test]
fn dependent_product_rejects_a_bad_arity() {
    let mut env = Env::new();
    let binary = env.declare(2);
    assert!(derived::ext::image_symbol(&mut env, binary).is_none());
}
