//! Extensionality for lambda graphs.
//!
//! As in `tests/funcs.rs`, every assertion pins the *exact* conclusion. A lemma
//! that is merely equivalent to the intended one is useless downstream, because
//! the next derivation matches formulas syntactically.

use derived::ext::{
    app_of_pair, dprod_const_fibre, dprod_ext, dprod_ext_same_domain, fs_cong, funspace_app_mem,
    funspace_retarget, image_ext, image_symbol, is_section, lam_ext, lam_ext_same_domain,
    values_in, DProd,
};
use derived::funcs::{lambda, Apply};
use derived::funspace::{is_single_valued, product, Funspace, Product};
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

/// `∀x. (x ∈ A → g₁ = g₂)`, the pointwise hypothesis over two arbitrary body
/// terms written in `x`.
fn pointwise_terms(x: kernel::FreeVar, g1: &Term, g2: &Term, a: &Term) -> Formula {
    Formula::forall(
        x,
        Formula::imp(Formula::mem(Term::var(x), a.clone()), Formula::eq(g1.clone(), g2.clone())),
    )
}

/// The general lemma [`lam_ext`] is now an instance of, at its exact
/// conclusion. The two images here are fibre images `{ b(x) : x ∈ A }`, whose
/// bodies are bare applications rather than ordered pairs — the case that
/// showed the argument never used the pair.
#[test]
fn replacement_image_extensionality() {
    let mut env = Env::new();
    let (b, b2) = (env.declare(1), env.declare(1));
    let (img, img_ax) = image_symbol(&mut env, b).expect("image_symbol");
    let (img2, img2_ax) = image_symbol(&mut env, b2).expect("image_symbol");

    let x = env.fresh_var();
    let (bx, b2x) = (Term::apply(b, vec![Term::var(x)]), Term::apply(b2, vec![Term::var(x)]));
    let thm = image_ext(&mut env, x, &bx, img, &img_ax, &b2x, img2, &img2_ax).expect("image_ext");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, big_a2) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_a2.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::eq(big_a.clone(), big_a2.clone()),
        Formula::imp(
            pointwise_terms(x, &bx, &b2x, &big_a),
            Formula::eq(Term::apply(img, vec![big_a]), Term::apply(img2, vec![big_a2])),
        ),
    );
    assert_eq!(*inst.concl(), expected, "image_ext has the wrong shape");
}

/// The characteristic axioms are checked, not assumed: swapping them describes
/// the wrong sets, and that is refused rather than silently derived.
#[test]
fn image_extensionality_rejects_a_foreign_axiom() {
    let mut env = Env::new();
    let (b, b2) = (env.declare(1), env.declare(1));
    let (img, img_ax) = image_symbol(&mut env, b).expect("image_symbol");
    let (img2, img2_ax) = image_symbol(&mut env, b2).expect("image_symbol");

    let x = env.fresh_var();
    let (bx, b2x) = (Term::apply(b, vec![Term::var(x)]), Term::apply(b2, vec![Term::var(x)]));
    assert!(image_ext(&mut env, x, &bx, img, &img2_ax, &b2x, img2, &img_ax).is_none());
    // A body term that is not the one the axiom images is refused too.
    assert!(image_ext(&mut env, x, &b2x, img, &img_ax, &b2x, img2, &img2_ax).is_none());
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
    p: Product,
    fsp: Funspace,
    b: FnSym,
    dp: DProd,
}

fn pi_prelude() -> Pi {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let b = env.declare(1);
    let dp = DProd::new(&mut env, &ap, &fsp, b).expect("DProd::new");
    Pi { env, ap, p, fsp, b, dp }
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

/// The members of `dprod(A)` are exactly the sections — **unconditionally**.
#[test]
fn dependent_product_members() {
    let Pi { mut env, ap, fsp, b, dp, .. } = pi_prelude();
    assert!(kernel::thm::debug_locally_closed(dp.dprod_ax.concl()), "dangling bound variable");
    assert_eq!(dp.dprod.arity(), 1);

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&dp.dprod_ax, std::slice::from_ref(&big_a)).expect("instantiate");

    let f = env.fresh_var();
    let l_f = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(f));
    let expected =
        Formula::forall(f, Formula::iff(Formula::mem(Term::var(f), dp.of(big_a)), l_f));
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

/// The defining axiom carries **no default disjunct**: the condition defined is
/// `L(f)` itself, so `dprod(A)` is the dependent product even when it is empty.
#[test]
fn dependent_product_definition_has_no_default() {
    let Pi { mut env, ap, fsp, b, dp, .. } = pi_prelude();
    let big_a = constant(&mut env);
    let f = env.fresh_var();
    let inst =
        derived::inst_all(&dp.dprod_def, &[big_a.clone(), Term::var(f)]).expect("instantiate");

    let l_f = section_cond(&mut env, &ap, &fsp, &dp, b, &big_a, &Term::var(f));
    let expected = Formula::iff(Formula::mem(Term::var(f), dp.of(big_a)), l_f);
    assert_eq!(*inst.concl(), expected, "dprod's defining axiom has the wrong shape");
}

/// And `dprod_members` refuses a symbol characterised by something else.
#[test]
fn dependent_product_members_rejects_a_foreign_symbol() {
    let Pi { mut env, ap, fsp, b, dp, .. } = pi_prelude();
    let bogus = env.declare(1);
    assert!(
        derived::ext::dprod_members(&mut env, &ap, &fsp, dp.img, b, bogus, &dp.dprod_def)
            .is_none()
    );
    assert!(
        derived::ext::dprod_members(&mut env, &ap, &fsp, dp.img, b, dp.dprod, &dp.img_ax)
            .is_none()
    );
}

/// A non-unary fibre symbol is rejected.
#[test]
fn dependent_product_rejects_a_bad_arity() {
    let mut env = Env::new();
    let binary = env.declare(2);
    assert!(derived::ext::image_symbol(&mut env, binary).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// Dependent product extensionality.
// ─────────────────────────────────────────────────────────────────────────────

/// Two dependent products over the same application apparatus and function
/// space — which is what makes their terms compose at all.
struct TwoPi {
    env: Env,
    ap: Apply,
    p: Product,
    fsp: Funspace,
    b: FnSym,
    dp: DProd,
    b2: FnSym,
    dp2: DProd,
}

fn two_pi_prelude() -> TwoPi {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let (b, b2) = (env.declare(1), env.declare(1));
    let dp = DProd::new(&mut env, &ap, &fsp, b).expect("DProd::new");
    let dp2 = DProd::new(&mut env, &ap, &fsp, b2).expect("DProd::new");
    TwoPi { env, ap, p, fsp, b, dp, b2, dp2 }
}

/// The main lemma, at its exact conclusion.
#[test]
fn dependent_product_extensionality() {
    let TwoPi { mut env, ap, fsp, b, dp, b2, dp2, .. } = two_pi_prelude();
    let thm = dprod_ext(&mut env, &ap, &fsp, b, &dp, b2, &dp2).expect("dprod_ext");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, big_a2) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_a2.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::eq(big_a.clone(), big_a2.clone()),
        Formula::imp(
            pointwise(&mut env, b, b2, &big_a),
            Formula::eq(dp.of(big_a), dp2.of(big_a2)),
        ),
    );
    assert_eq!(*inst.concl(), expected, "dprod_ext has the wrong shape");
}

/// Both domain quantifiers are really there.
#[test]
fn dependent_product_extensionality_is_fully_quantified() {
    let TwoPi { mut env, ap, fsp, b, dp, b2, dp2, .. } = two_pi_prelude();
    let thm = dprod_ext(&mut env, &ap, &fsp, b, &dp, b2, &dp2).expect("dprod_ext");

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
    assert!(concl.as_eq().is_some(), "dprod_ext should conclude an equation");
}

/// The same-domain corollary, at its exact conclusion.
#[test]
fn dependent_product_extensionality_same_domain() {
    let TwoPi { mut env, ap, fsp, b, dp, b2, dp2, .. } = two_pi_prelude();
    let thm = dprod_ext(&mut env, &ap, &fsp, b, &dp, b2, &dp2).expect("dprod_ext");
    let same = dprod_ext_same_domain(&mut env, &thm).expect("dprod_ext_same_domain");
    assert!(kernel::thm::debug_locally_closed(same.concl()), "dangling bound variable");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&same, std::slice::from_ref(&big_a)).expect("instantiate");
    let expected = Formula::imp(
        pointwise(&mut env, b, b2, &big_a),
        Formula::eq(dp.of(big_a.clone()), dp2.of(big_a)),
    );
    assert_eq!(*inst.concl(), expected, "dprod_ext_same_domain has the wrong shape");
}

/// The diagonal: one fibre symbol on both sides, which is what the checker hits
/// when only the domain moved.
#[test]
fn dependent_product_extensionality_with_one_fibre() {
    let Pi { mut env, ap, fsp, b, dp, .. } = pi_prelude();
    let thm = dprod_ext(&mut env, &ap, &fsp, b, &dp, b, &dp).expect("dprod_ext");

    let (big_a, big_a2) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_a2.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::eq(big_a.clone(), big_a2.clone()),
        Formula::imp(
            pointwise(&mut env, b, b, &big_a),
            Formula::eq(dp.of(big_a), dp.of(big_a2)),
        ),
    );
    assert_eq!(*inst.concl(), expected, "dprod_ext has the wrong shape on the diagonal");
}

/// A mismatched fibre symbol is refused: the defining axioms are rebuilt from
/// the symbols handed in and compared, so describing the wrong product is not
/// possible.
#[test]
fn dependent_product_extensionality_rejects_a_mismatch() {
    let TwoPi { mut env, ap, fsp, b, dp, b2, dp2, .. } = two_pi_prelude();
    // `dp` is the product over `b`, not over `b2`.
    assert!(dprod_ext(&mut env, &ap, &fsp, b2, &dp, b2, &dp2).is_none());
    assert!(dprod_ext(&mut env, &ap, &fsp, b, &dp, b, &dp2).is_none());
    let binary = env.declare(2);
    assert!(dprod_ext(&mut env, &ap, &fsp, binary, &dp, b2, &dp2).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// A dependent product over a constant fibre is the function space.
// ─────────────────────────────────────────────────────────────────────────────

/// The value of a single-valued graph at a point it relates, at its exact
/// conclusion. Non-vacuous: the two sides of the equation are `app(f,x)` and
/// `y`, which are different terms.
#[test]
fn application_at_a_pair() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let thm = app_of_pair(&mut env, &ap).expect("app_of_pair");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (f, x, y) = (constant(&mut env), constant(&mut env), constant(&mut env));
    let inst =
        derived::inst_all(&thm, &[f.clone(), x.clone(), y.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::and(
            is_single_valued(&mut env, &ap.sets, &f),
            Formula::mem(ap.sets.pair(x.clone(), y.clone()), f.clone()),
        ),
        Formula::eq(ap.apply(f, x), y.clone()),
    );
    assert_eq!(*inst.concl(), expected, "app_of_pair has the wrong shape");
    let (_, concl) = inst.concl().as_imp().expect("an implication");
    let (lhs, rhs) = concl.as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "app_of_pair would be vacuous");
}

/// A function's values lie in its codomain, at its exact conclusion.
#[test]
fn function_values_lie_in_the_codomain() {
    let Pi { mut env, ap, fsp, p, .. } = pi_prelude();
    let app_pair = app_of_pair(&mut env, &ap).expect("app_of_pair");
    let thm =
        funspace_app_mem(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_app_mem");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (a, b, f, x) =
        (constant(&mut env), constant(&mut env), constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[a.clone(), b.clone(), f.clone(), x.clone()])
        .expect("instantiate");
    let expected = Formula::imp(
        Formula::and(
            Formula::mem(f.clone(), fsp.of(a.clone(), b.clone())),
            Formula::mem(x.clone(), a),
        ),
        Formula::mem(ap.apply(f, x), b),
    );
    assert_eq!(*inst.concl(), expected, "funspace_app_mem has the wrong shape");
}

/// The codomain swap, at its exact conclusion. Non-vacuous: the conclusion
/// names `fs(a,c)` where the hypothesis names `fs(a,b)`, and `b` and `c` are
/// different constants.
#[test]
fn function_space_codomain_may_be_retargeted() {
    let Pi { mut env, ap, p, fsp, .. } = pi_prelude();
    let app_pair = app_of_pair(&mut env, &ap).expect("app_of_pair");
    let thm =
        funspace_retarget(&mut env, &ap, &p, &fsp, &app_pair).expect("funspace_retarget");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (a, b, c, f) =
        (constant(&mut env), constant(&mut env), constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[a.clone(), b.clone(), c.clone(), f.clone()])
        .expect("instantiate");
    let expected = Formula::imp(
        Formula::and(
            Formula::mem(f.clone(), fsp.of(a.clone(), b.clone())),
            values_in(&mut env, &ap, &a, &c, &f),
        ),
        Formula::mem(f.clone(), fsp.of(a.clone(), c.clone())),
    );
    assert_eq!(*inst.concl(), expected, "funspace_retarget has the wrong shape");
    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl, "funspace_retarget would be vacuous");
}

/// The payoff, at its exact conclusion: a dependent product over a constant
/// fibre is the function space.
///
/// Non-vacuous twice over: the two sides of the equation are built by different
/// symbols (`dprod` and `fs`), and the hypothesis is not the conclusion.
#[test]
fn dependent_product_over_a_constant_fibre() {
    let Pi { mut env, ap, p, fsp, b, dp } = pi_prelude();
    let thm = dprod_const_fibre(&mut env, &ap, &p, &fsp, b, &dp).expect("dprod_const_fibre");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, big_b) = (constant(&mut env), constant(&mut env));
    let inst =
        derived::inst_all(&thm, &[big_a.clone(), big_b.clone()]).expect("instantiate");

    let x = env.fresh_var();
    let expected = Formula::imp(
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(Term::var(x), big_a.clone()),
                Formula::eq(Term::apply(b, vec![Term::var(x)]), big_b.clone()),
            ),
        ),
        Formula::eq(dp.of(big_a.clone()), fsp.of(big_a, big_b)),
    );
    assert_eq!(*inst.concl(), expected, "dprod_const_fibre has the wrong shape");

    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    let (lhs, rhs) = concl.as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "dprod_const_fibre would be vacuous");
    assert_ne!(ante, concl, "dprod_const_fibre would be vacuous");
}

/// Both quantifiers are really there, and the fibre hypothesis really survives.
#[test]
fn dependent_product_over_a_constant_fibre_is_fully_quantified() {
    let Pi { mut env, ap, p, fsp, b, dp } = pi_prelude();
    let thm = dprod_const_fibre(&mut env, &ap, &p, &fsp, b, &dp).expect("dprod_const_fibre");

    let mut cur = thm.concl().clone();
    for i in 0..2 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let arg = constant(&mut env);
        cur = Thm::ax_inst(cur, arg).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    let (ante, concl) = cur.as_imp().expect("the fibre hypothesis");
    assert!(ante.is_forall(), "the fibre hypothesis must survive");
    assert!(concl.as_eq().is_some(), "dprod_const_fibre should conclude an equation");
}

/// The stack is checked, not assumed: a `DProd` over some other fibre symbol, or
/// a fibre symbol of the wrong arity, is refused.
#[test]
fn dependent_product_over_a_constant_fibre_rejects_a_mismatch() {
    let TwoPi { mut env, ap, p, fsp, b, dp, b2, dp2 } = two_pi_prelude();
    // The right product and the right fibres go through; crossing them does not.
    assert!(dprod_const_fibre(&mut env, &ap, &p, &fsp, b, &dp).is_some());
    assert!(dprod_const_fibre(&mut env, &ap, &p, &fsp, b, &dp2).is_none());
    assert!(dprod_const_fibre(&mut env, &ap, &p, &fsp, b2, &dp).is_none());
    let binary = env.declare(2);
    assert!(dprod_const_fibre(&mut env, &ap, &p, &fsp, binary, &dp).is_none());

    // A second, unrelated product symbol is refused too: `fs` was not carved
    // out of it, so the function space's members are not its pairs.
    let other = product(&mut env, &ap.sets).expect("product");
    assert!(dprod_const_fibre(&mut env, &ap, &other, &fsp, b, &dp).is_none());
}

/// The degenerate case, discharged rather than assumed away: on the empty
/// domain the fibre hypothesis is vacuously true, so the equation holds
/// outright — `⊢ dprod(∅) = fs(∅,B)` for an arbitrary `B`.
///
/// This is the case a route through `⋃img(A) = B` would have lost, since
/// `⋃img(∅)` is `∅` whatever the fibre and `B` is arbitrary here.
#[test]
fn dependent_product_over_a_constant_fibre_on_the_empty_domain() {
    let Pi { mut env, ap, p, fsp, b, dp } = pi_prelude();
    let thm = dprod_const_fibre(&mut env, &ap, &p, &fsp, b, &dp).expect("dprod_const_fibre");

    let empty = Term::apply(ap.empty, vec![]);
    let big_b = constant(&mut env);
    let inst = derived::inst_all(&thm, &[empty.clone(), big_b.clone()]).expect("instantiate");

    // `∀x. (x ∈ ∅ → b(x) = B)`, from the empty set having no members.
    let x = env.fresh_var();
    let bx = Term::apply(b, vec![Term::var(x)]);
    let not_mem =
        derived::inst_all(&ap.empty_ax, &[Term::var(x)]).expect("the empty set has no members");
    let vacuous = Thm::gen(
        x,
        &derived::syl(&not_mem, &derived::ex_falso(Formula::eq(bx, big_b.clone())))
            .expect("ex falso"),
    );

    let out = Thm::mp(&inst, &vacuous).expect("the hypothesis is vacuously true");
    assert_eq!(
        *out.concl(),
        Formula::eq(dp.of(empty.clone()), fsp.of(empty, big_b)),
        "the empty domain should need no hypothesis at all"
    );
}

/// The non-dependent case: congruence for the function space, in the
/// universally quantified implication form `pi_cong` needs.
#[test]
fn function_space_congruence() {
    let Pi { mut env, fsp, .. } = pi_prelude();
    let thm = fs_cong(&mut env, &fsp).expect("fs_cong");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (a, a2, b, b2) = (
        constant(&mut env),
        constant(&mut env),
        constant(&mut env),
        constant(&mut env),
    );
    let inst = derived::inst_all(&thm, &[a.clone(), a2.clone(), b.clone(), b2.clone()])
        .expect("instantiate");
    let expected = Formula::imp(
        Formula::eq(a.clone(), a2.clone()),
        Formula::imp(
            Formula::eq(b.clone(), b2.clone()),
            Formula::eq(fsp.of(a, b), fsp.of(a2, b2)),
        ),
    );
    assert_eq!(*inst.concl(), expected, "fs_cong has the wrong shape");
}
