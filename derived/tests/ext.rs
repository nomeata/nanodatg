//! Extensionality for lambda graphs.
//!
//! As in `tests/funcs.rs`, every assertion pins the *exact* conclusion. A lemma
//! that is merely equivalent to the intended one is useless downstream, because
//! the next derivation matches formulas syntactically.

use derived::ext::{
    app_of_pair, body_in_fibre, dprod_const_fibre, dprod_ext, dprod_ext_same_domain, fs_cong,
    funspace_app_mem, funspace_retarget, image_ext, image_symbol, is_section, lam_ext,
    lam_ext_same_domain, lam_in_dprod, lam_in_funspace, values_in, DProd,
};
use derived::ext::{dprod_in_universe, dprod_in_universe_of};
use derived::funcs::{beta_conditional, lambda, Apply, Sets};
use derived::funspace::{
    bin_union, funspace_in_universe_of, is_single_valued, mem_bin_union, pair_in_pow_pow, product,
    product_subset_pow_pow, upair_subset, Funspace, Product, Space,
};
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

// ─────────────────────────────────────────────────────────────────────────────
// Lean's lambda typing rule.
// ─────────────────────────────────────────────────────────────────────────────

/// The dependent-product stack together with a body symbol and its graph.
struct Lam {
    env: Env,
    ap: Apply,
    p: Product,
    fsp: Funspace,
    b: FnSym,
    dp: DProd,
    t: FnSym,
    lam: FnSym,
    lam_ax: Thm,
}

fn lam_prelude() -> Lam {
    let Pi { mut env, ap, p, fsp, b, dp } = pi_prelude();
    let t = env.declare(1);
    let (lam, lam_ax) = lambda(&mut env, &ap, t).expect("lambda");
    Lam { env, ap, p, fsp, b, dp, t, lam, lam_ax }
}

/// A lambda graph is a function into any codomain its body lands in, at its
/// exact conclusion.
///
/// Non-vacuous: the hypothesis speaks of `t(x)` and the conclusion of
/// `lam(A) ∈ fs(A,C)`, which are different formulas built by different symbols.
#[test]
fn lambda_graph_is_a_function() {
    let Lam { mut env, ap, p, fsp, t, lam, lam_ax, .. } = lam_prelude();
    let thm =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, big_c) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), big_c.clone()]).expect("instantiate");

    let x = env.fresh_var();
    let expected = Formula::imp(
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(Term::var(x), big_a.clone()),
                Formula::mem(Term::apply(t, vec![Term::var(x)]), big_c.clone()),
            ),
        ),
        Formula::mem(Term::apply(lam, vec![big_a.clone()]), fsp.of(big_a, big_c)),
    );
    assert_eq!(*inst.concl(), expected, "lam_in_funspace has the wrong shape");

    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl, "lam_in_funspace would be vacuous");
}

/// The hypothesis is exactly [`body_in`], and both quantifiers are really there.
#[test]
fn lambda_graph_is_a_function_is_fully_quantified() {
    let Lam { mut env, ap, p, fsp, t, lam, lam_ax, .. } = lam_prelude();
    let thm =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");

    let mut cur = thm.concl().clone();
    for i in 0..2 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let arg = constant(&mut env);
        cur = Thm::ax_inst(cur, arg).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    let (ante, concl) = cur.as_imp().expect("the pointwise hypothesis");
    assert!(ante.is_forall(), "the pointwise hypothesis must survive");
    assert!(concl.as_mem().is_some(), "lam_in_funspace should conclude a membership");
    let _ = (lam, t);
}

/// The empty domain needs no hypothesis at all: `⊢ lam(∅) ∈ fs(∅,C)` for an
/// arbitrary `C`. Nothing in the derivation asks for an inhabitant.
#[test]
fn lambda_graph_on_the_empty_domain_is_a_function() {
    let Lam { mut env, ap, p, fsp, t, lam, lam_ax, .. } = lam_prelude();
    let thm =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");

    let empty = Term::apply(ap.empty, vec![]);
    let big_c = constant(&mut env);
    let inst =
        derived::inst_all(&thm, &[empty.clone(), big_c.clone()]).expect("instantiate");

    let x = env.fresh_var();
    let tx_val = Term::apply(t, vec![Term::var(x)]);
    let not_mem =
        derived::inst_all(&ap.empty_ax, &[Term::var(x)]).expect("the empty set has no members");
    let vacuous = Thm::gen(
        x,
        &derived::syl(&not_mem, &derived::ex_falso(Formula::mem(tx_val, big_c.clone())))
            .expect("ex falso"),
    );
    let out = Thm::mp(&inst, &vacuous).expect("the hypothesis is vacuously true");
    assert_eq!(
        *out.concl(),
        Formula::mem(Term::apply(lam, vec![empty.clone()]), fsp.of(empty, big_c)),
        "the empty domain should need no hypothesis at all"
    );
}

/// The stack is checked, not assumed.
#[test]
fn lambda_graph_is_a_function_rejects_a_mismatch() {
    let Lam { mut env, ap, p, fsp, t, lam, lam_ax, .. } = lam_prelude();
    // A second body symbol with its own graph: crossing the two is refused.
    let t2 = env.declare(1);
    let (lam2, lam2_ax) = lambda(&mut env, &ap, t2).expect("lambda");
    assert!(lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam2_ax).is_none());
    assert!(lam_in_funspace(&mut env, &ap, &p, &fsp, t2, lam, &lam_ax).is_none());
    assert!(lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam2, &lam_ax).is_none());
    let binary = env.declare(2);
    assert!(lam_in_funspace(&mut env, &ap, &p, &fsp, binary, lam, &lam_ax).is_none());

    // A second, unrelated product symbol: `fs` was not carved out of it.
    let other = product(&mut env, &ap.sets).expect("product");
    assert!(lam_in_funspace(&mut env, &ap, &other, &fsp, t, lam, &lam_ax).is_none());
}

/// **Lean's lambda typing rule**, at its exact conclusion.
///
/// Non-vacuous: the hypothesis is a universally quantified membership about
/// `t(x)` and `b(x)`, the conclusion a single membership about `lam(A)` and
/// `dprod(A)` — different formulas over different symbols.
#[test]
fn lambda_graph_is_in_the_dependent_product() {
    let Lam { mut env, ap, p, fsp, b, dp, t, lam, lam_ax } = lam_prelude();
    let beta = beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");
    let lam_fs =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");
    let thm = lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta, &lam_fs)
        .expect("lam_in_dprod");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&big_a)).expect("instantiate");

    let x = env.fresh_var();
    let expected = Formula::imp(
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(Term::var(x), big_a.clone()),
                Formula::mem(
                    Term::apply(t, vec![Term::var(x)]),
                    Term::apply(b, vec![Term::var(x)]),
                ),
            ),
        ),
        Formula::mem(Term::apply(lam, vec![big_a.clone()]), dp.of(big_a)),
    );
    assert_eq!(*inst.concl(), expected, "lam_in_dprod has the wrong shape");

    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl, "lam_in_dprod would be vacuous");
    let (lhs, rhs) = concl.as_mem().expect("a membership");
    assert_ne!(lhs, rhs, "lam_in_dprod would be vacuous");
}

/// The hypothesis is exactly [`body_in_fibre`], rebuilt from scratch.
#[test]
fn lambda_typing_rule_hypothesis_is_the_pointwise_fibre_condition() {
    let Lam { mut env, ap, p, fsp, b, dp, t, lam, lam_ax } = lam_prelude();
    let beta = beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");
    let lam_fs =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");
    let thm = lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta, &lam_fs)
        .expect("lam_in_dprod");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&big_a)).expect("instantiate");
    let (ante, _) = inst.concl().as_imp().expect("an implication");
    assert_eq!(ante, body_in_fibre(&mut env, t, b, &big_a), "the hypothesis has drifted");
}

/// The empty domain again: `⊢ lam(∅) ∈ dprod(∅)`, with the hypothesis vacuous.
#[test]
fn lambda_graph_on_the_empty_domain_is_in_the_dependent_product() {
    let Lam { mut env, ap, p, fsp, b, dp, t, lam, lam_ax } = lam_prelude();
    let beta = beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");
    let lam_fs =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");
    let thm = lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta, &lam_fs)
        .expect("lam_in_dprod");

    let empty = Term::apply(ap.empty, vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&empty)).expect("instantiate");

    let x = env.fresh_var();
    let goal = Formula::mem(
        Term::apply(t, vec![Term::var(x)]),
        Term::apply(b, vec![Term::var(x)]),
    );
    let not_mem =
        derived::inst_all(&ap.empty_ax, &[Term::var(x)]).expect("the empty set has no members");
    let vacuous =
        Thm::gen(x, &derived::syl(&not_mem, &derived::ex_falso(goal)).expect("ex falso"));
    let out = Thm::mp(&inst, &vacuous).expect("the hypothesis is vacuously true");
    assert_eq!(
        *out.concl(),
        Formula::mem(Term::apply(lam, vec![empty.clone()]), dp.of(empty)),
        "the empty domain should need no hypothesis at all"
    );
}

/// Every ingredient is checked: a foreign beta theorem, a foreign function-space
/// membership, a `DProd` over another fibre, or a bad arity is refused.
#[test]
fn lambda_typing_rule_rejects_a_mismatch() {
    let TwoPi { mut env, ap, p, fsp, b, dp, b2, dp2 } = two_pi_prelude();
    let t = env.declare(1);
    let (lam, lam_ax) = lambda(&mut env, &ap, t).expect("lambda");
    let t2 = env.declare(1);
    let (lam2, lam2_ax) = lambda(&mut env, &ap, t2).expect("lambda");

    let beta = beta_conditional(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional");
    let beta2 = beta_conditional(&mut env, &ap, t2, lam2, &lam2_ax).expect("beta_conditional");
    let lam_fs =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t, lam, &lam_ax).expect("lam_in_funspace");
    let lam_fs2 =
        lam_in_funspace(&mut env, &ap, &p, &fsp, t2, lam2, &lam2_ax).expect("lam_in_funspace");

    assert!(lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta, &lam_fs).is_some());
    // The `DProd` must be the one over `b`.
    assert!(lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp2, &beta, &lam_fs).is_none());
    assert!(lam_in_dprod(&mut env, &ap, &fsp, t, lam, b2, &dp, &beta, &lam_fs).is_none());
    // The beta theorem and the function-space membership must be this graph's.
    assert!(lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta2, &lam_fs).is_none());
    assert!(lam_in_dprod(&mut env, &ap, &fsp, t, lam, b, &dp, &beta, &lam_fs2).is_none());
    let binary = env.declare(2);
    assert!(lam_in_dprod(&mut env, &ap, &fsp, binary, lam, b, &dp, &beta, &lam_fs).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// Lean's Π typing rule: the dependent product lands in a universe.
// ─────────────────────────────────────────────────────────────────────────────

/// The dependent-product stack, together with the universe apparatus built over
/// the *same* pairing and union symbols.
///
/// `Space::new` and `Apply::new` each introduce their own [`Sets`], and two
/// `Sets` are two unrelated definitional extensions — so the `Space` here is
/// assembled by hand from `Apply`'s, which is what makes every term compose.
struct Uni {
    env: Env,
    ap: Apply,
    fsp: Funspace,
    dp: DProd,
    lu: FnSym,
    c2: Thm,
    mem_lu: Thm,
    fs_in_u: Thm,
}

fn uni_prelude() -> Uni {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let b = env.declare(1);
    let dp = DProd::new(&mut env, &ap, &fsp, b).expect("DProd::new");

    let union_sing = derived::union_singleton(
        &mut env,
        ap.sets.up,
        &ap.sets.up_ax,
        ap.sets.un,
        &ap.sets.un_ax,
    )
    .expect("union_singleton");
    let (lu, lu_ax) = derived::universe::least_universe(&mut env).expect("least_universe");
    let mem_lu =
        derived::universe::mem_least_universe(&mut env, lu, &lu_ax).expect("mem_least_universe");
    let c2 = derived::universe::least_universe_closed_sub(&mut env, lu, &lu_ax).expect("C₂");
    let c3 = derived::universe::least_universe_closed_pow(&mut env, lu, &lu_ax, pow, &pow_ax)
        .expect("C₃");

    let space = Space {
        sets: Sets {
            up: ap.sets.up,
            up_ax: ap.sets.up_ax.clone(),
            un: ap.sets.un,
            un_ax: ap.sets.un_ax.clone(),
        },
        pow,
        pow_ax: pow_ax.clone(),
        union_sing,
        empty: ap.empty,
        empty_ax: ap.empty_ax.clone(),
        lu,
        lu_ax,
        mem_lu: mem_lu.clone(),
        c2: c2.clone(),
        c3,
        pair_inj: ap.pair_inj.clone(),
    };

    let up_sub = upair_subset(&mut env, &ap.sets).expect("upair_subset");
    let pair_pp =
        pair_in_pow_pow(&mut env, &ap.sets, pow, &pow_ax, &up_sub).expect("pair_in_pow_pow");
    let (ml, mr) = mem_bin_union(&mut env, &ap.sets).expect("mem_bin_union");
    let prod_sub =
        product_subset_pow_pow(&mut env, &ap.sets, pow, &p, &pair_pp, &ml, &mr).expect("prod_sub");
    let fs_in_u = funspace_in_universe_of(&mut env, &space, &p, &prod_sub, &fsp)
        .expect("funspace_in_universe_of");

    Uni { env, ap, fsp, dp, lu, c2, mem_lu, fs_in_u }
}

/// The reduction, at its exact conclusion: the antecedent is the *same* one
/// `funspace_in_universe_of` carries, and nothing else is assumed.
///
/// Non-vacuous: the antecedent is a membership of `A ∪ ⋃img(A)`, the conclusion
/// one of `dprod(A)` — different terms, and neither is the other.
#[test]
fn dependent_product_lands_in_a_universe_over_its_base() {
    let Uni { mut env, ap, fsp, dp, lu, c2, fs_in_u, .. } = uni_prelude();
    let thm = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (big_a, c) = (constant(&mut env), constant(&mut env));
    let inst = derived::inst_all(&thm, &[big_a.clone(), c.clone()]).expect("instantiate");

    let base_a = base(&ap, &dp, &big_a);
    let un = bin_union(&ap.sets, big_a.clone(), base_a);
    let w = Term::apply(lu, vec![c]);
    let expected = Formula::imp(
        Formula::mem(un.clone(), w.clone()),
        Formula::mem(dp.of(big_a), w),
    );
    assert_eq!(*inst.concl(), expected, "dprod_in_universe_of has the wrong shape");

    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl, "dprod_in_universe_of would be vacuous");
}

/// Both quantifiers are really there.
#[test]
fn dependent_product_in_a_universe_is_fully_quantified() {
    let Uni { mut env, ap, fsp, dp, lu, c2, fs_in_u, .. } = uni_prelude();
    let thm = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");

    let mut cur = thm.concl().clone();
    for i in 0..2 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let arg = constant(&mut env);
        cur = Thm::ax_inst(cur, arg).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    let (ante, concl) = cur.as_imp().expect("the base-set antecedent");
    assert!(ante.as_mem().is_some(), "the antecedent must survive as a membership");
    assert!(concl.as_mem().is_some(), "dprod_in_universe_of should conclude a membership");
}

/// **The payoff**: `⊢ ∀A. dprod(A) ∈ U(A ∪ ⋃img(A))`, with no hypothesis at all.
///
/// Non-vacuous: the two sides of the membership are built by different symbols,
/// and there is no antecedent left to hide behind.
#[test]
fn dependent_product_lands_in_a_universe_unconditionally() {
    let Uni { mut env, ap, fsp, dp, lu, c2, mem_lu, fs_in_u } = uni_prelude();
    let general = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");
    let thm = dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu, &general)
        .expect("dprod_in_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let big_a = constant(&mut env);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&big_a)).expect("instantiate");

    let un = bin_union(&ap.sets, big_a.clone(), base(&ap, &dp, &big_a));
    let expected =
        Formula::mem(dp.of(big_a.clone()), Term::apply(lu, vec![un]));
    assert_eq!(*inst.concl(), expected, "dprod_in_universe has the wrong shape");

    // No implication: this really is unconditional.
    assert!(inst.concl().as_imp().is_none(), "dprod_in_universe should carry no antecedent");
    let (lhs, rhs) = inst.concl().as_mem().expect("a membership");
    assert_ne!(lhs, rhs, "dprod_in_universe would be vacuous");
}

/// The ingredients are checked: `C₂`, the function-space chain and
/// `mem_least_universe` are each rebuilt at our own terms and compared, so a
/// theorem about some other universe operator is refused.
#[test]
fn dependent_product_in_a_universe_rejects_a_mismatch() {
    let Uni { mut env, ap, fsp, dp, lu, c2, mem_lu, fs_in_u } = uni_prelude();
    // A second, unrelated universe operator: its `C₂` is about `U'`, not `U`.
    let (lu2, lu2_ax) = derived::universe::least_universe(&mut env).expect("least_universe");
    let c2b = derived::universe::least_universe_closed_sub(&mut env, lu2, &lu2_ax).expect("C₂");
    let mem_lu2 =
        derived::universe::mem_least_universe(&mut env, lu2, &lu2_ax).expect("mem_least_universe");

    assert!(dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2b, &fs_in_u).is_none());
    assert!(dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu2, &c2b, &fs_in_u).is_none());
    // Swapping the two theorems around is refused too.
    assert!(dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &fs_in_u, &c2).is_none());

    let general = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");
    assert!(dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu2, &general).is_none());
    assert!(dprod_in_universe(&mut env, &ap, &dp, lu2, &mem_lu2, &general).is_none());
    assert!(dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu, &general).is_some());
}

// ─────────────────────────────────────────────────────────────────────────────
// The dependent `Π` typing rule with its antecedent discharged.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(x) ∈ U(c))) → dprod(A) ∈ U(c))` — the
/// form the checker wants, with `(A ∪ ⋃img(A)) ∈ U(c)` discharged by
/// Replacement, `⋃` and binary-union closure.
///
/// Non-vacuous twice over: the antecedent and the conclusion are about
/// different terms, and the antecedent is *satisfied* at `c := A ∪ ⋃img(A)`
/// only if the fibres are — so the test also checks the constant-fibre case,
/// where `b(x) ∈ U(c)` is discharged for every `x` at once.
#[test]
fn the_dependent_product_typing_rule_needs_no_union_antecedent() {
    use derived::universe as uni;

    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("Apply::new");
    let (pow, pow_ax) = derived::power(&mut env);
    let p = product(&mut env, &ap.sets).expect("product");
    let fsp =
        Funspace::new(&mut env, &ap.sets, pow, &pow_ax, &p, &ap.empty_ax).expect("Funspace::new");
    let b = env.declare(1);
    let dp = DProd::new(&mut env, &ap, &fsp, b).expect("DProd::new");

    let union_sing = derived::union_singleton(
        &mut env, ap.sets.up, &ap.sets.up_ax, ap.sets.un, &ap.sets.un_ax,
    )
    .expect("union_singleton");
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("least_universe");
    let mem_lu = uni::mem_least_universe(&mut env, lu, &lu_ax).expect("mem_least_universe");
    let c2 = uni::least_universe_closed_sub(&mut env, lu, &lu_ax).expect("C₂");
    let c3 = uni::least_universe_closed_pow(&mut env, lu, &lu_ax, pow, &pow_ax).expect("C₃");

    let space = Space {
        sets: ap.sets.clone(),
        pow,
        pow_ax: pow_ax.clone(),
        union_sing,
        empty: ap.empty,
        empty_ax: ap.empty_ax.clone(),
        lu,
        lu_ax: lu_ax.clone(),
        mem_lu,
        c2: c2.clone(),
        c3,
        pair_inj: ap.pair_inj.clone(),
    };
    let up_sub = upair_subset(&mut env, &ap.sets).expect("upair_subset");
    let pair_pp =
        pair_in_pow_pow(&mut env, &ap.sets, pow, &pow_ax, &up_sub).expect("pair_in_pow_pow");
    let (ml, mr) = mem_bin_union(&mut env, &ap.sets).expect("mem_bin_union");
    let prod_sub =
        product_subset_pow_pow(&mut env, &ap.sets, pow, &p, &pair_pp, &ml, &mr).expect("prod_sub");
    let fs_in_u = funspace_in_universe_of(&mut env, &space, &p, &prod_sub, &fsp)
        .expect("funspace_in_universe_of");
    let general = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");

    // The three closure properties the antecedent was waiting on.
    let pairing = uni::universe_pairing(
        &mut env, ap.sets.up, &ap.sets.up_ax, ap.empty, &ap.empty_ax, pow, &pow_ax,
    )
    .expect("universe_pairing");
    let mem_mem = uni::universe_mem_mem(&mut env).expect("universe_mem_mem");
    let two_cycle =
        derived::empty::no_two_cycle(&mut env, ap.sets.up, &ap.sets.up_ax).expect("no_two_cycle");
    let union_closed =
        uni::universe_union_closed(&mut env, &ap.sets, &ap.empty_ax, &mem_mem, &two_cycle)
            .expect("universe_union_closed");
    let least_union = uni::least_universe_union(&mut env, lu, &lu_ax, ap.sets.un, &union_closed)
        .expect("least_universe_union");
    let least_pairing = uni::least_universe_pairing(&mut env, lu, &lu_ax, ap.sets.up, &pairing)
        .expect("least_universe_pairing");
    let least_bin_union =
        uni::least_universe_bin_union(&mut env, lu, &ap.sets, &least_pairing, &least_union)
            .expect("least_universe_bin_union");
    let replacement =
        uni::universe_replacement(&mut env, &ap.empty_ax, dp.img, &dp.img_ax, b)
            .expect("universe_replacement");
    let least_replacement =
        uni::least_universe_replacement(&mut env, lu, &lu_ax, dp.img, b, &replacement)
            .expect("least_universe_replacement");

    let thm = derived::ext::dprod_in_universe_pair(
        &mut env,
        &ap,
        &dp,
        lu,
        b,
        &least_replacement,
        &least_union,
        &least_bin_union,
        &general,
    )
    .expect("dprod_in_universe_pair");
    assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

    let (c, big_a) = (env.fresh_var(), env.fresh_var());
    let (tc, ta) = (Term::var(c), Term::var(big_a));
    let w = Term::apply(lu, vec![tc.clone()]);
    let expected = Formula::imp(
        Formula::and(
            Formula::mem(ta.clone(), w.clone()),
            uni::fibres_in(&mut env, b, &ta, &w),
        ),
        Formula::mem(dp.of(ta.clone()), w.clone()),
    );
    let inst = derived::inst_all(&thm, &[tc, ta.clone()]).expect("instantiate");
    assert_eq!(*inst.concl(), expected, "dprod_in_universe_pair has the wrong shape");

    // The antecedent no longer mentions `A ∪ ⋃img(A)` at all — that is the
    // whole point — and it is not the conclusion.
    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl, "dprod_in_universe_pair would be vacuous");
    // And the antecedent of the *reduction* it replaces really is the union
    // membership, so the two statements are genuinely different.
    let un = bin_union(&ap.sets, ta.clone(), base(&ap, &dp, &ta));
    let old = derived::inst_all(&general, &[ta.clone(), Term::var(c)]).expect("instantiate");
    assert_eq!(old.concl().as_imp().expect("an implication").0, Formula::mem(un, w));
    assert_ne!(ante, old.concl().as_imp().expect("an implication").0);

    // A theorem that is not the reduction is refused.
    assert!(derived::ext::dprod_in_universe_pair(
        &mut env, &ap, &dp, lu, b, &least_replacement, &least_union, &least_bin_union, &fs_in_u,
    )
    .is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// Release-checked claims: the legs that used to be `debug_assert`s only.
//
// CI's test sweeps run in the debug profile, so a `debug_assert` does fire
// there. What loses them is the *release* measurement path — `scripts/arena.sh`,
// the `stepcount` binary, `cargo build --release` — i.e. exactly the runs that
// produce the headline numbers. A pin that carries the function's advertised
// claim therefore has to be a real check, and a `&Thm` argument has to be
// required unconditional as well as pinned, since `Thm::mp` unions `Γ`s
// silently and `concl()` cannot see them.
// ─────────────────────────────────────────────────────────────────────────────

/// `thm` weakened to hold only under `scope`: same conclusion, `Γ = {scope}`.
fn under_scope(thm: &Thm, scope: &Formula) -> Thm {
    let w = Thm::mp(&derived::a1i(thm, scope.clone()), &Thm::assume(scope.clone()))
        .expect("weaken into an open scope hypothesis");
    assert_eq!(*w.concl(), *thm.concl(), "weakening must not change the conclusion");
    assert!(!w.hyps().is_empty(), "weakening must leave a Γ behind");
    w
}

/// [`dprod_subset_funspace`] states `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`, so a
/// defining axiom that only holds under an open hypothesis must be refused.
///
/// Nothing here used to read `dp_def`'s hypothesis set, and the two shape
/// checks that would have caught a *wrong* axiom were `debug_assert`s — so in
/// release this was unpinned in both directions at once.
#[test]
fn the_subset_lemma_refuses_a_hypothetical_defining_axiom() {
    let Pi { mut env, ap, fsp, b, dp, .. } = pi_prelude();
    let scope = Formula::mem(Term::var(env.fresh_var()), constant(&mut env));

    // The genuine defining axiom still works.
    let good = derived::ext::dprod_subset_funspace(
        &mut env, &ap, &fsp, dp.img, b, dp.dprod, &dp.dprod_def,
    )
    .expect("the unconditional axiom proves the inclusion");
    assert!(good.hyps().is_empty());

    let bad = under_scope(&dp.dprod_def, &scope);
    assert!(
        derived::ext::dprod_subset_funspace(&mut env, &ap, &fsp, dp.img, b, dp.dprod, &bad)
            .is_none(),
        "a Γ-carrying defining axiom must not yield a theorem labelled ⊢"
    );

    // And an axiom about some other dependent product is refused rather than
    // described — the check that used to be a `debug_assert`.
    let b2 = env.declare(1);
    let dp2 = DProd::new(&mut env, &ap, &fsp, b2).expect("DProd::new");
    assert!(
        derived::ext::dprod_subset_funspace(
            &mut env, &ap, &fsp, dp.img, b, dp.dprod, &dp2.dprod_def
        )
        .is_none(),
        "a foreign defining axiom"
    );
}

/// [`dprod_in_universe`] states `⊢ ∀A. dprod(A) ∈ U(A ∪ ⋃img(A))`, and
/// `general` is never pinned before use — the `mp` constrains its *antecedent*
/// only. So the check on the result is the sole thing tying the output to the
/// header, in both its halves.
#[test]
fn the_unconditional_universe_lemma_pins_its_own_result() {
    let Uni { mut env, ap, fsp, dp, lu, c2, mem_lu, fs_in_u } = uni_prelude();
    let general = dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u)
        .expect("dprod_in_universe_of");
    assert!(
        dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu, &general).is_some(),
        "the genuine pair goes through"
    );

    // ── A `general` with the right antecedent and the wrong consequent ───────
    //
    // `∀A ∀c. (H → H)` instantiates to `H → H`, whose antecedent is exactly
    // what `mem_least_universe` supplies — so the `mp` succeeds and the result
    // concludes `A ∪ ⋃img(A) ∈ U(c)` rather than `dprod(A) ∈ U(c)`. Nothing
    // but the result check can notice.
    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let un = bin_union(&ap.sets, ta.clone(), base(&ap, &dp, &ta));
    let h = Formula::mem(un, Term::apply(lu, vec![tc]));
    let bogus = derived::gen_all(&[av, cv], &derived::imp_refl(h));
    assert!(
        dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu, &bogus).is_none(),
        "a lemma whose consequent is not the dependent product's membership"
    );

    // ── A `general` that holds only under an open hypothesis ────────────────
    let scope = Formula::mem(Term::var(env.fresh_var()), constant(&mut env));
    let bad_general = under_scope(&general, &scope);
    assert!(
        dprod_in_universe(&mut env, &ap, &dp, lu, &mem_lu, &bad_general).is_none(),
        "a Γ-carrying reduction must not produce an unconditional membership"
    );
    let bad_mem_lu = under_scope(&mem_lu, &scope);
    assert!(
        dprod_in_universe(&mut env, &ap, &dp, lu, &bad_mem_lu, &general).is_none(),
        "…nor a Γ-carrying self-membership"
    );
}

/// The same, for the conditional form: its three premises are each pinned in
/// release already, but none of them was required to be hypothesis-free.
#[test]
fn the_conditional_universe_lemma_refuses_hypothetical_premises() {
    let Uni { mut env, ap, fsp, dp, lu, c2, fs_in_u, .. } = uni_prelude();
    let scope = Formula::mem(Term::var(env.fresh_var()), constant(&mut env));
    assert!(
        dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &fs_in_u).is_some(),
        "the genuine stack goes through"
    );

    let bad_c2 = under_scope(&c2, &scope);
    assert!(
        dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &bad_c2, &fs_in_u).is_none(),
        "a Γ-carrying C₂"
    );
    let bad_fs = under_scope(&fs_in_u, &scope);
    assert!(
        dprod_in_universe_of(&mut env, &ap, &fsp, &dp, lu, &c2, &bad_fs).is_none(),
        "a Γ-carrying function-space chain"
    );
    let mut bad_dp = dp;
    bad_dp.dprod_sub = under_scope(&bad_dp.dprod_sub, &scope);
    assert!(
        dprod_in_universe_of(&mut env, &ap, &fsp, &bad_dp, lu, &c2, &fs_in_u).is_none(),
        "a Γ-carrying DProd::dprod_sub"
    );
}
