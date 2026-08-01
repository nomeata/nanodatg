//! The dependent product and Lean's `Π` typing rule over a fibre family
//! carrying a **parameter prefix** — [`derived::ext::dprod_n`],
//! [`derived::ext::dprod_universe_n`] and
//! [`derived::universe::replacement_n`].
//!
//! Every assertion pins the **exact** conclusion, rebuilt from scratch rather
//! than read off the theorem: the next derivation matches formulas
//! syntactically, so a lemma that is merely equivalent to the intended one is
//! useless. Three kinds of assertion appear, and all three matter:
//!
//! * that the prefixed statements are the intended ones at a genuine `k > 0`;
//! * that at `k = 0` they **coincide with the unary originals**, so the two
//!   cannot drift apart;
//! * that a foreign stack is refused (`None`) rather than described, and that
//!   the conditional rule's antecedent is actually dischargeable — otherwise
//!   the whole file could be vacuous.

use derived::ext::{
    dprod_in_universe_of_n, dprod_in_universe_pair_n, image_symbol_n, is_section, section_n,
    DProdN, UniverseParts,
};
use derived::funcs::Apply;
use derived::funspace::{bin_union, Funspace, Space};
use derived::tower::Tower;
use derived::universe as uni;
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

/// A fresh constant, usable to instantiate a quantifier at.
fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

/// `f(q⃗, a)`.
fn at(f: FnSym, prefix: &[Term], a: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(a);
    Term::apply(f, v)
}

/// The apparatus every test needs: one `Apply`, one `Space`, one `Funspace`,
/// all over the same pairing.
struct Kit {
    ap: Apply,
    space: Space,
    fs: Funspace,
}

fn kit(env: &mut Env) -> Kit {
    let ap = Apply::new(env).expect("Apply::new");
    let space = Space::with_apply(env, &ap).expect("Space::with_apply");
    let prod = derived::funspace::product(env, &space.sets).expect("product");
    let fs = Funspace::new(env, &space.sets, space.pow, &space.pow_ax, &prod, &space.empty_ax)
        .expect("Funspace::new");
    Kit { ap, space, fs }
}

// ─────────────────────────────────────────────────────────────────────────────
// The symbols.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀q⃗ ∀A ∀w. (w ∈ img(q⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(q⃗,x)))` — the Replacement
/// image, at a genuine two-parameter prefix.
#[test]
fn the_prefixed_image_has_its_defining_property() {
    let mut env = Env::new();
    let k = kit(&mut env);
    let b = env.declare(3); // two parameters plus the binder
    let dp = DProdN::new(&mut env, &k.ap, &k.fs, b).expect("DProdN::new");
    assert_eq!(dp.k, 2);

    let (q1, q2) = (constant(&mut env), constant(&mut env));
    let qts = [q1, q2];
    let (big_a, w) = (constant(&mut env), constant(&mut env));

    let x = env.fresh_var();
    let tx = Term::var(x);
    let img_at =
        derived::inst_all(&dp.img_ax, &[qts[0].clone(), qts[1].clone(), big_a.clone(), w.clone()])
            .expect("instantiate img_ax");
    assert_eq!(
        *img_at.concl(),
        Formula::iff(
            Formula::mem(w.clone(), dp.img_of(&qts, big_a.clone())),
            Formula::exists(
                x,
                Formula::and(
                    Formula::mem(tx.clone(), big_a),
                    Formula::eq(w, at(b, &qts, tx)),
                ),
            ),
        ),
    );
}

/// The image and product axioms, pinned by rebuilding the *conditions* rather
/// than by guessing the witness terms.
#[test]
fn the_prefixed_product_is_carved_out_of_the_right_function_space() {
    let mut env = Env::new();
    let k = kit(&mut env);
    let b = env.declare(3);
    let dp = DProdN::new(&mut env, &k.ap, &k.fs, b).expect("DProdN::new");

    let (q1, q2) = (constant(&mut env), constant(&mut env));
    let qts = [q1, q2];
    let big_a = constant(&mut env);
    let f = constant(&mut env);

    let base = k.ap.sets.union_of(dp.img_of(&qts, big_a.clone()));
    let fs_t = k.fs.of(big_a.clone(), base);
    let sec = section_n(&mut env, &k.ap, b, &qts, &big_a, &f);
    let l = Formula::and(Formula::mem(f.clone(), fs_t.clone()), sec);

    let at_f = derived::inst_all(
        &dp.dprod_ax,
        &[qts[0].clone(), qts[1].clone(), big_a.clone(), f.clone()],
    )
    .expect("instantiate dprod_ax");
    assert_eq!(*at_f.concl(), Formula::iff(Formula::mem(f, dp.of(&qts, big_a.clone())), l));

    // And the inclusion the universe argument runs on.
    let sub = derived::inst_all(&dp.dprod_sub, &[qts[0].clone(), qts[1].clone(), big_a.clone()])
        .expect("instantiate dprod_sub");
    assert_eq!(*sub.concl(), kernel::thm::subset(&mut env, dp.of(&qts, big_a), fs_t));
}

/// At `k = 0` the prefixed constructions **are** the unary ones: `section_n`
/// with an empty prefix is [`derived::ext::is_section`], and `fibres_in_n` is
/// [`derived::universe::fibres_in`]. Bound variables are de Bruijn, so these are
/// equalities of formulas, not merely alpha-equivalences.
#[test]
fn the_nullary_prefix_reproduces_the_unary_definitions() {
    let mut env = Env::new();
    let k = kit(&mut env);
    let b = env.declare(1);
    let (big_a, f, u) = (constant(&mut env), constant(&mut env), constant(&mut env));

    assert_eq!(
        section_n(&mut env, &k.ap, b, &[], &big_a, &f),
        is_section(&mut env, &k.ap, b, &big_a, &f),
    );
    assert_eq!(
        uni::fibres_in_n(&mut env, b, &[], &big_a, &u),
        uni::fibres_in(&mut env, b, &big_a, &u),
    );

    // The whole product, at an empty prefix, is the unary one's statement: the
    // condition `L(f)` is rebuilt from the *unary* `is_section` and matches.
    let dp = DProdN::new(&mut env, &k.ap, &k.fs, b).expect("DProdN::new");
    assert_eq!(dp.k, 0);
    let base = k.ap.sets.union_of(dp.img_of(&[], big_a.clone()));
    let fs_t = k.fs.of(big_a.clone(), base);
    let l = Formula::and(
        Formula::mem(f.clone(), fs_t),
        is_section(&mut env, &k.ap, b, &big_a, &f),
    );
    let at_f = derived::inst_all(&dp.dprod_ax, &[big_a.clone(), f.clone()]).expect("instantiate");
    assert_eq!(*at_f.concl(), Formula::iff(Formula::mem(f, dp.of(&[], big_a)), l));

    // And the arity discipline: a nullary symbol has no binder argument.
    let nullary = env.declare(0);
    assert!(image_symbol_n(&mut env, nullary).is_none());
    assert!(DProdN::new(&mut env, &k.ap, &k.fs, nullary).is_none());
}

/// The `Π` rule at an **empty prefix** is the unary
/// [`derived::ext::dprod_in_universe_pair`]'s statement, rebuilt with the unary
/// [`derived::universe::fibres_in`]. The n-ary port therefore extends the
/// original rather than sitting beside it.
#[test]
fn the_nary_pi_rule_at_an_empty_prefix_is_the_unary_rule() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let b = env.declare(1);
    let pi = pi_rule(&mut env, &t, b).expect("pi_rule");

    let (c, big_a) = (constant(&mut env), constant(&mut env));
    let w = Term::apply(t.space.lu, vec![c.clone()]);
    let fib = uni::fibres_in(&mut env, b, &big_a, &w);
    let inst = derived::inst_all(&pi.rule, &[c, big_a.clone()]).expect("instantiate");
    assert_eq!(
        *inst.concl(),
        Formula::imp(
            Formula::and(Formula::mem(big_a.clone(), w.clone()), fib),
            Formula::mem(pi.dp.of(&[], big_a), w),
        ),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Replacement closure at a prefixed fibre.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀q⃗ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ fibres)) → img(q⃗,A) ∈ u)` and its
/// hypothesis-free form at `U(c)`.
#[test]
fn every_universe_is_closed_under_replacement_at_a_prefixed_fibre() {
    let mut env = Env::new();
    let k = kit(&mut env);
    let b = env.declare(3);
    let dp = DProdN::new(&mut env, &k.ap, &k.fs, b).expect("DProdN::new");

    let ur = uni::universe_replacement_n(&mut env, &k.space.empty_ax, dp.img, &dp.img_ax, b)
        .expect("universe_replacement_n");
    let lr = uni::least_universe_replacement_n(&mut env, k.space.lu, &k.space.lu_ax, dp.img, b, &ur)
        .expect("least_universe_replacement_n");

    let (q1, q2) = (constant(&mut env), constant(&mut env));
    let qts = [q1, q2];
    let (u, big_a) = (constant(&mut env), constant(&mut env));

    let fib_u = uni::fibres_in_n(&mut env, b, &qts, &big_a, &u);
    let at_u = derived::inst_all(&ur, &[qts[0].clone(), qts[1].clone(), u.clone(), big_a.clone()])
        .expect("instantiate");
    assert_eq!(
        *at_u.concl(),
        Formula::imp(
            Formula::and(
                uni::is_universe(&mut env, &u),
                Formula::and(Formula::mem(big_a.clone(), u.clone()), fib_u),
            ),
            Formula::mem(dp.img_of(&qts, big_a.clone()), u),
        ),
    );

    let c = constant(&mut env);
    let w = Term::apply(k.space.lu, vec![c.clone()]);
    let fib_w = uni::fibres_in_n(&mut env, b, &qts, &big_a, &w);
    let at_c = derived::inst_all(&lr, &[qts[0].clone(), qts[1].clone(), c, big_a.clone()])
        .expect("instantiate");
    assert_eq!(
        *at_c.concl(),
        Formula::imp(
            Formula::and(Formula::mem(big_a.clone(), w.clone()), fib_w),
            Formula::mem(dp.img_of(&qts, big_a), w),
        ),
    );

    // A fibre symbol and an image symbol of mismatched arity do not compose.
    let other = env.declare(2);
    assert!(uni::universe_replacement_n(&mut env, &k.space.empty_ax, dp.img, &dp.img_ax, other)
        .is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// Lean's `Π` rule, n-ary.
// ─────────────────────────────────────────────────────────────────────────────

/// The universe apparatus a [`Tower`] already carries, in the shape the `Π`
/// rule takes it.
fn universe_parts(t: &Tower) -> UniverseParts<'_> {
    UniverseParts {
        lu: t.space.lu,
        c2: &t.space.c2,
        fs_in_u: &t.funspace_of,
        union: &t.union,
        bin_union: &t.bin_union,
    }
}

/// Everything [`dprod_in_universe_pair_n`] needs, built over one apparatus.
struct Pi {
    dp: DProdN,
    replacement: Thm,
    general: Thm,
    rule: Thm,
}

fn pi_rule(env: &mut Env, t: &Tower, b: FnSym) -> Option<Pi> {
    let dp = DProdN::new(env, &t.sums.ap, &t.sums.fs, b)?;
    let ur = uni::universe_replacement_n(env, &t.space.empty_ax, dp.img, &dp.img_ax, b)?;
    let replacement =
        uni::least_universe_replacement_n(env, t.space.lu, &t.space.lu_ax, dp.img, b, &ur)?;
    let u = universe_parts(t);
    let general =
        dprod_in_universe_of_n(env, &t.sums.ap, &t.sums.fs, &dp.fibre(&replacement), &u)?;
    let rule =
        dprod_in_universe_pair_n(env, &t.sums.ap, &dp.fibre(&replacement), &u, &general)?;
    Some(Pi { dp, replacement, general, rule })
}

/// `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x ∈ A. b(q⃗,x) ∈ U(c)) → dprod(q⃗,A) ∈ U(c))`,
/// together with the reduction it is assembled from.
#[test]
fn the_nary_pi_rule_has_the_stated_shape() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let b = env.declare(3);
    let pi = pi_rule(&mut env, &t, b).expect("pi_rule");

    let (q1, q2) = (constant(&mut env), constant(&mut env));
    let qts = [q1, q2];
    let (c, big_a) = (constant(&mut env), constant(&mut env));
    let w = Term::apply(t.space.lu, vec![c.clone()]);
    let dp_t = pi.dp.of(&qts, big_a.clone());

    // The rule.
    let fib = uni::fibres_in_n(&mut env, b, &qts, &big_a, &w);
    let inst =
        derived::inst_all(&pi.rule, &[qts[0].clone(), qts[1].clone(), c.clone(), big_a.clone()])
            .expect("instantiate");
    assert_eq!(
        *inst.concl(),
        Formula::imp(
            Formula::and(Formula::mem(big_a.clone(), w.clone()), fib),
            Formula::mem(dp_t.clone(), w.clone()),
        ),
    );

    // The reduction underneath it, whose antecedent the three closure steps
    // discharge.
    let base = bin_union(
        &t.sums.ap.sets,
        big_a.clone(),
        t.sums.ap.sets.union_of(pi.dp.img_of(&qts, big_a.clone())),
    );
    let gen =
        derived::inst_all(&pi.general, &[qts[0].clone(), qts[1].clone(), big_a, c]).expect("inst");
    assert_eq!(
        *gen.concl(),
        Formula::imp(Formula::mem(base, w.clone()), Formula::mem(dp_t, w)),
    );
}

/// A stack that does not fit together is **refused**, not described: the rule
/// rebuilds every argument at its own terms and compares.
#[test]
fn the_nary_pi_rule_refuses_a_foreign_stack() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let b = env.declare(3);
    let other = env.declare(3);

    let pi = pi_rule(&mut env, &t, b).expect("pi_rule");
    let dp2 = DProdN::new(&mut env, &t.sums.ap, &t.sums.fs, other).expect("DProdN::new");
    let u = universe_parts(&t);

    // A Replacement lemma for a *different* fibre family.
    assert!(dprod_in_universe_pair_n(
        &mut env,
        &t.sums.ap,
        &dp2.fibre(&pi.replacement),
        &u,
        &pi.general,
    )
    .is_none());

    // A `⋃`-closure lemma standing in for binary union.
    let mixed = UniverseParts { bin_union: &t.union, ..universe_parts(&t) };
    assert!(dprod_in_universe_pair_n(
        &mut env,
        &t.sums.ap,
        &pi.dp.fibre(&pi.replacement),
        &mixed,
        &pi.general,
    )
    .is_none());

    // A subset lemma from the wrong stack, in the reduction.
    let foreign = derived::ext::Fibre { dprod_sub: &dp2.dprod_sub, ..pi.dp.fibre(&pi.replacement) };
    assert!(
        dprod_in_universe_of_n(&mut env, &t.sums.ap, &t.sums.fs, &foreign, &u).is_none()
    );
}

/// **Non-vacuity**: the rule's antecedent is dischargeable, and discharging it
/// yields an unconditional membership.
///
/// The fibre is `b(q,x) := q`, a genuine arity-2 symbol whose value ignores the
/// binder, so its fibres are provably in a universe; at `A := ω`, `q := ∅` and
/// `c := ω` both conjuncts hold in `U₁ = U(ω)` and the conclusion
/// `dprod(∅,ω) ∈ U₁` comes out with **no hypothesis at all**. Without this the
/// rule could be an implication nobody can ever use.
#[test]
fn the_nary_pi_rules_antecedent_is_dischargeable() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let one = t.at(1).expect("Level 1");

    // `b(q,x) = q`.
    let (qv, xv): (FreeVar, FreeVar) = (env.fresh_var(), env.fresh_var());
    let (b, b_def) =
        derived::define_abbrev(&mut env, &[qv, xv], &Term::var(qv)).expect("define_abbrev");
    let pi = pi_rule(&mut env, &t, b).expect("pi_rule");

    let (omega, zero) = (t.omega(), Term::apply(t.space.empty, vec![]));
    let qts = [zero.clone()];
    let u1 = one.set.clone();

    // `⊢ ∀x. (x ∈ ω → b(∅,x) ∈ U₁)`, from `b(∅,x) = ∅` and `∅ ∈ U₁`.
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let eq = derived::inst_all(&b_def, &[zero.clone(), ty.clone()]).expect("b(∅,y) = ∅");
    let hole = env.fresh_var();
    let carry =
        Thm::eq_leibniz(zero.clone(), at(b, &qts, ty.clone()), hole, Formula::mem(Term::var(hole), u1.clone()));
    let flip = derived::eq_symm(&mut env, &eq).expect("∅ = b(∅,y)");
    let fibre_mem = Thm::mp(&Thm::mp(&carry, &flip).expect("leibniz"), &one.empty_mem)
        .expect("b(∅,y) ∈ U₁");
    let fibres = Thm::gen(yv, &derived::a1i(&fibre_mem, Formula::mem(ty.clone(), omega.clone())));
    assert_eq!(*fibres.concl(), uni::fibres_in_n(&mut env, b, &qts, &omega, &u1));

    // Both conjuncts, and the rule fires.
    let inst = derived::inst_all(&pi.rule, &[zero.clone(), omega.clone(), omega.clone()])
        .expect("instantiate");
    let out = Thm::mp(&inst, &derived::and_intro(&one.omega_mem, &fibres)).expect("mp");
    assert_eq!(*out.concl(), Formula::mem(pi.dp.of(&qts, omega), u1));
    assert!(out.hyps().is_empty(), "the Π rule fired under an assumption");
}
