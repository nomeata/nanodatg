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

    // ... with `is_universe` the axiom's own `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`.
    let c1 = uni::transitive(&mut env, &tu);
    let c2 = uni::closed_sub(&mut env, &tu);
    let c3 = uni::closed_pow(&mut env, &tu);
    let c4 = uni::inaccessible(&mut env, &tu);
    assert_eq!(
        uni::is_universe(&mut env, &tu),
        Formula::and(c1.clone(), Formula::and(c2.clone(), Formula::and(c3, c4)))
    );
    // `z ∈ y` and `z ⊆ y` are genuinely different clauses — confusing them would
    // leave the axiom exactly as weak as it was before 2026-07-31.
    assert_ne!(c1, c2, "the transitivity clause collapsed into the subset clause");
}

/// The clauses are the formulas their names claim, spelled out independently of
/// the module that builds them.
#[test]
fn clauses_have_the_stated_shapes() {
    let mut env = Env::new();
    let tu = Term::apply(env.declare(0), vec![]);

    let (y, z, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tz, tp) = (Term::var(y), Term::var(z), Term::var(p));

    let want_c1 = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), tu.clone()),
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), ty.clone()),
                    Formula::mem(tz.clone(), tu.clone()),
                ),
            ),
        ),
    );
    assert_eq!(uni::transitive(&mut env, &tu), want_c1);

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

/// `⊢ ∀u ∀y ∀z. ((is_universe(u) ∧ (y ∈ u ∧ z ∈ y)) → z ∈ u)` — `C₁` applied.
#[test]
fn a_universe_contains_the_members_of_its_members() {
    let mut env = Env::new();
    let thm = uni::universe_mem_mem(&mut env).expect("C₁ applied");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (u, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ty, tz) = (Term::var(u), Term::var(y), Term::var(z));
    let want = Formula::imp(
        Formula::and(
            uni::is_universe(&mut env, &tu),
            Formula::and(
                Formula::mem(ty.clone(), tu.clone()),
                Formula::mem(tz.clone(), ty.clone()),
            ),
        ),
        Formula::mem(tz.clone(), tu.clone()),
    );
    let mut cur = thm.clone();
    for v in [u, y, z] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want, "universe_mem_mem has the wrong shape");

    // Non-vacuity: `z ∈ y` and `z ⊆ y` are different antecedents, so this is not
    // `C₂` under another name.
    let sub_zy = kernel::thm::subset(&mut env, tz.clone(), ty.clone());
    assert_ne!(Formula::mem(tz, ty), sub_zy);
}

/// `U(x)` satisfies Tarski's **first** clause: it is transitive. This is the
/// clause countermodel A used to refute, and the reason `ax_tarski` grew a
/// fifth conjunct.
#[test]
fn least_universe_is_transitive() {
    let mut env = Env::new();
    let (lu, ax) = uni::least_universe(&mut env).expect("define U");

    let thm = uni::least_universe_transitive(&mut env, lu, &ax).expect("C₁ for U(x)");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let x = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(x)]);
    assert_eq!(*thm.concl(), Formula::forall(x, uni::transitive(&mut env, &w)));

    // Non-vacuity: this is genuinely `C₁` and not `C₂` at the same term.
    assert_ne!(uni::transitive(&mut env, &w), uni::closed_sub(&mut env, &w));

    // A universe operator of the wrong arity is refused.
    let other = env.declare(2);
    assert!(uni::least_universe_transitive(&mut env, other, &ax)
        .expect_err("a binary symbol is not a universe operator")
        .is_decline());
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

    // And that really is `is_universe(U(x))` with its first and last conjuncts
    // removed. (`C₁` for `U(x)` is `least_universe_transitive`, proved below;
    // `C₄` is the open one.)
    let c1 = uni::transitive(&mut env, &w);
    let c4 = uni::inaccessible(&mut env, &w);
    assert_eq!(
        uni::is_universe(&mut env, &w),
        Formula::and(c1, Formula::and(c2, Formula::and(c3, c4)))
    );
}

/// The reduction, on its own: a subset of `U(x)` that is not a member of it is
/// equinumerous with some universe containing `x` that misses it. Getting from
/// there to `y ≈ U(x)` is Cantor–Schröder–Bernstein, which
/// `uni::least_universe_inaccessible` does; this test pins the half that needs
/// nothing but the axiom, so a change to `crate::csb` cannot quietly move it.
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

// ─────────────────────────────────────────────────────────────────────────────
// Closure under unordered pairing.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ (¬(∅ = 𝒫∅) ∧ (¬(∅ = 𝒫𝒫∅) ∧ ¬(𝒫∅ = 𝒫𝒫∅)))`, stated independently.
///
/// The three sides are *different terms* — a "distinctness" lemma whose two
/// sides were the same term would prove nothing — so that is asserted too.
#[test]
fn the_bottom_of_the_power_tower_is_three_distinct_sets() {
    let mut env = Env::new();
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let thm = uni::power_tower_distinct(&mut env, empty, &empty_ax, pow, &pow_ax)
        .expect("power_tower_distinct");

    let e = Term::apply(empty, vec![]);
    let p1 = Term::apply(pow, vec![e.clone()]);
    let p2 = Term::apply(pow, vec![p1.clone()]);
    assert_ne!(e, p1);
    assert_ne!(e, p2);
    assert_ne!(p1, p2);

    let want = Formula::and(
        Formula::not(Formula::eq(e.clone(), p1.clone())),
        Formula::and(
            Formula::not(Formula::eq(e, p2.clone())),
            Formula::not(Formula::eq(p1, p2)),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀u ∀a. ((is_universe(u) ∧ a ∈ u) → (∅ ∈ u ∧ (𝒫∅ ∈ u ∧ 𝒫𝒫∅ ∈ u)))`.
#[test]
fn a_universe_with_a_member_has_the_bottom_three() {
    let mut env = Env::new();
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let thm = uni::universe_three_members(&mut env, empty, &empty_ax, pow, &pow_ax)
        .expect("universe_three_members");

    let (u, a) = (env.fresh_var(), env.fresh_var());
    let (tu, ta) = (Term::var(u), Term::var(a));
    let e = Term::apply(empty, vec![]);
    let p1 = Term::apply(pow, vec![e.clone()]);
    let p2 = Term::apply(pow, vec![p1.clone()]);

    let want = Formula::forall(
        u,
        Formula::forall(
            a,
            Formula::imp(
                Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(ta, tu.clone())),
                Formula::and(
                    Formula::mem(e, tu.clone()),
                    Formula::and(Formula::mem(p1, tu.clone()), Formula::mem(p2, tu)),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀u ∀a ∀b ∀v₁ ∀v₂ ∀v₃. ((three distinct members of u) → ¬({a,b} ≈ u))`,
/// stated independently and pinned to the kernel's own `equinumerous`.
#[test]
fn an_unordered_pair_is_not_equinumerous_with_a_three_element_set() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let thm = uni::upair_not_equinumerous(&mut env, up, &up_ax).expect("upair_not_equinumerous");

    let (u, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (v1, v2, v3) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(u), Term::var(a), Term::var(b));
    let (t1, t2, t3) = (Term::var(v1), Term::var(v2), Term::var(v3));
    let pair = Term::apply(up, vec![ta, tb]);

    let mems = Formula::and(
        Formula::mem(t1.clone(), tu.clone()),
        Formula::and(Formula::mem(t2.clone(), tu.clone()), Formula::mem(t3.clone(), tu.clone())),
    );
    let dist = Formula::and(
        Formula::not(Formula::eq(t1.clone(), t2.clone())),
        Formula::and(
            Formula::not(Formula::eq(t1, t3.clone())),
            Formula::not(Formula::eq(t2, t3)),
        ),
    );
    let equi = kernel::thm::equinumerous(&mut env, pair, tu);
    let want = Formula::imp(Formula::and(mems, dist), Formula::not(equi));

    let mut cur = thm.clone();
    for v in [u, a, b, v1, v2, v3] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);
    // The conclusion is a genuine negation of the kernel's own equinumerosity
    // formula, not of some look-alike rebuilt here.
    assert_ne!(*thm.concl(), Formula::false_());
}

/// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → {a,b} ∈ u)`.
#[test]
fn every_universe_is_closed_under_pairing() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let thm = uni::universe_pairing(&mut env, up, &up_ax, empty, &empty_ax, pow, &pow_ax)
        .expect("universe_pairing");

    let (u, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(u), Term::var(a), Term::var(b));
    let want = Formula::imp(
        Formula::and(
            uni::is_universe(&mut env, &tu),
            Formula::and(
                Formula::mem(ta.clone(), tu.clone()),
                Formula::mem(tb.clone(), tu.clone()),
            ),
        ),
        Formula::mem(Term::apply(up, vec![ta, tb]), tu),
    );
    let mut cur = thm.clone();
    for v in [u, a, b] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))` — the pairing closure
/// transferred through the intersection, with **no** hypothesis.
///
/// Non-vacuity: the antecedent is not the conclusion, and `{a,b}` is a
/// different term from both `a` and `b`.
#[test]
fn the_least_universe_is_closed_under_pairing() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("least_universe");
    let pairing = uni::universe_pairing(&mut env, up, &up_ax, empty, &empty_ax, pow, &pow_ax)
        .expect("universe_pairing");
    let thm = uni::least_universe_pairing(&mut env, lu, &lu_ax, up, &pairing)
        .expect("least_universe_pairing");

    // A theorem that is not the pairing closure is **declined**, and that it is
    // a decline rather than an assembly failure is the point. The wrong theorem
    // is stopped inside `rules::inst_all`, which runs out of leading
    // quantifiers before this function's own conclusion comparison is reached;
    // until `inst_all` declined on that, the verdict depended on *how far*
    // wrong the caller was — two quantifiers short reported `Thm::ax_inst was
    // passed bad data`, the right count with a wrong body reported the
    // documented precondition. See *Shape versus fit* in `derived::err`.
    assert!(uni::least_universe_pairing(&mut env, lu, &lu_ax, up, &lu_ax)
        .expect_err("the characteristic property is not the pairing closure")
        .is_decline());

    let (c, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(c), Term::var(a), Term::var(b));
    let w = Term::apply(lu, vec![tc]);
    let pair = Term::apply(up, vec![ta.clone(), tb.clone()]);
    assert_ne!(pair, ta);
    assert_ne!(pair, tb);

    let want = Formula::imp(
        Formula::and(
            Formula::mem(ta, w.clone()),
            Formula::mem(tb, w.clone()),
        ),
        Formula::mem(pair, w),
    );
    let mut cur = thm.clone();
    for v in [c, a, b] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))`, with `⟨a,b⟩` the
/// Kuratowski pair the rest of the development uses.
#[test]
fn the_least_universe_is_closed_under_ordered_pairs() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let (empty, empty_ax) = derived::empty::empty(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("least_universe");
    let up_pairing = uni::universe_pairing(&mut env, up, &up_ax, empty, &empty_ax, pow, &pow_ax)
        .expect("universe_pairing");
    let pairing = uni::least_universe_pairing(&mut env, lu, &lu_ax, up, &up_pairing)
        .expect("least_universe_pairing");
    let thm = uni::least_universe_opair(&mut env, lu, up, &pairing).expect("opair");

    let (c, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(c), Term::var(a), Term::var(b));
    let w = Term::apply(lu, vec![tc]);
    let want = Formula::imp(
        Formula::and(Formula::mem(ta.clone(), w.clone()), Formula::mem(tb.clone(), w.clone())),
        Formula::mem(derived::opair(up, ta, tb), w),
    );
    let mut cur = thm.clone();
    for v in [c, a, b] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    // A pairing theorem about a *different* universe operator is refused.
    let other = env.declare(1);
    assert!(uni::least_universe_opair(&mut env, other, up, &pairing)
        .expect_err("the pairing lemma is about a different universe operator")
        .is_decline());
}

// ─────────────────────────────────────────────────────────────────────────────
// Closure under `⋃`, and what falls out of it.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole `⋃`-closure stack, built once over a shared pairing.
struct UnionChain {
    sets: derived::funcs::Sets,
    lu: kernel::FnSym,
    lu_ax: Thm,
    /// `⊢ ∀u ∀s. ((is_universe(u) ∧ s ∈ u) → ⋃s ∈ u)`.
    union_closed: Thm,
    /// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))`.
    least_union: Thm,
    /// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → (a ∪ b) ∈ u)`.
    bin_union: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))`.
    least_bin_union: Thm,
    /// `⊢ ∀x. x ∈ U(x)`.
    mem_lu: Thm,
}

fn union_chain(env: &mut Env) -> UnionChain {
    let sets = derived::funcs::Sets::new(env);
    let (empty, empty_ax) = derived::empty::empty(env);
    let (pow, pow_ax) = derived::power(env);
    let (lu, lu_ax) = uni::least_universe(env).expect("least_universe");
    let mem_lu = uni::mem_least_universe(env, lu, &lu_ax).expect("mem_least_universe");

    let pairing =
        uni::universe_pairing(env, sets.up, &sets.up_ax, empty, &empty_ax, pow, &pow_ax)
            .expect("universe_pairing");
    let mem_mem = uni::universe_mem_mem(env).expect("universe_mem_mem");
    let two_cycle =
        derived::empty::no_two_cycle(env, sets.up, &sets.up_ax).expect("no_two_cycle");
    let union_closed = uni::universe_union_closed(env, &sets, &empty_ax, &mem_mem, &two_cycle)
        .expect("universe_union_closed");
    let least_union = uni::least_universe_union(env, lu, &lu_ax, sets.un, &union_closed)
        .expect("least_universe_union");
    let least_pairing = uni::least_universe_pairing(env, lu, &lu_ax, sets.up, &pairing)
        .expect("least_universe_pairing");
    let bin_union = uni::universe_bin_union(env, &sets, &pairing, &union_closed)
        .expect("universe_bin_union");
    let least_bin_union =
        uni::least_universe_bin_union(env, lu, &sets, &least_pairing, &least_union)
            .expect("least_universe_bin_union");
    UnionChain { sets, lu, lu_ax, union_closed, least_union, bin_union, least_bin_union, mem_lu }
}

/// `⊢ ∀u ∀s. ((is_universe(u) ∧ s ∈ u) → ⋃s ∈ u)` — every universe is closed
/// under `⋃`. The statement is rebuilt here from the kernel's constructors.
#[test]
fn every_universe_is_closed_under_union() {
    let mut env = Env::new();
    let c = union_chain(&mut env);
    assert!(kernel::thm::debug_locally_closed(c.union_closed.concl()));

    let (u, s) = (env.fresh_var(), env.fresh_var());
    let (tu, ts) = (Term::var(u), Term::var(s));
    let want = Formula::imp(
        Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(ts.clone(), tu.clone())),
        Formula::mem(c.sets.union_of(ts.clone()), tu.clone()),
    );
    let mut cur = c.union_closed.clone();
    for v in [u, s] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    // `⋃s` really is a different term from `s`, so the theorem is not a
    // disguised triviality.
    assert_ne!(c.sets.union_of(ts.clone()), ts);
}

/// **Non-vacuity for the arbitrary-universe form.** The antecedent
/// `is_universe(u) ∧ s ∈ u` is not merely unrefuted: Tarski's axiom satisfies
/// it, and discharging it there yields
/// `⊢ ∃u. ((x ∈ u ∧ is_universe(u)) ∧ ⋃x ∈ u)`.
#[test]
fn the_union_closure_antecedent_is_satisfiable() {
    let mut env = Env::new();
    let c = union_chain(&mut env);
    let x = env.fresh_var();
    let tx = Term::var(x);
    let u = env.fresh_var();
    let tu = Term::var(u);

    let ex = uni::tarski_at(&mut env, &tx, u).expect("Tarski at x");
    let body = uni::universe_body(&mut env, &tx, &tu);
    assert_eq!(*ex.concl(), Formula::exists(u, body.clone()));

    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let univ_u = uni::is_universe(&mut env, &tu);
    let b_x = derived::and_left(x_in_u.clone(), univ_u.clone());
    let b_univ = derived::and_right(x_in_u, univ_u);

    let at = derived::inst_all(&c.union_closed, &[tu.clone(), tx.clone()]).expect("instantiate");
    let b_goal = derived::hyp_mp(
        &derived::a1i(&at, body.clone()),
        &derived::hyp_and(&b_univ, &b_x).expect("pair the two clauses"),
    )
    .expect("discharge the antecedent");
    let step = derived::hyp_and(&derived::imp_refl(body.clone()), &b_goal).expect("conjoin");
    let mono = derived::exists_mono(u, &Thm::gen(u, &step)).expect("under the existential");
    let out = Thm::mp(&mono, &ex).expect("cash Tarski in");

    assert_eq!(
        *out.concl(),
        Formula::exists(
            u,
            Formula::and(body, Formula::mem(c.sets.union_of(tx), tu))
        ),
        "the antecedent was not discharged at a universe Tarski supplies"
    );
}

/// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))` — and, at `c := x`, the unconditional
/// `⊢ ∀x. ⋃x ∈ U(x)`, which is the sharpest non-vacuity statement available:
/// no hypothesis at all.
#[test]
fn the_least_universe_is_closed_under_union() {
    let mut env = Env::new();
    let c = union_chain(&mut env);

    let (cv, s) = (env.fresh_var(), env.fresh_var());
    let (tc, ts) = (Term::var(cv), Term::var(s));
    let w = Term::apply(c.lu, vec![tc]);
    let want = Formula::imp(
        Formula::mem(ts.clone(), w.clone()),
        Formula::mem(c.sets.union_of(ts.clone()), w.clone()),
    );
    let mut cur = c.least_union.clone();
    for v in [cv, s] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    // At `c := x` the antecedent is `x ∈ U(x)`, which is proved outright.
    let x = env.fresh_var();
    let tx = Term::var(x);
    let wx = Term::apply(c.lu, vec![tx.clone()]);
    let at = derived::inst_all(&c.least_union, &[tx.clone(), tx.clone()]).expect("instantiate");
    let self_mem =
        derived::inst_all(&c.mem_lu, std::slice::from_ref(&tx)).expect("x ∈ U(x)");
    let out = Thm::mp(&at, &self_mem).expect("discharge");
    assert_eq!(*out.concl(), Formula::mem(c.sets.union_of(tx), wx));

    // A theorem that is not the union closure is refused.
    assert!(uni::least_universe_union(&mut env, c.lu, &c.lu_ax, c.sets.un, &c.lu_ax)
        .expect_err("the characteristic property is not the union closure")
        .is_decline());
}

/// Binary union, at an arbitrary universe and at `U(c)` — the antecedent
/// `crate::funspace` and `crate::ext` were carrying.
#[test]
fn universes_are_closed_under_binary_union() {
    let mut env = Env::new();
    let c = union_chain(&mut env);

    let (u, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(u), Term::var(a), Term::var(b));
    let un = derived::funspace::bin_union(&c.sets, ta.clone(), tb.clone());
    assert_eq!(un, c.sets.union_of(Term::apply(c.sets.up, vec![ta.clone(), tb.clone()])));

    let want = Formula::imp(
        Formula::and(
            uni::is_universe(&mut env, &tu),
            Formula::and(
                Formula::mem(ta.clone(), tu.clone()),
                Formula::mem(tb.clone(), tu.clone()),
            ),
        ),
        Formula::mem(un.clone(), tu.clone()),
    );
    let mut cur = c.bin_union.clone();
    for v in [u, a, b] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let w = Term::apply(c.lu, vec![tc]);
    let want_least = Formula::imp(
        Formula::and(
            Formula::mem(ta.clone(), w.clone()),
            Formula::mem(tb.clone(), w.clone()),
        ),
        Formula::mem(un, w),
    );
    let mut cur = c.least_bin_union.clone();
    for v in [cv, a, b] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want_least);

    // Non-vacuity, and at two *distinct* arguments: `x ∈ U(x)` and
    // `⋃x ∈ U(x)`, so `⊢ ∀x. (x ∪ ⋃x) ∈ U(x)`.
    let x = env.fresh_var();
    let tx = Term::var(x);
    let wx = Term::apply(c.lu, vec![tx.clone()]);
    let ux = c.sets.union_of(tx.clone());
    let x_in = derived::inst_all(&c.mem_lu, std::slice::from_ref(&tx)).expect("x ∈ U(x)");
    let ux_in = Thm::mp(
        &derived::inst_all(&c.least_union, &[tx.clone(), tx.clone()]).expect("instantiate"),
        &x_in,
    )
    .expect("⋃x ∈ U(x)");
    let at = derived::inst_all(&c.least_bin_union, &[tx.clone(), tx.clone(), ux.clone()])
        .expect("instantiate");
    let out = Thm::mp(&at, &derived::and_intro(&x_in, &ux_in)).expect("discharge");
    assert_eq!(
        *out.concl(),
        Formula::mem(derived::funspace::bin_union(&c.sets, tx, ux), wx),
        "the binary-union closure does not discharge at U(x)"
    );
}

/// Application: `app(f,x) ∈ u` for `f ∈ u`, with **no** hypothesis that `f` is
/// single-valued or that `x` is in its domain.
#[test]
fn universes_are_closed_under_application() {
    let mut env = Env::new();
    let sets = derived::funcs::Sets::new(&mut env);
    let ap = derived::funcs::Apply::with_sets(&mut env, sets.clone()).expect("apply");
    let (_, empty_ax) = derived::empty::empty(&mut env);
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("least_universe");
    let mem_lu = uni::mem_least_universe(&mut env, lu, &lu_ax).expect("mem_least_universe");
    let mem_mem = uni::universe_mem_mem(&mut env).expect("universe_mem_mem");
    let sub_mem = uni::universe_sub_mem(&mut env).expect("universe_sub_mem");
    let two_cycle =
        derived::empty::no_two_cycle(&mut env, sets.up, &sets.up_ax).expect("no_two_cycle");
    let union_closed =
        uni::universe_union_closed(&mut env, &sets, &empty_ax, &mem_mem, &two_cycle)
            .expect("universe_union_closed");
    let coll_closed = uni::universe_coll_closed(&mut env, &ap, &union_closed, &sub_mem)
        .expect("universe_coll_closed");
    let app_closed = uni::universe_app_closed(&mut env, &ap, &union_closed, &coll_closed)
        .expect("universe_app_closed");
    let least_app =
        uni::least_universe_app(&mut env, &ap, lu, &lu_ax, &app_closed).expect("least_universe_app");

    let (u, f, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tf, tx) = (Term::var(u), Term::var(f), Term::var(x));
    let want = Formula::imp(
        Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(tf.clone(), tu.clone())),
        Formula::mem(ap.apply(tf.clone(), tx.clone()), tu.clone()),
    );
    let mut cur = app_closed.clone();
    for v in [u, f, x] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    // Non-vacuity: at `c := f` the antecedent is `f ∈ U(f)`, so
    // `⊢ ∀f ∀x. app(f,x) ∈ U(f)` with no hypothesis at all.
    let wf = Term::apply(lu, vec![tf.clone()]);
    let at = derived::inst_all(&least_app, &[tf.clone(), tf.clone(), tx.clone()])
        .expect("instantiate");
    let out = Thm::mp(
        &at,
        &derived::inst_all(&mem_lu, std::slice::from_ref(&tf)).expect("f ∈ U(f)"),
    )
    .expect("discharge");
    assert_eq!(*out.concl(), Formula::mem(ap.apply(tf, tx), wf));

    // A theorem that is not the application closure is declined too, stopped
    // inside `rules::inst_all` before this function's own conclusion check; see
    // the note in `the_least_universe_is_closed_under_pairing`.
    assert!(uni::least_universe_app(&mut env, &ap, lu, &lu_ax, &union_closed)
        .expect_err("⋃-closure is not application closure")
        .is_decline());
}

/// Replacement: the image `{ b(x) : x ∈ A }` of a member whose fibres are all
/// members is itself a member — at an arbitrary universe and at `U(c)`.
///
/// This is `image_in_universe` at its cheapest: `DOM` is a projection, `SV` is
/// transitivity of equality, and `ONTO` is the forward half of `img`'s own
/// characteristic property.
#[test]
fn universes_are_closed_under_replacement() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("least_universe");
    let mem_lu = uni::mem_least_universe(&mut env, lu, &lu_ax).expect("mem_least_universe");
    let b = env.declare(1);
    let (img, img_ax) = derived::ext::image_symbol(&mut env, b).expect("image_symbol");
    let repl = uni::universe_replacement(&mut env, &empty_ax, img, &img_ax, b)
        .expect("universe_replacement");
    assert!(kernel::thm::debug_locally_closed(repl.concl()));

    let (u, a) = (env.fresh_var(), env.fresh_var());
    let (tu, ta) = (Term::var(u), Term::var(a));
    let img_a = Term::apply(img, vec![ta.clone()]);
    let want = Formula::imp(
        Formula::and(
            uni::is_universe(&mut env, &tu),
            Formula::and(
                Formula::mem(ta.clone(), tu.clone()),
                uni::fibres_in(&mut env, b, &ta, &tu),
            ),
        ),
        Formula::mem(img_a.clone(), tu.clone()),
    );
    let mut cur = repl.clone();
    for v in [u, a] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want);

    // The fibre condition is what it says: `∀x. (x ∈ A → b(x) ∈ u)`.
    let x = env.fresh_var();
    let tx = Term::var(x);
    assert_eq!(
        uni::fibres_in(&mut env, b, &ta, &tu),
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), ta.clone()),
                Formula::mem(Term::apply(b, vec![tx]), tu.clone()),
            )
        )
    );

    let least = uni::least_universe_replacement(&mut env, lu, &lu_ax, img, b, &repl)
        .expect("least_universe_replacement");
    let cv = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(cv)]);
    let want_least = Formula::imp(
        Formula::and(
            Formula::mem(ta.clone(), w.clone()),
            uni::fibres_in(&mut env, b, &ta, &w),
        ),
        Formula::mem(img_a, w),
    );
    let mut cur = least.clone();
    for v in [cv, a] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want_least);

    // Non-vacuity: at a *constant* fibre symbol the condition is dischargeable.
    // `img(A) ∈ U(c)` is not the antecedent, and `mem_lu` is a real theorem
    // about the same operator.
    assert_ne!(
        *cur.concl(),
        *derived::inst_all(&mem_lu, std::slice::from_ref(&ta)).expect("x ∈ U(x)").concl()
    );

    // A theorem that is not the replacement closure is refused.
    assert!(uni::least_universe_replacement(&mut env, lu, &lu_ax, img, b, &lu_ax)
        .expect_err("the characteristic property is not the replacement closure")
        .is_decline());
}
