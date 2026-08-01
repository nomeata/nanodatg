//! The exact formula of [`Thm::ax_choice`], rebuilt from the constructors.
//!
//! # Why this shape of test
//!
//! `tarski_regression.rs` records the lesson: its guard test never referenced
//! `ax_tarski` at all — it grepped the *source text* for the string
//! `equinumerous` — so when a fifth clause was added to the axiom, a suite
//! written for four clauses passed without noticing. A test that does not
//! compare against the axiom's actual conclusion pins nothing.
//!
//! So every assertion below is against `Thm::ax_choice(&mut env).concl()`, and
//! the formula it is compared with is built here from `Formula` and `Term`
//! constructors only. In particular it does **not** call
//! `kernel::thm::is_choice_fn`, `is_opair`, `pair_in` or `nonempty` — reusing
//! the kernel's own builders would make the test a tautology, which is exactly
//! how a wrong clause survives.
//!
//! The locally nameless representation is what makes this comparison possible:
//! every quantifier closes over its variable, so two independently built copies
//! of the same closed formula are *syntactically* equal despite using different
//! fresh variables.

use kernel::{Env, Formula, Term, Thm};

// ─────────────────────────────────────────────────────────────────────────────
// Kuratowski pairs, described from scratch.
// ─────────────────────────────────────────────────────────────────────────────

/// `q = {a}`: `∀r. (r ∈ q ↔ r = a)`.
fn singleton(env: &mut Env, q: &Term, a: &Term) -> Formula {
    let r = env.fresh_var();
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q.clone()), Formula::eq(Term::var(r), a.clone())))
}

/// `q = {a,b}`: `∀r. (r ∈ q ↔ (r = a ∨ r = b))`.
fn upair(env: &mut Env, q: &Term, a: &Term, b: &Term) -> Formula {
    let r = env.fresh_var();
    let rhs = Formula::or(Formula::eq(Term::var(r), a.clone()), Formula::eq(Term::var(r), b.clone()));
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q.clone()), rhs))
}

/// `p = ⟨a,b⟩ = {{a},{a,b}}`: `∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b}))`.
fn opair(env: &mut Env, p: &Term, a: &Term, b: &Term) -> Formula {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let left = singleton(env, &tq, a);
    let right = upair(env, &tq, a, b);
    Formula::forall(q, Formula::iff(Formula::mem(tq, p.clone()), Formula::or(left, right)))
}

/// `⟨a,b⟩ ∈ f`: `∃p. (p ∈ f ∧ p = ⟨a,b⟩)`.
fn pair_in(env: &mut Env, f: &Term, a: &Term, b: &Term) -> Formula {
    let p = env.fresh_var();
    let tp = Term::var(p);
    let is_pair = opair(env, &tp, a, b);
    Formula::exists(p, Formula::and(Formula::mem(tp, f.clone()), is_pair))
}

// ─────────────────────────────────────────────────────────────────────────────
// The four clauses.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀p. (p ∈ f → ∃a ∃b. (a ∈ x ∧ p = ⟨a,b⟩))` — `f` is a graph over `x`.
fn clause_graph(env: &mut Env, f: &Term, x: &Term) -> Formula {
    let (p, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let is_pair = opair(env, &Term::var(p), &Term::var(a), &Term::var(b));
    let body = Formula::and(Formula::mem(Term::var(a), x.clone()), is_pair);
    let witness = Formula::exists(a, Formula::exists(b, body));
    Formula::forall(p, Formula::imp(Formula::mem(Term::var(p), f.clone()), witness))
}

/// `∀a ∀b ∀c. ((⟨a,b⟩ ∈ f ∧ ⟨a,c⟩ ∈ f) → b = c)` — single-valued.
fn clause_single_valued(env: &mut Env, f: &Term) -> Formula {
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let ab = pair_in(env, f, &Term::var(a), &Term::var(b));
    let ac = pair_in(env, f, &Term::var(a), &Term::var(c));
    let concl = Formula::eq(Term::var(b), Term::var(c));
    Formula::forall(a, Formula::forall(b, Formula::forall(c, Formula::imp(Formula::and(ab, ac), concl))))
}

/// `∀a. (a ∈ x → ∃b. ⟨a,b⟩ ∈ f)` — total on `x`.
fn clause_total(env: &mut Env, f: &Term, x: &Term) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let ab = pair_in(env, f, &Term::var(a), &Term::var(b));
    Formula::forall(a, Formula::imp(Formula::mem(Term::var(a), x.clone()), Formula::exists(b, ab)))
}

/// `∀a ∀b. (((a ∈ x ∧ ∃w. w ∈ a) ∧ ⟨a,b⟩ ∈ f) → b ∈ a)` — picks a member of
/// every non-empty member of `x`.
///
/// `guard` controls whether the `∃w. w ∈ a` conjunct is present; the unguarded
/// variant is built only so a test can assert the axiom is *not* it.
fn clause_chooses(env: &mut Env, f: &Term, x: &Term, guard: bool) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let ab = pair_in(env, f, &Term::var(a), &Term::var(b));
    let in_x = Formula::mem(Term::var(a), x.clone());
    let left = if guard {
        let w = env.fresh_var();
        let ne = Formula::exists(w, Formula::mem(Term::var(w), Term::var(a)));
        Formula::and(in_x, ne)
    } else {
        in_x
    };
    let concl = Formula::mem(Term::var(b), Term::var(a));
    Formula::forall(a, Formula::forall(b, Formula::imp(Formula::and(left, ab), concl)))
}

/// `∀X ∃f. IsChoiceFn(f, X)`, rebuilt.
fn expected_axiom(env: &mut Env, guard: bool) -> Formula {
    let (x, f) = (env.fresh_var(), env.fresh_var());
    let (tx, tf) = (Term::var(x), Term::var(f));
    let body = Formula::and(
        clause_graph(env, &tf, &tx),
        Formula::and(
            clause_single_valued(env, &tf),
            Formula::and(clause_total(env, &tf, &tx), clause_chooses(env, &tf, &tx, guard)),
        ),
    );
    Formula::forall(x, Formula::exists(f, body))
}

// ─────────────────────────────────────────────────────────────────────────────
// The tests.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole formula, clause for clause, conjunct for conjunct.
#[test]
fn ax_choice_is_exactly_the_reference_statement() {
    let mut env = Env::new();
    let expected = expected_axiom(&mut env, true);
    assert_eq!(
        *Thm::ax_choice(&mut env).concl(),
        expected,
        "ax_choice is not the formula this test rebuilt; if the axiom was changed deliberately, \
         change this test in the same commit and say why in the message"
    );
}

/// The non-emptiness guard on the choice clause is **load bearing**.
///
/// Without it the axiom says `f(x) ∈ x` for *every* `x ∈ X`, including an empty
/// one — and since the third clause makes `f` total on `X`, that yields
/// `∃b. b ∈ x` for every `x ∈ X`, i.e. "no set has an empty member", which
/// `derived::empty` refutes outright. That is the same failure mode as the
/// `ax_tarski` bug: a clause that reads plausibly and is not satisfiable.
///
/// So this asserts the axiom is *not* the unguarded formula. It is compared
/// against `ax_choice`'s own conclusion, not against the source text.
#[test]
fn ax_choice_guards_the_choice_clause() {
    let mut env = Env::new();
    let unguarded = expected_axiom(&mut env, false);
    assert_ne!(
        *Thm::ax_choice(&mut env).concl(),
        unguarded,
        "ax_choice's choice clause has lost its `∃w. w ∈ a` guard — that asserts every member \
         of every set is non-empty, which is inconsistent with the empty set"
    );
}

/// The axiom quantifies `∀X ∃f`, in that order, and its body is a four-fold
/// conjunction — checked by peeling the real conclusion apart rather than by
/// rebuilding it.
#[test]
fn ax_choice_has_the_expected_quantifier_prefix() {
    let mut env = Env::new();
    let ax = Thm::ax_choice(&mut env);

    // Instantiating the outer ∀ at an arbitrary constant must succeed and leave
    // an existential, i.e. a `¬∀¬`.
    let c = Term::apply(env.declare(0), vec![]);
    let inst = Thm::ax_inst(ax.concl().clone(), c).expect("ax_choice must start with ∀X");
    let (_, body) = inst.concl().as_imp().expect("instantiation is an implication");
    let (all_not, fls) = body.as_imp().expect("the body must be `∃f. …`, i.e. `(∀f. ¬…) → ⊥`");
    assert_eq!(fls, Formula::false_(), "the body is not an existential");

    // Four conjuncts: `A ∧ (B ∧ (C ∧ D))`, so three nested `∧`s.
    let d = env.fresh_var();
    let neg_body = Thm::ax_inst(all_not, Term::var(d))
        .expect("the existential must bind a single f")
        .concl()
        .as_imp()
        .expect("instantiation is an implication")
        .1;
    let (conj, fls2) = neg_body.as_imp().expect("`¬IsChoiceFn` is `IsChoiceFn → ⊥`");
    assert_eq!(fls2, Formula::false_());
    let mut rest = conj;
    for i in 0..3 {
        let (inner, f) = rest.as_imp().unwrap_or_else(|| panic!("conjunct {i}: not a conjunction"));
        assert_eq!(f, Formula::false_(), "conjunct {i}: not a conjunction");
        let (_left, not_right) = inner.as_imp().expect("conjunction shape");
        let (right, f2) = not_right.as_imp().expect("conjunction shape");
        assert_eq!(f2, Formula::false_(), "conjunction shape");
        rest = right;
    }
    // What remains is the fourth clause, which is a `∀`, not a further `∧`.
    assert!(
        Thm::ax_inst(rest.clone(), Term::var(d)).is_some(),
        "the fourth clause of IsChoiceFn should be universally quantified"
    );
}
