//! Quotients: the equivalence closure, `A/∼`, `mk`, `sound` and `lift`.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem with the right
//! *name* but the wrong *shape* fails here.
//!
//! **Non-vacuity is the whole game.** Every lemma in the module is satisfied by
//! the collapsed reading `eqv(A,R) = A²`, in which every quotient is a point,
//! `sound` is trivial and `lift` is a one-entry graph. The four tests in the
//! middle rule that out: at `R := ∅` the closure is inside the diagonal, `mk` is
//! injective, and `lift`'s compatibility antecedent is satisfied by *every* `f`,
//! so the computation rule holds unconditionally.
//!
//! The last group is about the *sequent*, not the formula. A `Thm` is `Γ ⊢ φ`
//! and every theorem this module hands out is documented `⊢ φ`, so each of those
//! tests feeds one entry a premise built with `Thm::assume` — or, in two cases,
//! a premise that is perfectly true but not the one the header names — and
//! checks that the entry refuses rather than passing the flaw through under an
//! unconditional label. Each has a control call on the honest input beside it,
//! so a guard that simply returned `None` always would fail here too.

use kernel::{Env, Formula, Term, Thm};

use derived::funspace::{is_function, is_single_valued};
use derived::quot::{self, Quotient};
use derived::sums::Sums;

/// The whole development, built once per test.
fn build(env: &mut Env) -> Quotient {
    Quotient::new(env).expect("quotient")
}

/// Four fresh variables, as terms.
fn vars4(env: &mut Env) -> (Term, Term, Term, Term) {
    (
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
    )
}

/// The one free variable of a variable term.
fn var_of(t: &Term) -> kernel::FreeVar {
    let mut fv = Vec::new();
    t.free_vars(&mut fv);
    fv[0]
}

/// Wrap `body` in `∀` over each of `vs`, outermost first.
fn forall_all(vs: &[Term], body: Formula) -> Formula {
    vs.iter().rev().fold(body, |acc, t| Formula::forall(var_of(t), acc))
}

// ─────────────────────────────────────────────────────────────────────────────
// The equivalence closure.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) → p ∈ prod(A,A))` — the closure is a relation on
/// `A`, so it cannot inherit pairs of `R` that reach outside the carrier.
#[test]
fn the_closure_is_a_relation_on_the_carrier() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.eqv_subset.concl()));

    let (a, r, p, _) = vars4(&mut env);
    let body = Formula::imp(
        Formula::mem(p.clone(), Term::apply(q.eqv, vec![a.clone(), r.clone()])),
        Formula::mem(p.clone(), q.sums.prod.of(a.clone(), a.clone())),
    );
    assert_eq!(*q.eqv_subset.concl(), forall_all(&[a, r, p], body));
}

/// The four closure clauses, each checked against the formula `eqv_closed`
/// conjoins — so a clause that drifted would fail here rather than silently
/// weaken `eqv_closed_self`.
#[test]
fn the_closure_is_an_equivalence_relation_containing_the_relation() {
    let mut env = Env::new();
    let q = build(&mut env);
    for t in [&q.eqv_refl, &q.eqv_sym, &q.eqv_trans, &q.eqv_incl, &q.eqv_closed] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    let (a, r, _, _) = vars4(&mut env);
    let eqv_t = Term::apply(q.eqv, vec![a.clone(), r.clone()]);
    let atoms = quot::eqv_atoms(&mut env, &q.sums, &a, &r, &eqv_t);

    for (i, t) in [&q.eqv_refl, &q.eqv_sym, &q.eqv_trans, &q.eqv_incl].iter().enumerate() {
        let at = derived::inst_all(t, &[a.clone(), r.clone()]).expect("instantiate");
        assert_eq!(*at.concl(), atoms[i], "clause {i} has drifted");
    }

    let want = derived::conj_of(&atoms).expect("four atoms");
    let closed = derived::inst_all(&q.eqv_closed, &[a.clone(), r.clone()]).expect("instantiate");
    assert_eq!(*closed.concl(), want);
}

/// `⊢ ∀A ∀R ∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → ∀p. (p ∈ eqv(A,R) → p ∈ E))` —
/// minimality, the half that makes `eqv` a *closure* and not merely some
/// equivalence relation above `R`.
#[test]
fn the_closure_is_the_least_such_relation() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.eqv_induction.concl()));

    let (a, r, e, p) = vars4(&mut env);
    let guard = quot::eqv_guard(&mut env, &q.sums, &a, &r, &e);
    let inner = Formula::imp(
        Formula::mem(p.clone(), Term::apply(q.eqv, vec![a.clone(), r.clone()])),
        Formula::mem(p.clone(), e.clone()),
    );
    let body = Formula::imp(guard, Formula::forall(var_of(&p), inner));
    assert_eq!(*q.eqv_induction.concl(), forall_all(&[a, r, e], body));
}

// ─────────────────────────────────────────────────────────────────────────────
// Classes, the quotient set, `mk` and `sound`.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈ quot(A,R))` — **`mk`'s typing rule**.
#[test]
fn mk_lands_in_the_quotient() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.mk_mem.concl()));

    let (a, r, x, _) = vars4(&mut env);
    let body = Formula::imp(
        Formula::mem(x.clone(), a.clone()),
        Formula::mem(
            Term::apply(q.class, vec![a.clone(), r.clone(), x.clone()]),
            Term::apply(q.quot, vec![a.clone(), r.clone()]),
        ),
    );
    assert_eq!(*q.mk_mem.concl(), forall_all(&[a, r, x], body));
}

/// `⊢ ∀A ∀R ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R)) → class(A,R,a) = class(A,R,b))`
/// — **`sound`**, the set-level content of `⟦sound_R⟧γ = •`.
#[test]
fn related_points_have_the_same_class() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.sound.concl()));

    let (a, r, x, y) = vars4(&mut env);
    let cls = |t: &Term| Term::apply(q.class, vec![a.clone(), r.clone(), t.clone()]);
    let hyp = Formula::and(
        Formula::mem(x.clone(), a.clone()),
        Formula::and(
            Formula::mem(y.clone(), a.clone()),
            Formula::mem(q.sums.ap.sets.pair(x.clone(), y.clone()), r.clone()),
        ),
    );
    let body = Formula::imp(hyp, Formula::eq(cls(&x), cls(&y)));
    // Not a disguised reflexivity: the two classes are different terms.
    assert_ne!(cls(&x), cls(&y));
    assert_eq!(*q.sound.concl(), forall_all(&[a.clone(), r.clone(), x, y], body));
}

/// `⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) → ∃x. (x ∈ A ∧ c = class(A,R,x)))` — **no junk**:
/// the quotient is exactly the image of `mk`.
#[test]
fn every_member_of_the_quotient_is_a_class() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.quot_cases.concl()));

    let (a, r, c, x) = vars4(&mut env);
    let ex = Formula::exists(
        var_of(&x),
        Formula::and(
            Formula::mem(x.clone(), a.clone()),
            Formula::eq(c.clone(), Term::apply(q.class, vec![a.clone(), r.clone(), x.clone()])),
        ),
    );
    let body =
        Formula::imp(Formula::mem(c.clone(), Term::apply(q.quot, vec![a.clone(), r.clone()])), ex);
    assert_eq!(*q.quot_cases.concl(), forall_all(&[a, r, c], body));
}

/// `⊢ ∀A ∀R ∀a ∀b. ((b ∈ A ∧ class(A,R,a) = class(A,R,b)) → ⟨a,b⟩ ∈ eqv(A,R))` —
/// **exactness**, the converse of [`related_points_have_the_same_class`] and the
/// reason `lift` is well defined.
#[test]
fn equal_classes_come_from_related_points() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.class_exact.concl()));

    let (a, r, x, y) = vars4(&mut env);
    let cls = |t: &Term| Term::apply(q.class, vec![a.clone(), r.clone(), t.clone()]);
    let body = Formula::imp(
        Formula::and(Formula::mem(y.clone(), a.clone()), Formula::eq(cls(&x), cls(&y))),
        Formula::mem(
            q.sums.ap.sets.pair(x.clone(), y.clone()),
            Term::apply(q.eqv, vec![a.clone(), r.clone()]),
        ),
    );
    assert_eq!(*q.class_exact.concl(), forall_all(&[a, r, x, y], body));
}

// ─────────────────────────────────────────────────────────────────────────────
// `lift`.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀R ∀f. (compat(A,R,f) → sv(lift(A,R,f)))` — **`lift` is well
/// defined**, the existence half of the thesis's "the function such that …".
#[test]
fn lift_is_well_defined() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.lift_single_valued.concl()));

    let (a, r, f, _) = vars4(&mut env);
    let lift_t = Term::apply(q.lift, vec![a.clone(), r.clone(), f.clone()]);
    let body = Formula::imp(
        quot::compat(&mut env, &q.sums, q.eqv, &a, &r, &f),
        is_single_valued(&mut env, &q.sums.ap.sets, &lift_t),
    );
    assert_eq!(*q.lift_single_valued.concl(), forall_all(&[a, r, f], body));
}

/// `⊢ ∀A ∀R ∀f ∀x. ((compat(A,R,f) ∧ x ∈ A) → app(lift(A,R,f), class(A,R,x)) = app(f,x))`
/// — **the computation rule**, `⟦lift_R β f h⟧γ([x]∼) = ⟦f⟧γ(x)`.
#[test]
fn lift_computes_on_representatives() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.lift_beta.concl()));

    let (a, r, f, x) = vars4(&mut env);
    let lift_t = Term::apply(q.lift, vec![a.clone(), r.clone(), f.clone()]);
    let cls_x = Term::apply(q.class, vec![a.clone(), r.clone(), x.clone()]);
    let body = Formula::imp(
        Formula::and(
            quot::compat(&mut env, &q.sums, q.eqv, &a, &r, &f),
            Formula::mem(x.clone(), a.clone()),
        ),
        Formula::eq(q.sums.ap.apply(lift_t, cls_x), q.sums.ap.apply(f.clone(), x.clone())),
    );
    assert_eq!(*q.lift_beta.concl(), forall_all(&[a, r, f, x], body));
}

/// `⊢ ∀A ∀R ∀B ∀f. ((f ∈ fs(A,B) ∧ compat(A,R,f)) → lift(A,R,f) ∈ fs(quot(A,R), B))`
/// — **`lift`'s typing rule**, and a check that `fs` really is the three-clause
/// function space.
#[test]
fn lift_is_a_function_on_the_quotient() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.lift_in_funspace.concl()));

    let (a, r, b, f) = vars4(&mut env);
    let lift_t = Term::apply(q.lift, vec![a.clone(), r.clone(), f.clone()]);
    let quot_t = Term::apply(q.quot, vec![a.clone(), r.clone()]);
    let body = Formula::imp(
        Formula::and(
            Formula::mem(f.clone(), q.sums.fs.of(a.clone(), b.clone())),
            quot::compat(&mut env, &q.sums, q.eqv, &a, &r, &f),
        ),
        Formula::mem(lift_t.clone(), q.sums.fs.of(quot_t.clone(), b.clone())),
    );
    assert_eq!(
        *q.lift_in_funspace.concl(),
        forall_all(&[a.clone(), r.clone(), b.clone(), f.clone()], body)
    );

    // `lift(A,R,f) ∈ fs(A/∼,B)` unfolds to the *intended* condition: a subset of
    // `A/∼ × B` that is total and single-valued. Without this the typing rule
    // could be about a weaker `fs`.
    let isfun = is_function(&mut env, &q.sums.ap.sets, &q.sums.prod, &quot_t, &b, &lift_t);
    let fs_at = derived::inst_all(&q.sums.fs.fs_ax, &[quot_t.clone(), b.clone(), lift_t.clone()])
        .expect("fs_ax instantiates");
    assert_eq!(
        *fs_at.concl(),
        Formula::iff(Formula::mem(lift_t, q.sums.fs.of(quot_t, b)), isfun),
        "fs_ax is not the intended condition"
    );
}

/// `⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → compat(A,R,f))` — **Lean's `Quot.lift`
/// hypothesis suffices**: compatibility with the raw relation propagates to the
/// closure, by induction at the kernel of `f`.
#[test]
fn compatibility_with_the_relation_propagates_to_the_closure() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.compat_closure.concl()));

    let (a, r, f, _) = vars4(&mut env);
    let body = Formula::imp(
        quot::rcompat(&mut env, &q.sums, &a, &r, &f),
        quot::compat(&mut env, &q.sums, q.eqv, &a, &r, &f),
    );
    assert_eq!(*q.compat_closure.concl(), forall_all(&[a.clone(), r.clone(), f.clone()], body));

    // The two are genuinely different statements — were they the same formula
    // this theorem would be `imp_refl` in disguise.
    assert_ne!(
        quot::rcompat(&mut env, &q.sums, &a, &r, &f),
        quot::compat(&mut env, &q.sums, q.eqv, &a, &r, &f)
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,∅) → x = y)` — **the closure of nothing is the
/// diagonal**.
///
/// Without this, every theorem in the module is satisfied by
/// `eqv(A,R) = prod(A,A)` and says nothing at all.
#[test]
fn the_closure_of_the_empty_relation_is_the_diagonal() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.eqv_of_empty.concl()));

    let (a, x, y, _) = vars4(&mut env);
    let body = Formula::imp(
        Formula::mem(
            q.sums.ap.sets.pair(x.clone(), y.clone()),
            Term::apply(q.eqv, vec![a.clone(), q.empty()]),
        ),
        Formula::eq(x.clone(), y.clone()),
    );
    assert_eq!(*q.eqv_of_empty.concl(), forall_all(&[a, x, y], body));
}

/// `⊢ ∀A ∀a ∀b. ((b ∈ A ∧ class(A,∅,a) = class(A,∅,b)) → a = b)` — **`mk` is
/// injective at `R := ∅`**, so `quot(A,∅)` has as many points as `A` and no
/// quotient in this module is a point by construction.
#[test]
fn mk_is_injective_when_nothing_is_identified() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.class_injective_at_empty.concl()));

    let (a, x, y, _) = vars4(&mut env);
    let cls = |t: &Term| Term::apply(q.class, vec![a.clone(), q.empty(), t.clone()]);
    let body = Formula::imp(
        Formula::and(Formula::mem(y.clone(), a.clone()), Formula::eq(cls(&x), cls(&y))),
        Formula::eq(x.clone(), y.clone()),
    );
    assert_eq!(*q.class_injective_at_empty.concl(), forall_all(&[a, x, y], body));
}

/// `⊢ ∀A ∀f. compat(A,∅,f)` — **the compatibility antecedent is satisfiable**.
///
/// `lift`'s three theorems all carry `compat(A,R,f)`, and an antecedent nothing
/// satisfies makes them vacuous. Every `f` satisfies this one.
#[test]
fn every_function_is_compatible_with_the_empty_relation() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.compat_at_empty.concl()));

    let (a, f, _, _) = vars4(&mut env);
    let body = quot::compat(&mut env, &q.sums, q.eqv, &a, &q.empty(), &f);
    assert_eq!(*q.compat_at_empty.concl(), forall_all(&[a, f], body));
}

/// `⊢ ∀A ∀f ∀x. (x ∈ A → app(lift(A,∅,f), class(A,∅,x)) = app(f,x))` —
/// the computation rule **with no compatibility hypothesis**, over a quotient
/// that [`mk_is_injective_when_nothing_is_identified`] shows is not a point.
#[test]
fn lift_computes_unconditionally_at_the_empty_relation() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.lift_beta_at_empty.concl()));

    let (a, f, x, _) = vars4(&mut env);
    let e = q.empty();
    let lift_t = Term::apply(q.lift, vec![a.clone(), e.clone(), f.clone()]);
    let cls_x = Term::apply(q.class, vec![a.clone(), e, x.clone()]);
    let body = Formula::imp(
        Formula::mem(x.clone(), a.clone()),
        Formula::eq(q.sums.ap.apply(lift_t, cls_x), q.sums.ap.apply(f.clone(), x.clone())),
    );
    assert_eq!(*q.lift_beta_at_empty.concl(), forall_all(&[a, f, x], body));
}

/// `⊢ ∀A ∀x. (x ∈ A → app(id(A),x) = x)` — the identity graph computes, which
/// is the one thing the non-vacuity argument needs beyond
/// [`quot::compat_closure`].
#[test]
fn the_identity_graph_computes() {
    let mut env = Env::new();
    let q = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(q.identity.beta.concl()));

    let (a, x, _, _) = vars4(&mut env);
    let id_a = Term::apply(q.identity.id, vec![a.clone()]);
    let body = Formula::imp(
        Formula::mem(x.clone(), a.clone()),
        Formula::eq(q.sums.ap.apply(id_a, x.clone()), x.clone()),
    );
    assert_eq!(*q.identity.beta.concl(), forall_all(&[a, x], body));
}

/// Every theorem the module hands out is **hypothesis-free**, and the whole
/// development shares one `Sets` stack.
#[test]
fn the_development_shares_one_sets_stack() {
    let mut env = Env::new();
    let q = build(&mut env);

    for t in [
        &q.eqv_ax,
        &q.class_ax,
        &q.quot_ax,
        &q.lift_ax,
        &q.ker_ax,
        &q.sound,
        &q.lift_beta,
        &q.compat_closure,
        &q.eqv_of_empty,
    ] {
        assert!(t.hyps().is_empty(), "a theorem escaped with hypotheses");
    }

    // The `lift` graph entry is built from the *same* pairing that `eqv` was
    // carved with: `q.sums.ap.sets.pair` is the only `⟨·,·⟩` in play, and the
    // defining biconditionals above all mention it.
    let (a, r, x, f) = vars4(&mut env);
    let entry = q.sums.ap.sets.pair(
        Term::apply(q.class, vec![a.clone(), r.clone(), x.clone()]),
        q.sums.ap.apply(f, x.clone()),
    );
    let mut fv = Vec::new();
    entry.free_vars(&mut fv);
    fv.sort_by_key(|v| v.id());
    fv.dedup();
    assert_eq!(fv.len(), 4, "the graph entry mentions exactly A, R, x and f");
}

// ─────────────────────────────────────────────────────────────────────────────
// The house rule: `Γ` in, refusal out.
// ─────────────────────────────────────────────────────────────────────────────

/// `{φ} ⊢ φ` for the `φ` a theorem concludes — a premise that *looks* right at
/// every call site that only reads `concl()`.
fn hypothetical(t: &Thm) -> Thm { Thm::assume(t.concl().clone()) }

/// `Quotient::over` refuses a [`Sums`] whose theorem fields are not all `⊢`.
///
/// The concrete hazard behind the whole sweep. `Sums` documents `pow_ax` as
/// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`, and `mk_mem` joins it with `Thm::mp`; before the
/// guard the quotient built happily and `mk_mem`, `quot_cases`, `sound`,
/// `lift_in_funspace` and all five non-vacuity fields came back carrying the
/// assumption, under doc comments that say `⊢`.
#[test]
fn quotient_over_refuses_a_hypothetical_sums() {
    // Control: the honest `Sums` builds a quotient.
    let mut env = Env::new();
    let sums = Sums::new(&mut env).expect("sums");
    assert!(Quotient::over(&mut env, sums).is_some(), "the honest Sums must still work");

    let mut env = Env::new();
    let mut sums = Sums::new(&mut env).expect("sums");
    sums.pow_ax = hypothetical(&sums.pow_ax);
    assert!(
        Quotient::over(&mut env, sums).is_none(),
        "a Sums with a hypothetical pow_ax must be refused, not carried into every field"
    );
}

/// `lift_beta` refuses an `app_pair` that proves the wrong **equation**.
///
/// The ι-rule's consequent arrives verbatim from `app_pair`; the kernel forces
/// only that the two antecedents meet. `⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) →
/// app(f,x) = app(f,x))` is true, is one weakening of `Thm::eq_refl` away, and
/// has exactly that antecedent — so before the pin it composed and produced a
/// reflexivity labelled as `⟦lift_R β f h⟧γ([x]∼) = ⟦f⟧γ(x)`.
#[test]
fn lift_beta_refuses_an_app_pair_proving_the_wrong_equation() {
    let mut env = Env::new();
    let q = build(&mut env);
    let lv = quot::Lift {
        s: &q.sums,
        eqv: q.eqv,
        class: q.class,
        quot: q.quot,
        lift: q.lift,
        lift_ax: &q.lift_ax,
    };

    // Control: the real `app_of_pair` still gives the computation rule.
    let honest = derived::ext::app_of_pair(&mut env, &q.sums.ap).expect("app_of_pair");
    assert!(
        quot::lift_beta(&mut env, &lv, &q.lift_single_valued, &q.lift_pair, &honest).is_some(),
        "the honest app_pair must still work"
    );

    let (fv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tx, ty) = (Term::var(fv), Term::var(xv), Term::var(yv));
    let antecedent = Formula::and(
        is_single_valued(&mut env, &q.sums.ap.sets, &tf),
        Formula::mem(q.sums.ap.sets.pair(tx.clone(), ty), tf.clone()),
    );
    let reflexive = derived::a1i(
        &Thm::eq_refl(q.sums.ap.apply(tf.clone(), tx.clone())),
        antecedent,
    );
    let wrong = derived::gen_all(&[fv, xv, yv], &reflexive);
    assert!(
        quot::lift_beta(&mut env, &lv, &q.lift_single_valued, &q.lift_pair, &wrong).is_none(),
        "an app_pair concluding app(f,x) = app(f,x) must not pass for the ι-rule"
    );
}

/// `q_sound` refuses a `class_eq` that proves the wrong **equation**.
///
/// The same shape one level up, and worth its own test because `sound` is a
/// headline theorem: the derivation is a single `syl`, so a `class_eq`
/// concluding `class(A,R,a) = class(A,R,a)` composes and yields a reflexivity
/// labelled `sound`, which is the claim "related points are identified" going
/// missing entirely.
#[test]
fn q_sound_refuses_a_class_eq_proving_the_wrong_equation() {
    let mut env = Env::new();
    let q = build(&mut env);

    // Control.
    assert!(
        quot::q_sound(&mut env, &q.sums, q.class, &q.eqv_incl, &q.class_eq).is_some(),
        "the honest class_eq must still work"
    );

    let (a, r, x, y) = vars4(&mut env);
    let related = Formula::mem(
        q.sums.ap.sets.pair(x.clone(), y.clone()),
        Term::apply(q.eqv, vec![a.clone(), r.clone()]),
    );
    let cls_a = Term::apply(q.class, vec![a.clone(), r.clone(), x.clone()]);
    let wrong = derived::gen_all(
        &[var_of(&a), var_of(&r), var_of(&x), var_of(&y)],
        &derived::a1i(&Thm::eq_refl(cls_a), related),
    );
    assert!(
        quot::q_sound(&mut env, &q.sums, q.class, &q.eqv_incl, &wrong).is_none(),
        "a class_eq concluding class(a) = class(a) must not pass for sound"
    );
}

/// The closure lemmas refuse a hypothetical premise.
///
/// One representative per position: the defining axiom, the `Sums` theorem
/// passed alongside it, and one of the four clauses a composite consumes. In
/// each case `Thm::mp` used to union the assumption into a result the header
/// calls `⊢`, and `Thm::gen` did not object because the assumed formula is
/// closed.
#[test]
fn the_closure_lemmas_refuse_hypothetical_premises() {
    let mut env = Env::new();
    let q = build(&mut env);

    assert!(
        quot::eqv_subset(&mut env, &q.sums, q.eqv, &hypothetical(&q.eqv_ax)).is_none(),
        "eqv_subset on a hypothetical eqv_ax"
    );
    assert!(
        quot::eqv_induction(&mut env, &q.sums, q.eqv, &hypothetical(&q.eqv_ax)).is_none(),
        "eqv_induction on a hypothetical eqv_ax"
    );
    assert!(
        quot::eqv_refl(
            &mut env,
            &q.sums,
            q.eqv,
            &q.eqv_ax,
            &hypothetical(&q.sums.pair_in_prod)
        )
        .is_none(),
        "eqv_refl on a hypothetical pair_in_prod"
    );
    assert!(
        quot::eqv_closed_self(
            &mut env,
            &q.sums,
            q.eqv,
            &hypothetical(&q.eqv_refl),
            &q.eqv_sym,
            &q.eqv_trans,
            &q.eqv_incl
        )
        .is_none(),
        "eqv_closed_self on a hypothetical clause"
    );
    assert!(
        quot::class_self(
            &mut env,
            &quot::Classes {
                s: &q.sums,
                eqv: q.eqv,
                class: q.class,
                class_ax: &q.class_ax
            },
            &hypothetical(&q.eqv_refl)
        )
        .is_none(),
        "class_self on a hypothetical eqv_refl"
    );

    // Controls, so that the guards above are not just a blanket `None`.
    assert!(quot::eqv_subset(&mut env, &q.sums, q.eqv, &q.eqv_ax).is_some());
    assert!(quot::eqv_refl(&mut env, &q.sums, q.eqv, &q.eqv_ax, &q.sums.pair_in_prod).is_some());
}

/// The three apparatus bundles refuse a hypothetical defining axiom.
///
/// `Classes`, `Ker` and `Lift` all have `pub` fields and a `parts` method that
/// pins the *conclusion* of the axiom they carry. That check says nothing about
/// `Γ`, so each bundle now also has a hypothesis check, and it covers the `Sums`
/// the bundle points at as well as the axiom itself.
#[test]
fn the_apparatus_bundles_refuse_a_hypothetical_defining_axiom() {
    let mut env = Env::new();
    let q = build(&mut env);

    let class_ax = hypothetical(&q.class_ax);
    let bad_classes =
        quot::Classes { s: &q.sums, eqv: q.eqv, class: q.class, class_ax: &class_ax };
    let good_classes =
        quot::Classes { s: &q.sums, eqv: q.eqv, class: q.class, class_ax: &q.class_ax };
    assert!(quot::class_subset(&mut env, &bad_classes).is_none(), "class_subset");
    assert!(quot::class_eq(&mut env, &bad_classes, &q.eqv_sym, &q.eqv_trans).is_none(), "class_eq");
    assert!(quot::class_subset(&mut env, &good_classes).is_some(), "control");

    let ker_ax = hypothetical(&q.ker_ax);
    let bad_ker = quot::Ker { s: &q.sums, ker: q.ker, ker_ax: &ker_ax };
    let good_ker = quot::Ker { s: &q.sums, ker: q.ker, ker_ax: &q.ker_ax };
    assert!(quot::ker_subset(&mut env, &bad_ker).is_none(), "ker_subset");
    assert!(quot::ker_pair(&mut env, &bad_ker).is_none(), "ker_pair");
    assert!(quot::ker_subset(&mut env, &good_ker).is_some(), "control");

    let lift_ax = hypothetical(&q.lift_ax);
    let bad_lift = quot::Lift {
        s: &q.sums,
        eqv: q.eqv,
        class: q.class,
        quot: q.quot,
        lift: q.lift,
        lift_ax: &lift_ax,
    };
    let good_lift = quot::Lift {
        s: &q.sums,
        eqv: q.eqv,
        class: q.class,
        quot: q.quot,
        lift: q.lift,
        lift_ax: &q.lift_ax,
    };
    assert!(quot::lift_pair(&mut env, &bad_lift).is_none(), "lift_pair");
    assert!(
        quot::lift_single_valued(&mut env, &bad_lift, &q.class_exact).is_none(),
        "lift_single_valued"
    );
    assert!(quot::lift_pair(&mut env, &good_lift).is_some(), "control");
}
