//! The accessibility carrier `acc(A,R)`: its defining biconditional, the
//! introduction rule, induction, well-founded induction over a formula, and
//! non-vacuity in both polarities.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem with the right
//! *name* but the wrong *shape* fails here.
//!
//! **Non-vacuity is the whole game, twice over.** Every lemma in the module is
//! trivially true when `acc(A,R)` is empty, and A2/A3 are trivially true when
//! `acc(A,R)` is all of `A`. [`the_empty_relation_makes_everything_accessible`]
//! rules out the first, [`a_reflexive_point_is_never_accessible`] the second.

use kernel::{Env, Formula, Term, Thm};

use derived::acc::{self, Acc};
use derived::funcs::Apply;
use derived::{a1i, and_intro, inst_all, opair};

/// The whole development, built once per test.
fn build(env: &mut Env) -> Acc {
    Acc::new(env).expect("acc")
}

/// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) ↔ (z ∈ A ∧ ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C)))`
#[test]
fn the_defining_biconditional_is_one_separation_on_the_carrier() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.acc_ax.concl()));

    let (a, r, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz) = (Term::var(a), Term::var(r), Term::var(z));
    let cond = acc::acc_cond(&mut env, ac.sets.up, &ta, &tr, &tz);
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(
                z,
                Formula::iff(
                    Formula::mem(tz.clone(), ac.of(ta.clone(), tr)),
                    Formula::and(Formula::mem(tz, ta), cond),
                ),
            ),
        ),
    );
    assert_eq!(*ac.acc_ax.concl(), want);
}

/// **A0**: `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → z ∈ A)`.
///
/// This is the theorem that makes the module cheap: there is a set to carve
/// `acc` out of, so unlike `W` it needs no bound parameter.
#[test]
fn the_accessible_set_is_a_subset_of_the_carrier() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.acc_subset.concl()));

    let (a, r, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz) = (Term::var(a), Term::var(r), Term::var(z));
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), ac.of(ta.clone(), tr)),
                    Formula::mem(tz, ta),
                ),
            ),
        ),
    );
    assert_eq!(*ac.acc_subset.concl(), want);
}

/// **A2**: `⊢ ∀A ∀R ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → ∀z. (z ∈ acc(A,R) → z ∈ C))`.
#[test]
fn accessibility_is_the_least_step_closed_subset() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.acc_induction.concl()));

    let (a, r, c, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc, tz) = (Term::var(a), Term::var(r), Term::var(c), Term::var(z));
    let guard = Formula::and(
        kernel::thm::subset(&mut env, tc.clone(), ta.clone()),
        ac.step_closed_at(&mut env, &ta, &tr, &tc),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(
                c,
                Formula::imp(
                    guard,
                    Formula::forall(
                        z,
                        Formula::imp(
                            Formula::mem(tz.clone(), ac.of(ta, tr)),
                            Formula::mem(tz, tc),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*ac.acc_induction.concl(), want);
}

/// **A1**, and the point of the whole entry:
/// `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc(A,R)))) → x ∈ acc(A,R))`
///
/// **Unconditional.** The corresponding W-type rule
/// `derived::wtype::sup_mem` carries `closed(A,B,u)` as an antecedent that only
/// `derived::bound` can discharge; the assertion below is that no such
/// antecedent is present here.
#[test]
fn the_introduction_rule_carries_no_bound_hypothesis() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.acc_intro.concl()));

    let (a, r, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx) = (Term::var(a), Term::var(r), Term::var(x));
    let acc_t = ac.of(ta.clone(), tr.clone());
    let hyp = Formula::and(
        Formula::mem(tx.clone(), ta.clone()),
        ac.preds_in_at(&mut env, &ta, &tr, &acc_t, &tx),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(x, Formula::imp(hyp, Formula::mem(tx, acc_t))),
        ),
    );
    assert_eq!(*ac.acc_intro.concl(), want);
}

/// **A3**: `⊢ ind_step(φ) → ∀z. (z ∈ acc(A,R) → φ(z))`, at `φ(z) := z ∈ S`.
///
/// The scheme is checked at a `φ` mentioning a parameter other than `A` and
/// `R`, since that is the case where the fresh symbol for `{z ∈ acc : φ(z)}`
/// has to be taken over the right argument list.
#[test]
fn well_founded_induction_over_a_formula() {
    let mut env = Env::new();
    let ac = build(&mut env);

    let (a, r, s, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, ts, tz) = (Term::var(a), Term::var(r), Term::var(s), Term::var(z));
    let acc_t = ac.of(ta.clone(), tr.clone());
    let phi = Formula::mem(tz.clone(), ts);

    let rect = acc::acc_rect(
        &mut env,
        &ac,
        &[a, r, s],
        acc::Params { a, r },
        z,
        &phi,
    )
    .expect("acc_rect");
    assert!(kernel::thm::debug_locally_closed(rect.concl()));

    let ih = acc::ind_step(&mut env, &ac, &acc_t, &ta, &tr, z, &phi);
    let want = Formula::imp(
        ih,
        Formula::forall(z, Formula::imp(Formula::mem(tz, acc_t), phi.clone())),
    );
    assert_eq!(*rect.concl(), want);

    // The scheme's side conditions really are checked. `A` and `R` must be
    // parameters, since the subset mentions `acc(A,R)`:
    assert!(acc::acc_rect(&mut env, &ac, &[a], acc::Params { a, r }, z, &phi).is_none());
    // the induction variable must not be one of them:
    assert!(
        acc::acc_rect(&mut env, &ac, &[a, r, z], acc::Params { a, r }, z, &phi).is_none()
    );
    // and `φ`'s other free variables must be covered — this one is refused by
    // `kernel::thm::define`'s own coverage check, not by `acc_rect`, since an
    // uncovered free variable in a defining axiom is unsound and not merely
    // untidy.
    assert!(acc::acc_rect(&mut env, &ac, &[a, r], acc::Params { a, r }, z, &phi).is_none());
}

/// The induction hypothesis of [`well_founded_induction_over_a_formula`] hands
/// the minor premise **both** `y ∈ acc(A,R)` and `φ(y)`, which is what makes it
/// an interpretation of Lean's `Acc.rec` rather than a weaker scheme.
#[test]
fn the_induction_hypothesis_carries_accessibility_as_well_as_the_motive() {
    let mut env = Env::new();
    let ac = build(&mut env);

    let (a, r, s, z, x, y) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, ts, tz) = (Term::var(a), Term::var(r), Term::var(s), Term::var(z));
    let (tx, ty) = (Term::var(x), Term::var(y));
    let acc_t = ac.of(ta.clone(), tr.clone());
    let phi = Formula::mem(tz, ts.clone());

    let hyp = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::imp(
                Formula::mem(ac.edge(ty.clone(), tx.clone()), tr.clone()),
                Formula::and(
                    Formula::mem(ty.clone(), acc_t.clone()),
                    Formula::mem(ty, ts.clone()),
                ),
            ),
        ),
    );
    let want = Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), ta.clone()),
            Formula::imp(hyp, Formula::mem(tx, ts)),
        ),
    );
    assert_eq!(acc::ind_step(&mut env, &ac, &acc_t, &ta, &tr, z, &phi), want);
}

/// `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. ¬(⟨y,x⟩ ∈ R)) → x ∈ acc(A,R))` — the base case.
#[test]
fn minimal_points_are_accessible() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.minimal.concl()));

    let (a, r, x, y) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, ty) = (Term::var(a), Term::var(r), Term::var(x), Term::var(y));
    let hyp = Formula::and(
        Formula::mem(tx.clone(), ta.clone()),
        Formula::forall(y, Formula::not(Formula::mem(ac.edge(ty, tx.clone()), tr.clone()))),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(x, Formula::imp(hyp, Formula::mem(tx, ac.of(ta, tr)))),
        ),
    );
    assert_eq!(*ac.minimal.concl(), want);
}

/// **Non-vacuity, positive**: `⊢ ∀A. acc(A,∅) = A`.
///
/// Without this every theorem in the module could be true because `acc(A,R)` is
/// always empty.
#[test]
fn the_empty_relation_makes_everything_accessible() {
    let mut env = Env::new();
    let ac = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(ac.empty_relation.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let want = Formula::forall(a, Formula::eq(ac.of(ta.clone(), ac.empty_term()), ta));
    assert_eq!(*ac.empty_relation.concl(), want);

    // Not a disguised reflexivity: the two sides are different terms.
    let ta = Term::var(a);
    assert_ne!(ac.of(ta.clone(), ac.empty_term()), ta);
}

/// **Non-vacuity, negative**: `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ¬(⟨z,z⟩ ∈ R))`.
#[test]
fn no_accessible_point_is_reflexive() {
    let mut env = Env::new();
    let ac = build(&mut env);
    let nl = ac.no_loops(&mut env).expect("no_loops");
    assert!(kernel::thm::debug_locally_closed(nl.concl()));

    let (a, r, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz) = (Term::var(a), Term::var(r), Term::var(z));
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), ac.of(ta, tr.clone())),
                    Formula::not(Formula::mem(ac.edge(tz.clone(), tz), tr)),
                ),
            ),
        ),
    );
    assert_eq!(*nl.concl(), want);
}

/// **Non-vacuity, negative, without reflexivity**:
/// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ∀w. ¬(w ∈ A ∧ (⟨z,w⟩ ∈ R ∧ ⟨w,z⟩ ∈ R)))`.
///
/// The `acc(A,R) ⊊ A` phenomenon is about well-foundedness, not about loops at
/// a point: an irreflexive `R` with a 2-cycle already excludes both ends of it.
/// This is also `acc_rect` at a `φ` with a bound variable of its own, which
/// `no_accessible_point_is_reflexive` does not exercise.
#[test]
fn no_accessible_point_lies_on_a_two_cycle() {
    let mut env = Env::new();
    let ac = build(&mut env);
    let ntc = ac.no_two_cycle(&mut env).expect("no_two_cycle");
    assert!(kernel::thm::debug_locally_closed(ntc.concl()));

    let (a, r, z, w) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz, tw) = (Term::var(a), Term::var(r), Term::var(z), Term::var(w));
    let cycle = Formula::and(
        Formula::mem(tw.clone(), ta.clone()),
        Formula::and(
            Formula::mem(ac.edge(tz.clone(), tw.clone()), tr.clone()),
            Formula::mem(ac.edge(tw, tz.clone()), tr.clone()),
        ),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            r,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz, ac.of(ta, tr)),
                    Formula::forall(w, Formula::not(cycle)),
                ),
            ),
        ),
    );
    assert_eq!(*ntc.concl(), want);
}

/// **The two polarities at one and the same carrier.**
///
/// At `A := {∅}` this derives, without hypotheses,
///
/// ```text
/// ⊢ ∅ ∈ acc({∅}, ∅)             — the accessible set is all of `A`
/// ⊢ ¬(∅ ∈ acc({∅}, {⟨∅,∅⟩}))    — and at a reflexive edge it is empty
/// ```
///
/// so `acc(A,R) ⊆ A` is strict for some `R`, and `acc` is genuinely a function
/// of the relation rather than a projection to `A`.
#[test]
fn a_reflexive_point_is_never_accessible() {
    let mut env = Env::new();
    let ac = build(&mut env);
    let nl = ac.no_loops(&mut env).expect("no_loops");

    let up = ac.sets.up;
    let e = ac.empty_term();
    let carrier = derived::singleton(up, e.clone()); // A := {∅}
    let loop_edge = ac.edge(e.clone(), e.clone()); // ⟨∅,∅⟩
    let rel = derived::singleton(up, loop_edge.clone()); // R := {⟨∅,∅⟩}

    // `t ∈ {t}`, from the pairing axiom and reflexivity of equality.
    let mem_singleton = |t: &Term| -> Thm {
        let at = inst_all(&ac.sets.up_ax, &[t.clone(), t.clone(), t.clone()])
            .expect("upair axiom");
        let eq = Thm::eq_refl(t.clone());
        let disj = a1i(&eq, Formula::not(Formula::eq(t.clone(), t.clone())));
        Thm::mp(&derived::iff_mpr(&at).expect("mpr"), &disj).expect("mem singleton")
    };
    let e_in_carrier = mem_singleton(&e);
    let loop_in_rel = mem_singleton(&loop_edge);
    assert_eq!(*e_in_carrier.concl(), Formula::mem(e.clone(), carrier.clone()));
    assert_eq!(*loop_in_rel.concl(), Formula::mem(loop_edge.clone(), rel.clone()));

    // Positive: `∅` is `∅`-minimal in `{∅}`, so it is accessible there.
    let y = env.fresh_var();
    let nopred = Thm::gen(
        y,
        &inst_all(&ac.empty_ax, &[opair(up, Term::var(y), e.clone())]).expect("empty"),
    );
    let min_at = inst_all(&ac.minimal, &[carrier.clone(), e.clone(), e.clone()])
        .expect("minimal");
    let accessible =
        Thm::mp(&min_at, &and_intro(&e_in_carrier, &nopred)).expect("minimal applies");
    assert_eq!(
        *accessible.concl(),
        Formula::mem(e.clone(), ac.of(carrier.clone(), e.clone()))
    );

    // Negative: at the reflexive edge it is not.
    let nl_at = inst_all(&nl, &[carrier.clone(), rel.clone(), e.clone()]).expect("no_loops");
    let excluded = derived::mpd_const(&nl_at, &loop_in_rel).expect("contradiction");
    assert_eq!(
        *excluded.concl(),
        Formula::not(Formula::mem(e, ac.of(carrier, rel)))
    );
}

/// An `Acc` built over an existing [`Apply`] shares its pairing and its empty
/// set, so `⟨y,x⟩` denotes the same term in both.
///
/// Building two apparatuses independently would mint two unrelated pairing
/// operations, and an `acc` over one would say nothing about a relation built
/// with the other.
#[test]
fn an_accessibility_apparatus_can_share_a_pairing() {
    let mut env = Env::new();
    let ap = Apply::new(&mut env).expect("apply");
    let ac = Acc::with_apply(&mut env, &ap).expect("acc over apply");

    let (x, y) = (env.fresh_var(), env.fresh_var());
    assert_eq!(
        ac.edge(Term::var(y), Term::var(x)),
        opair(ap.sets.up, Term::var(y), Term::var(x))
    );
    assert_eq!(ac.empty_term(), Term::apply(ap.empty, vec![]));

    // And the theorems really are about that shared pairing.
    let (a, r, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let nl = ac.no_loops(&mut env).expect("no_loops");
    let at = inst_all(&nl, &[Term::var(a), Term::var(r), Term::var(z)]).expect("inst");
    let (_, rhs) = at.concl().as_imp().expect("an implication");
    let (edge, _) = rhs.as_imp().expect("a negation").0.as_mem().expect("a membership");
    assert_eq!(edge, opair(ap.sets.up, Term::var(z), Term::var(z)));
}
