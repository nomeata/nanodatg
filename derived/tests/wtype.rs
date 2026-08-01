//! The W-type: `sup`'s typing rule, induction, inversion, injectivity, and
//! structural induction over a formula.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem with the right
//! *name* but the wrong *shape* fails here.
//!
//! **Non-vacuity is the whole game.** Every lemma in the module is trivially
//! true when `W(A,B,u)` is empty, so the module would prove nothing without a
//! witness. [`the_unit_wtype_is_inhabited`] is that witness.

use kernel::{Env, Formula, Term};

use derived::sums::Sums;
use derived::wtype::{self, Wtype};

/// The whole development, built once per test.
fn build(env: &mut Env) -> Wtype {
    Wtype::new(env).expect("W-type")
}

/// `⊢ ∀X ∀Y ∀Z ∀f. ((f ∈ fs(X,Y) ∧ Y ⊆ Z) → f ∈ fs(X,Z))`.
#[test]
fn the_function_space_is_monotone_in_its_target() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.fs_mono.concl()));

    let (x, y, z, f) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz, tf) = (Term::var(x), Term::var(y), Term::var(z), Term::var(f));
    let body = Formula::imp(
        Formula::and(
            Formula::mem(tf.clone(), w.sums.fs.of(tx.clone(), ty.clone())),
            kernel::thm::subset(&mut env, ty.clone(), tz.clone()),
        ),
        Formula::mem(tf, w.sums.fs.of(tx, tz)),
    );
    let want = Formula::forall(
        x,
        Formula::forall(y, Formula::forall(z, Formula::forall(f, body))),
    );
    assert_eq!(*w.fs_mono.concl(), want);

    // Non-vacuity of the *statement*: the two function spaces are different
    // terms, so this is not a disguised reflexivity.
    assert_ne!(w.sums.fs.of(Term::var(x), Term::var(y)), w.sums.fs.of(Term::var(x), Term::var(z)));
}

/// `⊢ ∀S. ∅ ∈ fs(∅, S)` — the empty function.
#[test]
fn the_empty_set_is_the_empty_function() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.empty_fun.concl()));

    let s = env.fresh_var();
    let e = w.empty();
    let want = Formula::forall(
        s,
        Formula::mem(e.clone(), w.sums.fs.of(e.clone(), Term::var(s))),
    );
    assert_eq!(*w.empty_fun.concl(), want);
}

/// `⊢ ∀a. app(∅, a) = ∅` — `∅` is the constant-empty family.
#[test]
fn the_empty_family_has_empty_fibres() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.app_empty.concl()));

    let a = env.fresh_var();
    let e = w.empty();
    let want =
        Formula::forall(a, Formula::eq(w.fibre(e.clone(), Term::var(a)), e.clone()));
    assert_eq!(*w.app_empty.concl(), want);

    // `app(∅,a)` is not syntactically `∅`, so the equation says something.
    assert_ne!(w.fibre(e.clone(), Term::var(a)), e);
}

/// The defining property of `W`:
/// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) ↔ (z ∈ u ∧ ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S)))`.
#[test]
fn the_wtype_has_its_defining_property() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.w_ax.concl()));

    let (a, b, u, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(a), Term::var(b), Term::var(u), Term::var(z));

    let cond = wtype::w_cond(&mut env, &w.sums, &ta, &tb, &tu, &tz);
    let lhs = Formula::mem(tz.clone(), w.of(ta, tb, tu.clone()));
    let rhs = Formula::and(Formula::mem(tz, tu), cond);
    // The two sides of the biconditional are genuinely different formulas.
    assert_ne!(lhs, rhs);

    let want = Formula::forall(
        a,
        Formula::forall(b, Formula::forall(u, Formula::forall(z, Formula::iff(lhs, rhs)))),
    );
    assert_eq!(*w.w_ax.concl(), want);
}

/// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) → z ∈ u)`.
#[test]
fn the_wtype_sits_inside_its_bound() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.w_subset.concl()));

    let (a, b, u, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(a), Term::var(b), Term::var(u), Term::var(z));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                u,
                Formula::forall(
                    z,
                    Formula::imp(
                        Formula::mem(tz.clone(), w.of(ta, tb, tu.clone())),
                        Formula::mem(tz, tu),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*w.w_subset.concl(), want);
}

/// **W2**, induction:
/// `⊢ ∀A ∀B ∀u ∀C. ((C ⊆ u ∧ closed(A,B,C)) → ∀z. (z ∈ W(A,B,u) → z ∈ C))`.
///
/// Note there is **no** `C ⊆ W` antecedent: `C` need only be a closed subset of
/// the bound.
#[test]
fn the_wtype_is_the_least_closed_subset() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.w_induction.concl()));

    let (a, b, u, c, z) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tu, tc, tz) =
        (Term::var(a), Term::var(b), Term::var(u), Term::var(c), Term::var(z));

    let hyp = Formula::and(
        kernel::thm::subset(&mut env, tc.clone(), tu.clone()),
        wtype::closed(&mut env, &w.sums, &ta, &tb, &tc),
    );
    let concl = Formula::forall(
        z,
        Formula::imp(
            Formula::mem(tz.clone(), w.of(ta, tb, tu)),
            Formula::mem(tz, tc),
        ),
    );
    assert_ne!(hyp, concl);
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(u, Formula::forall(c, Formula::imp(hyp, concl))),
        ),
    );
    assert_eq!(*w.w_induction.concl(), want);
}

/// **W1**, `sup`'s typing rule:
/// `⊢ ∀A ∀B ∀u. (closed(A,B,u) → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) → ⟨a,f⟩ ∈ W)))`.
///
/// The `closed(A,B,u)` antecedent is where the bound hypothesis does its work,
/// and the test pins that it is there.
#[test]
fn sup_lands_in_the_wtype() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.sup_mem.concl()));

    let (a, b, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (ta, tb, tu) = (Term::var(a), Term::var(b), Term::var(u));
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));

    let w_t = w.of(ta.clone(), tb.clone(), tu.clone());
    let inner = Formula::forall(
        pf,
        Formula::imp(
            Formula::mem(tpf.clone(), w.sums.fs.of(w.fibre(tb.clone(), tpa.clone()), w_t.clone())),
            Formula::mem(w.sup(tpa.clone(), tpf), w_t),
        ),
    );
    let body = Formula::imp(
        wtype::closed(&mut env, &w.sums, &ta, &tb, &tu),
        Formula::forall(pa, Formula::imp(Formula::mem(tpa, ta), inner)),
    );
    let want = Formula::forall(a, Formula::forall(b, Formula::forall(u, body)));
    assert_eq!(*w.sup_mem.concl(), want);
}

/// **W4**: `⊢ ∀a ∀f ∀a′ ∀f′. (⟨a,f⟩ = ⟨a′,f′⟩ → (a = a′ ∧ f = f′))`.
///
/// Reused from [`derived::pairs::opair_inj`] rather than re-derived — `sup` is
/// the Kuratowski pair.
#[test]
fn sup_is_injective() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.sup_inj.concl()));

    let (a, f, a2, f2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, ta2, tf2) = (Term::var(a), Term::var(f), Term::var(a2), Term::var(f2));
    let body = Formula::imp(
        Formula::eq(w.sup(ta.clone(), tf.clone()), w.sup(ta2.clone(), tf2.clone())),
        Formula::and(Formula::eq(ta, ta2), Formula::eq(tf, tf2)),
    );
    let want = Formula::forall(
        a,
        Formula::forall(f, Formula::forall(a2, Formula::forall(f2, body))),
    );
    assert_eq!(*w.sup_inj.concl(), want);
}

/// **The capstone**: structural induction over a formula,
/// `⊢ closed(A,B,u) → (IH → ∀z. (z ∈ W(A,B,u) → φ(z)))`.
///
/// Exercised at `φ(z) := z ∈ p` over a parameter `p` that has nothing to do
/// with the W-type, so the shape cannot be an accident of the instance.
#[test]
fn structural_induction_over_a_formula() {
    let mut env = Env::new();
    let w = build(&mut env);

    let (a, b, u, p, z) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tu, tp, tz) =
        (Term::var(a), Term::var(b), Term::var(u), Term::var(p), Term::var(z));
    let phi = Formula::mem(tz.clone(), tp);

    let out = wtype::w_rect(&mut env, &w, &[a, b, u, p], wtype::Params { a, b, u }, z, &phi).expect("w_rect");
    assert!(kernel::thm::debug_locally_closed(out.concl()));

    let w_t = w.of(ta.clone(), tb.clone(), tu.clone());
    let cl = wtype::closed(&mut env, &w.sums, &ta, &tb, &tu);
    let step = wtype::ind_step(&mut env, &w.sums, &w_t, &ta, &tb, z, &phi);
    let goal =
        Formula::forall(z, Formula::imp(Formula::mem(tz, w_t), phi.clone()));

    // The three parts are genuinely different formulas.
    assert_ne!(cl, step);
    assert_ne!(step, goal);
    assert_eq!(*out.concl(), Formula::imp(cl, Formula::imp(step, goal)));
}

/// The induction step really carries an induction hypothesis.
///
/// Compared against the same formula with `∀b ∈ B(a). φ(f b)` dropped — if
/// [`derived::wtype::ind_step`] had built the weaker premise the capstone would
/// be *stronger* than it is entitled to be, and this is the cheap check that it
/// did not.
#[test]
fn the_induction_step_has_an_induction_hypothesis() {
    let mut env = Env::new();
    let w = build(&mut env);
    let (a, b, u, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(a), Term::var(b), Term::var(u), Term::var(z));
    let w_t = w.of(ta.clone(), tb.clone(), tu);
    let phi = Formula::mem(tz, Term::var(a));

    let step = wtype::ind_step(&mut env, &w.sums, &w_t, &ta, &tb, z, &phi);

    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));
    let fibre = w.fibre(tb.clone(), tpa.clone());
    let without = Formula::forall(
        pa,
        Formula::imp(
            Formula::mem(tpa.clone(), ta),
            Formula::forall(
                pf,
                Formula::imp(
                    Formula::mem(tpf.clone(), w.sums.fs.of(fibre, w_t)),
                    phi.subst(z, &w.sup(tpa, tpf)),
                ),
            ),
        ),
    );
    assert_ne!(step, without);
}

/// `w_rect` refuses a parameter list that does not cover `A`, `B` and `u`.
///
/// Not pedantry: `C = {z ∈ W(A,B,u) : φ(z)}` mentions all three, and
/// `kernel::thm::define` would reject the extension — silently returning a
/// theorem about the wrong set is the failure mode this rules out.
#[test]
fn w_rect_insists_on_complete_parameters() {
    let mut env = Env::new();
    let w = build(&mut env);
    let (a, b, u, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(Term::var(z), Term::var(a));
    assert!(wtype::w_rect(&mut env, &w, &[a, b], wtype::Params { a, b, u }, z, &phi).is_none());
    assert!(wtype::w_rect(&mut env, &w, &[a, b, u, z], wtype::Params { a, b, u }, z, &phi).is_none());
}

/// **W3**, inversion:
/// `⊢ ∀A ∀B ∀u. (closed(A,B,u) → ∀w. (w ∈ W → ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a),W) ∧ w = ⟨a,f⟩))))`.
#[test]
fn every_member_of_the_wtype_is_a_sup() {
    let mut env = Env::new();
    let w = build(&mut env);
    let out = w.inversion(&mut env).expect("w_inversion");
    assert!(kernel::thm::debug_locally_closed(out.concl()));

    let (a, b, u, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(a), Term::var(b), Term::var(u), Term::var(z));
    let w_t = w.of(ta.clone(), tb.clone(), tu.clone());
    let psi = wtype::is_sup(&mut env, &w.sums, &w_t, &ta, &tb, &tz);
    let mem_w = Formula::mem(tz, w_t);
    assert_ne!(mem_w, psi);

    let body = Formula::imp(
        wtype::closed(&mut env, &w.sums, &ta, &tb, &tu),
        Formula::forall(z, Formula::imp(mem_w, psi)),
    );
    let want = Formula::forall(a, Formula::forall(b, Formula::forall(u, body)));
    assert_eq!(*out.concl(), want);
}

/// **Non-vacuity.** `⊢ ⟨•,∅⟩ ∈ W(1, ∅, {⟨•,∅⟩})` — the unit type as a W-type.
///
/// Without this the entire module is vacuous: every lemma above holds trivially
/// when `W(A,B,u)` is empty. This is the one test that says the construction
/// has something in it.
#[test]
fn the_unit_wtype_is_inhabited() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.inhabited.concl()));

    let e = w.empty();
    let sup0 = w.sup(e.clone(), e.clone());
    let u = derived::singleton(w.sums.ap.sets.up, sup0.clone());
    let want = Formula::mem(sup0.clone(), w.of(w.sums.unit(), e.clone(), u.clone()));
    assert_eq!(*w.inhabited.concl(), want);

    // The instance really is the intended one: `A` is `1`, not `∅`, and `u` is
    // the singleton of the witness, not the witness itself.
    assert_ne!(w.sums.unit(), e);
    assert_ne!(u, sup0);

    // And the same construction is reachable through the generic derivation.
    let again =
        wtype::unit_wtype_inhabited(&mut env, &w.sums, w.w, &w.w_ax, &w.empty_fun, &w.app_empty)
            .expect("inhabitedness");
    assert_eq!(*again.concl(), want);
}

/// **Non-vacuity of the bound hypothesis.** `⊢ closed(1, ∅, {⟨•,∅⟩})`.
///
/// W1, W3 and the capstone all carry `closed(A,B,u)` as an antecedent, so they
/// would say nothing if no `u` ever satisfied it. This exhibits one, and
/// together with [`the_unit_wtype_is_inhabited`] it means the hypothesis is
/// satisfiable at an instance whose `W` is non-empty.
#[test]
fn the_unit_bound_is_closed() {
    let mut env = Env::new();
    let w = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(w.bound_closed.concl()));

    let e = w.empty();
    let sup0 = w.sup(e.clone(), e.clone());
    let u = derived::singleton(w.sums.ap.sets.up, sup0);
    let want = wtype::closed(&mut env, &w.sums, &w.sums.unit(), &e, &u);
    assert_eq!(*w.bound_closed.concl(), want);

    // And it is a real antecedent-discharge: W1 at this instance now yields an
    // unconditional typing rule for `sup`.
    let sm = derived::inst_all(&w.sup_mem, &[w.sums.unit(), e.clone(), u.clone()])
        .expect("instantiate W1");
    let typed = kernel::Thm::mp(&sm, &w.bound_closed).expect("discharge closed(A,B,u)");
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));
    let w_t = w.of(w.sums.unit(), e.clone(), u);
    let want_typed = Formula::forall(
        pa,
        Formula::imp(
            Formula::mem(tpa.clone(), w.sums.unit()),
            Formula::forall(
                pf,
                Formula::imp(
                    Formula::mem(tpf.clone(), w.sums.fs.of(w.fibre(e, tpa.clone()), w_t.clone())),
                    Formula::mem(w.sup(tpa, tpf), w_t),
                ),
            ),
        ),
    );
    assert_eq!(*typed.concl(), want_typed);
}

/// `⊢ ∀T ∀f. (f ∈ fs(∅,T) → f = ∅)` — the empty function is the only one.
#[test]
fn the_only_function_out_of_nothing_is_empty() {
    let mut env = Env::new();
    let w = build(&mut env);
    let prod_empty = wtype::empty_product(&mut env, &w.sums).expect("empty_product");
    let only = wtype::empty_funspace(&mut env, &w.sums, &prod_empty).expect("empty_funspace");
    assert!(kernel::thm::debug_locally_closed(only.concl()));

    let (t, f) = (env.fresh_var(), env.fresh_var());
    let (tt, tf) = (Term::var(t), Term::var(f));
    let e = w.empty();
    let want = Formula::forall(
        t,
        Formula::forall(
            f,
            Formula::imp(
                Formula::mem(tf.clone(), w.sums.fs.of(e.clone(), tt)),
                Formula::eq(tf, e),
            ),
        ),
    );
    assert_eq!(*only.concl(), want);
}

/// The whole development is one definitional extension: rebuilding it must not
/// be necessary, and a caller-supplied `Sums` is threaded rather than replaced.
#[test]
fn the_development_shares_one_sets_stack() {
    let mut env = Env::new();
    let sums = Sums::new(&mut env).expect("sums");
    let unit = sums.unit();
    let w = Wtype::over(&mut env, sums).expect("W-type over a shared Sums");
    // The unit set built before the W-type is the same term afterwards.
    assert_eq!(unit, w.sums.unit());
}
