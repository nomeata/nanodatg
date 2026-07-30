//! Separation, derived from Replacement — as far as the axioms allow.

use kernel::{Env, Formula, Term, Thm};

/// A sample condition with designated free variable `x`: `x ∈ c`.
fn sample(env: &mut Env) -> (kernel::FreeVar, Formula, Term) {
    let x = env.fresh_var();
    let c = env.declare(0);
    let tc = Term::apply(c, vec![]);
    let phi = Formula::mem(Term::var(x), tc.clone());
    (x, phi, tc)
}

/// The choice relation `(φ(x) ∧ y = x) ∨ (¬φ(x) ∧ y = u)` is a genuine
/// function: `∃!y` holds outright, in exactly the shape Replacement's premise
/// demands.
#[test]
fn choice_relation_is_functional() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);
    let y = env.fresh_var();
    let u = env.fresh_var();
    let tu = Term::var(u);

    let thm = derived::separation::choice_relation_unique(&mut env, x, &phi, y, &tu)
        .expect("∃! for the choice relation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let psi = derived::separation::choice_relation(x, &phi, y, &tu);
    let expected = kernel::thm::exists_unique(&mut env, y, &psi);
    assert_eq!(*thm.concl(), expected, "not the ∃! shape the kernel builds");
}

/// The relation really is the disjunction it claims to be.
#[test]
fn choice_relation_shape() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);
    let y = env.fresh_var();
    let tu = Term::apply(env.declare(0), vec![]);

    let psi = derived::separation::choice_relation(x, &phi, y, &tu);
    let expected = Formula::or(
        Formula::and(phi.clone(), Formula::eq(Term::var(y), Term::var(x))),
        Formula::and(Formula::not(phi), Formula::eq(Term::var(y), tu)),
    );
    assert_eq!(psi, expected);
}

/// The propositional helpers this module adds.
#[test]
fn disjunction_introduction() {
    let mut env = Env::new();
    let (_, phi, _) = sample(&mut env);
    let psi = Formula::false_();

    let left = derived::separation::or_intro_left(phi.clone(), psi.clone());
    assert_eq!(*left.concl(), Formula::imp(phi.clone(), Formula::or(phi.clone(), psi.clone())));

    let right = derived::separation::or_intro_right(phi.clone(), psi.clone());
    assert_eq!(*right.concl(), Formula::imp(psi.clone(), Formula::or(phi, psi)));
}

/// Syllogism and ex falso under a fixed hypothesis.
#[test]
fn hypothesis_helpers() {
    let mut env = Env::new();
    let (_, a, _) = sample(&mut env);
    let h = Formula::not(Formula::false_());

    // ⊢ H → (a → a) and ⊢ H → (a → a) compose to ⊢ H → (a → a).
    let refl = derived::a1i(&derived::imp_refl(a.clone()), h.clone());
    let got = derived::separation::hyp_syl(&refl, &refl).expect("hyp_syl");
    assert_eq!(*got.concl(), Formula::imp(h.clone(), Formula::imp(a.clone(), a.clone())));

    // ⊢ H → ¬⊥ turns into ⊢ H → (⊥ → a).
    let h_not = derived::a1i(&derived::imp_refl(Formula::false_()), h.clone());
    let got = derived::separation::hyp_ex_falso(&h_not, a.clone()).expect("hyp_ex_falso");
    assert_eq!(*got.concl(), Formula::imp(h, Formula::imp(Formula::false_(), a)));
}

/// Sanity: the kernel's Replacement premise for this relation is exactly what
/// [`choice_relation_unique`] proves, so the two compose by modus ponens.
#[test]
fn premise_discharges_replacement() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);
    let y = env.fresh_var();
    let u = env.fresh_var();
    let a = env.fresh_var();
    let (tu, ta, tx) = (Term::var(u), Term::var(a), Term::var(x));

    let psi = derived::separation::choice_relation(x, &phi, y, &tu);
    let uniq = derived::separation::choice_relation_unique(&mut env, x, &phi, y, &tu).expect("∃!");

    let repl = Thm::ax_replacement(&mut env, x, y, psi).expect("distinct variables");
    let repl = derived::inst_all(&repl, std::slice::from_ref(&ta)).expect("instantiate a");
    let premise = Thm::gen(x, &derived::a1i(&uniq, Formula::mem(tx, ta)));
    let image = Thm::mp(&repl, &premise).expect("the premise discharges Replacement");
    assert!(kernel::thm::debug_locally_closed(image.concl()));
}

/// The Replacement image contains every separated element.
#[test]
fn image_contains_the_separated_elements() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);
    let (y, a, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let tu = Term::var(u);

    let thm = derived::separation::image_backward(x, &phi, y, a, &tu).expect("image_backward");
    let (lhs, _) = thm.concl().as_imp().expect("an implication");
    let expected = Formula::and(
        Formula::mem(Term::var(y), Term::var(a)),
        phi.subst(x, &Term::var(y)),
    );
    assert_eq!(lhs, expected, "image_backward's antecedent is not `y ∈ a ∧ φ(y)`");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
}

/// And, when the default value is itself separated, nothing else.
#[test]
fn image_contains_nothing_else() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);
    let (y, a, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, ta, tu) = (Term::var(y), Term::var(a), Term::var(u));

    let thm = derived::separation::image_forward(&mut env, x, &phi, y, a, u).expect("image_forward");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let psi = derived::separation::choice_relation(x, &phi, y, &tu);
    let expected = Formula::imp(
        Formula::and(Formula::mem(tu, ta.clone()), phi.subst(x, &Term::var(u))),
        Formula::imp(
            Formula::exists(x, Formula::and(Formula::mem(Term::var(x), ta.clone()), psi)),
            Formula::and(Formula::mem(ty.clone(), ta), phi.subst(x, &ty)),
        ),
    );
    assert_eq!(*thm.concl(), expected, "image_forward has the wrong shape");
}

/// Separation, in the case where something in `a` satisfies the condition.
/// This needs Replacement and nothing else — in particular no empty set.
#[test]
fn separation_when_the_condition_holds_somewhere() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);

    let thm = derived::separation::separation_nonvacuous(&mut env, x, &phi)
        .expect("non-vacuous separation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // ⊢ ∀a. (∃u. (u ∈ a ∧ φ(u))) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))
    let c = Term::apply(env.declare(0), vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&c)).expect("instantiate a");
    let (u, z, s) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tz, ts) = (Term::var(u), Term::var(z), Term::var(s));

    let hyp = Formula::exists(
        u,
        Formula::and(Formula::mem(tu.clone(), c.clone()), phi.subst(x, &tu)),
    );
    let goal = Formula::exists(
        s,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), ts),
                Formula::and(Formula::mem(tz.clone(), c), phi.subst(x, &tz)),
            ),
        ),
    );
    assert_eq!(*inst.concl(), Formula::imp(hyp, goal), "separation_nonvacuous has the wrong shape");
}

/// The full Separation scheme, with its one missing ingredient — an empty set —
/// carried as an explicit antecedent rather than assumed.
#[test]
fn separation_relative_to_an_empty_set() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);

    let thm = derived::separation::separation_existence(&mut env, x, &phi).expect("separation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // ⊢ ∀a ∀e. (∀z. ¬(z ∈ e)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))
    let (c, e) = (Term::apply(env.declare(0), vec![]), Term::apply(env.declare(0), vec![]));
    let inst = derived::inst_all(&thm, &[c.clone(), e.clone()]).expect("instantiate a and e");

    let (z, s) = (env.fresh_var(), env.fresh_var());
    let (tz, ts) = (Term::var(z), Term::var(s));
    let empty = Formula::forall(z, Formula::not(Formula::mem(tz.clone(), e)));
    let goal = Formula::exists(
        s,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), ts),
                Formula::and(Formula::mem(tz.clone(), c), phi.subst(x, &tz)),
            ),
        ),
    );
    assert_eq!(*inst.concl(), Formula::imp(empty, goal), "separation_existence has the wrong shape");
}

/// Separation at a refutable condition yields an empty set: the two are
/// equivalent, so the missing ingredient cannot be recovered from Separation.
#[test]
fn separation_would_give_an_empty_set() {
    let mut env = Env::new();
    let sep = env.declare(1);
    let thm = derived::separation::empty_from_separation(&mut env, sep).expect("empty_from_separation");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let c = Term::apply(env.declare(0), vec![]);
    let inst = derived::inst_all(&thm, std::slice::from_ref(&c)).expect("instantiate a");
    let (a, z) = (env.fresh_var(), env.fresh_var());
    let (ta, tz) = (Term::var(a), Term::var(z));

    let ax = Formula::forall(
        a,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::apply(sep, vec![ta.clone()])),
                Formula::and(
                    Formula::mem(tz.clone(), ta),
                    Formula::not(Formula::eq(tz.clone(), tz.clone())),
                ),
            ),
        ),
    );
    let concl = Formula::forall(
        z,
        Formula::not(Formula::mem(tz, Term::apply(sep, vec![c]))),
    );
    assert_eq!(*inst.concl(), Formula::imp(ax, concl), "empty_from_separation has the wrong shape");
}

/// [`separation`] refuses anything that is not a proof of emptiness — the
/// obligation cannot be discharged with an unrelated theorem.
#[test]
fn separation_rejects_a_bogus_empty_set() {
    let mut env = Env::new();
    let (x, phi, _) = sample(&mut env);

    // `∀z. z = z` is a theorem, and is not a proof that anything is empty.
    let z = env.fresh_var();
    let bogus = Thm::gen(z, &Thm::eq_refl(Term::var(z)));
    assert!(derived::separation::separation(&mut env, x, &phi, &bogus).is_none());

    // Neither is a non-universal theorem.
    let bogus2 = Thm::eq_refl(Term::var(z));
    assert!(derived::separation::separation(&mut env, x, &phi, &bogus2).is_none());
}
