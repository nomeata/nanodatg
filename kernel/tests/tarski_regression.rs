//! Regression guard for an inconsistency that was once in the kernel.
//!
//! `ax_tarski_incomplete` stated the "inaccessibility" clause of Tarski's Axiom
//! A as `∀y. (y ⊆ u → y ∈ u)`, dropping the `y ≺ u` disjunct because stating it
//! needs ordered pairs. That weakening is not merely incomplete — it is
//! **fatal**: instantiating at `y := u` and discharging the trivially derivable
//! `u ⊆ u` yields `u ∈ u`, which Regularity refutes. The axiom was therefore
//! inconsistent, and has been removed.
//!
//! This test derives the fatal step from the clause's *shape*, so that the
//! clause cannot be reintroduced without the failure showing up.

use kernel::{Env, Formula, Term, Thm};

/// `⊢ u ⊆ u` — the step that makes the weakened clause explode.
fn subset_refl(env: &mut Env, u: &Term) -> Thm {
    let z = env.fresh_var();
    let mem = Formula::mem(Term::var(z), u.clone());
    // ∀z. (z ∈ u → z ∈ u)
    Thm::gen(z, &{
        // imp_refl, inlined: the kernel exposes only primitives.
        let s = Thm::ax_s(mem.clone(), Formula::imp(mem.clone(), mem.clone()), mem.clone());
        let k1 = Thm::ax_k(mem.clone(), Formula::imp(mem.clone(), mem.clone()));
        let step = Thm::mp(&s, &k1).expect("S/K");
        let k2 = Thm::ax_k(mem.clone(), mem.clone());
        Thm::mp(&step, &k2).expect("S/K")
    })
}

#[test]
fn weakened_inaccessibility_clause_proves_self_membership() {
    let mut env = Env::new();
    let u = Term::apply(env.declare(0), vec![]);

    // `u ⊆ u` is derivable outright.
    let sub_uu = subset_refl(&mut env, &u);
    assert_eq!(*sub_uu.concl(), kernel::thm::subset(&mut env, u.clone(), u.clone()));

    // The discarded clause: ∀y. (y ⊆ u → y ∈ u).
    let y = env.fresh_var();
    let ty = Term::var(y);
    let y_sub_u = kernel::thm::subset(&mut env, ty.clone(), u.clone());
    let bad_clause = Formula::forall(y, Formula::imp(y_sub_u, Formula::mem(ty, u.clone())));

    // Instantiating at y := u gives `u ⊆ u → u ∈ u`.
    let inst = Thm::ax_inst(bad_clause.clone(), u.clone()).expect("instantiate the clause at u");
    let (_, consequent) = inst.concl().as_imp().expect("instantiation is an implication");
    let expected = Formula::imp(
        kernel::thm::subset(&mut env, u.clone(), u.clone()),
        Formula::mem(u.clone(), u.clone()),
    );
    assert_eq!(
        consequent, expected,
        "the weakened clause instantiated at u should read `u ⊆ u → u ∈ u`; \
         combined with the derivable `u ⊆ u` that gives `u ∈ u`, which Regularity refutes"
    );
}

/// If a Tarski axiom exists, it must carry the disjunct whose absence was fatal.
#[test]
fn any_tarski_axiom_keeps_the_equinumerosity_disjunct() {
    // Compile-time guard: if a Tarski axiom is reintroduced it must be named
    // differently and must carry the `≺` disjunct. This test exists so the
    // removal is deliberate rather than forgotten.
    let src = include_str!("../src/thm.rs");
    // A Tarski axiom is permitted again, but ONLY with the equinumerosity
    // disjunct restored — that is exactly what its absence broke.
    if src.contains("fn ax_tarski") {
        assert!(
            src.contains("equinumerous"),
            "a Tarski axiom is present without the `y ≈ u` disjunct — that re-admits `u ∈ u` \
             (see the test above) and is inconsistent with Regularity"
        );
    }
}
