//! **`⊢ ⟦T⟧ ∈ U₁` from a `DeclSpec`** — the composition of
//! `derived/src/inductive/` (the general carrier) with `derived/src/cumul/`
//! (the cumulative hierarchy), run end to end at the shapes the checker's three
//! hand-written recognisers currently carry.
//!
//! `derived/tests/cumul.rs`'s `the_general_membership_statement_reproves_the_naturals_in_u1`
//! walks the same route at `derived/src/wnat.rs`'s hand-built `N`. These tests
//! are its analogue **from declaration data**: nothing below mentions a fibre,
//! a tag or a seed by hand.
//!
//! **Non-vacuity is checked at every shape.** A membership theorem about `∅`
//! would satisfy every `∈ U₁` assertion here, so each declaration is also made
//! to exhibit provably distinct elements of the set just placed in `U₁`.

use kernel::{Env, Formula, Term, Thm};

use derived::cumul::{
    nullary_summands_in_u1, tags_in_u1, DeclUniverse, IndChain,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// Translate `spec`, discharge `A ∈ U₁` from its (all nullary) constructors,
/// and land on `⟦T⟧ ∈ U₁`.
fn nullary_decl(env: &mut Env, spec: &DeclSpec) -> (IndChain, Inductive, DeclUniverse) {
    let mut ic = IndChain::new(env).expect("the apparatus and the chain, over one signature");
    let ind = ic.build(env, spec).expect("the translation");
    let summands = nullary_summands_in_u1(env, &ic, &ind).expect("each summand is 1");
    let tags = tags_in_u1(env, &ic, &ind, None, &summands).expect("A ∈ U₁");
    let du = DeclUniverse::over(env, &ic, &ind, None, &tags).expect("⟦T⟧ ∈ U₁");
    (ic, ind, du)
}

/// `inductive Bool | false | true`, from declaration data alone.
///
/// This is what `derived/src/cumul/enums.rs` proves by hand, for a tag set it
/// is handed; here the tag set, the fibre family, the bound and the seed are
/// all produced by `Inductive::build` from `DeclSpec::new(0, [nullary; 2])`.
#[test]
fn bool_from_a_declspec_lands_in_u1() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let (ic, ind, du) = nullary_decl(&mut env, &spec);

    let u1 = ic.chain.u1.set.clone();
    assert!(du.rests_on_nothing(), "every field is a ⊢ with nothing on the left");
    assert_eq!(*du.ty_in_u1.concl(), Formula::mem(ind.carrier.clone(), u1.clone()));
    assert!(closed(du.ty_in_u1.concl()), "⊢ ⟦Bool⟧ ∈ U₁ is closed and unconditional");
    assert_eq!(*du.wty_in_u1.concl(), Formula::mem(ind.wty.clone(), u1));

    // Non-vacuity: two constructors, provably in the carrier and provably
    // different — so the set just placed in `U₁` has at least two elements.
    for c in &ind.ctors {
        assert!(c.hyp.is_none());
        assert_eq!(*c.mem.concl(), Formula::mem(c.term.clone(), ind.carrier.clone()));
    }
    let ne = ind.distinct(&mut env, &ic.mach, 0, 1).expect("false ≠ true");
    assert_eq!(
        *ne.concl(),
        Formula::not(Formula::eq(ind.ctors[0].term.clone(), ind.ctors[1].term.clone()))
    );
}

/// `inductive N | zero | succ : N → N`, from declaration data alone.
///
/// The analogue of `cumul.rs`'s
/// `the_general_membership_statement_reproves_the_naturals_in_u1`, which runs
/// the same `w_in_universe_bnd` at `derived/src/wnat.rs`'s hand-built `N`. The
/// two carriers are **not the same set** — `wnat`'s fibres are the von Neumann
/// numerals `0` and `1`, this one's are `finord(0)` and `finord(1)`, and
/// `finord(1) = 1 + 0` is a set of ordered pairs — so what is reproduced is the
/// statement and its route, not the term.
#[test]
fn the_naturals_from_a_declspec_land_in_u1() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 1)]);
    let (ic, ind, du) = nullary_decl(&mut env, &spec);

    let u1 = ic.chain.u1.set.clone();
    assert!(du.rests_on_nothing());
    assert_eq!(*du.ty_in_u1.concl(), Formula::mem(ind.carrier.clone(), u1));
    assert!(closed(du.ty_in_u1.concl()), "⊢ ⟦N⟧ ∈ U₁ is closed and unconditional");

    // The fibre condition really is the general one, at this file's own seed.
    assert_eq!(
        *du.fin.concl(),
        derived::cumul::fin_bnd(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &du.seed,
            &ind.tags,
            &ind.fibre.fam,
        ),
        "the discharged hypothesis is Fin⁺ at S = A ∪ ⋃T"
    );

    // Non-vacuity: `zero ∈ N`, `succ` maps `N` into `N`, and they are distinct
    // — so the carrier is infinite, not a singleton.
    let zero = &ind.ctors[0];
    assert!(zero.hyp.is_none());
    assert_eq!(*zero.mem.concl(), Formula::mem(zero.term.clone(), ind.carrier.clone()));
    let succ = &ind.ctors[1];
    assert!(succ.hyp.is_some(), "succ needs its predecessor in the carrier");
    assert!(ind.distinct(&mut env, &ic.mach, 0, 1).is_some(), "zero ≠ succ n");
    assert!(succ.inj.is_some(), "succ is injective, so the carrier is infinite");
}

/// `inductive Unit | star` and `inductive Empty` — the two degenerate ends.
///
/// `Empty` has no constructors at all, so the tag set is `Sum_0()`, the fibre
/// codomain is `∅` and the elimination over it is vacuous; the route still
/// closes, which is the check that nothing below assumes a constructor exists.
#[test]
fn the_degenerate_ends_land_in_u1() {
    for ctors in [vec![CtorSpec::nullary()], vec![]] {
        let mut env = Env::new();
        let spec = DeclSpec::new(0, ctors);
        let (ic, ind, du) = nullary_decl(&mut env, &spec);
        assert!(du.rests_on_nothing());
        assert_eq!(
            *du.ty_in_u1.concl(),
            Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone())
        );
        assert!(closed(du.ty_in_u1.concl()));
    }
}

/// **Three** nullary constructors — beyond what `derived/src/enums.rs`, and
/// hence the checker's `enum_in_u1` recogniser, can express at all.
#[test]
fn a_three_constructor_enumeration_lands_in_u1() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(); 3]);
    let (ic, ind, du) = nullary_decl(&mut env, &spec);

    assert!(du.rests_on_nothing());
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone())
    );
    // Three provably distinct elements.
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        assert!(ind.distinct(&mut env, &ic.mach, i, j).is_some());
    }
}

/// **Two** recursive arguments in one constructor — the fibre is `finord(2)`,
/// which is neither `∅` nor a von Neumann numeral, so this is the shape that
/// forced `Fin⁺` in the first place.
#[test]
fn a_binary_tree_lands_in_u1() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 2)]);
    let (ic, ind, du) = nullary_decl(&mut env, &spec);

    assert!(du.rests_on_nothing());
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone())
    );
    assert_eq!(ind.fibre.counts, vec![0, 2]);
    assert!(ind.distinct(&mut env, &ic.mach, 0, 1).is_some());
}

/// `inductive List (α) | nil | cons : α → List α → List α`, from declaration
/// data alone — and **under the antecedent `α ∈ U₁`**, which is not an artefact
/// of the route: a `List` over a parameter that is not itself small is no
/// member of any universe.
///
/// This is the shape `derived/src/cumul` never reached by hand: its closing
/// note records `crate::wlist` as "not instantiated". Everything below is the
/// same code the two closed shapes above run, plus
/// `cumul::unary_summand_in_u1` for `cons`'s one-argument `Σ`-telescope.
#[test]
fn list_lands_in_u1_under_an_assumption_about_its_parameter() {
    let mut env = Env::new();
    let mut ic = IndChain::new(&mut env).expect("IndChain");
    let pv = env.fresh_var();
    let (id, id_ax) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = ic.build(&mut env, &spec).expect("List");

    let alpha = Term::var(ind.params[0]);
    let u1 = ic.chain.u1.set.clone();
    let h = Formula::mem(alpha.clone(), u1.clone());

    // `⊢ α ∈ U₁ → β₀(α) ∈ U₁`, i.e. the assumption moved onto the *symbol*
    // application the telescope's `Σ` is over. One Leibniz step.
    let id_at = derived::inst_all(&id_ax, std::slice::from_ref(&alpha)).expect("β₀(α) = α");
    let hole = env.fresh_var();
    let arg = derived::syl(
        &derived::imp_refl(h.clone()),
        &Thm::mp(
            &Thm::eq_leibniz(
                alpha.clone(),
                Term::apply(id, vec![alpha.clone()]),
                hole,
                Formula::mem(Term::var(hole), u1.clone()),
            ),
            &derived::eq_symm(&mut env, &id_at).expect("symm"),
        )
        .expect("mp"),
    )
    .expect("syl");

    let nil = derived::cumul::nullary_summand_in_u1(&mut env, &ic, &ind, 0).expect("A₀ = 1");
    let cons =
        derived::cumul::unary_summand_in_u1(&mut env, &ic, &ind, 1, Some(&h), &arg).expect("A₁");
    let tags = tags_in_u1(&mut env, &ic, &ind, Some(&h), &[derived::a1i(&nil, h.clone()), cons])
        .expect("A ∈ U₁ under α ∈ U₁");
    let du = DeclUniverse::over(&mut env, &ic, &ind, Some(&h), &tags).expect("⟦List α⟧ ∈ U₁");

    assert!(du.rests_on_nothing(), "the antecedent is in the conclusion, not in a Γ");
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::forall(
            ind.params[0],
            Formula::imp(h.clone(), Formula::mem(ind.carrier.clone(), u1.clone()))
        ),
        "⊢ ∀α. (α ∈ U₁ → ⟦List α⟧ ∈ U₁)"
    );
    assert!(closed(du.ty_in_u1.concl()), "and it is closed once α is generalised");

    // The two obligations that stay unconditional even for a parameterised
    // declaration: the fibre condition and the bound-side seed membership.
    assert_eq!(
        *du.fin.concl(),
        derived::cumul::fin_bnd(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &du.seed,
            &ind.tags,
            &ind.fibre.fam,
        ),
        "Fin⁺ is discharged outright, with no assumption about α"
    );
    assert_eq!(
        *du.seed_in_bound.concl(),
        Formula::mem(du.seed.clone(), ind.bound.clone()),
        "the bound-side seed membership costs the parameter nothing"
    );

    // Non-vacuity: `nil` and `cons` are distinct, and `cons` is injective in
    // both its head and its tail, so the carrier sees `α`'s elements.
    assert!(ind.distinct(&mut env, &ic.mach, 0, 1).is_some());
    assert!(ind.ctors[1].inj.is_some());
}

/// The guards: a theorem about **another** apparatus, and a hypothetical one,
/// are both refused rather than composed.
#[test]
fn the_composition_refuses_a_foreign_or_hypothetical_tag_membership() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let mut ic = IndChain::new(&mut env).expect("IndChain");
    let ind = ic.build(&mut env, &spec).expect("Bool");
    let summands = nullary_summands_in_u1(&mut env, &ic, &ind).expect("summands");
    let tags = tags_in_u1(&mut env, &ic, &ind, None, &summands).expect("A ∈ U₁");

    // A `Γ ⊢ A ∈ U₁` has the conclusion the real theorem has.
    let hypothetical = Thm::assume(tags.concl().clone());
    assert!(hypothetical.concl() == tags.concl() && !hypothetical.hyps().is_empty());
    assert!(DeclUniverse::over(&mut env, &ic, &ind, None, &hypothetical).is_none());

    // A second apparatus answers every internal step out of *its* symbols.
    let mut other = IndChain::new(&mut env).expect("a second IndChain");
    let other_ind = other.build(&mut env, &spec).expect("a second Bool");
    assert!(!other_ind.is_over(&ic.mach));
    assert!(DeclUniverse::over(&mut env, &ic, &other_ind, None, &tags).is_none());

    // And the tag membership must be about *this* declaration's tag set: the
    // second apparatus's `A ∈ U₁` is a true theorem about a different `Sum_2`.
    let other_summands = nullary_summands_in_u1(&mut env, &other, &other_ind).expect("summands");
    let other_tags =
        tags_in_u1(&mut env, &other, &other_ind, None, &other_summands).expect("A′ ∈ U₁");
    assert_ne!(other_tags.concl(), tags.concl(), "two apparatus, two tag sets");
    assert!(DeclUniverse::over(&mut env, &ic, &ind, None, &other_tags).is_none());
}
