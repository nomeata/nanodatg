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

use derived::cumul::{nullary_summands_in_u1, tags_in_u1, DeclUniverse, IndChain};
use derived::bound::Bound;
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};
use derived::tower::{Cumul, Tower};
use derived::wtype::Wtype;

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// Translate `spec`, discharge `A ∈ U₁` from its (all nullary) constructors,
/// and land on `⟦T⟧ ∈ U₁`.
fn nullary_decl(env: &mut Env, spec: &DeclSpec) -> (IndChain, Machine, Inductive, DeclUniverse) {
    let (ic, mut mach) =
        IndChain::new(env).expect("the chain and the apparatus, over one signature");
    let ind = Inductive::build(env, &mut mach, spec).expect("the translation");
    let summands = nullary_summands_in_u1(env, &ic, &mach, &ind).expect("each summand is 1");
    let tags = tags_in_u1(env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");
    let du = DeclUniverse::over(env, &ic, &mach, &ind, None, &tags).expect("⟦T⟧ ∈ U₁");
    (ic, mach, ind, du)
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
    let (ic, mach, ind, du) = nullary_decl(&mut env, &spec);

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
    let ne = ind.distinct(&mut env, &mach, 0, 1).expect("false ≠ true");
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
    let (ic, mach, ind, du) = nullary_decl(&mut env, &spec);

    let u1 = ic.chain.u1.set.clone();
    assert!(du.rests_on_nothing());
    assert_eq!(*du.ty_in_u1.concl(), Formula::mem(ind.carrier.clone(), u1));
    assert!(closed(du.ty_in_u1.concl()), "⊢ ⟦N⟧ ∈ U₁ is closed and unconditional");

    // The fibre condition really is the one the path route spends, at this
    // file's own seed — `Fin⁺` with the `bnd` conjunct gone.
    assert_eq!(
        *du.fin.concl(),
        derived::cumul::fin_sub(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &du.seed,
            &ind.tags,
            &ind.fibre.fam,
        ),
        "the discharged hypothesis is `A ⊆ S ∧ ∀a ∈ A. B(a) ⊆ S` at S = A ∪ ⋃T"
    );

    // Non-vacuity: `zero ∈ N`, `succ` maps `N` into `N`, and they are distinct
    // — so the carrier is infinite, not a singleton.
    let zero = &ind.ctors[0];
    assert!(zero.hyp.is_none());
    assert_eq!(*zero.mem.concl(), Formula::mem(zero.term.clone(), ind.carrier.clone()));
    let succ = &ind.ctors[1];
    assert!(succ.hyp.is_some(), "succ needs its predecessor in the carrier");
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some(), "zero ≠ succ n");
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
        let (ic, _mach, ind, du) = nullary_decl(&mut env, &spec);
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
    let (ic, mach, ind, du) = nullary_decl(&mut env, &spec);

    assert!(du.rests_on_nothing());
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone())
    );
    // Three provably distinct elements.
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        assert!(ind.distinct(&mut env, &mach, i, j).is_some());
    }
}

/// **Two** recursive arguments in one constructor — the fibre is `finord(2)`,
/// which is neither `∅` nor a von Neumann numeral. This is the shape that
/// forced `Fin⁺` in the first place, back when the tower was the catcher; the
/// path route needs only `finord(2) ⊆ S`, which is what it now checks.
#[test]
fn a_binary_tree_lands_in_u1() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 2)]);
    let (ic, mach, ind, du) = nullary_decl(&mut env, &spec);

    assert!(du.rests_on_nothing());
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone())
    );
    // `Fibre` no longer holds the counts — it takes *values* — so the
    // declaration's shape is read off the values it was given.
    assert_eq!(
        ind.fibre.values,
        vec![
            mach.syms.finord(&mach.wt.sums, 0).expect("finord(0)"),
            mach.syms.finord(&mach.wt.sums, 2).expect("finord(2)"),
        ]
    );
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
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
    let (ic, mut mach) = IndChain::new(&mut env).expect("IndChain");
    let pv = env.fresh_var();
    let (id, id_ax) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("List");

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

    let nil =
        derived::cumul::nullary_summand_in_u1(&mut env, &ic, &mach, &ind, 0).expect("A₀ = 1");
    let cons = derived::cumul::unary_summand_in_u1(&mut env, &ic, &mach, &ind, 1, Some(&h), &arg)
        .expect("A₁");
    let tags =
        tags_in_u1(&mut env, &ic, &mach, &ind, Some(&h), &[derived::a1i(&nil, h.clone()), cons])
            .expect("A ∈ U₁ under α ∈ U₁");
    let du =
        DeclUniverse::over(&mut env, &ic, &mach, &ind, Some(&h), &tags).expect("⟦List α⟧ ∈ U₁");

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
        derived::cumul::fin_sub(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &du.seed,
            &ind.tags,
            &ind.fibre.fam,
        ),
        "the fibre condition is discharged outright, with no assumption about α"
    );
    assert_eq!(
        *du.seed_in_bound.concl(),
        Formula::mem(du.seed.clone(), ind.bound.clone()),
        "the bound-side seed membership costs the parameter nothing"
    );

    // Non-vacuity: `nil` and `cons` are distinct, and `cons` is injective in
    // both its head and its tail, so the carrier sees `α`'s elements.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
    assert!(ind.ctors[1].inj.is_some());
}

/// The guards: a theorem about **another** apparatus, and a hypothetical one,
/// are both refused rather than composed.
#[test]
fn the_composition_refuses_a_foreign_or_hypothetical_tag_membership() {
    let mut env = Env::new();
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let (ic, mut mach) = IndChain::new(&mut env).expect("IndChain");
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("Bool");
    let summands = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("summands");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");

    // A `Γ ⊢ A ∈ U₁` has the conclusion the real theorem has.
    let hypothetical = Thm::assume(tags.concl().clone());
    assert!(hypothetical.concl() == tags.concl() && !hypothetical.hyps().is_empty());
    assert!(DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &hypothetical).is_none());

    // A second apparatus answers every internal step out of *its* symbols.
    let (other, mut other_mach) = IndChain::new(&mut env).expect("a second IndChain");
    let other_ind = Inductive::build(&mut env, &mut other_mach, &spec).expect("a second Bool");
    assert!(!other_ind.is_over(&mach));
    assert!(!other.is_over(&mach));
    assert!(DeclUniverse::over(&mut env, &ic, &mach, &other_ind, None, &tags).is_none());

    // And the tag membership must be about *this* declaration's tag set: the
    // second apparatus's `A ∈ U₁` is a true theorem about a different `Sum_2`.
    let other_summands =
        nullary_summands_in_u1(&mut env, &other, &other_mach, &other_ind).expect("summands");
    let other_tags = tags_in_u1(&mut env, &other, &other_mach, &other_ind, None, &other_summands)
        .expect("A′ ∈ U₁");
    assert_ne!(other_tags.concl(), tags.concl(), "two apparatus, two tag sets");
    assert!(DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &other_tags).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// `⟦T⟧ ∈ Uₙ` — `DeclUniverse::over_at`, at rungs above `Type 0`.
//
// `over` is `over_at` at `chain.u1`; these tests run the same declarations one
// and two rungs higher and check that nothing about the route changes but the
// rung, that the antecedent list stays exactly `A ∈ Uₙ`, and that a rung from
// another tower is refused.
// ─────────────────────────────────────────────────────────────────────────────

/// The chain, the apparatus and the **tower they were built over** — which
/// `IndChain::new` does not hand back, and which is where a rung above `U₁`
/// comes from.
fn over_a_tower(env: &mut Env) -> (Tower, Cumul, IndChain, Machine) {
    let tower = Tower::new(env).expect("the tower");
    let wt = Wtype::over(env, tower.sums.clone()).expect("the W-type");
    let bound =
        Bound::over(env, &wt, tower.space.lu, tower.space.lu_ax.clone()).expect("the bound");
    let ic = IndChain::over(env, &tower, &wt, &bound).expect("the chain");
    let cumul = Cumul::new(env, &tower, 3).expect("the cumulativity table");
    let mach = Machine::over(env, wt, bound).expect("the apparatus");
    assert!(ic.is_over(&mach));
    (tower, cumul, ic, mach)
}

/// **The deliverable.** `inductive Bool` lands in `U₁`, `U₂` **and** `U₃`, from
/// one tag membership raised by `Cumul::raise`, with `over_at` doing the same
/// work at each.
///
/// Three rungs, not two: two cannot distinguish "the rung is threaded" from
/// "the rung is `tower.at(1)` unless asked otherwise", and the tower's rungs
/// are provably distinct (`Cumul::strict`), so the three conclusions are three
/// different statements rather than one restated.
#[test]
fn a_closed_declaration_lands_at_every_rung_of_the_tower() {
    let mut env = Env::new();
    let (tower, cumul, ic, mut mach) = over_a_tower(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("Bool");
    let summands = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("each summand is 1");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");

    // The three rungs are three different sets, and the tower does not collapse
    // between any two of them — so what follows is not one theorem thrice.
    for n in 1..3 {
        assert_ne!(tower.u(n), tower.u(n + 1));
        assert!(cumul.strict(n).is_some(), "¬(U₍ₙ₊₁₎ ⊆ Uₙ)");
    }

    for n in 1..=3 {
        let rung = tower.at(n).expect("a rung of this tower");
        // The one antecedent, moved up a rung and nothing else.
        let tags_n = cumul.raise(1, n, &tags).expect("A ∈ Uₙ");
        assert_eq!(*tags_n.concl(), Formula::mem(ind.tags.clone(), tower.u(n)));

        let du = DeclUniverse::over_at(&mut env, &ic, &mach, &ind, None, &rung, &tags_n)
            .expect("⟦Bool⟧ ∈ Uₙ");
        assert!(du.rests_on_nothing());
        assert_eq!(du.universe, tower.u(n), "the rung it was asked for");
        assert_eq!(
            *du.ty_in_u1.concl(),
            Formula::mem(ind.carrier.clone(), tower.u(n)),
            "⊢ ⟦Bool⟧ ∈ Uₙ"
        );
        assert!(closed(du.ty_in_u1.concl()));

        // The two obligations that are independent of the rung: they are the
        // *same theorems* at every `n`, not merely the same shape.
        let at_one = DeclUniverse::over_at(
            &mut env,
            &ic,
            &mach,
            &ind,
            None,
            &tower.at(1).expect("rung 1"),
            &tags,
        )
        .expect("⟦Bool⟧ ∈ U₁");
        assert_eq!(du.fin.concl(), at_one.fin.concl(), "the fibre condition does not mention the rung");
        assert_eq!(
            du.seed_in_bound.concl(),
            at_one.seed_in_bound.concl(),
            "nor does the bound-side seed membership"
        );
        assert_eq!(du.seed, at_one.seed, "one seed, S = A ∪ ⋃T");
    }

    // And `over` really is `over_at` at rung 1 — same statement, one line.
    let plain = DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &tags).expect("⟦Bool⟧ ∈ U₁");
    let explicit =
        DeclUniverse::over_at(&mut env, &ic, &mach, &ind, None, &tower.at(1).unwrap(), &tags)
            .expect("⟦Bool⟧ ∈ U₁");
    assert_eq!(plain.ty_in_u1.concl(), explicit.ty_in_u1.concl());
    assert_eq!(plain.universe, ic.chain.u1.set);

    // Non-vacuity: the set placed in `U₃` has two provably distinct elements.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
}

/// `List α` at `U₂`: the antecedent list at `Type n` is still **exactly one
/// item**, `α ∈ U₂`, and it is the `U₁` one raised by a single syllogism.
///
/// The tag membership is `⊢ H → A ∈ U₁` with `H` in the *conclusion*, so
/// `Cumul::raise` — a `⊢`-to-`⊢` rule — does not apply and `Cumul::lift` is
/// used directly. That one line is the whole cost of moving a parameterised
/// declaration up the tower.
#[test]
fn a_parameterised_declaration_lands_a_rung_higher_under_the_same_one_antecedent() {
    let mut env = Env::new();
    let (tower, cumul, ic, mut mach) = over_a_tower(&mut env);
    let pv = env.fresh_var();
    let (id, id_ax) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("List");

    let alpha = Term::var(ind.params[0]);
    let u1 = ic.chain.u1.set.clone();
    let h = Formula::mem(alpha.clone(), u1.clone());

    // `⊢ α ∈ U₁ → β₀(α) ∈ U₁`, exactly as the `U₁` test builds it.
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
    let nil = derived::cumul::nullary_summand_in_u1(&mut env, &ic, &mach, &ind, 0).expect("A₀");
    let cons = derived::cumul::unary_summand_in_u1(&mut env, &ic, &mach, &ind, 1, Some(&h), &arg)
        .expect("A₁");
    let tags =
        tags_in_u1(&mut env, &ic, &mach, &ind, Some(&h), &[derived::a1i(&nil, h.clone()), cons])
            .expect("H → A ∈ U₁");

    // **The one line.** `⊢ H → A ∈ U₁` to `⊢ H → A ∈ U₂`.
    let tags_2 = derived::syl(
        &tags,
        &derived::inst_all(cumul.lift(1, 2).expect("U₁ ⊆ U₂"), std::slice::from_ref(&ind.tags))
            .expect("at A"),
    )
    .expect("syl");
    assert_eq!(
        *tags_2.concl(),
        Formula::imp(h.clone(), Formula::mem(ind.tags.clone(), tower.u(2))),
        "the antecedent is still α ∈ U₁, and only the right-hand side moved"
    );

    let du = DeclUniverse::over_at(
        &mut env,
        &ic,
        &mach,
        &ind,
        Some(&h),
        &tower.at(2).expect("rung 2"),
        &tags_2,
    )
    .expect("⟦List α⟧ ∈ U₂");
    assert!(du.rests_on_nothing(), "the antecedent is in the conclusion, not in a Γ");
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::forall(
            ind.params[0],
            Formula::imp(h.clone(), Formula::mem(ind.carrier.clone(), tower.u(2)))
        ),
        "⊢ ∀α. (α ∈ U₁ → ⟦List α⟧ ∈ U₂)"
    );
    assert!(closed(du.ty_in_u1.concl()));
    assert_eq!(du.universe, tower.u(2));

    // The two rung-free obligations stay unconditional at the higher rung.
    assert_eq!(
        *du.seed_in_bound.concl(),
        Formula::mem(du.seed.clone(), ind.bound.clone()),
        "the bound-side seed membership costs the parameter, and the rung, nothing"
    );
    assert!(du.fin.hyps().is_empty());

    // Non-vacuity: `nil ≠ cons`, and `cons` is injective.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
    assert!(ind.ctors[1].inj.is_some());
}

/// A `Rung` from a **second** tower in the same `Env` is refused, even though
/// it satisfies every closure clause a rung has to satisfy.
///
/// The three checks that catch it: `Uₙ` must be *this* chain's `U(·)` of the
/// rung's own seed, and the rung's `⊢ ∅ ∈ Uₙ` and `⊢ ω ∈ Uₙ` must be about
/// this chain's `∅` and this chain's `ω`. Without them the composition would
/// return a true theorem about a set that is not this declaration's carrier.
#[test]
fn a_rung_from_another_tower_is_refused() {
    let mut env = Env::new();
    let (tower, cumul, ic, mut mach) = over_a_tower(&mut env);
    let (other_tower, other_cumul, _other_ic, _other_mach) = over_a_tower(&mut env);
    assert_ne!(tower.u(2), other_tower.u(2), "two towers, two U₂s");

    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("Bool");
    let summands = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("summands");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");
    let tags_2 = cumul.raise(1, 2, &tags).expect("A ∈ U₂");

    // The right rung, the right tag membership: this is the positive control.
    assert!(DeclUniverse::over_at(
        &mut env,
        &ic,
        &mach,
        &ind,
        None,
        &tower.at(2).unwrap(),
        &tags_2
    )
    .is_some());

    // The other tower's rung 2 is a genuine universe with every clause; it is
    // simply not this chain's.
    assert!(
        DeclUniverse::over_at(
            &mut env,
            &ic,
            &mach,
            &ind,
            None,
            &other_tower.at(2).unwrap(),
            &tags_2
        )
        .is_none(),
        "a rung from a second tower is refused"
    );

    // And a tag membership raised in the *other* tower is refused at this one.
    assert!(other_cumul.raise(1, 2, &tags).is_none(), "A ∈ U₁ is not about that tower's U₁");

    // The hypothesis leg of the three checks is live, not decorative: a `Rung`
    // whose theorems hold only under a `Γ` has the conclusions the real ones
    // have, and would ride into a result labelled `⊢ ⟦Bool⟧ ∈ U₂`.
    for doctored in [0usize, 1, 2] {
        let mut lv = tower.at(2).unwrap();
        let field = match doctored {
            0 => &mut lv.empty_mem,
            1 => &mut lv.omega_mem,
            _ => &mut lv.pairing,
        };
        *field = Thm::assume(field.concl().clone());
        assert!(
            DeclUniverse::over_at(&mut env, &ic, &mach, &ind, None, &lv, &tags_2).is_none(),
            "a hypothetical rung theorem is refused (field {doctored})"
        );
    }
}
