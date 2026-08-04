//! **`DeclUniverse::over_at_general`** — the carrier's universe placement when
//! a constructor's fibre value is not `finord(mᵢ)`.
//!
//! `over_at` reads each fibre value twice, through `bnd_finords` and
//! `finords_in_universe`, and both used to be stated at `finord(mᵢ)` alone. A
//! **function-typed** recursive argument — `RTree.node : (Bool → RTree) → RTree`
//! — gives its slot the fibre summand `Σ(z::γ)` rather than `1`
//! (`thesis.txt:1800`), so the value is `Sum_m(Σ(z::γ⃗))` and neither reader
//! could be instantiated.
//!
//! Two things this file measures rather than asserts:
//!
//! * the plain path is **unchanged** — `over_at_general` with the facts
//!   supplied explicitly returns exactly what `over_at` returns;
//! * at an `RTree`-shaped declaration the placement still declines, and
//!   [`the_remaining_obligation_is_named_at_its_own_term`] names the two
//!   theorems a consumer would have to bring and the term each is about. That
//!   is the residue, recorded where it can be re-measured rather than in prose.

use kernel::{Env, Formula, FnSym, FreeVar, Term};

use derived::cumul::{bnd, bnd_unit, nullary_summands_in_u1, tags_in_u1, DeclUniverse, FibreFacts, IndChain};
use derived::inductive::{CtorSpec, DeclSpec, Inductive};

/// A symbol of the given arity whose body is a fixed closed set.
fn konst(env: &mut Env, arity: usize, v: Term) -> FnSym {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    derived::define_abbrev(env, &vars, &v).expect("an abbreviation").0
}

/// **The plain path pays nothing.** Supplying the unit facts by hand produces
/// the same theorem the `None` path produces.
///
/// Two constructors and one of them recursive, so the fibre values are two
/// *different* finite ordinals and a reader that dropped the per-constructor
/// indexing would be caught.
#[test]
fn the_explicit_unit_facts_reproduce_the_plain_placement() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    // `N`: `zero` and `succ : N → N`.
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(Vec::new(), 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration");
    let summands =
        nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("each summand is 1");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");

    let plain = DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &tags).expect("W ∈ U₁");

    // The same, with the two facts about `1` handed in rather than synthesised.
    let s = mach.wt.sums.clone();
    let ub = bnd_unit(&mut env, &ic.chain.r, &ic.chain.st, &s).expect("bnd(1)");
    let um = derived::inst_all(&ic.clo.unit, &[ic.chain.u1.seed.clone()]).expect("1 ∈ U₁");
    let facts = FibreFacts {
        bnd: vec![Vec::new(), vec![ub.clone()]],
        mem: vec![Vec::new(), vec![um.clone()]],
    };
    let explicit = DeclUniverse::over_at_general(
        &mut env,
        &ic,
        &mach,
        &ind,
        None,
        &ic.chain.u1,
        &tags,
        Some(&facts),
    )
    .expect("W ∈ U₁ with the facts supplied");

    assert_eq!(plain.ty_in_u1.concl(), explicit.ty_in_u1.concl());
    assert_eq!(plain.fin.concl(), explicit.fin.concl());
    assert_eq!(plain.target_in_u1.concl(), explicit.target_in_u1.concl());
    assert_eq!(plain.wty_in_u1.concl(), explicit.wty_in_u1.concl());
    assert!(explicit.rests_on_nothing());

    // ── what the reader refuses ─────────────────────────────────────────────
    //
    // One entry per constructor and one per that constructor's slots. The
    // second constructor has one recursive argument, so a bare `zero` shape is
    // not a rearrangement of the right list — it is the wrong list.
    for bad in [
        FibreFacts { bnd: vec![vec![ub.clone()]], mem: vec![vec![um.clone()]] },
        FibreFacts {
            bnd: vec![Vec::new(), Vec::new()],
            mem: vec![Vec::new(), vec![um.clone()]],
        },
        // A `bnd` about `∅` where the summand is `1`.
        FibreFacts {
            bnd: vec![
                Vec::new(),
                vec![derived::cumul::bnd_empty(&mut env, &ic.chain.r, &ic.chain.st)
                    .expect("bnd(∅)")],
            ],
            mem: vec![Vec::new(), vec![um.clone()]],
        },
    ] {
        assert!(
            DeclUniverse::over_at_general(
                &mut env,
                &ic,
                &mach,
                &ind,
                None,
                &ic.chain.u1,
                &tags,
                Some(&bad),
            )
            .is_none(),
            "a fact list that does not fit the declaration is refused"
        );
    }
}

/// **`RTree`.** The placement still declines, and this names exactly what is
/// missing and at which term.
///
/// Three constructors — nullary, plain recursive, function-typed recursive —
/// because a check that ignored `rec_doms` passes on the first two and one that
/// applied a telescope uniformly passes on the last two
/// (`tests/fibre_values.rs` makes the same argument about the values).
#[test]
fn the_remaining_obligation_is_named_at_its_own_term() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let s = mach.wt.sums.clone();
    mach.syms.ensure(&mut env, &s, 4).expect("the sum symbols");
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let bool_sym = konst(&mut env, 0, boolean);

    let spec = DeclSpec::new(
        0,
        vec![
            CtorSpec::nullary(),
            CtorSpec::new(Vec::new(), 1),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]]),
        ],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration");
    let summands =
        nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("each summand is 1");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");

    // The fibre summands, read off the recursive-argument functions — which is
    // where `over_at_general` reads them, so this is the obligation's own term
    // and not a reconstruction of it.
    let fib: Vec<Vec<Term>> =
        (0..3).map(|i| ind.recargs[i].summands.clone()).collect();
    assert_eq!(fib[0], Vec::<Term>::new(), "`leaf` has no recursive argument");
    assert_eq!(fib[1], vec![s.unit()], "a plain recursive argument's summand is `1`");
    assert_eq!(fib[2].len(), 1);
    assert_ne!(fib[2][0], s.unit(), "`node`'s summand is a telescope's type, not `1`");

    let tel = mach.telescope(&mut env, 0, &[bool_sym]).expect("the domain telescope");
    assert_eq!(fib[2][0], tel.ty_of(Vec::new()), "and it is `Σ(z::Bool)` itself");

    // Each value really is the sum of its own summands — the check
    // `over_at_general` makes on the way in.
    for i in 0..3 {
        assert_eq!(mach.syms.sum(&fib[i]).expect("Sum"), ind.fibre.values[i]);
    }
    // …and the third is no finite ordinal.
    for m in 0..=4 {
        assert_ne!(ind.fibre.values[2], mach.syms.finord(&s, m).expect("finord"));
    }

    // **The decline, reproduced.** `None` claims every summand is `1`, and the
    // third constructor's is not.
    assert!(
        DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &tags).is_none(),
        "the plain path is refused rather than mis-applied"
    );

    // **The two theorems a consumer must bring** for the third constructor, at
    // this exact term. `bnd_telescope1` and `unary_telescope_at` produce them
    // from a fact about the *domain*, and
    // `the_placement_goes_through_at_a_function_typed_recursive_argument`
    // composes the whole chain; this test is the statement of the obligation,
    // pinned where it can be re-measured if either producer moves.
    let want_bnd = bnd(&mut env, &ic.chain.r, &ic.chain.st, &fib[2][0]);
    let want_mem = Formula::mem(fib[2][0].clone(), ic.chain.u1.set.clone());
    assert_ne!(want_bnd, bnd(&mut env, &ic.chain.r, &ic.chain.st, &s.unit()));
    assert!(kernel::thm::debug_locally_closed(&want_bnd));
    assert!(kernel::thm::debug_locally_closed(&want_mem));
}

/// **`⊢ bnd(⟦Bool⟧)`** — a declaration with no recursive arguments has a
/// bounded carrier.
///
/// Three constructors rather than two: `bnd(A)` is a fold over the tag
/// summands, and a fold that dropped or duplicated one is invisible at two.
/// The carrier is also shown **inhabited by distinct elements**, so the `bnd`
/// is not a statement about the empty set — `bnd(∅)` is free.
#[test]
fn a_declaration_with_no_recursive_arguments_has_a_bounded_carrier() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::nullary(), CtorSpec::nullary()],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration");
    let inversion = derived::wtype::w_inversion(&mut env, &mach.wt).expect("W3");

    let tags_bnd = derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &ind)
        .expect("bnd(A) at three unit summands");
    assert_eq!(*tags_bnd.concl(), bnd(&mut env, &ic.chain.r, &ic.chain.st, &ind.tags));

    let th = derived::cumul::bnd_carrier(&mut env, &ic, &mach, &ind, &inversion, &tags_bnd)
        .expect("bnd(ind())");
    assert!(th.hyps().is_empty(), "rests on nothing");
    assert_eq!(
        *th.concl(),
        bnd(&mut env, &ic.chain.r, &ic.chain.st, &ind.carrier),
        "the conclusion is about the abbreviation, not about the raw W-type"
    );
    assert_ne!(ind.carrier, ind.wty, "and those are two different terms");

    // Non-vacuity: the bounded set has three provably distinct elements.
    for i in 0..3 {
        assert!(ind.ctors[i].mem.hyps().is_empty());
    }
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        assert!(ind.distinct(&mut env, &mach, i, j).is_some(), "ctor {i} and {j} are distinct");
    }

    // A recursive constructor is refused rather than mis-applied: `N`'s `succ`
    // has a non-empty fibre and the inversion below would say nothing.
    let rec_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(Vec::new(), 1)]);
    let rec_ind = Inductive::build(&mut env, &mut mach, &rec_spec).expect("N");
    assert!(derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &rec_ind).is_none());
    assert!(
        derived::cumul::bnd_carrier(&mut env, &ic, &mach, &rec_ind, &inversion, &tags_bnd)
            .is_none(),
        "a recursive declaration is refused"
    );
}

/// **`⊢ bnd(Σ z:⟦Bool⟧. 1)`** — the fibre telescope, and with it the whole
/// chain `FibreFacts::bnd` sits on, at `RTree.node`'s own summand.
///
/// The telescope is the **fibre** one — the same `Machine::telescope` call
/// `fibre_summands` makes, so the term is `recargs[i].summands[j]` on the nose
/// rather than a look-alike. `unary_summand_at` cannot be pointed here: it
/// reads `ind.telescopes[i]`, the *argument* telescope of constructor `i`,
/// pins its result against `ind.summands[i]`, and requires
/// `ctors[i].args.len() == 1`, which for `node` is `0`.
#[test]
fn the_fibre_telescope_over_a_bounded_domain_is_bounded() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    // `⟦Bool⟧` as a real declaration, so its `bnd` is derived and not assumed.
    let bool_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let boolean = Inductive::build(&mut env, &mut mach, &bool_spec).expect("Bool");
    let inversion = derived::wtype::w_inversion(&mut env, &mach.wt).expect("W3");
    let bool_tags = derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &boolean)
        .expect("bnd(A) for Bool");
    let bool_bnd =
        derived::cumul::bnd_carrier(&mut env, &ic, &mach, &boolean, &inversion, &bool_tags)
            .expect("bnd(⟦Bool⟧)");

    // `RTree.node : (⟦Bool⟧ → RTree) → RTree`, over that carrier's own symbol.
    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![boolean.ty]])],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("RTree");
    let tel = mach.telescope(&mut env, 0, &[boolean.ty]).expect("the fibre telescope");
    assert_eq!(
        ind.recargs[1].summands[0],
        tel.ty_of(Vec::new()),
        "the fibre summand is this telescope's type"
    );

    let th = derived::cumul::bnd_telescope1(&mut env, &ic, &mach, &tel, &[], &bool_bnd)
        .expect("bnd(Σ z:⟦Bool⟧. 1)");
    assert!(th.hyps().is_empty(), "rests on nothing");
    assert_eq!(
        *th.concl(),
        bnd(&mut env, &ic.chain.r, &ic.chain.st, &ind.recargs[1].summands[0]),
        "and it is about the summand `over_at_general` reads"
    );
    assert_ne!(
        *th.concl(),
        *bool_bnd.concl(),
        "`Σ z:⟦Bool⟧. 1` and `⟦Bool⟧` are two different sets"
    );

    // A domain whose `bnd` is about something else is refused.
    let other = derived::cumul::bnd_empty(&mut env, &ic.chain.r, &ic.chain.st).expect("bnd(∅)");
    assert!(derived::cumul::bnd_telescope1(&mut env, &ic, &mach, &tel, &[], &other).is_none());

    // Depth 2 is refused by the guard, not mis-derived. `βᵢ` has arity
    // `np + i`, so the second binder's type is a unary symbol.
    let b1 = konst(&mut env, 1, boolean.carrier.clone());
    let deep = mach
        .telescope(&mut env, 0, &[boolean.ty, b1])
        .expect("a two-binder telescope");
    assert!(
        derived::cumul::bnd_telescope1(&mut env, &ic, &mach, &deep, &[], &bool_bnd).is_none(),
        "depth 2 needs a merge over the domain and is declined"
    );
}

/// **The whole chain, at `RTree`.** `over_at_general` places the carrier of a
/// declaration with a function-typed recursive argument, with every fibre fact
/// derived rather than assumed.
///
/// This is the composition the four preceding tests take apart:
///
/// ```text
/// bnd(⟦Bool⟧)              bnd_carrier          over the Bool declaration
/// bnd(Σ z:⟦Bool⟧. 1)       bnd_telescope1       the fibre telescope
/// bnd(Sum_1(…))            bnd_isum             inside over_at_general
/// ⟦Bool⟧ ∈ U₁              DeclUniverse::over   over the Bool declaration
/// Σ z:⟦Bool⟧. 1 ∈ U₁       unary_telescope_at   the same fibre telescope
/// Sum_1(…) ∈ U₁            isum_in_universe     inside over_at_general
/// ```
///
/// Nothing here is special-cased to two constructors or to `Bool`: every step
/// reads a `DeclSpec`, an `Inductive` or a `Telescope`.
#[test]
fn the_placement_goes_through_at_a_function_typed_recursive_argument() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let inversion = derived::wtype::w_inversion(&mut env, &mach.wt).expect("W3");

    // ── `⟦Bool⟧`, with both facts derived over its own declaration ──────────
    let bool_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let boolean = Inductive::build(&mut env, &mut mach, &bool_spec).expect("Bool");
    let bt = derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &boolean).expect("bnd(A)");
    let bool_bnd =
        derived::cumul::bnd_carrier(&mut env, &ic, &mach, &boolean, &inversion, &bt)
            .expect("bnd(⟦Bool⟧)");
    let bool_u1 = {
        let su = nullary_summands_in_u1(&mut env, &ic, &mach, &boolean).expect("summands");
        let tg = tags_in_u1(&mut env, &ic, &mach, &boolean, None, &su).expect("A ∈ U₁");
        DeclUniverse::over(&mut env, &ic, &mach, &boolean, None, &tg)
            .expect("⟦Bool⟧ ∈ U₁")
            .ty_in_u1
    };
    assert_eq!(
        *bool_u1.concl(),
        Formula::mem(boolean.carrier.clone(), ic.chain.u1.set.clone())
    );

    // ── `RTree`: `leaf` and `node : (⟦Bool⟧ → RTree) → RTree` ───────────────
    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![boolean.ty]])],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("RTree");
    let tel = mach.telescope(&mut env, 0, &[boolean.ty]).expect("the fibre telescope");

    let fib_bnd = derived::cumul::bnd_telescope1(&mut env, &ic, &mach, &tel, &[], &bool_bnd)
        .expect("bnd(Σ z:⟦Bool⟧. 1)");
    let fib_mem = derived::cumul::unary_telescope_at(
        &mut env,
        &ic,
        &mach,
        &tel,
        &[],
        None,
        &ic.chain.u1,
        &bool_u1,
    )
    .expect("Σ z:⟦Bool⟧. 1 ∈ U₁");

    // Both are about the summand `over_at_general` reads, and nothing else.
    let summand = ind.recargs[1].summands[0].clone();
    assert_eq!(*fib_bnd.concl(), bnd(&mut env, &ic.chain.r, &ic.chain.st, &summand));
    assert_eq!(*fib_mem.concl(), Formula::mem(summand, ic.chain.u1.set.clone()));

    // ── the placement ──────────────────────────────────────────────────────
    let su = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("summands");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &su).expect("A ∈ U₁");
    let facts = FibreFacts {
        bnd: vec![Vec::new(), vec![fib_bnd]],
        mem: vec![Vec::new(), vec![fib_mem]],
    };
    let du = DeclUniverse::over_at_general(
        &mut env,
        &ic,
        &mach,
        &ind,
        None,
        &ic.chain.u1,
        &tags,
        Some(&facts),
    )
    .expect("⟦RTree⟧ ∈ U₁");

    assert!(du.rests_on_nothing(), "unconditional at a closed declaration");
    assert_eq!(du.universe, ic.chain.u1.set);
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone()),
        "the carrier itself, not the W-type behind it"
    );

    // Non-vacuity: the placed set has two provably distinct elements.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());

    // And the plain path still refuses this declaration, so the facts were
    // load-bearing rather than decoration.
    assert!(DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &tags).is_none());
}
