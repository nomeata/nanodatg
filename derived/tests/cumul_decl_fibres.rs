//! **`DeclUniverse::over_at_general`** — the carrier's universe placement when
//! a constructor's fibre value is not `finord(mᵢ)`.
//!
//! `over_at` reads each fibre value through `finords_in_universe`, which used
//! to be stated at `finord(mᵢ)` alone. A **function-typed** recursive argument
//! — `RTree.node : (Bool → RTree) → RTree` — gives its slot the fibre summand
//! `Σ(z::γ)` rather than `1` (`thesis.txt:1800`), so the value is
//! `Sum_m(Σ(z::γ⃗))` and the reader could not be instantiated.
//!
//! It used to read each value **twice**, the second time through
//! `bnd_finords`. That half is gone: step (f) is
//! `wpath::w_in_universe_paths`, which asks nothing about the fibres, so
//! [`FibreFacts`] carries one theorem per summand and not two. The `bnd`
//! producers below are still derived and still tested — they have simply
//! stopped being on this path.
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

    // The same, with the fact about `1` handed in rather than synthesised.
    let um = derived::inst_all(&ic.clo.unit, std::slice::from_ref(&ic.chain.u1.seed))
        .expect("1 ∈ U₁");
    let facts = FibreFacts { mem: vec![Vec::new(), vec![um.clone()]] };
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
    let zm = derived::cumul::zero_in_u1(&ic.chain);
    for bad in [
        // One entry too few at the outer level.
        FibreFacts { mem: vec![vec![um.clone()]] },
        // The right outer shape, the wrong inner one.
        FibreFacts { mem: vec![Vec::new(), Vec::new()] },
        // A membership about `∅` where the summand is `1`.
        FibreFacts { mem: vec![Vec::new(), vec![zm]] },
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
    for (i, a) in fib.iter().enumerate() {
        assert_eq!(mach.syms.sum(a).expect("Sum"), ind.fibre.values[i]);
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

    // **The one theorem a consumer must bring** for the third constructor, at
    // this exact term. `unary_telescope_at` produces it from a fact about the
    // *domain*, and
    // `the_placement_goes_through_at_a_function_typed_recursive_argument`
    // composes the whole chain; this test is the statement of the obligation,
    // pinned where it can be re-measured if the producer moves.
    //
    // It used to be two, the other being `⊢ bnd(Σ(z::γ))`. The `bnd` half is
    // what an infinite `γ` could not supply and what the path route stopped
    // asking for; the membership below has no such guard and never did.
    let want_mem = Formula::mem(fib[2][0].clone(), ic.chain.u1.set.clone());
    assert_ne!(want_mem, Formula::mem(s.unit(), ic.chain.u1.set.clone()));
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
    //
    // The `tags_bnd` this is given is **N's own**, built here rather than by
    // `bnd_nullary_tags` — which refuses `N` on `recs`, not on the tags, since
    // `N`'s two summands are both `1`. That matters: handed the *other*
    // declaration's `tags_bnd`, `bnd_carrier` refuses on the conclusion
    // comparison two checks earlier and never reads a fibre value at all, so
    // the fixture would pin nothing about recursion. With the matching one the
    // discriminator is the fibre value: `succ`'s is not `Sum_0()`, so
    // `fin_elim`'s per-value case list cannot be built.
    let rec_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(Vec::new(), 1)]);
    let rec_ind = Inductive::build(&mut env, &mut mach, &rec_spec).expect("N");
    assert!(derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &rec_ind).is_none());

    let rec_tags = {
        let unit_bnd = bnd_unit(&mut env, &ic.chain.r, &ic.chain.st, &mach.wt.sums)
            .expect("bnd(1)");
        let bnds: Vec<kernel::Thm> = (0..rec_ind.summands.len())
            .map(|i| {
                let base_at =
                    derived::inst_all(&rec_ind.telescopes[i].base_ax, &[]).expect("base_ax");
                let summand = rec_ind.summands[i].clone();
                assert_eq!(
                    *base_at.concl(),
                    Formula::eq(summand.clone(), mach.wt.sums.unit()),
                    "N's tag summands are both `1`, recursion or not"
                );
                let hole = env.fresh_var();
                let body = bnd(&mut env, &ic.chain.r, &ic.chain.st, &Term::var(hole));
                kernel::Thm::mp(
                    &kernel::Thm::mp(
                        &kernel::Thm::eq_leibniz(mach.wt.sums.unit(), summand, hole, body),
                        &derived::eq_symm(&mut env, &base_at).expect("symm"),
                    )
                    .expect("leibniz"),
                    &unit_bnd,
                )
                .expect("bnd of the summand")
            })
            .collect();
        derived::cumul::bnd_isum(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &mach.wt.sums,
            &mach.syms,
            &ic.bnd_sum,
            &rec_ind.summands,
            &bnds,
        )
        .expect("bnd(A) for N, built without `bnd_nullary_tags`")
    };
    assert_eq!(*rec_tags.concl(), bnd(&mut env, &ic.chain.r, &ic.chain.st, &rec_ind.tags));

    assert!(
        derived::cumul::bnd_carrier(&mut env, &ic, &mach, &rec_ind, &inversion, &rec_tags)
            .is_none(),
        "a recursive declaration is refused, and refused on its fibre value"
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

/// **Depth ≥ 2, measured** — what is left of that decline now that `bnd` is off
/// the path, and it is not what the estimate said.
///
/// SCOPING.md §14.5 recorded the `bnd` reason (a Replacement-indexed union over
/// `β₀`-many indices, which `Stages::directed` cannot give) as *removed rather
/// than discharged*, and predicted that what remains is a `mem` half which
/// `cumul::sigma_n::summand_at` "already proves `k`-ary", so that "the remaining
/// work is one `k`-ary call site, not a theorem".
///
/// **The first half holds and the second does not.** `bnd_telescope1`'s depth
/// guard is indeed off the path — nothing calls it. But `summand_at` is `k`-ary
/// only over an [`Inductive`]'s *argument* telescope: its `levels()` reads
/// `ind.telescopes[ci]`, checks `ind.spec.ctors[ci].args.len()` and pins the
/// result against `ind.summands[ci]`, none of which a **fibre** telescope has.
/// The only entry point that takes a `Telescope` directly is
/// `unary_telescope_at`, and it is unary: `unary_sum_of` requires
/// `tel.ys.len() == 1`.
///
/// So the remaining work is the `k`-ary analogue of `unary_telescope_at` —
/// exactly the split that already exists between `unary_summand_at` (over an
/// `Inductive`) and `unary_telescope_at` (over a `Telescope`), made at depth
/// `k`. That is a refactor of `summand_at`'s core rather than new mathematics,
/// which is the part of the estimate that survives; it is *not* a call site.
#[test]
fn a_fibre_telescope_of_depth_two_declines_at_the_unary_entry_point() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    let bool_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let boolean = Inductive::build(&mut env, &mut mach, &bool_spec).expect("Bool");
    let bool_u1 = {
        let su = nullary_summands_in_u1(&mut env, &ic, &mach, &boolean).expect("summands");
        let tg = tags_in_u1(&mut env, &ic, &mach, &boolean, None, &su).expect("A ∈ U₁");
        DeclUniverse::over(&mut env, &ic, &mach, &boolean, None, &tg)
            .expect("⟦Bool⟧ ∈ U₁")
            .ty_in_u1
    };

    // Depth 1 over the same domain goes through — so the decline below is the
    // depth and nothing about `⟦Bool⟧`.
    let one = mach.telescope(&mut env, 0, &[boolean.ty]).expect("Σ(z::Bool)");
    assert!(
        derived::cumul::unary_telescope_at(
            &mut env, &ic, &mach, &one, &[], None, &ic.chain.u1, &bool_u1,
        )
        .is_some(),
        "the unary entry point is happy at depth 1"
    );

    // `βᵢ` has arity `np + i`, so the second binder's type is a unary symbol.
    let b1 = konst(&mut env, 1, boolean.carrier.clone());
    let deep = mach
        .telescope(&mut env, 0, &[boolean.ty, b1])
        .expect("a two-binder telescope");
    assert!(
        derived::cumul::unary_telescope_at(
            &mut env, &ic, &mach, &deep, &[], None, &ic.chain.u1, &bool_u1,
        )
        .is_none(),
        "and refuses depth 2 — `unary_sum_of` wants exactly one binder"
    );

    // And the `k`-ary derivation cannot be pointed here: it is stated over a
    // constructor of a declaration, not over a telescope. `RTree.node` has a
    // *function-typed recursive* argument and therefore **no** non-recursive
    // ones, so `summand_at`'s own `k` for it is `0` and its subject is
    // `ind.summands[1] = 1` — a different set from `deep`'s type.
    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![boolean.ty]])],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("RTree");
    assert_eq!(ind.spec.ctors[1].args.len(), 0, "`node` has no non-recursive argument");
    let ka = derived::cumul::summand_at(&mut env, &ic, &mach, &ind, 1, None, &ic.chain.u1, &[])
        .expect("the k-ary entry point, at k = 0");
    assert_eq!(
        *ka.concl(),
        Formula::mem(ind.summands[1].clone(), ic.chain.u1.set.clone()),
        "and its subject is the *tag* summand"
    );
    assert_ne!(
        ind.summands[1],
        deep.ty_of(Vec::new()),
        "which is not the fibre telescope's type — the two are different sets, and that is why \
         `summand_at` is not the missing call site"
    );
}

/// **The whole chain, at `RTree`.** `over_at_general` places the carrier of a
/// declaration with a function-typed recursive argument, with every fibre fact
/// derived rather than assumed.
///
/// This is the composition the four preceding tests take apart:
///
/// ```text
/// ⟦Bool⟧ ∈ U₁              DeclUniverse::over   over the Bool declaration
/// Σ z:⟦Bool⟧. 1 ∈ U₁       unary_telescope_at   the fibre telescope
/// Sum_1(…) ∈ U₁            isum_in_universe     inside over_at_general
/// ```
///
/// **Three rows and it used to be six** — the `bnd` column of the same
/// composition went with `FibreFacts::bnd`.
///
/// Nothing here is special-cased to two constructors or to `Bool`: every step
/// reads a `DeclSpec`, an `Inductive` or a `Telescope`.
#[test]
fn the_placement_goes_through_at_a_function_typed_recursive_argument() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    // ── `⟦Bool⟧`, with its universe fact derived over its own declaration ───
    let bool_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let boolean = Inductive::build(&mut env, &mut mach, &bool_spec).expect("Bool");
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

    // It is about the summand `over_at_general` reads, and nothing else.
    let summand = ind.recargs[1].summands[0].clone();
    assert_eq!(*fib_mem.concl(), Formula::mem(summand, ic.chain.u1.set.clone()));

    // ── the placement ──────────────────────────────────────────────────────
    let su = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("summands");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &su).expect("A ∈ U₁");
    let facts = FibreFacts { mem: vec![Vec::new(), vec![fib_mem]] };
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

/// **The same chain under an antecedent** — `over_at_general` at
/// `hyp = Some(H)`, with a function-typed recursive argument.
///
/// This is what a **parameterised** declaration needs and what the placement
/// could not do until `isum_in_universe_under` existed:
/// `inductive Tree (α) | node : (α → Tree α) → Tree α` has the fibre summand
/// `Σ(z::α)`, whose universe membership exists under `α`'s own typing and under
/// nothing weaker, so `T ∈ Uₙ` — the finite set of the constructors' fibre
/// values — inherits the antecedent and every step above it must carry it.
///
/// The declaration here is the *closed* `RTree` of
/// [`the_placement_goes_through_at_a_function_typed_recursive_argument`], with
/// every input lifted under an `H` that has nothing to do with it. That is
/// deliberate and it is the stronger test: `H` is `x ∈ U₁` at a free variable
/// **no term in the declaration mentions**, so
///
/// * a derivation that discharged `H` somewhere in the middle could not produce
///   this conclusion, since nothing in scope proves it;
/// * a derivation that generalised over `x` would produce a different one;
/// * and the antecedent cannot be arriving by accident from the declaration,
///   because the declaration is the one the sibling test places *without* it.
///
/// The two placements are compared directly at the end: same carrier, same
/// universe, and the conditional one's conclusion is the unconditional one's
/// behind exactly one `→`.
#[test]
fn the_placement_carries_an_antecedent_through_the_fibre_side() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");

    let bool_spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let boolean = Inductive::build(&mut env, &mut mach, &bool_spec).expect("Bool");
    let bool_u1 = {
        let su = nullary_summands_in_u1(&mut env, &ic, &mach, &boolean).expect("summands");
        let tg = tags_in_u1(&mut env, &ic, &mach, &boolean, None, &su).expect("A ∈ U₁");
        DeclUniverse::over(&mut env, &ic, &mach, &boolean, None, &tg)
            .expect("⟦Bool⟧ ∈ U₁")
            .ty_in_u1
    };

    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![boolean.ty]])],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("RTree");
    let tel = mach.telescope(&mut env, 0, &[boolean.ty]).expect("the fibre telescope");

    // `H`, at a variable the declaration does not mention.
    let x = env.fresh_var();
    let h = Formula::mem(Term::var(x), ic.chain.u1.set.clone());

    // The fibre summand's membership, derived under `H` by the same entry point
    // `mini` uses — `unary_telescope_at` takes the antecedent too.
    let fib_mem = derived::cumul::unary_telescope_at(
        &mut env,
        &ic,
        &mach,
        &tel,
        &[],
        Some(&h),
        &ic.chain.u1,
        &derived::a1i(&bool_u1, h.clone()),
    )
    .expect("H → Σ z:⟦Bool⟧. 1 ∈ U₁");
    assert_eq!(
        *fib_mem.concl(),
        Formula::imp(
            h.clone(),
            Formula::mem(ind.recargs[1].summands[0].clone(), ic.chain.u1.set.clone())
        ),
        "the summand `over_at_general` reads, under `H`"
    );

    let su = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("summands");
    let lifted: Vec<_> = su.iter().map(|t| derived::a1i(t, h.clone())).collect();
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, Some(&h), &lifted).expect("H → A ∈ U₁");
    let facts = FibreFacts { mem: vec![Vec::new(), vec![fib_mem]] };
    let du = DeclUniverse::over_at_general(
        &mut env,
        &ic,
        &mach,
        &ind,
        Some(&h),
        &ic.chain.u1,
        &tags,
        Some(&facts),
    )
    .expect("H → ⟦RTree⟧ ∈ U₁");

    // Every field still rests on nothing: `H` is in the conclusion, which is
    // the whole reason the final `Thm::gen` over a declaration's parameters is
    // legal.
    assert!(du.rests_on_nothing(), "the antecedent is not a sequent hypothesis");
    assert_eq!(du.universe, ic.chain.u1.set);

    let mem = Formula::mem(ind.carrier.clone(), ic.chain.u1.set.clone());
    assert_eq!(
        *du.ty_in_u1.concl(),
        Formula::imp(h.clone(), mem.clone()),
        "⊢ H → ⟦RTree⟧ ∈ U₁, at the carrier and not at the W-type"
    );
    // The fibre side is where `H` enters, so `T ∈ U₁` carries it and the two
    // rung-free facts do not.
    assert_eq!(
        *du.target_in_u1.concl(),
        Formula::imp(h.clone(), Formula::mem(ind.fibre.target.clone(), ic.chain.u1.set.clone())),
        "`T ∈ U₁` is conditional exactly when a fibre summand is"
    );

    // ── the same declaration without `H`, for comparison ────────────────────
    let plain_tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &su).expect("A ∈ U₁");
    let plain_fib = derived::cumul::unary_telescope_at(
        &mut env, &ic, &mach, &tel, &[], None, &ic.chain.u1, &bool_u1,
    )
    .expect("Σ z:⟦Bool⟧. 1 ∈ U₁");
    let plain = DeclUniverse::over_at_general(
        &mut env,
        &ic,
        &mach,
        &ind,
        None,
        &ic.chain.u1,
        &plain_tags,
        Some(&FibreFacts { mem: vec![Vec::new(), vec![plain_fib]] }),
    )
    .expect("⟦RTree⟧ ∈ U₁");
    assert_eq!(*plain.ty_in_u1.concl(), mem, "one derivation, two contexts");
    // The two rung-free facts are *identical* across the two contexts, which is
    // what "unconditional at every declaration" means and is stronger than any
    // shape test on the conditional one alone. A conjunction is spelled with
    // implications in this kernel, so `as_imp().is_none()` would not say it.
    assert_eq!(du.fin.concl(), plain.fin.concl(), "`fin` is unconditional");
    assert_eq!(
        du.seed_in_bound.concl(),
        plain.seed_in_bound.concl(),
        "and so is `S ∈ U({{A,T}})`"
    );
    assert!(du.fin.hyps().is_empty() && du.seed_in_bound.hyps().is_empty());

    // ── and the shape is required on the way in ─────────────────────────────
    //
    // A fibre fact that arrives *without* the antecedent is refused, so the
    // conditional placement is composing `H` rather than recovering it.
    let bare = derived::cumul::unary_telescope_at(
        &mut env, &ic, &mach, &tel, &[], None, &ic.chain.u1, &bool_u1,
    )
    .expect("Σ z:⟦Bool⟧. 1 ∈ U₁");
    assert!(
        DeclUniverse::over_at_general(
            &mut env,
            &ic,
            &mach,
            &ind,
            Some(&h),
            &ic.chain.u1,
            &tags,
            Some(&FibreFacts { mem: vec![Vec::new(), vec![bare]] }),
        )
        .is_none(),
        "an unconditional fibre fact under `Some(H)` must be refused"
    );
}
