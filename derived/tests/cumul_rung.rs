//! **The constructor-summand / tag-set pipeline at an arbitrary rung** —
//! `derived/src/cumul/{sigma_n,sigma,tags}.rs`, run at `U₂` as well as at `U₁`.
//!
//! Six entry points were generalised from `U₁` to a caller-supplied
//! [`derived::tower::Rung`], with the six `*_in_u1` names kept as one-line
//! `n = 1` instances. Four things are pinned here:
//!
//! 1. the `n = 1` instances agree with the generalised entries **on the nose**,
//!    conclusion for conclusion, so no existing caller moved;
//! 2. a genuine `U₂` run — the tags of a closed declaration folded at rung 2
//!    and fed to `DeclUniverse::over_at`, with the conclusion pinned at
//!    `Tower::u(2)` and *not* at `Tower::u(1)`;
//! 3. the case that forces the generalisation: a constructor argument whose
//!    type is `U₁` itself, whose membership `⊢ U₁ ∈ U₂` (`Rung::mem_below`)
//!    exists only above the first universe. Raising goes upward only, so there
//!    is nothing to lower and the old `U₁`-only pipeline could not state the
//!    obligation at all. The **negative** half is pinned beside it: the same
//!    call at rung 1 is `None`, which is what a pipeline that ignored its rung
//!    would fail;
//! 4. a `Rung` from a *second* `Tower` in the same `Env` is refused — `None`,
//!    not a true theorem about the wrong `U(·)`.
//!
//! Every membership assertion is accompanied by a non-vacuity one: `∈ U₂` is
//! satisfied by `∅`, so each set placed in a universe is also made to exhibit
//! provably distinct elements.

use kernel::{Env, Formula, Term, Thm};

use derived::anchor::falsity;
use derived::bound::Bound;
use derived::cumul::{
    arg_obligations, arg_obligations_at, nullary_summand_at, nullary_summand_in_u1,
    nullary_summands_at, nullary_summands_in_u1, summand_at, summand_in_u1, tags_at, tags_in_u1,
    unary_summand_at, unary_summand_in_u1, DeclUniverse, IndChain,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};
use derived::sigma::Telescope;
use derived::tower::{Cumul, Rung, Tower};
use derived::wtype::Wtype;
use derived::{a1i, and_intro, eq_symm, inst_all, mpd_const, syl};

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

/// `⊢ b ∈ Uₙ → a ∈ Uₙ` for a defining equation `⊢ a = b`.
fn back_along(env: &mut Env, un: &Term, def_eq: &Thm) -> Thm {
    let (lhs, rhs) = def_eq.concl().as_eq().expect("a defining equation");
    let hole = env.fresh_var();
    Thm::mp(
        &Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(Term::var(hole), un.clone())),
        &eq_symm(env, def_eq).expect("symm"),
    )
    .expect("leibniz")
}

/// `⊢ a ∈ Uₙ` from `⊢ b ∈ Uₙ` and `⊢ a = b`.
fn along(env: &mut Env, un: &Term, def_eq: &Thm, rhs_in: &Thm) -> Thm {
    Thm::mp(&back_along(env, un, def_eq), rhs_in).expect("mp")
}

/// `⊢ H → a ∈ Uₙ` from `⊢ H → b ∈ Uₙ` and `⊢ a = b`.
fn along_hyp(env: &mut Env, un: &Term, def_eq: &Thm, rhs_in: &Thm) -> Thm {
    syl(rhs_in, &back_along(env, un, def_eq)).expect("syl")
}

/// `⊢ t ∈ β(args)` from `⊢ t ∈ <definition>` and `⊢ β(args) = <definition>`.
fn into_sym(env: &mut Env, def_eq: &Thm, t: &Term, mem: &Thm) -> Thm {
    let (lhs, rhs) = def_eq.concl().as_eq().expect("a defining equation");
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(t.clone(), Term::var(hole)));
    Thm::mp(&Thm::mp(&carry, &eq_symm(env, def_eq).expect("symm")).expect("leibniz"), mem)
        .expect("mp")
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The `n = 1` instances are the generalised entries at `ic.chain.u1`.
// ─────────────────────────────────────────────────────────────────────────────

/// **All six `*_in_u1` names agree on the nose** with the generalised entry at
/// `&ic.chain.u1` — the same formulas and the same conclusions, resting on
/// nothing.
///
/// `List α`, so that the run exercises a nullary constructor, a unary one, the
/// `k`-ary induction at `k = 1`, an antecedent `H = α ∈ U₁` and the fold, all
/// in one declaration.
#[test]
fn the_u1_entry_points_are_the_generalised_ones_at_rung_one() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let pv = env.fresh_var();
    let (id, id_ax) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("List");

    let u1 = ic.chain.u1.set.clone();
    let alpha = Term::var(ind.params[0]);
    let h = Formula::mem(alpha.clone(), u1.clone());
    let id_at = inst_all(&id_ax, std::slice::from_ref(&alpha)).expect("β₀(α) = α");
    let arg = along_hyp(&mut env, &u1, &id_at, &derived::imp_refl(h.clone()));

    // ── `arg_obligations` / `arg_obligations_at` ────────────────────────────
    let want = arg_obligations(&mut env, &ic, &mach, &ind, 1, Some(&h)).expect("obligations");
    let want_at =
        arg_obligations_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &ic.chain.u1).expect("at u1");
    assert_eq!(want, want_at, "the obligation formulas are the same, not merely alike");
    assert_eq!(want.len(), 1);
    assert_eq!(*arg.concl(), want[0]);

    // ── `summand_in_u1` / `summand_at` ──────────────────────────────────────
    let gen = summand_in_u1(&mut env, &ic, &mach, &ind, 1, Some(&h), std::slice::from_ref(&arg))
        .expect("the k-ary route");
    let gen_at = summand_at(
        &mut env,
        &ic,
        &mach,
        &ind,
        1,
        Some(&h),
        &ic.chain.u1,
        std::slice::from_ref(&arg),
    )
    .expect("the k-ary route, at rung 1");
    assert_eq!(gen.concl(), gen_at.concl());
    assert!(gen.hyps().is_empty() && gen_at.hyps().is_empty());

    // ── `unary_summand_in_u1` / `unary_summand_at` ──────────────────────────
    let fast = unary_summand_in_u1(&mut env, &ic, &mach, &ind, 1, Some(&h), &arg)
        .expect("the k = 1 route");
    let fast_at = unary_summand_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &ic.chain.u1, &arg)
        .expect("the k = 1 route, at rung 1");
    assert_eq!(fast.concl(), fast_at.concl());
    assert_eq!(fast.concl(), gen.concl(), "and both routes to the same summand agree");
    assert_eq!(
        *fast_at.concl(),
        Formula::imp(h.clone(), Formula::mem(ind.summands[1].clone(), u1.clone())),
        "⊢ α ∈ U₁ → A₁ ∈ U₁"
    );

    // ── `nullary_summand_in_u1` / `nullary_summand_at` ──────────────────────
    let nil = nullary_summand_in_u1(&mut env, &ic, &mach, &ind, 0).expect("A₀ = 1");
    let nil_at =
        nullary_summand_at(&mut env, &ic, &mach, &ind, 0, &ic.chain.u1).expect("A₀ at rung 1");
    assert_eq!(nil.concl(), nil_at.concl());
    assert_eq!(*nil_at.concl(), Formula::mem(ind.summands[0].clone(), u1.clone()));

    // ── `tags_in_u1` / `tags_at` ────────────────────────────────────────────
    let legs = [a1i(&nil, h.clone()), fast.clone()];
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, Some(&h), &legs).expect("H → A ∈ U₁");
    let tags_at_1 =
        tags_at(&mut env, &ic, &mach, &ind, Some(&h), &ic.chain.u1, &legs).expect("at rung 1");
    assert_eq!(tags.concl(), tags_at_1.concl());
    assert!(tags.hyps().is_empty() && tags_at_1.hyps().is_empty());
    assert_eq!(
        *tags_at_1.concl(),
        Formula::imp(h, Formula::mem(ind.tags.clone(), u1)),
        "⊢ α ∈ U₁ → A ∈ U₁"
    );

    // ── `nullary_summands_in_u1` / `nullary_summands_at`, on a closed decl ──
    let closed_spec =
        DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary(), CtorSpec::nullary()]);
    let closed = Inductive::build(&mut env, &mut mach, &closed_spec).expect("a 3-way enum");
    let all = nullary_summands_in_u1(&mut env, &ic, &mach, &closed).expect("each summand is 1");
    let all_at =
        nullary_summands_at(&mut env, &ic, &mach, &closed, &ic.chain.u1).expect("at rung 1");
    assert_eq!(all.len(), 3);
    for (a, b) in all.iter().zip(all_at.iter()) {
        assert_eq!(a.concl(), b.concl());
    }

    // Non-vacuity: the tag set just placed in `U₁` is not `∅` — `List`'s two
    // constructors are provably distinct elements of the carrier.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. A genuine `U₂` run.
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable, closed half.** A three-constructor enumeration's summands
/// and tag set are produced *directly* at rung 2 and fed to
/// `DeclUniverse::over_at`, giving `⊢ ⟦T⟧ ∈ U₂`.
///
/// The conclusion is pinned at `Tower::u(2)` and asserted **different** from
/// `Tower::u(1)`, and the tower is asserted not to collapse between them
/// (`Cumul::strict`), so this is a different statement from the `U₁` one rather
/// than the same one restated.
#[test]
fn a_closed_declaration_folds_its_tags_at_rung_two() {
    let mut env = Env::new();
    let (tower, cumul, ic, mut mach) = over_a_tower(&mut env);
    let spec =
        DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary(), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("a 3-way enum");

    let rung2 = tower.at(2).expect("rung 2");
    let (u1, u2) = (tower.u(1), tower.u(2));
    assert_ne!(u1, u2, "two different terms");
    assert!(cumul.strict(1).is_some(), "⊢ ¬(U₂ ⊆ U₁): the tower does not collapse");
    assert_eq!(rung2.set, u2, "and the rung is the one we asked for");

    // ── The pipeline, run at rung 2 from the start ──────────────────────────
    let summands = nullary_summands_at(&mut env, &ic, &mach, &ind, &rung2).expect("each Aᵢ ∈ U₂");
    assert_eq!(summands.len(), 3);
    for (i, t) in summands.iter().enumerate() {
        assert!(t.hyps().is_empty());
        assert_eq!(*t.concl(), Formula::mem(ind.summands[i].clone(), u2.clone()));
        assert_ne!(
            *t.concl(),
            Formula::mem(ind.summands[i].clone(), u1.clone()),
            "at U₂, not at U₁"
        );
    }
    let tags = tags_at(&mut env, &ic, &mach, &ind, None, &rung2, &summands).expect("A ∈ U₂");
    assert!(tags.hyps().is_empty());
    assert_eq!(*tags.concl(), Formula::mem(ind.tags.clone(), u2.clone()), "⊢ A ∈ U₂");

    // ── and onto the carrier, at the same rung ──────────────────────────────
    let du = DeclUniverse::over_at(&mut env, &ic, &mach, &ind, None, &rung2, &tags)
        .expect("⟦T⟧ ∈ U₂");
    assert!(du.rests_on_nothing());
    assert_eq!(du.universe, u2, "the rung it was asked for");
    assert_eq!(*du.ty_in_u1.concl(), Formula::mem(ind.carrier.clone(), u2.clone()), "⊢ ⟦T⟧ ∈ U₂");
    let mut vs = Vec::new();
    du.ty_in_u1.concl().free_vars(&mut vs);
    assert!(vs.is_empty(), "closed and unconditional");

    // The `U₁` tag membership is a *different* theorem, and it is not what was
    // used: the pipeline ran once, at rung 2.
    let rung1 = tower.at(1).expect("rung 1");
    let low = nullary_summands_at(&mut env, &ic, &mach, &ind, &rung1).expect("each Aᵢ ∈ U₁");
    let at_one =
        tags_at(&mut env, &ic, &mach, &ind, None, &rung1, &low).expect("A ∈ U₁");
    assert_ne!(at_one.concl(), tags.concl());
    // And it does raise to the same statement, which is the cheap route the
    // headers prescribe when `n₀ = 1`.
    let raised = cumul.raise(1, 2, &at_one).expect("A ∈ U₁ ⟹ A ∈ U₂");
    assert_eq!(raised.concl(), tags.concl(), "one `mp`, and the same theorem");

    // Non-vacuity: **three** pairwise distinct elements of the set now in `U₂`.
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        assert!(
            ind.distinct(&mut env, &mach, i, j).is_some(),
            "⊢ ¬(ctor_{i}() = ctor_{j}())"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. A field that cannot be lowered.
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable, and the reason the generalisation is not optional.** A
/// two-argument constructor whose *first* argument type is `U₁` itself.
///
/// `⊢ U₁ ∈ U₂` is `Rung::mem_below`, and there is no `⊢ U₁ ∈ U₁` — a universe
/// is not a member of itself. So the first obligation exists only at rung 2 and
/// cannot be lowered, while the second (`β₁(y₀) = U₀`) is proved at `U₁` and
/// **raised** by `Cumul::raise`. `summand_at` at rung 2 succeeds; the identical
/// call at rung 1 is `None`, which is the half a rung-ignoring pipeline would
/// fail.
#[test]
fn an_argument_that_only_lives_above_u1_forces_the_rung() {
    let mut env = Env::new();
    let (tower, cumul, ic, mut mach) = over_a_tower(&mut env);
    let s = mach.wt.sums.clone();
    let (rung1, rung2) = (tower.at(1).expect("rung 1"), tower.at(2).expect("rung 2"));
    let (u1, u2) = (tower.u(1), tower.u(2));

    // `β₀() = U₁` and `β₁(y₀) = U₀` — the first is only small one rung up.
    let (b0, b0_ax) = derived::define_abbrev(&mut env, &[], &u1).expect("β₀() = U₁");
    let y0 = env.fresh_var();
    let (b1, b1_ax) =
        derived::define_abbrev(&mut env, &[y0], &falsity::truth_values(&s)).expect("β₁(y₀) = U₀");
    assert_ne!(b0, b1);

    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0, b1], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the translation");

    let want =
        arg_obligations_at(&mut env, &ic, &mach, &ind, 0, None, &rung2).expect("obligations at U₂");
    assert_eq!(want.len(), 2);
    let want_1 =
        arg_obligations_at(&mut env, &ic, &mach, &ind, 0, None, &rung1).expect("obligations at U₁");
    assert_ne!(want, want_1, "the two rungs ask for different things");

    // ── The first argument: `⊢ β₀() ∈ U₂`, from `⊢ U₁ ∈ U₂` and nothing else ─
    assert_eq!(*rung2.mem_below.concl(), Formula::mem(u1.clone(), u2.clone()), "⊢ U₁ ∈ U₂");
    let p0 = along(&mut env, &u2, &b0_ax, &rung2.mem_below);
    assert_eq!(*p0.concl(), want[0]);

    // ── The second: proved at `U₁`, then **raised** ─────────────────────────
    let u0_in_u1 = rung1.u0_mem.clone();
    assert_eq!(*u0_in_u1.concl(), Formula::mem(falsity::truth_values(&s), u1.clone()));
    let u0_in_u2 = cumul.raise(1, 2, &u0_in_u1).expect("U₀ ∈ U₁ ⟹ U₀ ∈ U₂");
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let b1_at = inst_all(&b1_ax, std::slice::from_ref(&ty)).expect("β₁(y₀) = U₀");
    let guard = Formula::mem(ty.clone(), Term::apply(b0, vec![]));
    let p1 = Thm::gen(yv, &a1i(&along(&mut env, &u2, &b1_at, &u0_in_u2), guard));
    assert_eq!(*p1.concl(), want[1]);

    // ── The construction, at rung 2 ─────────────────────────────────────────
    let out = summand_at(&mut env, &ic, &mach, &ind, 0, None, &rung2, &[p0.clone(), p1.clone()])
        .expect("Σy₀:U₁. Σy₁:U₀. 1 ∈ U₂");
    assert!(out.hyps().is_empty());
    assert_eq!(*out.concl(), Formula::mem(ind.summands[0].clone(), u2.clone()), "⊢ A₀ ∈ U₂");
    assert_ne!(*out.concl(), Formula::mem(ind.summands[0].clone(), u1.clone()));

    // ── **The negative half.** The same call at rung 1 is refused ───────────
    assert!(
        summand_at(&mut env, &ic, &mach, &ind, 0, None, &rung1, &[p0.clone(), p1.clone()])
            .is_none(),
        "a U₂ obligation does not discharge a U₁ one"
    );
    assert!(
        summand_in_u1(&mut env, &ic, &mach, &ind, 0, None, &[p0, p1]).is_none(),
        "and the `n = 1` instance is that same call"
    );

    // ── Non-vacuity: three pairwise distinct elements of `A₀` ───────────────
    //
    // `⟨∅,⟨0,•⟩⟩`, `⟨U₀,⟨0,•⟩⟩` and `⟨∅,⟨1,•⟩⟩`. The first components are
    // distinct because `0 ∈ U₀` and `0 ∉ ∅`; the second because `¬(0 = 1)`.
    let (zero, one) = (s.zero(), s.unit());
    let u0 = falsity::truth_values(&s);
    let zero_in_b0 = into_sym(&mut env, &b0_ax, &zero, &rung1.empty_mem);
    let u0_in_b0 = into_sym(&mut env, &b0_ax, &u0, &rung1.u0_mem);
    let in_b1 = |env: &mut Env, y: &Term, x: &Term, mem: &Thm| -> Thm {
        let ax = inst_all(&b1_ax, std::slice::from_ref(y)).expect("β₁(y₀)");
        into_sym(env, &ax, x, mem)
    };
    let false_in = falsity::false_in_prop(&s).expect("0 ∈ U₀");
    let true_in = falsity::true_in_prop(&s).expect("1 ∈ U₀");

    let tel: &Telescope = &ind.telescopes[0];
    let pack = |env: &mut Env, y: &Term, x: &Term, h0: &Thm, xm: &Thm| -> Thm {
        let rule = inst_all(&tel.intro, &[y.clone(), x.clone()]).expect("the introduction rule");
        let h1 = in_b1(env, y, x, xm);
        Thm::mp(&rule, &and_intro(h0, &h1)).expect("mp")
    };
    let e_a = pack(&mut env, &zero, &zero, &zero_in_b0, &false_in);
    let e_b = pack(&mut env, &u0, &zero, &u0_in_b0, &false_in);
    let e_c = pack(&mut env, &zero, &one, &zero_in_b0, &true_in);
    let t_of = |y: &Term, x: &Term| Telescope::tuple_of(&s, &[y.clone(), x.clone()]);
    for (t, y, x) in [(&e_a, &zero, &zero), (&e_b, &u0, &zero), (&e_c, &zero, &one)] {
        assert_eq!(*t.concl(), Formula::mem(t_of(y, x), ind.summands[0].clone()));
    }
    assert_ne!(e_a.concl(), e_b.concl());
    assert_ne!(e_a.concl(), e_c.concl());
    assert_ne!(e_b.concl(), e_c.concl());

    // `⊢ ¬(∅ = U₀)`, because `0 ∈ U₀` and `0 ∉ ∅`.
    let ne_first = {
        let hole = env.fresh_var();
        let carry = Thm::eq_leibniz(
            u0.clone(),
            zero.clone(),
            hole,
            Formula::mem(zero.clone(), Term::var(hole)),
        );
        let to_absurd = mpd_const(&carry, &false_in).expect("U₀ = ∅ → 0 ∈ ∅");
        let flip = derived::eq_symm_imp(&mut env, zero.clone(), u0.clone());
        syl(
            &syl(&flip, &to_absurd).expect("syl"),
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&zero)).expect("0 ∉ ∅"),
        )
        .expect("syl")
    };
    assert_eq!(*ne_first.concl(), Formula::not(Formula::eq(zero.clone(), u0.clone())));

    // `⊢ ¬(⟨0,•⟩ = ⟨1,•⟩)`, because `¬(0 = 1)`.
    let nil_tuple = Telescope::tuple_of(&s, &[]);
    let (t0, t1) = (
        Telescope::tuple_of(&s, std::slice::from_ref(&zero)),
        Telescope::tuple_of(&s, std::slice::from_ref(&one)),
    );
    let ne_tails = syl(
        &syl(
            &inst_all(
                &s.ap.pair_inj,
                &[zero.clone(), nil_tuple.clone(), one.clone(), nil_tuple.clone()],
            )
            .expect("pair injectivity"),
            &derived::and_left(
                Formula::eq(zero.clone(), one.clone()),
                Formula::eq(nil_tuple.clone(), nil_tuple),
            ),
        )
        .expect("syl"),
        &falsity::prop_two_valued(&s).expect("¬(0 = 1)"),
    )
    .expect("syl");
    assert_eq!(*ne_tails.concl(), Formula::not(Formula::eq(t0.clone(), t1.clone())));

    // and lift both through ordered-pair injectivity, once on each component.
    let ne_ab = syl(
        &syl(
            &inst_all(&s.ap.pair_inj, &[zero.clone(), t0.clone(), u0.clone(), t0.clone()])
                .expect("pair injectivity"),
            &derived::and_left(
                Formula::eq(zero.clone(), u0.clone()),
                Formula::eq(t0.clone(), t0.clone()),
            ),
        )
        .expect("syl"),
        &ne_first,
    )
    .expect("syl");
    let ne_ac = syl(
        &syl(
            &inst_all(&s.ap.pair_inj, &[zero.clone(), t0.clone(), zero.clone(), t1.clone()])
                .expect("pair injectivity"),
            &derived::and_right(
                Formula::eq(zero.clone(), zero.clone()),
                Formula::eq(t0.clone(), t1.clone()),
            ),
        )
        .expect("syl"),
        &ne_tails,
    )
    .expect("syl");
    assert_eq!(
        *ne_ab.concl(),
        Formula::not(Formula::eq(t_of(&zero, &zero), t_of(&u0, &zero))),
        "the first two elements differ in their first component"
    );
    assert_eq!(
        *ne_ac.concl(),
        Formula::not(Formula::eq(t_of(&zero, &zero), t_of(&zero, &one))),
        "the first and third differ in their second"
    );
    assert_ne!(ne_ab.concl(), ne_ac.concl(), "three elements, two independent reasons");
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. A rung from a second tower.
// ─────────────────────────────────────────────────────────────────────────────

/// **A `Rung` from a second `Tower` in the same `Env` is refused** by all six
/// generalised entry points.
///
/// This is the check that has to be on *statements*: the other tower's rung is
/// a perfectly good rung — every closure clause holds of it — so an unguarded
/// pipeline would happily return a true theorem about the **wrong** `U(·)`,
/// carrying this chain's tag set into a universe this chain's
/// `w_in_universe_bnd` says nothing about. The contrast is pinned beside it:
/// the same calls at this tower's own rungs 1 and 2 succeed.
#[test]
fn a_rung_from_a_second_tower_is_refused() {
    let mut env = Env::new();
    let (tower, _cumul, ic, mut mach) = over_a_tower(&mut env);
    let other = Tower::new(&mut env).expect("a second, independent tower");
    let alien: Rung = other.at(1).expect("and it is a genuine rung");

    // The alien rung is *not* broken — it is simply not ours.
    assert_ne!(alien.set, tower.u(1), "two towers, two `U(ω)`s");
    assert_ne!(alien.seed, tower.at(1).expect("rung 1").seed, "and two `ω`s");
    assert!(
        alien.empty_mem.hyps().is_empty()
            && alien.pairing.hyps().is_empty()
            && alien.sub.hyps().is_empty()
            && alien.product.hyps().is_empty()
            && alien.union.hyps().is_empty()
            && alien.bin_union.hyps().is_empty(),
        "every closure clause of the alien rung is a genuine `⊢`"
    );

    let pv = env.fresh_var();
    let (id, id_ax) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("List");

    let u1 = tower.u(1);
    let alpha = Term::var(ind.params[0]);
    let h = Formula::mem(alpha.clone(), u1.clone());
    let id_at = inst_all(&id_ax, std::slice::from_ref(&alpha)).expect("β₀(α) = α");
    let arg = along_hyp(&mut env, &u1, &id_at, &derived::imp_refl(h.clone()));

    let own = tower.at(1).expect("rung 1");
    let own2 = tower.at(2).expect("rung 2");

    // ── the six, at the alien rung ──────────────────────────────────────────
    assert!(
        arg_obligations_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &alien).is_none(),
        "arg_obligations_at"
    );
    assert!(
        summand_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &alien, std::slice::from_ref(&arg))
            .is_none(),
        "summand_at"
    );
    assert!(
        unary_summand_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &alien, &arg).is_none(),
        "unary_summand_at"
    );
    assert!(
        nullary_summand_at(&mut env, &ic, &mach, &ind, 0, &alien).is_none(),
        "nullary_summand_at"
    );
    assert!(
        nullary_summands_at(&mut env, &ic, &mach, &ind, &alien).is_none(),
        "nullary_summands_at — refused before the fold even sees a summand"
    );
    let nil = nullary_summand_at(&mut env, &ic, &mach, &ind, 0, &own).expect("A₀ ∈ U₁");
    let cons =
        unary_summand_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &own, &arg).expect("A₁ ∈ U₁");
    let legs = [a1i(&nil, h.clone()), cons];
    assert!(
        tags_at(&mut env, &ic, &mach, &ind, Some(&h), &alien, &legs).is_none(),
        "tags_at"
    );

    // ── the contrast: our own rungs 1 and 2 do work ─────────────────────────
    assert!(arg_obligations_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &own).is_some());
    assert!(arg_obligations_at(&mut env, &ic, &mach, &ind, 1, Some(&h), &own2).is_some());
    let tags = tags_at(&mut env, &ic, &mach, &ind, Some(&h), &own, &legs).expect("H → A ∈ U₁");
    assert_eq!(*tags.concl(), Formula::imp(h, Formula::mem(ind.tags.clone(), u1)));
    assert!(nullary_summand_at(&mut env, &ic, &mach, &ind, 0, &own2).is_some());
}
