//! The dependent sum `Σ` — §5.2's rule for a constructor's non-recursive
//! arguments (`thesis.txt:1795–1797`), at one argument and at a telescope.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** An introduction rule alone is satisfied
//! by a one-element `Σ` that forgets its arguments;
//! [`the_telescope_remembers_both_arguments`] shows the two components come
//! back out as *different* sets, and [`the_telescope_is_genuinely_dependent`]
//! shows the second argument's stated type mentions the first.

use kernel::{Env, Formula, Term, Thm};

use derived::ext::app_of_pair;
use derived::funcs::Apply;
use derived::isum::{finord, inj_of, ISum};
use derived::point_fun::PointFun;
use derived::proj::Proj;
use derived::sigma::{dsum, product_parts, Telescope};
use derived::sums::Sums;
use derived::{define_abbrev, eq_trans, inst_all, singleton};

struct Dev {
    s: Sums,
    proj: Proj,
    pparts: Thm,
}

fn build(env: &mut Env) -> Dev {
    let s = Sums::new(env).expect("sums");
    let app_pair = app_of_pair(env, &s.ap).expect("app_of_pair");
    let pf = PointFun::over(env, &s, &app_pair).expect("point functions");
    let proj = Proj::new(env, &s.ap, &pf).expect("projections");
    let pparts = product_parts(env, &s.ap, &s.prod, &proj).expect("product_parts");
    Dev { s, proj, pparts }
}

/// A formula with no free variables — an *unconditional*, closed statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
fn congr<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq).unwrap(), &Thm::eq_refl(lhs)).unwrap()
}

/// `⊢ ∀A ∀B ∀q. (q ∈ A × B → (π₁q ∈ A ∧ (π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)))` — the
/// bridge from [`derived::proj`]'s rules "at a literal pair" to a `Σ`'s
/// elimination rule, which is handed a bare element.
#[test]
fn a_product_member_is_its_own_two_projections() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let (av, bv, qv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tq) = (Term::var(av), Term::var(bv), Term::var(qv));

    assert!(kernel::thm::debug_locally_closed(d.pparts.concl()));
    let at = inst_all(&d.pparts, &[ta.clone(), tb.clone(), tq.clone()]).expect("instantiate");
    let (f, g) = (d.proj.fst_of(&s.ap, tq.clone()), d.proj.snd_of(&s.ap, tq.clone()));
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(tq.clone(), s.prod.of(ta.clone(), tb.clone())),
            Formula::and(
                Formula::mem(f.clone(), ta),
                Formula::and(
                    Formula::mem(g.clone(), tb),
                    Formula::eq(s.ap.sets.pair(f, g), tq),
                ),
            ),
        )
    );
}

/// One `Σ` level: the defining axiom, the introduction rule and the three
/// elimination rules, at a *dependent* fibre.
///
/// The instance is `Σx : 1. {x}` — the fibre genuinely mentions the bound
/// variable, so `snd_mem` reads `π₂q ∈ {π₁q}` and nothing about it could be
/// stated without the projections being real term-formers.
#[test]
fn one_dependent_sum_level_packs_and_unpacks() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let ap: &Apply = &s.ap;
    let up = ap.sets.up;

    let (dom, _) = define_abbrev(&mut env, &[], &s.unit()).expect("dom = 1");
    let xv = env.fresh_var();
    let sing = singleton(up, Term::var(xv));
    let (fib, fib_ax) = define_abbrev(&mut env, &[xv], &sing).expect("fib(x) = {x}");
    let ds = dsum(&mut env, s, &d.proj, &d.pparts, dom, fib).expect("Σx : 1. {x}");

    let sig = Term::apply(ds.sigma, vec![]);
    let (aav, vvv, qv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (taa, tvv, tq) = (Term::var(aav), Term::var(vvv), Term::var(qv));

    // Introduction.
    let intro = inst_all(&ds.intro, &[taa.clone(), tvv.clone()]).expect("instantiate");
    assert_eq!(
        *intro.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(taa.clone(), Term::apply(dom, vec![])),
                Formula::mem(tvv.clone(), Term::apply(fib, vec![taa.clone()])),
            ),
            Formula::mem(ap.sets.pair(taa.clone(), tvv.clone()), sig.clone()),
        )
    );

    // The three eliminations, with the fibre's dependency visible in `snd_mem`.
    let (f, g) = (d.proj.fst_of(ap, tq.clone()), d.proj.snd_of(ap, tq.clone()));
    let hyp = Formula::mem(tq.clone(), sig.clone());
    assert_eq!(
        *inst_all(&ds.fst_mem, std::slice::from_ref(&tq)).unwrap().concl(),
        Formula::imp(hyp.clone(), Formula::mem(f.clone(), Term::apply(dom, vec![])))
    );
    assert_eq!(
        *inst_all(&ds.snd_mem, std::slice::from_ref(&tq)).unwrap().concl(),
        Formula::imp(hyp.clone(), Formula::mem(g.clone(), Term::apply(fib, vec![f.clone()])))
    );
    assert_eq!(
        *inst_all(&ds.eta, std::slice::from_ref(&tq)).unwrap().concl(),
        Formula::imp(hyp, Formula::eq(ap.sets.pair(f, g), tq))
    );

    // Non-vacuous: the fibre at `•` really is `{•}`, and `⟨•,•⟩ ∈ Σ` follows
    // from `• ∈ 1` twice, with no hypothesis left.
    let point = s.point();
    let fib_at = inst_all(&fib_ax, std::slice::from_ref(&point)).expect("fib(•) = {•}");
    assert_eq!(
        *fib_at.concl(),
        Formula::eq(Term::apply(fib, vec![point.clone()]), singleton(up, point.clone()))
    );
    assert_eq!(singleton(up, point.clone()), s.unit(), "{{•}} is 1");
}

/// A two-argument telescope whose second argument's type **mentions the
/// first** — `Σy₀ : α. Σy₁ : {y₀}. 1` — so the thesis's `[π₁p'/y]` substitution
/// is doing real work: `proj_mem[1]` states `π₁π₂q ∈ {π₁q}`.
#[test]
fn the_telescope_is_genuinely_dependent() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let ap: &Apply = &s.ap;
    let up = ap.sets.up;

    let av = env.fresh_var();
    let (b0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀(α) = α");
    let (a2, y0) = (env.fresh_var(), env.fresh_var());
    let (b1, _) = define_abbrev(&mut env, &[a2, y0], &singleton(up, Term::var(y0)))
        .expect("β₁(α,y₀) = {y₀}");

    let tel = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[b0, b1]).expect("telescope");
    assert_eq!(tel.levels.len(), 3);
    assert_eq!(tel.proj_mem.len(), 2);
    assert_eq!(tel.tail_mem.len(), 3);

    let alpha = Term::var(env.fresh_var());
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let ty = tel.ty_of(vec![alpha.clone()]);
    let c0 = Telescope::comp_of(ap, &d.proj, 0, tq.clone());
    let c1 = Telescope::comp_of(ap, &d.proj, 1, tq.clone());
    let hyp = Formula::mem(tq.clone(), ty.clone());

    // `q ∈ T(α) → π₁q ∈ β₀(α)`.
    assert_eq!(
        *inst_all(&tel.proj_mem[0], &[alpha.clone(), tq.clone()]).unwrap().concl(),
        Formula::imp(hyp.clone(), Formula::mem(c0.clone(), Term::apply(b0, vec![alpha.clone()])))
    );
    // `q ∈ T(α) → π₁π₂q ∈ β₁(α, π₁q)` — **the dependency**.
    assert_eq!(
        *inst_all(&tel.proj_mem[1], &[alpha.clone(), tq.clone()]).unwrap().concl(),
        Formula::imp(
            hyp.clone(),
            Formula::mem(c1.clone(), Term::apply(b1, vec![alpha.clone(), c0.clone()]))
        )
    );
    // η: the tuple of the components is the element back again.
    assert_eq!(
        *inst_all(&tel.eta, &[alpha.clone(), tq.clone()]).unwrap().concl(),
        Formula::imp(hyp, Formula::eq(Telescope::tuple_of(s, &[c0, c1]), tq))
    );

    // Introduction, with the two hypotheses right-nested.
    let (u, v) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let intro = inst_all(&tel.intro, &[alpha.clone(), u.clone(), v.clone()]).expect("instantiate");
    assert_eq!(
        *intro.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(u.clone(), Term::apply(b0, vec![alpha.clone()])),
                Formula::mem(v.clone(), Term::apply(b1, vec![alpha.clone(), u.clone()])),
            ),
            Formula::mem(Telescope::tuple_of(s, &[u, v]), ty),
        )
    );
}

/// **The packing is faithful.** With `Σy₀ : α. Σy₁ : α. 1` at `α = finord(2)`,
/// pack the two *different* elements of `α` and read them back: the components
/// of the tuple compute to the two originals, which are different sets. So the
/// telescope is not a one-element set that forgets its arguments.
#[test]
fn the_telescope_remembers_both_arguments() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let ap: &Apply = &s.ap;

    let av = env.fresh_var();
    let (b0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀(α) = α");
    let (a2, y0) = (env.fresh_var(), env.fresh_var());
    let (b1, _) = define_abbrev(&mut env, &[a2, y0], &Term::var(a2)).expect("β₁(α,y₀) = α");
    let tel = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[b0, b1]).expect("telescope");

    // Two distinct elements of `finord(2)`.
    let iso = ISum::new(&mut env, s, 2).expect("iterated sum at depth 2");
    let alpha = finord(s, 2);
    let point = s.point();
    let vals: Vec<Term> = (0..2).map(|i| inj_of(s, i, point.clone())).collect();
    let mems: Vec<Thm> = (0..2)
        .map(|i| {
            Thm::mp(
                &inst_all(&iso.inj_mem[i], &[s.unit(), s.unit(), point.clone()]).unwrap(),
                &s.unit_mem,
            )
            .expect("inj_i(•) ∈ finord(2)")
        })
        .collect();
    for i in 0..2 {
        assert_eq!(*mems[i].concl(), Formula::mem(vals[i].clone(), alpha.clone()));
    }
    assert_ne!(vals[0], vals[1]);

    // The two components of `⟨v₀, ⟨v₁, •⟩⟩` compute back to `v₀` and `v₁`.
    let tuple = Telescope::tuple_of(s, &vals);
    let inner = Telescope::tuple_of(s, &vals[1..]);
    let c0 = inst_all(&d.proj.fst, &[vals[0].clone(), inner.clone()]).unwrap();
    assert_eq!(
        *c0.concl(),
        Formula::eq(Telescope::comp_of(ap, &d.proj, 0, tuple.clone()), vals[0].clone())
    );
    let c1 = {
        let outer_snd = inst_all(&d.proj.snd, &[vals[0].clone(), inner.clone()]).unwrap();
        let lifted = congr(&mut env, &outer_snd, |t| d.proj.fst_of(ap, t));
        let inner_fst = inst_all(&d.proj.fst, &[vals[1].clone(), point.clone()]).unwrap();
        eq_trans(&mut env, &lifted, &inner_fst).expect("compose")
    };
    assert_eq!(
        *c1.concl(),
        Formula::eq(Telescope::comp_of(ap, &d.proj, 1, tuple.clone()), vals[1].clone())
    );
    assert!(closed(c0.concl()) && closed(c1.concl()), "both readbacks must be closed");

    // And the tuple really is in the telescope, with no hypothesis left: the
    // two memberships are transported across the defining equations of `β₀`
    // and `β₁`, which is all the introduction rule asks for.
    let intro = inst_all(&tel.intro, &[alpha.clone(), vals[0].clone(), vals[1].clone()])
        .expect("instantiate");
    let want = intro.concl().as_imp().unwrap().0;
    assert_eq!(
        want,
        Formula::and(
            Formula::mem(vals[0].clone(), Term::apply(b0, vec![alpha.clone()])),
            Formula::mem(vals[1].clone(), Term::apply(b1, vec![alpha.clone(), vals[0].clone()])),
        )
    );
    assert_eq!(
        intro.concl().as_imp().unwrap().1,
        Formula::mem(tuple, tel.ty_of(vec![alpha]))
    );
}

/// The degenerate telescopes. `k = 0` is a nullary constructor: the packed type
/// is `1` and the tuple is `•`, with **no** hypothesis — the thesis's base case
/// `t e ctor ⇒ 1_ℓ` exactly. `k = 1` is a one-argument constructor.
#[test]
fn the_degenerate_telescopes_are_not_special_cases() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;

    let empty = Telescope::new(&mut env, s, &d.proj, &d.pparts, 0, &[]).expect("k = 0");
    assert_eq!(empty.levels.len(), 1);
    assert!(empty.proj_mem.is_empty());
    assert_eq!(*empty.intro.concl(), Formula::mem(s.point(), empty.ty.clone()));
    assert!(closed(empty.intro.concl()), "a nullary constructor's tag is closed");
    // The packed type really is `1`.
    assert_eq!(*empty.base_ax.concl(), Formula::eq(empty.ty.clone(), s.unit()));

    let av = env.fresh_var();
    let (b0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀(α) = α");
    let one = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[b0]).expect("k = 1");
    assert_eq!(one.proj_mem.len(), 1);
    let (alpha, u) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let intro = inst_all(&one.intro, &[alpha.clone(), u.clone()]).expect("instantiate");
    assert_eq!(
        *intro.concl(),
        Formula::imp(
            Formula::mem(u.clone(), Term::apply(b0, vec![alpha.clone()])),
            Formula::mem(s.ap.sets.pair(u, s.point()), one.ty_of(vec![alpha])),
        )
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The reindexing `pull(g,D)` — a function on `β₀(p⃗)`, transported to `Σ(z::γ)`.
// ─────────────────────────────────────────────────────────────────────────────

/// A depth-one telescope over `β₀(α) = α`, and the reindexing over it.
fn depth_one(env: &mut Env, d: &Dev) -> (kernel::FnSym, Telescope, derived::sigma::Reindex, Thm) {
    let av = env.fresh_var();
    let (b0, _) = define_abbrev(env, &[av], &Term::var(av)).expect("β₀(α) = α");
    let tel = Telescope::new(env, &d.s, &d.proj, &d.pparts, 1, &[b0]).expect("k = 1");
    let rx = derived::sigma::Reindex::new(env, &d.s, &d.proj).expect("reindex");
    let app_pair = app_of_pair(env, &d.s.ap).expect("app_of_pair");
    let app_mem =
        derived::ext::funspace_app_mem(env, &d.s.ap, &d.s.prod, &d.s.fs, &app_pair)
            .expect("app_mem");
    (b0, tel, rx, app_mem)
}

/// **A function on the telescope's argument is a function on the telescope**,
/// and it computes back to the function it was pulled from.
///
/// The obligation this exists for: `Ctor::mem` at a function-typed recursive
/// argument wants `fs(Σ(z::γ), ind)` and Lean's field interprets to
/// `fs(⟦γ₀⟧, ind)`.
#[test]
fn a_function_on_the_argument_becomes_a_function_on_the_telescope() {
    let mut env = Env::new();
    let d = build(&mut env);
    let (b0, tel, rx, app_mem) = depth_one(&mut env, &d);
    let s = &d.s;

    let typing = derived::sigma::reindex_in_funspace(&mut env, s, &d.proj, &tel, &rx, &app_mem)
        .expect("reindex_in_funspace");
    let computes =
        derived::sigma::reindex_at_tuple(&mut env, s, &d.proj, &tel, &rx).expect("at_tuple");
    for t in [&typing, &computes] {
        assert!(t.hyps().is_empty(), "unconditional");
    }

    // ── the typing rule, rebuilt at fresh arguments ─────────────────────────
    let (alpha, big_s, g) = (
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
    );
    let beta0 = Term::apply(b0, vec![alpha.clone()]);
    let ty = tel.ty_of(vec![alpha.clone()]);
    let at = inst_all(&typing, &[alpha.clone(), big_s.clone(), g.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(g.clone(), s.fs.of(beta0.clone(), big_s.clone())),
            Formula::mem(rx.of(g.clone(), ty.clone()), s.fs.of(ty.clone(), big_s)),
        ),
        "the typing rule does not say a function on β₀ is a function on Σ(z::γ)"
    );

    // ── it computes, at three distinct arguments ────────────────────────────
    //
    // Three and not two: two would be satisfied by a pulled function that
    // *swapped* its two arguments' values, and the whole content of the
    // reindexing is that the tuple's component comes back out unpermuted.
    let bs: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let mut concls = Vec::new();
    for b in &bs {
        let at = inst_all(&computes, &[alpha.clone(), g.clone(), b.clone()]).expect("instantiate");
        let want = Formula::imp(
            Formula::mem(b.clone(), beta0.clone()),
            Formula::eq(
                s.ap.apply(
                    rx.of(g.clone(), ty.clone()),
                    s.ap.sets.pair(b.clone(), s.point()),
                ),
                s.ap.apply(g.clone(), b.clone()),
            ),
        );
        assert_eq!(*at.concl(), want, "the pulled function does not compute at ⟨b,•⟩");
        concls.push(want);
    }
    assert_ne!(concls[0], concls[1]);
    assert_ne!(concls[1], concls[2]);
    assert_ne!(concls[0], concls[2]);
}

/// The three ways to ask for a reindexing that cannot be stated.
///
/// Depth zero and depth two are the two sides of the `k = 1` guard the module
/// header states — at `k ≥ 2` the map is an uncurrying and the typing needs a
/// `dprod` nest — and a hypothetical `app_mem` is the input that would
/// otherwise ride a `Γ` into a theorem documented `⊢ …`.
#[test]
fn the_reindexing_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let d = build(&mut env);
    let (_, tel, rx, app_mem) = depth_one(&mut env, &d);
    let s = &d.s;

    assert!(
        derived::sigma::reindex_in_funspace(&mut env, s, &d.proj, &tel, &rx, &app_mem).is_some(),
        "the control case must build"
    );

    // 1. Depth zero — a nullary constructor has no argument to pull along.
    let k0 = Telescope::new(&mut env, s, &d.proj, &d.pparts, 0, &[]).expect("k = 0");
    assert!(
        derived::sigma::reindex_in_funspace(&mut env, s, &d.proj, &k0, &rx, &app_mem).is_none(),
        "k = 0"
    );
    assert!(
        derived::sigma::reindex_at_tuple(&mut env, s, &d.proj, &k0, &rx).is_none(),
        "k = 0, at_tuple"
    );

    // 2. Depth two — the uncurrying, which is not built.
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (c0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀");
    let (c1, _) = define_abbrev(&mut env, &[av, bv], &Term::var(av)).expect("β₁");
    let k2 = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[c0, c1]).expect("k = 2");
    assert!(
        derived::sigma::reindex_in_funspace(&mut env, s, &d.proj, &k2, &rx, &app_mem).is_none(),
        "k = 2"
    );

    // 3. A hypothetical `app_mem`.
    let tainted = Thm::mp(
        &derived::ex_falso(app_mem.concl().clone()),
        &Thm::assume(Formula::false_()),
    )
    .expect("ex falso");
    assert!(!tainted.hyps().is_empty() && tainted.concl() == app_mem.concl());
    assert!(
        derived::sigma::reindex_in_funspace(&mut env, s, &d.proj, &tel, &rx, &tainted).is_none(),
        "hypothetical app_mem"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The push `push(t,B)` — a function on `Σ(z::γ)`, transported to its argument.
// ─────────────────────────────────────────────────────────────────────────────

/// The depth-one apparatus of [`depth_one`], plus the push operator and the
/// function extensionality the round trip consumes.
fn depth_one_push(
    env: &mut Env,
    d: &Dev,
) -> (kernel::FnSym, Telescope, derived::sigma::Reindex, Thm, derived::sigma::Push, Thm) {
    let (b0, tel, rx, app_mem) = depth_one(env, d);
    let px = derived::sigma::Push::new(env, &d.s).expect("push");
    let app_pair = app_of_pair(env, &d.s.ap).expect("app_of_pair");
    let fun_ext = derived::ext::funspace_ext(env, &d.s.ap, &d.s.prod, &d.s.fs, &app_pair)
        .expect("funspace_ext");
    (b0, tel, rx, app_mem, px, fun_ext)
}

/// **A function on the telescope is a function on the telescope's argument**,
/// and it computes back to the function it was pushed from.
///
/// The obligation this exists for: `dep_minor` binds a function-typed
/// recursive slot at `fs(Σ(z::γ), W)` and Lean's minor premise binds the same
/// field at a `dprod` over `⟦γ⟧`, so a caller that has bound the first has to
/// produce the second before it can apply the minor premise at all.
#[test]
fn a_function_on_the_telescope_becomes_a_function_on_the_argument() {
    let mut env = Env::new();
    let d = build(&mut env);
    let (b0, tel, _, app_mem, px, _) = depth_one_push(&mut env, &d);
    let s = &d.s;

    let typing =
        derived::sigma::push_in_funspace(&mut env, s, &tel, &px, &app_mem).expect("push_in_funspace");
    for t in [&typing, &px.app] {
        assert!(t.hyps().is_empty(), "unconditional");
    }

    // ── the typing rule, rebuilt at fresh arguments ─────────────────────────
    let (alpha, big_s, t) = (
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
    );
    let beta0 = Term::apply(b0, vec![alpha.clone()]);
    let ty = tel.ty_of(vec![alpha.clone()]);
    let at = inst_all(&typing, &[alpha.clone(), big_s.clone(), t.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(t.clone(), s.fs.of(ty.clone(), big_s.clone())),
            Formula::mem(px.of(t.clone(), beta0.clone()), s.fs.of(beta0.clone(), big_s)),
        ),
        "the typing rule does not say a function on Σ(z::γ) is a function on β₀"
    );

    // ── it computes, at three distinct arguments ────────────────────────────
    //
    // Three and not two, for [`a_function_on_the_argument_becomes_a_function_on_the_telescope`]'s
    // reason: two are satisfied by a push that swaps its two arguments' values.
    let bs: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let mut concls = Vec::new();
    for b in &bs {
        let at = inst_all(&px.app, &[t.clone(), beta0.clone(), b.clone()]).expect("instantiate");
        let want = Formula::imp(
            Formula::mem(b.clone(), beta0.clone()),
            Formula::eq(
                s.ap.apply(px.of(t.clone(), beta0.clone()), b.clone()),
                s.ap.apply(t.clone(), s.ap.sets.pair(b.clone(), s.point())),
            ),
        );
        assert_eq!(*at.concl(), want, "the pushed function does not compute at b");
        concls.push(want);
    }
    assert_ne!(concls[0], concls[1]);
    assert_ne!(concls[1], concls[2]);
    assert_ne!(concls[0], concls[2]);
}

/// **The round trip**: `pull(push(t, β₀(p⃗)), T(p⃗)) = t`.
///
/// This is what reconciles the two sides of the seam. A minor premise's caller
/// binds `t` on `fs(Σ(z::γ), W)`, hands Lean's minor the pushed function, and
/// is left holding a constructor built from the *pulled push* where its
/// obligation names one built from `t`. Without this equation the two terms
/// are unrelated and the ι rule cannot close.
#[test]
fn the_round_trip_returns_the_function_it_started_with() {
    let mut env = Env::new();
    let d = build(&mut env);
    let (b0, tel, rx, app_mem, px, fun_ext) = depth_one_push(&mut env, &d);
    let s = &d.s;

    let trip = derived::sigma::push_pull_roundtrip(
        &mut env, s, &d.proj, &tel, &rx, &px, &app_mem, &fun_ext,
    )
    .expect("push_pull_roundtrip");
    assert!(trip.hyps().is_empty(), "unconditional");
    assert!(closed(trip.concl()), "the round trip is a closed statement");

    let (alpha, big_s, t) = (
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
    );
    let beta0 = Term::apply(b0, vec![alpha.clone()]);
    let ty = tel.ty_of(vec![alpha.clone()]);
    let at = inst_all(&trip, &[alpha.clone(), big_s.clone(), t.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(t.clone(), s.fs.of(ty.clone(), big_s)),
            Formula::eq(rx.of(px.of(t.clone(), beta0), ty), t.clone()),
        ),
        "the round trip does not return the function it started with"
    );
}

/// The four ways to ask for a push that cannot be stated.
///
/// Depth zero and depth two are the two sides of the `k = 1` guard the module
/// header states, and the two hypothetical inputs are the theorems that would
/// otherwise ride a `Γ` into a result documented `⊢ …` — `app_mem`, which the
/// typing rule `mp`s against, and `fun_ext`, which only the round trip reads.
///
/// **Which `return None` each row reaches, measured** — one `eprintln!` above
/// every one of the ten, in a detached worktree, thrown away. As shipped, all
/// four rows reach the check they are named after. Two mutations of the depth
/// guard then say how much of that is the guard's doing:
///
/// * admitting `k = 0` (`len() != 1` → `len() > 1`) fails this test, so the
///   depth-zero row does pin the guard;
/// * admitting `k ≥ 2` (`len() != 1` → `is_empty()`) **fails nothing**. The
///   marker run under that mutation reaches `push_in_funspace`'s
///   `Telescope::intro` shape pin instead: a `k ≥ 2` telescope's `intro` has
///   `k` binders after the outer parameters, so instantiating it at `p⃗` and
///   one `b` leaves a `∀y₁ …` standing and the depth-one shape cannot match.
///   The guard is a *specification pin* at `k ≥ 2` — it states the restriction
///   the header documents rather than letting it fall out of a mismatch deep in
///   the derivation — and the row is honest about the refusal while not being
///   the thing that produces it.
///
/// The round trip's own depth guard survives **both** mutations, for the
/// smaller reason that it delegates to the two typing rules and each of those
/// guards; see the module header.
#[test]
fn the_push_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let d = build(&mut env);
    let (_, tel, rx, app_mem, px, fun_ext) = depth_one_push(&mut env, &d);
    let s = &d.s;

    let trip = |env: &mut Env, tel: &Telescope, am: &Thm, fe: &Thm| {
        derived::sigma::push_pull_roundtrip(env, s, &d.proj, tel, &rx, &px, am, fe)
    };
    assert!(
        derived::sigma::push_in_funspace(&mut env, s, &tel, &px, &app_mem).is_some(),
        "the control case must build"
    );
    assert!(trip(&mut env, &tel, &app_mem, &fun_ext).is_some(), "the control case must build");

    // 1. Depth zero — a nullary constructor has no argument to push onto.
    let k0 = Telescope::new(&mut env, s, &d.proj, &d.pparts, 0, &[]).expect("k = 0");
    assert!(
        derived::sigma::push_in_funspace(&mut env, s, &k0, &px, &app_mem).is_none(),
        "k = 0"
    );
    assert!(trip(&mut env, &k0, &app_mem, &fun_ext).is_none(), "k = 0, round trip");

    // 2. Depth two — the currying, which is not built.
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (c0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀");
    let (c1, _) = define_abbrev(&mut env, &[av, bv], &Term::var(av)).expect("β₁");
    let k2 = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[c0, c1]).expect("k = 2");
    assert!(
        derived::sigma::push_in_funspace(&mut env, s, &k2, &px, &app_mem).is_none(),
        "k = 2"
    );
    assert!(trip(&mut env, &k2, &app_mem, &fun_ext).is_none(), "k = 2, round trip");

    // 3. A hypothetical `app_mem`, and 4. a hypothetical `fun_ext`.
    let hypothetical = |env: &mut Env, t: &Thm| {
        let out = Thm::mp(
            &derived::ex_falso(t.concl().clone()),
            &Thm::assume(Formula::false_()),
        )
        .expect("ex falso");
        assert!(!out.hyps().is_empty() && out.concl() == t.concl());
        let _ = env;
        out
    };
    let bad_am = hypothetical(&mut env, &app_mem);
    let bad_fe = hypothetical(&mut env, &fun_ext);
    assert!(
        derived::sigma::push_in_funspace(&mut env, s, &tel, &px, &bad_am).is_none(),
        "hypothetical app_mem"
    );
    assert!(trip(&mut env, &tel, &bad_am, &fun_ext).is_none(), "hypothetical app_mem, round trip");
    assert!(trip(&mut env, &tel, &app_mem, &bad_fe).is_none(), "hypothetical fun_ext");
}

/// **The λ-graph mini's induction hypothesis needs is `push` itself** — fed to
/// [`derived::ext::lam_in_dprod_n`], `Push`'s own four pieces yield the
/// dependent-product introduction rule at an arbitrary fibre.
///
/// This is a measurement and not a prediction, and it is here because the claim
/// it settles is about another crate's route: `derived`'s ih atom at a
/// function-typed slot is *pointwise* over `Σ(z::γ)`, what Lean's minor premise
/// wants in that position is a member of `⟦∀z:γ, C (f z)⟧` — a `dprod` over
/// `⟦γ⟧` at a **dependent** fibre — and getting from one to the other is a
/// λ-introduction rather than a rewrite. `push_in_funspace` cannot do it, since
/// `dep_minor` gives the ih binder no `fs` typing at all; the existing
/// `lam_in_dprod_n` can, provided the graph it is handed is one whose body is
/// `app(v, ⟨z,•⟩)`. That graph is `push`, which is why [`Push::beta`] is a
/// public field: `lam_in_dprod_n` pins the computation rule **over the body
/// symbol**, not the unfolded form the rest of this file consumes.
#[test]
fn the_push_is_the_lambda_introduction_a_dependent_fibre_needs() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let px = derived::sigma::Push::new(&mut env, s).expect("push");

    // An arbitrary fibre `b(q,z)`, and the `dprod` over it.
    let b = env.declare(2);
    let (img, img_ax) = derived::ext::image_symbol_n(&mut env, b).expect("image_symbol_n");
    let (dprod, dprod_def) =
        derived::ext::dprod_symbol_n(&mut env, &s.ap, &s.fs, img, b).expect("dprod_symbol_n");

    let rule = derived::ext::lam_in_dprod_n(
        &mut env,
        &s.ap,
        &s.fs,
        (px.body, px.graph, &px.beta, &px.lam_in_funspace),
        (b, img, &img_ax, dprod, &dprod_def),
    )
    .expect("push is not the graph lam_in_dprod_n wants");
    assert!(rule.hyps().is_empty(), "unconditional");

    let (v, q, dom, z) = (
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        Term::var(env.fresh_var()),
        env.fresh_var(),
    );
    let tz = Term::var(z);
    let at = inst_all(&rule, &[v.clone(), q.clone(), dom.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), dom.clone()),
                    Formula::mem(
                        Term::apply(px.body, vec![v.clone(), tz.clone()]),
                        Term::apply(b, vec![q.clone(), tz.clone()]),
                    ),
                ),
            ),
            Formula::mem(px.of(v.clone(), dom.clone()), Term::apply(dprod, vec![q, dom])),
        ),
        "push is not the dependent-product introduction rule it is claimed to be"
    );

    // And the body condition is the ih atom's, one `Push::app` step away: the
    // hypothesis speaks of `Q(v,z)`, which is `app(v, ⟨z,•⟩)` — the value the
    // pointwise ih gives at the tuple `Telescope::intro` builds from `z`.
    let unfold = inst_all(&px.body_ax, &[v.clone(), tz.clone()]).expect("instantiate");
    assert_eq!(
        *unfold.concl(),
        Formula::eq(
            Term::apply(px.body, vec![v.clone(), tz.clone()]),
            s.ap.apply(v, s.ap.sets.pair(tz, s.point())),
        )
    );
}
