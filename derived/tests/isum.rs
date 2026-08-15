//! The iterated binary sum `A₀ + (… + (A_{n-1} + 0))` and its `rec₊`
//! dispatcher — §5.2's tag set and case function at arbitrary arity.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** `n` memberships in one set are all true
//! of a singleton, so [`the_tags_are_pairwise_distinct`] and
//! [`the_dispatcher_separates_its_branches`] are what say the construction
//! discriminates: the three elements of `finord(3)` are pairwise provably
//! distinct with no hypothesis left, and the dispatcher returns a *different*
//! value on each of them.

use kernel::{Env, Formula, Term, Thm};

use derived::ext::app_of_pair;
use derived::isum::{dispatch_of, finord, inj_distinct, inj_of, isum_of, Dispatch, ISum, ISumSyms};
use derived::point_fun::PointFun;
use derived::sums::{Cases, Sums};
use derived::wtype::empty_is_a_function;
use derived::{gen_all, inst_all};

/// A formula with no free variables — an *unconditional*, closed statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

struct Dev {
    s: Sums,
    cases: Cases,
    syms: ISumSyms,
    pf: PointFun,
    empty_fun: Thm,
}

fn build(env: &mut Env) -> Dev {
    let s = Sums::new(env).expect("sums");
    let cases = Cases::new(env, &s).expect("rec₊");
    let app_pair = app_of_pair(env, &s.ap).expect("app_of_pair");
    let pf = PointFun::over(env, &s, &app_pair).expect("point functions");
    let empty_fun = empty_is_a_function(env, &s).expect("∅ ∈ fs(0,S)");
    let mut syms = ISumSyms::new();
    syms.ensure(env, &s, 4).expect("the sum symbols");
    Dev { s, cases, syms, pf, empty_fun }
}

/// The tag set is right-nested and **terminates in `0`**, exactly as
/// `thesis.txt:1789–1791` writes it — that is what makes `inj_i = inr^i ∘ inl`
/// uniform in `i`, and it is where this differs from the hand-written
/// `enums`/`wlist` (and the deleted `wnat`), which collapse the trailing `+ 0`.
#[test]
fn the_tag_set_is_right_nested_and_ends_in_zero() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let (a, b, c) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()), Term::var(env.fresh_var()));

    assert_eq!(isum_of(s, &[]), s.zero());
    assert_eq!(isum_of(s, std::slice::from_ref(&a)), s.sum_of(a.clone(), s.zero()));
    assert_eq!(
        isum_of(s, &[a.clone(), b.clone(), c.clone()]),
        s.sum_of(a.clone(), s.sum_of(b.clone(), s.sum_of(c.clone(), s.zero())))
    );

    // `inj_i = inr^i ∘ inl`, with no special case for the last constructor.
    assert_eq!(inj_of(s, 0, a.clone()), s.inl(a.clone()));
    assert_eq!(inj_of(s, 1, a.clone()), s.inr(s.inl(a.clone())));
    assert_eq!(inj_of(s, 2, a.clone()), s.inr(s.inr(s.inl(a))));

    // `finord(m)` is the same construction with every summand `1`.
    assert_eq!(finord(s, 0), s.zero());
    assert_eq!(finord(s, 2), s.sum_of(s.unit(), s.sum_of(s.unit(), s.zero())));
}

/// `⊢ ∀A₀ ∀A₁ ∀A₂ ∀a. (a ∈ Aᵢ → inj_i(a) ∈ A₀ + (A₁ + (A₂ + 0)))`, for each of
/// the three `i`.
#[test]
fn every_injection_lands_in_the_iterated_sum() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let iso = ISum::new(&mut env, s, 3).expect("iterated sum at depth 3");

    assert_eq!(iso.n, 3);
    let terms: Vec<Term> = iso.vars.iter().map(|v| Term::var(*v)).collect();
    assert_eq!(iso.sum, isum_of(s, &terms));

    let av = env.fresh_var();
    let ta = Term::var(av);
    for i in 0..3 {
        assert!(kernel::thm::debug_locally_closed(iso.inj_mem[i].concl()));
        let at = inst_all(&iso.inj_mem[i], &[terms[0].clone(), terms[1].clone(), terms[2].clone(), ta.clone()])
            .expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(ta.clone(), terms[i].clone()),
                Formula::mem(inj_of(s, i, ta.clone()), iso.sum.clone()),
            )
        );
    }
}

/// `⊢ ∀a ∀b. (inj_i(a) = inj_i(b) → a = b)` — the injections are injective, so
/// a constructor's arguments are recoverable from its tag.
#[test]
fn every_injection_is_injective() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let iso = ISum::new(&mut env, s, 4).expect("iterated sum at depth 4");

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    for i in 0..4 {
        let at = inst_all(&iso.inj_inj[i], &[ta.clone(), tb.clone()]).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::eq(inj_of(s, i, ta.clone()), inj_of(s, i, tb.clone())),
                Formula::eq(ta.clone(), tb.clone()),
            )
        );
        // Not vacuous: the two sides of the antecedent are different terms.
        assert_ne!(inj_of(s, i, ta.clone()), inj_of(s, i, tb.clone()));
    }
}

/// `⊢ ∀a ∀b. ¬(inj_i(a) = inj_j(b))` for every `i ≠ j`, in **both** orders —
/// distinct constructors get distinct tags whatever their arguments are.
///
/// This is the non-vacuity witness for [`every_injection_lands_in_the_iterated_sum`]:
/// without it every membership above could be satisfied by a one-element set.
#[test]
fn the_tags_are_pairwise_distinct() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));

    for i in 0..4 {
        for j in 0..4 {
            if i == j {
                assert!(inj_distinct(&mut env, s, i, j).is_none(), "i = j must be refused");
                continue
            }
            let th = inj_distinct(&mut env, s, i, j).expect("distinctness");
            assert!(kernel::thm::debug_locally_closed(th.concl()));
            let at = inst_all(&th, &[ta.clone(), tb.clone()]).expect("instantiate");
            assert_eq!(
                *at.concl(),
                Formula::not(Formula::eq(inj_of(s, i, ta.clone()), inj_of(s, j, tb.clone())))
            );
        }
    }
}

/// The three elements of `finord(3)` are in it and are pairwise distinct, with
/// **no hypothesis left** — so a three-constructor declaration's fibre of three
/// recursive arguments really does have three of them.
#[test]
fn finord_three_has_exactly_three_visible_elements() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let iso = ISum::new(&mut env, s, 3).expect("iterated sum at depth 3");
    let three = finord(s, 3);
    let point = s.point();

    for i in 0..3 {
        let at = inst_all(
            &iso.inj_mem[i],
            &[s.unit(), s.unit(), s.unit(), point.clone()],
        )
        .expect("instantiate at three copies of 1");
        let mem = Thm::mp(&at, &s.unit_mem).expect("• ∈ 1");
        assert_eq!(*mem.concl(), Formula::mem(inj_of(s, i, point.clone()), three.clone()));
        assert!(closed(mem.concl()), "the membership must be closed");
    }
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        let th = inj_distinct(&mut env, s, i, j).expect("distinctness");
        let at = inst_all(&th, &[point.clone(), point.clone()]).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::not(Formula::eq(inj_of(s, i, point.clone()), inj_of(s, j, point.clone())))
        );
        assert!(closed(at.concl()), "distinctness must be closed");
    }
}

/// A three-branch dispatcher: the term is the right nest, it is a function on
/// the tag set, and each of the three computation rules fires.
///
/// The instance is the identity on `finord(3)` — branch `i` is the one-point
/// graph `{⟨•, inj_i(•)⟩}` — chosen because its three values are provably
/// different sets, which is what makes the three computation rules say three
/// different things.
#[test]
fn the_dispatcher_separates_its_branches() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let three = d.syms.finord(s, 3).expect("finord(3)");
    let point = s.point();

    let summands = vec![s.unit(), s.unit(), s.unit()];
    let values: Vec<Term> =
        (0..3).map(|i| d.syms.inj(i, point.clone()).expect("Inj_i")).collect();
    let branches: Vec<Term> =
        values.iter().map(|v| PointFun::of(s, point.clone(), v.clone())).collect();

    let branch_fs: Vec<Thm> = (0..3)
        .map(|i| {
            let mem = Thm::mp(
                &inst_all(
                    d.syms.inj_mem(3, i).expect("Inj_i ∈ Sum_3"),
                    &[s.unit(), s.unit(), s.unit(), point.clone()],
                )
                .unwrap(),
                &s.unit_mem,
            )
            .expect("Inj_i(•) ∈ finord(3)");
            Thm::mp(
                &inst_all(&d.pf.in_fs, &[point.clone(), values[i].clone(), three.clone()]).unwrap(),
                &mem,
            )
            .expect("the branch is a function into finord(3)")
        })
        .collect();

    let typed: Vec<(Term, Thm)> =
        branches.iter().cloned().zip(branch_fs.iter().cloned()).collect();
    let disp = Dispatch::new(&mut env, s, &d.cases, &d.syms, &summands, &three, &typed, &d.empty_fun)
        .expect("the dispatcher");

    // The term is the right-nested `case` ending at `∅`.
    assert_eq!(disp.fun, dispatch_of(s, &d.cases, &summands, &three, &branches));
    assert_eq!(disp.tags, three);
    assert_eq!(disp.tail_in_funspace.len(), 4);
    assert_eq!(
        *disp.tail_in_funspace[3].concl(),
        Formula::mem(s.zero(), s.fs.of(d.syms.sum(&[]).expect("Sum_0"), three.clone()))
    );

    // ⊢ disp ∈ fs(finord(3), finord(3)), unconditionally.
    assert!(kernel::thm::debug_locally_closed(disp.in_funspace.concl()));
    assert_eq!(
        *disp.in_funspace.concl(),
        Formula::mem(disp.fun.clone(), s.fs.of(three.clone(), three.clone()))
    );
    assert!(closed(disp.in_funspace.concl()));

    // Each computation rule, then discharged at `•` and composed with the
    // one-point graph's own beta rule: `app(disp, inj_i •) = inj_i •`.
    let mut reduced = Vec::new();
    for i in 0..3 {
        let av = env.fresh_var();
        let at = inst_all(&disp.beta[i], std::slice::from_ref(&Term::var(av))).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(Term::var(av), s.unit()),
                Formula::eq(
                    s.ap.apply(disp.fun.clone(), d.syms.inj(i, Term::var(av)).expect("Inj_i")),
                    s.ap.apply(branches[i].clone(), Term::var(av)),
                ),
            )
        );
        let at_point = inst_all(&disp.beta[i], std::slice::from_ref(&point)).expect("at •");
        let eq1 = Thm::mp(&at_point, &s.unit_mem).expect("• ∈ 1");
        let eq2 = inst_all(&d.pf.app, &[point.clone(), values[i].clone()]).expect("point beta");
        let out = derived::eq_trans(&mut env, &eq1, &eq2).expect("compose");
        assert_eq!(
            *out.concl(),
            Formula::eq(
                s.ap.apply(disp.fun.clone(), d.syms.inj(i, point.clone()).expect("Inj_i")),
                values[i].clone()
            )
        );
        assert!(closed(out.concl()), "the reduction must be closed");
        reduced.push(out);
    }

    // The three results are three *different* sets, so the dispatcher is not
    // constant and the three rules are not the same rule.
    assert_ne!(values[0], values[1]);
    assert_ne!(values[0], values[2]);
    assert_ne!(values[1], values[2]);
    assert_eq!(reduced.len(), 3);
}

/// The degenerate arities. `n = 0` is Lean's `Empty`: the tag set is `0`, the
/// dispatcher is `∅`, and there is nothing to compute. `n = 1` is a structure:
/// the tag set is `β₀ + 0` and the single injection is `inl`.
#[test]
fn the_degenerate_arities_are_not_special_cases() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;

    let empty = ISum::new(&mut env, s, 0).expect("depth 0");
    assert_eq!(empty.sum, s.zero());
    assert!(empty.inj_mem.is_empty());

    let target = s.unit();
    let nothing = Dispatch::new(&mut env, s, &d.cases, &d.syms, &[], &target, &[], &d.empty_fun)
        .expect("the empty dispatcher");
    assert_eq!(nothing.fun, s.zero());
    assert_eq!(
        *nothing.in_funspace.concl(),
        Formula::mem(s.zero(), s.fs.of(d.syms.sum(&[]).expect("Sum_0"), target.clone()))
    );
    assert!(nothing.beta.is_empty());

    let one = ISum::new(&mut env, s, 1).expect("depth 1");
    let a = Term::var(one.vars[0]);
    assert_eq!(one.sum, s.sum_of(a.clone(), s.zero()));
    let xv = env.fresh_var();
    let at = inst_all(&one.inj_mem[0], &[a.clone(), Term::var(xv)]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(Term::var(xv), a.clone()),
            Formula::mem(s.inl(Term::var(xv)), s.sum_of(a, s.zero())),
        )
    );
    let _ = gen_all(&[xv], &at);
}

// ─────────────────────────────────────────────────────────────────────────────
// The symbol layer: `Sum_n` and `Inj_i` as real symbols.
// ─────────────────────────────────────────────────────────────────────────────

/// The tag set is one symbol application, not a nest — and its defining
/// equation is still reachable, which is how a failed proof gets unfolded.
#[test]
fn the_sum_symbol_hides_the_nest() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let args: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();

    let sym = d.syms.sum(&args).expect("Sum_3");
    assert_ne!(sym, isum_of(s, &args), "the symbol is not the nest");
    assert_eq!(
        *inst_all(d.syms.sum_ax(3).expect("Sum_3's equation"), &args)
            .expect("instantiate")
            .concl(),
        Formula::eq(sym, isum_of(s, &args)),
        "and it unfolds to exactly the nest"
    );

    // The injection is one node whatever its depth, where `inr^i(inl a)` is `i`.
    let a = Term::var(env.fresh_var());
    for i in 0..4 {
        let t = d.syms.inj(i, a.clone()).expect("Inj_i");
        assert_eq!(
            *inst_all(d.syms.inj_ax(i).expect("Inj_i's equation"), std::slice::from_ref(&a))
                .expect("instantiate")
                .concl(),
            Formula::eq(t, inj_of(s, i, a.clone()))
        );
    }
}

/// **The cache is keyed by `i` alone, not by `(n, i)`.** The *same* `Inj_1`
/// symbol lands in `Sum_2` and in `Sum_4`, which is what keeping the trailing
/// `+ 0` buys: the injection does not know how many summands follow it.
#[test]
fn the_injection_symbol_does_not_depend_on_the_arity() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let a = Term::var(env.fresh_var());
    let one = d.syms.inj(1, a.clone()).expect("Inj_1");

    for n in [2usize, 3, 4] {
        let summands: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
        let mut at = summands.clone();
        at.push(a.clone());
        let mem = inst_all(d.syms.inj_mem(n, 1).expect("membership"), &at).expect("instantiate");
        assert_eq!(
            *mem.concl(),
            Formula::imp(
                Formula::mem(a.clone(), summands[1].clone()),
                Formula::mem(one.clone(), d.syms.sum(&summands).expect("Sum_n")),
            ),
            "one symbol, every arity"
        );
    }

    // Injectivity and distinctness never mention the arity at all.
    let b = Term::var(env.fresh_var());
    assert_eq!(
        *inst_all(d.syms.inj_inj(1).expect("injective"), &[a.clone(), b.clone()])
            .expect("instantiate")
            .concl(),
        Formula::imp(
            Formula::eq(one.clone(), d.syms.inj(1, b.clone()).expect("Inj_1")),
            Formula::eq(a.clone(), b.clone()),
        )
    );
    let apart = d.syms.inj_distinct(&mut env, s, 1, 3).expect("disjoint ranges");
    assert_eq!(
        *inst_all(&apart, &[a.clone(), b.clone()]).expect("instantiate").concl(),
        Formula::not(Formula::eq(one, d.syms.inj(3, b).expect("Inj_3")))
    );
}

/// **No junk**: nothing but the injections is in the sum. The exhaustiveness
/// half, without which every membership theorem would hold of the universe.
#[test]
fn nothing_but_the_injections_is_in_the_sum() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;

    // The expected statement, rebuilt from the kernel's own constructors.
    let expect = |env: &mut Env, syms: &ISumSyms, n: usize| -> (Vec<Term>, Term, Formula) {
        let args: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
        let p = Term::var(env.fresh_var());
        let atoms: Vec<Formula> = (0..n)
            .map(|i| {
                let av = env.fresh_var();
                Formula::exists(
                    av,
                    Formula::and(
                        Formula::mem(Term::var(av), args[i].clone()),
                        Formula::eq(p.clone(), syms.inj(i, Term::var(av)).expect("Inj_i")),
                    ),
                )
            })
            .collect();
        let body = Formula::imp(
            Formula::mem(p.clone(), syms.sum(&args).expect("Sum_n")),
            derived::disj_of(&atoms).unwrap_or_else(Formula::false_),
        );
        (args, p, body)
    };

    for n in 0..=3 {
        let junk = d.syms.no_junk(&mut env, s, n).expect("no junk");
        let (args, p, body) = expect(&mut env, &d.syms, n);
        let mut at = args.clone();
        at.push(p);
        assert_eq!(
            *inst_all(&junk, &at).expect("instantiate").concl(),
            body,
            "no_junk at arity {n}"
        );
        assert!(closed(junk.concl()));
    }

    // **Non-vacuity.** At `n = 0` the statement says `Sum_0()` is empty, and
    // `inj_mem` puts `Inj_0(•)` in `Sum_1(1)` — so the two are different sets
    // and neither statement is about the same one.
    let empty = d.syms.no_junk(&mut env, s, 0).expect("no junk at 0");
    let pv = env.fresh_var();
    assert_eq!(
        *inst_all(&empty, &[Term::var(pv)]).expect("instantiate").concl(),
        Formula::not(Formula::mem(Term::var(pv), d.syms.sum(&[]).expect("Sum_0")))
    );
    let inhabited = Thm::mp(
        &inst_all(d.syms.inj_mem(1, 0).expect("membership"), &[s.unit(), s.point()])
            .expect("instantiate"),
        &s.unit_mem,
    )
    .expect("Inj_0(•) ∈ Sum_1(1)");
    assert_eq!(
        *inhabited.concl(),
        Formula::mem(
            d.syms.inj(0, s.point()).expect("Inj_0"),
            d.syms.sum(&[s.unit()]).expect("Sum_1")
        )
    );
    assert_ne!(d.syms.sum(&[]).expect("Sum_0"), d.syms.sum(&[s.unit()]).expect("Sum_1"));

    // A second request is a cache hit and hands back the same theorem.
    let again = d.syms.no_junk(&mut env, s, 2).expect("no junk again");
    let once = d.syms.no_junk(&mut env, s, 2).expect("no junk again");
    assert_eq!(*again.concl(), *once.concl(), "the cache stores the theorem, not the key");
}

/// **One cache, one `Sums`.** The symbols' theorems are statements about *the*
/// `+` they were derived over, so a cache built over one family must not answer
/// questions about another — and, more sharply, a refused call must leave no
/// trace, because [`ISumSyms::ensure`] keys its progress on how many entries it
/// has and would otherwise count an arity it never derived.
///
/// The sequence is the one that goes wrong when it does not: succeed at arity 2
/// over `s1`, be refused at arity 3 over `s2`, then ask for arity 3 over `s1`
/// again. The last call must really derive it — `inj_mem(3, ·)` present, and
/// `Sum_3`'s defining equation over `s1`'s nest, not `s2`'s.
#[test]
fn the_cache_belongs_to_one_sums_family() {
    let mut env = Env::new();
    let s1 = Sums::new(&mut env).expect("first family");
    let s2 = Sums::new(&mut env).expect("second family");
    assert_ne!(s1.sum, s2.sum, "two `Sums` are two different `+`s");

    let mut syms = ISumSyms::new();
    syms.ensure(&mut env, &s1, 2).expect("arity 2 over the first family");
    assert_eq!(syms.arity(), 2);
    assert!(syms.is_over(&s1) && !syms.is_over(&s2));

    // A call over the second family is refused …
    assert!(syms.ensure(&mut env, &s2, 3).is_none(), "a second family is refused");
    // … and leaves the cache exactly as it was.
    assert_eq!(syms.arity(), 2, "a refused `ensure` caches nothing");
    assert!(syms.sum_ax(3).is_none());
    assert!(syms.inj_mem(3, 0).is_none());

    // Extending over the *original* family derives arity 3 for real.
    syms.ensure(&mut env, &s1, 3).expect("arity 3 over the first family");
    assert_eq!(syms.arity(), 3);
    for i in 0..3 {
        assert!(syms.inj_mem(3, i).is_some(), "inj_mem(3, {i}) was derived");
    }
    assert!(syms.inj_inj(2).is_some());

    // And what it derived is over `s1`: `Sum_3(A⃗) = A₀ + (A₁ + (A₂ + 0))` with
    // `s1`'s sum symbol throughout.
    let args: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    assert_eq!(
        *inst_all(syms.sum_ax(3).expect("Sum_3's equation"), &args)
            .expect("instantiate")
            .concl(),
        Formula::eq(syms.sum(&args).expect("Sum_3"), isum_of(&s1, &args)),
        "the defining equation is over the caller's own family"
    );
    assert_ne!(isum_of(&s1, &args), isum_of(&s2, &args));

    // Every accessor that names a family refuses the foreign one, rather than
    // answering out of this cache.
    assert!(syms.no_junk(&mut env, &s2, 2).is_none());
    assert!(syms.inj_distinct(&mut env, &s2, 0, 1).is_none());
    assert!(syms.finord(&s2, 2).is_none());
    assert!(syms.no_junk(&mut env, &s1, 2).is_some());
}

/// Asking for a property beyond the ensured arity is a `None`, like every other
/// accessor here — not a panic.
#[test]
fn properties_beyond_the_ensured_arity_fail_closed() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert_eq!(d.syms.arity(), 4);
    assert!(d.syms.no_junk(&mut env, &d.s, 5).is_none());
    assert!(d.syms.sum(&vec![d.s.unit(); 5]).is_none());
    assert!(d.syms.inj(4, d.s.point()).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// `Dispatch::under` — branches that are *variables*.
//
// **Three branches, not two.** The `i`-th computation rule walks `i`
// right-branches of the nest before its `inl` step, so `n = 3` is the smallest
// arity that exercises a chain of length 0, of length 1, *and* a composition of
// two chain links under the compound context `H ∧ (a ∈ Aᵢ)`. At `n = 2` a bug
// in composing two links has nothing to fail on.
// ─────────────────────────────────────────────────────────────────────────────

/// The apparatus, three variable summands, a variable codomain and three
/// variable branches, with the hypothesis that each branch is a function.
struct Open {
    summands: Vec<Term>,
    target: Term,
    branches: Vec<Term>,
    atoms: Vec<Formula>,
    h: Formula,
    typed: Vec<(Term, Thm)>,
}

fn open_branches(env: &mut Env, d: &Dev, n: usize) -> Open {
    let s = &d.s;
    let summands: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
    let target = Term::var(env.fresh_var());
    let branches: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
    let atoms: Vec<Formula> = (0..n)
        .map(|i| Formula::mem(branches[i].clone(), s.fs.of(summands[i].clone(), target.clone())))
        .collect();
    let h = derived::conj_of(&atoms).expect("a non-empty hypothesis");
    let typed: Vec<(Term, Thm)> = branches
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, g)| (g, derived::conj_proj(&atoms, i).expect("project")))
        .collect();
    Open { summands, target, branches, atoms, h, typed }
}

/// Every export is `⊢ H → …`, the `n` computation rules included — because
/// `beta_left` cannot compute at a branch without knowing the branch is a
/// function.
#[test]
fn a_dispatcher_over_variable_branches_carries_its_hypothesis_everywhere() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let o = open_branches(&mut env, &d, 3);

    let disp = Dispatch::under(
        &mut env,
        s,
        &d.cases,
        &d.syms,
        &o.summands,
        &o.target,
        &o.h,
        &o.typed,
        &d.empty_fun,
    )
    .expect("the dispatcher under a hypothesis");

    // The **term** is the very one `dispatch_of` builds — the hypothesis
    // changes the statements and nothing else.
    assert_eq!(disp.fun, dispatch_of(s, &d.cases, &o.summands, &o.target, &o.branches));
    assert_eq!(disp.hyp, Some(o.h.clone()));

    assert_eq!(
        *disp.in_funspace.concl(),
        Formula::imp(
            o.h.clone(),
            Formula::mem(
                disp.fun.clone(),
                s.fs.of(d.syms.sum(&o.summands).expect("Sum_3"), o.target.clone())
            )
        )
    );

    assert_eq!(disp.tail_in_funspace.len(), 4);
    for th in &disp.tail_in_funspace {
        let (ante, _) = th.concl().as_imp().expect("every tail typing is conditional");
        assert_eq!(ante, o.h.clone());
    }

    // `⊢ H → ∀a. (a ∈ Aᵢ → app(disp, Inj_i a) = app(gᵢ, a))`, with the `∀`
    // **inside** the hypothesis.
    for i in 0..3 {
        let av = env.fresh_var();
        let ta = Term::var(av);
        let want = Formula::imp(
            o.h.clone(),
            Formula::forall(
                av,
                Formula::imp(
                    Formula::mem(ta.clone(), o.summands[i].clone()),
                    Formula::eq(
                        s.ap.apply(disp.fun.clone(), d.syms.inj(i, ta.clone()).expect("Inj_i")),
                        s.ap.apply(o.branches[i].clone(), ta),
                    ),
                ),
            ),
        );
        assert_eq!(*disp.beta[i].concl(), want, "computation rule {i}");
    }
    assert!(derived::all_unconditional(&[
        &disp.in_funspace,
        &disp.beta[0],
        &disp.beta[1],
        &disp.beta[2]
    ]));

    // Non-vacuity: the three rules name three *different* branches, so this is
    // not one rule stated three times.
    assert_ne!(o.branches[0], o.branches[1]);
    assert_ne!(o.branches[1], o.branches[2]);
    assert_ne!(o.branches[0], o.branches[2]);
}

/// The hypothesis is **checked**, not assumed: a typing stated under the wrong
/// antecedent — or under none — is refused, and so is an unconditional typing
/// handed to the conditional entry point and vice versa.
#[test]
fn the_branch_typings_must_match_the_declared_hypothesis() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let o = open_branches(&mut env, &d, 3);

    // `new` refuses typings that carry `H →`.
    assert!(
        Dispatch::new(&mut env, s, &d.cases, &d.syms, &o.summands, &o.target, &o.typed, &d.empty_fun)
            .is_none(),
        "the unconditional entry point must not accept a conditional typing"
    );

    // `under` refuses a typing stated under a *different* hypothesis — here the
    // conjunction with the first two branches only.
    let wrong = derived::conj_of(&o.atoms[..2]).expect("a shorter hypothesis");
    assert!(
        Dispatch::under(
            &mut env,
            s,
            &d.cases,
            &d.syms,
            &o.summands,
            &o.target,
            &wrong,
            &o.typed,
            &d.empty_fun
        )
        .is_none(),
        "the declared hypothesis must be the one the typings carry"
    );
}

/// `Dispatch::new` **is** `Dispatch::under` at no hypothesis: same code path,
/// same term, and the degenerate arity still comes out unconditional.
#[test]
fn the_unconditional_entry_point_is_the_same_derivation() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;

    let target = s.unit();
    let nothing = Dispatch::new(&mut env, s, &d.cases, &d.syms, &[], &target, &[], &d.empty_fun)
        .expect("the empty dispatcher");
    assert_eq!(nothing.hyp, None);
    assert!(closed(nothing.in_funspace.concl()));
    assert!(nothing.in_funspace.concl().as_imp().is_none(), "no antecedent at n = 0");
}
