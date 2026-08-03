//! The fibre family `B` of an inductive declaration — §5.2's `B` component,
//! assembled by iterated `rec₊` from the constructors' recursive-argument
//! counts.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** `B` would satisfy every equation below
//! if it were constant, so [`the_fibres_of_different_counts_are_different`] is
//! what says it is not: `finord(0)`, `finord(1)` and `finord(2)` are pairwise
//! distinct sets, witnessed by their differing elements.

use kernel::{Env, Formula, Term, Thm};

use derived::ext::app_of_pair;
use derived::fibre::{target_of, Fibre};
use derived::isum::ISumSyms;
use derived::point_fun::PointFun;
use derived::proj::Proj;
use derived::sigma::{product_parts, Telescope};
use derived::sums::{Cases, Sums};
use derived::wtype::empty_is_a_function;
use derived::{define_abbrev, inst_all};

struct Dev {
    s: Sums,
    cases: Cases,
    syms: ISumSyms,
    empty_fun: Thm,
    app_pair: Thm,
    proj: Proj,
    pparts: Thm,
}

fn build(env: &mut Env) -> Dev {
    let s = Sums::new(env).expect("sums");
    let cases = Cases::new(env, &s).expect("rec₊");
    let app_pair = app_of_pair(env, &s.ap).expect("app_of_pair");
    let pf = PointFun::over(env, &s, &app_pair).expect("point functions");
    let empty_fun = empty_is_a_function(env, &s).expect("∅ ∈ fs(0,S)");
    let proj = Proj::new(env, &s.ap, &pf).expect("projections");
    let pparts = product_parts(env, &s.ap, &s.prod, &proj).expect("product_parts");
    let mut syms = ISumSyms::new();
    syms.ensure(env, &s, 4).expect("the sum symbols");
    Dev { s, cases, syms, empty_fun, app_pair, proj, pparts }
}

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// The finite ordinals `finord(m⃗)` — what `Inductive::build` hands `Fibre`,
/// spelled here because `Fibre::new` now takes **values** and no longer knows
/// what a count is.
fn fins(d: &Dev, ms: &[usize]) -> Vec<Term> {
    ms.iter().map(|m| d.syms.finord(&d.s, *m).expect("finord")).collect()
}

/// `List`'s fibre family, at the general arity: two constructors, tag summands
/// `1` and `α`, recursive-argument counts `0` and `1`. Everything comes out
/// **unconditional in `α`**, matching what `derived/src/wlist.rs` derives by
/// hand — except that the fibres are `finord(0)` and `finord(1)` rather than
/// `0` and `1`, which is the general shape.
#[test]
fn the_list_shaped_declaration_gets_its_two_fibres() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let alpha = Term::var(env.fresh_var());
    let summands = vec![s.unit(), alpha.clone()];

    let f = Fibre::new(
        &mut env,
        s,
        &d.cases,
        &d.syms,
        &summands,
        &fins(&d, &[0, 1]),
        &d.empty_fun,
        &d.app_pair,
    )
    .expect("the fibre family");

    assert_eq!(f.tags, d.syms.sum(&summands).expect("the sum symbol"));
    assert_eq!(f.values, vec![d.syms.finord(s, 0).expect("finord"), d.syms.finord(s, 1).expect("finord")]);
    assert_eq!(f.target, target_of(s, &f.values));
    // `finord(0)` is the *symbol* `Sum_0()`, whose defining equation unfolds it
    // to `∅` — the point of the symbol layer is that downstream statements no
    // longer mention `∅` at all.
    assert_eq!(
        *d.syms.sum_ax(0).expect("Sum_0's defining equation").concl(),
        Formula::eq(d.syms.sum(&[]).expect("Sum_0"), s.zero()),
        "no recursive arguments means the empty fibre"
    );

    // Both fibres are in the codomain, with no hypothesis.
    for i in 0..2 {
        assert_eq!(*f.value_mem[i].concl(), Formula::mem(f.values[i].clone(), f.target.clone()));
        assert!(closed(f.value_mem[i].concl()));
    }

    // `B ∈ fs(1 + (α + 0), T)`, with `α` free and no hypothesis about it.
    assert!(kernel::thm::debug_locally_closed(f.in_funspace.concl()));
    assert_eq!(
        *f.in_funspace.concl(),
        Formula::mem(f.fam.clone(), s.fs.of(f.tags.clone(), f.target.clone()))
    );

    // The two computation rules.
    let av = env.fresh_var();
    let ta = Term::var(av);
    for (i, summand) in summands.iter().enumerate() {
        let at = inst_all(&f.fibre[i], std::slice::from_ref(&ta)).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(ta.clone(), summand.clone()),
                Formula::eq(
                    s.ap.apply(f.fam.clone(), d.syms.inj(i, ta.clone()).expect("inj")),
                    f.values[i].clone()
                ),
            )
        );
    }

    // The `nil` fibre is reachable **unconditionally**: `• ∈ 1` is a theorem,
    // so `app(B, inj_0 •) = finord(0)` has no hypothesis left — exactly the
    // asymmetry `wlist.rs` records between its two fibres.
    let nil = Thm::mp(
        &inst_all(&f.fibre[0], std::slice::from_ref(&s.point())).unwrap(),
        &s.unit_mem,
    )
    .expect("• ∈ 1");
    assert_eq!(
        *nil.concl(),
        Formula::eq(
            s.ap.apply(f.fam.clone(), d.syms.inj(0, s.point()).expect("inj")),
            d.syms.finord(s, 0).expect("finord")
        )
    );

    // `∀a ∈ tags. app(B,a) ∈ T` — the shape a bound obligation reduces to.
    let bv = env.fresh_var();
    let at = inst_all(&f.values_in_target, std::slice::from_ref(&Term::var(bv))).unwrap();
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(Term::var(bv), f.tags.clone()),
            Formula::mem(s.ap.apply(f.fam.clone(), Term::var(bv)), f.target.clone()),
        )
    );
}

/// **`B` is not constant.** Three constructors branching `0`, `1` and `2`
/// times: the three fibres are pairwise distinct sets, so the three
/// computation rules say three different things.
///
/// Distinctness is cashed rather than asserted syntactically: `finord(1)` has
/// an element and `finord(0) = ∅` has none, and `finord(2)` has two elements
/// that `finord(1)`'s single element cannot both be — all from
/// [`derived::isum::inj_distinct`] and the injections' memberships.
#[test]
fn the_fibres_of_different_counts_are_different() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let summands = vec![s.unit(), s.unit(), s.unit()];

    let f = Fibre::new(
        &mut env,
        s,
        &d.cases,
        &d.syms,
        &summands,
        &fins(&d, &[0, 1, 2]),
        &d.empty_fun,
        &d.app_pair,
    )
    .expect("the fibre family");

    // Syntactically different, which is necessary but not sufficient.
    assert_ne!(f.values[0], f.values[1]);
    assert_ne!(f.values[1], f.values[2]);
    assert_ne!(f.values[0], f.values[2]);

    // `finord(0)` is `Sum_0()`, which unfolds to `∅`.
    assert_eq!(
        *d.syms.sum_ax(0).expect("Sum_0's defining equation").concl(),
        Formula::eq(f.values[0].clone(), s.zero())
    );

    // `finord(2)` has two provably distinct elements; `finord(1)` has one.
    let point = s.point();
    let e0 = Thm::mp(
        &inst_all(d.syms.inj_mem(2, 0).expect("Inj_0 ∈ Sum_2"), &[s.unit(), s.unit(), point.clone()])
            .unwrap(),
        &s.unit_mem,
    )
    .expect("Inj_0 • ∈ finord(2)");
    let e1 = Thm::mp(
        &inst_all(d.syms.inj_mem(2, 1).expect("Inj_1 ∈ Sum_2"), &[s.unit(), s.unit(), point.clone()])
            .unwrap(),
        &s.unit_mem,
    )
    .expect("Inj_1 • ∈ finord(2)");
    assert_eq!(*e0.concl(), Formula::mem(d.syms.inj(0, point.clone()).expect("inj"), f.values[2].clone()));
    assert_eq!(*e1.concl(), Formula::mem(d.syms.inj(1, point.clone()).expect("inj"), f.values[2].clone()));
    let ne = d.syms.inj_distinct(&mut env, s, 0, 1).expect("distinctness");
    let at = inst_all(&ne, &[point.clone(), point.clone()]).unwrap();
    assert_eq!(
        *at.concl(),
        Formula::not(Formula::eq(d.syms.inj(0, point.clone()).expect("inj"), d.syms.inj(1, point.clone()).expect("inj")))
    );
    assert!(closed(e0.concl()) && closed(e1.concl()) && closed(at.concl()));

    // And the three computation rules discharge unconditionally, since every
    // summand is `1`.
    let mut reduced = Vec::new();
    for i in 0..3 {
        let th = Thm::mp(
            &inst_all(&f.fibre[i], std::slice::from_ref(&point)).unwrap(),
            &s.unit_mem,
        )
        .expect("• ∈ 1");
        assert_eq!(
            *th.concl(),
            Formula::eq(
                s.ap.apply(f.fam.clone(), d.syms.inj(i, point.clone()).expect("inj")),
                d.syms.finord(s, i).expect("finord")
            )
        );
        assert!(closed(th.concl()));
        reduced.push(th);
    }
    assert_eq!(reduced.len(), 3);
}

/// The degenerate declaration: no constructors at all (Lean's `Empty`). The tag
/// set is `0`, the family is `∅`, and nothing is claimed about any fibre.
#[test]
fn a_declaration_with_no_constructors_is_not_a_special_case() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;

    let f = Fibre::new(&mut env, s, &d.cases, &d.syms, &[], &[], &d.empty_fun, &d.app_pair)
        .expect("the empty fibre family");
    assert_eq!(f.tags, d.syms.sum(&[]).expect("Sum_0"));
    assert_eq!(f.fam, s.zero());
    assert_eq!(f.target, s.zero());
    assert!(f.fibre.is_empty());
    assert_eq!(
        *f.in_funspace.concl(),
        Formula::mem(s.zero(), s.fs.of(d.syms.sum(&[]).expect("Sum_0"), s.zero()))
    );
    assert!(closed(f.in_funspace.concl()));

    // A mismatched count list is refused rather than guessed at.
    assert!(Fibre::new(&mut env, s, &d.cases, &d.syms, &[s.unit()], &[], &d.empty_fun, &d.app_pair).is_none());
}

/// **The three pieces compose.** `List α` end to end, from declaration data
/// only: two constructors, `nil` with no arguments and `cons` with one
/// non-recursive argument of type `α` and one recursive argument.
///
/// The tag summands are [`Telescope`]s rather than hand-written terms —
/// `nil`'s is the empty telescope `1`, `cons`'s is `Σh : α. 1` — and the fibre
/// family is [`Fibre`] over the counts `(0,1)`. Nothing in this test knows the
/// declaration is `List`; it is the three primitives run at that shape.
#[test]
fn a_list_shaped_declaration_assembles_from_telescopes_and_counts() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let ap = &s.ap;

    // `β₀(α) = α` — the type of `cons`'s head argument.
    let av = env.fresh_var();
    let (b0, _) = define_abbrev(&mut env, &[av], &Term::var(av)).expect("β₀(α) = α");

    let nil_tel = Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[]).expect("nil telescope");
    let cons_tel =
        Telescope::new(&mut env, s, &d.proj, &d.pparts, 1, &[b0]).expect("cons telescope");

    let alpha = Term::var(env.fresh_var());
    let summands = vec![nil_tel.ty_of(vec![alpha.clone()]), cons_tel.ty_of(vec![alpha.clone()])];
    let f = Fibre::new(&mut env, s, &d.cases, &d.syms, &summands, &fins(&d, &[0, 1]), &d.empty_fun, &d.app_pair)
        .expect("the fibre family");

    // `nil`'s tag: the empty telescope's point, injected at index 0. Its
    // membership is unconditional and so is its fibre.
    let nil_tag_arg = inst_all(&nil_tel.intro, std::slice::from_ref(&alpha)).expect("nil intro");
    assert_eq!(*nil_tag_arg.concl(), Formula::mem(s.point(), summands[0].clone()));
    let nil_fibre = Thm::mp(
        &inst_all(&f.fibre[0], std::slice::from_ref(&s.point())).unwrap(),
        &nil_tag_arg,
    )
    .expect("discharge");
    assert_eq!(
        *nil_fibre.concl(),
        Formula::eq(ap.apply(f.fam.clone(), d.syms.inj(0, s.point()).expect("inj")), d.syms.finord(s, 0).expect("finord"))
    );

    // `cons`'s tag: the one-element tuple `⟨h,•⟩`, injected at index 1. Its
    // only hypothesis is `h ∈ β₀(α)`, which is what Lean's
    // `cons : α → List α → List α` states — no hypothesis about `α` itself.
    let hv = env.fresh_var();
    let th = Term::var(hv);
    let tuple = Telescope::tuple_of(s, std::slice::from_ref(&th));
    let cons_tag_arg =
        inst_all(&cons_tel.intro, &[alpha.clone(), th.clone()]).expect("cons intro");
    assert_eq!(
        *cons_tag_arg.concl(),
        Formula::imp(
            Formula::mem(th.clone(), Term::apply(b0, vec![alpha.clone()])),
            Formula::mem(tuple.clone(), summands[1].clone()),
        )
    );
    let cons_fibre = derived::syl(
        &cons_tag_arg,
        &inst_all(&f.fibre[1], std::slice::from_ref(&tuple)).unwrap(),
    )
    .expect("chain");
    assert_eq!(
        *cons_fibre.concl(),
        Formula::imp(
            Formula::mem(th.clone(), Term::apply(b0, vec![alpha.clone()])),
            Formula::eq(ap.apply(f.fam.clone(), d.syms.inj(1, tuple.clone()).expect("inj")), d.syms.finord(s, 1).expect("finord")),
        )
    );

    // The head argument is recoverable from the packed tag — so the tag set
    // sees `α` rather than merely recording that `cons` was used.
    let readback = inst_all(&cons_tel.proj_mem[0], &[alpha.clone(), tuple.clone()]).unwrap();
    assert_eq!(
        *readback.concl(),
        Formula::imp(
            Formula::mem(tuple.clone(), summands[1].clone()),
            Formula::mem(
                Telescope::comp_of(ap, &d.proj, 0, tuple.clone()),
                Term::apply(b0, vec![alpha.clone()])
            ),
        )
    );
    let computes = inst_all(&d.proj.fst, &[th.clone(), s.point()]).unwrap();
    assert_eq!(
        *computes.concl(),
        Formula::eq(Telescope::comp_of(ap, &d.proj, 0, tuple), th)
    );

    // The whole family is still a function into a codomain holding both fibres.
    assert_eq!(
        *f.in_funspace.concl(),
        Formula::mem(f.fam.clone(), s.fs.of(f.tags.clone(), f.target.clone()))
    );
    assert!(kernel::thm::debug_locally_closed(f.in_funspace.concl()));
}

/// **The fibre values are arbitrary sets the declaration names** — which is
/// `SCOPING.md` §12's own phrasing of what `#37` restricts, and this is the
/// test that says it is lifted at this layer.
///
/// The three values are the three shapes the census names, and none of them is
/// produced by a recursive-argument count:
///
/// * a **named** set `Bool()` — `RTree.node : (Bool → RTree) → RTree`. Its
///   fibre is `⟦Bool⟧`, which arrives as a symbol; that it happens to be
///   *provably* `finord(2)` is beside the point, because it is not that term
///   and no count produces it. This is the goal-required blocker's shape.
/// * `1` spelled directly, rather than as `finord(1)` — the degenerate case
///   present in the same declaration as the general ones, so it stands beside
///   them rather than for them.
/// * `finord(0)` — the nullary constructor, unchanged.
///
/// All three in **one** declaration, so a `Fibre` that had quietly kept a
/// uniform shape fails here rather than at the fourth one.
#[test]
fn the_fibre_values_are_arbitrary_named_sets() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let ap = &s.ap;

    // `Bool()` — a *named* closed set, exactly how an interpretation arrives.
    let (bool_sym, bool_ax) =
        derived::define_abbrev(&mut env, &[], &d.syms.finord(s, 2).expect("finord(2)"))
            .expect("an abbreviation");
    let boolean = Term::apply(bool_sym, Vec::new());
    assert!(bool_ax.hyps().is_empty());

    let alpha = Term::var(env.fresh_var());
    let summands = vec![s.unit(), alpha.clone(), s.unit()];
    let values = vec![boolean.clone(), s.unit(), d.syms.finord(s, 0).expect("finord(0)")];
    for m in 0..4 {
        assert_ne!(values[0], d.syms.finord(s, m).expect("finord"), "Bool() is not finord({m})");
    }

    let f = Fibre::new(
        &mut env,
        s,
        &d.cases,
        &d.syms,
        &summands,
        &values,
        &d.empty_fun,
        &d.app_pair,
    )
    .expect("a fibre family at arbitrary named values");

    assert_eq!(f.values, values, "the values are the caller's, verbatim");
    assert_eq!(f.summands, summands);

    // `⊢ B ∈ fs(Sum_3(1, α, 1), T)` — unconditional, and still open in `α`.
    assert_eq!(
        *f.in_funspace.concl(),
        Formula::mem(f.fam.clone(), s.fs.of(f.tags.clone(), f.target.clone()))
    );
    assert!(f.in_funspace.hyps().is_empty());

    for i in 0..3 {
        assert_eq!(
            *f.value_mem[i].concl(),
            Formula::mem(values[i].clone(), f.target.clone()),
            "value_mem[{i}]"
        );
        let av = env.fresh_var();
        let ta = Term::var(av);
        let at = inst_all(&f.fibre[i], std::slice::from_ref(&ta)).expect("at a");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(ta.clone(), summands[i].clone()),
                Formula::eq(
                    ap.apply(f.fam.clone(), d.syms.inj(i, ta).expect("inj")),
                    values[i].clone()
                )
            ),
            "fibre[{i}] computes to the caller's own value"
        );
        assert!(f.fibre[i].hyps().is_empty(), "unconditional at an open summand");
    }
}

/// **The boundary, witnessed rather than asserted: an *open* fibre value is
/// refused.**
///
/// This is the genuinely infinitary shape `α → T α`, whose fibre *is* a
/// parameter — the case `#37` is named after and which has no witness anywhere
/// in `vendor/arena-tests`. It does not fail for a reason anyone predicted: the
/// four theorems never inspect a value, but each branch is a lambda graph over
/// a **constant body symbol** `coᵢ(y) = vᵢ`, and `define_abbrev` refuses a body
/// whose free variables are not among its parameters.
///
/// So the widening this file just received covers **closed** values, which is
/// `RTree` and every declaration whose fibre is a named set, and stops at open
/// ones. The route is named and not guessed: `funcs::lambda_n`,
/// `funcs::beta_conditional_n` and `ext::lam_in_funspace_n` are the arity-`k+1`
/// siblings of the three helpers this file uses, so an open value costs
/// `Fibre::new` a parameter list and those three swaps — not a new construction.
#[test]
fn an_open_fibre_value_is_refused_and_the_reason_is_the_constant_body() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.s;
    let alpha = Term::var(env.fresh_var());

    // The direct cause, on its own: a constant body over an open value.
    let yv = env.fresh_var();
    assert!(
        derived::define_abbrev(&mut env, &[yv], &alpha).is_none(),
        "`coᵢ(y) = α` has a free variable outside its parameter list"
    );
    // …and with `α` in the list it succeeds, which is the whole of the fix.
    assert!(derived::define_abbrev(&mut env, &[yv], &s.unit()).is_some());

    // Hence the fibre family refuses it.
    let summands = vec![s.unit(), s.unit()];
    let values = vec![s.unit(), alpha];
    assert!(
        Fibre::new(
            &mut env,
            s,
            &d.cases,
            &d.syms,
            &summands,
            &values,
            &d.empty_fun,
            &d.app_pair,
        )
        .is_none(),
        "an open fibre value — the infinitary case — is not yet expressible"
    );
}
