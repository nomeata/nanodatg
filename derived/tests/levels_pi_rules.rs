//! **Dependent** Π-formation at a variable level — the `dprod` twin of the
//! flagship, checked over the tower's own chain and **computed at ground
//! instances on both sides of the split** ([`derived::levels::pi_rules`]).
//!
//! The assembly mirrors `levels_rules.rs` (rebuild [`Rec`] from the tower's
//! own `Apply` and `Peano`) plus the `Π`-rule stack of `dprod_n.rs`
//! (`DProdN::new`, the Replacement port, `dprod_in_universe_pair_n`). The
//! shape test runs at prefix length **k = 2 with distinct probe variables**,
//! so a prefix-dropping or prefix-reordering bug cannot pass; the two ground
//! tests run at k = 1 over the base `A := ∅`, whose fibres conjunct is
//! discharged vacuously through `ex_falso` — the one discharge shape
//! available for an *opaque* fibre symbol, and enough, because what these
//! tests pin is the conditional's computation, not the fibre's.
//!
//! # Mutation record
//!
//! Two deliberate breaks were run against this file and reverted, each
//! turning it red:
//!
//! * raising the fibres from `srt(u)` instead of `srt(v)` (`srt_v_sub` built
//!   over `u_sub`) — the pointwise chain no longer composes with the
//!   hypothesis and `pi_rules` itself returns `None`, so every test dies at
//!   `expect("pi_rules")`;
//! * instantiating the `Π` rule at `c := tq` instead of `c := app(lvl,q)` —
//!   the raised conjuncts are about `U(app(lvl,q))` and the rule instance
//!   about `U(q)`, `Thm::mp` refuses, and `pi_rules` returns `None` likewise.

use derived::ext::{
    dprod_in_universe_of_n, dprod_in_universe_pair_n, DProdN, UniverseParts,
};
use derived::levels::ite0::{ite0, Ite0};
use derived::levels::order::{order, Order};
use derived::levels::pi_rules::{pi_rules_minting, PiRules};
use derived::levels::rules::rules;
use derived::levels::srt::{srt, Srt};
use derived::levels::utower::{utower, UTower};
use derived::recursion::{app_of_graph, Rec};
use derived::tower::Tower;
use derived::universe as uni;
use kernel::{Env, FnSym, Formula, Term, Thm};

/// The one-chain assembly every test shares, at a caller-chosen fibre arity.
struct Setup {
    t: Tower,
    r: Rec,
    i: Ite0,
    ut: UTower,
    s: Srt,
    o: Order,
    dp: DProdN,
    pr: PiRules,
    pair: Thm,
}

fn setup(env: &mut Env, fibre_arity: u32) -> Setup {
    let t = Tower::new(env).expect("Tower");
    let lu = t.space.lu;
    let lu_ax = t.space.lu_ax.clone();
    let (pow, pow_ax) = (t.space.pow, t.space.pow_ax.clone());
    let ap = t.sums.ap.clone();
    let peano = t.peano.clone();
    let app_of_graph = app_of_graph(env, &ap).expect("app_of_graph");
    let r = Rec { ap, peano, app_of_graph };
    let i = ite0(env, &r.ap).expect("ite0");
    let ut = utower(env, &r, lu, &lu_ax, pow, &pow_ax).expect("utower");
    let s = srt(env, &r, &i, &ut, &t).expect("srt");
    let o = order(env, &r).expect("order");
    let ru = rules(env, &r, &i, &o, &ut, &s, &t).expect("rules");

    // The Π-rule stack, exactly as `dprod_n.rs` assembles it.
    let b = env.declare(fibre_arity);
    let dp = DProdN::new(env, &t.sums.ap, &t.sums.fs, b).expect("DProdN::new");
    let ur = uni::universe_replacement_n(env, &t.space.empty_ax, dp.img, &dp.img_ax, b)
        .expect("universe_replacement_n");
    let replacement =
        uni::least_universe_replacement_n(env, t.space.lu, &t.space.lu_ax, dp.img, b, &ur)
            .expect("least_universe_replacement_n");
    let u = UniverseParts {
        lu: t.space.lu,
        c2: &t.space.c2,
        fs_in_u: &t.funspace_of,
        union: &t.union,
        bin_union: &t.bin_union,
    };
    let general = dprod_in_universe_of_n(env, &t.sums.ap, &t.sums.fs, &dp.fibre(&replacement), &u)
        .expect("dprod_in_universe_of_n");
    let pair = dprod_in_universe_pair_n(env, &t.sums.ap, &dp.fibre(&replacement), &u, &general)
        .expect("dprod_in_universe_pair_n");

    let pr = pi_rules_minting(env, &r, &i, &o, &ut, &s, &ru, &t, &dp, &pair).expect("pi_rules");
    Setup { t, r, i, ut, s, o, dp, pr, pair }
}

/// `x ∈ a` and `a = b` give `x ∈ b`.
fn set_rw(env: &mut Env, eq: &Thm, mem: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("set_rw: not an equation");
    let (x, _) = mem.concl().as_mem().expect("set_rw: not a membership");
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, w, Formula::mem(x, Term::var(w)));
    Thm::mp(&Thm::mp(&leib, eq).expect("set_rw"), mem).expect("set_rw")
}

/// `a ∈ y` and `a = b` give `b ∈ y`.
fn elt_rw(env: &mut Env, eq: &Thm, mem: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("elt_rw: not an equation");
    let (_, y) = mem.concl().as_mem().expect("elt_rw: not a membership");
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, w, Formula::mem(Term::var(w), y));
    Thm::mp(&Thm::mp(&leib, eq).expect("elt_rw"), mem).expect("elt_rw")
}

/// `a = b` gives `srt(a) = srt(b)`.
fn srt_congr(env: &mut Env, s: &Srt, eq: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("srt_congr: not an equation");
    let w = env.fresh_var();
    let phi = Formula::eq(s.at(a.clone()), s.at(Term::var(w)));
    let leib = Thm::eq_leibniz(a.clone(), b, w, phi);
    Thm::mp(&Thm::mp(&leib, eq).expect("srt_congr"), &Thm::eq_refl(s.at(a)))
        .expect("srt_congr")
}

/// `⊢ srt(1̄) = U(ω)` — the `levels_rules.rs` route.
fn srt1_eq_uw(env: &mut Env, se: &Setup) -> Thm {
    let zero = se.r.zero();
    let omega = se.r.omega();
    let lu = se.t.space.lu;
    let e1 = Thm::mp(
        &derived::inst_all(&se.s.at_succ, std::slice::from_ref(&zero)).expect("at_succ at ∅"),
        &se.r.core().zero_mem,
    )
    .expect("srt(1̄) = U(app(lvl,∅))");
    let l0 = se.ut.at(zero);
    let ul0 = Term::apply(lu, vec![l0.clone()]);
    let w = env.fresh_var();
    let congr = derived::mpd_const(
        &Thm::eq_leibniz(
            l0,
            omega,
            w,
            Formula::eq(ul0.clone(), Term::apply(lu, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(ul0),
    )
    .expect("congruence");
    let u_eq = Thm::mp(&congr, &se.ut.base).expect("U(app(lvl,∅)) = U(ω)");
    derived::eq_trans(env, &e1, &u_eq).expect("srt(1̄) = U(ω)")
}

/// `⊢ ∀x. (x ∈ ∅ → b(q⃗,x) ∈ s)` — the fibres conjunct over the empty base,
/// discharged vacuously: `x ∈ ∅` is refuted by the empty-set axiom and
/// `ex_falso` supplies the consequent.
fn vacuous_fibres(env: &mut Env, r: &Rec, b: FnSym, qts: &[Term], s: &Term) -> Thm {
    let xv = env.fresh_var();
    let mut args = qts.to_vec();
    args.push(Term::var(xv));
    let want = Formula::mem(Term::apply(b, args), s.clone());
    let na = derived::inst_all(&r.core().empty_ax, std::slice::from_ref(&Term::var(xv)))
        .expect("empty_ax");
    let out = derived::syl(&na, &derived::ex_falso(want)).expect("vacuous fibre");
    Thm::gen(xv, &out)
}

/// Every exported conclusion, pinned against a rebuild from the kernel's own
/// constructors — at prefix length **2**, with the two prefix slots and the
/// base distinct variables, so prefix dropping *and* prefix reordering both
/// fail here (three atoms; two pass under either bug).
#[test]
fn the_dependent_rule_kit_has_the_advertised_shape() {
    let mut env = Env::new();
    let se = setup(&mut env, 3); // k = 2
    let (r, s, o, i, pr, dp) = (&se.r, &se.s, &se.o, &se.i, &se.pr, &se.dp);
    let omega = r.omega();
    let zero = r.zero();
    let unit = se.t.sums.unit();

    for thm in [&pr.cndd_ax, &pr.pi_imax_dep] {
        assert!(thm.hyps().is_empty(), "nothing is assumed");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // `⊢ ∀q1 ∀q2 ∀A ∀z. (z ∈ cndd(q1,q2,A) ↔ (z ∈ 1 ∧ ∀x. (x ∈ A → • ∈ b(q1,q2,x))))`.
    let (q1, q2, a, z, x) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tq1, tq2, ta, tz) = (Term::var(q1), Term::var(q2), Term::var(a), Term::var(z));
    let cndd_t = Term::apply(pr.cndd, vec![tq1.clone(), tq2.clone(), ta.clone()]);
    let b_x = Term::apply(dp.b, vec![tq1.clone(), tq2.clone(), Term::var(x)]);
    let phi = Formula::forall(
        x,
        Formula::imp(
            Formula::mem(Term::var(x), ta.clone()),
            Formula::mem(se.t.sums.point(), b_x),
        ),
    );
    assert_eq!(
        *pr.cndd_ax.concl(),
        Formula::forall(
            q1,
            Formula::forall(
                q2,
                Formula::forall(
                    a,
                    Formula::forall(
                        z,
                        Formula::iff(
                            Formula::mem(tz.clone(), cndd_t),
                            Formula::and(Formula::mem(tz, unit), phi),
                        ),
                    ),
                ),
            ),
        ),
        "cndd_ax has the wrong shape"
    );

    // The dependent flagship, rebuilt in full.
    let (q1b, q2b, u, v, a2) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tq1b, tq2b, tu, tv, ta2) = (
        Term::var(q1b),
        Term::var(q2b),
        Term::var(u),
        Term::var(v),
        Term::var(a2),
    );
    let qts = [tq1b.clone(), tq2b.clone()];
    let fib = uni::fibres_in_n(&mut env, dp.b, &qts, &ta2, &s.at(tv.clone()));
    let kk = Formula::and(
        Formula::and(
            Formula::mem(tu.clone(), omega.clone()),
            Formula::mem(tv.clone(), omega.clone()),
        ),
        Formula::and(Formula::mem(ta2.clone(), s.at(tu.clone())), fib),
    );
    let cndd_t2 = Term::apply(pr.cndd, vec![tq1b.clone(), tq2b.clone(), ta2.clone()]);
    let dp_t = dp.of(&qts, ta2.clone());
    let imax_t = i.at(tv.clone(), zero.clone(), o.max(tu, tv.clone()));
    assert_eq!(
        *pr.pi_imax_dep.concl(),
        Formula::forall(
            q1b,
            Formula::forall(
                q2b,
                Formula::forall(
                    u,
                    Formula::forall(
                        v,
                        Formula::forall(
                            a2,
                            Formula::imp(
                                kk,
                                Formula::mem(i.at(tv, cndd_t2, dp_t), s.at(imax_t)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        "pi_imax_dep has the wrong shape"
    );
}

/// **Ground instantiation, Prop side**: the dependent flagship at
/// `q := ω, u := ∅, v := ∅, A := ∅` — antecedents discharged (the fibres
/// vacuously), the conclusion computed by the `when_zero` equations down to
/// exactly `⊢ cndd(ω,∅) ∈ U₀`.
#[test]
fn pi_imax_dep_computes_on_the_prop_side() {
    let mut env = Env::new();
    let se = setup(&mut env, 2); // k = 1
    let (r, s, o, i, pr, dp) = (&se.r, &se.s, &se.o, &se.i, &se.pr, &se.dp);
    let zero = r.zero();
    let omega = r.omega();
    let zero_om = &r.core().zero_mem;

    let qts = [omega.clone()];
    let cndd_t = Term::apply(pr.cndd, vec![omega.clone(), zero.clone()]);
    let dp_t = dp.of(&qts, zero.clone());
    let max00 = o.max(zero.clone(), zero.clone());
    let imax00 = i.at(zero.clone(), zero.clone(), max00.clone());

    // The base: `∅ ∈ srt(∅)` is `∅ ∈ U₀` carried through the reversed
    // `at_zero`. The fibres: vacuous over the empty base.
    let at_zero_rev = derived::eq_symm(&mut env, &s.at_zero).expect("U₀ = srt(∅)");
    let base = set_rw(&mut env, &at_zero_rev, &se.t.false_in_u0);
    let fib = vacuous_fibres(&mut env, r, dp.b, &qts, &s.at(zero.clone()));

    let at = derived::inst_all(
        &pr.pi_imax_dep,
        &[omega.clone(), zero.clone(), zero.clone(), zero.clone()],
    )
    .expect("pi_imax_dep at (ω,∅,∅,∅)");
    let concl = Thm::mp(
        &at,
        &derived::and_intro(
            &derived::and_intro(zero_om, zero_om),
            &derived::and_intro(&base, &fib),
        ),
    )
    .expect("antecedents discharged");
    assert_eq!(
        *concl.concl(),
        Formula::mem(i.at(zero.clone(), cndd_t.clone(), dp_t.clone()), s.at(imax00.clone())),
        "the instantiated conclusion has the wrong shape"
    );

    // Compute both conditionals at the true guard `∅ = ∅`.
    let refl0 = Thm::eq_refl(zero.clone());
    let eq_term = Thm::mp(
        &derived::inst_all(&i.when_zero, &[zero.clone(), cndd_t.clone(), dp_t])
            .expect("when_zero"),
        &refl0,
    )
    .expect("ite0(∅, cndd, dprod) = cndd(ω,∅)");
    let eq_imax = Thm::mp(
        &derived::inst_all(&i.when_zero, &[zero.clone(), zero.clone(), max00])
            .expect("when_zero"),
        &refl0,
    )
    .expect("imax(∅,∅) = ∅");
    let srt_eq = srt_congr(&mut env, s, &eq_imax);
    let srt_u0 = derived::eq_trans(&mut env, &srt_eq, &s.at_zero).expect("srt(imax(∅,∅)) = U₀");

    let cndd_in_srt = elt_rw(&mut env, &eq_term, &concl);
    let out = set_rw(&mut env, &srt_u0, &cndd_in_srt);
    assert_eq!(
        *out.concl(),
        Formula::mem(cndd_t, se.t.u0()),
        "the Prop clause did not compute to cndd(ω,∅) ∈ U₀"
    );
    assert!(out.hyps().is_empty());
}

/// **Ground instantiation, Type side**: the dependent flagship at
/// `q := ω, u := 1̄, v := 1̄, A := ∅` — the guard refuted by `succ_ne_zero`,
/// `1̄ ∪ 1̄` collapsed by `max_absorb`, and the conclusion computed down to
/// exactly `⊢ dprod(ω,∅) ∈ U(ω)`, the rung pinned as the existing tower's
/// `U₁`. Together with the Prop-side test this pins that BOTH branches of the
/// one dependent theorem compute to the right ground facts.
#[test]
fn pi_imax_dep_computes_on_the_type_side() {
    let mut env = Env::new();
    let se = setup(&mut env, 2); // k = 1
    let (r, s, o, i, pr, dp) = (&se.r, &se.s, &se.o, &se.i, &se.pr, &se.dp);
    let zero = r.zero();
    let omega = r.omega();
    let one = r.succ_of(zero.clone());
    let zero_om = &r.core().zero_mem;

    let one_om = Thm::mp(
        &derived::inst_all(&r.core().succ_closed, std::slice::from_ref(&zero))
            .expect("succ_closed"),
        zero_om,
    )
    .expect("1̄ ∈ ω");

    let qts = [omega.clone()];
    let cndd_t = Term::apply(pr.cndd, vec![omega.clone(), zero.clone()]);
    let dp_t = dp.of(&qts, zero.clone());
    let max11 = o.max(one.clone(), one.clone());
    let imax11 = i.at(one.clone(), zero.clone(), max11.clone());

    // The base: `∅ ∈ srt(1̄)` — `∅ ∈ U₀ ∈ U(ω)`, closed by transitivity and
    // read back through `srt(1̄) = U(ω)`. The fibres: vacuous again.
    let u0_in_uw = derived::inst_all(&se.t.u0_in, std::slice::from_ref(&omega)).expect("u0_in");
    let all_z = Thm::mp(
        &derived::inst_all(&se.t.transitive, &[omega.clone(), se.t.u0()]).expect("transitive"),
        &u0_in_uw,
    )
    .expect("U₀'s elements are in U(ω)");
    let zero_in_uw = Thm::mp(
        &derived::inst_all(&all_z, std::slice::from_ref(&zero)).expect("at ∅"),
        &se.t.false_in_u0,
    )
    .expect("∅ ∈ U(ω)");
    let srt1_uw = srt1_eq_uw(&mut env, &se);
    let uw_srt1 = derived::eq_symm(&mut env, &srt1_uw).expect("U(ω) = srt(1̄)");
    let base = set_rw(&mut env, &uw_srt1, &zero_in_uw);
    let fib = vacuous_fibres(&mut env, r, dp.b, &qts, &s.at(one.clone()));

    let at = derived::inst_all(
        &pr.pi_imax_dep,
        &[omega.clone(), one.clone(), one.clone(), zero.clone()],
    )
    .expect("pi_imax_dep at (ω,1̄,1̄,∅)");
    let concl = Thm::mp(
        &at,
        &derived::and_intro(
            &derived::and_intro(&one_om, &one_om),
            &derived::and_intro(&base, &fib),
        ),
    )
    .expect("antecedents discharged");
    assert_eq!(
        *concl.concl(),
        Formula::mem(i.at(one.clone(), cndd_t.clone(), dp_t.clone()), s.at(imax11.clone())),
        "the instantiated conclusion has the wrong shape"
    );

    // The guard is refuted, so both conditionals take the nonzero branch.
    let ne1 = Thm::mp(
        &derived::inst_all(&r.peano.succ_ne_zero, std::slice::from_ref(&zero))
            .expect("succ_ne_zero"),
        zero_om,
    )
    .expect("¬(1̄ = ∅)");
    let eq_term = Thm::mp(
        &derived::inst_all(&i.when_nonzero, &[one.clone(), cndd_t, dp_t.clone()])
            .expect("when_nonzero"),
        &ne1,
    )
    .expect("ite0(1̄, cndd, dprod) = dprod(ω,∅)");
    let eq_imax = Thm::mp(
        &derived::inst_all(&i.when_nonzero, &[one.clone(), zero, max11.clone()])
            .expect("when_nonzero"),
        &ne1,
    )
    .expect("imax(1̄,1̄) = 1̄ ∪ 1̄");

    let absorb = Thm::mp(
        &derived::inst_all(&o.max_absorb, &[one.clone(), one.clone()]).expect("max_absorb"),
        &derived::and_intro(&one_om, &one_om),
    )
    .expect("(1̄∪1̄ = 1̄) ∨ (1̄∪1̄ = 1̄)");
    let collapse = Thm::mp(&derived::clavius(Formula::eq(max11, one)), &absorb)
        .expect("1̄ ∪ 1̄ = 1̄");

    let imax_is_one = derived::eq_trans(&mut env, &eq_imax, &collapse).expect("imax(1̄,1̄) = 1̄");
    let srt_eq = srt_congr(&mut env, s, &imax_is_one);
    let full = derived::eq_trans(&mut env, &srt_eq, &srt1_uw).expect("srt(imax(1̄,1̄)) = U(ω)");

    let dp_in_srt = elt_rw(&mut env, &eq_term, &concl);
    let out = set_rw(&mut env, &full, &dp_in_srt);
    let uw = Term::apply(se.t.space.lu, vec![omega]);
    assert_eq!(uw, se.t.u(1), "U(ω) is not the tower's U₁");
    assert_eq!(
        *out.concl(),
        Formula::mem(dp_t, uw),
        "the Type clause did not compute to dprod(ω,∅) ∈ U(ω)"
    );
    assert!(out.hyps().is_empty());
}

/// A stack over a **different fibre** is refused: the `pair` theorem handed
/// in must be about the very `DProdN` the kit is being built for.
#[test]
fn a_foreign_pair_theorem_is_refused() {
    let mut env = Env::new();
    let se = setup(&mut env, 2);

    // A second, unrelated fibre stack over the same tower.
    let b2 = env.declare(2);
    let dp2 = DProdN::new(&mut env, &se.t.sums.ap, &se.t.sums.fs, b2).expect("DProdN::new");
    let ur2 = uni::universe_replacement_n(&mut env, &se.t.space.empty_ax, dp2.img, &dp2.img_ax, b2)
        .expect("universe_replacement_n");
    let repl2 = uni::least_universe_replacement_n(
        &mut env,
        se.t.space.lu,
        &se.t.space.lu_ax,
        dp2.img,
        b2,
        &ur2,
    )
    .expect("least_universe_replacement_n");
    let u = UniverseParts {
        lu: se.t.space.lu,
        c2: &se.t.space.c2,
        fs_in_u: &se.t.funspace_of,
        union: &se.t.union,
        bin_union: &se.t.bin_union,
    };
    let general2 =
        dprod_in_universe_of_n(&mut env, &se.t.sums.ap, &se.t.sums.fs, &dp2.fibre(&repl2), &u)
            .expect("dprod_in_universe_of_n");
    let pair2 =
        dprod_in_universe_pair_n(&mut env, &se.t.sums.ap, &dp2.fibre(&repl2), &u, &general2)
            .expect("dprod_in_universe_pair_n");

    // `pair2` is a perfectly good theorem — about the *other* product. The
    // probe check must refuse the mix.
    let lu = se.t.space.lu;
    let lu_ax = se.t.space.lu_ax.clone();
    let (pow, pow_ax) = (se.t.space.pow, se.t.space.pow_ax.clone());
    let ap = se.t.sums.ap.clone();
    let peano = se.t.peano.clone();
    let app_of_graph = app_of_graph(&mut env, &ap).expect("app_of_graph");
    let r = Rec { ap, peano, app_of_graph };
    let i2 = ite0(&mut env, &r.ap).expect("ite0");
    let ut2 = utower(&mut env, &r, lu, &lu_ax, pow, &pow_ax).expect("utower");
    let s2 = srt(&mut env, &r, &i2, &ut2, &se.t).expect("srt");
    let o2 = order(&mut env, &r).expect("order");
    let ru2 = rules(&mut env, &r, &i2, &o2, &ut2, &s2, &se.t).expect("rules");
    assert!(
        pi_rules_minting(&mut env, &r, &i2, &o2, &ut2, &s2, &ru2, &se.t, &se.dp, &pair2).is_none(),
        "a pair theorem for another fibre stack must be refused"
    );
}

/// **A `cndd` pair over a foreign fibre is refused by the probe.** The lazy
/// consumer hands `pi_rules` the singleton it already interpreted terms with;
/// this is what stops a mismatched pair — a perfectly good conditional
/// singleton, about the *other* fibre — from being described as this stack's
/// Prop clause. Two fibres are the atoms: the probe compares `φ` built from
/// `dp.b`, and with one fibre in the environment there is nothing unequal to
/// hand it.
#[test]
fn a_foreign_cndd_pair_is_refused() {
    use derived::levels::pi_rules::{pi_body_dep, pi_rules};
    let mut env = Env::new();
    let se = setup(&mut env, 2);

    // A second fibre of the same arity, and an honest singleton over it.
    let b2 = env.declare(2);
    let q = env.fresh_var();
    let a = env.fresh_var();
    let phi2 = pi_body_dep(&mut env, &se.t.sums, b2, &[Term::var(q)], &Term::var(a));
    let (cndd2, cndd2_ax) =
        derived::prop::conditional_singleton(&mut env, &se.t.sums, &[q, a], &phi2)
            .expect("conditional_singleton");

    // The chain, rebuilt as in the sibling foreign-pair test.
    let lu = se.t.space.lu;
    let lu_ax = se.t.space.lu_ax.clone();
    let (pow, pow_ax) = (se.t.space.pow, se.t.space.pow_ax.clone());
    let ap = se.t.sums.ap.clone();
    let peano = se.t.peano.clone();
    let app_of_graph = app_of_graph(&mut env, &ap).expect("app_of_graph");
    let r = Rec { ap, peano, app_of_graph };
    let i2 = ite0(&mut env, &r.ap).expect("ite0");
    let ut2 = utower(&mut env, &r, lu, &lu_ax, pow, &pow_ax).expect("utower");
    let s2 = srt(&mut env, &r, &i2, &ut2, &se.t).expect("srt");
    let o2 = order(&mut env, &r).expect("order");
    let ru2 = rules(&mut env, &r, &i2, &o2, &ut2, &s2, &se.t).expect("rules");
    assert!(
        pi_rules(
            &mut env, &r, &i2, &o2, &ut2, &s2, &ru2, &se.t, &se.dp, &se.pair, cndd2, &cndd2_ax
        )
        .is_none(),
        "a cndd pair over another fibre must be refused by the probe"
    );
    // …and the same pair over the right fibre goes through, so the refusal
    // above is the probe and not some incidental mismatch.
    let q3 = env.fresh_var();
    let a3 = env.fresh_var();
    let phi3 = pi_body_dep(&mut env, &se.t.sums, se.dp.b, &[Term::var(q3)], &Term::var(a3));
    let (cndd3, cndd3_ax) =
        derived::prop::conditional_singleton(&mut env, &se.t.sums, &[q3, a3], &phi3)
            .expect("conditional_singleton");
    assert!(
        pi_rules(
            &mut env, &r, &i2, &o2, &ut2, &s2, &ru2, &se.t, &se.dp, &se.pair, cndd3, &cndd3_ax
        )
        .is_some(),
        "the same pair over this fibre must be accepted"
    );
}
