//! The rule kit at a variable level — Π-formation at `imax` with the
//! Prop/Type split as an `ite0` inside the term — checked over the tower's own
//! chain, and **computed at ground instances on both sides of the split**.
//!
//! The assembly mirrors `levels_srt.rs` (rebuild [`Rec`] from the tower's own
//! `Apply` and `Peano`, so every symbol is the tower's) plus [`Order`] and
//! [`rules`]. The two ground-instantiation tests are the point of the file:
//! *one* quantified theorem, instantiated once with `v = ∅` and once with
//! `v = 1̄`, computes to `⊢ cnd(1,1) ∈ U₀` (the Prop clause) and
//! `⊢ fs(ω,ω) ∈ U(ω)` (the Type clause) respectively — the if-then-else
//! genuinely carries the split (`LEVELPOLY.md` §1.4).

use derived::levels::ite0::{ite0, Ite0};
use derived::levels::order::{order, Order};
use derived::levels::rules::{rules, Rules};
use derived::levels::srt::{srt, Srt};
use derived::levels::utower::{utower, UTower};
use derived::recursion::{app_of_graph, Rec};
use derived::tower::Tower;
use kernel::{Env, Formula, Term, Thm};

/// The one-chain assembly every test shares.
struct Setup {
    t: Tower,
    r: Rec,
    i: Ite0,
    ut: UTower,
    s: Srt,
    o: Order,
    ru: Rules,
}

fn setup(env: &mut Env) -> Setup {
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
    Setup { t, r, i, ut, s, o, ru }
}

/// `x ∈ a` and `a = b` give `x ∈ b` — one Leibniz, for the reductions below.
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

/// `a = b` gives `srt(a) = srt(b)` — congruence via Leibniz over reflexivity.
fn srt_congr(env: &mut Env, s: &Srt, eq: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("srt_congr: not an equation");
    let w = env.fresh_var();
    let phi = Formula::eq(s.at(a.clone()), s.at(Term::var(w)));
    let leib = Thm::eq_leibniz(a.clone(), b, w, phi);
    Thm::mp(&Thm::mp(&leib, eq).expect("srt_congr"), &Thm::eq_refl(s.at(a)))
        .expect("srt_congr")
}

/// `⊢ srt(1̄) = U(ω)` — `at_succ` at `∅`, closed to `U(ω)` by a congruence
/// along the ladder's base equation (the `levels_srt.rs` route).
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

/// Every exported conclusion, pinned against a rebuild from the kernel's own
/// constructors; empty hypothesis sets; local closure.
#[test]
fn the_rule_kit_has_the_advertised_shape() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, s, o, i, ru) = (&se.r, &se.s, &se.o, &se.i, &se.ru);
    let omega = r.omega();
    let zero = r.zero();
    let unit = se.t.sums.unit();

    for thm in [&ru.cnd_ax, &ru.mono_sub, &ru.pi_imax, &ru.fun_type_demo, &ru.punit_demo] {
        assert!(thm.hyps().is_empty(), "nothing is assumed");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // `⊢ ∀A ∀b ∀z. (z ∈ cnd(A,b) ↔ (z ∈ 1 ∧ ∀x. (x ∈ A → • ∈ b)))`.
    let (a, b, z, x) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let cnd_ab = Term::apply(ru.cnd, vec![ta.clone(), tb.clone()]);
    let phi = Formula::forall(
        x,
        Formula::imp(
            Formula::mem(Term::var(x), ta.clone()),
            Formula::mem(se.t.sums.point(), tb.clone()),
        ),
    );
    assert_eq!(
        *ru.cnd_ax.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    z,
                    Formula::iff(
                        Formula::mem(tz.clone(), cnd_ab.clone()),
                        Formula::and(Formula::mem(tz, unit.clone()), phi),
                    ),
                ),
            ),
        ),
        "cnd_ax has the wrong shape"
    );

    // `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n → srt(m) ⊆ srt(n)))`.
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let mn_om = Formula::and(
        Formula::mem(tm.clone(), omega.clone()),
        Formula::mem(tn.clone(), omega.clone()),
    );
    let sub_mn = kernel::thm::subset(&mut env, tm.clone(), tn.clone());
    let sub_srt = kernel::thm::subset(&mut env, s.at(tm), s.at(tn));
    assert_eq!(
        *ru.mono_sub.concl(),
        Formula::forall(
            m,
            Formula::forall(n, Formula::imp(mn_om, Formula::imp(sub_mn, sub_srt))),
        ),
        "mono_sub has the wrong shape"
    );

    // The flagship: `⊢ ∀u ∀v ∀A ∀b. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧
    // b ∈ srt(v))) → ite0(v, cnd(A,b), fs(A,b)) ∈ srt(ite0(v, ∅, u ∪ v)))`.
    let (u, v, a2, b2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, ta2, tb2) = (Term::var(u), Term::var(v), Term::var(a2), Term::var(b2));
    let k = Formula::and(
        Formula::and(
            Formula::mem(tu.clone(), omega.clone()),
            Formula::mem(tv.clone(), omega.clone()),
        ),
        Formula::and(
            Formula::mem(ta2.clone(), s.at(tu.clone())),
            Formula::mem(tb2.clone(), s.at(tv.clone())),
        ),
    );
    let cnd_t = Term::apply(ru.cnd, vec![ta2.clone(), tb2.clone()]);
    let fs_t = se.t.sums.fs.of(ta2.clone(), tb2.clone());
    let imax_t = i.at(tv.clone(), zero.clone(), o.max(tu, tv.clone()));
    assert_eq!(
        *ru.pi_imax.concl(),
        Formula::forall(
            u,
            Formula::forall(
                v,
                Formula::forall(
                    a2,
                    Formula::forall(
                        b2,
                        Formula::imp(k, Formula::mem(i.at(tv, cnd_t, fs_t), s.at(imax_t))),
                    ),
                ),
            ),
        ),
        "pi_imax has the wrong shape"
    );

    // `⊢ ∀u ∀a. ((u ∈ ω ∧ a ∈ srt(succ u)) → fs(a,a) ∈ srt(succ u))`.
    let (u3, a3) = (env.fresh_var(), env.fresh_var());
    let (tu3, ta3) = (Term::var(u3), Term::var(a3));
    let srt_su = s.at(r.succ_of(tu3.clone()));
    assert_eq!(
        *ru.fun_type_demo.concl(),
        Formula::forall(
            u3,
            Formula::forall(
                a3,
                Formula::imp(
                    Formula::and(
                        Formula::mem(tu3.clone(), omega.clone()),
                        Formula::mem(ta3.clone(), srt_su.clone()),
                    ),
                    Formula::mem(se.t.sums.fs.of(ta3.clone(), ta3), srt_su),
                ),
            ),
        ),
        "fun_type_demo has the wrong shape"
    );

    // `⊢ ∀u. (u ∈ ω → 1 ∈ srt(u))`.
    let u4 = env.fresh_var();
    let tu4 = Term::var(u4);
    assert_eq!(
        *ru.punit_demo.concl(),
        Formula::forall(
            u4,
            Formula::imp(Formula::mem(tu4.clone(), omega), Formula::mem(unit, s.at(tu4))),
        ),
        "punit_demo has the wrong shape"
    );
}

/// **Ground instantiation, Prop side**: `pi_imax` at `u := ∅, v := ∅,
/// A := 1, b := 1` — the antecedents discharged, the conclusion computed by
/// the `when_zero` equations down to exactly `⊢ cnd(1,1) ∈ U₀`.
#[test]
fn pi_imax_computes_on_the_prop_side() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, s, o, i, ru) = (&se.r, &se.s, &se.o, &se.i, &se.ru);
    let zero = r.zero();
    let unit = se.t.sums.unit();

    let cnd_11 = Term::apply(ru.cnd, vec![unit.clone(), unit.clone()]);
    let fs_11 = se.t.sums.fs.of(unit.clone(), unit.clone());
    let max00 = o.max(zero.clone(), zero.clone());
    let imax00 = i.at(zero.clone(), zero.clone(), max00.clone());

    // Discharge the antecedents: `∅ ∈ ω` twice, `1 ∈ srt(∅)` twice (the
    // latter is `1 ∈ U₀` carried through the reversed `at_zero`).
    let zero_om = &r.core().zero_mem;
    let at_zero_rev = derived::eq_symm(&mut env, &s.at_zero).expect("U₀ = srt(∅)");
    let unit_srt0 = set_rw(&mut env, &at_zero_rev, &se.t.true_in_u0);
    let at =
        derived::inst_all(&ru.pi_imax, &[zero.clone(), zero.clone(), unit.clone(), unit.clone()])
            .expect("pi_imax at (∅,∅,1,1)");
    let concl = Thm::mp(
        &at,
        &derived::and_intro(
            &derived::and_intro(zero_om, zero_om),
            &derived::and_intro(&unit_srt0, &unit_srt0),
        ),
    )
    .expect("antecedents discharged");
    assert_eq!(
        *concl.concl(),
        Formula::mem(i.at(zero.clone(), cnd_11.clone(), fs_11.clone()), s.at(imax00.clone())),
        "the instantiated conclusion has the wrong shape"
    );

    // Compute both conditionals at the true guard `∅ = ∅`.
    let refl0 = Thm::eq_refl(zero.clone());
    let eq_term = Thm::mp(
        &derived::inst_all(&i.when_zero, &[zero.clone(), cnd_11.clone(), fs_11]).expect("when_zero"),
        &refl0,
    )
    .expect("ite0(∅, cnd, fs) = cnd(1,1)");
    let eq_imax = Thm::mp(
        &derived::inst_all(&i.when_zero, &[zero.clone(), zero.clone(), max00]).expect("when_zero"),
        &refl0,
    )
    .expect("imax(∅,∅) = ∅");
    let srt_eq = srt_congr(&mut env, s, &eq_imax);
    let srt_u0 = derived::eq_trans(&mut env, &srt_eq, &s.at_zero).expect("srt(imax(∅,∅)) = U₀");

    // `⊢ cnd(1,1) ∈ U₀`, explicitly.
    let cnd_in_srt = elt_rw(&mut env, &eq_term, &concl);
    let out = set_rw(&mut env, &srt_u0, &cnd_in_srt);
    assert_eq!(
        *out.concl(),
        Formula::mem(cnd_11, se.t.u0()),
        "the Prop clause did not compute to cnd(1,1) ∈ U₀"
    );
    assert!(out.hyps().is_empty());
}

/// **Ground instantiation, Type side**: `pi_imax` at `u := 1̄, v := 1̄,
/// A := ω, b := ω` — the guard refuted by `succ_ne_zero`, `1̄ ∪ 1̄` collapsed
/// by `max_absorb`, and the conclusion computed down to exactly
/// `⊢ fs(ω,ω) ∈ U(ω)`. Together with the Prop-side test this pins that BOTH
/// branches of the one theorem compute to the right ground facts.
#[test]
fn pi_imax_computes_on_the_type_side() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, s, o, i, ru) = (&se.r, &se.s, &se.o, &se.i, &se.ru);
    let zero = r.zero();
    let omega = r.omega();
    let one = r.succ_of(zero.clone());
    let zero_om = &r.core().zero_mem;

    let one_om = Thm::mp(
        &derived::inst_all(&r.core().succ_closed, std::slice::from_ref(&zero)).expect("succ_closed"),
        zero_om,
    )
    .expect("1̄ ∈ ω");
    // `ω ∈ srt(1̄)` — the size fact at the variable rung, instantiated at ∅.
    let om_in_srt1 = Thm::mp(
        &derived::inst_all(&s.omega_mem, std::slice::from_ref(&zero)).expect("omega_mem"),
        zero_om,
    )
    .expect("ω ∈ srt(succ ∅)");

    let cnd_ww = Term::apply(ru.cnd, vec![omega.clone(), omega.clone()]);
    let fs_ww = se.t.sums.fs.of(omega.clone(), omega.clone());
    let max11 = o.max(one.clone(), one.clone());
    let imax11 = i.at(one.clone(), zero.clone(), max11.clone());

    let at = derived::inst_all(&ru.pi_imax, &[one.clone(), one.clone(), omega.clone(), omega.clone()])
        .expect("pi_imax at (1̄,1̄,ω,ω)");
    let concl = Thm::mp(
        &at,
        &derived::and_intro(
            &derived::and_intro(&one_om, &one_om),
            &derived::and_intro(&om_in_srt1, &om_in_srt1),
        ),
    )
    .expect("antecedents discharged");
    assert_eq!(
        *concl.concl(),
        Formula::mem(i.at(one.clone(), cnd_ww, fs_ww.clone()), s.at(imax11.clone())),
        "the instantiated conclusion has the wrong shape"
    );

    // The guard is refuted, so both conditionals take the nonzero branch.
    let ne1 = Thm::mp(
        &derived::inst_all(&r.peano.succ_ne_zero, std::slice::from_ref(&zero)).expect("succ_ne_zero"),
        zero_om,
    )
    .expect("¬(1̄ = ∅)");
    let cnd_ww2 = Term::apply(ru.cnd, vec![omega.clone(), omega.clone()]);
    let eq_term = Thm::mp(
        &derived::inst_all(&i.when_nonzero, &[one.clone(), cnd_ww2, fs_ww.clone()])
            .expect("when_nonzero"),
        &ne1,
    )
    .expect("ite0(1̄, cnd, fs) = fs(ω,ω)");
    let eq_imax = Thm::mp(
        &derived::inst_all(&i.when_nonzero, &[one.clone(), zero, max11.clone()])
            .expect("when_nonzero"),
        &ne1,
    )
    .expect("imax(1̄,1̄) = 1̄ ∪ 1̄");

    // `1̄ ∪ 1̄ = 1̄`: `max_absorb` at `(1̄,1̄)` has both disjuncts identical, and
    // `∨` is `¬· → ·`, so Clavius collapses it.
    let absorb = Thm::mp(
        &derived::inst_all(&o.max_absorb, &[one.clone(), one.clone()]).expect("max_absorb"),
        &derived::and_intro(&one_om, &one_om),
    )
    .expect("(1̄∪1̄ = 1̄) ∨ (1̄∪1̄ = 1̄)");
    let collapse = Thm::mp(&derived::clavius(Formula::eq(max11, one)), &absorb)
        .expect("1̄ ∪ 1̄ = 1̄");

    // `srt(imax(1̄,1̄)) = U(ω)`, through `srt(1̄) = U(ω)`.
    let imax_is_one = derived::eq_trans(&mut env, &eq_imax, &collapse).expect("imax(1̄,1̄) = 1̄");
    let srt_eq = srt_congr(&mut env, s, &imax_is_one);
    let srt1_uw = srt1_eq_uw(&mut env, &se);
    let full = derived::eq_trans(&mut env, &srt_eq, &srt1_uw).expect("srt(imax(1̄,1̄)) = U(ω)");

    // `⊢ fs(ω,ω) ∈ U(ω)`, explicitly — and `U(ω)` is the tower's `U₁`.
    let fs_in_srt = elt_rw(&mut env, &eq_term, &concl);
    let out = set_rw(&mut env, &full, &fs_in_srt);
    let uw = Term::apply(se.t.space.lu, vec![omega]);
    assert_eq!(uw, se.t.u(1), "U(ω) is not the tower's U₁");
    assert_eq!(
        *out.concl(),
        Formula::mem(fs_ww, uw),
        "the Type clause did not compute to fs(ω,ω) ∈ U(ω)"
    );
    assert!(out.hyps().is_empty());
}

/// `punit_demo` cashed out at two levels: the one quantified theorem
/// instantiates to `⊢ 1 ∈ U₀` at `∅` and to `⊢ 1 ∈ U(ω)` at `1̄` — where the
/// ground schedule would mint a fresh interpretation symbol per instantiation
/// (`LEVELPOLY.md` §1.6).
#[test]
fn punit_demo_instantiates_at_both_bottom_rungs() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, s, ru) = (&se.r, &se.s, &se.ru);
    let zero = r.zero();
    let omega = r.omega();
    let one = r.succ_of(zero.clone());
    let unit = se.t.sums.unit();
    let zero_om = &r.core().zero_mem;

    // At `∅`: `⊢ 1 ∈ srt(∅)`, read through `at_zero` as `⊢ 1 ∈ U₀`.
    let p0 = Thm::mp(
        &derived::inst_all(&ru.punit_demo, std::slice::from_ref(&zero)).expect("punit at ∅"),
        zero_om,
    )
    .expect("1 ∈ srt(∅)");
    let in_u0 = set_rw(&mut env, &s.at_zero, &p0);
    assert_eq!(*in_u0.concl(), Formula::mem(unit.clone(), se.t.u0()));
    assert!(in_u0.hyps().is_empty());

    // At `1̄`: `⊢ 1 ∈ srt(1̄)`, read through `srt(1̄) = U(ω)` as `⊢ 1 ∈ U(ω)`.
    let one_om = Thm::mp(
        &derived::inst_all(&r.core().succ_closed, std::slice::from_ref(&zero)).expect("succ_closed"),
        zero_om,
    )
    .expect("1̄ ∈ ω");
    let p1 = Thm::mp(
        &derived::inst_all(&ru.punit_demo, std::slice::from_ref(&one)).expect("punit at 1̄"),
        &one_om,
    )
    .expect("1 ∈ srt(1̄)");
    let srt1_uw = srt1_eq_uw(&mut env, &se);
    let in_uw = set_rw(&mut env, &srt1_uw, &p1);
    assert_eq!(
        *in_uw.concl(),
        Formula::mem(unit, Term::apply(se.t.space.lu, vec![omega])),
    );
    assert!(in_uw.hyps().is_empty());
}
