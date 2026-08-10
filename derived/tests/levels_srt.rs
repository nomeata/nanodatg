//! The sort ladder `srt(n) = ite0(n, U₀, app(lvl, n))`, checked over the
//! tower's own chain.
//!
//! The assembly mirrors `levels_utower.rs`: build the [`Tower`], keep its
//! `U(·)`, its power set and its rung terms, then rebuild [`Rec`] from the
//! tower's own `Apply` and `Peano` — so every symbol `srt` speaks of is the
//! tower's, and `srt(1̄) = U(ω)` lands on `Tower::u(1)` on the nose.

use derived::levels::ite0::{ite0, Ite0};
use derived::levels::srt::{srt, Srt};
use derived::levels::utower::{utower, UTower};
use derived::recursion::{app_of_graph, Rec};
use derived::tower::Tower;
use kernel::{Env, FnSym, Formula, Term, Thm};

/// The one-chain assembly both tests share.
struct Setup {
    r: Rec,
    lu: FnSym,
    /// `U₀` and `Tower::u(1)`, captured off the tower.
    u0: Term,
    u1: Term,
    /// `⊢ ∀c. U₀ ∈ U(c)`, kept for the non-vacuity derivation.
    u0_in: Thm,
    i: Ite0,
    ut: UTower,
    s: Srt,
}

fn setup(env: &mut Env) -> Setup {
    let t = Tower::new(env).expect("Tower");
    let u0 = t.u0();
    let u1 = t.u(1);
    let lu = t.space.lu;
    let lu_ax = t.space.lu_ax.clone();
    let (pow, pow_ax) = (t.space.pow, t.space.pow_ax.clone());
    let ap = t.sums.ap.clone();
    let peano = t.peano.clone();
    let u0_in = t.u0_in.clone();
    let app_of_graph = app_of_graph(env, &ap).expect("app_of_graph");
    let r = Rec { ap, peano, app_of_graph };
    let i = ite0(env, &r.ap).expect("ite0");
    let ut = utower(env, &r, lu, &lu_ax, pow, &pow_ax).expect("utower");
    let s = srt(env, &r, &i, &ut, &t).expect("srt");
    Setup { r, lu, u0, u1, u0_in, i, ut, s }
}

/// Every exported conclusion, pinned against a rebuild from the kernel's own
/// constructors, with `⊆` spelled `kernel::thm::subset` exactly.
#[test]
fn the_sort_ladder_has_the_advertised_shape() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, ut, s) = (&se.r, &se.ut, &se.s);
    let omega = r.omega();
    let zero = r.zero();
    let u_of = |t: Term| Term::apply(se.lu, vec![t]);

    for thm in [
        &s.at_zero,
        &s.at_succ,
        &s.step_sub,
        &s.sort_in_sort,
        &s.mono_mem,
        &s.omega_mem,
        &s.u0_mem,
    ] {
        assert!(thm.hyps().is_empty(), "nothing is assumed");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // `Srt::at` is literally the `ite0` application — no new symbol.
    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(
        s.at(tn.clone()),
        se.i.at(tn.clone(), se.u0.clone(), ut.at(tn.clone())),
        "Srt::at does not spell the ite0 application"
    );
    assert_eq!(s.u0(), se.u0, "Srt::u0 is not the tower's rung 0");

    // `⊢ srt(∅) = U₀`.
    assert_eq!(*s.at_zero.concl(), Formula::eq(s.at(zero.clone()), se.u0.clone()));

    let h = Formula::mem(tn.clone(), omega.clone());
    let sn = r.succ_of(tn.clone());

    // `⊢ ∀n. (n ∈ ω → srt(succ n) = U(app(lvl, n)))`.
    assert_eq!(
        *s.at_succ.concl(),
        Formula::forall(
            n,
            Formula::imp(h.clone(), Formula::eq(s.at(sn.clone()), u_of(ut.at(tn.clone()))))
        ),
        "at_succ has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → srt(n) ∈ srt(succ n))`.
    assert_eq!(
        *s.sort_in_sort.concl(),
        Formula::forall(
            n,
            Formula::imp(h.clone(), Formula::mem(s.at(tn.clone()), s.at(sn.clone())))
        ),
        "sort_in_sort has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → srt(n) ⊆ srt(succ n))`.
    let sub_step = kernel::thm::subset(&mut env, s.at(tn.clone()), s.at(sn.clone()));
    assert_eq!(
        *s.step_sub.concl(),
        Formula::forall(n, Formula::imp(h.clone(), sub_step)),
        "step_sub has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ n → srt(m) ⊆ srt(n)))`.
    let m = env.fresh_var();
    let tm = Term::var(m);
    let sub_mn = kernel::thm::subset(&mut env, s.at(tm.clone()), s.at(tn.clone()));
    assert_eq!(
        *s.mono_mem.concl(),
        Formula::forall(
            n,
            Formula::imp(
                h.clone(),
                Formula::forall(m, Formula::imp(Formula::mem(tm, tn.clone()), sub_mn))
            )
        ),
        "mono_mem has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → ω ∈ srt(succ n))`.
    assert_eq!(
        *s.omega_mem.concl(),
        Formula::forall(
            n,
            Formula::imp(h.clone(), Formula::mem(omega.clone(), s.at(sn.clone())))
        ),
        "omega_mem has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → U₀ ∈ srt(succ n))`.
    assert_eq!(
        *s.u0_mem.concl(),
        Formula::forall(n, Formula::imp(h, Formula::mem(se.u0.clone(), s.at(sn)))),
        "u0_mem has the wrong shape"
    );
}

/// **Non-vacuity**: `⊢ srt(1̄) = U(ω)` — landing on `Tower::u(1)` syntactically
/// — and `⊢ ¬(srt(∅) = srt(1̄))`, so `Prop` and `Type 0` stay distinct through
/// the encoding.
///
/// The first is `at_succ` at `∅` with `U(app(lvl,∅))` closed to `U(ω)` by a
/// congruence along the base equation. The second transports `U₀ ∈ U(ω)`
/// (`Tower::u0_in` at `ω`) to `srt(∅) ∈ srt(1̄)` along the two equations; were
/// the two values equal, Leibniz would give `srt(∅) ∈ srt(∅)`, against
/// Regularity's no-self-membership.
#[test]
fn prop_and_type_zero_stay_distinct() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let (r, ut, s) = (&se.r, &se.ut, &se.s);
    let omega = r.omega();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let srt0 = s.at(zero.clone());
    let srt1 = s.at(one.clone());
    let uw = Term::apply(se.lu, vec![omega.clone()]);

    // ── `⊢ srt(1̄) = U(ω)`, and it is literally `Tower::u(1)` ────────────────
    let e1 = Thm::mp(
        &derived::inst_all(&s.at_succ, std::slice::from_ref(&zero)).expect("at_succ at ∅"),
        &r.core().zero_mem,
    )
    .expect("srt(1̄) = U(app(lvl,∅))");
    // `U(app(lvl,∅)) = U(ω)`, by congruence along the base equation.
    let l0 = ut.at(zero.clone());
    let ul0 = Term::apply(se.lu, vec![l0.clone()]);
    let w = env.fresh_var();
    let congr = derived::mpd_const(
        &Thm::eq_leibniz(
            l0,
            omega.clone(),
            w,
            Formula::eq(ul0.clone(), Term::apply(se.lu, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(ul0),
    )
    .expect("congruence");
    let u_eq = Thm::mp(&congr, &ut.base).expect("U(app(lvl,∅)) = U(ω)");
    let srt1_eq = derived::eq_trans(&mut env, &e1, &u_eq).expect("srt(1̄) = U(ω)");
    assert_eq!(se.u1, uw, "Tower::u(1) is not U(ω)");
    assert_eq!(
        *srt1_eq.concl(),
        Formula::eq(srt1.clone(), se.u1.clone()),
        "srt(1̄) does not land on the tower's U₁"
    );
    assert!(srt1_eq.hyps().is_empty());

    // ── `⊢ srt(∅) ∈ srt(1̄)`: `U₀ ∈ U(ω)` carried to srt-terms ───────────────
    let u0_in_uw =
        derived::inst_all(&se.u0_in, std::slice::from_ref(&omega)).expect("U₀ ∈ U(ω)");
    let sym0 = Thm::mp(&derived::eq_symm_imp(&mut env, srt0.clone(), se.u0.clone()), &s.at_zero)
        .expect("U₀ = srt(∅)");
    let leib_l =
        Thm::eq_leibniz(se.u0.clone(), srt0.clone(), w, Formula::mem(Term::var(w), uw.clone()));
    let m1 = Thm::mp(&Thm::mp(&leib_l, &sym0).expect("mp"), &u0_in_uw).expect("srt(∅) ∈ U(ω)");
    let sym1 = Thm::mp(&derived::eq_symm_imp(&mut env, srt1.clone(), uw.clone()), &srt1_eq)
        .expect("U(ω) = srt(1̄)");
    let leib_r = Thm::eq_leibniz(uw, srt1.clone(), w, Formula::mem(srt0.clone(), Term::var(w)));
    let s0_in_s1 = Thm::mp(&Thm::mp(&leib_r, &sym1).expect("mp"), &m1).expect("srt(∅) ∈ srt(1̄)");
    assert_eq!(*s0_in_s1.concl(), Formula::mem(srt0.clone(), srt1.clone()));

    // ── `⊢ ¬(srt(∅) = srt(1̄))`, by no-self-membership at `srt(∅)` ────────────
    let not_self = derived::inst_all(&r.peano.no_self_mem, std::slice::from_ref(&srt0))
        .expect("¬(srt(∅) ∈ srt(∅))");
    let leib2 = Thm::eq_leibniz(srt1.clone(), srt0.clone(), w, Formula::mem(srt0.clone(), Term::var(w)));
    let step = derived::mpd_const(&leib2, &s0_in_s1).expect("mpd_const");
    let ne = derived::syl(&step, &not_self).expect("¬(srt(1̄) = srt(∅))");
    let out = derived::syl(&derived::eq_symm_imp(&mut env, srt0.clone(), srt1.clone()), &ne)
        .expect("¬(srt(∅) = srt(1̄))");
    assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(srt0, srt1)),
        "the Prop/Type-0 distinctness statement has the wrong shape"
    );
    assert!(out.hyps().is_empty());
}

/// **The ground bridge `⊢ srt(n̄) = Uₙ`, at three rungs** — `LEVELPOLY.md`
/// §1.2's numeral bridge, which is what lets one vocabulary replace two.
///
/// Three atoms is the floor here for a reason the ladder makes concrete: the
/// two ladders agree at every rung but are built differently at *three*
/// different places. Rung 0 comes from the `ite0` guard and never touches
/// `lvl`; rung 1 comes from `at_succ` composed with the ladder's `ω` **base**;
/// rung 2 is the first that composes `at_succ` with a recursive ladder result.
/// A bridge tested at rungs 0 and 1 alone passes under an implementation that
/// never recurses — which is exactly the degenerate case this file's sibling
/// found — and one tested at 1 and 2 alone passes under one that has no `ite0`
/// guard at all and would put `⟦Prop⟧` at `U(ω)`.
///
/// The right-hand sides are compared against [`Tower::u`] **syntactically**,
/// not up to any equation: the point of the bridge is that after it the two
/// spellings are the *same term*, so a checker's literal-formula guard matches.
///
/// Mutations run against this test (each red, then reverted): asking the
/// ladder for rung `n` instead of `n-1` inside `Srt::rung_eq`, which leaves
/// rung 0 green and moves rungs 1 and 2 one rung up — the off-by-one the
/// recursion exists to get right, invisible without a rung that recurses; and
/// answering rung 0 from `at_succ` rather than `at_zero`, which leaves rungs 1
/// and 2 green and is caught only because rung 0 is *not* the ladder's.
#[test]
fn the_ground_bridge_equates_the_sort_ladder_with_the_tower_rungs() {
    let mut env = Env::new();
    let se = setup(&mut env);
    let t = Tower::new(&mut env);
    // The tower rung terms come from the *same* assembly `setup` built over;
    // rebuilding one here would compare two different chains' look-alikes.
    let _ = t;
    let (r, ut, s) = (&se.r, &se.ut, &se.s);
    let u_of = |x: Term| Term::apply(se.lu, vec![x]);

    // `U₀`, `U(ω)`, `U(U(ω))` — `Tower::u(0..=2)`, spelled here so the test
    // states the ladder it is checking rather than deferring to the thing
    // under test.
    let want = [se.u0.clone(), u_of(r.omega()), u_of(u_of(r.omega()))];
    assert_eq!(want[1], se.u1, "Tower::u(1) is not U(ω)");

    let mut numerals = Vec::new();
    let mut k = r.zero();
    for _ in 0..3 {
        numerals.push(k.clone());
        k = r.succ_of(k);
    }

    for (n, (num, rhs)) in numerals.iter().zip(want.iter()).enumerate() {
        let br = s.rung_eq(&mut env, r, ut, se.lu, n).expect("the ground bridge must build");
        assert!(br.hyps().is_empty(), "rung {n}: the bridge must be unconditional");
        assert_eq!(
            *br.concl(),
            Formula::eq(s.at(num.clone()), rhs.clone()),
            "rung {n}: the bridge does not equate srt({n}̄) with the tower's own rung term"
        );
        assert!(kernel::thm::debug_locally_closed(br.concl()));
    }

    // The ladder's own rungs, which the sort ladder's differ from at 0 only.
    // `lvl(0̄) = ω` while `srt(0̄) = U₀`: the one place the two disagree, and
    // the reason the sort bridge cannot just delegate.
    let l0 = ut.rung_eq(&mut env, r, se.lu, 0).expect("lvl rung 0");
    assert_eq!(*l0.concl(), Formula::eq(ut.at(numerals[0].clone()), r.omega()));
    assert_ne!(
        r.omega(),
        se.u0,
        "if ω and U₀ were the same term the bottom of the two ladders would coincide and \
         this whole test would be vacuous"
    );
    for n in 1..3 {
        let ln = ut.rung_eq(&mut env, r, se.lu, n).expect("lvl rung");
        assert_eq!(
            *ln.concl(),
            Formula::eq(ut.at(numerals[n].clone()), want[n].clone()),
            "the ladder and the sort ladder must agree from rung 1 up"
        );
    }
}
