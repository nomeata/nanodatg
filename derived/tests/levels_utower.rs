//! The internal universe ladder `lvl`, checked over the tower's own chain.
//!
//! The assembly mirrors `cumul::Chain::new`: build the [`Tower`], keep its
//! `U(·)`, its power set and its rung terms, then rebuild [`Rec`] from the
//! tower's own `Apply` and `Peano` — so every symbol the ladder speaks of is
//! the tower's, and the rung equations land on `Tower::u(1)` and `Tower::u(2)`
//! on the nose.

use derived::levels::utower::{utower, UTower};
use derived::recursion::{app_of_graph, Rec};
use derived::tower::Tower;
use derived::universe as uni;
use kernel::{Env, FnSym, Formula, Term, Thm};

/// The one-chain assembly both tests share.
struct Setup {
    r: Rec,
    lu: FnSym,
    lu_ax: Thm,
    /// `Tower::u(1)` and `Tower::u(2)`, captured before the tower is consumed.
    u1: Term,
    u2: Term,
    ut: UTower,
}

fn setup(env: &mut Env) -> Setup {
    let t = Tower::new(env).expect("Tower");
    let (u1, u2) = (t.u(1), t.u(2));
    let lu = t.space.lu;
    let lu_ax = t.space.lu_ax.clone();
    let (pow, pow_ax) = (t.space.pow, t.space.pow_ax.clone());
    let ap = t.sums.ap.clone();
    let Tower { peano, .. } = t;
    let app_of_graph = app_of_graph(env, &ap).expect("app_of_graph");
    let r = Rec { ap, peano, app_of_graph };
    let ut = utower(env, &r, lu, &lu_ax, pow, &pow_ax).expect("utower");
    Setup { r, lu, lu_ax, u1, u2, ut }
}

/// Every exported conclusion, pinned against a rebuild from the kernel's own
/// constructors — including the two numeral bridges against the tower's own
/// rung terms.
#[test]
fn the_ladder_has_the_advertised_shape() {
    let mut env = Env::new();
    let s = setup(&mut env);
    let (r, ut) = (&s.r, &s.ut);
    let omega = r.omega();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let two = r.succ_of(one.clone());
    let u_of = |t: Term| Term::apply(s.lu, vec![t]);

    for thm in [
        &ut.base,
        &ut.step,
        &ut.step_is_universe,
        &ut.climb,
        &ut.omega_mem,
        &ut.rung1_eq,
        &ut.rung2_eq,
    ] {
        assert!(thm.hyps().is_empty(), "nothing is assumed");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // `UTower::at` spells `app(lvl, ·)` exactly as the recursion does.
    assert_eq!(ut.at(zero.clone()), r.apply(ut.set.clone(), zero.clone()));

    // `⊢ app(lvl, ∅) = ω`.
    assert_eq!(*ut.base.concl(), Formula::eq(ut.at(zero.clone()), omega.clone()));

    let n = env.fresh_var();
    let tn = Term::var(n);
    let h = Formula::mem(tn.clone(), omega.clone());
    let lsn = ut.at(r.succ_of(tn.clone()));

    // `⊢ ∀n. (n ∈ ω → app(lvl, succ n) = U(app(lvl, n)))`.
    assert_eq!(
        *ut.step.concl(),
        Formula::forall(
            n,
            Formula::imp(h.clone(), Formula::eq(lsn.clone(), u_of(ut.at(tn.clone()))))
        ),
        "step has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → is_universe(app(lvl, succ n)))`.
    let isu = uni::is_universe(&mut env, &lsn);
    assert_eq!(
        *ut.step_is_universe.concl(),
        Formula::forall(n, Formula::imp(h.clone(), isu)),
        "step_is_universe has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → app(lvl, n) ∈ app(lvl, succ n))`.
    assert_eq!(
        *ut.climb.concl(),
        Formula::forall(
            n,
            Formula::imp(h.clone(), Formula::mem(ut.at(tn.clone()), lsn.clone()))
        ),
        "climb has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → ω ∈ app(lvl, succ n))`.
    assert_eq!(
        *ut.omega_mem.concl(),
        Formula::forall(n, Formula::imp(h, Formula::mem(omega.clone(), lsn))),
        "omega_mem has the wrong shape"
    );

    // The numeral bridges land on the tower's own rungs: `Tower::u(1)` is
    // literally `U(ω)` and `Tower::u(2)` literally `U(U(ω))` over this chain.
    assert_eq!(s.u1, u_of(omega), "Tower::u(1) is not U(ω)");
    assert_eq!(s.u2, u_of(s.u1.clone()), "Tower::u(2) is not U(U(ω))");
    assert_eq!(
        *ut.rung1_eq.concl(),
        Formula::eq(ut.at(one), s.u1.clone()),
        "rung1_eq does not land on the tower's U₁"
    );
    assert_eq!(
        *ut.rung2_eq.concl(),
        Formula::eq(ut.at(two), s.u2.clone()),
        "rung2_eq does not land on the tower's U₂"
    );
}

/// **Non-vacuity**: `⊢ ¬(app(lvl, ∅) = app(lvl, succ ∅))` — i.e. `¬(ω = U(ω))`
/// — so the ladder actually climbs rather than sitting at a fixed point.
///
/// From `ω ∈ U(ω)` (`mem_least_universe` at `ω`) carried across the two
/// equations to `app(lvl,∅) ∈ app(lvl,1̄)`, and no-self-membership: were the
/// two values equal, Leibniz would give `app(lvl,∅) ∈ app(lvl,∅)`.
#[test]
fn the_ladder_actually_climbs() {
    let mut env = Env::new();
    let s = setup(&mut env);
    let (r, ut) = (&s.r, &s.ut);
    let omega = r.omega();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let l0 = ut.at(zero);
    let l1 = ut.at(one);
    let uw = Term::apply(s.lu, vec![omega.clone()]);

    // `⊢ ω ∈ U(ω)`.
    let mem_lu = uni::mem_least_universe(&mut env, s.lu, &s.lu_ax).expect("mem_least_universe");
    let om_in_uw =
        derived::inst_all(&mem_lu, std::slice::from_ref(&omega)).expect("ω ∈ U(ω)");

    // Rewrite `U(ω)` to `app(lvl,1̄)` along the reversed `rung1_eq`, then `ω`
    // to `app(lvl,∅)` along the reversed base equation.
    let w = env.fresh_var();
    let uw_eq = Thm::mp(&derived::eq_symm_imp(&mut env, l1.clone(), uw.clone()), &ut.rung1_eq)
        .expect("U(ω) = app(lvl,1̄)");
    let leib1 = Thm::eq_leibniz(uw, l1.clone(), w, Formula::mem(omega.clone(), Term::var(w)));
    let om_in_l1 =
        Thm::mp(&Thm::mp(&leib1, &uw_eq).expect("mp"), &om_in_uw).expect("ω ∈ app(lvl,1̄)");

    let om_eq = Thm::mp(&derived::eq_symm_imp(&mut env, l0.clone(), omega.clone()), &ut.base)
        .expect("ω = app(lvl,∅)");
    let leib0 = Thm::eq_leibniz(omega, l0.clone(), w, Formula::mem(Term::var(w), l1.clone()));
    let l0_in_l1 = Thm::mp(&Thm::mp(&leib0, &om_eq).expect("mp"), &om_in_l1)
        .expect("app(lvl,∅) ∈ app(lvl,1̄)");
    assert_eq!(*l0_in_l1.concl(), Formula::mem(l0.clone(), l1.clone()));

    // `⊢ ¬(app(lvl,∅) = app(lvl,1̄))`, by no-self-membership at `app(lvl,∅)`.
    let not_self = derived::inst_all(&r.peano.no_self_mem, std::slice::from_ref(&l0))
        .expect("¬(app(lvl,∅) ∈ app(lvl,∅))");
    let leib2 = Thm::eq_leibniz(l1.clone(), l0.clone(), w, Formula::mem(l0.clone(), Term::var(w)));
    let step = derived::mpd_const(&leib2, &l0_in_l1).expect("mpd_const");
    let ne = derived::syl(&step, &not_self).expect("¬(app(lvl,1̄) = app(lvl,∅))");
    let out = derived::syl(&derived::eq_symm_imp(&mut env, l0.clone(), l1.clone()), &ne)
        .expect("¬(app(lvl,∅) = app(lvl,1̄))");
    assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(l0, l1)),
        "the non-collapse statement has the wrong shape"
    );
    assert!(out.hyps().is_empty());
}
