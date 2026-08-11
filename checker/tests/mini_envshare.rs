//! The shared semantic core at the engine roots (ENV-UNIFY.md §3.3, B1/B2).
//!
//! `nanoda_lib::tg::EnvCore` is the handle both engines take: one kernel
//! `Env` (one brand), one canonical-variable series, one W-type `Machine`.
//! These tests pin the sharing at mini's root — two `Interp`s over one core
//! agree object-for-object, and two private cores disagree, which is the
//! `Nat::over` template (two-over-one agree, fresh disagrees) one level up.
//! The cross-engine half — the checker running over the same core — is
//! `mini/tests/envshare_tg.rs`, behind `--features tg` because driving the
//! checker's evidence path needs its backend compiled in.
//!
//! Everything here runs off committed fixtures or no input at all; nothing
//! reads the gitignored corpus, so there is nothing to skip.

use std::rc::Rc;

use kernel::Term;
use nanoda_lib::mini::interp::Interp;
use nanoda_lib::tg::EnvCore;

/// Two `Interp`s over one core give one skeleton key for one shape — the same
/// `Term`, hole for hole — because `x_canon` and the hole series are the
/// core's. This is the object-identity fact every shared site table would
/// stand on: equal keys must be equal *terms*, not terms equal up to a
/// renaming of engine-private variables.
#[test]
fn two_interps_over_one_core_key_one_shape_with_one_term() {
    let core = EnvCore::fresh();
    let mut ip1 = Interp::over(core.clone());
    let mut ip2 = Interp::over(core.clone());
    // A body shape mentioning the binder `v` beside a `v`-free subterm `w`:
    // `app(w, v)`. The skeleton abstracts `w` into hole 0 and sends `v` to
    // the canonical slot.
    let v = core.fresh_var();
    let w = core.fresh_var();
    let app = ip1.prelude.ap.app;
    let t = Term::apply(app, vec![Term::var(w), Term::var(v)]);
    let (mut h1, mut h2) = (Vec::new(), Vec::new());
    let k1 = ip1.skeleton(&t, v, &mut h1);
    let k2 = ip2.skeleton(&t, v, &mut h2);
    assert_eq!(k1, k2, "one core, one skeleton key");
    assert_eq!(h1, h2, "and the same holes, in the same order");
    assert_eq!(ip1.x_canon(), ip2.x_canon(), "one canonical binder slot");
}

/// The disagree direction, so the test above cannot pass vacuously: a private
/// core is a private signature, and the same shape keys differently under it.
/// (`Interp::new` is exactly `Interp::over(EnvCore::fresh())`, so this is
/// also the historical two-`Env` state, preserved.)
#[test]
fn a_fresh_core_is_a_different_signature() {
    let core = EnvCore::fresh();
    let mut ip1 = Interp::over(core.clone());
    let mut ip3 = Interp::new();
    let v = core.fresh_var();
    let w = core.fresh_var();
    let app = ip1.prelude.ap.app;
    let t = Term::apply(app, vec![Term::var(w), Term::var(v)]);
    let (mut h1, mut h3) = (Vec::new(), Vec::new());
    let k1 = ip1.skeleton(&t, v, &mut h1);
    let k3 = ip3.skeleton(&t, v, &mut h3);
    assert_ne!(
        k1, k3,
        "a fresh core mints its own canonical variables, so the key differs"
    );
    assert_ne!(ip1.x_canon(), ip3.x_canon());
}

/// The hole series is one series per core: stable across handle clones, grown
/// once, and a second core's is a different family of variables outright.
#[test]
fn the_hole_series_is_one_series_per_core() {
    let core = EnvCore::fresh();
    let other = core.clone();
    assert!(core.same_core(&other));
    let h2 = core.hole_var(2);
    assert_eq!(other.hole_var(2), h2, "clones read the same series");
    assert_eq!(other.hole(2), Some(h2));
    assert_eq!(core.hole_var(2), h2, "asking again mints nothing new");

    let fresh = EnvCore::fresh();
    assert!(!fresh.same_core(&core));
    assert_ne!(fresh.hole_var(2), h2, "a second core is a second series");
}

/// **B2**: the inductive apparatus's `Machine` *is* the core's — one object,
/// so a second `Interp` over the same core is welded to the same machine and
/// its carriers compose. And the mutation direction: two private cores are
/// two machines with two `MachineId`s, the state whose theorems cannot cross.
#[test]
fn the_machine_is_the_cores_and_two_cores_are_two_machines() {
    let pre = derived::prelude::prelude();
    let core = EnvCore::fresh();
    let mut ip1 = Interp::over(core.clone());
    let mut ip2 = Interp::over(core.clone());
    let m1 = ip1.ind_apparatus().expect("apparatus builds").mach.clone();
    let m2 = ip2.ind_apparatus().expect("apparatus builds").mach.clone();
    let mc = core.machine(&pre).expect("the core's machine");
    assert!(Rc::ptr_eq(&m1, &mc), "the apparatus machine is the core's");
    assert!(Rc::ptr_eq(&m1, &m2), "two Interps over one core: one machine");

    let mut ip3 = Interp::new();
    let m3 = ip3.ind_apparatus().expect("apparatus builds").mach.clone();
    assert!(!Rc::ptr_eq(&m1, &m3));
    assert_ne!(
        m1.borrow().ident(),
        m3.borrow().ident(),
        "two cores mint two MachineIds — the is_over guards tell them apart"
    );
}

/// [`nanoda_lib::mini::run::check_file_with_interp`] really runs over the caller's
/// `Interp` and hands it back with the signature the run grew — the driver
/// seam for per-declaration engine routing.
#[test]
fn check_file_with_interp_runs_over_the_callers_core() {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/delta_inside_a_proof.ndjson");
    let core = EnvCore::fresh();
    let before = core.fresh_var();
    let (out, ip) = nanoda_lib::mini::run::check_file_with_interp(
        &fixture,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "the fixture is a good file: {:?}", out.verdict);
    assert!(ip.core().same_core(&core), "the run kept the caller's core");
    let after = core.fresh_var();
    assert!(
        after.id() > before.id() + 1,
        "the run minted from the caller's Env — the counters moved"
    );
}

/// A second core cannot be installed under a thread whose checker `Shared`
/// already exists: replacing the signature mid-run would strand every symbol
/// the first one minted, so the seam refuses loudly rather than mislabels.
#[test]
#[should_panic(expected = "already has a Shared")]
fn installing_a_second_core_on_one_thread_panics() {
    nanoda_lib::tg::install_shared_core(EnvCore::fresh());
    nanoda_lib::tg::install_shared_core(EnvCore::fresh());
}
