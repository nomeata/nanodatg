//! **Both engines over one core, in one process** — the cross-engine half of
//! `mini/tests/envshare.rs` (ENV-UNIFY.md §3.3, B1/B2).
//!
//! One `nanoda_lib::tg::EnvCore` is handed to mini (`Interp::over` +
//! `check_file_with_interp`) and installed as the checker's per-thread
//! signature (`tg::install_shared_core`); both engines then run a real
//! tutorial export to completion **in this thread**, minting from one kernel
//! `Env`. What that pins, beyond either engine's own suite: the two roots
//! really accept a caller's core, neither strands the other's `RefCell`
//! borrows, the counters are one pair of counters, and the W-type machine is
//! one object on both sides — in either engine order.
//!
//! Behind `--features tg` because the checker's evidence path exists only
//! with its backend compiled in; `ci/check.sh` runs it with
//! `cargo test -p mini --features tg`.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::rc::Rc;

use mini::interp::Interp;
use nanoda_lib::tg::EnvCore;

// SKIP is not PASS: both tests below return early when `vendor/arena-tests`
// is absent, and cargo reports them `ok`. See ci/skip-guard.rs.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests")
}

/// Drive the checker in-process over `export`, on this thread — so it builds
/// its `Shared` from whatever core was installed. Panics if checking fails,
/// which is the checker's own contract.
fn run_checker(export: &Path) {
    let cfg_path = std::env::temp_dir().join(format!(
        "nanodatg-envshare-{}-{}.json",
        std::process::id(),
        export.file_stem().unwrap_or_default().to_string_lossy(),
    ));
    let cfg = format!(
        r#"{{"export_file_path": {},
             "unpermitted_axiom_hard_error": false,
             "unsafe_permit_all_axioms": true,
             "nat_extension": true,
             "string_extension": true,
             "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let config = nanoda_lib::util::Config::try_from(cfg_path.as_path()).expect("config parses");
    let _ = std::fs::remove_file(&cfg_path);
    let (export_file, _skipped) = config.to_export_file().expect("export parses");
    export_file.check_all_declars();
}

/// mini first, checker second, one core. The assertions at the end are the
/// sharing facts: the checker minted from the same `Env` mini grew, and the
/// machine both sides reach is one object.
#[test]
fn one_core_serves_both_engines_mini_then_checker() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let core = EnvCore::fresh();
    let (out, mut ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034: {:?}", out.verdict);

    nanoda_lib::tg::install_shared_core(core.clone());
    let before = core.fresh_var();
    run_checker(&export);
    let after = core.fresh_var();
    assert!(
        after.id() > before.id() + 1,
        "the checker minted from the shared Env — one pair of counters"
    );

    let pre = derived::prelude::prelude();
    let mc = core.machine(&pre).expect("the shared machine builds");
    let mm = ip.ind_apparatus().expect("mini's apparatus builds").mach.clone();
    assert!(Rc::ptr_eq(&mc, &mm), "one machine on both sides of the seam");
}

/// The same, checker first — the seam is order-independent: installing the
/// core before either engine has minted anything and running mini into the
/// signature the checker grew is the routing driver's other half-step.
#[test]
fn one_core_serves_both_engines_checker_then_mini() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let core = EnvCore::fresh();
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);

    let before = core.fresh_var();
    let (out, ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034 after the checker: {:?}", out.verdict);
    assert!(ip.core().same_core(&core));
    let after = core.fresh_var();
    assert!(after.id() > before.id() + 1, "mini minted from the Env the checker grew");
}
