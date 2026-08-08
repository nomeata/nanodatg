//! SKIP is not PASS, for the Rust test suites.
//!
//! `ci/check.sh` learned this the hard way three times in one day — `modelgen`
//! had no step at all, `monotest`'s 107 checks were entirely unrun, and
//! `scripts/mini-vs-nanoda.sh` was never invoked — and the shell side now
//! answers it with exit 77 (SKIP, and *not* PASS) plus a count guard on every
//! step. The Rust side had the same hole and is the larger surface: **41
//! `#[test]` functions** across `checker/tests/{corpus,tg_tutorial}.rs` and
//! `mini/tests/{tutorial,dump}.rs` return early when `vendor/arena-tests` is
//! absent, and `cargo test` reports every one of them `ok`. The corpus is
//! gitignored for size (17 MB; `README.md` says how to fetch it), so on any
//! machine that has not fetched it those 41 tests are green having executed
//! nothing, and no summary line says so.
//!
//! This file is the one place a test suite is allowed to decide "I cannot run".
//! It is not a module of any crate: each suite pulls it in with
//!
//! ```ignore
//! #[path = "../../ci/skip-guard.rs"]
//! mod skip_guard;
//! ```
//!
//! which keeps one copy of the rule for two crates without adding a workspace
//! member or touching `checker/Cargo.toml` — `checker/` is an inherited fork
//! whose diff against upstream is an advertised audit artefact, and `mini`
//! reuses it unchanged.
//!
//! # The rule
//!
//! A skip stays a skip for a developer and becomes a **failure** for CI:
//!
//! * `NANODATG_REQUIRE_CORPUS` unset — the historical behaviour, unchanged. A
//!   fresh clone with no corpus still gets a useful `cargo test`: the committed
//!   fixtures under `checker/tests/fixtures` and `mini/tests/fixtures` run, so
//!   there is always negative coverage, exactly as `README.md` promises.
//! * `NANODATG_REQUIRE_CORPUS=1` — a skip panics, naming the path. `ci/check.sh`
//!   exports it *only when `vendor/arena-tests` is actually present*, so a CI
//!   machine without the corpus does not turn a legitimate absence into a red;
//!   it reports a SKIP step instead, and the summary says "all checks that ran
//!   passed".
//!
//! `NANODATG_REQUIRE_MODELGEN` is the same rule for the one test that needs the
//! Lean-built `modelgen` binary rather than the corpus.
//!
//! # Why a guard at every site, and not one global assertion
//!
//! A single "the corpus directory exists" test would catch the common case and
//! miss the rest: five of the 41 sites are gated on an *individual* export
//! (`good/init-prelude.ndjson`, `073_boolRecEqns`, …), so a corpus that unpacked
//! short would still skip them silently with the directory in place. Routing
//! every site through one predicate costs one line per site and cannot be
//! fooled that way.
//!
//! # Why this file self-tests
//!
//! [`the_guard_fails_when_the_input_is_required`] runs in every suite that
//! includes this module, so `ci/check.sh` watches the panic path fire on every
//! run. A guard nobody has watched fail is not known to work — that is the
//! whole lesson, and it is why every shell step landed alongside this one
//! carries a `--self-test`.

#![allow(dead_code)]

use std::path::Path;

/// The corpus variable. Exported by `ci/check.sh` when `vendor/arena-tests` is
/// present.
const CORPUS: &str = "NANODATG_REQUIRE_CORPUS";
/// The toolchain variable, for the one test that execs `modelgen`.
const MODELGEN: &str = "NANODATG_REQUIRE_MODELGEN";

/// Set, non-empty, and not `0`.
fn required(var: &str) -> bool {
    std::env::var_os(var).is_some_and(|v| !v.is_empty() && v != "0")
}

/// The decision, with the environment factored out so it can be self-tested
/// without mutating a process-global variable under a parallel test harness.
///
/// Returns `true` — "skip" — or panics.
fn decide(required: bool, var: &str, what: &str, detail: &str) -> bool {
    assert!(
        !required,
        "{var}=1, but this test would have SKIPPED: {what} — {detail}.\n\
         A skip reports `ok` to cargo, so under {var} it is a failure instead. \
         Either provide the input or unset {var}."
    );
    eprintln!("SKIP: {what} — {detail}. This test ran nothing. Set {var}=1 to make that a failure.");
    true
}

/// `true` when `p` is not there and the caller should return early.
///
/// Deliberately `exists()` rather than the `is_dir()`/`is_file()` the call sites
/// used to spell out: a path of the wrong *kind* is a broken corpus, and letting
/// the test proceed and fail loudly beats skipping it.
pub fn absent(p: &Path) -> bool {
    !p.exists()
        && decide(
            required(CORPUS),
            CORPUS,
            "the arena corpus",
            &format!("{} is absent (gitignored for size; see README.md)", p.display()),
        )
}

/// The counted form, for a suite that reads a whole directory: `true` when it
/// found nothing to work on.
///
/// This is the Rust half of the shell steps' "count what executed and report
/// BROKEN on zero". It fires on a *present but empty* directory too, which the
/// hand-rolled `if files.is_empty()` skips it replaces did not distinguish from
/// an absent one — an unpacked-short corpus is exactly as unmeasured as a
/// missing one.
pub fn no_inputs(dir: &Path, n: usize) -> bool {
    n == 0
        && decide(
            required(CORPUS),
            CORPUS,
            "the arena corpus",
            &format!("{} yielded 0 export files", dir.display()),
        )
}

/// `true` when a tool the test execs has not been built.
///
/// Separate from [`absent`] because the input is separate: `modelgen` is a Lean
/// package, `ci/check-modelgen.sh` is what builds it, and a machine with no Lean
/// toolchain legitimately has neither.
pub fn tool_absent(p: &Path, hint: &str) -> bool {
    !p.exists()
        && decide(
            required(MODELGEN),
            MODELGEN,
            "a tool this test execs",
            &format!("{} is not built — {hint}", p.display()),
        )
}

/// The skip path: reports "skip me" and does not panic.
#[test]
fn the_guard_skips_when_the_input_is_optional() {
    assert!(decide(false, CORPUS, "a thing", "it is not here"), "an optional missing input is a skip");
}

/// **The panic path, watched firing on every `cargo test`.**
///
/// Verified to be load-bearing by making `decide` return `true` unconditionally:
/// this test fails and [`the_guard_skips_when_the_input_is_optional`] does not,
/// so the pair pins both directions.
#[test]
fn the_guard_fails_when_the_input_is_required() {
    let r = std::panic::catch_unwind(|| decide(true, CORPUS, "a thing", "it is not here"));
    assert!(r.is_err(), "a required missing input must fail, not skip — that is the whole point of this file");
}

/// A present path is not a skip in either mode, so the guard costs a `stat` and
/// changes nothing when the corpus is there.
#[test]
fn a_present_path_is_never_a_skip() {
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    assert!(!absent(here), "an existing path must not be reported absent");
    assert!(!no_inputs(here, 3), "a non-zero count must not be reported empty");
}
