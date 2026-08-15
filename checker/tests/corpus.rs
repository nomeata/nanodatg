//! Corpus tests: the checker must accept well-typed export files and — the part
//! that actually matters — reject ill-typed ones.
//!
//! A checker that accepts everything passes the positive tests trivially, so the
//! negative fixtures are the ones carrying the weight here.
//!
//! Two corpora are exercised:
//!
//! * `tests/fixtures/{good,bad}` — small, hand-written, committed to the repo,
//!   so `cargo test` always has negative coverage with no external download.
//! * `vendor/arena-tests/{good,bad}` — the full Lean Kernel Arena corpus (102
//!   good, 55 bad). Large, so it is gitignored; when absent these tests skip —
//!   which cargo reports as `ok`, so the skip goes through `ci/skip-guard.rs`
//!   and becomes a failure under `NANODATG_REQUIRE_CORPUS`, which `ci/check.sh`
//!   sets whenever the corpus is in fact there.
//!
//! Each file is checked in a subprocess. That is deliberate: the checker signals
//! rejection by panicking (`assert!`), and catching that in-process would be
//! both fragile and unable to distinguish a rejection from a genuine crash in
//! the harness.

use std::path::{Path, PathBuf};
use std::process::Command;

// SKIP is not PASS: `arena_corpus` below returns early when `vendor/arena-tests`
// is absent and cargo reports it `ok`. See ci/skip-guard.rs.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn repo_root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf() }

/// Run the checker on one export file; `true` means accepted.
fn accepts(export: &Path) -> bool { outcome(export).0 }

/// The same, keeping the checker's own output, so a refusal can be checked
/// against **its stated reason** and not merely counted.
///
/// The distinction matters for the one shape this repository declines that the
/// arena considers valid (see [`DECLINED_REASON`]): "we turned this away" and
/// "we turned this away *for the reason we think*" are different claims, and
/// only the second notices a file that starts failing for a new reason.
fn outcome(export: &Path) -> (bool, String) {
    let cfg_path = std::env::temp_dir().join(format!(
        "nanodatg-corpus-{}-{}.json",
        std::process::id(),
        export.file_name().unwrap().to_string_lossy()
    ));
    // `unsafe_permit_all_axioms` keeps the corpora's own axioms from counting as
    // errors — we are testing the type checker, not the axiom whitelist. The
    // nat/string extensions must be on or files containing literals are refused
    // outright, which would look like a type error but is not one.
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
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn checker");
    let _ = std::fs::remove_file(&cfg_path);
    let mut text = String::from_utf8_lossy(&out.stderr).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stdout));
    (out.status.success(), text)
}

fn ndjson_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(dir) else { return out };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            out.extend(ndjson_files(&p));
        } else if p.extension().is_some_and(|x| x == "ndjson") {
            out.push(p);
        }
    }
    out.sort();
    out
}

/// **The one shape Lean accepts and this checker turns away.**
///
/// The export format numbers names, levels and expressions by back-reference,
/// and nothing in it requires those indices to be dense or increasing. This
/// checker's parser requires both, and declines a file that is neither — a
/// *parser policy*, not a judgement that the file is ill-typed, which is why
/// the arena counts such a file apart rather than as a failure
/// (`scripts/arena.sh`, "the arena considers such files valid").
///
/// Measured 2026-08-15 over all 99 non-`perf` `good/` exports, **through
/// `nanoda_bin`, which is the binary this file spawns and the one
/// `scripts/arena.sh` gates**: exactly two files are turned away, both by this
/// policy, and no other `good/` file is refused for any reason.
///
/// Scoped to that binary deliberately. The *production* checker
/// (`CARGO_BIN_EXE_checker`, `bin/checker.rs:71`) declines a third —
/// `good/init-prelude.ndjson`, `declined: Nested inductive Lean.Syntax not
/// supported`, unless `--nested` — so "the corpus is fully accepted" is true of
/// the binary the gate runs and false of the binary the project ships. See
/// `TEST-INVENTORY.md` §7.1; it is not this test's subject and is not asserted
/// here.
///
/// `checker/tests/fixtures/declined/` holds a copy of both, because the arena
/// corpus is gitignored and a gap that is only visible when an optional
/// download is present is not documented. See
/// [`declined_fixtures_are_declined_for_the_stated_reason`].
const DECLINED_REASON: &str = "Back-refs must be continuous";

#[test]
fn committed_fixtures_good_are_accepted() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good");
    let files = ndjson_files(&dir);
    assert!(!files.is_empty(), "no committed good fixtures found in {}", dir.display());
    for f in files {
        assert!(accepts(&f), "expected {} to be ACCEPTED, but it was rejected", f.display());
    }
}

#[test]
fn committed_fixtures_bad_are_rejected() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bad");
    let files = ndjson_files(&dir);
    assert!(!files.is_empty(), "no committed bad fixtures found in {}", dir.display());
    for f in files {
        assert!(!accepts(&f), "expected {} to be REJECTED, but it was accepted", f.display());
    }
}

/// **The completeness gap, documented in the repository rather than in an
/// optional download.**
///
/// These two exports are `good/` corpus files — Lean accepts them — and this
/// checker refuses them, for the reason in [`DECLINED_REASON`]. Committed here
/// so the gap is visible with no corpus present, and asserted *with its reason*
/// so that three different futures are three different outcomes:
///
/// * the parser learns sparse back-refs — this test fails, saying the file is
///   now accepted, and the right response is to delete it and move both files
///   into `fixtures/good/`;
/// * the parser refuses them for some *new* reason — this test fails on the
///   message, rather than staying green on "still refused";
/// * nothing changes — green, and the repository still states what is missing.
///
/// The files are 4 and 6 lines and are the corpus's own; both are `axiom`
/// declarations over a `Sort`, so nothing about typing is involved and the only
/// thing under test is the index policy.
#[test]
fn declined_fixtures_are_declined_for_the_stated_reason() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/declined");
    let files = ndjson_files(&dir);
    assert_eq!(
        files.len(),
        2,
        "expected the two committed declined fixtures in {}, found {}",
        dir.display(),
        files.len()
    );
    for f in files {
        let (accepted, why) = outcome(&f);
        assert!(
            !accepted,
            "{} is now ACCEPTED. That is an improvement, not a failure: the parser has \
             learned a back-reference shape it used to decline. Move both fixtures to \
             tests/fixtures/good/, drop this test, and remove the skip in `arena_corpus` \
             and in scripts/arena.sh.",
            f.display()
        );
        assert!(
            why.contains(DECLINED_REASON),
            "{} is refused, but not for the reason this gap is documented under.\n\
             wanted a message containing: {DECLINED_REASON}\n\
             got:\n{why}",
            f.display()
        );
    }
}

#[test]
fn arena_corpus() {
    let corpus = repo_root().join("vendor/arena-tests");
    if skip_guard::absent(&corpus) {
        return
    }

    let mut failures = Vec::new();
    let (mut checked, mut declined) = (0usize, 0usize);
    // **A floor per leg, not one for the pair.** Task #137: "one counter lets a
    // healthy leg hide a dead one." This loop has two legs with opposite
    // expectations, and only the `bad` one carries the weight — a checker that
    // accepts everything passes `good` trivially. A single `checked > 0` over
    // the sum is satisfied by `good`'s 102 files alone, so an unpacked-short or
    // half-linked corpus could delete every negative case in the suite and
    // still report `ok`. Each leg is therefore counted and floored by name.
    let mut per_leg: Vec<(&str, usize)> = Vec::new();

    for (sub, expect_accept) in [("good", true), ("bad", false)] {
        let before = checked;
        for f in ndjson_files(&corpus.join(sub)) {
            // The perf files are large; they are a benchmark corpus, not a
            // correctness one, and would dominate test runtime.
            if f.components().any(|c| c.as_os_str() == "perf") {
                continue
            }
            // **Matched by reason, not by filename.** This used to be
            // `is_declined(&f)`, a hardcoded list of two names tested *before*
            // the checker ran — so `declined` was the constant 2 whatever the
            // checker did. A file that started being accepted (an improvement)
            // and a file that started failing for a new reason (a regression)
            // were both invisible: neither could move a number that was decided
            // by `file_name()`. Running it first and matching the message makes
            // the exclusion a measurement, and lets both of those fall through
            // to the ordinary check below.
            let (got, why) = outcome(&f);
            if expect_accept && !got && why.contains(DECLINED_REASON) {
                declined += 1;
                continue
            }
            checked += 1;
            if got != expect_accept {
                let want = if expect_accept { "accept" } else { "reject" };
                let had = if got { "accept" } else { "reject" };
                failures.push(format!("{}: expected {want}, got {had}", f.display()));
            }
        }
        per_leg.push((sub, checked - before));
    }

    let legs = per_leg.iter().map(|(s, n)| format!("{s}={n}")).collect::<Vec<_>>().join(" ");
    eprintln!("arena: checked={checked} declined={declined} legs[{legs}] failures={}", failures.len());
    for (sub, n) in &per_leg {
        assert!(
            *n > 0,
            "the `{sub}` leg of the arena corpus checked 0 files, so this test proved \
             nothing about it — the other leg's count is what kept `checked` nonzero. \
             Legs: {legs}. See {}",
            corpus.join(sub).display()
        );
    }
    assert!(checked > 0, "arena corpus directory exists but contained no files");
    assert!(failures.is_empty(), "{} of {checked} arena files mismatched ({declined} declined):\n  {}", failures.len(), failures.join("\n  "));
}
