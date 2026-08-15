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
fn accepts(export: &Path) -> bool {
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
    let status = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn checker");
    let _ = std::fs::remove_file(&cfg_path);
    status.status.success()
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

/// Upstream nanoda *declines* export files whose name/level back-references are
/// not densely numbered. That is a parser policy, not a judgement that the file
/// is ill-typed, so such files are not counted as type-checking failures.
fn is_declined(export: &Path) -> bool {
    let name = export.file_name().unwrap().to_string_lossy();
    name == "sparse-name-index.ndjson" || name == "level-index-out-of-order.ndjson"
}

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
            if expect_accept && is_declined(&f) {
                declined += 1;
                continue
            }
            checked += 1;
            let got = accepts(&f);
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
