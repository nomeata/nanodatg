//! End-to-end tests for the Tarski–Grothendieck backend.
//!
//! These assert something stronger than "the checker accepted the file": they
//! assert that for the listed tutorial exports, **every** definitional-equality
//! step was discharged by a real kernel derivation, with no gaps. That is the
//! property the whole project exists to establish, so it is worth a test that
//! fails the moment a step silently starts being taken on trust.
//!
//! Only meaningful with `--features tg`; otherwise the backend is
//! `NullCertifier` and there is nothing to check.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::process::Command;

fn corpus() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests") }

/// Run one export and return (accepted, derived_count, gap_count).
fn check(export: &Path) -> (bool, u64, u64) {
    let cfg_path =
        std::env::temp_dir().join(format!("nanodatg-tg-{}-{}.json", std::process::id(), export.file_name().unwrap().to_string_lossy()));
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

    let text = String::from_utf8_lossy(&out.stderr);
    let grab = |label: &str| -> u64 {
        text.lines()
            .find(|l| l.trim_start().starts_with(label))
            .and_then(|l| l.split_whitespace().last())
            .and_then(|n| n.parse().ok())
            .unwrap_or(u64::MAX)
    };
    (out.status.success(), grab("derived (real kernel Thm)"), grab("TOTAL gaps"))
}

/// Tutorial exports the TG kernel can currently discharge completely.
///
/// These exercise `Sort`, `Pi`/arrow types, dependent types, constants and
/// weak-head normalisation of foralls — the equational fragment, which follows
/// from the equality axioms alone and so needs no defining axioms for the
/// interpretation's function symbols.
const FULLY_DERIVED: &[&str] = &[
    "001_basicDef",
    "003_arrowType",
    "004_dependentType",
    "005_constType",
    "008_forallSortWhnf",
];

/// Exports that still contain a gap, with the reason. Listing them explicitly
/// means a *newly* incomplete file shows up as a failure rather than going
/// unnoticed — and that closing a gap shows up too, as an unexpected pass.
const HAS_GAPS: &[&str] = &[
    // Beta needs `lam`/`app` to denote a function and its application, which
    // requires defining axioms the signature deliberately does not yet have.
    "006_betaReduction",
    "007_betaReduction2",
];

#[test]
fn tutorial_files_are_fully_derived() {
    let dir = corpus().join("good/tutorial");
    if !dir.is_dir() {
        eprintln!("skipping: no arena corpus at {}", dir.display());
        return
    }
    for name in FULLY_DERIVED {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        assert_eq!(gaps, 0, "{name}: expected a complete derivation, found {gaps} gap(s)");
        assert!(derived > 0, "{name}: reported no derivation steps at all — is the backend wired up?");
    }
}

#[test]
fn files_with_known_gaps_are_still_accepted() {
    let dir = corpus().join("good/tutorial");
    if !dir.is_dir() {
        return
    }
    for name in HAS_GAPS {
        let f = dir.join(format!("{name}.ndjson"));
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        // The point of these is that the gap is *reported*, not hidden.
        assert!(gaps > 0, "{name}: expected a reported gap; if this now derives fully, move it to FULLY_DERIVED");
        assert!(derived > 0, "{name}: no steps derived at all");
    }
}

/// The backend must not change what the checker accepts or rejects — it only
/// adds evidence. An ill-typed file must still be rejected with TG active.
#[test]
fn tg_backend_still_rejects_bad_files() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bad");
    for entry in std::fs::read_dir(&dir).expect("fixtures/bad").flatten() {
        let p = entry.path();
        if p.extension().is_some_and(|e| e == "ndjson") {
            let (accepted, _, _) = check(&p);
            assert!(!accepted, "{}: accepted an ill-typed file with the TG backend", p.display());
        }
    }
}
