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
/// interpretation's function symbols — plus, in `006`/`007`, beta reduction,
/// which does not.
///
/// `006` and `007` both reduce `(λ x y : Type. x) Prop (Prop → Prop)` in a
/// single two-argument contraction. The first argument is a sort, so its domain
/// premise is `x ∈ U(x)`; the second is an arrow, and needs
/// `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧`. That is now available: a non-dependent `Pi` is
/// interpreted as `derived::funspace`'s function space `fs`, and
/// `⊢ ∀a. fs(a,a) ∈ U(a)` is a theorem of that development.
const FULLY_DERIVED: &[&str] = &[
    "001_basicDef",
    "003_arrowType",
    "004_dependentType",
    "005_constType",
    "006_betaReduction",
    "007_betaReduction2",
    "008_forallSortWhnf",
];

/// Exports that still contain a gap, with the reason. Listing them explicitly
/// means a *newly* incomplete file shows up as a failure rather than going
/// unnoticed — and that closing a gap shows up too, as an unexpected pass.
///
/// Currently empty: every tutorial file this test names is fully derived. The
/// list (and the test over it) is kept because it is where the next partially
/// derived file belongs, and because an empty list is itself a claim worth
/// stating.
const HAS_GAPS: &[&str] = &[];

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

/// Beta is a *derivation*, not an admit.
///
/// The fixture reduces `(λ x y : Type. x) Prop Prop`, a two-argument contraction
/// under a `constType` that has to be delta-unfolded first. Every argument is a
/// sort, so both domain premises are instances of `x ∈ U(x)` and the whole file
/// comes out with no gaps at all. Asserting *zero* gaps rather than "the beta
/// gap is gone" is what makes this a test of the derivation rather than of the
/// wording of a report.
#[test]
fn beta_over_a_sort_argument_is_fully_derived() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/beta-sort-argument.ndjson");
    let (accepted, derived, gaps) = check(&f);
    assert!(accepted, "beta fixture: checker rejected a good file");
    assert!(derived > 0, "beta fixture: no steps derived at all");
    assert_eq!(gaps, 0, "beta fixture: beta is supposed to be derived, found {gaps} gap(s)");
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

/// Zeta reduction where the `let`'s expansion contains a **free variable**.
///
/// `let` is interpreted as an explicit definition of its expansion, so zeta is
/// the defining equation. When the expansion mentions Lean locals — i.e. kernel
/// free variables — those must become *parameters* of the defined symbol, since
/// `kernel::thm::define` refuses a body with a free variable it does not
/// abstract (that side condition was added after an unsoundness was found
/// without it).
///
/// Nothing in the arena corpus exercises this: zeta fires exactly once there,
/// in `032_letRed`, whose expansion is closed. This fixture is
/// `∀ x : Type, (let y := x; y) → x` proved by `λ x p. p`, which forces
/// `(let y := x; y) ≡ x` through definitional equality with the expansion being
/// the local `x`. Verified to genuinely reach zeta by temporarily forcing that
/// rule to admit and observing the gap appear.
///
/// The file still reports `pi congruence` gaps, which are unrelated; the
/// assertion is specifically that **no zeta gap** arises.
#[test]
fn zeta_with_a_free_variable_expansion() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/let-free-variable.ndjson");
    let (accepted, derived, _gaps) = check(&f);
    assert!(accepted, "checker rejected a well-typed file");
    assert!(derived > 0, "no steps derived at all");
    assert!(
        !gap_reasons(&f).iter().any(|r| r.contains("zeta")),
        "zeta gapped on a let whose expansion is a free variable: {:?}",
        gap_reasons(&f)
    );
}

/// The gap reasons reported for one export.
fn gap_reasons(export: &Path) -> Vec<String> {
    let cfg_path = std::env::temp_dir().join(format!("nanodatg-gaps-{}.json", std::process::id()));
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    String::from_utf8_lossy(&out.stderr)
        .lines()
        .filter(|l| l.trim_start().starts_with("gap:"))
        .map(|l| l.trim().to_string())
        .collect()
}
