//! The merged checker's command-line policy: split by default, old mini under
//! `--naive`, and no successful certification verdict while TG gaps remain.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn run_on(name: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_checker"))
        .args(args)
        .arg(fixture(name))
        .output()
        .expect("spawn unified checker")
}

fn run(args: &[&str]) -> Output { run_on("nat_char_equations.ndjson", args) }

#[test]
fn split_is_default_naive_is_explicit_and_tg_gaps_are_debt() {
    let split = run(&["--no-modelgen"]);
    let stdout = String::from_utf8_lossy(&split.stdout);
    assert_eq!(split.status.code(), Some(4), "{stdout}");
    assert!(stdout.contains("route\tmode=Split"), "the default did not use the split dispatch:\n{stdout}");
    assert!(stdout.contains("tg gaps:"), "TG incompleteness was hidden from the verdict:\n{stdout}");

    let acceptance = run(&["--no-modelgen", "--acceptance-only"]);
    assert_eq!(acceptance.status.code(), Some(0), "acceptance-only must ignore certification debt");

    let naive = run(&["--naive", "--no-modelgen"]);
    let stdout = String::from_utf8_lossy(&naive.stdout);
    assert_eq!(naive.status.code(), Some(0), "{stdout}");
    assert!(!stdout.contains("route\t"), "--naive entered the routed checker:\n{stdout}");
}

#[test]
fn default_does_not_run_minis_definition_checker() {
    let split = run_on(
        "budget_decline.ndjson",
        &["--no-modelgen", "--acceptance-only"],
    );
    let stdout = String::from_utf8_lossy(&split.stdout);
    assert_eq!(split.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("toMini=2\ttoChecker=1"), "{stdout}");

    let naive = run_on("budget_decline.ndjson", &["--naive", "--no-modelgen"]);
    let stdout = String::from_utf8_lossy(&naive.stdout);
    assert_eq!(naive.status.code(), Some(2), "{stdout}");
    assert!(stdout.contains("recursed past 2000 levels"), "{stdout}");
}

#[test]
fn default_checks_every_axiom_while_naive_keeps_its_ignore_rule() {
    let split = run_on(
        "unused_axiom_illtyped.ndjson",
        &["--no-modelgen", "--acceptance-only"],
    );
    let stdout = String::from_utf8_lossy(&split.stdout);
    let stderr = String::from_utf8_lossy(&split.stderr);
    assert_eq!(split.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.contains("reject\tbadAx"), "{stdout}");
    assert!(!stderr.contains("panicked"), "caught rejection leaked panic-hook noise:\n{stderr}");

    let naive = run_on(
        "unused_axiom_illtyped.ndjson",
        &["--naive", "--no-modelgen"],
    );
    let stdout = String::from_utf8_lossy(&naive.stdout);
    assert_eq!(naive.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("ignored axioms: badAx"), "{stdout}");
}
