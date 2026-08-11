//! The merged checker's command-line policy: split by default, old mini under
//! `--naive`, and no successful certification verdict while TG gaps remain.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_checker"))
        .args(args)
        .arg(fixture("nat_char_equations.ndjson"))
        .output()
        .expect("spawn unified checker")
}

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
