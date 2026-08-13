//! The merged checker's command-line policy: split by default, old mini under
//! `--naive`, and no successful certification verdict while TG gaps remain.

#![cfg(feature = "tg")]

use std::fs;
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

/// Run a declaration-boundary prefix of `nat_char_equations`. The three
/// boundaries below are deliberate mutations of one fixture: after `recAdd`,
/// after its zero theorem, and after its successor theorem. Keeping them as
/// prefixes avoids three copied exports drifting apart.
fn run_nat_prefix(lines: usize, args: &[&str]) -> Output {
    let source = fs::read_to_string(fixture("nat_char_equations.ndjson")).expect("read Nat fixture");
    let mut prefix = source.lines().take(lines).collect::<Vec<_>>().join("\n");
    prefix.push('\n');
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("target").join("test-prefixes");
    fs::create_dir_all(&dir).expect("create target/test-prefixes");
    let path = dir.join(format!("nat-{lines}-{}.ndjson", std::process::id()));
    fs::write(&path, prefix).expect("write Nat fixture prefix");
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .args(args)
        .arg(&path)
        .output()
        .expect("spawn unified checker on Nat prefix");
    fs::remove_file(path).expect("remove Nat fixture prefix");
    out
}

fn report_count(stdout: &str, label: &str) -> u64 {
    let line = stdout
        .lines()
        .find(|line| line.contains(label))
        .unwrap_or_else(|| panic!("no report row `{label}` in:\n{stdout}"));
    line.split_whitespace().last().expect("report count").parse().expect("numeric report count")
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

/// Mini owns `Nat`'s declaration and publishes its carrier, constructors and
/// recursor. TG checks each following declaration once, consuming those exact
/// terms and the shared lambda certificates. These declaration-boundary
/// mutations make a parallel TG Nat nest, or a return to abbreviation-only
/// iota, fail at the first affected equation rather than hiding in the full
/// fixture's aggregate debt.
#[test]
fn authoritative_nat_handoff_reaches_recadd_and_both_iota_equations() {
    let rec_add = run_nat_prefix(75, &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&rec_add.stdout);
    assert_eq!(rec_add.status.code(), Some(0), "recAdd stopped certifying:\n{stdout}");
    assert!(stdout.contains("route\tmode=Split\ttoMini=1\ttoChecker=1\tunclaimed=0"), "recAdd was not checked by exactly one dispatch:\n{stdout}");
    assert!(stdout.contains("adoptedByCheckerTyping=4"), "TG did not consume all four Nat typings:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 0, "recAdd acquired TG debt:\n{stdout}");

    let zero = run_nat_prefix(139, &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&zero.stdout);
    assert_eq!(zero.status.code(), Some(4), "the unrelated Eq typing debt moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 1, "the zero prefix's debt moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.zero"), 1, "recAddZero did not consume mini's zero carrier:\n{stdout}");
    assert!(!stdout.contains("iota: the constructor has no defining equation"), "TG demanded its retired Nat.zero abbreviation:\n{stdout}");

    let succ = run_nat_prefix(152, &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&succ.stdout);
    assert_eq!(succ.status.code(), Some(4), "the successor prefix's unrelated debt moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 7, "the successor prefix's debt moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.zero"), 1, "the zero ratchet regressed:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.succ"), 1, "recAddSucc did not consume the shared successor and recursor graphs:\n{stdout}");
    assert!(!stdout.contains("iota: the constructor has no defining equation"), "TG demanded its retired Nat.succ abbreviation:\n{stdout}");
    assert!(!stdout.contains("iota: the inductive has no defining equation"), "TG demanded its retired Nat carrier abbreviation:\n{stdout}");

    let full = run(&["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&full.stdout);
    assert_eq!(full.status.code(), Some(4), "the full fixture's known TG debt moved:\n{stdout}");
    assert!(stdout.lines().next().is_some_and(|line| line.ends_with("tg gaps:164")), "the measured full-fixture baseline moved:\n{stdout}");
    assert!(stdout.contains("checkerSlots=30\tadoptedByCheckerTyping=15"), "the inductive typing handoff regressed:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.zero"), 10, "a zero iota certificate was lost:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.succ"), 13, "a successor iota certificate was lost:\n{stdout}");
}

/// Mini owns the `Pair`/`Tri` declarations and publishes their class-(T)
/// translations. TG interprets projections with that shared machine, lifts
/// projection congruence through the same tuple projection, and consumes the
/// retained constructor computation rule for direct redexes. The projection
/// trace now also retains a subject's already-computed whnf certificate and
/// hands it to TG: delta-only, Mini's parameterless fieldless and unary
/// plain-recursive dependent-iota families, and nested projection subjects
/// compose without a second reduction. Other iota traces remain behind the
/// readiness gate, so exposing an independently unsupported rule cannot
/// increase the ledger.
#[test]
fn authoritative_projection_handoff_computes_direct_redexes_and_congruence() {
    let direct = run_on("proj_reduced_subject.ndjson", &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&direct.stdout);
    assert_eq!(direct.status.code(), Some(4), "the fixture's remaining TG debt moved:\n{stdout}");
    assert!(
        stdout.contains("route\tmode=Split\ttoMini=3\ttoChecker=10\tunclaimed=0"),
        "the projection fixture was not handled by the one dispatch loop:\n{stdout}",
    );
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 7, "the reduced-subject projection ratchet moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites the DEPENDENT rule computed"), 1, "Two.rec did not consume mini's dependent recursor evidence:\n{stdout}");
    assert!(!stdout.contains("gap: iota:"), "the ready Two.rec subject trace was not certified:\n{stdout}");
    assert!(!stdout.contains("gap: proj_reduce"), "the certified iota subject did not compose with projection computation:\n{stdout}");
    assert!(!stdout.contains("gap: whnf"), "a subject trace drifted from its endpoints:\n{stdout}");
    assert!(
        !stdout.contains("beta: the contracted body does not match its interpretation"),
        "the projection interpretation changed underneath a shared lambda graph:\n{stdout}",
    );

    let congr = run_on("proj_stuck_subject.ndjson", &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&congr.stdout);
    assert_eq!(congr.status.code(), Some(4), "the fixture's remaining TG debt moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 9, "the nested projection ratchet moved:\n{stdout}");
    assert!(!stdout.contains("gap: proj_reduce"), "a nested subject trace was not consumed:\n{stdout}");
    assert!(
        !stdout.contains("def_eq_proj: derived equation does not match the claim"),
        "projection congruence used the retired opaque spelling:\n{stdout}",
    );

    // The structural-recursion compiler's projection subjects reduce through
    // `N.rec` at both `N.z` and the applied recursive constructor `N.s n`.
    // Mini owns the carrier, dependent recursor, constructor nest and iota
    // evidence; TG composes those certificates without consulting its private
    // constructor bridge or running another reduction. Before the handoff this
    // was 139 gaps, including seven missing carrier equations and six missing
    // constructor equations. The initial carrier handoff computed 17 ready
    // iota sites and left three applied projections. Recording each as an
    // inner projection plus application congruence closes those origins and
    // exposes three further ready iota sites, so all 20 now compute. The first
    // exact lazy-delta recipe also lets the equality cache replay
    // `N.below motive N.z ≡ PUnit` without retaining its conditional theorem;
    // The recursive-constructor equality ends in a structurally equal PProd
    // application. Its retained recipe composes the successor reduction with
    // application congruence, whose differing argument is the exact earlier
    // `N.below` reduction in reverse; no conditional theorem is retained.
    let carrier = run_on("proj_reduced_carrier.ndjson", &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&carrier.stdout);
    assert_eq!(carrier.status.code(), Some(4), "the carrier fixture's verdict moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 24, "the recursive-subject ratchet moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites the DEPENDENT rule computed"), 22, "the structural cache replay did not consume Mini's dependent evidence:\n{stdout}");
    assert!(!stdout.contains("gap: eq_cache"), "a cache hit still lacks an exact structural recipe:\n{stdout}");
    assert!(!stdout.contains("gap: iota:"), "a ready N.rec subject trace was not certified:\n{stdout}");
    assert!(!stdout.contains("gap: proj_reduce"), "an applied projection lost its inner computation evidence:\n{stdout}");
    assert!(!stdout.contains("gap: whnf"), "application congruence was not recorded faithfully:\n{stdout}");

    let u0 = run_on("field_in_u0_by_carrier.ndjson", &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&u0.stdout);
    assert_eq!(u0.status.code(), Some(0), "the zero-gap projection control regressed:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 0, "the zero-gap projection control moved:\n{stdout}");
}
