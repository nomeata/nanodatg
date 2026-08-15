//! The merged checker's command-line policy: split by default, old mini under
//! `--naive`, and no successful certification verdict while TG gaps remain.


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
///
/// **The full-fixture ratchet moved 152 → 61, and both trades are written here.**
/// `TgBackend::iota_nat_clause_ready` added the direct-clause arm to the ι
/// readiness gate. Before it, every `Nat.rec` ι step inside a `PProd`
/// projection subject was refused — `Nat` is a direct clause and publishes no
/// class-(T) translation for the gate's only question — so `reduce_proj`
/// dropped the subject trace at all 14 `PProd` sites and `proj_red` admitted.
/// What is bought: `gap: proj_reduce` 14 → **0** and `gap: eq_cache` 2 → 0,
/// with their relays. What is paid, and it is a real cost: the escape ledger
/// rises 20 → 26, because a derivation that used to be admitted outright now
/// reaches the boundary carrying antecedents. That tranche alone is −87, which
/// is *better* than the −74 `NANODA_ASSUME=proj_reduce` priced, because the
/// deletion acquires the equation as an antecedent and this derives it.
///
/// Equality-query scope provenance is the second tranche, and it composes
/// additively: it closes four of those escapes at the judgement boundary
/// (26 → **22**) and takes the fixture 65 → **61**. Its own cost, two
/// `checkerSlots`, is written at the assertion that pins it.
///
/// The two ι counts are the ratchet that says the subject traces are actually
/// being consumed rather than the gate merely being quieter: they **rise**,
/// 10 → 17 at `Nat.zero` and 13 → 22 at `Nat.succ`. A change that widened the
/// gate without the ι rule certifying anything new would move the gap total
/// and leave these two alone.
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
    assert!(stdout.lines().next().is_some_and(|line| line.ends_with("tg gaps:61")), "the measured full-fixture baseline moved:\n{stdout}");
    assert!(
        stdout.contains("conditional derivations: 805 made (0 of them copies), 779 accounted for by a rule, 22 escaped"),
        "the full fixture retained conditional trace evidence:\n{stdout}",
    );
    assert!(
        stdout.contains("at the judgement boundary: 4 closed as the ambient context's own typings (4 atoms), 20 still conditional (5 of their atoms ambient)"),
        "the scope-provenance boundary row moved on the full fixture:\n{stdout}",
    );
    // 28, not the 30 this pinned before scope provenance landed, and the two
    // are a **measured cost of the boundary abstraction**, recorded here rather
    // than smoothed over.
    //
    // A certificate closed at the judgement boundary is a real `Thm` whose `Γ`
    // is the ambient context's typings. `ty_conv` composes the outermost
    // equality answer into the declaration's typing, so that typing inherits
    // the same `Γ` — and `Sealed`/`hypothesis_free` then correctly refuse to
    // persist it, because the store's key does not mention `Γ`. Two of this
    // fixture's declarations lose their stored `⟦c⟧ ∈ ⟦T⟧` that way
    // (`stored as ⟦c⟧ ∈ ⟦T⟧` 9 → 7, `uses answered from the store` 426 → 418,
    // both re-measured against `bad5c51` after the merge rather than carried
    // over from the branch's own pre-merge 319 → 311).
    //
    // It costs no gap: the fixture's total falls 65 → 61 and no file in
    // `vendor/arena-tests/good/tutorial` regresses (217 → 185 over the 91 of
    // them, with `072_sortElimProp2Rec` reaching zero). The refusal is the
    // conservative direction — an unstorable typing is re-derived, not
    // mis-stored — so the trade is taken and pinned. `adoptedByCheckerTyping`
    // is unchanged at 15, which is what says the *handoff* did not regress.
    assert!(stdout.contains("checkerSlots=28\tadoptedByCheckerTyping=15"), "the inductive typing handoff regressed:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.zero"), 17, "a zero iota certificate was lost:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.succ"), 22, "a successor iota certificate was lost:\n{stdout}");
    assert!(!stdout.contains("gap: proj_reduce"), "the PProd projection origin came back:\n{stdout}");
}

/// **The ι readiness gate has two arms, and the direct-clause one is new.**
///
/// `nat_char_equations`'s seventeen theorems are all `Eq.refl _` through Lean's
/// `brecOn`/`below` nest, whose step case projects the induction hypothesis out
/// of a `PProd`. Before `TgBackend::iota_nat_clause_ready` every one of those
/// projections was admitted, and the reason was **not** the projection rule:
/// the subject is a `Nat.rec` redex, `authoritative_reduction_ready` refused its
/// ι step because `Nat` is a `mini::direct` clause and publishes no class-(T)
/// translation for the gate's only question, `reduce_proj` therefore dropped the
/// subject trace, and `proj_red` was handed an unreduced subject whose head is a
/// recursor rather than a constructor.
///
/// What this pins, and how each line was falsified:
///
/// * **Deleting the new disjunct in `wants_proj_red_iota`** returns the fixture
///   to 148 gaps with `gap: proj_reduce` back at 14 and `gap: eq_cache` back at
///   2, and takes the two ι counts back to 10 and 13 — every assertion below
///   fails. That is the construction's own falsification and it is measured.
/// * **Making `iota_nat_clause_ready` return `true` unconditionally** is *not*
///   visible here: measured, every fixture in this directory is byte-identical,
///   including the `gap: iota:` rows of `mutual_aux_encoding` and
///   `ctor_abbrev_major`. It is visible on the export corpus —
///   `tutorial/076_listRecReduction` moves **45 → 48** — because that is where
///   recursors outside the `Nat` shape reach this gate. So the guard is real and
///   this file cannot see it; `tg_tutorial.rs`'s corpus ratchet is what does.
#[test]
fn nat_direct_clause_iota_readies_the_pprod_projection_subjects() {
    let full = run(&["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&full.stdout);
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 61, "the PProd projection ratchet moved:\n{stdout}");
    // The origin this tranche was scoped on, and the one that went with it.
    assert!(!stdout.contains("gap: proj_reduce"), "a PProd projection subject lost its iota evidence:\n{stdout}");
    assert!(!stdout.contains("gap: eq_cache"), "a cache hit lost the replayable Nat.rec trace:\n{stdout}");
    // The gate is a *prediction*: anything it readies must actually certify, or
    // the ledger trades a projection gap for an iota one and nets nothing.
    assert!(!stdout.contains("gap: iota:"), "a readied Nat.rec subject trace was not certified:\n{stdout}");
    assert!(!stdout.contains("gap: whnf"), "a subject trace drifted from its endpoints:\n{stdout}");
    // …and it must certify by *consuming* mini's Nat evidence, not by going
    // quiet. Both counts rise when the gate opens; a gate that merely stopped
    // asking would leave them where they were (10 and 13).
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.zero"), 17, "the zero carrier is not being consumed:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites computed at Nat.succ"), 22, "the successor carrier is not being consumed:\n{stdout}");
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
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 2, "the reduced-subject projection ratchet moved:\n{stdout}");
    assert!(
        stdout.contains("conditional derivations: 71 made (0 of them copies), 69 accounted for by a rule, 2 escaped"),
        "a direct-subject reduction parked conditional evidence:\n{stdout}",
    );
    // **This row is printed although the general path was never consulted, and
    // that is the point.** All the degenerate and dependent rows live in
    // `gen_report`, which used to return early on `GEN_BUILT == 0 && no
    // declines` — a gate about the *general* path standing in front of rows
    // about two other arms. On this fixture TG now adopts mini's carriers and
    // builds none of its own, so `declarations translated` is 0 and the early
    // return swallowed the whole section: the dependent arm fired and reported
    // nothing, and the assertion below read `no report row` rather than a
    // wrong number. `TEST-INVENTORY.md` §4.5 in reporting code.
    //
    // The two are asserted together so the shadow cannot come back unseen: if
    // the gate is ever narrowed to the general path again, `translated == 0`
    // is exactly the condition that hides the row beneath it.
    let translated = report_count(&stdout, "declarations translated");
    assert_eq!(
        translated, 0,
        "TG built {translated} carrier(s) of its own here; the row below is then printed for \
         the general path's reasons and stops witnessing the dependent arm:\n{stdout}"
    );
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
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 6, "the nested projection ratchet moved:\n{stdout}");
    assert!(
        stdout.contains("conditional derivations: 132 made (0 of them copies), 126 accounted for by a rule, 6 escaped"),
        "a nested-subject reduction parked conditional evidence:\n{stdout}",
    );
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
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 13, "the recursive-subject ratchet moved:\n{stdout}");
    assert_eq!(report_count(&stdout, "ι sites the DEPENDENT rule computed"), 22, "the structural cache replay did not consume Mini's dependent evidence:\n{stdout}");
    assert!(
        stdout.contains("conditional derivations: 433 made (0 of them copies), 417 accounted for by a rule, 13 escaped"),
        "a conditional reduction certificate was retained or the escape family moved:\n{stdout}",
    );
    // Scope provenance, pinned as an exact split rather than as a total.
    //
    // `addN`, `dblN` and `leN` each escaped with a single antecedent that was
    // nothing but an ambient local's own typing, and those are the three that
    // close. The other five ambient atoms are the four `N.brecOn.go`
    // certificates, which also carry raw beta obligations and so are *not*
    // closed — the row states that separately, so a change that closed them by
    // relabelling their raw debt would move this assertion rather than hide
    // inside the total. The eight atoms here are exactly the eight the escape
    // census counts as context-local typings.
    assert!(
        stdout.contains("at the judgement boundary: 3 closed as the ambient context's own typings (3 atoms), 13 still conditional (5 of their atoms ambient)"),
        "the ambient/query-opened split moved on the carrier fixture:\n{stdout}",
    );
    assert!(!stdout.contains("gap: eq_cache"), "a cache hit still lacks an exact structural recipe:\n{stdout}");
    assert!(!stdout.contains("gap: iota:"), "a ready N.rec subject trace was not certified:\n{stdout}");
    assert!(!stdout.contains("gap: proj_reduce"), "an applied projection lost its inner computation evidence:\n{stdout}");
    assert!(!stdout.contains("gap: whnf"), "application congruence was not recorded faithfully:\n{stdout}");

    let u0 = run_on("field_in_u0_by_carrier.ndjson", &["--no-modelgen", "--verbose"]);
    let stdout = String::from_utf8_lossy(&u0.stdout);
    assert_eq!(u0.status.code(), Some(0), "the zero-gap projection control regressed:\n{stdout}");
    assert_eq!(report_count(&stdout, "TOTAL gaps"), 0, "the zero-gap projection control moved:\n{stdout}");
}
