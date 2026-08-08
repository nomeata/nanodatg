//! **The characteristic equations of Lean's `Nat` operations, as mini sees
//! them today.**
//!
//! `NAT-BRIDGE-FEASIBILITY.md` is the measurement; this is the measurement as a
//! test, so that the day it changes, it changes here first.
//!
//! The chain for efficient `Nat` needs, per operation, a theorem of the shape
//! *"any `f` satisfying these two equations equals the efficient
//! implementation"*, instantiated at `f := ⟦Nat.add⟧`. Instantiating it needs
//! the two equations **about the export's own `Nat.add`**, with a TG
//! certificate. The plan of record synthesises them as declarations proved by
//! `rfl` — which is exactly what `mini/tests/fixtures/nat_char_equations.lean`
//! writes down by hand, so this fixture *is* the synthesised declaration, one
//! step ahead of the generator.
//!
//! # Two axes, and they must not be conflated
//!
//! * **Acceptance** — does mini's `whnf`/`defeq` decide `Nat.add n 0 ≡ n`?
//!   Yes, all seventeen, and that has never been the question.
//! * **Certification** — does mini produce `⊢ ⟦Nat.add n 0⟧ = ⟦n⟧` as a kernel
//!   theorem? **All seventeen, and every one of the eight operations.** The run
//!   exits `0`.
//!
//! # What changed, and there is no residue left
//!
//! *(Rewritten twice. This module first said "**No**, for all seventeen" and
//! pinned `constEv = 14`, over twelve `proj(PProd)` and twelve `no-endpoint`;
//! `68ed247`/`3071105` took it to `32/38` and left the six *step* equations on
//! a single `proj(PProd)`. Those six are now closed too. Every cause was a
//! general defect in mini's projection handling that `Nat` merely exposed — see
//! `MINI-HANDOFF.md` §40 — and each has a `Nat`-free minimal reproduction in
//! `mini/tests/fixtures/proj_reduced_{carrier,subject}.lean` and
//! `mini/tests/fixtures/proj_stuck_subject.lean`. The expectations are
//! re-derived here rather than relaxed.)*
//!
//! `constEv` went **14/38 → 32/38 → 38/38**, `typeEv` 23 → 38, `valuesOk`
//! 32/38 → 38/38, gapped conversions 33 → **0**.
//!
//! **All four defects were the same defect.** A projection whose subject or
//! carrier had to be *computed*, a recursor whose major had to be *computed*,
//! and a projection whose subject reduced and **stayed stuck**, are one
//! sentence: a reduction performed for acceptance whose certificate was thrown
//! away. The labels this fixture wore — `proj(PProd)`, `no-endpoint` /
//! `proj(OfNat)`, `stuck-recursor(Nat.rec)`, and finally `proj(PProd)` again —
//! were four spellings of it.
//!
//! **The last one split base from step, and that was the clue.** Every *base*
//! equation certified a round before every *step* equation did, because a step
//! case is where the projection `f.1` is applied to an argument whose subject
//! never reaches a constructor: `whnf`'s `Expr::Proj` arm has three exits for
//! that, and all three returned the reduced expression alongside the unreduced
//! expression's certificate. Nothing about `Nat`, nothing about `PProd`, and
//! nothing about which field.
//!
//! `Nat.div` and `Nat.mod` are absent from the fixture and the reason is in its
//! header: they have no primitive-recursion characterisation to state at all.
//!
//! # This is the tripwire, and it has fired all the way
//!
//! `NAT-BRIDGE-FEASIBILITY.md` §4.4: *"the day `natAddZero` moves from
//! `proj(PProd)` to certified, `mini/tests/nat_equations.rs` fails, and that
//! failure is the signal to instantiate the bridge for real."* It fired on
//! `natAddZero` one round ago and the *pair* was still one short. It is not any
//! more: `natAddSucc` certifies, and so does every other step equation, so the
//! `(base, step)` pair each of the eight operations owes the bridge is complete.
//!
//! # Cost
//!
//! Certifying the six that were blocked made the fixture **cheaper**, which is
//! the opposite of every previous round here and is worth not smoothing over: a
//! certified reduction lets the walk stop where it used to keep looking.
//! Conversions `proved` went 561 387 → 465 655, −17.1 %. It is still minutes
//! rather than seconds in a debug build, for the reason `MINI-HANDOFF.md` §40
//! gives — nothing caches `infer_type` — but the half-hour figure this note
//! used to carry is gone with the gaps.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The seventeen equations, and the gap each waits on today. `None` means the
/// pair certifies.
///
/// Written out rather than derived: a change that moved one operation from one
/// gap to the other, or certified one of them, is the whole point of this
/// module, and a derived expectation would absorb it silently. **Every entry
/// is `None` now**, and the column is kept rather than deleted for the same
/// reason it was written out: the next regression here is a name acquiring a
/// gap, and a table of names with nothing to compare against would not show it.
const EXPECTED: &[(&str, Option<&str>)] = &[
    // the control: primitive recursion straight onto `Nat.rec`
    ("recAdd", None),
    ("recAddZero", None),
    ("recAddSucc", None),
    // **Every one of the eight operations certifies**, value and typing, and so
    // does the whole nest they are built out of. Before `68ed247` none of the
    // six in the fixture did.
    ("Nat.add", None),
    ("Nat.beq", None),
    ("Nat.ble", None),
    ("Nat.sub", None),
    ("Nat.mul", None),
    ("Nat.pow", None),
    ("Nat.pred", None),
    // the nest's own scaffolding, which certified before this round too
    ("Nat.below", None),
    ("Nat.brecOn", None),
    ("Nat.brecOn.go", None),
    ("Nat.casesOn", None),
    ("Nat.add.match_1", None),
    ("Nat.beq.match_1", None),
    ("Nat.ble.match_1", None),
    ("Nat.mul.match_1", None),
    // **`Nat.pow.match_1` is the one the old table called a *different and
    // earlier* blocker**, because it carries `OfNat.ofNat Nat 0 (instOfNatNat
    // 0)` in its motive and the run recorded `convGap:proj(OfNat) = 2`. It was
    // a projection like the others.
    ("Nat.pow.match_1", None),
    ("OfNat.ofNat", None),
    ("instOfNatNat", None),
    // ── the seventeen equations ─────────────────────────────────────────────
    //
    // **Every base case and every step case.** The base/step split was the
    // whole residue for one round and it crossed all six operations, which is
    // what said the remaining cause was structural rather than per-operation:
    // a step case is where `f.1`'s subject reduces and never reaches a
    // constructor, and `whnf`'s three stuck exits returned the reduct with the
    // *un*reduced expression's certificate. `natSubSucc` was the last one
    // wearing a different label — `Gap::StuckRecursor`, the same defect in the
    // recursor arm, because `Nat.sub`'s step goes through `Nat.pred`.
    ("natAddZero", None),
    ("natAddSucc", None),
    ("natSubZero", None),
    ("natSubSucc", None),
    ("natMulZero", None),
    ("natMulSucc", None),
    ("natPowZero", None),
    ("natPowSucc", None),
    ("natBeqZZ", None),
    ("natBeqZS", None),
    ("natBeqSZ", None),
    ("natBeqSS", None),
    ("natBleZ", None),
    ("natBleSZ", None),
    ("natBleSS", None),
];


fn fixture() -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join("nat_char_equations.ndjson");
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini <flags> <fixture>` in a subprocess — `checker`'s parser reports a
/// declined export by calling `std::process::exit(2)`, which an in-process
/// harness cannot contain.
fn run(flags: &[&str]) -> (Option<i32>, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_mini"));
    cmd.arg("--no-modelgen");
    for f in flags {
        cmd.arg(f);
    }
    let out = cmd.arg(fixture()).output().expect("spawn mini");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
}

/// The `evidence` row's plain counters, `waiting:` keys excluded.
fn evidence(stdout: &str) -> BTreeMap<String, u64> {
    let Some(line) = stdout.lines().find(|l| l.starts_with("evidence\t")) else {
        panic!("no `evidence` row in:\n{stdout}")
    };
    let mut m = BTreeMap::new();
    for kv in line.split('\t').skip(1) {
        if let Some((k, v)) = kv.split_once('=') {
            if !k.starts_with("waiting:") {
                m.insert(k.to_string(), v.parse().unwrap_or(0));
            }
        }
    }
    m
}

/// Every `(declaration, gap)` the `--dump-theorems` constants section reports,
/// with `None` for a pair whose constant typing is in hand.
fn certification(stdout: &str) -> BTreeMap<String, Option<String>> {
    let mut m = BTreeMap::new();
    let mut name: Option<String> = None;
    let mut in_constants = false;
    for l in stdout.lines() {
        if l.starts_with("── constants") {
            in_constants = true;
            continue;
        }
        if l.starts_with("── ") {
            in_constants = false;
        }
        if !in_constants {
            continue;
        }
        if let Some(rest) = l.strip_prefix("  ") {
            if !rest.starts_with(' ') && !rest.is_empty() {
                name = rest.split_whitespace().next().map(str::to_string);
                continue;
            }
        }
        let t = l.trim_start();
        if let Some(rest) = t.strip_prefix("typing   ") {
            let Some(n) = name.clone() else { continue };
            let gap = rest
                .split_once("waiting on ")
                // the reason is parenthesised by the dump's own message, so
                // exactly one `)` comes off — `trim_end_matches` would eat the
                // gap's own, and `proj(PProd` is not a gap name.
                .map(|(_, g)| g.strip_suffix(')').unwrap_or(g).to_string());
            m.insert(n, gap);
        }
    }
    assert!(!m.is_empty(), "no constants section in:\n{stdout}");
    m
}

/// **Acceptance: yes.** mini's conversion decides every one of the seventeen
/// equations, `Nat.add n 0 ≡ n` and `Nat.add n (m+1) ≡ Nat.succ (Nat.add n m)`
/// included, and the export is accepted.
///
/// This is the axis the synthesised-declaration plan needs first: a declaration
/// the checker refuses cannot be added to the environment at all. It passing
/// says the `brecOn`/`below` nest is not an *acceptance* problem, so the plan
/// is viable at that level, whatever the certification row says.
#[test]
fn mini_accepts_every_characteristic_equation() {
    let (code, stdout) = run(&["--acceptance-only", "--verbose"]);
    assert_eq!(code, Some(0), "the fixture was not accepted:\n{stdout}");
    assert!(
        stdout.lines().next().is_some_and(|l| l.contains("\taccept\t")),
        "expected an accept verdict:\n{stdout}"
    );
}

/// **Certification: all seventeen.**
///
/// The per-declaration gap is still pinned rather than counted, and now that
/// every entry is `None` that is the *only* form the pin can usefully take: a
/// count would report a regression as "38 → 37" and say nothing about which of
/// the eight operations, or whether it was a base case or a step case. That
/// distinction is what carried the last three rounds here.
///
/// The `Nat.rec` control certifies, as it always did. It is what makes the
/// rest a comparison: `recAdd` states the same two equations about the same
/// recursion without going through the elaborator's structural compiler, so a
/// regression that broke primitive recursion itself shows up here and is not
/// confusable with the nest.
#[test]
fn every_characteristic_equation_certifies() {
    let (code, stdout) = run(&["--verbose", "--dump-theorems"]);
    assert_eq!(code, Some(0), "expected accept with everything certified (0):\n{stdout}");

    let got = certification(&stdout);
    for (decl, want) in EXPECTED {
        let have = got
            .get(*decl)
            .unwrap_or_else(|| panic!("{decl} is not in the fixture's constants:\n{stdout}"));
        assert_eq!(
            have.as_deref(),
            *want,
            "{decl}: expected {want:?}, got {have:?}\n{stdout}"
        );
    }

    let ev = evidence(&stdout);
    assert_eq!(ev["pairs"], 38, "the fixture's pair population changed:\n{stdout}");
    assert_eq!(ev["constEv"], 38, "the certified-constant count changed:\n{stdout}");
    assert_eq!(ev["typeEv"], 38, "a type typing stopped deriving:\n{stdout}");
    assert_eq!(ev["unsealed"], 0, "a certificate came back unsealed:\n{stdout}");
    // **Not one conversion left uncertified**, which `constEv` alone does not
    // say: a pair whose typing derives can still have reached the walk's end
    // through a gapped conversion somewhere below it.
    let convs = row_of(&stdout, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "a conversion is still gapped:\n{stdout}");
}

/// The `key=value` pairs of one tab-separated row.
fn row_of(stdout: &str, prefix: &str) -> BTreeMap<String, u64> {
    let Some(line) = stdout.lines().find(|l| l.starts_with(&format!("{prefix}\t"))) else {
        panic!("no `{prefix}` row in:\n{stdout}")
    };
    line.split('\t')
        .skip(1)
        .filter_map(|kv| kv.split_once('='))
        .filter_map(|(k, v)| v.parse().ok().map(|n| (k.to_string(), n)))
        .collect()
}
