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
//!   Yes. Every one of the seventeen equations is accepted, and
//!   `--acceptance-only` exits `0`. mini's conversion is a faithful port of
//!   mini-lean's, and Lean's own `Nat.add_zero` is `rfl`, so this is the
//!   expected answer — but it is the answer that would be a serious bug if it
//!   ever became `no`, so it is pinned.
//! * **Certification** — does mini produce `⊢ ⟦Nat.add n 0⟧ = ⟦n⟧` as a kernel
//!   theorem? **No**, for all seventeen. The plain run exits `4`.
//!
//! # What distinguishes the one that certifies
//!
//! `recAdd` is the same recursion written straight onto `Nat.rec`, and it
//! certifies — value, typing, and both equations. Everything that went through
//! Lean's structural-recursion compiler does not. So the obstruction is not
//! `Nat`, not `Nat.rec`, and not primitive recursion: it is the
//! `brecOn`/`below` nest the elaborator emits.
//!
//! Two distinct gaps, and the fixture separates them:
//!
//! * `add`, `beq`, `ble` — `proj(PProd)`, a **library** gap. The nest's step
//!   case is `Nat.succ (f.1 n)` where `f : Nat.below motive (Nat.succ m)`, so
//!   the projection's subject has a type that only *reduces* to `PProd`.
//!   `Nat.below`, `Nat.brecOn`, `Nat.brecOn.go`, `Nat.casesOn` and
//!   `Nat.add.match_1` all certify on their own — only the operation itself
//!   does not.
//! * `sub`, `mul`, `pow` — `no-endpoint`, a **threading** gap, and it fires
//!   *earlier*: `Nat.pow.match_1` (which `Nat.pred` and `Nat.sub` share) has
//!   `OfNat.ofNat Nat 0 (instOfNatNat 0)` in its motive, and that numeral
//!   wrapper is uncertified before the nest is ever reached. So those three are
//!   blocked twice over.
//!
//! `Nat.div` and `Nat.mod` are absent from the fixture and the reason is in its
//! header: they have no primitive-recursion characterisation to state at all.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The seventeen equations, and the gap each waits on today. `None` means the
/// pair certifies.
///
/// Written out rather than derived: a change that moved one operation from one
/// gap to the other, or certified one of them, is the whole point of this
/// module, and a derived expectation would absorb it silently.
const EXPECTED: &[(&str, Option<&str>)] = &[
    // the control: primitive recursion straight onto `Nat.rec`
    ("recAdd", None),
    ("recAddZero", None),
    ("recAddSucc", None),
    // Lean's own operations, and the equations about them
    ("Nat.add", Some("proj(PProd)")),
    ("natAddZero", Some("proj(PProd)")),
    ("natAddSucc", Some("proj(PProd)")),
    ("Nat.beq", Some("proj(PProd)")),
    ("natBeqZZ", Some("proj(PProd)")),
    ("natBeqZS", Some("proj(PProd)")),
    ("natBeqSZ", Some("proj(PProd)")),
    ("natBeqSS", Some("proj(PProd)")),
    ("Nat.ble", Some("proj(PProd)")),
    ("natBleZ", Some("proj(PProd)")),
    ("natBleSZ", Some("proj(PProd)")),
    ("natBleSS", Some("proj(PProd)")),
    ("Nat.sub", Some("no-endpoint")),
    ("natSubZero", Some("no-endpoint")),
    ("natSubSucc", Some("no-endpoint")),
    ("Nat.mul", Some("no-endpoint")),
    ("natMulZero", Some("no-endpoint")),
    ("natMulSucc", Some("no-endpoint")),
    ("Nat.pow", Some("no-endpoint")),
    ("natPowZero", Some("no-endpoint")),
    ("natPowSucc", Some("no-endpoint")),
    // the nest's own scaffolding, which certifies — so the obstruction is the
    // operation's use of it, not the scaffolding
    ("Nat.below", None),
    ("Nat.brecOn", None),
    ("Nat.brecOn.go", None),
    ("Nat.casesOn", None),
    ("Nat.add.match_1", None),
    ("Nat.beq.match_1", None),
    ("Nat.ble.match_1", None),
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

/// **Certification: no, and exactly where.**
///
/// Seventeen equations, none certified; the `Nat.rec` control certified. The
/// per-declaration gap is pinned because the two gaps have different causes and
/// different owners — `proj(PProd)` is a library item, `no-endpoint` is
/// threading debt — and a change that fixed one without the other must show up
/// as a readable diff rather than a count that moved.
#[test]
fn none_of_the_equations_certify_and_the_nat_rec_control_does() {
    let (code, stdout) = run(&["--verbose", "--dump-theorems"]);
    assert_eq!(code, Some(4), "expected accept-with-uncertified (4):\n{stdout}");

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
    assert_eq!(ev["constEv"], 14, "the certified-constant count changed:\n{stdout}");
    assert_eq!(ev["unsealed"], 0, "a certificate came back unsealed:\n{stdout}");
}
