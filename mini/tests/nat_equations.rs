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
//!   theorem? **Eleven of the seventeen, and every one of the eight
//!   operations.** The run still exits `4`, on six.
//!
//! # What changed, and what the residue is
//!
//! *(Rewritten at `68ed247`/`3071105`. This module used to say "**No**, for all
//! seventeen" and pin `constEv = 14`; the table below was twelve
//! `proj(PProd)` and twelve `no-endpoint`. Both causes were general defects in
//! mini's projection handling that `Nat` merely exposed — see
//! `MINI-HANDOFF.md` §40 — and each now has a `Nat`-free minimal reproduction
//! in `mini/tests/fixtures/proj_reduced_{carrier,subject}.lean`. The
//! expectations are re-derived here rather than relaxed.)*
//!
//! `constEv` went **14/38 → 32/38**, `typeEv` 23 → 38, `valuesOk` 32/38 →
//! 38/38.
//!
//! **The two causes turned out to be one.** The table used to split the
//! operations three ways: `add`/`beq`/`ble` on `proj(PProd)`, and
//! `sub`/`mul`/`pow` on a *different and earlier* `no-endpoint` whose real
//! content was `Nat.pow.match_1` carrying `OfNat.ofNat Nat 0 (instOfNatNat 0)`
//! in its motive. That second group is gone: `OfNat.ofNat`, `instOfNatNat`,
//! `Nat.pow.match_1`, `Nat.pred` and `Nat.sub` all certify now, and
//! `natMulSucc`/`natPowSucc` wait on the *same* `proj(PProd)` as
//! `natAddSucc`. The `OfNat` projection was a projection like the others and
//! was fixed by the same change.
//!
//! **The residue is exactly the successor equations, and that is the finding.**
//! Every *base* equation certifies — `natAddZero`, `natSubZero`, `natMulZero`,
//! `natPowZero`, `natBeqZZ`, `natBeqZS`, `natBeqSZ`, `natBleZ`, `natBleSZ` —
//! and so does every operation's own value and typing. What does not is the
//! six equations whose left-hand side reduces through the nest's **step**
//! case, where the projection `f.1` is *applied* to an argument. Whoever picks
//! this up should start there: the split is base-versus-step, not
//! operation-by-operation, and no operation is special.
//!
//! `Nat.div` and `Nat.mod` are absent from the fixture and the reason is in its
//! header: they have no primitive-recursion characterisation to state at all.
//!
//! # This is the tripwire, and it has fired
//!
//! `NAT-BRIDGE-FEASIBILITY.md` §4.4: *"the day `natAddZero` moves from
//! `proj(PProd)` to certified, `mini/tests/nat_equations.rs` fails, and that
//! failure is the signal to instantiate the bridge for real."* It has.
//! `natAddZero` certifies; `natAddSucc` does not, so the *pair* the bridge
//! needs is still one short.
//!
//! # Cost
//!
//! This fixture takes about half an hour in a debug build, against 8.8 s
//! before. Nothing caches `infer_type` and certifying one ι through a recursor
//! is thousands of conversions; `MINI-HANDOFF.md` §40 has the three memos that
//! were tried and what each measured. It is the reason
//! `designed::a_projection_certifies_when_its_carrier_has_to_be_computed` is
//! `#[ignore]`d and this module is not: this is the measurement of record.

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
    // **Every base case certifies and every step case does not.** That split is
    // the whole residue, it crosses all six operations, and it is what the next
    // round is about — not `add` versus `sub`, and not `PProd` versus `OfNat`.
    ("natAddZero", None),
    ("natAddSucc", Some("proj(PProd)")),
    ("natSubZero", None),
    // The one residual that is not `proj(PProd)`. `Nat.sub`'s step goes through
    // `Nat.pred`, which certifies, so this is no longer the numeral wrapper the
    // old table blamed; it is unclassified and it is the odd one out of six.
    ("natSubSucc", Some("no-endpoint")),
    ("natMulZero", None),
    ("natMulSucc", Some("proj(PProd)")),
    ("natPowZero", None),
    ("natPowSucc", Some("proj(PProd)")),
    ("natBeqZZ", None),
    ("natBeqZS", None),
    ("natBeqSZ", None),
    ("natBeqSS", Some("proj(PProd)")),
    ("natBleZ", None),
    ("natBleSZ", None),
    ("natBleSS", Some("proj(PProd)")),
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

/// **Certification: eleven of seventeen, and exactly where the other six are.**
///
/// The per-declaration gap is pinned rather than counted, because the split
/// that matters is not visible in a count. `constEv` alone would report this
/// round as "14 → 32" and hide the two things worth knowing: that the
/// `no-endpoint`/`proj(OfNat)` group merged into `proj(PProd)` instead of
/// closing separately, and that what remains is *every step case and no base
/// case*.
///
/// The `Nat.rec` control certifies, as it always did. It is what makes the
/// rest a comparison: `recAdd` states the same two equations about the same
/// recursion without going through the elaborator's structural compiler, so a
/// regression that broke primitive recursion itself shows up here and is not
/// confusable with the nest.
#[test]
fn eleven_of_the_equations_certify_and_the_residue_is_every_step_case() {
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
    assert_eq!(ev["constEv"], 32, "the certified-constant count changed:\n{stdout}");
    assert_eq!(ev["typeEv"], 38, "a type typing stopped deriving:\n{stdout}");
    assert_eq!(ev["unsealed"], 0, "a certificate came back unsealed:\n{stdout}");
}
