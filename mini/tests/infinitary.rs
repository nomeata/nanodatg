//! **Infinitary branching, end to end** — the one shape of Lean inductive the
//! `ω`-tower cannot hold, measured on a real export.
//!
//! `NTree.node : (N → NTree) → NTree` is ordinary Lean. `mini` accepts the
//! file, computes the eliminator class, interprets every clause — and cannot
//! place the carrier, because `derived/src/cumul/bounded.rs` closes the tower
//! `T = ⋃ₙ Vₙ` under `sup` only at a fibre `k` satisfying
//!
//! ```text
//! bnd(k) := ∀g. ((∀b. b ∈ k → g(b) ∈ T) → ∃p ∈ ω. ∀b. b ∈ k → g(b) ∈ Vₚ)
//! ```
//!
//! and at `k = ⟦N⟧` that is **refutable**: `bnd(k)` says every function out of
//! `k` into the tower has a bounded image-stage, which holds exactly when
//! `|k| < cf(ω)`, i.e. when `k` is finite. The thesis's answer is §6.2.1 — a
//! tower at a regular `κ` with `cf(κ) > sup_{a∈A}|B(a)|` — and it is **not the
//! only route**: SCOPING.md §14 costs it against bounding `W` by its path codes,
//! which needs no ordinals. What it is *not* is a Grothendieck universe: a
//! universe is already the W-type's bound and is already sup-closed at an
//! infinite fibre (`derived::bound::least_universe_closed`, no fibre condition
//! at all), and what `bnd` buys is not that but a sup-closed **member** of `U₁`
//! — see §14 "Route C". `DECISIONS.md` §"The tower's height" and
//! `RECURSOR-DESIGN.md` carry the tradeoff; this file is its witness.
//!
//! # Why this file exists beside `designed.rs` rather than inside it
//!
//! Two reasons, and the second is the load-bearing one.
//!
//! `designed.rs`'s `run` asserts exit `0` on every fixture, because a designed
//! fixture that the *frontend* declines is measuring the frontend. This fixture
//! is accepted by the frontend and leaves four obligations underived, which is
//! the same shape as `beyond_the_tower` — but unlike that one it is a fixture
//! with a **shelf life on purpose**: it is the acceptance test for the `κ`-tower
//! and it is meant to go green. Nothing here asserts an exit code, so the
//! reporting path may move underneath it without a false failure.
//!
//! # Three fibres, because two cannot distinguish
//!
//! The fixture declares three trees with the same shape and different
//! recursive-argument domains `γ`:
//!
//! | declaration | `γ` | `γ`'s constructors | today | why |
//! |---|---|---|---|---|
//! | `FinTree` | `B2` | two, nullary | **certifies** | `bnd_carrier` applies |
//! | `FieldTree` | `P1` | one, **with a field** | declines | `bnd_nullary_tags` refuses a field |
//! | `NTree` | `N` | two, one **recursive** | declines | `bnd(⟦N⟧)` is *false* at the `ω`-tower |
//!
//! A single declining row could not have said that, and the distinction is not
//! cosmetic: `FieldTree`'s `bnd` is **true and unbuilt** (a one-point set), so
//! it is a missing lemma; `NTree`'s is **false**, so it is a missing
//! construction. Fixing the tower closes `NTree` and leaves `FieldTree` where
//! it is; fixing `bnd_nullary_tags` does the converse. Only if `bnd` becomes
//! *derivable from membership* — which is what a regular `κ` buys — do both
//! close at once, and `constEv` below is the number that says which happened.
//!
//! # The reason string does not name the cause, and that is measured
//!
//! Both declining declarations report `ind-fibre-value(·)`, the same
//! `Gap::IndFibreValue` key, and it names the **fibre value**. Neither refusal
//! is about a fibre value. A `?`-census over `zoneb::fibre_facts`,
//! `interp::IndApparatus::carrier_bnd` and `derived::cumul::carrier_bnd` puts
//! both stops inside **`bnd_nullary_tags`** — the boundedness of `γ`'s *tag
//! sum* `A_γ`, one construction before the fibre is reached — on its two
//! different disjuncts. `derived/tests/cumul_infinite_fibre.rs` is where that
//! is pinned at the terms; this file pins that it reaches mini at all.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name);
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini --verbose --acceptance-only <fixture>`, with **no status assertion**.
///
/// The exit code is deliberately not read here: `mini`'s certification exit
/// codes are a live surface, and this fixture's whole content is a set of
/// underived obligations, so an assertion on the code would couple a
/// construction test to the reporting path. The rows below are what the test
/// is about.
fn run(name: &str) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .args(["--verbose", "--acceptance-only"])
        .arg(fixture(name))
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert!(
        stdout.lines().next().is_some_and(|l| l.contains("\taccept\t")),
        "the frontend must ACCEPT this file — a rejection is measuring the parser, not the \
         tower:\n{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    stdout
}

fn row(stdout: &str, prefix: &str) -> BTreeMap<String, u64> {
    let mut m = BTreeMap::new();
    let Some(line) = stdout.lines().find(|l| l.starts_with(&format!("{prefix}\t"))) else {
        panic!("no `{prefix}` row in:\n{stdout}")
    };
    for kv in line.split('\t').skip(1) {
        if let Some((k, v)) = kv.split_once('=') {
            if let Ok(v) = v.parse::<u64>() {
                m.insert(k.to_string(), v);
            }
        }
    }
    m
}

fn waiting(stdout: &str) -> BTreeMap<String, u64> {
    row(stdout, "evidence")
        .into_iter()
        .filter_map(|(k, v)| k.strip_prefix("waiting:").map(|s| (s.to_string(), v)))
        .collect()
}

/// **The witness.** `NTree` is well typed, is accepted, and its carrier is not
/// placed — and the two declarations beside it say that the property that fails
/// is the fibre's and not the shape's.
///
/// # What each number means when it moves
///
/// * `constEv == 2` — `FinTree`'s two pairs, and only those. It becomes `4`
///   when `NTree` joins and `6` when `FieldTree` does too. **That is the
///   interface question, readable off one integer**, and it is also the check
///   that a `κ`-tower was landed with its consumers: a tower that makes
///   `bnd(⟦N⟧)` *true* without making it **derivable** leaves this at `2`,
///   because the only route to `bnd(⟦γ⟧)` runs through `bnd_carrier`, whose
///   pullback needs every fibre empty and which therefore refuses a recursive
///   `γ` structurally rather than conservatively. SCOPING.md §14 §4.
/// * the `waiting` set — exactly two keys. If either disappears without
///   `constEv` rising, a gap has been *renamed* rather than closed.
/// * the `elim` rows — every one of the six declarations is computed and agrees
///   with Lean's own flag. The decline is in the placement and nowhere else; a
///   fixture that failed earlier would be measuring the frontend.
#[test]
fn an_infinitary_fibre_is_accepted_interpreted_and_left_unplaced() {
    let out = run("infinitary_branching.ndjson");

    // ── the frontend got all the way through ─────────────────────────────
    let elim: BTreeMap<String, (bool, bool)> = out
        .lines()
        .filter(|l| l.starts_with("elim\t"))
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            let g = |s: &str, p: &str| s.strip_prefix(p).map(|v| v == "true").expect("flag");
            (c[1].to_string(), (g(c[2], "computed="), g(c[3], "oracle=")))
        })
        .collect();
    for name in ["B2", "P1", "N", "FinTree", "FieldTree", "NTree"] {
        assert_eq!(
            elim.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    // ── three fibres, three outcomes, and the middle one is the control ──
    let ev = row(&out, "evidence");
    assert_eq!(ev.get("pairs"), Some(&6), "two defs per tree:\n{out}");
    assert_eq!(
        ev.get("constEv"),
        Some(&2),
        "exactly `FinTree`'s two pairs certify. 4 means `NTree` joined — which needs a *producer* \
         for `bnd` at a recursive carrier, not only a taller tower; 6 means `bnd` now follows \
         from membership and `FieldTree` came with it. Still 2 after a tower change means the \
         tower was landed ahead of its consumers — see this file's header:\n{out}"
    );
    assert_eq!(
        waiting(&out),
        BTreeMap::from([
            ("ind-fibre-value(FieldTree)".to_string(), 2),
            ("ind-fibre-value(NTree)".to_string(), 2),
        ]),
        "the two declining declarations, and *only* those two — `FinTree` is the discrimination \
         that keeps this from passing under a checker that declined everything:\n{out}"
    );

    // The reason string is the same for both and names the fibre value, which
    // is not what either refusal is about. Pinned so that a future reader is
    // not misled by it, and so that splitting the key is a visible change.
    assert_eq!(
        row(&out, "ledger").get("pairs"),
        Some(&6),
        "the ledger and the evidence row must agree on the population:\n{out}"
    );

    // ── the same two declarations, counted per *declaration* ──────────────
    //
    // `waiting` is per pair and `untranslated` is per declaration, so the two
    // rows are `2`/`2` and `1`/`1` for the same two names. Both are asserted
    // because they fail differently: a bug that dropped one declaration's pairs
    // moves `waiting` and not `untranslated`, and a bug that merged the two
    // declarations moves `untranslated` and not `waiting`.
    let ut = row(&out, "untranslated");
    assert_eq!(
        ut.get("declarations"),
        Some(&2),
        "`FieldTree` and `NTree` are the two declarations mini did not translate; `FinTree`, \
         `B2`, `P1` and `N` all did:\n{out}"
    );
    assert_eq!(
        ut.get("notrans:ind-fibre-value(FieldTree)"),
        Some(&1),
        "the finite-fibre row — closes on a lemma for `bnd_nullary_tags`, not on the tower:\n{out}"
    );
    assert_eq!(
        ut.get("notrans:ind-fibre-value(NTree)"),
        Some(&1),
        "the infinite-fibre row — this is the one the κ-tower is for:\n{out}"
    );
}
