//! **Infinitary branching, end to end** — the one shape of Lean inductive the
//! `ω`-tower could not hold, and the export on which it now certifies.
//!
//! `NTree.node : (N → NTree) → NTree` is ordinary Lean. `mini` accepts the
//! file, computes the eliminator class, interprets every clause — and used to
//! stop at the carrier, because `derived/src/cumul/bounded.rs` closes the tower
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
//! route taken**: `derived/src/wpath/` proves `W(A,B,u) ∈ U(d)` outright, at an
//! arbitrary fibre family and with no ordinals, by bounding `W` by its labelled
//! path codes. `DeclUniverse::over_at_general`'s step (f) spends that theorem,
//! `FibreFacts` has no `bnd` field to supply, and **all six pairs certify**.
//!
//! The tower did not go and was never the problem: it stopped being the
//! *catcher* and became the set the paths live in
//! (`derived::cumul::tower_amb`), where its height was never in question. Nor
//! was a Grothendieck universe ever the missing piece — a universe is already
//! the W-type's bound and is already sup-closed at an infinite fibre
//! (`derived::bound::least_universe_closed`, no fibre condition at all), and
//! what `bnd` bought was not that but a sup-closed **member** of `U₁`; see
//! SCOPING.md §14 "Route C". `DECISIONS.md` §"The tower's height" and
//! `RECURSOR-DESIGN.md` carry the tradeoff; this file is its witness.
//!
//! # Why this file exists beside `designed.rs` rather than inside it
//!
//! Two reasons, and the second is the load-bearing one.
//!
//! `designed.rs`'s `run` asserts exit `0` on every fixture, because a designed
//! fixture that the *frontend* declines is measuring the frontend. This fixture
//! used to be accepted by the frontend and leave four obligations underived,
//! which was the same shape as `beyond_the_tower` — but unlike that one it was
//! a fixture with a **shelf life on purpose**: it was the acceptance test for
//! the infinitary-branching work and it was meant to go green. It has. Nothing
//! here asserts an exit code, so the reporting path may move underneath it
//! without a false failure, and that stays true now that there is nothing left
//! to report.
//!
//! # Three fibres, because two cannot distinguish
//!
//! The fixture declares three trees with the same shape and different
//! recursive-argument domains `γ`:
//!
//! | declaration | `γ` | `γ`'s constructors | before | after | what `bnd` needed |
//! |---|---|---|---|---|---|
//! | `FinTree` | `B2` | two, nullary | certifies | certifies | `bnd_carrier` applied |
//! | `FieldTree` | `P1` | one, **with a field** | declined | **certifies** | `bnd_nullary_tags` refused a field |
//! | `NTree` | `N` | two, one **recursive** | declined | **certifies** | `bnd(⟦N⟧)` is *false* at the `ω`-tower |
//!
//! A single declining row could not have said that, and the distinction was not
//! cosmetic: `FieldTree`'s `bnd` was **true and unbuilt** (a one-point set), so
//! it was a missing lemma; `NTree`'s is **false**, so it was a missing
//! construction. That is why the two closing *together* is the measurement that
//! identifies the route: a taller tower would have closed `NTree` and left
//! `FieldTree`, and a lemma for `bnd_nullary_tags` the converse. They closed at
//! the same commit because neither is asked for any more — the path route
//! deletes the obligation rather than discharging it, so the true-but-unbuilt
//! one and the false one go the same way.
//!
//! # Where the two stops were, measured rather than argued
//!
//! Both declining declarations reported `ind-fibre-value(·)`, the same
//! `Gap::IndFibreValue` key, and it names the **fibre value**. Neither refusal
//! was about a fibre value. A `?`-census over `zoneb::fibre_facts`,
//! `interp::IndApparatus::carrier_bnd` and `derived::cumul::carrier_bnd` put
//! both stops at `zoneb.rs`' `app.carrier_bnd(…)` line and, one frame down, at
//! `interp.rs`' `bnd_nullary_tags(…)` — the boundedness of `γ`'s *tag sum*
//! `A_γ`, one construction before the fibre is reached — on its two different
//! disjuncts. **Two sites, no others**, which is why deleting the `bnd` chain
//! closed both rows and needed nothing else: every other `?` in `fibre_facts`
//! already passed for `P1` and for `N`, including the `mem` half at `⟦N⟧`.
//! `derived/tests/cumul_infinite_fibre.rs` is where that is pinned at the
//! terms; this file pins that it reaches mini at all.

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
/// codes are a live surface, and this fixture's whole content used to be a set
/// of underived obligations, so an assertion on the code would couple a
/// construction test to the reporting path. The rows below are what the test is
/// about, and they say more than an exit code would now that the obligations
/// are discharged.
fn run(name: &str) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .args(["--no-modelgen", "--verbose", "--acceptance-only"])
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

/// **The witness.** `NTree` is well typed, is accepted, and its carrier **is
/// placed** — and the two declarations beside it say that what changed is the
/// obligation about the fibre and not the shape of the declaration.
///
/// # What each number means when it moves
///
/// * `constEv == 6` — every pair. It was `2` (`FinTree` alone) for as long as
///   `FibreFacts` had a `bnd` field, and it went **straight to 6**: `FieldTree`
///   declined *only* because of that field, so deleting it closed `FieldTree`
///   at the same moment it closed `NTree`. A landing that had reached `4` would
///   have done step 3 of SCOPING.md §14.6 by halves, and one that stayed at `2`
///   after a `derived/`-side change would mean the construction was landed
///   ahead of its consumers — which it was, for one commit, and was recorded
///   rather than hidden.
/// * the `waiting` set — **empty**. A key reappearing here without `constEv`
///   falling would be a gap *renamed* rather than opened.
/// * the `elim` rows — every one of the six declarations is computed and agrees
///   with Lean's own flag. This was true while the placement declined too: the
///   decline was in the placement and nowhere else, and a fixture that failed
///   earlier would have been measuring the frontend.
#[test]
fn an_infinitary_fibre_is_accepted_interpreted_and_placed() {
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
        Some(&6),
        "every pair certifies, including the infinitely branching one. 2 is `FinTree` alone, the \
         state before `FibreFacts` lost its `bnd` field; 4 would mean one of the two other rows \
         closed without the other, which on this route cannot happen — both are blocked by that \
         one field and by nothing else:\n{out}"
    );
    assert_eq!(
        waiting(&out),
        BTreeMap::new(),
        "nothing is waiting. `FinTree` is still the discrimination that keeps this from passing \
         under a checker that certified nothing — it is counted in `constEv` above:\n{out}"
    );

    assert_eq!(
        row(&out, "ledger").get("pairs"),
        Some(&6),
        "the ledger and the evidence row must agree on the population:\n{out}"
    );

    // ── nothing untranslated, counted per *declaration* ───────────────────
    //
    // `waiting` is per pair and `untranslated` is per declaration, so the two
    // rows are asserted separately: a bug that dropped one declaration's pairs
    // moves `waiting` and not `untranslated`, and one that merged two
    // declarations moves `untranslated` and not `waiting`.
    let ut = row(&out, "untranslated");
    assert_eq!(
        ut.get("declarations"),
        Some(&0),
        "all six declarations translate — `B2`, `P1`, `N` and the three trees over them:\n{out}"
    );
    assert_eq!(
        ut.keys().filter(|k| k.starts_with("notrans:")).count(),
        0,
        "and no declaration carries a reason for not having been translated:\n{out}"
    );
}
