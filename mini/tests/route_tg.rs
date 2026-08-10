//! **Routing, pinned** (ENV-UNIFY.md §5 track D; `mini/src/route.rs`) — the
//! policy split, the force flags, both crossing directions, the counted
//! fallback and the stray sweep, each against a named file.
//!
//! Behind `--features tg` because the checker's evidence path exists only
//! with its backend compiled in; `ci/check.sh` runs it with
//! `cargo test -p mini --features tg`. Every routed run owns its thread
//! (`run_routed` installs the shared core as the checker's per-thread
//! signature), which `check_file_deep_with` provides — so each test below is
//! one file, one thread, exactly like production.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};

use mini::route::Mode;
use mini::run::{check_file_deep_with, Options, Outcome};

// SKIP is not PASS: corpus-dependent tests return early when
// `vendor/arena-tests` is absent, and cargo reports them `ok`. See
// ci/skip-guard.rs.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests")
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn routed(path: &Path, mode: Mode) -> Outcome {
    check_file_deep_with(path, Options { route: Some(mode), ..Default::default() })
}

/// One `k=v` field of the `cross` report row.
fn cross_field(out: &Outcome, k: &str) -> u64 {
    let r = &out.route.as_ref().expect("a routed run carries a route report").cross;
    r.split('\t')
        .skip(1)
        .filter_map(|kv| kv.split_once('='))
        .find(|(key, _)| *key == k)
        .unwrap_or_else(|| panic!("{k} missing from:\n{r}"))
        .1
        .parse()
        .expect("a number")
}

/// **The policy function, pinned with three atoms** — the three modes over
/// one file, because two modes pass under a policy that ignores the flag and
/// hardcodes one split. `034_boolType` is one inductive and one definition,
/// so every cell below is attributable to a kind:
///
/// * `ForceMini` walks both groups on mini and hands the checker nothing —
///   the historical mini run (6 published entries, the number
///   `envshare_tg.rs` pins for the unrouted seam test);
/// * `ForceChecker` hands mini nothing (0 mini entries);
/// * `Split` sends the inductive to mini (its 5 Bool-family entries and no
///   def entry) and the definition to the checker.
#[test]
fn the_flag_forces_either_engine_and_split_routes_by_kind() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let fm = routed(&export, Mode::ForceMini);
    let rep = fm.route.as_ref().expect("route report");
    assert_eq!((rep.to_mini, rep.to_checker), (2, 0), "{}", rep.row());
    assert_eq!(cross_field(&fm, "miniEntries"), 6, "{}", rep.cross);
    assert_eq!(cross_field(&fm, "checkerEntries"), 0, "{}", rep.cross);

    let fc = routed(&export, Mode::ForceChecker);
    let rep = fc.route.as_ref().expect("route report");
    assert_eq!((rep.to_mini, rep.to_checker), (0, 2), "{}", rep.row());
    assert_eq!(cross_field(&fc, "miniEntries"), 0, "{}", rep.cross);

    let sp = routed(&export, Mode::Split);
    let rep = sp.route.as_ref().expect("route report");
    assert_eq!((rep.to_mini, rep.to_checker), (1, 1), "{}", rep.row());
    assert_eq!(cross_field(&sp, "miniEntries"), 5, "the inductive's family:\n{}", rep.cross);
}

/// **Split sends a definition to the checker, which certifies it** —
/// `012_levelComp1` is one definition and nothing else: mini walks no pair,
/// publishes nothing; the checker publishes the def's carrier with both
/// certificate slots. Goes red if the policy stops splitting by kind (mini
/// would publish, the checker would not) or if the checker's evidence path
/// stops publishing under routing.
#[test]
fn split_sends_the_definition_to_the_checker_which_certifies_it() {
    let export = corpus().join("good/tutorial/012_levelComp1.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let out = routed(&export, Mode::Split);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!((rep.to_mini, rep.to_checker), (0, 1), "{}", rep.row());
    assert_eq!(out.ledger.as_ref().expect("accepted").pairs, 0, "mini must walk no pair");
    assert_eq!(cross_field(&out, "miniEntries"), 0, "{}", rep.cross);
    assert_eq!(cross_field(&out, "checkerEntries"), 1, "{}", rep.cross);
    assert_eq!(cross_field(&out, "checkerSlots"), 2, "carrier + typing/defeq:\n{}", rep.cross);
    assert_eq!(cross_field(&out, "alias"), 0, "{}", rep.cross);
    assert_eq!(cross_field(&out, "incoherent"), 0, "{}", rep.cross);
}

/// **The interleaving, checker←mini direction.** Under `Split` on `034`,
/// mini publishes the Bool family at declaration 1 and the checker checks
/// the definition at declaration 2 *in the same walk* — so the checker's
/// use-site reads consult mini's entries and the statement guard's verdict
/// is *counted*: one declined typing offer, none adopted (the B5 skeleton
/// residue, visible under routing exactly as B4 measured it sequentially).
/// Goes red if the interleaving breaks (the def checked before mini
/// published: nothing to consult, `declined = 0`) or if the guard is
/// loosened (`adopted > 0`).
#[test]
fn the_checker_consults_minis_inductive_entries_under_split() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let out = routed(&export, Mode::Split);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!(cross_field(&out, "declinedByCheckerTyping"), 1, "{}", rep.cross);
    assert_eq!(cross_field(&out, "adoptedByCheckerTyping"), 0, "{}", rep.cross);
    assert_eq!(cross_field(&out, "adoptedByCheckerDefeq"), 0, "{}", rep.cross);
}

/// **The crossing direction B4 could not observe: a typing crosses from the
/// checker to mini.** B4 measured mini-side adoption at 0 *because without
/// routing mini fills everything itself before any use can miss*
/// (ENV-UNIFY.md §5 B4). Under `Split` on `072_sortElimProp2Rec`, the
/// checker certifies a definition mini's own construction later needs; the
/// miss path (`Checker::adopt_shared`) finds the checker's typing-carrying
/// entry and adopts it — one crossed typing, one converged key. This is the
/// first production witness of that direction; it goes red if routing stops
/// making the miss observable, if the adoption path regresses, or if the
/// checker stops publishing the typing.
#[test]
fn a_typing_crosses_from_the_checker_to_mini_under_split() {
    let export = corpus().join("good/tutorial/072_sortElimProp2Rec.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let out = routed(&export, Mode::Split);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!(cross_field(&out, "adoptedByMiniTyping"), 1, "{}", rep.cross);
    assert_eq!(cross_field(&out, "converged"), 1, "{}", rep.cross);
    assert_eq!(cross_field(&out, "alias"), 0, "{}", rep.cross);
    assert_eq!(cross_field(&out, "incoherent"), 0, "{}", rep.cross);
}

/// **A mini decline falls back to the checker — counted and named, never
/// silent.** The fixture is the corpus's one surviving decliner
/// (`squash_at_nonzero_sigma`, see `mini/tests/dump.rs`): `Squash` is
/// routed to mini by kind, mini records `ind-spec(Squash: class (P) above
/// Prop)`, and the driver hands the group to the checker. Three cells make
/// the event unfakeable:
///
/// * the fallback row carries the name *and* mini's own reason;
/// * `declinesUnfallen` is empty — the checker really had the group;
/// * `strays` is empty — the sweep found nothing unvouched-for, which is
///   the cell that goes red if the fallback records the event without
///   actually running the checker (the group would be neither covered by
///   mini nor claimed, and the sweep would check and name it).
#[test]
fn a_mini_decline_falls_back_to_the_checker_counted_and_named() {
    let out = routed(&fixture("squash_at_nonzero_sigma.ndjson"), Mode::Split);
    assert!(out.verdict.is_accepted(), "{:?}", out.verdict);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!(
        rep.fallbacks_to_checker,
        vec![("Squash".to_string(), "ind-spec(Squash: class (P) above Prop)".to_string())],
        "{}",
        rep.row()
    );
    assert!(rep.declines_unfallen.is_empty(), "{}", rep.row());
    assert!(rep.strays.is_empty(), "{}", rep.row());
}

/// **The stray sweep: a group neither engine was routed is checked and
/// named.** The natural population is exactly one declaration shape: an
/// unused non-standard axiom, which mini's frontend drops before the
/// evidence pass (`run.rs`'s retain — `unusedAx` is in `ignored axioms`,
/// not in mini's walked declarations) while the checker's export still
/// carries it. Under `Split` the sweep finds it unvouched-for, checks it on
/// the checker, and names it. Goes red if the sweep is dropped — silently
/// unvalidated coverage is the failure mode this cell exists to forbid.
#[test]
fn an_unrouted_export_group_is_swept_and_named_a_stray() {
    let out = routed(&fixture("route_unused_axiom.ndjson"), Mode::Split);
    assert!(out.verdict.is_accepted(), "{:?}", out.verdict);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!(rep.strays, vec!["unusedAx".to_string()], "{}", rep.row());
    assert!(rep.fallbacks_to_checker.is_empty(), "{}", rep.row());
}

/// **`ForceMini` reproduces the unrouted evidence run.** Same file, one
/// unrouted and one force-mini walk, and the whole evidence ledger must
/// agree row for row — the factoring of `Ledger::run`'s loop body into
/// `walk_decl` (this arc's one refactor of existing behaviour) is pinned
/// here to have changed nothing. `084_projProp1` because it is the richest
/// of the pinned files: 4 declarations, 20 published entries, projections
/// and props in the walk.
#[test]
fn force_mini_reproduces_the_unrouted_evidence_run() {
    let export = corpus().join("good/tutorial/084_projProp1.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let plain = check_file_deep_with(&export, Options::default());
    let fm = routed(&export, Mode::ForceMini);
    assert_eq!(plain.verdict, fm.verdict);
    let (a, b) = (plain.ledger.expect("accepted"), fm.ledger.expect("accepted"));
    assert_eq!(a.row(), b.row());
    assert_eq!(a.evidence_row(), b.evidence_row());
    assert_eq!(a.untranslated.row(), b.untranslated.row());
    assert_eq!(a.conv_row(), b.conv_row());
    let rep = fm.route.expect("route report");
    assert_eq!(rep.to_checker, 0, "{}", rep.row());
}
