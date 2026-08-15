//! **Both engines over one core, in one process** — the cross-engine half of
//! `mini/tests/envshare.rs` (ENV-UNIFY.md §3.3, B1/B2).
//!
//! One `nanoda_lib::tg::EnvCore` is handed to mini (`Interp::over` +
//! `check_file_with_interp`) and installed as the checker's per-thread
//! signature (`tg::install_shared_core`); both engines then run a real
//! tutorial export to completion **in this thread**, minting from one kernel
//! `Env`. What that pins, beyond either engine's own suite: the two roots
//! really accept a caller's core, neither strands the other's `RefCell`
//! borrows, the counters are one pair of counters, and the W-type machine is
//! one object on both sides — in either engine order.
//!
//! # The `_tg` in the file name, and what it now means
//!
//! This header used to read: *"Behind `--features tg` because the checker's
//! evidence path exists only with its backend compiled in; `ci/check.sh` runs
//! it with `cargo test -p mini --features tg`."* **Every clause of that is now
//! false**, and each was false in a way that would send the next reader
//! somewhere that does not exist: `--features tg` was retired with the
//! `Certifier` trait when one backend stopped needing selecting (`d746251`,
//! `checker/src/certify.rs` — "There is one backend, and it is not selected"),
//! `-p mini` names a crate merged into `checker` at `4e86d46`, and the
//! `ci/check.sh` step that ran this line is one of the three deleted with the
//! feature. The suite is unconditional, runs under a plain `cargo test`, and
//! `ci/check.sh` reaches it through the bare `cargo test -p nanoda_lib`.
//!
//! So the suffix does **not** mean "needs a special build" — there is one
//! build. What separates this file from its sibling `mini_envshare.rs` is that
//! the sibling exercises mini's root alone (two `Interp`s over one core, no
//! corpus, no checker), while this one drives **both engines** in one process.
//! That is the distinction the name should carry, and a suffix that instead
//! names a deleted feature is how a suite gets read as optional and drops off
//! a gate list — which is exactly what happened to it. Renamed accordingly;
//! `TEST-INVENTORY.md` §3.2 records the trade.


use std::path::{Path, PathBuf};
use std::rc::Rc;

use nanoda_lib::mini::interp::Interp;
use nanoda_lib::tg::EnvCore;

// SKIP is not PASS: both tests below return early when `vendor/arena-tests`
// is absent, and cargo reports them `ok`. See ci/skip-guard.rs.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests")
}

/// Drive the checker in-process over `export`, on this thread — so it builds
/// its `Shared` from whatever core was installed. Panics if checking fails,
/// which is the checker's own contract.
fn run_checker(export: &Path) {
    let cfg_path = std::env::temp_dir().join(format!(
        "nanodatg-envshare-{}-{}.json",
        std::process::id(),
        export.file_stem().unwrap_or_default().to_string_lossy(),
    ));
    let cfg = format!(
        r#"{{"export_file_path": {},
             "unpermitted_axiom_hard_error": false,
             "unsafe_permit_all_axioms": true,
             "nat_extension": true,
             "string_extension": true,
             "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let config = nanoda_lib::util::Config::try_from(cfg_path.as_path()).expect("config parses");
    let _ = std::fs::remove_file(&cfg_path);
    let (export_file, _skipped) = config.to_export_file().expect("export parses");
    export_file.check_all_declars();
}

/// mini first, checker second, one core. The assertions at the end are the
/// sharing facts: the checker minted from the same `Env` mini grew, and the
/// machine both sides reach is one object.
#[test]
fn one_core_serves_both_engines_mini_then_checker() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let core = EnvCore::fresh();
    let (out, mut ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034: {:?}", out.verdict);

    nanoda_lib::tg::install_shared_core(core.clone());
    let before = core.fresh_var();
    run_checker(&export);
    let after = core.fresh_var();
    assert!(
        after.id() > before.id() + 1,
        "the checker minted from the shared Env — one pair of counters"
    );

    let pre = derived::prelude::prelude();
    let mc = core.machine(&pre).expect("the shared machine builds");
    let mm = ip.ind_apparatus().expect("mini's apparatus builds").mach.clone();
    assert!(Rc::ptr_eq(&mc, &mm), "one machine on both sides of the seam");
}

/// Both engines over one core and one export, mini first; the shared
/// constant store's crossing report handed back for pinning.
fn cross_report(file: &str) -> Option<String> {
    let export = corpus().join(file);
    if skip_guard::absent(&export) {
        return None
    }
    let core = EnvCore::fresh();
    let (out, _ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts {file}: {:?}", out.verdict);
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);
    let report = core.consts().borrow().report();
    eprintln!("{report}");
    Some(report)
}

/// One `k=v` field of a `cross` report row.
fn field(report: &str, k: &str) -> u64 {
    report
        .split('\t')
        .skip(1)
        .filter_map(|kv| kv.split_once('='))
        .find(|(key, _)| *key == k)
        .unwrap_or_else(|| panic!("{k} missing from:\n{report}"))
        .1
        .parse()
        .expect("a number")
}

/// **The B4 crossing, measured and pinned — the adopting file** (ENV-UNIFY.md
/// §3.4 items 3, 5, 6). `012_levelComp1` is one definition whose body both
/// dispatches interpret to the same term, so mini's defining equation is the
/// one the checker adopts: one mini entry, no checker entry beside it
/// (`converged`, not `divergent`), one crossed certificate.
///
/// The exact numbers are the point: `adoptedByCheckerDefeq = 1` goes red if
/// the statement guard in `const_abbrev` is loosened (more would cross,
/// wrongly labelled) *or* if the crossing regresses to 0.
#[test]
fn a_defining_equation_crosses_from_mini_to_checker() {
    let Some(r) = cross_report("good/tutorial/012_levelComp1.ndjson") else { return };
    assert_eq!(field(&r, "miniEntries"), 1, "{r}");
    assert_eq!(field(&r, "checkerEntries"), 0, "the checker minted beside mini's carrier:\n{r}");
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 1, "the crossing moved:\n{r}");
    assert_eq!(field(&r, "converged"), 1, "{r}");
    assert_eq!(field(&r, "divergent"), 0, "{r}");
    assert_eq!(field(&r, "alias"), 0, "a NameKey meant two different names:\n{r}");
    assert_eq!(field(&r, "incoherent"), 0, "a certificate not about its carrier:\n{r}");
}

/// **The declining side of the defeq slot.** `004_dependentType`'s one
/// definition interprets to different bodies under the two dispatches, so
/// mini's defining equation is *offered* and the statement guard in
/// `const_abbrev` refuses it: one counted decline, a second carrier beside
/// mini's (`divergent = 1`), and no adoption. This is the fixture that goes
/// red if that guard is loosened — `034` below cannot catch it.
///
/// *(The reason given here used to be "because an inductive-only file never
/// calls `const_abbrev` at all", and **`034` is not an inductive-only file**:
/// it is one `inductive` and one `def`. The true reason is narrower and is now
/// visible in `034`'s own numbers — its one defining equation is **adopted**,
/// `adoptedByCheckerDefeq = 1` with no decline beside it, so that file offers
/// the declining side of this slot no witness at all. Corrected in place
/// rather than annotated, because the old sentence was a claim about the
/// fixture and it was simply false.)*
///
/// **Moved off `003_arrowType` on 2026-08-11, with a written trade** (task
/// #151). `003` used to carry this cell and stopped being divergent when the
/// `Π` mint merged, because its divergence *was* the thing the merge removes:
/// its body is an arrow type, both engines interpreted it to a `dprod` at the
/// constant fibre, and the two terms differed **only in the symbol**. So this
/// cell was passing for the wrong reason — it was measuring the duplicate-mint
/// bug, not the statement guard, and a fixture that green-lights on a defect
/// stops testing the moment the defect is fixed.
///
/// `003` is *restated* rather than deleted, in the cell below, and it now
/// carries the merge's own falsifier. The guard's population is not lost with
/// it: `declinedByCheckerDefeq` is **20** across the 89 tutorial exports after
/// the merge, over 20 divergent files, and `004`'s divergence is genuine —
/// a dependent type, where the two dispatches really do build different bodies.
#[test]
fn a_mismatched_defining_equation_is_declined_not_adopted() {
    let Some(r) = cross_report("good/tutorial/004_dependentType.ndjson") else { return };
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 0, "a defeq crossed unguarded:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerDefeq"), 1, "the declined population moved:\n{r}");
    assert_eq!(field(&r, "divergent"), 1, "{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "{r}");
}

/// **`003_arrowType` restated: the file the Π merge converged, and why.**
///
/// The cell above used to be this file, asserting `divergent = 1` and one
/// counted decline. It asserts the opposite now, and the change is the merge
/// working rather than a guard weakening — so the mechanism is *pinned here*
/// rather than argued in a comment.
///
/// `003`'s definition is an arrow type. Both engines interpret it to a `dprod`
/// at the constant fibre; before the merge they minted **two symbols** for that
/// one fibre shape, so mini's defining equation and the checker's carrier
/// differed in exactly that symbol and the statement guard refused the
/// crossing. That is `pi_store`'s header sentence made concrete: *a gap where
/// reflexivity was the whole proof*.
///
/// # Why this cell can fail
///
/// The Π assertion is the load-bearing one. `converged = 1` alone would also
/// hold if the guard were loosened to accept a mismatch, which is the failure
/// this cell must not green-light; requiring that the two engines asked for the
/// **same** Π shape and that neither has a one-sided one says *why* they
/// converged. Un-merging the Π table turns `askedByBoth` to 0 and both halves
/// of this cell red.
#[test]
fn the_arrow_type_converged_because_its_pi_symbol_is_now_one() {
    let Some((r, pi)) = both_reports("good/tutorial/003_arrowType.ndjson") else { return };
    assert_eq!(field(&r, "converged"), 1, "003 stopped converging:\n{r}");
    assert_eq!(field(&r, "divergent"), 0, "003 diverged again:\n{r}");
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 1, "the equation stopped crossing:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerDefeq"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "a certificate not about its carrier:\n{r}");

    assert!(
        field(&pi, "askedByBoth") > 0,
        "the two engines share no Π shape here, so the convergence above is \
         not the merge and this cell no longer explains it:\n{pi}"
    );
    assert_eq!(field(&pi, "askedByMiniOnly"), 0, "a one-sided Π shape appeared:\n{pi}");
    assert_eq!(field(&pi, "askedByCheckerOnly"), 0, "a one-sided Π shape appeared:\n{pi}");
}

/// **The `has_type_const` guard, specifically** — and the file that still has
/// a live decline population to guard. `034` below exercises only `ty_const`'s
/// read (whose statement check lives inside `typing`), so a loosened guard in
/// `has_type_const` — the obligation-discharge read — slips past it;
/// `084_projProp1` is the file where it shows.
///
/// # Re-based 0/13 → 9/4 at `18212fc`, and the offers are conserved
///
/// This cell pinned `adoptedByCheckerTyping = 0` with **all thirteen** offers
/// declined. It reads **9 adopted, 4 declined** now. Attributed by measurement
/// over the four commits of the mini-unification block: `4e86d46~1`,
/// `4e86d46` and `8815abb` all read `0 / 13`, and **`18212fc` "checker:
/// consume mini Nat certificates in TG"** reads `9 / 4`, which is master's.
/// One commit, one step, both this fixture and `034`'s.
///
/// **It is convergence, not a loosened guard**, and the order of the evidence
/// is the order of its strength:
///
/// 1. **The offer population is conserved**: `13 = 4 + 9`. The guard is still
///    consulted on every offer; only the verdict moved. A guard that had
///    stopped being consulted would have dropped the *total*, and that is the
///    failure this arithmetic separates from this one.
/// 2. `TgBackend::typing` (`tg.rs`) returns `Derived` **only** under
///    `u_concl(&thm, …) == want`, where `want = Formula::mem(⟦e⟧, ⟦ty⟧)` is
///    built from the interpretation on the spot — re-read on this tree, after
///    the `Certifier` retirement rewrote the impl around it. An adopted typing
///    is by construction a slot whose conclusion is literally the statement the
///    reader asked for, so "the guard loosened" is not available as an
///    explanation for an adoption.
/// 3. `alias = 0` and `incoherent = 0` throughout: no certificate is about the
///    wrong carrier.
/// 4. `18212fc` **declared this effect when it landed**, on its own fixture:
///    ENV-UNIFY.md B6 records `nat_char_equations.ndjson` going "mini typings
///    adopted by TG **0 → 15**, declined typings **16 → 3**" as TG stopped
///    minting a second Nat carrier and started reading mini's entries. This
///    fixture is the same handoff seen from the tutorial corpus. Nobody re-ran
///    this suite, which is why the pin outlived the change by 67 commits.
///
/// The four that still decline are what keeps this cell a guard rather than a
/// record: `034` has **no** decline left, so if this fixture's 4 ever go to 0
/// the tree has no live witness that a mismatched typing is refused, and that
/// is a finding rather than an improvement.
///
/// # Falsified per assertion — and two mutations that stayed green
///
/// Every mutation below was applied to `checker/src/tg.rs`, watched, and
/// restored; `git diff checker/src/` is empty.
///
/// | mutation | dies at | reads |
/// | --- | --- | --- |
/// | the `ty_const` statement read never matches (`if false && *t.concl() == want`) | the **offer sum**, `:331` | `left: 14  right: 13` |
/// | the obligation read records every consulted offer as *adopted* | `adoptedByCheckerTyping`, `:336` | `left: 13  right: 9` |
/// | the obligation read records every consulted offer as *declined* | the **offer sum**, `:331` | `left: 14  right: 13` |
///
/// The second is the separation that matters: the offer sum **passes** at 13
/// under it and the run dies one line later, so the two assertions are not one
/// assertion twice.
///
/// **`declinedByCheckerTyping = 4` is unfalsifiable from here**, and is
/// recorded as such rather than left to read as coverage: with the sum pinned
/// at 13 and the adoptions at 9, it follows by arithmetic and no mutation can
/// reach it. It is kept because it is the number this header is written about.
///
/// **The claim this cell used to make about loosening is refuted.** Its old
/// header said a loosened `has_type_const` "shows" here — *"one mini typing
/// gets wrongly adopted there (0 → 1)"*. Two loosening mutations were run and
/// **both leave this suite and `mini_route.rs` entirely green**: accepting any
/// offer at the `ty_const` read (`if true || *t.concl() == want`), and making
/// the obligation read's `find` never locate the asked-for statement so it
/// falls back to `slots[0]`. The reason is §6.1's fourth gate, a **degenerate
/// instantiation**: wherever these reads find a hit there is only *one* slot
/// offered for the key, so "pick the one whose conclusion is what was asked"
/// and "pick the first" select the same certificate and the mutation is the
/// identity. The old measurement was taken when this fixture had 13 declines;
/// the 9 that converged at `18212fc` took the discriminating population with
/// them. **So this cell catches the regression direction and the
/// stopped-consulting direction, and it does not catch loosening** — a
/// separating fixture would need a key with two offered slots, and no fixture
/// in the corpus has one. That is a gap with a stated shape, which is worth
/// more than the sentence it replaces.
#[test]
fn the_obligation_read_declines_mismatched_typings() {
    let Some(r) = cross_report("good/tutorial/084_projProp1.ndjson") else { return };
    // The conserved total, asserted *first* and as a sum, because it is the
    // one statement that separates "the verdict moved" from "the guard stopped
    // being consulted" — and a pair of pinned constants cannot say that on its
    // own. 21 mini entries offer 13 typings across this file.
    assert_eq!(
        field(&r, "adoptedByCheckerTyping") + field(&r, "declinedByCheckerTyping"),
        13,
        "the checker stopped consulting mini's typing offers:\n{r}"
    );
    assert_eq!(field(&r, "adoptedByCheckerTyping"), 9, "the crossing moved:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerTyping"), 4, "the declined population moved:\n{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "{r}");
}

/// **`034_boolType` restated: the file whose carriers stopped differing, and
/// why.** Follows the precedent two cells up — a divergence cell whose
/// divergence went away is *restated with the mechanism pinned*, not deleted
/// and not weakened.
///
/// This cell used to be called `a_mismatched_typing_is_declined_not_adopted`
/// and read: *"On `034_boolType` (inductive-only) the two engines' carriers
/// genuinely differ, so nothing may cross: the checker consults mini's three
/// typings (`Bool`, its recursor spine) and the statement guard refuses each."*
/// It asserted `adoptedByCheckerTyping = 0` and `declinedByCheckerTyping = 3`.
/// **It reads 3 adopted and 0 declined now** — and two sentences of that
/// description were already wrong on their own terms:
///
/// * `034` is **not** inductive-only. The export is one `inductive` *and one
///   `def`* (counted off the ndjson: `{inductive: 1, def: 1}`), which is why
///   `mini_route.rs`'s `Split` cell can send declaration 1 to mini and
///   declaration 2 to the checker. The same wrong claim is repeated in
///   [`a_mismatched_defining_equation_is_declined_not_adopted`]'s header,
///   corrected there.
/// * "the two engines' carriers genuinely differ" is what stopped being true.
///
/// # Attribution, and why this is convergence
///
/// Measured over the mini-unification block: `4e86d46~1`, `4e86d46` and
/// `8815abb` all read `adopted 0 / declined 3 / defeq 0 / converged 0`;
/// **`18212fc` "checker: consume mini Nat certificates in TG"** reads
/// `3 / 0 / 1 / 1`, which is master's. One commit, and the same commit that
/// moved `084` above — see that cell for the four-point argument that this is
/// TG consuming mini's entries rather than a guard that stopped refusing. The
/// short form: the typing offers are conserved, `3 = 0 + 3`, and
/// `TgBackend::typing` can only return `Derived` at a conclusion equal to the
/// statement asked for.
///
/// The **defeq** slot is the one number that is not a conserved re-verdict:
/// `adoptedByCheckerDefeq` 0 → 1 with `declinedByCheckerDefeq` flat at 0, so
/// the offer is *new* rather than re-decided. That is the same fact as
/// `converged` 0 → 1: before `18212fc` the checker never consulted mini's
/// entry for `034`'s definition at all, and it does now. An offer appearing
/// where there was none cannot be explained by a weakened guard — a weakened
/// guard moves declines into adoptions, and there was no decline here to move.
///
/// # What this cell can still catch
///
/// The regression direction, which is the one it was always for: if the
/// crossing goes back to 0 adopted, or if the statement guard in
/// `has_type_const`/`ty_const` starts refusing again, every assertion below
/// moves. What it can **no longer** catch is a *loosened* guard, because there
/// is no decline left on this file to be wrongly converted — that duty passed
/// wholly to [`the_obligation_read_declines_mismatched_typings`], whose four
/// remaining declines are now the tree's only live witness for it, and which
/// says so at its own header.
///
/// # Falsified per assertion
///
/// Both mutations applied to `checker/src/tg.rs`, watched, and restored.
///
/// | mutation | dies at | reads |
/// | --- | --- | --- |
/// | the obligation read records every consulted offer as *declined* | `adoptedByCheckerTyping`, `:428` | `left: 0  right: 3` |
/// | the `const_abbrev` statement guard never matches | `adoptedByCheckerDefeq`, `:432` | `left: 0  right: 1` |
///
/// The first passes the offer sum at 3 and dies one line later; the second
/// passes **every** typing assertion and dies in the defeq block, so the two
/// slots are pinned separately rather than by one number twice.
///
/// **Two assertions here are unfalsifiable from here and are kept as recorded
/// outcomes** (`TEST-INVENTORY.md` §6.2): `declinedByCheckerTyping = 0`
/// follows from the sum and the adoptions by arithmetic; and the **offer sum
/// itself** had no separating mutation — every mutation that moved the total
/// on this fixture also moved the adoptions, so it died at the adoption line
/// first. It is asserted anyway because the property it names, "the checker
/// stopped asking", is the one a pair of pinned constants cannot express, and
/// on `084_projProp1` the same assertion *is* separately falsifiable — two
/// mutations trip it there with the constants intact. Enforced on the sibling
/// fixture, documentation here; that is its honest status.
#[test]
fn the_bool_family_crossed_because_the_checker_reads_minis_entries() {
    let Some(r) = cross_report("good/tutorial/034_boolType.ndjson") else { return };
    assert_eq!(field(&r, "miniEntries"), 6, "{r}");
    // Conserved, and asserted as a sum for the reason `084` gives: it is what
    // separates "the verdict moved" from "the checker stopped asking".
    assert_eq!(
        field(&r, "adoptedByCheckerTyping") + field(&r, "declinedByCheckerTyping"),
        3,
        "the checker stopped consulting mini's typing offers:\n{r}"
    );
    assert_eq!(field(&r, "adoptedByCheckerTyping"), 3, "the crossing regressed:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerTyping"), 0, "the declined population moved:\n{r}");
    // The new offer, and the pair that says it is one: an adoption with no
    // decline beside it and one converged entry.
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 1, "the defining equation stopped crossing:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerDefeq"), 0, "{r}");
    assert_eq!(field(&r, "converged"), 1, "{r}");
    assert_eq!(field(&r, "divergent"), 0, "a second carrier appeared beside mini's:\n{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "a certificate not about its carrier:\n{r}");
}

/// **The B4 measurement across the whole tutorial corpus** — one process,
/// one thread per export (an `EnvCore` is `!Send`, so each file's core lives
/// and dies on its own thread), mini first and the checker second over one
/// core, the crossing ledgers summed. `#[ignore]`d: this is the measurement
/// run behind ENV-UNIFY.md B4's numbers, minutes of work the default suite
/// does not owe; `cargo test … cross_sweep_tutorial -- --ignored --nocapture`
/// reproduces it.
#[test]
#[ignore]
fn cross_sweep_tutorial() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("corpus dir")
        .map(|e| e.expect("entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    files.sort();
    let mut totals: std::collections::BTreeMap<String, u64> = Default::default();
    let mut lam_totals: std::collections::BTreeMap<String, u64> = Default::default();
    let mut pi_totals: std::collections::BTreeMap<String, u64> = Default::default();
    for f in files {
        let name = f.file_stem().unwrap().to_string_lossy().to_string();
        let report = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let core = EnvCore::fresh();
                let (out, _ip) = nanoda_lib::mini::run::check_file_with_interp(
                    &f,
                    nanoda_lib::mini::run::Options::default(),
                    Interp::over(core.clone()),
                );
                if !out.verdict.is_accepted() {
                    return format!("skip\tfile={name}\tverdict=declined")
                }
                nanoda_lib::tg::install_shared_core(core.clone());
                run_checker(&f);
                let r = core.consts().borrow().report();
                let l = core.lams().borrow().report();
                let pi = core.pis().borrow().report();
                format!("{r}\tfile={name}\n{l}\tfile={name}\n{pi}\tfile={name}")
            })
            .expect("spawn")
            .join()
            .expect("file thread");
        eprintln!("{report}");
        for line in report.lines() {
            let bucket = match line.split('\t').next() {
                Some("cross") => &mut totals,
                Some("lammint") => &mut lam_totals,
                Some("pimint") => &mut pi_totals,
                _ => continue,
            };
            for kv in line.split('\t').skip(1) {
                let (k, v) = kv.split_once('=').expect("k=v");
                if let Ok(n) = v.parse::<u64>() {
                    *bucket.entry(k.to_string()).or_default() += n;
                }
            }
        }
    }
    let row: Vec<String> = totals.iter().map(|(k, v)| format!("{k}={v}")).collect();
    eprintln!("crossTotal\t{}", row.join("\t"));
    let row: Vec<String> = lam_totals.iter().map(|(k, v)| format!("{k}={v}")).collect();
    eprintln!("lamTotal\t{}", row.join("\t"));
    let row: Vec<String> = pi_totals.iter().map(|(k, v)| format!("{k}={v}")).collect();
    eprintln!("piTotal\t{}", row.join("\t"));
}

/// Both engines over one core and one export, mini first; the shared lambda
/// mint's report handed back for pinning.
fn lam_report(file: &str) -> Option<String> {
    let export = corpus().join(file);
    if skip_guard::absent(&export) {
        return None
    }
    let core = EnvCore::fresh();
    let (out, _ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts {file}: {:?}", out.verdict);
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);
    let report = core.lams().borrow().report();
    eprintln!("{report}");
    Some(report)
}

/// **The one-lambda merge, measured.** Both dispatches walk
/// `007_betaReduction2` over one core; the shared table is what they both
/// mint into, and on this file they mint into it *identically*: three body
/// shapes, all three minted by mini, all three asked for again by the
/// checker and answered with mini's symbol.
///
/// `crossHitsChecker > 0` is the claim. Before the merge that lookup missed
/// — the two tables were private — and a second `lam` symbol was declared
/// for the same shape, at which point `⊢ lam₁(h⃗,A) = lam₂(h⃗,A)` was provable
/// and nothing proved it: a mini typing about the first met a checker
/// obligation about the second and was refused at the statement guard, a
/// counted gap where reflexivity was the whole proof.
///
/// **Three shapes, not two, and that is deliberate.** Two sites cannot
/// distinguish a table that merges from one that happens to answer the
/// second ask; and `mintedByChecker = 0` here is the strong form — the
/// checker minted *nothing* on this file, so every symbol it used is one
/// mini already owned.
///
/// `inert = 0` and `failed = 0` are the two ways the shared mint can hand
/// back something weaker than a graph. Both are zero on every corpus
/// measured, and they are pinned so that a construction that starts refusing
/// says so here rather than as a drifting gap count somewhere downstream.
#[test]
fn one_lam_symbol_serves_both_engines() {
    let Some(r) = lam_report("good/tutorial/007_betaReduction2.ndjson") else { return };
    assert_eq!(field(&r, "sites"), 3, "the shape population moved:\n{r}");
    assert_eq!(field(&r, "mintedByMini"), 3, "{r}");
    assert_eq!(field(&r, "mintedByChecker"), 0, "the checker minted its own symbol:\n{r}");
    assert_eq!(field(&r, "askedByBoth"), 3, "a shape stopped being shared:\n{r}");
    assert_eq!(field(&r, "askedByMiniOnly"), 0, "{r}");
    assert_eq!(field(&r, "askedByCheckerOnly"), 0, "{r}");
    assert_eq!(
        field(&r, "crossHitsChecker"),
        6,
        "no lookup was answered from the other engine's mint — the tables are \
         merged in name only:\n{r}"
    );
    assert_eq!(field(&r, "inert"), 0, "a graph construction refused:\n{r}");
    assert_eq!(field(&r, "failed"), 0, "a mint failed outright:\n{r}");
}

/// Both engines over one core and one export, mini first; the shared **Π**
/// mint's report handed back for pinning.
fn pi_report(file: &str) -> Option<String> { both_reports(file).map(|(_, pi)| pi) }

/// The crossing ledger **and** the Π mint report from **one** run.
///
/// `install_shared_core` is once per thread by construction — replacing a
/// `Shared` mid-run would strand every symbol the old one minted — so a cell
/// that wants both numbers cannot call `cross_report` and `pi_report` in
/// sequence. It has to ask once and read twice, which is this.
fn both_reports(file: &str) -> Option<(String, String)> {
    let export = corpus().join(file);
    if skip_guard::absent(&export) {
        return None
    }
    let core = EnvCore::fresh();
    let (out, _ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts {file}: {:?}", out.verdict);
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);
    let cross = core.consts().borrow().report();
    let pi = core.pis().borrow().report();
    eprintln!("{cross}\n{pi}");
    Some((cross, pi))
}

/// **The Π merge, and the contrast with λ that made it worth doing.**
///
/// `ENV-UNIFY.md` §B5 measured, before either merge was built, that λ's
/// one-sided shapes are *structural* divergence while Π's are the same
/// skeleton wearing two symbols — 467+467 one-sided collapsing to 3+3 once the
/// `FnSym` ids are blanked. This is that prediction, cashed: the shapes both
/// dispatches ask for should dominate, where the λ table's
/// `the_lam_populations_are_disjoint_on_an_inductive_only_file` pins the
/// opposite for λ on the same corpus.
///
/// # Why this cell can fail
///
/// `askedByBoth` is asserted **positive** and `crossHitsChecker` likewise: a
/// merge that renamed two tables into one without either engine ever reading
/// the other's mint would leave both at zero and pass any `<=` assertion.
#[test]
fn one_pi_mint_for_both_engines() {
    let Some(r) = pi_report("good/tutorial/034_boolType.ndjson") else { return };
    let both = field(&r, "askedByBoth");
    let sites = field(&r, "sites");
    assert!(both > 0, "no Π shape was asked for by both engines — merged in name only:\n{r}");
    assert!(
        field(&r, "crossHitsChecker") > 0,
        "no lookup was answered from the other engine's mint:\n{r}"
    );
    // The residue is the finding: on this file every shape either engine keys
    // is keyed by both. Asserted as an identity rather than a bound, so that a
    // shape appearing on one side only turns this red and gets looked at.
    assert_eq!(both, sites, "a one-sided Π shape appeared — say which:\n{r}");
    assert_eq!(field(&r, "inert"), 0, "a fibre construction refused:\n{r}");
    assert_eq!(field(&r, "failed"), 0, "a mint failed outright:\n{r}");
    assert_eq!(field(&r, "upgradeFailed"), 0, "{r}");
}

/// **The tiering's upgrade path, which the mini-first order never exercises.**
///
/// A `Π` site is two depths: [`nanoda_lib::pi_store::Fibre`] is what the symbol
/// *is* and both engines get it, [`nanoda_lib::pi_store::Full`] is the universe
/// layer only `mini` needs. Whoever asks first decides which is built, so when
/// the **checker** mints first the entry is core-only and `mini` must *upgrade*
/// it — keeping the symbol and adding the proofs — rather than mint a second.
///
/// Every other cell here runs mini first, so `upgrades` is 0 in all of them and
/// this path would be a green cell that cannot go red. Hence checker first.
///
/// # Mutation, verified
///
/// Making the upgrade arm mint a fresh site instead of extending the stored one
/// leaves `upgrades` at 0 and fails the first assertion; making it return the
/// core-only entry unchanged makes `mini`'s `fibre_view` decline, which takes
/// `034_boolType` off accepted and fails the verdict assertion below.
#[test]
fn a_checker_minted_pi_is_upgraded_not_reminted() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let core = EnvCore::fresh();
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);
    let minted_by_checker = field(&core.pis().borrow().report(), "mintedByChecker");
    assert!(minted_by_checker > 0, "the checker minted no Π site; the upgrade cannot be tested");

    let (out, _ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034 after the checker: {:?}", out.verdict);
    let r = core.pis().borrow().report();
    eprintln!("{r}");
    assert!(field(&r, "upgrades") > 0, "no site was upgraded — mini re-minted instead:\n{r}");
    assert_eq!(field(&r, "upgradeFailed"), 0, "an upgrade failed:\n{r}");
    // The point of the upgrade: the site count did not grow by a second copy
    // of what the checker already minted.
    assert_eq!(
        field(&r, "mintedByChecker"),
        minted_by_checker,
        "the checker's mints changed while mini ran:\n{r}"
    );
    assert!(field(&r, "crossHitsMini") > 0, "mini never read the checker's mint:\n{r}");
}

/// **What the merge does not fix, pinned as a number.** On `034_boolType`
/// the two engines mint **nine** shapes between them — four mini, five
/// checker — and *not one is shared*.
///
/// This is not the merge failing; it is the merge revealing where the
/// divergence actually is. The two engines are not naming one lambda twice
/// here, they are interpreting **different lambdas**: `mini` generates
/// `Bool`'s recursor itself (the export's recursors are dropped at load) and
/// skeletonises the bodies of its own graph nest, while the checker walks
/// the export's `Expr::Lambda` nodes. Traced, the shapes do not even have
/// the same arity — mini's are single applications of an arity-4 nest symbol
/// to three holes and the binder, the checker's are `x`, `x h`, and a hole.
///
/// So a shared λ table cannot merge them, and no change to lambda handling
/// will: the divergence is upstream, in what each engine takes the
/// declaration to *be*. That is what makes this fixture worth keeping — it
/// is the standing measurement of the residue, and it goes red in the good
/// direction if routing ever puts one engine's inductive construction behind
/// the other's walk.
#[test]
fn the_lam_populations_are_disjoint_on_an_inductive_only_file() {
    let Some(r) = lam_report("good/tutorial/034_boolType.ndjson") else { return };
    assert_eq!(field(&r, "sites"), 9, "{r}");
    assert_eq!(field(&r, "mintedByMini"), 4, "{r}");
    assert_eq!(field(&r, "mintedByChecker"), 5, "{r}");
    assert_eq!(field(&r, "askedByBoth"), 0, "a shape became shared — say so:\n{r}");
    assert_eq!(field(&r, "crossHitsChecker"), 0, "{r}");
    assert_eq!(field(&r, "inert"), 0, "{r}");
    assert_eq!(field(&r, "failed"), 0, "{r}");
}

/// The same, checker first — the seam is order-independent: installing the
/// core before either engine has minted anything and running mini into the
/// signature the checker grew is the routing driver's other half-step.
#[test]
fn one_core_serves_both_engines_checker_then_mini() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let core = EnvCore::fresh();
    nanoda_lib::tg::install_shared_core(core.clone());
    run_checker(&export);

    let before = core.fresh_var();
    let (out, ip) = nanoda_lib::mini::run::check_file_with_interp(
        &export,
        nanoda_lib::mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034 after the checker: {:?}", out.verdict);
    assert!(ip.core().same_core(&core));
    let after = core.fresh_var();
    assert!(after.id() > before.id() + 1, "mini minted from the Env the checker grew");
}
