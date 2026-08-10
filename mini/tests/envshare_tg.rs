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
//! Behind `--features tg` because the checker's evidence path exists only
//! with its backend compiled in; `ci/check.sh` runs it with
//! `cargo test -p mini --features tg`.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::rc::Rc;

use mini::interp::Interp;
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
    let (out, mut ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
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
    let (out, _ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
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

/// **The declining side of the defeq slot.** `003_arrowType`'s one
/// definition interprets to different bodies under the two dispatches, so
/// mini's defining equation is *offered* and the statement guard in
/// `const_abbrev` refuses it: one counted decline, a second carrier beside
/// mini's (`divergent = 1`), and no adoption. This is the fixture that goes
/// red if that guard is loosened — `034` below cannot catch it, because an
/// inductive-only file never calls `const_abbrev` at all.
#[test]
fn a_mismatched_defining_equation_is_declined_not_adopted() {
    let Some(r) = cross_report("good/tutorial/003_arrowType.ndjson") else { return };
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 0, "a defeq crossed unguarded:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerDefeq"), 1, "the declined population moved:\n{r}");
    assert_eq!(field(&r, "divergent"), 1, "{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "{r}");
}

/// **The `has_type_const` guard, specifically.** `034` below exercises only
/// `ty_const`'s read (whose statement check lives inside `typing`), so a
/// loosened guard in `has_type_const` — the obligation-discharge read — slips
/// past it; measured under exactly that mutation, `084_projProp1` is a file
/// where it shows: one mini typing gets wrongly adopted there (0 → 1) while
/// this fixture pins 0 adopted and all thirteen offers declined.
#[test]
fn the_obligation_read_declines_mismatched_typings() {
    let Some(r) = cross_report("good/tutorial/084_projProp1.ndjson") else { return };
    assert_eq!(field(&r, "adoptedByCheckerTyping"), 0, "a typing crossed unguarded:\n{r}");
    assert_eq!(field(&r, "declinedByCheckerTyping"), 13, "the declined population moved:\n{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "{r}");
}

/// **The B4 crossing, measured and pinned — the declining file.** On
/// `034_boolType` (inductive-only) the two engines' carriers genuinely
/// differ, so nothing may cross: the checker consults mini's three typings
/// (`Bool`, its recursor spine) and the statement guard refuses each. The
/// declines being *counted* — rather than the entries being trusted — is the
/// adopt-and-check discipline itself, so `adopted* = 0` here is as load-
/// bearing as `adopted = 1` is in the fixture above; it goes red if the
/// typing guard in `has_type_const`/`ty_const` is loosened.
#[test]
fn a_mismatched_typing_is_declined_not_adopted() {
    let Some(r) = cross_report("good/tutorial/034_boolType.ndjson") else { return };
    assert_eq!(field(&r, "miniEntries"), 6, "{r}");
    assert_eq!(field(&r, "adoptedByCheckerTyping"), 0, "a typing crossed unguarded:\n{r}");
    assert_eq!(field(&r, "adoptedByCheckerDefeq"), 0, "{r}");
    assert_eq!(field(&r, "declinedByCheckerTyping"), 3, "the declined population moved:\n{r}");
    assert_eq!(field(&r, "alias"), 0, "{r}");
    assert_eq!(field(&r, "incoherent"), 0, "{r}");
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
    for f in files {
        let name = f.file_stem().unwrap().to_string_lossy().to_string();
        let report = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let core = EnvCore::fresh();
                let (out, _ip) = mini::run::check_file_with_interp(
                    &f,
                    mini::run::Options::default(),
                    Interp::over(core.clone()),
                );
                if !out.verdict.is_accepted() {
                    return format!("skip\tfile={name}\tverdict=declined")
                }
                nanoda_lib::tg::install_shared_core(core.clone());
                run_checker(&f);
                let r = core.consts().borrow().report();
                let l = core.lams().borrow().report();
                format!("{r}\tfile={name}\n{l}\tfile={name}")
            })
            .expect("spawn")
            .join()
            .expect("file thread");
        eprintln!("{report}");
        for line in report.lines() {
            let bucket = match line.split('\t').next() {
                Some("cross") => &mut totals,
                Some("lammint") => &mut lam_totals,
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
}

/// Both engines over one core and one export, mini first; the shared lambda
/// mint's report handed back for pinning.
fn lam_report(file: &str) -> Option<String> {
    let export = corpus().join(file);
    if skip_guard::absent(&export) {
        return None
    }
    let core = EnvCore::fresh();
    let (out, _ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
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
    let (out, ip) = mini::run::check_file_with_interp(
        &export,
        mini::run::Options::default(),
        Interp::over(core.clone()),
    );
    assert!(out.verdict.is_accepted(), "mini accepts 034 after the checker: {:?}", out.verdict);
    assert!(ip.core().same_core(&core));
    let after = core.fresh_var();
    assert!(after.id() > before.id() + 1, "mini minted from the Env the checker grew");
}
