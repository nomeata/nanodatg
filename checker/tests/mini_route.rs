//! **Routing, pinned** (ENV-UNIFY.md §5 track D;
//! [`nanoda_lib::mini::route`]) — the policy split, both crossing directions,
//! and one-pass ownership and coverage accounting, each against a named file.
//!
//! # The `_tg` in the file name, and what it now means
//!
//! This header used to read *"Behind `--features tg` … `ci/check.sh` runs it
//! with `cargo test -p nanoda_lib --features tg`"*, and both halves are now
//! false: the feature was retired with the `Certifier` trait at `d746251`
//! (one backend, nothing to select) and the `ci/check.sh` step that named this
//! file went with it. The suite is unconditional and `ci/check.sh` reaches it
//! through the bare `cargo test -p nanoda_lib`, which runs every integration
//! target in the package.
//!
//! The suffix therefore does not mean "needs a special build" — there is one
//! build, and a name that says otherwise is how a suite gets read as optional
//! and drops off a gate list. There is nothing left for it to distinguish this
//! file *from*, so it goes; the subject is routing. Renamed accordingly,
//! `TEST-INVENTORY.md` §3.2.
//!
//! Every routed run owns its thread
//! (the routed driver installs the shared core as the checker's per-thread
//! signature), which `check_file_deep_with` provides — so each test below is
//! one file, one thread, exactly like production.


use std::path::{Path, PathBuf};

use nanoda_lib::mini::route::Mode;
use nanoda_lib::mini::run::{check_file_deep_with, Options, Outcome};

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

/// `034_boolType` is one inductive and one definition: split sends the
/// construction to mini and the definition to nanoda, exactly once each.
#[test]
fn split_routes_once_by_kind() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
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
/// is *counted*.
///
/// # Re-based 0 adopted / 1 declined → 1 adopted / 0 declined at `18212fc`
///
/// The cell used to add: *"one declined typing offer, none adopted (the B5
/// skeleton residue, visible under routing exactly as B4 measured it
/// sequentially)"*, and to say it goes red *"if the guard is loosened
/// (`adopted > 0`)"*. The one offer is **adopted** now. Attributed by
/// measurement, on this fixture and this mode: `8815abb` reads
/// `declined 1 / adopted 0` and its child **`18212fc` "checker: consume mini
/// Nat certificates in TG"** reads `declined 0 / adopted 1`. That is the same
/// commit, in one step, as the two sequential cells in `mini_envshare_cross.rs`
/// — which is the sentence this cell's own parenthesis predicted: what B4
/// measures sequentially, routing shows here.
///
/// **The offer population is conserved at 1**, so the interleaving is intact
/// and only the verdict moved; the argument that this is TG consuming mini's
/// entries rather than a guard that stopped refusing is written out at
/// `mini_envshare_cross.rs::the_obligation_read_declines_mismatched_typings`,
/// and is not repeated here.
///
/// # What it still catches
///
/// The interleaving break, which is the property this cell is named for and
/// the one that did **not** move: if the definition were checked before mini
/// published, there would be nothing to consult and the offer total below
/// would be **0**, not 1. That assertion is now the load-bearing one, so it is
/// asserted as the sum rather than left implicit in a pair of constants — a
/// pinned `adopted = 1` alone would also hold if the total had risen and a
/// decline had appeared beside it.
///
/// # Falsified
///
/// Mutating `checker/src/tg.rs` so the obligation read records every consulted
/// offer as *declined* — watched and restored — leaves the offer sum passing
/// at 1 and dies at `declinedByCheckerTyping`, `mini_route.rs:161`, reading
/// `left: 1  right: 0`. That is the regression this cell is for, arriving at
/// the line it is asserted on rather than at the sum above it.
///
/// **`adoptedByCheckerTyping = 1` is unfalsifiable from here** and is kept as
/// a recorded outcome: with the sum pinned at 1 and the declines at 0 it
/// follows by arithmetic. It is written out because it is the number this
/// header is about.
#[test]
fn the_checker_consults_minis_inductive_entries_under_split() {
    let export = corpus().join("good/tutorial/034_boolType.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let out = routed(&export, Mode::Split);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!(
        cross_field(&out, "adoptedByCheckerTyping") + cross_field(&out, "declinedByCheckerTyping"),
        1,
        "the interleaving broke: the checker consulted no mini entry at all:\n{}",
        rep.cross
    );
    assert_eq!(cross_field(&out, "declinedByCheckerTyping"), 0, "{}", rep.cross);
    assert_eq!(cross_field(&out, "adoptedByCheckerTyping"), 1, "the crossing regressed:\n{}", rep.cross);
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

/// A mini-owned inductive decline remains untranslated debt. It is never
/// handed to nanoda as a second validation pass.
#[test]
fn a_mini_decline_does_not_fall_back() {
    let out = routed(&fixture("squash_at_nonzero_sigma.ndjson"), Mode::Split);
    assert!(out.verdict.is_accepted(), "{:?}", out.verdict);
    let rep = out.route.as_ref().expect("route report");
    assert!(rep.to_mini > 0, "{}", rep.row());
    assert!(out.untranslated().declarations > 0, "{}", rep.row());
    assert!(rep.unclaimed.is_empty(), "{}", rep.row());
}

/// An unused axiom is still a declaration in the unified product and is
/// dispatched to nanoda in the loop; no post-loop sweep is needed.
#[test]
fn an_unused_axiom_is_dispatched_in_the_loop() {
    let out = routed(&fixture("route_unused_axiom.ndjson"), Mode::Split);
    assert!(out.verdict.is_accepted(), "{:?}", out.verdict);
    let rep = out.route.as_ref().expect("route report");
    assert!(rep.to_checker > 0, "{}", rep.row());
    assert!(rep.unclaimed.is_empty(), "{}", rep.row());
}

/// **A checker-routed declaration is checked at every scheduled σ, not just
/// one.** `017_levelComp4` is a *single* level-polymorphic definition the
/// pre-pass schedules at **two** instantiations (`scheduledPairs=2` on
/// `declars=1`), routed to the checker under `Split`; each σ is a distinct
/// joint key, so one declaration yields **2 entries / 4 slots**. Added
/// against a measured green mutation: `check_declar_scheduled` taking only
/// the first scheduled σ ran the whole suite green, because every other
/// pinned file's declarations carry one σ each — one name at two σs is what
/// a per-name collapse cannot fake.
#[test]
fn a_checker_routed_declaration_is_checked_at_every_scheduled_instantiation() {
    let export = corpus().join("good/tutorial/017_levelComp4.ndjson");
    if skip_guard::absent(&export) {
        return
    }
    let out = routed(&export, Mode::Split);
    let rep = out.route.as_ref().expect("route report");
    assert_eq!((rep.to_mini, rep.to_checker), (0, 1), "{}", rep.row());
    assert_eq!(cross_field(&out, "checkerEntries"), 2, "a scheduled σ was skipped:\n{}", rep.cross);
    assert_eq!(cross_field(&out, "checkerSlots"), 4, "{}", rep.cross);
}

/// **The paired-subterm lam measurement** — de-confounding the whole-run
/// sweep below, whose lam residue (673 mini / 440 checker after nominal
/// blinding) mixes two populations: genuine skeleton disagreement, and
/// *surface asymmetry* — lambdas one engine's walk interprets that the
/// other's never reaches (mini's constructions, the checker's per-σ
/// re-checks). Here the surface is forced equal: for every definition-like
/// declaration and every scheduled σ, **both dispatches interpret exactly
/// the declared type and value** — the same `ExprPtr`s, one parse, one core
/// (mini substitutes σ into the expression, the checker carries σ in its
/// context; same pair, same subterm structure). What survives nominal
/// blinding on one side only is genuine disagreement about what a lambda
/// body's skeleton *is*; everything else was surface.
///
/// *(An earlier version of this header said the checker's lam side was
/// build-only, "no `as_lam`, no `lam_by_sym`". That was wrong and is
/// corrected here rather than appended to: the tg backend had
/// `Shared::lam_by_lam`, the exact by-symbol index, and read it in three
/// places — the beta head in `target_eq`, and twice in the target-shape
/// classification. What it lacked was only `as_lam`'s **shape**, a
/// decomposition returning the occurrence's holes and domain. So the two
/// sides were symmetric in what they stored and asymmetric only in what they
/// offered, which is a smaller gap than claimed and made the merge easier,
/// not harder.)* Under `nanoda_lib::lam_store::LamStore` there is one
/// `by_lam` index, and `mini`'s `as_lam` takes apart a lambda the *checker*
/// minted.
#[test]
#[ignore]
fn paired_subterm_lam_divergence() {
    use nanoda_lib::mini::env::Declaration;
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
    let mut totals = [0usize; 18];
    for f in files {
        let name = f.file_stem().unwrap().to_string_lossy().to_string();
        let row = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let Ok(loaded) = nanoda_lib::mini::convert::load_with(&f, Default::default()) else {
                    return (format!("pairskel\tfile={name}\tskipped"), [0usize; 18])
                };
                let mut env = nanoda_lib::mini::env::Environment::empty();
                for d in &loaded.decls {
                    if nanoda_lib::mini::kernel::add(&mut env, d).is_err() {
                        return (format!("pairskel\tfile={name}\trejected"), [0usize; 18])
                    }
                }
                // The paired surface: (declaration, σ) for every
                // definition-like declaration, σ from mini's own schedule.
                let mut pairs: Vec<(&Declaration, Vec<u32>)> = Vec::new();
                for d in &loaded.decls {
                    let lp = match d {
                        Declaration::Def { lparams, .. } | Declaration::Axiom { lparams, .. } => {
                            lparams
                        }
                        _ => continue,
                    };
                    let sigmas = loaded
                        .schedule
                        .get(&d.name())
                        .cloned()
                        .unwrap_or_else(|| vec![vec![0; lp.len()]]);
                    for s in sigmas {
                        pairs.push((d, s));
                    }
                }
                let core = nanoda_lib::tg::EnvCore::fresh();
                let mut ip = nanoda_lib::mini::interp::Interp::over(core.clone());
                for (d, sigma) in &pairs {
                    let (lparams, ty, val) = match d {
                        Declaration::Def { lparams, ty, value, .. } => {
                            (lparams, ty, Some(value))
                        }
                        Declaration::Axiom { lparams, ty, .. } => (lparams, ty, None),
                        _ => unreachable!("pairs holds defs and axioms only"),
                    };
                    let ty_g = nanoda_lib::mini::ground::subst_ground(ty, lparams, sigma);
                    let mut c = nanoda_lib::mini::kernel::Checker::threaded(&env, &mut ip);
                    let _ = c.infer_type(&ty_g);
                    if let Some(v) = val {
                        let v_g = nanoda_lib::mini::ground::subst_ground(v, lparams, sigma);
                        let _ = c.infer_type(&v_g);
                    }
                }
                let (ml, mp, mc) = ip.skeleton_keys();
                nanoda_lib::tg::install_shared_core(core.clone());
                let ef = nanoda_lib::mini::arena::installed_export_file().expect("load installed the file");
                for (d, sigma) in &pairs {
                    if let Some(cd) = ef.declars.get(&d.name().0) {
                        ef.interp_declar_exprs_at(cd, sigma);
                    }
                }
                let Some((cl, cp, cc)) = nanoda_lib::tg::skeleton_keys() else {
                    return (format!("pairskel\tfile={name}\tno-shared"), [0usize; 18])
                };
                let mut cells = [0usize; 18];
                let mut s = format!("pairskel\tfile={name}");
                for (i, (label, m, c)) in
                    [("lam", ml, cl), ("pi", mp, cp), ("cond", mc, cc)].into_iter().enumerate()
                {
                    let (raw, blind) = compare_keys(&m, &c);
                    cells[6 * i..6 * i + 3].copy_from_slice(&raw);
                    cells[6 * i + 3..6 * i + 6].copy_from_slice(&blind);
                    s.push_str(&format!(
                        "\t{label}Common={}\t{label}MiniOnly={}\t{label}CheckerOnly={}\t\
                         {label}BlindCommon={}\t{label}BlindMiniOnly={}\t{label}BlindCheckerOnly={}",
                        raw[0], raw[1], raw[2], blind[0], blind[1], blind[2]
                    ));
                }
                (s, cells)
            })
            .expect("spawn")
            .join()
            .expect("file thread");
        eprintln!("{}", row.0);
        for (t, v) in totals.iter_mut().zip(row.1) {
            *t += v;
        }
    }
    let l = ["lam", "pi", "cond"];
    let mut s = String::from("pairskelTotal");
    for i in 0..3 {
        s.push_str(&format!(
            "\t{0}Common={1}\t{0}MiniOnly={2}\t{0}CheckerOnly={3}\t{0}BlindCommon={4}\t\
             {0}BlindMiniOnly={5}\t{0}BlindCheckerOnly={6}",
            l[i],
            totals[6 * i],
            totals[6 * i + 1],
            totals[6 * i + 2],
            totals[6 * i + 3],
            totals[6 * i + 4],
            totals[6 * i + 5]
        ));
    }
    eprintln!("{s}");
}

/// Raw and nominal-blind `(common, mini-only, checker-only)` for one table's
/// key sets — the shared comparison of the two measurement tests.
fn compare_keys(m: &[kernel::Term], c: &[kernel::Term]) -> ([usize; 3], [usize; 3]) {
    use std::collections::HashSet;
    let ms: HashSet<_> = m.iter().cloned().collect();
    let cs: HashSet<_> = c.iter().cloned().collect();
    let common = ms.intersection(&cs).count();
    let raw = [common, ms.len() - common, cs.len() - common];
    let nm: HashSet<String> = m.iter().map(nominal_blind).collect();
    let nc: HashSet<String> = c.iter().map(nominal_blind).collect();
    let bc = nm.intersection(&nc).count();
    ([raw[0], raw[1], raw[2]], [bc, nm.len() - bc, nc.len() - bc])
}

/// A key modulo the *nominal* mints: the Debug rendering with every `FnSym`
/// id and every memoised hash blanked, leaving structure, brands and the
/// (shared) free variables. Two keys equal under this are one skeleton keyed
/// through two independently-minted symbol series — the population one
/// shared mint path merges by construction.
fn nominal_blind(t: &kernel::Term) -> String {
    let d = format!("{t:?}");
    let mut out = String::with_capacity(d.len());
    let mut rest = d.as_str();
    while let Some(i) = rest.find("id: ") {
        out.push_str(&rest[..i + 4]);
        rest = &rest[i + 4..];
        let fnsym =
            out.rfind("FnSym").is_some_and(|f| out.rfind("FreeVar").is_none_or(|v| f > v));
        let n = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        if fnsym {
            out.push('_');
        } else {
            out.push_str(&rest[..n]);
        }
        rest = &rest[n..];
    }
    out.push_str(rest);
    let mut out2 = String::with_capacity(out.len());
    let mut rest = out.as_str();
    while let Some(i) = rest.find("hash: ") {
        out2.push_str(&rest[..i + 6]);
        rest = &rest[i + 6..];
        let n = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        out2.push('_');
        rest = &rest[n..];
    }
    out2.push_str(rest);
    out2
}

/// **The skeleton-key divergence measurement** — sizing the one-mint-path
/// programme (the owner's "for a merged environment, `interp` must return
/// the same terms; use the same code to handle lambdas in both modules").
///
/// Both engines run one export to completion over one core (mini first, the
/// checker second — the sequential seam, maximal interpretation surface on
/// both sides), and then the three skeleton-site tables are compared **as
/// key sets**: mini's `fibres`/`conds` against the checker's
/// `pi_infos`/`prop_infos`. Over a shared core a skeleton key is
/// a plain term, so `common` counts shapes both dispatches keyed
/// identically — where today two site objects (two nominal symbols) stand
/// for one shape, the population one shared mint path merges by
/// construction — and the one-sided residues bound the *genuine* divergence:
/// shapes one dispatch keys that the other, walking the same file, never
/// produces (different normal form, or different skeletonise-vs-opaque
/// decisions). `#[ignore]`d: a measurement run, minutes over the corpus;
/// `cargo test -p nanoda_lib --features tg skeleton_key_divergence -- --ignored
/// --nocapture` reproduces it.
///
/// # The `lam` column no longer measures anything, and that is the result
///
/// This test sized the one-mint-path programme, and the lambda third of it
/// has since been carried out: `nanoda_lib::lam_store::LamStore` on the
/// shared core is the *only* λ table now, so `Interp::skeleton_keys` and
/// `tg::skeleton_keys` return **the same vector** and their intersection is
/// trivially everything. The `lam*` columns are kept — deleting them would
/// silently drop the row the merge is measured against — but they are read
/// as a *witness that the merge is in place*, not as a measurement:
/// `lamMiniOnly = lamCheckerOnly = 0` is now a tautology, and the assertion
/// below says so rather than letting a future reader mistake it for evidence.
///
/// The measurement it replaced lives on as `LamStore::asked` /
/// `askedByBoth`, taken from the *asking* side. The baseline it is measured
/// against, this test at `9ac7d41` over the 91 tutorial exports:
///
/// ```text
/// lamCommon=49   lamMiniOnly=919  lamCheckerOnly=554
/// piCommon=159   piMiniOnly=467   piCheckerOnly=467
/// condCommon=208 condMiniOnly=561 condCheckerOnly=545
/// ```
///
/// The `pi` and `cond` rows are the follow-on: their one-sided residues are
/// **entirely nominal** — per file, `piNomBlind*Only` and `condNomBlind*Only`
/// are 0 on all but the four `12x_quot*` exports — so those two thirds are
/// the same merge again, with `PiInfo`/`PropInfo` in place of `LamInfo`.
#[test]
#[ignore]
fn skeleton_key_divergence_sweep() {
    use std::collections::HashSet;
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
    let mut totals = [0usize; 9]; // (common, mini-only, checker-only) × (lam, pi, cond)
    for f in files {
        let name = f.file_stem().unwrap().to_string_lossy().to_string();
        let row = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let core = nanoda_lib::tg::EnvCore::fresh();
                let (out, ip) = nanoda_lib::mini::run::check_file_with_interp(
                    &f,
                    nanoda_lib::mini::run::Options::default(),
                    nanoda_lib::mini::interp::Interp::over(core.clone()),
                );
                if !out.verdict.is_accepted() {
                    return (format!("skelcmp\tfile={name}\tskipped"), [0usize; 9])
                }
                nanoda_lib::tg::install_shared_core(core.clone());
                run_checker(&f);
                let (ml, mp, mc) = ip.skeleton_keys();
                let Some((cl, cp, cc)) = nanoda_lib::tg::skeleton_keys() else {
                    return (format!("skelcmp\tfile={name}\tno-shared"), [0usize; 9])
                };
                if std::env::var_os("MINI_SKEL_DUMP").is_some() {
                    for (label, m, c) in
                        [("lam", &ml, &cl), ("pi", &mp, &cp), ("cond", &mc, &cc)]
                    {
                        let ms: std::collections::HashSet<_> = m.iter().collect();
                        let cs: std::collections::HashSet<_> = c.iter().collect();
                        for t in m.iter().filter(|t| !cs.contains(t)) {
                            let d = format!("{t:?}");
                            eprintln!("skelkey\t{label}\tmini\tlen={}\t{}", d.len(), &d[..d.len().min(220)]);
                        }
                        for t in c.iter().filter(|t| !ms.contains(t)) {
                            let d = format!("{t:?}");
                            eprintln!("skelkey\t{label}\tchecker\tlen={}\t{}", d.len(), &d[..d.len().min(220)]);
                        }
                    }
                }
                // A key modulo the *nominal* mints: the Debug rendering with
                // every `FnSym` id and every memoised hash blanked, leaving
                // structure, brands and the (shared) free variables. Two keys
                // equal under this are one skeleton keyed through two
                // independently-minted symbol series — the population one
                // shared mint path merges by construction.
                fn nominal_blind(t: &kernel::Term) -> String {
                    let d = format!("{t:?}");
                    let mut out = String::with_capacity(d.len());
                    let mut rest = d.as_str();
                    while let Some(i) = rest.find("id: ") {
                        out.push_str(&rest[..i + 4]);
                        rest = &rest[i + 4..];
                        // Blank the digits only when this `id:` follows a
                        // FnSym (free variables keep theirs — they are shared
                        // and load-bearing).
                        let fnsym = out.rfind("FnSym").map_or(false, |f| {
                            out.rfind("FreeVar").map_or(true, |v| f > v)
                        });
                        let n = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
                        if fnsym {
                            out.push('_');
                        } else {
                            out.push_str(&rest[..n]);
                        }
                        rest = &rest[n..];
                    }
                    out.push_str(rest);
                    // The memoised hashes fold the FnSym ids in; blank them.
                    let mut out2 = String::with_capacity(out.len());
                    let mut rest = out.as_str();
                    while let Some(i) = rest.find("hash: ") {
                        out2.push_str(&rest[..i + 6]);
                        rest = &rest[i + 6..];
                        let n = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
                        out2.push('_');
                        rest = &rest[n..];
                    }
                    out2.push_str(rest);
                    out2
                }
                let mut cells = [0usize; 9];
                let mut s = format!("skelcmp\tfile={name}");
                for (i, (label, m, c)) in
                    [("lam", ml, cl), ("pi", mp, cp), ("cond", mc, cc)].into_iter().enumerate()
                {
                    let ms: HashSet<_> = m.iter().cloned().collect();
                    let cs: HashSet<_> = c.iter().cloned().collect();
                    let common = ms.intersection(&cs).count();
                    let mo = ms.len() - common;
                    let co = cs.len() - common;
                    let nm: HashSet<String> = m.iter().map(nominal_blind).collect();
                    let nc: HashSet<String> = c.iter().map(nominal_blind).collect();
                    let ncommon = nm.intersection(&nc).count();
                    cells[3 * i] = common;
                    cells[3 * i + 1] = mo;
                    cells[3 * i + 2] = co;
                    s.push_str(&format!(
                        "\t{label}Common={common}\t{label}MiniOnly={mo}\t{label}CheckerOnly={co}\t{label}NomBlindCommon={ncommon}\t{label}NomBlindMiniOnly={}\t{label}NomBlindCheckerOnly={}",
                        nm.len() - ncommon,
                        nc.len() - ncommon,
                    ));
                }
                (s, cells)
            })
            .expect("spawn")
            .join()
            .expect("file thread");
        eprintln!("{}", row.0);
        for (t, v) in totals.iter_mut().zip(row.1) {
            *t += v;
        }
    }
    eprintln!(
        "skelcmpTotal\tlamCommon={}\tlamMiniOnly={}\tlamCheckerOnly={}\tpiCommon={}\t\
         piMiniOnly={}\tpiCheckerOnly={}\tcondCommon={}\tcondMiniOnly={}\tcondCheckerOnly={}",
        totals[0], totals[1], totals[2], totals[3], totals[4], totals[5], totals[6], totals[7],
        totals[8]
    );
    // The λ third of the one-mint-path programme has landed, so the `lam`
    // columns are a *witness* and no longer a measurement — one table read
    // twice cannot disagree with itself. Asserted rather than left implicit,
    // because a silent 0 is exactly what a reader would mistake for evidence
    // that the two dispatches agree.
    assert_eq!(
        (totals[1], totals[2]),
        (0, 0),
        "the λ tables are supposed to be one shared LamStore; a one-sided \
         lam residue means an engine grew a private table again"
    );
    assert!(totals[0] > 0, "no lambda shape at all — the sweep measured nothing");
}

/// Drive the checker in-process over `export`, on this thread — the same
/// helper `mini_envshare_cross.rs` uses, for the sequential half of the measurement
/// above (the *routed* driver shares mini's parse; this deliberately runs
/// the checker's own full pass).
fn run_checker(export: &Path) {
    let cfg_path = std::env::temp_dir().join(format!(
        "nanodatg-route-skel-{}-{}.json",
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
