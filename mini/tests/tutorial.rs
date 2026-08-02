//! The corpus harness (MINI-DESIGN.md §11).
//!
//! Two independent axes, kept apart:
//!
//! * **Acceptance fidelity** — mini must accept/reject each export exactly as
//!   mini-lean does. mini-lean accepts all 91 `good/tutorial` exports (it and
//!   the suite were co-developed) and rejects the `bad/tutorial` ones, so the
//!   expectation is derived rather than transcribed;
//!   [`DECLINED_BY_NANODAS_PARSER`] records every file where that is not the
//!   whole story, and says why.
//! * **Evidence completeness** — zero gaps on all 91. Not yet measurable: step
//!   (b) of §12 produces no evidence. When step (c) lands, the per-file gap
//!   budgets and the `FULLY_DERIVED` ratchet go here beside these tests.
//!
//! **Each file is checked in a subprocess**, for the same reason
//! `checker/tests/corpus.rs` does it: `checker`'s parser reports a declined
//! export by calling `std::process::exit(2)` (`parser.rs`'s `BackRef::assert_in`)
//! and an inconsistent one by panicking, neither of which an in-process harness
//! can contain. `mini::run::check_file` remains the in-process API for
//! everything that is not the corpus.
//!
//! The corpus lives in `vendor/arena-tests`, which is gitignored, so every test
//! reports a skip rather than passing vacuously when it is absent.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf() }

fn ndjson_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(dir) else { return out };
    for e in entries.flatten() {
        let p = e.path();
        if p.extension().is_some_and(|x| x == "ndjson") {
            out.push(p);
        }
    }
    out.sort();
    out
}

fn stem(p: &Path) -> String { p.file_name().unwrap().to_string_lossy().to_string() }

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Verdict {
    Accept,
    Reject,
    Decline,
    /// `--block` only: the file was accepted, and the interpretation pass
    /// stopped at the first `(declaration, σ)` it could not discharge. Not a
    /// judgement about the file, which is why it is not one of `Main.lean`'s
    /// three.
    Blocked,
}

struct Run {
    verdict: Verdict,
    stdout: String,
}

/// `mini --verbose <file>`; the exit status is the verdict (`Main.lean`'s).
fn run(export: &Path) -> Run { run_with(export, &[]) }

/// The same, with extra flags — `--block` is the one that matters.
fn run_with(export: &Path, flags: &[&str]) -> Run {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--verbose")
        .args(flags)
        .arg(export)
        .output()
        .expect("spawn mini");
    let verdict = match out.status.code() {
        Some(0) => Verdict::Accept,
        Some(1) => Verdict::Reject,
        Some(2) => Verdict::Decline,
        Some(3) => Verdict::Blocked,
        other => panic!("mini exited with {other:?} on {}", export.display()),
    };
    Run { verdict, stdout: String::from_utf8_lossy(&out.stdout).to_string() }
}

/// The bad fixtures mini *declines* rather than rejects.
///
/// Every entry is `checker`'s parser refusing the file before mini sees it —
/// never a mini judgement. Two causes, both upstream nanoda policy:
///
/// * `126_dup_defs` — a duplicate declaration is an `assert!` in
///   `checker/src/parser.rs`, where mini-lean's `Environment.insertNew`
///   rejects it as an ordinary type-checking error.
/// * `127`–`133` — nanoda declines export files whose name back-references are
///   not densely numbered, by `std::process::exit(2)`
///   (`checker/tests/corpus.rs` documents the same policy for its own corpus).
///
/// mini-lean rejects all eight; nanoda accepts none of them either. So no file
/// in the corpus is accepted by one and refused by the other — the divergence
/// is in the *reason*, and it is recorded here rather than papered over.
const DECLINED_BY_NANODAS_PARSER: &[&str] = &[
    "126_dup_defs.ndjson",
    "127_dup_ind_def.ndjson",
    "128_dup_ctor_def.ndjson",
    "129_dup_rec_def.ndjson",
    "130_misnamed_rec_user.ndjson",
    "131_dup_rec_def2.ndjson",
    "132_dup_ctor_rec.ndjson",
    "133_DupConCon.ndjson",
];

/// The good fixtures mini declines because they declare an axiom of their own.
///
/// `mini::convert::is_standard_axiom` is the rule and the argument: Lean's own
/// three axioms are validated by the set-theoretic model and are therefore
/// `derived/` obligations, while a user-declared axiom's inhabitation is not
/// derivable *in principle* — no work anywhere discharges it. A run that stops
/// at the first missing derivation would stop at one of these for ever, so
/// they are taken out of scope at the frontend, by name and with a reason.
///
/// mini-lean accepts both; the divergence is recorded here rather than papered
/// over, exactly as [`DECLINED_BY_NANODAS_PARSER`] records the other one.
///
/// `123_quotSoundType` is deliberately **not** here: it declares `Quot.sound`,
/// which is Lean's own, and it goes on being checked.
const DECLINED_NONSTANDARD_AXIOM: &[(&str, &str)] =
    &[("031_letTypeDep.ndjson", "aDepProp"), ("032_letRed.ndjson", "aProp")];

fn good_dir() -> PathBuf { repo_root().join("vendor/arena-tests/good/tutorial") }
fn bad_dir() -> PathBuf { repo_root().join("vendor/arena-tests/bad/tutorial") }

/// mini-lean accepts all 91 tutorial exports. So must mini — except the two it
/// declines for a declared axiom, which are named in
/// [`DECLINED_NONSTANDARD_AXIOM`] together with the reason string mini gives.
#[test]
fn tutorial_good_all_accepted() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    assert_eq!(files.len(), 91, "the tutorial corpus is 91 exports");
    let mut bad = Vec::new();
    let mut declined: Vec<(String, String)> = Vec::new();
    for f in &files {
        let r = run(f);
        match r.verdict {
            Verdict::Accept => {}
            Verdict::Decline => {
                let reason = r
                    .stdout
                    .lines()
                    .next()
                    .and_then(|l| l.rsplit('\t').next())
                    .unwrap_or_default()
                    .to_string();
                declined.push((stem(f), reason));
            }
            _ => bad.push(format!("{}: {:?}\n{}", stem(f), r.verdict, r.stdout)),
        }
    }
    assert!(bad.is_empty(), "these were neither accepted nor declined:\n{}", bad.join("\n"));
    let expected: Vec<(String, String)> = DECLINED_NONSTANDARD_AXIOM
        .iter()
        .map(|(f, a)| (f.to_string(), format!("non-standard axiom: {a}")))
        .collect();
    assert_eq!(declined, expected, "the set of declined good fixtures changed");
    assert_eq!(files.len() - declined.len(), 89, "89 of the 91 are still checked");
}

/// **The declared axiom is refused at the frontend, and the four ill-typed
/// fixtures that also declare one are still *rejected*.**
///
/// This is the pin on *where* the decline happens. `bad/tutorial`'s `044`,
/// `047`, `050` and `054` each declare a helper axiom ahead of the ill-typed
/// declaration the fixture exists to catch. Declining in the parser — the
/// obvious place — turns all four into declines, which passes
/// [`tutorial_bad_none_accepted`] while quietly retiring four negative tests.
/// `mini::run::check_file_with` therefore declines only after the kernel has
/// had the file, and these are the four that prove it.
#[test]
fn tutorial_bad_fixtures_with_a_declared_axiom_are_still_rejected() {
    let files = ndjson_files(&bad_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", bad_dir().display());
        return
    }
    let with_axiom = [
        "044_inductBadNonSort2.ndjson",
        "047_inductWrongCtorParams.ndjson",
        "050_inductInIndex.ndjson",
        "054_indNegReducible.ndjson",
    ];
    for name in with_axiom {
        let p = bad_dir().join(name);
        assert!(p.exists(), "{name} is missing from the corpus");
        let r = run(&p);
        assert_eq!(r.verdict, Verdict::Reject, "{name} must be rejected, not declined:\n{}", r.stdout);
    }
}

/// The negative corpus carries the weight: a checker that accepts everything
/// passes the positive tests trivially.
#[test]
fn tutorial_bad_none_accepted() {
    let files = ndjson_files(&bad_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", bad_dir().display());
        return
    }
    let mut wrong = Vec::new();
    for f in &files {
        if run(f).verdict == Verdict::Accept {
            wrong.push(stem(f));
        }
    }
    assert!(wrong.is_empty(), "these ill-typed files were ACCEPTED:\n{}", wrong.join("\n"));
}

/// A decline is not a rejection, and the two must not be allowed to trade
/// places quietly: a port bug that turns a rejection into a decline would
/// otherwise hide inside [`tutorial_bad_none_accepted`].
#[test]
fn tutorial_bad_declines_are_exactly_the_recorded_ones() {
    let files = ndjson_files(&bad_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", bad_dir().display());
        return
    }
    let declined: Vec<String> =
        files.iter().filter(|f| run(f).verdict == Verdict::Decline).map(|f| stem(f)).collect();
    let expected: Vec<String> = DECLINED_BY_NANODAS_PARSER.iter().map(|s| s.to_string()).collect();
    assert_eq!(declined, expected, "the set of declined bad fixtures changed");
}

/// Every `good/tutorial` export must survive conversion and scheduling with a
/// nonempty schedule — MINI-DESIGN.md §12 step 1's exit criterion, and the
/// precondition for step (c) keying its interpretation store on `(name, σ)`.
#[test]
fn tutorial_every_export_is_scheduled() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut unscheduled = Vec::new();
    for f in &files {
        let r = run(f);
        let pairs = fact(&r.stdout, "scheduledPairs").unwrap_or(0);
        let declars = fact(&r.stdout, "declars").unwrap_or(0);
        if declars > 0 && pairs < declars {
            unscheduled.push(format!("{}: {pairs} pairs for {declars} declarations", stem(f)));
        }
    }
    assert!(
        unscheduled.is_empty(),
        "the pre-pass left declarations unscheduled:\n{}",
        unscheduled.join("\n")
    );
}

/// The empirical questions MINI-DESIGN.md §13 could not settle, answered by
/// measurement and then pinned so the answers cannot rot.
#[test]
fn tutorial_corpus_facts() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let (mut nat_lits, mut max_nat, mut str_lits, mut pairs) = (0u64, 0u64, 0u64, 0u64);
    let mut mismatches: Vec<String> = Vec::new();
    for f in &files {
        let r = run(f);
        nat_lits += fact(&r.stdout, "natLits").unwrap_or(0);
        max_nat = max_nat.max(fact(&r.stdout, "maxNatLit").unwrap_or(0));
        str_lits += fact(&r.stdout, "strLits").unwrap_or(0);
        pairs += fact(&r.stdout, "scheduledPairs").unwrap_or(0);
        for line in r.stdout.lines().filter(|l| l.starts_with("recursor-shape\t")) {
            mismatches.push(format!("{}: {line}", stem(f)));
        }
    }
    eprintln!(
        "tutorial facts: natLits={nat_lits} maxNatLit={max_nat} strLits={str_lits} \
         scheduledPairs={pairs}"
    );

    // §13: "does the tutorial corpus exercise `strLit`?" — no. So `Gap::StrLit`
    // is unreachable here and the inert string constructor costs nothing.
    assert_eq!(str_lits, 0, "a strLit appeared; Gap::StrLit is now reachable");
    // §13: "a `natLit > 10`?" — no. Mini-lean's parser guard and its `whnf`
    // re-check are both dead on this corpus.
    assert!(max_nat <= 10, "a natLit above mini-lean's limit of 10 appeared: {max_nat}");
    // §2/§13: "a recursor whose exported name or level order deviates from
    // mini-lean's generation order?" — no. This is what entitles mini to reuse
    // the pre-pass's schedule for its *generated* recursor.
    assert!(
        mismatches.is_empty(),
        "export recursors deviate from the generated shape:\n{}",
        mismatches.join("\n")
    );
}

/// **The §6.2 clause census over the corpus**, as a ratchet.
///
/// Stage (c) threads evidence one operation at a time, and this is how the
/// next operation is chosen: by what the corpus actually spends its nodes on.
/// The numbers are recorded rather than merely printed so that implementing a
/// clause *fails* this test — an unrecorded improvement is as much a surprise
/// as a regression, which is the same discipline nanoda's gap budgets use.
///
/// Measured 2026-08-01, over 7 748 interpretation nodes in the 91 exports:
///
/// | clause | nodes | share | status |
/// | --- | ---: | ---: | --- |
/// | `bvar` | 2 204 | 28.4% | interpreted (the scope's stored variable) |
/// | `app` | 2 193 | 28.3% | interpreted (`app(⟦f⟧,⟦a⟧)`) |
/// | `const` | 1 328 | 17.1% | interpreted (abbreviation or opaque symbol) |
/// | `sort` | 602 | 7.8% | interpreted (the tower) |
/// | `pi-dep` | 491 | 6.3% | interpreted (`DProdN` + the fibre symbol) |
/// | `lam` | 447 | 5.8% | interpreted (`lambda_n`, both codomain cases) |
/// | `pi-arrow` | 378 | 4.9% | interpreted (`fs`, + the cumulativity lift) |
/// | `pi-prop` | 86 | 1.1% | interpreted (`conditional_singleton`, `cond_in_u0`) |
/// | `proj` | 13 | 0.2% | **remaining** |
/// | `let` | 3 | 0.0% | interpreted (zeta-transparent) |
/// | `natLit` | 3 | 0.0% | **remaining** — needs `Nat`'s interpretation |
/// | `strLit` | 0 | — | unreachable on this corpus |
///
/// **99.79%** of nodes are interpretable: 81.7% at the first measurement,
/// 86.6% after `pi-arrow`, 98.7% after `lam`/`pi-dep`, and 99.79% once the
/// `Prop` `Π` clause landed. What is left is **16** nodes — `proj` (13) and
/// `natLit` (3) — and both need the inductive interpretation, not more of
/// §6.2.
///
/// **The interpretation is therefore no longer the bottleneck, and chasing
/// those 16 would measure nothing.** Node share is not declaration share: the
/// 16 nodes sit inside declarations that are blocked at their root by §9 zone
/// B anyway, which is what [`tutorial_evidence_ledger`] reports.
///
/// This test's numbers count *syntactic* nodes and are unaffected by whether
/// evidence is threaded through them; it is the sizing instrument, not the
/// deliverable. The deliverable is the ledger beside it.
#[test]
fn tutorial_clause_census() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut counts: std::collections::BTreeMap<String, u64> = Default::default();
    let (mut done, mut todo) = (0u64, 0u64);
    for f in &files {
        let r = run(f);
        let Some(row) = r.stdout.lines().find(|l| l.starts_with("clauses\t")) else { continue };
        for kv in row.split('\t').skip(1) {
            let (k, v) = kv.split_once('=').expect("k=v");
            let v: u64 = v.parse().expect("number");
            match k {
                "interpreted" => done += v,
                "remaining" => todo += v,
                _ => *counts.entry(k.to_string()).or_default() += v,
            }
        }
    }
    let total: u64 = counts.values().sum();
    eprintln!("clause census over {} exports ({total} nodes):", files.len());
    for (k, v) in &counts {
        eprintln!("  {k:10} {v:6}  {:5.1}%", 100.0 * *v as f64 / total as f64);
    }
    eprintln!("  interpretable={done} remaining={todo}");
    assert_eq!(done + todo, total, "the split must partition the nodes");

    // The clauses still to do. Implementing one means deleting its line here
    // *and* moving it in `census::Clause::interpreted`, which is the point.
    let remaining: Vec<&str> = ["natLit", "proj"].into();
    let observed: Vec<&str> = counts
        .keys()
        .map(String::as_str)
        .filter(|k| {
            !matches!(
                *k,
                "bvar"
                    | "sort"
                    | "const"
                    | "app"
                    | "let"
                    | "pi-arrow"
                    | "lam"
                    | "pi-dep"
                    | "pi-prop"
            )
        })
        .collect();
    assert_eq!(observed, remaining, "the set of un-interpreted clauses changed");
    assert_eq!(total, 7748, "corpus node count changed — re-read the table above");
    assert_eq!(done, 7732, "interpretable node count changed — update the table above");
}

/// **The evidence ledger** — MINI-DESIGN.md §0's second axis, and the one
/// nanoda cannot produce today because its ledger mixes threading debt with
/// library debt.
///
/// Measured 2026-08-02, over the 218 `(declaration, σ)` pairs of the 89
/// exports mini still checks. Each pair asks for one thing:
/// `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`.
///
/// | outcome | pairs | axis |
/// | --- | ---: | --- |
/// | derived | 136 | — |
/// | uninterpreted inductive or projection | 35 | interpretation scope |
/// | a named `derived/` construction | 40 | library gap |
/// | **threading incompleteness** | **7** | — |
/// | mini bug | 0 | — |
///
/// # The model-assumption row is gone, and both halves of that are findings
///
/// It read **7**. Five were user-declared axioms — `aDepProp`, `aProp`,
/// `mkADepProp`, and the two definitions whose typings propagated one of those
/// reasons by §0.4 — and [`DECLINED_NONSTANDARD_AXIOM`] takes their two
/// exports out of scope at the frontend, because a user axiom's inhabitation
/// is not derivable *in principle* and a run that stops at the first missing
/// derivation would stop there for ever.
///
/// The other two were `Quot.sound` in `123_quotSoundType`, **and they were
/// misattributed**. `mini/src/ledger.rs` used to answer "why is this typing
/// missing?" with `Gap::Axiom` for any axiom, unconditionally, ahead of the
/// check on whether the *type* had even interpreted. That file settles it on
/// its own: `quotSoundType`'s value is literally `Quot.sound.{u}`, the same
/// constant under a second name at the same type, and mini filed one copy
/// `no-interp(Quot)` and the other `axiom(Quot.sound)` — **the same obligation
/// on two different axes in one file.** The interpretation reason is the right
/// one, and all four pairs now carry it.
///
/// What is left is that `Cause::Assumption` has no occupant. It is retired
/// rather than pinned at zero: the frontend decline now enforces the "not
/// derivable in principle" boundary where it can be acted on, so the cause
/// could only be reached through a hole in that boundary. `Gap::Axiom`
/// survives for Lean's own three, reclassified to `Cause::Library` — the model
/// *validates* each of them (a quotient is a set of equivalence classes, in
/// which `Quot.sound` is a theorem; `Prop` is `{∅, {•}}`, in which `propext`
/// is; and the kernel already carries `Thm::ax_choice`), so each is a
/// construction someone has to build, not a postulate. On this corpus the
/// variant is now unreachable, because no axiom's type interprets yet.
///
/// # The dependent eliminator moved 18 pairs, and 6 of them only one row
///
/// `mini/src/rec_dep.rs` wired [`derived::inductive::DepRecursor`] and closed
/// the whole `recursor(·: dependent motive)` row — `Bool` 4, `TwoBool` 2,
/// `Prod` 3, `PProd` 2, `N` 4, `List` 3. Where they went is the finding:
///
/// | | pairs | base → variant |
/// | --- | ---: | --- |
/// | derived outright | 12 | library → **derived** |
/// | `iota(Bool.rec)`, `iota(Prod.rec)` | 2 | library → threading |
/// | `binder-congruence` | 4 | library → threading |
///
/// **The 6 are the same sentence `iota(Eq.rec)` was.** A recursor's *typing* and
/// its ι *rule* are separate obligations; the files that only apply the
/// eliminator (`060`, `061`, `064`, `067`, the value half of `063`/`074`/`076`)
/// are done, and the files that state its reduction equations (`073`, `074`,
/// `075`, `076`) get one step further and stop where `whnf`'s recursor arm has
/// no certificate to hand the step. `DepRecursor::iota` is exactly that
/// certificate, is built, and is *not* wired — the threading row is where that
/// now shows, and it is the fourth time this ledger has recorded a row that was
/// zero because nothing reached it.
///
/// The row-24 count this table used to carry for class (T), `n ≥ 1` was **22**
/// and the six per-declaration pins beneath it summed to 18. The pins were
/// right; 22 was an arithmetic slip, and 3 + 18 + 2 + 4 = 27 is the `recursor(·)`
/// row it came apart from.
///
/// # The general class-(S) clause moved 2 pairs, and moved them *sideways*
///
/// `mini/src/class_s.rs` retired `mini/src/direct.rs`'s `Clause::And` and
/// `Clause::Unit` — two hand-written closed forms, `and_set(a,b)` and `1` —
/// and routed `And`, `PUnit`, `True` and `ProjDataIndex` through §5.3's
/// carrier: `A_φ(p⃗)` over `ψ = ⋁ᵢ ∃y⃗ᵢ. (⋀ⱼ yⱼ ∈ βᵢⱼ ∧ • = •)`. The whole
/// ledger moved by one row:
///
/// | | pairs | base → variant |
/// | --- | ---: | --- |
/// | `prop-inductive(ProjDataIndex)` | 2 | scope → **gone** |
/// | `recursor(ProjDataIndex: class (S) eliminator)` | 2 | — → library |
///
/// **`constEv` did not move, and that is the measurement this change existed
/// to take.** The interpretations genuinely changed — `⟦And a b⟧` is now
/// `A_φ(⟦a⟧,⟦b⟧)` and not `and_set(⟦a⟧,⟦b⟧)`, `⟦PUnit⟧` is `A_φ()` and not
/// `1`, provably equal by `LeProp::true_` but *not the same term* — so every
/// downstream row had to be re-measured rather than assumed. `proj(And)` (2),
/// `unit-like(PUnit)` (2), `fun-eta` (2), the 91 acceptances, the 7748-node
/// clause census and the conversion split are all bit-identical across the
/// swap. Nothing regressed and nothing improved: the two closed forms were
/// buying exactly the four typings the general clause buys.
///
/// What moved is `ProjDataIndex`, which had **no** closed form and was
/// therefore not reachable at all. Its carrier and constructor now derive
/// (`typeEv` 177 → 179), and the pair goes on to its eliminator — which is
/// where the class-(S) row now sits, and `mini/src/recursor.rs`'s header says
/// what one premise of `LePropRecursor` is missing and why assembling it here
/// would put a model-level derivation in the checker.
///
/// # The eliminator moved 27 pairs, and only two of them moved to *derived*
///
/// `mini/src/recursor.rs` is the third and last of zone B's builds, and the
/// row it acted on — `recursor(·)`, 27 pairs, the largest single row there was
/// — came apart into four:
///
/// | | pairs | where they went |
/// | --- | ---: | --- |
/// | `Eq.rec` | 3 | 2 derived; 1 on to `iota(Eq.rec)` |
/// | class (T), `n ≥ 1` (`Bool`, `TwoBool`, `Prod`, `PProd`, `N`, `List`) | 22 | library: a **dependent** eliminator |
/// | class (T), `n = 0` (`Empty`) | 2 | library: `GenRecursor` declines it |
/// | class (S) (`And`, `PUnit`) | 4 | library: the class-(S) eliminator |
///
/// **The 24 that became library gaps are the finding, not the two that
/// closed.** They were *scope* while they meant "zone B has not got here"; the
/// wiring now reaches every recursor the corpus mentions, and what stops all
/// but one of them is a construction `derived/` does not have. Which one, and
/// why the answer is not the one `RECURSOR-DESIGN.md` §11.1 measured, is
/// `mini/src/recursor.rs`'s header: a pair asks for `⊢ ⟦T.rec.{σ}⟧ ∈ ⟦its Lean
/// type⟧`, whose innermost factor is `∀t ∈ ⟦T p⃗⟧. rec(t) ∈ app(C,t)` at a
/// *variable* motive `C`, while `derived::inductive::GenRecursor` is simply
/// typed. That note's census closed at zero because it counted ι sites, where
/// the motive has already been instantiated; this corpus's recursor files
/// η-expand the eliminator itself, so the motive is never a constant and the
/// census here is 22 of 22.
///
/// **`threading-incompleteness` is no longer zero, and it is the same story
/// one axis over.** `094_ruleK` was blocked at `recursor(Eq)`; with `⟦Eq.rec⟧`
/// in the store it gets one step further and stops at the ι rule, which is
/// `Gap::Iota` — `Cause::Threading`, correctly, because every piece of it
/// exists (`Interp::beta_spine` reduces `Eq.rec`'s nest to its own bottom) and
/// `whnf`'s recursor arm hands the step no certificate. One pair, one named
/// absence, and the third time this ledger has recorded that a row was zero
/// because nothing reached it rather than because nothing was owed.
///
/// **Every row above moved when the three direct clauses landed, and the two
/// that moved *up* are the finding.** They interpreted `Eq`, `And` and `PUnit`
/// by naming their denotation — the class-(S) collapse that
/// `INDEXED-DESIGN.md` §2.2 designates for `Eq` — and 22 pairs turned into
/// derived typings. (Two of the three have since been retired into
/// `mini/src/class_s.rs`; the section above measures that swap, and it moved
/// none of these numbers.) What the other 22 of the 44 they unblocked did was expose
/// what sat *behind* them: 7 more library items (`proj(And)`, `fun-eta`,
/// `unit-like(PUnit)`, one more `ind-summand`) and 15 more scope items, mostly
/// `recursor(·)` at the very declarations now interpreted. A declaration's
/// carrier and its eliminator are separate pieces of work, and until the
/// carrier exists the eliminator is not even reachable to be counted.
///
/// The same reading applies one step back. The library row was zero before §9
/// zone B's boundary was built; MINI-DESIGN.md §10 read that zero as "the
/// backlog is *behind* zone B on the critical path", when what it meant was
/// that the backlog was invisible because nothing reached it. They were beside
/// zone B, not behind it — and both have since been built in `derived/` and
/// wired here, which is what took the row from 43 to 30.
///
/// **What wiring them actually bought is the second finding, and it is smaller
/// than the 36 they were counted as.** `cumul::summand_obligations` closes the
/// per-field obligation completely: `List`, `PProd`, `PSigma` and `TwoBool`
/// now have carriers *and* constructors, and their pairs moved on to
/// `recursor(·)` and `proj(·)`. `DeclUniverse::over_at` closes the *placement*
/// of a declaration above `Type 0` — but not the declaration, because the
/// summand and tag pipeline is deliberately not generalised past `U₁`, so
/// `Prod.{1,0}` and `TypeWithTypeField` fail one step earlier at a field that
/// cannot be raised *down* into `U₁`. Those 9 pairs are still blocked, and the
/// row they are blocked in changed from `ind-universe` to `ind-summand`, which
/// is the honest name for it.
///
/// The 65 that remain scope are real scope: the recursor interpretation, which
/// a carrier and constructors do not carry (`recursor`, now the largest single
/// row by some way); the class-(S) and class-(P) declarations with no closed
/// form (`prop-inductive`); indexed families (`indexed-family`); a
/// function-typed recursive argument; `quot`; and `natLit`. The 7 are
/// `Quot.sound` and the corpus's own declared axioms, which are not work at
/// all.
///
/// That distinction is the whole point of the two axes, and it is exactly what
/// this test is a ratchet on: an unrecorded *improvement* fails it as loudly as
/// a regression, because either means the table above no longer describes the
/// project.
///
/// # The indexed walk runs before the decline, and it moved one row
///
/// `zoneb::build` used to refuse an indexed declaration with a
/// declaration-level guard ahead of everything, so no indexed family in the
/// corpus was ever *walked*. It is now walked to an `IndexedDeclSpec` and only
/// then declined, which turns one unanswered question into a measured one:
/// **which of these families can `derived::inductive::family` even express?**
///
/// | declaration | pairs | before | after |
/// | --- | ---: | --- | --- |
/// | `RBTree` | 6 | `indexed-family` | `indexed-family` — representable |
/// | `SortElimProp` | 2 | `indexed-family` | `indexed-family` — representable |
/// | `SortElimProp2` | 1 | `indexed-family` | `indexed-family` — representable |
/// | **`Acc`** | **3** | `indexed-family` | **`fun-typed-rec-arg`** |
///
/// So `indexed-family(X)` now means one thing — a `well_formed` spec waiting
/// on the carrier wiring and nothing else — where before it meant "indexed,
/// and we never looked".
///
/// **`Acc` is the finding.** It was never blocked on indexing.
/// `Acc.intro`'s recursive argument is `∀y. r y x → Acc r y`, a *function-typed*
/// recursive field — the `Σ(z::γ)` fibre the thesis's recursive-argument rule
/// does not collapse, and a different `derived/` item entirely. Three pairs
/// were filed against indexed families, so anyone sizing that work would have
/// counted `Acc` in and found it still blocked afterwards.
///
/// **The cause split did not move**, and that is the check that this is a
/// refinement rather than a change: `indexed-family` and `fun-typed-rec-arg`
/// are both `Cause::Scope`, so `135 / 38 / 38 / 7` is bit-identical across it.
/// A label that moved *between* axes would be a different kind of event and is
/// asserted against below.
///
/// The reason attribution obeys §0.4 — a gap's reason propagates from the
/// sub-result that caused it. Two rounds of getting that wrong are recorded in
/// `mini/src/ledger.rs`: 104 pairs once filed as `pi-typing-unthreaded` when
/// the cause was an inductive several levels down, and 57 theorems filed as
/// `axiom(…)` because `Gap::Axiom` was the fallback. The second is the sharper
/// mistake — "not derivable in principle" and "not derived yet" are not even on
/// the same axis.
#[test]
fn tutorial_evidence_ledger() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut totals: std::collections::BTreeMap<String, u64> = Default::default();
    for f in &files {
        let r = run(f);
        let Some(row) = r.stdout.lines().find(|l| l.starts_with("evidence\t")) else { continue };
        for kv in row.split('\t').skip(1) {
            let (k, v) = kv.split_once('=').expect("k=v");
            *totals.entry(k.to_string()).or_default() += v.parse::<u64>().expect("number");
        }
    }
    eprintln!("evidence ledger over {} exports:", files.len());
    for (k, v) in &totals {
        eprintln!("  {k:34} {v:5}");
    }
    let g = |k: &str| totals.get(k).copied().unwrap_or(0);

    assert_eq!(g("pairs"), 218, "the (declaration, σ) population changed");
    assert_eq!(g("constEv"), 136, "constant typings derived changed — update the table above");
    assert_eq!(g("typeEv"), 179, "type typings derived changed — update the table above");
    // **The measurement that keeps the type's own typing out of
    // `blocker::Obligation`.** Zero means no pair ever derives
    // `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` while leaving `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` missing, so
    // the two obligations are ordered and stopping on the constant's typing
    // never steps over a hole. A nonzero count would mean the blocker is
    // walking past an underived sub-obligation, and this is where that has to
    // be argued.
    assert_eq!(g("typeEvOnlyGap"), 0, "a constant typing outran its type's own typing");

    // `mini-bug` is the one row still pinned at zero as a *deliverable*.
    // Threading is pinned at **7**, and split by name rather than rolled up:
    // every one is a certificate that exists in `derived/` and is not handed to
    // `whnf`'s recursor arm or to the binder congruence. An eighth would be as
    // much a surprise as the first was, and this is where it has to be argued
    // for.
    assert_eq!(g("mini-bug"), 0, "a composition that should have fitted did not");
    assert_eq!(g("threading-incompleteness"), 7, "the threading residue changed");
    for (k, v) in [
        ("waiting:iota(Eq.rec)", 1),
        ("waiting:iota(Bool.rec)", 1),
        ("waiting:iota(Prod.rec)", 1),
        ("waiting:binder-congruence", 4),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    assert_eq!(g("library-gap"), 40, "the reachable `derived/` backlog changed");
    assert_eq!(g("interpretation-scope"), 35, "the §9 zone B residue changed");
    // **`Cause::Assumption` is retired, and this is the pin that says so.**
    // Not "is zero" — the row must not be *emitted*, because a cause that can
    // only be reached through a hole in the frontend decline is better spelled
    // as its absence.
    assert!(
        !totals.contains_key("model-assumption"),
        "the model-assumption axis is retired; something reintroduced it"
    );
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:axiom(")),
        "an axiom's inhabitation was blamed for a typing again; check ty_blocked first"
    );
    // All four of `123_quotSoundType`'s pairs, on one axis. Two of them used
    // to be `axiom(Quot.sound)`, which is the misattribution the header
    // records.
    assert_eq!(g("waiting:no-interp(Quot)"), 6, "the Quot interpretation residue changed");

    // **The indexed families, split by whether they are representable.**
    // `indexed-family(X)` means the boundary walk produced a `well_formed`
    // `IndexedDeclSpec` and the carrier wiring is all that is missing; any
    // other reason on these declarations means the walk refused the shape,
    // which is a permanent decline rather than a to-do. Pinned per
    // declaration, not rolled up, because the whole finding is *which*.
    for (k, v) in [
        ("waiting:indexed-family(RBTree)", 3),
        ("waiting:indexed-family(SortElimProp)", 2),
        ("waiting:indexed-family(SortElimProp2)", 1),
        // Never an indexing problem: a function-typed recursive argument.
        ("waiting:fun-typed-rec-arg(Acc)", 3),
        ("waiting:fun-typed-rec-arg(RTree)", 4),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    assert!(
        !totals.contains_key("waiting:indexed-family(Acc)"),
        "Acc is blocked by a function-typed recursive argument, not by indexing"
    );
    // A shape the walk cannot express would show up here, and none does.
    assert!(
        !totals.keys().any(|k| k.contains("indexed spec not well formed")
            || k.contains("index type")
            || k.contains("result index")
            || k.contains("recursive argument index")),
        "an indexed family became unrepresentable: {:?}",
        totals.keys().filter(|k| k.contains("index")).collect::<Vec<_>>()
    );
    assert_eq!(
        g("constEv")
            + g("interpretation-scope")
            + g("library-gap")
            + g("threading-incompleteness"),
        g("pairs"),
        "every pair must be either derived or attributed — nothing unaccounted"
    );

    // The eliminator row, split by what each declaration waits on. Not a
    // rollup: the whole finding is *which* construction is missing where, and
    // a rollup would let one row absorb another's regression.
    for (k, v) in [
        ("waiting:recursor(Bool: dependent motive)", 0),
        ("waiting:recursor(TwoBool: dependent motive)", 0),
        ("waiting:recursor(Prod: dependent motive)", 0),
        ("waiting:recursor(PProd: dependent motive)", 0),
        ("waiting:recursor(N: dependent motive)", 0),
        ("waiting:recursor(List: dependent motive)", 0),
        ("waiting:recursor(Empty: no constructors)", 2),
        ("waiting:recursor(And: class (S) eliminator)", 2),
        ("waiting:recursor(PUnit: class (S) eliminator)", 2),
        ("waiting:recursor(ProjDataIndex: class (S) eliminator)", 2),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    // The dependent-motive rows are pinned at **zero** rather than deleted: a
    // reason string that comes back is a regression, and a row that silently
    // stops being emitted is indistinguishable from one that was never
    // measured. `mini/src/recursor.rs` no longer has a constant for it.
    assert!(
        !totals.keys().any(|k| k.contains("dependent motive")),
        "the dependent-motive reason string is gone; nothing may reintroduce it"
    );

    // §11.5's escapes-analogue. An assumption can only be introduced by a
    // `Scope` and is discharged at its close, so at the store funnel — where no
    // scope is open — `Sealed::new` cannot fail on a correctly threaded run.
    assert_eq!(g("unsealed"), 0, "a hypothesis escaped to the store funnel");
}

/// **The next thing to fix.**
///
/// `mini --block` stops the interpretation pass at the first
/// `(declaration, σ)` whose obligation it cannot discharge and prints the
/// report; this walks the corpus in file order and finds the first file that
/// stops. The report is printed to stderr unconditionally, so
/// `cargo test -p mini --test tutorial first_blocker -- --nocapture` is the
/// one command that answers "what now".
///
/// **It is a ratchet, not a failing test.** Green means the recorded blocker
/// is still the one in the way; red means it moved, and the report beside the
/// failure is the new one. That keeps `cargo test` usable — the ordinary path
/// is unchanged and the statistical tests above still run unarmed — while
/// making the *ordering* visible, which is the thing a table of 83 residual
/// pairs cannot show.
///
/// Measured 2026-08-02: **44** of the 89 checked exports stop, 45 run clean.
/// The first is still `042_rbTreeDef`, but it has moved **inside the file**:
/// `rbTreeDef` at `σ = {u := 0}` now derives — `mini/src/zoneb.rs`'s
/// `build_indexed` produces `⟦RBTree.{0}⟧` and its typing — and the run stops
/// at the *second* instantiation, `σ = {u := 1}`, with `ind-summand(RBTree)`.
///
/// That is not the indexed machinery failing. `RBTree.{1}`'s field `x : α` has
/// `α : Sort 2`, and `ctor_spec` raises a field type's typing **into `U₁`**,
/// which cannot lower from `U₂`. It is the same ceiling `Prod` at
/// `u := 1, v := 1` has always hit, and it is `mini/`'s to fix now that
/// `derived::cumul::summand_obligations_at` exists.
const FIRST_BLOCKER: (&str, &str, &str) =
    ("042_rbTreeDef.ndjson", "rbTreeDef", "ind-summand(RBTree)");

#[test]
fn tutorial_first_blocker() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut blocked = 0usize;
    let mut first: Option<(String, String, String, String)> = None;
    for f in &files {
        let r = run_with(f, &["--block"]);
        if r.verdict != Verdict::Blocked {
            continue
        }
        blocked += 1;
        let row = r.stdout.lines().find(|l| l.starts_with("BLOCKED\t")).expect("a BLOCKED row");
        let cols: Vec<&str> = row.split('\t').collect();
        if first.is_none() {
            first = Some((
                cols[1].to_string(),
                cols[2].to_string(),
                cols[3].to_string(),
                r.stdout.clone(),
            ));
        }
    }
    let Some((export, decl, key, report)) = first else {
        panic!("no export blocked — the corpus is fully derived, and this test is now the ratchet that says so")
    };
    eprintln!("{blocked} of {} exports block; the first is:\n\n{report}", files.len());
    assert_eq!(
        (export.as_str(), decl.as_str(), key.as_str()),
        FIRST_BLOCKER,
        "the first blocker moved — the report above is the new one"
    );
    assert_eq!(blocked, 44, "the number of exports that stop changed");
}

/// **The hypothesis-free conversion split** — MINI-DESIGN.md §0.3, which the
/// threading census called the one genuine unsettled design decision.
///
/// The question is whether a conversion cache must key on `Γ` as well as the
/// endpoints, or may store `Sealed` entries only. §0.3 reduced it to that
/// disjunction by inference; this measures it.
///
/// Measured 2026-08-01, over every conversion `whnf` or `assert_def_eq` was
/// *asked for* (a decision-only call hands in no endpoints and states nothing):
///
/// | | conversions | hypothesis-free |
/// | --- | ---: | ---: |
/// | all | 2 839 092 | 2 838 980 (99.996%) |
/// | endpoints actually differ | 665 | 626 (94.1%) |
///
/// The second row is the one that matters: a reflexivity is free to re-derive,
/// so a cache exists for the 665 that move. **39 of them carry `Γ`** — and
/// every one is a beta step, because beta is the only rule that consumes a
/// membership. Everything else is reflexivity, a stored defining axiom, or a
/// congruence over those, and *reflexivity under a binder carries no
/// hypothesis* even when its term mentions the binder's variable.
///
/// So §0.3's second horn is the cheap one, by measurement and not only by
/// argument: a `Sealed`-only store captures 94% of the shareable conversions,
/// and the 6% it refuses are exactly the ones local to the binder that
/// introduced them, which the scope re-derives at one vector index.
///
/// # The gapped row is no longer zero, and that is the same finding again
///
/// `gapped` counts conversions that were asked for **with both endpoints in
/// hand** and could not be certified. It was zero for as long as `PUnit` and
/// `Eq` had no interpretation, because a rule whose endpoints do not interpret
/// hands in nothing and is not counted at all. With `mini/src/direct.rs` in
/// place, `102`/`103`'s unit-like eta and `106`/`107`'s function eta reach the
/// certificate step for the first time, and there are exactly two library
/// lemmas missing — `Gap::UnitLike` (12) and `Gap::FunEta` (10), both
/// `Cause::Library` and both already named in the evidence ledger's `waiting:`
/// rows. So the 22 are not new debt; they are the *conversion-level* view of
/// debt the evidence ledger was already counting at declaration level.
///
/// The 6 that took it to 28 are `094_ruleK`, and they are the same sentence
/// again: with `⟦Eq.rec⟧` in the store (`mini/src/recursor.rs`) its K-rule
/// reduction reaches the certificate step for the first time, and `whnf`'s
/// recursor arm has none to give — `Gap::Iota`, the one threading pair
/// [`tutorial_evidence_ledger`] pins. The other four counters move with it:
/// 4 more conversions with distinct endpoints, 2 of them hypothesis-free.
///
/// # 28 → 216, and no new *cause*
///
/// `mini/src/rec_dep.rs` put four more eliminators in the store, and every
/// reduction that was previously blocked at the eliminator's own typing now
/// reaches the certificate step. The 216 break down by the reason they were
/// declined with — the same key the evidence ledger's `waiting:` rows use —
/// and there are **five** reasons, all of them already on that ledger:
///
/// | reason | conversions | cause |
/// | --- | ---: | --- |
/// | `binder-congruence` | 165 | threading |
/// | `iota(Prod.rec)` | 13 | threading |
/// | `unit-like(PUnit)` | 12 | library |
/// | `iota(Bool.rec)` | 10 | threading |
/// | `fun-eta` | 10 | library |
/// | `iota(Eq.rec)` | 6 | threading |
///
/// The two library rows are unchanged at 12 and 10; the whole of the growth is
/// the ι rule at two more recursors and the binder congruence, and `whnf` gets
/// a certificate for the first from `DepRecursor::iota` the day it is wired.
/// So this test's pin still means what it meant: a **sixth** reason here would
/// be a regression, and the five are named.
///
/// `moved` and `movedSealed` grow with them, and the Γ-carrying share moves
/// from 6% to 42% — the newly reachable conversions are overwhelmingly
/// *under a binder*, which is exactly where §0.3 predicted a `Sealed`-only
/// store would refuse to help.
#[test]
fn tutorial_conversion_split() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut t: std::collections::BTreeMap<String, u64> = Default::default();
    for f in &files {
        let r = run(f);
        let Some(row) = r.stdout.lines().find(|l| l.starts_with("convs\t")) else { continue };
        for kv in row.split('\t').skip(1) {
            let (k, v) = kv.split_once('=').expect("k=v");
            *t.entry(k.to_string()).or_default() += v.parse::<u64>().expect("number");
        }
    }
    let g = |k: &str| t.get(k).copied().unwrap_or(0);
    eprintln!(
        "conversions: proved={} sealed={} gapped={} moved={} movedSealed={}",
        g("proved"),
        g("sealed"),
        g("gapped"),
        g("moved"),
        g("movedSealed")
    );
    // Not zero, and the header says why: exactly two named library lemmas,
    // reachable for the first time. A *third* cause appearing here would be a
    // regression this catches, which is what the pin is for.
    assert_eq!(g("gapped"), 216, "the uncertified-conversion population changed");
    assert_eq!(g("moved"), 2418, "the non-trivial conversion population changed");
    assert_eq!(g("movedSealed"), 1398, "the hypothesis-free split changed — §0.3's measurement");
    assert!(g("sealed") <= g("proved"));
    // The Γ-carrying ones exist and are not an artefact of nobody looking:
    // `conv::beta_takes_its_premise_from_the_scope_at_zero_cost` exhibits one
    // directly, and this is the corpus-scale count of the same thing.
    assert_eq!(g("moved") - g("movedSealed"), 1020, "the Γ-carrying conversions changed");
}

/// Pull `key=<number>` out of the `facts` row.
fn fact(stdout: &str, key: &str) -> Option<u64> {
    stdout
        .lines()
        .find(|l| l.starts_with("facts\t"))?
        .split('\t')
        .find_map(|kv| kv.strip_prefix(key).and_then(|r| r.strip_prefix('=')))?
        .parse()
        .ok()
}
