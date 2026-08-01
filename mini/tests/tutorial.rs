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
}

struct Run {
    verdict: Verdict,
    stdout: String,
}

/// `mini --verbose <file>`; the exit status is the verdict (`Main.lean`'s).
fn run(export: &Path) -> Run {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--verbose")
        .arg(export)
        .output()
        .expect("spawn mini");
    let verdict = match out.status.code() {
        Some(0) => Verdict::Accept,
        Some(1) => Verdict::Reject,
        Some(2) => Verdict::Decline,
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

fn good_dir() -> PathBuf { repo_root().join("vendor/arena-tests/good/tutorial") }
fn bad_dir() -> PathBuf { repo_root().join("vendor/arena-tests/bad/tutorial") }

/// mini-lean accepts all 91 tutorial exports. So must mini.
#[test]
fn tutorial_good_all_accepted() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    assert_eq!(files.len(), 91, "the tutorial corpus is 91 exports");
    let mut bad = Vec::new();
    for f in &files {
        let r = run(f);
        if r.verdict != Verdict::Accept {
            bad.push(format!("{}: {:?}\n{}", stem(f), r.verdict, r.stdout));
        }
    }
    assert!(bad.is_empty(), "expected all 91 accepted; these were not:\n{}", bad.join("\n"));
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
/// Measured 2026-08-01, over the 223 `(declaration, σ)` pairs of the 91
/// exports. Each pair asks for one thing: `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`.
///
/// | outcome | pairs | axis |
/// | --- | ---: | --- |
/// | derived | 93 | — |
/// | uninterpreted inductive, projection or recursor | 123 | interpretation scope |
/// | an axiom's inhabitation | 7 | model assumption |
/// | **threading incompleteness** | **0** | — |
/// | **library gap** | **0** | — |
/// | mini bug | 0 | — |
///
/// **The residue is not a threading worklist.** Every one of the 123 is an
/// inductive constant, its recursor or a projection out of it, blocked by §9
/// zone B — which is *interpretation scope*, work the design has not reached,
/// not work it reached and left undone. The 7 are `Quot.sound` and the
/// corpus's own declared axioms, which are not work at all.
///
/// That distinction is the whole point of the two axes, and it is exactly what
/// this test is a ratchet on: an unrecorded *improvement* fails it as loudly as
/// a regression, because either means the table above no longer describes the
/// project.
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

    assert_eq!(g("pairs"), 223, "the (declaration, σ) population changed");
    assert_eq!(g("constEv"), 93, "constant typings derived changed — update the table above");
    assert_eq!(g("typeEv"), 112, "type typings derived changed — update the table above");

    // The three named axes. Two of them are the deliverable and are pinned at
    // zero; the third is the honest remainder.
    assert_eq!(g("threading-incompleteness"), 0, "threading debt reappeared");
    assert_eq!(g("library-gap"), 0, "a `derived/` item is now on the critical path");
    assert_eq!(g("mini-bug"), 0, "a composition that should have fitted did not");
    assert_eq!(g("interpretation-scope"), 123, "the §9 zone B residue changed");
    assert_eq!(g("model-assumption"), 7, "the axiom count changed");
    assert_eq!(
        g("constEv") + g("interpretation-scope") + g("model-assumption"),
        g("pairs"),
        "every pair must be either derived or attributed — nothing unaccounted"
    );

    // §11.5's escapes-analogue. An assumption can only be introduced by a
    // `Scope` and is discharged at its close, so at the store funnel — where no
    // scope is open — `Sealed::new` cannot fail on a correctly threaded run.
    assert_eq!(g("unsealed"), 0, "a hypothesis escaped to the store funnel");
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
/// | all | 1 039 457 | 1 039 427 (99.997%) |
/// | endpoints actually differ | 548 | 523 (95.4%) |
///
/// The second row is the one that matters: a reflexivity is free to re-derive,
/// so a cache exists for the 548 that move. **25 of them carry `Γ`** — and
/// every one is a beta step, because beta is the only rule that consumes a
/// membership. Everything else is reflexivity, a stored defining axiom, or a
/// congruence over those, and *reflexivity under a binder carries no
/// hypothesis* even when its term mentions the binder's variable.
///
/// So §0.3's second horn is the cheap one, by measurement and not only by
/// argument: a `Sealed`-only store captures 95% of the shareable conversions,
/// and the 5% it refuses are exactly the ones local to the binder that
/// introduced them, which the scope re-derives at one vector index.
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
    assert_eq!(g("gapped"), 0, "a conversion that was asked for could not be certified");
    assert_eq!(g("moved"), 548, "the non-trivial conversion population changed");
    assert_eq!(g("movedSealed"), 523, "the hypothesis-free split changed — §0.3's measurement");
    assert!(g("sealed") <= g("proved"));
    // The Γ-carrying ones exist and are not an artefact of nobody looking:
    // `conv::beta_takes_its_premise_from_the_scope_at_zero_cost` exhibits one
    // directly, and this is the corpus-scale count of the same thing.
    assert_eq!(g("moved") - g("movedSealed"), 25, "the Γ-carrying conversions changed");
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
