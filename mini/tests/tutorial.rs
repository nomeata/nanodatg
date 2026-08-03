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
/// | `natLit` | 3 | 0.0% | interpreted (expanded to `Nat.succ^n Nat.zero`) |
/// | `strLit` | 0 | — | unreachable on this corpus |
///
/// **99.83%** of nodes are interpretable: 81.7% at the first measurement,
/// 86.6% after `pi-arrow`, 98.7% after `lam`/`pi-dep`, 99.79% once the `Prop`
/// `Π` clause landed, and 99.83% when `natLit` moved. What is left is **13**
/// nodes, all `proj`, and they need the inductive interpretation rather than
/// more of §6.2.
///
/// *(`natLit`'s 3 read "**remaining** — needs `Nat`'s interpretation". `Nat` is
/// an ordinary inductive and had translated for some time; what was missing was
/// the literal's own clause, and it is `⟦natLit n⟧ = ⟦Nat.succ^n Nat.zero⟧` —
/// the expansion inferred through the general route, with nothing here knowing
/// what a numeral is. The row moved because a *different* thing landed than the
/// one its note named.)*
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
    let remaining: Vec<&str> = ["proj"].into();
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
                    | "natLit"
            )
        })
        .collect();
    assert_eq!(observed, remaining, "the set of un-interpreted clauses changed");
    assert_eq!(total, 7748, "corpus node count changed — re-read the table above");
    assert_eq!(done, 7735, "interpretable node count changed — update the table above");
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
/// | derived | 150 | — |
/// | uninterpreted inductive or projection | 26 | interpretation scope |
/// | a named `derived/` construction | 30 | library gap |
/// | **threading incompleteness** | **12** | — |
/// | mini bug | 0 | — |
///
/// # `indexed-family` was one row over three problems, and splitting it moved
/// 7 pairs off the wrong axis
///
/// The label named where the walk stopped, not what was missing — the fourth
/// time on this project, after `Acc`, `Quot.sound` and the class-(S)
/// eliminator. Three unrelated constructions sat under it, owed on two axes:
///
/// | row | pairs | was | is |
/// | --- | ---: | --- | --- |
/// | `indexed-family(SortElimProp: class (S) carrier at an index)` | 2 | scope | scope — **since derived** |
/// | `indexed-family(SortElimProp2: class (P) truncation over an indexed base)` | 1 | scope | scope |
/// | `recursor(RBTree: indexed eliminator: a Prop-valued motive)` | 2 | scope | **library** |
/// | `recursor(RBTree: indexed eliminator: a value-valued motive)` | 2 | scope | **threading** |
///
/// So `interpretation-scope` 30 → 26, `library-gap` 28 → 30, and
/// `threading-incompleteness` 10 → 12. **No pair derived and none stopped
/// deriving**; every number above is the same work under a name that says
/// whose it is. The two carriers are still scope because neither is wired at
/// all; the eliminator is not scope any more, because after
/// `mini/src/ctor_ix.rs` the family *is* translated and what is left is one
/// named construction each.
///
/// The eliminator's own split is §6.2's clause on the motive's sort, read off
/// the recursor's motive binder and not off σ: at `u₁ = 0` the eliminator is a
/// **proof**, `⟦T.rec⟧` is `•`, and one `derived/` theorem over
/// `IndexedCtor::inv` is owed; at `u₁ ≥ 1` it is a value at a possibly
/// family-valued motive, which was filed as §5.2's `T`-policy and is a mini-side
/// recogniser. Reading that binder needed one fix of its own: `motive_level`
/// peeled a single binder, which is right for a non-indexed motive
/// `C : T p⃗ → Sort u₁` and returns `None` at every indexed one, where the
/// `Sort` sits under `ni + 1`. It reported "this is not a Lean motive" for
/// "this function does not know about indices" until `RBTree` was asked.
///
/// # The indexed constructors moved 2 pairs, and only on the *type* axis
///
/// `mini/src/ctor_ix.rs` builds `⟦T.ctorᵢ⟧` for an indexed family, and
/// `RBTree`'s three constructors are the corpus's only occupants. `typeEv` goes
/// 189 → 191 and **`constEv` does not move at all**: the two pairs whose
/// *types* mention `RBTree.leaf`/`red`/`black` now interpret, and both then go
/// on to need `RBTree.rec`, which is the indexed eliminator and a different
/// row. Nothing else on the ledger moves, and that is the honest reading of a
/// piece of work that makes objects *exist* rather than discharging an
/// obligation: `waiting:indexed-family(RBTree)` is still 4, and every one of
/// those 4 is now waiting on the eliminator rather than on the carrier's
/// constructors.
///
/// What did move and is not a number is the **label**. `no-interp(RBTree.leaf)`
/// was `stored_or_reason_after`'s fallback — "not in the store", which reads
/// the same whether the constructor path declined for a nameable reason or
/// nothing ever tried it. `Gap::IndexedCtor` carries the reason and its own
/// cause, and the fallback is now reached only in the second case.
///
/// # The class-(S) eliminator moved 6 pairs, all of them to *derived*
///
/// `mini/src/rec_prop.rs` closed the whole `recursor(·: class (S) eliminator)`
/// row — `And` 2, `PUnit` 2, `ProjDataIndex` 2 — and every one went straight to
/// a derived typing. Nothing moved sideways and no new row appeared: the
/// conversion split is bit-identical across the change (216 / 2418 / 1398), the
/// clause census is unchanged, and `library-gap` and `interpretation-scope` did
/// not move at all.
///
/// **That the whole row went to `derived` is the measurement, and it is the
/// second half of the cause correction.** Those six pairs were filed
/// `Cause::Library` until `Gap::Recursor` started carrying its cause, at which
/// point they moved *library → threading* (37 → 28 and 7 → 16, together with
/// three `dependent recursor` pairs). The prediction the carried cause encoded
/// was "`derived/` owes nothing here; this is wiring", and the wiring is what
/// closed it — so the correction was right, and the column it moved them into
/// is the column the work was actually done in. Had the label still read
/// `Cause::Library`, this landing would have shown 6 pairs leaving a column
/// that names a `derived/` shortfall for a change that touched no `derived/`
/// file.
///
/// What is left on the row is a **different** problem under a **different**
/// label: a class-(S) declaration with no constructors is
/// `recursor(·: class (S) eliminator: no constructors)`, which is `¬ψ`,
/// `LeProp::false_` and ex falso and shares no step with the rule above. It has
/// no occupant in this corpus — `VoidProp` lives in
/// `mini/tests/fixtures/empty_parameterised.lean` — which is why the split was
/// made with this landing rather than after it: the moment the row had one
/// occupant left, a label covering both would have described a derivation that
/// occupant does not need.
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
/// | `SortElimProp` | 2 | `indexed-family` | `indexed-family` — representable, and **since derived at both σ** |
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
/// # The summand ceiling is gone, and it took eleven pairs with it
///
/// `ctor_spec` raised a field type's typing **into `U₁`**, and `decl_universe`
/// ran the summand induction there and lifted the finished tag sum afterwards.
/// That works only when every *field* can be lowered into `U₁` first, which is
/// the one thing cumulativity cannot do — so a declaration whose fields live
/// in `Sort 2` stopped, however tall its own carrier was allowed to be.
///
/// Both now run at the declaration's **own** resultant rung
/// (`cumul::summand_obligations_at`, `summand_at`, `tags_at`), and the raise
/// afterwards is deleted rather than generalised: `tags_at` already states
/// `⊢ [H →] A ∈ Uₙ` where the placement wants it. A Lean inductive's resultant
/// sort is the max over its field levels, so the raise `ctor_spec` now asks
/// for always exists.
///
/// | row | before | after |
/// | --- | ---: | ---: |
/// | `ind-summand(Prod)` | 6 | **0** |
/// | `ind-summand(RBTree)` | 2 | **0** |
/// | `ind-summand(TypeWithTypeFieldPoly)` | 2 | **0** |
/// | `ind-summand(TypeWithTypeField)` | 1 | **0** |
///
/// Five of the eleven derive outright — `042` at both σ, `056`, `057` at both
/// σ. The other six are `Prod`'s, and they move **on**, not away:
/// `proj(Prod)` goes 7 → 12, because a declaration whose carrier now exists at
/// `u := 1, v := 1` reaches its projection for the first time. That is the
/// same reading this ledger has recorded four times: a row that was zero
/// because nothing reached it is not a row that was zero because nothing was
/// owed.
///
/// # The truncation clause closed the `prop-inductive` row, and only one pair
/// of it was actually about truncation
///
/// `zoneb::build_trunc` wires Carneiro's class (P): `⟦T⟧ := ‖ind(p⃗)‖`, the
/// truncation of the ordinary §5.2 carrier over the erased declaration.
/// `TruncCarrier::in_u0` is unconditional — a truncation is a subset of `1`
/// whatever it truncates — so there is no `DeclUniverse`, no summand legs, and
/// no exposure to the field-type raise class (T) spends its rung on.
///
/// | declaration | pairs | before | after |
/// | --- | ---: | --- | --- |
/// | `PredWithTypeField` | 1 | `prop-inductive` | **derived** |
/// | `BoolProp` | 1 | `prop-inductive` | `recursor(BoolProp: …)`, since **derived** |
/// | `Exists` | 2 | `prop-inductive` | `recursor(Exists: …)`, since **derived** |
/// | `PropStructure` | 2 | `prop-inductive` | **`proj(PropStructure)`** |
///
/// **One of the six derived and five moved on**, which is the fifth time this
/// ledger has recorded a row that was zero — or, here, uniform — because
/// nothing had reached past it. `084`/`086` are the sharpest case: their last
/// gap was never the class, it was the `Prop`-structure projection, and they
/// could not say so until the carrier existed. Reading the six as "class (P)
/// work" would have over-counted it by five.
///
/// `072_sortElimProp2Rec` is deliberately **not** in this table: `SortElimProp2`
/// has `ni = 2`, so the indexed guard fires ahead of the trichotomy and it
/// reports `indexed-family`. It is not class-(P) movement and must not be
/// counted as any.
///
/// # `Empty`'s eliminator, and a row that closed without an ι rule
///
/// `derived::inductive::EmptyDecl` and `mini/src/recursor.rs`'s `empty_rec`
/// close `recursor(Empty: no constructors)`, 2 pairs, both σ of
/// `059_emptyRec`. The carrier is `0`, so the major premise's membership is
/// false and `EmptyDecl::anything` types **any** term against the motive;
/// `⟦Empty.rec C t⟧` is `•` because that needs nothing to build, and nothing
/// observes the choice — there are no ι rules for a declaration with no
/// constructors, and no closed term of `⟦Empty⟧` for a use site to reduce
/// against.
///
/// Worth noting against every other recursor row here: this is the only one
/// where the typing is the *whole* obligation. `Bool`, `Prod` and the rest
/// close their typing and then appear again under `iota(·)`.
///
/// # Nine pairs were in the library column and belong in threading
///
/// `Gap::Recursor` mapped unconditionally to `Cause::Library` while
/// `mini/src/recursor.rs`'s own header said in bold that the class-(S) row is
/// *wiring, not library*. The variant now **carries** its cause, because the
/// four recursor routes genuinely differ and only the site that writes the
/// decline knows which it is:
///
/// | row | pairs | was | is |
/// | --- | ---: | --- | --- |
/// | `recursor(And / PUnit / ProjDataIndex: class (S) eliminator)` | 6 | library | **threading** |
/// | `recursor(BoolProp / Exists: … no class-(T) carrier)` | 3 | library | **threading** |
///
/// All nine waited on a `derived/` construction that **exists**:
/// `LePropFields` and `LeProp` for the first six, `TruncRecursor` for the other
/// three. Same shape as the `Quot.sound` mislabel and wrong in the same
/// direction — reporting the project further behind where the library is and
/// further ahead where the threading is, which is the one direction that
/// misallocates people.
///
/// **The first six have since been closed by wiring, which is the check on the
/// correction.** `mini/src/rec_prop.rs` derived all six without touching a
/// `derived/` file, so `threading` is where that work was, and the numbers
/// went 37 / 7 → 28 / 16 on the relabel and 28 / 10 on the landing. A relabel
/// that had been wrong would have shown up here as work leaving a column it
/// had never belonged in.
///
/// **And so have the other three** — `mini/src/rec_trunc.rs`, again without
/// touching a `derived/` file. Both halves of the relabel are now checked the
/// same way, and nine pairs left the library column that had never been in it.
///
/// # The `Prop`-motive indexed eliminator closed, and half of its row was
/// never about it
///
/// `mini/src/rec_ix_prop.rs` wires `INDEXED-DESIGN.md` §5.3 —
/// `IndexedPropRecursor::over_family` at `⟦RBTree.rec.{0,0}⟧ = •` — and the
/// row went to zero. It was **two** pairs and they did two different things:
///
/// | pair | before | after |
/// | --- | --- | --- |
/// | `068_rbTreeRef`, `u := 0` | `recursor(RBTree: … a Prop-valued motive)` | **derived** |
/// | `077_RBTree.id_spec` | `recursor(RBTree: … a Prop-valued motive)` | `recursor(RBTree: … a value-valued motive)` |
///
/// `077` uses `RBTree.rec` at **both** motive sorts — `Sort 0` for the `Eq`
/// proof and `Sort 1` for `RBTree.id` itself — and a pair reports the *first*
/// gap it meets, so with the `Prop` clause missing it could not say that the
/// value clause was also missing. One pair derived; one moved across the axis.
/// That is the sixth time this ledger has recorded a row whose count was not
/// the size of the work behind it, and the first time in the direction that
/// *over*-counts the library rather than hiding it.
///
/// # …and then the value row moved back, because it was misfiled
///
/// Reaching the value clause is what made it readable, which is the same
/// sentence one row along. It was filed **threading** on the strength of
/// `INDEXED-DESIGN.md` §5.2 — "the engine is the existing `GenRecursor` with the
/// indices dead, and the only new thing is a `T`-policy, which is a mini-side
/// recogniser, so `derived/` owes nothing". §5.1 is right about the *term* and
/// the *ι rule* and silent about the recursor constant's **typing**:
/// `GenRecursor` concludes `app(grec,t) ∈ T`, one target *set*, and the
/// obligation is `app(grec,t) ∈ app(C,x⃗,t)`, a *fibre*. No `T` makes those the
/// same statement. `DepRecursor` reaches a fibre but its `DEPᵢ` applies the
/// motive to the **tree alone** (`inductive/motive.rs::dep_minor`), while Lean's
/// indexed minor applies it at the constructor's own indices — so it is not
/// instantiable at any motive that states Lean's premise. What is owed is the
/// value sibling of D7, in `derived/`. `INDEXED-DESIGN.md` §5.1 carries the
/// argument and the statement.
///
/// So the three pairs are **library**, and the two columns settle at
/// `library-gap` 30 → 31 and `threading-incompleteness` 12 → 10 across the two
/// changes together. The `T`-policy recogniser those pairs were sized as does
/// not need to be written at all — the second time a target policy on this
/// project has turned out to be void once the dependent rule existed, the first
/// being `RECURSOR-DESIGN.md` §5.2.
///
/// **Both directions of this correction were found the same way**: by a
/// consumer reaching the row and reading what the premise actually says, not by
/// re-reading the label. A row's *cause* is as much a measurement as its count,
/// and it is wrong until something has stood where it is owed.
///
/// # …and then it closed, and `RBTree` left the ledger
///
/// `derived`'s D8 (`IndexedDepRecursor`) landed and `mini/src/rec_ix_dep.rs`
/// wired it. Three pairs: `068`'s second σ **derives**, which takes that export
/// off the blocked list after five moves; `077`'s two move to
/// `binder-congruence`, 4 → 6.
///
/// | column | Prop half | value half | net |
/// | --- | ---: | ---: | ---: |
/// | `constEv` | 150 → 151 | 151 → **152** | +2 |
/// | `library-gap` | 30 → 28 | 31 → **28** | −2 |
/// | `threading-incompleteness` | 12 → 13 | 10 → **12** | 0 |
///
/// (the middle column starts from the refile, which is why the two halves do
/// not compose arithmetically — see the section above.)
///
/// **The prediction for what was hiding behind it was wrong, and in an
/// instructive direction.** Per the `059` lesson the expectation was
/// `iota(RBTree.rec)`: `RBTree.id_spec` compares `RBTree.id … (red …)` with its
/// reduct, and those are `RBTree` *values*, so `proof_eq` cannot short-circuit
/// them. What actually happens is that the pair never reaches ι — it stops one
/// step earlier, at `binder-congruence`, in the `λ` clause's own typing
/// (`mini/src/kernel.rs:2094`). `⟦RBTree.id⟧` is built; what is missing is
/// `⊢ ⟦val⟧ ∈ ⟦ty⟧`. So the ι row may still be behind *that*, and the honest
/// statement is that nothing has reached it yet — the fifth instance of this
/// document's own rule, arrived at by predicting the wrong row and measuring.
///
/// No new reason appeared: every `waiting:` row is one that already existed.
///
/// # A third instance of evidence produced and then discarded
///
/// `069_boolPropRec` blocked on `no-interp(BoolProp.a)` for as long as that row
/// existed, and nothing was owed for it: `TruncCarrier::over_declaration`
/// *computes* `tc.ctors` — `⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)` per
/// constructor — and `zoneb::build_trunc` ended at `former_at` and dropped
/// them. Same shape as `ctor_ix` minting a constructor abbreviation and letting
/// its defining axiom die with the call, and as `field_sort` before that. The
/// pattern in all three: a value computed at the bottom of a call whose site
/// outlives nothing.
///
/// `zoneb::trunc_constructors` stores them. **`typeEv` 191 → 192 and nothing
/// else moves** — `069`'s *type* mentions `BoolProp.a` and now derives, while
/// the pair itself was already attributed to the recursor row and stays there.
/// That is the whole delta and it is worth stating plainly: the row that was
/// blocking a file was not the row the ledger was counting the file under.
///
/// The scope is one pair and the reason is a short-circuit rather than a
/// backlog: a proof-valued *application* interprets to `•` without consulting
/// its head constant, so only a **bare `Expr::Const`** routes to
/// `zoneb::ensure`, and a class-(P) constructor is unapplied only when it has
/// no parameters and no fields. `BoolProp.a`/`.b` are the only ones the
/// tutorials reach. The same short-circuit is why `084`/`086` closed outright
/// instead of moving to a projection row — `⟦proj x⟧` at a `Prop` is `•` and
/// never needs projection machinery, which `proj(Prod)` at 12 does.
///
/// The general `np`/`kᵢ`/`mᵢ` path is wired and is tested **outside this
/// corpus**, because outside is the only place it is reachable:
/// `mini/tests/designed.rs`'s `prop_recursive_interleaved` fixture inverted
/// from four `no-interp` rows to six derived pairs, and its interleaved mask
/// `Plain Rec Plain Rec Plain` is the only thing anywhere that distinguishes
/// `TruncCtor`'s plains-then-recs atom order from the nest's Lean binder order.
/// `squash_at_nonzero_sigma` inverted too, `constEv` 1 → 2. Both fixtures'
/// headers had predicted their own inversion, which is what a frontier test is
/// for.
///
/// # The class-(P) eliminator: nothing was owed, and nothing could be called
///
/// `recursor(BoolProp / Exists: … no class-(T) carrier)`, 3 pairs, was already
/// recorded above as waiting on `TruncRecursor` — a `derived/` construction
/// that had been **built and tested for a month**
/// (`derived/tests/family_trunc_rec.rs`) and had no consumer. The reason it had
/// no consumer is the fourth instance of this document's own pattern, and the
/// largest: `zoneb::build_trunc` ended at the type former and dropped `ind`,
/// `tc` and both abbreviation families. `TruncRecursor::over_declaration`'s
/// second argument is a `TruncCarrier`, and by the time the eliminator was
/// asked for there was no longer one anywhere — re-deriving mints a second
/// Separation and a second family of symbols, related to the stored type former
/// by nothing.
///
/// `crate::interp::TruncTranslation` stores it and `mini/src/rec_trunc.rs`
/// consumes it. **`constEv` 155 → 158, `threading-incompleteness` 9 → 6, and
/// no successor row at all.**
///
/// | pair | before | after |
/// | --- | --- | --- |
/// | `069_boolPropRec` | `recursor(BoolProp: …)` | **derived** |
/// | `070_existsRec`, both σ | `recursor(Exists: …)` | **derived** |
///
/// The successor being *empty* is worth stating, because the expectation —
/// reasonable, and right five times running — was `iota(BoolProp.rec)` and
/// `iota(Exists.rec)`. Neither exists: both exports are `def f := T.rec`, a
/// bare constant with nothing applied to it, so no use site ever asks for a ι
/// step. **The declaration that η-expands its eliminator is the one that
/// reaches ι**, which is `recursor.rs`'s §5.1 observation read from the other
/// end, and these two do not.
///
/// So this is the first row in this file to close *without* moving anything,
/// and the corpus's whole remaining threading residue is now one shape:
/// `iota(·.rec)` at six declarations.
///
/// # The binder-congruence row closes, and ι doubles
///
/// `mini/src/interp.rs`'s `dprod_fs_bridge` wires
/// `derived::ext::dprod_const_fibre_n` into `BinderShapes::apply`'s two
/// mismatch arms. The library owed nothing: the theorem existed and had no
/// consumer, and the pointwise family the congruence already discharges *is*
/// its hypothesis, because the function-space side's `sym_at` is reflexivity.
///
/// | column | before | after |
/// | --- | ---: | ---: |
/// | `constEv` | 152 | **155** |
/// | `threading-incompleteness` | 12 | **9** |
/// | `waiting:binder-congruence(…)` | 6 | **0** |
/// | `waiting:iota(N.rec)` / `(List.rec)` / `(RBTree.rec)` | — | **1 each** |
///
/// Six pairs, and they split evenly: `N.add`, `myListApped` and `RBTree.id`
/// certify outright, while `nRecReduction`, `listRecReduction` and
/// `RBTree.id_spec` move to **three different** ι rows. So the count moves by
/// three and the *population* of `iota(·.rec)` doubles — six declarations where
/// the census behind the blocker showed three. That is the same lesson as
/// `068`'s five moves, from the other direction: a row measured behind a
/// blocker under-counts what is behind it.
///
/// The reason attribution obeys §0.4 — a gap's reason propagates from the
/// sub-result that caused it. Two rounds of getting that wrong are recorded in
/// `mini/src/ledger.rs`: 104 pairs once filed as `pi-typing-unthreaded` when
/// the cause was an inductive several levels down, and 57 theorems filed as
/// `axiom(…)` because `Gap::Axiom` was the fallback. The second is the sharper
/// mistake — "not derivable in principle" and "not derived yet" are not even on
/// the same axis.
///
/// # The ι row is four keys shorter and it cost no theorem
///
/// `mini/src/iota_dep.rs` wires `derived::inductive::DepRecursor::iota` at a
/// **use site's own** minors, which is the whole of `SCOPING.md` §8's
/// construction 2.
///
/// | column | before | after |
/// | --- | ---: | ---: |
/// | `constEv` | 162 | **166** |
/// | `threading-incompleteness` | 5 | **1** |
/// | `waiting:iota(Bool.rec)` / `(Prod.rec)` / `(N.rec)` / `(List.rec)` | 1 each | **absent** |
/// | `waiting:iota(RBTree.rec)` | 1 | 1 |
///
/// **Four keys, one construction, and `derived/` owed none of it.** The ι
/// theorem had been in `IndApparatus::deprecs` since each eliminator's typing
/// was derived; what was missing was `PRE = COD(C,T) ∧ DEP(C,S⃗)` at terms
/// other than the eliminator nest's binders, and the abbreviation naming
/// `app(drec,⟦t⟧)`. `rec_dep::dep_bottom` derived both and dropped both, which
/// is `MINI-HANDOFF.md` §2's sixth instance; `rec_dep::pre_at` and
/// `crate::interp::DepElim` are the two halves kept.
///
/// **Say which unit.** The row was 5 pairs over 5 keys in 1 family and **2**
/// constructions. Four pairs and four keys closed; the family did not, and the
/// construction count went 2 → 1. A sentence about "the ι row" that does not
/// name its unit would have been wrong here in either direction.
///
/// # `proj(And)` closes, and the `proj` row is four constructions and not three
///
/// `mini/src/proj_prop.rs` gives `Expr::Proj` a typing when the structure is
/// class (S): the projection is a **proof**, so `⟦proj[T,j] x⟧` is `•` and the
/// whole obligation is that `⟦βⱼ⟧` is inhabited — which is
/// `derived::…::LePropFields`, built, tested and *already consumed* by
/// `rec_prop`. A second call site, no theorem, nothing new in `derived/`.
///
/// | column | before | after |
/// | --- | ---: | ---: |
/// | `constEv` | 166 | **168** |
/// | `library-gap` | 28 | **26** |
/// | `waiting:proj(And)` | 2 | **absent** |
/// | `waiting:proj(PProd)` / `(PSigma)` | 4 each | 4 each |
///
/// **The scope said 10 pairs over three declarations and it is 2 over one.**
/// `SCOPING.md` §9 assigns `And`, `PProd.{0,0}` and `PSigma.{0,0}` to one
/// construction on the ground that all three project to `•`. They do — and the
/// `•` is not evidence of the *structure's* class. It comes from the λ clause's
/// proof branch, which fires because the projection's **type** is a `Prop`,
/// and that is true of a `Prop` field in a `Type`-resultant structure too.
/// Measured: this corpus's `PProd` and `PSigma` are `Prop → Prop → Type 0`,
/// land in `IndApparatus::decls` rather than `props`, and have no `A_φ` for
/// `LePropFields` to be about.
///
/// So the row splits by **carrier** class into four, not three: `And` (S, done,
/// 2 pairs); `PProd`/`PSigma` (T with `Prop` fields — `⟦proj⟧` is still `•`,
/// the obligation is still inhabitation, and the premise is plain carrier
/// membership instead of `A_φ`'s — **8 pairs by key and 4 by obligation**, see
/// below); `PropStructure` (P, **1 of 2** — see below); `Prod` and the `{1,1}`
/// half of the other two (T with data fields — the only ones owing a term, 16
/// pairs).
///
/// # The class-(P) half closes, and the corner walk found **two** layers
///
/// `TruncFields` (Isla, `386ca07`) is the class-(S) ladder with the major
/// premise swapped, and `mini/src/proj_prop.rs`'s second branch spends it.
/// `084` (index 0) went through immediately; `086` (index 2, so `P₀ ∧ P₁ ∧ P₂`
/// over a **data** field at index 1) took two more findings, and they were
/// stacked:
///
/// 1. **`Pⱼ = βⱼ ⊆ 1` is strictly weaker than "βⱼ is a `Prop`"**, and the first
///    revision checked only the Lean sort. `PUnit.{1}`'s Lean sort is `Type 0`
///    — but a unit-like declaration never reaches the W-carrier, it reaches
///    `class_s`, and `⊢ ⟦PUnit.{1}⟧ ∈ ⟦Sort 0⟧` was sitting in the store.
///    `proj_prop::field_in_u0` is the second route.
/// 2. **`086` cannot ask `infer_proj` for field 1's type**, because projecting
///    field 1 is illegal — that is what `085_projProp2` is in `bad/` for. The
///    ladder still quantifies `P₁`, so the *type* is needed where the
///    *projection* is refused. `Checker::infer_proj_ty` reads it with the two
///    guards off; the guards themselves stay exactly where they are.
///
/// The instructive part is the order. The corner walk localised layer 1
/// correctly and *only* layer 1 — everything `086` used beyond `P₁` and `P₂`,
/// `084` had already exercised — and layer 2 was invisible until layer 1 was
/// fixed. A note written at that point saying `⟦PUnit.{1}⟧ ⊆ 1` "looks false,
/// because `1` is `{•}` and a W-encoded unit's inhabitant is a pair" was
/// **wrong about the translation**, and one `--dump-only=PUnit` settled it. Two
/// blockers in series look exactly like one blocker plus a bad guess about
/// what is behind it.
///
/// That is the third time a `proj` estimate has moved and the second time the
/// *reason* was a `•` read as a class.
///
/// # The class-(T) half closes at one σ, and the σ question answers "different"
///
/// `DeclFields` (Isla, `57b5dcd`) is the third and smallest member of the same
/// family — the major premise is plain `z ∈ ind(p⃗)`, which is *quantified* over
/// `z`, so this branch needs neither a move onto `•` nor a carrier
/// abbreviation. `proj_prop`'s third branch spends it and routes on `decls`,
/// where the other two route on `props` and `truncs`.
///
/// | column | before | after |
/// | --- | ---: | ---: |
/// | `constEv` | 170 | **174** |
/// | `library-gap` | 24 | **20** |
/// | `waiting:proj(PProd)` / `(PSigma)` | 4 each | **2** each |
///
/// **Four pairs, not eight, and the row is honest at both numbers.** It is 8 by
/// *key* and 4 by *obligation*: `PProd.fst.{0,0}` owes only this certificate,
/// and `PProd.fst.{1,1}` owes a **term** and belongs with `Prod`. The theorem
/// is σ-generic — `Pⱼ = βⱼ ⊆ 1` is a *hypothesis*, so it holds at every σ —
/// and what is σ-specific is whether a consumer can discharge it: at `u = v = 1`
/// the field is data, `⟦α⟧ ∈ U₁` gives no `⟦α⟧ ⊆ 1`, and the projection is not a
/// proof at all. So **this is the first row on the project where the σ question
/// answers "different"**, and the reason is narrow: only a field whose sort is a
/// *bare parameter* can be `Prop` at one σ and data at another. `And.left`
/// (`Sort 0`) and `Prod.fst` (`Sort (u+1)`) both answer "the same".
///
/// The two synthetic witnesses are in `mini/src/proj_prop.rs` and they are the
/// corner walk: one declaration, parameters at `Prop` and at `Type 0`,
/// `a_class_t_structures_prop_fields_are_typed_at_every_field` and
/// `a_data_field_of_a_class_t_structure_is_declined_not_spoken_for`. The first
/// is the flipped frontier test — it asserted the decline until `fd6b16b` — and
/// the second is that frontier moved one cell along.
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
    assert_eq!(g("constEv"), 211, "constant typings derived changed — update the table above");
    assert_eq!(g("typeEv"), 213, "type typings derived changed — update the table above");
    // **The measurement that keeps the type's own typing out of
    // `blocker::Obligation`.** Zero means no pair ever derives
    // `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` while leaving `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` missing, so
    // the two obligations are ordered and stopping on the constant's typing
    // never steps over a hole. A nonzero count would mean the blocker is
    // walking past an underived sub-obligation, and this is where that has to
    // be argued.
    assert_eq!(g("typeEvOnlyGap"), 0, "a constant typing outran its type's own typing");
    // **The masked-reason detector**, and it is not the same measurement as the
    // line above. `typeEvOnlyGap` says nothing was *stepped over*;
    // `typeEvMasked` says a pair's printed reason is about its **value** while
    // its type's own typing is separately missing — so the row underneath the
    // label is a different row.
    //
    // **Pinned at 0, and the one occupant it ever had is closed.** *(This read
    // `1` with the occupant named: `117_accRecType` at `σ = [1,1]`, waiting on
    // `ind-spec(Acc: acc: Acc.intro's step hypothesis is not transported to
    // preds_in)`. `Acc.intro`'s typing was a **prerequisite** for that pair
    // rather than an optional extra — the finding the counter was built for —
    // and building it took `typeEv` 204 → 205 and moved nothing else at all.)*
    //
    // A zero here is the row this file's own `read a zero row twice` rule is
    // about, so it is worth saying which zero it is: **no pair has a masked
    // reason**, measured, not *nothing has reached one*. A change means a new
    // masked row appeared, and the answer is the five-line instrument
    // [`mini::ledger::Ledger::type_ev_masked`]'s own doc records, run in a
    // detached worktree *before* anything is scoped on top of the label.
    assert_eq!(g("typeEvMasked"), 0, "the masked type-typing census changed");

    // `mini-bug` is the one row still pinned at zero as a *deliverable*.
    //
    // **Threading is pinned at 3, and the rows below sum to exactly that**
    // — so the list is not a sample. It was 1 and the whole of it was
    // `iota(RBTree.rec)`, one declaration in `whnf`'s recursor arm; the second
    // row is `recursor(Acc: …)`, and it was **new debt on this axis and not
    // new debt overall**. `Acc`'s three pairs were `fun-typed-rec-arg(Acc)` on
    // the *scope* axis until `Acc` took [`mini::direct`]'s clause: the
    // declaration now translates, so what is left is its eliminator, and
    // `derived::rec_acc` is built. A row moving Scope -> Threading is the
    // intended direction and `interpretation-scope` below dropped by exactly
    // the same three.
    //
    // *(4 → 3 at `mini/src/rec_acc.rs`. The `Acc` row is **two rules**, and
    // only one of them is `derived::rec_acc::pack`: `Acc.rec.{0,u}`'s motive
    // lands in `Prop`, so the eliminator is a proof and `derived::acc::acc_rect`
    // at `φ(z) := • ∈ app(app(⟦C⟧,z),•)` is the whole of it. The pair that left
    // is `117_accRecType` at σ `(0,0)`; the two that remain are the `u₁ ≥ 1`
    // half, and they are pinned under a reason that now says so.)*
    //
    // *(A third row, `iota(Quot.lift)`, existed for one increment: its pair was
    // `quot-classes(Quot.lift, u:1)` on the *scope* axis until the `u ≥ 1`
    // `lift` clause landed, then the computation rule until
    // `mini/src/quot_iota.rs` gave it a route. It is closed, and the arrival
    // and the departure are both the intended direction.)*
    assert_eq!(g("mini-bug"), 0, "a composition that should have fitted did not");
    assert_eq!(g("threading-incompleteness"), 3, "the threading residue changed");
    for (k, v) in [
        // **`Eq.rec` is off the ι row**, and it was never a missing theorem:
        // `thesis.txt:2124` interprets the equality recursor, so `⟦Eq.rec⟧`'s
        // stored nest has the ι right-hand side at its bottom and
        // `Checker::nest_iota`'s β chain is the certificate. Pinned at zero
        // rather than deleted, for the reason every closed row here is.
        ("waiting:iota(Eq.rec)", 0),
        // **The four class-(T) ι rows are off it too, and they went together.**
        // One construction — `mini/src/iota_dep.rs` — over
        // `DepRecursor::iota`, which was stored and unread. `Bool`/`Prod` have
        // `mᵢ = 0` and `N`/`List` do not, so the recursive half of the ι rule
        // and the recursive half of `Hᵢ` are exercised by two of the four; that
        // is the split that made this one construction and not two. Pinned at
        // zero rather than deleted: a reappearance means the wiring stopped
        // reaching a declaration it reaches today, which a total would hide.
        ("waiting:iota(Bool.rec)", 0),
        ("waiting:iota(Prod.rec)", 0),
        ("waiting:iota(N.rec)", 0),
        ("waiting:iota(List.rec)", 0),
        // Construction 3, `SCOPING.md` §8: `IndexedDepRecursor::iota` at a
        // value motive, landed in `derived` at `211c46e` and unread.
        ("waiting:iota(RBTree.rec)", 1),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    // …and *only* ι. Asserted as a shape rather than as a total, because a
    // total cannot tell six-ι-and-nothing-else from three-ι-and-three-of-
    // something-new.
    //
    // **This assertion was rewritten twice in one day and is back where it
    // started, which is the finding.** Between `b7a3aed` and this commit it
    // carried an exemption for
    // `recursor(SortElimProp2: … derived/ owes the indexed TruncRecursor)` — a
    // real row, on the **library** axis, that existed for exactly as long as
    // `072`'s carrier stood in front of a construction `derived/` had not
    // built. `derived` built it (`c0519af`) and `mini/src/rec_trunc_ix.rs`
    // spends it, so the exemption is gone rather than kept at zero: what it
    // guarded was a transient, and a permanent exemption for a transient is how
    // an assertion stops asserting. The *row* is pinned at zero below, by name,
    // which is the durable half.
    //
    // *(Rewritten in place, and **not** as an exemption of the kind the
    // paragraph above disowns. `recursor(Acc: …)` is not a transient standing
    // in front of a `derived/` construction that does not exist —
    // `derived::rec_acc::pack` and `derived::acc::acc_rect` are both built —
    // it is a route with a named occupant, so it is pinned **by name and at a
    // count**, exactly as the six ι rows are, rather than let through by a
    // predicate. A second unnamed recursor row still fails here.)*
    assert_eq!(
        g("waiting:recursor(Acc: acc eliminator: rec_acc::pack is not wired at u:1)"),
        2,
        "the Acc eliminator row changed"
    );
    assert!(
        totals
            .keys()
            .filter(|k| k.starts_with("waiting:"))
            .filter(|k| !k.starts_with("waiting:iota("))
            .filter(|k| !k.contains("recursor(Acc: "))
            .all(|k| !k.contains("recursor(")),
        "a recursor route other than ι and Acc is owed again: {:?}",
        totals.keys().filter(|k| k.contains("recursor(")).collect::<Vec<_>>()
    );
    // **The class-(S) eliminator row is gone, not merely small.** Six pairs
    // over three declarations at two σ each, and the pin is on the *absence* of
    // the key: a reappearance at any count means `rec_prop` stopped reaching a
    // declaration it reaches today, which a threshold on the total would let
    // through.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:recursor(") && k.contains("class (S)")),
        "the class-(S) eliminator stopped reaching a declaration: {:?}",
        totals.keys().filter(|k| k.contains("class (S)")).collect::<Vec<_>>()
    );
    // **Zero, and the axis is the finding.** 6 until `mini::axiom` inhabited
    // `Quot.sound.{0}`; 4 → 2 at function η; 2 → **0** at unit-like η. `ev.rs`
    // files `StructProj | StructEta | UnitLike | FunEta` as `Cause::Library` in
    // one block, and **both of the two that were reachable turned out to be
    // wiring**: `fun-eta` wanted `derived::ext::Eta`, built and unwired, and
    // `unit-like` wanted `LeProp::subsingleton`, built and already carried by
    // every class-(S) translation `mini::class_s` performs. Neither owed
    // `derived/` anything.
    //
    // Pinned at zero rather than deleted, and read the way
    // `MINI-DESIGN.md` §0.5 says: this is *nothing is owed on this axis*,
    // measured, not *nothing has reached it*. The two rows that could reach it
    // did, and both left.
    assert_eq!(g("library-gap"), 0, "the reachable `derived/` backlog changed");
    // **`PProd` is gone from the row at both σ, and `PSigma` is not** — and the
    // one that remains is not a *typing*. `PSigma.snd.{1,1}` has its term and
    // its type; what it lacks is the conversion between the declared codomain
    // `β (PSigma.fst α β self)` and `infer_proj`'s `β (self.PSigma.0)`, which
    // are one type in two spellings. Pinned on `PProd`'s absence and
    // `PSigma`'s count, because the asymmetry is the finding: the two
    // declarations differ only in whether the second field's type mentions the
    // first, so a threshold over both would hide which one is left.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:proj(")),
        "a projection row is owed again: {:?}",
        totals.keys().filter(|k| k.contains("proj(")).collect::<Vec<_>>()
    );
    // **The proj-of-ctor reduction is closed** — `093_projRed`, over
    // `proj_data::iota`, which is `computes` composed with `beta_spine` down
    // `⟦T.mk⟧`'s own nest. Pinned on the key's absence rather than at zero,
    // because a reappearance at any count means `whnf`'s `Expr::Proj` arm
    // stopped reaching a reduction it reaches today.
    assert!(
        !totals.contains_key("waiting:proj(Prod)"),
        "whnf's proj-of-ctor step stopped carrying its certificate"
    );
    // **η moved rather than closed, which `SCOPING.md` §9 predicted and flagged
    // as a prediction.** `105_structEta` now has both projections as terms and
    // stops on `Gap::StructEta`; `DeclProj::eta` is the theorem it wants and it
    // is stored and unread. Pinned at 2 so that spending it is visible here.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:struct-eta(")),
        "structure η is owed again: {:?}",
        totals.keys().filter(|k| k.contains("struct-eta")).collect::<Vec<_>>()
    );
    // 16 until `Acc` took a direct clause; the three `fun-typed-rec-arg(Acc)`
    // pairs left this axis for `threading-incompleteness`, which is pinned
    // three higher above. The two numbers are asserted separately and on
    // purpose: a row that moved axis and a row that closed look identical in
    // either one alone.
    // **13 until the `u ≥ 1` quotient clauses landed.** *(Then 12 at `mk`.)*
    // At `mk`, one pair left this axis and
    // it did *not* close: `123_quotSoundType`'s `Quot.sound` moved off
    // `quot-classes` onto `ind-spec(Eq: …)`, which the ledger scores as a
    // different cause. The one that genuinely closed is `120_quotMkType`'s,
    // and it is visible in `constEv` 197 → 198 rather than here — a row
    // that changed axis and a row that closed still look identical in either
    // number alone, which is what the paragraph above is about.
    assert_eq!(g("interpretation-scope"), 4, "the §9 zone B residue changed");
    // **`Cause::Assumption` is retired, and this is the pin that says so.**
    // Not "is zero" — the row must not be *emitted*, because a cause that can
    // only be reached through a hole in the frontend decline is better spelled
    // as its absence.
    assert!(
        !totals.contains_key("model-assumption"),
        "the model-assumption axis is retired; something reintroduced it"
    );
    // **`axiom(Quot.sound)` is closed, and the absence pin is back — but not
    // the one that was here before.**
    //
    // *(Rewritten twice, and the two revisions are opposite in meaning, which
    // is why the history is kept. Revision 1 asserted no `waiting:axiom(` key
    // at all, and it was a pin against a **misattribution**: `Gap::Axiom` used
    // to answer "why is this typing missing?" for any axiom, unconditionally
    // and ahead of the check on whether the type had interpreted, so `123`'s
    // four pairs carried one obligation on two axes. Revision 2 turned it into
    // a count of 2, because `⟦Quot.{0}⟧` landed and the row came back on the
    // axis where it belonged — the guard working rather than failing.*
    //
    // *This revision is the row **closing**: `mini::axiom` inhabits
    // `Quot.sound.{0}` at the declaration pipeline, the interpretation's third
    // insertion point, and both `u = 0` pairs in `123` derive their constant
    // typing. So the absence is asserted again — and it now says something
    // stronger than revision 1 did, because the misattribution it guarded
    // against is separately pinned by `typeEvOnlyGap = 0` above: no constant's
    // typing outruns its type's, corpus-wide. A `waiting:axiom(` key
    // reappearing today means an axiom this project decided to certify stopped
    // being certifiable, not that a reason was filed on the wrong axis.)*
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:axiom(")),
        "an axiom's inhabitation is owed again: {:?}",
        totals.keys().filter(|k| k.starts_with("waiting:axiom(")).collect::<Vec<_>>()
    );
    // **`no-interp(Quot)` is closed** — `mini/src/quot.rs`'s formation clause.
    // `⟦Quot.{0}⟧ = λA λr. A`, whose bottom is the `α` binder's own scope
    // typing returned unaltered: no theorem, no symbol, nothing owed to
    // `derived/`. Pinned on the key's *absence*, because a reappearance at any
    // count means the clause stopped reaching a declaration it reaches today.
    assert!(
        !totals.contains_key("waiting:no-interp(Quot)"),
        "the Sort 0 formation clause stopped reaching Quot"
    );
    // **`Quot.mk` is closed at `u = 0`**, and it was one export: `120`, the
    // only declaration whose *value* is the bare constant. Everywhere else
    // `Quot.mk α r a` is an application whose type is a `Prop`, so §6.2's
    // application clause gives it `•` and the constant is never consulted.
    assert!(
        !totals.contains_key("waiting:no-interp(Quot.mk)"),
        "the Sort 0 mk clause stopped reaching Quot.mk"
    );
    // **`Quot.ind` is closed at `u = 0`**, and with it `125`'s ι rule: both
    // sides of `ind β h (mk a) ≡ h a` are proofs, which `QUOT-MODEL.md` §2.3's
    // T7 says is uniform in `u` — measured here rather than assumed.
    assert!(
        !totals.contains_key("waiting:no-interp(Quot.ind)"),
        "the Sort 0 ind clause stopped reaching Quot.ind"
    );
    // **All four primitives are interpreted at `u = 0`**, and `124`'s ι rule
    // with them. Pinned as the absence of the whole family's keys rather than
    // four separate zeroes: what would be wrong is any of them reappearing.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:no-interp(Quot")),
        "a Sort 0 quotient clause stopped reaching its primitive: {:?}",
        totals.keys().filter(|k| k.contains("Quot")).collect::<Vec<_>>()
    );
    // **The other half of the row, and the whole reason the key carries `u`.**
    // Every `Quot`-bearing declaration is scheduled at both `u = 0` and
    // `u = 1`, so neither clause alone closes an export. A key without the
    // level would have reported this row as untouched while six of its type
    // interpretations moved.
    //
    // **The key now carries the primitive too, and the argument is the same one
    // measured a second time.** *(This was one assertion, `waiting:quot-classes(u:1)
    // == 7`.)* The `u ≥ 1` half is **four** clauses. Landing the formation
    // clause moved `typeEv` 205 → 207 and left that single row bit-identical at
    // 7 — a quarter-closed row reading as untouched, which is precisely what the
    // level was added to prevent, one level down. Split, it says what is owed:
    //
    // | primitive | pairs | exports |
    // |---|---:|---|
    // | `Quot.mk` | 4 | `120`, `123`×2, `125` |
    // | `Quot.lift` | 2 | `122`, `124` |
    // | `Quot.ind` | 1 | `121` |
    //
    // `125_quotIndReduction` waiting on **`Quot.mk`** rather than on `Quot.ind`
    // is not a mislabel: `Quot.ind`'s own declared type is
    // `∀β, (∀a, β (Quot.mk α r a)) → ∀q, β q`, so a declaration *about* `ind`
    // meets `mk` first. Reading the row as "one `ind` pair and one `lift` pair"
    // would size the wrong clause.
    // *(The counts below read 4 / 2 / 1 when the split was introduced, then
    // 0 / 2 / 2. Landing `mk` took its four to zero, moved
    // `125_quotIndReduction` on to `ind`, and closed `120_quotMkType` outright
    // — the first `Quot` export to derive at **both** σ, which
    // `QUOT-MODEL.md` §5.1 said no single clause could do. Landing `ind` then
    // closed `121` and `125`. `123_quotSoundType`'s two left the family
    // altogether; see below. `lift` is what is left.)*
    for (k, v) in [
        ("waiting:quot-classes(Quot.mk, u:1)", 0),
        ("waiting:quot-classes(Quot.lift, u:1)", 0),
        ("waiting:quot-classes(Quot.ind, u:1)", 0),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    // **The whole family is at zero and so is everything it moved to.** Keeping
    // the two apart is what this file exists for, and the history is the point:
    // `124_quotLiftReduction` moved to `iota(Quot.lift)` on the *threading*
    // axis and `123_quotSoundType`'s two to `ind-spec(Eq: …)` before either
    // closed. Four clauses, one axiom and one computation rule; **all six
    // `Quot` exports now derive at both σ**, which `QUOT-MODEL.md` §5.1 said no
    // single clause could do and which no clause did.
    assert_eq!(g("waiting:iota(Quot.lift)"), 0, "the quotient computation rule changed");
    // **`Quot.sound`'s two pairs are off the quotient family and the label they
    // landed on is about `Eq`.** At `u ≥ 1` its codomain is
    // `Eq (Quot α r) (mk a) (mk b)` with the two sides `class(A,R̄,ā)` and
    // `class(A,R̄,b̄)` — *genuinely different terms*, where at `u = 0` both were
    // `•`. So `crate::axiom`'s route through `direct::eq_refl_bottom` is the
    // wrong rule at this level: what is needed is `derived::quot::q_sound`.
    //
    // Measured, and this is the part that is not obvious: it declines at
    // `direct.rs`'s **`beta_spine`**, *before* reflexivity is tried at all. So
    // the two are **blockers in series** — repairing the spine would then meet
    // the refl comparison and still need `q_sound` — which is the one case
    // `SCOPING.md` §0's corner walk explicitly cannot tell from one blocker
    // plus a bad guess. Pinned by its real key so that a successor sees the
    // count move when either of the two is fixed.
    // *(This was 2. Both pairs closed, and the diagnosis behind the label was
    // **not** the one the label suggested: `direct::eq_refl_bottom` hardcoded
    // `inst: vec![0]`, so at `u = 1` it fetched `⟦Eq.{0}⟧`'s nest and the
    // `beta_spine` could not match a `⟦Sort 1⟧` argument. A hardcoded level,
    // not a spine defect — and behind it, as pinned, a second blocker: the two
    // sides really are different terms and reflexivity really is the wrong
    // rule. Both are fixed; `eq_bottom` takes the level and an optional
    // equation, and `q_sound` supplies the second.)*
    assert_eq!(g("waiting:ind-spec(Eq: type former spine)"), 0, "Quot.sound's u ≥ 1 row changed");
    // The unsplit key must not come back: it is what made the row unmeasurable.
    assert_eq!(g("waiting:quot-classes(u:1)"), 0, "the levelled-but-unsplit key reappeared");

    // **The indexed families, split by *which* construction each waits on.**
    // `indexed-family(X)` used to be one row over three unrelated problems —
    // a class-(S) carrier, a class-(P) truncation, and the eliminator — owed on
    // three different axes by different people. Pinned per declaration *and*
    // per construction, because the whole finding is which.
    for (k, v) in [
        // **The last `indexed-family(·)` row is closed** — `mini/src/class_p_ix.rs`
        // — and pinned at zero rather than deleted, for the reason the two
        // `RBTree` eliminator rows below are. `072`'s pair has moved one step
        // on, to the eliminator, and is the row after this one.
        ("waiting:indexed-family(SortElimProp2: class (P) truncation over an indexed base)", 0),
        // The class-(P) eliminator at an index. It existed as a **library** row
        // for one commit — `b7a3aed`, between the carrier landing and
        // `derived`'s `IndexedTruncRecursor` — and is pinned at zero rather
        // than deleted for the reason the two `RBTree` rows below are: a reason
        // string that comes back is a regression, and a row that silently stops
        // being emitted cannot be told from one that was never measured.
        (
            "waiting:recursor(SortElimProp2: class (P) eliminator at an index: derived/ owes \
             the indexed TruncRecursor)",
            0,
        ),
        // The eliminator, split by §6.2's own clause on the motive's sort: a
        // `Prop`-valued motive makes `⟦T.rec⟧` a proof and owes one `derived/`
        // theorem over `IndexedCtor::inv` (**library**); a value-valued one is
        // owes a dependent rule over the indexed carrier (**library** — see
        // `INDEXED-DESIGN.md` §5.1; it was filed threading and is not).
        // **Both `RBTree` eliminator rows are closed** —
        // `mini/src/rec_ix_prop.rs` and `mini/src/rec_ix_dep.rs` — and pinned
        // at zero rather than deleted, for the reason the dependent-motive rows
        // below are: a reason string that comes back is a regression, and a row
        // that silently stops being emitted cannot be told from one that was
        // never measured. Both strings are gone from mini's vocabulary, which
        // the two `assert!`s after this loop state.
        ("waiting:recursor(RBTree: indexed eliminator: a Prop-valued motive)", 0),
        (
            "waiting:recursor(RBTree: indexed eliminator: a value-valued motive, and no \
             dependent rule over the indexed carrier)",
            0,
        ),
        // Never an indexing problem: a function-typed recursive argument.
        //
        // **`Acc` is off this row and is pinned at zero rather than deleted.**
        // Its three pairs did not close: `Acc` stopped taking the general
        // translation at all, because §6.2 gives it its own interpretation
        // clause (`⟦Acc α r x⟧ = [x̄ ∈ acc(⟦α⟧,R̄)]`) and
        // [`mini::direct::clause_for`] routes it there before the walk that
        // reads the constructor's fields. So `Acc.intro`'s function-typed field
        // is never examined — it is not that it became acceptable — and the
        // three pairs are now `recursor(Acc: …)`, pinned above. A reappearance
        // here would mean the clause stopped being selected.
        ("waiting:fun-typed-rec-arg(Acc)", 0),
        ("waiting:fun-typed-rec-arg(RTree)", 4),
    ] {
        assert_eq!(totals.get(k).copied().unwrap_or(0), v, "{k} changed");
    }
    assert!(
        !totals.keys().any(|k| k.contains("Prop-valued motive")),
        "the Prop-motive indexed eliminator's reason string is gone; nothing may reintroduce it"
    );
    assert!(
        !totals.keys().any(|k| k.contains("value-valued motive")),
        "the value-motive indexed eliminator's reason string is gone too"
    );
    // **`RBTree`'s *translation* is off the ledger entirely.** Carrier,
    // constructors and both eliminators; `068` derives at both σ. A row naming
    // it is a regression, and this is the assertion that says the declaration
    // is done rather than merely quiet.
    //
    // The one exception, and it is not about `RBTree`: `iota(RBTree.rec)` is a
    // `whnf` row, one of six spelled `iota(·.rec)`, and it says the recursor's
    // *reduction* is uncertified — not that anything about the family failed to
    // translate. It became visible only when the binder congruence stopped
    // stopping `077` one step earlier, which is why the pin is written as an
    // exception rather than by weakening the substring.
    assert!(
        !totals.keys().any(|k| k.contains("RBTree") && !k.starts_with("waiting:iota(")),
        "RBTree reappeared on the ledger: {:?}",
        totals
            .keys()
            .filter(|k| k.contains("RBTree") && !k.starts_with("waiting:iota("))
            .collect::<Vec<_>>()
    );
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:indexed-family(Acc")),
        "Acc is blocked by a function-typed recursive argument, not by indexing"
    );
    // **`RBTree` is off the carrier row entirely.** `mini/src/ctor_ix.rs`
    // finished its translation, so a reappearance under any `indexed-family`
    // row means the carrier or a constructor stopped building.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:indexed-family(RBTree")),
        "RBTree's family is translated; it waits on its eliminator only"
    );
    // And the rolled-up spelling is gone rather than merely empty: a bare
    // `indexed-family(X)` with no construction named is the label this split
    // removed, and it must not come back.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:indexed-family(") && !k.contains(':')),
        "an indexed-family row without a named construction reappeared"
    );
    // **The class-(P) row is closed.** `Gap::PropInductive` is no longer
    // reachable: every `Prop`-valued, small-eliminating declaration now gets
    // the truncation carrier, and what remains on those declarations is a
    // recursor or a projection. A reappearance means `build_trunc` declined
    // something it used to reach.
    assert!(
        !totals.keys().any(|k| k.starts_with("waiting:prop-inductive(")),
        "the truncation clause stopped reaching a class-(P) declaration: {:?}",
        totals.keys().filter(|k| k.contains("prop-inductive")).collect::<Vec<_>>()
    );
    // **Both, and getting there took two corrections.** Pinned on the key's
    // *absence*: a reappearance at any count means the class-(P) branch stopped
    // reaching a declaration it reaches today, which a threshold would let
    // through.
    assert!(
        !totals.contains_key("waiting:proj(PropStructure)"),
        "the class-(P) projection branch stopped reaching PropStructure"
    );
    // **The class-(P) *eliminator* row is closed, and this zero is a reachable
    // one.** `BoolProp` and `Exists` are still translated at every σ and still
    // routed to `crate::rec_trunc` — the pin is on a row that something stands
    // in front of, not on one nothing reaches. That distinction is the whole
    // content of §0.5 and it applies to a test's own pins: an absence assertion
    // on a row the walk never gets to would go on passing after it broke.
    //
    // The string is the *class-(T)* route's complaint, and it is asserted gone
    // for these two rather than pinned at zero, because a class-(P) declaration
    // reaching `crate::rec_dep` at all is the bug, not the count.
    assert!(
        !totals.keys().any(|k| {
            k.contains("no class-(T) carrier")
                && (k.contains("BoolProp") || k.contains("Exists"))
        }),
        "a class-(P) declaration is being routed to the class-(T) eliminator: {:?}",
        totals.keys().filter(|k| k.contains("no class-(T) carrier")).collect::<Vec<_>>()
    );
    // Neither class-(P) eliminator declines — `crate::rec_trunc` at `ni = 0`
    // and `crate::rec_trunc_ix` at `ni ≥ 1`. Two routes, two constructions, one
    // assertion, because what would be wrong is the same thing in both cases.
    assert!(
        !totals.keys().any(|k| k.contains("class (P) eliminator")),
        "the class-(P) eliminator declined: {:?}",
        totals.keys().filter(|k| k.contains("class (P) eliminator")).collect::<Vec<_>>()
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
        // Pinned at zero for the same reason the six above are, and the reason
        // is sharper here: the *string* still exists in
        // `mini/src/recursor.rs`'s vocabulary as the prefix of
        // `CLASS_S_EMPTY`, so "the row is not emitted" and "the row is zero"
        // are genuinely different statements and this asserts the second.
        ("waiting:recursor(And: class (S) eliminator)", 0),
        ("waiting:recursor(PUnit: class (S) eliminator)", 0),
        ("waiting:recursor(ProjDataIndex: class (S) eliminator)", 0),
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

/// **The eliminator class, computed against the export's own recursor.**
///
/// Carneiro §2.6.2's judgement decides which of the three clauses a
/// declaration takes, and `mini::zoneb::large_eliminating` **computes** it from
/// the declaration: reason 1 is `provably_nonzero` on the resultant sort,
/// reason 2 is at most one constructor each of whose non-recursive arguments is
/// a proposition or appears among the result indices.
///
/// It used to be read off `T.rec`'s level-parameter count instead. That was
/// wrong twice over: mini **generates** its eliminators and does not consult
/// exported ones anywhere else (`MINI-DESIGN.md` §2), and it made the class
/// depend on whether a recursor happened to be exported — which is not a
/// property of the type. `bad/large-elim-param.ndjson` omits recursors because
/// they are irrelevant to what it tests, and such a declaration is ordinary,
/// not malformed.
///
/// The exported recursor is kept as an **oracle**. Measured 2026-08-02 over
/// **29** declarations with an exported recursor across the 91 files: zero
/// disagreements. The cases that make it worth running:
///
/// * `PUnit` and `PProd` — *identical* recursor signatures, opposite sides of
///   the trichotomy. Both are large-eliminating; `provably_nonzero` on the
///   declaration's own sort is what separates them, and a rule that got the
///   class from the recursor alone could not tell them apart at all.
/// * `Acc` — subsingleton-eliminating only because `intro`'s non-propositional
///   field `x : α` **appears in the result index**. The one declaration here
///   that exercises the `y ∈ e` side condition.
/// * `Eq` — one constructor with no fields, so large-eliminating despite being
///   a `Prop`; the thesis's own worked example.
/// * `Exists`, `PredWithTypeField`, `PropStructure`, `BoolProp`,
///   `SortElimProp2` — the five that come out small.
///
/// A disagreement is a **finding**, not a bug to fix quietly: it would mean
/// either the reading of §2.6.2 or the corpus is wrong, and which one is not
/// obvious in advance.
#[test]
fn tutorial_eliminator_class_matches_the_export_recursor() {
    let files = ndjson_files(&good_dir());
    if files.is_empty() {
        eprintln!("SKIP: {} absent (gitignored corpus)", good_dir().display());
        return
    }
    let mut seen: std::collections::BTreeMap<String, (String, String)> = Default::default();
    let mut disagree = Vec::new();
    for f in &files {
        for line in run(f).stdout.lines().filter(|l| l.starts_with("elim\t")) {
            let c: Vec<&str> = line.split('\t').collect();
            let (name, computed, oracle) = (c[1].to_string(), c[2].to_string(), c[3].to_string());
            if computed.strip_prefix("computed=") != oracle.strip_prefix("oracle=") {
                disagree.push(format!("{}: {name} {computed} {oracle}", stem(f)));
            }
            seen.insert(name, (computed, oracle));
        }
    }
    eprintln!("eliminator class over {} declarations:", seen.len());
    for (n, (a, b)) in &seen {
        eprintln!("  {n:24} {a:16} {b}");
    }
    assert!(
        disagree.is_empty(),
        "the computed §2.6.2 class disagrees with the export recursor — report this before \
         changing either:\n{}",
        disagree.join("\n")
    );
    assert_eq!(seen.len(), 29, "the audited population changed");
    // The boundary case, by name: identical recursor signatures, both large,
    // and the trichotomy splits them on the declaration's own sort instead.
    for n in ["PUnit", "PProd"] {
        assert_eq!(
            seen.get(n).map(|(c, _)| c.as_str()),
            Some("computed=true"),
            "{n} must be large-eliminating"
        );
    }
    // The `y ∈ e` side condition's only witness here.
    assert_eq!(seen.get("Acc").map(|(c, _)| c.as_str()), Some("computed=true"));
    for n in ["Exists", "PredWithTypeField", "PropStructure", "BoolProp", "SortElimProp2"] {
        assert_eq!(
            seen.get(n).map(|(c, _)| c.as_str()),
            Some("computed=false"),
            "{n} must be small-eliminating"
        );
    }
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
/// Measured 2026-08-03: **31** of the 89 checked exports stop, 58 run clean.
///
/// **`068_rbTreeRef` is off this list, and that is the landmark.** It had been
/// the first blocker for the whole life of the ratchet and moved five times
/// without leaving: `no-interp(RBTree.leaf)` → the indexed eliminator declined
/// wholesale → the eliminator split by §6.2's clause on the motive's sort →
/// the `Prop` half closed and it slid to its own second σ → the value half
/// closed and it derives at both. Carrier, constructors and both eliminators;
/// `RBTree`'s translation is off the ledger entirely, which
/// [`tutorial_evidence_ledger`] asserts from the other side. What still names
/// it is `iota(RBTree.rec)`, which is a `whnf` row about the recursor's
/// *reduction* and not about the family.
///
/// Each move was one row of `INDEXED-DESIGN.md`, which is the ordering this
/// ratchet exists to make visible, and three of the five moved the *count* by
/// nothing at all — the file went on blocking at its next obligation. That is
/// the argument for a first-blocker ratchet over a blocked-count one: the count
/// went 35 → 35 → 35 → 35 → 34 while four distinct constructions landed.
///
/// `069_boolPropRec` is off it too, and it moved twice for the *same* reason
/// both times. First `no-interp(BoolProp.a)`, which was not a projection but a
/// nullary constructor whose rule `TruncCarrier::over_declaration` computes and
/// `build_trunc` was throwing away; then
/// `recursor(BoolProp: … no class-(T) carrier)`, which was not a missing
/// eliminator but the *whole class-(P) translation* thrown away by the same
/// call, leaving `TruncRecursor` — built and tested — with an argument that no
/// longer existed. `crate::interp::TruncTranslation` keeps it and
/// `mini/src/rec_trunc.rs` spends it; `070_existsRec` went with it.
///
/// Two moves, one defect, and it is the pattern §2 of `MINI-HANDOFF.md` names:
/// *a value computed at the bottom of a call whose site outlives nothing.* A
/// row of the form "`derived/` owes X" is worth checking against "X exists and
/// its input was discarded" before it is sized.
///
/// `071_sortElimPropRec` is off this list too, and the paragraph here is a
/// **rewrite**: at `0b105f5` it said `071` was the first blocker and that what
/// stopped it was `LeCarrier::build` declining a constructor with plain fields
/// at `ni ≥ 1`. That was measured correctly and diagnosed halfway. It was not a
/// limitation but a **variable capture** in `LeCarrier`'s existential closure,
/// fixed in `derived` at `8d9c94c`; `mini/src/class_s_ix.rs` then built the
/// carrier, the former and the constructor, and `mini/src/rec_s_ix.rs` the
/// eliminator, at **both** σ.
///
/// The eliminator is §5.3's delayed elimination (`thesis.txt:1866–1870`) and
/// the shape of it is worth keeping: the minor is addressed by the
/// constructor's *fields*, the goal by its *index slots*, and applying the
/// minor at the indices the field↔slot map names makes the permutation **cancel
/// against itself**. `SortElimProp.mk`'s two fields go into its two slots
/// swapped, the minor's own motive arguments are swapped back, and the result
/// is the goal — nothing is proved about the eliminated variables.
///
/// `072_sortElimProp2Rec` is off this list too, and this paragraph is a
/// **rewrite**: at `9bb19c9` it named the class-(P) truncation over an indexed
/// base, "which is `TruncCarrier::over_family` and is the last `Scope` row in
/// the ledger". Both halves were right and both have moved. `072` derives at
/// its one σ, and it is the **fifth** `indexed-family(·)` move and the last:
/// the label covered four problems and all four are now closed, so
/// `INDEXED-DESIGN` is done and the ledger is not.
///
/// Four things are worth keeping, because none is what the scope predicted:
///
/// * the §5.2 indexed chain (`Inductive::build` → `IndexedInductive::build`)
///   reads no level anywhere, so running it at a `Prop`-resultant declaration
///   needed no new derivation — only a caller, since `zoneb::build_indexed` is
///   reached solely when the resultant sort is provably nonzero. The carrier
///   was scoped as the unsized risk and it was a composition;
/// * the boundary walk retained across the old decline (`08c91ea`) was the
///   whole input. Nothing was walked twice and no symbol was re-minted;
/// * the **δ-redex** in `sortElimProp2Rec`'s declared minor never reached the
///   eliminator. It is a conversion between the alias's declared type and
///   `SortElimProp2.rec`'s own, discharged by `assert_def_eq`, exactly as
///   `kernel::tests::a_delta_redex_in_an_argument_converts_under_a_binder`
///   measured — no carrier and no wire;
/// * the one real defect the work found is invisible to this corpus. The
///   `∀y⃗` prefix of a transported minor was generalised over a *prefix of the
///   levels*, which is right at both class-(T) routes and at every mask that is
///   plains-then-recs. `072` has `recs = 0` and cannot see it;
///   `crate::class_p_ix::tests::cells`' interleaved `Pe` is the only thing in
///   the repository that can.
///
/// `073_boolRecEqns`, `074_prodRecEqns`, `075_nRecReduction` and
/// `076_listRecReduction` are off this list too, and this paragraph is a
/// **rewrite**: at `7d30266` it said the first blocker was `073` at
/// `iota(Bool.rec)`, that this was "a `whnf` row about a *reduction* and not
/// about any family", and that "six ι rows remain". The first two halves held.
/// The count did not: the six keys were **two** constructions, and one of them
/// closed all four of these exports at once.
///
/// What closed them is `mini/src/iota_dep.rs`, and it is `MINI-HANDOFF.md` §2's
/// sixth instance discharged rather than a derivation:
/// `derived::inductive::DepRecursor::iota` had been in the store since each
/// eliminator's *typing* was derived, and what a use site lacked was `PRE` at
/// its **own** minors — which `rec_dep::dep_bottom` derived at the eliminator
/// nest's binders and dropped — together with the abbreviation naming
/// `app(drec, ⟦t⟧)`, dropped in the same three lines. `derived/` owed this row
/// nothing, and nothing was added to it.
///
/// Three things are worth keeping, because two of them contradict the scope:
///
/// * **the composite is one leg, not one per level.** The route predicted a β
///   chain emitted as one `step!` per argument, which is true of
///   `Checker::nest_iota` and is where the `ConvCompose` trap lives.
///   `Interp::beta_spine` does the `congr` lifting internally and returns the
///   whole spine's equation, so the consumed arguments come off `stack_tms`
///   first and one `step!` carries all of it;
/// * **`rec_dep`'s premise builders needed no variant.** `cx_of`, `minor_at`
///   and `cod_at_rung` are parameterised over terms and memberships, and a nest
///   binder's scope assumption and `⊢ ⟦a⟧ ∈ ⟦declared domain⟧` are the same
///   statement — `Checker::nest_arg_mems` is the twelve lines that produce the
///   second from a Lean argument, and `Cx` did not move;
/// * **`mᵢ > 0` costs one extra step and it is the *same* step.** The Lean
///   right-hand side spells each recursive result `T.rec p⃗ C S⃗ tⱼ`, so
///   `N`/`List` need step 1 again at `tⱼ`, reversed, under `mᵢ` congruences.
///   The `Bool`/`Prod` half of the row could not see it and the four landed
///   together anyway.
///
/// The new first blocker is `077_RBTree.id_spec` at `iota(RBTree.rec)`, which
/// is construction 3 — the same table one row along, over
/// `IndexedDepRecursor::iota` (landed in `derived` at `211c46e`). It is the
/// whole of the threading residue, at **one** row.
const FIRST_BLOCKER: (&str, &str, &str) =
    ("077_RBTree.id_spec.ndjson", "RBTree.id_spec", "iota(RBTree.rec)");

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
    // **5, from 17.** All six `Quot` exports derive at both σ — `120` at `mk`,
    // `121` and `125` at `ind` (the latter including its ι rule, which is
    // `•  ≡ •` at every `u` and needed no separate step), `122` at `lift`,
    // `123` at `q_sound`, `124` at the computation rule — both `Nat` literal
    // exports at `⟦natLit n⟧`, both function-η exports at `Eta::eta`, and both
    // unit-η exports at `LeProp::subsingleton`.
    assert_eq!(blocked, 5, "the number of exports that stop changed");
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
///
/// # `gapped` did not move when the indexed constructors landed, and that is
/// the check
///
/// `mini/src/ctor_ix.rs` added 28 conversions with distinct endpoints (2418 →
/// 2446), 4 of them hypothesis-free — `RBTree`'s three constructors and
/// `Depth.mk`, each reached through `assert_def_eq` at its own index
/// expressions for the first time. **`gapped` stayed at 216 and the five named
/// reasons are unchanged**, which is the assertion: a build that reached the
/// certificate step and could not answer would have shown up here as a sixth
/// reason, and none appeared. The 24 Γ-carrying ones are under the
/// constructor's own field binders, again where §0.3 said they would be.
///
/// # 216 → 988, and the reason table is now **emitted** rather than reproduced
///
/// Both indexed eliminators landing put `⟦RBTree.rec⟧` in the store at both
/// motive sorts, and `077_RBTree.id_spec` — which had contributed no gapped
/// conversion at all, because nothing of it reached the certificate step — now
/// contributes 772. `moved` 2446 → 4430 and the Γ-carrying share rises again,
/// both for the same reason and both where §0.3 said.
///
/// **That movement had no recoverable cause, and now it does.**
/// `Interp::note_conv` counted `Ev::Gap(_)` and discarded the reason, so the
/// table above came from a one-off instrumentation and could not be
/// reproduced — a 772-row movement whose only description was its size. That
/// is worse than the declaration-level version of the same defect, where an
/// unattributed row at least names *a* gap. `ConvStats::gapped_by` records it,
/// keyed by [`Ledger::key`](mini::ledger::Ledger::key) so a conversion-level
/// reason and a declaration-level one that name the same missing theorem
/// compare equal, and the `convs` row carries one `convGap:<key>` column per
/// reason. The assertions below are on the table itself; a sixth reason is now
/// a **test failure** rather than a paragraph nobody can check.
///
/// | reason | 216-era | now | cause |
/// | --- | ---: | ---: | --- |
/// | `binder-congruence` | 165 | **937** | threading |
/// | `iota(Prod.rec)` | 13 | 13 | threading |
/// | `unit-like(PUnit)` | 12 | 12 | library |
/// | `iota(Bool.rec)` | 10 | 10 | threading |
/// | `fun-eta` | 10 | 10 | library |
/// | `iota(Eq.rec)` | 6 | 6 | threading |
///
/// **The whole of the growth is one reason and the other five did not move at
/// all** — which is the check the prose could only assert, and the binder
/// congruence was then, by a wide margin, the largest single uncertified
/// population in the checker.
///
/// The absence of an `iota(RBTree.rec)` row was read here as evidence that the
/// value eliminator's use sites "stop before ι rather than at it". **That
/// reading was wrong and the census that produced it was taken behind a
/// blocker**: `077` stops one step *earlier*, at `binder-congruence`, so ι was
/// never reached to be counted. Discharging the binder row below makes the row
/// appear at 14. A count taken behind a blocker under-counts the population,
/// not merely the demand.
///
/// # …and the 937 are **one** shape, which is not the shape the label named
///
/// `Gap::BinderCongruence` was payload-free, so the largest row in the checker
/// read as one bucket over what
/// [`BinderShapes::apply`](mini::kernel::BinderShapes) treats as five distinct
/// outcomes — `dprod_ext_n`, `cond_ext_n`, `fs_cong`, `lam_ext_n`, and a
/// **non-rule**: the arm where the two sides took *different* §6.2 clauses and
/// nothing relates them. It carries a [`BinderRule`](mini::ev::BinderRule) now.
/// Measured:
///
/// | rule wanted | conversions | declaration pairs |
/// | --- | ---: | ---: |
/// | `clauses differ: dprod vs fs` | **937** | **6** |
/// | `dprod_ext_n` | 0 | 0 |
/// | `cond_ext_n` | 0 | 0 |
/// | `lam_ext_n` | 0 | 0 |
/// | `fs_cong` | 0 | 0 |
///
/// **Every single one is the non-rule, and every single one is the same pair of
/// clauses.** Not three rules at ~300 each; not five outcomes; one shape at
/// 100%. So the row is *not* "the extensionality lemmas are unthreaded" — no
/// conversion in the corpus has ever asked for one of them and failed. It is:
/// one side interpreted its `Π` as a **dependent product** and the other as a
/// **function space**, which is a question about the codomain mentioning the
/// binder — a *classification* disagreement across a conversion, not a missing
/// theorem. Whoever scopes it should start there and not at `dprod_ext_n`.
///
/// That is the fifth time a row's label has named something other than the
/// problem behind it, and the first where the instrument was fixed *before* the
/// scoping rather than after a wrong estimate.
///
/// # 988 → 81: the two clauses were never in conflict, only unbridged
///
/// Both classifications were right. `dep = has_bvar(body, 0)` is a *syntactic*
/// test on a Lean expression and β does not preserve it — `(fun _ => T) x`
/// mentions the binder and `T` does not — so one conversion can hold a
/// dependent product and a function space that are two spellings of one set.
/// Every occurrence in this corpus has one source: a recursor at a constant
/// motive whose body is a non-dependent `Π`. Making the two agree would mean
/// whnf-ing the codomain before classifying, i.e. making `⟦·⟧` a function of a
/// normal form; the repair is a **bridge**, `derived::ext::dprod_const_fibre_n`,
/// wired at [`Interp::dprod_fs_bridge`](mini::interp::Interp).
///
/// | reason | before | after | cause |
/// | --- | ---: | ---: | --- |
/// | `binder-congruence` | 937 | **0** | — |
/// | `iota(RBTree.rec)` | — | **14** | threading |
/// | `iota(Prod.rec)` | 13 | 13 | threading |
/// | `unit-like(PUnit)` | 12 | 12 | library |
/// | `iota(Bool.rec)` | 10 | 10 | threading |
/// | `fun-eta` | 10 | 10 | library |
/// | `iota(N.rec)` | — | **8** | threading |
/// | `iota(List.rec)` | — | **7** | threading |
/// | `iota(Eq.rec)` | 6 | 6 | threading |
/// | `no-endpoint` | — | **1** | — |
///
/// **Three of the four new rows are ι at a recursor that was previously
/// unreachable**, which is the masking above, measured from the other side:
/// `iota(·.rec)` is now six declarations rather than three.
///
/// The `no-endpoint` row is one conversion in `077`, and it is *not* the
/// bridge's: it is `def_eq_struct`'s reflexivity at `mini/src/kernel.rs:2156`
/// with one side's interpretation absent, on a path the walk did not previously
/// reach. It blocks nothing — `077`'s pair stops at `iota(RBTree.rec)` — but it
/// is a row, so it is named rather than folded into a total.
///
/// `moved` 4430 → 8305 and the Γ-carrying share with it, both for the same
/// reason as before: a walk that gets further asks for more conversions under
/// more binders.
///
/// **All five `BinderShapes::apply` arms now fire and all five succeed.** The
/// mirror `Mismatch(fs, dprod)` measured 0 for as long as `(dprod, fs)` was
/// undischarged and appears at 6 sites the moment it is — the same "read a zero
/// row twice" that the four extensionality rows needed, one level down.
///
/// # 81 → 37: the four class-(T) ι rows go **to zero**, not down
///
/// `mini/src/iota_dep.rs` gives `whnf`'s constructor-match branch a
/// certificate, and the interesting thing is the shape of the movement rather
/// than its size:
///
/// | reason | before | after | cause |
/// | --- | ---: | ---: | --- |
/// | `iota(RBTree.rec)` | 14 | 14 | threading |
/// | `iota(Prod.rec)` | 13 | **0** | — |
/// | `unit-like(PUnit)` | 12 | 12 | library |
/// | `iota(Bool.rec)` | 10 | **0** | — |
/// | `fun-eta` | 10 | 10 | library |
/// | `iota(N.rec)` | 8 | **0** | — |
/// | `iota(List.rec)` | 7 | **0** | — |
/// | `no-endpoint` | 1 | 1 | — |
///
/// **All 38 of those conversions are certified, and no partial row is left.**
/// That is the assertion worth having: a wiring that handled the `mᵢ = 0` half
/// would have closed `Bool` and `Prod` and left `N` and `List` at 8 and 7, and
/// a wiring that got the field order wrong would have left a *residue* at each
/// rather than a zero. `iota(RBTree.rec)` holding at exactly 14 is the same
/// check from the other side: construction 3 was not disturbed.
///
/// `moved` 8347 → 8781 and `movedSealed` 1488 → **1476**, the one counter that
/// went down. Measured per export against the previous binary, **the entire
/// delta is these four files and nothing else in the corpus moved at all** —
/// and it does not go one way:
///
/// | export | `proved` | `moved` | `movedSealed` |
/// | --- | ---: | ---: | ---: |
/// | `073` | −3536 | −46 | −60 |
/// | `074` | +3741 | +23 | +1 |
/// | `075` | +2208 | +166 | +47 |
/// | `076` | +10734 | +291 | 0 |
///
/// `073` asks for *fewer* conversions than it did while blocked, which is the
/// opposite of every previous row in this header and is worth not smoothing
/// over: a certified reduction lets the walk finish where it used to keep
/// looking. **Why the hypothesis-free share in particular falls by 60 there is
/// not measured**, and this note says so rather than offering the obvious
/// story; the counter that the pin is actually about, `gapped`, is exact.
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
    // Not zero, and the header says why: named library lemmas, reachable for
    // the first time. A cause appearing here that is not in the table below is
    // a regression this catches, which is what the pin is for.
    //
    // **This total went 37 → 53 when `proj`'s row 4 landed, and going up is the
    // right answer.** Sixteen pairs that used to stop at the *term* now have
    // one and reach conversions nobody had ever run: `proj(Prod)` 7,
    // `proj(PSigma)` 5 and `struct-eta(Prod)` 4 are all newly *reached*, not
    // newly broken. A conversion census counts what the walk got to, so closing
    // a typing row can only grow it — which is why this number is pinned
    // against the reason table below and never read on its own.
    // *(37, then 50 when the `u ≥ 1` `Quot.lift` clause landed — thirteen
    // conversions that had never been reached, reached and stopping at the
    // computation rule — and **back to 37** when `mini/src/quot_iota.rs` gave
    // that rule a route. All thirteen now carry certificates, and `moved` went
    // 8824 → 8835 rather than staying put, because a fired ι moves endpoints
    // where a gapped one does not.)*
    // *(…then 27 when function η landed: its ten conversions all carry
    // certificates, and `moved` went 8835 → 8845 for the reason the ι row gave
    // — a fired rule moves endpoints where a gapped one does not.)*
    // *(…then 15 when unit-like η landed, taking its twelve.)*
    assert_eq!(g("gapped"), 15, "the uncertified-conversion population changed");
    assert_eq!(g("moved"), 8857, "the non-trivial conversion population changed");

    assert!(g("sealed") <= g("proved"));
    // The Γ-carrying ones exist and are not an artefact of nobody looking:
    // `conv::beta_takes_its_premise_from_the_scope_at_zero_cost` exhibits one
    // directly, and this is the corpus-scale count of the same thing.
    assert_eq!(g("moved") - g("movedSealed"), 7362, "the Γ-carrying conversions changed");
    assert_eq!(g("movedSealed"), 1495, "the hypothesis-free count changed");

    // **The reason table, asserted rather than described.** Exhaustive on
    // purpose: the map is compared whole, so a *sixth* reason fails here
    // instead of hiding inside a total that a threshold would wave through.
    // The keys are `Ledger::key`'s, the same strings the evidence ledger's
    // `waiting:` rows use, which is what lets the two censuses be read against
    // each other.
    let reasons: std::collections::BTreeMap<String, u64> = t
        .iter()
        .filter_map(|(k, v)| k.strip_prefix("convGap:").map(|r| (r.to_string(), *v)))
        .collect();
    let expected: std::collections::BTreeMap<String, u64> = [
        // The only ι row left, and it is construction 3 —
        // `IndexedDepRecursor::iota`, the same table one row along. Holding at
        // *exactly* 14 is half the check on `mini/src/iota_dep.rs`: the indexed
        // route was not disturbed, and it declines by name rather than by
        // falling through the class-(T) transport.
        // **The only ι row left, again.** `iota(Quot.lift)` held 13 for one
        // increment and is gone: it appeared *because* a typing row closed and
        // left when `mini/src/quot_iota.rs` gave the rule a route. `RBTree`'s
        // 14 held at exactly 14 across both, which is what says the quotient
        // route did not disturb the indexed one.
        ("iota(RBTree.rec)", 14),
        // *(`fun-eta`'s ten and `unit-like(PUnit)`'s twelve are both gone, and
        // neither was library debt: `Eta::eta` and `LeProp::subsingleton` were
        // both built and unwired. The remaining row is the indexed ι.)*
        // `iota(Eq.rec)`'s **6** conversions are gone, not moved: the equality
        // recursor is interpreted (`thesis.txt:2124`) and its reduction is β
        // down its own stored nest, so those six now carry certificates. The
        // four class-(T) rows — `Prod` 13, `Bool` 10, `N` 8, `List` 7 — went
        // the same way at `mini/src/iota_dep.rs`, and what to read is that each
        // went to **zero**: a transport that got the declared field order or
        // the `mᵢ > 0` half wrong would have left a residue at one of them.
        ("no-endpoint", 1),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect();
    assert_eq!(reasons, expected, "the uncertified-conversion reasons changed");
    // **Every `BinderShapes::apply` outcome is now discharged, and a
    // reappearance at any count is the finding to re-read the header for.**
    // Asserted as an absence per rule rather than as a total, because a total
    // cannot tell 0-and-0 from 600-and-337 — and because the mismatch rows in
    // particular held at zero only while the walk stopped short of them.
    for r in [
        "dprod_ext_n",
        "cond_ext_n",
        "lam_ext_n",
        "fs_cong",
        "clauses differ: dprod vs fs",
        "clauses differ: fs vs dprod",
    ] {
        assert!(
            !reasons.contains_key(&format!("binder-congruence({r})")),
            "a binder congruence is now genuinely wanted ({r}); the row has split"
        );
    }
    assert_eq!(
        reasons.values().sum::<u64>(),
        g("gapped"),
        "a gapped conversion was counted without a reason"
    );
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
