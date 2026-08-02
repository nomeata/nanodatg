//! `mini --dump-theorems` — the stored context, and the two properties that
//! make it worth reading.
//!
//! The corpus lives in `vendor/arena-tests`, which is gitignored, so each test
//! skips rather than fails when it is absent — the idiom `tutorial.rs` uses.
//!
//! # What is asserted, and why these and not "the dump is non-empty"
//!
//! * **Determinism**, in two *processes*. Every store behind the dump is a
//!   `HashMap`, and Rust seeds `RandomState` per process, so two runs in one
//!   process share a seed and would pass while the feature was broken. Two
//!   subprocesses is the only test that actually pins the sorting.
//! * **Honest absence**, in both directions: a declaration that **declined**
//!   prints its reason, and a pair the run never reached prints as *not
//!   reached* rather than being silently missing. MINI-DESIGN.md §0.5 — *read a
//!   zero row twice* — is the reason the second one is a test and not a nicety.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf() }

fn export(name: &str) -> Option<PathBuf> {
    let p = repo_root().join("vendor/arena-tests/good/tutorial").join(name);
    p.exists().then_some(p)
}

/// `mini <flags> <export>`, returning stdout. The exit status is not asserted:
/// `--block` exits 3 by design, and this suite is about what was printed.
fn run(path: &Path, flags: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .args(flags)
        .arg(path)
        .output()
        .expect("spawn mini");
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// **Two processes, byte-identical.**
///
/// `042_rbTreeDef` is the fixture because it is the one that fills the most
/// stores: two non-indexed carriers, an indexed family at two σ, and the
/// constructor tables of all three. A dump that iterated any of them in
/// `HashMap` order would differ here and nowhere else.
#[test]
fn the_dump_is_byte_identical_across_two_processes() {
    let Some(p) = export("042_rbTreeDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let a = run(&p, &["--dump-theorems"]);
    let b = run(&p, &["--dump-theorems"]);
    assert!(a.contains("indexed RBTree"), "the fixture must reach zone B:\n{a}");
    if a != b {
        let first = a
            .lines()
            .zip(b.lines())
            .enumerate()
            .find(|(_, (x, y))| x != y)
            .map(|(i, (x, y))| format!("line {i}:\n  run 1: {x}\n  run 2: {y}"))
            .unwrap_or_else(|| "the runs differ in length".to_string());
        panic!("the dump is not deterministic across processes — {first}");
    }
}

/// The same for a **filtered** dump, which takes a different path through the
/// collection and could sort correctly in one and not the other.
#[test]
fn a_filtered_dump_is_deterministic_too() {
    let Some(p) = export("042_rbTreeDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let a = run(&p, &["--dump-only=RBTree"]);
    let b = run(&p, &["--dump-only=RBTree"]);
    assert_eq!(a, b, "a filtered dump must be deterministic too");
    assert!(a.contains("indexed RBTree"), "the filter must keep its subject:\n{a}");
    assert!(!a.contains("inductive Color"), "the filter must drop everything else:\n{a}");
}

/// **A declined declaration is shown, with its reason.**
///
/// `117_accRecType` declines `Acc` at both of its instantiations, so this also
/// pins that a decline is reported *per σ* rather than once per name — the two
/// rows are what distinguish a decline that is about the declaration from one
/// that is about a particular instantiation.
///
/// The reason is matched as the ledger's own key, not as prose: `blocker` and
/// `ledger` already agree on that vocabulary and the dump is the third
/// instrument using it.
#[test]
fn a_declined_declaration_is_shown_with_its_reason() {
    let Some(p) = export("117_accRecType.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    let declines: Vec<&str> = out
        .lines()
        .skip_while(|l| !l.contains("── declines"))
        .filter(|l| l.contains("declined:"))
        .collect();
    assert_eq!(
        declines.len(),
        2,
        "Acc declines at both σ and each must be its own row:\n{out}"
    );
    for l in &declines {
        assert!(l.contains("fun-typed-rec-arg(Acc)"), "the reason must be the ledger's key: {l}");
    }
    assert!(declines[0].contains("[0]") && declines[1].contains("[1]"), "sorted by σ: {declines:?}");
}

/// **"Never reached" is not spelled like "succeeded".**
///
/// Armed, the run stops at the first blocker, so a later scheduled pair has no
/// entry in the store at all. That pair must still appear, and must say that
/// nothing was attempted for it — the distinction §0.5 says costs planning
/// mistakes when a ledger cannot make it. Asserted alongside a pair that *was*
/// stored, because a dump in which every row said "not reached" would pass a
/// one-sided check.
#[test]
fn an_unreached_pair_is_named_as_unreached_not_omitted() {
    let Some(p) = export("117_accRecType.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--block", "--dump-theorems"]);
    assert!(
        out.contains("THEOREMS\t2 pairs\t1 stored"),
        "the fixture must have one stored pair and one unreached:\n{out}"
    );
    assert!(out.contains("not reached"), "the unreached pair must say so:\n{out}");
    // Both pairs are listed even though only one is in the store.
    let rows = out.lines().filter(|l| l.trim_start().starts_with("accRecType   σ =")).count();
    assert_eq!(rows, 2, "every scheduled pair gets a row:\n{out}");
}

/// **No absence is unexplained.**
///
/// Every `(…)` the dump prints in place of a theorem must carry a reason. An
/// empty or bare parenthetical would be the §0.5 defect reintroduced as a
/// formatting bug, which is exactly how it would come back.
#[test]
fn every_absence_carries_a_reason() {
    let Some(p) = export("117_accRecType.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    for l in out.lines() {
        let t = l.trim();
        assert!(!t.ends_with("()"), "an unexplained absence:\n  {l}");
        if let Some(i) = t.find("  (") {
            let reason = &t[i + 3..];
            assert!(
                reason.len() > 12,
                "an absence must say why, not just that it is absent:\n  {l}"
            );
        }
    }
}

/// The dump must not **create** what it reports.
///
/// `Interp::ind_apparatus` builds the apparatus on demand; a dump that reached
/// for it would turn "no declaration reached zone B" into a page of theorems
/// about an apparatus this file never asked for. `001_basicDef` has no
/// inductive at all, so the section must say the apparatus was never built.
#[test]
fn the_dump_does_not_build_the_apparatus_it_reports() {
    let Some(p) = export("001_basicDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    assert!(
        out.contains("not built — no declaration in this file reached zone B"),
        "an apparatus that was never built must be reported as absent, not constructed:\n{out}"
    );
}

/// The statements printed are the **stored** ones.
///
/// `001_basicDef` is `def basicDef : Type := Prop`, so its two theorems are
/// exactly `⊢ ⟦basicDef⟧ ∈ ⟦Sort 1⟧` and `⊢ ⟦basicDef⟧ = ⟦Sort 0⟧`. Pinned
/// because it is the smallest case where a *wrong* dump — one that printed the
/// type it believed rather than the conclusion it holds — would still look
/// plausible.
#[test]
fn a_constants_typing_and_defining_equation_are_the_real_ones() {
    let Some(p) = export("001_basicDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    assert!(out.contains("typing   ⊢ ⟦basicDef.{}⟧ ∈ ⟦Sort 1⟧"), "{out}");
    assert!(out.contains("defeq    ⊢ ⟦basicDef.{}⟧ = ⟦Sort 0⟧"), "{out}");
}
