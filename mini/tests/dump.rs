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
/// The reason is matched as the ledger's own key, not as prose: `blocker` and
/// `ledger` already agree on that vocabulary and the dump is the third
/// instrument using it.
///
/// *(Rewritten in place. The prior revision ran on `117_accRecType`, where
/// `Acc` declined `fun-typed-rec-arg(Acc)` at **both** of its instantiations,
/// and it pinned a second property with that: that a decline is reported per σ
/// rather than once per name. `Acc` now takes [`mini::direct`]'s clause and
/// declines at neither σ, and the per-σ half has **no corpus witness left** —
/// `RTree` is the only declaration that still declines and it has no universe
/// parameters, so its decline is one row by construction. That half is
/// therefore not asserted here rather than asserted vacuously; restoring it
/// wants a fixture with a level-parametric declining declaration, and this
/// paragraph is the record that it is owed.)*
#[test]
fn a_declined_declaration_is_shown_with_its_reason() {
    let Some(p) = export("115_rTreeRec.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    let declines: Vec<&str> = out
        .lines()
        .skip_while(|l| !l.contains("── declines"))
        .filter(|l| l.contains("declined:"))
        .collect();
    assert_eq!(declines.len(), 1, "RTree declines and the decline must be a row:\n{out}");
    assert!(
        declines[0].contains("fun-typed-rec-arg(RTree)"),
        "the reason must be the ledger's key: {}",
        declines[0]
    );
    assert!(declines[0].contains("RTree"), "the row must name its subject: {}", declines[0]);
}

/// **"Never reached" is not spelled like "succeeded".**
///
/// Armed, the run stops at the first blocker, so a later scheduled pair has no
/// entry in the store at all. That pair must still appear, and must say that
/// nothing was attempted for it — the distinction §0.5 says costs planning
/// mistakes when a ledger cannot make it. Asserted alongside a pair that *was*
/// stored, because a dump in which every row said "not reached" would pass a
/// one-sided check.
///
/// *(The two-sidedness used to be a header count, `2 pairs / 1 stored`. That
/// counts **every** stored constant, not the scheduled pairs — `Acc` and
/// `Acc.intro` are stored here too since the direct clause landed — so it was
/// measuring the wrong population and would move again for any reason at all.
/// It is now asserted where it belongs: the first pair's own interpretation
/// line.)*
///
/// *(**The export moved, at `a9c49d8`'s predecessor**, and the prior revision
/// read `117_accRecType.ndjson` with `⟦accRecType.{0,0}⟧` as the stored side.
/// `5658439` landed `Acc.rec` at `u₁ = 0`, so `117`'s first pair stopped
/// blocking and its second pair became **reached** — it now carries a stored
/// `⟦c.{σ}⟧` and a named `waiting on …`, which is a different row and the right
/// one. There was no "not reached" left in that file to assert, so the test was
/// red from `5658439` until here; the property is unchanged and only its
/// witness moved. `115_rTreeRec.ndjson` is the witness now: `u_1 := 0` blocks on
/// `fun-typed-rec-arg(RTree)` and `u_1 := 1` is never attempted. **It will flip
/// the day `RTree` builds**, and the successor should move it again rather than
/// weaken it — the property this asserts is about the dump, not about `RTree`,
/// and any export that stops at its first of two pairs will do.)*
#[test]
fn an_unreached_pair_is_named_as_unreached_not_omitted() {
    let Some(p) = export("115_rTreeRec.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--block", "--dump-theorems"]);
    assert!(
        out.contains("⟦rTreeRec.{0}⟧"),
        "the first pair must be stored, or the check below is one-sided:\n{out}"
    );
    assert!(out.contains("not reached"), "the unreached pair must say so:\n{out}");
    // Both pairs are listed even though only one is in the store.
    let rows = out.lines().filter(|l| l.trim_start().starts_with("rTreeRec   σ =")).count();
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

/// **A store that acquires a theorem must stop being printed as an absence.**
///
/// Two rows, one defect, and it is the one this module's header calls property
/// 2 read backwards. A dump that cannot see a store costs a reader a search; a
/// dump that **denies** one costs them a construction, because "not stored"
/// beside a `derived/` module path reads as a library gap.
///
/// * `value-motive ι` said *"not stored — `IndexedDepRecursor` has no `iota`
///   field"*, and that stopped being true at `211c46e`, when `derived` built it
///   beside `typing`. The absence outlived its cause by one landing.
/// * `rec abbrev` is the other direction and the ordinary one: the eliminator
///   nest bottom's defining axiom had no reader at all until
///   `mini/src/iota_dep.rs`, and a `define_abbrev` whose equation is not stored
///   is a symbol no consumer can get inside.
///
/// `077` is the fixture because it has both: an indexed family whose ι rules
/// are built, and a value-motive eliminator whose bottom is named. Asserted as
/// the *presence of a theorem line* rather than the absence of a string, so a
/// future rename of the reason does not quietly satisfy it.
#[test]
fn a_store_that_gained_a_theorem_is_no_longer_printed_as_absent() {
    let Some(p) = export("077_RBTree.id_spec.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems", "--dump-only=RBTree"]);
    let thm = |label: &str| {
        out.lines()
            .filter(|l| l.contains(label))
            .any(|l| l.contains('⊢'))
    };
    for i in 0..3 {
        assert!(
            thm(&format!("value-motive ι {i}")),
            "IndexedDepRecursor::iota[{i}] is built and must be printed as a theorem:\n{out}"
        );
    }
    assert!(
        !out.contains("has no `iota` field") && !out.contains("neither built nor tested"),
        "the dump is still denying a store that exists:\n{out}"
    );
    assert!(
        thm("rec abbrev RBTree.rec"),
        "the value-motive eliminator's nest bottom must have its defining axiom stored:\n{out}"
    );
    assert!(
        out.lines().any(|l| l.contains("rec target RBTree.rec") && l.contains("Sort")),
        "…and the set `T` was instantiated at, which is the rung and not u₁:\n{out}"
    );
}
