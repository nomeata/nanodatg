//! **The designed fixtures** — end-to-end exports built to exercise shapes the
//! inherited corpus does not contain.
//!
//! `mini/tests/tutorial.rs` measures the 91 exports of `vendor/arena-tests`,
//! which were co-developed with `lean-mini-kernel` before any of this code
//! existed. Coverage of anything landed since is therefore *whatever those
//! fixtures happen to contain*, and repeatedly this week that has been the
//! wrong thing: the `scope_vars` off-by-one was structurally invisible to
//! `RBTree`, no non-indexed class-(P) declaration in the corpus is recursive,
//! and the `y ∈ e` clause of Carneiro §2.6.2 has exactly one witness in 91
//! files. Nothing is added to the corpus. These are added beside it.
//!
//! # The fixtures, and how to regenerate them
//!
//! `mini/tests/fixtures/<name>.lean` is the source; `<name>.ndjson` is the
//! export, generated from it and checked in beside it. Neither `lean` nor the
//! network is needed to run these tests.
//!
//! ```text
//! scripts/export-fixture.sh                       # all of them
//! scripts/export-fixture.sh rung_ladder.lean      # just this one
//! ```
//!
//! **There is no version skew.** The script pins Lean `v4.29.1` and
//! `lean4export` at `caccfbe`, and the exports it produces carry the *same*
//! meta line as every corpus file, byte for byte:
//!
//! ```text
//! {"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},
//!          "format":{"version":"3.1.0"},
//!          "lean":{"githash":"f72c35b3...","version":"4.29.1"}}}
//! ```
//!
//! `lean4export` has emitted format `3.1.0` continuously from v4.29 to
//! v4.33-rc1 and `checker/src/parser.rs`'s `check_semver` accepts
//! `>= 3.1.0, < 3.2.0`, so a newer toolchain would parse too; the pin holds the
//! content generator fixed, not the parser happy. `scripts/export-fixture.sh`'s
//! header carries the rest, including why every source says `prelude` and why
//! each carries `def`s.
//!
//! # Why every fixture carries `def`s
//!
//! `mini::ledger::run` opens a `(declaration, σ)` pair for every `Axiom` and
//! `Def` and for **no** `Inductive` — a type former, its constructors and its
//! recursor are one `Declaration::Inductive`, and nothing asks them for
//! `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` on their own. An export that declares an inductive and
//! nothing else is accepted with an empty ledger and measures *nothing*. The
//! `def`s are the pairs. [`elim_class_trichotomy_matches_lean`] is the one test
//! here that legitimately runs at zero pairs, because the eliminator class is
//! computed in the pre-pass and reported before any pair is opened.
//!
//! # Some of these tests pin a decline
//!
//! Three of them pin what mini reports *today*, decline and all, with the
//! reason named in the fixture header. That is deliberate and it is not a
//! weakened test: `Acc` was filed under `indexed-family` for the whole project
//! until the week it was found to be a function-typed recursive argument
//! instead, and a wrong label sizes the next piece of work wrongly. A decline
//! that changes should fail here and be re-read, not silently absorbed.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name);
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini --verbose <fixture>`, in a subprocess for the reason
/// `tutorial.rs` gives: `checker`'s parser reports a declined export by calling
/// `std::process::exit(2)`, which an in-process harness cannot contain.
fn run(name: &str) -> String {
    let path = fixture(name);
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--verbose")
        .arg(&path)
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(
        out.status.code(),
        Some(0),
        "{name} must be ACCEPTED — a designed fixture that mini rejects or declines is \
         measuring the frontend, not the clause it was built for:\n{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    stdout
}

/// The `key=value` pairs of one tab-separated row.
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

/// The `evidence` row, which is the one that says what derived and what did
/// not: `pairs`, `constEv`, and a `waiting:<reason>` per attributed gap.
fn evidence(stdout: &str) -> BTreeMap<String, u64> { row(stdout, "evidence") }

/// Every `waiting:` key, with its `waiting:` prefix stripped — the set of
/// reasons a fixture is blocked on, which is what these tests assert *exactly*
/// rather than by count.
fn waiting(stdout: &str) -> BTreeMap<String, u64> {
    evidence(stdout)
        .into_iter()
        .filter_map(|(k, v)| k.strip_prefix("waiting:").map(|s| (s.to_string(), v)))
        .collect()
}

/// `name -> (computed, oracle)` from the `elim` rows.
fn elim(stdout: &str) -> BTreeMap<String, (bool, bool)> {
    let mut m = BTreeMap::new();
    for l in stdout.lines().filter(|l| l.starts_with("elim\t")) {
        let c: Vec<&str> = l.split('\t').collect();
        let g = |s: &str, p: &str| s.strip_prefix(p).map(|v| v == "true").expect("flag");
        m.insert(c[1].to_string(), (g(c[2], "computed="), g(c[3], "oracle=")));
    }
    m
}

/// `T -> (numParams, numIndices)`, read out of the export itself.
///
/// **Lean decides what is indexed, and it is not what the source says.**
/// `fixedIndicesToParams` promotes an index that is the same variable in every
/// constructor result and every recursive occurrence into a parameter, and the
/// promotion is invisible in the `.lean` file — it appears only here. Two of
/// these fixtures depend on a declaration really having the indices its source
/// appears to give it, and both had a draft where it did not, so the fixtures
/// assert it rather than trusting it.
///
/// A deliberately small reader: the export is NDJSON from a *pinned* generator
/// (`scripts/export-fixture.sh`), and the two shapes needed are
/// `{"in":N,"str":{"pre":P,"str":"S"}}` and the `"types":[{…}]` array of an
/// `"inductive"` line, whose keys are emitted in alphabetical order so that
/// `"name"` precedes `"numIndices"` precedes `"numParams"`. Pulling in a JSON
/// parser to read two integers would put a dependency in `mini`'s dev tree for
/// no gain.
fn index_arity(name: &str) -> BTreeMap<String, (u64, u64)> {
    let text = std::fs::read_to_string(fixture(name)).expect("read fixture");
    // Keyed on the explicit `"in"` back-reference, not on insertion order: a
    // `NameNum` node carries no `"str"`, so counting would drift.
    let mut names: BTreeMap<u64, String> = [(0, String::new())].into();
    let mut out = BTreeMap::new();
    let num_after = |s: &str, key: &str| -> Option<u64> {
        let r = &s[s.find(key)? + key.len()..];
        let end = r.find(|c: char| !c.is_ascii_digit()).unwrap_or(r.len());
        r[..end].parse().ok()
    };
    for line in text.lines() {
        if let Some(i) = line.find("\"str\":{\"pre\":") {
            // A `NameStr` node. `pre` is the prefix's own back-reference.
            let (Some(idx), Some(pre)) =
                (num_after(line, "\"in\":"), num_after(&line[i..], "\"pre\":"))
            else {
                continue
            };
            let Some(s) = line[i..].split("\"str\":\"").nth(1).and_then(|r| r.split('"').next())
            else {
                continue
            };
            let full = match names.get(&pre) {
                Some(p) if p.is_empty() => s.to_string(),
                Some(p) => format!("{p}.{s}"),
                None => continue,
            };
            names.insert(idx, full);
            continue
        }
        let Some(t) = line.find("\"types\":[{") else { continue };
        for entry in line[t..].split("{\"all\":").skip(1) {
            let (Some(n), Some(ni), Some(np)) = (
                num_after(entry, "\"name\":"),
                num_after(entry, "\"numIndices\":"),
                num_after(entry, "\"numParams\":"),
            ) else {
                continue
            };
            if let Some(nm) = names.get(&n) {
                out.insert(nm.clone(), (np, ni));
            }
        }
    }
    assert!(!out.is_empty(), "no inductive found in {name}");
    out
}

/// Assert that every pair in the fixture derived: `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` for all
/// of them, and `n` of them, so that a fixture which silently stopped
/// scheduling its use sites fails rather than passing vacuously.
fn all_derived(stdout: &str, n: u64) {
    let e = evidence(stdout);
    let g = |k: &str| e.get(k).copied().unwrap_or(0);
    assert_eq!(g("pairs"), n, "the pair population changed:\n{stdout}");
    assert_eq!(g("constEv"), n, "not every pair derived:\n{stdout}");
    assert!(waiting(stdout).is_empty(), "a gap appeared:\n{stdout}");
}

// ─────────────────────────────────────────────────────── indexed families ──

/// **An indexed family whose index types mention earlier binders derives, at
/// three indices with three different dependencies.**
///
/// `zoneb::spec_of` abstracts index `k`'s interpreted type over
/// `scope_vars(np + k)` and hands it to `derived::define_abbrev`, which refuses
/// a body mentioning a variable it was not given. Every index type in the
/// corpus is closed (`RBTree`: `Color`, `N`) or is a bare parameter (`Acc`:
/// `α`), and `define_abbrev` accepts *any* parameter list for a closed body — so
/// an off-by-one in that abstraction is invisible on 91 files. It was invisible,
/// and `Acc` caught it by luck.
///
/// `indexed_index_type_depends.lean` is three parameters and three indices
/// whose types mention, respectively, parameter 0; parameter 1 **and** index 0;
/// and parameter 2 **and both** earlier indices. No single wrong abstraction is
/// right for all three, and the third is the only place a rule that stops at one
/// earlier index would show — which is why there are three and not two.
///
/// **The first draft of this fixture measured nothing, and the reason is worth
/// keeping.** It indexed the constructor's result at its own field variables,
/// and Lean's `fixedIndicesToParams` promoted the whole telescope: the export
/// said `numParams=5, numIndices=0`, an ordinary non-indexed declaration. The
/// assertion on [`index_arity`] below is there so that can never happen again
/// silently, and it is why these fixtures are generated from `.lean` sources
/// rather than hand-written — a hand-written export claiming `numIndices=3` for
/// that declaration would be a shape Lean does not emit.
///
/// `zoneb::build_indexed` builds the type former and **not** the constructors,
/// so `depthTy` derives and `depthMk` does not. `⟦Depth⟧` existing at all *is*
/// the claim: the walk had to abstract all three index types correctly to
/// produce a `well_formed` `IndexedDeclSpec` and carve the carrier out of the
/// skeleton.
#[test]
fn an_indexed_family_whose_index_types_mention_earlier_binders_derives() {
    // Non-vacuity, and the thing the first draft got wrong: Lean must actually
    // have left three indices on this declaration.
    assert_eq!(
        index_arity("indexed_index_type_depends.ndjson").get("Depth"),
        Some(&(3, 3)),
        "Lean promoted Depth's indices to parameters; the fixture measures nothing"
    );
    let out = run("indexed_index_type_depends.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&2), "the pair population changed:\n{out}");
    // `depthTy`: `⟦Depth⟧` exists, which is the whole claim.
    assert_eq!(e.get("constEv"), Some(&1), "Depth's type former stopped deriving:\n{out}");
    // …and no index-shaped refusal from the walk. These four strings are the
    // ways `spec_of` says it could not express the family, and none may appear.
    let w = waiting(&out);
    for bad in ["index type", "index variables", "indexed spec not well formed", "result index"] {
        assert!(
            !w.keys().any(|k| k.contains(bad)),
            "the walk refused the shape with `{bad}`:\n{out}"
        );
    }
    assert_eq!(
        w,
        [("no-interp(Depth.mk)".to_string(), 1u64)].into(),
        "the indexed frontier moved:\n{out}"
    );
    assert_eq!(e.get("pairs"), Some(&2));
    assert_eq!(elim(&out).get("Depth"), Some(&(true, true)), "Depth must be class (T):\n{out}");
}

/// **Lean decides what is indexed, and the indexed branch builds a carrier and
/// no constructors.** Two measured negatives, and both are the point.
///
/// `indexed_result_index_shape.lean` declares four families that look
/// identically indexed in Lean source and are not:
///
/// | declaration | source says | Lean exports | `⟦T⟧` | `⟦T.ctor⟧` |
/// | --- | --- | --- | --- | --- |
/// | `IxVar` | one index `N` | `np=2, ni=0` — **promoted** | derives | derives |
/// | `IxRec` | one index `N` | `np=2, ni=0` — **promoted** | derives | derives |
/// | `IxConst` | one index `N` | `np=1, ni=1` | derives | `no-interp(IxConst.mk)` |
/// | `IxComputed` | one index `N` | `np=1, ni=1` | derives | `no-interp(IxComputed.mk)` |
///
/// `Lean.Elab.Command`'s `fixedIndicesToParams` promotes an index that is the
/// same variable in every constructor result and every recursive occurrence
/// into a **parameter**, invisibly in the source. So the split above is exactly
/// the promotion and **not** recursion: `IxRec` is recursive at two
/// constructors, one with a recursive field, and both its constructors
/// interpret. Four declarations rather than two, because with one promoted and
/// one indexed example "is it recursion?" and "is it indexing?" are the same
/// hypothesis.
///
/// **A hand-written `.ndjson` asserting `numIndices=1` for `IxVar` would be a
/// shape Lean never emits.** The export would parse, this test would pass, and
/// it would be measuring a declaration that cannot arise. That is the argument
/// for `scripts/export-fixture.sh` in one table, and it is why the arities are
/// asserted here rather than narrated.
///
/// The corpus cannot show any of this: it contains no declaration whose index
/// is a fixed constructor field, so nothing in 91 files is on the promoted side
/// of the line.
///
/// The reason string is pinned as it stands, and it is a poor one:
/// `no-interp(IxConst.mk)` is `zoneb::stored_or_reason_after`'s fallback. The
/// declaration translated and `⟦IxConst⟧` is in the store; the constructor is
/// simply absent, and the label says "absent" rather than "the indexed branch
/// builds no constructors". If it acquires a better name, update this test to
/// it — do not delete the row.
#[test]
fn lean_promotes_fixed_indices_and_the_indexed_branch_builds_no_constructors() {
    // The promotion itself, from the export. Without this the table above is
    // hearsay and the two "derives" rows could be measuring indexed families.
    let a = index_arity("indexed_result_index_shape.ndjson");
    for (n, want) in [("IxVar", (2, 0)), ("IxRec", (2, 0)), ("IxConst", (1, 1)), ("IxComputed", (1, 1))]
    {
        assert_eq!(a.get(n), Some(&want), "{n}'s (numParams, numIndices) changed: {a:?}");
    }
    let out = run("indexed_result_index_shape.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&7), "the pair population changed:\n{out}");
    // Every carrier exists, indexed or not — the split below is about
    // constructors, and a fixture where the *types* stopped interpreting would
    // be measuring something else.
    assert_eq!(e.get("typeEv"), Some(&7), "an indexed carrier stopped deriving:\n{out}");
    assert_eq!(e.get("constEv"), Some(&5), "the derived population changed:\n{out}");
    let w = waiting(&out);
    let expected: BTreeMap<String, u64> = [
        ("no-interp(IxConst.mk)".to_string(), 1),
        ("no-interp(IxComputed.mk)".to_string(), 1),
    ]
    .into();
    assert_eq!(w, expected, "the indexed-constructor frontier moved:\n{out}");
    // Pinned by *name*, because the whole finding is which two: a regression
    // that swapped `IxRec` for `IxVar` would keep every count above.
    for n in ["IxVar", "IxRec"] {
        assert!(!w.keys().any(|k| k.contains(n)), "{n}'s constructors must still derive:\n{out}");
    }
}

// ─────────────────────────────────────────────────────────────── the rungs ──

/// **The summand chain runs at the declaration's own rung, four rungs up and at
/// three field rungs at once.**
///
/// `ctor_spec` used to raise every field type into `U₁`; `5a89420` runs the
/// chain at the declaration's own resultant rung instead. The corpus's four
/// witnesses — `Prod`, `TypeWithTypeField`, `TypeWithTypeFieldPoly`,
/// `RBTree.{1}` — are all exactly **one** rung up and were all found by
/// accident, so a fix that hardcoded the next rung would pass every one of
/// them.
///
/// `rung_ladder.lean` climbs on purpose: `R2` (`Sort 1` fields) is the corpus's
/// case and the control, `R3` is the rung the fix bought, `R4` and `R5` say it
/// is a generalisation rather than an increment, and `Mixed` has **three**
/// fields at three distinct rungs with the declaration's own rung above all of
/// them. Three, because with two "take the max" and "take the last" agree; the
/// fields ascend, so the last field's rung is not the answer either.
///
/// Ten pairs — carrier and constructor for each of the five — all derived.
#[test]
fn the_summand_chain_climbs_four_rungs_and_mixes_three_in_one_declaration() {
    let out = run("rung_ladder.ndjson");
    all_derived(&out, 10);
    // Non-vacuity: all five were walked as class (T). A collapse to some closed
    // form would derive the pairs without touching the summand chain at all.
    let e = elim(&out);
    for n in ["R2", "R3", "R4", "R5", "Mixed"] {
        assert_eq!(e.get(n), Some(&(true, true)), "{n} must be class (T):\n{out}");
    }
}

// ──────────────────────────────────────────────────────────────── class (P) ──

/// **A recursive class-(P) carrier derives, with an interleaved field mask —
/// and its constructors do not, which is where the mask claim actually stops.**
///
/// `derived::inductive::family::trunc_rec`'s `minor_atoms` is positional against
/// the Lean field spine while the carrier's order is plains-then-recs, so the
/// two differ by a permutation exactly when the mask interleaves. **No
/// non-indexed class-(P) declaration in the corpus is recursive**, so that
/// permutation is the identity on every corpus witness and the interleaving has
/// no export exercising it at all.
///
/// `PTree.node` is `Plain Rec Plain Rec Plain` with three *distinct* plain field
/// types — distinct because a permutation of three copies of one type is
/// invisible, which is the mistake three tests on this project already made —
/// and two recursive fields, because with one, several orderings coincide.
///
/// What this reaches:
///
/// * **`⟦PTree⟧` and `⟦PList⟧` derive.** `zoneb::build_trunc` truncates the
///   ordinary §5.2 carrier over the *erased* declaration, and a recursive
///   erased declaration has never been through it. That is real new coverage.
/// * **The four constructors do not.** `build_trunc` stores the carrier and no
///   constructor, so `⟦PTree.leaf⟧` and friends are absent.
///
/// So the interleaved-mask theorem is **not yet reachable end to end**: the
/// recursor sits behind a constructor interpretation that does not exist. This
/// test records that frontier rather than asserting a success the file cannot
/// witness. When the class-(P) constructors are wired the negative rows invert,
/// and this fixture becomes the mask test it was built to be.
#[test]
fn a_recursive_class_p_carrier_derives_and_its_constructors_do_not_yet() {
    let out = run("prop_recursive_interleaved.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&6), "the pair population changed:\n{out}");
    // `ptreeTy`/`plistTy` — the recursive truncation carriers. This is the
    // positive half and it must not be allowed to regress into the negative
    // half unnoticed, which a bare `constEv` count would permit.
    assert_eq!(e.get("constEv"), Some(&2), "the derived population changed:\n{out}");
    let w = waiting(&out);
    let expected: BTreeMap<String, u64> = [
        ("no-interp(PTree.leaf)".to_string(), 1),
        ("no-interp(PTree.node)".to_string(), 1),
        ("no-interp(PList.nil)".to_string(), 1),
        ("no-interp(PList.cons)".to_string(), 1),
    ]
    .into();
    assert_eq!(w, expected, "the class-(P) constructor frontier moved:\n{out}");
    // The carriers themselves: neither may appear as a gap, which is what
    // separates "the constructors are missing" from "the whole clause broke".
    for n in ["PTree", "PList"] {
        assert!(
            !w.contains_key(&format!("ind-spec({n}: spec not well formed)")),
            "{n}'s truncation carrier stopped being built:\n{out}"
        );
    }
    // Both are class (P), not (S): two constructors each, so §2.6.2's reason 2
    // fails on the count. A declaration that classified as (S) would take a
    // different clause and this test would be measuring that instead.
    let el = elim(&out);
    for n in ["PTree", "PList"] {
        assert_eq!(el.get(n), Some(&(false, false)), "{n} must be small-eliminating:\n{out}");
    }
}

// ───────────────────────────────────────── the eliminator class, §2.6.2 ──

/// **Carneiro §2.6.2's reason 2, at six shapes the corpus does not contain, with
/// Lean adjudicating.**
///
/// `zoneb::large_eliminating` computes the class from the declaration.
/// `tutorial_eliminator_class_matches_the_export_recursor` checks that against
/// the exported recursor over 29 corpus declarations with zero disagreements —
/// but the corpus does not contain:
///
/// | declaration | clause | class |
/// | --- | --- | --- |
/// | `Zero` | **zero** constructors: "at most one" holds vacuously | large |
/// | `OneNoField` | one constructor, no fields | large |
/// | `TwoAllProp` | **two** constructors, every field a proposition | small |
/// | `OnePropField` | one constructor, field **is** a proposition | large |
/// | `OneTypeField` | the same with the field's type changed and nothing else | small |
/// | `IdxHit` | a `Type` field **rescued** by the result index | large |
/// | `IdxMiss` | `IdxHit` plus one field of the same type that is not an index | small |
/// | `IdxUnder` | the field occurs *inside* the result index rather than being it | small |
///
/// Three findings sit in that table.
///
/// * **`y ∈ e` had exactly one witness in 91 files — `Acc`.** `IdxHit` is the
///   second, and `IdxMiss` is the first *near*-miss: it differs from `IdxHit` by
///   one extra field of the same type, so a rule that ignored the clause and a
///   rule that applied it vacuously are distinguished. Both index at two
///   positions, the first of them computed, because Lean's
///   `fixedIndicesToParams` promotes a fixed constructor field to a parameter:
///   the draft that wrote `IdxHit (α) : α → Prop | mk : (a : α) → IdxHit α a`
///   exported `numIndices=0` and got both verdicts right without ever reaching
///   the clause. The arities are asserted below for that reason.
/// * **`IdxUnder` settles what "appears among the result indices" means.** Its
///   field occurs inside `Wrap.wrap a` rather than being an index. Lean says
///   small and mini says small, so the clause is *equality with an index*, not
///   occurrence anywhere in one. Neither of those readings was obviously right
///   in advance, and generating the fixture is what settled it.
/// * **`TwoAllProp` is small although every field of both constructors is a
///   proposition**, which is the count failing before the field test is reached.
///
/// Every declaration here is `Prop`-valued, so reason 1 never fires and reason 2
/// is the only thing measured; a file with `Type`-valued rows would pass with
/// reason 2 unimplemented. This is also the one test in this file that runs at
/// **zero pairs**, legitimately: the class is computed in the pre-pass and
/// reported before any pair is opened, so no use site is needed to reach it.
///
/// A disagreement between `computed` and `oracle` is a **finding** — about the
/// reading of §2.6.2 or about Lean — and not a test to relax.
#[test]
fn elim_class_trichotomy_matches_lean() {
    // The `y ∈ e` rows are only about `y ∈ e` if Lean left the indices alone.
    let a = index_arity("elim_class_trichotomy.ndjson");
    for (n, want) in [("IdxHit", (1, 2)), ("IdxMiss", (1, 2)), ("IdxUnder", (1, 1))] {
        assert_eq!(
            a.get(n),
            Some(&want),
            "Lean promoted {n}'s index to a parameter; the `y ∈ e` clause is not reached: {a:?}"
        );
    }
    let out = run("elim_class_trichotomy.ndjson");
    let e = elim(&out);
    let mut disagree = Vec::new();
    for (n, (c, o)) in &e {
        if c != o {
            disagree.push(format!("{n}: computed={c} oracle={o}"));
        }
    }
    assert!(
        disagree.is_empty(),
        "the computed §2.6.2 class disagrees with the export recursor — report this before \
         changing either:\n{}\n{out}",
        disagree.join("\n")
    );
    let expect: &[(&str, bool)] = &[
        // the constructor-count boundary
        ("Zero", true),
        ("OneNoField", true),
        ("TwoAllProp", false),
        // a Prop field against a Type field, everything else equal
        ("OnePropField", true),
        ("OneTypeField", false),
        // `y ∈ e`, hit and missed
        ("IdxHit", true),
        ("IdxMiss", false),
        ("IdxUnder", false),
    ];
    for (n, want) in expect {
        assert_eq!(
            e.get(*n).map(|(c, _)| *c),
            Some(*want),
            "{n} must be {}-eliminating:\n{out}",
            if *want { "large" } else { "small" }
        );
    }
    // Plus `A` and `Wrap`. This count is load-bearing rather than decorative:
    // `zoneb::elim_audit` emits **no row at all** for a declaration with no
    // exported recursor, so a fixture that lost its `--#export …rec` lines
    // would quietly stop being audited and every `false` row above would pass
    // by absence.
    assert_eq!(e.len(), expect.len() + 2, "the audited population changed:\n{out}");
}

/// **`Squash.{u}` at `u := 1`: a class-(P) declaration whose resultant sort is a
/// nonzero numeral, and the branch that is closed for want of exactly this
/// file.**
///
/// # This test pins a decline on purpose
///
/// `zoneb::build_trunc` declines when the ground resultant level is not `0`,
/// with `ind-spec(Squash: class (P) above Prop)`. Tara established that the case
/// is reachable, that deriving it would be sound, and that the fix is one line
/// — and then that **no file in `good/` can exercise it**, because every
/// class-(P) declaration in the corpus has resultant sort literally `Sort 0`.
/// The only witnesses are in `bad/`, which is rejected before any clause runs.
/// This is the `good/` witness, and the expectations below are what mini reports
/// *today*. When the one-line change lands, the `u := 1` rows invert and this
/// fixture proves it.
///
/// # Two things it pins that are not the decline
///
/// * **`Squash` is small-eliminating, and Lean says so.** The prediction was
///   that `Squash` reaches class (P) the subtle way — one constructor, whose
///   field `a : α` fails `is_zero` and is *not* rescued, because the result
///   spine `Squash α` carries the parameter and not the field. That is the same
///   `y ∈ e` clause, from the failing side. The export carries `Squash.rec`, so
///   Lean adjudicates rather than we do, and it agrees.
/// * **Both instantiations are scheduled.** `squashProp` demands `u := 0` and
///   `squashType` demands `u := 1`; mini's σ schedule is the pre-pass's, so
///   without the second use site the fixture would measure the `Sort 0` case
///   twice and say nothing about the branch it exists for. `constEv = 1` — the
///   `u := 0` carrier — against two `class (P) above Prop` gaps is what
///   distinguishes the two σ having been reached from one of them silently
///   going missing.
///
/// The reason-1 half of the σ story is also here: a test that read the
/// **σ-substituted** sort would see `Sort 1`, call `Squash` provably nonzero,
/// and be about to hand a possibly-`Prop` declaration a W-type — which
/// `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3 forbids and which was a real bug when
/// `eliminator_class` was rewritten. Such a mini reports `computed=true` here
/// and disagrees with Lean, which is the first assertion below.
#[test]
fn squash_is_class_p_at_a_nonzero_sigma_and_is_declined_there_today() {
    let out = run("squash_at_nonzero_sigma.ndjson");
    let e = elim(&out);
    // Lean's own verdict, from the exported `Squash.rec`. A `computed=true`
    // here is the σ-substituted-sort bug and nothing else.
    assert_eq!(
        e.get("Squash"),
        Some(&(false, false)),
        "Squash must be small-eliminating, at the declaration and per Lean:\n{out}"
    );
    let ev = evidence(&out);
    assert_eq!(ev.get("pairs"), Some(&4), "the pair population changed:\n{out}");
    // `squashPropTy` — `⟦Squash P0⟧` at `u := 0`, the truncation carrier. The
    // one thing here that derives, and the pin that says `u := 0` still works
    // while `u := 1` does not.
    assert_eq!(ev.get("constEv"), Some(&1), "the derived population changed:\n{out}");
    let w = waiting(&out);
    let expected: BTreeMap<String, u64> = [
        // `u := 1`: `squashTypeTy` and `squashType`. **This is the row that
        // should invert.**
        ("ind-spec(Squash: class (P) above Prop)".to_string(), 2),
        // `u := 0`: the class-(P) constructor wiring, the same absence
        // `a_recursive_class_p_carrier_derives_and_its_constructors_do_not_yet`
        // records. Not the branch this fixture is about.
        ("no-interp(Squash.mk)".to_string(), 1),
    ]
    .into();
    assert_eq!(w, expected, "the Squash frontier moved — re-read the fixture header:\n{out}");
}
