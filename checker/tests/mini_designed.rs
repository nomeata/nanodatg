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
//! `nanoda_lib::mini::ledger::run` opens a `(declaration, σ)` pair for every `Axiom` and
//! `Def` and for **no** `Inductive` — a type former, its constructors and its
//! recursor are one `Declaration::Inductive`, and nothing asks them for
//! `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` on their own. An export that declares an inductive and
//! nothing else is accepted with an empty ledger and measures *nothing*. The
//! `def`s are the pairs. [`elim_class_trichotomy_matches_lean`] is the one test
//! here that legitimately runs at zero pairs, because the eliminator class is
//! computed in the pre-pass and reported before any pair is opened.
//!
//! # Every number here is read from the run that asserts it
//!
//! No count in this file is a constant measured once with one binary and
//! compared against another later: [`run`] spawns `CARGO_BIN_EXE_checker` and the
//! assertions read that run's own `evidence` row. That is deliberate — a
//! `tutorial_evidence_ledger` failure was once a **stale test binary** rather
//! than a divergence, and the tests most likely to hit that trap are the ones
//! that pin fresh measurements. The counts were also cross-checked against a
//! `--release` build of `mini`, which agrees row for row.
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
///
/// **`--acceptance-only`, and the assertion below is why.** The exit status
/// checked here is that the *frontend* took the file, and mini now exits `4`
/// when it accepted a file and left an obligation underived — which several
/// fixtures here deliberately do, since a fixture that owed nothing would be
/// measuring nothing. The flag pins the assertion to the axis it was always
/// about; the certification axis is asserted by every `evidence`-row check in
/// this file, and end to end by
/// [`the_certification_axis_is_in_the_verdict_and_in_the_exit_code`].
fn run(name: &str) -> String {
    let path = fixture(name);
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg("--acceptance-only")
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

/// Every theorem `mini --dump-theorems` reports for `decl`, as
/// `"<label> ⊢ <statement>"` with runs of whitespace collapsed — for instance
/// `"typing ⊢ ⟦R5.{}⟧ ∈ ⟦Sort 5⟧"`.
///
/// # Why a fixture ever needs this instead of a counter
///
/// [`evidence`]'s counters answer *did it derive?*. Some claims are not about
/// whether a derivation exists but about **what it says**, and for those a
/// count is the wrong instrument: it stays green for a wrong answer that still
/// typechecks, so the test occupies the slot of the test that would have caught
/// the regression.
///
/// The rung ladder is where that was expected to bite — see
/// [`the_summand_chain_climbs_four_rungs_and_mixes_three_in_one_declaration`],
/// whose whole claim is *which rung* each carrier lands at. **Measured, it does
/// not:** three rung mutations all move `constEv`, because that clause pins its
/// own rung three separate ways, and its header records which. So the value the
/// helper adds there is legibility and independence from those guards, not
/// coverage the count lacks. Both statements are worth having; only the second
/// was hypothesised, and only the first survived the check.
///
/// The dump prints **real conclusions** — `∀`s are peeled by `mp(ax_inst(…))` —
/// so what is matched here is a derivation and not a rendering of one.
///
/// # Where it does *not* help
///
/// Where the clause already compares its own conclusion against the intended
/// statement, a gap count is a sufficient oracle and this adds rigour rather
/// than reach; `a_recursive_class_p_carrier_and_its_constructors_derive_at_an_interleaved_mask`
/// says so at the one place in this file where it applies. And on a
/// `Prop`-valued declaration every constant is a proof, so every term is `•`
/// and the *term* column carries no information at all — `plistCons` and
/// `ptreeLeaf` both print `= ⟦PTree.leaf⟧`, which is true by proof irrelevance
/// and says nothing. On those, read the `typing` line or nothing.
///
/// Groups are keyed by `(declaration, σ)`; a declaration scheduled at several σ
/// contributes all of its groups, in the dump's own sorted order.
/// `--dump-theorems` over a fixture, as stdout.
///
/// Split out of [`theorem_lines`] because the dump carries two sections that
/// are not theorem lines and that a test may legitimately want: the group
/// headers, which name *which carrier* a `(declaration, σ)` pair got, and the
/// `── untranslated` rows, which name the pairs that got none. A count cannot
/// see either — [`waiting`] says how many pairs are blocked and on what, never
/// at which σ — and "at which σ" is the whole question for a declaration whose
/// instantiations want different carriers.
fn dump(file: &str) -> String {
    let path = fixture(file);
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .arg("--dump-theorems")
        // `--acceptance-only` for [`run`]'s reason: the status asserted below
        // is that the file was taken, and `empty_parameterised` legitimately
        // owes two constant typings.
        .arg("--acceptance-only")
        .arg(&path)
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(out.status.code(), Some(0), "mini did not accept {file}:\n{stdout}");
    stdout
}

/// The dump's `(declaration, σ)` group headers, as the dump spells them —
/// e.g. `inductive PSigma   σ = [0, 1]`, `class-(P) PSigma'   σ = [0, 0]`.
///
/// The leading word is the **carrier class**, which is the thing being read:
/// `inductive` is the general data carrier, `class-(P)` the truncation. Only
/// the `── inductive apparatus` section is scanned, so a constant's own group
/// header — same indentation, no class word — cannot be mistaken for one.
fn apparatus_headers(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .skip_while(|l| !l.contains("── inductive apparatus"))
        .take_while(|l| !l.contains("── untranslated"))
        .filter(|l| l.starts_with("  ") && !l.starts_with("   ") && l.contains("σ = "))
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

/// The dump's `── untranslated` rows — `<decl> σ=<inst>  (<reason>)`, one per
/// `(declaration, σ)` pair that was reached and produced nothing.
fn untranslated_rows(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .skip_while(|l| !l.contains("── untranslated"))
        .filter(|l| l.contains("not translated:"))
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

fn theorem_lines(file: &str, decl: &str) -> Vec<String> {
    let stdout = dump(file);
    let mut lines = Vec::new();
    let mut here = false;
    for l in stdout.lines() {
        // A group header is indented by **exactly** two spaces and reads
        // `<name>   σ = <inst>`; the summary rows above it (`scheduled …`,
        // `filter …`) share the indent but not that shape.
        if l.starts_with("  ") && !l.starts_with("   ") {
            let p: Vec<&str> = l.split_whitespace().collect();
            here = p.len() >= 3 && p[1] == "σ" && p[2] == "=" && p[0] == decl;
            continue
        }
        if here && l.contains(" ⊢ ") {
            lines.push(l.split_whitespace().collect::<Vec<_>>().join(" "));
        }
    }
    assert!(!lines.is_empty(), "no theorem for `{decl}` in {file}:\n{stdout}");
    lines
}

/// `T -> (numParams, numIndices, numConstructors)`, read out of the export
/// itself.
///
/// **Lean decides what is indexed, and it is not what the source says.**
/// `fixedIndicesToParams` promotes an index that is the same variable in every
/// constructor result and every recursive occurrence into a parameter, and the
/// promotion is invisible in the `.lean` file — it appears only here. Two of
/// these fixtures depend on a declaration really having the indices its source
/// appears to give it, and both had a draft where it did not, so the fixtures
/// assert it rather than trusting it.
///
/// The constructor count rides along because it decides the branch as sharply
/// as the arities do: `empty_parameterised.lean` is only about `EmptyDecl` for
/// as long as its declarations have none.
///
/// A deliberately small reader: the export is NDJSON from a *pinned* generator
/// (`scripts/export-fixture.sh`), and the two shapes needed are
/// `{"in":N,"str":{"pre":P,"str":"S"}}` and the `"types":[{…}]` array of an
/// `"inductive"` line, whose keys are emitted in alphabetical order. Pulling in
/// a JSON parser to read three integers would put a dependency in `mini`'s dev
/// tree for no gain.
fn decl_arity(name: &str) -> BTreeMap<String, (u64, u64, u64)> {
    let text = std::fs::read_to_string(fixture(name)).expect("read fixture");
    // Keyed on the explicit `"in"` back-reference, not on insertion order: a
    // `NameNum` node carries no `"str"`, so counting would drift.
    let mut names: BTreeMap<u64, String> = [(0, String::new())].into();
    let mut out: BTreeMap<String, (u64, u64, u64)> = BTreeMap::new();
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
            // `"ctors":[2,3]` — the count, not the names.
            let nc = entry
                .split("\"ctors\":[")
                .nth(1)
                .and_then(|r| r.split(']').next())
                .map(|r| if r.is_empty() { 0 } else { r.split(',').count() as u64 })
                .unwrap_or(0);
            if let Some(nm) = names.get(&n) {
                out.insert(nm.clone(), (np, ni, nc));
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
/// assertion on [`decl_arity`] below is there so that can never happen again
/// silently, and it is why these fixtures are generated from `.lean` sources
/// rather than hand-written — a hand-written export claiming `numIndices=3` for
/// that declaration would be a shape Lean does not emit.
///
/// # Both pairs derive, and the constructor is the one that matters
///
/// `depthTy` was the whole claim while `build_indexed` built the type former
/// and no constructors. `mini/src/ctor_ix.rs` builds them, and **`depthMk`
/// derives too** — which turns this fixture from a test of the index-type
/// *abstraction* into the only test anywhere of the index-type *dependency* at
/// a constructor.
///
/// `IndexedCtor::mem_atoms` states `Eₖ` at `ιₖ(p⃗, e⃗<ₖ)`, at the abbreviation
/// **symbols**, while inference hands back `⟦j⟧ ∈ app(⟦β⟧, ⟦Wrap.wrap a⟧)`, at
/// the **interpretations**. For `RBTree` the two coincide, because `Color` and
/// `N` are closed and `ιₖ` ignores its index arguments; for `Depth` they are
/// three different terms and the composition only goes through if `ιₖ` is
/// instantiated at the interpretations and carried onto the symbols by a
/// congruence along the `e` axioms. `mem_lean`'s header calls this sub-case
/// untested at both ends and says a consumer meeting one owes a **named
/// decline**. It turned out to cost one congruence, which at a closed `ιₖ` is
/// reflexivity — so the general case is written and this fixture is what says
/// it is exercised. Nothing in the corpus does.
#[test]
fn an_indexed_family_whose_index_types_mention_earlier_binders_derives() {
    // Non-vacuity, and the thing the first draft got wrong: Lean must actually
    // have left three indices on this declaration.
    assert_eq!(
        decl_arity("indexed_index_type_depends.ndjson").get("Depth"),
        Some(&(3, 3, 1)),
        "Lean promoted Depth's indices to parameters; the fixture measures nothing"
    );
    let out = run("indexed_index_type_depends.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&2), "the pair population changed:\n{out}");
    // Both: `depthTy` reaches `⟦Depth⟧` and `depthMk` reaches `⟦Depth.mk⟧`.
    // `1` here means the constructor stopped deriving — read the blocked row,
    // and if it is `ctor(Depth.mk: an index type that mentions an earlier
    // index)` then the congruence above has been lost and `RBTree` cannot tell.
    assert_eq!(e.get("constEv"), Some(&2), "Depth's pairs stopped deriving:\n{out}");
    // …and no index-shaped refusal from the walk or from the constructor nest.
    // These strings are the ways `spec_of` and `ctor_ix` say they could not
    // express the family, and none may appear.
    let w = waiting(&out);
    for bad in [
        "index type",
        "index variables",
        "indexed spec not well formed",
        "result index",
        "an earlier index",
    ] {
        assert!(
            !w.keys().any(|k| k.contains(bad)),
            "the shape was refused with `{bad}`:\n{out}"
        );
    }
    assert!(w.is_empty(), "the indexed frontier moved:\n{out}");
    assert_eq!(elim(&out).get("Depth"), Some(&(true, true)), "Depth must be class (T):\n{out}");
}

/// **Lean decides what is indexed, and both sides of the line now build.**
///
/// `indexed_result_index_shape.lean` declares four families that look
/// identically indexed in Lean source and are not:
///
/// | declaration | source says | Lean exports | `⟦T⟧` | `⟦T.ctor⟧` |
/// | --- | --- | --- | --- | --- |
/// | `IxVar` | one index `N` | `np=2, ni=0` — **promoted** | derives | derives |
/// | `IxRec` | one index `N` | `np=2, ni=0` — **promoted** | derives | derives |
/// | `IxConst` | one index `N` | `np=1, ni=1` | derives | **derives** |
/// | `IxComputed` | one index `N` | `np=1, ni=1` | derives | **derives** |
///
/// The last column's bottom half was `no-interp(IxConst.mk)` until
/// `mini/src/ctor_ix.rs` landed, and the *fixture's* finding is unchanged by
/// that: the promotion is still invisible in the source, still exactly what
/// splits the table's two halves, and still asserted from the export. What the
/// two halves no longer differ in is whether the constructor interprets — so
/// the assertion that carries the finding is the arity table above, not the
/// evidence counts, and it is why that table is asserted rather than narrated.
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
/// **The poor reason string is gone, and it was worth naming.**
/// `no-interp(IxConst.mk)` was `zoneb::stored_or_reason_after`'s fallback:
/// "absent", said without saying why, and indistinguishable from a constant no
/// code path ever attempted. This test asked for a better name and got two
/// things instead — the constructors, and `Gap::IndexedCtor`, which carries the
/// reason and its own cause for the cases that still decline. There is no row
/// left here to pin it on; `ctor_ix`'s own
/// `a_declining_constructor_reports_its_reason_not_its_absence` is where the
/// distinction is asserted now.
#[test]
fn lean_promotes_fixed_indices_and_the_indexed_branch_builds_no_constructors() {
    // The promotion itself, from the export. Without this the table above is
    // hearsay and the two "derives" rows could be measuring indexed families.
    let a = decl_arity("indexed_result_index_shape.ndjson");
    for (n, want) in
        [("IxVar", (2, 0, 1)), ("IxRec", (2, 0, 2)), ("IxConst", (1, 1, 1)), ("IxComputed", (1, 1, 1))]
    {
        assert_eq!(a.get(n), Some(&want), "{n}'s (numParams, numIndices, ctors) changed: {a:?}");
    }
    let out = run("indexed_result_index_shape.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&7), "the pair population changed:\n{out}");
    // Every carrier exists, indexed or not — the split below is about
    // constructors, and a fixture where the *types* stopped interpreting would
    // be measuring something else.
    assert_eq!(e.get("typeEv"), Some(&7), "an indexed carrier stopped deriving:\n{out}");
    assert_eq!(e.get("constEv"), Some(&7), "the derived population changed:\n{out}");
    let w = waiting(&out);
    assert!(w.is_empty(), "the indexed-constructor frontier moved:\n{out}");
    // Pinned by *name* as well as by count, because the finding is which
    // declarations are on which side of the promotion: a regression that lost
    // only `IxConst`/`IxComputed` — the two the promotion left indexed — is the
    // one this fixture exists to catch, and `constEv = 5` is what it looks
    // like.
    for n in ["IxVar", "IxRec", "IxConst", "IxComputed"] {
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
/// # This test asserts the rungs, not just that ten pairs derived
///
/// It used to assert only `constEv == 10`: a count standing in for a claim
/// about a value. The claim is *which rung each carrier lands at*; the counter
/// answers *did it derive*.
///
/// **The argument for splitting them was that cumulativity would let a carrier
/// placed a rung too high go on typechecking, so a wrong rung would keep
/// `constEv` at 10 and this test green. That argument is wrong here, and it was
/// checked rather than assumed.** Three mutations — the chain run a rung high,
/// the resultant sort misread upwards, and misread downwards — all reduce
/// `constEv`, so the count caught every one. The rung in this clause is
/// **over-determined**, by three independent guards:
///
/// * `ctor_spec`'s `raise_in_gamma(l, rung)` needs every field level `≤ rung`,
///   so the chain cannot run *below* the tallest field;
/// * `decl_universe` compares `du.universe` against `ip.sort(result_level)` and
///   returns `IndUniverseHeight` otherwise, so it cannot run *above* it either;
/// * `former_at` accepts the bottom only when its conclusion is literally
///   `mem(carrier, ip.sort(n))` at the `n` it was handed.
///
/// A wrong rung is therefore a **decline**, never a wrong-but-accepted answer —
/// the same property that makes a gap count sufficient for the class-(P) mask.
/// So the statements below add **rigour, not reach**, and that is the honest
/// description of them.
///
/// They are kept for two reasons that survive the correction. They make the
/// claim *legible*: a reader now sees the five rungs the number 10 was standing
/// for, and `Mixed`'s three field rungs, without reconstructing them from the
/// fixture. And they do not depend on those three guards, which are
/// implementation and not law — if any is relaxed, the count silently stops
/// being sufficient and these do not.
///
/// The five rungs, as **derived statements**, via [`theorem_lines`]:
///
/// ```text
/// ⊢ ⟦R2.{}⟧ ∈ ⟦Sort 2⟧   ⊢ ⟦R3.{}⟧ ∈ ⟦Sort 3⟧   ⊢ ⟦R4.{}⟧ ∈ ⟦Sort 4⟧
/// ⊢ ⟦R5.{}⟧ ∈ ⟦Sort 5⟧   ⊢ ⟦Mixed.{}⟧ ∈ ⟦Sort 4⟧
/// ```
///
/// and `Mixed`'s **constructor** with them, which is the strongest single
/// statement in this file:
///
/// ```text
/// ⊢ ⟦mixedMk.{}⟧ ∈ fs(⟦Sort 1⟧, fs(⟦Sort 2⟧, fs(⟦Sort 3⟧, ⟦Mixed.{}⟧)))
/// ```
///
/// Three *distinct* field rungs, in declared order, landing in a carrier a rung
/// above all of them. "Take the max", "take the last" and "raise everything
/// into `U₁`" are three different wrong answers and this statement excludes all
/// three at once, which no count can.
///
/// `constEv == 10` is kept as the non-vacuity pin, and on the evidence above it
/// is the load-bearing one: without it a fixture whose use sites stopped being
/// scheduled would satisfy every statement above vacuously, since
/// [`theorem_lines`] reads the store and the store would still hold the
/// carriers.
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
    // **The rungs themselves.** Each carrier's own typing, as the theorem that
    // was actually derived about it.
    for (n, rung) in [("R2", 2), ("R3", 3), ("R4", 4), ("R5", 5), ("Mixed", 4)] {
        let want = format!("typing ⊢ ⟦{n}.{{}}⟧ ∈ ⟦Sort {rung}⟧");
        let got = theorem_lines("rung_ladder.ndjson", n);
        assert!(
            got.contains(&want),
            "{n} was derived, but not at rung {rung}.\n\
             wanted: {want}\n   got: {got:#?}"
        );
    }
    // **The heterogeneous constructor**, which pins the three field rungs *and*
    // their order in one statement.
    //
    // *(Re-spelled at the `fs`-clause removal, `SCOPING.md` §10. `⟦Π⟧` has one
    // value clause now, so a non-dependent arrow is `dprod₀(B, A)` where it was
    // `fs(A, B)` — same arity, arguments swapped, so the nest reads outside-in
    // instead of inside-out. **The assertion's content is unchanged**: three
    // distinct rungs in declared field order, `1`, `2`, `3` reading left to
    // right in the Lean type and now right to left in the term. That the string
    // had to move and the *fact* did not is the check on the change.)*
    let want = "typing ⊢ ⟦mixedMk.{}⟧ ∈ \
                dprod₀(dprod₀(dprod₀(⟦Mixed.{}⟧, ⟦Sort 3⟧), ⟦Sort 2⟧), ⟦Sort 1⟧)";
    let got = theorem_lines("rung_ladder.ndjson", "mixedMk");
    assert!(
        got.contains(&want.to_string()),
        "Mixed's constructor no longer states three distinct field rungs in declared \
         order.\nwanted: {want}\n   got: {got:#?}"
    );
}

// ──────────────────────────────────────────────────────────────── class (P) ──

/// **A recursive class-(P) carrier and its constructors derive, with an
/// interleaved field mask — and this fixture is now the mask test it was built
/// to be.**
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
/// **The frontier this test recorded has moved, and the rows inverted exactly
/// as its previous revision said they would.** `zoneb::trunc_constructors`
/// stores `⟦T.ctorᵢ⟧` from `TruncCtor::mem` / `TruncCtor::trunc_mem`, which
/// `TruncCarrier::over_declaration` had been computing and `build_trunc`
/// discarding. All six pairs derive: two recursive truncation carriers and four
/// constructors.
///
/// **A gap count is a sufficient oracle here, and it is worth saying why so
/// nobody reaches for [`theorem_lines`] reflexively.** `trunc_ctor_bottom` ends
/// by comparing its conclusion against `Formula::mem(point, goal)`, so a wrong
/// mask cannot produce a wrong-but-accepted theorem — it produces a **gap**.
/// The dump could not help in any case: on a `Prop`-valued declaration every
/// constant is a proof, so every term is `•` and `plistCons`, `plistNil`,
/// `ptreeLeaf` and `ptreeNode` all print `defeq ⊢ … = ⟦PTree.leaf⟧` — true by
/// proof irrelevance, and no information whatever.
///
/// **The mask is guarded, and that was checked rather than assumed.** Three
/// mutations in `trunc_ctor_bottom`, each firing **only** this test, and each
/// invisible to the corpus because every corpus class-(P) declaration has
/// `m = 0`:
///
/// * the plains taken as "the first `k` fields" rather than the masked ones —
///   the plains-then-recs versus Lean-binder-order confusion itself;
/// * the antecedent assembled recs-then-plains;
/// * the plain fields threaded in reverse declared order, which is caught
///   **only** because `A`, `B` and `C` are three *distinct* types. Had the
///   plain fields shared a type that permutation would have passed, which is
///   the design decision earning its keep.
///
/// **This fixture is now the only thing testing the mask at all, and that is
/// its whole value.** No non-indexed class-(P) declaration in the corpus is
/// recursive, so on every export `m = 0` and the permutation is the identity.
/// Here it is not: `TruncCtor`'s atoms are plains-then-recs while the nest's
/// binders are in Lean order, so `trunc_ctor_bottom` splits by the mask, and
/// `PTree.node`'s `Plain Rec Plain Rec Plain` with three *distinct* plain types
/// is what makes a wrong split fail rather than pass. It also exercises
/// `trunc_mem`'s recursive hypotheses, which are stated at `•` — the field is a
/// proof — and so cost a `point_of_proof` off the former's own `⊢ ⟦T p⃗⟧ ∈ U₀`
/// that `m = 0` never needs.
#[test]
fn a_recursive_class_p_carrier_and_its_constructors_derive_at_an_interleaved_mask() {
    let out = run("prop_recursive_interleaved.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&6), "the pair population changed:\n{out}");
    // Two carriers and four constructors, all of them. A bare "no gaps" would
    // pass if the pair population shrank, which is why both are pinned.
    assert_eq!(e.get("constEv"), Some(&6), "the derived population changed:\n{out}");
    let w = waiting(&out);
    assert_eq!(w, BTreeMap::new(), "the class-(P) constructor frontier moved:\n{out}");
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
    let a = decl_arity("elim_class_trichotomy.ndjson");
    for (n, want) in [("IdxHit", (1, 2, 1)), ("IdxMiss", (1, 2, 1)), ("IdxUnder", (1, 1, 1))] {
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
    // `squashPropTy` and `squashProp` — `⟦Squash P0⟧` and `⟦Squash.mk⟧` at
    // `u := 0`. The pin that says `u := 0` works while `u := 1` does not; it
    // went 1 → 2 when `zoneb::trunc_constructors` landed, which is the
    // *other* row this header called an absence rather than a branch.
    assert_eq!(ev.get("constEv"), Some(&2), "the derived population changed:\n{out}");
    let w = waiting(&out);
    let expected: BTreeMap<String, u64> = [
        // `u := 1`: `squashTypeTy` and `squashType`. **This is the row that
        // should invert**, and it has not — it is the branch this fixture is
        // about and it is still owed (`TruncCarrier::in_un`).
        ("ind-spec(Squash: class (P) above Prop)".to_string(), 2),
    ]
    .into();
    assert_eq!(w, expected, "the Squash frontier moved — re-read the fixture header:\n{out}");
}

/// **`PSigma'` and `PSigma` at mixed σ — `(0,1)` and `(1,0)`, the
/// instantiations of a basis member that nothing had ever run.**
///
/// `MODEL-BASIS.md` §8.6 lists "whether `PSigma'` translates at mixed universes
/// `(0,1)` and `(1,0)`" as not established. It was not established because it
/// was not *reachable*: `instantiations::DEFAULT_LEVELS` seeds a defaulted
/// declaration at `vec![l; nparams]`, which is uniform by construction, so a
/// mixed σ appears only where some declaration demands one — and nothing in
/// `vendor/arena-tests` or in this directory did. **Skip is not pass.** The
/// eight `def`s in `psigma_mixed_sigma.lean` demand all four σ of both types by
/// name, so neither type is defaulted at all and the fixture measures the same
/// eight pairs whatever `DEFAULT_LEVELS` becomes.
///
/// # What it measures, and why the second declaration is the instrument
///
/// `PSigma'` (`Sort (max u v)`) and `PSigma` (`Sort (max 1 u v)`) are **the same
/// instantiated declaration at both mixed σ**: `max 0 1`, `max 1 0`,
/// `max 1 0 1` and `max 1 1 0` are all `1`. Same parameters, same constructor,
/// same fields, same ground resultant sort. The only difference is one Lean
/// cannot see through σ and the checker decides on before σ exists —
/// `zoneb::large_eliminating` reads the **declaration's own** level expression
/// (`zoneb.rs:1149`), where `max u v` is not `provably_nonzero` and `max 1 u v`
/// is.
///
/// So `PSigma` is not a second subject, it is the **control**: it puts the
/// general data carrier over one `Prop` component and one data component at
/// rung 1 — the carrier a per-σ basis clause for `PSigma'` would have to reach
/// — and measures it on the identical instantiated shape rather than on an
/// analogy. It derives at all four σ, mixed included, and that is the finding:
/// the mixed instantiations owe **no new `derived/` construction**.
/// `Cumul::lift(0,n)` (`derived/src/tower/cumulative.rs:180`), which
/// `MODEL-BASIS.md` §8.6 predicted this case would spend, is already built,
/// already public through `Interp::raise_in_gamma`, and already in the path at
/// `zoneb.rs:2953`.
///
/// # This test pins a decline, and pins that it is not a new one
///
/// `PSigma'` derives at `(0,0)` and declines at the other **three** σ with one
/// reason, `ind-spec(PSigma': class (P) above Prop)` — `build_trunc` refusing a
/// nonzero ground resultant level, the same site `Squash.{1}` reaches above.
/// Mixed σ is therefore *not* a second, harder gap beside `(1,1)`: one
/// classification decision covers all three, and closing it closes all three.
/// That is the load-bearing negative result, and it is why the expectations
/// below are the current behaviour, decline and all.
///
/// **The class must not be "fixed" by reading σ.** A `large_eliminating` that
/// read the substituted sort would see `Sort 1` at three of `PSigma'`'s four σ,
/// call it provably nonzero, and hand a possibly-`Prop` declaration a W-type —
/// `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3, pinned by
/// `zoneb::tests::a_possibly_prop_declaration_never_acquires_a_w_type`. Such a
/// checker reports `computed=true` for `PSigma'` here and disagrees with Lean's
/// own exported recursor, which is the first assertion below.
///
/// # Why the rows and not the counts
///
/// `constEv = 5` against `waiting = 3` splits the eight `def`s, and it is a
/// real oracle — `tight01` and `tight10` are on the blocked side while
/// `wide01` and `wide10` are on the derived side, which no count of a single
/// declaration could say. But it cannot tell `(0,1)` from `(1,0)`, and those
/// are **not interchangeable**: at `(0,1)` the first component is the
/// proposition and the fibre is data, at `(1,0)` it is the other way round. A
/// checker that sorted, `max`-ed or otherwise normalised σ would collapse the
/// two into one pair and every count here would stay green. The two `σ=[0, 1]`
/// / `σ=[1, 0]` rows and the two `σ = [0, 1]` / `σ = [1, 0]` headers are what
/// refuses that, and they are asserted as *exact sets* so a fifth carrier or a
/// fourth decline cannot appear quietly.
///
/// The headers also carry the answer to "which carrier does each mixed σ get?"
/// in the dump's own vocabulary — `inductive` is the general data carrier,
/// `class-(P)` the truncation — so the day a basis clause gives `PSigma'` the
/// per-σ licence, the two mixed rows move from the untranslated list to
/// `inductive PSigma' σ = [0, 1]` / `σ = [1, 0]` and this test is what shows
/// they landed on the carrier the control already validates.
///
/// # Falsifiers (`TEST-INVENTORY.md` §6)
///
/// Four mutants of `psigma_mixed_sigma.lean`, each re-exported through
/// `scripts/export-fixture.sh` and run against this test. Each died at its own
/// assertion and at no earlier one — measured, not predicted:
///
/// | mutation | died at |
/// | --- | --- |
/// | `tight01`/`tight10` rewritten to demand `PSigma'.{1,1}` — the mixed σ stop being demanded, `pairs`, `constEv`, `waiting` and the headers **all stay put** | `untranslated_rows`: one row where three were wanted |
/// | `wide01`/`wide10` rewritten to demand `PSigma.{1,1}` — same, on the control | `apparatus_headers`: three headers where five were wanted |
/// | `PSigma` declared `Sort (max u v)` instead of `Sort (max 1 u v)`, i.e. made into a second `PSigma'` | the `PSigma` `elim` assertion: `(false, false)` where `(true, true)` was wanted |
/// | `tight00` rewritten to demand `PSigma'.{1,1}` — the one green tight σ taken away | `constEv`: 4 where 5 was wanted |
///
/// The first is the one worth reading twice: it is the **"skip is not pass"**
/// mutation, it is what this fixture exists to refuse, and every counter in the
/// test survives it. Without the row assertions the fixture could stop
/// exercising mixed σ entirely and stay green.
///
/// Two assertions are **not** independently falsified here and say so rather
/// than being claimed:
///
/// * **`PSigma'`'s `elim` row.** The mutation that trips it is
///   `zoneb::large_eliminating` reading the σ-substituted sort, and that file
///   belongs to another seat. It is the same mutation
///   [`squash_is_class_p_at_a_nonzero_sigma_and_is_declined_there_today`] pins
///   with the same instrument, and `zoneb::tests::
///   a_possibly_prop_declaration_never_acquires_a_w_type` pins directly.
/// * **`waiting`'s count.** Over this fixture's fixed eight pairs `5 + 3 = 8`,
///   so `constEv` and `waiting` are co-determined and every mutation found here
///   moves both — `constEv` is asserted first and shadows it (§6.1 gate 1).
///   What `waiting` adds that `constEv` cannot is the **reason key**: that all
///   three declines are `ind-spec(PSigma': class (P) above Prop)` and nothing
///   else, so a decline arriving from a different site would trip it with the
///   counts unchanged. That mutation is also `zoneb.rs`'s.
#[test]
fn psigma_at_mixed_sigma_declines_only_where_the_declared_sort_may_be_prop() {
    let out = run("psigma_mixed_sigma.ndjson");
    let e = elim(&out);
    // Lean's own verdict, from the two exported recursors. `PSigma'`'s
    // `computed=true` would be the σ-substituted-sort bug and nothing else;
    // `PSigma`'s `computed=false` would be the mirror mistake, a `max 1 …`
    // read as possibly zero.
    assert_eq!(
        e.get("PSigma'"),
        Some(&(false, false)),
        "PSigma' must be small-eliminating, at the declaration and per Lean:\n{out}"
    );
    assert_eq!(
        e.get("PSigma"),
        Some(&(true, true)),
        "PSigma must be large-eliminating, at the declaration and per Lean:\n{out}"
    );

    let ev = evidence(&out);
    assert_eq!(ev.get("pairs"), Some(&8), "the pair population changed:\n{out}");
    // The five that derive: `tight00`, and all four `wide*` — including both
    // mixed ones, which is the positive half of the finding.
    assert_eq!(ev.get("constEv"), Some(&5), "the derived population changed:\n{out}");
    let expected: BTreeMap<String, u64> =
        [("ind-spec(PSigma': class (P) above Prop)".to_string(), 3)].into();
    assert_eq!(
        waiting(&out),
        expected,
        "the PSigma' frontier moved — re-read the fixture header:\n{out}"
    );

    // Which carrier each (declaration, σ) pair got, per σ and in the dump's own
    // words. Five and exactly five.
    let d = dump("psigma_mixed_sigma.ndjson");
    assert_eq!(
        apparatus_headers(&d),
        vec![
            "inductive PSigma σ = [0, 0]",
            "inductive PSigma σ = [0, 1]",
            "inductive PSigma σ = [1, 0]",
            "inductive PSigma σ = [1, 1]",
            "class-(P) PSigma' σ = [0, 0]",
        ],
        "the carriers moved:\n{d}"
    );
    // …and the three that got none. `PSigma' σ=[0, 0]` is absent because it
    // derived, and no `PSigma` row is here at any σ; both absences are the
    // point and both are pinned by the equality.
    let why = "declaration not translated: ind-spec(PSigma': class (P) above Prop)";
    assert_eq!(
        untranslated_rows(&d),
        vec![
            format!("PSigma' σ=[0, 1] ({why})"),
            format!("PSigma' σ=[1, 0] ({why})"),
            format!("PSigma' σ=[1, 1] ({why})"),
        ],
        "the untranslated pairs moved:\n{d}"
    );
}

// ─────────────────────────────────────────── zero constructors, with params ──

/// **A declaration with no constructors *and parameters* derives its
/// eliminator — the first witness anywhere for the `np > 0` branch.**
///
/// `recursor::empty_bottom` holds `t ∈ ⟦T p⃗⟧`, the applied spine, while
/// `derived::inductive::EmptyDecl` speaks of `ind(p⃗)`, and
/// `Interp::beta_spine` bridges them — *reflexivity at `np = 0` and a real
/// derivation above it*. **`Empty` has `np = 0`.** `059_emptyRec` is the only
/// witness in the corpus and it is the degenerate one, so the `np > 0` branch,
/// the `ps` threading through `inst_all(any, p⃗ ++ [t])`, and
/// `EmptyDecl::over_declaration` at a parameterised carrier were all written on
/// faith. This is the archetype of "the case that exercises the least structure
/// certifies nothing": a generality with exactly one witness, and that witness
/// the one where the generality collapses.
///
/// | declaration | np | sort | outcome |
/// | --- | ---: | --- | --- |
/// | `Void0` | 0 | `Type` | derives — the control, `Empty` again in this file |
/// | `Void` | 1 | `Type` | **derives** |
/// | `Void3` | 3 | `Type` | **derives**, parameters in a dependency chain |
/// | `VoidU` | 1 | `Type u` | **derives**, at a universe parameter in the declaration's own resultant sort |
/// | `VoidProp` | 1 | `Prop` | carrier derives; eliminator waits on `recursor(VoidProp: class (S) eliminator)` |
///
/// Three parameters and not two: `Thm::mp` against the major premise matches
/// `ind(p⃗)` exactly, so a *permutation* is already caught at `np = 2`. What two
/// cannot catch is a rule that threads some *prefix* of `p⃗`, and `Void3`'s
/// chain `α`, `β : α → Type`, `γ : (a : α) → β a → Type` makes every wrong
/// subset ill-formed.
///
/// # `VoidU`'s row is about a value, and is asserted as one
///
/// `VoidU.{u} : Type u → Type u` is scheduled at both `u := 0` and `u := 1`,
/// and its carrier is placed at `⟦Sort 1⟧` and `⟦Sort 2⟧` respectively. A
/// counter cannot see that: `constEv = 14` is equally true of a placement that
/// ignored σ and put both at the same rung, which is precisely the bug a
/// universe parameter in the resultant sort is here to expose. The two
/// statements are pinned via [`theorem_lines`]. Unlike the rung ladder's, this
/// one has not been shown redundant — I could not construct a mutation that
/// keeps `constEv` at 14 and moves a rung, but neither did I find the
/// over-determination argument that would prove there is none.
///
/// # `VoidProp` is the contrast, and its label is the real one
///
/// Zero constructors is large-eliminating by §2.6.2's reason 2 at any sort, but
/// `provably_nonzero(Sort 0)` is false, so `VoidProp` is routed to **class (S)**
/// and never reaches `EmptyDecl`. "Zero constructors" and "class (T), `n = 0`"
/// are therefore different questions, and `recursor.rs`'s table row is the
/// second. Two findings sit in that row:
///
/// * **`class_s::build` handles an empty disjunction.** `⟦VoidProp⟧` exists —
///   `voidPropTy` derives — so the `ψ = ⋁ᵢ …` carrier is fine with no
///   summands. Nothing had asked it before.
/// * **The eliminator's gap is `Cause::Library`, not a fallback.** The
///   `--block` report shows `⟦ty[σ]⟧` and `⟦val[σ]⟧` both in hand and only the
///   typing missing, on the same named row `And`, `PUnit` and `ProjDataIndex`
///   already occupy. So `VoidProp` joins a scoped backlog item rather than
///   revealing a new one.
#[test]
fn a_constructor_less_declaration_with_parameters_derives_its_eliminator() {
    // The arities and, above all, the **constructor counts**: this file is only
    // about `EmptyDecl` for as long as every declaration in it has none.
    let a = decl_arity("empty_parameterised.ndjson");
    for (n, want) in [
        ("Void0", (0, 0, 0)),
        ("Void", (1, 0, 0)),
        ("Void3", (3, 0, 0)),
        ("VoidU", (1, 0, 0)),
        ("VoidProp", (1, 0, 0)),
    ] {
        assert_eq!(a.get(n), Some(&want), "{n}'s (numParams, numIndices, ctors) changed: {a:?}");
    }
    let out = run("empty_parameterised.ndjson");
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&16), "the pair population changed:\n{out}");
    assert_eq!(e.get("typeEv"), Some(&16), "a carrier stopped deriving:\n{out}");
    // 16 less `voidPropRec` at its two σ. Every `Type`-valued row above — the
    // `np = 0` control, `np = 1`, `np = 3`, and the polymorphic sort — derives
    // carrier *and* eliminator.
    assert_eq!(e.get("constEv"), Some(&14), "the derived population changed:\n{out}");
    // Matched by **declaration**, not by the label's prose: the reason string
    // after the colon was refined from `class (S) eliminator` to
    // `class (S) eliminator: no constructors` while `062` was being written,
    // which is informative and is not what this test is about. The finding is
    // that `VoidProp` is the only row and every `Type`-valued declaration
    // derives; the wording is asserted separately and loosely.
    assert_eq!(
        blocked_recursors(&out),
        [("VoidProp".to_string(), 2u64)].into(),
        "the constructor-less frontier moved:\n{out}"
    );
    assert_eq!(blocked_recursors(&out).len(), waiting(&out).len(), "a non-recursor gap:\n{out}");
    for k in waiting(&out).keys() {
        assert!(k.contains("class (S) eliminator"), "unexpected reason `{k}`:\n{out}");
    }
    // Non-vacuity, and the point of the `VoidProp` row: zero constructors makes
    // *all five* large-eliminating by reason 2, and Lean agrees, so the split
    // between them above is the resultant sort and nothing else.
    let el = elim(&out);
    for n in ["Void0", "Void", "Void3", "VoidU", "VoidProp"] {
        assert_eq!(el.get(n), Some(&(true, true)), "{n} must be large-eliminating:\n{out}");
    }
    // **`VoidU`'s rung moves with σ, and that is a value the counters cannot
    // see.** `VoidU.{u} : Type u → Type u`, so its carrier is placed at
    // `⟦Sort 1⟧` when `u := 0` and at `⟦Sort 2⟧` when `u := 1`. `constEv = 14`
    // says both σ derived; it does not say they derived at *different* rungs,
    // and a placement that ignored σ would be exactly the bug this fixture's
    // `VoidU` row exists for. Pinned as the two derived statements.
    let vu = theorem_lines("empty_parameterised.ndjson", "VoidU");
    for want in [
        // `dprod₀(B, A)` is `A → B`; see the `mixedMk` note for why the
        // spelling moved and the fact did not.
        "typing ⊢ ⟦VoidU.{0}⟧ ∈ dprod₀(⟦Sort 1⟧, ⟦Sort 1⟧)",
        "typing ⊢ ⟦VoidU.{1}⟧ ∈ dprod₀(⟦Sort 2⟧, ⟦Sort 2⟧)",
    ] {
        assert!(
            vu.contains(&want.to_string()),
            "VoidU's carrier is no longer placed at a σ-dependent rung.\n\
             wanted: {want}\n   got: {vu:#?}"
        );
    }
}

// ─────────────────────────────────────────────── class (S), dependent fields ──

/// The declaration a `recursor(X: …)` gap is about, for the `waiting:` keys
/// whose reason string starts `recursor(`.
///
/// The suffix after the colon is prose that has been refined at least once
/// while a build was in flight, so tests that care *which declaration* is
/// blocked match on this and assert the shape of the label separately. That is
/// not a weakening: the finding is which declarations stop, not how the stop is
/// worded.
fn blocked_recursors(stdout: &str) -> BTreeMap<String, u64> {
    waiting(stdout)
        .into_iter()
        .filter_map(|(k, v)| {
            let r = k.strip_prefix("recursor(")?;
            Some((r.split(':').next()?.to_string(), v))
        })
        .collect()
}

/// **A class-(S) declaration whose field type depends on an earlier field.**
///
/// # The trap this guards, stated before the code exists
///
/// `nanoda_lib::mini::class_s` retains a typing `⊢ ⟦βⱼ⟧ ∈ U₀` per plain field. For **every**
/// class-(S) declaration in the corpus that typing is scope-dependent in a way
/// that hides its provenance: `And a b`'s field types are the parameters `a`
/// and `b`, `ProjDataIndex p`'s is the parameter `p`, and `PUnit` has no fields
/// at all. So `⊢ ⟦βⱼ⟧ ∈ U₀` is literally the parameter binder's own scope
/// assumption — `[a ∈ U₀] ⊢ a ∈ U₀` — and a hypothesis-carrying theorem cannot
/// be `inst_all`'d.
///
/// An eliminator that takes `Pⱼ` from **its own nest's parameter scope** and one
/// that takes it from `ClassS::field_sort` therefore agree on all three corpus
/// declarations and on all six of their pairs. **The corpus cannot distinguish
/// the two sources**, and the first is wrong for any declaration whose field
/// type is neither a parameter nor closed. This is the `scope_vars` shape again
/// — invisible to every witness — except that this time it is known first.
///
/// | declaration | field types | role |
/// | --- | --- | --- |
/// | `AndLike a b` | the parameters `a`, `b` | the corpus shape. **Control.** |
/// | `Closed` | the closed constants `Tru`, `Tru2` | the other corpus shape. **Control.** |
/// | `Dep2 α β` | `α`, then `β a` | the minimal dependent case |
/// | `Dep3 α β γ` | `α`, then `β a`, then `γ a b` | **the target** |
///
/// Three fields and not two: `LePropFields::steps` is a prefix fold, and at two
/// fields the prefix *is* everything. A rule threading the parameters plus a
/// **fixed one-field prefix** is right for `Dep2`'s `β a` and wrong for
/// `Dep3`'s `γ a b`, which mentions both earlier fields. Only the third
/// separates "fold the whole prefix" from "take the first of it" — `Void3`'s
/// argument, one clause over.
///
/// # What this reaches in `derived`, and how it lines up with the synthetic spec
///
/// `LePropFields`' ladder is `P₀ ⟹ H₀ ⟹ P₁ ⟹ H₁ ⟹ P₂ ⟹ …`, with the
/// contract that `Hⱼ` needs `P₀ … Pⱼ` and no others. Its header names the three
/// corpus declarations and says none of them needs it — `And`'s fields are its
/// parameters, `ProjDataIndex`'s is the closed `True`, `PUnit` has none — and
/// `derived/tests/family_le_prop_fields.rs` derives the fold at a **synthetic**
/// three-field spec `β₀(p)`, `β₁(p,y₀)`, `β₂(p,y₀,y₁)`.
///
/// The declarations here are the export-level counterparts, one per row of that
/// taxonomy:
///
/// | here | `LePropFields`' taxonomy |
/// | --- | --- |
/// | `AndLike` | `And` — fields are parameters |
/// | `Closed` | `ProjDataIndex` — closed field types (two distinct ones, not one) |
/// | `Dep3` | the synthetic three-field dependent spec |
///
/// `Dep3` matches that spec's dependency structure exactly — field 1's type
/// mentions field 0, field 2's mentions **both** — with one deliberate
/// difference: its `β₀` is the bare parameter `α` rather than a symbol applied
/// to a parameter. That makes it *sharper* for the trap, not weaker. `P₀` is
/// then the parameter binder's own scope assumption, so a build that reads `Pⱼ`
/// off the parameter scope gets field 0 right and fields 1 and 2 wrong, inside
/// a single declaration.
///
/// It also qualifies for the clause: `ni = 0`, one constructor, no recursive
/// field, which is what `LePropRecursor::build` refuses on. And it is a
/// *consumer* test rather than an export test — a Lean declaration through the
/// whole front end, not a `LeSpec` assembled in `derived`.
///
/// # Finding: Lean puts dependent-field declarations in class (S)
///
/// This was the open question and it was not safe to assume. All four
/// declarations export a recursor with **one** universe parameter, so all four
/// are large-eliminating; `Prop` is not provably nonzero, so all four are class
/// (S). Dependent class-(S) field types are therefore a real shape and not an
/// impossible one, which settles a question that had been circled from two
/// sides. The assertion below is against the exported recursor, so Lean
/// adjudicates.
///
/// # What this pins, and the outcome it turned out to be
///
/// **All sixteen pairs derive — `Dep2` and `Dep3` included — and the blocked
/// set is empty.** That is the first of the two outcomes this fixture was
/// written to distinguish: `nanoda_lib::mini::rec_prop` takes `Pⱼ` from
/// `ClassS::field_sort` and climbs `LePropFields::steps`, so field 1's and
/// field 2's propositionality come off `H₀` and `H₀ ∧ H₁` rather than off any
/// parameter binder, and the whole prefix is folded rather than a fixed one of
/// it. The alternative reading — `AndLike` and `Closed` deriving while `Dep2`
/// and `Dep3` did not — would have meant `Pⱼ` was coming from the parameter
/// scope. It did not happen, and this fixture is why we know rather than hope.
///
/// The claim survives the sharpening the header describes: `Dep3`'s `β₀` is the
/// bare parameter `α`, so a parameter-scope build would have got field 0 right
/// and fields 1 and 2 wrong *inside one declaration*, and the count would have
/// been neither 8 nor 16.
///
/// What made it possible is on the `zoneb` side rather than the eliminator's:
/// `CtorEvidence::field_sort` is retained **discharged**,
/// `⊢ ∀p⃗.(p⃗ ∈ ⟦σ⃗⟧ → ∀y⃗<ⱼ.(y⃗<ⱼ ∈ ⟦β⃗<ⱼ⟧ → ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧))`, because the raw
/// hypothesis-carrying form it kept before cannot be `inst_all`'d and so was
/// unusable by any consumer at another nest — which on the three corpus
/// declarations is invisible, and here is the whole test.
///
/// # The provenance of the numbers, which is still the point
///
/// The **previous** pin (8 derived, all four blocked) was measured in a clean
/// worktree at committed HEAD while `062` sat uncommitted in the tree deriving
/// 16. Pinning the local binary would have produced a test that fails on every
/// clean checkout and in CI while looking green to its author. The numbers
/// below are the post-`062` measurement of the same fixture, taken from the
/// tree that landed it. This is the stale-binary trap one level up — not an
/// out-of-date build but an *ahead*-of-HEAD one — and the rule that catches
/// both is the same: measure the state you are pinning, not the state you
/// happen to have.
///
/// # A count is the only instrument here, and that is a property of the shape
///
/// The claim this fixture makes is about `Dep3`'s field types being threaded in
/// dependency order, which sounds like a claim about a *value* — the kind
/// [`theorem_lines`] exists for. **It cannot be pinned that way, and the reason
/// generalises.** Every declaration here is `Prop`-valued, so every constant is
/// a proof interpreting to `•` and every type is `⟦Sort 0⟧`: the dump reports
/// `⊢ ⟦Dep3.{}⟧ ∈ f150(⟦Sort 0⟧, ⟦Sort 0⟧, ⟦Sort 0⟧, ⟦Sort 0⟧)` and
/// `defeq ⊢ ⟦dep3Mk.{}⟧ = ⟦Tru.triv.{}⟧`, in which neither the field order nor
/// the dependency is visible at all.
///
/// So the rule is not "prefer statements to counts" but the narrower one: a
/// statement is a better oracle **where the types differ**. On an all-`Prop`
/// declaration they do not, and the count is not a stand-in for something
/// better — it is the only thing there is. The two `Prop`-heavy fixtures in
/// this file are both in that position.
///
/// # Why the label is matched by prefix
///
/// While this was being written, the working tree refined these strings to
/// `… : the field inhabitations` and `… : the constructor's own interpretation`
/// — informative, and *not* what the test is about. The declaration set and its
/// counts are asserted exactly; the prose after the colon is not.
#[test]
fn a_class_s_declaration_whose_field_type_depends_on_an_earlier_field() {
    // Shape first, out of the export. `Dep3` is only a three-field prefix fold
    // for as long as Lean leaves it three parameters and one constructor.
    let a = decl_arity("class_s_dependent_fields.ndjson");
    for (n, want) in [
        ("AndLike", (2, 0, 1)),
        ("Closed", (0, 0, 1)),
        ("Dep2", (2, 0, 1)),
        ("Dep3", (3, 0, 1)),
    ] {
        assert_eq!(a.get(n), Some(&want), "{n}'s (numParams, numIndices, ctors) changed: {a:?}");
    }
    let out = run("class_s_dependent_fields.ndjson");
    // **The open question, answered by Lean.** All four large-eliminating, so
    // all four are class (S) — a dependent class-(S) field type is a real
    // shape. `computed` must agree, or §2.6.2's reading is wrong.
    let el = elim(&out);
    for n in ["AndLike", "Closed", "Dep2", "Dep3"] {
        assert_eq!(el.get(n), Some(&(true, true)), "{n} must be class (S):\n{out}");
    }
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&16), "the pair population changed:\n{out}");
    assert_eq!(e.get("typeEv"), Some(&16), "a class-(S) carrier stopped deriving:\n{out}");
    // **All sixteen.** Each declaration's `…Ty`, `…Mk` and `…Rec` at two σ,
    // with the eliminator reaching the dependent declarations as readily as the
    // controls. `8` here means the class-(S) eliminator stopped deriving
    // outright; anything strictly between is the split below.
    assert_eq!(
        e.get("constEv"),
        Some(&16),
        "the derived population changed. 8 means the class-(S) eliminator stopped reaching \
         this fixture at all. Anything between 8 and 16 means some declarations were left \
         behind: read the blocked set below, and if it is `Dep2`/`Dep3` that is the \
         parameter-scope bug this fixture exists to catch — see the header before changing \
         a line of this test.\n{out}"
    );
    // **The split, by declaration**, and it is empty. If it ever comes back as
    // exactly `Dep2`/`Dep3`, `Pⱼ` has started coming off the parameter scope
    // and the corpus's six pairs would report everything fine.
    let blocked = blocked_recursors(&out);
    assert_eq!(
        blocked,
        BTreeMap::new(),
        "the class-(S) eliminator frontier moved. If `Dep2`/`Dep3` are the only rows, that \
         is the parameter-scope bug this fixture exists to catch and NOT a fixture problem \
         — read the header before changing anything:\n{out}"
    );
    // And nothing else crept in on any other axis either.
    assert!(waiting(&out).is_empty(), "a gap appeared on this fixture:\n{out}");
}

/// **The certification axis is in the verdict and in the exit code.**
///
/// `MINI-DESIGN.md` §0 has two axes, and until this test only one of them
/// reached a caller who did not pass `--verbose`: a bare `mini export.ndjson`
/// printed `accept N declarations` and exited `0` whether or not every
/// obligation had been discharged. For a tool whose claim is *every
/// definitional-equality conclusion carries a certificate*, that is the wrong
/// default, and the two directions below are what make it not the default any
/// more.
///
/// * **A fully-certified run stays quiet**, exactly as it always has —
///   `rung_ladder` prints three tab columns and exits `0`. Half a test on its
///   own: a tool that reported every run as uncertified would satisfy the other
///   half and be useless.
/// * **A partially-certified run says so and exits nonzero** —
///   `beyond_the_tower` is the witness, and its header argues why it is a
///   *permanent* one rather than a fixture with a shelf life.
/// * **A run that did not translate something says so and exits nonzero, even
///   with every obligation counter at zero** — `elim_class_trichotomy` is the
///   witness, and it is the direction the first version of this test could not
///   have caught. See below.
///
/// `4` and not `1` or `2`: those are verdicts about the file, and this is not
/// one. `beyond_the_tower` is well typed and mini accepted it. In particular an
/// untranslated declaration is **not** an arena decline: `2` is the arena's
/// code for an unsupported feature at file level and its population is the
/// arena's contract, while `elim_class_trichotomy` is a file mini accepted.
///
/// # The second axis, and why the first could not see it
///
/// *Added in place; the list above had two bullets and the sentence "the two
/// directions below are what make it not the default any more" counted them.*
/// `Uncertified`'s counters are **shortfalls against `pairs`**, and
/// `Declaration::Inductive` schedules no pair. `elim_class_trichotomy` reads
/// `pairs=0 constEv=0 typeEv=0 gapped=0 unsealed=0` — every counter in that set
/// is *structurally* zero — while four eliminators went unbuilt. It printed
/// `accept 10 declarations` and exited `0`. `nanoda_lib::mini::ledger::Untranslated` is the
/// second set, and this fixture is the case that distinguishes them: nothing
/// else here can make it exit `4`.
///
/// `--block`'s `3` still wins, and that ordering is deliberate: a blocked run
/// stopped at the first gap, so its counters are partial by design and must not
/// be published as a census.
#[test]
fn the_certification_axis_is_in_the_verdict_and_in_the_exit_code() {
    /// `mini <flags> <fixture>` with no status assertion — the status *is* what
    /// is under test here.
    fn raw(name: &str, flags: &[&str]) -> (Option<i32>, String) {
        let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
            .arg("--no-modelgen")
            .args(flags)
            .arg(fixture(name))
            .output()
            .expect("spawn mini");
        (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
    }
    let verdict = |s: &str| s.lines().next().unwrap_or_default().to_string();

    // ── clean: quiet, and unchanged ──────────────────────────────────────
    let (code, out) = raw("rung_ladder.ndjson", &[]);
    let v = verdict(&out);
    assert_eq!(code, Some(0), "a fully-certified run must exit 0:\n{out}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec!["rung_ladder.ndjson", "accept", "15 declarations"],
        "a clean verdict line must read exactly as it always has"
    );

    // ── uncertified: named, and nonzero ──────────────────────────────────
    let (code, out) = raw("beyond_the_tower.ndjson", &[]);
    let v = verdict(&out);
    assert_eq!(code, Some(4), "an accepted-but-uncertified run must not exit 0:\n{out}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec!["beyond_the_tower.ndjson", "accept", "2 declarations", "uncertified: 1 type typing"],
        "the verdict must name what is owed, and a reader must not be able to mistake it \
         for a clean run"
    );
    // **The half a `constEv`-only definition of "uncertified" would have
    // missed.** Every constant typing on this fixture derives; what is owed is
    // the *type's own* typing, and `Uncertified::type_typings` is in the set
    // because of exactly this row. If this ever reads `constEv=1`, the fixture
    // has drifted and the claim above is no longer what it is measuring.
    let e = evidence(&run("beyond_the_tower.ndjson"));
    assert_eq!(e.get("constEv"), Some(&2), "every constant typing must still derive");
    assert_eq!(e.get("typeEv"), Some(&1), "the tower gap closed — re-point the fixture higher");
    assert_eq!(e.get("typeEvOnlyGap"), Some(&1), "the constant typing must outrun its type's");

    // ── untranslated: the axis with no obligation behind it ───────────────
    //
    // Every counter in `Uncertified` is zero here and cannot be otherwise —
    // `pairs=0`, because this fixture's ten declarations are inductives and
    // an inductive schedules no `(declaration, σ)` pair. So this run's exit `4`
    // is produced by the untranslated axis and by nothing else, which is the
    // whole reason that axis is a second set rather than a fifth counter.
    let (code, out) = raw("elim_class_trichotomy.ndjson", &[]);
    let v = verdict(&out);
    assert_eq!(code, Some(4), "an untranslated eliminator must not exit 0:\n{out}");
    assert_ne!(code, Some(2), "and it must not become an arena decline:\n{out}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec!["elim_class_trichotomy.ndjson", "accept", "10 declarations", "untranslated: 4 eliminators"],
        "the verdict must name what was not translated, and must not carry an `uncertified:` \
         column — there is no obligation here to be short of"
    );
    let verb = run("elim_class_trichotomy.ndjson");
    let e = evidence(&verb);
    assert_eq!(
        (e.get("pairs"), e.get("constEv"), e.get("typeEv"), e.get("unsealed")),
        (Some(&0), Some(&0), Some(&0), Some(&0)),
        "the fixture drifted: if it now schedules a pair, exit 4 could come from the other \
         axis and this direction stops being tested:\n{verb}"
    );
    assert_eq!(e.get("gapped"), None, "…and `gapped` lives on the `convs` row, not this one");
    assert_eq!(row(&verb, "convs").get("gapped"), Some(&0), "no gapped conversion either");
    // A ratchet on the count, so that four eliminators landing fails here
    // loudly instead of quietly retiring the only witness for this direction.
    let u = row(&verb, "untranslated");
    assert_eq!(
        (u.get("declarations"), u.get("constructors"), u.get("eliminators")),
        (Some(&0), Some(&0), Some(&4)),
        "the untranslated population moved — re-point this direction at a live witness:\n{verb}"
    );

    // ── the opt-out, for a run that only cares about acceptance ───────────
    let (code, out) = raw("beyond_the_tower.ndjson", &["--acceptance-only"]);
    assert_eq!(code, Some(0), "--acceptance-only must restore Main.lean's three codes:\n{out}");
    assert!(
        verdict(&out).contains("uncertified: 1 type typing"),
        "the flag governs the exit code, not what is printed:\n{out}"
    );
    // …and it must opt out of the *other* half too, or `scripts/mini-vs-nanoda.sh`
    // — which compares acceptance and nothing else — starts failing on files
    // both tools accept.
    let (code, out) = raw("elim_class_trichotomy.ndjson", &["--acceptance-only"]);
    assert_eq!(code, Some(0), "--acceptance-only must cover the untranslated axis too:\n{out}");
    assert!(
        verdict(&out).contains("untranslated: 4 eliminators"),
        "the flag governs the exit code, not what is printed:\n{out}"
    );

    // ── `--block` keeps its own code, and keeps stopping ──────────────────
    let (code, out) = raw("empty_parameterised.ndjson", &["--block"]);
    assert_eq!(code, Some(3), "--block's exit 3 must survive the new code:\n{out}");
    assert!(out.contains("BLOCKED\t"), "--block must still print its report:\n{out}");
    // Its counters are the ones from a run that stopped, and they are still
    // reported — the verdict line is the same line, with the same column.
    assert!(
        verdict(&out).contains("uncertified: 1 const typing"),
        "a blocked run's verdict must still carry the column:\n{out}"
    );

    // ── the two stop-sets are **not** the same set, and this is the proof ──
    //
    // `--block` deliberately does not stop on an underived
    // `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`: `Ledger::type_ev_only_gap` is the measurement
    // that keeps it out of `blocker::Obligation`, on the argument that on the
    // corpus no constant typing ever outran its type's. `beyond_the_tower` is a
    // file where one does — so `--block` runs it to the *end* and reports no
    // blocker at all, while a real obligation is owed.
    //
    // That is an argument for this whole test and not a defect in `--block`:
    // the development mode is *stop at the first thing I can act on*, and it
    // could never have surfaced this row. Only the default can.
    let (code, out) = raw("beyond_the_tower.ndjson", &["--block"]);
    assert_eq!(code, Some(4), "--block finds nothing to stop on here:\n{out}");
    assert!(!out.contains("BLOCKED"), "the blocker's stop-set does not include this:\n{out}");
}

// ────────────────────────────────── a parameter as a branching domain ──

/// **A recursive argument whose domain is a *parameter* certifies, and the
/// certificate is conditional on that parameter's typing.**
///
/// `PTree.node : (α → PTree α) → PTree α` gives its slot the fibre summand
/// `Σ(z::α)`, and `Σ(z::α) ∈ Uₙ` is available under `α ∈ Uₙ` and under nothing
/// weaker — a `PTree α` over an `α` that is not small has no W-type in `Uₙ` at
/// all. That is not a gap; it is what the theorem *says*. A Lean declaration is
/// always closed, so a parameterised one's placement is
/// `⊢ ∀p⃗. (H → ind(p⃗) ∈ Uₙ)` and every use site has `H` ready.
///
/// The placement demanded its fibre facts unconditional for two rounds, for two
/// reasons that both expired: `bnd` at a parameter is refutable (`bnd` is gone),
/// and `isum::isum_in_universe` refuses a conditional input where the fact is
/// spent (`isum_in_universe_under` carries it). What the mini side needed was
/// not a placement change at all — the row was sitting with `α ∈ ⟦Sort ℓ⟧` in
/// its **hypothesis set** and stated at the walk's own scope variable, one
/// discharge away from the shape every summand leg was already in.
///
/// # Five trees, and the fifth was found by a mutation
///
/// | declaration | `np` | recursive-argument domains | before | after |
/// |---|---|---|---|---|
/// | `CTree.node : (B2 → CTree) → CTree`                     | 0 | one, closed            | certifies | certifies |
/// | `KTree.node : (B2 → KTree α) → KTree α`                 | 1 | one, closed            | certifies | certifies |
/// | `PTree.node : (α → PTree α) → PTree α`                  | 1 | one, **the parameter** | declined  | **certifies** |
/// | `MTree.node : (B2 → MTree α) → (α → MTree α) → MTree α` | 1 | **two, mixed**         | declined  | **certifies** |
/// | `XTree.node : XTree α → (α → XTree α) → XTree α`        | 1 | one **empty**, one parameter | declined | **certifies** |
///
/// `CTree` and `KTree` are the controls, and they are not decoration: they say
/// that neither a function-typed recursive argument nor a parameter is on its
/// own what the placement could not do, so the row that moved names the
/// property that moved. `PTree` is the witness. `MTree` is the row a fixture of
/// three would have missed — its constructor's fibre value is
/// `Sum_2(Σ(z::⟦B2⟧), Σ(z::α))`, two *different* summands in one sum, only one
/// of which would be provable without `H`; the other three trees would all be
/// `Sum_1`.
///
/// **Where the rows are made uniform is not the fold**, and the fixture's own
/// header says so rather than leaving the obvious wrong answer standing:
/// `spec_of` discharges *every* recursive-argument domain typing through the
/// parameter scopes, needed or not, so both of `MTree`'s rows already carry `H`
/// when `isum_in_universe_under` sees them. The lifting the fold does is at
/// each tree's `leaf`, which contributes no summand and whose `Sum_0()` rests
/// on `∅ ∈ Uₙ` — a fact about the universe, lifted into `H` rather than
/// obtained there.
///
/// `XTree` is the fifth row and **a mutation put it here, not a design**. Its
/// first recursive slot has an *empty* `γ`, so `zoneb::fibre_facts` synthesises
/// that summand as the one-point set rather than deriving it — and that
/// synthesised row has to be lifted into `H` like every other. Deleting the
/// lift killed **nothing** across the whole `derived` and `mini` suites before
/// this row existed: the branch is reached only when some *other* slot in the
/// same declaration has a non-empty `γ`, the four rows above are all-or-nothing
/// on that, and `np = 0` makes the lift vacuous.
///
/// # `constEv == 10`, and what each number means when it moves
///
/// * `constEv == 10` — every pair, two `def`s per tree. It was **4** (`CTree`
///   and `KTree`) for as long as `FibreFacts` was required unconditional, and
///   it went straight to 10: `PTree`, `MTree` and `XTree` were blocked by that
///   one requirement and by nothing else. A landing at 6 or 8 would mean one of
///   the three had been left behind, which on this route cannot happen.
/// * `typeEv == 10` — it was **6**. `ptreeNode`'s declared type mentions
///   `PTree B2`, so the type typing was owed on the declaration being placed;
///   both halves close together.
/// * the `waiting` set — **empty**. A key reappearing here without `constEv`
///   falling would be a gap *renamed* rather than opened.
/// * `untranslated declarations == 0`.
///
/// # The eliminators — three closed, and the fourth is a different axis
///
/// `KTree.rec`, `PTree.rec` and `MTree.rec` used to report
/// `recursor(…: dependent recursor: a minor premise does not transport)`, on an
/// axis this section named correctly: **the parameterised dependent recursor**,
/// not the branching domain — `KTree` reported it at `np = 1` with a *closed*
/// `γ`, and `CTree.rec` at `np = 0` was the control that said so.
///
/// All three translate now, and it was **two** bugs on that one axis, both in
/// `rec_dep` and both the same sentence: a term stated at the *declaration's own
/// parameter variables* compared against one stated at `⟦p⃗⟧`.
///
/// * `crossings` compared `Inductive::ctor_slot_domains`' `Aⱼ` — which is
///   `RecArg::summands`, at `Inductive::params` — against `tel.ty_of(⟦p⃗⟧)`.
/// * `ctor_at_binders` built the constructor term with `Inductive::ctor_term`,
///   which is `ctor_term_at` at `Inductive::params`; `derived`'s own header for
///   that function calls the mixture "half at its own variables and half at the
///   declaration's, which is not a constructor application of anything".
///
/// **Both are invisible at a closed `γ`**, where the fibre summands mention no
/// parameter and the two spellings are literally the same term — which is why
/// `KTree` (closed `γ`, `np = 1`) declined for the *first* reason and every
/// `np = 0` cell in `rec_dep`'s own unit tests passed throughout. `P.c` in
/// `rec_dep::tests::a_function_typed_recursive_slot_stops_the_dependent_eliminator_at_both_sigma`
/// is the cell added for it: `P (α : Type) | c : (α → P α) → P α`, the shortest
/// declaration at which the two frames differ.
///
/// `XTree.rec` is the remaining row and it is the **other** axis: a mixed
/// constructor's plain recursive slot, which needs `derived::point_fun` at
/// `a := •` and is untouched by any of this.
#[test]
fn a_recursive_argument_ranging_over_a_parameter_is_placed_under_its_typing() {
    let out = run("parameter_domain_branching.ndjson");

    // ── the frontend got all the way through ─────────────────────────────
    let el = elim(&out);
    for name in ["B2", "CTree", "KTree", "PTree", "MTree", "XTree"] {
        assert_eq!(
            el.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    // ── five trees, ten pairs, and every one of them certifies ───────────
    all_derived(&out, 10);
    let e = evidence(&out);
    assert_eq!(
        e.get("typeEv"),
        Some(&10),
        "the type typings close with the const typings — `ptreeNode`'s type mentions the \
         declaration being placed, so 6 here is the state before it was:\n{out}"
    );
    assert_eq!(e.get("unsealed"), Some(&0), "nothing persists with a hypothesis:\n{out}");
    assert_eq!(
        row(&out, "convs").get("gapped"),
        Some(&0),
        "no conversion is left unproved:\n{out}"
    );

    // ── and the declarations themselves are translated ───────────────────
    let u = row(&out, "untranslated");
    assert_eq!(
        u.get("declarations"),
        Some(&0),
        "`ind-fibre-value` is what `PTree` and `MTree` reported, and it is gone:\n{out}"
    );
    assert_eq!(u.get("constructors"), Some(&0), "and so are the constructors:\n{out}");

    // The one axis this fixture does *not* close, named rather than left to be
    // rediscovered. It was two; the parameterised-recursor one is closed, and
    // the count alone would not have said which — the two carried different
    // strings, and asserting both by name is what makes the residue readable.
    assert_eq!(
        u.get("eliminators"),
        Some(&1),
        "one untranslated recursor. It was four: the parameterised dependent recursor's \
         two frame bugs closed `KTree`, `PTree` and `MTree` together, and `XTree` is the \
         other axis:\n{out}"
    );
    for name in ["CTree", "KTree", "PTree", "MTree"] {
        assert!(
            !out.contains(&format!("notrans:recursor({name}")),
            "{name}.rec translates — a `minor premise does not transport` row reappearing \
             here is a revert of one of the two parameter-frame fixes:\n{out}"
        );
    }
    // `XTree.rec` is the *other* axis and it is not the parameterised recursor:
    // its constructor mixes a plain recursive slot with a function-typed one,
    // so the eliminator meets a shape the placement is untroubled by.
    assert!(
        out.contains(
            "notrans:recursor(XTree: dependent recursor: a mixed constructor's plain \
             recursive slot)"
        ),
        "`XTree.rec`'s decline is its own, and must not be folded into the other three:\n{out}"
    );
}

// ───────────────────── a recursive field that only reduces to the spine ──

/// **A recursive field's Lean type is what the user wrote; the eliminator's
/// atom is what it reduces to.**
///
/// `zoneb::rec_field` classifies a field as recursive **by its reduct**, so
/// `constType (T α) (T α)` is a recursive argument — and then everything the
/// minor premise's walk does is stated at `⟦constType (T α) (T α)⟧` while
/// `derived`'s own atom is at the carrier. The two are one conversion apart and
/// `rec_dep::minor_at` cannot mint it: it holds an `Interp`, which β-reduces a
/// stored λ, and δ-unfolding a Lean constant with a certificate is `whnf`.
/// `rec_dep::ctor_bridges` mints it where a `Checker` exists.
///
/// | declaration | recursive slots | what it exercises |
/// |---|---|---|
/// | `Spelled` | one plain, spelled | the control — a recursive field alone is not the obstacle |
/// | `Cod` | one plain, `constType (Cod α) (Cod α)` | `at_atom`'s set equation, composed with the reduction |
/// | `FunCod` | **three** function-typed: spelled, then two *different* aliases | `push_into_pi`, at slots 1 and 2 of 3 |
///
/// **Seen red.** With `rec_dep::rec_slot_eq` stubbed to `None` — the state
/// before this landed — `Cod.rec` and `FunCod.rec` both report
/// `recursor(…: dependent recursor: a minor premise does not transport)` and
/// `Spelled.rec` does not, which is what makes the control a control.
///
/// **Three function-typed slots, two of them different aliases.**
/// `CtorBridge::rec_eq` is indexed by recursive-slot order, and this cell is
/// shaped against the three ways an index map goes wrong rather than one: a
/// shift sends slot 1 to slot 2's equation, a clamp `j ↦ min(j,1)` sends slot 2
/// to slot 1's, and a reversal sends slot 2 to slot 0's `None`. `constType` and
/// `constType2` are two definitions with the same reduct, so the first two read
/// an equation whose left endpoint is the *other* alias and fail its check.
///
/// **The clamp is why there are two aliased slots and not one.** With the
/// single alias at the middle of three, `min(j,1)` is the identity everywhere
/// it matters and the mutation **survived** — measured, before this shape.
///
/// The **other** half of the corpus rows — a constructor whose *parameter*
/// binder is a reducible alias of the type former's — is not here, and that is
/// a measurement: writing `inductive T (α : id Type) : Type` puts the alias on
/// the type former, the constructors and the recursor at once, which is a
/// uniform frame that exercises nothing and declines earlier under
/// `ind-spec(T: type former spine)`. The corpus's `052`/`113`/`114` are
/// hand-built kernel tests, and `rec_dep`'s `Q.c` cell builds that environment
/// directly.
#[test]
fn a_recursive_field_that_only_reduces_to_the_spine_carries_its_eliminator() {
    let out = run("reducible_ctor_binders.ndjson");

    let el = elim(&out);
    for name in ["B2", "Spelled", "Cod", "FunCod"] {
        assert_eq!(
            el.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    // Three declarations, three `def`s each, plus `constType` and
    // `constType2`: eleven pairs, and every one of them certifies.
    all_derived(&out, 11);
    let e = evidence(&out);
    assert_eq!(e.get("typeEv"), Some(&11), "the type typings close too:\n{out}");
    assert_eq!(e.get("unsealed"), Some(&0), "nothing persists with a hypothesis:\n{out}");
    assert_eq!(
        row(&out, "convs").get("gapped"),
        Some(&0),
        "no conversion is left unproved:\n{out}"
    );

    let u = row(&out, "untranslated");
    assert_eq!(u.get("declarations"), Some(&0), "every declaration translates:\n{out}");
    assert_eq!(u.get("constructors"), Some(&0), "and every constructor:\n{out}");
    assert_eq!(
        u.get("eliminators"),
        Some(&0),
        "and every eliminator. `Cod.rec` and `FunCod.rec` are the two that did not, both \
         as `a minor premise does not transport`, and a count alone would not say which — \
         so the names are asserted below as well:\n{out}"
    );
    for name in ["Spelled", "Cod", "FunCod"] {
        assert!(
            !out.contains(&format!("notrans:recursor({name}")),
            "{name}.rec translates — a `minor premise does not transport` row reappearing \
             here is a revert of the recursive-field bridge:\n{out}"
        );
    }
}

// ─────────────────────────── an indexed family that branches ──

/// **An indexed family with a function-typed recursive argument — four layers
/// lifted, and the fifth is a different obligation.**
///
/// This fixture is the only export anywhere that is indexed (`ni ≥ 1`), has a
/// parameter (`np ≥ 1`) *and* takes a function-typed recursive argument, which
/// is the combination under which the indexed constructor abbreviation's
/// abstraction over the fields alone is distinguishable from one over
/// `p⃗ ++ f⃗`. At `np = 0` the two spellings are the same term, which is why 91
/// corpus exports could not see the difference.
///
/// **Every one of its four pairs certifies.** `constEv = 4` was the target from
/// the day it was exported; what is left is the *eliminator*, which is a
/// separate obligation with its own key.
///
/// | round | the stop |
/// |---|---|
/// | as exported | `ind-spec(IxT: indexed function-typed recursive argument)` — a blanket `ni != 0` refusal in `zoneb::ctor_spec` |
/// | lift 1 | `ind-spec(IxT: naming a constructor's term)` — `ctor_ix::ctor_abbrevs` over the fields alone |
/// | lift 2 | `ind-spec(IxT: indexed carrier)` — **`derived/`**'s good-set matrix |
/// | lift 3 | `ctor(IxT.node: a recursive argument's indices)` — `ctor_ix`'s frame |
/// | lift 4 | `ctor(IxT.node: a function-typed recursive field)` — `ctor_ix`'s five-step bridge |
/// | now | `recursor(IxT: indexed value recursor: …)` — the eliminator, a different obligation |
///
/// # What each lift actually needed, and none of it was what was predicted
///
/// **Lift 1 was a de Bruijn frame, not an abstraction list.** The refusal's
/// stated ground was that such a field's index expressions may mention the
/// bound `z⃗`, which `index_syms` cannot abstract over. True in general and
/// false here: `IxT.node`'s recursive occurrence is indexed by the *plain
/// field* `n`. `rec_field` peels `∀z⃗` to find the spine, so the indices come
/// back stated `|γ⃗|` binders deeper than the checker has open — and read at the
/// shallower depth `n` resolves to the **parameter** `α`, which is also in the
/// abstraction list, so a wrong symbol would have been minted in silence.
///
/// **Lift 2 was predicted exactly and its consumers were not.** Three other
/// readers instantiate the abbreviation — `ctor_ix::build`, `iota_ix_dep` and
/// `minor_ix` — and they surfaced as ten failing tests including the corpus.
///
/// **Lift 3 was a construction in `derived/`, and it had two stops.** A
/// `?`-census put the first at `Good::build`'s ι *statement* rebuild — the
/// plain `ctor_atoms` wrapper where `iota_core` had used
/// `ctor_atoms_at`/`rec_sets`, which agree only when every slot is plain.
/// Aligned, the census moved to the `?` the general case really owed:
/// `GoodIota::ih_eqs`, an *unconditional* `app(cmp, Injⱼ(•)) = app(goodrec,
/// rⱼ)` that does not exist at a fibre with more than one point. The good-set
/// matrix's conjunct became a bounded universal and the ih row became a
/// conditional `z`-indexed identity; five sites moved together.
///
/// **Lift 4 was lift 1's hazard one construction over, and then prior art.**
/// `ctor_ix::ctor_bottom` read `d⃗` off the field's `local_type` at the nest's
/// own depth, and a function-typed field's type is `∀z::γ. T p⃗ d⃗` — so
/// `ind_spine` was matching a `Forall` against a spine and failing. It is asked
/// at `nf + |γ⃗|` now, and the `γ⃗` binders are opened *interpreted* for the
/// inference, exactly as `ctor_spec` does. The rest is `zoneb::ctor_bottom`'s
/// five steps at an indexed codomain, the fourth of which composes two
/// equations rather than one: `⟦T p⃗ ⟦d⃗⟧⟧ → ind(p⃗, ⟦d⃗⟧) → ind(p⃗, d⃗ᵢⱼ)`.
///
/// **The frame is checked and not trusted.** `index_congr` requires each `d`
/// abbreviation's right-hand side to be the term inference produced, and the
/// abbreviation was minted by `ctor_spec` reading the same expressions in the
/// same frame — so a shifted read is a decline rather than a theorem about
/// another declaration's carrier.
/// `ctor_ix::tests::a_function_typed_recursive_arguments_indices_are_read_inside_its_own_binders`
/// is the cell that says so, at **two** indices, **two** plain fields and
/// **two** recursive slots whose index vectors are the same pair in opposite
/// orders — every axis this fixture leaves at one.
///
/// # What this test protects
///
/// The four lifts, in the only direction they can regress. A reason string
/// from any earlier round reappearing is a revert; a *new* one is a new layer
/// and worth knowing about immediately.
#[test]
fn an_indexed_family_with_a_function_typed_recursive_argument_reaches_derived() {
    let out = run("indexed_infinitary_ctor.ndjson");

    let el = elim(&out);
    for name in ["N", "B2", "T3", "IxT"] {
        assert_eq!(
            el.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    // ── the target, reached ──────────────────────────────────────────────
    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&4), "four defs:\n{out}");
    assert_eq!(
        e.get("constEv"),
        Some(&4),
        "every pair's constant typing. `ixTNode` and `ixTWide` are the two whose \
         constructor takes a function-typed recursive argument, and they were the \
         last two to land:\n{out}"
    );
    assert_eq!(e.get("typeEv"), Some(&4), "and every type typing:\n{out}");
    assert!(waiting(&out).is_empty(), "**no** waiting key at all:\n{out}");
    assert_eq!(e.get("unsealed"), Some(&0), "nothing persists with a hypothesis:\n{out}");
    assert_eq!(row(&out, "convs").get("gapped"), Some(&0), "no conversion is unproved:\n{out}");

    // The declaration and both branching constructors translate; what is left
    // is the **eliminator**, a separate obligation with its own key. A
    // `declarations` or `constructors` count above zero is a revert of one of
    // the four lifts.
    let un = row(&out, "untranslated");
    assert_eq!(un.get("declarations"), Some(&0), "the carrier is placed:\n{out}");
    assert_eq!(un.get("constructors"), Some(&0), "every constructor is built:\n{out}");
    assert_eq!(un.get("eliminators"), Some(&1), "and only the recursor is not:\n{out}");
    assert!(
        out.contains("notrans:recursor(IxT: indexed value recursor:"),
        "…under the recursor's own key, not a constructor's or a declaration's:\n{out}"
    );
}

/// **A constructor spelled through an abbreviation, on both sides of ι.**
///
/// `ctor_abbrev_major.lean` states every recursor's minors *and* its major
/// premise through `def`s that unfold to constructors — `nz := N.z`,
/// `ixba a := Ix.iba a` — and asserts the computation rules as `Eq.refl _`.
/// Lean takes all of it definitionally; this pins that mini's **evidence** axis
/// does too, which needed two independent fixes.
///
/// # Why this is not `mutual_aux_encoding` again
///
/// It is the same mechanism with the mutual recursion taken out. The aux
/// encoding is where the shape was found, and it cannot avoid it: an installed
/// `A.rec` must state its minors at `A.aB`, since a recursor stated at
/// `Aux.aB` is a different constant. But that fixture belongs to the mutual arc
/// and measures three interlocking members at once, so a regression there names
/// the encoding. Here the two failures are separated, each at its own family.
///
/// # The two fixes, and the four numbers that separate them
///
/// Measured on this fixture, `constEv` out of 32:
///
/// | `conv::app_cong` records its endpoints | ι reduces the major with a certificate | `constEv` |
/// | --- | --- | --- |
/// | no  | no  | 21 |
/// | no  | yes | 26 |
/// | yes | no  | 25 |
/// | yes | yes | **32** |
///
/// Neither fix subsumes the other and neither is redundant, which is what the
/// off-diagonal rows say. The fixture is built to make that true:
///
/// * **`nrec`** hands `N.rec` its motive directly. Its minors are at `nz`/`ns`/
///   `nd`, so the conversion against `N.rec`'s `m N.z` is between two terms
///   `infer_type` built through `Interp::app` — both decompose, and only the
///   *major* half fails.
/// * **`nrec2`** computes the motive with `Tag.rec`. Now the recursor's own
///   minor type only reaches `m₂ N.z` by ι and δ, so its interpretation is a
///   term `conv::app_cong` built inside the kernel — and an endpoint that was
///   never recorded in `Interp`'s `parts` table is one `Checker::split_app`
///   cannot take apart, so the congruence below it gapped `no-endpoint`.
/// * **`irec`** is the indexed family, which reaches `iota_ix_dep` rather than
///   `iota_dep` — a different arm of the same match, so a fix applied to one
///   would pass on `N` alone.
///
/// `nrec2` selects `Tag.tb`, the **middle** tag: a motive selection that
/// clamped to either end would pass at `ta` or at `tc`.
///
/// # What a failure means
///
/// `waiting:iota(N.rec)` or `waiting:iota(Ix.rec)` — the ι site is refusing a
/// major that had to reduce, which is the `major2 == major` guard back.
/// `waiting:no-endpoint` — a congruence's endpoint has stopped being recorded.
#[test]
fn a_constructor_abbreviation_certifies_at_a_recursor_use_site() {
    let out = run("ctor_abbrev_major.ndjson");

    let el = elim(&out);
    for name in ["N", "Tag", "Ix", "Eq"] {
        assert_eq!(
            el.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    let e = evidence(&out);
    assert_eq!(e.get("pairs"), Some(&32), "the fixture's pair population changed:\n{out}");
    assert_eq!(
        e.get("constEv"),
        Some(&32),
        "every pair must carry `⊢ ⟦c.{{σ}}⟧ ∈ ⟦ty[σ]⟧`; see the table above for which \
         fix each shortfall names:\n{out}"
    );
    assert_eq!(e.get("typeEv"), Some(&32), "every type typing lands too:\n{out}");
    assert_eq!(waiting(&out), BTreeMap::new(), "nothing is waiting on anything:\n{out}");
    assert_eq!(e.get("unsealed"), Some(&0), "nothing persists with a hypothesis:\n{out}");
    assert_eq!(
        row(&out, "convs").get("gapped"),
        Some(&0),
        "**zero**, not merely small: the ι rules are `Eq.refl _`, so a conversion that \
         does not certify is one mini could not state:\n{out}"
    );
    assert_eq!(
        row(&out, "untranslated").get("declarations"),
        Some(&0),
        "both families translate whole:\n{out}"
    );
}

// ──────────────────────────── a field in `U₀` whose Lean sort is not `Prop` ──

/// **A data field still denotes `•` when its own carrier is in `U₀`** —
/// `nanoda_lib::mini::proj_prop::field_in_u0`'s *second* route, end to end.
///
/// `INTERP-AUDIT.md` L4. The rung premise `Pⱼ = ⟦βⱼ⟧ ⊆ 1` has two sources: the
/// field's inferred sort being `⟦Prop⟧` (route 1, `SCOPING.md` §6.2's own
/// wording) and the field type's own declaration's `⊢ ⟦βⱼ⟧ ∈ U₀` moved back
/// along `beta_spine` (route 2). Route 2 is strictly weaker, L4 kept it rather
/// than gating on `is_prop_ev`, and **no corpus member is in the cell where
/// they disagree**. `field_in_u0_by_carrier.lean` is, and its header carries
/// the argument.
///
/// # Why this reads terms and not counts
///
/// Under L4's option B — gate the route on `is_prop_ev` — `W.u` and `Mixed.u`
/// would route to `crate::proj_data` and answer `πⱼ(z)`, and **every pair here
/// would still derive**, because `proj_data` supplies a well-typed term for the
/// projection of a class-(T) structure. `constEv` is blind to the choice, so
/// the oracle is [`theorem_lines`]. `all_derived` is asserted too, but as
/// non-vacuity: it says the file was walked, not that the route was taken.
///
/// # Reading the three `defeq` lines
///
/// `⟦Tru.triv.{}⟧` **is** `•`: the dump names a term by a constant that denotes
/// it, and `Tru.triv` is a proof. So
///
/// ```text
/// W.u      = f?(•, ⟦W⟧)             λ z. •      route 2
/// Mixed.u  = f?(•, ⟦Mixed⟧, ⟦Sort 0⟧)   λα. λ z. •      routes 1 and 2
/// Mixed.a  = f?(⟦Mixed⟧, ⟦Sort 0⟧)      λα. λ z. π₂(z)  neither route
/// ```
///
/// The **`•` argument** is what carries the meaning, and it is
/// `Interp::lam_site`'s own invariant: the body is abstracted to a skeleton
/// over the binder, and every maximal subterm not mentioning the binder becomes
/// a hole passed to the site's symbol. A body that is the point mentions the
/// binder nowhere, so it is one whole hole and `•` is passed in; a body that is
/// `π₂(z)` has no hole and lives inside the symbol's own defining axiom. The
/// trailing `⟦Sort 0⟧` on the two `Mixed` rows is the parameter binder's
/// domain, which is why they are one argument longer than `W.u`'s — and it
/// cancels in the last assertion, which is the same claim with `Mixed`'s two
/// rows compared against each other rather than against a literal.
///
/// Symbol *numbers* are masked to `f?`: they are minting order, and a symbol
/// added anywhere earlier would renumber them without changing a fact.
///
/// # `Mixed`'s parameter is what makes route 1 load-bearing, and that was measured
///
/// A projection at index `j` is owed `P₀ ∧ … ∧ Pⱼ`, so `Mixed.u` at index 1
/// needs rung 0 as well as its own. **Rung 0 is the parameter `α` and not a
/// closed `Prop`, because the first draft used `p : Tru` and the route-1
/// mutation stayed green**: `whnf` of a closed `Prop` is a `Const` application,
/// so route 2 answers it out of `Tru`'s own `ClassS::in_u0` and route 1 is
/// never reached. A parameter has no declaration to consult. That is also the
/// corpus's shape — `And a b`'s field types are its parameters — and it is why
/// route 1 exists at all.
///
/// `Mixed.p` is deliberately not an oracle: a function into a `Prop` is itself
/// a `Prop`, so `⟦Mixed.p⟧` is `•` by proof irrelevance whatever the projection
/// clause did.
///
/// # The witness is level-polymorphic, and that is not cosmetic
///
/// `zoneb::provably_nonzero` reads the declaration's own resultant level
/// *expression*, so `PU.{u} : Sort u` is class (S) at every σ — `props`,
/// carrying `ClassS::in_u0`, which is what route 2 reads. A ground
/// `inductive PU : Type 0` is class (T), lands in `decls`, and routes to
/// `proj_data` instead; it was tried first and failed for exactly that. Pinned
/// here by `elim`, which says `PU` is large-eliminating and that Lean agrees.
#[test]
fn a_data_field_whose_carrier_is_in_u0_denotes_the_point() {
    let out = run("field_in_u0_by_carrier.ndjson");
    // Non-vacuity, and the reason the header gives: this says the fixture was
    // walked whole, not that either route was taken.
    all_derived(&out, 8);
    let e = elim(&out);
    for n in ["PU", "W", "Mixed"] {
        assert_eq!(e.get(n), Some(&(true, true)), "{n}'s eliminator class must agree:\n{out}");
    }
    // Four `Expr::Proj` clauses: `W.u`, and `Mixed`'s three. A fixture that
    // stopped exporting the generated projection functions would still derive
    // its eight pairs and measure nothing.
    assert_eq!(row(&out, "clauses").get("proj"), Some(&4), "four projections:\n{out}");

    // `f<n>` is minting order; the arity and the arguments are the claim.
    fn mask(l: &str) -> String {
        let mut s = String::new();
        let mut it = l.chars().peekable();
        while let Some(c) = it.next() {
            s.push(c);
            if c != 'f' {
                continue
            }
            let mut any = false;
            while it.peek().is_some_and(char::is_ascii_digit) {
                it.next();
                any = true;
            }
            if any {
                s.push('?');
            }
        }
        s
    }
    let defeq = |decl: &str| -> String {
        let ls = theorem_lines("field_in_u0_by_carrier.ndjson", decl);
        ls.iter()
            .find(|l| l.starts_with("defeq "))
            .unwrap_or_else(|| panic!("no `defeq` line for {decl}: {ls:#?}"))
            .clone()
    };
    let (wu, mu, ma) = (defeq("W.u"), defeq("Mixed.u"), defeq("Mixed.a"));

    // **Route 2, at L4's own witness.** `λ z ∈ ⟦W⟧. •`.
    assert_eq!(
        mask(&wu),
        "defeq ⊢ ⟦W.u.{}⟧ = f?(⟦Tru.triv.{}⟧, ⟦W.{}⟧)",
        "L4's witness no longer projects to `•`. If this reads `f?(⟦W.{{}}⟧)` the second \
         route of `proj_prop::field_in_u0` has stopped firing and `proj_data` answered \
         instead — read the fixture header before changing this."
    );
    // **Both routes at once**, at index 1 over a parameter field. The extra
    // `⟦Sort 0⟧` is the parameter binder's own domain: `Mixed.u` is
    // `λ α ∈ ⟦Prop⟧. λ z ∈ ⟦Mixed α⟧. •`, so the site has one more hole than
    // `W.u`'s.
    assert_eq!(
        mask(&mu),
        "defeq ⊢ ⟦Mixed.u.{}⟧ = f?(⟦Tru.triv.{}⟧, ⟦Mixed.{}⟧, ⟦Sort 0⟧)",
        "`Mixed.u` needs route 1 for rung 0 and route 2 for rung 1; one of them stopped."
    );
    // **Neither route**, which is what makes the two above falsifiable.
    assert_eq!(
        mask(&ma),
        "defeq ⊢ ⟦Mixed.a.{}⟧ = f?(⟦Mixed.{}⟧, ⟦Sort 0⟧)",
        "a genuine data field must project to a *value*. If this grew a `⟦Tru.triv.{{}}⟧` \
         argument then `⟦Two⟧ ⊆ 1` was discharged, which is false."
    );
    // The whole claim in one line: over the *same* structure, at two adjacent
    // field indices, the two rows differ by exactly the `•` argument — which is
    // the hole the constant body occupies and the data body does not.
    assert_eq!(
        mask(&ma),
        mask(&mu).replace("Mixed.u", "Mixed.a").replacen("⟦Tru.triv.{}⟧, ", "", 1),
        "the point row and the value row must differ in the point and nowhere else:\n\
         {mu}\n{ma}"
    );
}

// ──────────────────────────────────────────────────────────── projections ──

/// **A projection whose subject has to reduce before the ι step fires.**
///
/// `nanoda_lib::mini::kernel`'s `whnf` reduced a projection's subject with the
/// acceptance-only `self.whnf(s)`, which threads no certificate, and then
/// guarded the whole computation rule on `s2 == s` — *the subject was already
/// a constructor application*. `proj_data::iota`'s header called the decline
/// unreachable, on the evidence that `093_projRed`'s subject satisfies the
/// guard and no corpus member exercises it.
///
/// Both halves of that were true; the conclusion was not. **Every** projection
/// Lean's structural-recursion compiler emits takes the decline — `Nat.brecOn`
/// is literally `(Nat.brecOn.go motive t F).1` — and the corpus's one
/// hand-written projection stood in for the clause.
///
/// # The fixture was red, and this is what it read
///
/// `proj_reduced_subject` at `HEAD~`: `constEv 6/10`,
/// `waiting:proj(Pair) = 4`. The four are `defFst`, `defSnd`, `recFst`,
/// `nestedFst` — every cell whose subject is not already `Pair.mk …` — and the
/// two `ctorFst`/`ctorSnd` cells that certified are the control the guard
/// admitted.
///
/// The assertion is `all_derived`, which pins the **reason set** as empty and
/// not merely the count: a route that certified these four by some other means
/// while leaving a new gap behind would fail here rather than pass.
#[test]
fn a_projection_certifies_when_its_subject_has_to_reduce_to_a_constructor() {
    let out = run("proj_reduced_subject.ndjson");
    // 10 pairs: `mk2`, `pick`, `Pair.fst`, `Pair.snd` and the six theorems.
    all_derived(&out, 10);
}

/// **A projection whose subject reduces and *stays stuck*** — the sibling of
/// the case above, and the exit the case above did not have.
///
/// `whnf`'s `Expr::Proj` arm has four exits after it reduces the subject. One
/// fires ι and hands the subject's reduction to `proj_data::iota`, which
/// composes it in front of the computation rule. The other three — the reduct's
/// head is not a constant, the projected type is not an inductive, the head is
/// not the declaration's single constructor — `done!`d the **changed**
/// expression `proj[T,j] s₂` while leaving `acc.ev` at the certificate for the
/// unreduced `proj[T,j] s`. `whnf_conv`'s contract is that `acc.ev`'s right
/// endpoint is `⟦acc.to⟧`; there it was the left one.
///
/// Nothing rejects on that — the theorem is *true*, it is stated about the
/// wrong term — so the cost falls entirely on consumers that check their
/// endpoints. `proj_data::proj_congr` is the one that does.
///
/// # Red, and this is what it read
///
/// At `HEAD~`: `constEv 10/13`, `waiting:proj(Tri) = 3`, 24 gapped conversions.
/// Here: **13/13, zero gapped**. The three are `stuckOne`, `stuckTwo`,
/// `stuckThd` — the cells whose two sides reach the identical stuck reduct from
/// two different spellings — and `ctorTwo` plus the three `flip` cells are the
/// control: they take the same exit and were already agreeing, because *both*
/// sides were stale by the same amount.
///
/// # Not about `PProd`, and the label says so itself
///
/// `Gap::StructProj` renders as `proj({name})` with whatever structure the
/// projection was on. The Nat bridge read `proj(PProd)`; this fixture reads
/// `proj(Tri)` out of a structure it declares itself, and the export contains
/// neither `Nat` nor `PProd` — checked below rather than claimed.
///
/// # Why the `flip` cells are not decoration
///
/// They certify before the fix *and* after it, so they pin nothing on their
/// own — but the leg the fix composes runs through them, and it is indexed.
/// `flip` repacks `sel`'s three fields in reverse, so the two indices across
/// `flipOne`/`flipTwo`/`flipThd` differ by `+2`, `0` and `−2`. A congruence
/// built at a fixed wrong index, or at the subject's index rather than the
/// projection's, is a true equation about the wrong field.
///
/// **Measured**: the `index-zero` mutation — `stuck_leg` at `0` rather than at
/// `*idx` — takes this fixture to `9/13` with `conv-compose(trans) = 4`, and
/// leaves `nat_char_equations` at `38/38` and `proj_reduced_carrier` at
/// `24/24` **untouched**, because every projection either of those takes is at
/// index 0 and the mutation is the identity there. This file is the only thing
/// in the suite that kills it, and two fields would not have: at `k = 2` the
/// one available wrong index is the other field, and `flip` would have nothing
/// to permute.
#[test]
fn a_projection_certifies_when_its_subject_reduces_and_stays_stuck() {
    let out = run("proj_stuck_subject.ndjson");
    // 13 pairs: `sel`, `selAlias`, `flip`, `Tri.one`, `Tri.two`, `Tri.thd` and
    // the seven theorems.
    all_derived(&out, 13);
    // The **conversion** census, not only the pair count: the three exits are
    // reached by every cell in the file, and a fix that certified the three
    // pairs by some other route while leaving the exits stale would pass
    // `all_derived` and fail here.
    let convs = row(&out, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
    // The claim the fixture exists to make, checked rather than asserted.
    let text = std::fs::read_to_string(fixture("proj_stuck_subject.ndjson")).expect("read");
    assert!(
        !text.split_whitespace().any(|w| w == "Nat" || w == "PProd"),
        "`Nat` or `PProd` reached the export; the fixture no longer shows the defect is \
         about neither"
    );
}

/// **A projection whose structure has to be computed** — the `brecOn` nest,
/// with no `Nat` in it.
///
/// `NAT-BRIDGE-FEASIBILITY.md` §2.3 blocked `Nat.add`'s value on
/// `proj(PProd)` and §6.1 left *why* open, with the obvious hypothesis already
/// refuted: a projection out of a `Nat.below`-typed subject certifies in
/// isolation and `080_PProd.snd`/`081_PSigma.snd` certify, so it is neither
/// `PProd` nor `below`. This fixture answers it, and the answer has nothing to
/// do with `Nat`: the fixture declares its own Peano type and the export
/// contains the name `Nat` **nowhere**, which is asserted below rather than
/// claimed.
///
/// Two causes, both in `proj_data::typing`, both fixed:
///
/// 1. the structure's parameter memberships were handed to
///    `Interp::beta_spine` straight out of `infer_type`, and it compares each
///    premise's set against the nest's domain on the nose — `N.below`'s
///    reduct leaves `N.rec … k` in a parameter position, whose inferred type
///    is the redex `(fun _ => Type) k` against a declared `Sort 1`;
/// 2. the subject's membership never travelled to the reduced type, because
///    the route read the structure's identity off the acceptance-only
///    `c.whnf(&te.ty)`.
///
/// # The numbers, measured at every state
///
/// | state | `constEv` | waiting |
/// | --- | --- | --- |
/// | before | 14/24 | `proj(PProd) = 10` |
/// | (1) alone | 14/24 | `proj(PProd) = 10` |
/// | (1) + (2) | 17/24 | `proj(PProd) = 7` |
/// | (2) + (3), **without** (1) | 14/24 | `proj(PProd) = 10` |
/// | (1) + (2) + (3) | **21/24** | `proj(PProd) = 3` |
///
/// **Neither (1) nor (2) pays anything alone, and each is necessary.** The
/// fourth row is the mutation `param-mems-unconverted` — the whole fix with
/// only the parameter conversion reverted — and it falls all the way back to
/// the pre-fix number, so the parameter conversion is load-bearing even though
/// adding it first moved nothing.
///
/// *(Corrected. `68ed247`'s commit message reports this row as "17/24 with the
/// subject's membership alone", which was inferred from the other three and
/// not measured. It is 14/24. The mutation is the measurement.)*
///
/// # It was slow, and the residue is what made it slow
///
/// *(Rewritten. This note read "ten minutes in a debug build, against 4.5 s
/// before — 40 271 conversions become 4 369 255", and the test carried an
/// `#[ignore]` on that figure. Both were true of the state where three pairs
/// still gapped. With the stuck-subject exits composing their leg the file is
/// **21 s and 131 419 conversions**, a 33× drop, because a certified reduction
/// lets the walk stop where it used to keep looking — and the `#[ignore]` is
/// gone with it. The standing cost note in `MINI-HANDOFF.md` §40 about
/// `infer_type` not being cached still holds; it was not the whole story
/// here.)*
#[test]
fn a_projection_certifies_when_its_carrier_has_to_be_computed() {
    let out = run("proj_reduced_carrier.ndjson");
    // 24 pairs, and **all of them**. 14 is the number before `68ed247`, 17 is
    // that fix with the parameter conversion reverted, and 21 is it complete
    // but with `whnf`'s stuck-projection exits still handing back the reduct
    // with the unreduced expression's certificate.
    all_derived(&out, 24);
    let convs = row(&out, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
    // The claim the fixture exists to make, checked rather than asserted.
    let text = std::fs::read_to_string(fixture("proj_reduced_carrier.ndjson")).expect("read");
    assert!(
        !text.split_whitespace().any(|w| w == "Nat"),
        "`Nat` reached the export; the fixture no longer shows the defect is Nat-free"
    );
}

/// **A recursor whose major reduces and stays stuck.**
///
/// `whnf`'s recursor arm reduces the major and then either fires ι or gives
/// up. The giving-up branch minted `Gap::StuckRecursor` whenever the major had
/// moved, because — it said — *"the major's own reduction is not threaded (it
/// is the acceptance-only `whnf` above)"*. That was true when written and
/// stopped being true when the `whnf` above became `whnf_conv`: the ι arm
/// forty lines up already composes the major's conversion through
/// `Checker::spine_cong`, and this arm went on declining for a repaired
/// reason. Code and comment drifted, and **no corpus declaration reaches the
/// branch** — its own note records `0` mints over all 91 exports, which is why
/// nothing caught it.
///
/// # Red, and this is what it read
///
/// At `HEAD~`: `constEv 3/5`, `waiting:stuck-recursor(N.rec) = 2`, and 22
/// gapped conversions. Here: **5/5, zero gapped**, and the file exits `0`.
///
/// # Why not `nested_model`
///
/// `nested_model.ndjson` reaches the branch 3 214 times and is where the
/// nested seat found it, so it looks like the natural regression. It is not a
/// usable one: with the certificate actually built it needs more than the 4 GB
/// the project caps checker runs at, and it aborts. Measured — the unfixed
/// build completes at 3.6 GB and 30 617 648 conversions, the fixed one dies.
/// This fixture reaches the same branch in 8 522 conversions, and the delta
/// against the unfixed build is 9 %, so the memory is `nested_model`'s scale
/// rather than this branch's cost.
///
/// # `outerTwice` is not decoration
///
/// The major moves **twice** there. With one level a composed chain and a
/// single congruence are indistinguishable, which is the standing reason this
/// project wants three elements wherever a count could stand in for an axis.
#[test]
fn a_recursor_certifies_when_its_major_reduces_and_stays_stuck() {
    let out = run("stuck_recursor_major.ndjson");
    // 5 pairs: `dbl`, `outer`, `outerTwice` and the two equations.
    all_derived(&out, 5);
    // The **conversion** census, not only the pair count: the branch is reached
    // 22 times and every one of them used to be a gap, so a fix that certified
    // the two pairs by some other route while leaving the branch gapping would
    // pass `all_derived` and fail here.
    let convs = row(&out, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
}

/// **An indexed family with two parameters — the cell `index_congr` is never
/// reached at, and the guard's blind spot measured there.**
///
/// `ctor_ix::index_congr` checks each *index* against the term inference
/// produced and puts the **parameters at `Thm::eq_refl`** (`ctor_ix.rs:913`),
/// so it cannot itself see a wrong parameter: both sides of the congruence
/// carry the same wrong `p⃗` and the equation is well formed. That is a real
/// gap in the one guard the whole confluence idea is modelled on, and the
/// question it raises is whether anything else catches it.
///
/// **It does, and this fixture is what let it be asked.** Measured as
/// mutations, at both cells:
///
/// | mutation | where | `constEv` |
/// | --- | --- | --- |
/// | `param-subst` (an index term into parameter slot 0) | `077_RBTree.id_spec`, `np = 1` | 3/3 → **1/3** |
/// | `param-swap` (exchange the two parameters) | this fixture, `np = 2` | 2/2 → **0/2** |
///
/// Both die at the *consumers*: a wrong `p⃗` makes both endpoints of the
/// congruence wrong, and `retarget_set(&mem, &cong)` requires `cong`'s
/// left-hand side to be the set `mem` already holds — where `mem` comes from
/// `IndexedCtor::mem` instantiated at the true arguments. That is the
/// independent second route, and it already exists. **A parameter check inside
/// `index_congr` would be dead weight**, undistinguishable by either mutation,
/// which is why none was added.
///
/// # Why the corpus could not answer this
///
/// `scripts/arm-coverage.py` reports 35 indexed declarations and none at
/// `np = 0`, which reads as good parameter coverage. At the **guard** it is not:
/// instrumenting `index_congr` over all 91 exports, it is reached by *exactly
/// one*, `077_RBTree.id_spec`, and only at `np = 1` — 69 calls, 3 at `nx = 0`,
/// 3 at `nx = 1`, 63 at `nx = 2`. The corpus's thirty `np = 2` indexed
/// declarations are all `Eq`, which never takes this route.
///
/// So a swap is a **no-op on the whole corpus**: there are never two parameters
/// to swap where the guard runs. A first draft ran exactly that mutation,
/// watched it survive on six exports, and would have reported a hole. The
/// survival was vacuous, and the reachability count is what caught it — which
/// is the reason this test asserts the fixture reaches `np = 2` at all rather
/// than only that it certifies.
#[test]
fn an_indexed_family_with_two_parameters_certifies() {
    let out = run("indexed_two_params.ndjson");
    // `ixMk` and `ixStep`; the inductives open no pair of their own.
    all_derived(&out, 2);
    // **The non-vacuity pin.** `Ix` must still be `np = 2, ni = 1` — Lean's
    // `fixedIndicesToParams` promotes an index that is the same variable
    // everywhere, and a promotion here would leave a fixture that reaches the
    // `np = 2` arm with nothing indexed and measures nothing.
    let ar = decl_arity("indexed_two_params.ndjson");
    assert_eq!(
        ar.get("Ix").map(|&(np, ni, _)| (np, ni)),
        Some((2, 1)),
        "Ix is no longer a two-parameter indexed family; the cell is gone:\n{ar:#?}"
    );
}

/// **Reducing a proof is reflexivity, and the walk has to say so** —
/// `Checker::proof_point_leg`'s regression, at 8 393 conversions.
///
/// §6.2 sends a proof-valued application to `•`, so `Checker::split_app`
/// cannot peel it and every endpoint after the first `App` node of a
/// proof-valued spine is lost. The walk then files a `no-endpoint` at whichever
/// step comes next — `delta_evidence`'s first line, `beta_evidence`'s, the
/// stuck-recursor arm's `spine_cong` inputs — and **all three are correct
/// reports of an absence decided upstream**. What is wrong is the absence:
/// `⟦e⟧` and `⟦whnf e⟧` are both `•`.
///
/// The fixture's own header says which three ingredients have to be present at
/// once and which neighbouring file has which two. The one that is only here is
/// that the **conversion is consumed**: `twoProofs`'s left side is a `def`, so
/// the two sides are not the same expression and `def_eq_struct`'s `App`
/// reflexivity arm (`#90(b)`) cannot answer for them.
///
/// Measured both ways on this file, with the leg disabled behind an
/// environment variable in one binary:
///
/// ```text
///                  constEv   conversions   gapped
/// without the leg    4/5          8 130       11    waiting:no-endpoint=1
/// with it            5/5          8 393        0
/// ```
///
/// The conversion count **rises** and that is the walk getting further: eleven
/// conversions that used to stop now compose, and what they compose is counted.
///
/// The big witness is `nested_model.ndjson`, whose `iotaNode` is this shape with
/// the nesting on — `treeRec … (treeNode l)` δι-reduces to a transport along
/// `packUnpack (pack l)` where the theorem states one along
/// `congrPack (unpack (pack l)) l (unpackPack l)`. That file is 3.1 million
/// conversions and 39/41 constant typings before this leg and **41/41** after
/// it; `mini/src/eq_cash.rs`'s model table is where it is asserted.
#[test]
fn reducing_a_proof_is_reflexivity_and_the_walk_says_so() {
    let out = run("whnf_of_a_proof.ndjson");
    // `myCongr`, `sameEq`, `altCongr`, `moveA`, `twoProofs`; the two inductives
    // open no pair of their own.
    all_derived(&out, 5);
    // **The conversion census, not only the pair count.** Eleven conversions
    // used to gap here and the pair count alone cannot see them: a repair that
    // certified `twoProofs` by some other route while leaving the proof-valued
    // walk gapping would pass `all_derived` and fail this.
    let convs = row(&out, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
    // …and the file is not clean by having stopped *doing* anything: the whole
    // point is that `twoProofs`' two sides are different expressions, so the
    // conversion has to move.
    assert!(
        convs.get("moved").copied().unwrap_or(0) > 0,
        "the fixture performs no non-trivial conversion, so the assertions above are about a \
         walk that no longer happens:\n{out}"
    );
}

/// **An unused non-standard axiom is ignored; a used one still declines** —
/// both polarities, and neither means anything without the other.
///
/// `nanoda_lib::mini::convert::is_standard_axiom` used to take **any** file declaring a user
/// axiom out of scope, and that single line is what held `init-prelude`: it declares
/// `sorryAx`, **nothing in it uses `sorryAx`**, and the decline landed *after*
/// 1 459 declarations and 3 078 scheduled pairs had already come through
/// `convert::load`. `nanoda_lib::mini::unused_axiom` narrows the rule to the axioms
/// something in the file actually refers to, and states why that is a narrowing
/// and not a reversal.
///
/// # What each half rules out
///
/// `unused_axiom_ignored.ndjson` is passed by a checker that ignores **every**
/// axiom; `used_axiom_declines.ndjson` is passed by one that ignores **none**.
/// Between them:
///
/// | wrong implementation | which half fails, and how |
/// | --- | --- |
/// | the old rule — decline on the first non-standard axiom | the ignored half declines; the used half reports `spareAx` instead of `usedOnlyInAValue` |
/// | ignore every non-standard axiom | the used half is **accepted** — the must-kill |
/// | treat a used axiom as unused | the same |
/// | a walk that reads declarations' types but not their values | the same, because `usedOnlyInAValue` occurs only in `viaValue`'s value |
/// | report only the first ignored axiom | the ignored half's verdict column and `ignoredAxioms=2` |
/// | ignore the axiom but let it keep its pair | `pairs` on the ignored half |
///
/// # The visible-skip half
///
/// `#64`'s lesson is that *a declined declaration with no scheduled pair is
/// invisible*, and an ignored axiom has no pair **by construction** — every
/// counter in the ledger is indexed by one. So the verdict line carries the
/// names and the `ledger` row carries the count, and both are asserted here.
/// Exit `0` is asserted too, and deliberately: `Uncertified` and `Untranslated`
/// are obligations mini *owes*, and nothing in the file rests on either axiom.
///
/// # `5 declarations` became `3`, and that is the waived property
///
/// The drop used to happen *after* the kernel pass, so the two ignored axioms
/// were checked and counted and only then withheld from the interpretation.
/// `nanoda_lib::mini::decl_pass` runs one per-declaration loop, and
/// `unused_axiom::classify` reads the declaration list and no environment — so
/// the drop is ahead of the loop and the axioms are never added at all. The
/// owner waived the property that went with the old position ("it will not
/// complain about the type of a dropped axiom; that's not a concern") and
/// [`an_unused_axiom_may_now_be_illtyped`] is that waiver as a fixture.
///
/// The count on the verdict line is the number of declarations zone A checked,
/// so it has to be **3**: saying 5 would claim two checks that did not happen.
/// Both halves of the visible-skip requirement are unchanged — the names are on
/// the verdict line and the count is in the ledger.
#[test]
fn an_unused_axiom_is_ignored_and_a_used_one_still_declines() {
    fn raw(name: &str) -> (Option<i32>, String) {
        let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
            .arg("--no-modelgen")
            .arg("--verbose")
            .arg(fixture(name))
            .output()
            .expect("spawn mini");
        (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
    }

    // ── in scope, and the skip is visible ────────────────────────────────
    let (code, out) = raw("unused_axiom_ignored.ndjson");
    let v = out.lines().next().unwrap_or_default().to_string();
    assert_eq!(
        code,
        Some(0),
        "an unused non-standard axiom must not take the file out of scope, and must not be \
         debt either:\n{out}"
    );
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec![
            "unused_axiom_ignored.ndjson",
            "accept",
            "3 declarations",
            "ignored axioms: unusedProp, unusedRel"
        ],
        "the ignored axioms must be **named** on the verdict line — a count alone would let a \
         reader think the file is a file with nothing missing from it:\n{out}"
    );
    let l = row(&out, "ledger");
    assert_eq!(l.get("ignoredAxioms"), Some(&2), "both must be counted in the ledger:\n{out}");
    assert!(
        out.lines().any(|x| x.contains("\tignored:unusedProp=1"))
            && out.lines().any(|x| x.contains("\tignored:unusedRel=1")),
        "…and named there too:\n{out}"
    );
    // **No pair, and this is the half that says "not translated".** `N` opens
    // none (an inductive schedules no pair) and `nZero`/`nSucc` open one each,
    // so an axiom that kept its pair would read 4.
    assert_eq!(l.get("pairs"), Some(&2), "an ignored axiom must schedule no pair:\n{out}");
    assert_eq!(l.get("declars"), Some(&3), "…and must not be walked at all:\n{out}");
    let e = evidence(&out);
    assert_eq!(e.get("constEv"), Some(&2), "and the rest of the file still certifies:\n{out}");

    // ── out of scope, exactly as before ──────────────────────────────────
    let (code, out) = raw("used_axiom_declines.ndjson");
    let v = out.lines().next().unwrap_or_default().to_string();
    assert_eq!(code, Some(2), "a **used** non-standard axiom is still an arena decline:\n{out}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec![
            "used_axiom_declines.ndjson",
            "decline",
            "non-standard axiom: usedOnlyInAValue"
        ],
        "the reason must name the axiom that is **used**, not the first one declared:\n{out}"
    );
    assert!(
        !v.contains("spareAx") && !v.contains("alsoSpare"),
        "reporting an unused axiom as the reason is the old rule, unnarrowed:\n{out}"
    );
}

/// **The one property the fused pipeline gives up, as a fixture** — an unused
/// non-standard axiom whose *type* does not typecheck is now accepted.
///
/// `unused_axiom_illtyped.ndjson` declares `axiom badAx : Prop Prop`, which is
/// `Sort 0` applied to `Sort 0` and infers nothing, and one definition that does
/// not mention it. Under the old pipeline the whole file went through
/// `kernel::add` first and the drop came after, so mini **rejected** it:
///
/// ```text
/// reject  badAx
/// Expected a function type in application of Sort 0 to Sort 0, got Sort (0+1)
/// ```
///
/// `nanoda_lib::mini::unused_axiom::classify` reads the declaration list and no
/// environment, so in a per-declaration pipeline it belongs ahead of the loop
/// and the axiom is never added. The owner waived the lost rejection
/// explicitly: *"yes, it will not complain about the type of a dropped axiom;
/// that's not a concern."*
///
/// **This is a fixture and not a note, because a lost rejection is a
/// measurement.** It is red on the old pipeline (`reject`, exit 1) and green on
/// the new one, so if the drop ever moves back behind the kernel the test says
/// which behaviour changed rather than leaving a silent difference. The
/// mutation is the same statement read the other way: move
/// `unused_axiom::classify`'s `retain` after the loop and this goes red.
///
/// The skip is still **visible**, which is what keeps the waiver from being a
/// hole: the axiom is named on the verdict line and counted in the ledger, so a
/// reader sees that the file declares a symbol mini looked at and did not check.
#[test]
fn an_unused_axiom_may_now_be_illtyped() {
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg(fixture("unused_axiom_illtyped.ndjson"))
        .output()
        .expect("spawn mini");
    let code = out.status.code();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let v = stdout.lines().next().unwrap_or_default().to_string();
    assert_eq!(
        code,
        Some(0),
        "an unused non-standard axiom is dropped before the loop, so its type is never \
         checked and the file is accepted:\n{stdout}"
    );
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec![
            "unused_axiom_illtyped.ndjson",
            "accept",
            "1 declarations",
            "ignored axioms: badAx"
        ],
        "…and the skip stays visible — the count is the declarations zone A actually \
         checked, and the axiom is named:\n{stdout}"
    );
    let l = row(&stdout, "ledger");
    assert_eq!(l.get("ignoredAxioms"), Some(&1), "the ledger counts it too:\n{stdout}");
    // **The rest of the file still certifies.** Without this the test would pass
    // for a run that dropped everything.
    assert_eq!(evidence(&stdout).get("constEv"), Some(&1), "the definition still certifies:\n{stdout}");
}

// ────────────────────────────── monomorphization, and what it may rewrite ──

/// **A subsingleton at a ground nonzero sort keeps the class-(S) carrier.**
///
/// `ground_unit_subsingleton.lean`. `zoneb::build`'s trichotomy used to ask
/// `provably_nonzero` on the declaration's own level expression *first*, so
/// `U1 : Type` — one constructor, no fields — took the class-(T) W branch and
/// with it lost the `LeProp` that `unit_like` and `proj_prop::field_in_u0`'s
/// second route consume. Measured against that code this fixture reports
/// `waiting:unit-like(U1)=1` and `gapped=4`; the branch is `zoneb::subsingleton`
/// now, which is structural, and it derives.
///
/// **The controls are the assertion, not decoration.** `all_derived` is what
/// says the narrowing held: `EmptyG` (no constructors) and `RecU` (one
/// recursive field) are subsingletons by Carneiro §2.6.2 reason 2 and must
/// *not* be preferred to class (T), because `class_s` has no `LeProp` for
/// either — widen the preference past
/// [`collapsed_subsingleton`](nanoda_lib::mini::zoneb::collapsed_subsingleton) and this
/// file reports `recursor(EmptyG: class (S) eliminator: no constructors)` and
/// `ind-spec(RecU: class (S): recursive constructor)` before the corpus does.
/// `Three` and `Pair2` are the other pair: `U1` differs from `Pair2` in its
/// fields and from `Three` in its constructor count, so neither alone says what
/// the preference is keyed on.
#[test]
fn a_subsingleton_at_a_ground_sort_keeps_the_class_s_carrier() {
    let out = run("ground_unit_subsingleton.ndjson");
    all_derived(&out, 10);
    assert_eq!(
        row(&out, "untranslated").get("eliminators"),
        Some(&0),
        "`EmptyG.rec` is the narrowing's witness: on the class-(S) route it is \
         `CLASS_S_EMPTY` and there is no eliminator at all:\n{out}"
    );
    assert_eq!(
        row(&out, "convs").get("gapped"),
        Some(&0),
        "unit-like η is a *conversion* gap before it is a pair gap, and the four \
         `convGap:unit-like(U1)` conversions are what `102_unitEta1` reports under \
         `monomorph`:\n{out}"
    );
    // Every one of the five declarations is large-eliminating and Lean agrees;
    // the trichotomy is downstream of that and this is the oracle for the
    // half of it that is not being changed.
    let e = elim(&out);
    for n in ["U1", "Three", "Pair2", "EmptyG", "RecU", "WG"] {
        assert_eq!(e.get(n), Some(&(true, true)), "{n}'s eliminator class must agree:\n{out}");
    }

    // **The second route, at a ground unit.** `field_in_u0_by_carrier.lean`'s
    // `W.u` with `PU.{1}` replaced by `U1`, which that fixture's header records
    // as having been "written first and **failed**". `f?(<the point>, ⟦WG⟧)` is
    // `λ z ∈ ⟦WG⟧. •`; if this reads `f?(⟦WG.{}⟧)` the route stopped firing and
    // `proj_data` answered with a projection instead.
    let ls = theorem_lines("ground_unit_subsingleton.ndjson", "WG.u");
    let defeq = ls
        .iter()
        .find(|l| l.starts_with("defeq "))
        .unwrap_or_else(|| panic!("no `defeq` line for WG.u: {ls:#?}"));
    let masked: String = {
        let mut s = String::new();
        let mut it = defeq.chars().peekable();
        while let Some(c) = it.next() {
            s.push(c);
            if c != 'f' {
                continue
            }
            let mut any = false;
            while it.peek().is_some_and(char::is_ascii_digit) {
                it.next();
                any = true;
            }
            if any {
                s.push('?');
            }
        }
        s
    };
    assert_eq!(
        masked, "defeq ⊢ ⟦WG.u.{}⟧ = f?(⟦Eq.refl.{0}⟧, ⟦WG.{}⟧)",
        "the projection of a ground unit field must denote the point:\n{out}"
    );
}

/// **`monomorph`'s output, end to end** — `mono_prefix.ndjson` is the one
/// fixture here that is not `lean4export`'s output (`--#monomorph`, see
/// `scripts/export-fixture.sh`).
///
/// It carries the two decisions `MONOMORPH.md` §4.3 found the pass entitled to
/// rewrite, and measured against the code before the fix it reports all three
/// of
///
/// ```text
/// waiting:ind-spec(_at.1.0.Acc: recursive argument telescope depth)=1
/// waiting:ind-spec(_at.1.1.Acc: recursive argument telescope depth)=1
/// waiting:unit-like(_at.1.1.PU)=1
/// ```
///
/// **Two copies of `Acc`, not one.** `monomorph` emits `_at.1.0.Acc` for the
/// `Prop` instantiation `accRec` defaults to and `_at.1.1.Acc` for the one
/// `accIntro` uses at `PU.{1}`, so the fixture has two names that must both
/// reach `direct::Clause::Acc` and two σ's that must stay distinct. A strip
/// that returned the wrong copy, or one that collapsed the two, is visible
/// here and would not be at a single instantiation.
#[test]
fn a_monomorphized_export_costs_nothing() {
    let out = run("mono_prefix.ndjson");
    all_derived(&out, 5);
    assert_eq!(
        row(&out, "untranslated").get("declarations"),
        Some(&0),
        "an `Acc` the named clause did not reach is declined by the general walk at \
         `Acc.intro`'s depth-2 telescope and counted here:\n{out}"
    );
    // The prefix is *in* the file — a regenerated fixture that lost the
    // `--#monomorph` line would derive its five pairs and measure nothing.
    let e = elim(&out);
    for n in ["_at.1.0.Acc", "_at.1.1.Acc", "_at.1.1.PU"] {
        assert_eq!(
            e.get(n),
            Some(&(true, true)),
            "{n} must be in the export under its monomorphized name — regenerate with \
             `scripts/export-fixture.sh mono_prefix.lean`:\n{out}"
        );
    }
    assert_eq!(
        row(&out, "convs").get("gapped"),
        Some(&0),
        "`_at.1.1.PU`'s η is the conversion half of the second cause:\n{out}"
    );
}

/// **`Quot.lift` of `Quot.mk`, off the corpus** — `quot_lift_reduction.lean`.
///
/// `mini/src/quot_iota.rs`'s ι chain (β down the lift's nest, β down
/// `Quot.mk`'s, then `lift_beta` with both antecedents discharged) had
/// exactly one input anywhere: the gitignored corpus's
/// `124_quotLiftReduction`. When the kernel `Env` moved behind the shared
/// `EnvCore` cell, the chain's composition held one `env_mut()` guard as a
/// statement-long temporary while a closure took a second — a re-entrant
/// borrow, a panic, on this path and no other — and only the corpus ratchet
/// saw it. This fixture is that path as a committed export: red (exit 101)
/// under the re-introduced chained borrow, green as landed.
///
/// The `gapped=0` on the `convs` row is the sharp half: the run not merely
/// surviving the quot ι step but certifying it, so a future regression that
/// *declines* the chain instead of panicking is equally visible.
#[test]
fn quot_lift_of_mk_is_certified_off_the_corpus() {
    let out = run("quot_lift_reduction.ndjson");
    all_derived(&out, 2);
    let convs = row(&out, "convs");
    assert_eq!(convs.get("gapped"), Some(&0), "the quot ι chain must certify:\n{out}");
    assert!(
        convs.get("moved").copied().unwrap_or(0) > 0,
        "no conversion moved — the fixture no longer reaches the quot ι step:\n{out}"
    );
}

// ─────────────────────────────── the fused pipeline: what the loop buys ──

/// **A rejection mid-file certifies everything before it** — the capability the
/// per-declaration loop exists for (`mini/src/decl_pass.rs`).
///
/// The pipeline used to be a whole-file acceptance pass and then a whole-file
/// interpretation pass. Acceptance early-returns at the first rejection, so a
/// file with one bad declaration produced **no certificate at all** — not for
/// the declarations before the bad one, not for anything. `good/init-prelude`
/// is the measured case: it stops 231 declarations into 2059 and certified
/// zero.
///
/// # Three good, one bad, two more
///
/// `reject_midfile_prefix.ndjson` is six definitions, the fourth ill-typed
/// (`def badFour : Prop := Type`). Three before the stop and two after, and
/// both counts are the point: **two atoms cannot tell a prefix from a
/// constant.** With one good declaration before the stop, `certified=1` is also
/// what "certify the first declaration only" produces; with none after, it is
/// also what "certify the whole file" produces. Three and two separate all
/// four readings — 0 (the old pipeline), 1, 3 (the prefix) and 6.
///
/// The verdict, its tag and the exit code are asserted alongside, because the
/// whole restructure is only legal if they did not move: this file rejected at
/// `badFour` with exit 1 before and does now.
#[test]
fn a_rejection_certifies_the_prefix() {
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg(fixture("reject_midfile_prefix.ndjson"))
        .output()
        .expect("spawn mini");
    let code = out.status.code();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(code, Some(1), "the acceptance verdict has not moved:\n{stdout}");
    assert_eq!(
        stdout.lines().next().unwrap_or_default().split('\t').collect::<Vec<_>>(),
        vec!["reject_midfile_prefix.ndjson", "reject", "badFour"],
        "…and it still names the declaration that failed:\n{stdout}"
    );
    let p = row(&stdout, "prefix");
    assert_eq!(
        p.get("declarations"),
        Some(&3),
        "the three declarations before the stop must have been walked — this is 0 on the \
         two-pass pipeline:\n{stdout}"
    );
    assert_eq!(p.get("pairs"), Some(&3), "…one pair each:\n{stdout}");
    assert_eq!(
        p.get("certified"),
        Some(&3),
        "…and a constant typing derived for each, which is what 'certified' means:\n{stdout}"
    );
    // **And not the whole file.** A run that carried on past the rejection
    // would read 6 here and would be certifying declarations mini does not
    // accept.
    assert!(
        p.get("declarations") < Some(&6),
        "the prefix must stop at the rejection, not run through it:\n{stdout}"
    );
    // The certification axis says nothing about a rejected file, and the ledger
    // rows are the observable half of that: `Outcome::ledger` is `None`, so
    // none of them is printed.
    assert!(
        !stdout.lines().any(|l| l.starts_with("ledger\t")),
        "a rejected file must carry no gap ledger — the two axes stay apart:\n{stdout}"
    );
}

/// **A used non-standard axiom declines only when nothing rejected first**, and
/// the rule is *the rejection always wins*, not *the earlier event wins*.
///
/// This is the ordering the fused pipeline had to keep. The decline used to be
/// issued after a completed whole-file kernel pass, which made it lose to a
/// rejection for free. With one loop the axiom is known from the parse, so the
/// decline could have been issued at the top — and four `bad/tutorial` fixtures
/// (044, 047, 050, 054) declare a helper axiom ahead of the ill-typed
/// declaration they are about, so doing that would have turned four rejections
/// into declines: a weaker claim, made silently, on the axis that is supposed
/// to be exact.
///
/// # Three cells, because two cannot tell the rule from its shadow
///
/// | fixture | the axiom sits | verdict |
/// | --- | --- | --- |
/// | `used_axiom_declines` | alone | `decline` |
/// | `used_axiom_before_reject` | **before** the ill-typed declaration | `reject` |
/// | `used_axiom_after_reject` | **after** it | `reject` |
///
/// The first two alone are also satisfied by "whichever comes first wins"; the
/// third is what rules that out. The first is what rules out "never decline".
#[test]
fn a_used_axiom_decline_loses_to_any_rejection() {
    fn verdict(name: &str) -> (Option<i32>, String) {
        let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
            .arg("--no-modelgen")
            .arg(fixture(name))
            .output()
            .expect("spawn mini");
        let s = String::from_utf8_lossy(&out.stdout).to_string();
        (out.status.code(), s.lines().next().unwrap_or_default().to_string())
    }

    let (code, v) = verdict("used_axiom_declines.ndjson");
    assert_eq!(code, Some(2), "a used non-standard axiom on its own is still an arena decline: {v}");
    assert!(v.contains("\tdecline\t"), "{v}");

    let (code, v) = verdict("used_axiom_before_reject.ndjson");
    assert_eq!(code, Some(1), "a rejection after the axiom must win: {v}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec!["used_axiom_before_reject.ndjson", "reject", "badLast"],
        "…and name the ill-typed declaration, not the axiom"
    );

    let (code, v) = verdict("used_axiom_after_reject.ndjson");
    assert_eq!(code, Some(1), "a rejection before the axiom must win too: {v}");
    assert_eq!(
        v.split('\t').collect::<Vec<_>>(),
        vec!["used_axiom_after_reject.ndjson", "reject", "badFirst"],
        "…so the rule is 'a rejection wins', not 'the first event wins'"
    );
}

/// **`Outcome::prefix` and the ledger agree on an accepted file.**
///
/// The prefix counters are read off the same ledger the accepted outcome
/// carries, so on a file that ran to the end they must be that ledger's own
/// `declars`, `pairs` and `constEv`. Asserted because they are two rows a
/// reader will compare, and because a prefix that quietly stopped counting
/// early would otherwise look like a small file.
#[test]
fn the_prefix_agrees_with_the_ledger_on_an_accepted_file() {
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg(fixture("unused_axiom_ignored.ndjson"))
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let p = row(&stdout, "prefix");
    let l = row(&stdout, "ledger");
    let e = evidence(&stdout);
    assert_eq!(p.get("declarations"), l.get("declars"), "prefix vs ledger declars:\n{stdout}");
    assert_eq!(p.get("pairs"), l.get("pairs"), "prefix vs ledger pairs:\n{stdout}");
    assert_eq!(p.get("certified"), e.get("constEv"), "prefix vs evidence constEv:\n{stdout}");
    // Not vacuous: the file does certify something.
    assert!(p.get("certified") > Some(&0), "the fixture certifies nothing:\n{stdout}");
}

/// **`MINI_CONV_TRACE` still names every declaration as the run reaches it.**
///
/// The trace was `Ledger::run`'s loop. `nanoda_lib::mini::decl_pass` fused the pipeline and
/// stopped calling that loop, so the trace went **silent** — and a silent
/// progress trace does not look broken, it looks like a run that has not
/// started yet. It cost most of an hour on `init-prelude` before anyone asked
/// why there were no rows. It lives in `Ledger::walk_decl` now, which every
/// path that walks a declaration goes through, and this is the cell that says
/// so.
///
/// # Three rows, and a fourth that must not be there
///
/// `reject_midfile_prefix.ndjson` is three good definitions, then an ill-typed
/// one, then two more. The trace must carry **`one`, `two`, `three` in that
/// order and stop** — which is four claims a single row cannot make:
///
/// * that it fires at all (the regression above);
/// * that it fires per declaration and not once (one row would satisfy a
///   trace that only ever names the first);
/// * that the order is the file's (three names, not a set);
/// * that it stops at the rejection, so the last row names the last
///   declaration certified — the property the whole trace exists for, and the
///   one that makes an aborted run's tail readable.
#[test]
fn the_conversion_trace_names_each_declaration_as_the_loop_reaches_it() {
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--naive")
        .arg("--no-modelgen")
        .env("MINI_CONV_TRACE", "1")
        .arg(fixture("reject_midfile_prefix.ndjson"))
        .output()
        .expect("spawn mini");
    let err = String::from_utf8_lossy(&out.stderr).to_string();
    let rows: Vec<Vec<&str>> = err
        .lines()
        .filter(|l| l.starts_with("convtrace\t"))
        .map(|l| l.split('\t').collect())
        .collect();
    let named: Vec<&str> = rows.iter().filter_map(|r| r.get(3).copied()).collect();
    assert_eq!(
        named,
        vec!["one", "two", "three"],
        "the trace must name each declaration the loop reaches, in file order, and stop at \
         the rejection:\n{err}"
    );
    // The index is the count of declarations already finished, so the rows are
    // numbered from zero and the last one is the last certified.
    let idx: Vec<&str> = rows.iter().filter_map(|r| r.get(1).copied()).collect();
    assert_eq!(idx, vec!["0", "1", "2"], "the trace index is not the position in the walk:\n{err}");
    assert!(
        rows.iter().all(|r| r.get(2) == Some(&"starting")),
        "the row is emitted before the declaration it names, and says so:\n{err}"
    );
}

// ───────────────────────────────────────────────── Lean's standard axioms ──

/// **`propext` is inhabited, and `Classical.choice` is not.**
///
/// `nanoda_lib::mini::ev::Gap::Axiom` is reached only once the axiom's own *type* has
/// interpreted, and `mini/tests/tutorial.rs` records that on the 91-file corpus
/// the variant is unreachable for exactly that reason — "no axiom's type
/// interprets yet". `standard_axioms.lean` is the smallest export where they
/// do: `Iff` is class (S) and `Nonempty` is class (P), both carriers build, and
/// the two axioms with no clause in `nanoda_lib::mini::axiom` reach the fallback.
///
/// The measurement this test exists to hold is the *split*. Before
/// `nanoda_lib::mini::axiom::Clause::PropExt` the row was
///
/// ```text
/// constEv=1  library-gap=6  waiting:axiom(Classical.choice)=4  waiting:axiom(propext)=2
/// ```
///
/// and the `propext` half is gone. **So is the `Classical.choice` half**, and
/// this file is where the whole arc is recorded, because the paragraph that
/// stood here told the next reader the opposite.
///
/// It said the obstruction was that "`nanoda_lib::mini::ev::Sealed` refuses a hypothetical
/// theorem while `nanoda_lib::mini::ledger` stores `ip.point()` for every inhabited axiom",
/// that this was "an architecture question, not a missing lemma", and that a
/// change closing it "should fail here and be re-read". It did, twice, and this
/// is the re-read. Both halves of the sentence were wrong, in different ways
/// and at different levels:
///
/// * **`Sealed` refuses nothing here.** `kernel::thm::henkin` mints `ε` as a
///   0-ary constant and `derived::choice::Epsilon`'s theorems are
///   hypothesis-free sentences. (What *does* legitimately carry hypotheses is a
///   nest binder's typing — `nanoda_lib::mini::scope` is mini's `assume` module — and those
///   are discharged by `lam_evidence` as the nest closes, exactly as they are
///   for every other clause. A guard that refused them declined every call.)
/// * **`ip.point()` was a real obstruction and only at `u ≥ 1`.** At `u = 0`
///   the codomain `α` *is* a `Prop` and §6.2 gives it `•` like every other
///   proof, so nothing had to move; the obligation is `⊢ • ∈ ⟦α⟧` from
///   `Nonempty`'s class-(P) ladder, with **no `ε` at all**. At `u ≥ 1` the
///   interpretation really is `ε(⟦α⟧)`, and `inhabit` now returns its term and
///   the ledger stores it.
///
/// # The four pairs, and what each half closed
///
/// They were never four σ of one declaration: they are **two σ each of two
/// declarations**, `Classical.choice` and its use site `choiceUse`, at
/// `u := 0` and `u := 1`.
///
/// ```text
/// propext clause     constEv=3  library-gap=4  waiting:axiom(Classical.choice)=4
/// + Clause::Choice   constEv=5  library-gap=2  waiting:axiom(Classical.choice)=2
///   at u = 0
/// + the ε arm        constEv=7  (no library-gap)  (no waiting rows at all)
///   at u ≥ 1
/// ```
///
/// `constEv == pairs` is the assertion that matters now, and it is a stronger
/// statement than any count of what is left: **every pair in this file is
/// certified**, so there is no reason row for a later change to hide behind.
///
/// # Two axioms, not one
///
/// A fixture with `propext` alone would pass under a clause that inhabited
/// *any* axiom whose type interpreted — the failure mode the module header
/// calls "the name is not the evidence", one level up. That argument no longer
/// has this test's silence to rest on, now that both axioms are certified, and
/// it is carried instead by `nanoda_lib::mini::axiom`'s unit tests: an axiom named
/// `Classical.choice` that does not return its own binder, and one whose
/// premise is about another binder, are both declined against a positive
/// control one `Expr` away.
#[test]
fn propext_and_classical_choice_are_both_inhabited() {
    let out = run("standard_axioms.ndjson");
    let e = evidence(&out);
    // Non-vacuity: every *type* interprets, so both axioms really do reach the
    // inhabitation obligation. A fixture whose types stopped interpreting would
    // report the same `constEv` for an entirely different reason.
    assert_eq!(e.get("pairs"), Some(&7), "the pair population changed:\n{out}");
    assert_eq!(e.get("typeEv"), Some(&7), "an axiom's type stopped interpreting:\n{out}");
    // All seven: `propext`, `propextUse`, `trueIff`, and `Classical.choice`
    // and `choiceUse` at both σ.
    assert_eq!(e.get("constEv"), Some(&7), "the derived population changed:\n{out}");
    assert_eq!(e.get("unsealed"), Some(&0), "a nest left a hypothesis undischarged:\n{out}");
    let w = waiting(&out);
    assert!(
        w.is_empty(),
        "every pair in this file is certified; a reason row means one stopped being:\n{out}"
    );
}

/// **What the choice clause derived, not merely that it derived something.**
///
/// Both σ are certified, and they are certified *differently* — that is the
/// claim, and a counter cannot make it. The `u = 0` pair denotes `•`, because
/// its codomain is a `Prop`; the `u = 1` pair denotes `app(ε, ⟦α⟧)`, and the
/// two must not be confused, because a clause that quietly gave the `u = 1`
/// pair the point would move `constEv` exactly the same way and store a
/// denotation the membership is not about.
///
/// Each typing must also mention the premise's own type former, so a clause
/// that certified the axiom against some other set is caught here.
#[test]
fn the_choice_clause_certifies_both_levels_and_they_denote_differently() {
    let lines = theorem_lines("standard_axioms.ndjson", "Classical.choice");
    let typing: Vec<&String> = lines.iter().filter(|l| l.starts_with("typing ")).collect();
    assert_eq!(typing.len(), 2, "Classical.choice has two pairs, u := 0 and u := 1: {lines:?}");
    for t in &typing {
        assert!(!t.contains("waiting on"), "a Classical.choice pair is a gap again: {t}");
    }
    for want in ["⟦Nonempty.{0}⟧", "⟦Nonempty.{1}⟧"] {
        assert!(
            typing.iter().any(|t| t.contains(want)),
            "no typing is about {want} — the clause is not reading its own premise: {typing:?}"
        );
    }

    // **And the two denote differently.** The dump names a term after a
    // constant interpreted to it, and `⟦Classical.choice.{0}⟧` is `•` — shared
    // with every other proof in the file, so the dump prints somebody else's
    // name for it. `⟦Classical.choice.{1}⟧` is `app(ε, ⟦α⟧)`, a term nothing
    // else in the file denotes, so it is printed under its own name.
    //
    // That asymmetry is the observable form of "the codomain is a `Prop` at
    // `u = 0` and is not at `u ≥ 1`", and it is what a clause that gave the
    // `u = 1` pair the point would lose — while moving `constEv` identically.
    let named: Vec<&&String> =
        typing.iter().filter(|t| t.contains("⟦Classical.choice.")).collect();
    assert_eq!(
        named.len(),
        1,
        "exactly one σ denotes a term of its own; the other denotes the shared point: {typing:?}"
    );
    assert!(
        named[0].contains("⟦Nonempty.{1}⟧"),
        "it must be the `u = 1` pair that denotes ε(⟦α⟧), not the `u = 0` one: {}",
        named[0]
    );
}

/// **The premise is read, not assumed.** `propext`'s clause takes its
/// biconditional apart through the class-(S) apparatus of whatever the third
/// binder's head constant is, and the two fields must be the two arrows between
/// the two binders. The fixture's `Iff` is the declaration that satisfies that;
/// `trueIff` in the same file is the witness that `Iff` is a real class-(S)
/// structure with an inhabitant, and it derives with no axiom in sight.
///
/// Pinned through the dump rather than a counter because the claim is about
/// *what* was derived: `propext`'s typing must be a membership in the
/// interpretation of its own declared type, and a clause that certified the
/// axiom against some other set would still move `constEv`.
#[test]
fn propexts_typing_is_about_its_own_declared_type() {
    let lines = theorem_lines("standard_axioms.ndjson", "propext");
    let typing: Vec<&String> = lines.iter().filter(|l| l.starts_with("typing ")).collect();
    assert_eq!(typing.len(), 1, "propext has one pair and so one typing: {lines:?}");
    assert!(!typing[0].contains("waiting on"), "propext's typing is a gap again: {}", typing[0]);
    // The set is the interpretation of `∀ {a b : Prop}, (a ↔ b) → a = b`, so
    // **both** the premise's type former and the codomain's appear in it — and
    // `Eq` at level 1, because the equation is between two propositions and
    // `Prop : Sort 1`. A clause that certified the axiom against the level-0
    // equation would move `constEv` and print `⟦Eq.{0}⟧` here.
    for want in ["⟦Iff.{}⟧", "⟦Eq.{1}⟧"] {
        assert!(
            typing[0].contains(want),
            "propext's typing is not about its own declared type — no {want} in {}",
            typing[0]
        );
    }
}

// ── The `EnvCore` seam, for indexed class-(T) evidence ───────────────────────

/// The **unified** route — no `--naive`. Every other runner in this file uses
/// the whole-file Mini checker, which never crosses the `EnvCore` seam because
/// one engine holds both ends. The seam only exists on the production route,
/// where Mini owns the inductive group and nanoda/TG check the definitions in
/// the same call, so a test about publication has to run that route.
///
/// `--acceptance-only` for [`run`]'s reason: these fixtures accept while still
/// owing certification debt, and the axis under test here is neither.
/// **`--features tg` only.** The binary this spawns refuses the unified route
/// without it — "the unified checker requires a `--features tg` build; use
/// --naive only for the historical mini checker" — so without the feature the
/// two tests below do not measure a weaker version of the property, they fail
/// on the build configuration. They were failing exactly that way: this suite
/// was 32/34 under `--no-default-features` and 34/34 under `--features tg`,
/// and the established gate only ever ran the second, so the red was invisible.
///
/// A `cfg`-ed-out test is *absent* rather than skipped — `running 0 tests … ok`
/// — which is the hazard `ci/check.sh` documents. What holds it here is that
/// `ci/check.sh` runs `cargo test -p nanoda_lib --features tg`, and
/// `ci/check-test-inputs.sh` refuses a feature no step builds and a step that
/// names a feature without selecting the package declaring it. So these two run
/// on every full check; they are removed only from the configuration in which
/// they cannot mean anything.
fn run_unified(name: &str) -> String {
    let path = fixture(name);
    let out = Command::new(env!("CARGO_BIN_EXE_checker"))
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg("--acceptance-only")
        .arg(&path)
        .output()
        .expect("spawn checker");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(
        out.status.code(),
        Some(0),
        "{name} must be ACCEPTED on the unified route:\n{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    stdout
}

/// `(translations, eliminators)` off the seam readiness row, `(0, 0)` when the
/// row is absent — which is exactly the state this test exists to forbid.
fn published_indexed(stdout: &str) -> (u64, u64) {
    let Some(l) = stdout.lines().find(|l| l.contains("indexed class-(T) evidence PUBLISHED"))
    else {
        return (0, 0)
    };
    let n: Vec<u64> = l
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().expect("digits"))
        .collect();
    assert_eq!(n.len(), 2, "the readiness row changed shape: {l}");
    (n[0], n[1])
}

/// `(asked, discharged)` off the `ICOD` readiness row. The third number on the
/// row — how many owe nothing — is deliberately *not* asserted on: every
/// discharge stands under the nest's own motive-typing assumptions, which is
/// the shape `fire_dep` already carries, and pinning it here would pin an
/// accounting artefact rather than the conjunct.
fn icod_counts(row: &str) -> (u64, u64) {
    let n: Vec<u64> = row
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().expect("digits"))
        .collect();
    assert_eq!(n.len(), 3, "the ICOD readiness row changed shape: {row}");
    (n[0], n[1])
}

/// **TG consumes the published indexed evidence as far as the rule itself.**
///
/// The sibling test above pins the *producing* side; this pins the consuming
/// side, and the two together are what make "the indexed consumer never fired"
/// and "mini handed it nothing" distinguishable observations.
///
/// What is asserted is a decline, deliberately. `RecBottom::IxDep` reaches
/// `IndexedDepRecursor::iota[i]`, instantiates it at the use site's own
/// parameters, motive, minors and target, and checks that its antecedent is the
/// conjunction `ICOD ∧ IDEP` — everything route (A) must do *before* the
/// premise. **The first conjunct is now discharged**: `TgBackend::ix_icod`
/// re-derives `ICOD` at the rung `DepElim::target` names, so the honest outcome
/// is a gap naming the conjunct that is *left*, `IDEP`. The row asserted here
/// moved with it, and the readiness counter `ICOD ... discharged` is asserted
/// beside it so that "ICOD is derived" and "the site still declines" stay two
/// observations rather than one.
///
/// That naming is the whole content. Before this, an indexed recursor declined
/// as `iota: no interpretation — an indexed family`, a label
/// `ORIGIN-RANKING.md` measured at −117 and then had to split by hand into a
/// genuine −89, a K-like `Eq.rec` −20 and an `Acc.rec` −8 on a different
/// engine, because `num_indices != 0` was tested ahead of `is_k` and every
/// indexed declaration got the same row whatever its real blocker was. A row
/// that prices three tranches is a row that prices none of them. This decline
/// is reached only through `mini_ix_dep_rec_bottom`, which tests `is_k` and the
/// motive count, so it counts the −89 and nothing else.
///
/// Both fixtures, because they fail differently: `Ix` is tag-indexed with two
/// firings and `Aux` is the six-constructor mutual encoding with three, so a
/// consumer that happened to work at one arity is caught at the other.
#[test]
fn tg_discharges_the_indexed_iota_rules_premise() {
    for name in ["ctor_abbrev_major.ndjson", "mutual_aux_encoding.ndjson"] {
        let out = run_unified(name);
        // **The counters, not a decline label.** The label moved inward on
        // every increment of this clause — `PRE = ICOD ∧ IDEP`, then
        // `ICOD is discharged; IDEP … is not`, then a named sub-population of
        // `IDEP`, then `PRE is discharged` — and its endpoint is no decline at
        // all. A test pinned to any one spelling measures the spelling. What
        // this pins is the thing that must hold at every stage *and* at the
        // end: the site reaches mini's rule and discharges its premise.
        // The conjunct itself, from the readiness row: a decline that named
        // `IDEP` while `ICOD` silently stopped being derived would read exactly
        // the same, and that is the regression this catches.
        assert!(
            out.contains("indexed premise ICOD at the motive's own rung — asked"),
            "{name}: no ICOD readiness row — the conjunct is not being asked for at all.\n{out}"
        );
        let row = out
            .lines()
            .find(|l| l.contains("indexed premise ICOD at the motive's own rung"))
            .expect("the row was just found");
        let (asked, done) = icod_counts(row);
        assert!(asked > 0, "{name}: ICOD was never asked for: {row}");
        assert_eq!(
            done, asked,
            "{name}: ICOD is no longer discharged at every firing of the rule: {row}"
        );
        // `IDEP`, every conjunct of it: the premise is a conjunction over all
        // `n` constructors, so a clause that served some of them and not the
        // rest would leave `PRE` undischarged while the fieldless column looked
        // healthy. Asserted as `asked == complete` rather than at a number,
        // because the number is the constructor count times the firing count.
        let idep = out
            .lines()
            .find(|l| l.contains("indexed premise IDEP, by CONSTRUCTOR"))
            .unwrap_or_else(|| panic!("{name}: no IDEP readiness row\n{out}"));
        let n: Vec<u64> = idep
            .split(|ch: char| !ch.is_ascii_digit())
            .filter(|s| !s.is_empty())
            .map(|s| s.parse().expect("digits"))
            .collect();
        assert_eq!(n.len(), 4, "{name}: the IDEP readiness row changed shape: {idep}");
        assert!(n[0] > 0, "{name}: IDEP was never asked for: {idep}");
        assert_eq!(
            n[1], n[0],
            "{name}: not every IDEP conjunct is discharged any more: {idep}"
        );
        assert!(
            n[2] > 0 && n[3] > 0,
            "{name}: one of IDEP's two constructor populations is unserved — both fixtures \
             have fieldless *and* fielded constructors, and a clause serving only one of them \
             is what this pair exists to catch: {idep}"
        );
        // And the whole premise, which is what the rule's `mp` consumes.
        let pre = out
            .lines()
            .find(|l| l.contains("indexed premise PRE = ICOD ∧ IDEP discharged"))
            .unwrap_or_else(|| panic!("{name}: no PRE readiness row\n{out}"));
        let pn: Vec<u64> = pre
            .split(|ch: char| !ch.is_ascii_digit())
            .filter(|w| !w.is_empty())
            .map(|w| w.parse().expect("digits"))
            .collect();
        assert_eq!(pn.len(), 2, "{name}: the PRE readiness row changed shape: {pre}");
        assert!(pn[0] > 0, "{name}: PRE is not discharged at any use site: {pre}");
        // **And the composite is built at every one of them.** `PRE` discharged
        // with the composite unbuilt was a real intermediate state of this
        // clause and looked identical on every other row, so the two are
        // asserted apart.
        assert_eq!(
            pn[1], pn[0],
            "{name}: the indexed composite is no longer built at every site whose premise is \
             discharged: {pre}"
        );
        // **The end-to-end result, which neither row above pins.** Building the
        // composite is not the same as the site certifying: `derive_iota_core`
        // still joins it against the reduct's own contraction, and a mutation
        // that dropped step 4 left every row above unchanged while the join
        // failed. The gap count is what noticed, so the gap count is asserted.
        let want = match name {
            "ctor_abbrev_major.ndjson" => 23,
            "mutual_aux_encoding.ndjson" => 49,
            other => panic!("no indexed ratchet recorded for {other}"),
        };
        let got: u64 = out
            .lines()
            .next()
            .and_then(|l| l.rsplit("tg gaps:").next().map(|w| w.trim().to_string()))
            .and_then(|w| w.parse().ok())
            .unwrap_or_else(|| panic!("{name}: no `tg gaps:` on the verdict line\n{out}"));
        assert_eq!(
            got, want,
            "{name}: the indexed iota ratchet moved. Every remaining gap on these two \
             fixtures is an escaped assumption at the boundary; a change here is either \
             the tranche regressing or the escape ledger moving, and both need saying.\n{out}"
        );
        assert!(
            !out.contains("iota: no interpretation — an indexed family"),
            "{name}: the declaration still declines under the label that prices three \
             separate causes as one. `mini_ix_dep_rec_bottom` is what takes it out of \
             that row, and it must, or the −89 is unmeasurable again.\n{out}"
        );
    }
}

/// **Mini's indexed class-(T) evidence reaches the shared core.**
///
/// `derived::inductive::family::IndexedDepRecursor::iota` concludes the indexed
/// ι rule, `crate::mini::rec_ix_dep` builds it and mini fires it live — and for
/// as long as this project has had an indexed route, **none of it crossed the
/// `EnvCore` seam**. `rec_ix_dep`'s value clause inserted into mini's private
/// `IndApparatus::dep_elims` and omitted the `publish_dep_elim` its non-indexed
/// sibling `rec_dep` performs three lines from the identical insert, and
/// `zoneb`'s indexed branch likewise inserted `IndexedTranslation` privately
/// where its non-indexed branch publishes first. `EnvCore` is the only channel
/// TG reads, so TG saw nothing.
///
/// Measured cost of that silence (`ORIGIN-RANKING.md` rank 1): **89 gaps**
/// across `mutual_aux_encoding`, `ctor_abbrev_major` and `077_RBTree.id_spec`,
/// the largest single tranche in the tree.
///
/// **This test asserts readiness, not consumption.** It is deliberately the
/// weaker claim: a publication channel's failure mode is silence, and silence
/// is indistinguishable from "the consumer declined" unless the producing side
/// is counted. Pinning it separately means a future regression names which of
/// the two halves broke.
///
/// Three fixtures, not one, and each carries a different indexed shape: `Ix` is
/// tag-indexed beside a plain `N` (so a route that published *any* translation
/// would pass on one of them alone), `Aux` is the three-member mutual encoding
/// at six constructors, and `RBTree` is the two-index family with a genuinely
/// family-valued motive.
#[test]
fn mini_publishes_indexed_class_t_evidence_across_the_envcore_seam() {
    for name in ["ctor_abbrev_major.ndjson", "mutual_aux_encoding.ndjson"] {
        let (tr, el) = published_indexed(&run_unified(name));
        assert!(
            tr >= 1,
            "{name}: mini published NO indexed translation. `zoneb`'s indexed branch \
             filled `IndApparatus::indexed` without `publish_indexed_translation`, so \
             `EnvCore` — the only store TG reads — holds nothing for this family."
        );
        assert!(
            el >= 1,
            "{name}: mini published an indexed translation but NO indexed eliminator. \
             `rec_ix_dep`'s value clause built `IndexedDepRecursor` evidence, kept the \
             nest-bottom abbreviation, and did not call `publish_ix_dep_elim`. This is \
             the exact seam defect, and it is worth 89 gaps."
        );
    }
}
