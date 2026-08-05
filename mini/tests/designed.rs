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
//! # Every number here is read from the run that asserts it
//!
//! No count in this file is a constant measured once with one binary and
//! compared against another later: [`run`] spawns `CARGO_BIN_EXE_mini` and the
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
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
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
fn theorem_lines(file: &str, decl: &str) -> Vec<String> {
    let path = fixture(file);
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
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
/// `mini::class_s` retains a typing `⊢ ⟦βⱼ⟧ ∈ U₀` per plain field. For **every**
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
/// written to distinguish: `mini::rec_prop` takes `Pⱼ` from
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
/// `accept 10 declarations` and exited `0`. `mini::ledger::Untranslated` is the
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
        let out = Command::new(env!("CARGO_BIN_EXE_mini"))
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
/// # Four trees, because three cannot distinguish
///
/// | declaration | `np` | recursive-argument domains | before | after |
/// |---|---|---|---|---|
/// | `CTree.node : (B2 → CTree) → CTree`                     | 0 | one, closed            | certifies | certifies |
/// | `KTree.node : (B2 → KTree α) → KTree α`                 | 1 | one, closed            | certifies | certifies |
/// | `PTree.node : (α → PTree α) → PTree α`                  | 1 | one, **the parameter** | declined  | **certifies** |
/// | `MTree.node : (B2 → MTree α) → (α → MTree α) → MTree α` | 1 | **two, mixed**         | declined  | **certifies** |
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
/// # `constEv == 8`, and what each number means when it moves
///
/// * `constEv == 8` — every pair, two `def`s per tree. It was **4** (`CTree`
///   and `KTree`) for as long as `FibreFacts` was required unconditional, and
///   it went straight to 8: `PTree` and `MTree` were blocked by that one
///   requirement and by nothing else. A landing at 6 would mean the mixed row
///   had been left behind, which on this route cannot happen.
/// * `typeEv == 8` — it was **6**. `ptreeNode`'s declared type mentions
///   `PTree B2`, so the type typing was owed on the declaration being placed;
///   both halves close together.
/// * the `waiting` set — **empty**. A key reappearing here without `constEv`
///   falling would be a gap *renamed* rather than opened.
/// * `untranslated declarations == 0`.
///
/// # The three untranslated eliminators are a different axis
///
/// `KTree.rec`, `PTree.rec` and `MTree.rec` report
/// `recursor(…: dependent recursor: a minor premise does not transport)`, and
/// **`KTree` reported it before this change too** — at `np = 1` with a *closed*
/// `γ`, where the placement was never in question. So it is a property of the
/// parameterised dependent recursor and not of the branching domain, it is
/// asserted here rather than left to be rediscovered, and `CTree.rec` at
/// `np = 0` is the control that says which axis it is on.
#[test]
fn a_recursive_argument_ranging_over_a_parameter_is_placed_under_its_typing() {
    let out = run("parameter_domain_branching.ndjson");

    // ── the frontend got all the way through ─────────────────────────────
    let el = elim(&out);
    for name in ["B2", "CTree", "KTree", "PTree", "MTree"] {
        assert_eq!(
            el.get(name),
            Some(&(true, true)),
            "{name}'s eliminator class must be computed and agree with Lean's:\n{out}"
        );
    }
    assert_eq!(row(&out, "clauses").get("remaining"), Some(&0), "every clause interprets:\n{out}");

    // ── four trees, eight pairs, and every one of them certifies ─────────
    all_derived(&out, 8);
    let e = evidence(&out);
    assert_eq!(
        e.get("typeEv"),
        Some(&8),
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
    // rediscovered — and named at `np = 1` only, which is what says it is the
    // parameterised recursor and not the branching domain.
    assert_eq!(
        u.get("eliminators"),
        Some(&3),
        "the three parameterised dependent recursors — a separate axis:\n{out}"
    );
    for name in ["KTree", "PTree", "MTree"] {
        assert!(
            out.contains(&format!(
                "notrans:recursor({name}: dependent recursor: a minor premise does not transport)"
            )),
            "{name}.rec's decline must be the parameterised-recursor one:\n{out}"
        );
    }
    assert!(
        !out.contains("notrans:recursor(CTree"),
        "`CTree.rec` at np = 0 is the control: it translates:\n{out}"
    );
}
