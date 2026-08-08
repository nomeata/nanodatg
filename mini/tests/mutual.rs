//! **Mutual inductives** — the fixtures, and how far the pipeline takes them.
//!
//! `mini/tests/designed.rs` is the general home for designed fixtures. This is
//! a separate module for one reason: mutual inductives are a *feature arc*
//! rather than a clause, and the arc moves the frontend. Keeping the whole
//! arc's measurements in one file means the commit that moves one of them is
//! one file's diff.
//!
//! # Where the arc stands
//!
//! * **Zone A takes a mutual block.** `kernel::add_block` checks every member
//!   and computes one recursor per member over one shared motive and minor
//!   telescope, and the ι rules fire.
//! * **The block is encoded away before the evidence pass.**
//!   `mutual_aux::expand` replaces it, in `run::check_file_with`, by an
//!   enumeration, one indexed inductive, and ordinary definitions and theorems
//!   over them — under the block's *own* names. The interpretation pass then
//!   runs on those, so `⟦T.{σ}⟧`, `⟦T.ctor.{σ}⟧` and `⟦T.rec.{σ}⟧` land in the
//!   store at the keys every later use site reads. **There is no install
//!   step**: the store never learns a block was there.
//! * **Every fixture certifies every pair and exits 0**, indexed families and
//!   members with *different* index telescopes included. The telescopes live in
//!   the tag — `Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗`, one constructor per member carrying
//!   that member's own indices — so `Aux` has no index telescope to make the
//!   members share, and an unindexed block is the case where every tag
//!   constructor is nullary.
//! * **The frontend still declines by default.** `--mutual` opens the gate;
//!   without it the file is exit 2, as it has always been. `convert::LoadOptions`
//!   says why that is a separate decision, and both halves are pinned below.
//! * **The encoder never names a `Term` or a `Thm`**, and
//!   `ci/check-mutual-blackbox.sh` is that claim as a check that can fail.
//!
//! # The fixtures
//!
//! | fixture | what it covers |
//! | --- | --- |
//! | `mutual_three_way_cycle` | three members, a cycle, recursors applied positionally |
//! | `mutual_expr_stmt_ast` | the realistic shape: `Exp`/`Stm`/`Stms`, eight minors |
//! | `mutual_parameters` | two shared parameters across three members |
//! | `mutual_indices` | per-member indices, none of them promoted |
//! | `mutual_prop_even_odd` | `Prop`-valued, at two members and at three |
//! | `mutual_one_recursive` | only one member recursive; one member unreferenced |
//! | `mutual_universe_polymorphic` | two level parameters, recursor takes a third |
//! | `mutual_iota_reduction` | the rules **fired**, as three `rfl` theorems |
//! | `mutual_index_sorts` | two indices at two sorts, two parameters, and `Tag`'s universe |
//! | `mutual_index_telescopes` | telescopes that differ: how many members, the index type, and which member fixes `Tag`'s universe |
//! | `mutual_aux_encoding` | steps 3–5 written by hand: the encoding, and `rfl` |
//!
//! Each `.lean` carries its own header saying what breaks if it regresses.
//! `scripts/export-fixture.sh <name>.lean` regenerates the `.ndjson`.
//!
//! `mutual_aux_encoding` is the odd one out and deliberately so: it contains no
//! `mutual` block at all. It is the *output* the rest of the arc is meant to
//! generate — the three-member family encoded as one tag-indexed inductive,
//! with the type formers, constructors and recursors as ordinary `def`s and the
//! recursor rules as ordinary theorems proved by `rfl`. It is checked in
//! because it settles the design's central premise before any generator exists,
//! and it goes on being checked so that a change which quietly breaks the
//! premise fails here.
//!
//! # Three members, everywhere it could matter
//!
//! Every claim in this arc that is about *position* — which motive a minor's
//! induction hypothesis is stated at, which member a recursor eliminates, the
//! order of the shared minor telescope — is made at **three** members. Two
//! members distinguish a permutation from the identity and nothing else: a
//! builder that reverses the list and a builder that clamps to one end agree on
//! every two-element list. `mutual_prop_even_odd` carries the two-member
//! classic *and* a three-member family of the same shape so that the member
//! count is the only thing that differs between them.
//!
//! # The oracle, and why it is worth more than the fixtures
//!
//! [`the_generated_recursors_are_the_ones_lean_exports`] compares the recursor
//! mini **generates** against the one the export **declares**, type and rules,
//! for every recursor in every fixture — and, when `vendor/arena-tests` is
//! present, for every recursor in the tutorial corpus too. Everything else zone
//! A is checked against is mini agreeing with mini: `check_type` on the
//! generated type is mini's own inference, and an ι rule that fires is mini's
//! own whnf finding mini's own right-hand side. This is the one measurement
//! whose other side was produced by Lean.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use mini::convert::{load_with, LoadOptions};
use mini::env::{instantiate_lparams, ConstantInfo, Declaration, Environment, IndType};
use mini::expr::{arrow, konst, sort, Expr, Level, Name, E};

/// Every mutual fixture, and the first member of its first block — the name
/// `convert::load` reports when it declines. Read from the fixture rather than
/// derived, so a fixture whose block order changed fails here rather than
/// silently re-pointing.
const FIXTURES: [(&str, &str); 10] = [
    ("mutual_three_way_cycle", "A"),
    ("mutual_expr_stmt_ast", "Exp"),
    ("mutual_parameters", "PA"),
    ("mutual_indices", "T0"),
    ("mutual_prop_even_odd", "Even"),
    ("mutual_one_recursive", "OA"),
    ("mutual_universe_polymorphic", "UA"),
    ("mutual_iota_reduction", "A"),
    ("mutual_index_sorts", "SA"),
    ("mutual_index_telescopes", "MA"),
];

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{name}.ndjson"));
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini [--mutual] --verbose <fixture>`, in a subprocess — `checker`'s parser
/// reports a declined export by calling `std::process::exit(2)`, which an
/// in-process harness cannot contain. Returns `(exit code, stdout)`.
fn run(name: &str, gate: bool) -> (Option<i32>, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_mini"));
    // The suite is hermetic — see `mini/src/modelgen.rs`; the fixtures are
    // committed already filtered, so the pass would only cost a toolchain.
    cmd.arg("--no-modelgen");
    cmd.arg("--verbose");
    if gate {
        cmd.arg("--mutual");
    }
    let out = cmd.arg(fixture(name)).output().expect("spawn mini");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
}

/// The `facts` row's counters.
fn facts(stdout: &str) -> BTreeMap<String, u64> {
    let Some(line) = stdout.lines().find(|l| l.starts_with("facts\t")) else {
        panic!("no `facts` row in:\n{stdout}")
    };
    let mut m = BTreeMap::new();
    for kv in line.split('\t').skip(1) {
        if let Some((k, v)) = kv.split_once('=') {
            if let Ok(v) = v.parse() {
                m.insert(k.to_string(), v);
            }
        }
    }
    m
}

/// The `evidence` row's plain counters, `waiting:` keys excluded.
fn evidence(stdout: &str) -> BTreeMap<String, u64> {
    let Some(line) = stdout.lines().find(|l| l.starts_with("evidence\t")) else {
        panic!("no `evidence` row in:\n{stdout}")
    };
    let mut m = BTreeMap::new();
    for kv in line.split('\t').skip(1) {
        if let Some((k, v)) = kv.split_once('=') {
            if !k.starts_with("waiting:") {
                m.insert(k.to_string(), v.parse().unwrap_or(0));
            }
        }
    }
    m
}

/// Every `waiting:` key of the `evidence` row, with the prefix stripped.
fn waiting(stdout: &str) -> BTreeMap<String, u64> {
    let Some(line) = stdout.lines().find(|l| l.starts_with("evidence\t")) else {
        panic!("no `evidence` row in:\n{stdout}")
    };
    let mut m = BTreeMap::new();
    for kv in line.split('\t').skip(1) {
        if let Some((k, v)) = kv.split_once('=') {
            if let Some(k) = k.strip_prefix("waiting:") {
                m.insert(k.to_string(), v.parse().unwrap_or(0));
            }
        }
    }
    m
}

// ────────────────────────────────────────────────────────── the frontend ──

/// **Every mutual fixture parses, and every one declines without the gate.**
///
/// The two halves are one test on purpose. A fixture that fails to *parse* also
/// exits 2 — `LoadError::Io`, a `checker` parser panic, an `.ndjson` that was
/// never regenerated — and would pass a bare "exit 2" assertion while measuring
/// nothing at all. So the reason string is matched too: it has to be the mutual
/// decline, naming the block's first member, and not any other way of reaching
/// the same code.
///
/// **This is the arena's exit-2 contract and it has not moved.** Zone A can
/// check these files now; the frontend still refuses them, because a file whose
/// every declaration is untranslated is not support and the population of exit
/// 2 is not a thing to change as a side effect of wiring.
#[test]
fn every_mutual_fixture_declines_without_the_gate() {
    for (name, member) in FIXTURES {
        let (code, stdout) = run(name, false);
        assert_eq!(code, Some(2), "{name} did not decline:\n{stdout}");
        let want = format!("declined: Mutual inductive {member} not supported");
        assert!(
            stdout.contains(&want),
            "{name} declined for the wrong reason — expected `{want}`:\n{stdout}"
        );
    }
}

/// **With the gate open, every fixture is accepted — and every block the
/// encoder can express certifies every pair.**
///
/// The table is the arc's measurement, and both columns of every row are
/// pinned. `pairs` is the population the run actually opens: the encoding's own
/// definitions are declarations too, so a file whose block is encoded has more
/// pairs than one whose block is not — and all of them certify.
///
/// **`mutual_three_way_cycle` went from `constEv 0` to 21**, two of which are
/// `aSize` and `cSize`, whole recursor applications over a three-member block.
/// **`mutual_indices` went from 0 to 22 and `mutual_prop_even_odd` from 23 to
/// 53** when the indexed encoding landed; both had been exit 4 with every
/// member untranslated.
///
/// **Every row is all-green.** `mutual_index_sorts` was the exception until the
/// index telescopes moved into the tag: its second block's members do not share
/// one, and there is no longer any such thing as sharing one. Its `pairs` went
/// 42 → 56 in the same step, because a block that encodes contributes its own
/// definitions and a block that declines contributes none.
#[test]
fn with_the_gate_open_the_encoded_blocks_certify_and_the_rest_say_why_not() {
    /// `(pairs, constEv, typeEv, lazyFills)`.
    type Ev = (u64, u64, u64, u64);
    /// `(blocks seen, blocks encoded, rule theorems stated)`.
    type Enc = (u64, u64, u64);
    // fixture, exit, evidence, encoder
    let want: [(&str, i32, Ev, Enc); 10] = [
        ("mutual_three_way_cycle", 0, (21, 21, 21, 0), (1, 1, 0)),
        ("mutual_expr_stmt_ast", 0, (27, 27, 27, 0), (1, 1, 0)),
        // **Five rule theorems under a two-parameter telescope.** This file
        // carries an `Eq` for exactly that reason: `mutual_iota_reduction` has
        // no parameters, so the shift that carries a constructor field's type
        // past the motives and the minors is the identity there. Deleting that
        // shift outright passed the whole suite before this row existed.
        ("mutual_parameters", 0, (34, 34, 34, 0), (1, 1, 5)),
        ("mutual_one_recursive", 0, (22, 22, 22, 0), (1, 1, 0)),
        ("mutual_universe_polymorphic", 0, (34, 34, 34, 0), (1, 1, 0)),
        // **`lazyFills` is 0 here, and this row is the one that measures it.**
        // It was 1 — `Eq` at `σ = [1]` — for as long as the rule theorems were
        // emitted at the block: this file declares `Eq` *after* its block, so
        // a rule theorem's statement reached `Eq` before `Eq`'s own
        // declaration had filled the store. The three files with rule theorems
        // were the only three the design's `lazyFills = 0` did not hold on.
        // See `mutual_aux::expand`'s header.
        ("mutual_iota_reduction", 0, (26, 26, 26, 0), (1, 1, 6)),
        // Indexed, and formerly the measurable: `constEv` was 0.
        ("mutual_indices", 0, (22, 22, 22, 0), (1, 1, 0)),
        // Four blocks, two of them indexed, and formerly 23 of 34.
        ("mutual_prop_even_odd", 0, (53, 53, 53, 0), (4, 4, 0)),
        // **Three blocks, all three encoded**, and the only file in the suite
        // whose members do not all carry the same index telescope.
        //
        //  * `SA`/`SB`/`SC` — two parameters, two closed indices at two
        //    different sorts, and the `Prop`-valued family indexed by a large
        //    type that separates `Tag`'s universe from the cheap guess `1`.
        //  * `VA`/`VB` — indexed by `Pair α`, an index *type* that mentions the
        //    block's parameter, and the only witness for the index shift the
        //    encoding still has.
        //  * `HA : N → Type` / `HB : Type` — the **arity** axis, one index
        //    against none. This was `ind-spec(HA: mutual with unequal index
        //    telescopes)` and exit 4 with three pairs uncertified.
        ("mutual_index_sorts", 0, (56, 56, 56, 0), (3, 3, 10)),
        // **The three axes `mutual_index_sorts`' `HA`/`HB` leaves open**, one
        // block each: three members where the one whose telescope differs is
        // the *middle* one; two members at equal arity whose index **types**
        // differ (`N` against `Bit`); and a block whose **first** member has
        // no indices while its second is indexed by `Type 1`, which is the
        // only place `W` over every member differs from `W` over member 0.
        // Five of the first block's six constructors hold a member at a
        // different telescope from the one they build, and its three `Size`
        // defs apply the recursors over motives at two telescopes at once.
        ("mutual_index_telescopes", 0, (72, 72, 72, 0), (3, 3, 13)),
    ];
    for (name, code, (pairs, const_ev, type_ev, lazy), (blocks, encoded, rules)) in want {
        let (got, stdout) = run(name, true);
        assert_eq!(got, Some(code), "{name}: wrong exit status:\n{stdout}");
        assert!(stdout.contains("\taccept\t"), "{name} was not accepted:\n{stdout}");
        let e = evidence(&stdout);
        let f = facts(&stdout);
        let g = |m: &BTreeMap<String, u64>, k: &str| m.get(k).copied().unwrap_or(0);
        assert_eq!(
            (g(&e, "pairs"), g(&e, "constEv"), g(&e, "typeEv"), g(&e, "lazyFills")),
            (pairs, const_ev, type_ev, lazy),
            "{name}: the evidence row moved:\n{stdout}"
        );
        assert_eq!(
            (g(&f, "mutualBlocks"), g(&f, "mutualEncoded"), g(&f, "mutualRules")),
            (blocks, encoded, rules),
            "{name}: the encoder's own counts moved:\n{stdout}"
        );
    }
}

/// **A block whose members' index telescopes differ encodes, at every member.**
///
/// Separate from the counts above because it is a different claim: the counts
/// say every pair certifies, this says the reason is that the *members* were
/// translated and not that the file happened to open no pair about them. A
/// `waiting:` key naming a member would be either `ind-spec(HA: …)` — the
/// encoder declining and recording a shape — or `no-interp(HA)` — the reason
/// table not written and the miss path answering with its fallback. Neither
/// may appear, and the two are distinguished because they used to be confused.
///
/// *This test asserted the opposite until the telescopes moved into the tag.*
/// `HA : N → Type` and `HB : Type` were `ind-spec(HA: mutual with unequal index
/// telescopes)`, `Reason::IndicesDiffer`, the encoding's own scope line and not
/// the kernel's — the kernel was always happy with the block. `Aux` has no
/// index telescope at all now, so there is nothing for the members to disagree
/// about and the reason is retired rather than unreachable.
#[test]
fn a_block_whose_members_index_telescopes_differ_encodes_at_every_member() {
    for (file, members) in [
        ("mutual_index_sorts", &["SA", "SB", "SC", "VA", "VB", "HA", "HB"][..]),
        ("mutual_index_telescopes", &["MA", "MB", "MC", "DA", "DB", "EA", "EB"][..]),
    ] {
        let (code, stdout) = run(file, true);
        assert_eq!(code, Some(0), "{file}: not accepted:\n{stdout}");
        let w = waiting(&stdout);
        for m in members {
            assert!(
                !w.keys().any(|k| k.contains(&format!("({m}:")) || k == &format!("no-interp({m})")),
                "{file}: {m} is waiting:\n{stdout}"
            );
        }
        assert!(w.is_empty(), "{file}: something is waiting:\n{stdout}");
    }
}

/// **The ι rules of a mutual block fire.**
///
/// `mutual_iota_reduction` states four of them as theorems proved by
/// reflexivity, so accepting the file *is* the assertion: mini's whnf has to
/// locate the major argument past three motives and six minors, pick the rule
/// for the applied constructor, and produce an induction hypothesis that is an
/// application of a **different member's** recursor to the same shared prefix.
///
/// A separate test from the acceptance sweep above so that the failure reads
/// correctly. This file failing means reduction is wrong; the sweep failing
/// means the frontend or the ledger is.
#[test]
fn the_mutual_iota_rules_reduce_and_the_rfl_proofs_check() {
    let (code, stdout) = run("mutual_iota_reduction", true);
    assert_eq!(code, Some(0), "the ι fixture was not accepted:\n{stdout}");
    // Ten declarations: `Eq`, `N`, the block, three `def`s, four theorems —
    // counted so that a fixture that lost its theorems fails here instead of
    // passing on the two that remain.
    assert!(
        stdout.contains("accept\t10 declarations"),
        "the ι fixture's declaration population changed:\n{stdout}"
    );
}

/// **The aux encoding makes every recursor rule definitional.**
///
/// The premise the whole arc rests on, tested where it can be tested cheaply:
/// in Lean, by hand, before there is a generator. `mutual_aux_encoding.lean`
/// encodes `mutual_three_way_cycle`'s family as one tag-indexed inductive and
/// states its three recursor rules as theorems proved by `Eq.refl _`; mini's
/// kernel accepting the file *is* the assertion that they are reflexivity.
///
/// **No `--mutual` here**, and that is the point: the encoding rides the
/// ordinary pipeline. If this file ever needs the gate, the encoding has stopped
/// being an encoding.
///
/// Nineteen declarations: `Eq`, `Tag`, `Aux`, three type formers, six
/// constructors, `Mot`, three recursors, three rules. Counted so that a fixture
/// which lost its rules fails here rather than passing on what remains.
///
/// **And every pair of it certifies.** When this fixture landed, the three
/// recursors and the three rule theorems had no `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` — twelve
/// of twenty-three pairs waiting on `no-endpoint`. The cause was two faults in
/// the *ordinary* pipeline, both since fixed (`548ed57`): `conv::app_cong` did
/// not record the endpoints `derived::congr` built inside the kernel, so they
/// could not be decomposed, and the ι site refused every major argument that
/// had to δ-reduce first — which `Arec … Amk0` does, because `Amk0` is a
/// constructor abbreviation.
///
/// So the number is pinned now, and it is pinned as an *equality* on both
/// columns rather than as a floor: `constEv` climbing past `pairs` is not
/// possible, and `pairs` moving is a fixture change that has to be read.
/// **This is the target the generator has to reproduce** — whatever
/// `mutual_aux::encode` emits, if it emits this, it certifies.
#[test]
fn the_aux_encoding_makes_every_recursor_rule_reflexivity_and_all_of_it_certifies() {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--no-modelgen")
        .arg("--verbose")
        .arg(fixture("mutual_aux_encoding"))
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(
        out.status.code(),
        Some(0),
        "the aux encoding is no longer clean — a rule that stopped being `rfl`, or a pair \
         that stopped certifying, lands here:\n{stdout}"
    );
    assert!(
        stdout.contains("accept\t19 declarations"),
        "the aux fixture's declaration population changed:\n{stdout}"
    );
    let e = evidence(&stdout);
    let g = |k: &str| e.get(k).copied().unwrap_or(0);
    assert_eq!(g("pairs"), 23, "the aux fixture's pair population changed:\n{stdout}");
    assert_eq!(g("constEv"), 23, "not every pair of the aux encoding certifies:\n{stdout}");
    assert_eq!(g("typeEv"), 23, "a type typing of the aux encoding is missing:\n{stdout}");
    assert!(waiting(&stdout).is_empty(), "a gap appeared in the aux encoding:\n{stdout}");
}

// ─────────────────────────────────────────────────── what is refused ──

/// A block built by hand, at no level parameters, for the kernel to reject.
///
/// **A shape Lean will not export is exactly what a negative test needs.**
/// `mini/tests/designed.rs`'s warning about hand-written declarations is about
/// *positive* fixtures — asserting `numIndices` for a promotion Lean would have
/// undone measures a declaration that cannot arise. Here the whole point is a
/// declaration Lean's elaborator refuses to build, so it has to be built here,
/// the way the arena's `bad/` half is built. The kernel is the thing under
/// test, and the kernel's input is a `Declaration`.
type Member<'a> = (&'a str, E, Vec<(&'a str, E)>);

fn block(types: Vec<Member<'_>>) -> Declaration {
    Declaration::Mutual {
        lparams: Vec::new(),
        num_params: 0,
        types: types
            .into_iter()
            .map(|(n, ty, ctors)| IndType {
                name: Name::simple(n),
                ty,
                ctors: ctors.into_iter().map(|(c, t)| (Name::simple(c), t)).collect(),
            })
            .collect(),
    }
}

fn k(n: &str) -> E { konst(Name::simple(n), Vec::new().into()) }

/// **A member occurring in the domain of another member's recursive argument is
/// not strictly positive**, and the check ranges over the whole block.
///
/// `C.mk : (B → C) → C` is the discriminating shape. Its field type mentions
/// `B` and `C` and **not** `A`, which is the block's first member — so a
/// positivity guard that asked `has_const(names[0], …)` instead of "does any
/// member occur" skips the walk entirely and accepts it. Three members, and the
/// bad occurrence at neither the first nor the constructor's own: with two
/// members every field type that mentions one mentions the other or the first,
/// and the two guards agree.
///
/// The block is otherwise well formed and its sibling `A.mk : B → A` is
/// accepted below, so the rejection is about the domain and not about the file.
#[test]
fn a_cross_member_occurrence_in_a_domain_is_not_strictly_positive() {
    let ty = sort(Level::Succ(std::rc::Rc::new(Level::Zero)));
    let good = block(vec![
        ("A", ty.clone(), vec![("A.mk", arrow(k("B"), k("A")))]),
        ("B", ty.clone(), vec![("B.mk", k("B"))]),
        ("C", ty.clone(), vec![("C.mk", arrow(k("B"), k("C")))]),
    ]);
    let mut env = Environment::empty();
    mini::kernel::add(&mut env, &good).expect("a positive cross-member field is fine");

    let bad = block(vec![
        ("A", ty.clone(), vec![("A.mk", arrow(k("B"), k("A")))]),
        ("B", ty.clone(), vec![("B.mk", k("B"))]),
        // `(B → C) → C`: `B` in the domain of a recursive argument.
        ("C", ty.clone(), vec![("C.mk", arrow(arrow(k("B"), k("C")), k("C")))]),
    ]);
    let mut env = Environment::empty();
    let err = mini::kernel::add(&mut env, &bad).expect_err("a non-positive block was accepted");
    assert!(
        err.contains("Not strictly positive"),
        "rejected, but not for positivity:\n{err}"
    );
}

/// **The members of a block must live in one universe.**
///
/// The kernel's rule (`nanoda`'s `check_inductive_specs_mutual1` asserts it) and
/// the reason one shared motive level is meaningful at all. Lean's elaborator
/// unifies the universes before the kernel ever sees the block, so this too is a
/// shape only a hand-built declaration can carry.
///
/// The control is the same block with both members at `Type`: without it, a
/// kernel that rejected every hand-built block would pass.
#[test]
fn a_block_whose_members_live_at_different_universes_is_rejected() {
    let ty0 = sort(Level::Succ(std::rc::Rc::new(Level::Zero)));
    let ty1 = sort(Level::Succ(std::rc::Rc::new(Level::Succ(std::rc::Rc::new(Level::Zero)))));
    let mut env = Environment::empty();
    mini::kernel::add(
        &mut env,
        &block(vec![
            ("A", ty0.clone(), vec![("A.mk", arrow(k("B"), k("A")))]),
            ("B", ty0.clone(), vec![("B.mk", k("B"))]),
        ]),
    )
    .expect("one universe is fine");

    let mut env = Environment::empty();
    let err = mini::kernel::add(
        &mut env,
        &block(vec![
            ("A", ty0, vec![("A.mk", arrow(k("B"), k("A")))]),
            ("B", ty1, vec![("B.mk", k("B"))]),
        ]),
    )
    .expect_err("a block spanning two universes was accepted");
    assert!(
        err.contains("must live in one universe"),
        "rejected, but not for the universe:\n{err}"
    );
}

// ───────────────────────────────────────────────── the recursor oracle ──

/// `l0, l1, …` — one canonical level parameter per position, so that mini's
/// `v` and Lean's `u` compare equal without either being renamed to the other.
fn canon(n: usize) -> Vec<Level> {
    (0..n).map(|i| Level::Param(Name::simple(&format!("l{i}")))).collect()
}

/// Peel every `∀`, returning the body.
fn peel_all(ty: &E) -> (usize, E) {
    let mut n = 0usize;
    let mut cur = ty.clone();
    while let Expr::Forall { body, .. } = &*cur {
        let b = body.clone();
        cur = b;
        n += 1;
    }
    (n, cur)
}

/// Peel `n` `fun` binders, or say there were not that many.
fn strip_lams(e: &E, n: usize) -> Option<E> {
    let mut cur = e.clone();
    for _ in 0..n {
        let Expr::Lam { body, .. } = &*cur else { return None };
        let b = body.clone();
        cur = b;
    }
    Some(cur)
}

/// A constructor's field count: its telescope minus **its own** type's
/// parameters.
///
/// `np` is the *recursor's* parameter count and is only the fallback. The two
/// agree for every recursor whose rules are its own type's constructors, and
/// differ for a **nested** one: `Tree.rec_1` has `numParams = 0` and a rule for
/// `List.cons`, whose first argument is `List`'s parameter and not a field.
/// Reading the owner is what makes the peel below land on the export's rhs
/// instead of one binder past it.
fn num_fields(env: &Environment, ctor: &Name, np: usize) -> Option<usize> {
    let ConstantInfo::Opaque { ty, .. } = env.get(ctor)? else { return None };
    let mut n = 0usize;
    let mut cur = ty.clone();
    while let Expr::Forall { body, .. } = &*cur {
        let b = body.clone();
        cur = b;
        n += 1;
    }
    let owned = env
        .owner(ctor)
        .and_then(|o| env.get(o))
        .and_then(|ci| match ci {
            ConstantInfo::Inductive { num_params, .. } => Some(*num_params as usize),
            _ => None,
        })
        .unwrap_or(np);
    n.checked_sub(owned)
}

/// Compare every recursor mini generated for `path` against the export's own.
/// Returns `(matched, complaints)`; `Quot`'s two eliminators are skipped,
/// because the export declares them as `quot` entries and not as recursors.
fn compare_recursors(
    path: &Path,
    k_diverge: &mut Vec<String>,
    declined: &mut Vec<String>,
) -> (usize, Vec<String>) {
    let stem = path.file_name().unwrap().to_string_lossy().to_string();
    let opts = LoadOptions { mutual: true, nested: true, keep_export_recursors: true, ..Default::default() };
    let loaded = match load_with(path, opts) {
        Ok(l) => l,
        // **A fixture the frontend refuses has no recursors to compare, and
        // that is not a mismatch.** `nested_shapes.ndjson` declines for being
        // nested and there is no gate for it; sweeping the whole fixture
        // directory used to report that as "1 recursor differs". The skipped
        // set is collected and asserted below rather than swallowed, so it
        // cannot grow to hide a fixture that ought to have loaded.
        Err(mini::convert::LoadError::Declined(why)) => {
            declined.push(format!("{stem}: {why}"));
            return (0, Vec::new())
        }
        Err(e) => return (0, vec![format!("{stem}: did not load: {e}")]),
    };
    let mut env = Environment::empty();
    for d in &loaded.decls {
        if let Err(m) = mini::kernel::add(&mut env, d) {
            return (0, vec![format!("{stem}: rejected at {}: {m}", d.name())])
        }
    }
    let mut ok = 0usize;
    let mut bad: Vec<String> = Vec::new();
    let mut names: Vec<Name> = env.consts.keys().cloned().collect();
    names.sort_by_key(Name::to_string);
    for n in &names {
        let Some(ConstantInfo::Recursor {
            lparams, ty, num_params, num_motives, num_minors, num_indices, rules, k_type,
        }) = env.get(n)
        else {
            continue
        };
        let Some(er) = loaded.export_recs.get(n) else {
            // `Quot.lift`/`Quot.ind` are minted by `add_quot`, and the export
            // carries them as `quot` entries. Everything else must be there.
            if !matches!(n.to_string().as_str(), "Quot.lift" | "Quot.ind") {
                bad.push(format!("{stem}: {n}: mini generated it, the export has no recursor"));
            }
            continue
        };
        let mut p: Vec<String> = Vec::new();
        let mine = (*num_params, *num_motives, *num_minors, *num_indices);
        let theirs = (er.num_params, er.num_motives, er.num_minors, er.num_indices);
        if mine != theirs {
            p.push(format!("(params, motives, minors, indices) {mine:?} vs {theirs:?}"));
        }
        if k_type.is_some() != er.is_k {
            // **A divergence that predates this work and is mini-lean's, not
            // mini's.** A declaration whose resultant sort is a bare level
            // *parameter* — `PUnit : Sort u` and its relatives — is neither
            // provably zero nor provably nonzero, and the two kernels ask
            // different questions about that: mini-lean's `Environment.add`
            // writes `if indLevel.isNotZero then none`, Lean's `init_k_target`
            // writes `if is_zero(level) then …`. So mini says K-like and Lean
            // says not.
            //
            // Not corrected here: mini is a port of mini-lean and this is the
            // port being faithful, and changing it moves the acceptance axis on
            // the corpus. It costs nothing observable — Lean reaches the same
            // conversions through unit-like eta, which mini also has.
            //
            // **Keyed on the cause and not on the name.** It was `PUnit.rec`
            // until a designed fixture landed with a second declaration of the
            // same shape under a different name, and a name list would have
            // reported that as a new divergence. The predicate below is the
            // mini-lean/Lean disagreement written out: mini K-like, Lean not,
            // and the owner's own resultant level a bare parameter. Anything
            // else is new and fails.
            let owner_param_sort = env
                .owner(n)
                .and_then(|o| env.get(o))
                .map(|ci| matches!(&*peel_all(ci.ty()).1, Expr::Sort(Level::Param(_))))
                .unwrap_or(false);
            let known = k_type.is_some() && !er.is_k && owner_param_sort;
            if known {
                k_diverge.push(format!("{stem}: {n}: mini true export false (parameter sort)"));
            } else {
                p.push(format!("K-like {} vs {}", k_type.is_some(), er.is_k));
            }
        }
        if lparams.len() != er.lparams.len() {
            p.push(format!("{} level parameters vs {}", lparams.len(), er.lparams.len()));
        } else {
            let ls = canon(lparams.len());
            let a = instantiate_lparams(ty, lparams, &ls).expect("levels");
            let b = instantiate_lparams(&er.ty, &er.lparams, &ls).expect("levels");
            if a != b {
                p.push(format!("type:\n    mini   {a}\n    export {b}"));
            }
            if rules.len() != er.rules.len() {
                p.push(format!("{} rules vs {}", rules.len(), er.rules.len()));
            } else {
                for (i, (cn, rhs)) in rules.iter().enumerate() {
                    let (ecn, erhs) = &er.rules[i];
                    if cn != ecn {
                        p.push(format!("rule {i} is for {cn}, the export's for {ecn}"));
                        continue
                    }
                    // The export's right-hand side still carries
                    // `fun params motives minors fields =>`; mini stores the
                    // open body. Peel exactly those, never "all of them": a
                    // rule whose body happens to be a `fun` would otherwise
                    // compare against the wrong expression.
                    let Some(nf) = num_fields(&env, cn, *num_params as usize) else {
                        p.push(format!("rule {i} {cn}: no constructor in the environment"));
                        continue
                    };
                    let k = (*num_params + *num_motives + *num_minors) as usize + nf;
                    let Some(body) = strip_lams(erhs, k) else {
                        p.push(format!("rule {i} {cn}: the export's rhs has fewer than {k} binders"));
                        continue
                    };
                    let a = instantiate_lparams(rhs, lparams, &ls).expect("levels");
                    let b = instantiate_lparams(&body, &er.lparams, &ls).expect("levels");
                    if a != b {
                        p.push(format!("rule {i} {cn}:\n    mini   {a}\n    export {b}"));
                    }
                }
            }
        }
        if p.is_empty() {
            ok += 1;
        } else {
            bad.push(format!("{stem}: {n}:\n  {}", p.join("\n  ")));
        }
    }
    (ok, bad)
}

/// **Mini's generated recursor is the one Lean exports** — type, rule count,
/// rule order and every rule's right-hand side — for every designed fixture,
/// and for the tutorial corpus when it is checked out.
///
/// This is the oracle the whole of zone A's recursor builder rests on, and it
/// is the reason the mutual generalisation could be made to the *existing*
/// builder rather than beside it: a block of one has to keep matching, and 150
/// of the recursors compared here are blocks of one.
///
/// Not vacuous by construction: the number of comparisons is asserted, so a
/// change that stopped populating `Loaded::export_recs` — or a fixture list
/// that lost its mutual files — fails here rather than passing at zero.
#[test]
fn the_generated_recursors_are_the_ones_lean_exports() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("fixture directory")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    files.sort();
    let designed = files.len();
    assert!(designed >= 8, "the designed fixture set shrank to {designed}");

    // `vendor/arena-tests` is gitignored, so the corpus half is a bonus and
    // never a requirement. When it is there it more than triples the sample.
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../vendor/arena-tests/good/tutorial");
    if corpus.is_dir() {
        let mut c: Vec<PathBuf> = std::fs::read_dir(&corpus)
            .expect("corpus directory")
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
            .collect();
        c.sort();
        files.extend(c);
    }

    let mut total = 0usize;
    let mut bad: Vec<String> = Vec::new();
    let mut k_diverge: Vec<String> = Vec::new();
    let mut declined: Vec<String> = Vec::new();
    for f in &files {
        let (ok, mut b) = compare_recursors(f, &mut k_diverge, &mut declined);
        total += ok;
        bad.append(&mut b);
    }
    // **No designed fixture is refused by the frontend any more.** It used to
    // be exactly one — `nested_shapes.ndjson`, for being nested — and the
    // oracle's blind spot was that file. `LoadOptions::nested` opens it here,
    // so all four of its nested declarations and all nine of their recursors
    // are compared against Lean's. The corpus gate is a separate decision and
    // stays shut; `mini/tests/nested.rs` pins both halves.
    declined.sort();
    assert_eq!(declined, Vec::<String>::new(), "the set of fixtures this oracle cannot see changed");
    assert!(bad.is_empty(), "{} recursor(s) differ from the export:\n{}", bad.len(), bad.join("\n"));
    // **Every K-likeness divergence is the parameter-sort one**, which the
    // comparison above recognises by cause and records instead of failing on;
    // anything it did not recognise is already in `bad`. What is asserted here
    // is only that the recognised set is not *empty*: the exemption exists
    // because there really are such declarations, and an exemption with no
    // occupant is one that has stopped being exercised and should be deleted.
    assert!(
        !k_diverge.is_empty(),
        "no declaration at a bare parameter sort was compared — the K-likeness \
         exemption has no occupant left and should be removed"
    );
    // The designed fixtures alone carry this many; the corpus adds more.
    assert!(total >= 40, "only {total} recursors were compared — the oracle went quiet");
}

/// **The shared telescope is the whole block's**, at the four shapes that could
/// each have been got right by a builder that was wrong about the others.
///
/// The oracle above already compares these against Lean, and this asserts them
/// as literals anyway, because the two say different things. The oracle says
/// "mini agrees with Lean"; this says *what they agree on*, and it is the table
/// a reader needs to see that the sample covers what it claims: three motives
/// where there are three members, eight minors where the members have 3 + 3 + 2
/// constructors, a level parameter list one longer than the block's for a
/// `Type`-valued block and exactly as long for a `Prop`-valued one.
#[test]
fn a_members_recursor_binds_the_whole_blocks_motives_and_minors() {
    /// `(params, motives, minors, indices, level parameters)`.
    type Telescope = (u32, u32, u32, u32, usize);

    // fixture, recursor, (params, motives, minors, indices, level parameters)
    let want: [(&str, &str, Telescope); 9] = [
        // Three members, two constructors each; large-eliminating, so one
        // level parameter — the motive's — over a block that declares none.
        ("mutual_three_way_cycle", "B.rec", (0, 3, 6, 0, 1)),
        // 3 + 3 + 2 constructors: the minor count is the block's, not the
        // member's, and `Stms` has two of the eight.
        ("mutual_expr_stmt_ast", "Stms.rec", (0, 3, 8, 0, 1)),
        // Two shared parameters, and they are the recursor's first two binders.
        ("mutual_parameters", "PB.rec", (2, 3, 5, 0, 1)),
        // One index, per member — the recursor of `T1` binds `T1`'s.
        ("mutual_indices", "T1.rec", (0, 3, 4, 1, 1)),
        // `Prop` at two members: **no** extra level parameter, because a block
        // of more than one type never eliminates large.
        ("mutual_prop_even_odd", "Odd.rec", (0, 2, 3, 1, 0)),
        // …and the same at three, so the zero above is about `Prop` and not
        // about the block size.
        ("mutual_prop_even_odd", "M2.rec", (0, 3, 4, 1, 0)),
        // **The separating case.** `Sa` has one constructor and its only field
        // is a proof, so the per-constructor `elimToSort` walk says `true`; the
        // empty level list here is the block-size rule and nothing else.
        // `Even.rec` and `M2.rec` above would keep their empty lists if that
        // rule were deleted, because their first members have two constructors.
        ("mutual_prop_even_odd", "Sa.rec", (0, 2, 3, 0, 0)),
        // `OB` has no recursive constructor at all and still takes all three
        // motives and all five minors.
        ("mutual_one_recursive", "OB.rec", (0, 3, 5, 0, 1)),
        // Two declared levels plus the motive's: three, and the oracle above
        // is what says the motive's is the *first* of them.
        ("mutual_universe_polymorphic", "UC.rec", (2, 3, 4, 0, 3)),
    ];
    for (file, rec, shape) in want {
        let opts = LoadOptions { mutual: true, nested: false, keep_export_recursors: false, ..Default::default() };
        let loaded = load_with(&fixture(file), opts).expect("load");
        let mut env = Environment::empty();
        for d in &loaded.decls {
            mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{file}: {e}"));
        }
        let n = rec.split('.').fold(Name::Anon, |p, s| Name::str(&p, s));
        let Some(ConstantInfo::Recursor {
            lparams, num_params, num_motives, num_minors, num_indices, ..
        }) = env.get(&n)
        else {
            panic!("{file}: no recursor {rec}")
        };
        assert_eq!(
            (*num_params, *num_motives, *num_minors, *num_indices, lparams.len()),
            shape,
            "{file}: {rec}'s telescope"
        );
    }
}
