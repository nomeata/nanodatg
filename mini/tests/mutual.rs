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
//! * **Zone A takes a mutual block.** `kernel::add_block` checks every member,
//!   computes one recursor per member over one shared motive and minor
//!   telescope, and the ι rules fire. That is what this file measures.
//! * **Zone B does not.** The block reaches `ledger::fill_declaration`, which
//!   records `ind-spec(T: mutual)` against every member, every constructor and
//!   every eliminator, so a use site reports that reason rather than a bare
//!   miss. Every fixture is therefore *accepted and wholly untranslated* —
//!   exit 4.
//! * **The frontend still declines by default.** `--mutual` opens the gate;
//!   without it the file is exit 2, as it has always been. `convert::LoadOptions`
//!   says why that is a separate decision, and both halves are pinned below.
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
const FIXTURES: [(&str, &str); 8] = [
    ("mutual_three_way_cycle", "A"),
    ("mutual_expr_stmt_ast", "Exp"),
    ("mutual_parameters", "PA"),
    ("mutual_indices", "T0"),
    ("mutual_prop_even_odd", "Even"),
    ("mutual_one_recursive", "OA"),
    ("mutual_universe_polymorphic", "UA"),
    ("mutual_iota_reduction", "A"),
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
    cmd.arg("--verbose");
    if gate {
        cmd.arg("--mutual");
    }
    let out = cmd.arg(fixture(name)).output().expect("spawn mini");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
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

/// **With the gate open, the kernel accepts every one of them — and reports the
/// whole block as untranslated, by name.**
///
/// Exit 4, not 0 and not 2: the file *was* accepted, and what is untrue is the
/// claim that all of it was translated. The `waiting:` row is asserted rather
/// than counted because the reason is the measurement: `ind-spec(T: mutual)`
/// says zone B refused a shape its `DeclSpec` cannot express, which is where
/// the aux encoding will land. A bare `no-interp(T)` would mean the block had
/// reached zone B and fallen through — a different bug with the same count.
#[test]
fn with_the_gate_open_the_kernel_accepts_and_zone_b_says_why_it_did_not() {
    // The members whose *reason* is asserted. Every fixture's whole block is
    // recorded; these are the ones a use site actually reaches, so these are
    // the ones whose reason reaches the row.
    let blocks: [(&str, &[&str]); 8] = [
        ("mutual_three_way_cycle", &["A", "B", "C"]),
        ("mutual_expr_stmt_ast", &["Exp", "Stm", "Stms"]),
        ("mutual_parameters", &["PA", "PB", "PC"]),
        ("mutual_indices", &["T0", "T1", "T2"]),
        ("mutual_prop_even_odd", &["Even", "Odd", "M0", "M1", "M2", "Sa", "Sb", "Ka", "Kb"]),
        ("mutual_one_recursive", &["OA", "OB", "OC"]),
        ("mutual_universe_polymorphic", &["UA", "UB", "UC"]),
        ("mutual_iota_reduction", &["A", "B", "C"]),
    ];
    for (name, members) in blocks {
        let (code, stdout) = run(name, true);
        assert_eq!(
            code,
            Some(4),
            "{name}: expected accept-with-untranslated (exit 4):\n{stdout}"
        );
        assert!(stdout.contains("\taccept\t"), "{name} was not accepted:\n{stdout}");
        let w = waiting(&stdout);
        for m in members {
            let key = format!("ind-spec({m}: mutual)");
            assert!(
                w.contains_key(&key),
                "{name}: no `{key}` among {:?}\n{stdout}",
                w.keys().collect::<Vec<_>>()
            );
        }
        // Nothing may be waiting on a *bare absence* of a block member: that
        // would mean the reason table was not written and the miss path
        // answered with its fallback.
        for m in members {
            assert!(
                !w.keys().any(|k| k.starts_with(&format!("no-interp({m}"))),
                "{name}: {m} reported as absent rather than as mutual:\n{stdout}"
            );
        }
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
    assert_eq!(code, Some(4), "the ι fixture was not accepted:\n{stdout}");
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
/// **Acceptance only.** The exit code is 4 because the file's evidence axis is
/// not clean — the three recursors and the three rule theorems have no
/// `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` today. That is a gap in the *ordinary* pipeline, not in
/// anything mutual, and it is not pinned here: pinning a number that belongs to
/// another seat's live work would make this test fail for reasons it is not
/// about.
#[test]
fn the_aux_encoding_makes_every_recursor_rule_reflexivity() {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--acceptance-only")
        .arg(fixture("mutual_aux_encoding"))
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert_eq!(
        out.status.code(),
        Some(0),
        "the aux encoding was not accepted — a rule that is not `rfl` lands here:\n{stdout}"
    );
    assert!(
        stdout.contains("accept\t19 declarations"),
        "the aux fixture's declaration population changed:\n{stdout}"
    );
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

/// A constructor's field count: its telescope minus the parameters.
fn num_fields(env: &Environment, ctor: &Name, np: usize) -> Option<usize> {
    let ConstantInfo::Opaque { ty, .. } = env.get(ctor)? else { return None };
    let mut n = 0usize;
    let mut cur = ty.clone();
    while let Expr::Forall { body, .. } = &*cur {
        let b = body.clone();
        cur = b;
        n += 1;
    }
    n.checked_sub(np)
}

/// Compare every recursor mini generated for `path` against the export's own.
/// Returns `(matched, complaints)`; `Quot`'s two eliminators are skipped,
/// because the export declares them as `quot` entries and not as recursors.
fn compare_recursors(path: &Path, k_diverge: &mut Vec<String>) -> (usize, Vec<String>) {
    let stem = path.file_name().unwrap().to_string_lossy().to_string();
    let opts = LoadOptions { mutual: true, keep_export_recursors: true };
    let loaded = match load_with(path, opts) {
        Ok(l) => l,
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
            // mini's.** `PUnit : Sort u` has one fieldless constructor, and the
            // two kernels ask different questions about `u`: mini-lean's
            // `Environment.add` writes `if indLevel.isNotZero then none`, and
            // Lean's `init_k_target` writes `if is_zero(level) then …`. A bare
            // level *parameter* is neither provably zero nor provably nonzero,
            // so mini says K-like and Lean says not.
            //
            // Not corrected here: mini is a port of mini-lean and this is the
            // port being faithful, and changing it moves the acceptance axis on
            // seven corpus exports. It costs nothing observable — Lean reaches
            // the same conversions through unit-like eta, which mini also has —
            // but it is a real difference and it is collected by name below
            // rather than waved through by the comparison.
            k_diverge.push(format!("{stem}: {n}: mini {} export {}", k_type.is_some(), er.is_k));
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
    for f in &files {
        let (ok, mut b) = compare_recursors(f, &mut k_diverge);
        total += ok;
        bad.append(&mut b);
    }
    assert!(bad.is_empty(), "{} recursor(s) differ from the export:\n{}", bad.len(), bad.join("\n"));
    // **The K-likeness divergence is exactly `PUnit.rec` and nothing else.**
    // The comparison above records it instead of failing on it, for the reason
    // written at that site; this is what keeps the exemption from widening. A
    // new name here is a new divergence and must be read, not absorbed.
    let others: Vec<&String> =
        k_diverge.iter().filter(|d| !d.contains(" PUnit.rec:")).collect();
    assert!(others.is_empty(), "a new K-likeness divergence:\n{others:?}");
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
        let opts = LoadOptions { mutual: true, keep_export_recursors: false };
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
