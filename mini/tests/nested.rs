//! **Nested inductives** — where the arc stands, and the measurements that
//! decided its shape.
//!
//! # Where the arc stands
//!
//! * **Zone A takes a nested declaration.** [`mini::nested`] specialises it
//!   into a mutual block with a *mimic* copy of every container it nests into,
//!   hands that straight back to `kernel::add`, and **restores** what comes
//!   out — the copy back to the real container, the copy's constructors back to
//!   the real ones, and the copy's recursor to `T.rec_k`.
//! * **The generated recursors are the ones Lean exports.** Not by inspection:
//!   `mini/tests/mutual.rs`'s `the_generated_recursors_are_the_ones_lean_exports`
//!   compares mini's generated recursor against the export's own — type, rule
//!   count, rule order and every rule's right-hand side — and both nested
//!   fixtures are now in its sweep. That covers `numNested = 1` at a recursive
//!   and a non-recursive container, `numNested = 2` at one container twice
//!   (`DTree`) and at **two different** containers (`BTree`, `nested_iota`).
//! * **The ι rules fire.** `nested_iota.lean` states all nine of them as `rfl`
//!   theorems, so Lean's kernel checks them at export time and mini's kernel
//!   must reduce the same redexes or reject the file. It accepts.
//! * **The frontend still declines by default.** `--nested` opens the gate,
//!   and it is a *second* gate rather than `--mutual`'s, for the reason below.
//! * **Zone B takes one, through its model.** [`mini::nested_splice`] puts the
//!   generated model into the run beside the primitives and keys `⟦T⟧`,
//!   `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧` onto it;
//!   [`every_pair_of_the_shape_fixture_certifies_once_the_model_is_keyed`] is
//!   `nested_shapes` going from two derived pairs out of ten to **all
//!   eighty-one**, and
//!   [`the_nested_declarations_interpretation_is_its_models`] is the same
//!   claim next to the input that tells a table from a name rule.
//!   `ind-spec(T: nested occurrence)` is no longer any nested declaration's
//!   answer.
//! * **And every ι rule of every nested recursor carries a certificate.**
//!   [`every_rule_the_model_proved_fires_across_the_whole_specification`] is
//!   `nested_iota` at **134 of 134** pairs with `gapped 0` — fourteen rules,
//!   seven recursors, three declarations, at every shape the arc has. It is
//!   `#[ignore]`d and its own note says what that costs and what ignoring it
//!   gives up; [`the_iota_dispatch_arm_fires_the_rules_its_model_proved`] is
//!   the same claim at one declaration, in CI, at five minutes.
//!
//! # What the acceptance axis does **not** check, stated plainly
//!
//! The block that is checked is the specialised one and the declarations that
//! are installed are the restored ones. The restoration is a **rewrite, not a
//! derivation**: `List Tree` and the mimic are isomorphic and not equal, and
//! the round trip that would identify them is propositional —
//! [`the_round_trip_the_encoding_would_need_is_not_definitional`] is that
//! sentence as a check the kernel runs, with two closed instances accepted
//! beside it so the rejection is about the variable and not about the term
//! being nonsense.
//!
//! So `Tree.rec_1`'s ι rule on `List.cons` enters the environment as an
//! **assumption transported along an isomorphism nothing here checks**. The
//! export oracle says mini's rule is the same rule Lean declares; it does not
//! say either of them is sound.
//!
//! `thesis.txt` says the general form in one line — mutual inductives, nested
//! inductive types and coinductive types "can all be encoded using regular
//! inductives, although some definitional equalities may fail to hold in the
//! encodings". This is which equality, for this encoding.
//!
//! # The half of that which is no longer an assumption
//!
//! `nested_model` is the model, written out and checked: no nested declaration
//! at all, the specialised block as an ordinary `mutual`, `Tree` and its
//! constructors as `def`s over it, and **both** recursors as `def`s — including
//! the one whose major premise is `List Tree` and whose rules are the real
//! `List`'s own constructors. Its four ι rules are theorems with proofs, and
//! [`the_model_of_a_nested_recursor_is_checked`] is mini's kernel checking
//! every one of them.
//!
//! That says the rule mini installs is **satisfiable** — a `Tree.rec_1` obeying
//! it exists over the real `List`. The keying says mini's *interpretation* of
//! the primitive is that one. What says the rule **fires** with a certificate is
//! [`mini::iota_model`], the fourth ι dispatch arm, and
//! [`the_iota_dispatch_arm_fires_the_rules_its_model_proved`] is it doing so.
//! The corpus still never sees a nested file.
//!
//! [`two_of_the_four_model_iota_rules_are_definitional_and_two_are_not`] is the
//! price, measured rather than described: `leaf` and `List.nil` survive the
//! encoding definitionally, `Tree.node` and `List.cons` do not, and each of the
//! two is one transport lemma.
//!
//! # …and the whole of it, generated, for every shape rather than for `Tree`
//!
//! `modelgen` builds that development as an export filter, and
//! [`the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`] runs it
//! over all **eight** nested declarations in this directory: the block, the
//! carrier, `pack`/`unpack` and both round trips per mimic, the declared type's
//! constructors, one recursor per block member, one congruence per mimic, and
//! **one ι theorem per rule of every recursor** — thirty-six of them, each a
//! theorem with a proof and each through `kernel::add`. Nothing declines.
//!
//! Well-typedness is not the claim, so the statements are compared against zone
//! A's own in [`the_generated_round_trips_state_the_isomorphism`]: the round
//! trips against a statement this file rebuilds from the plan, and the
//! recursors and **their rules** against the `T.rec_k` that `nested::add`
//! installed. A generator that produced a well-typed recursor, or a well-typed
//! equation, of some *other* type passes the kernel and fails there.
//!
//! [`mini::nested_splice`] is what that generation is now *for*: the model goes
//! into the run and `IndApparatus::model_of` points the export's names at it.
//!
//! # The fixtures
//!
//! | fixture | what it covers |
//! | --- | --- |
//! | `nested_shapes` | the declaration side: depth, container parameterised, copy recursive, container also used un-nested, and `BTree.node : Pair BTree → Pair BTree → BTree`, two packed positions in one **root** constructor |
//! | `nested_iota` | the **rules**, as fourteen `rfl` theorems; `numNested = 2` at two *different* containers; a container at an unrelated type in the same constructor list; a nested type with **parameters of its own** |
//! | `nested_iota_arm` | the ι *dispatch*, at the smallest input carrying both rule shapes: one nested declaration, two recursors, four rules — two the model proves by `Eq.refl` and two it **transports** — all four firing, in five minutes |
//! | `nested_deep` | `DTree`'s inner `cons : M₁ → M₀ → M₀`, two packed positions in one **mimic** constructor — the other side of the transport fold's case split |
//! | `nested_roundtrip` | why the auxiliary encoding does not extend, as a theorem the kernel rejects |
//! | `nested_model` | the model: pack/unpack, both round trips, both recursors and all four ι rules, none of them primitive and none of them assumed |
//! | `nested_keying` | the **join**: two nested declarations of one shape, one modelled and one whose model's name the file has taken — the input that tells `model_of` from a name rule, and the only one here cheap enough for an inner loop |

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

// SKIP is not PASS. See ci/skip-guard.rs. The one test here that needs the
// Lean-built `modelgen` binary skips without it, and cargo calls that `ok`.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

use mini::convert::{load_with, LoadOptions};
use mini::env::{ConstantInfo, DefKind, Declaration, Environment};
use mini::expr::{app, app_n, bvar, forall, konst, lam, Level, Name, E};

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{name}.ndjson"));
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini [flags] <fixture>`, in a subprocess — `checker`'s parser reports a
/// declined export by calling `std::process::exit(2)`, which an in-process
/// harness cannot contain.
fn run(name: &str, flags: &[&str]) -> (Option<i32>, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_mini"));
    // The suite is hermetic — see `mini/src/modelgen.rs`. Every nested fixture
    // here is committed **already filtered**, which is what makes the model
    // `nested_splice::recognise` looks for be in the file at all.
    cmd.arg("--no-modelgen");
    for f in flags {
        cmd.arg(f);
    }
    let out = cmd.arg(fixture(name)).output().expect("spawn mini");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
}

/// `a.b`, as a two-component `Name` — `Name::simple("List.nil")` is a *single*
/// component whose string contains a dot, which is a different name and one no
/// export in this directory declares.
fn dot(a: &str, b: &str) -> Name { Name::str(&Name::simple(a), b) }

/// Every nested recursor the two fixtures declare, as `(type, recursor)`.
/// `Tree.rec_1` and `BTree.rec_2` are the ones that ι-reduce on **another
/// declaration's** constructors.
const NESTED_RECS: [(&str, &str); 7] = [
    ("Tree", "rec"),
    ("Tree", "rec_1"),
    ("BTree", "rec"),
    ("BTree", "rec_1"),
    ("BTree", "rec_2"),
    ("PT", "rec"),
    ("PT", "rec_1"),
];

/// The environment a fixture leaves behind when every declaration is added.
fn env_of(name: &str) -> Environment {
    let opts = LoadOptions { nested: true, ..Default::default() };
    let loaded = load_with(&fixture(name), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    env
}

/// **Nesting declines at the parser, and `--mutual` is not the switch.**
///
/// Two gates, not one. `--mutual` opens a block whose recursor rules the
/// kernel *derives*; `--nested` opens a declaration whose `T.rec_1` carries an
/// ι rule on another type's constructors that no acceptance-side check
/// justifies. Pinning both spellings is what says they are separate decisions.
///
/// The reason string is matched too: a fixture that failed to *parse* would
/// exit 2 as well and pass a bare status assertion while measuring nothing.
#[test]
fn a_nested_declaration_declines_and_only_its_own_gate_opens_it() {
    for f in ["nested_shapes", "nested_iota"] {
        // **Two gates and two reasons, and which one is reached depends on the
        // filter.** A fixture is committed *already filtered*
        // (`mini/src/modelgen.rs`), so `T._model.0 … T._model.{n−1}` — a
        // `mutual … end` block — stands in front of the nested declaration and
        // is the first thing either gate refuses. With `--mutual` open the
        // block is taken and the nested declaration is what stops the file, at
        // its own reason. Both are exit 2 and both name a gate; asserting the
        // pair is what says the two gates are still two decisions.
        for (flags, why) in [
            (&[][..], "declined: Mutual inductive"),
            (&["--mutual"][..], "declined: Nested inductive"),
        ] {
            let (code, stdout) = run(f, flags);
            assert_eq!(code, Some(2), "{f} at {flags:?} did not decline:\n{stdout}");
            assert!(
                stdout.contains(why),
                "{f} at {flags:?} declined for the wrong reason (wanted {why:?}):\n{stdout}"
            );
        }
        // **Accepted behind `--nested`, and asked in process.**
        //
        // *This spawned `mini --nested` and read the verdict word off the
        // first line. That is a whole run — parse, check, interpret — and
        // after the `modelgen` pipeline `nested_shapes` and `nested_iota` are
        // the two most expensive files in the directory: the model of each of
        // their seven nested declarations is now in the file and is
        // interpreted. The claim here is about the **gate**, which is
        // `convert::load_with`'s and is settled before a single declaration is
        // checked, so it is asked there.*
        let opts = LoadOptions { nested: true, ..Default::default() };
        assert!(
            load_with(&fixture(f), opts).is_ok(),
            "{f} still declined behind --nested"
        );
    }
}

/// **The nested recursors compute** — all fourteen rules, as `rfl` theorems
/// Lean's own kernel already checked.
///
/// `nested_iota.lean` is the specification: `Tree.rec` on `Tree.leaf` and
/// `Tree.node`, `Tree.rec_1` on `List.nil` and `List.cons`, and `BTree`'s three
/// recursors on `BTree`'s, `Box`'s and `List`'s constructors. Each is stated at
/// **variable** motives, minors and major, because a closed major reduces one
/// constructor at a time whatever the rule says.
///
/// `BTree` is `Lean.Syntax`'s shape at the smallest size that has it:
/// `{BTree, Box BTree, List BTree}` against `{Syntax, Array Syntax,
/// List Syntax}`, three motives, a copy of a **structure** over a copy of a
/// list, and one constructor carrying a container at an unrelated type
/// (`BTree.tag : List N → BTree`, for `Lean.Syntax.ident`'s
/// `List Lean.Syntax.Preresolved`).
///
/// `PT α` is the parameter axis: `Tree` and `BTree` have no parameters of
/// their own, so on both of them a treatment that dropped the block's
/// parameter telescope is the identity. `PT`'s copy of `List (PT α)` has to be
/// declared over `α` and referred to as `copy α`, and restored with the
/// parameter put back.
///
/// The negative control is the point of the second half:
/// [`the_theorems_are_accepted_because_the_rules_fire`] strips the rules and
/// asserts the same theorems are then rejected. Without it this test would
/// pass on an environment where `Eq` had been made trivial.
#[test]
fn the_nested_iota_rules_fire() {
    let env = env_of("nested_iota");
    for t in [
        "treeIotaLeaf",
        "treeIotaNode",
        "treeIota1Nil",
        "treeIota1Cons",
        "btreeIotaLeaf",
        "btreeIotaTag",
        "btreeIotaNode",
        "btreeIota1Mk",
        "btreeIota2Nil",
        "btreeIota2Cons",
        "ptIotaLeaf",
        "ptIotaNode",
        "ptIota1Nil",
        "ptIota1Cons",
    ] {
        assert!(
            env.get(&Name::simple(t)).is_some(),
            "{t} is not in the environment — the fixture stopped stating the rule"
        );
    }
    // The two recursors of `Tree` and the three of `BTree`, under the names the
    // export declares. `Tree._nested.1.rec` is this module's internal name and
    // must not be one of them.
    for (t, r) in NESTED_RECS {
        assert!(
            matches!(env.get(&Name::str(&Name::simple(t), r)), Some(ConstantInfo::Recursor { .. })),
            "{t}.{r} is not a recursor in the environment"
        );
    }
}

/// **The theorems above are accepted because the rules fire**, and not because
/// the kernel found some cheaper way to close an `Eq`.
///
/// The control removes the *rules* from every nested recursor — the types, the
/// motive and minor counts and the whole rest of the environment are untouched
/// — and re-adds the nine theorems. Every one of them must now be rejected. A
/// change that made `Eq` trivial, or that stopped checking a theorem's body
/// against its type, passes [`the_nested_iota_rules_fire`] and fails here.
#[test]
fn the_theorems_are_accepted_because_the_rules_fire() {
    let opts = LoadOptions { nested: true, ..Default::default() };
    let loaded = load_with(&fixture("nested_iota"), opts).expect("load");
    let mut env = Environment::empty();
    let mut thms: Vec<&Declaration> = Vec::new();
    for d in &loaded.decls {
        let n = d.name().to_string();
        if n.contains("Iota") {
            thms.push(d);
            continue
        }
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{n}: {e}"));
    }
    assert_eq!(thms.len(), 14, "the fixture stopped carrying fourteen rule theorems");

    // Sanity: with the rules in place they all go in.
    for d in &thms {
        let mut e = env.clone();
        mini::kernel::add(&mut e, d)
            .unwrap_or_else(|m| panic!("{} was rejected with the rules present: {m}", d.name()));
    }

    // The control: the same environment with every nested recursor's rule list
    // emptied.
    let mut blunt = env.clone();
    let mut stripped = 0usize;
    for (t, r) in NESTED_RECS {
        let n = Name::str(&Name::simple(t), r);
        let Some(ConstantInfo::Recursor {
            lparams,
            ty,
            num_params,
            num_motives,
            num_minors,
            num_indices,
            k_type,
            ..
        }) = blunt.get(&n).cloned()
        else {
            panic!("{t}.{r} is not a recursor")
        };
        blunt.consts.insert(
            n,
            ConstantInfo::Recursor {
                lparams,
                ty,
                num_params,
                num_motives,
                num_minors,
                num_indices,
                rules: Vec::new(),
                k_type,
            },
        );
        stripped += 1;
    }
    assert_eq!(stripped, NESTED_RECS.len(), "the control did not strip every nested recursor");
    for d in &thms {
        let mut e = blunt.clone();
        assert!(
            mini::kernel::add(&mut e, d).is_err(),
            "{} was still accepted with every nested ι rule removed — the theorem \
             is not measuring the reduction",
            d.name()
        );
    }
}

/// **The mimics do not survive into the environment.**
///
/// `Tree._nested.1` is this module's name for `List Tree` and is an artefact of
/// the encoding: it is checked in a scratch environment and never installed. A
/// consumer that found it — the census, the ledger, zone B — would be looking
/// at a declaration the export never made, and `mutual_aux`'s arc is the
/// precedent for what that costs.
///
/// Asserted on the *whole* name table rather than on the names this module
/// happens to mint, so a future mimic under a different spelling is caught too.
#[test]
fn the_specialised_copies_are_not_installed() {
    for f in ["nested_shapes", "nested_iota"] {
        let env = env_of(f);
        let leaked: Vec<String> = env
            .consts
            .keys()
            .map(Name::to_string)
            .filter(|n| n.contains("_nested"))
            .collect();
        assert!(leaked.is_empty(), "{f} leaked the specialised copies: {leaked:?}");
        // …and the real containers are untouched, which is what `listOfN` and
        // `pairOfN` exist to catch: a treatment that replaced `List` by its
        // copy would break exactly those and nothing else.
        for n in [Name::simple("List"), dot("List", "nil"), dot("List", "cons"), dot("List", "rec")]
        {
            assert!(env.get(&n).is_some(), "{f} lost the real {n}");
        }
    }
}

/// **Every nested declaration in the fixtures gets exactly the recursors the
/// export declares, and no others.**
///
/// The oracle in `mini/tests/mutual.rs` compares the recursors that exist on
/// both sides; this is the count, which the oracle does not check — a
/// treatment that generated `Tree.rec` and forgot `Tree.rec_1` would satisfy
/// every comparison it made.
#[test]
fn the_recursor_count_is_one_per_specialised_member() {
    for (f, expected) in [
        ("nested_shapes", &[("Tree", 2), ("PTree", 2), ("DTree", 3), ("BTree", 2)][..]),
        ("nested_iota", &[("Tree", 2), ("BTree", 3), ("PT", 2)][..]),
    ] {
        let env = env_of(f);
        for (ind, n) in expected {
            let got: Vec<String> = env
                .consts
                .keys()
                .filter(|k| env.owner(k) == Some(&Name::simple(ind)))
                .filter(|k| matches!(env.get(k), Some(ConstantInfo::Recursor { .. })))
                .map(Name::to_string)
                .collect();
            assert_eq!(got.len(), *n, "{f}: {ind} has recursors {got:?}, expected {n}");
        }
    }
}

/// The `key=value` pairs of one tab-separated row of `--verbose` output.
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

/// Every `waiting:` key of the `evidence` row, prefix stripped — the set of
/// reasons a fixture is blocked on. Asserted as a *set* and not as a count, for
/// `mini/tests/designed.rs`'s reason: a count is equally true of a different
/// blockage.
fn waiting(stdout: &str) -> BTreeMap<String, u64> {
    row(stdout, "evidence")
        .into_iter()
        .filter_map(|(k, v)| k.strip_prefix("waiting:").map(|s| (s.to_string(), v)))
        .collect()
}

/// **The keying: `⟦Tree⟧` is the generated model's carrier, and it is that
/// because a table says so.**
///
/// `nested_keying.lean` puts two nested declarations of the same shape side by
/// side and takes one name away. `Tree` gets a model, and its two `def`s — one
/// naming the type former, one naming a constructor — certify, which they never
/// did before: the whole population used to come back
/// `ind-spec(Tree: nested occurrence)`. `UTree` is the same declaration with
/// `UTree._model.self` already declared by the file, so
/// `modelgen` answers `nested model name taken`, nothing is keyed, and its two
/// `def`s must **wait**.
///
/// # What each number is, and which mutation moves it
///
/// The counts are exact rather than bounded, because that is what tells the
/// table apart from a name rule. Under
/// `⟦T⟧ := ⟦T._model.self⟧`-by-spelling, the file's own `UTree._model.self` is
/// in the store — it is an ordinary `def` at an ordinary type — so `⟦UTree⟧`
/// resolves to `⟦N⟧`, `utreeTy` certifies against a model nobody built, and
/// this reads `constEv = 21` with one waiting pair instead of two. That is the
/// `_auxCarrier` failure, and it is the input that produces it.
///
/// A second mutation the exact reason kills: making the missing-entry case
/// *fall through* to the class-(T) walk instead of declining. The walk answers
/// `ind-spec(UTree: nested occurrence)` — true, and the least informative of
/// the reasons there are — so the counts are unchanged and only the string
/// moves. It is asserted as a string for exactly that reason.
///
/// # What the filter changed here, in numbers
///
/// *This test read `pairs = 22, constEv = 20, typeEv = 21` and
/// `untranslated: declarations = 1, eliminators = 4`, the four being
/// `Tree.rec` and `Tree.rec_1` at the two motive levels
/// `checker::instantiations`' `DEFAULT_LEVELS` pads the schedule with. The
/// file applies neither, and the splice — which put the model in itself — kept
/// the recursor half out on a measured cost argument: 27 000 conversions
/// against over 950 000.*
///
/// *There is nothing left to keep out. `modelgen` splices `Tree`'s whole
/// tower into the export, so `pack`, `unpack`, both round trips, both
/// recursors and all four ι theorems are **declarations of the file** and
/// `Ledger::run` opens a pair for each. `untranslated: eliminators` is **0**:
/// `Tree.rec` and `Tree.rec_1` are keyed at the σ they are scheduled at,
/// which is what the propagation in `nested_splice::recognise` is for. The
/// file certifies strictly more than it did.*
///
/// *`pairs` is **63** and was 45, and the eighteen are `MODELGEN.md` §1.7's
/// composition: the model of `Tree` is a `mutual … end` block, and the filter
/// now models **that** too, so `Tree._model.0._model.tag`, `.aux`, the three
/// carriers, the constructors, the recursors and their ι theorems are also
/// declarations of the file. `constEv` 61 and `typeEv` 62 are again
/// "everything but `UTree`'s two", so every one of the eighteen certifies —
/// which is the interesting part, and the reason this number is pinned rather
/// than the file merely being loaded.*
///
/// *It also costs strictly more, and the number is the reason this test is at
/// five and a half minutes: **9 775 526 conversions against 28 570**, 342×,
/// for 2× the pairs. That is not a regression in this module — it is the
/// honest price of the model being in the file, and `MINI-HANDOFF.md` carries
/// where it lands and what would move it.*
#[test]
fn the_nested_declarations_interpretation_is_its_models() {
    let (code, out) = run("nested_keying", &["--verbose", "--nested"]);
    assert_ne!(code, Some(2), "nested_keying declined:\n{out}");
    let e = row(&out, "evidence");
    assert_eq!(
        (e.get("pairs"), e.get("constEv"), e.get("typeEv"), e.get("unsealed")),
        (Some(&63), Some(&61), Some(&62), Some(&0)),
        "the derived population changed:\n{out}"
    );
    assert_eq!(
        waiting(&out),
        [("ind-spec(UTree: nested model over a later declaration)".to_string(), 2)]
            .into_iter()
            .collect(),
        "the keying's blockage is not the one this fixture is about:\n{out}"
    );
    // **`eliminators = 0`**, and that is the propagation working rather than
    // nothing being asked: `Tree.rec` and `Tree.rec_1` are keyed at the σ the
    // pre-pass scheduled them at and `Tree._model.rec_k` is scheduled there
    // too, so neither recursor declines. `UTree`'s declaration is the one
    // thing left, and it is the fixture's point.
    let u = row(&out, "untranslated");
    assert_eq!(
        (u.get("declarations"), u.get("eliminators")),
        (Some(&1), Some(&0)),
        "the untranslated set moved:\n{out}"
    );
    assert_eq!(
        u.get("notrans:ind-spec(UTree: nested model over a later declaration)"),
        Some(&1),
        "the squatter's declaration must decline by name:\n{out}"
    );
}

/// **The four `def`s of `nested_shapes` that used to wait now certify, and so
/// does every declaration of the model behind them.**
///
/// The companion to the test above at the *shape* axis rather than the keying
/// axis: four nested declarations, one per row of this file's fixture table —
/// depth two, a parameterised container, a recursive copy, and two packed
/// positions in one root constructor — and eight `def`s over them.
///
/// `constEv == pairs` is the claim, and the absolute number is pinned beside it
/// because the model **changes the denominator**: its declarations are `Def`s
/// and `Ledger::run` opens a pair for each, so `pairs` went from 10 to 81 when
/// this landed. A reading that only checked the ratio would be equally
/// satisfied by a run that saw no model at all and by one that saw a model
/// that certifies trivially.
///
/// # `#[ignore]`, and the number that put it there
///
/// **This fixture no longer completes.** Measured on the filtered export at
/// the test profile: `mini --nested` ran for **33m20 and was killed by the
/// allocator at a 12 GB cap** (`memory allocation of 56 bytes failed`,
/// SIGABRT). Before the `modelgen` pipeline it was 1m40.
///
/// The cause is not in this module and is not a regression in what mini
/// *does*: `nested_shapes` declares four nested types, `modelgen` splices
/// **66 declarations** of model in front of them, and every one is a
/// declaration of the file that `Ledger::run` opens a pair for and interprets.
/// The old splice pruned the model to what the file demanded and this file
/// demands almost none of it; a filtered export has no such half. The
/// companion numbers are in `nested_keying` (9 775 526 conversions against
/// 28 570, 5m21) and `nested_iota_arm` (9 818 364, 5m24) — both of which still
/// run, and which is why this one is ignored rather than deleted: the claim is
/// unchanged and it will be measurable again when the interpretation of a
/// model tower is affordable. `CACHING-DESIGN.md`'s narrowing is **not** that
/// lever, measured: with `frame_put`'s `Gap` gate removed entirely,
/// `nested_keying` went 5m20 → 5m14.
///
/// **Neither is the level schedule, measured.** Truncating *every* declaration
/// to a single σ — the optimistic bound on any scheduling-side narrowing, and
/// not a fix, since it drops demanded σ — makes this fixture **complete** in
/// 23m46 at 42 305 813 conversions inside the same 12 GB cap, but certifying
/// less: `pairs` 126, `constEv` 96, `lazyFills` 363, and nine
/// `waiting:no-interp(X._model.k.rec)` rows. So the schedule is what stands
/// between this fixture and the memory cap, and **not** what stands between it
/// and being affordable; 42 M conversions is a floor on what monomorphization
/// can leave behind. `MEASUREMENTS.md` carries the companion census on
/// `nested_keying`, where the doubling is 8 pairs of 31 and worth 2.38× at
/// most.
///
/// *The assertions below are the pre-filter ones and are **known stale**, and
/// `MODELGEN.md` §1.7's composition has since moved them again — the file now
/// carries a second model per nested declaration, worth +18 pairs each on the
/// two fixtures that were re-measured. They are left in place rather than
/// guessed at because a number nobody measured is worse than one that is
/// marked as unmeasured; re-measure before
/// un-ignoring.*
#[test]
#[ignore = "33m20 and OOM at 12 GB on the filtered export — see the note above"]
fn every_pair_of_the_shape_fixture_certifies_once_the_model_is_keyed() {
    let (code, out) = run("nested_shapes", &["--verbose", "--nested"]);
    assert_ne!(code, Some(2), "nested_shapes declined:\n{out}");
    let e = row(&out, "evidence");
    assert_eq!(
        (e.get("pairs"), e.get("constEv"), e.get("typeEv"), e.get("unsealed")),
        (Some(&81), Some(&81), Some(&81), Some(&0)),
        "the derived population changed:\n{out}"
    );
    assert_eq!(waiting(&out), BTreeMap::new(), "something is still waiting:\n{out}");
    assert_eq!(
        row(&out, "untranslated").get("declarations"),
        Some(&0),
        "a nested declaration is still untranslated:\n{out}"
    );
}

/// **The fourth ι dispatch arm, at the smallest input that exercises both of
/// its rule shapes.**
///
/// `nested_iota_arm` is one nested declaration, its two recursors and all four
/// of its rules. All four are `rfl` in Lean and Lean's own kernel checked all
/// four; what differs is the **model's** proof. `Tree.leaf` and `List.nil`
/// carry no field at the mimic, so the model's rule for them is `Eq.refl`;
/// `Tree.node` and `List.cons` each carry one, so their rules **transport**
/// along `unpackPack`. **The arm fires all four**, and `45/45` with an empty
/// `waiting` map is the claim.
///
/// *(This asserted `34` of `36` and `waiting` = one `no rule` per recursor: the
/// two transporting rules were not seeded, because their own constant typings
/// had no endpoint and `eq_cash` had nothing to read. The residual behind those
/// typings was `Checker::proof_point_leg` — `whnf` on a proof-valued spine —
/// and with it closed the seeding is total and the split is gone.
/// [`mini::iota_model::fire`] still declines by that reason —
/// `recursor(T.rec_k: iota: the model has no rule for this constructor at this
/// level)` — for a rule at a σ nothing keyed, and it is still the discriminator
/// its module note is about; what no longer has an occupant is a rule of a
/// *keyed* recursor declining by it, so the `no_rule` helper that spelled the
/// string went with the two assertions that read it.)*
///
/// # What the `modelgen` pipeline moved, in numbers
///
/// *`39 / 39` became `45 / 45`. The six extra pairs are the model's own
/// declarations that the splice used to prune away and the filter now writes
/// into the file — the ledger opens a pair for each, and every one certifies.
/// `waiting` is still empty, `gapped` still 0, `untranslated` still 0.*
///
/// *And `45 / 45` became **`63 / 63`**, which is `MODELGEN.md` §1.7's
/// composition: `Tree`'s model is a `mutual … end` block and the filter now
/// models that block too, so its tag, carrier, type formers, constructors,
/// recursors and ι theorems are eighteen more declarations of the file.
/// Every one of them certifies — `waiting` still empty, `gapped` still 0,
/// `untranslated` still `(0, 0)` — and that is the claim: `mini` reads the
/// second layer with no gate of its own and nothing left over.*
///
/// *The cost: **9 818 364 conversions in 5m24** against 6 031 316 in about
/// five minutes. 63% more conversions for 15% more pairs and the same order of
/// wall clock. This is the cheapest of the three end-to-end nested tests that
/// still run in CI, and `ci/check.sh` runs this file three times (#110).*
#[test]
fn the_iota_dispatch_arm_fires_the_rules_its_model_proved() {
    let (code, out) = run("nested_iota_arm", &["--verbose", "--nested"]);
    assert_ne!(code, Some(2), "nested_iota_arm declined:\n{out}");
    let e = row(&out, "evidence");
    assert_eq!(
        (e.get("pairs"), e.get("constEv"), e.get("typeEv"), e.get("unsealed")),
        (Some(&63), Some(&63), Some(&63), Some(&0)),
        "the derived population changed:\n{out}"
    );
    assert!(
        waiting(&out).is_empty(),
        "a rule of a keyed recursor did not fire:\n{out}"
    );
    // **Not vacuously**: the arm has to have *run*. A run in which the fixture
    // stopped applying its recursors would have an empty `waiting` map too.
    let c = row(&out, "convs");
    assert_eq!(c.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
    assert!(
        c.get("moved").copied().unwrap_or(0) > 0,
        "the fixture performs no non-trivial conversion at all:\n{out}"
    );
    let u = row(&out, "untranslated");
    assert_eq!(
        (u.get("declarations"), u.get("eliminators")),
        (Some(&0), Some(&0)),
        "a nested declaration or one of its eliminators has no translation:\n{out}"
    );
}

/// **The same arm over the whole specification, and the residual named.**
///
/// `nested_iota` is the one fixture that applies a nested recursor at every
/// shape the arc has: `numNested = 2` at two *different* containers, a
/// container at an unrelated type in the same constructor list, and a nested
/// type with parameters of its own. Seven recursors, all keyed, with
/// `untranslated eliminators = 0`.
///
/// **All fourteen rules fire**, at every shape the arc has — and this is the
/// finish line of the nested arc, which is why it is asserted and why it is
/// `#[ignore]`d.
///
/// Every one of the fourteen is `rfl` in Lean. Seven of them are `Eq.refl` in
/// the *model* too and seven **transport** along `unpackPack`; the arm fires
/// all fourteen, `constEv = pairs = 134`, `gapped 0`, `waiting` empty.
///
/// *(This asserted `124 / 117` with seven `no rule` declines, one per recursor,
/// and named the residual `#90(b)`. It was neither `#90(b)` nor anything in
/// `nested_splice`: it was `Checker::proof_point_leg`, `whnf` on a proof-valued
/// spine. The pair count moves 124 → 134 because the seven newly seeded ι
/// theorems and the three transport lemmas behind them are `Def`s the ledger
/// opens pairs for, and all ten certify.)*
///
/// # Why it does not run in CI, stated rather than absorbed
///
/// ```text
///                  conversions      time     peak RSS   pairs / constEv
/// before          3 878 982        2m27                 124 / 117
/// after          51 830 194       25m52      > 7.5 G    134 / 134
/// ```
///
/// **13× the conversions and past the 4 GB a seat runs under** — a run capped
/// there is killed at about nine minutes. This file already takes 336 s and
/// runs three times in `ci/check.sh` (#110 is live about that), so leaving this
/// test on would add some seventy-five minutes and an OOM risk to every check.
///
/// What is lost by ignoring it is stated too: this is the **only** measurement
/// of the evidence axis at `numNested = 2` over two different containers, at a
/// container of an unrelated type in the same constructor list, and at a nested
/// type with parameters of its own.
/// [`the_iota_dispatch_arm_fires_the_rules_its_model_proved`] keeps the arm
/// itself in CI at one declaration and five minutes, and the *acceptance* and
/// *keying* axes of this fixture are still measured by
/// [`the_nested_iota_rules_fire`], [`the_theorems_are_accepted_because_the_rules_fire`]
/// and the generated-model sweeps, none of which pay the interpretation pass.
///
/// Run it with `cargo test -p mini --test nested -- --ignored
/// every_rule_the_model_proved`, and give it more than 4 GB.
///
/// **The `134` below is stale and is marked rather than guessed.**
/// `MODELGEN.md` §1.7's composition puts a second model in the file per nested
/// declaration — `Tree`, `BTree` and `PT` here — and the two fixtures that
/// were re-measured each gained exactly 18 pairs, all certifying. Nobody has
/// run this one since; re-measure before trusting the number, and note that
/// the memory it needs went up with it.
#[test]
#[ignore = "51.8 M conversions, 26 minutes and over 7.5 GB — see the note"]
fn every_rule_the_model_proved_fires_across_the_whole_specification() {
    let (code, out) = run("nested_iota", &["--verbose", "--nested"]);
    assert_ne!(code, Some(2), "nested_iota declined:\n{out}");
    let e = row(&out, "evidence");
    assert_eq!(
        (e.get("pairs"), e.get("constEv"), e.get("typeEv"), e.get("unsealed")),
        (Some(&134), Some(&134), Some(&134), Some(&0)),
        "the derived population changed:\n{out}"
    );
    // Seven recursors, and every one of them keyed: the eliminator column is
    // the half of the keying this fixture is the only witness for.
    let u = row(&out, "untranslated");
    assert_eq!(
        (u.get("declarations"), u.get("eliminators")),
        (Some(&0), Some(&0)),
        "a nested declaration or one of its eliminators has no translation:\n{out}"
    );
    assert!(waiting(&out).is_empty(), "a rule of a keyed recursor did not fire:\n{out}");
    let c = row(&out, "convs");
    assert_eq!(c.get("gapped"), Some(&0), "a conversion is still gapped:\n{out}");
}

/// `Sort 1` — the sort `List Tree` lives at, and the level `Eq` is used at.
fn one() -> Rc<[Level]> { vec![Level::Succ(Rc::new(Level::Zero))].into() }

fn k(n: &str) -> E { konst(Name::simple(n), Vec::new().into()) }

fn dotted(a: &str, b: &str) -> E { konst(Name::str(&Name::simple(a), b), Vec::new().into()) }

/// `Eq.refl.{1}` — `Eq`'s constructor carries `Eq`'s own level list, and it is
/// the one place in this file where a constant is not at no levels.
fn eq_refl() -> E { konst(Name::str(&Name::simple("Eq"), "refl"), one()) }

/// **The equation the nested encoding would need, and the kernel's answer.**
///
/// `Eq (fromAux (toAux l)) l` at a variable `l : List Tree`, proved by
/// `Eq.refl`. Mini must reject it — and the two closed instances beside it must
/// be accepted, because that is what says the rejection is about the variable
/// and not about the term being nonsense. Without them a typo in the built
/// expression would pass this test and look like a finding.
///
/// The closed instances are also the sharpest form of the statement: the round
/// trip *does* hold at `nil`, and at `cons leaf nil`, and at every closed list
/// — one ι step at a time. What fails is holding it uniformly, which is exactly
/// what a recursor rule at a bound argument asks for.
///
/// **This is still the finding, and the arc has not refuted it.** What
/// [`mini::nested`] does is not to make this equation hold: it *transports*
/// `Tree.rec_1` along the isomorphism instead, and owes a certificate that the
/// two interpretations agree. If this test ever fails by the theorem being
/// accepted, the isomorphism has become an equality and the whole construction
/// should be re-scoped rather than this test deleted.
#[test]
fn the_round_trip_the_encoding_would_need_is_not_definitional() {
    let loaded = load_with(&fixture("nested_roundtrip"), LoadOptions::default()).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    // `List Tree`, and the round trip applied to `arg`.
    let list_tree = app(k("List"), k("Tree"));
    let trip = |arg: E| app(k("fromAux"), app(k("toAux"), arg));

    // `Eq.{1} (List Tree) (fromAux (toAux arg)) arg`, proved by reflexivity —
    // built once and instantiated three ways.
    let claim = |arg: E, binder: Option<E>| {
        let stmt = app_n(konst(Name::simple("Eq"), one()), &[
            list_tree.clone(),
            trip(arg.clone()),
            arg.clone(),
        ]);
        let proof = app_n(eq_refl(), &[list_tree.clone(), trip(arg)]);
        let (ty, value) = match binder {
            Some(b) => (forall(b.clone(), stmt), lam(b, proof)),
            None => (stmt, proof),
        };
        Declaration::Def {
            name: Name::simple("_roundTripClaim"),
            lparams: Vec::new(),
            ty,
            value,
            kind: DefKind::Theorem,
        }
    };
    // `Eq.refl`'s own level list is `Eq`'s.
    let refl_at_one = |d: Declaration| match d {
        Declaration::Def { name, ty, value, kind, .. } => {
            Declaration::Def { name, lparams: Vec::new(), ty, value, kind }
        }
        other => other,
    };

    // The controls: closed arguments, one at `nil` and one after a `cons` step.
    let nil = app(dotted("List", "nil"), k("Tree"));
    let cons1 = app_n(dotted("List", "cons"), &[k("Tree"), k("treeLeaf"), nil.clone()]);
    for (what, arg) in [("nil", nil), ("cons leaf nil", cons1)] {
        let mut e = env.clone();
        mini::kernel::add(&mut e, &refl_at_one(claim(arg, None))).unwrap_or_else(|m| {
            panic!("the round trip at the closed `{what}` was rejected — the built term is \
                    wrong, not the finding:\n{m}")
        });
    }

    // The claim: the same equation at a variable.
    let mut e = env.clone();
    let err = mini::kernel::add(&mut e, &refl_at_one(claim(bvar(0), Some(list_tree.clone()))))
        .expect_err(
            "`fromAux (toAux l) ≡ l` was accepted at a variable — the round trip has become \
             definitional, and the nested increment should be re-scoped rather than this test \
             deleted",
        );
    // The message the kernel actually gives, matched so that a rejection for
    // *any other* reason — an unknown constant, a level mismatch, a malformed
    // application — fails this test instead of being read as the finding.
    assert!(
        err.starts_with("Expected definitional equality"),
        "rejected, but not by the conversion check:\n{err}"
    );
    assert!(
        err.contains("fromAux") || err.contains("Aux.rec"),
        "the conversion that failed is not the round trip:\n{err}"
    );
}

/// **The `Eq.refl` machinery this file builds on is real**, i.e. the fixture's
/// own constants are the ones the test thinks they are.
///
/// A guard rather than a claim. `the_round_trip_…` distinguishes a *rejected*
/// theorem from an accepted one, and both outcomes are cheap to produce by
/// accident: a misnamed constant makes everything fail, and a vacuous statement
/// makes everything pass. This checks the fixture declares what the test names
/// and that `toAux`/`fromAux` have the two directions the finding is about.
#[test]
fn the_fixture_declares_the_constants_the_finding_is_about() {
    let loaded = load_with(&fixture("nested_roundtrip"), LoadOptions::default()).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).expect("the fixture is well-typed");
    }
    for n in ["List", "Tag", "Aux", "Tree", "LT", "toAux", "fromAux", "treeLeaf", "treeNode", "Eq"]
    {
        assert!(env.get(&Name::simple(n)).is_some(), "the fixture lost `{n}`");
    }
    // `toAux : List Tree → LT` and `fromAux : LT → List Tree`, by their
    // *codomains*, which is what makes them a round trip rather than two maps.
    let cod = |n: &str| {
        let t = env.get(&Name::simple(n)).expect("declared").ty().clone();
        match &*t {
            mini::expr::Expr::Forall { body, .. } => body.clone(),
            _ => panic!("{n} is not a function"),
        }
    };
    assert_eq!(cod("toAux"), k("LT"), "toAux does not land in the specialised copy");
    assert_eq!(
        cod("fromAux"),
        app(k("List"), k("Tree")),
        "fromAux does not land in the real container"
    );
}


// ─────────────────────────── the model, and its price ───────────────────────

/// The four rules `nested_model` states about its **defined** recursors, and
/// whether `Eq.refl` proves each one. This table is the fixture's header as an
/// assertion, and it is the whole sizing of the evidence axis: two of the four
/// ι rules survive the pack/unpack encoding definitionally and two do not.
const MODEL_IOTA: [(&str, bool); 4] = [
    ("iotaLeaf", true),
    ("iota1Nil", true),
    ("iotaNode", false),
    ("iota1Cons", false),
];

/// Every declaration of a fixture, at the given options, added in order.
fn env_with(name: &str, opts: LoadOptions) -> (Environment, Vec<Declaration>) {
    let loaded = load_with(&fixture(name), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    (env, loaded.decls)
}

/// Peel every `∀`, returning the binder types outermost-first and the body.
fn peel_all(ty: &E) -> (Vec<E>, E) {
    let mut tys = Vec::new();
    let mut cur = ty.clone();
    while let mini::expr::Expr::Forall { ty: d, body } = &*cur.clone() {
        tys.push(d.clone());
        cur = body.clone();
    }
    (tys, cur)
}

/// `fun <binders> => Eq.refl α lhs`, for a statement `∀ <binders>, Eq α lhs rhs`
/// — the `rfl` proof of an ι rule, built from the *declared* statement so that
/// it is the fixture's own equation and not one this file invented.
fn refl_proof_of(stmt: &E) -> (E, E) {
    let (binders, body) = peel_all(stmt);
    let (head, args) = mini::expr::get_app(&body);
    let mini::expr::Expr::Const(n, ls) = &*head else {
        panic!("the statement does not end in a constant application")
    };
    assert_eq!(n.to_string(), "Eq", "the statement is not an `Eq`");
    assert_eq!(args.len(), 3, "`Eq` is not applied to three arguments");
    let refl = konst(Name::str(&Name::simple("Eq"), "refl"), ls.clone());
    let mut proof = app_n(refl, &[args[0].clone(), args[1].clone()]);
    for b in binders.iter().rev() {
        proof = lam(b.clone(), proof);
    }
    (stmt.clone(), proof)
}

/// **A `Tree.rec_1` that computes exists, and mini's kernel checks it.**
///
/// `nested_iota` measures that mini's *primitive* `Tree.rec_1` reduces on
/// `List.nil` and `List.cons`. It cannot measure that such a recursor is
/// consistent, because the rule is installed rather than derived — that is the
/// sentence [`the_round_trip_the_encoding_would_need_is_not_definitional`]
/// leaves standing.
///
/// `nested_model` is the other side. It declares **no nested inductive at
/// all**: the specialised block is an ordinary `mutual`, `Tree` and its
/// constructors are `def`s over it, and both recursors — including the one
/// whose major premise is `List Tree` and whose rules are `List`'s own
/// constructors — are `def`s whose ι rules are stated as theorems and *proved*.
/// Every one of those proofs is checked here.
#[test]
fn the_model_of_a_nested_recursor_is_checked() {
    let opts = LoadOptions { mutual: true, ..Default::default() };
    let (env, decls) = env_with("nested_model", opts);
    // The two maps, the two round trips, the two transports, both recursors and
    // the four rules. Named individually rather than counted: a fixture that
    // lost `packUnpack` and kept the rest would still be a file that checks.
    for n in [
        "Tree", "treeLeaf", "treeNode", "pack", "unpack", "unpackPack", "packUnpack",
        "congrPack", "congrCons", "transportNode", "transportCons", "ndMinor", "csMinor",
        "treeRec", "blockRec1", "treeRec1", "treeSize",
    ] {
        assert!(env.get(&Name::simple(n)).is_some(), "nested_model lost `{n}`");
    }
    for (n, _) in MODEL_IOTA {
        assert!(env.get(&Name::simple(n)).is_some(), "nested_model lost the rule `{n}`");
    }
    // Neither recursor is primitive — that is the point of the file. A treatment
    // that let `treeRec` in as a `ConstantInfo::Recursor` would be measuring
    // Lean's own nested compiler again and not this model.
    for n in ["treeRec", "treeRec1"] {
        assert!(
            !matches!(env.get(&Name::simple(n)), Some(ConstantInfo::Recursor { .. })),
            "`{n}` is a primitive recursor in the model, which is the thing being modelled"
        );
    }
    // The block is a `mutual`, so it arrives as **one** declaration; the model
    // is everything else. Counted so that a fixture that silently stopped
    // exporting half of itself fails here rather than passing the name list
    // above by accident.
    let blocks = decls.iter().filter(|d| matches!(d, Declaration::Mutual { .. })).count();
    assert_eq!(blocks, 1, "the model's specialised block is not one mutual declaration");
}

/// **Exactly two of the four ι rules survive pack/unpack definitionally**, and
/// the other two are theorems.
///
/// The measurement is `Eq.refl` at the fixture's **own** statement: for each
/// rule, the declared type is peeled and re-proved by reflexivity, and the
/// kernel's answer is compared against [`MODEL_IOTA`].
///
/// This is the sizing as a check rather than as a comment. `leaf` and
/// `List.nil` come out definitionally — `pack List.nil` ι-reduces to the
/// mimic's `nil` and `unpackPack List.nil` ι-reduces to `Eq.refl`, so the
/// transport in `treeRec1` disappears. `Tree.node` and `List.cons` do not:
/// each needs its transport pushed through a stuck `Eq.rec`, which is
/// `transportNode` and `transportCons`. If a future encoding made one of the
/// two hard rules definitional this test fails, and that is a result and not a
/// breakage.
#[test]
fn two_of_the_four_model_iota_rules_are_definitional_and_two_are_not() {
    let opts = LoadOptions { mutual: true, ..Default::default() };
    let loaded = load_with(&fixture("nested_model"), opts).expect("load");
    let mut env = Environment::empty();
    let mut rules: Vec<(&str, E)> = Vec::new();
    for d in &loaded.decls {
        let n = d.name().to_string();
        if let Some((name, _)) = MODEL_IOTA.iter().find(|(m, _)| *m == n) {
            let Declaration::Def { ty, .. } = d else { panic!("{n} is not a definition") };
            rules.push((name, ty.clone()));
            continue
        }
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{n}: {e}"));
    }
    assert_eq!(rules.len(), MODEL_IOTA.len(), "the fixture stopped stating four rules");

    for (name, definitional) in MODEL_IOTA {
        let ty = &rules.iter().find(|(n, _)| *n == name).expect("stated").1;
        let (ty, value) = refl_proof_of(ty);
        let mut e = env.clone();
        let got = mini::kernel::add(&mut e, &Declaration::Def {
            name: Name::simple("_modelIotaByRefl"),
            lparams: Vec::new(),
            ty,
            value,
            kind: DefKind::Theorem,
        });
        if definitional {
            got.unwrap_or_else(|m| {
                panic!("`{name}` was expected to hold by reflexivity and did not:\n{m}")
            });
        } else {
            let err = got.expect_err(
                "was proved by reflexivity — the encoding has become definitional, and the \
                 model should be re-scoped rather than this table edited",
            );
            assert!(
                err.starts_with("Expected definitional equality"),
                "`{name}` was rejected, but not by the conversion check:\n{err}"
            );
        }
    }
}

/// **The model the export carries, recognised — the generator's tests, and
/// what replaced them.**
///
/// *This file used to end with 480 lines that ran `mini::nested_ev::iso` over
/// every nested declaration in the directory, asserted the declaration counts
/// of each generated tower, and compared the generated round trips, recursors
/// and ι rules against zone A's own. `mini/src/nested_ev.rs` is deleted:
/// `modelgen/` generates the model now, as an export filter, and* `modelgen/Test.lean`
/// *pins the same counts against the same table while* `modelgen`'s
/// *statement oracle (`MODELGEN.md` §4, oracle 3) makes the same comparison
/// against the recursors Lean itself mints. Both oracles moved; neither was
/// dropped.*
///
/// *What is left on this side is the consumer's half, and it is
/// [`the_recognition_reads_the_model_the_filter_wrote`] below: that mini finds
/// the tower the filter spliced in, that it checks each statement against the
/// export's own before keying anything, and that a tower which is not there —
/// or is there and states something else — **declines by name** instead of
/// falling back. `nested_keying`'s `UTree` is the input that tells the two
/// apart and it is still here.*
///
/// # What the recognition asserts, per fixture
///
/// One row per nested declaration: its name and either the number of `_model`
/// constants keyed for it — the type former, its constructors and every
/// recursor — or the reason it got none.
#[test]
fn the_recognition_reads_the_model_the_filter_wrote() {
    // `(fixture, declaration, Ok(constants keyed) | Err(reason))`.
    //
    // The counts are `1 + ctors + recursors`: `nested_keying`'s `Tree` is
    // `Tree`, `Tree.leaf`, `Tree.node`, `Tree.rec`, `Tree.rec_1` — five.
    let expected: &[(&str, &str, Result<usize, &str>)] = &[
        ("nested_keying", "Tree", Ok(5)),
        // **The whole point of the fixture.** The file declares its own
        // `UTree._model.self`, `modelgen` therefore declines `UTree` for
        // `nested model name taken`, and this side must reach a decline of its
        // own rather than key `⟦UTree⟧ := ⟦N⟧`. The reason it gives is the
        // *first* thing wrong with the squatter, which is that it is declared
        // after the declaration it would model.
        ("nested_keying", "UTree", Err("nested model over a later declaration")),
        ("nested_iota_arm", "Tree", Ok(5)),
    ];
    let mut got: Vec<(&str, String, Result<usize, String>)> = Vec::new();
    for (fx, _, _) in expected {
        if got.iter().any(|(f, _, _)| f == fx) {
            continue
        }
        for (name, r) in recognise(fx) {
            got.push((fx, name, r));
        }
    }
    let want: Vec<(&str, String, Result<usize, String>)> = expected
        .iter()
        .map(|(f, n, r)| (*f, n.to_string(), r.map_err(str::to_string)))
        .collect();
    assert_eq!(got, want);
}

/// Load a fixture, install it, and ask [`mini::nested_splice::recognise`] what
/// it found — one row per nested declaration.
fn recognise(fixture_name: &str) -> Vec<(String, Result<usize, String>)> {
    let opts = LoadOptions { nested: true, mutual: true, ..Default::default() };
    let loaded = load_with(&fixture(fixture_name), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    let r = mini::nested_splice::recognise(&env, &loaded.decls, &loaded.schedule);
    // **A recursor is keyed at a σ and not at "the" σ.** Read here rather than
    // asserted separately: every key whose constant is a recursor must carry a
    // non-empty instantiation, because a nested recursor binds a motive
    // universe. Dropping σ from the key — which is one of this arc's killed
    // mutations — makes the whole population empty-σ and is caught by the
    // panic below, in a test that costs twenty seconds instead of five
    // minutes.
    for (n, sigma) in r.model_of.keys() {
        if matches!(env.get(n), Some(ConstantInfo::Recursor { .. })) {
            assert!(!sigma.is_empty(), "{n} is keyed at the empty instantiation");
        }
    }
    let mut out: Vec<(String, Result<usize, String>)> = r
        .nested
        .iter()
        .map(|(n, rec)| {
            (n.to_string(), match rec.why {
                Some(w) => Err(w.to_string()),
                None => Ok(rec.constants.len()),
            })
        })
        .collect();
    out.sort();
    out
}

/// **A `_model` tower that states something else is a decline and not a
/// keying**, and this is the input that says so.
///
/// The recognition's shape check is a *diagnostic* — `mini/src/nested_splice.rs`
/// says why the certificate and not this is what makes a conclusion
/// trustworthy — but it fails closed, and "fails closed" is a claim that needs
/// an occupant. The occupant is built here rather than exported: take
/// `nested_iota_arm`, whose `Tree` is recognised, and **swap the two ι
/// theorems' statements**, so `Tree._model.iota_0_0` states the rule
/// `iota_0_1` is about. Nothing about the file stops being well-typed; what
/// changes is that the theorem indexed at rule 0 is about rule 1's
/// constructor.
///
/// Under `MODELGEN.md` §1.1's property 2 read as a *promise* — line the
/// theorems up by index, take the key on faith — that swap is invisible and
/// `Tree.rec`'s rule on `Tree.leaf` would fire against a theorem about
/// `Tree.node`. Read as this module reads it — take the key off the theorem's
/// own left-hand side and compare it against the rule's — it is
/// `nested model has no iota rule for a constructor the export's recursor
/// reduces on`.
#[test]
fn a_model_whose_iota_theorem_is_about_another_rule_declines() {
    let opts = LoadOptions { nested: true, mutual: true, ..Default::default() };
    let loaded = load_with(&fixture("nested_iota_arm"), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    let a = Name::str(&dot("Tree", "_model"), "iota_0_0");
    let b = Name::str(&dot("Tree", "_model"), "iota_0_1");
    // The statements only: the *values* stay where they are, so the environment
    // is no longer one the kernel would accept. That is deliberate and is what
    // makes this a test of the recognition rather than of the kernel — the
    // question here is what the table does with a tower whose indices lie.
    let (ta, tb) = (env.get(&a).unwrap().ty().clone(), env.get(&b).unwrap().ty().clone());
    retype(&mut env, &a, tb);
    retype(&mut env, &b, ta);
    let r = mini::nested_splice::recognise(&env, &loaded.decls, &loaded.schedule);
    assert_eq!(
        r.nested.get(&Name::simple("Tree")).and_then(|n| n.why),
        Some("nested model has no iota rule for a constructor the export's recursor reduces on"),
    );
    assert_eq!(r.modelled, 0, "nothing may be keyed off a tower whose rules are misindexed");
}

/// **A nested declaration with no model at all declines by name**, and the
/// reason says the model is absent rather than that the declaration is a shape
/// mini cannot handle.
///
/// This is the case an unfiltered export produces — `modelgen` was not run, or
/// it declined the declaration for one of `MODELGEN.md` §5's shapes — and
/// `MODELGEN.md` §1.3 is explicit that a consumer must treat it as "no model"
/// and not as an error. There is no *fixture* for it, and that is a
/// consequence of the pipeline rather than an omission: `scripts/export-fixture.sh`
/// filters every `.ndjson` it writes, so a committed export with a nested
/// inductive and no model would have to be produced by hand and would rot the
/// moment the script ran. The occupant is built here instead, by taking the
/// carrier back out of an environment that has one.
#[test]
fn a_nested_declaration_with_no_model_declines_saying_so() {
    let opts = LoadOptions { nested: true, mutual: true, ..Default::default() };
    let loaded = load_with(&fixture("nested_iota_arm"), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    let carrier = Name::str(&dot("Tree", "_model"), "self");
    assert!(env.consts.remove(&carrier).is_some(), "the fixture is supposed to be filtered");
    let r = mini::nested_splice::recognise(&env, &loaded.decls, &loaded.schedule);
    assert_eq!(
        r.nested.get(&Name::simple("Tree")).and_then(|n| n.why),
        Some("no nested model in the export"),
    );
    assert_eq!(r.modelled, 0);
    assert_eq!(r.seen, 1, "the declaration is still *seen*: it is nested, and it has no model");
}

/// **A `_model` recursor that is not the export's statement declines**, at the
/// recursor and not three modules downstream.
///
/// The sibling of [`a_model_whose_iota_theorem_is_about_another_rule_declines`]
/// one level up, and the one that matters most: `model_of` is what puts
/// `⟦T.rec_k⟧` in the store, so a tower keyed here whose `rec_k` states
/// something else would give the export's recursor an interpretation that is
/// not its own. The occupant is `Tree._model.rec_0` retyped to
/// `Tree._model.rec_1`'s statement — still a well-formed type, still about the
/// model, and not `Tree.rec`'s.
#[test]
fn a_model_whose_recursor_states_another_recursor_declines() {
    let opts = LoadOptions { nested: true, mutual: true, ..Default::default() };
    let loaded = load_with(&fixture("nested_iota_arm"), opts).expect("load");
    let mut env = Environment::empty();
    for d in &loaded.decls {
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    let a = Name::str(&dot("Tree", "_model"), "rec_0");
    let b = Name::str(&dot("Tree", "_model"), "rec_1");
    let tb = env.get(&b).expect("rec_1").ty().clone();
    retype(&mut env, &a, tb);
    let r = mini::nested_splice::recognise(&env, &loaded.decls, &loaded.schedule);
    assert_eq!(
        r.nested.get(&Name::simple("Tree")).and_then(|n| n.why),
        Some("nested model recursor does not state the export's"),
    );
    assert_eq!(r.modelled, 0);
}

/// **A `modelgen` that fails is a decline that names it, and never a run on
/// the unfiltered input.**
///
/// `mini/src/modelgen.rs`'s header says why: a silent skip would report a
/// toolchain problem as the *declaration's* problem — the file would be
/// accepted and every nested declaration would answer `no nested model in the
/// export`, which is true of what mini was shown and false of the file.
///
/// `/bin/false` is the smallest binary that is there, is executable and exits
/// non-zero, so this measures the failure path and not the discovery one; the
/// discovery path's failure is a usage error and exits 2 before any file is
/// read.
#[test]
fn a_modelgen_that_fails_declines_and_names_it() {
    // `false` off `$PATH` and not `/bin/false`: this repository is built under
    // Nix, where `/bin` holds `sh` and nothing else, and the hard-coded path
    // made the test **skip**. It skipped silently, and the mutation "a failing
    // `modelgen` falls back to the unfiltered input" survived it.
    let false_bin = std::env::var("PATH")
        .unwrap_or_default()
        .split(':')
        .filter(|d| !d.is_empty())
        .map(|d| Path::new(d).join("false"))
        .find(|p| p.is_file());
    let Some(false_bin) = false_bin else {
        panic!("no `false` on $PATH — this test cannot measure anything without one")
    };
    let false_bin = false_bin.display().to_string();
    // **Not through [`run`]**, which prepends `--no-modelgen` so that the rest
    // of this file is hermetic. Passing both flags makes `--no-modelgen` win
    // and the filter is never reached: the first version of this test did
    // exactly that, and the mutation "a failing `modelgen` falls back to the
    // unfiltered input" **survived** it. A distinguishing input that nothing
    // observes is not a test.
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg(format!("--modelgen={false_bin}"))
        .arg("--nested")
        .arg(fixture("nested_iota_arm"))
        .output()
        .expect("spawn mini");
    let code = out.status.code();
    let text = String::from_utf8_lossy(&out.stdout).to_string()
        + &String::from_utf8_lossy(&out.stderr);
    assert_eq!(code, Some(2), "a failing filter did not decline:\n{text}");
    assert!(
        text.contains("modelgen:") && text.contains("exited 1"),
        "the decline does not name the subprocess or its status:\n{text}"
    );
}

/// **The filter's report reaches the user, and says *why* there is no model.**
///
/// The half of the process boundary the previous test does not reach. `mini`
/// execs the filter with `-o -` and no `--quiet`, so the export arrives on the
/// child's stdout and the report on its stderr; `mini/src/convert.rs` writes
/// the report through. While the report was on *stdout* a streaming consumer
/// had to pass `--quiet` to keep the export parseable and lost every decline
/// reason doing it, and mini could only ever say `no nested model in the
/// export` — where the lookup stopped, not why it stopped.
///
/// **The two streams are captured separately and both are asserted on**, which
/// is the only way to see the split: a report leaking back onto stdout would
/// corrupt the export, and a test that concatenated them would pass either way.
///
/// The input is a committed fixture, which is **already filtered**
/// (`scripts/export-fixture.sh`), so the filter's idempotence guard fires and
/// the reason is `nested model name taken`. That the run then reaches a
/// verdict at all is the other claim: the bytes `-o -` produced parsed.
///
/// This is the one test in the file that needs the Lean toolchain, and it says
/// so out loud when it cannot run rather than passing quietly — the note on
/// [`a_modelgen_that_fails_declines_and_names_it`] records what a silent skip
/// cost here once already.
#[test]
fn the_filters_report_reaches_the_user_and_says_why_there_is_no_model() {
    let mg = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("mini/ has a parent")
        .join("modelgen/.lake/build/bin/modelgen");
    if skip_guard::tool_absent(&mg, "run `lake build` in modelgen/; the report/export split is UNMEASURED in this run") {
        return
    }
    // Not through [`run`], which prepends `--no-modelgen`: that would make the
    // filter unreachable and this test vacuous.
    //
    // **No `--nested`**, and that is deliberate rather than an oversight: the
    // claim here is about the process boundary, and the gate stays shut so the
    // run stops at the model's mutual block in 0.2 s instead of deep-checking
    // `nested_iota_arm` for minutes in a debug build. The verdict is a decline
    // and it still witnesses the parse — a decline that names `Tree._model.0`
    // could only have read it out of the bytes the child streamed.
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg(format!("--modelgen={}", mg.display()))
        .arg("--acceptance-only")
        .arg(fixture("nested_iota_arm"))
        .output()
        .expect("spawn mini");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let both = format!("--- stdout:\n{stdout}--- stderr:\n{stderr}");
    // The reason, on stderr, in the filter's own words.
    assert!(
        stderr.contains("declined — nested model name taken"),
        "the filter's reason did not reach the user:\n{both}"
    );
    // And not on stdout, which carries the export from the child and the
    // verdict to the user and must carry nothing else.
    assert!(!stdout.contains("declined —"), "a report line reached stdout:\n{both}");
    // The export streamed through `-o -` and parsed: there is a verdict, and
    // it is about a declaration that is only in the export.
    assert!(
        stdout.contains("nested_iota_arm.ndjson\t") && stdout.contains("Tree._model.0"),
        "the run produced no verdict, so the streamed export did not parse:\n{both}"
    );
}

/// Replace a `Def`'s declared type in place — the mutation
/// [`a_model_whose_iota_theorem_is_about_another_rule_declines`] performs.
fn retype(env: &mut Environment, n: &Name, ty: E) {
    let ConstantInfo::Def { lparams, value, .. } = env.get(n).expect("declared").clone() else {
        panic!("{n} is not a def")
    };
    env.consts.insert(*n, ConstantInfo::Def { lparams, ty, value });
}
