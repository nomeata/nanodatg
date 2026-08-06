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
//! * **Zone B does not take one.** Every nested declaration's pairs come back
//!   `ind-spec(T: nested occurrence)`, which is the model obligation and is not
//!   this file's subject.
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
//! say either of them is sound. Discharging that is the evidence axis's job,
//! and until it lands the corpus never sees a nested file.
//!
//! `thesis.txt` says the general form in one line — mutual inductives, nested
//! inductive types and coinductive types "can all be encoded using regular
//! inductives, although some definitional equalities may fail to hold in the
//! encodings". This is which equality, for this encoding.
//!
//! # The fixtures
//!
//! | fixture | what it covers |
//! | --- | --- |
//! | `nested_shapes` | the declaration side: depth, container parameterised, copy recursive, container also used un-nested, two positions in one constructor |
//! | `nested_iota` | the **rules**, as fourteen `rfl` theorems; `numNested = 2` at two *different* containers; a container at an unrelated type in the same constructor list; a nested type with **parameters of its own** |
//! | `nested_roundtrip` | why the auxiliary encoding does not extend, as a theorem the kernel rejects |

use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

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
        for flags in [&[][..], &["--mutual"][..]] {
            let (code, stdout) = run(f, flags);
            assert_eq!(code, Some(2), "{f} at {flags:?} did not decline:\n{stdout}");
            assert!(
                stdout.contains("declined: Nested inductive"),
                "{f} declined for the wrong reason:\n{stdout}"
            );
        }
        // Accepted, not declined. The exit *code* is 0 or 4 depending on
        // whether anything went untranslated, and both nested fixtures have
        // declarations zone B cannot interpret yet — so the assertion is on
        // the verdict word, which is the acceptance axis, and on "not 2".
        let (code, stdout) = run(f, &["--nested"]);
        assert_ne!(code, Some(2), "{f} still declined behind --nested:\n{stdout}");
        assert!(
            stdout.lines().next().is_some_and(|l| l.contains("\taccept\t")),
            "{f} was not accepted behind --nested:\n{stdout}"
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
