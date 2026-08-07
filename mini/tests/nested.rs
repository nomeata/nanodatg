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
//! it exists over the real `List`. What it does not yet say is that mini's
//! *interpretation* of the primitive `Tree.rec_1` is that one:
//! `mini/src/zoneb.rs` still answers `ind-spec(Tree: nested occurrence)`, so
//! `⟦Tree⟧` is unbuilt and nothing keys the model onto the export's names. Until
//! that lands the corpus never sees a nested file.
//!
//! [`two_of_the_four_model_iota_rules_are_definitional_and_two_are_not`] is the
//! price, measured rather than described: `leaf` and `List.nil` survive the
//! encoding definitionally, `Tree.node` and `List.cons` do not, and each of the
//! two is one transport lemma.
//!
//! # The fixtures
//!
//! | fixture | what it covers |
//! | --- | --- |
//! | `nested_shapes` | the declaration side: depth, container parameterised, copy recursive, container also used un-nested, two positions in one constructor |
//! | `nested_iota` | the **rules**, as fourteen `rfl` theorems; `numNested = 2` at two *different* containers; a container at an unrelated type in the same constructor list; a nested type with **parameters of its own** |
//! | `nested_roundtrip` | why the auxiliary encoding does not extend, as a theorem the kernel rejects |
//! | `nested_model` | the model: pack/unpack, both round trips, both recursors and all four ι rules, none of them primitive and none of them assumed |

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

/// Run the generator over a fixture: for every nested declaration in it, the
/// plan and then the isomorphism, against the environment as it stood *before*
/// that declaration — which is where `nested::add` itself stands.
fn generate(fixture_name: &str) -> Vec<(String, Result<usize, String>)> {
    let opts = LoadOptions { nested: true, ..Default::default() };
    let loaded = load_with(&fixture(fixture_name), opts).expect("load");
    let mut env = Environment::empty();
    let mut out = Vec::new();
    for d in &loaded.decls {
        if let Declaration::Inductive { name, lparams, num_params, ty, ctors } = d {
            let types = vec![mini::env::IndType {
                name: name.clone(),
                ty: ty.clone(),
                ctors: ctors.clone(),
            }];
            if let Ok(Some(plan)) = mini::nested::plan(&env, lparams, *num_params, &types) {
                let r = mini::nested_ev::iso(&env, lparams, *num_params, &types, &plan)
                    .map(|iso| iso.decls.len())
                    .map_err(|e| e.label().to_string());
                out.push((name.to_string(), r));
            }
        }
        mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
    }
    out
}

/// One expected row: a nested declaration's name, and either how many
/// declarations its isomorphism came to or the reason it declined.
type Row = (&'static str, Result<usize, &'static str>);

/// One generated tower held back until its declaration is installed, so the
/// recursors can be compared against the ones zone A then mints.
type Generated = (mini::nested_ev::Iso, Name, Vec<(Name, E)>);

/// **The isomorphism the restoration stands on, generated and checked.**
///
/// `nested_model.lean` is this development written by hand at `Tree`;
/// [`mini::nested_ev::iso`] is it generated, and **every declaration it returns
/// has been through `kernel::add`** — including the two round trips, which are
/// theorems with proofs and not assumptions. A proof the checker rejects comes
/// back as `Err`, so an `Ok` here is the kernel's answer and not the module's.
///
/// The counts are asserted and not just the `Ok`: one for the block, one for
/// the carrier, and four per mimic. A generator that quietly emitted fewer —
/// dropping a round trip, or a mimic — satisfies `is_ok()` and measures
/// nothing.
///
/// The three fixtures are three different answers on purpose, and each decline
/// is named rather than lumped:
///
/// * `nested_iota` — `Tree` at one container, `BTree` at **two different**
///   containers (`Box BTree` over `List BTree`, which is `Lean.Syntax`'s
///   shape), and `PT α`, which has a parameter telescope of its own and is the
///   one shape here the generator does not write.
/// * `nested_deep` — `DTree`'s inner `cons : M₁ → M₀ → M₀`, the only
///   constructor in the directory with **two** packed positions, and therefore
///   the only occupant of the congruence fold's loop.
/// * `nested_shapes` — declares no `Eq`, and the round trips are equations. All
///   four of its nested declarations decline for that one reason, which is the
///   same refusal `mutual_aux` makes: a `prelude` export that never mentions
///   equality does not get an `Eq` mini minted for it.
#[test]
fn the_nested_isomorphism_is_generated_and_the_kernel_accepts_it() {
    let want: [(&str, &[Row]); 3] = [
        ("nested_iota", &[
            ("Tree", Ok(11)),
            ("BTree", Ok(18)),
            ("PT", Ok(11)),
        ]),
        ("nested_deep", &[("DTree", Ok(17))]),
        // Four declarations on four separated axes, and the generator writes
        // all of them: `PTree`'s container is **not recursive**, and `BTree`
        // uses one at **two positions in one constructor**, which is one mimic
        // and not two — the reuse `nested::plan` keys on the whole occurrence
        // rather than on the container's name.
        ("nested_shapes", &[
            ("Tree", Ok(11)),
            ("PTree", Ok(11)),
            ("DTree", Ok(17)),
            ("BTree", Ok(11)),
        ]),
    ];
    for (f, rows) in want {
        let got = generate(f);
        assert_eq!(got.len(), rows.len(), "{f}: nested declarations changed: {got:?}");
        for ((n, r), (wn, wr)) in got.iter().zip(rows.iter()) {
            assert_eq!(n, wn, "{f}: declaration order changed");
            match (r, wr) {
                (Ok(k), Ok(w)) => assert_eq!(k, w, "{f}/{n}: {k} declarations, expected {w}"),
                (Err(e), Err(w)) => assert_eq!(e, w, "{f}/{n} declined for the wrong reason"),
                _ => panic!("{f}/{n}: got {r:?}, expected {wr:?}"),
            }
        }
    }
}

/// **The generated round trips say what they are supposed to say**, compared
/// against a statement this file builds independently.
///
/// A test that only asks whether `kernel::add` accepted the development
/// measures well-typedness, and well-typedness is not the claim: a `pack` and
/// an `unpack` at the *wrong* parameters, or a round trip quantified over the
/// wrong thing, can be perfectly well-typed and prove something weaker than the
/// isomorphism. So the four types are reconstructed here from
/// `nested::Plan`'s own occurrence and compared syntactically.
///
/// **This check was written before the code it guards**, because the parameter
/// telescope is a `p⃗` prefix on every declaration and a shift on every
/// occurrence, and a term read at the wrong depth is the family that has
/// produced this project's silent wrong terms — three of the indexed row's five
/// layers were exactly that.
///
/// **It has no occupant the kernel misses, and that is measured rather than
/// assumed.** Every depth error the generator made while the telescope was
/// being added — a field type compared at the telescope's depth instead of its
/// own binder's, a field type handed to the congruence fold un-lifted — was
/// caught by `kernel::add` first, and a deliberate mutation putting the `Eq`'s
/// own type argument one depth out is caught there too, so `iso` returns `Err`
/// and this test never sees the statement. What it did catch is **its own**
/// depth error: written at `np = 0`, where parameters are `#0` at every depth,
/// it was wrong the first time it met `PT` and said so. Keep it for the shape
/// it pins — that these four are *the isomorphism* and not four other
/// well-typed equations — and not for a kill it has made.
#[test]
fn the_generated_round_trips_state_the_isomorphism() {
    let opts = LoadOptions { nested: true, ..Default::default() };
    let mut checked = 0usize;
    let mut pending: Vec<Generated> = Vec::new();
    for f in ["nested_iota", "nested_deep", "nested_shapes"] {
        let loaded = load_with(&fixture(f), opts).expect("load");
        let mut env = Environment::empty();
        for d in &loaded.decls {
            if let Declaration::Inductive { name, lparams, num_params, ty, ctors } = d {
                let types = vec![mini::env::IndType {
                    name: name.clone(),
                    ty: ty.clone(),
                    ctors: ctors.clone(),
                }];
                if let Ok(Some(plan)) = mini::nested::plan(&env, lparams, *num_params, &types) {
                    if let Ok(iso) =
                        mini::nested_ev::iso(&env, lparams, *num_params, &types, &plan)
                    {
                        checked += check_iso_statements(&iso, &plan, name, *num_params, ctors);
                        pending.push((iso, name.clone(), ctors.clone()));
                    }
                }
            }
            mini::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
            // **The recursors, against zone A's own.** Checked *after* the
            // declaration is added, because that is when `nested::add` installs
            // `T.rec_k` — and comparing against the installed recursor rather
            // than against a statement this file rebuilds is what makes this an
            // oracle rather than a restatement of the generator.
            for (iso, root, cs) in pending.drain(..) {
                checked += check_recursors(&iso, &env, &root, &cs);
            }
        }
    }
    // Four statements per mimic plus one per constructor, over every nested
    // declaration the generator writes. Pinned so that a generator that stopped
    // emitting — or a fixture that stopped being nested — fails here instead of
    // passing at zero.
    assert!(checked >= 54, "only {checked} statements were compared");
}

/// The four declared types of one mimic, rebuilt from the plan and compared.
/// Returns how many were checked.
fn check_iso_statements(
    iso: &mini::nested_ev::Iso,
    plan: &mini::nested::Plan,
    root: &Name,
    num_params: u32,
    export_ctors: &[(Name, E)],
) -> usize {
    use mini::expr::Expr;
    let ty_of = |n: &Name| iso.env.get(n).map(|c| c.ty().clone());
    // `occ` with the export's `T` rewritten to the model's own carrier, which
    // is what every generated statement is about.
    let to_self: std::collections::HashMap<Name, (u32, E)> =
        [(root.clone(), (0u32, konst(iso.self_name.clone(), Vec::new().into())))]
            .into_iter()
            .collect();
    let unit: Rc<[Level]> = Vec::new().into();
    let mut n = 0usize;
    for (i, m) in plan.mimics.iter().enumerate() {
        let (pack, unpack, retract, section) = iso
            .maps
            .iter()
            .find(|(p, ..)| *p == Name::str(&Name::str(root, "_model"), &format!("pack_{i}")))
            .cloned()
            .unwrap_or_else(|| panic!("no maps entry for mimic {i} of {root}"));
        let occ = mini::nested::restore(&to_self, &m.occ);
        let member = konst(iso.members[i + 1].clone(), unit.clone());
        // **Every depth is written out.** The parameters are the outermost
        // binders of every generated declaration, so at a scope of depth `d`
        // parameter `l` is `d − 1 − l`; and `Plan` stores an occurrence at the
        // telescope's own depth `np`, so using it at `d` is a shift by `d − np`.
        // At `np = 0` both are the identity, which is why this expectation was
        // wrong the first time it met a parameter and the assertion caught it.
        let np = num_params;
        let ps = |d: u32| -> Vec<E> { (0..np).map(|l| bvar(d - 1 - l)).collect() };
        let occ_at = |d: u32| mini::expr::shift(&occ, 0, d - np);
        let mem_at = |d: u32| app_n(member.clone(), &ps(d));
        let call = |f: &Name, d: u32, x: E| {
            let mut a = ps(d);
            a.push(x);
            app_n(konst(f.clone(), unit.clone()), &a)
        };
        let wrap = |body: E| {
            let mut cur = plan.types[0].ty.clone();
            let mut ptys = Vec::new();
            for _ in 0..np {
                let Expr::Forall { ty, body } = &*cur.clone() else { panic!("too few params") };
                ptys.push(ty.clone());
                cur = body.clone();
            }
            ptys.iter().rev().fold(body, |b, t| forall(t.clone(), b))
        };
        let eq_at = |a_ty: E, x: E, y: E| {
            app_n(konst(Name::simple("Eq"), one()), &[a_ty, x, y])
        };
        let want_pack = wrap(forall(occ_at(np), mem_at(np + 1)));
        let want_unpack = wrap(forall(mem_at(np), occ_at(np + 1)));
        let want_retract = wrap(forall(
            occ_at(np),
            eq_at(occ_at(np + 1), call(&unpack, np + 1, call(&pack, np + 1, bvar(0))), bvar(0)),
        ));
        let want_section = wrap(forall(
            mem_at(np),
            eq_at(mem_at(np + 1), call(&pack, np + 1, call(&unpack, np + 1, bvar(0))), bvar(0)),
        ));
        for (nm, want) in [
            (&pack, want_pack),
            (&unpack, want_unpack),
            (&retract, want_retract),
            (&section, want_section),
        ] {
            let got = ty_of(nm).unwrap_or_else(|| panic!("{nm} was not declared"));
            assert_eq!(got, want, "{root}: {nm} does not state what it is supposed to");
            n += 1;
        }
    }
    // **The constructors carry the export's own declared type**, with `T`
    // rewritten to the carrier and nothing else. This is the keying's soundness
    // condition, not a convenience: `⟦T.ctorᵢ⟧ := ⟦T._model.ctorᵢ⟧` is an alias
    // and not a coincidence *only* if the two types are the same statement, so
    // the comparison exists before the keying that will rely on it.
    for (export_c, model_c) in &iso.ctors {
        // The export's own declared type, taken from the **declaration** rather
        // than from the model's environment: `T.ctorᵢ` is not in that
        // environment, because the model is a parallel development and the
        // primitive it will be keyed to has not been installed yet.
        let declared = export_ctors
            .iter()
            .find(|(n, _)| n == export_c)
            .map(|(_, t)| t.clone())
            .unwrap_or_else(|| panic!("{export_c} is not a constructor of {root}"));
        let want = mini::nested::restore(&to_self, &declared);
        let got = ty_of(model_c).unwrap_or_else(|| panic!("{model_c} was not declared"));
        assert_eq!(got, want, "{root}: {model_c} is not the export's {export_c} at the carrier");
        n += 1;
    }
    n
}


/// **The model's recursors carry zone A's own statement.**
///
/// `T._model.rec_k` is compared against the `T.rec_k` that `nested::add`
/// installed, with the export's names rewritten to the model's and nothing
/// else. That is the keying's soundness condition at the recursors:
/// `⟦T.rec_k⟧ := ⟦T._model.rec_k⟧` is an alias exactly when the two are the
/// same statement about different constants, and a generator that produced a
/// well-typed recursor of some *other* type would pass `kernel::add` and fail
/// here.
fn check_recursors(
    iso: &mini::nested_ev::Iso,
    env: &Environment,
    root: &Name,
    export_ctors: &[(Name, E)],
) -> usize {
    let unit: Rc<[Level]> = Vec::new().into();
    let mut to_model: std::collections::HashMap<Name, (u32, E)> = Default::default();
    to_model.insert(root.clone(), (0, konst(iso.self_name.clone(), unit.clone())));
    for ((export_c, _), (_, model_c)) in export_ctors.iter().zip(iso.ctors.iter()) {
        to_model.insert(export_c.clone(), (0, konst(model_c.clone(), unit.clone())));
    }
    for (k, model_r) in iso.recs.iter().enumerate() {
        let export_r = mini::nested::Plan::rec_name(root, k);
        to_model.insert(export_r, (0, konst(model_r.clone(), unit.clone())));
    }
    let mut n = 0usize;
    for (k, model_r) in iso.recs.iter().enumerate() {
        let export_r = mini::nested::Plan::rec_name(root, k);
        let declared = env
            .get(&export_r)
            .unwrap_or_else(|| panic!("{export_r} was not installed"))
            .ty()
            .clone();
        let want = mini::nested::restore(&to_model, &declared);
        let got = iso
            .env
            .get(model_r)
            .unwrap_or_else(|| panic!("{model_r} was not generated"))
            .ty()
            .clone();
        assert_eq!(got, want, "{root}: {model_r} is not the export's {export_r} at the model");
        n += 1;
    }
    n
}


