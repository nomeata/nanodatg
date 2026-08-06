//! **Nested inductives** — where the arc stands, and the one measurement that
//! decided its shape.
//!
//! # The finding, first
//!
//! The mutual arc works by *replacing* a `mutual … end` block with an auxiliary
//! inductive and defining the members over it, and every recursor rule comes out
//! definitionally. Lean's own nested compiler reduces
//! `inductive Tree | node : List Tree → Tree` to exactly such a block —
//! `{Tree, ListTree}` — so the obvious move is to run the same encoding on it.
//!
//! **It does not extend, and the reason is one equation.** In a mutual block
//! every member is a name the encoding introduces. In a nested declaration
//! `List` already exists with its interpretation already fixed, and `List Tree`
//! is an application of it — so the encoding gets a specialised copy `LT`
//! isomorphic to `List Tree` and *not equal* to it, while every constructor and
//! every rule the export declares is stated at `List Tree`. Bridging them needs
//! `fromAux (toAux l) ≡ l` at a **variable** `l`, and that is propositional.
//!
//! [`the_round_trip_the_encoding_would_need_is_not_definitional`] is that
//! sentence as a check the kernel runs: it builds the theorem out of the
//! fixture's own constants and asserts mini **rejects** it, with the same
//! theorem at two *closed* arguments accepted as the controls. Without the
//! controls the test would pass on a term that is simply ill-formed.
//!
//! `thesis.txt` says it in one line — mutual inductives, nested inductive types
//! and coinductive types "can all be encoded using regular inductives, although
//! some definitional equalities may fail to hold in the encodings". This is
//! which equality, for this encoding.
//!
//! # What the export says Lean does instead
//!
//! A nested `Tree` is **one** `Declar::Inductive` with `all = [Tree]` and
//! `numNested = 1`, and **two** recursors — `Tree.rec` with rules for
//! `Tree.leaf`/`Tree.node`, and `Tree.rec_1` with rules for `List.nil`/
//! `List.cons`, both at two motives and four minors. So the un-specialisation
//! has already happened in the exporter, and what a kernel keeps is a
//! *primitive* `Tree.rec_1`: a recursor for one type that ι-reduces on
//! **another type's** constructors. No encoding produces that rule.
//!
//! # Where that leaves the increment
//!
//! Not with `mutual_aux`. `⟦Tree⟧` has to be built as a carrier over the *real*
//! `⟦List⟧` — the initial algebra of `X ↦ 1 + List X` — with `⟦Tree.rec⟧` and
//! `⟦Tree.rec_1⟧` and their ι theorems. That is a `derived/` construction, and
//! it is a different piece of work from anything the mutual arc built.
//!
//! # The index question, measured
//!
//! The specialised copy of a container keeps the container's own index
//! telescope. For an **unindexed** container — `List`, `Pair`, every shape in
//! `nested_shapes.lean` — the specialised block is unindexed, so `mutual_aux`'s
//! "members must share an index telescope" line was never what nesting was
//! waiting on. For an **indexed** container it was: nesting `Vec α n` inside an
//! unindexed `Tree` gives a block whose members are `Tree : Type` and
//! `VecTree : N → Type`, which is the `HA`/`HB` shape
//! `mutual_index_sorts.lean` carries.
//!
//! *That line is gone.* The index telescopes live in the tag now, so a block's
//! members need not share one and `HA`/`HB` encodes. Nesting waits on the
//! paragraph above and on nothing else in `mutual_aux`.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

use mini::convert::{load_with, LoadOptions};
use mini::env::{DefKind, Declaration, Environment};
use mini::expr::{app, app_n, bvar, forall, konst, lam, Level, Name, E};

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{name}.ndjson"));
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// **Nesting declines at the parser, with or without `--mutual`.**
///
/// The gate is about `mutual … end` blocks; nesting is a separate refusal in
/// `convert::load`, and pinning both spellings is what says the two are not
/// the same switch. The reason string is matched too: a fixture that failed to
/// *parse* would exit 2 as well and pass a bare status assertion while
/// measuring nothing.
#[test]
fn a_nested_declaration_declines_and_the_mutual_gate_does_not_open_it() {
    for gate in [false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_mini"));
        if gate {
            cmd.arg("--mutual");
        }
        let out = cmd.arg(fixture("nested_shapes")).output().expect("spawn mini");
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        assert_eq!(out.status.code(), Some(2), "nested_shapes did not decline:\n{stdout}");
        assert!(
            stdout.contains("declined: Nested inductive Tree not supported"),
            "declined for the wrong reason:\n{stdout}"
        );
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
/// **If this test ever fails by the theorem being accepted, the finding has
/// changed and the nested increment should be re-scoped**, not the test
/// deleted.
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
