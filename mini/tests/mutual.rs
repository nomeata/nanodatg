//! **Mutual inductives** — the fixtures, and what mini does with them today.
//!
//! `mini/tests/designed.rs` is the general home for designed fixtures. This is
//! a separate module for one reason: mutual inductives are a *feature arc*
//! rather than a clause, and the arc moves the frontend — a file that declines
//! at exit 2 today is meant to be accepted later. Keeping the whole arc's
//! measurements in one file means the diff that flips them is one file, and the
//! decline pins below are the before-picture the flip has to beat.
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
//!
//! Each `.lean` carries its own header saying what breaks if it regresses.
//! `scripts/export-fixture.sh <name>.lean` regenerates the `.ndjson`.
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
//! # Why the exit code is asserted and not just the word
//!
//! `decline` on the verdict line and **exit 2** are the arena's contract for an
//! unsupported feature, and `MINI-DESIGN.md` §0 is emphatic that the population
//! of exit 2 is a set that must not grow by accident. These fixtures are in it
//! deliberately and by name. When mutual support lands, this file's pins become
//! acceptance measurements and the exit-2 set shrinks by seven — a contract
//! change made and measured here, not a side effect somewhere else.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every mutual fixture, in the order the table above lists them.
const FIXTURES: [&str; 7] = [
    "mutual_three_way_cycle",
    "mutual_expr_stmt_ast",
    "mutual_parameters",
    "mutual_indices",
    "mutual_prop_even_odd",
    "mutual_one_recursive",
    "mutual_universe_polymorphic",
];

fn fixture(name: &str) -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{name}.ndjson"));
    assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
    p
}

/// `mini --verbose <fixture>`, in a subprocess — `checker`'s parser reports a
/// declined export by calling `std::process::exit(2)`, which an in-process
/// harness cannot contain. Returns `(exit code, stdout)`.
fn run(name: &str) -> (Option<i32>, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .arg("--verbose")
        .arg(fixture(name))
        .output()
        .expect("spawn mini");
    (out.status.code(), String::from_utf8_lossy(&out.stdout).to_string())
}

/// **Every mutual fixture parses, and every one declines at the frontend.**
///
/// The two halves are one test on purpose. A fixture that fails to *parse*
/// also exits 2 — `LoadError::Io`, a `checker` parser panic, an `.ndjson` that
/// was never regenerated — and would pass a bare "exit 2" assertion while
/// measuring nothing at all. So the reason string is matched too: it has to be
/// the mutual decline, naming the block's first member, and not any other way
/// of reaching the same code.
#[test]
fn every_mutual_fixture_declines_for_being_mutual() {
    // The first member of each block, which is the name `convert::load`
    // reports. Read from the fixture rather than derived, so that a fixture
    // whose block order changed fails here rather than silently re-pointing.
    let first_member = [
        ("mutual_three_way_cycle", "A"),
        ("mutual_expr_stmt_ast", "Exp"),
        ("mutual_parameters", "PA"),
        ("mutual_indices", "T0"),
        ("mutual_prop_even_odd", "Even"),
        ("mutual_one_recursive", "OA"),
        ("mutual_universe_polymorphic", "UA"),
    ];
    assert_eq!(first_member.len(), FIXTURES.len());
    for (name, member) in first_member {
        let (code, stdout) = run(name);
        assert_eq!(code, Some(2), "{name} did not decline:\n{stdout}");
        let want = format!("declined: Mutual inductive {member} not supported");
        assert!(
            stdout.contains(&want),
            "{name} declined for the wrong reason — expected `{want}`:\n{stdout}"
        );
    }
}
