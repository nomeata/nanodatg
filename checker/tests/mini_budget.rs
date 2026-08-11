//! **A budget refusal is a decline, not a rejection** — the classification
//! `233bbc1` designed, now actually reachable.
//!
//! The two words are different claims about the world: `reject` says the
//! *file* is ill-typed, `decline` says *mini* does not handle it, and a
//! budget bound is the second — the file may be perfectly good. `233bbc1`
//! landed [`nanoda_lib::mini::kernel::BUDGET_DECLINE`] and `run.rs`'s `starts_with`
//! classification, but **neither budget site ever attached the prefix**
//! (`git log -S '{BUDGET_DECLINE}'` finds no interpolation in any commit), so
//! the classification was dead code and a budget refusal printed `reject` —
//! putting a true file in the population of false ones. Nothing could go red
//! on it because no committed fixture exhausted the budget; the first run to
//! traverse the path was track D's routed `init-prelude` measurement, which
//! printed `reject ByteArray.IsValidUTF8` where `NAT-REPRESENTATION.md:257`
//! records `decline budget: …` for the same stop.
//!
//! The fixture is generated (`fixtures/budget_decline.ndjson`): `Eq`, `Nat`
//! and a theorem `deepEq : Eq Nat 2100 (succ^2100 zero) := Eq.refl Nat 2100`.
//! Deciding the type forces `def_eq(natLit 2100, succ-tower)`, which steps a
//! level per successor and exhausts [`nanoda_lib::mini::kernel::DEFEQ_MAX_DEPTH`] = 2000
//! — cheaply (well under a second), unlike the 22.3 T-instruction
//! `init-prelude` witness. **Red before `budget_refusal` (the verdict was
//! `Rejected`), green after.**

use std::path::Path;

#[test]
fn a_budget_refusal_is_a_decline_not_a_rejection() {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/budget_decline.ndjson");
    let out = nanoda_lib::mini::run::check_file_deep_with(&p, nanoda_lib::mini::run::Options::default());
    match &out.verdict {
        nanoda_lib::mini::run::Verdict::Declined { reason } => {
            assert!(
                reason.starts_with(nanoda_lib::mini::kernel::BUDGET_DECLINE),
                "the decline must carry the budget prefix the classifier reads: {reason}"
            );
            assert!(
                reason.contains("recursed past"),
                "the decline must still say what ran out: {reason}"
            );
        }
        v => panic!(
            "a well-typed file that exhausts the recursion budget must be *declined* — \
             reject says the file is ill-typed, and this one is not. Got {v:?}"
        ),
    }
}
