//! **SUPERSEDED, and this is the file that decided it.** The merge cost of the
//! above-kernel deduction layer, measured: `13u² + 73u − 134` kernel calls for
//! `u = |Γ ∪ Δ|`, exact at every point measured, against a constant 53 once the
//! sets agree. See the "SUPERSEDED" section of `derived/src/hyp.rs`.
//!
//! Kernel-call cost of the **union-merge** itself, as a function of the two
//! hypothesis-set sizes.
//!
//! # Why this file exists
//!
//! A [`derived::hyp::Hyp`] keeps its hypotheses as *antecedents inside the
//! formula*, because that is the only place a `Thm` has room for them. So
//! combining two `Hyp`s is **not** the set union a natural-deduction system
//! performs beside the formula: both theorems have to be re-proved against the
//! larger antecedent, which means rebuilding projections and reassembling a
//! conjunction. That is real kernel work, and this file measures it rather than
//! estimating it.
//!
//! # How to read a number off
//!
//! Every test here is an *entry point for a coverage run*, not an assertion
//! about cost — nothing is asserted, because a kernel-call count is not a
//! property the build should fail on. Build the test binary with
//! `-C instrument-coverage`, run one test per process with its own
//! `LLVM_PROFILE_FILE`, and read the execution count of each
//! `kernel::thm::Thm::*` function out of `llvm-cov export`.
//!
//! Each cell comes in two halves:
//!
//! * `base_m_n` builds the two `Hyp`s and stops;
//! * `full_m_n` does the same and then performs one `and_intro`.
//!
//! `full − base` is the cost of one binary operation on sets of sizes `m` and
//! `n`. Subtracting the `same_*` pair — two `Hyp`s over the *identical* set,
//! where the merge is a no-op — removes the constant cost of `hyp_and` and
//! leaves the merge alone.
//!
//! Memoisation is **off** throughout, so these are the raw per-merge figures.
//! `hyp_rederivation.rs` reports the memoised cost in a real derivation, which
//! is the number that matters for whether the layer is affordable.

use derived::hyp::{order, Hyp};
use kernel::{Env, Formula, Term};

/// `n` distinct atomic formulas over fresh 0-ary symbols.
fn atoms(env: &mut Env, n: usize) -> Vec<Formula> {
    (0..n)
        .map(|_| {
            let a = Term::apply(env.declare(0), vec![]);
            let b = Term::apply(env.declare(0), vec![]);
            Formula::mem(a, b)
        })
        .collect()
}

/// A `Hyp` assuming exactly `hs`, built with one weakening step.
fn under(hs: &[Formula]) -> Hyp {
    let h = Hyp::assume(hs[0].clone());
    if hs.len() == 1 {
        h
    } else {
        h.weaken(&hs[1..]).expect("weaken")
    }
}

/// Two `Hyp`s over disjoint sets of sizes `m` and `n`; merge them or not.
fn disjoint(m: usize, n: usize, merge: bool) {
    let was = order::memo_enabled(false);
    let mut env = Env::new();
    let all = atoms(&mut env, m + n);
    let a = under(&all[..m]);
    let b = under(&all[m..]);
    if merge {
        let out = a.and_intro(&b).expect("merge");
        assert_eq!(out.hyps().len(), m + n, "the union must have every hypothesis");
    }
    order::memo_enabled(was);
    order::forget();
}

/// Two `Hyp`s over the *same* set of size `k`, where the merge is a no-op.
fn shared(k: usize, merge: bool) {
    let was = order::memo_enabled(false);
    let mut env = Env::new();
    let all = atoms(&mut env, k);
    let a = under(&all);
    let b = under(&all);
    if merge {
        let out = a.and_intro(&b).expect("merge");
        assert_eq!(out.hyps().len(), k);
    }
    order::memo_enabled(was);
    order::forget();
}

/// A chain of `k` merges, each folding one fresh hypothesis into a growing set
/// — the shape a deep derivation actually has. Run with the memo on and off to
/// see how much of the cost is recovered by reuse.
fn chain(k: usize, memo: bool, run: bool) {
    let was = order::memo_enabled(memo);
    let mut env = Env::new();
    let all = atoms(&mut env, k + 1);
    let mut acc = Hyp::assume(all[0].clone());
    if run {
        for a in &all[1..] {
            acc = acc.and_intro(&Hyp::assume(a.clone())).expect("merge");
        }
        assert_eq!(acc.hyps().len(), k + 1);
    }
    order::memo_enabled(was);
    order::forget();
}

macro_rules! cells {
    ($($name:ident => $body:expr;)*) => { $(
        #[test]
        fn $name() { $body }
    )* };
}

cells! {
    base_1_1 => disjoint(1, 1, false);
    full_1_1 => disjoint(1, 1, true);
    base_1_2 => disjoint(1, 2, false);
    full_1_2 => disjoint(1, 2, true);
    base_2_2 => disjoint(2, 2, false);
    full_2_2 => disjoint(2, 2, true);
    base_2_3 => disjoint(2, 3, false);
    full_2_3 => disjoint(2, 3, true);
    base_3_3 => disjoint(3, 3, false);
    full_3_3 => disjoint(3, 3, true);
    base_4_4 => disjoint(4, 4, false);
    full_4_4 => disjoint(4, 4, true);
    base_5_5 => disjoint(5, 5, false);
    full_5_5 => disjoint(5, 5, true);
    base_6_6 => disjoint(6, 6, false);
    full_6_6 => disjoint(6, 6, true);
    base_8_8 => disjoint(8, 8, false);
    full_8_8 => disjoint(8, 8, true);
    base_1_7 => disjoint(1, 7, false);
    full_1_7 => disjoint(1, 7, true);

    same_base_1 => shared(1, false);
    same_full_1 => shared(1, true);
    same_base_4 => shared(4, false);
    same_full_4 => shared(4, true);
    same_base_8 => shared(8, false);
    same_full_8 => shared(8, true);

    chain_base_memo_8 => chain(8, true, false);
    chain_full_memo_8 => chain(8, true, true);
    chain_base_raw_8 => chain(8, false, false);
    chain_full_raw_8 => chain(8, false, true);
    chain_base_memo_16 => chain(16, true, false);
    chain_full_memo_16 => chain(16, true, true);
    chain_base_raw_16 => chain(16, false, false);
    chain_full_raw_16 => chain(16, false, true);
}
