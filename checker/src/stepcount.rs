//! Definitional-equality step counters.
//!
//! A measurement probe, not a feature. The question it answers: how many
//! conversion steps, and of which kinds, does checking a real Lean development
//! actually take? Nobody has run a library of mathlib's size through a
//! set-theoretic checker, so the number is genuinely unknown — and it decides
//! whether the whole proof-carrying approach is affordable, and which step kinds
//! the eventual kernel API should be optimised for.
//!
//! Deliberately kept to a one-line call at each reduction site rather than any
//! restructuring: the number is only trustworthy if the code producing it is
//! still recognisably upstream nanoda.
//!
//! Zero cost unless the `stepcount` feature is enabled — [`bump`] compiles to
//! nothing, so ordinary builds are unaffected and the call sites need no `cfg`.
//!
//! Counters are global atomics rather than per-`TypeChecker` fields because
//! `check_all_declars_par` checks declarations on several threads, and threading
//! a counter struct through would be exactly the restructuring we are avoiding.

#[cfg(feature = "stepcount")]
use std::sync::atomic::{AtomicU64, Ordering};

/// The kinds of step we bucket by. Ordering matches the report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Kind {
    /// `def_eq` was entered.
    DefEqCall,
    /// `def_eq` returned early from the union-find / pointer-equality cache.
    DefEqCacheHit,
    /// Beta: `(λx. b) a ↝ b[a/x]`.
    Beta,
    /// Zeta: `let x := v; b ↝ b[v/x]`.
    Zeta,
    /// Delta: unfolding a definition.
    Delta,
    /// Iota: recursor applied to a constructor.
    Iota,
    /// `Quot.lift` / `Quot.ind` reduction.
    Quot,
    /// Structure projection reduced against a constructor application.
    Proj,
    /// Literal arithmetic short-circuited to host bignum ops (`Nat.add`, ...).
    NatLit,
    /// String literal expanded to its constructor form.
    StringLit,
    /// Two terms identified because both are proofs of the same proposition.
    ProofIrrel,
    /// Eta for functions: `λx. f x ≡ f`.
    Eta,
    /// Eta for structures: `s ≡ ⟨s.1, ..., s.n⟩`.
    EtaStruct,
    /// A beta contraction whose argument the backend had no typing for, so
    /// `whnf` was asked to infer one. See `TypeChecker::beta_arg_typing`.
    BetaArgAsked,
    /// …and the inference produced a typing at the binder's domain, handed to
    /// the backend's store. The gap between the two is arguments `def_eq`
    /// declined or inference could not type.
    BetaArgTyped,
}

/// Number of variants in [`Kind`]. Keep in step with the enum.
pub const N_KINDS: usize = 15;

/// Human-readable names, indexed by `Kind as usize`.
pub const KIND_NAMES: [&str; N_KINDS] = [
    "def_eq calls",
    "def_eq cache hits",
    "beta",
    "zeta (let)",
    "delta",
    "iota (rec)",
    "quot",
    "proj",
    "nat literal arith",
    "string literal",
    "proof irrelevance",
    "eta",
    "eta struct",
    "beta arg: typing asked of whnf",
    "beta arg: typing derived and handed off",
];

#[cfg(feature = "stepcount")]
static COUNTS: [AtomicU64; N_KINDS] = [
    AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
    AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
    AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
    AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
];

/// Record one step of the given kind. Compiles to nothing without the
/// `stepcount` feature.
#[inline(always)]
pub fn bump(kind: Kind) {
    #[cfg(feature = "stepcount")]
    // `Relaxed` is right here: the counters are a monotone tally that is only
    // read after all checking threads have joined, so no ordering against other
    // memory matters and we do not want to slow the hot path.
    COUNTS[kind as usize].fetch_add(1, Ordering::Relaxed);
    #[cfg(not(feature = "stepcount"))]
    let _ = kind;
}

/// Snapshot the counters.
pub fn snapshot() -> [u64; N_KINDS] {
    #[cfg(feature = "stepcount")]
    {
        let mut out = [0u64; N_KINDS];
        for (i, c) in COUNTS.iter().enumerate() {
            out[i] = c.load(Ordering::Relaxed);
        }
        out
    }
    #[cfg(not(feature = "stepcount"))]
    [0u64; N_KINDS]
}

/// Whether counting is compiled in.
pub const fn enabled() -> bool { cfg!(feature = "stepcount") }

/// Render the counters as a report, or `None` if counting is not compiled in.
pub fn report() -> Option<String> {
    if !enabled() {
        return None
    }
    let counts = snapshot();
    const TOTAL_LABEL: &str = "TOTAL reduction steps";
    let width = KIND_NAMES.iter().map(|n| n.len()).chain([TOTAL_LABEL.len()]).max().unwrap_or(0);
    // Reduction steps proper — excludes the two `def_eq` bookkeeping rows.
    let total: u64 = counts[Kind::Beta as usize..].iter().sum();
    let mut s = String::from("definitional-equality step counts\n");
    for (i, name) in KIND_NAMES.iter().enumerate() {
        s.push_str(&format!("  {name:<width$}  {:>14}\n", counts[i]));
    }
    s.push_str(&format!("  {TOTAL_LABEL:<width$}  {total:>14}\n"));
    Some(s)
}
