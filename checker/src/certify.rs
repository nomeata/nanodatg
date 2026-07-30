//! Selection of the active proof backend, and the result type that carries
//! certificates out of definitional-equality checks.
//!
//! # Why `def_eq` cannot return `bool`
//!
//! The point of the project is that "these two Lean terms are definitionally
//! equal" must come with evidence. A `bool` loses the evidence, and — worse —
//! makes it impossible to tell, by reading the code, whether a given conclusion
//! *has* a justification. So every definitional-equality path returns
//! [`DefEq`], which is `Option`-shaped: `Some(cert)` carries the reason, `None`
//! means "not shown equal".
//!
//! # Backend selection
//!
//! Exactly one backend is active per build. [`Backend`] is the alias every
//! other module refers to; today it is the kernel's `NullCertifier`, whose
//! `Cert` is `()` and therefore free. Milestone 3 swaps this alias for the
//! Tarski–Grothendieck backend and nothing else in the checker changes shape.
//!
//! Note that the null backend is instantiated with the checker's *real* context
//! type, `TcCtx`, not with `()`. It ignores the context, but every call site
//! passes the genuine arena, so the code is already in the shape the real
//! backend needs. That is deliberate: the failure mode this design is guarding
//! against is discovering at milestone 3 that certificates were never
//! obtainable at the places that claimed them.

#[cfg(not(feature = "tg"))]
use crate::util::{ExprPtr, TcCtx};

/// The proof backend in force for this build.
///
/// **Milestone 3 obligation:** once the TG backend exists, `NullCertifier` must
/// be unreachable in a release build. The `null-certifier` feature on the
/// `kernel` crate exists so that gate is a one-line change.
#[cfg(not(feature = "tg"))]
pub type Backend<'x, 't, 'p> = kernel::NullCertifier<ExprPtr<'t>, TcCtx<'t, 'p>>;

/// The real Tarski–Grothendieck backend, whose `Cert` is a genuine kernel
/// theorem. Enable with `--features tg`.
///
/// It is opt-in rather than default for now because it is strictly more
/// expensive — it interprets every Lean expression into a first-order term and
/// builds an actual derivation at every step — and because the parts it cannot
/// yet prove (beta, delta, zeta, eta) are reported rather than assumed, so the
/// two backends answer different questions. `NullCertifier` answers "does this
/// development check?"; `TgBackend` answers "and was every step derived?".
#[cfg(feature = "tg")]
pub type Backend<'x, 't, 'p> = crate::tg::TgBackend<'x, 't, 'p>;

/// Build the active backend.
///
/// The `Env` is what lets the TG backend resolve a constant to its *value*, so
/// that `⟦c⟧` can be introduced as an explicit definition `⟦c⟧ := ⟦value⟧`
/// rather than as an opaque symbol. Without it, delta reduction could never be
/// justified: there would be nothing relating the constant to what it unfolds
/// to. The null backend ignores it.
#[cfg(feature = "tg")]
pub fn new_backend<'x, 't: 'x, 'p: 't>(env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    crate::tg::TgBackend::new(env)
}

/// Build the active backend (null variant; the environment is unused).
#[cfg(not(feature = "tg"))]
pub fn new_backend<'x, 't: 'x, 'p: 't>(_env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    kernel::NullCertifier::new()
}

/// The certificate type of the active backend.
#[cfg(feature = "tg")]
pub type Cert<'t, 'p> = crate::tg::TgCert;

/// The certificate type of the active backend (null variant: no information).
#[cfg(not(feature = "tg"))]
pub type Cert<'t, 'p> = ();

/// The result of a definitional-equality check.
///
/// `Some(cert)` means the two terms were shown equal, and `cert` is why.
/// `None` means they were not shown equal — which, for a *checker*, is the
/// same as "reject": we never assert an equality we cannot justify.
pub type DefEq<'t, 'p> = Option<Cert<'t, 'p>>;

/// The places that still conclude an equality without a real justification,
/// i.e. that call [`Certifier::admit`].
///
/// Every variant is a hole that milestone 3 must close. They are an enum rather
/// than scattered string literals so that the remaining work is enumerable, a
/// new hole cannot be added without naming it here, and each site can be
/// counted (see [`admit_report`]).
///
/// The plumbing was introduced from the *outside in*: the top-level `def_eq`
/// entry points and the rules that map directly onto backend primitives
/// (reflexivity, sort equality, constant equality, eta) thread real
/// certificates, while the deeper structural comparisons — which upstream
/// nanoda expresses as plain `bool`-returning recursion — still admit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Admit {
    /// Structural/alpha comparison of two binder chains (`def_eq_binder_aux`).
    Binder,
    /// Congruence over a spine of applications (`def_eq_app`).
    App,
    /// Two `Local`s with the same id (`def_eq_local`).
    Local,
    /// Two projections of def-eq structures (`def_eq_proj`).
    Proj,
    /// Proof irrelevance: two proofs of def-eq propositions.
    ProofIrrel,
    /// Eta for structures.
    EtaStruct,
    /// String literal expanded to constructor form.
    StringLit,
    /// Elements of a subsingleton structure.
    UnitLike,
    /// Recovered from the union-find equality cache. A proof-producing
    /// union-find (an explain-path over a proof forest) is what replaces this,
    /// and it is the highest-value hole to close: 88% of `def_eq` calls are
    /// answered here (see `MEASUREMENTS.md`).
    Cache,
    /// The lazy-delta loop concluded equality after unfolding.
    LazyDelta,
    /// `Bool.true`-normalisation shortcut in `def_eq`.
    BoolTrue,
    /// Weak-head normalisation: `e` reduces to `whnf(e)`.
    ///
    /// `whnf` performs beta, zeta, delta, iota, quotient and projection steps
    /// internally and returns only the reduced term, so the checker cannot
    /// currently say *which* rules justify the reduction. Making `whnf` return
    /// evidence alongside the reduct is the next structural piece of work; see
    /// DECISIONS.md.
    Whnf,
}

/// Number of [`Admit`] variants.
pub const N_ADMITS: usize = 12;

impl Admit {
    /// A stable name, used in the report and passed to the backend.
    pub const fn name(self) -> &'static str {
        match self {
            Admit::Binder => "def_eq_binder",
            Admit::App => "def_eq_app",
            Admit::Local => "def_eq_local",
            Admit::Proj => "def_eq_proj",
            Admit::ProofIrrel => "proof_irrel",
            Admit::EtaStruct => "eta_struct",
            Admit::StringLit => "string_lit",
            Admit::UnitLike => "unit_like",
            Admit::Cache => "eq_cache",
            Admit::LazyDelta => "lazy_delta",
            Admit::BoolTrue => "bool_true",
            Admit::Whnf => "whnf",
        }
    }

    /// All variants, for reporting.
    pub const ALL: [Admit; N_ADMITS] = [
        Admit::Binder,
        Admit::App,
        Admit::Local,
        Admit::Proj,
        Admit::ProofIrrel,
        Admit::EtaStruct,
        Admit::StringLit,
        Admit::UnitLike,
        Admit::Cache,
        Admit::LazyDelta,
        Admit::BoolTrue,
        Admit::Whnf,
    ];
}

#[cfg(feature = "stepcount")]
static ADMIT_COUNTS: [std::sync::atomic::AtomicU64; N_ADMITS] = [
    const { std::sync::atomic::AtomicU64::new(0) }; N_ADMITS
];

/// Certificates produced by a real backend rule rather than by an admit.
#[cfg(feature = "stepcount")]
static CERTIFIED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one use of an admit site. Compiles to nothing without `stepcount`.
#[inline(always)]
pub fn bump_admit(site: Admit) {
    #[cfg(feature = "stepcount")]
    ADMIT_COUNTS[site as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "stepcount"))]
    let _ = site;
}

/// Record one certificate produced by a genuine backend rule.
#[inline(always)]
pub fn bump_certified() {
    #[cfg(feature = "stepcount")]
    CERTIFIED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Render the certified-vs-admitted breakdown, or `None` if counting is off.
///
/// This is the honest measure of how far the milestone-3 work has to go: the
/// admitted count must reach zero before the TG backend can be trusted.
pub fn admit_report() -> Option<String> {
    if !cfg!(feature = "stepcount") {
        return None
    }
    #[cfg(feature = "stepcount")]
    {
        use std::sync::atomic::Ordering::Relaxed;
        let certified = CERTIFIED.load(Relaxed);
        const CERT_LABEL: &str = "certified (real rule)";
        const TOTAL_LABEL: &str = "TOTAL admitted";
        // Width must cover the rendered label, which for admit rows includes the
        // "admit " prefix — otherwise those rows sit one column out.
        let width = Admit::ALL
            .iter()
            .map(|a| a.name().len() + "admit ".len())
            .chain([CERT_LABEL.len(), TOTAL_LABEL.len()])
            .max()
            .unwrap_or(0);
        let mut s = String::from("definitional-equality certificate provenance\n");
        s.push_str(&format!("  {CERT_LABEL:<width$}  {certified:>14}\n"));
        let mut total_admitted = 0u64;
        for site in Admit::ALL {
            let n = ADMIT_COUNTS[site as usize].load(Relaxed);
            total_admitted += n;
            let label = format!("admit {}", site.name());
            s.push_str(&format!("  {label:<width$}  {n:>14}\n"));
        }
        s.push_str(&format!("  {TOTAL_LABEL:<width$}  {total_admitted:>14}\n"));
        Some(s)
    }
    #[cfg(not(feature = "stepcount"))]
    None
}
