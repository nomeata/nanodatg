//! **`succ` as an element of a function space** — the graph
//! `{⟨x, succ x⟩ : x ∈ ω}`, its typing, and its β rule.
//!
//! # Interface
//!
//! ```text
//! SuccFun::over(env, nat) -> SuccFun
//!   .term          the term `lam(ω)`
//!   .in_funspace   ⊢ lam(ω) ∈ fs(ω, ω)
//!   .beta          ⊢ ∀n. (n ∈ ω → app(lam(ω), n) = succ(n))
//! ```
//!
//! # Why this exists at all — a term-former is not a set
//!
//! Everything else in [`crate::nat`] speaks of `succ` as a **term-former**:
//! [`Nat::succ_of`](crate::nat::Nat::succ_of) builds `succ(t)` and
//! [`Nat::iota_succ`](crate::nat::Nat::iota_succ) is stated at it. That is the
//! right shape for arithmetic and the wrong one for an *interpretation of
//! Lean*, where `Nat.succ` is a constant of type `Nat → Nat` and therefore has
//! to interpret to a **set** lying in `fs(⟦Nat⟧,⟦Nat⟧)` — something the checker
//! can apply with `app` and pass around as a value.
//!
//! The W-type presentation this replaces carried the same three fields
//! (`succ_fun`, `succ_in_funspace`, `succ_beta` on `crate::wnat::Nat`), so the
//! consumer's shape is unchanged; only the object is.
//!
//! # It is assembly, not a new derivation
//!
//! Nothing here is proved. All three pieces already exist, and the only content
//! is that their statements line up:
//!
//! * [`crate::funcs::lambda_n`] mints the graph symbol `lam` and its defining
//!   axiom from **any** unary symbol, and `succ` is one
//!   ([`OmegaCore::succ`](crate::recursion::naturals::OmegaCore::succ));
//! * [`crate::ext::lam_in_funspace_n`] concludes
//!   `⊢ ∀A ∀C. ((∀x. (x ∈ A → succ(x) ∈ C)) → lam(A) ∈ fs(A,C))`, and at
//!   `A := C := ω` **its antecedent is literally
//!   [`Nat::succ_mem`](crate::nat::Nat::succ_mem)** — `⊢ ∀n. (n ∈ ω → succ(n) ∈ ω)`,
//!   the closure property `ω` is defined by. So the discharge is one `mp` and
//!   no side derivation;
//! * [`crate::funcs::beta_conditional_n`] concludes
//!   `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = succ(a))`, and `A := ω` is the β rule.
//!
//! The `k = 0` shape is used throughout: `succ` has arity 1, so there is no
//! parameter prefix and `lam` has arity 1 — the domain alone.
//!
//! # The funspace is the tower's, so nothing has to be passed in
//!
//! There is no `fs` anywhere else under [`crate::nat`], deliberately: `ω`'s
//! arithmetic never needs one. But it does not have to be a parameter either —
//! [`Nat`] carries its own [`Tower`](crate::tower::Tower), and
//! `tower.sums.prod` / `tower.sums.fs` are the very product and function space
//! [`crate::prelude::prelude`] hands the interpretation (`prelude.rs:192` reads
//! them off the same tower). So the `fs` this typing is stated at **is** the
//! `fs` `⟦α → β⟧` is interpreted with, by construction rather than by a
//! caller's discipline. Taking them as arguments would let a caller pass a
//! second pair and get a true theorem about the wrong set.

use kernel::{Env, Formula, FnSym, Term, Thm};

use crate::err::imported;
use crate::nat::Nat;
use crate::{inst_all, DResult};

/// The successor as a set function on `ω`.
pub struct SuccFun {
    /// The graph symbol `lam`, arity 1 — its argument is the domain.
    pub lam: FnSym,
    /// `⊢ ∀A ∀z. (z ∈ lam(A) ↔ ∃x. (x ∈ A ∧ z = ⟨x, succ x⟩))`, the graph's
    /// defining axiom. Kept because a caller that wants the graph at a domain
    /// other than `ω` needs it and rebuilding it would mint a second symbol.
    pub lam_ax: Thm,
    /// `lam(ω)` — the term `⟦Nat.succ⟧` interprets to.
    pub term: Term,
    /// `⊢ lam(ω) ∈ fs(ω, ω)`.
    pub in_funspace: Thm,
    /// `⊢ ∀n. (n ∈ ω → app(lam(ω), n) = succ(n))`.
    pub beta: Thm,
}

impl SuccFun {
    /// Build the graph, over `nat`'s own tower.
    ///
    /// Every operator involved — the `app`, the product and the function space
    /// — is read off `nat.tower`, so there is no provenance for a caller to get
    /// wrong. The conclusion pin below still fails loudly if the terms do not
    /// line up.
    pub fn over(env: &mut Env, nat: &Nat) -> DResult<SuccFun> {
        let succ = nat.core().succ;
        let omega = nat.omega();
        let sums = &nat.tower.sums;
        let (ap, prod, fs) = (&sums.ap, &sums.prod, &sums.fs);

        let (lam, lam_ax) =
            imported("crate::funcs::lambda_n", crate::funcs::lambda_n(env, ap, succ))?;
        let term = Term::apply(lam, vec![omega.clone()]);

        // ── `⊢ lam(ω) ∈ fs(ω,ω)`, by `succ_mem` and nothing else ─────────────
        let generic = imported(
            "crate::ext::lam_in_funspace_n",
            crate::ext::lam_in_funspace_n(env, ap, prod, fs, succ, lam, &lam_ax),
        )?;
        let at = imported(
            "instantiating lam_in_funspace_n at A := C := ω",
            inst_all(&generic, &[omega.clone(), omega.clone()]),
        )?;
        let in_funspace =
            imported("discharging lam_in_funspace_n by Nat::succ_mem", Thm::mp(&at, nat.succ_mem()))?;
        // Pinned rather than `debug_assert`ed: this is the statement every
        // consumer rests on, and an antecedent that failed to match would
        // otherwise leave an implication looking like a membership.
        let want = Formula::mem(term.clone(), fs.of(omega.clone(), omega.clone()));
        if *in_funspace.concl() != want {
            return Err(crate::decline!(
                "the successor graph's typing is not `lam(ω) ∈ fs(ω,ω)`"
            ))
        }

        // ── `⊢ ∀n. (n ∈ ω → app(lam(ω), n) = succ(n))` ───────────────────────
        let generic_beta = imported(
            "crate::funcs::beta_conditional_n",
            crate::funcs::beta_conditional_n(env, ap, succ, lam, &lam_ax),
        )?;
        let beta = imported(
            "instantiating beta_conditional_n at A := ω",
            inst_all(&generic_beta, &[omega.clone()]),
        )?;

        Ok(SuccFun { lam, lam_ax, term, in_funspace, beta })
    }
}
