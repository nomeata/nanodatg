//! **The one place `derived/` introduces a hypothesis** — and discharges it.
//!
//! # Interface
//!
//! ```text
//! assuming(h)              {h} ⊢ h                       — Thm::assume
//! discharge(&h, Γ ⊢ φ)     Γ∖{h} ⊢ h → φ                 — Thm::implies_intr
//! under(h, body)           the matched pair, in one call
//! under_all(&hs, body)     the same at several hypotheses, outermost first
//! ```
//!
//! `ci/check-boundary.sh` rule R6′/I1 allows `Thm::assume` and
//! `Thm::implies_intr` in shipped `derived/` code **only in this file**. It is
//! the analogue of `checker/src/scope.rs`, and the reason it exists is worth
//! stating rather than leaving to the CI script.
//!
//! # Why `derived/` acquired one, having managed without
//!
//! R6′ used to record that `derived/` "has no such module: it *derives*, it does
//! not assume". That was a true statement about the code, and the code it
//! described worked by building implications out of `S` and `K` — the
//! `a1i`/`syl`/`hyp_mp`/`hyp_eq_trans` toolkit in `crate` and
//! [`crate::recursion::hyp`]. That style is fine for a derivation five links
//! long. It is not fine for arithmetic: [`crate::nat`] proves a dozen lemmas
//! that are each a ten-link equational chain under an induction hypothesis, and
//! written combinator-style every link becomes a `syl` whose two implications
//! have to be spelled out. The result is unreadable, and unreadable derivations
//! are where this project's bugs have come from.
//!
//! The kernel already has the rule that fixes this — [`Thm::implies_intr`] is
//! the deduction theorem *as a rule* — and using it is sound: `assume` asserts
//! nothing about `h`, which is exactly what R6′'s own header says. What the ban
//! was really protecting was two engineering weaknesses, and neither is
//! reintroduced here:
//!
//! * **`Thm::gen` panics when the generalised variable is free in a
//!   hypothesis.** `derived/` has ~700 `gen` call sites and R6′ deliberately
//!   does not apply I3 to it. So a caller of this module that generalises must
//!   discharge first, or use [`crate::prim::gen`] — `Thm::gen_checked` with a
//!   site attached, so the side condition arrives as an `Assembly` naming the
//!   variable and the theorem rather than as a bare `None` or an abort.
//!   [`under`] and [`under_all`] make the discharge structural — the hypothesis
//!   cannot outlive the call — which is why they are the forms to prefer and
//!   `assuming`/`discharge` are for the cases where the two ends are far apart.
//! * **A `Thm` establishes its conclusion only when `hyps()` is empty.** That
//!   is the consumer half, and it is unchanged: every public entry of
//!   `derived/` still owes `⊢`, and [`crate::all_unconditional`] is how a
//!   consumer pins it. `derived/tests/nat.rs` asserts it on every theorem
//!   `crate::nat` exports.
//!
//! # What this file does *not* do
//!
//! It does not make a hypothesis safe to *return*. Nothing here checks that the
//! caller discharged everything it assumed, because a legitimate nested
//! derivation discharges an inner hypothesis while an outer one is still open —
//! [`crate::nat::glue::induct_step`] does exactly that inside a lemma that has
//! already assumed `x ∈ ω`. The guarantee this file buys is narrower and still
//! worth having: `Thm::assume` appears in one auditable place, so "which
//! `derived/` code can put something in `Γ`" is a one-file question.
//!
//! **`under` does not make escape impossible either, and that is worth saying
//! plainly rather than leaving to a reader's optimism.** The *discharge* is
//! forced by the shape — line 86 and the `rev().fold` below apply
//! [`Thm::implies_intr`] unconditionally, and no return path skips them — but
//! the assumption itself is handed to `body` as a `&Thm`, `Thm` is `Clone`, and
//! the closure's captures are unconstrained. A body that stashes
//! `assumed.clone()` in a captured `RefCell` keeps `{h} ⊢ h` alive after `under`
//! has returned `⊢ h → ψ`. So does calling [`assuming`] directly, which is
//! `pub` and deliberately so. The property this module has is *auditability*,
//! not containment; the property the crate relies on is the consumer half —
//! every public entry owing `⊢` checks [`crate::all_unconditional`] on what it
//! was given, and `derived/tests/nat.rs` asserts `hyps().is_empty()` on
//! everything [`crate::nat`] exports.

use kernel::{Formula, Thm};

/// `{h} ⊢ h`. The only introduction of a hypothesis in `derived/`.
///
/// Prefer [`under`], which cannot leave the hypothesis open.
pub fn assuming(h: Formula) -> Thm { Thm::assume(h) }

/// From `Γ ⊢ φ` infer `Γ∖{h} ⊢ h → φ`.
///
/// **`h` need not be among the hypotheses**; the rule then silently weakens.
/// That is [`Thm::implies_intr`]'s own documented behaviour and it is sound, but
/// it means a caller who *believes* it has discharged something should check
/// [`Thm::hyps`] — or use [`under`], where the pairing is structural.
pub fn discharge(h: &Formula, thm: &Thm) -> Thm { Thm::implies_intr(h, thm) }

/// `⊢ h → ψ`, from a derivation of `ψ` that may use `h`.
///
/// The matched pair in one call: `body` is handed `{h} ⊢ h` and returns `ψ`,
/// and the hypothesis is discharged on the way out. Any *other* hypothesis the
/// body picked up survives, which is what makes this usable inside a derivation
/// that has already assumed something.
pub fn under<F>(h: Formula, body: F) -> Option<Thm>
where
    F: FnOnce(&Thm) -> Option<Thm>,
{
    let assumed = assuming(h.clone());
    let out = body(&assumed)?;
    Some(discharge(&h, &out))
}

/// `⊢ h₀ → (h₁ → … → ψ)`, outermost first.
///
/// `body` receives `{hᵢ} ⊢ hᵢ` for each, in the same order.
pub fn under_all<F>(hs: &[Formula], body: F) -> Option<Thm>
where
    F: FnOnce(&[Thm]) -> Option<Thm>,
{
    let assumed: Vec<Thm> = hs.iter().cloned().map(assuming).collect();
    let out = body(&assumed)?;
    Some(hs.iter().rev().fold(out, |acc, h| discharge(h, &acc)))
}
