//! The **accessibility carrier** `acc(A,R)`, as the intersection of all
//! step-closed subsets of `A`.
//!
//! Following Carneiro's *The Type Theory of Lean* §6.2.2: "If `R ⊆ A × A` is a
//! relation, `acc(A,R) ⊆ A` is the set of all elements `x ∈ A` that are
//! `R`-accessible… It is the smallest set `C` such that if `y ∈ C` for all `y`
//! such that `⟨y,x⟩ ∈ R`, then `x ∈ C`." Writing `⟨y,x⟩` for the Kuratowski
//! pair, that is
//!
//! ```text
//! preds_in(A,R,C,x)  :=  ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ C))
//! step_closed(A,R,C) :=  ∀x. (x ∈ A → (preds_in(A,R,C,x) → x ∈ C))
//! acc(A,R)           :=  { z ∈ A : ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C) }
//! ```
//!
//! **Nothing here is an axiom.** `acc` is one Separation on `A`; every theorem
//! below is derived from that plus the pairing apparatus already in this crate.
//! Phrasing the intersection as a *condition* rather than as
//! `⋂{C ∈ 𝒫A : step_closed(A,R,C)}` is what keeps it to a single Separation —
//! `𝒫(A)` is never needed. That is the trick [`crate::wtype`] uses, and this
//! module is its least-closed-set pattern transplanted.
//!
//! # Why it is cheaper than `W`, and how much cheaper
//!
//! `acc(A,R) ⊆ A` **by definition**, so the set being carved out of is already
//! given. Consequently:
//!
//! * there is no bound parameter `u` and no `closed(A,B,u)` antecedent, hence
//!   no [`crate::bound`]-style companion module, no universe hypothesis and no
//!   `ω`-tower;
//! * every theorem exported here is **unconditional** — including the
//!   introduction rule, which is the one that costs `W` the whole bound
//!   apparatus (see [`intro`]);
//! * the module needs a pairing operation and an empty set, and nothing else:
//!   no function space, no application, no universe.
//!
//! Measured on 2026-08-01: [`crate::wtype`] and [`crate::bound`] together are
//! 3612 lines, of which `bound` — the module that exists solely to discharge
//! `closed(A,B,u)` at a universe — is 1891. This module is 1291, and there is
//! nothing corresponding to `bound` because there is nothing to discharge.
//!
//! # Why it is needed
//!
//! `acc` is the one member of the thesis's §5.1 menagerie (`⊥`, `Σ`, `+`,
//! `ulift`, `‖·‖`, `W`, `=`, `acc`) that this crate did not have. The
//! interpretation is `⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r⟧)]` (thesis.txt:2126),
//! and §5.3 translates *every* subsingleton eliminator — `Eq.rec` included —
//! through it, because propositional truncation would destroy large
//! elimination. So the indexed-family chain (`acc`, then §5.3, then §5.2's
//! `spec` judgment) starts here.
//!
//! The `φ`-restricted variant `acc^φ_r` of thesis.txt:1831–1845 is *defined
//! from* plain `acc` — `acc^φ_r x := ∃h : φ x. acc_{r'}(x,h)` over the
//! subtype — so it is a separate construction on top of this one and is not
//! built here.
//!
//! # The shape of the development
//!
//! | fact | lemma |
//! |---|---|
//! | `z ∈ acc(A,R) ↔ (z ∈ A ∧ ∀C. …)` | [`acc_symbol`] |
//! | `z ∈ acc(A,R) → z ∈ A` — **A0** | [`acc_subset`] |
//! | `(C ⊆ A ∧ step_closed(A,R,C)) → acc(A,R) ⊆ C` — **A2** | [`acc_induction`] |
//! | `(x ∈ A ∧ preds_in(A,R,acc,x)) → x ∈ acc(A,R)` — **A1** | [`acc_intro`] |
//! | well-founded induction over a formula — **A3** | [`acc_rect`] |
//!
//! **A1 and A2 together say `acc` is the least step-closed subset of `A`**, and
//! A3 is A2 applied to `{z ∈ acc : φ(z)}`. There is no analogue of `W`'s
//! inversion rule W3 or injectivity W4: `acc` has no constructors, only
//! members, which is exactly why the thesis reaches for it when the eliminator
//! is a subsingleton one.
//!
//! # Non-vacuity
//!
//! Both polarities are pinned, and both matter — see [`witness`]:
//!
//! ```text
//! ⊢ ∀A. acc(A,∅) = A                          [acc_empty_relation]
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ¬(⟨z,z⟩ ∈ R))   [acc_no_loops]
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) →
//!       ∀w. ¬(w ∈ A ∧ (⟨z,w⟩ ∈ R ∧ ⟨w,z⟩ ∈ R)))   [acc_no_two_cycle]
//! ```
//!
//! The first shows `acc` is not always empty (so A0, A1 and A2 are not
//! vacuously true); the second and third show it is not always `A` (so A2 and
//! A3 have content, and the `x ∈ A` guard in [`step_closed`] has not collapsed
//! the definition), the third additionally at an *irreflexive* relation.
//!
//! # Out of scope
//!
//! `rec_acc` — the recursor of thesis.txt:2155–2166, defined by transfinite
//! recursion along `acc(A,R)` — is a **separate** construction and is not here.
//! This module is the carrier and its introduction and induction principles;
//! [`acc_rect`] is induction over a *formula*, which is what the soundness
//! argument needs first, not recursion into `V`.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::acc::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`condition`] | [`preds_in`], [`step_closed`], [`acc_cond`], the symbol `acc(A,R)`, and `acc ⊆ A` |
//! | [`induction`] | **A2** — `acc` is the least step-closed subset of `A` |
//! | [`intro`] | **A1** — the introduction rule, unconditionally |
//! | [`rect`] | **A3** — well-founded induction over a formula: [`ind_step`], [`Params`], [`acc_rect`] |
//! | [`witness`] | non-vacuity in both polarities |
//! | [`apparatus`] | [`Acc`] — every symbol and theorem over one definitional extension |
//!
//! `shared` holds the one private combinator more than one of them needs; it
//! exports no theorem and is not re-exported.

pub mod apparatus;
pub mod condition;
pub mod induction;
pub mod intro;
pub mod rect;
mod shared;
pub mod witness;

pub use apparatus::Acc;
pub use condition::{acc_cond, acc_subset, acc_symbol, preds_in, step_closed};
pub use induction::acc_induction;
pub use intro::acc_intro;
pub use rect::{acc_rect, ind_step, Params};
pub use witness::{acc_empty_relation, acc_minimal, acc_no_loops, acc_no_two_cycle};
