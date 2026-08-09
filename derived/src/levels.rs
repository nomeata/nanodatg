//! **Levels as elements of `ω`** — the target-side vocabulary for
//! level-polymorphic checking (`LEVELPOLY.md`).
//!
//! This module is a **hub** in the crate's usual shape: every construction
//! lives in its own file with its own interface header. Nothing here is
//! consumed by the ground-σ checker path yet; the constructions exist to
//! establish, in the set theory itself, the vocabulary the level-quantified
//! design needs:
//!
//! | file | what it exports |
//! |---|---|
//! | [`ite0`] | the conditional term former `ite0(g,a,b)` — `a` if `g = ∅`, else `b` |
//! | [`order`] | trichotomy on `ω`, the case principle, `⊆`-linearity, and `max = ∪` |
//! | [`utower`] | the internal universe ladder `lvl` — the recursion theorem at `G := U(·)`, seed `ω` |
//! | [`srt`] | `srt(n) = ite0(n, U₀, app(lvl,n))` — `⟦Sort ·⟧` as one term function of a variable level |
//! | [`rules`] | typing rules at a variable level: Π-formation at `imax`, with the `ite0` split |
//!
//! Interpreting a Lean level expression over parameters `u⃗` (each under a
//! `uᵢ ∈ ω` hypothesis):
//!
//! ```text
//! 0̂ = ∅      (succ ℓ)̂ = succ(ℓ̂)      (max ℓ ℓ')̂ = ℓ̂ ∪ ℓ̂'
//! (imax ℓ ℓ')̂ = ite0(ℓ̂', ∅, ℓ̂ ∪ ℓ̂')
//! ```
//!
//! `max` is binary union on the nose — von Neumann naturals are `⊆`-linearly
//! ordered ([`order`]) — and `imax` is the one conditional, which is the
//! if-then-else the design brief predicted.

pub mod ite0;
pub mod order;
pub mod srt;
pub mod utower;
pub mod rules;
