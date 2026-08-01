//! Deduction-style reasoning: a theorem together with the *set* of hypotheses
//! it is proved under.
//!
//! # SUPERSEDED — kept as the experiment, not as the plan
//!
//! **This layer is not the design that was adopted, and it should not be built
//! on.** It is kept, complete and passing, because it is the measurement that
//! decided against it. The decision is that hypotheses go **into the kernel's
//! judgement**, Isabelle-style (`Γ ⊢ φ`, hypotheses beside the formula), on the
//! criterion that *each kernel operation must cost `O(1)`*.
//!
//! ## Why this design cannot meet that criterion
//!
//! A `Thm` here is a bare formula, so a `Hyp` has nowhere to put its hypotheses
//! except **inside** that formula, as the antecedent `conj(Γ) → φ`. Combining
//! two `Hyp`s is therefore not the set union a natural-deduction system performs
//! *beside* the formula: both theorems must be re-proved against the larger
//! antecedent, which means rebuilding projections and reassembling a
//! conjunction. That is real kernel work, and it is not constant.
//!
//! ## What it costs, measured
//!
//! `derived/tests/hyp_merge_cost.rs` is the harness; run one test per process
//! under `-C instrument-coverage` and read the execution counts of
//! `kernel::thm::Thm::*` out of `llvm-cov export`. With `u = |Γ ∪ Δ|` and the
//! memo off:
//!
//! ```text
//!   u      |   2    3    4    5    6     8    10    12    16
//!   merge  |  64  202  366  556  772  1282  1896  2614  4362   kernel calls
//! ```
//!
//! which is **exactly** `13u² + 73u − 134` at every point measured — quadratic,
//! not linear, because both operands are retargeted and each of the `u`
//! projections out of the union is itself `O(u)` deep. It depends only on `u`:
//! the splits `(m,n) = (4,4)` and `(1,7)` both cost 1282. The operation's own
//! cost once the sets agree is a constant **53** (measured at `|Γ| = 1, 4, 8`),
//! so a merge is between 1× and 82× the cost of the inference it enables.
//!
//! It compounds. A chain of `k` binary operations each folding in one fresh
//! hypothesis — the shape of any nested argument — costs 6 296 kernel calls at
//! `k = 8` and 33 072 at `k = 16`, i.e. `Θ(k³)`, and memoisation makes **no
//! difference at all** to those figures, because every merge in such a chain
//! targets a hypothesis set that has never been seen before. The memo only pays
//! when a set recurs.
//!
//! Real hypothesis sets do get that deep: the `P₀…P₃` chain in
//! `universe/union.rs::covers_universe` accumulates nine assumptions
//! (`is_universe(u)`, `s ∈ u`, the bijection body, `SBODY(S)`, `z ∈ u`,
//! `⟨x,z⟩ ∈ f`, `w ∈ s`, `x ∈ w`, `IMG(w,b)`), and performs dozens of binary
//! steps at that depth. At `u = 9` a single merge is 1 576 kernel calls.
//!
//! ## The end-to-end comparison
//!
//! `derived/tests/hyp_rederivation.rs` derives one real existing result —
//! `⊢ (is_universe(u) ∧ s ∈ u) → ⋃s ⊆ u`, the `⋃s ⊆ u` step of
//! `universe/union.rs` — twice, and checks that the two conclusions are the same
//! formula. Kernel calls, shared setup subtracted:
//!
//! ```text
//!   hand-written, transcribed from union.rs   705
//!   this layer, memoised                     1443   (2.05×)
//!   this layer, memo off                     1662   (2.36×)
//! ```
//!
//! and that is the *favourable* case: the hypothesis set never exceeds three.
//!
//! ## What survives, for the in-kernel version
//!
//! The interface below is mostly still right — `assume`, `discharge`, the
//! union-merge on every binary operation, `obtain`, and `gen` with the
//! free-variable side condition checked against the hypothesis set are all
//! operations the in-kernel judgement will need. What changes is that they
//! become free: with `Γ` beside the formula, merging is `Vec` union and the
//! formula is untouched. Two findings from building it that carry over verbatim:
//!
//! * **A canonical order on hypotheses is needed, and it cannot be structural
//!   from outside the kernel.** `Formula` exposes `as_eq`/`as_mem`/`as_imp` but
//!   not a `Forall` body, and `Term` cannot be destructured at all, so this layer
//!   had to order by the cached structural hash with a registry to break
//!   collisions ([`order::rank`]). *Inside* the kernel that problem disappears —
//!   `FormulaData` is right there and a real lexicographic order is a dozen
//!   lines. Do that; do not export a hash-based order.
//! * **An unstable order is not a soundness bug but it is a completeness cliff.**
//!   If two equal hypothesis sets can be listed differently, nothing composes and
//!   every later operation returns `None` — silently, and far from the cause. The
//!   in-kernel version should compare hypothesis sets by a canonical form
//!   computed once, not by set-equality at each rule.
//!
//! # Interface
//!
//! ```text
//! struct Hyp { hyps: <canonically ordered, duplicate-free set of Formula>, thm: Thm }
//!
//! ── invariant ────────────────────────────────────────────────────────────────
//!   thm.concl() == conj(hyps) → concl()          and `concl()` is recoverable
//!
//! ── construction and reading ─────────────────────────────────────────────────
//!   Hyp::assume(φ)              {φ} ⊢ φ                     (thm: ⊢ φ → φ)
//!   Hyp::lift(&Thm)             {}  ⊢ φ                     (thm: ⊢ ⊤ → φ)
//!   h.hyps() -> &[Formula]      the hypothesis set, canonically ordered
//!   h.concl() -> &Formula       φ
//!   h.thm()   -> &Thm           ⊢ conj(hyps) → φ
//!   h.into_thm() -> Option<Thm> ⊢ φ, only when hyps is empty
//!
//! ── the hypothesis set ───────────────────────────────────────────────────────
//!   h.weaken(&[Formula])        add hypotheses
//!   h.discharge(&Formula)       Γ∪{φ} ⊢ ψ  ⟹  Γ ⊢ φ → ψ
//!   h.close(&[Formula])         ⊢ conj(order) → ψ, in the caller's nesting
//!
//! ── propositional (`hyp/prop.rs`) — every binary operation union-merges ──────
//!   a.mp(&b)                    Γ ⊢ φ→ψ,  Δ ⊢ φ      ⟹ Γ∪Δ ⊢ ψ
//!   a.syl(&b)                   Γ ⊢ φ→ψ,  Δ ⊢ ψ→χ    ⟹ Γ∪Δ ⊢ φ→χ
//!   a.and_intro(&b)             Γ ⊢ φ,    Δ ⊢ ψ      ⟹ Γ∪Δ ⊢ φ∧ψ
//!   a.or_elim(&l, &r)           Γ ⊢ φ∨ψ, Δ ⊢ φ→χ, Ε ⊢ ψ→χ ⟹ Γ∪Δ∪Ε ⊢ χ
//!   a.iff_intro(&b)             Γ ⊢ φ→ψ,  Δ ⊢ ψ→φ    ⟹ Γ∪Δ ⊢ φ↔ψ
//!   a.and_left() / a.and_right()          Γ ⊢ φ∧ψ ⟹ Γ ⊢ φ / Γ ⊢ ψ
//!   a.iff_mp() / a.iff_mpr()              Γ ⊢ φ↔ψ ⟹ Γ ⊢ φ→ψ / Γ ⊢ ψ→φ
//!   a.rule(&Thm)                Γ ⊢ φ,  ⊢ φ→ψ        ⟹ Γ ⊢ ψ
//!   a.contrapos() / a.not_elim() / a.absurd(&Formula)
//!
//! ── quantifiers (`hyp/quant.rs`) ─────────────────────────────────────────────
//!   a.gen(x)                    Γ ⊢ φ ⟹ Γ ⊢ ∀x.φ,  provided x ∉ FV(Γ)
//!   a.inst(t) / a.inst_all(&[t])          Γ ⊢ ∀x.φ ⟹ Γ ⊢ φ[t/x]
//!   a.exists_intro(v, φ, t)     Γ ⊢ φ[t/v] ⟹ Γ ⊢ ∃v.φ
//!   Hyp::obtain(v, &ex, &body)  Δ ⊢ ∃v.E,  Γ∪{E} ⊢ ψ ⟹ Γ∪Δ ⊢ ψ,  v fresh
//!
//! ── equality (`hyp/eq.rs`) ───────────────────────────────────────────────────
//!   Hyp::eq_refl(t)             {} ⊢ t = t
//!   a.symm(env)                 Γ ⊢ a=b ⟹ Γ ⊢ b=a
//!   a.trans(env, &b)            Γ ⊢ a=b, Δ ⊢ b=c ⟹ Γ∪Δ ⊢ a=c
//!   a.leibniz(w, &φ)            Γ ⊢ a=b ⟹ Γ ⊢ φ[a/w] → φ[b/w]
//!   a.subst(w, &φ, &b)          Γ ⊢ a=b, Δ ⊢ φ[a/w] ⟹ Γ∪Δ ⊢ φ[b/w]
//!   a.congr_arg(env, f, args, i)          Γ ⊢ a=b ⟹ Γ ⊢ f(..a..) = f(..b..)
//! ```
//!
//! `conj` is right-nested with no `⊤` padding: `[]` is `⊤`, `[φ]` is `φ`, and
//! `[φ,ψ,χ]` is `φ ∧ (ψ ∧ χ)`. See [`order`].
//!
//! # The invariant, and how each operation preserves it
//!
//! > **A `Hyp` is a pair `(Γ, t)` with `Γ` a canonically ordered duplicate-free
//! > list of formulas and `t` a theorem whose conclusion is *syntactically*
//! > `conj(Γ) → φ`.**
//!
//! It is checked, not assumed: [`Hyp::wrap`] is the only constructor, it takes
//! `Γ` and the theorem, and it returns `None` unless the theorem's conclusion is
//! an implication whose antecedent is exactly `conj(Γ)`. Every operation below
//! ends in a `wrap`, so an operation that miscomputes its hypothesis set yields
//! `None` rather than a `Hyp` that lies about what it assumed.
//!
//! * **`assume(φ)`** — `Γ = {φ}`, `t = ⊢ φ → φ`; `conj([φ])` is `φ`.
//! * **`lift(⊢ φ)`** — `Γ = {}`, `t = ⊢ ⊤ → φ` by weakening; `conj([])` is `⊤`.
//! * **Every binary operation** computes `Γ ∪ Δ`, *re-proves both premises
//!   against it* with [`Hyp::retarget`], and applies the corresponding fixed-`H`
//!   rule from `lib.rs`. `retarget` goes through `order::implies_conj`, which
//!   returns `None` unless the old set is contained in the new one, so the
//!   re-proof cannot silently drop a hypothesis.
//! * **`discharge(φ)`** — removes `φ` from `Γ`, builds
//!   `⊢ (conj(Γ∖φ) ∧ φ) → conj(Γ)` from the projections, chains it onto `t`, and
//!   [`crate::uncurry`]s. The conclusion becomes `φ → ψ`, so what leaves the
//!   hypothesis set reappears in the formula: the pair `(Γ, φ)` denotes the same
//!   assertion throughout.
//! * **`gen(x)`** — rejects unless `x` is free in no member of `Γ`, then uses
//!   `ax_dist` at `conj(Γ)`. This is the one operation whose side condition is
//!   *about* the hypothesis set, and it is the reason the set is carried.
//! * **`obtain(v, ex, body)`** — `discharge`s `E`, merges, and eliminates the
//!   existential; `v` must be free in neither the resulting hypothesis set nor
//!   the conclusion, which is checked directly and again inside
//!   [`crate::exists_elim_imp`].
//!
//! # Untrusted, and what that buys
//!
//! Nothing here is trusted. A `Hyp` reaches a [`Thm`] only through the kernel's
//! primitive rules and this crate's existing derived ones, so the worst a bug
//! can do is build a theorem that is true but not the one wanted, or — far more
//! likely, since almost every step is guarded — return `None`. In particular the
//! invariant is not a soundness property: a `Hyp` whose `hyps` field disagreed
//! with its theorem's antecedent would still hold a genuine theorem, it would
//! just be labelled wrongly. It is enforced anyway, because a mislabelled `Hyp`
//! is how a *caller* would go wrong.
//!
//! # Relationship to `hyp_mp` and friends in `lib.rs`
//!
//! This is their generalisation from one fixed hypothesis to a set.
//! [`crate::hyp_mp`], [`crate::hyp_and`], [`crate::hyp_syl`] and the rest all
//! require their premises to carry the *same* antecedent `H`, which is why the
//! hand-written derivations in this crate pick one conjunction `H` at the start
//! of an argument and re-project out of it at every step. This layer keeps the
//! set instead and rebuilds the conjunction on demand, so two derivations made
//! under different assumptions can simply be combined. The `lib.rs` functions
//! are unchanged and are what this layer calls; nothing here replaces them.

use kernel::{Formula, Thm};

pub mod eq;
pub mod order;
pub mod prop;
pub mod quant;

pub use order::{conj, forget, memo_enabled, truth};

/// A theorem together with the set of hypotheses it was proved under.
///
/// The invariant — `thm` concludes `conj(hyps) → concl` — is stated in full in
/// the module documentation, along with the argument that each operation
/// preserves it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hyp {
    /// Canonically ordered (see [`order::rank`]) and duplicate-free.
    hyps: Vec<Formula>,
    /// The conclusion `φ`. Redundant — it is `thm`'s consequent — and stored so
    /// that reading it is not a formula decomposition at every call site.
    concl: Formula,
    /// `⊢ conj(hyps) → concl`.
    thm: Thm,
}

impl Hyp {
    /// The only constructor: pair a hypothesis list with a theorem, checking the
    /// invariant.
    ///
    /// `hyps` is canonicalised here, so a caller may hand over any order and any
    /// duplicates — but the theorem must already have `conj` of the
    /// *canonicalised* list as its antecedent, which in practice means it came
    /// out of one of the operations below. Returns `None` otherwise.
    pub fn wrap(hyps: Vec<Formula>, thm: Thm) -> Option<Hyp> {
        let hyps = order::canonicalise(hyps);
        let (ante, concl) = thm.concl().as_imp()?;
        if ante != order::conj(&hyps) {
            return None
        }
        Some(Hyp { hyps, concl, thm })
    }

    /// `{φ} ⊢ φ`, the theorem being `⊢ φ → φ`.
    pub fn assume(phi: Formula) -> Hyp {
        let thm = crate::imp_refl(phi.clone());
        Hyp { hyps: vec![phi.clone()], concl: phi, thm }
    }

    /// `{} ⊢ φ`, from a theorem `⊢ φ`, the wrapped theorem being `⊢ ⊤ → φ`.
    pub fn lift(t: &Thm) -> Hyp {
        Hyp { hyps: Vec::new(), concl: t.concl().clone(), thm: crate::a1i(t, order::truth()) }
    }

    /// The hypothesis set, in canonical order.
    pub fn hyps(&self) -> &[Formula] { &self.hyps }

    /// The conclusion `φ`.
    pub fn concl(&self) -> &Formula { &self.concl }

    /// The wrapped theorem, `⊢ conj(hyps) → φ`.
    ///
    /// This is the escape hatch into the rest of the crate: a `Hyp` with a
    /// single hypothesis has exactly the shape [`crate::hyp_mp`] and friends
    /// consume, so existing code can be fed from here without change.
    pub fn thm(&self) -> &Thm { &self.thm }

    /// Whether anything is assumed.
    pub fn is_closed(&self) -> bool { self.hyps.is_empty() }

    /// `⊢ φ`, discharging the vacuous `⊤` antecedent. `None` if anything is
    /// still assumed.
    pub fn into_thm(self) -> Option<Thm> {
        if !self.hyps.is_empty() {
            return None
        }
        Thm::mp(&self.thm, &order::truth_thm())
    }

    /// `⊢ conj(hyps) → φ` with `hyps` re-proved against `target`.
    ///
    /// Free when the sets already agree, which is the common case inside a
    /// single argument and is why merging costs nothing when nothing changes.
    fn retarget(&self, target: &[Formula]) -> Option<Thm> {
        if self.hyps == target {
            return Some(self.thm.clone())
        }
        crate::syl(&order::implies_conj(target, &self.hyps)?, &self.thm)
    }

    /// Both premises re-proved against the union of their hypothesis sets.
    ///
    /// **This is the core of the layer.** Every binary operation starts here:
    /// it is what a natural-deduction system gets for free from `Γ ⊢ φ`, and
    /// what the hand-written derivations in this crate do by choosing one
    /// conjunction up front and projecting out of it by hand.
    pub(crate) fn merge(a: &Hyp, b: &Hyp) -> Option<(Vec<Formula>, Thm, Thm)> {
        let hs = order::union(&a.hyps, &b.hyps);
        Some((hs.clone(), a.retarget(&hs)?, b.retarget(&hs)?))
    }

    /// The same, for three premises — the case analysis rule needs it.
    pub(crate) fn merge3(a: &Hyp, b: &Hyp, c: &Hyp) -> Option<(Vec<Formula>, Thm, Thm, Thm)> {
        let hs = order::union(&order::union(&a.hyps, &b.hyps), &c.hyps);
        Some((hs.clone(), a.retarget(&hs)?, b.retarget(&hs)?, c.retarget(&hs)?))
    }

    /// Add hypotheses. The conclusion is unchanged.
    ///
    /// Rarely needed directly — the binary operations weaken their own operands
    /// — but it is what makes "prove the lemma under fewer assumptions" a
    /// non-event rather than a reason to restate it.
    pub fn weaken(&self, extra: &[Formula]) -> Option<Hyp> {
        let hs = order::union(&self.hyps, &order::canonicalise(extra.to_vec()));
        let thm = self.retarget(&hs)?;
        Hyp::wrap(hs, thm)
    }

    /// `Γ ∪ {φ} ⊢ ψ  ⟹  Γ ⊢ φ → ψ` — the deduction step this kernel has no
    /// meta-rule for.
    ///
    /// Returns `None` if `φ` is not among the hypotheses. Note the conclusion
    /// grows an implication as the hypothesis set shrinks, which is the sense in
    /// which nothing is lost: `(Γ ∪ {φ}, ψ)` and `(Γ, φ → ψ)` denote the same
    /// assertion.
    pub fn discharge(&self, phi: &Formula) -> Option<Hyp> {
        if !self.hyps.iter().any(|h| h == phi) {
            return None
        }
        let rest: Vec<Formula> = self.hyps.iter().filter(|h| *h != phi).cloned().collect();
        // Work under `conj(rest) ∧ φ`, whose two projections regenerate every
        // hypothesis of `self`, hence `conj(self.hyps)`; then uncurry.
        let bridge = order::discharge_bridge(&self.hyps, phi)?;
        let both = crate::syl(&bridge, &self.thm)?;
        Hyp::wrap(rest, crate::uncurry(&both)?)
    }

    /// `⊢ conj(order) → ψ`, with the conjunction nested the way the caller asks.
    ///
    /// The boundary operation. Inside the layer the hypothesis order is
    /// [`order::rank`]'s and callers should not care; at the point where a
    /// derivation becomes a theorem for the rest of the crate, the exact shape
    /// of the antecedent matters, and this is where it is chosen. `order` must
    /// contain every hypothesis (it may contain more, which weakens).
    ///
    /// The result is `⊢ conj(order) → ψ` uniformly, so `close(&[])` gives
    /// `⊢ ⊤ → ψ`; use [`Hyp::into_thm`] for the bare `⊢ ψ`.
    pub fn close(&self, order: &[Formula]) -> Option<Thm> {
        if self.hyps == order {
            return Some(self.thm.clone())
        }
        crate::syl(&order::implies_conj(order, &self.hyps)?, &self.thm)
    }

    /// Rebuild with a new conclusion under the same hypotheses, checking the
    /// invariant. Every unary operation goes through this.
    pub(crate) fn same_hyps(&self, thm: Thm) -> Option<Hyp> {
        let (ante, concl) = thm.concl().as_imp()?;
        if ante != order::conj(&self.hyps) {
            return None
        }
        Some(Hyp { hyps: self.hyps.clone(), concl, thm })
    }
}
