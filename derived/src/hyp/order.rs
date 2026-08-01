//! **SUPERSEDED.** Part of the above-kernel deduction layer; see the
//! "SUPERSEDED" section of `derived/src/hyp.rs` for why hypotheses went into
//! the kernel's judgement instead. This file is where the cost that decided it
//! lives: [`implies_conj`] and [`project`] are the merge machinery, and they are
//! `O(|Γ ∪ Δ|²)` per binary operation rather than the `O(1)` a kernel-side
//! hypothesis set gives. Kept as the experiment.
//!
//! The canonical order on hypothesis sets, the conjunction they denote, and the
//! projections out of it.
//!
//! # Interface
//!
//! ```text
//! truth()                       ⊤, spelled ⊥ → ⊥
//! conj(&[φ₀..φₙ])               ⊤ | φ₀ | φ₀ ∧ (φ₁ ∧ (… φₙ))   — right-nested
//! canonicalise(Vec<Formula>)    sorted by `rank`, duplicate-free
//! union(&[..], &[..])           the canonical union of two canonical sets
//! project(hs, i)                ⊢ conj(hs) → hs[i]
//! implies_conj(from, to)        ⊢ conj(from) → conj(to),  for to ⊆ from
//! memo_enabled(bool) / forget() the memo controls
//! ```
//!
//! # Why an order is needed at all, and why it is this one
//!
//! [`crate::hyp::Hyp`] carries a *set* of hypotheses but a single [`Thm`], and
//! that theorem's antecedent has to be one definite formula. So the set must
//! have a canonical listing: two `Hyp`s whose hypothesis sets are equal must
//! build the *same* conjunction, or nothing composes.
//!
//! The obvious order — structural, lexicographic on the syntax tree — is **not
//! available outside the kernel**. `Formula` exposes `as_eq`, `as_mem` and
//! `as_imp`, but `Forall`'s body is `pub(crate)`, and `Term` cannot be taken
//! apart at all, so a derived crate cannot walk a formula to the leaves. What it
//! *can* see is the cached 64-bit structural hash (via `Hash`, which writes
//! exactly that hash) and `==`.
//!
//! So the order is: **by structural hash, ties broken by order of first
//! registration**. [`rank`] keeps a per-hash bucket of the distinct formulas it
//! has seen, so two colliding-but-distinct formulas get a fixed relative order
//! for the lifetime of the thread. That makes `rank` a genuine total order —
//! antisymmetric, transitive, and a function of the formulas alone once both
//! have been seen — rather than a preorder that would silently reorder equal
//! sets under a collision.
//!
//! Had it been left as a bare hash comparison, a collision would not have been
//! unsound — it would produce a conjunction in an unexpected order, and every
//! later merge against it would return `None`. That is the failure mode of
//! everything in this file: reading formulas apart and comparing them builds no
//! [`Thm`], so a bug here rejects, it never concludes.
//!
//! # Memoisation
//!
//! [`project`] and [`implies_conj`] are called repeatedly with the *same*
//! arguments — every merge into a given hypothesis set rebuilds the same
//! projections — so both are memoised per thread. This is what the hand-written
//! `⊢ H → φ` style gets by binding `h_univ` once and reusing it; without it the
//! layer pays for the projections again at every step.
//!
//! The memo stores only theorems this module itself derived, and a `Thm` does
//! not depend on an `Env` (`kernel::thm`, "What a `Thm` asserts"), so sharing
//! one across environments is sound. Note the narrow reading: `Env`-independence
//! is the property being used, *not* "a `Thm` is valid absolutely" — that
//! stronger phrasing, which this sentence used, stopped being true when `Thm`
//! became a sequent. It happens not to matter here, because every `Thm` this
//! layer builds carries its assumptions inside the formula as an antecedent and
//! so is hypothesis-free at the kernel level; a store that could hold a
//! hypothetical `Thm` would need the guard `certify::hypothesis_free` applies. It costs memory
//! proportional to the number of distinct hypothesis sets seen; [`forget`]
//! clears it and [`memo_enabled`] turns it off, which is how the kernel-call
//! measurement in `derived/tests/hyp_rederivation.rs` reports both figures.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use kernel::{Formula, Thm};

use crate::{a1i, and_left, and_right, hyp_and, imp_refl, syl};

/// `⊤`, spelled `⊥ → ⊥`.
///
/// The antecedent of a [`crate::hyp::Hyp`] with no hypotheses. Every operation
/// is then uniform in the number of hypotheses, including zero — which is the
/// whole reason a hypothesis-free `Hyp` still carries an implication rather than
/// a bare theorem.
pub fn truth() -> Formula { Formula::not(Formula::false_()) }

/// `⊢ ⊤`.
pub fn truth_thm() -> Thm { imp_refl(Formula::false_()) }

/// The conjunction of a hypothesis list, right-nested and with no `⊤` padding.
///
/// `[]` is `⊤`, `[φ]` is `φ`, and `[φ,ψ,χ]` is `φ ∧ (ψ ∧ χ)` — the shape the
/// hand-written derivations in this crate already use, so a `Hyp` closed with
/// [`crate::hyp::Hyp::close`] lands on a formula existing callers recognise.
pub fn conj(hs: &[Formula]) -> Formula {
    match hs {
        [] => truth(),
        [h] => h.clone(),
        [h, rest @ ..] => Formula::and(h.clone(), conj(rest)),
    }
}

thread_local! {
    /// Distinct formulas seen per structural hash, in first-registration order.
    /// Almost always one entry per bucket; see the module docs.
    static BUCKETS: RefCell<HashMap<u64, Vec<Formula>>> = RefCell::new(HashMap::new());

    /// `(conj(hs), hs.len(), i) ↦ ⊢ conj(hs) → hs[i]`.
    ///
    /// The length is part of the key because `conj` alone does not determine the
    /// split: `[a ∧ b]` and `[a, b]` have the same conjunction and different
    /// projections. With the length, peeling `len - 1` conjunctions recovers the
    /// list, so the key is faithful.
    static PROJECTIONS: RefCell<HashMap<(Formula, usize, usize), Thm>> = RefCell::new(HashMap::new());

    /// `(conj(from), from.len(), conj(to), to.len()) ↦ ⊢ conj(from) → conj(to)`.
    static BRIDGES: RefCell<HashMap<(Formula, usize, Formula, usize), Thm>> = RefCell::new(HashMap::new());

    /// `(conj(hs), hs.len(), φ) ↦ ⊢ (conj(hs∖φ) ∧ φ) → conj(hs)`.
    static DISCHARGES: RefCell<HashMap<(Formula, usize, Formula), Thm>> = RefCell::new(HashMap::new());

    /// Whether the two memos above are consulted and filled.
    static MEMO: RefCell<bool> = const { RefCell::new(true) };
}

/// Turn memoisation on or off for this thread, returning the previous setting.
///
/// Off is not a correctness question — it changes only how many kernel calls a
/// derivation makes — and exists so the comparison in
/// `derived/tests/hyp_rederivation.rs` can report the layer's cost with and
/// without it.
pub fn memo_enabled(on: bool) -> bool {
    MEMO.with(|m| {
        let was = *m.borrow();
        *m.borrow_mut() = on;
        was
    })
}

/// Drop every memoised theorem and every registered tie-break.
///
/// Clearing the tie-break registry changes the canonical order only if two
/// distinct formulas share a hash, so in practice this is pure memory
/// reclamation. Do not call it while `Hyp`s built before the call are still in
/// use unless that is acceptable.
pub fn forget() {
    BUCKETS.with(|b| b.borrow_mut().clear());
    PROJECTIONS.with(|p| p.borrow_mut().clear());
    BRIDGES.with(|b| b.borrow_mut().clear());
    DISCHARGES.with(|d| d.borrow_mut().clear());
}

/// The kernel's cached structural hash, extracted through `Hash`.
///
/// `Formula::hash` writes exactly one `u64` — the cached hash — and
/// `DefaultHasher` is seeded deterministically, so this is a pure function of
/// the formula's structure.
fn digest(f: &Formula) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    f.hash(&mut h);
    h.finish()
}

/// The sort key: structural hash, then order of first registration among
/// formulas sharing that hash. A total order; see the module docs.
pub fn rank(f: &Formula) -> (u64, usize) {
    let d = digest(f);
    let tie = BUCKETS.with(|b| {
        let mut b = b.borrow_mut();
        let bucket = b.entry(d).or_default();
        match bucket.iter().position(|g| g == f) {
            Some(i) => i,
            None => {
                bucket.push(f.clone());
                bucket.len() - 1
            }
        }
    });
    (d, tie)
}

/// Sort into canonical order and drop duplicates.
pub fn canonicalise(mut hs: Vec<Formula>) -> Vec<Formula> {
    hs.sort_by_key(rank);
    hs.dedup();
    hs
}

/// The canonical union of two canonical sets.
pub fn union(a: &[Formula], b: &[Formula]) -> Vec<Formula> {
    if a == b {
        return a.to_vec()
    }
    let mut out = a.to_vec();
    out.extend_from_slice(b);
    canonicalise(out)
}

/// `⊢ conj(hs) → hs[i]` — the `i`th projection.
///
/// Built as `i` applications of [`crate::and_right`] to strip the leading
/// conjuncts, followed by [`crate::and_left`] to take the head — except at the
/// last position, where the tail *is* the conjunct and the step is reflexivity.
pub fn project(hs: &[Formula], i: usize) -> Option<Thm> {
    if i >= hs.len() {
        return None
    }
    let key = (conj(hs), hs.len(), i);
    if let Some(t) = memo_get(&PROJECTIONS, &key) {
        return Some(t)
    }
    let out = project_uncached(hs, i)?;
    memo_put(&PROJECTIONS, key, out.clone());
    Some(out)
}

fn project_uncached(hs: &[Formula], i: usize) -> Option<Thm> {
    let n = hs.len();
    // `acc` proves `⊢ conj(hs) → conj(hs[j..])`; `None` means `j == 0`, where
    // that implication is reflexivity and is not worth building.
    let mut acc: Option<Thm> = None;
    for j in 0..i {
        let step = and_right(hs[j].clone(), conj(&hs[j + 1..]));
        acc = Some(match acc {
            None => step,
            Some(a) => syl(&a, &step)?,
        });
    }
    if i + 1 == n {
        // The tail is the conjunct itself; there is nothing left to take apart.
        return Some(match acc {
            None => imp_refl(hs[i].clone()),
            Some(a) => a,
        })
    }
    let head = and_left(hs[i].clone(), conj(&hs[i + 1..]));
    Some(match acc {
        None => head,
        Some(a) => syl(&a, &head)?,
    })
}

/// `⊢ conj(from) → conj(to)` — the weakening bridge.
///
/// Returns `None` unless every formula of `to` occurs in `from`, which is
/// exactly the condition under which the implication is derivable this way.
/// `to` may be shorter, longer, or in a different order than `from`; the only
/// requirement is containment, so this doubles as the reordering step
/// [`crate::hyp::Hyp::close`] uses to land on a caller-chosen nesting.
pub fn implies_conj(from: &[Formula], to: &[Formula]) -> Option<Thm> {
    let src = conj(from);
    let key = (src.clone(), from.len(), conj(to), to.len());
    if let Some(t) = memo_get(&BRIDGES, &key) {
        return Some(t)
    }
    let out = implies_conj_uncached(from, to, &src)?;
    memo_put(&BRIDGES, key, out.clone());
    Some(out)
}

fn implies_conj_uncached(from: &[Formula], to: &[Formula], src: &Formula) -> Option<Thm> {
    if to.is_empty() {
        // `⊢ conj(from) → ⊤`, i.e. weakening a proof of `⊤`.
        return Some(a1i(&truth_thm(), src.clone()))
    }
    let mut parts = Vec::with_capacity(to.len());
    for t in to {
        let i = from.iter().position(|f| f == t)?;
        parts.push(project(from, i)?);
    }
    // `conj` is right-nested, so fold from the right.
    let mut acc = parts.pop()?;
    while let Some(p) = parts.pop() {
        acc = hyp_and(&p, &acc)?;
    }
    Some(acc)
}

/// `⊢ (conj(hs ∖ φ) ∧ φ) → conj(hs)` — the bridge [`crate::hyp::Hyp::discharge`]
/// needs to move one hypothesis out of the antecedent and into the conclusion.
///
/// Lives here rather than at the call site so that all conjunction plumbing —
/// and so all of the layer's bookkeeping cost — is in one place and memoised by
/// the same switch.
pub fn discharge_bridge(hs: &[Formula], phi: &Formula) -> Option<Thm> {
    if !hs.iter().any(|h| h == phi) {
        return None
    }
    let key = (conj(hs), hs.len(), phi.clone());
    if let Some(t) = memo_get(&DISCHARGES, &key) {
        return Some(t)
    }
    let rest: Vec<Formula> = hs.iter().filter(|h| *h != phi).cloned().collect();
    let pair = vec![conj(&rest), phi.clone()];
    let mut parts = Vec::with_capacity(hs.len());
    for h in hs {
        parts.push(if h == phi {
            project(&pair, 1)?
        } else {
            let i = rest.iter().position(|g| g == h)?;
            syl(&project(&pair, 0)?, &project(&rest, i)?)?
        });
    }
    let mut out = parts.pop()?;
    while let Some(p) = parts.pop() {
        out = hyp_and(&p, &out)?;
    }
    memo_put(&DISCHARGES, key, out.clone());
    Some(out)
}

fn memo_get<K: Eq + Hash>(cell: &'static std::thread::LocalKey<RefCell<HashMap<K, Thm>>>, key: &K) -> Option<Thm> {
    if !MEMO.with(|m| *m.borrow()) {
        return None
    }
    cell.with(|c| c.borrow().get(key).cloned())
}

fn memo_put<K: Eq + Hash>(cell: &'static std::thread::LocalKey<RefCell<HashMap<K, Thm>>>, key: K, t: Thm) {
    if !MEMO.with(|m| *m.borrow()) {
        return
    }
    cell.with(|c| {
        c.borrow_mut().insert(key, t);
    });
}
