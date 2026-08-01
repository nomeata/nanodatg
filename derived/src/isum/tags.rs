//! **The iterated (right-nested) binary sum** `A₀ + (A₁ + (… + (A_{n-1} + 0)))`,
//! its `n` injections, and what distinguishes them.
//!
//! # What the thesis asks for
//!
//! §5.2's `spec` judgment builds the tag set of an inductive by recursion on
//! the *constructor list*:
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ 0 spec ⇒ 0; rec0; rec0
//! Γ; t : F ⊢ (c : β) + K spec ⇒ A₁ + A;  rec₊ (λp.B₁) B;  rec₊ (λpg(x::α).G₁) G
//! ```
//!
//! so `n` constructors with tag types `β₀ … β_{n-1}` give the **right-nested**
//! sum `β₀ + (β₁ + (… + (β_{n-1} + 0)))`, terminating in `0` — one `+` per
//! constructor, with no summand for the empty tail. That is what [`isum_of`]
//! builds, and the terminating `0` is not decoration: it is what makes the
//! `i`-th injection
//!
//! ```text
//! inj_i(a) = inr^i(inl(a))
//! ```
//!
//! **uniform in `i`**, for every `i < n` and every `n`. A translation that
//! collapsed the last `+ 0` — as `derived/src/enums.rs`, `wnat.rs` and
//! `wlist.rs` all do by hand, writing `Bool`'s tag set as `1 + 1` rather than
//! `1 + (1 + 0)` — has to special-case the last constructor, whose injection
//! becomes `inr^{n-1}` with no `inl`. Every lemma below would then need two
//! forms. Keeping the `0` costs one extra `+` in the term and buys a single
//! uniform statement, so this file keeps it.
//!
//! Note the degenerate arities come out right for free: `n = 0` gives the tag
//! set `0` (Lean's `Empty`, no injections) and `n = 1` gives `β₀ + 0` (a
//! single-constructor structure), neither of which is a special case here.
//!
//! # Finite-ordinal fibres are not a separate construction
//!
//! Taking every `βᵢ = 1` gives `1 + (1 + (… + 0))`, a set with exactly `m`
//! elements `inj_0(•) … inj_{m-1}(•)`. That is [`finord`], and it is the
//! *same* construction, not a new one — which is why the recursive-argument
//! rule of §5.2 (`:1800`), whose fibre gains a `Σ(z::γ) + B` per recursive
//! argument and hence a `1 + B` when `γ` is empty, needs nothing built for it.
//! [`crate::fibre`] uses it.
//!
//! # This file is the *construction*; callers want [`super::symbols`]
//!
//! Everything here is a meta-level term former, so the whole nest is inlined at
//! every mention — `O(n)` for the tag set and `O(i)` for the `i`-th injection.
//! [`super::symbols`] names both with real symbols, `Sum_n(A⃗)` and `Inj_i(a)`,
//! cached per arity and per depth, and re-exports every property below over
//! them. **Downstream code should state nothing over the nest.** This file
//! stays public because `symbols` is derived from it and because unfolding a
//! failed proof by hand ends up here.
//!
//! One thing the split makes sharper. The argument below for the trailing
//! `+ 0` — that it makes `inj_i = inr^i ∘ inl` uniform — has a second payoff
//! once the injections are symbols: `inj_i` mentions neither `n` nor any `Aⱼ`,
//! so **one symbol per depth serves every arity**, and the cache is linear
//! rather than quadratic. Collapsing the last `+ 0` would make the last
//! injection depend on `n`.
//!
//! # Interface
//!
//! Terms — [`isum_of`], [`inj_of`], [`finord`]. Theorems, with `Σ⁺` written for
//! `A₀ + (A₁ + (… + (A_{n-1} + 0)))`:
//!
//! ```text
//! ⊢ ∀A₀ … ∀A_{n-1} ∀a. (a ∈ Aᵢ → inj_i(a) ∈ Σ⁺)          [ISum::inj_mem[i]]
//! ⊢ ∀a ∀b. (inj_i(a) = inj_i(b) → a = b)                  [ISum::inj_inj[i]]
//! ⊢ ∀a ∀b. ¬(inj_i(a) = inj_j(b))            for i ≠ j    [inj_distinct]
//! ```
//!
//! [`ISum::new`] derives the first two for every `i < n` in one call;
//! [`inj_distinct`] is derived on demand because it depends on the *pair*
//! `(i,j)` and not on `n` at all. [`inj_mem_at`] is the same membership at
//! caller-supplied summand *terms* and a caller-supplied element, which is what
//! [`super::dispatch`] needs and what [`ISum::new`] generalises.
//!
//! # Non-vacuity
//!
//! `n` memberships in one set say nothing if that set could be a singleton.
//! [`inj_distinct`] is what stops that: the `n` injections have pairwise
//! disjoint ranges, so `Σ⁺` sees each summand separately, and together with
//! [`ISum::inj_inj`] the map `(i,a) ↦ inj_i(a)` is injective. `tests/isum.rs`
//! cashes this at `finord(3)`, whose three elements are pairwise provably
//! distinct with no hypothesis left.
//!
//! # Nothing here is an axiom
//!
//! Everything is [`crate::sums`]' binary sum iterated at the meta level: the
//! term is a nest of the existing `sum` symbol and every derivation is a chain
//! of the existing [`Sums::inl_mem`](crate::sums::Sums::inl_mem),
//! [`inr_mem`](crate::sums::Sums::inr_mem),
//! [`inl_inj`](crate::sums::Sums::inl_inj),
//! [`inr_inj`](crate::sums::Sums::inr_inj) and
//! [`disjoint`](crate::sums::Sums::disjoint). No new symbol is introduced.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::sums::Sums;
use crate::{eq_symm_imp, gen_all, imp_refl, inst_all, syl};

/// The term `A₀ + (A₁ + (… + (A_{n-1} + 0)))`; `isum_of(s, &[])` is `0`.
pub fn isum_of(s: &Sums, summands: &[Term]) -> Term {
    summands
        .iter()
        .rev()
        .fold(s.zero(), |acc, a| s.sum_of(a.clone(), acc))
}

/// The term `inj_i(a) = inr^i(inl(a))` — the `i`-th injection into an iterated
/// sum with at least `i + 1` summands.
pub fn inj_of(s: &Sums, i: usize, a: Term) -> Term {
    (0..i).fold(s.inl(a), |t, _| s.inr(t))
}

/// The finite ordinal `m = 1 + (1 + (… + 0))`, with `m` copies of `1`.
///
/// `finord(s, 0)` is `0` and `finord(s, m)` has exactly the `m` elements
/// `inj_0(•) … inj_{m-1}(•)`. This is the fibre a constructor with `m`
/// recursive arguments gets in §5.2 (`thesis.txt:1800`), where each recursive
/// argument contributes a `Σ(z::γ) + B` and `γ` is empty for a plain one.
pub fn finord(s: &Sums, m: usize) -> Term {
    isum_of(s, &vec![s.unit(); m])
}

/// `⊢ a ∈ Aᵢ → inj_i(a) ∈ A₀ + (… + (A_{n-1} + 0))`, at caller-supplied terms.
///
/// One [`Sums::inl_mem`](crate::sums::Sums::inl_mem) followed by `i` uses of
/// [`Sums::inr_mem`](crate::sums::Sums::inr_mem), each climbing one summand
/// outwards. Returns `None` if `i` is out of range.
pub fn inj_mem_at(s: &Sums, summands: &[Term], i: usize, a: &Term) -> Option<Thm> {
    if i >= summands.len() {
        return None
    }
    let tail = |k: usize| isum_of(s, &summands[k..]);
    let mut th = inst_all(&s.inl_mem, &[summands[i].clone(), tail(i + 1), a.clone()])?;
    let mut cur = s.inl(a.clone());
    for k in (0..i).rev() {
        let step = inst_all(&s.inr_mem, &[summands[k].clone(), tail(k + 1), cur.clone()])?;
        th = syl(&th, &step)?;
        cur = s.inr(cur);
    }
    debug_assert_eq!(
        *th.concl(),
        Formula::imp(
            Formula::mem(a.clone(), summands[i].clone()),
            Formula::mem(inj_of(s, i, a.clone()), tail(0)),
        ),
        "isum: inj_mem_at has the wrong shape"
    );
    Some(th)
}

/// `⊢ ∀a ∀b. (inj_i(a) = inj_i(b) → a = b)` — each injection is injective.
///
/// `i` uses of [`Sums::inr_inj`](crate::sums::Sums::inr_inj) strip the tags one
/// at a time; [`Sums::inl_inj`](crate::sums::Sums::inl_inj) strips the last.
/// The statement does not mention the summands, so it holds for every `n > i`
/// at once.
pub fn inj_injective(env: &mut Env, s: &Sums, i: usize) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let mut th = imp_refl(Formula::eq(
        inj_of(s, i, ta.clone()),
        inj_of(s, i, tb.clone()),
    ));
    for k in (0..i).rev() {
        let step = inst_all(&s.inr_inj, &[inj_of(s, k, ta.clone()), inj_of(s, k, tb.clone())])?;
        th = syl(&th, &step)?;
    }
    th = syl(&th, &inst_all(&s.inl_inj, &[ta.clone(), tb.clone()])?)?;
    Some(gen_all(&[av, bv], &th))
}

/// `⊢ ∀a ∀b. ¬(inj_i(a) = inj_j(b))`, for `i ≠ j` — **the injections have
/// pairwise disjoint ranges**.
///
/// For `i < j`: `i` uses of [`Sums::inr_inj`](crate::sums::Sums::inr_inj) strip
/// the common `inr` prefix, leaving `inl(a) = inr(w)` with
/// `w = inr^{j-i-1}(inl(b))` — which [`Sums::disjoint`](crate::sums::Sums::disjoint)
/// refutes, because the two *tags* `∅` and `1` are different sets. For `i > j`
/// the same theorem is derived at `(j,i)` and flipped along symmetry of `=`.
///
/// Returns `None` when `i == j`, where the statement is false.
pub fn inj_distinct(env: &mut Env, s: &Sums, i: usize, j: usize) -> Option<Thm> {
    if i == j {
        return None
    }
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let (li, rj) = (inj_of(s, i, ta.clone()), inj_of(s, j, tb.clone()));

    let out = if i < j {
        let mut th = imp_refl(Formula::eq(li.clone(), rj.clone()));
        for t in 0..i {
            let u = inj_of(s, i - t - 1, ta.clone());
            let v = inj_of(s, j - t - 1, tb.clone());
            th = syl(&th, &inst_all(&s.inr_inj, &[u, v])?)?;
        }
        // `inl(a) = inr(w)` is now the consequent, and it is refutable.
        let w = inj_of(s, j - i - 1, tb.clone());
        syl(&th, &inst_all(&s.disjoint, &[ta.clone(), w])?)?
    } else {
        let flipped = inj_distinct(env, s, j, i)?;
        let at = inst_all(&flipped, &[tb.clone(), ta.clone()])?;
        syl(&eq_symm_imp(env, li.clone(), rj.clone()), &at)?
    };
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(li, rj)),
        "isum: inj_distinct has the wrong shape"
    );
    Some(gen_all(&[av, bv], &out))
}

/// The iterated sum at `n` universally quantified summands, with the two
/// families of theorems that depend on `n`.
///
/// [`ISum::new`] is the entry point; the fields are the theorems, stated at the
/// quantified variables [`ISum::vars`] so a caller instantiates them with
/// [`crate::inst_all`] at whatever summands its declaration has.
pub struct ISum {
    /// The number of summands.
    pub n: usize,
    /// The `n` quantified summand variables, outermost first.
    pub vars: Vec<FreeVar>,
    /// `A₀ + (A₁ + (… + (A_{n-1} + 0)))` at those variables.
    pub sum: Term,
    /// For each `i < n`: `⊢ ∀A₀ … ∀A_{n-1} ∀a. (a ∈ Aᵢ → inj_i(a) ∈ Σ⁺)`.
    pub inj_mem: Vec<Thm>,
    /// For each `i < n`: `⊢ ∀a ∀b. (inj_i(a) = inj_i(b) → a = b)`.
    pub inj_inj: Vec<Thm>,
}

impl ISum {
    /// Build the iterated sum at depth `n` and derive both families.
    pub fn new(env: &mut Env, s: &Sums, n: usize) -> Option<ISum> {
        let vars: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
        let terms: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
        let sum = isum_of(s, &terms);

        let av = env.fresh_var();
        let ta = Term::var(av);
        let mut quant = vars.clone();
        quant.push(av);

        let mut inj_mem = Vec::with_capacity(n);
        let mut inj_inj = Vec::with_capacity(n);
        for i in 0..n {
            inj_mem.push(gen_all(&quant, &inj_mem_at(s, &terms, i, &ta)?));
            inj_inj.push(inj_injective(env, s, i)?);
        }
        Some(ISum { n, vars, sum, inj_mem, inj_inj })
    }

    /// The term `A₀ + (… + (A_{n-1} + 0))` at caller-supplied summands.
    pub fn of(s: &Sums, summands: &[Term]) -> Term { isum_of(s, summands) }

    /// The term `inj_i(a)`.
    pub fn inj(s: &Sums, i: usize, a: Term) -> Term { inj_of(s, i, a) }
}
