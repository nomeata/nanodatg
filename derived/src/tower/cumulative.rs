//! **Cumulativity**: `Uₙ ⊆ U₍ₙ₊₁₎`, and the lift between any two levels,
//! exported as named theorems rather than recomposed at each use site.
//!
//! # Interface
//!
//! Writing `Uₙ` for [`Tower::level`], a [`Cumul`] built to `height` `h` exports,
//! for every `0 ≤ m ≤ n ≤ h`:
//!
//! ```text
//! ⊢ Uₙ ⊆ U₍ₙ₊₁₎, i.e. ∀x. (x ∈ Uₙ → x ∈ U₍ₙ₊₁₎)      n < h   [Cumul::step]
//! ⊢ Uₘ ⊆ Uₙ,     i.e. ∀x. (x ∈ Uₘ → x ∈ Uₙ)          m ≤ n   [Cumul::lift]
//! ⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)                                   n < h   [Cumul::strict]
//! ```
//!
//! and the three derived rules a caller normally wants,
//!
//! ```text
//! from ⊢ t ∈ Uₘ  infer  ⊢ t ∈ Uₙ                     m ≤ n   [Cumul::raise]
//! ⊢ ∀x. (γ → v ∈ Uₘ) → ∀x. (γ → v ∈ Uₙ)              m ≤ n   [Cumul::fibres_mono]
//! from ⊢ ∀x. (γ → v ∈ Uₘ)  infer  ⊢ ∀x. (γ → v ∈ Uₙ) m ≤ n   [Cumul::raise_fibres]
//! ```
//!
//! The formulas are literally [`kernel::thm::subset`], so a consumer that
//! matches subset formulas syntactically — which is every consumer here — sees
//! what it expects. Nothing below is needed by a caller.
//!
//! # Why it is nearly free, and what the content actually is
//!
//! One line per level: `U₍ₙ₋₁₎ ∈ Uₙ` ([`Level::mem_below`]) fed to
//! `C₁(Uₙ)` ([`Level::transitive`]) is `∀z. (z ∈ U₍ₙ₋₁₎ → z ∈ Uₙ)` on the nose.
//! Transitivity is the clause that was added to `ax_tarski` on 2026-07-31; before
//! that this file could not have existed, since `U(c)` was not transitive and
//! `Uₙ ⊆ U₍ₙ₊₁₎` was *refutable* along with `⋃`-closure and the rest — see the
//! countermodels at the end of [`crate::universe`].
//!
//! The **base case is not special**. One might expect `U₀ ⊆ U₁` to need its own
//! argument — `U₀ = {0,1}` is not a universe and level 1 is not `U(U₀)` — and
//! the direct route is indeed `0 ∈ U(ω)` from `∅`-closure plus `1 = {0,0}` from
//! [`crate::universe::least_universe_pairing`]. It is not needed:
//! [`Tower::at`] already defines level 1's `mem_below` as `U₀ ∈ U₁`
//! ([`Tower::u0_in`] at `ω`), so the very same two lines apply, and `0, 1 ∈ U₁`
//! come out as *instances* of the lift rather than as its ingredients. The test
//! `both_truth_values_lift_from_level_zero_to_level_one` checks exactly that.
//!
//! So the content here is the **export**, not the proof: a table of
//! `(m,n)`-indexed theorems, built once, so a consumer lifting a membership `i`
//! levels does one [`Thm::mp`] instead of re-running the chain. That matters
//! because the consumers lift *repeatedly*: see below.
//!
//! # Who wants this
//!
//! * **`Π` at `Sort max(u,v)`.** [`crate::ext::dprod_universe_n`]'s rule reads
//!   `(A ∈ U(c) ∧ ∀x ∈ A. b(q⃗,x) ∈ U(c)) → dprod(q⃗,A) ∈ U(c)` at **one**
//!   universe `c`, while Lean's rule types the base at `Sort u` and the fibres
//!   at `Sort v` and lands in `Sort max(u,v)`. Both memberships have to be
//!   raised to the max before the n-ary Π rule applies, and the fibre one has to
//!   be raised *under a `∀x`* — [`Cumul::fibres_mono`] is that shape.
//! * **`ulift`.** `⟦ulift α⟧ = ⟦α⟧` (thesis.txt:2106), so its typing clause is
//!   `Uₙ ⊆ U₍ₙ′₎` and nothing else (thesis.txt:2284). There is no other `ulift`
//!   work; this file is all of it.
//!
//! # Non-vacuity, in both directions
//!
//! A subset statement is worthless if the smaller set is empty and misleading if
//! the two are equal. Both are excluded here: `∅`, `U₀` and `ω` are members of
//! every `Uₙ` with `n ≥ 1` ([`Level::empty_mem`], [`Level::u0_mem`],
//! [`Level::omega_mem`]) and `0, 1` are members of `U₀`, so every inclusion is a
//! statement about an inhabited set; and [`Cumul::strict`] refutes the converse
//! inclusion outright, from `Uₙ ∈ U₍ₙ₊₁₎` and Regularity's `¬(x ∈ x)`. The tower
//! therefore does not collapse anywhere, not merely at the bottom, which is all
//! [`Tower::u0_ne_u1`] said.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use super::levels::Tower;
use crate::{inst_all, mpd_const, syl};

/// The cumulativity table for a tower, built up to a fixed height.
///
/// `Cumul::new(env, t, h)` proves `Uₙ ⊆ U₍ₙ₊₁₎` for every `n < h` and composes
/// them into `Uₘ ⊆ Uₙ` for every `m ≤ n ≤ h`. `h` is a *meta-level* bound, like
/// [`Tower::level`]'s argument and for the same reason: a closed Lean level
/// evaluates to a numeral before the interpretation runs, so the highest level a
/// file mentions is known, and nothing here needs a set-theoretic recursion.
///
/// The table is `O(h²)` theorems and `h` is a small numeral in practice, so it
/// is built eagerly; [`Cumul::lift`] is then a lookup and cannot fail for
/// in-range indices.
pub struct Cumul {
    /// The greatest level the table covers.
    pub height: usize,
    /// `levels[n]` is the term `Uₙ`, for `n ≤ height`. Carried so that the
    /// rules below need no second reference to the [`Tower`] — a `Cumul` is
    /// already about one tower and nothing else, and taking the tower again
    /// would let a caller pair a table with the wrong one.
    levels: Vec<Term>,
    /// `steps[n]` is `⊢ Uₙ ⊆ U₍ₙ₊₁₎`, for `n < height`.
    steps: Vec<Thm>,
    /// `lifts[m][n - m]` is `⊢ Uₘ ⊆ Uₙ`, for `m ≤ n ≤ height`.
    lifts: Vec<Vec<Thm>>,
    /// `strict[n]` is `⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)`, for `n < height`.
    strict: Vec<Thm>,
}

impl Cumul {
    /// Prove every inclusion up to `height` and tabulate the composites.
    ///
    /// Fails only if the tower handed in is not one that [`Tower::new`] built —
    /// every
    /// step is checked against the subset formula rebuilt from
    /// [`kernel::thm::subset`], so a `Level` whose fields have drifted is
    /// refused rather than silently described.
    pub fn new(env: &mut Env, t: &Tower, height: usize) -> Option<Cumul> {
        let mut steps = Vec::with_capacity(height);
        let mut strict = Vec::with_capacity(height);
        for n in 0..height {
            steps.push(step(env, t, n)?);
            strict.push(no_descent(env, t, n)?);
        }

        // `Uₘ ⊆ Uₙ` by composing the steps `m, m+1, …, n-1`, memoised rather
        // than recomposed: the row for `m` extends its own previous entry.
        let mut lifts = Vec::with_capacity(height + 1);
        for m in 0..=height {
            let mut row = vec![refl(env, &t.level(m))];
            for (n, one) in steps.iter().enumerate().skip(m) {
                let prev = row.last()?.clone();
                row.push(compose(env, &prev, one, &t.level(m), &t.level(n + 1))?);
            }
            lifts.push(row);
        }
        let levels = (0..=height).map(|n| t.level(n)).collect();
        Some(Cumul { height, levels, steps, lifts, strict })
    }

    /// The term `Uₙ`, for `n ≤ height` — the tower's own, not a rebuilt copy.
    pub fn level(&self, n: usize) -> Option<Term> { self.levels.get(n).cloned() }

    /// `⊢ Uₙ ⊆ U₍ₙ₊₁₎` — the single step, for `n < height`.
    pub fn step(&self, n: usize) -> Option<&Thm> { self.steps.get(n) }

    /// `⊢ Uₘ ⊆ Uₙ`, i.e. `∀x. (x ∈ Uₘ → x ∈ Uₙ)`, for `m ≤ n ≤ height`.
    ///
    /// `m = n` is the reflexive instance and is included: a caller computing
    /// `max(u,v)` does not want to case-split on whether the max is reached.
    pub fn lift(&self, m: usize, n: usize) -> Option<&Thm> {
        self.lifts.get(m)?.get(n.checked_sub(m)?)
    }

    /// `⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)` — the inclusion is **strict**, for `n < height`.
    ///
    /// `Uₙ ∈ U₍ₙ₊₁₎` and `¬(Uₙ ∈ Uₙ)`, so `Uₙ` itself is the witness. This is
    /// the negative polarity of [`Cumul::lift`]: without it the table could in
    /// principle be a table of identities.
    pub fn strict(&self, n: usize) -> Option<&Thm> { self.strict.get(n) }

    /// From `⊢ t ∈ Uₘ` infer `⊢ t ∈ Uₙ`, for `m ≤ n ≤ height`.
    ///
    /// The membership is checked against [`Cumul::level`]: `mem` must conclude
    /// `t ∈ Uₘ` for the `Uₘ` of *this* tower, so a membership in some other set
    /// is refused rather than instantiated into nonsense.
    pub fn raise(&self, m: usize, n: usize, mem: &Thm) -> Option<Thm> {
        let (x, _) = mem.concl().as_mem()?;
        if *mem.concl() != Formula::mem(x.clone(), self.level(m)?) {
            return None
        }
        Thm::mp(&inst_all(self.lift(m, n)?, std::slice::from_ref(&x))?, mem)
    }

    /// `⊢ ∀x. (γ → v ∈ Uₘ) → ∀x. (γ → v ∈ Uₙ)` — the lift **under a binder and
    /// a guard**, for `m ≤ n ≤ height`.
    ///
    /// This is the shape the `Π` rule needs and the one [`Cumul::raise`] cannot
    /// reach: a fibre premise is `∀x. (x ∈ A → b(q⃗,x) ∈ U(c))`
    /// ([`crate::universe::fibres_in`]), so raising the fibres to `max(u,v)`
    /// happens under the binder. It is handed back as an *implication* rather
    /// than as a rule so that a caller carrying antecedents can chain it with
    /// [`crate::hyp_mp`]; [`Cumul::raise_fibres`] is the rule form.
    ///
    /// The pieces are taken rather than read off a theorem because a `∀` cannot
    /// be taken apart — the binder is de Bruijn — and rebuilding is the check.
    pub fn fibres_mono(
        &self,
        xv: FreeVar,
        guard: &Formula,
        val: &Term,
        m: usize,
        n: usize,
    ) -> Option<Thm> {
        let one = inst_all(self.lift(m, n)?, std::slice::from_ref(val))?;
        let under_guard = crate::imp_mono_r(&one, guard.clone())?;
        crate::forall_mono(xv, &Thm::gen(xv, &under_guard))
    }

    /// From `⊢ ∀x. (γ → v ∈ Uₘ)` infer `⊢ ∀x. (γ → v ∈ Uₙ)`, for `m ≤ n`.
    ///
    /// [`Cumul::fibres_mono`] plus one [`Thm::mp`], with the premise rebuilt
    /// from the pieces and compared first, so a theorem about some other family
    /// or some other level is refused rather than instantiated into nonsense.
    pub fn raise_fibres(
        &self,
        xv: FreeVar,
        guard: &Formula,
        val: &Term,
        m: usize,
        n: usize,
        fib: &Thm,
    ) -> Option<Thm> {
        let want =
            Formula::forall(xv, Formula::imp(guard.clone(), Formula::mem(val.clone(), self.level(m)?)));
        if *fib.concl() != want {
            return None
        }
        Thm::mp(&self.fibres_mono(xv, guard, val, m, n)?, fib)
    }
}

/// `⊢ Uₙ ⊆ U₍ₙ₊₁₎`.
///
/// `U₍ₙ₊₁₎`'s `mem_below` is `Uₙ ∈ U₍ₙ₊₁₎` — including at `n = 0`, where
/// [`Tower::at`] supplies `U₀ ∈ U₁` from [`Tower::u0_in`] rather than from
/// `x ∈ U(x)` — and `C₁(U₍ₙ₊₁₎)` turns a membership into an inclusion. Two
/// lines, and the only two in this file that touch the tower's fields.
fn step(env: &mut Env, t: &Tower, n: usize) -> Option<Thm> {
    let above = t.at(n + 1)?;
    let below = t.level(n);
    let at_y = inst_all(&above.transitive, std::slice::from_ref(&below))?;
    let out = Thm::mp(&at_y, &above.mem_below)?;
    (*out.concl() == kernel::thm::subset(env, below, above.set)).then_some(out)
}

/// `⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)`, from `Uₙ ∈ U₍ₙ₊₁₎` and Regularity's `¬(x ∈ x)`.
///
/// The inclusion, instantiated at `Uₙ`, would give `Uₙ ∈ Uₙ`. Exactly the
/// argument [`Tower::u0_ne_u1`] runs at the bottom of the tower, run at every
/// rung and delivering the stronger statement — non-equality follows from
/// non-inclusion, not the other way round.
fn no_descent(env: &mut Env, t: &Tower, n: usize) -> Option<Thm> {
    let above = t.at(n + 1)?;
    let below = t.level(n);
    let s = kernel::thm::subset(env, above.set, below.clone());
    let at = Thm::ax_inst(s.clone(), below.clone())?;
    let self_mem = mpd_const(&at, &above.mem_below)?; // `⊢ s → Uₙ ∈ Uₙ`
    let no_self = inst_all(&t.no_self_mem, std::slice::from_ref(&below))?;
    let out = syl(&self_mem, &no_self)?;
    (*out.concl() == Formula::not(s)).then_some(out)
}

/// `⊢ A ⊆ A`, at the bound variable [`kernel::thm::subset`] uses.
fn refl(env: &mut Env, a: &Term) -> Thm {
    let v = env.fresh_var();
    let out = Thm::gen(v, &crate::imp_refl(Formula::mem(Term::var(v), a.clone())));
    debug_assert_eq!(*out.concl(), kernel::thm::subset(env, a.clone(), a.clone()));
    out
}

/// `⊢ A ⊆ C` from `⊢ A ⊆ B` and `⊢ B ⊆ C`.
///
/// Both are `∀`-statements, so this opens each at a fresh variable, chains with
/// [`syl`] and re-generalises; the result is checked against
/// [`kernel::thm::subset`] rather than assumed to be it.
fn compose(env: &mut Env, ab: &Thm, bc: &Thm, a: &Term, c: &Term) -> Option<Thm> {
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l = inst_all(ab, std::slice::from_ref(&tv))?;
    let r = inst_all(bc, std::slice::from_ref(&tv))?;
    let out = Thm::gen(v, &syl(&l, &r)?);
    (*out.concl() == kernel::thm::subset(env, a.clone(), c.clone())).then_some(out)
}
