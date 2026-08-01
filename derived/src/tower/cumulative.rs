//! **Cumulativity**: `Uₙ ⊆ U₍ₙ₊₁₎`, and the lift between any two rungs,
//! exported as named theorems rather than recomposed at each use site.
//!
//! `m` and `n` throughout are **rung indices** ([`Rung::n`]), not Lean universe
//! levels; a closed Lean level has already been evaluated to the numeral that
//! indexes the rung by the time anything here is called.
//!
//! # Interface
//!
//! Writing `Uₙ` for [`Tower::u`], a [`Cumul`] built to `height` `h` exports,
//! for every pair of rungs `0 ≤ m ≤ n ≤ h`:
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
//! and the same two at **any number of binders and an optional guard**,
//! writing `x⃗` for `x₀ … x_{j-1}` and `[γ →]` for a guard that may be absent:
//!
//! ```text
//! ⊢ ∀x⃗. ([γ →] v ∈ Uₘ) → ∀x⃗. ([γ →] v ∈ Uₙ)           m ≤ n   [Cumul::fibres_mono_n]
//! from ⊢ ∀x⃗. ([γ →] v ∈ Uₘ) infer ⊢ ∀x⃗. ([γ →] v ∈ Uₙ) m ≤ n  [Cumul::raise_fibres_n]
//! ```
//!
//! The one-binder pair is literally the `j = 1`, `guard = Some` instance of the
//! `_n` pair — it is *defined* as that instance below, not derived a second
//! way — and `j = 0` with no guard is [`Cumul::raise`]'s implication. So a
//! caller with the general shape has one rule to reach for and the shapes
//! provably agree; `raise_fibres_n_at_one_binder_is_raise_fibres` pins it.
//!
//! The formulas are literally [`kernel::thm::subset`], so a consumer that
//! matches subset formulas syntactically — which is every consumer here — sees
//! what it expects. Nothing below is needed by a caller.
//!
//! # Why it is nearly free, and what the content actually is
//!
//! One line per rung: `U₍ₙ₋₁₎ ∈ Uₙ` ([`Rung::mem_below`]) fed to
//! `C₁(Uₙ)` ([`Rung::transitive`]) is `∀z. (z ∈ U₍ₙ₋₁₎ → z ∈ Uₙ)` on the nose.
//! Transitivity is the clause that was added to `ax_tarski` on 2026-07-31; before
//! that this file could not have existed, since `U(c)` was not transitive and
//! `Uₙ ⊆ U₍ₙ₊₁₎` was *refutable* along with `⋃`-closure and the rest — see the
//! countermodels at the end of [`crate::universe`].
//!
//! The **base case is not special**. One might expect `U₀ ⊆ U₁` to need its own
//! argument — `U₀ = {0,1}` is not a universe and rung 1 is not `U(U₀)` — and
//! the direct route is indeed `0 ∈ U(ω)` from `∅`-closure plus `1 = {0,0}` from
//! [`crate::universe::least_universe_pairing`]. It is not needed:
//! [`Tower::at`] already defines rung 1's `mem_below` as `U₀ ∈ U₁`
//! ([`Tower::u0_in`] at `ω`), so the very same two lines apply, and `0, 1 ∈ U₁`
//! come out as *instances* of the lift rather than as its ingredients. The test
//! `both_truth_values_lift_from_rung_zero_to_rung_one` checks exactly that.
//!
//! So the content here is the **export**, not the proof: a table of
//! `(m,n)`-indexed theorems, built once, so a consumer lifting a membership `i`
//! rungs does one [`Thm::mp`] instead of re-running the chain. That matters
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
//! * **A constructor's field obligations, at any depth.**
//!   [`crate::cumul::arg_obligations_at`]`()[j]` is
//!   `∀y₀ … ∀y_{j-1}. (Dⱼ → βⱼ(p⃗,y⃗) ∈ Uₙ)` — `j` *nested* binders, one per
//!   earlier field, and no guard at all when `j = 0` and the caller passes no
//!   `H`. [`Cumul::fibres_mono`]'s single binder covers `j ≤ 1` and so covers
//!   `Prod.{1,0}` and `TypeWithTypeField`, but a `k ≥ 3` declaration with a
//!   field above `U₁` needs `j = 2`, and [`Cumul::fibres_mono_n`] is that
//!   shape at every `j`. This is on the hot path, not an occasional
//!   convenience: [`crate::cumul::sigma_n`]'s rule is to run the telescope
//!   induction **once**, at `n₀ = max(1, max field rung)`, and raise — so a
//!   field whose membership is available below `n₀` is raised into place
//!   through here on every declaration that has one.
//! * **`ulift`.** `⟦ulift α⟧ = ⟦α⟧` (thesis.txt:2106), so its typing clause is
//!   `Uₙ ⊆ U₍ₙ′₎` and nothing else (thesis.txt:2284). There is no other `ulift`
//!   work; this file is all of it.
//!
//! # Non-vacuity, in both directions
//!
//! A subset statement is worthless if the smaller set is empty and misleading if
//! the two are equal. Both are excluded here: `∅`, `U₀` and `ω` are members of
//! every `Uₙ` with `n ≥ 1` ([`Rung::empty_mem`], [`Rung::u0_mem`],
//! [`Rung::omega_mem`]) and `0, 1` are members of `U₀`, so every inclusion is a
//! statement about an inhabited set; and [`Cumul::strict`] refutes the converse
//! inclusion outright, from `Uₙ ∈ U₍ₙ₊₁₎` and Regularity's `¬(x ∈ x)`. The tower
//! therefore does not collapse anywhere, not merely at the bottom, which is all
//! [`Tower::u0_ne_u1`] said.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use super::rungs::Tower;
use crate::{inst_all, mpd_const, syl};

/// The cumulativity table for a tower, built up to a fixed height.
///
/// `Cumul::new(env, t, h)` proves `Uₙ ⊆ U₍ₙ₊₁₎` for every `n < h` and composes
/// them into `Uₘ ⊆ Uₙ` for every `m ≤ n ≤ h`. `h` is a *meta-level* bound, like
/// [`Tower::u`]'s argument and for the same reason: a closed Lean level
/// evaluates to a numeral before the interpretation runs, so the highest rung a
/// file mentions is known, and nothing here needs a set-theoretic recursion.
///
/// The table is `O(h²)` theorems and `h` is a small numeral in practice, so it
/// is built eagerly; [`Cumul::lift`] is then a lookup and cannot fail for
/// in-range indices.
pub struct Cumul {
    /// The greatest rung the table covers.
    pub height: usize,
    /// `sets[n]` is the term `Uₙ`, for `n ≤ height`. Carried so that the
    /// rules below need no second reference to the [`Tower`] — a `Cumul` is
    /// already about one tower and nothing else, and taking the tower again
    /// would let a caller pair a table with the wrong one.
    sets: Vec<Term>,
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
    /// every step is checked against the subset formula rebuilt from
    /// [`kernel::thm::subset`] **and checked to rest on nothing**, so a `Rung`
    /// whose fields have drifted, or whose theorems hold only under a
    /// hypothesis, is refused rather than silently described. The second half
    /// matters more than it looks: this table is memoised, so one hypothesis
    /// admitted here would be replayed by every later [`Cumul::lift`] and
    /// [`Cumul::raise`] rather than mislabelling a single theorem.
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
            let mut row = vec![refl(env, &t.u(m))];
            for (n, one) in steps.iter().enumerate().skip(m) {
                let prev = row.last()?.clone();
                row.push(compose(env, &prev, one, &t.u(m), &t.u(n + 1))?);
            }
            lifts.push(row);
        }
        let sets = (0..=height).map(|n| t.u(n)).collect();
        Some(Cumul { height, sets, steps, lifts, strict })
    }

    /// The term `Uₙ` at rung `n ≤ height` — the tower's own, not a rebuilt
    /// copy.
    pub fn u(&self, n: usize) -> Option<Term> { self.sets.get(n).cloned() }

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
    /// The membership is checked against [`Cumul::u`]: `mem` must conclude
    /// `t ∈ Uₘ` for the `Uₘ` of *this* tower, so a membership in some other set
    /// is refused rather than instantiated into nonsense. It must also be
    /// **unconditional** — the rule is `⊢`-to-`⊢`, and [`Thm::mp`] below would
    /// otherwise union the caller's `Γ` into a result labelled `⊢ t ∈ Uₙ`.
    /// This is not hypothetical: `mini`'s `fs_typing` calls this on theorems it
    /// obtained under scope hypotheses, and `mini` is exempt from the
    /// boundary rule that keeps `Thm::assume` out of shipped code.
    pub fn raise(&self, m: usize, n: usize, mem: &Thm) -> Option<Thm> {
        let (x, _) = mem.concl().as_mem()?;
        if !crate::establishes(mem, &Formula::mem(x.clone(), self.u(m)?)) {
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
        self.fibres_mono_n(std::slice::from_ref(&xv), Some(guard), val, m, n)
    }

    /// `⊢ ∀x⃗. ([γ →] v ∈ Uₘ) → ∀x⃗. ([γ →] v ∈ Uₙ)` — the lift under **any
    /// number** of nested binders and an **optional** guard, for `m ≤ n`.
    ///
    /// `xs` is the binder list outermost-first, so `xs = [y₀, y₁]` produces
    /// `∀y₀ ∀y₁. …` — the order [`crate::cumul::arg_obligations_at`] quantifies
    /// in, and the order matters: the guard `Dⱼ` mentions the *earlier*
    /// variables, so binding them in the other order would leave `y₀` free
    /// under `∀y₁` and the rebuilt formula would not be the one the consumer
    /// states. The variables are handed in rather than read off a formula for
    /// the reason [`Cumul::fibres_mono`] gives: a `∀` cannot be taken apart,
    /// the binder being de Bruijn, and rebuilding is the check.
    ///
    /// `guard = None` is not a convenience for `⊤` — this kernel has no `⊤` —
    /// it is the genuinely guardless shape, which `arg_obligations_at()[0]`
    /// with no caller antecedent really has.
    ///
    /// The derivation is [`Cumul::fibres_mono`]'s, iterated: one
    /// [`crate::forall_mono`] per binder, innermost first, so the cost is
    /// linear in `xs.len()` and nothing new is minted. At `xs = []` and
    /// `guard = None` it is [`Cumul::lift`] instantiated at `val`, i.e. exactly
    /// the implication [`Cumul::raise`] applies.
    pub fn fibres_mono_n(
        &self,
        xs: &[FreeVar],
        guard: Option<&Formula>,
        val: &Term,
        m: usize,
        n: usize,
    ) -> Option<Thm> {
        let one = inst_all(self.lift(m, n)?, std::slice::from_ref(val))?;
        let mut cur = match guard {
            Some(g) => crate::imp_mono_r(&one, g.clone())?,
            None => one,
        };
        // Innermost binder first: `forall_mono` turns `⊢ ∀x. (φ → ψ)` into
        // `⊢ (∀x. φ) → (∀x. ψ)`, so each step wraps one more `∀` around *both*
        // sides and the next step out sees an implication again.
        for x in xs.iter().rev() {
            cur = crate::forall_mono(*x, &Thm::gen(*x, &cur))?;
        }
        Some(cur)
    }

    /// `∀x⃗. ([γ →] v ∈ Uₘ)` as a formula — what [`Cumul::raise_fibres_n`]
    /// compares its premise against, built from the same pieces that build the
    /// theorem.
    fn fibres_formula(
        &self,
        xs: &[FreeVar],
        guard: Option<&Formula>,
        val: &Term,
        m: usize,
    ) -> Option<Formula> {
        let goal = Formula::mem(val.clone(), self.u(m)?);
        let body = match guard {
            Some(g) => Formula::imp(g.clone(), goal),
            None => goal,
        };
        Some(xs.iter().rev().fold(body, |acc, x| Formula::forall(*x, acc)))
    }

    /// From `⊢ ∀x. (γ → v ∈ Uₘ)` infer `⊢ ∀x. (γ → v ∈ Uₙ)`, for `m ≤ n`.
    ///
    /// [`Cumul::fibres_mono`] plus one [`Thm::mp`], with the premise rebuilt
    /// from the pieces and compared first, so a theorem about some other family
    /// or some other rung is refused rather than instantiated into nonsense.
    /// `fib` must also be unconditional, for the reason given on
    /// [`Cumul::raise`]: the header says `⊢`-to-`⊢`, and the `mp` would
    /// otherwise carry the caller's `Γ` into the result.
    pub fn raise_fibres(
        &self,
        xv: FreeVar,
        guard: &Formula,
        val: &Term,
        m: usize,
        n: usize,
        fib: &Thm,
    ) -> Option<Thm> {
        self.raise_fibres_n(std::slice::from_ref(&xv), Some(guard), val, m, n, fib)
    }

    /// From `⊢ ∀x⃗. ([γ →] v ∈ Uₘ)` infer `⊢ ∀x⃗. ([γ →] v ∈ Uₙ)`, for `m ≤ n`
    /// and **any number** of nested binders.
    ///
    /// [`Cumul::fibres_mono_n`] plus one [`Thm::mp`], with the premise rebuilt
    /// from the pieces and compared first, so a
    /// theorem about some other family, some other binder order or some other
    /// rung is refused rather than instantiated into nonsense. `fib` must also
    /// be **unconditional**, for the reason given on [`Cumul::raise`]: the
    /// header says `⊢`-to-`⊢`, and the `mp` would otherwise carry the caller's
    /// `Γ` into a result the label calls unconditional.
    #[allow(clippy::too_many_arguments)]
    pub fn raise_fibres_n(
        &self,
        xs: &[FreeVar],
        guard: Option<&Formula>,
        val: &Term,
        m: usize,
        n: usize,
        fib: &Thm,
    ) -> Option<Thm> {
        let want = self.fibres_formula(xs, guard, val, m)?;
        if !crate::establishes(fib, &want) {
            return None
        }
        Thm::mp(&self.fibres_mono_n(xs, guard, val, m, n)?, fib)
    }
}

/// `⊢ Uₙ ⊆ U₍ₙ₊₁₎`.
///
/// `U₍ₙ₊₁₎`'s `mem_below` is `Uₙ ∈ U₍ₙ₊₁₎` — including at `n = 0`, where
/// [`Tower::at`] supplies `U₀ ∈ U₁` from [`Tower::u0_in`] rather than from
/// `x ∈ U(x)` — and `C₁(U₍ₙ₊₁₎)` turns a membership into an inclusion. Two
/// lines, and the only two in this file that touch the tower's fields.
///
/// The output is checked to rest on nothing as well as to have the right shape.
/// These two lines are the only place a `Tower`'s theorems enter the table, and
/// the table is *memoised* — a hypothesis riding in from a doctored `Rung`
/// would be stored once and replayed by every later [`Cumul::lift`] and
/// [`Cumul::raise`], which is the stored-certificate shape rather than a single
/// mislabelled theorem. The live path gets its `Tower` honestly built through
/// `Rc<Prelude>`, so this is belt-and-braces; it costs one `&&`.
fn step(env: &mut Env, t: &Tower, n: usize) -> Option<Thm> {
    let above = t.at(n + 1)?;
    let below = t.u(n);
    let at_y = inst_all(&above.transitive, std::slice::from_ref(&below))?;
    let out = Thm::mp(&at_y, &above.mem_below)?;
    let want = kernel::thm::subset(env, below, above.set);
    crate::establishes(&out, &want).then_some(out)
}

/// `⊢ ¬(U₍ₙ₊₁₎ ⊆ Uₙ)`, from `Uₙ ∈ U₍ₙ₊₁₎` and Regularity's `¬(x ∈ x)`.
///
/// The inclusion, instantiated at `Uₙ`, would give `Uₙ ∈ Uₙ`. Exactly the
/// argument [`Tower::u0_ne_u1`] runs at the bottom of the tower, run at every
/// rung and delivering the stronger statement — non-equality follows from
/// non-inclusion, not the other way round.
fn no_descent(env: &mut Env, t: &Tower, n: usize) -> Option<Thm> {
    let above = t.at(n + 1)?;
    let below = t.u(n);
    let s = kernel::thm::subset(env, above.set, below.clone());
    let at = Thm::ax_inst(s.clone(), below.clone())?;
    let self_mem = mpd_const(&at, &above.mem_below)?; // `⊢ s → Uₙ ∈ Uₙ`
    let no_self = inst_all(&t.no_self_mem, std::slice::from_ref(&below))?;
    let out = syl(&self_mem, &no_self)?;
    crate::establishes(&out, &Formula::not(s)).then_some(out)
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
    let want = kernel::thm::subset(env, a.clone(), c.clone());
    crate::establishes(&out, &want).then_some(out)
}
