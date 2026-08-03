//! **The iterated `rec₊` dispatcher** — one set function on
//! `A₀ + (… + (A_{n-1} + 0))` built from `n` branch functions, with the `n`
//! computation rules `app(disp, inj_i(a)) = app(fᵢ, a)`.
//!
//! # What the thesis asks for
//!
//! §5.2's `spec` judgment (`thesis.txt:1789–1791`) dispatches the fibre family
//! over the constructor list by **iterated `rec₊`**:
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ 0 spec ⇒ 0; rec0; rec0
//! Γ; t : F ⊢ (c : β) + K spec ⇒ A₁ + A;  rec₊ (λp.B₁) B;  …
//! ```
//!
//! — one `rec₊` per constructor, nested to the right in step with
//! [`super::tags`]' sum, and bottoming out at `rec0`, the unique function out
//! of `0`. In this development that function is `∅`
//! ([`crate::wtype::empty_is_a_function`]), so the term is
//!
//! ```text
//! disp = case(A₀, A₁+(…+0), T, f₀, case(A₁, A₂+(…+0), T, f₁, … case(A_{n-1}, 0, T, f_{n-1}, ∅) …))
//! ```
//!
//! # Interface
//!
//! [`Dispatch::new`] takes the summands, the common codomain `T`, the `n`
//! branch functions **and their typing theorems**, and returns
//!
//! ```text
//! ⊢ disp ∈ fs(Sum_n(A₀ … A_{n-1}), T)                         [Dispatch::in_funspace]
//! ⊢ ∀a. (a ∈ Aᵢ → app(disp, Inj_i(a)) = app(fᵢ, a))           [Dispatch::beta[i]]
//! ```
//!
//! **Both are stated over [`super::symbols`]' symbols, not over the meta-level
//! nest.** `Sum_n(A⃗)` and `Inj_i(a)` are provably equal to `A₀ + (… + 0)` and
//! `inr^i(inl a)` — [`ISumSyms::sum_ax`](super::ISumSyms::sum_ax) and
//! [`ISumSyms::inj_ax`](super::ISumSyms::inj_ax) are the equations — but they
//! are *different terms*, and a caller who rebuilds the nest form and compares
//! `concl()` gets a rejection. The dispatcher's own term (above) is still the
//! nest of `case`s; only the statements are over the symbols.
//!
//! [`dispatch_of`] is the term on its own, for a caller that wants to mention
//! it before proving anything.
//!
//! # The hypothetical variant — [`Dispatch::under`], and what it actually cost
//!
//! `#37` wants a dispatcher whose branches are *variables* `g⃗` with
//! `gⱼ ∈ fs(Aⱼ, T)` as the **caller's hypothesis** rather than a fact. The
//! branch typings taken by [`Dispatch::new`] are inputs and must be
//! unconditional, so that needs a second entry point:
//!
//! ```text
//! ⊢ H → disp ∈ fs(Sum_n(A⃗), T)                                [Dispatch::in_funspace]
//! ⊢ H → ∀a. (a ∈ Aᵢ → app(disp, Inj_i(a)) = app(gᵢ, a))       [Dispatch::beta[i]]
//! ```
//!
//! **The first estimate, from reading the shape of the file, was that only the
//! `tails` fold consumes `branch_fs` — so `beta` would be untouched and the
//! variant would be `hyp_mp`/`a1i` in one loop. That is wrong.** `beta` consumes
//! both: the `inr` chain spends `tails[k+1]` (the nest's own typing) and the
//! `inl` step spends `branch_fs[i]` directly, because
//! [`Cases::beta_left`](crate::sums::Cases) cannot compute at a branch without
//! knowing the branch is a function. So under a hypothetical `H` **every**
//! export is `⊢ H → …`, the `n` computation rules included.
//!
//! That is not a defect to engineer around; it is the truth about the object. A
//! dispatcher over *arbitrary* branches computes only where the branches are
//! functions. The degenerate case escapes because its branches are
//! **constructed** — [`crate::point_fun`]'s one-point graphs are functions by
//! construction and [`crate::finset::FinSet`] makes their codomain free — and a
//! construction cannot be recovered from a variable.
//!
//! **Both entry points are one derivation.** The nest, the fold and the `n`
//! chains are written once against [`crate::ctx::Ctx`], an *optional*
//! antecedent, so `new` is literally `under` at `Ctx(None)` and the two cannot
//! drift. That is what keeps the degenerate spelling term-identical rather than
//! merely provably equal. The `n` computation rules need one thing the rest does
//! not: their chain runs under `H ∧ (a ∈ Aᵢ)` — two antecedents, of which only
//! the first survives into the statement — so the loop opens a compound context
//! and curries out of it at the end.
//!
//! One consequence worth having in front of a reader of
//! [`crate::recarg`]: `RecArg::app` was **unconditional**, and its header said
//! that is what makes a constructor injective in its recursive arguments. The
//! general form cannot be, so the generalisation changes that contract and
//! reaches `RecArg`'s consumers, not just `RecArg`.
//!
//! The dispatcher's *term* mentions its codomain, so a general variant cannot
//! simply take `S` — the constructor term would then mention a set that is not
//! part of the constructor's data. The codomain has to be built from the
//! branches, as `FinSet::of(r⃗)` is in the degenerate case; at a general fibre
//! that is [`crate::ran::Ran`] and **not**
//! [`crate::funcs::snd_in_union2`], whose `⋃⋃f` holds the domain as well as the
//! values.
//!
//! **The side condition, not the algebra, is what resists** — the same shape as
//! [`crate::fibre`]'s open-value boundary, where the four theorems are generic
//! in a value and `define_abbrev` is not.
//!
//! # Why the branch typings are *inputs* rather than an antecedent
//!
//! The alternative — quantifying `f₀ … f_{n-1}` and carrying
//! `⋀ᵢ fᵢ ∈ fs(Aᵢ,T)` as one antecedent — states the same thing, but it forces
//! every caller to build and then take apart an `n`-fold conjunction, and it
//! has no sensible form at `n = 0`. Taking the theorems as arguments keeps all
//! `n + 1` exports **unconditional**, and it is what the callers actually have:
//! `wnat.rs` and `wlist.rs` each hold their two branch typings as separate
//! theorems already. The typings are *checked* against the branches and the
//! codomain rather than assumed, so a mismatched pair is refused.
//!
//! # Why `beta[i]` needs every typing and not just `fᵢ`'s
//!
//! Reaching branch `i` walks `i` right-branches of the nest, and
//! [`Cases::beta_right`](crate::sums::Cases::beta_right) charges
//! `g ∈ fs(B,T)` for each — where `g` is the whole remaining nest. So the
//! `i`-th computation rule consumes the typings of branches `i, i+1, … n-1`,
//! and the `inl` step at the end consumes `fᵢ`'s. The other antecedent,
//! `b ∈ B`, is discharged by [`super::tags::inj_mem_at`] on the suffix, which
//! is the only place the tail memberships are needed.
//!
//! # Nothing here is an axiom
//!
//! One nest of the existing `case` symbol, with every step an instance of
//! [`Cases::in_funspace`](crate::sums::Cases::in_funspace),
//! [`beta_left`](crate::sums::Cases::beta_left) or
//! [`beta_right`](crate::sums::Cases::beta_right). No new symbol.

use kernel::{Env, Formula, Term, Thm};

use crate::ctx::Ctx;
use crate::recursion::hyp::hyp_eq_trans;
use crate::sums::{Cases, Sums};
use crate::{a1i, and_left, and_right, curry, inst_all, syl, uncurry};

use super::symbols::ISumSyms;
use super::tags::{inj_mem_at, inj_of, isum_of};

/// The term `case(A₀, …, T, f₀, case(A₁, …, T, f₁, … ∅ …))`.
///
/// `summands` and `branches` must have the same length; the result for the
/// empty list is `∅`, the unique function out of `0`.
pub fn dispatch_of(s: &Sums, cases: &Cases, summands: &[Term], t: &Term, branches: &[Term]) -> Term {
    let n = summands.len();
    let mut acc = s.zero();
    for k in (0..n).rev() {
        acc = cases.of(
            summands[k].clone(),
            isum_of(s, &summands[k + 1..]),
            t.clone(),
            branches[k].clone(),
            acc,
        );
    }
    acc
}

/// The dispatcher at concrete summands, codomain and branches, with its typing
/// rule and its `n` computation rules.
pub struct Dispatch {
    /// `A₀ … A_{n-1}`.
    pub summands: Vec<Term>,
    /// The common codomain `T`.
    pub target: Term,
    /// `f₀ … f_{n-1}`.
    pub branches: Vec<Term>,
    /// `Sum_n(A₀ … A_{n-1})`.
    pub tags: Term,
    /// The dispatcher itself.
    pub fun: Term,
    /// The antecedent every export below carries, or `None` for
    /// [`Dispatch::new`], where there is none. `Some(H)` is
    /// [`Dispatch::under`]'s hypothesis and is stated **outermost**, in front of
    /// each rule's own `∀` — see the field docs.
    pub hyp: Option<Formula>,
    /// `⊢ H → disp ∈ fs(Sum_n(A⃗), T)`, without the `H →` at
    /// [`Dispatch::new`].
    pub in_funspace: Thm,
    /// For each `i < n`:
    /// `⊢ H → ∀a. (a ∈ Aᵢ → app(disp, Inj_i(a)) = app(fᵢ, a))`, without the
    /// `H →` at [`Dispatch::new`].
    ///
    /// **The hypothesis does not become optional here.** A dispatcher over
    /// branch *variables* computes only where the branches are functions, and
    /// that is the caller's assumption — see this module's header.
    pub beta: Vec<Thm>,
    /// For each `k ≤ n`: `⊢ H → nestₖ ∈ fs(Sum_{n-k}(A_k …), T)`, the typing of
    /// the `k`-th tail of the nest — `nest₀` is [`Dispatch::in_funspace`] and
    /// `nestₙ` is `∅ ∈ fs(Sum_0(), T)`, the empty function typed at the
    /// *symbol* for the trailing `0`. Exposed because a caller reducing at a tag
    /// deeper in the nest needs it and re-deriving it would repeat the work.
    pub tail_in_funspace: Vec<Thm>,
}

impl Dispatch {
    /// Build the dispatcher and derive its typing and computation rules,
    /// **unconditionally**.
    ///
    /// `typed_branches[i]` is the pair `(fᵢ, ⊢ fᵢ ∈ fs(Aᵢ, T))` — the branch
    /// function together with its typing, which is checked against `summands`
    /// and `target` rather than assumed. `empty_fun` must be
    /// [`crate::wtype::empty_is_a_function`]'s `⊢ ∀S. ∅ ∈ fs(∅,S)` over the
    /// same [`Sums`], and is checked too.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        s: &Sums,
        cases: &Cases,
        syms: &ISumSyms,
        summands: &[Term],
        target: &Term,
        typed_branches: &[(Term, Thm)],
        empty_fun: &Thm,
    ) -> Option<Dispatch> {
        build(env, s, cases, syms, summands, target, &Ctx(None), typed_branches, empty_fun)
    }

    /// The same dispatcher **under a hypothesis** `h`, for branches that are
    /// variables rather than constructions.
    ///
    /// `typed_branches[i]` is `(fᵢ, ⊢ h → fᵢ ∈ fs(Aᵢ, T))`, checked as above,
    /// and every export comes back `⊢ h → …`. `empty_fun` is still the
    /// unconditional `⊢ ∀S. ∅ ∈ fs(∅,S)`; it is weakened here rather than by the
    /// caller.
    ///
    /// The computation rules are **not** exempt: `beta_left` cannot compute at a
    /// branch without knowing the branch is a function, so `h` reaches all
    /// `n + 1` exports. See this module's header.
    #[allow(clippy::too_many_arguments)]
    pub fn under(
        env: &mut Env,
        s: &Sums,
        cases: &Cases,
        syms: &ISumSyms,
        summands: &[Term],
        target: &Term,
        h: &Formula,
        typed_branches: &[(Term, Thm)],
        empty_fun: &Thm,
    ) -> Option<Dispatch> {
        build(
            env,
            s,
            cases,
            syms,
            summands,
            target,
            &Ctx(Some(h.clone())),
            typed_branches,
            empty_fun,
        )
    }
}

/// The `i`-th computation rule's **compound** context: the caller's `H`, if
/// any, conjoined with `a ∈ Aᵢ`.
///
/// Only `H` survives into the statement — `a ∈ Aᵢ` is the rule's own
/// antecedent and goes back under the `∀a` — so the chain is derived under the
/// conjunction and curried apart at the end. Four converters, because the three
/// ingredients arrive under three different antecedents: the nest's typing under
/// `H`, the tag membership under `a ∈ Aᵢ`, and `beta_left`'s output under both.
struct Both<'a> {
    outer: &'a Option<Formula>,
    inner: Formula,
}

impl Both<'_> {
    /// The context the chain runs in.
    fn ctx(&self) -> Ctx {
        Ctx(Some(match self.outer {
            Some(h) => Formula::and(h.clone(), self.inner.clone()),
            None => self.inner.clone(),
        }))
    }

    /// From `⊢ H → φ` — or `⊢ φ`, when there is no `H` — infer `⊢ D → φ`.
    fn join_outer(&self, t: &Thm) -> Option<Thm> {
        match self.outer {
            Some(h) => syl(&and_left(h.clone(), self.inner.clone()), t),
            None => Some(a1i(t, self.inner.clone())),
        }
    }

    /// From `⊢ (a ∈ Aᵢ) → φ` infer `⊢ D → φ`.
    fn join_inner(&self, t: &Thm) -> Option<Thm> {
        match self.outer {
            Some(h) => syl(&and_right(h.clone(), self.inner.clone()), t),
            None => Some(t.clone()),
        }
    }

    /// From `⊢ H → ((a ∈ Aᵢ) → φ)` infer `⊢ D → φ`.
    fn join_both(&self, t: &Thm) -> Option<Thm> {
        match self.outer {
            Some(_) => curry(t),
            None => Some(t.clone()),
        }
    }

    /// From `⊢ D → φ` infer `⊢ H → ((a ∈ Aᵢ) → φ)` — the shape the rule is
    /// stated in.
    fn release(&self, t: &Thm) -> Option<Thm> {
        match self.outer {
            Some(_) => uncurry(t),
            None => Some(t.clone()),
        }
    }
}

/// The one derivation both entry points run. `ctx` decides whether every step
/// carries an antecedent; nothing else differs.
#[allow(clippy::too_many_arguments)]
fn build(
    env: &mut Env,
    s: &Sums,
    cases: &Cases,
    syms: &ISumSyms,
    summands: &[Term],
    target: &Term,
    ctx: &Ctx,
    typed_branches: &[(Term, Thm)],
    empty_fun: &Thm,
) -> Option<Dispatch> {
    let n = summands.len();
    if typed_branches.len() != n {
        return None
    }
    let branches: Vec<Term> = typed_branches.iter().map(|(f, _)| f.clone()).collect();
    let branch_fs: Vec<Thm> = typed_branches.iter().map(|(_, t)| t.clone()).collect();
    for (i, (f, th)) in typed_branches.iter().enumerate() {
        let want =
            ctx.under(Formula::mem(f.clone(), s.fs.of(summands[i].clone(), target.clone())));
        if *th.concl() != want {
            return None
        }
    }
    let tail = |k: usize| isum_of(s, &summands[k..]);

    // ── the nest's typing, from `∅ ∈ fs(0,T)` outwards ──────────────────────
    let empty_at = inst_all(empty_fun, std::slice::from_ref(target))?;
    if *empty_at.concl() != Formula::mem(s.zero(), s.fs.of(s.zero(), target.clone())) {
        return None
    }
    let mut tails: Vec<Thm> = vec![ctx.lift(&empty_at)];
    for k in (0..n).rev() {
        let rest = tails.last()?.clone();
        let rule = inst_all(
            &cases.in_funspace,
            &[
                summands[k].clone(),
                tail(k + 1),
                target.clone(),
                branches[k].clone(),
                dispatch_of(s, cases, &summands[k + 1..], target, &branches[k + 1..]),
            ],
        )?;
        tails.push(ctx.syl(&ctx.and(&branch_fs[k], &rest)?, &rule)?);
    }
    tails.reverse();
    let fun = dispatch_of(s, cases, summands, target, &branches);

    // ── the `n` computation rules ───────────────────────────────────────────
    let av = env.fresh_var();
    let ta = Term::var(av);
    let mut beta = Vec::with_capacity(n);
    for i in 0..n {
        // Each chain runs under `H ∧ (a ∈ Aᵢ)`; only `H` survives the release.
        let both = Both { outer: &ctx.0, inner: Formula::mem(ta.clone(), summands[i].clone()) };
        let d = both.ctx();

        let mut chain: Option<Thm> = None;
        for k in 0..i {
            // `app(nestₖ, inr(b)) = app(nest_{k+1}, b)` with
            // `b = inj_{i-k-1}(a)` the injection into the `(k+1)`-th tail.
            let inner = dispatch_of(s, cases, &summands[k + 1..], target, &branches[k + 1..]);
            let b = inj_of(s, i - k - 1, ta.clone());
            let rule = inst_all(
                &cases.beta_right,
                &[
                    summands[k].clone(),
                    tail(k + 1),
                    target.clone(),
                    branches[k].clone(),
                    inner,
                    b.clone(),
                ],
            )?;
            let typed = both.join_outer(&ctx.syl(&tails[k + 1], &rule)?)?;
            let mem = both.join_inner(&inj_mem_at(s, &summands[k + 1..], i - k - 1, &ta)?)?;
            let step = d.mp(&typed, &mem)?;
            chain = Some(match chain {
                None => step,
                Some(c) => hyp_eq_trans(env, &c, &step)?,
            });
        }
        // The `inl` step: `app(nestᵢ, inl(a)) = app(fᵢ, a)`.
        let last = {
            let inner = dispatch_of(s, cases, &summands[i + 1..], target, &branches[i + 1..]);
            let rule = inst_all(
                &cases.beta_left,
                &[
                    summands[i].clone(),
                    tail(i + 1),
                    target.clone(),
                    branches[i].clone(),
                    inner,
                    ta.clone(),
                ],
            )?;
            both.join_both(&ctx.syl(&branch_fs[i], &rule)?)?
        };
        let out = both.release(&match chain {
            None => last,
            Some(c) => hyp_eq_trans(env, &c, &last)?,
        })?;
        debug_assert_eq!(
            *out.concl(),
            ctx.under(Formula::imp(
                Formula::mem(ta.clone(), summands[i].clone()),
                Formula::eq(
                    s.ap.apply(fun.clone(), inj_of(s, i, ta.clone())),
                    s.ap.apply(branches[i].clone(), ta.clone()),
                ),
            )),
            "isum::dispatch: beta has the wrong shape"
        );
        beta.push(ctx.gen(av, &out)?);
    }

    // ── restate every export over the *symbols* ─────────────────────────────
    // `tails` and `beta` above are proved against the nest, which is this
    // file's construction; nothing outside sees it.
    let mut tail_in_funspace = Vec::with_capacity(n + 1);
    for (k, th) in tails.iter().enumerate() {
        let hole = env.fresh_var();
        let carry = Thm::eq_leibniz(
            tail(k),
            syms.sum(&summands[k..])?,
            hole,
            Formula::mem(
                dispatch_of(s, cases, &summands[k..], target, &branches[k..]),
                s.fs.of(Term::var(hole), target.clone()),
            ),
        );
        let unfold = crate::eq_symm(env, &inst_all(syms.sum_ax(n - k)?, &summands[k..])?)?;
        tail_in_funspace.push(ctx.syl(th, &Thm::mp(&carry, &unfold)?)?);
    }
    let in_funspace = tail_in_funspace[0].clone();
    debug_assert_eq!(
        *in_funspace.concl(),
        ctx.under(Formula::mem(fun.clone(), s.fs.of(syms.sum(summands)?, target.clone()))),
        "isum::dispatch: in_funspace has the wrong shape"
    );

    let mut folded = Vec::with_capacity(n);
    for (i, th) in beta.iter().enumerate() {
        let at = ctx.inst(th, ta.clone())?;
        let hole = env.fresh_var();
        let carry = Thm::eq_leibniz(
            inj_of(s, i, ta.clone()),
            syms.inj(i, ta.clone())?,
            hole,
            Formula::imp(
                Formula::mem(ta.clone(), summands[i].clone()),
                Formula::eq(
                    s.ap.apply(fun.clone(), Term::var(hole)),
                    s.ap.apply(branches[i].clone(), ta.clone()),
                ),
            ),
        );
        let unfold = crate::eq_symm(env, &inst_all(syms.inj_ax(i)?, std::slice::from_ref(&ta))?)?;
        folded.push(ctx.gen(av, &ctx.syl(&at, &Thm::mp(&carry, &unfold)?)?)?);
    }

    Some(Dispatch {
        summands: summands.to_vec(),
        target: target.clone(),
        branches,
        tags: syms.sum(summands)?,
        fun,
        hyp: ctx.0.clone(),
        in_funspace,
        beta: folded,
        tail_in_funspace,
    })
}
