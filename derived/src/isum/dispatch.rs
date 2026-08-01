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

use crate::recursion::hyp::hyp_eq_trans;
use crate::sums::{Cases, Sums};
use crate::{and_intro, gen_all, inst_all, syl};

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
    /// `⊢ disp ∈ fs(Sum_n(A⃗), T)`.
    pub in_funspace: Thm,
    /// For each `i < n`: `⊢ ∀a. (a ∈ Aᵢ → app(disp, Inj_i(a)) = app(fᵢ, a))`.
    pub beta: Vec<Thm>,
    /// For each `k ≤ n`: `⊢ nestₖ ∈ fs(Sum_{n-k}(A_k …), T)`, the typing of the
    /// `k`-th tail of the nest — `nest₀` is [`Dispatch::in_funspace`] and
    /// `nestₙ` is `∅ ∈ fs(Sum_0(), T)`, the empty function typed at the
    /// *symbol* for the trailing `0`. Exposed because a caller reducing at a tag
    /// deeper in the nest needs it and re-deriving it would repeat the work.
    pub tail_in_funspace: Vec<Thm>,
}

impl Dispatch {
    /// Build the dispatcher and derive its typing and computation rules.
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
        let n = summands.len();
        if typed_branches.len() != n {
            return None
        }
        let branches: Vec<Term> = typed_branches.iter().map(|(f, _)| f.clone()).collect();
        let branch_fs: Vec<Thm> = typed_branches.iter().map(|(_, t)| t.clone()).collect();
        for (i, (f, th)) in typed_branches.iter().enumerate() {
            if *th.concl() != Formula::mem(f.clone(), s.fs.of(summands[i].clone(), target.clone())) {
                return None
            }
        }
        let tail = |k: usize| isum_of(s, &summands[k..]);

        // ── the nest's typing, from `∅ ∈ fs(0,T)` outwards ──────────────────
        let mut tails: Vec<Thm> = vec![inst_all(empty_fun, std::slice::from_ref(target))?];
        if *tails[0].concl() != Formula::mem(s.zero(), s.fs.of(s.zero(), target.clone())) {
            return None
        }
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
            tails.push(Thm::mp(&rule, &and_intro(&branch_fs[k], &rest))?);
        }
        tails.reverse();
        let fun = dispatch_of(s, cases, summands, target, &branches);

        // ── the `n` computation rules ───────────────────────────────────────
        let av = env.fresh_var();
        let ta = Term::var(av);
        let mut beta = Vec::with_capacity(n);
        for i in 0..n {
            let mut chain: Option<Thm> = None;
            for k in 0..i {
                // `app(nestₖ, inr(b)) = app(nest_{k+1}, b)` with
                // `b = inj_{i-k-1}(a)` the injection into the `(k+1)`-th tail.
                let inner = dispatch_of(
                    s,
                    cases,
                    &summands[k + 1..],
                    target,
                    &branches[k + 1..],
                );
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
                let typed = Thm::mp(&rule, &tails[k + 1])?;
                let mem = inj_mem_at(s, &summands[k + 1..], i - k - 1, &ta)?;
                let step = syl(&mem, &typed)?;
                chain = Some(match chain {
                    None => step,
                    Some(c) => hyp_eq_trans(env, &c, &step)?,
                });
            }
            // The `inl` step: `app(nestᵢ, inl(a)) = app(fᵢ, a)`.
            let last = {
                let inner =
                    dispatch_of(s, cases, &summands[i + 1..], target, &branches[i + 1..]);
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
                Thm::mp(&rule, &branch_fs[i])?
            };
            let out = match chain {
                None => last,
                Some(c) => hyp_eq_trans(env, &c, &last)?,
            };
            debug_assert_eq!(
                *out.concl(),
                Formula::imp(
                    Formula::mem(ta.clone(), summands[i].clone()),
                    Formula::eq(
                        s.ap.apply(fun.clone(), inj_of(s, i, ta.clone())),
                        s.ap.apply(branches[i].clone(), ta.clone()),
                    ),
                ),
                "isum::dispatch: beta has the wrong shape"
            );
            beta.push(gen_all(&[av], &out));
        }

        // ── restate every export over the *symbols* ─────────────────────────
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
            tail_in_funspace.push(Thm::mp(&Thm::mp(&carry, &unfold)?, th)?);
        }
        let in_funspace = tail_in_funspace[0].clone();
        debug_assert_eq!(
            *in_funspace.concl(),
            Formula::mem(fun.clone(), s.fs.of(syms.sum(summands)?, target.clone())),
            "isum::dispatch: in_funspace has the wrong shape"
        );

        let mut folded = Vec::with_capacity(n);
        for (i, th) in beta.iter().enumerate() {
            let at = inst_all(th, std::slice::from_ref(&ta))?;
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
            let unfold =
                crate::eq_symm(env, &inst_all(syms.inj_ax(i)?, std::slice::from_ref(&ta))?)?;
            folded.push(gen_all(&[av], &Thm::mp(&Thm::mp(&carry, &unfold)?, &at)?));
        }

        Some(Dispatch {
            summands: summands.to_vec(),
            target: target.clone(),
            branches,
            tags: syms.sum(summands)?,
            fun,
            in_funspace,
            beta: folded,
            tail_in_funspace,
        })
    }
}
