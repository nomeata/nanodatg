//! **The fibre family `B` of an inductive declaration** — one set function on
//! the tag set, sending each constructor's tag to the finite ordinal of its
//! recursive-argument count.
//!
//! # What the thesis asks for
//!
//! §5.2's `spec` judgment produces `A; B; G` together, and the `B` component is
//! assembled by iterated `rec₊` over the constructor list
//! (`thesis.txt:1789–1791`):
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ 0 spec ⇒ 0; rec0; rec0
//! Γ; t : F ⊢ (c : β) + K spec ⇒ A₁ + A;  rec₊ (λp.B₁) B;  …
//! ```
//!
//! and each constructor's own `B₁` is built by the `ctor` rules: `0_ℓ` at the
//! base (`:1793`) and, per **recursive** argument (`:1800`),
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ (∀z :: γ. t e) → τ ctor ⇒ A; p. Σ(z :: γ) + B;  …
//! ```
//!
//! For a *plain* recursive argument the telescope `γ` is empty, so `Σ(z::γ)` is
//! `1` and the clause is `1 + B`. A constructor with `m` recursive arguments
//! therefore gets `1 + (1 + (… + 0))` with `m` copies — the finite ordinal `m`.
//! **So "finite-ordinal fibres" is not a primitive to build**: it is
//! [`ISumSyms::finord`](crate::isum::ISumSyms::finord), the iterated binary sum
//! with every summand `1` named as a real symbol, and
//! that is the whole content of this observation.
//!
//! Two consequences worth stating, because they are what make this file short.
//! The fibre of a plain (non-nested, non-indexed) constructor does **not**
//! depend on the constructor's arguments — the thesis's `p.B` binds `p` but
//! nothing in `Σ(z::γ) + B` mentions it when every `γ` is empty — so each
//! branch of the `rec₊` is a *constant* function. And the thesis's `0_ℓ` base
//! case is `finord(0)`, so a constructor with no recursive arguments is not a
//! special case either.
//!
//! # The construction
//!
//! Given tag summands `A₀ … A_{n-1}` and counts `m₀ … m_{n-1}`,
//!
//! ```text
//! vᵢ  := finord(mᵢ)                     the symbol Sum_{mᵢ}(1,…,1);
//!                                       unfolds to 1 + (1 + (… + 0)), mᵢ copies
//! T   := {v₀} ∪ ({v₁} ∪ (… ∪ ∅))        a codomain holding every fibre
//! fᵢ  := λ_ : Aᵢ. vᵢ                    a constant lambda graph
//! B   := rec₊(f₀, rec₊(f₁, … rec₊(f_{n-1}, ∅) … ))
//! ```
//!
//! The codomain has to be *some* set containing every fibre before
//! [`crate::sums::Cases`] can type the branches, and the finite union of
//! singletons is the cheapest one. It is [`crate::finset::FinSet`], which also
//! supplies the `n` memberships; it is *not* the least such set and nothing
//! here needs it to be.
//!
//! Each branch is the lambda graph over a constant body symbol, typed by
//! [`crate::ext::lam_in_funspace`] — the pattern `derived/src/wlist.rs` had to
//! invent for its one constant fibre on an arbitrary `α`, here used uniformly
//! for all `n` branches. `derived/src/wnat.rs` used one-point graphs instead,
//! which works only because its summands are both `1`; that shortcut does not
//! generalise and is not taken.
//!
//! # Interface
//!
//! ```text
//! ⊢ B ∈ fs(Sum_n(A₀ … A_{n-1}), T)                             [Fibre::in_funspace]
//! ⊢ ∀a. (a ∈ Aᵢ → app(B, Inj_i(a)) = finord(mᵢ))               [Fibre::fibre[i]]
//! ⊢ finord(mᵢ) ∈ T                                             [Fibre::value_mem[i]]
//! ⊢ ∀a. (a ∈ Sum_n(A⃗) → app(B,a) ∈ T)                          [Fibre::values_in_target]
//! ```
//!
//! All unconditional at the caller's own summand terms — which may be open, so
//! a parameterised declaration's `α` stays a free variable exactly as it does
//! in `wlist.rs`. The last one is what a bound obligation
//! `∀a ∈ A. app(B,a) ∈ U(c)` reduces to, and it costs nothing beyond
//! [`crate::ext::funspace_app_mem`] applied to the first.
//!
//! # Non-vacuity
//!
//! `B` is a constant function unless the counts differ, so the `n` computation
//! rules say `n` different things only if the `finord(mᵢ)` are different sets.
//! They are, and `tests/fibre.rs` pins it:
//! [`ISumSyms::inj_distinct`](crate::isum::ISumSyms::inj_distinct) makes
//! `finord(m)` have exactly `m` visibly distinct elements, so `finord(0)`,
//! `finord(1)` and `finord(2)` are pairwise distinct, and a declaration whose
//! constructors branch differently gets a genuinely non-constant `B`.
//!
//! # Nothing here is an axiom
//!
//! `n` constant-body [`crate::define_abbrev`]s, `n` lambda graphs
//! ([`crate::funcs::lambda`], one Replacement each) and one
//! [`crate::isum::Dispatch`]. No new axiom.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::finset::FinSet;
use crate::isum::{dispatch_of, Dispatch, ISumSyms};
use crate::recursion::hyp::hyp_eq_trans;
use crate::sums::{Cases, Sums};
use crate::{a1i, define_abbrev, eq_symm, gen_all, inst_all};

/// The fibre family of a declaration, at concrete tag summands.
pub struct Fibre {
    /// The tag summands `A₀ … A_{n-1}`.
    pub summands: Vec<Term>,
    /// The recursive-argument counts `m₀ … m_{n-1}`.
    pub counts: Vec<usize>,
    /// `Sum_n(A₀ … A_{n-1})`.
    pub tags: Term,
    /// `finord(mᵢ)` for each constructor.
    pub values: Vec<Term>,
    /// `{v₀} ∪ ({v₁} ∪ (… ∪ ∅))` — the codomain.
    pub target: Term,
    /// `⊢ finord(mᵢ) ∈ T`.
    pub value_mem: Vec<Thm>,
    /// The constant body symbols, `coᵢ(y) = finord(mᵢ)`.
    pub co: Vec<FnSym>,
    /// The lambda-graph symbols, `lamᵢ(A) = {⟨y, coᵢ(y)⟩ : y ∈ A}`.
    pub lam: Vec<FnSym>,
    /// `fᵢ = lamᵢ(Aᵢ)`, the constant function on the `i`-th summand.
    pub branches: Vec<Term>,
    /// `⊢ fᵢ ∈ fs(Aᵢ, T)`.
    pub branch_fs: Vec<Thm>,
    /// The fibre family `B` itself.
    pub fam: Term,
    /// `⊢ B ∈ fs(Sum_n(A⃗), T)`.
    pub in_funspace: Thm,
    /// `⊢ ∀a. (a ∈ Aᵢ → app(B, Inj_i(a)) = finord(mᵢ))`.
    pub fibre: Vec<Thm>,
    /// `⊢ ∀a. (a ∈ Sum_n(A⃗) → app(B,a) ∈ T)`.
    pub values_in_target: Thm,
    /// The underlying dispatcher, for a caller that needs its tails.
    pub dispatch: Dispatch,
}

/// The codomain `{v₀} ∪ ({v₁} ∪ (… ∪ ∅))`; the empty list gives `∅`.
pub fn target_of(s: &Sums, values: &[Term]) -> Term { FinSet::of(s, values) }

impl Fibre {
    /// The fibre family term, for a caller that wants to mention it before
    /// proving anything.
    pub fn fam_of(s: &Sums, cases: &Cases, summands: &[Term], branches: &[Term], target: &Term) -> Term {
        dispatch_of(s, cases, summands, target, branches)
    }

    /// Build the fibre family from a declaration's recursive-argument counts.
    ///
    /// `summands[i]` is the `i`-th constructor's tag type — its non-recursive
    /// arguments packed by [`crate::sigma::Telescope`], or `1` when it has
    /// none — and `counts[i]` is its number of recursive arguments.
    /// `empty_fun` must be [`crate::wtype::empty_is_a_function`] and
    /// `app_pair` [`crate::ext::app_of_pair`], both over the same [`Sums`].
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        s: &Sums,
        cases: &Cases,
        syms: &ISumSyms,
        summands: &[Term],
        counts: &[usize],
        empty_fun: &Thm,
        app_pair: &Thm,
    ) -> Option<Fibre> {
        let n = summands.len();
        if counts.len() != n {
            return None
        }
        let ap = &s.ap;
        let values: Vec<Term> = counts.iter().map(|m| syms.finord(s, *m)).collect::<Option<_>>()?;
        let target = target_of(s, &values);

        // ── `finord(mᵢ) ∈ T`, walking out of the union chain ────────────────
        let fin = FinSet::new(env, s)?;
        let value_mem: Vec<Thm> =
            (0..n).map(|i| fin.mem(s, &values, i)).collect::<Option<_>>()?;
        debug_assert!(
            value_mem
                .iter()
                .enumerate()
                .all(|(i, th)| *th.concl() == Formula::mem(values[i].clone(), target.clone())),
            "fibre: value_mem has the wrong shape"
        );

        // ── The `n` constant branches, as lambda graphs ─────────────────────
        let mut co = Vec::with_capacity(n);
        let mut lam = Vec::with_capacity(n);
        let mut co_beta = Vec::with_capacity(n);
        let mut co_ax = Vec::with_capacity(n);
        let mut branches = Vec::with_capacity(n);
        let mut branch_fs = Vec::with_capacity(n);
        for i in 0..n {
            let yv = env.fresh_var();
            let (co_i, co_ax_i) = define_abbrev(env, &[yv], &values[i])?;
            let (lam_i, lam_ax_i) = crate::funcs::lambda(env, ap, co_i)?;
            let beta_i = crate::funcs::beta_conditional(env, ap, co_i, lam_i, &lam_ax_i)?;
            let rule = crate::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, co_i, lam_i, &lam_ax_i)?;

            // `body_in(Aᵢ,T) = ∀x. (x ∈ Aᵢ → coᵢ(x) ∈ T)`, from `vᵢ ∈ T`
            // backwards along `coᵢ(x) = vᵢ`.
            let xv = env.fresh_var();
            let tx = Term::var(xv);
            let co_x = inst_all(&co_ax_i, std::slice::from_ref(&tx))?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                values[i].clone(),
                Term::apply(co_i, vec![tx.clone()]),
                hole,
                Formula::mem(Term::var(hole), target.clone()),
            );
            let at_x = Thm::mp(&Thm::mp(&carry, &eq_symm(env, &co_x)?)?, &value_mem[i])?;
            let body = Thm::gen(
                xv,
                &a1i(&at_x, Formula::mem(tx.clone(), summands[i].clone())),
            );
            debug_assert_eq!(
                *body.concl(),
                crate::ext::body_in(env, co_i, &summands[i], &target),
                "fibre: the constant body's typing has the wrong shape"
            );
            let fs_i = Thm::mp(
                &inst_all(&rule, &[summands[i].clone(), target.clone()])?,
                &body,
            )?;
            branches.push(Term::apply(lam_i, vec![summands[i].clone()]));
            branch_fs.push(fs_i);
            co.push(co_i);
            lam.push(lam_i);
            co_beta.push(beta_i);
            co_ax.push(co_ax_i);
        }

        // ── The dispatcher, and the `n` fibre equations ─────────────────────
        let typed: Vec<(Term, Thm)> =
            branches.iter().cloned().zip(branch_fs.iter().cloned()).collect();
        let dispatch = Dispatch::new(env, s, cases, syms, summands, &target, &typed, empty_fun)?;
        let fam = dispatch.fun.clone();

        let av = env.fresh_var();
        let ta = Term::var(av);
        let mut fibre = Vec::with_capacity(n);
        for i in 0..n {
            let e1 = inst_all(&dispatch.beta[i], std::slice::from_ref(&ta))?;
            let e2 = inst_all(&co_beta[i], &[summands[i].clone(), ta.clone()])?;
            let e3 = a1i(
                &inst_all(&co_ax[i], std::slice::from_ref(&ta))?,
                Formula::mem(ta.clone(), summands[i].clone()),
            );
            let head = hyp_eq_trans(env, &e1, &e2)?;
            let chain = hyp_eq_trans(env, &head, &e3)?;
            // The claim this struct exists to make: the fibre at **the `i`-th
            // injection**, at the caller's own value. A wrong index or a
            // foreign `syms` would still compose — `Dispatch` release-checks
            // its own joins, but a header should not hold by another module's
            // discipline — so this is a check and not an assertion.
            if !chain.hyps().is_empty()
                || *chain.concl()
                    != Formula::imp(
                        Formula::mem(ta.clone(), summands[i].clone()),
                        Formula::eq(
                            ap.apply(fam.clone(), syms.inj(i, ta.clone())?),
                            values[i].clone(),
                        ),
                    )
            {
                return None
            }
            fibre.push(gen_all(&[av], &chain));
        }

        // ── `∀a ∈ tags. app(B,a) ∈ T`, straight off the typing rule ─────────
        let values_in_target = {
            let rule = crate::ext::funspace_app_mem(env, ap, &s.prod, &s.fs, app_pair)?;
            let at = inst_all(
                &rule,
                &[syms.sum(summands)?, target.clone(), fam.clone(), ta.clone()],
            )?;
            let curried = crate::uncurry(&at)?;
            gen_all(&[av], &Thm::mp(&curried, &dispatch.in_funspace)?)
        };
        debug_assert_eq!(
            *values_in_target.concl(),
            Formula::forall(
                av,
                Formula::imp(
                    Formula::mem(ta.clone(), syms.sum(summands)?),
                    Formula::mem(ap.apply(fam.clone(), ta.clone()), target.clone()),
                )
            ),
            "fibre: values_in_target has the wrong shape"
        );

        Some(Fibre {
            summands: summands.to_vec(),
            counts: counts.to_vec(),
            tags: syms.sum(summands)?,
            values,
            target,
            value_mem,
            co,
            lam,
            branches,
            branch_fs,
            fam,
            in_funspace: dispatch.in_funspace.clone(),
            fibre,
            values_in_target,
            dispatch,
        })
    }
}
