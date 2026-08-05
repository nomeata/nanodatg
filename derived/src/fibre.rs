//! **The fibre family `B` of an inductive declaration** — one set function on
//! the tag set, sending each constructor's tag to **a caller-supplied set**.
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
//! with every summand `1` named as a real symbol.
//!
//! **And this file does not build it.** The fibre values are an *argument*, and
//! nothing here inspects one: `Fibre::new` takes `v₀ … v_{n-1}` as terms, and
//! the codomain, the `n` branches, the dispatcher and all four theorems are
//! stated at whatever it was given. `finord(mᵢ)` reaches this construction only
//! because [`Inductive::build`](crate::inductive::Inductive::build) computes it
//! from [`CtorSpec::recs`](crate::inductive::CtorSpec), which is a `usize`.
//! **That field is where the restriction lives**, and `spec.rs`'s own header
//! says so in as many words. Nothing in this file has to change for a general
//! fibre; that was measured by widening it, not predicted.
//!
//! # The restriction that *is* still here, and it is a different one
//!
//! Each branch of the `rec₊` is a **constant** function `λ_:Aᵢ. vᵢ`, so the
//! fibre of constructor `i` cannot depend on that constructor's own arguments.
//! For a plain recursive argument that is free — the thesis's `p.B` binds `p`
//! and nothing in `Σ(z::γ) + B` mentions it when every `γ` is empty — and it
//! stays free for `RTree.node : (Bool → RTree) → RTree`, whose fibre `⟦Bool⟧`
//! is closed, and for a genuinely infinitary `α → T α`, whose fibre is a
//! *parameter*. It is **not** free for `Acc.intro`, whose second-level
//! telescope depends on the first field.
//!
//! So the two restrictions come apart, and they are not the same size:
//!
//! | restriction | needed for | costs |
//! |---|---|---|
//! | the value is `finord(m)` for a counted `m` | `RTree`, infinitary `α → T α` | the spec, and this file's caller |
//! | the value is **constant** in the fields | `Acc.intro`, a dependent depth-1 fibre | a non-constant branch, hence a codomain `T` that is not a finite union of the values |
//!
//! The second is why `target_of` is a finite union of singletons: with a
//! non-constant branch there is no such set to hand, and the caller would have
//! to supply one. Naming that here is the point — the first restriction is now
//! lifted at this layer and the second is not, and a reader should not have to
//! discover the difference by trying.
//!
//! # And the values are stated over the **parameter telescope**
//!
//! "Nothing inspects a value" is true of the four theorems and false of the
//! construction: each branch is a lambda graph over a *constant body symbol*,
//! and [`define_abbrev`] refuses a body whose free variables are not among its
//! abstraction list. That list used to be one fresh variable, `coᵢ(y) = vᵢ`,
//! so an **open** value — the genuinely infinitary `α → T α`, whose fibre
//! summand is `Σ(z::γ(p⃗))` and mentions the declaration's parameters — was
//! refused outright.
//!
//! [`Fibre::new`] now takes the declaration's parameter telescope `p⃗` and mints
//! `coᵢ(p⃗,y) = vᵢ`, spending [`crate::funcs::lambda_n`],
//! [`crate::funcs::beta_conditional_n`] and [`crate::ext::lam_in_funspace_n`] —
//! the arity-`k+1` siblings of the three helpers, which is exactly the route
//! this header named while it was still undone. **At `np = 0` every symbol is
//! unary again and nothing moves**, because those three are line-for-line the
//! unary ones with an empty prefix.
//!
//! The restriction that remains is the honest one: a value free in a variable
//! the caller did not declare a parameter is still refused, by the same
//! `define_abbrev` guard and for its soundness reason. `tests/fibre.rs` pins
//! both halves at the same value.
//!
//! **What this does not do is place the resulting declaration.** `Σ(z::γ(p⃗))`
//! at a parameter domain is a summand whose `bnd` is *refutable* — take
//! `α := ⟦Nat⟧` — so [`crate::cumul::DeclUniverse`] declines it, and the two
//! corpus exports whose field is `α → T α` now build a carrier and stop
//! there instead. See `mini/src/zoneb.rs`'s `fibre_facts`, which is where that
//! obligation is composed.
//!
//! The thesis's `0_ℓ` base case is `finord(0)`, so a constructor with no
//! recursive arguments is not a special case either.
//!
//! # The construction
//!
//! Given tag summands `A₀ … A_{n-1}` and fibre values `v₀ … v_{n-1}`,
//!
//! ```text
//! T   := {v₀} ∪ ({v₁} ∪ (… ∪ ∅))        a codomain holding every fibre
//! fᵢ  := lamᵢ(p⃗, Aᵢ) = λ_ : Aᵢ. vᵢ        a constant lambda graph
//! B   := rec₊(f₀, rec₊(f₁, … rec₊(f_{n-1}, ∅) … ))
//! ```
//!
//! Every symbol carries `p⃗` in front of its own argument, so `Aᵢ`, `vᵢ` and
//! `T` may all mention the declaration's parameters. The kernel has no
//! term-level substitution, and the symbols *are* it: a client stating the
//! family at other parameter terms applies `lamᵢ` to those instead —
//! [`crate::inductive::carrier_at`] is the one that does.
//!
//! The codomain has to be *some* set containing every fibre before
//! [`crate::sums::Cases`] can type the branches, and the finite union of
//! singletons is the cheapest one. It is [`crate::finset::FinSet`], which also
//! supplies the `n` memberships; it is *not* the least such set and nothing
//! here needs it to be.
//!
//! Each branch is the lambda graph over a constant body symbol, typed by
//! [`crate::ext::lam_in_funspace_n`] — the pattern `derived/src/wlist.rs` had to
//! invent for its one constant fibre on an arbitrary `α`, here used uniformly
//! for all `n` branches. `derived/src/wnat.rs` used one-point graphs instead,
//! which works only because its summands are both `1`; that shortcut does not
//! generalise and is not taken.
//!
//! # Interface
//!
//! ```text
//! ⊢ B ∈ fs(Sum_n(A₀ … A_{n-1}), T)                             [Fibre::in_funspace]
//! ⊢ ∀a. (a ∈ Aᵢ → app(B, Inj_i(a)) = vᵢ)                       [Fibre::fibre[i]]
//! ⊢ vᵢ ∈ T                                                     [Fibre::value_mem[i]]
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
//! `B` is a constant function unless the values differ, so the `n` computation
//! rules say `n` different things only if the `vᵢ` are different sets.
//! They are, and `tests/fibre.rs` pins it:
//! [`ISumSyms::inj_distinct`](crate::isum::ISumSyms::inj_distinct) makes
//! `finord(m)` have exactly `m` visibly distinct elements, so `finord(0)`,
//! `finord(1)` and `finord(2)` are pairwise distinct, and a declaration whose
//! constructors branch differently gets a genuinely non-constant `B`.
//!
//! # Nothing here is an axiom
//!
//! `n` constant-body [`crate::define_abbrev`]s, `n` lambda graphs
//! ([`crate::funcs::lambda_n`], one Replacement each) and one
//! [`crate::isum::Dispatch`]. No new axiom.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::finset::FinSet;
use crate::isum::{dispatch_of, Dispatch, ISumSyms};
use crate::recursion::hyp::hyp_eq_trans;
use crate::sums::{Cases, Sums};
use crate::{a1i, define_abbrev, eq_symm, gen_all, inst_all};

/// The fibre family of a declaration, at concrete tag summands.
pub struct Fibre {
    /// The declaration's parameter variables `p⃗`, in order — the abstraction
    /// list every symbol below carries in front of its own argument, and the
    /// variables the values, the summands and the family are stated *at*.
    ///
    /// Empty for a closed declaration, where every symbol is unary and this is
    /// [`crate::funcs::lambda`]'s shape exactly.
    pub params: Vec<FreeVar>,
    /// The tag summands `A₀ … A_{n-1}`.
    pub summands: Vec<Term>,
    /// `Sum_n(A₀ … A_{n-1})`.
    pub tags: Term,
    /// The fibre value `vᵢ` of each constructor — whatever the caller supplied.
    pub values: Vec<Term>,
    /// `{v₀} ∪ ({v₁} ∪ (… ∪ ∅))` — the codomain.
    pub target: Term,
    /// `⊢ vᵢ ∈ T`.
    pub value_mem: Vec<Thm>,
    /// The constant body symbols, `coᵢ(p⃗,y) = vᵢ` — arity `np + 1`.
    pub co: Vec<FnSym>,
    /// The lambda-graph symbols, `lamᵢ(p⃗,A) = {⟨y, coᵢ(p⃗,y)⟩ : y ∈ A}` — arity
    /// `np + 1`.
    pub lam: Vec<FnSym>,
    /// `fᵢ = lamᵢ(p⃗,Aᵢ)`, the constant function on the `i`-th summand.
    pub branches: Vec<Term>,
    /// `⊢ fᵢ ∈ fs(Aᵢ, T)`.
    pub branch_fs: Vec<Thm>,
    /// The fibre family `B` itself.
    pub fam: Term,
    /// `⊢ B ∈ fs(Sum_n(A⃗), T)`.
    pub in_funspace: Thm,
    /// `⊢ ∀a. (a ∈ Aᵢ → app(B, Inj_i(a)) = vᵢ)`.
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

    /// Build the fibre family from a declaration's **fibre values**.
    ///
    /// `params` is the declaration's parameter telescope `p⃗` — the variables
    /// the summands and the values may mention, and the abstraction list every
    /// symbol below is minted over. `summands[i]` is the `i`-th constructor's
    /// tag type — its non-recursive arguments packed by
    /// [`crate::sigma::Telescope`], or `1` when it has none — and `values[i]`
    /// is the set that constructor's tag is sent to. `empty_fun` must be
    /// [`crate::wtype::empty_is_a_function`] and `app_pair`
    /// [`crate::ext::app_of_pair`], both over the same [`Sums`].
    ///
    /// **The values are arbitrary sets over `p⃗`.** Nothing here inspects one,
    /// so a caller may pass `finord(mᵢ)` (which is what
    /// [`Inductive::build`](crate::inductive::Inductive::build) does at a plain
    /// constructor, because [`CtorSpec::recs`](crate::inductive::CtorSpec) is a
    /// count), a named closed set, `Sum_m(Σ(z::γ(p⃗)))` — which mentions `p⃗`
    /// and is why the list exists — or anything else. See the header for where
    /// the restriction actually lives now.
    ///
    /// `None` if `values` and `summands` differ in length, or if some value has
    /// a free variable outside `params`, which
    /// [`define_abbrev`] refuses.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        s: &Sums,
        cases: &Cases,
        syms: &ISumSyms,
        params: &[FreeVar],
        summands: &[Term],
        values: &[Term],
        empty_fun: &Thm,
        app_pair: &Thm,
    ) -> Option<Fibre> {
        let n = summands.len();
        if values.len() != n {
            return None
        }
        let ap = &s.ap;
        let values = values.to_vec();
        let target = target_of(s, &values);
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        // `[p⃗, x]` — the argument list every symbol below takes, and the only
        // thing that changes between the closed case and the parameterised one.
        let args_at = |x: Term| {
            let mut v = ps.clone();
            v.push(x);
            v
        };

        // ── `vᵢ ∈ T`, walking out of the union chain ────────────────────────
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
            let abs: Vec<FreeVar> =
                params.iter().copied().chain(std::iter::once(yv)).collect();
            let (co_i, co_ax_i) = define_abbrev(env, &abs, &values[i])?;
            let (lam_i, lam_ax_i) = crate::funcs::lambda_n(env, ap, co_i)?;
            let beta_i = crate::funcs::beta_conditional_n(env, ap, co_i, lam_i, &lam_ax_i)?;
            let rule =
                crate::ext::lam_in_funspace_n(env, ap, &s.prod, &s.fs, co_i, lam_i, &lam_ax_i)?;

            // `body_in_n(p⃗,Aᵢ,T) = ∀x. (x ∈ Aᵢ → coᵢ(p⃗,x) ∈ T)`, from `vᵢ ∈ T`
            // backwards along `coᵢ(p⃗,x) = vᵢ`.
            let xv = env.fresh_var();
            let tx = Term::var(xv);
            let co_x = inst_all(&co_ax_i, &args_at(tx.clone()))?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                values[i].clone(),
                Term::apply(co_i, args_at(tx.clone())),
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
                crate::ext::body_in_n(env, co_i, &ps, &summands[i], &target),
                "fibre: the constant body's typing has the wrong shape"
            );
            let mut rule_args = args_at(summands[i].clone());
            rule_args.push(target.clone());
            let fs_i = Thm::mp(&inst_all(&rule, &rule_args)?, &body)?;
            branches.push(Term::apply(lam_i, args_at(summands[i].clone())));
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
            let mut beta_args = args_at(summands[i].clone());
            beta_args.push(ta.clone());
            let e2 = inst_all(&co_beta[i], &beta_args)?;
            let e3 = a1i(
                &inst_all(&co_ax[i], &args_at(ta.clone()))?,
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
            params: params.to_vec(),
            summands: summands.to_vec(),
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
