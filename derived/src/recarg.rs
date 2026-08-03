//! **A constructor's recursive-argument function** — the set function out of the
//! fibre `finord(m)` that hands back the `m` recursive arguments.
//!
//! # What the thesis asks for
//!
//! §5.2's recursive-argument rule (`thesis.txt:1800`) gives a constructor with
//! `m` plain recursive arguments the fibre `1 + (1 + (… + 0))` — the finite
//! ordinal `m`, which is [`ISumSyms::finord`](crate::isum::ISumSyms::finord)
//! and is what
//! [`crate::fibre`] puts on the tag. The W-type's `sup` rule then wants the
//! constructor's second component to be a function
//!
//! ```text
//! f(r₀ … r_{m-1}) ∈ fs(finord(m), carrier)      with  f(r⃗)(Inj_j •) = r_j
//! ```
//!
//! For `m = 1` and a fibre written literally as `1 = {•}` that function is the
//! one-point graph `{⟨•, r₀⟩}`, which is what `derived/src/wnat.rs` and
//! `wlist.rs` use. **That does not survive the general case**, and for two
//! independent reasons: `finord(1)` is `Sum_1(1)`, which unfolds to `1 + 0` and
//! whose single element is `Inj_0(•) = ⟨∅,•⟩` and not `•`, so the domain is not
//! the singleton
//! [`crate::point_fun`] produces; and `m ≥ 2` is not a one-point graph at all.
//!
//! # The construction: a dispatcher, with the elements as their own codomain
//!
//! The function is a [`crate::isum::Dispatch`] over `m` copies of `1`, whose
//! `j`-th branch is the one-point graph `{⟨•, r_j⟩}`:
//!
//! ```text
//! f(r⃗) := case(1, …, R, {⟨•,r₀⟩}, case(1, …, R, {⟨•,r₁⟩}, … ∅ …))
//! ```
//!
//! The one thing that is not obvious is **what `R` should be**.
//! [`Dispatch::new`](crate::isum::Dispatch::new) takes the branch typings as
//! *inputs* and requires them **unconditional**, whereas `{⟨•,r_j⟩} ∈ fs(1, S)`
//! needs `r_j ∈ S` — a hypothesis, and precisely the one the constructor's
//! typing rule is trying to prove something under. Taking
//!
//! ```text
//! R := fin(r₀ … r_{m-1}) = {r₀} ∪ ({r₁} ∪ (… ∪ ∅))
//! ```
//!
//! makes every branch typing unconditional, because `r_j ∈ R` holds *by
//! construction* ([`crate::finset::FinSet::mem`]). The real codomain is then
//! reached in one step by [`Wtype::fs_mono`](crate::wtype::Wtype::fs_mono),
//! whose premise `R ⊆ S` is [`crate::finset::FinSet::subset`] — and *that* is
//! where the `m` hypotheses `r_j ∈ S` land, all at once. So the hypothesis is
//! paid exactly once, in the inclusion, instead of `m` times inside the
//! dispatcher.
//!
//! # Interface
//!
//! [`RecArg::new`] builds the function at `m` fresh variables `r⃗` and one fresh
//! codomain variable `S`, and derives
//!
//! ```text
//! ⊢ ∀S ∀r₀ … ∀r_{m-1}. ((r₀ ∈ S ∧ (… ∧ r_{m-1} ∈ S)) → f(r⃗) ∈ fs(finord(m), S))   [RecArg::in_funspace]
//! ⊢ ∀r₀ … ∀r_{m-1}. app(f(r⃗), Inj_j(•)) = r_j                                     [RecArg::app[j]]
//! ```
//!
//! At `m = 0` the function is `∅`, the antecedent is empty and
//! [`RecArg::in_funspace`] degenerates to `⊢ ∀S. ∅ ∈ fs(0, S)` — which is
//! [`crate::wtype::empty_is_a_function`] verbatim, so the nullary constructor is
//! not a special case of the *construction*, only of the bookkeeping. The
//! computation rules are **unconditional**: they are what makes the function
//! injective in `r⃗` and hence what makes a constructor injective in its
//! recursive arguments.
//!
//! [`RecArg::of`] is the term at caller-supplied arguments.
//!
//! # Generalising to a function-typed field — the two decisions, settled
//!
//! `#37` step 2 replaces the `m` copies of `1` with arbitrary summands `A⃗` and
//! the one-point graphs with *functions* `g⃗`. Two things had to be decided
//! before writing it, and both are measurements rather than preferences.
//!
//! ## What survives of injectivity
//!
//! [`RecArg::app`] is unconditional, and that is what
//! [`crate::inductive::distinct`]'s `ctor_injective` spends: it instantiates
//! `app[j]` at **both** argument lists to compute both sides of an equation
//! between constructor applications. The general form **cannot** be
//! unconditional — computing `app(f(g⃗), Inj_j z)` at all needs `gⱼ` to be a
//! function, which is the caller's hypothesis and not a fact
//! ([`crate::isum::dispatch`]'s header has the general statement of why). So:
//!
//! * **`ctors_distinct` is untouched.** It reads only the *tag* half of the
//!   Kuratowski pair and refutes it with
//!   [`inj_distinct`](crate::isum::ISumSyms::inj_distinct); it never spends
//!   `app`, and it explicitly does not care whether the arguments are well
//!   typed.
//! * **`ctor_injective` gains typing antecedents** — `gⱼ ∈ fs(Aⱼ,W)` for both
//!   sides — because today's statement quantifies *arbitrary* arguments and the
//!   general computation rule does not hold at arbitrary ones.
//! * **Nothing consumes the unconditional form.** `mini` reaches
//!   [`Inductive::distinct`](crate::inductive::Inductive) at two sites and
//!   `ctor_injective` at none, so the weakening costs no consumer. That was
//!   checked before the change rather than after.
//!
//! At `γ = ∅` the antecedent is dischargeable outright — the branches are
//! one-point graphs and typed by construction — so the degenerate rule keeps
//! its present strength.
//!
//! ## The codomain, and why `⋃⋃g` is not one
//!
//! The dispatcher's *term* mentions its codomain, so a general variant cannot
//! take `S`: a constructor term would then mention a set that is not part of
//! the constructor's data. It has to be built from the branches, as
//! `FinSet::of(r⃗)` is below.
//!
//! [`snd_in_union2`](crate::funcs::snd_in_union2) is `⟨a,y⟩ ∈ f → y ∈ ⋃⋃f` and
//! looks like the answer. **It is not.** `⟨a,y⟩` is `{{a},{a,y}}`, so `⋃⋃f`
//! contains the *domain* elements as well as the values, and `⋃⋃gⱼ ⊆ W` is
//! therefore false whenever the fibre `Aⱼ` is not itself inside the carrier —
//! which is the whole point of a general fibre. So a genuine **range** is
//! forced: `ran(g) := { y ∈ ⋃⋃g : ∃a. ⟨a,y⟩ ∈ g }`, one
//! [`separation_full`](crate::funcs::separation_full) over that superset, plus
//! `ran g ⊆ S` and `g ∈ fs(A,S) → g ∈ fs(A, ran g)`. A small module, on the
//! scale of [`crate::finset`], but a new one.
//!
//! ## And it must not be the codomain at `γ = ∅`
//!
//! `ran(PointFun(•,r))` is `{r}` as a *set* and not as a *term*, so a
//! `ran`-based codomain would change the degenerate dispatcher's term — and
//! with it every constructor term in the project. The resolution is the one
//! [`fibre_values`](crate::inductive::carrier::fibre_values) already uses for
//! `Σ(z::∅)`: **one rule, two spellings of one set, chosen by normal form.**
//! The term-former takes the codomain as a parameter; the degenerate entry
//! point supplies `FinSet::of(r⃗)` and the general one `⋃ⱼ ran(gⱼ)`. That keeps
//! `γ = ∅` term-identical, which is the property every step of `#37` has been
//! kept on.
//!
//! # Non-vacuity
//!
//! [`RecArg::in_funspace`] alone would be satisfied by `f := ∅` for every `m`.
//! [`RecArg::app`] rules that out: at `m ≥ 1` it says `f(r⃗)` *computes*, at `m`
//! visibly distinct points
//! ([`ISumSyms::inj_distinct`](crate::isum::ISumSyms::inj_distinct)), to `m`
//! values the
//! caller chose. `tests/recarg.rs` pins both and checks that `f(r₀,r₁)` at
//! `m = 2` returns each argument at its own point.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::isum::Dispatch`], `m` one-point graphs
//! ([`crate::point_fun`]), one [`crate::finset::FinSet`] and one
//! [`Wtype::fs_mono`](crate::wtype::Wtype::fs_mono). No new symbol.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::finset::FinSet;
use crate::isum::{dispatch_of, Dispatch, ISumSyms};
use crate::point_fun::PointFun;
use crate::sums::{Cases, Sums};
use crate::{a1i, conj_of, eq_trans, gen_all, hyp_and, inst_all, syl};

/// A constructor's recursive-argument function, at `m` quantified arguments.
pub struct RecArg {
    /// The number of recursive arguments.
    pub m: usize,
    /// The quantified codomain variable `S`.
    pub target: FreeVar,
    /// The `m` quantified argument variables `r₀ … r_{m-1}`.
    pub vars: Vec<FreeVar>,
    /// The fibre `finord(m)` this function's domain is.
    pub domain: Term,
    /// `f(r⃗)` at [`RecArg::vars`].
    pub fun: Term,
    /// `⊢ ∀S ∀r⃗. ((r₀ ∈ S ∧ (… ∧ r_{m-1} ∈ S)) → f(r⃗) ∈ fs(finord(m), S))`,
    /// and at `m = 0` the antecedent-free `⊢ ∀S. ∅ ∈ fs(0, S)`.
    pub in_funspace: Thm,
    /// For each `j < m`: `⊢ ∀r⃗. app(f(r⃗), Inj_j(•)) = r_j` — **unconditional**.
    pub app: Vec<Thm>,
    /// The underlying dispatcher, absent at `m = 0`.
    pub dispatch: Option<Dispatch>,
}

impl RecArg {
    /// The term `f(r⃗)` at caller-supplied recursive arguments; the empty list
    /// gives `∅`.
    pub fn of(s: &Sums, cases: &Cases, args: &[Term]) -> Term {
        let branches: Vec<Term> =
            args.iter().map(|r| PointFun::of(s, s.point(), r.clone())).collect();
        dispatch_of(s, cases, &vec![s.unit(); args.len()], &FinSet::of(s, args), &branches)
    }

    /// Build the function at `m` fresh arguments and derive its typing rule and
    /// its `m` computation rules.
    ///
    /// `pf` must be the [`PointFun`] and `cases` the [`Cases`] over the same
    /// [`Sums`]; `fs_mono` is
    /// [`Wtype::fs_mono`](crate::wtype::Wtype::fs_mono) and `empty_fun`
    /// [`crate::wtype::empty_is_a_function`], both checked rather than assumed
    /// by the shapes they are used at.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        s: &Sums,
        cases: &Cases,
        syms: &ISumSyms,
        pf: &PointFun,
        fin: &FinSet,
        fs_mono: &Thm,
        empty_fun: &Thm,
        m: usize,
    ) -> Option<RecArg> {
        let point = s.point();
        let domain = syms.finord(s, m)?;
        let sv = env.fresh_var();
        let ts = Term::var(sv);
        let vars: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
        let rs: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();

        if m == 0 {
            let fun = RecArg::of(s, cases, &rs);
            debug_assert_eq!(fun, s.zero(), "recarg: the empty function is not ∅");
            debug_assert_eq!(
                *empty_fun.concl(),
                Formula::forall(sv, Formula::mem(s.zero(), s.fs.of(s.zero(), ts.clone()))),
                "recarg: empty_fun is not ⊢ ∀S. ∅ ∈ fs(0,S)"
            );
            // `finord(0)` is the symbol `Sum_0()`, not the term `∅`, so even
            // the degenerate case is restated over the symbol.
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                s.zero(),
                domain.clone(),
                hole,
                Formula::mem(s.zero(), s.fs.of(Term::var(hole), ts.clone())),
            );
            let fold = crate::eq_symm(env, &inst_all(syms.sum_ax(0)?, &[])?)?;
            let at = Thm::mp(
                &Thm::mp(&carry, &fold)?,
                &inst_all(empty_fun, std::slice::from_ref(&ts))?,
            )?;
            return Some(RecArg {
                m,
                target: sv,
                vars,
                domain,
                fun,
                in_funspace: gen_all(&[sv], &at),
                app: Vec::new(),
                dispatch: None,
            })
        }

        // ── the dispatcher, over the arguments' own finite set ──────────────
        let codomain = FinSet::of(s, &rs);
        let summands = vec![s.unit(); m];
        let mut typed: Vec<(Term, Thm)> = Vec::with_capacity(m);
        for j in 0..m {
            let g = PointFun::of(s, point.clone(), rs[j].clone());
            let fs_j = Thm::mp(
                &inst_all(&pf.in_fs, &[point.clone(), rs[j].clone(), codomain.clone()])?,
                &fin.mem(s, &rs, j)?,
            )?;
            typed.push((g, fs_j));
        }
        let d = Dispatch::new(env, s, cases, syms, &summands, &codomain, &typed, empty_fun)?;
        let fun = d.fun.clone();
        debug_assert_eq!(fun, RecArg::of(s, cases, &rs), "recarg: the term builder disagrees");

        // ── the `m` computation rules, unconditional ────────────────────────
        let mut app = Vec::with_capacity(m);
        for (j, r) in rs.iter().enumerate() {
            let at_point = Thm::mp(
                &inst_all(&d.beta[j], std::slice::from_ref(&point))?,
                &s.unit_mem,
            )?;
            let value = inst_all(&pf.app, &[point.clone(), r.clone()])?;
            let chain = eq_trans(env, &at_point, &value)?;
            debug_assert_eq!(
                *chain.concl(),
                Formula::eq(
                    s.ap.apply(fun.clone(), syms.inj(j, point.clone())?),
                    r.clone()
                ),
                "recarg: the computation rule has the wrong shape"
            );
            app.push(gen_all(&vars, &chain));
        }

        // ── the typing rule, widened from `fin(r⃗)` to an arbitrary `S` ──────
        let atoms: Vec<Formula> =
            rs.iter().map(|r| Formula::mem(r.clone(), ts.clone())).collect();
        let h = conj_of(&atoms)?;
        let sub = fin.subset(env, s, &rs, &ts)?;
        let mono = inst_all(
            fs_mono,
            &[domain.clone(), codomain.clone(), ts.clone(), fun.clone()],
        )?;
        let widened = syl(&hyp_and(&a1i(&d.in_funspace, h.clone()), &sub)?, &mono)?;
        debug_assert_eq!(
            *widened.concl(),
            Formula::imp(h, Formula::mem(fun.clone(), s.fs.of(domain.clone(), ts.clone()))),
            "recarg: in_funspace has the wrong shape"
        );
        let mut quant = vec![sv];
        quant.extend(vars.iter().copied());

        Some(RecArg {
            m,
            target: sv,
            vars,
            domain,
            fun,
            in_funspace: gen_all(&quant, &widened),
            app,
            dispatch: Some(d),
        })
    }
}
