//! **The per-constructor `good` value** `Gᵢ(p⃗, σ, r)` — §5.2's `G`, specialised
//! to the set level, as one Separation per constructor.
//!
//! # What it is
//!
//! `INDEXED-DESIGN.md` §3.3. With `σ` the tag payload (the plain fields packed
//! into the constructor's telescope) and `r` the row of recursive *good-sets*:
//!
//! ```text
//! ⊢ ∀p⃗ ∀σ ∀r ∀w.  ( w ∈ Gᵢ(p⃗,σ,r)  ↔
//!       ( w ∈ Idx(p⃗)
//!       ∧ ( w = tup(e⃗ᵢ(p⃗, comp₀σ … comp_{kᵢ−1}σ))
//!         ∧ ⋀ⱼ  tup(d⃗ᵢⱼ(p⃗, comp₀σ …)) ∈ app(r, Injⱼ(•)) ) ) )
//! ```
//!
//! i.e. `Gᵢ` is `{tup(e⃗ᵢ)}` when every recursive child is good at the index the
//! declaration demands of it, and `∅` otherwise. The three `ctor` rules of
//! `thesis.txt:1793–1801` map onto the three parts exactly: the base case is
//! the `w = tup(e⃗ᵢ)` conjunct; the `∀y : β` rule is absorbed into `σ` being the
//! telescope tuple — the thesis's `[π₁p′/y][π₂p′/p]` substitutions *are* the
//! `compⱼ` projections; the recursive-argument rule is the `⋀ⱼ … ∈ app(r,…)`
//! conjunct.
//!
//! # The ih-row spelling, settled
//!
//! `INDEXED-DESIGN.md`'s open question 2 asked whether the row needs a second
//! application (`app(app(r, Injⱼ(•)), •)`) or one. **One.** The row this is
//! consumed at is [`crate::wrec_total`]'s composite
//! `comp(goodrec, recfun, finord(mᵢ))`, whose computation rule is
//! `app(comp, b) = app(goodrec, app(recfun, b))` — a single application, and
//! `app(recfun, Injⱼ(•)) = rⱼ`. So `app(r, Injⱼ(•))` *is* `app(goodrec, rⱼ)`,
//! which is the child's good-set, and a second application would be applying a
//! set of index tuples to `•`. The composite's rule is what fixes this; there
//! was never a fork.
//!
//! # Why `w ∈ Idx(p⃗)` is a conjunct and not an afterthought
//!
//! It is what makes `Gᵢ` a Separation **out of a set**, hence a member of
//! `𝒫(Idx(p⃗))` with no hypothesis about `σ` or `r` at all — which is the whole
//! reason [`super::goodstep`]'s `step_typed` comes out unconditional where the
//! value recursor's needs `HYP`. [`GoodValues::in_target`] is that observation,
//! and it is two lines.
//!
//! # Interface
//!
//! ```text
//! Gᵢ(p⃗,σ,r)                                   arity np + 2   [GoodValues::syms]
//! ⊢ ∀p⃗∀σ∀r∀w. (w ∈ Gᵢ(p⃗,σ,r) ↔ (w ∈ Idx(p⃗) ∧ ψᵢ))            [GoodValues::axioms]
//! ⊢ ∀p⃗∀σ∀r. Gᵢ(p⃗,σ,r) ∈ 𝒫(Idx(p⃗))            unconditional  [GoodValues::in_target]
//! ```
//!
//! [`GoodValues::matrix`] rebuilds `ψᵢ` at caller-supplied `σ`, `r` and `w`, so
//! a consumer states exactly the formula the axiom carries.
//!
//! # Nothing here is an axiom
//!
//! `n` Separations ([`crate::funcs::separation_full`], itself derived from
//! Replacement) and `n` [`crate::define_by_membership`]s.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::sigma::Telescope;
use crate::{and_left, conj_of, gen_all, iff_mp, iff_mpr, inst_all, syl};

use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// The `n` `good` values of one indexed declaration.
pub struct GoodValues {
    /// `G₀ … G_{n−1}`, each of arity `np + 2`.
    pub syms: Vec<FnSym>,
    /// Per constructor,
    /// `⊢ ∀p⃗ ∀σ ∀r ∀w. (w ∈ Gᵢ(p⃗,σ,r) ↔ (w ∈ Idx(p⃗) ∧ ψᵢ(w,σ,r)))`.
    pub axioms: Vec<Thm>,
    /// Per constructor, `⊢ ∀p⃗ ∀σ ∀r. Gᵢ(p⃗,σ,r) ∈ 𝒫(Idx(p⃗))` —
    /// **unconditional**, and the reason the `good` recursion is total with no
    /// hypothesis.
    pub in_target: Vec<Thm>,
}

impl GoodValues {
    /// Mint the `n` symbols and derive their axioms.
    ///
    /// `ix` must be [`IndexSpace::build`] over the same `spec` and the same
    /// parameters as `ind` was built at; nothing else ties the terms together.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ix: &IndexSpace,
    ) -> Option<GoodValues> {
        if !spec.well_formed() || spec.indices.is_empty() {
            return None
        }
        let s = &mach.wt.sums;
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let n = spec.len();

        let mut syms = Vec::with_capacity(n);
        let mut axioms = Vec::with_capacity(n);
        let mut in_target = Vec::with_capacity(n);
        for i in 0..n {
            let (sv, rv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
            let (sigma, r, w) = (Term::var(sv), Term::var(rv), Term::var(wv));
            let psi = GoodValues::matrix(mach, spec, i, &ps, &sigma, &r, &w)?;
            let cond = Formula::and(Formula::mem(w.clone(), ix.idx.clone()), psi);

            let existence = crate::funcs::separation_full(
                env,
                wv,
                &GoodValues::matrix(mach, spec, i, &ps, &sigma, &r, &w)?,
                &ix.idx,
                &s.ap.empty_ax,
            )?;
            let mut params = ind.params.clone();
            params.push(sv);
            params.push(rv);
            let (g, g_ax) = crate::define_by_membership(env, &params, &existence, wv, &cond)?;

            // `Gᵢ ⊆ Idx(p⃗)`, hence `Gᵢ ∈ 𝒫(Idx(p⃗))`. The whole of `step_typed`.
            let mut args = ps.clone();
            args.push(sigma.clone());
            args.push(r.clone());
            let g_term = Term::apply(g, args.clone());
            args.push(w.clone());
            let at = inst_all(&g_ax, &args)?;
            let fwd = syl(
                &iff_mp(&at)?,
                &and_left(
                    Formula::mem(w.clone(), ix.idx.clone()),
                    GoodValues::matrix(mach, spec, i, &ps, &sigma, &r, &w)?,
                ),
            )?;
            let sub = Thm::gen(wv, &fwd);
            if *sub.concl() != kernel::thm::subset(env, g_term.clone(), ix.idx.clone()) {
                return None
            }
            let pw = iff_mpr(&inst_all(&s.pow_ax, &[ix.idx.clone(), g_term.clone()])?)?;
            let mem = Thm::mp(&pw, &sub)?;
            if *mem.concl() != Formula::mem(g_term, ix.target.clone()) {
                return None
            }

            syms.push(g);
            axioms.push(g_ax);
            in_target.push(gen_all(&params, &mem));
        }
        Some(GoodValues { syms, axioms, in_target })
    }

    /// `Gᵢ(p⃗, σ, r)` at caller-supplied terms.
    pub fn of(&self, i: usize, ps: &[Term], sigma: &Term, r: &Term) -> Option<Term> {
        let mut a = ps.to_vec();
        a.push(sigma.clone());
        a.push(r.clone());
        Some(Term::apply(*self.syms.get(i)?, a))
    }

    /// `ψᵢ(w, σ, r)` — the axiom's second conjunct, rebuilt at caller-supplied
    /// terms so that a consumer states exactly what the axiom carries.
    #[allow(clippy::too_many_arguments)]
    pub fn matrix(
        mach: &Machine,
        spec: &IndexedDeclSpec,
        i: usize,
        ps: &[Term],
        sigma: &Term,
        r: &Term,
        w: &Term,
    ) -> Option<Formula> {
        conj_of(&GoodValues::matrix_atoms(mach, spec, i, ps, sigma, r, w)?)
    }

    /// `ψᵢ`'s conjuncts as a list: the base-case equality first, then one
    /// membership per recursive argument. [`super::carrier`]'s inversion rule
    /// projects out of exactly this list, so it is the list and not only the
    /// conjunction that is exported.
    #[allow(clippy::too_many_arguments)]
    pub fn matrix_atoms(
        mach: &Machine,
        spec: &IndexedDeclSpec,
        i: usize,
        ps: &[Term],
        sigma: &Term,
        r: &Term,
        w: &Term,
    ) -> Option<Vec<Formula>> {
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ctor = spec.base.ctors.get(i)?;
        // The plain fields, read out of the packed payload: the thesis's
        // `[π₁p′/y][π₂p′/p]`, as terms.
        let comps: Vec<Term> = (0..ctor.args.len())
            .map(|j| Telescope::comp_of(ap, &mach.proj, j, sigma.clone()))
            .collect();

        let mut atoms = vec![Formula::eq(
            w.clone(),
            IndexedDeclSpec::tup(s, &spec.result_vec(i, ps, &comps)?),
        )];
        for j in 0..ctor.recs {
            let child = IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, ps, &comps)?);
            let slot = ap.apply(r.clone(), mach.syms.inj(j, s.point())?);
            atoms.push(Formula::mem(child, slot));
        }
        Some(atoms)
    }
}
