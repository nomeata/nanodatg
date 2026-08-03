//! **The general recursor**, packaged — `grec(p⃗, s⃗, T)` and the four theorem
//! schemas (S1)–(S4), derived from declaration data alone.
//!
//! # What this is
//!
//! The layer between the carrier machine ([`super::carrier`]) and
//! [`crate::wrec_total`]: the W-recursor is arity-blind and already general,
//! the carrier is already general, and what was still hand-written per
//! inductive (`wnat_rec`, `wlist_rec`) was only the packed step and the
//! discharge of the recursor's hypotheses. This module builds both from the
//! [`super::DeclSpec`], so
//!
//! ```text
//! grec(p⃗, s⃗, T) := wrec(A, B, U({A,T'}), T, e(p⃗, s⃗, T))
//! ```
//!
//! exists — with its ι rules — at whatever arity the declaration has.
//!
//! # Interface
//!
//! Writing `HYP` for [`super::premise`]'s pointwise bundle and `Hᵢ^ctor` for
//! the constructor's own argument typings:
//!
//! ```text
//! (S1) ⊢ ∀p⃗ ∀s⃗ ∀T ∀σ ∀f ∀r. ((σ ∈ Aᵢ ∧ (f ∈ FWᵢ ∧ r ∈ FTᵢ)) →
//!          app(e, ⟨Injᵢ(σ), ⟨f,r⟩⟩) = valᵢ(σ, f, r))         [GenRecursor::computes[i]]
//! (S2) ⊢ ∀p⃗ ∀s⃗ ∀T. sv(e(p⃗,s⃗,T))                              [GenRecursor::sv]
//! (S3) ⊢ ∀p⃗ ∀s⃗ ∀T. (HYP → step_typed(A, B, U({A,T'}), T, e)) [GenRecursor::step_typed]
//! (S4) ⊢ ∀p⃗ ∀s⃗ ∀T ∀y⃗ ∀t⃗. ((HYP ∧ Hᵢ^ctor) →
//!          app(grec, ctorᵢ(y⃗,t⃗))
//!            = sᵢ ⟪y⃗,t⃗ in declared order⟫ app(grec,t₀) … )   [GenRecursor::iota[i]]
//! ```
//!
//! The quantifier prefix is always parameters, then minors in constructor
//! order, then the target, then the rule's own variables.
//!
//! # What the theorems assume — the complete list
//!
//! `HYP` (dischargeable is a wiring/`T`-policy question; the schemas just
//! carry it), `Hᵢ^ctor` (exactly what Lean's constructor states, recursive
//! arguments at `ind(p⃗)`), and `closed(A,B,u)` — discharged unconditionally
//! by the carrier. Nothing else: no parameter typing, no `Sort` facts, no
//! choice, no new axiom — the step is `n` Replacements, `n−1` binary unions,
//! and instances of existing lemmas.
//!
//! # One per declaration, over one apparatus
//!
//! Every `Replacement` mints fresh symbols, so building this twice for one
//! declaration yields two recursors whose theorems cannot be chained — the
//! lesson recorded three times over (`RecCore` sharing, `PointFun`,
//! `Machine`). A caller must build the `GenRecursor` **once**, over the
//! *same* [`Machine`], [`Inductive`] and [`crate::wrec_total::Recursor`] it
//! uses for everything else, and cache it — with these theorems, per the
//! standing memo rule — alongside the `Inductive`.
//!
//! # Declarations with no constructors
//!
//! [`GenRecursor::build`] returns `None` for `Empty`, and
//! [`super::EmptyDecl`] is what serves it instead — not a counted gap, and not
//! this file with a relaxed guard. The decline is **load-bearing in three
//! independent places**:
//!
//! * `HYP` is a [`Formula`], built by [`conj_of`] over the `n` minor typings;
//!   at `n = 0` there is no formula for it to be, and
//!   [`GenRecursor::hyp`] would have to become an `Option` through
//!   [`step_typed_at`](super::typed) and [`iota_at`](super::iota) and every
//!   consumer;
//! * [`step_cases`](super::members) splits the tag through `disj_of` over the
//!   `n` summands, so [`step_single_valued`](super::values) — hence (S2) —
//!   cannot run;
//! * `step_typed_at` splits the same way *and* compares `no_junk`'s statement
//!   against `mem(a, A) → ⋁ᵢ …`. At `n = 0` `no_junk` states `¬(a ∈ A)`, a
//!   different shape, so even the guard would refuse.
//!
//! The last is the tell: at `n = 0` the mathematics is not this argument with
//! an empty loop but a shorter and different one — the step is `∅`,
//! single-valuedness is immediate rather than `n²` branch comparisons, the
//! typing is vacuous rather than a case analysis, and there is no ι rule at
//! all. See [`super::empty_decl`].

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::fibre::Fibre;
use crate::funspace::bin_union;
use crate::wrec_total::Recursor;
use crate::{conj_of, gen_all};

use super::carrier::Inductive;
use super::computes::step_app;
use super::iota::iota_at;
use super::machine::{Machine, MachineId};
use super::premise::minors_of;
use super::step::{Rx, StepSym, Vals};
use super::typed::step_typed_at;
use super::values::step_single_valued;

/// The general recursor of one declaration: the step symbols, the hypothesis
/// bundle, and (S1)–(S4).
pub struct GenRecursor {
    /// The minor-premise variables `s₀ … s_{n-1}`, in constructor order.
    pub minors: Vec<FreeVar>,
    /// The target variable `T`.
    pub target: FreeVar,
    /// One Replacement symbol per constructor.
    pub steps: Vec<StepSym>,
    /// The `minor_typedᵢ` conjuncts of `HYP`, at the working variables
    /// ([`Inductive::params`], [`GenRecursor::minors`],
    /// [`GenRecursor::target`]).
    pub minor_typed: Vec<Formula>,
    /// `HYP`, their right-nested conjunction.
    pub hyp: Formula,
    /// (S1), per constructor.
    pub computes: Vec<Thm>,
    /// (S2).
    pub sv: Thm,
    /// (S3).
    pub step_typed: Thm,
    /// (S4), per constructor.
    pub iota: Vec<Thm>,
    /// The declaration this recursor is *of* — [`Inductive::ty`], the carrier's
    /// own defined symbol.
    pub decl: FnSym,
    /// The apparatus it was built over.
    pub machine: MachineId,
}

impl GenRecursor {
    /// Derive the whole development over a caller-supplied carrier and
    /// W-recursor. `iota` and `funspace` must be
    /// [`crate::wrec_total::iota`] and [`crate::wrec_total::wrec_funspace`]
    /// over the *same* [`Recursor`] as `rc`. `None` for a declaration with no
    /// constructors — see the module header for why that is a genuine gap
    /// rather than a strict guard, and [`super::EmptyDecl`] for what serves it
    /// — or if any internal shape check fails.
    ///
    /// # What is checked about the caller's theorems, and why
    ///
    /// `iota` and `funspace` arrive as bare `&Thm`s, and a [`Thm`] is a
    /// sequent: `concl()` is only what the theorem *would* say if its
    /// hypotheses were discharged. Every one of the four schemas below is
    /// documented `⊢ …`, and (S4) is built by `mp`-ing against `iota` and
    /// `funspace` — and [`Thm::mp`] unions the two sides' hypothesis sets in
    /// silence. So a caller who passed `Thm::assume(φ)` with `φ` the real
    /// theorem's conclusion would get a `GenRecursor` whose every `iota[i]` is
    /// `{φ} ⊢ …` under a header that promises `⊢ …`, with no step of the
    /// derivation noticing. Both theorems are therefore required to be
    /// **unconditional**, and their conclusions are pinned against the
    /// statements rebuilt by [`super::wrec_input`] over `mach.wt` and `rc`.
    ///
    /// Pinning the conclusions is not redundant with the kernel joins further
    /// down — those do reject a wrong `iota`, but only after `StepSym::new`
    /// has minted one Replacement symbol per constructor into `env`, so the
    /// refusal used to leave the environment permanently larger. Checking here
    /// costs two formula rebuilds and leaks nothing.
    ///
    /// `ind` must also be the declaration translated over *this* `mach`
    /// ([`Inductive::is_over`]): every term below resolves `Inj`, `rec₊` and
    /// the fibre against `mach`'s symbols, and a second apparatus with warm
    /// caches answers all of them — with theorems about somebody else's sets.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        rc: &Recursor,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<GenRecursor> {
        let n = ind.spec.ctors.len();
        if n == 0 || !ind.is_over(mach) || ind.has_function_typed_recs() {
            return None
        }
        let want_iota = super::wrec_input::wrec_iota_stmt(env, &mach.wt, rc);
        let want_funspace = super::wrec_input::wrec_funspace_stmt(env, &mach.wt, rc);
        if !crate::establishes(iota, &want_iota) || !crate::establishes(funspace, &want_funspace) {
            return None
        }
        let s = &mach.wt.sums;
        let minors: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
        let tv = env.fresh_var();
        let cx = Rx {
            mach,
            ind,
            ps: ind.params.iter().map(|v| Term::var(*v)).collect(),
            minors: minors.iter().map(|v| Term::var(*v)).collect(),
            t: Term::var(tv),
            bin: crate::sums::mem_bin_union_iff(env, &mach.wt.sums.ap.sets)?,
            vals: Vals::Minor,
        };

        // ── the step: one Replacement per constructor ───────────────────────
        let steps: Vec<StepSym> = (0..n)
            .map(|i| StepSym::new(env, &cx, i, &[minors[i], tv]))
            .collect::<Option<_>>()?;

        // ── the hypothesis bundle ───────────────────────────────────────────
        let minor_typed =
            minors_of(env, s, &ind.spec.ctors, &cx.ps, &ind.wty, &cx.minors, &cx.t);
        let hyp = conj_of(&minor_typed)?;

        // ── (S2), (S1) ──────────────────────────────────────────────────────
        let sv = step_single_valued(env, &cx, &steps)?;
        let mut computes = Vec::with_capacity(n);
        for i in 0..n {
            let (sv_v, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
            let at = step_app(
                env,
                &cx,
                &steps,
                &sv,
                i,
                &Term::var(sv_v),
                &Term::var(fv),
                &Term::var(rv),
            )?;
            computes.push(gen_all(&[sv_v, fv, rv], &at));
        }

        // ── (S3) ────────────────────────────────────────────────────────────
        let st = step_typed_at(env, &cx, &steps, &computes, &minor_typed, &hyp)?;

        // ── (S4), per constructor ───────────────────────────────────────────
        let comp_app = crate::wrec_typing::composite_app(env, &s.ap, rc.comp, &rc.comp_ax)?;
        let comp_typed = crate::wrec_typing::composite_typed(env, s, rc.comp, &rc.comp_ax)?;
        let mut iotas = Vec::with_capacity(n);
        let mut iota_vars = Vec::with_capacity(n);
        for i in 0..n {
            let yvs: Vec<FreeVar> = (0..ind.spec.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
            let tvs: Vec<FreeVar> = (0..ind.spec.ctors[i].recs).map(|_| env.fresh_var()).collect();
            let ia = iota_at(
                env, &cx, &steps, rc, &computes, &st, &hyp, iota, funspace, &comp_app,
                &comp_typed, i, &yvs, &tvs,
            )?;
            iotas.push(ia);
            iota_vars.push((yvs, tvs));
        }

        // ── generalise: parameters, minors, target, then each rule's own ────
        let mut outer: Vec<FreeVar> = ind.params.clone();
        outer.extend(minors.iter().copied());
        outer.push(tv);
        let computes: Vec<Thm> = computes.iter().map(|t| gen_all(&outer, t)).collect();
        let iota_thms: Vec<Thm> = iotas
            .iter()
            .zip(&iota_vars)
            .map(|(t, (yvs, tvs))| {
                let mut q = outer.clone();
                q.extend(yvs.iter().copied());
                q.extend(tvs.iter().copied());
                gen_all(&q, t)
            })
            .collect();
        let sv = gen_all(&outer, &sv);
        let step_typed = gen_all(&outer, &st);

        // The way out. All four schemas are stated `⊢ …` in the header, and
        // `Thm::gen` cannot discharge a sequent hypothesis — anything that
        // reached here is still here. The two doors above make this
        // unreachable, which is the point: it is what says so.
        let mut fields: Vec<&Thm> = vec![&sv, &step_typed];
        fields.extend(computes.iter());
        fields.extend(iota_thms.iter());
        if !crate::all_unconditional(&fields) {
            return None
        }

        Some(GenRecursor {
            minors,
            target: tv,
            steps,
            minor_typed,
            hyp,
            computes,
            sv,
            step_typed,
            iota: iota_thms,
            decl: ind.ty,
            machine: mach.ident(),
        })
    }

    /// Whether `mach` and `ind` are the apparatus and the declaration this
    /// recursor was built over.
    ///
    /// [`Inductive::is_over`] ties a declaration to a machine; this ties *the
    /// recursor* to both. The term-builders below need all three to agree, and
    /// two of the three agreeing is not enough: a second declaration over the
    /// same machine has its own `Inj`s, its own fibre and its own carrier, so
    /// `gr₁.rec_of(mach, ind₂, …)` would splice this recursor's Replacement
    /// symbols into that declaration's `W` and hand back a term nothing is
    /// true of. There is no theorem here to be wrong — that is exactly why the
    /// check has to be at the door, since a mislabelled *term* is caught by
    /// nothing downstream.
    pub fn is_over(&self, mach: &Machine, ind: &Inductive) -> bool {
        self.machine == mach.ident() && self.decl == ind.ty && ind.is_over(mach)
    }

    /// The packed step `e(p⃗, s⃗, T)` at caller-supplied terms.
    ///
    /// `None` unless `mach`/`ind` are this recursor's own
    /// ([`GenRecursor::is_over`]) and `ps`/`minors` have the declaration's own
    /// arities — a step symbol applied to the wrong number of parameters is not
    /// a term at all, and a short `minors` used to index out of bounds.
    pub fn step_of(
        &self,
        mach: &Machine,
        ind: &Inductive,
        ps: &[Term],
        minors: &[Term],
        t: &Term,
    ) -> Option<Term> {
        if !self.is_over(mach, ind)
            || ps.len() != ind.params.len()
            || minors.len() != self.steps.len()
        {
            return None
        }
        let s = &mach.wt.sums;
        Some((0..self.steps.len()).rev().fold(s.zero(), |acc, i| {
            let mut args = ps.to_vec();
            args.push(minors[i].clone());
            args.push(t.clone());
            bin_union(&s.ap.sets, Term::apply(self.steps[i].e, args), acc)
        }))
    }

    /// The recursor term `grec(p⃗, s⃗, T)` at caller-supplied terms.
    ///
    /// `None` under the same conditions as [`GenRecursor::step_of`] and
    /// [`carrier_at`], which this is the composition of. In particular `mach`
    /// is not a free choice: every symbol in the returned term comes from it,
    /// so a foreign machine would yield a perfectly well-formed `grec` about
    /// somebody else's sets, and a client stating an obligation at that term
    /// would be stating it about the wrong thing.
    pub fn rec_of(
        &self,
        mach: &Machine,
        ind: &Inductive,
        rc: &Recursor,
        ps: &[Term],
        minors: &[Term],
        t: &Term,
    ) -> Option<Term> {
        if !self.is_over(mach, ind) {
            return None
        }
        let (tags, fam, u, _) = carrier_at(mach, ind, ps)?;
        Some(rc.of(&tags, &fam, &u, t, &self.step_of(mach, ind, ps, minors, t)?))
    }
}

/// The carrier's raw data `(A, B, U({A,T'}), W(A,B,U({A,T'})))` at
/// caller-supplied parameter terms — what a client needs to *state* something
/// about the recursor at an instantiation, since the kernel has no term-level
/// substitution.
///
/// `None` unless `ind` is the declaration translated over `mach`
/// ([`Inductive::is_over`]) and `ps` has the declaration's parameter arity.
///
/// The `is_over` guard is the whole safety of this function. Every one of the
/// four parts is resolved against `mach` — the tags through `mach.syms.sum`,
/// the fibre through `mach.cases`, the bound through `mach.bnd` — and a
/// *second* apparatus whose caches have been warmed by some other declaration
/// answers every one of those lookups. What comes back is then
/// `(Sum′ₙ(A⃗), fam′, U′(…), W(A′, fam′, …))`: well-formed, built from the
/// wrong symbols, and not `ind.wty` at `ps`. Since the result is a tuple of
/// *terms*, nothing downstream can catch it — the client states its obligation
/// about them and the mislabelling is invisible, which is the cost
/// [`Inductive::is_over`]'s own comment says is a session.
pub fn carrier_at(mach: &Machine, ind: &Inductive, ps: &[Term]) -> Option<(Term, Term, Term, Term)> {
    if !ind.is_over(mach) || ps.len() != ind.params.len() {
        return None
    }
    let s = &mach.wt.sums;
    let summands: Vec<Term> =
        ind.telescopes.iter().map(|t| t.ty_of(ps.to_vec())).collect();
    let tags = mach.syms.sum(&summands)?;
    let branches: Vec<Term> = ind
        .fibre
        .lam
        .iter()
        .zip(&summands)
        .map(|(l, a)| Term::apply(*l, vec![a.clone()]))
        .collect();
    let fam = Fibre::fam_of(s, &mach.cases, &summands, &branches, &ind.fibre.target);
    let seed = Term::apply(s.ap.sets.up, vec![tags.clone(), ind.fibre.target.clone()]);
    let u = mach.bnd.universe_of(seed);
    let w = mach.wt.of(tags.clone(), fam.clone(), u.clone());
    Some((tags, fam, u, w))
}
