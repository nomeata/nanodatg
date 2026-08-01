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
//! [`GenRecursor::build`] returns `None` for `Empty`: its step is `∅`, it has
//! no ι rule to state and no `HYP` to carry, and a wiring that needs
//! `Empty.rec` must treat it separately (a counted gap until then) rather
//! than receive theorems about nothing.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::fibre::Fibre;
use crate::funspace::bin_union;
use crate::sums::Sums;
use crate::wrec_total::Recursor;
use crate::{conj_of, gen_all};

use super::carrier::Inductive;
use super::computes::step_app;
use super::iota::iota_at;
use super::machine::Machine;
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
}

impl GenRecursor {
    /// Derive the whole development over a caller-supplied carrier and
    /// W-recursor. `iota` and `funspace` must be
    /// [`crate::wrec_total::iota`] and [`crate::wrec_total::wrec_funspace`]
    /// over the *same* [`Recursor`] as `rc`. `None` for a declaration with no
    /// constructors, or if any internal shape check fails.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        rc: &Recursor,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<GenRecursor> {
        let n = ind.spec.ctors.len();
        if n == 0 {
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
        let computes = computes.iter().map(|t| gen_all(&outer, t)).collect();
        let iota_thms = iotas
            .iter()
            .zip(&iota_vars)
            .map(|(t, (yvs, tvs))| {
                let mut q = outer.clone();
                q.extend(yvs.iter().copied());
                q.extend(tvs.iter().copied());
                gen_all(&q, t)
            })
            .collect();

        Some(GenRecursor {
            minors,
            target: tv,
            steps,
            minor_typed,
            hyp,
            computes,
            sv: gen_all(&outer, &sv),
            step_typed: gen_all(&outer, &st),
            iota: iota_thms,
        })
    }

    /// The packed step `e(p⃗, s⃗, T)` at caller-supplied terms.
    pub fn step_of(&self, s: &Sums, ps: &[Term], minors: &[Term], t: &Term) -> Term {
        (0..self.steps.len()).rev().fold(s.zero(), |acc, i| {
            let mut args = ps.to_vec();
            args.push(minors[i].clone());
            args.push(t.clone());
            bin_union(&s.ap.sets, Term::apply(self.steps[i].e, args), acc)
        })
    }

    /// The recursor term `grec(p⃗, s⃗, T)` at caller-supplied terms.
    pub fn rec_of(
        &self,
        mach: &Machine,
        ind: &Inductive,
        rc: &Recursor,
        ps: &[Term],
        minors: &[Term],
        t: &Term,
    ) -> Option<Term> {
        let (tags, fam, u, _) = carrier_at(mach, ind, ps)?;
        Some(rc.of(&tags, &fam, &u, t, &self.step_of(&mach.wt.sums, ps, minors, t)))
    }
}

/// The carrier's raw data `(A, B, U({A,T'}), W(A,B,U({A,T'})))` at
/// caller-supplied parameter terms — what a client needs to *state* something
/// about the recursor at an instantiation, since the kernel has no term-level
/// substitution.
pub fn carrier_at(mach: &Machine, ind: &Inductive, ps: &[Term]) -> Option<(Term, Term, Term, Term)> {
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
