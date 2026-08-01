//! **`goodrec`, and the `good`-ι rules** — the riskiest derived rung of
//! `INDEXED-DESIGN.md` (§8, D3), and the one with no hand-written ancestor at
//! its shape.
//!
//! # What is derived
//!
//! ```text
//! goodrec(p⃗) := wrec(A, B, U({A,T′}), 𝒫(Idx(p⃗)), e_G(p⃗))
//! ```
//!
//! — the same [`crate::wrec_total::Recursor`] the value recursor runs on, over
//! the same skeleton, at the target [`super::IndexSpace::target`]. Because
//! [`super::goodstep`]'s `step_typed` is unconditional and
//! [`Inductive::closed`](crate::inductive::Inductive::closed) is discharged by
//! the carrier, **both of the W-recursor's standing hypotheses are gone before
//! this file starts**, and everything below is a closed theorem or one carrying
//! only the constructor's own argument typings:
//!
//! ```text
//! ⊢ goodrec(p⃗) ∈ fs(W, 𝒫(Idx(p⃗)))                            [Good::funspace]
//! ⊢ ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W)) →
//!       app(goodrec, ⟨a,f⟩)
//!         = app(e_G, ⟨a, ⟨f, comp(goodrec, f, B(a))⟩⟩))       [Good::wrec_iota]
//!
//! (G-ι)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗. ( Hᵢ^ctor →
//!            app(goodrec(p⃗), ctorᵢ(y⃗,r⃗)) = Gᵢ(p⃗, tup(y⃗), cmpᵢ) )   [Good::iota]
//!        with  cmpᵢ = comp(goodrec, f(r⃗), finord(mᵢ))
//!        and   ⊢ app(cmpᵢ, Injⱼ(•)) = app(goodrec, rⱼ)             [GoodIota::ih_eqs]
//! ```
//!
//! `Hᵢ^ctor` is [`crate::inductive::carrier::ctor_atoms`] — *exactly* the
//! conjunction the erased carrier's constructor rule carries, recursive
//! arguments at `ind(p⃗)` — and is **absent** when the constructor is nullary,
//! so `RBTree.leaf`'s (G-ι) is a closed equation.
//!
//! # How little of this is new
//!
//! The ι argument's whole prefix — fire the W-recursor's unguarded ι at
//! `a := Injᵢ(tup y⃗)`, rewrite the composite's domain along the fibre equation,
//! type the composite, compute the step by (S1), read the components back — is
//! *value-agnostic* and is [`crate::inductive::iota::iota_core`], called here
//! unchanged. What the value recursor does next (rewrite `sᵢ`'s arguments, one
//! application position at a time) has no counterpart: `valᵢ(tup y⃗, f(r⃗), cmp)`
//! **is** `Gᵢ(p⃗, tup(y⃗), cmp)` already. So D3's "compose a `wrec` ι with a
//! `define_by_membership` unfolding under an ambient hypothesis across `n`
//! branches" turned out to be the composition [`super::carrier`] does, and this
//! file is the shorter half.
//!
//! # The trivial ambient, and why it is here
//!
//! [`crate::inductive::iota::iota_core`] carries an ambient `HYP` because the
//! value recursor has one; `good` has none, and a nullary constructor has no
//! argument typings either, so the honest statement of `leaf`'s (G-ι) is a
//! *bare equation* with no implication at all. Rather than duplicate the core
//! for the hypothesis-free case, this file passes the provable ambient
//! `∅ = ∅` and discharges it at the end with one `Thm::eq_refl`. The shape
//! check on the way out is what makes that safe: what is returned is compared
//! against the rebuilt statement, so a leftover `⊤ →` would be caught.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms, Inductive};
use crate::inductive::iota::iota_core;
use crate::inductive::machine::Machine;
use crate::inductive::step::Rx;
use crate::sigma::Telescope;
use crate::wrec_total::Recursor;
use crate::{a1i, and_intro, conj_of, gen_all, inst_all, uncurry};

use super::goodstep::{good_rx, GoodStep};
use super::gval::GoodValues;
use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// One constructor's `good`-ι, and the working terms the carrier's membership
/// and inversion rules are stated at.
pub struct GoodIota {
    /// The `k` plain-field variables `y₀ … y_{k−1}`.
    pub yvs: Vec<FreeVar>,
    /// The `m` recursive-argument variables `r₀ … r_{m−1}`.
    pub tvs: Vec<FreeVar>,
    /// `Hᵢ^ctor`, or `None` for a nullary constructor.
    pub hyp: Option<Formula>,
    /// `⊢ [Hᵢ^ctor →] app(goodrec, ctorᵢ(y⃗,r⃗)) = Gᵢ(p⃗, tup(y⃗), cmp)`, at the
    /// working variables.
    pub eq: Thm,
    /// `ctorᵢ(y⃗, r⃗)`.
    pub ctor: Term,
    /// `tup(y⃗)`, the tag payload — the `σ` the `Gᵢ` axiom is instantiated at.
    pub tuple: Term,
    /// `cmp = comp(goodrec, f(r⃗), finord(mᵢ))`, the ih row.
    pub cmp: Term,
    /// `⊢ compⱼ(tup(y⃗)) = yⱼ` — unconditional.
    pub comp_eqs: Vec<Thm>,
    /// `⊢ app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)` — unconditional.
    pub ih_eqs: Vec<Thm>,
}

/// The `good` recursion of one indexed declaration.
pub struct Good {
    /// `goodrec(p⃗)`.
    pub rec: Term,
    /// `⊢ goodrec(p⃗) ∈ fs(W, 𝒫(Idx(p⃗)))` — **unconditional**.
    pub funspace: Thm,
    /// `⊢ ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W)) → app(goodrec,⟨a,f⟩) = …)` — the
    /// W-recursor's unguarded ι with both hypotheses discharged.
    pub wrec_iota: Thm,
    /// Per constructor, the ι at the working variables and the terms it is
    /// about.
    pub at: Vec<GoodIota>,
    /// Per constructor,
    /// `⊢ ∀p⃗ ∀y⃗ ∀r⃗. ([Hᵢ^ctor →] app(goodrec, ctorᵢ(y⃗,r⃗)) = Gᵢ(p⃗, tup(y⃗), cmp))`.
    pub iota: Vec<Thm>,
}

impl Good {
    /// Derive the `good` recursion. `rc`, `iota` and `funspace` must be the
    /// same [`Recursor`] apparatus and its
    /// [`crate::wrec_total::iota`]/[`crate::wrec_total::wrec_funspace`] the
    /// caller uses everywhere else.
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ix: &IndexSpace,
        gv: &GoodValues,
        gs: &GoodStep,
        rc: &Recursor,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<Good> {
        let n = spec.len();
        if n == 0 {
            return None
        }
        let s = &mach.wt.sums;
        let cx = good_rx(env, mach, ind, gv, ix)?;
        let ps: Vec<Term> = cx.ps.clone();

        let args = [
            ind.tags.clone(),
            ind.fibre.fam.clone(),
            ind.bound.clone(),
            ix.target.clone(),
            gs.step.clone(),
        ];
        let rec = rc.of(&args[0], &args[1], &args[2], &args[3], &args[4]);

        // Both of the W-recursor's hypotheses, discharged before anything else.
        let both = and_intro(&ind.closed, &gs.step_typed);
        let wrec_iota = Thm::mp(&inst_all(iota, &args)?, &both)?;
        let fs_thm = Thm::mp(&inst_all(funspace, &args)?, &both)?;
        if *fs_thm.concl() != Formula::mem(rec.clone(), s.fs.of(ind.wty.clone(), ix.target.clone()))
        {
            return None
        }

        // The provable ambient. See the header.
        let triv = Formula::eq(s.zero(), s.zero());
        let triv_thm = Thm::eq_refl(s.zero());
        let st = a1i(&gs.step_typed, triv.clone());

        let comp_app = crate::wrec_typing::composite_app(env, &s.ap, rc.comp, &rc.comp_ax)?;
        let comp_typed = crate::wrec_typing::composite_typed(env, s, rc.comp, &rc.comp_ax)?;

        let mut at = Vec::with_capacity(n);
        let mut iotas = Vec::with_capacity(n);
        for i in 0..n {
            let yvs: Vec<FreeVar> =
                (0..spec.base.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
            let tvs: Vec<FreeVar> =
                (0..spec.base.ctors[i].recs).map(|_| env.fresh_var()).collect();
            let core = iota_core(
                env,
                &cx,
                &gs.steps,
                rc,
                &gs.computes,
                &st,
                &triv,
                iota,
                funspace,
                &comp_app,
                &comp_typed,
                i,
                &yvs,
                &tvs,
            )?;

            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
            let hyp = conj_of(&ctor_atoms(cx.tel(i), &ps, &ys, &ts, &ind.carrier));

            // Strip the trivial ambient: `(⊤ ∧ H) → C` becomes `H → C`, and
            // a bare `⊤ → C` becomes `C`.
            let eq = match &hyp {
                Some(_) => Thm::mp(&uncurry(&core.chain)?, &triv_thm)?,
                None => Thm::mp(&core.chain, &triv_thm)?,
            };

            // The statement, rebuilt rather than trusted.
            let rhs = gv.of(i, &ps, &core.tuple, &core.cmp)?;
            let want = Formula::eq(s.ap.apply(rec.clone(), core.ctor.clone()), rhs);
            let want = match &hyp {
                Some(h) => Formula::imp(h.clone(), want),
                None => want,
            };
            if *eq.concl() != want || !eq.hyps().is_empty() {
                return None
            }

            let mut quant = ind.params.clone();
            quant.extend(yvs.iter().copied());
            quant.extend(tvs.iter().copied());
            iotas.push(gen_all(&quant, &eq));
            at.push(GoodIota {
                yvs,
                tvs,
                hyp,
                eq,
                ctor: core.ctor,
                tuple: core.tuple,
                cmp: core.cmp,
                comp_eqs: core.comp_eqs,
                ih_eqs: core.ih_eqs,
            });
        }
        drop(cx);
        Some(Good { rec, funspace: fs_thm, wrec_iota, at, iota: iotas })
    }

    /// `app(goodrec(p⃗), z)` — "the good-set of the skeleton element `z`".
    pub fn apply(&self, mach: &Machine, z: Term) -> Term {
        mach.wt.sums.ap.apply(self.rec.clone(), z)
    }

    /// The term-forming context, rebuilt — needed by [`super::vacuous`], which
    /// runs the step's branch computation at a decomposition of an arbitrary
    /// element of `W` rather than at a constructor.
    pub(super) fn rx<'a>(
        env: &mut Env,
        mach: &'a Machine,
        ind: &'a Inductive,
        gv: &GoodValues,
        ix: &IndexSpace,
    ) -> Option<Rx<'a>> {
        good_rx(env, mach, ind, gv, ix)
    }

    /// `tup(y⃗)` at caller-supplied plain fields — the same spelling
    /// [`GoodIota::tuple`] has.
    pub fn tag_payload(mach: &Machine, ys: &[Term]) -> Term {
        Telescope::tuple_of(&mach.wt.sums, ys)
    }
}
