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
//!        with  cmpᵢ = comp(goodrec, f(r⃗), Sum_{mᵢ}(A⃗))
//!        and   ⊢ app(cmpᵢ, Injⱼ(•)) = app(goodrec, rⱼ)             [IhRow::Point]
//! ```
//!
//! **That last line is the plain fibre's.** A constructor taking
//! [`crate::recarg::RecArg::general`] has `Aⱼ = Σ(z::γⱼ)` rather than `1`, so
//! `Injⱼ(•)` is not a point of its fibre and there is no single child to name:
//! the ih row's `j`-th entry identifies the composite's value at **each** point
//! of `Aⱼ`,
//!
//! ```text
//!        ⊢ Hᵢ^ctor → ∀z. (z ∈ Aⱼ →
//!              app(cmpᵢ, Injⱼ(z)) = app(goodrec, app(rⱼ, z)))      [IhRow::Fibre]
//! ```
//!
//! and it is **conditional** — computing `app(f(g⃗), Injⱼ z)` at all needs the
//! branches to be functions, which is `RecArg::general`'s own antecedent and is
//! exactly the content of `Hᵢ^ctor` here. That is why
//! [`crate::inductive::iota`] states it under the ambient rather than as a bare
//! equation, and why [`IhRow`] is two variants and not one shape with a
//! degenerate case. `mini/tests/fixtures/indexed_infinitary_ctor.lean` is the
//! witness that reached it.
//!
//! *This file used to decline such a declaration outright, at `core.ih_eqs?`,
//! on the ground that it "has no ambient to carry it under". It has one: the
//! constructor's own argument typings, which every other theorem here is
//! already stated under.*
//!
//! `Hᵢ^ctor` is [`crate::inductive::carrier::ctor_atoms_at`] at
//! [`rec_sets`](crate::inductive::carrier::rec_sets) — *exactly* the
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

use crate::inductive::carrier::{ctor_atoms_at, rec_sets, Inductive};
use crate::inductive::iota::iota_core;
pub use crate::inductive::iota::IhRow;
use crate::inductive::machine::Machine;
use crate::inductive::step::Rx;
use crate::inductive::wrec_input;
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
    /// **The ih row**, in the spelling this constructor's fibre forces:
    /// [`IhRow::Point`]'s `⊢ app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)` at a
    /// constructor whose recursive arguments are plain, and
    /// [`IhRow::Fibre`]'s
    /// `⊢ Hᵢ^ctor → ∀z. (z ∈ Aⱼ → app(cmp, Injⱼ(z)) = app(goodrec, app(rⱼ, z)))`
    /// at one taking [`crate::recarg::RecArg::general`].
    ///
    /// The second is conditional and cannot be made otherwise — the general
    /// computation rule needs the branches to be functions — so the ambient it
    /// is stated under is `Hᵢ^ctor`, the same conjunction [`GoodIota::hyp`]
    /// holds and [`GoodIota::eq`] is stated under. The trivial `∅ = ∅` this
    /// file passes `iota_core` is discharged from both alike.
    pub ih: IhRow,
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
    ///
    /// # What is checked about the caller's theorems, and why
    ///
    /// `iota` and `funspace` are bare `&Thm`s — sequents `Γ ⊢ φ` — and both are
    /// consumed by [`Thm::mp`], which unions the two sides' `Γ`s without
    /// comment. Every theorem this struct hands back is documented `⊢ …`
    /// (`Good::funspace` says "unconditional" in as many words), so a
    /// hypothetical premise here would ride into all of them under a label that
    /// denies it. Both are therefore pinned against the statements rebuilt by
    /// [`crate::inductive::wrec_input`] **and** required to be unconditional,
    /// before any work is done.
    ///
    /// It is not enough that the two in-crate consumers happen to re-check the
    /// outputs ([`super::vacuous`] reads `hyps()`, and the per-constructor loop
    /// below reads `eq.hyps()`): a new consumer that reads
    /// `good.funspace.concl()` — the ordinary way to use a struct field with a
    /// `⊢` in its doc — would inherit the hypothesis silently. The check
    /// belongs at the door.
    ///
    /// `ind` must also be the skeleton translated over *this* `mach`
    /// ([`Inductive::is_over`]), since every term below resolves against
    /// `mach`'s symbols.
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
        if n == 0 || !ind.is_over(mach) {
            return None
        }
        let want_iota = wrec_input::wrec_iota_stmt(env, &mach.wt, rc);
        let want_funspace = wrec_input::wrec_funspace_stmt(env, &mach.wt, rc);
        if !crate::establishes(iota, &want_iota) || !crate::establishes(funspace, &want_funspace) {
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
        // Both stored fields, against their own doc comments. `wrec_iota` had
        // no check at all: `mp` against a discharged premise cannot change the
        // shape, but it can carry `Γ` in from either side, and `ind.closed` /
        // `gs.step_typed` are themselves documented `⊢`.
        let want_wrec_iota = wrec_input::wrec_iota_body(env, &mach.wt, rc, &args);
        if !crate::establishes(
            &fs_thm,
            &Formula::mem(rec.clone(), s.fs.of(ind.wty.clone(), ix.target.clone())),
        ) || !crate::establishes(&wrec_iota, &want_wrec_iota)
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
            // **`ctor_atoms_at`, at this constructor's own recursive-argument
            // sets** — `rⱼ ∈ W` for a plain slot and `gⱼ ∈ fs(Aⱼ, W)` for a
            // function-typed one. This rebuilt `want` has to be the *same*
            // conjunction `iota_core` put in its ambient (`iota.rs`, which uses
            // exactly this pair), and the plain `ctor_atoms` wrapper is that
            // conjunction only when every slot is plain. At a function-typed
            // slot the two disagreed and the `eq.concl() != want` check below
            // was the decline — measured by a `?`-census as this file's first
            // stop on `mini/tests/fixtures/indexed_infinitary_ctor.ndjson`,
            // ahead of the `ih_eqs` one the general case really owes.
            let ra = ind.recargs.get(i)?;
            let hyp = conj_of(&ctor_atoms_at(
                cx.tel(i),
                &ps,
                &ys,
                &ts,
                &rec_sets(s, ra, &ind.carrier),
            ));

            // Strip the trivial ambient: `(⊤ ∧ H) → C` becomes `H → C`, and
            // a bare `⊤ → C` becomes `C`. Everything `iota_core` states under
            // its ambient comes back through this one door.
            let strip = |t: &Thm| -> Option<Thm> {
                match &hyp {
                    Some(_) => Thm::mp(&uncurry(t)?, &triv_thm),
                    None => Thm::mp(t, &triv_thm),
                }
            };
            let eq = strip(&core.chain)?;

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

            // **The ih row, with the trivial ambient stripped from it too.**
            // `IhRow::Point` is unconditional and is carried across as it
            // stands; `IhRow::Fibre` arrives under `∅ = ∅ ∧ Hᵢ^ctor` — a
            // general constructor has `m > 0` and so has a `Hᵢ^ctor` — and
            // comes out under `Hᵢ^ctor`, the ambient every other theorem this
            // struct exports is stated at. This used to be `core.ih_eqs?`,
            // i.e. the `good` recursion declining a function-typed
            // declaration outright.
            let ih = match &core.ih_row {
                IhRow::Point(v) => IhRow::Point(v.clone()),
                IhRow::Fibre(v) => {
                    IhRow::Fibre(v.iter().map(&strip).collect::<Option<Vec<Thm>>>()?)
                }
            };

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
                ih,
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
