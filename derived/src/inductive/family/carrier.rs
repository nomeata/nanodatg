//! **The indexed carrier** `ind(p⃗, x⃗)`, with constructor membership and
//! inversion — `INDEXED-DESIGN.md` §4, and the composition D3 named as the
//! riskiest derived step.
//!
//! # The carrier
//!
//! ```text
//! ind(p⃗, x⃗) := { s ∈ W(A,B,U({A,T′})) : tup(x⃗) ∈ app(goodrec(p⃗), s) }
//! ```
//!
//! — one [`crate::define_by_membership`] of arity `np + ni`, and the thesis's
//! `λx :: α. {s : Wp:A. B p | rec_W (λp. G p) s x}` (`thesis.txt:1784`) with
//! `rec_W … s x` read as "the index tuple is in the good-set of `s`". It is a
//! subset of `W` **for every `x⃗`, junk ones included** — a Separation is a
//! subset no matter what is asked of it — which is what makes
//! [`super::universe`] one `C₂` step and what makes the weakening bridge below
//! unconditional.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) ↔ (z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)))  [IndexedCarrier::ty_ax]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ W)                             [IndexedCarrier::subset_w]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ skel(p⃗))                       [IndexedCarrier::bridge]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → tup(x⃗) ∈ app(goodrec,z))           [IndexedCarrier::good_of]
//! ⊢ ∀p⃗∀x⃗∀z. ((z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)) → z ∈ ind(p⃗,x⃗)) [IndexedCarrier::intro]
//!
//! (M) ⊢ ∀p⃗∀y⃗∀r⃗. ( (Hᵢ^ind ∧ Eᵢ) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)) ) [IndexedCtor::mem]
//! (I) ⊢ ∀p⃗∀y⃗∀r⃗∀x⃗. ( ([Hᵢ^skel ∧] ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)) →
//!         ( tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗)) ∧ ⋀ⱼ rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗)) ) ) [IndexedCtor::inv]
//! ```
//!
//! writing `skel(p⃗)` for the erased declaration's carrier (the *skeleton*
//! W-type, [`crate::inductive::Inductive::carrier`]) and `Hᵢ^skel` for its
//! constructor hypotheses.
//!
//! # (M)'s antecedent is longer than the design said — a measured negative
//!
//! `INDEXED-DESIGN.md` §4.2 states (M) with antecedent `Hᵢ^ind` alone: the
//! plain fields at their types and each recursive argument at
//! `ind(p⃗, d⃗ᵢⱼ)`. **That is not enough**, and the gap is structural rather
//! than an oversight in the proof:
//!
//! ```text
//! Eᵢ  :=  ⋀ₖ  eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, eᵢ₀(p⃗,y⃗) … eᵢ_{k−1}(p⃗,y⃗))
//! ```
//!
//! `Gᵢ` is a Separation *out of `Idx(p⃗)`*, so putting `tup(e⃗ᵢ)` into it needs
//! `tup(e⃗ᵢ) ∈ Idx(p⃗)` — and the index expressions are opaque `FnSym`s, by the
//! same convention that makes the whole spec expressible, so nothing in
//! `derived/` can prove it. Dropping the `w ∈ Idx(p⃗)` conjunct from `Gᵢ` is not
//! an escape: that conjunct is exactly what makes
//! [`super::goodstep`]'s `step_typed` unconditional. So `ni` extra antecedents
//! it is, discharged at the checker boundary where the Lean typing derivation
//! lives. For `RBTree.red` they are `Color.r ∈ Color` — closed — and `n ∈ N`,
//! which is the plain field's own typing and is already in hand.
//!
//! Inversion is unaffected: it reads the equality *out*, and never needs the
//! index tuple to be well typed.
//!
//! # Why this is the composition D3 was worried about
//!
//! (M) chains, under one ambient hypothesis and at every constructor: a
//! Separation unfolding (`ind(p⃗,x⃗)`'s axiom, backwards), a `wrec` ι
//! ([`super::good`]), a second Separation unfolding (`Gᵢ`'s axiom, backwards),
//! `ni` telescope introductions, `k` literal projections `compⱼ(tup y⃗) = yⱼ`
//! and `m` composite computations `app(cmp, Injⱼ(•)) = app(goodrec, rⱼ)`. (I)
//! is the same chain read right to left. Every one of those is an instance of
//! something that existed; what had no ancestor is the *composition*, and the
//! answer is that it goes through with the ambient hypothesis carried in
//! implication form throughout, exactly as (S3) and (S4) do.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms, Inductive};
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{carry_under, congr_ctx, hyp_conj, rewrite_under, under};
use crate::sigma::Telescope;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conj_sub, eq_symm, eq_trans, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl,
};

use super::good::Good;
use super::gval::GoodValues;
use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// One constructor of an indexed family: its membership rule and its
/// inversion rule.
pub struct IndexedCtor {
    /// Its position in the declaration.
    pub index: usize,
    /// The `k` plain-field variables — the same ones
    /// [`super::good::GoodIota`] is stated at.
    pub yvs: Vec<FreeVar>,
    /// The `m` recursive-argument variables.
    pub tvs: Vec<FreeVar>,
    /// The `ni` index variables that (I) quantifies over.
    pub xvs: Vec<FreeVar>,
    /// (M)'s antecedent, atom by atom, at the working variables: the `k` plain
    /// typings, then the `m` recursive arguments at their *indexed* types, then
    /// the `ni` result-index typings `Eᵢ`. Exported so a caller discharging it
    /// rebuilds exactly what the theorem carries.
    pub mem_atoms: Vec<Formula>,
    /// `⊢ ∀p⃗∀y⃗∀r⃗. ((Hᵢ^ind ∧ Eᵢ) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)))`.
    pub mem: Thm,
    /// (I)'s antecedent atoms: `Hᵢ^skel`'s atoms, then
    /// `ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)`.
    pub inv_atoms: Vec<Formula>,
    /// `⊢ ∀p⃗∀y⃗∀r⃗∀x⃗. (… → (tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗)) ∧ ⋀ⱼ rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)))`.
    pub inv: Thm,
}

/// The indexed family's carrier.
pub struct IndexedCarrier {
    /// The type symbol, of arity `np + ni`.
    pub ty: FnSym,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) ↔ (z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)))`.
    pub ty_ax: Thm,
    /// The `ni` index variables [`IndexedCarrier::carrier`] is stated at.
    pub xvs: Vec<FreeVar>,
    /// `ind(p⃗, x⃗)` at the declaration's parameters and [`IndexedCarrier::xvs`].
    pub carrier: Term,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ W)`.
    pub subset_w: Thm,
    /// **The D6 weakening bridge**: `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ skel(p⃗))`,
    /// the same statement one Leibniz step past the abbreviation. This is what
    /// turns Lean-shaped hypotheses (recursive arguments at *indexed* types)
    /// into the skeleton-shaped hypotheses the erased recursor's (S4) carries.
    pub bridge: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → tup(x⃗) ∈ app(goodrec,z))`.
    pub good_of: Thm,
    /// `⊢ ∀p⃗∀x⃗∀z. ((z ∈ W ∧ tup(x⃗) ∈ app(goodrec,z)) → z ∈ ind(p⃗,x⃗))`.
    pub intro: Thm,
    /// One entry per constructor.
    pub ctors: Vec<IndexedCtor>,
}

impl IndexedCarrier {
    /// `ind(p⃗, x⃗)` at caller-supplied parameters and indices. `None` unless
    /// the two lists have the declaration's own lengths — a shorter list is a
    /// well-formed term that is not this family.
    pub fn ty_of(&self, ps: &[Term], xs: &[Term]) -> Option<Term> {
        if ps.len() + xs.len() != self.ty.arity() as usize {
            return None
        }
        let mut a = ps.to_vec();
        a.extend(xs.iter().cloned());
        Some(Term::apply(self.ty, a))
    }

    /// Carve the carrier out of the skeleton, and derive (M) and (I).
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ix: &IndexSpace,
        gv: &GoodValues,
        good: &Good,
    ) -> Option<IndexedCarrier> {
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ni = spec.num_indices();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        // ── the Separation ──────────────────────────────────────────────────
        let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let tup_x = IndexedDeclSpec::tup(s, &xs);
        let psi = Formula::mem(tup_x.clone(), ap.apply(good.rec.clone(), tz.clone()));
        let cond = Formula::and(Formula::mem(tz.clone(), ind.wty.clone()), psi.clone());
        let existence = crate::funcs::separation_full(env, zv, &psi, &ind.wty, &ap.empty_ax)?;
        let mut params = ind.params.clone();
        params.extend(xvs.iter().copied());
        let (ty, ty_ax) = crate::define_by_membership(env, &params, &existence, zv, &cond)?;

        let carrier = Term::apply(ty, {
            let mut a = ps.clone();
            a.extend(xs.iter().cloned());
            a
        });

        // ── the four one-line consequences ──────────────────────────────────
        let mut ax_args = ps.clone();
        ax_args.extend(xs.iter().cloned());
        ax_args.push(tz.clone());
        let at = inst_all(&ty_ax, &ax_args)?;
        let mem_w = Formula::mem(tz.clone(), ind.wty.clone());
        let quant = {
            let mut q = params.clone();
            q.push(zv);
            q
        };
        let subset_w = gen_all(
            &quant,
            &syl(&iff_mp(&at)?, &and_left(mem_w.clone(), psi.clone()))?,
        );
        let good_of = gen_all(
            &quant,
            &syl(&iff_mp(&at)?, &and_right(mem_w.clone(), psi.clone()))?,
        );
        let intro = gen_all(&quant, &iff_mpr(&at)?);

        // The bridge: `W` is `skel(p⃗)`, one Leibniz along the erased carrier's
        // defining equation.
        let to_skel = eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?; // ⊢ W = skel(p⃗)
        let bridge = {
            let base = syl(&iff_mp(&at)?, &and_left(mem_w, psi.clone()))?;
            let tzc = tz.clone();
            gen_all(
                &quant,
                &carry_under(env, &to_skel, move |t| Formula::mem(tzc.clone(), t), &base)?,
            )
        };

        // ── the per-constructor rules ───────────────────────────────────────
        let mut ctors = Vec::with_capacity(spec.len());
        for i in 0..spec.len() {
            ctors.push(ctor_rules(
                env,
                mach,
                ind,
                spec,
                ix,
                gv,
                good,
                &Handles { ty, subset_w: &subset_w, good_of: &good_of, intro: &intro },
                i,
            )?);
        }

        Some(IndexedCarrier {
            ty,
            ty_ax,
            xvs,
            carrier,
            subset_w,
            bridge,
            good_of,
            intro,
            ctors,
        })
    }
}

/// The carrier-level facts a constructor rule is built from. Private.
struct Handles<'a> {
    ty: FnSym,
    subset_w: &'a Thm,
    good_of: &'a Thm,
    intro: &'a Thm,
}

/// From `⊢ aⱼ = bⱼ` for each `j`, infer `⊢ ctx(a⃗) = ctx(b⃗)`.
///
/// The `a⃗` appear in `ni` places at once (once per index symbol), which is why
/// this is a context-with-a-list rather than [`congr_ctx`] at a single hole.
fn rewrite_args<F>(env: &mut Env, eqs: &[Thm], ctx: F) -> Option<Thm>
where
    F: Fn(&[Term]) -> Term,
{
    let mut olds = Vec::with_capacity(eqs.len());
    let mut news = Vec::with_capacity(eqs.len());
    for e in eqs {
        let (a, b) = e.concl().as_eq()?;
        olds.push(a);
        news.push(b);
    }
    if eqs.is_empty() {
        return Some(Thm::eq_refl(ctx(&[])))
    }
    let mut acc: Option<Thm> = None;
    for pos in 0..eqs.len() {
        let (news_c, olds_c) = (news.clone(), olds.clone());
        let step = congr_ctx(env, &eqs[pos], |x| {
            let mut a = news_c[..pos].to_vec();
            a.push(x);
            a.extend(olds_c[pos + 1..].iter().cloned());
            ctx(&a)
        })?;
        acc = Some(match acc {
            None => step,
            Some(prev) => eq_trans(env, &prev, &step)?,
        });
    }
    acc
}

/// (M) and (I) at one constructor.
#[allow(clippy::too_many_arguments)]
fn ctor_rules(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ix: &IndexSpace,
    gv: &GoodValues,
    good: &Good,
    h: &Handles<'_>,
    i: usize,
) -> Option<IndexedCtor> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ni = spec.num_indices();
    let (kk, m) = (spec.base.ctors[i].args.len(), spec.base.ctors[i].recs);
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let gi = &good.at[i];
    let (yvs, tvs) = (gi.yvs.clone(), gi.tvs.clone());
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();

    // The comps of the tag payload, and the equations that read them back.
    let comps: Vec<Term> = (0..kk)
        .map(|j| Telescope::comp_of(ap, &mach.proj, j, gi.tuple.clone()))
        .collect();

    // `ind(p⃗, x⃗)` at an arbitrary index vector.
    let fam_at = |xs: &[Term]| -> Term {
        let mut a = ps.clone();
        a.extend(xs.iter().cloned());
        Term::apply(h.ty, a)
    };
    let res = spec.result_vec(i, &ps, &ys)?;
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, &ps, &ys)).collect::<Option<_>>()?;

    // ── (M) ─────────────────────────────────────────────────────────────────
    // The antecedent: plain typings, recursive arguments at their indexed
    // types, then the result-index typings the header explains.
    let mut atoms: Vec<Formula> = (0..kk)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(spec.base.ctors[i].args[j], a))
        })
        .collect();
    for j in 0..m {
        atoms.push(Formula::mem(ts[j].clone(), fam_at(&childs[j])));
    }
    for k in 0..ni {
        atoms.push(Formula::mem(res[k].clone(), spec.index_type_at(k, &ps, &res)?));
    }
    let hm = conj_of(&atoms)?; // `ni ≥ 1`, so never empty

    // The skeleton-shaped hypotheses, via the bridge.
    let skel_atoms = ctor_atoms(&ind.telescopes[i], &ps, &ys, &ts, &ind.carrier);
    let hyp_skel = conj_of(&skel_atoms);
    let m_skel = match &hyp_skel {
        None => None,
        Some(_) => {
            let mut parts: Vec<Thm> = Vec::with_capacity(kk + m);
            for j in 0..kk {
                parts.push(conj_proj(&atoms, j)?);
            }
            for j in 0..m {
                let mut a = ps.clone();
                a.extend(childs[j].iter().cloned());
                a.push(ts[j].clone());
                let sub = inst_all(h.subset_w, &a)?;
                let at_w = syl(&conj_proj(&atoms, kk + j)?, &sub)?;
                let tj = ts[j].clone();
                let to_skel = eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?;
                parts.push(carry_under(
                    env,
                    &to_skel,
                    move |t| Formula::mem(tj.clone(), t),
                    &at_w,
                )?);
            }
            Some(hyp_conj(&parts)?)
        }
    };

    // `H → app(goodrec, ctorᵢ) = Gᵢ(p⃗, tup(y⃗), cmp)`.
    let m_iota = match &m_skel {
        Some(t) => syl(t, &gi.eq)?,
        None => under(&gi.eq, &hm),
    };

    // `H → tup(e⃗ᵢ(p⃗,y⃗)) ∈ Idx(p⃗)`, from the result-index typings.
    let tup_res = IndexedDeclSpec::tup(s, &res);
    let m_idx = {
        let mut a = ps.clone();
        a.extend(res.iter().cloned());
        syl(&conj_sub(&atoms, kk + m, kk + m + ni)?, &inst_all(ix.intro(), &a)?)?
    };

    // The base-case equality, and the child memberships, at the *comps*.
    let (psc, resc) = (ps.clone(), i);
    let res_eq = rewrite_args(env, &gi.comp_eqs, |a| {
        IndexedDeclSpec::tup(s, &spec.result_vec(resc, &psc, a).expect("arity ensured"))
    })?;
    let m_eq = under(&eq_symm(env, &res_eq)?, &hm);

    let mut child_thms = Vec::with_capacity(m);
    for j in 0..m {
        // `H → tup(d⃗ᵢⱼ(p⃗,y⃗)) ∈ app(goodrec, rⱼ)`.
        let mut a = ps.clone();
        a.extend(childs[j].iter().cloned());
        a.push(ts[j].clone());
        let gd = syl(&conj_proj(&atoms, kk + j)?, &inst_all(h.good_of, &a)?)?;
        // Move to the comps, and to the ih row.
        let pb = spec.plains_before(i, j)?;
        let (psc, ic) = (ps.clone(), i);
        let arg_eq = rewrite_args(env, &gi.comp_eqs[..pb], |a| {
            IndexedDeclSpec::tup(s, &spec.rec_index_vec(ic, j, &psc, a).expect("arity ensured"))
        })?;
        let slot = ap.apply(good.rec.clone(), ts[j].clone());
        let arg_back = eq_symm(env, &arg_eq)?;
        let step1 = carry_under(env, &arg_back, move |w| Formula::mem(w, slot.clone()), &gd)?;
        let child_c = IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, &ps, &comps)?);
        let ih_back = eq_symm(env, &gi.ih_eqs[j])?;
        let step2 =
            carry_under(env, &ih_back, move |v| Formula::mem(child_c.clone(), v), &step1)?;
        child_thms.push(step2);
    }

    // `H → tup(e⃗ᵢ) ∈ Gᵢ(p⃗, tup(y⃗), cmp)`, by the `Gᵢ` axiom backwards.
    let mut g_args = ps.clone();
    g_args.push(gi.tuple.clone());
    g_args.push(gi.cmp.clone());
    g_args.push(tup_res.clone());
    let g_at = inst_all(&gv.axioms[i], &g_args)?;
    let mut matrix_thms = vec![m_eq];
    matrix_thms.extend(child_thms.iter().cloned());
    let m_in_g = hyp_mp(
        &a1i(&iff_mpr(&g_at)?, hm.clone()),
        &hyp_and(&m_idx, &hyp_conj(&matrix_thms)?)?,
    )?;

    // Carry it back along the ι, then put the constructor in the carrier.
    let m_in_app = {
        let back = crate::recursion::hyp::hyp_eq_symm(env, &m_iota)?;
        let tr = tup_res.clone();
        rewrite_under(env, &back, move |v| Formula::mem(tr.clone(), v), &m_in_g)?
    };
    let m_ctor_w = {
        let mut a = ps.clone();
        a.extend(ys.iter().cloned());
        a.extend(ts.iter().cloned());
        let at_skel = match &m_skel {
            Some(t) => syl(t, &inst_all(&ind.ctors[i].mem, &a)?)?,
            None => under(&inst_all(&ind.ctors[i].mem, &a)?, &hm),
        };
        let ctor_c = gi.ctor.clone();
        rewrite_under(
            env,
            &under(&inst_all(&ind.ty_ax, &ps)?, &hm),
            move |t| Formula::mem(ctor_c.clone(), t),
            &at_skel,
        )?
    };
    let mut i_args = ps.clone();
    i_args.extend(res.iter().cloned());
    i_args.push(gi.ctor.clone());
    let mem_body = hyp_mp(
        &a1i(&inst_all(h.intro, &i_args)?, hm.clone()),
        &hyp_and(&m_ctor_w, &m_in_app)?,
    )?;
    if *mem_body.concl() != Formula::imp(hm, Formula::mem(gi.ctor.clone(), fam_at(&res))) {
        return None
    }
    let mut mquant = ind.params.clone();
    mquant.extend(yvs.iter().copied());
    mquant.extend(tvs.iter().copied());
    let mem = gen_all(&mquant, &mem_body);

    // ── (I) ─────────────────────────────────────────────────────────────────
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let tup_x = IndexedDeclSpec::tup(s, &xs);
    let mem_at_x = Formula::mem(gi.ctor.clone(), fam_at(&xs));
    let mut inv_atoms = skel_atoms.clone();
    inv_atoms.push(mem_at_x.clone());
    let hk = conj_of(&inv_atoms)?;

    let (k_skel, k_mem) = match &hyp_skel {
        Some(hs) => (
            Some(syl(&conj_sub(&inv_atoms, 0, kk + m)?, &imp_refl(hs.clone()))?),
            conj_proj(&inv_atoms, kk + m)?,
        ),
        None => (None, imp_refl(mem_at_x.clone())),
    };
    let k_iota = match &k_skel {
        Some(t) => syl(t, &gi.eq)?,
        None => under(&gi.eq, &hk),
    };

    // `K → tup(x⃗) ∈ Gᵢ(p⃗, tup(y⃗), cmp)`.
    let mut g_args = ps.clone();
    g_args.extend(xs.iter().cloned());
    g_args.push(gi.ctor.clone());
    let k_good = syl(&k_mem, &inst_all(h.good_of, &g_args)?)?;
    let k_in_g = {
        let tx = tup_x.clone();
        rewrite_under(env, &k_iota, move |v| Formula::mem(tx.clone(), v), &k_good)?
    };

    let mut ga = ps.clone();
    ga.push(gi.tuple.clone());
    ga.push(gi.cmp.clone());
    ga.push(tup_x.clone());
    let k_matrix = syl(
        &syl(&k_in_g, &iff_mp(&inst_all(&gv.axioms[i], &ga)?)?)?,
        &and_right(
            Formula::mem(tup_x.clone(), ix.idx.clone()),
            GoodValues::matrix(mach, spec, i, &ps, &gi.tuple, &gi.cmp, &tup_x)?,
        ),
    )?;
    let matrix_atoms =
        GoodValues::matrix_atoms(mach, spec, i, &ps, &gi.tuple, &gi.cmp, &tup_x)?;

    // The base-case equality, moved off the comps.
    let k_eq = {
        let base = syl(&k_matrix, &conj_proj(&matrix_atoms, 0)?)?;
        let tx = tup_x.clone();
        carry_under(env, &res_eq, move |v| Formula::eq(tx.clone(), v), &base)?
    };

    // The children, moved off the comps and off the ih row, then re-typed.
    let mut inv_children = Vec::with_capacity(m);
    for j in 0..m {
        let base = syl(&k_matrix, &conj_proj(&matrix_atoms, 1 + j)?)?;
        let step1 = {
            let cmp_c = ap.apply(gi.cmp.clone(), mach.syms.inj(j, s.point())?);
            let _ = &cmp_c;
            let pb = spec.plains_before(i, j)?;
            let (psc, ic) = (ps.clone(), i);
            let arg_eq = rewrite_args(env, &gi.comp_eqs[..pb], |a| {
                IndexedDeclSpec::tup(s, &spec.rec_index_vec(ic, j, &psc, a).expect("arity ensured"))
            })?;
            carry_under(env, &arg_eq, move |w| Formula::mem(w, cmp_c.clone()), &base)?
        };
        let child = IndexedDeclSpec::tup(s, &childs[j]);
        let step2 = {
            let ch = child.clone();
            carry_under(env, &gi.ih_eqs[j], move |v| Formula::mem(ch.clone(), v), &step1)?
        };
        // `rⱼ ∈ W`, from the skeleton hypothesis.
        let k_rw = match &hyp_skel {
            Some(_) => {
                let at = syl(&conj_proj(&inv_atoms, kk + j)?, &imp_refl(skel_atoms[kk + j].clone()))?;
                let tj = ts[j].clone();
                rewrite_under(
                    env,
                    &under(&inst_all(&ind.ty_ax, &ps)?, &hk),
                    move |t| Formula::mem(tj.clone(), t),
                    &at,
                )?
            }
            None => return None, // `m > 0` forces a non-empty `Hᵢ^skel`
        };
        let mut ia = ps.clone();
        ia.extend(childs[j].iter().cloned());
        ia.push(ts[j].clone());
        inv_children.push(hyp_mp(
            &a1i(&inst_all(h.intro, &ia)?, hk.clone()),
            &hyp_and(&k_rw, &step2)?,
        )?);
    }

    let mut concl_thms = vec![k_eq];
    concl_thms.extend(inv_children);
    let inv_body = hyp_conj(&concl_thms)?;
    let mut want_atoms = vec![Formula::eq(tup_x, tup_res)];
    for j in 0..m {
        want_atoms.push(Formula::mem(ts[j].clone(), fam_at(&childs[j])));
    }
    if *inv_body.concl() != Formula::imp(hk, conj_of(&want_atoms)?) {
        return None
    }
    let mut iquant = mquant.clone();
    iquant.extend(xvs.iter().copied());
    let inv = gen_all(&iquant, &inv_body);

    Some(IndexedCtor { index: i, yvs, tvs, xvs, mem_atoms: atoms, mem, inv_atoms, inv })
}
