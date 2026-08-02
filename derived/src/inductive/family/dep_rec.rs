//! **The indexed class-(T) eliminator at a value motive** — the value sibling
//! of [`IndexedPropRecursor`](super::IndexedPropRecursor), and what `077`'s
//! `RBTree.id` / `068`'s second σ decline for.
//!
//! # Why nothing that existed served it
//!
//! [`GenRecursor`] concludes `app(grec, t) ∈ T` — one target **set**. The
//! obligation at an indexed recursor's bottom is `app(grec, t) ∈ app(C, x⃗, t)`,
//! a **fibre** that varies with `t`. No choice of `T` makes those the same
//! statement, so no target policy discharges it however chosen, and
//! `INDEXED-DESIGN.md` §5.2's answer for `RBTree.id` — `T := S`, the skeleton —
//! is *strictly weaker* than the goal, because `ind(p⃗,x⃗) ⊊ S`.
//!
//! [`DepRecursor`](super::super::dep::DepRecursor) reaches the fibre in the
//! non-indexed case and cannot be instantiated here: its `DEPᵢ` applies the
//! motive to the **tree alone**, and Lean's indexed minor applies it at the
//! constructor's own indices. [`super::dep_motive`]'s header argues that the
//! two are not instances of one another in either direction. **The mismatch is
//! in the premise, not the wiring**, which is what makes this `derived/`'s.
//!
//! # Interface
//!
//! Writing `irec := grec(p⃗, gmin⃗, T)` for [`IndexedDepRecursor::rec`],
//! `PRE := ICOD(m,T) ∧ IDEP(m,S⃗)` ([`super::dep_motive`]) and `app(m, x⃗, t)`
//! for [`super::motive_app`]'s curried spine:
//!
//! ```text
//! ⊢ ∀p⃗ ∀m ∀S⃗ ∀T. ( PRE →
//!       ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → app(irec, t) ∈ app(m, x⃗, t) ) )
//!                                                 [IndexedDepRecursor::typing]
//! ```
//!
//! stated at **Lean's own** minor premises `S⃗`, not at the guarded ones
//! [`super::dep_guard`] instantiates `GenRecursor` with — the guard is an
//! implementation detail of the term, and `IndexedGuardedMinors::fires` is what
//! removes it from the statement. §5.1's term *is* the right term: `irec` is
//! `GenRecursor`'s, with the index arguments nowhere in it.
//!
//! # It is `dep.rs` at an indexed `φ`, not `prop_rec.rs` with `•` swapped out
//!
//! The `Prop` induction step fires no ι at all, because `•` is `•` at every
//! tree. This one **must** fire (S4) inside the step, so it needs the guarded
//! minors as well as the inversion:
//!
//! ```text
//! φ(z) := ∀x⃗. ( tup(x⃗) ∈ app(goodrec(p⃗), z) → app(irec, z) ∈ app(m, x⃗, z) )
//! ```
//!
//! and per constructor, under `rect_stepᵢ(φ)`'s antecedent and `φ`'s own:
//!
//! 1. [`invert_under`] — shared with the `Prop` rule, not copied — gives
//!    `xₖ = eᵢₖ` and each `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)`;
//! 2. `φ(tⱼ)` at the child's own indices, with [`IndexedCarrier::good_of`]
//!    discharging its antecedent, gives the induction hypothesis
//!    `vⱼ := app(irec,tⱼ) ∈ app(m, d⃗ᵢⱼ, tⱼ)`;
//! 3. those two **are** the indexed guard, so `fires` rewrites `gminᵢ` to `Sᵢ`
//!    on (S4)'s right-hand side — `ICOV` supplies the `vⱼ ∈ T` that
//!    `minor_typedᵢ`'s antecedent also asks for;
//! 4. `IDEPᵢ` at the same fields puts `Sᵢ⟪y⃗,t⃗⟫v⃗` in `app(m, e⃗ᵢ, ctorᵢ)`;
//! 5. one [`kernel::Thm::eq_leibniz`] per index moves `e⃗ᵢ` to `x⃗`.
//!
//! Step 3 is the one with no counterpart in either ancestor: the guard's
//! condition is discharged by *inversion*, which only an indexed rule has.
//!
//! # The `T`-policy is void, and this construction is why
//!
//! `RECURSOR-DESIGN.md` §5.2's three-way target choice died when `guard.rs`
//! made `HYP` dischargeable from `COD ∧ DEP` alone. `INDEXED-DESIGN.md` §5.2
//! re-introduced a policy — a family-valued-motive recogniser — on the premise
//! that the engine for an indexed recursor is the *simply typed* `grec`. That
//! premise is what this file removes: `T` is a bound variable of
//! [`IndexedDepRecursor::typing`] constrained only by `ICOD`, and nothing below
//! chooses it. Otto argued the recogniser would therefore not be needed and
//! marked it *argued, not derived* for want of a rule to check against.
//! **Confirmed**: `T` appears in this file only as `guards.target`, and the
//! sole thing ever asked of it is `ICOD`. §5.2's recogniser does not need to be
//! written.
//!
//! # The one interface risk, flagged rather than discovered
//!
//! **`ICOV`'s index binders are unrestricted.** `COD`'s tree binder is bounded
//! by `z ∈ W`, and `ICOV` keeps that, but there is no corresponding bound on
//! `x⃗` — a consumer discharging `PRE` therefore owes the covering condition at
//! index vectors the family never reaches, where `app(m, x⃗, z)` is `∅` because
//! the motive's outermost application is off its own domain. That is provable
//! ([`crate::funcs::app_off_domain`]) and it is not free.
//!
//! Two alternatives were available and both cost something else, so this is a
//! judgement rather than an oversight:
//!
//! * bounding by `z ∈ ind(p⃗, x⃗)` instead of `z ∈ W` makes junk indices vacuous
//!   for free, but then [`super::dep_guard`]'s `lands` needs
//!   `ctorᵢ ∈ ind(p⃗, e⃗ᵢ)` rather than `ctorᵢ ∈ W`, which drags the `ni`
//!   result-index typings `Eᵢ` (see [`IndexedCtor::mem`](super::IndexedCtor::mem))
//!   into the guard and thence onto every consumer of `fires`;
//! * stating the covering condition **only at the sites it is used** — at
//!   `(e⃗ᵢ, ctorᵢ)` and at each `(d⃗ᵢⱼ, tⱼ)`, all closed forms in the fields —
//!   makes every instance bounded and directly matches what a recursor nest
//!   holds, at the cost of `n·(1 + mᵢ)` premises in place of one.
//!
//! The second is probably the better interface and is **not** built. If
//! discharging `ICOV` at junk indices turns out to be real work at the boundary,
//! that is the change to make, and nothing below it would move: `ICOV` is
//! consumed in exactly two places, [`super::dep_guard`]'s `lands` and this
//! file's `vⱼ ∈ T`.
//!
//! # What is not here
//!
//! The **ι rule**. `INDEXED-DESIGN.md` §5.1's finding is that the indexed ι is
//! the erased one with `ni` dead binders, so `GenRecursor::iota` plus
//! `IndexedGuardedMinors::fires` is expected to be all of it; but that is a
//! separate theorem with its own antecedent, and it is not built or tested
//! here. A consumer needing ι at a value motive should read this as a gap, not
//! as available.
//!
//! # Nothing here is an axiom
//!
//! One [`decl_rect`] (one Separation) and instances of theorems that already
//! exist; the guarded minors' symbols are [`super::dep_guard`]'s.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms, Inductive};
use crate::inductive::machine::Machine;
use crate::inductive::motive::cod_parts;
use crate::inductive::rec_shared::{
    carry_back, gen_under, hyp_conj, hyp_inst, rewrite_under, under,
};
use crate::inductive::rect::{decl_rect, rect_parts};
use crate::inductive::recursor::GenRecursor;
use crate::inductive::step::applied_minor;
use crate::recursion::hyp::hyp_eq_symm;
use crate::wrec::hyp_eq_trans;
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, establishes, gen_all, hyp_and, hyp_mp,
    imp_refl, inst_all, syl, uncurry,
};

use super::carrier::IndexedCarrier;
use super::dep_guard::IndexedGuardedMinors;
use super::prop_rec::{invert_under, lean_order_of, minor_atoms_at, motive_app, Inverted};
use super::spec::IndexedDeclSpec;
use super::IndexedInductive;

/// An indexed class-(T) declaration's eliminator at a value-valued motive.
pub struct IndexedDepRecursor {
    /// The motive variable `m`.
    pub motive: FreeVar,
    /// Lean's dependent minor-premise variables `S₀ … S_{n-1}`.
    pub minors: Vec<FreeVar>,
    /// The target variable `T`.
    pub target: FreeVar,
    /// The guarded minors `GenRecursor` was instantiated at.
    pub guards: IndexedGuardedMinors,
    /// `irec = grec(p⃗, gmin⃗, T)` at the declaration's own parameters.
    pub rec: Term,
    /// `PRE = ICOD(m,T) ∧ IDEP(m,S⃗)`.
    pub premise: Formula,
    /// The `ni` index variables the conclusion quantifies over, outermost
    /// first, and the major premise, bound inside all of them.
    pub xvs: Vec<FreeVar>,
    /// The major-premise variable `t`.
    pub major: FreeVar,
    /// **`⊢ ∀p⃗ ∀m ∀S⃗ ∀T. (PRE → ∀x⃗ ∀t. (t ∈ ind(p⃗,x⃗) → app(irec,t) ∈ app(m,x⃗,t)))`**
    /// — unconditional, checked on the way out.
    pub typing: Thm,
}

impl IndexedDepRecursor {
    /// Derive the eliminator over an already-translated indexed family.
    ///
    /// `gr` must be [`GenRecursor::build`]'s output over *this* `mach`, `ind`
    /// and `rc`, and `fam` [`IndexedInductive::build`] over the same. `None`
    /// for a declaration with no constructors or no indices, for a family whose
    /// spec and skeleton disagree, and on any internal shape check.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, plus the
    /// guarded minors' own; build this once per declaration and cache it with
    /// the result.
    pub fn over_family(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        fam: &IndexedInductive,
        gr: &GenRecursor,
        rc: &Recursor,
    ) -> Option<IndexedDepRecursor> {
        let spec = &fam.spec;
        let ixc = &fam.carrier;
        let (n, ni) = (spec.len(), spec.num_indices());
        if n == 0 || ni == 0 || !gr.is_over(mach, ind) || ind.spec.ctors.len() != n {
            return None
        }
        if ind.params.len() != spec.base.params || ixc.ctors.len() != n {
            return None
        }
        if !crate::all_unconditional(&[&ixc.subset_w, &ixc.good_of, &ixc.intro, &ind.ty_ax]) {
            return None
        }

        let s = &mach.wt.sums;
        let ap = &s.ap;
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let grec = fam.good.rec.clone();

        let motive = env.fresh_var();
        let minors: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
        let target = env.fresh_var();
        let guards =
            IndexedGuardedMinors::build(env, mach, ind, spec, ixc, motive, &minors, target)?;
        let (tm, tt) = (Term::var(motive), Term::var(target));
        let irec = gr.rec_of(mach, ind, rc, &ps, &guards.terms, &tt)?;
        let premise = Formula::and(guards.cod.clone(), guards.dep.clone());

        // ── `φ(z) := ∀x⃗. (tup(x⃗) ∈ app(goodrec,z) → app(irec,z) ∈ app(m,x⃗,z))`
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let pxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let pxs: Vec<Term> = pxvs.iter().map(|v| Term::var(*v)).collect();
        let phi = pxvs.iter().rev().fold(
            Formula::imp(
                Formula::mem(IndexedDeclSpec::tup(s, &pxs), ap.apply(grec.clone(), tz.clone())),
                Formula::mem(
                    ap.apply(irec.clone(), tz.clone()),
                    motive_app(s, &tm, &pxs, &tz),
                ),
            ),
            |acc, v| Formula::forall(*v, acc),
        );

        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != n {
            return None
        }
        let mut steps: Vec<Thm> = Vec::with_capacity(n);
        for (i, part) in parts.iter().enumerate() {
            let cx = Step {
                mach,
                ind,
                spec,
                ixc,
                gr,
                guards: &guards,
                grec: &grec,
                irec: &irec,
                ps: &ps,
                tm: &tm,
                tt: &tt,
                zv,
                phi: &phi,
                premise: &premise,
            };
            let st = induction_step(env, &cx, i)?;
            if *st.concl() != Formula::imp(premise.clone(), part.clone()) {
                return None
            }
            steps.push(st);
        }
        let h_all = syl(&hyp_conj(&steps)?, &decl_rect(env, mach, ind, zv, &phi)?)?;

        // ── the conclusion, at the carrier and at the motive's own indices ──
        let fxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let fxs: Vec<Term> = fxvs.iter().map(|v| Term::var(*v)).collect();
        let tv = env.fresh_var();
        let ttm = Term::var(tv);
        let mem_t = Formula::mem(ttm.clone(), ixc.ty_of(&ps, &fxs)?);
        let kf = Formula::and(premise.clone(), mem_t.clone());
        let k_h = and_left(premise.clone(), mem_t.clone());
        let k_m = and_right(premise.clone(), mem_t.clone());

        let mut ca = ps.clone();
        ca.extend(fxs.iter().cloned());
        ca.push(ttm.clone());
        let sub = inst_all(&ixc.subset_w, &ca)?;
        if *sub.concl()
            != Formula::imp(mem_t.clone(), Formula::mem(ttm.clone(), ind.wty.clone()))
        {
            return None
        }
        let gof = inst_all(&ixc.good_of, &ca)?;
        if *gof.concl()
            != Formula::imp(
                mem_t.clone(),
                Formula::mem(
                    IndexedDeclSpec::tup(s, &fxs),
                    ap.apply(grec.clone(), ttm.clone()),
                ),
            )
        {
            return None
        }

        let k_phi = hyp_mp(
            &hyp_inst(&syl(&k_h, &h_all)?, std::slice::from_ref(&ttm))?,
            &syl(&k_m, &sub)?,
        )?;
        let k_goal = hyp_mp(&hyp_inst(&k_phi, &fxs)?, &syl(&k_m, &gof)?)?;

        let want_body = Formula::mem(
            ap.apply(irec.clone(), ttm.clone()),
            motive_app(s, &tm, &fxs, &ttm),
        );
        if *k_goal.concl() != Formula::imp(kf, want_body.clone()) {
            return None
        }
        let mut closed = gen_under(tv, &premise, &uncurry(&k_goal)?)?;
        for v in fxvs.iter().rev() {
            closed = gen_under(*v, &premise, &closed)?;
        }

        let mut quant = ind.params.clone();
        quant.push(motive);
        quant.extend(minors.iter().copied());
        quant.push(target);
        let typing = gen_all(&quant, &closed);
        let inner = fxvs.iter().rev().fold(
            Formula::forall(tv, Formula::imp(mem_t, want_body)),
            |acc, v| Formula::forall(*v, acc),
        );
        let want = quant
            .iter()
            .rev()
            .fold(Formula::imp(premise.clone(), inner), |acc, v| Formula::forall(*v, acc));
        if !establishes(&typing, &want) {
            return None
        }

        Some(IndexedDepRecursor {
            motive,
            minors,
            target,
            guards,
            rec: irec,
            premise,
            xvs: fxvs,
            major: tv,
            typing,
        })
    }
}

/// The context one induction step is built in. Private.
struct Step<'a> {
    mach: &'a Machine,
    ind: &'a Inductive,
    spec: &'a IndexedDeclSpec,
    ixc: &'a IndexedCarrier,
    gr: &'a GenRecursor,
    guards: &'a IndexedGuardedMinors,
    grec: &'a Term,
    irec: &'a Term,
    ps: &'a [Term],
    tm: &'a Term,
    tt: &'a Term,
    zv: FreeVar,
    phi: &'a Formula,
    premise: &'a Formula,
}

/// `⊢ PRE → rect_stepᵢ(φ)`.
fn induction_step(env: &mut Env, cx: &Step<'_>, i: usize) -> Option<Thm> {
    let (mach, ind, spec, ixc) = (cx.mach, cx.ind, cx.spec, cx.ixc);
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ps = cx.ps;
    let ni = spec.num_indices();
    let c = &spec.base.ctors[i];
    let (k, m) = (c.args.len(), c.recs);

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = ts.iter().map(|t| ap.apply(cx.irec.clone(), t.clone())).collect();
    let ctor = ind.ctor_term(mach, i, &ys, &ts)?;
    let res = spec.result_vec(i, ps, &ys)?;
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, ps, &ys)).collect::<Option<_>>()?;

    // ── `rect_stepᵢ`'s own antecedent ───────────────────────────────────────
    let mut ratoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(c.args[j], a))
        })
        .collect();
    ratoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    ratoms.extend(ts.iter().map(|t| cx.phi.subst(cx.zv, t)));
    let hr = conj_of(&ratoms);
    let kf = match &hr {
        Some(h) => Formula::and(cx.premise.clone(), h.clone()),
        None => cx.premise.clone(),
    };
    let (k_pre, k_rect) = match &hr {
        Some(h) => (
            and_left(cx.premise.clone(), h.clone()),
            Some(and_right(cx.premise.clone(), h.clone())),
        ),
        None => (imp_refl(cx.premise.clone()), None),
    };
    let rect_at = |j: usize| -> Option<Thm> { syl(k_rect.as_ref()?, &conj_proj(&ratoms, j)?) };

    // ── under `K2 = kf ∧ (tup(x⃗) ∈ app(goodrec, ctorᵢ))` ────────────────────
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let mem_g = Formula::mem(
        IndexedDeclSpec::tup(s, &xs),
        ap.apply(cx.grec.clone(), ctor.clone()),
    );
    let k2 = Formula::and(kf.clone(), mem_g.clone());
    let k2_kf = and_left(kf.clone(), mem_g.clone());
    let k2_g = and_right(kf.clone(), mem_g.clone());
    let lift = |t: &Thm| syl(&k2_kf, t);

    let plains: Vec<Thm> = (0..k).map(|j| lift(&rect_at(j)?)).collect::<Option<_>>()?;
    let in_w: Vec<Thm> = (0..m).map(|j| lift(&rect_at(k + j)?)).collect::<Option<_>>()?;
    let Inverted { skel, idx_eqs, child_mem } = invert_under(
        env, mach, ind, spec, ixc, i, ps, &ys, &ts, &xs, &k2, &plains, &in_w, &k2_g,
    )?;

    // ── the induction hypotheses, at each child's own index vector ──────────
    let mut ihs: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        let at_child = hyp_inst(&lift(&rect_at(k + m + j)?)?, &childs[j])?;
        let mut ga = ps.to_vec();
        ga.extend(childs[j].iter().cloned());
        ga.push(ts[j].clone());
        ihs.push(hyp_mp(&at_child, &syl(&child_mem[j], &inst_all(&ixc.good_of, &ga)?)?)?);
    }

    // `vⱼ ∈ T`, which `minor_typedᵢ`'s antecedent also asks for. `ICOV` at the
    // child's own index vector, and the child in the skeleton.
    let (covers, empty_in) = cod_parts(&cx.guards.cod)?;
    let k_pre2 = lift(&k_pre)?;
    let k_cod = syl(&k_pre2, &and_left(cx.guards.cod.clone(), cx.guards.dep.clone()))?;
    let k_covers = syl(&k_cod, &and_left(covers, empty_in))?;
    let mut in_t: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        let mut ix = childs[j].clone();
        ix.push(ts[j].clone());
        let inner = hyp_mp(&hyp_inst(&k_covers, &ix)?, &in_w[j])?;
        in_t.push(hyp_mp(&hyp_inst(&inner, std::slice::from_ref(&vs[j]))?, &ihs[j])?);
    }

    // ── (S4), at the guarded minors, then the guard fires ───────────────────
    let mut args = ps.to_vec();
    args.extend(cx.guards.terms.iter().cloned());
    args.push(cx.tt.clone());
    args.extend(ys.iter().cloned());
    args.extend(ts.iter().cloned());
    let iota_at = inst_all(&cx.gr.iota[i], &args)?;
    let k_hyp = syl(&k_pre2, &cx.guards.hyp)?;
    let hctor = ctor_atoms(&ind.telescopes[i], ps, &ys, &ts, &ind.carrier);
    let k_iota = match conj_of(&hctor) {
        None => hyp_mp(&a1i(&iota_at, k2.clone()), &k_hyp)?,
        Some(_) => hyp_mp(&a1i(&iota_at, k2.clone()), &hyp_and(&k_hyp, &hyp_conj(&skel)?)?)?,
    };

    let k_eq = match &cx.guards.fires[i] {
        None => k_iota,
        Some(fired) => {
            let mut h_thms: Vec<Thm> = plains.clone();
            h_thms.extend(in_w.iter().cloned());
            h_thms.extend(in_t.iter().cloned());
            let mut psi_thms: Vec<Thm> = child_mem.clone();
            psi_thms.extend(ihs.iter().cloned());
            let mut insts = ys.clone();
            insts.extend(ts.iter().cloned());
            insts.extend(vs.iter().cloned());
            let at = hyp_inst(&under(fired, &k2), &insts)?;
            let k_fire =
                hyp_mp(&at, &hyp_and(&hyp_conj(&h_thms)?, &hyp_conj(&psi_thms)?)?)?;
            hyp_eq_trans(env, &k_iota, &k_fire)?
        }
    };
    let want_eq = Formula::eq(
        ap.apply(cx.irec.clone(), ctor.clone()),
        applied_minor(ap, &c.order, &Term::var(cx.guards.minors[i]), &ys, &ts, &vs),
    );
    if *k_eq.concl() != Formula::imp(k2.clone(), want_eq) {
        return None
    }

    // ── `IDEPᵢ` at the same fields ──────────────────────────────────────────
    let a_atoms = minor_atoms_at(s, spec, ixc, i, cx.tm, ps, &ys, &ts, &vs)?;
    let mut a_thms = lean_order_of(&c.order, &plains, &child_mem)?;
    a_thms.extend(ihs.iter().cloned());
    for (q, th) in a_thms.iter().enumerate() {
        if *th.concl() != Formula::imp(k2.clone(), a_atoms.get(q)?.clone()) {
            return None
        }
    }
    let k_dep = syl(&k_pre2, &and_right(cx.guards.cod.clone(), cx.guards.dep.clone()))?;
    let k_dep_i = syl(&k_dep, &conj_proj(&cx.guards.dep_parts, i)?)?;
    let mut insts = lean_order_of(&c.order, &ys, &ts)?;
    insts.extend(vs.iter().cloned());
    let at = hyp_inst(&k_dep_i, &insts)?;
    let k_val = match hyp_conj(&a_thms) {
        Some(prem) => hyp_mp(&at, &prem)?,
        None => at,
    };

    // `app(irec, ctorᵢ) ∈ app(m, e⃗ᵢ, ctorᵢ)`.
    let mut cur = carry_back(env, &k_eq, &k_val, &motive_app(s, cx.tm, &res, &ctor))?;

    // ── move the conclusion from `e⃗ᵢ` to `x⃗`, one index at a time ──────────
    let mut spine = res.clone();
    for q in 0..ni {
        let back = hyp_eq_symm(env, &idx_eqs[q])?;
        let (pre, post) = (xs[..q].to_vec(), spine[q + 1..].to_vec());
        let (sc, tmc, cc, rc) = (s.clone(), cx.tm.clone(), ctor.clone(), cx.irec.clone());
        let apc = ap.clone();
        cur = rewrite_under(
            env,
            &back,
            move |hole| {
                let mut v = pre.clone();
                v.push(hole);
                v.extend(post.iter().cloned());
                Formula::mem(
                    apc.apply(rc.clone(), cc.clone()),
                    motive_app(&sc, &tmc, &v, &cc),
                )
            },
            &cur,
        )?;
        spine[q] = xs[q].clone();
    }
    if *cur.concl()
        != Formula::imp(
            k2,
            Formula::mem(ap.apply(cx.irec.clone(), ctor.clone()), motive_app(s, cx.tm, &xs, &ctor)),
        )
    {
        return None
    }

    // ── close `∀x⃗`, then the constructor's own fields ───────────────────────
    let mut acc = uncurry(&cur)?;
    for v in xvs.iter().rev() {
        acc = gen_under(*v, &kf, &acc)?;
    }
    if *acc.concl() != Formula::imp(kf, cx.phi.subst(cx.zv, &ctor)) {
        return None
    }
    match &hr {
        None => Some(acc),
        Some(_) => {
            let mut out = uncurry(&acc)?;
            for v in tvs.iter().rev() {
                out = gen_under(*v, cx.premise, &out)?;
            }
            for v in yvs.iter().rev() {
                out = gen_under(*v, cx.premise, &out)?;
            }
            Some(out)
        }
    }
}
