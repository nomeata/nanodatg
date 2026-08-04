//! **Structural induction over a declaration's carrier** — [`crate::wtype::w_rect`]
//! re-phrased in the declaration's own constructors.
//!
//! # Interface
//!
//! Writing `W` for the raw carrier `W(A,B,U({A,T}))`, `ctorᵢ(y⃗,t⃗)` for
//! [`Inductive::ctor_term`] and `φ(t)` for the caller's formula at `t`
//! (`phi.subst(zv, t)`):
//!
//! ```text
//! rect_stepᵢ(φ) := ∀y₀ … y_{k-1} ∀t₀ … t_{m-1}.
//!     (( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1}) ∧ ⋀ⱼ tⱼ ∈ W ∧ ⋀ⱼ φ(tⱼ) )
//!        → φ(ctorᵢ(y⃗, t⃗)))                                        [rect_step]
//! RECT(φ) := rect_step₀ ∧ ( … ∧ rect_step_{n-1})                    [rect_hyp]
//!
//! ⊢ RECT(φ) → ∀z. (z ∈ W → φ(z))                                   [decl_rect]
//! ```
//!
//! The antecedent of `rect_stepᵢ` is **one flat right-nested conjunction** of
//! `k + 2m` atoms in the order *arguments, recursive arguments, induction
//! hypotheses* — the same order [`super::premise`]'s `minor_typedᵢ` uses for
//! `y⃗, t⃗, v⃗`, so a caller can read the two side by side. For a constructor with
//! no fields at all it is **absent**, and `rect_stepᵢ` is the bare `φ(ctorᵢ)`,
//! mirroring how the constructor's own typing rule loses its antecedent.
//!
//! # A function-typed recursive argument
//!
//! At a constructor that takes [`RecArg::general`](crate::recarg::RecArg::general) the `j`-th recursive
//! argument is a **function** `tⱼ ∈ fs(Aⱼ, W)`, and the induction hypothesis is
//! stated pointwise over its own domain:
//!
//! ```text
//!     ⋀ⱼ tⱼ ∈ fs(Aⱼ, W)      ⋀ⱼ ∀z. (z ∈ Aⱼ → φ(app(tⱼ, z)))
//! ```
//!
//! The grain is [`Inductive::ctor_slot_domains`] and **not**
//! [`Inductive::rec_slot_domains`]: `φ` is applied to `ctorᵢ(y⃗,t⃗)` itself, so
//! the `t⃗` these binders range over are the constructor term's own arguments,
//! and a mixed constructor's plain slot is a function out of `1` there. That
//! choice is forced, not preferred — `ctor_term` cannot be written at the other
//! grain — and it is what makes [`decl_rect`]'s case analysis able to hand the
//! step the restriction `f|ⱼ` it projects out of the packed fibre function.
//!
//! `decl_rect` is a **scheme**: `φ` is a formula of the ambient language, so
//! there is one theorem per `φ`, built on demand, and each call mints the
//! Separation symbol [`crate::wtype::w_rect`] runs W2 at. Build it once per
//! `(declaration, φ)` and cache it with the result.
//!
//! # Why this is not `w_rect`, and what the gap costs
//!
//! [`crate::wtype::w_rect`]'s minor premise speaks of `⟨a,f⟩` for an arbitrary
//! `a ∈ A` and `f ∈ fs(B(a), W)`. A declaration's induction principle speaks of
//! `ctorᵢ(y⃗,t⃗)`, and the two are the same element only after three inversions,
//! none of which `w_rect` performs:
//!
//! * `a ∈ A = Sum_n(A⃗)` is some `Injᵢ(σ)` with `σ ∈ Aᵢ` —
//!   [`crate::isum::ISumSyms::no_junk`];
//! * `σ ∈ Aᵢ` is the tuple of its own components —
//!   [`crate::sigma::Telescope::eta`];
//! * `f ∈ fs(finord(m), W)` is the recursive-argument function of its own
//!   values — **[`recarg_eta`], which did not exist**: `crate::recarg` proves
//!   the typing rule and the `m` computation rules and never inverts a given
//!   `f`. It is derived here, from [`Machine::fs_ext`] plus `no_junk` at
//!   `finord(m) = Sum_m(1,…,1)` and [`crate::sums::Sums::unit_eta`] to
//!   enumerate the domain — the `crate::cumul::finord` argument, at the
//!   function rather than at the set. At the **general** fibre the same rule
//!   holds of the `m` restrictions `f|ⱼ` instead of the `m` values, and there
//!   `unit_eta` is dropped and [`crate::isum::Branch`] spent in its place.
//!
//! [`super::typed`] gets away without the last two because it *instantiates*
//! `minor_typedᵢ` at `compⱼ(σ)` and `app(f, Injⱼ(•))` and never has to write
//! `⟨a,f⟩` as a constructor. An induction principle has to, because `φ` is
//! applied to the carrier element itself.
//!
//! # Nothing here is an axiom
//!
//! One Separation per `φ` (inside `w_rect`) and instances of lemmas that
//! already existed. Function extensionality is [`Machine::fs_ext`]'s memo —
//! **one** Extensionality instance per apparatus, not one per `φ`.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::isum::Branch;
use crate::sigma::Telescope;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::rect::{ind_step, w_rect, Params};
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, disj_of, ex_falso, gen_all, hyp_and, hyp_mp,
    imp_refl, inst_all, syl, uncurry,
};

use super::carrier::Inductive;
use super::machine::Machine;
use super::rec_shared::{
    gen_under, hyp_conj, hyp_disj_elim, hyp_ex_branch, hyp_inst, rewrite_under, under,
};

// ─────────────────────────────────────────────────────────────────────────────
// The premise
// ─────────────────────────────────────────────────────────────────────────────

/// `rect_stepᵢ(φ)` — the `i`-th constructor's induction step, as a formula.
///
/// Fresh bound variables each call; the kernel's de-Bruijn closure makes two
/// calls α-invariantly equal, so a caller discharging the premise can rebuild
/// exactly what [`decl_rect`] consumes. `None` if `i` is out of range or the
/// constructor term cannot be built over `mach` ([`Inductive::is_over`]).
pub fn rect_step(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Formula> {
    let ctor = ind.spec.ctors.get(i)?;
    let (k, m) = (ctor.args.len(), ctor.recs);
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();

    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    let s = &mach.wt.sums;
    let doms = ind.ctor_slot_domains(i);
    if doms.len() != m {
        return None
    }
    for j in 0..m {
        atoms.push(match &doms[j] {
            None => Formula::mem(ts[j].clone(), ind.wty.clone()),
            Some(a) => Formula::mem(ts[j].clone(), s.fs.of(a.clone(), ind.wty.clone())),
        });
    }
    for j in 0..m {
        atoms.push(match &doms[j] {
            None => phi.subst(zv, &ts[j]),
            Some(a) => {
                let zz = env.fresh_var();
                Formula::forall(
                    zz,
                    Formula::imp(
                        Formula::mem(Term::var(zz), a.clone()),
                        phi.subst(zv, &s.ap.apply(ts[j].clone(), Term::var(zz))),
                    ),
                )
            }
        });
    }

    let concl = phi.subst(zv, &ind.ctor_term(mach, i, &ys, &ts)?);
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    Some(quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc)))
}

/// `RECT(φ)`, the right-nested conjunction of every [`rect_step`]. `None` for a
/// declaration with no constructors — whose carrier is empty, so the conclusion
/// holds for nothing and there is no induction to state.
pub fn rect_hyp(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Formula> {
    let parts = rect_parts(env, mach, ind, zv, phi)?;
    conj_of(&parts)
}

/// The conjuncts of [`rect_hyp`], for a caller that projects them one at a
/// time. `None` for a declaration with no constructors.
pub fn rect_parts(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Vec<Formula>> {
    if ind.spec.ctors.is_empty() {
        return None
    }
    (0..ind.spec.ctors.len())
        .map(|i| rect_step(env, mach, ind, i, zv, phi))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// The inversion `crate::recarg` does not prove
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀S ∀f. (f ∈ fs(finord(m), S) → f = recfun(app(f,I₀(•)) … app(f,I_{m-1}(•))))`
/// — **η for the recursive-argument function**.
///
/// Every function out of the `m`-element fibre *is* the canonical one built
/// from its own values. [`crate::recarg`] proves the two halves this needs —
/// `recfun(r⃗) ∈ fs(finord(m), S)` and `app(recfun(r⃗), Injⱼ(•)) = rⱼ` — and
/// stops there; what closes the loop is function extensionality plus an
/// enumeration of the domain, since `finord(m)` is `Sum_m(1,…,1)` and
/// `no_junk` followed by `unit_eta` says its only members are the `m` points
/// `Injⱼ(•)`.
///
/// At a constructor that takes [`RecArg::general`](crate::recarg::RecArg::general) the statement is the same
/// one at the general fibre, with the `m` **values** replaced by the `m`
/// **restrictions** [`crate::isum::Branch`] projects out:
///
/// ```text
/// ⊢ ∀S ∀f. (f ∈ fs(Sum_m(A⃗), S) → f = recfun(f|₀ … f|_{m-1}))
/// ```
///
/// and three of the four moves are the same. What changes: `no_junk` at `A⃗`
/// hands back a witness `z ∈ Aⱼ` that **is not `•`**, so `Sums::unit_eta` has
/// nothing to say and the witness is kept; [`RecArg::app`](crate::recarg::RecArg::app) is conditional on
/// the branches being functions, which is [`crate::isum::branch_in_funspace`]
/// at `f`'s own typing; and the step from `app(f, Injⱼ(z))` to `app(f|ⱼ, z)` is
/// [`Branch::app`], which the plain path does not need because there the value
/// *is* `app(f, Injⱼ(•))`. The note that scoped this named the first two and
/// not the third.
///
/// **The right-hand side goes through [`Inductive::recfun_of`]**, the same
/// funnel [`Inductive::ctor_term`] uses, so the η rule cannot identify `f` with
/// a dispatcher no constructor of this declaration is built from — the defect
/// `4ba0904` fixed in the other direction.
///
/// `fs_ext` must be [`Machine::fs_ext`] over the same apparatus. At `m = 0` the
/// pointwise premise is vacuous — `Sum_0()` has no members at all — and the
/// conclusion is `f = ∅`. `None` if `i` is out of range or `ind` was not
/// translated over `mach`.
pub fn recarg_eta(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    fs_ext: &Thm,
) -> Option<Thm> {
    if !ind.is_over(mach) {
        return None
    }
    if ind.recargs.get(i)?.hyp.is_some() {
        return recarg_eta_general(env, mach, ind, i, fs_ext)
    }
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ra = &ind.recargs[i];
    let m = ra.m;
    let fin = mach.syms.finord(s, m)?;

    let (sv, fv) = (env.fresh_var(), env.fresh_var());
    let (t_s, tf) = (Term::var(sv), Term::var(fv));
    let h = Formula::mem(tf.clone(), s.fs.of(fin.clone(), t_s.clone()));

    let pts: Vec<Term> = (0..m).map(|j| mach.syms.inj(j, s.point())).collect::<Option<_>>()?;
    let vals: Vec<Term> = pts.iter().map(|p| ap.apply(tf.clone(), p.clone())).collect();
    let g = ind.recfun_of(mach, i, &vals)?;

    // `⊢ h → app(f, Injⱼ(•)) ∈ S`, one per point of the fibre.
    let mut h_vals = Vec::with_capacity(m);
    for (j, pt_j) in pts.iter().enumerate() {
        let rule = inst_all(
            &mach.wt.app_mem,
            &[fin.clone(), t_s.clone(), tf.clone(), pt_j.clone()],
        )?;
        let pt = under(&inj_pt_mem(mach, m, j)?, &h);
        h_vals.push(hyp_mp(&a1i(&rule, h.clone()), &hyp_and(&imp_refl(h.clone()), &pt)?)?);
    }

    // `⊢ h → g ∈ fs(finord(m), S)`.
    let mut fs_args = vec![t_s.clone()];
    fs_args.extend(vals.iter().cloned());
    let g_typed_rule = inst_all(&ra.in_funspace, &fs_args)?;
    let h_g = match hyp_conj(&h_vals) {
        Some(prem) => hyp_mp(&a1i(&g_typed_rule, h.clone()), &prem)?,
        None => under(&g_typed_rule, &h),
    };

    // ── the pointwise premise ───────────────────────────────────────────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let mx = Formula::mem(tx.clone(), fin.clone());
    let agree = Formula::eq(ap.apply(tf.clone(), tx.clone()), ap.apply(g.clone(), tx.clone()));
    let hx = Formula::and(h.clone(), mx.clone());
    let hx_mx = and_right(h.clone(), mx.clone());

    let body = if m == 0 {
        // `Sum_0()` is empty: the premise is vacuous.
        let empty = inst_all(&mach.syms.no_junk(env, s, 0)?, std::slice::from_ref(&tx))?;
        if *empty.concl() != Formula::not(mx.clone()) {
            return None
        }
        syl(&hx_mx, &syl(&empty, &ex_falso(agree.clone()))?)?
    } else {
        let nj = mach.syms.no_junk(env, s, m)?;
        let mut nj_args: Vec<Term> = (0..m).map(|_| s.unit()).collect();
        nj_args.push(tx.clone());
        let nj_at = inst_all(&nj, &nj_args)?;
        let cvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
        let bodies: Vec<Formula> = (0..m)
            .map(|j| {
                let tc = Term::var(cvs[j]);
                Some(Formula::and(
                    Formula::mem(tc.clone(), s.unit()),
                    Formula::eq(tx.clone(), mach.syms.inj(j, tc)?),
                ))
            })
            .collect::<Option<_>>()?;
        let disjuncts: Vec<Formula> =
            (0..m).map(|j| Formula::exists(cvs[j], bodies[j].clone())).collect();
        if *nj_at.concl() != Formula::imp(mx.clone(), disj_of(&disjuncts)?) {
            return None
        }
        let cases = syl(&hx_mx, &nj_at)?;

        let mut branches = Vec::with_capacity(m);
        for j in 0..m {
            let tc = Term::var(cvs[j]);
            let k = Formula::and(hx.clone(), bodies[j].clone());
            let k_body = and_right(hx.clone(), bodies[j].clone());
            let mem_c = Formula::mem(tc.clone(), s.unit());
            let eq_x = Formula::eq(tx.clone(), mach.syms.inj(j, tc.clone())?);
            let k_c = syl(&k_body, &and_left(mem_c.clone(), eq_x.clone()))?;
            let k_x = syl(&k_body, &and_right(mem_c, eq_x))?;

            // `c = •`, so `x = Injⱼ(•)`.
            let k_pt = syl(&k_c, &inst_all(&s.unit_eta, std::slice::from_ref(&tc))?)?;
            let inj_j = mach.syms.inj_sym(j)?;
            let k_inj = hyp_congr(env, &k_pt, move |q| Term::apply(inj_j, vec![q]))?;
            let k_at = hyp_eq_trans(env, &k_x, &k_inj)?;

            // `app(f,x) = app(f,Iⱼ) = app(g,Iⱼ) = app(g,x)`.
            let tf_c = tf.clone();
            let e_f = hyp_congr(env, &k_at, move |q| ap.apply(tf_c.clone(), q))?;
            let raw = inst_all(&ra.app[j], &vals)?;
            let e_g0 = hyp_eq_symm(env, &under(&raw, &k))?;
            let g_c = g.clone();
            let back = hyp_eq_symm(env, &k_at)?;
            let e_g1 = hyp_congr(env, &back, move |q| ap.apply(g_c.clone(), q))?;
            let half = hyp_eq_trans(env, &e_f, &e_g0)?;
            let step = hyp_eq_trans(env, &half, &e_g1)?;
            branches.push(hyp_ex_branch(cvs[j], &step, &hx, &agree)?);
        }
        hyp_disj_elim(&cases, &hx, &branches)?
    };

    // ── function extensionality ─────────────────────────────────────────────
    let pw = Formula::forall(xv, Formula::imp(mx.clone(), agree.clone()));
    if pw != crate::ext::pointwise(env, ap, &fin, &tf, &g) {
        return None
    }
    let h_pw = gen_under(xv, &h, &uncurry(&body)?)?;
    let rule = inst_all(fs_ext, &[fin.clone(), t_s.clone(), tf.clone(), g.clone()])?;
    let out = hyp_mp(
        &a1i(&rule, h.clone()),
        &hyp_and(&imp_refl(h.clone()), &hyp_and(&h_g, &h_pw)?)?,
    )?;
    if *out.concl() != Formula::imp(h, Formula::eq(tf, g)) {
        return None
    }
    Some(gen_all(&[sv, fv], &out))
}

/// [`recarg_eta`] at the **general** fibre. See that function's header for the
/// statement and for which three moves differ from the plain one.
fn recarg_eta_general(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    fs_ext: &Thm,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ra = &ind.recargs[i];
    let m = ra.m;
    let doms = ra.summands.clone();
    let dom = ra.domain.clone();
    if m == 0 || doms.len() != m {
        return None
    }

    let (sv, fv) = (env.fresh_var(), env.fresh_var());
    let (t_s, tf) = (Term::var(sv), Term::var(fv));
    let h = Formula::mem(tf.clone(), s.fs.of(dom.clone(), t_s.clone()));

    // The `m` restrictions, and the dispatcher over them.
    let brs: Vec<std::rc::Rc<Branch>> =
        (0..m).map(|j| mach.syms.branch(env, s, j)).collect::<Option<_>>()?;
    let gs: Vec<Term> = (0..m).map(|j| brs[j].of(tf.clone(), doms[j].clone())).collect();
    let g = ind.recfun_of(mach, i, &gs)?;

    // `⊢ h → H`, `RecArg::general`'s own antecedent at these branches.
    let mut h_gs = Vec::with_capacity(m);
    for j in 0..m {
        let bfs = mach.syms.branch_in_funspace(env, s, &mach.wt.app_mem, m, j)?;
        let mut a = doms.clone();
        a.push(t_s.clone());
        a.push(tf.clone());
        h_gs.push(inst_all(&bfs, &a)?);
    }
    let h_hyp = hyp_conj(&h_gs)?;

    // `⊢ h → g ∈ fs(Sum_m(A⃗), S)`.
    let mut fs_args = vec![t_s.clone()];
    fs_args.extend(gs.iter().cloned());
    let h_g = hyp_mp(&a1i(&inst_all(&ra.in_funspace, &fs_args)?, h.clone()), &h_hyp)?;

    // ── the pointwise premise ───────────────────────────────────────────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let mx = Formula::mem(tx.clone(), dom.clone());
    let agree = Formula::eq(ap.apply(tf.clone(), tx.clone()), ap.apply(g.clone(), tx.clone()));
    let hx = Formula::and(h.clone(), mx.clone());
    let hx_h = and_left(h.clone(), mx.clone());
    let hx_mx = and_right(h.clone(), mx.clone());

    let nj = mach.syms.no_junk(env, s, m)?;
    let mut nj_args = doms.clone();
    nj_args.push(tx.clone());
    let nj_at = inst_all(&nj, &nj_args)?;
    let cvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let bodies: Vec<Formula> = (0..m)
        .map(|j| {
            let tc = Term::var(cvs[j]);
            Some(Formula::and(
                Formula::mem(tc.clone(), doms[j].clone()),
                Formula::eq(tx.clone(), mach.syms.inj(j, tc)?),
            ))
        })
        .collect::<Option<_>>()?;
    let disjuncts: Vec<Formula> =
        (0..m).map(|j| Formula::exists(cvs[j], bodies[j].clone())).collect();
    if *nj_at.concl() != Formula::imp(mx.clone(), disj_of(&disjuncts)?) {
        return None
    }
    let cases = syl(&hx_mx, &nj_at)?;

    let mut branches = Vec::with_capacity(m);
    for j in 0..m {
        let tc = Term::var(cvs[j]);
        let k = Formula::and(hx.clone(), bodies[j].clone());
        let k_hx = and_left(hx.clone(), bodies[j].clone());
        let k_body = and_right(hx.clone(), bodies[j].clone());
        let mem_c = Formula::mem(tc.clone(), doms[j].clone());
        let eq_x = Formula::eq(tx.clone(), mach.syms.inj(j, tc.clone())?);
        let k_c = syl(&k_body, &and_left(mem_c.clone(), eq_x.clone()))?;
        let k_x = syl(&k_body, &and_right(mem_c, eq_x))?;
        let k_h = syl(&k_hx, &hx_h)?;

        // `app(f,x) = app(f, Injⱼ(z))`, the witness kept rather than collapsed.
        let tf_c = tf.clone();
        let e_f = hyp_congr(env, &k_x, move |q| ap.apply(tf_c.clone(), q))?;

        // `app(f, Injⱼ(z)) = app(f|ⱼ, z)` — `Branch::app`, reversed.
        let br_at = inst_all(&brs[j].app, &[tf.clone(), doms[j].clone(), tc.clone()])?;
        let e_br = hyp_eq_symm(env, &hyp_mp(&a1i(&br_at, k.clone()), &k_c)?)?;

        // `app(f|ⱼ, z) = app(g, Injⱼ(z))` — `RecArg::app[j]`, reversed, its two
        // antecedents `H` and `z ∈ Aⱼ` discharged.
        let mut a = vec![t_s.clone()];
        a.extend(gs.iter().cloned());
        a.push(tc.clone());
        let raw = inst_all(&ra.app[j], &a)?;
        let k_hyp = syl(&k_h, &h_hyp)?;
        let e_g0 =
            hyp_eq_symm(env, &hyp_mp(&hyp_mp(&a1i(&raw, k.clone()), &k_hyp)?, &k_c)?)?;

        // `app(g, Injⱼ(z)) = app(g, x)`.
        let g_c = g.clone();
        let back = hyp_eq_symm(env, &k_x)?;
        let e_g1 = hyp_congr(env, &back, move |q| ap.apply(g_c.clone(), q))?;

        let step = hyp_eq_trans(env, &e_f, &e_br)?;
        let step = hyp_eq_trans(env, &step, &e_g0)?;
        let step = hyp_eq_trans(env, &step, &e_g1)?;
        branches.push(hyp_ex_branch(cvs[j], &step, &hx, &agree)?);
    }
    let body = hyp_disj_elim(&cases, &hx, &branches)?;

    // ── function extensionality ─────────────────────────────────────────────
    let pw = Formula::forall(xv, Formula::imp(mx.clone(), agree.clone()));
    if pw != crate::ext::pointwise(env, ap, &dom, &tf, &g) {
        return None
    }
    let h_pw = gen_under(xv, &h, &uncurry(&body)?)?;
    let rule = inst_all(fs_ext, &[dom.clone(), t_s.clone(), tf.clone(), g.clone()])?;
    let out = hyp_mp(
        &a1i(&rule, h.clone()),
        &hyp_and(&imp_refl(h.clone()), &hyp_and(&h_g, &h_pw)?)?,
    )?;
    if *out.concl() != Formula::imp(h, Formula::eq(tf, g)) {
        return None
    }
    Some(gen_all(&[sv, fv], &out))
}

/// `⊢ Injⱼ(•) ∈ finord(m)` — unconditional. [`super::step::Rx`]'s own
/// `inj_pt_mem`, rebuilt here so this file needs no recursor context.
fn inj_pt_mem(mach: &Machine, m: usize, j: usize) -> Option<Thm> {
    let s = &mach.wt.sums;
    let mut args: Vec<Term> = (0..m).map(|_| s.unit()).collect();
    args.push(s.point());
    Thm::mp(&inst_all(mach.syms.inj_mem(m, j)?, &args)?, &s.unit_mem)
}

// ─────────────────────────────────────────────────────────────────────────────
// The principle
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ RECT(φ) → ∀z. (z ∈ W → φ(z))` — structural induction over the
/// declaration's carrier.
///
/// `zv` is the variable `phi` speaks about and must not be free in anything
/// else the caller cares about; every other free variable of `phi` is carried
/// into the Separation symbol `w_rect` mints, so `phi` may mention the
/// parameters, a motive, minors, or a recursor term at them.
///
/// `None` unless `ind` was translated over `mach` and has at least one
/// constructor, or if any internal shape check fails.
pub fn decl_rect(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Thm> {
    let n = ind.spec.ctors.len();
    if n == 0 || !ind.is_over(mach) {
        return None
    }
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let w = ind.wty.clone();
    let tags = ind.tags.clone();
    let fam = ind.fibre.fam.clone();

    let parts = rect_parts(env, mach, ind, zv, phi)?;
    let hyp = conj_of(&parts)?;

    // ── `w_rect` at the declaration's own `A`, `B` and bound ────────────────
    let (av, bv, uv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let mut params: Vec<FreeVar> = Vec::new();
    phi.free_vars(&mut params);
    params.retain(|v| *v != zv);
    params.extend([av, bv, uv]);
    params.sort_unstable();
    params.dedup();
    let generic = w_rect(env, &mach.wt, &params, Params { a: av, b: bv, u: uv }, zv, phi)?;
    let at = inst_all(&gen_all(&[av, bv, uv], &generic), &[tags.clone(), fam.clone(), ind.bound.clone()])?;
    let rule = Thm::mp(&at, &ind.closed)?;

    let step_f = ind_step(env, s, &w, &tags, &fam, zv, phi);
    let goal_all = {
        let zt = Term::var(zv);
        Formula::forall(zv, Formula::imp(Formula::mem(zt, w.clone()), phi.clone()))
    };
    if *rule.concl() != Formula::imp(step_f.clone(), goal_all.clone()) {
        return None
    }

    // ── derive `ind_step(φ)` from `RECT(φ)` ─────────────────────────────────
    let (iv, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(iv), Term::var(fv));
    let fibre_t = ap.apply(fam.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre_t.clone(), w.clone()));
    let bvv = env.fresh_var();
    let tb = Term::var(bvv);
    let ihf = Formula::forall(
        bvv,
        Formula::imp(
            Formula::mem(tb.clone(), fibre_t.clone()),
            phi.subst(zv, &ap.apply(tf.clone(), tb.clone())),
        ),
    );
    let hm = Formula::and(hyp.clone(), ma.clone());
    let front = Formula::and(hm.clone(), mf.clone());
    let p = Formula::and(front.clone(), ihf.clone());
    let sup = s.ap.sets.pair(ta.clone(), tf.clone());
    let goal = phi.subst(zv, &sup);

    let p_front = and_left(front.clone(), ihf.clone());
    let p_ih = and_right(front.clone(), ihf.clone());
    let p_hm = syl(&p_front, &and_left(hm.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(hm.clone(), mf.clone()))?;
    let p_hyp = syl(&p_hm, &and_left(hyp.clone(), ma.clone()))?;
    let p_ma = syl(&p_hm, &and_right(hyp.clone(), ma.clone()))?;

    // `no_junk` splits the tag, exactly as `super::typed` does.
    let nj = mach.syms.no_junk(env, s, n)?;
    let mut nj_args: Vec<Term> = ind.summands.clone();
    nj_args.push(ta.clone());
    let nj_at = inst_all(&nj, &nj_args)?;
    let sigvs: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let bodies: Vec<Formula> = (0..n)
        .map(|i| {
            let tsig = Term::var(sigvs[i]);
            Some(Formula::and(
                Formula::mem(tsig.clone(), ind.summands[i].clone()),
                Formula::eq(ta.clone(), mach.syms.inj(i, tsig)?),
            ))
        })
        .collect::<Option<_>>()?;
    let disjuncts: Vec<Formula> =
        (0..n).map(|i| Formula::exists(sigvs[i], bodies[i].clone())).collect();
    if *nj_at.concl() != Formula::imp(ma.clone(), disj_of(&disjuncts)?) {
        return None
    }
    let cases = syl(&p_ma, &nj_at)?;

    let fs_ext = mach.fs_ext(env)?;

    let mut branches = Vec::with_capacity(n);
    for i in 0..n {
        let (k, m) = (ind.spec.ctors[i].args.len(), ind.spec.ctors[i].recs);
        let tsig = Term::var(sigvs[i]);
        // The **constructor's own** fibre, `Sum_{mᵢ}(A⃗)` — literally
        // `finord(mᵢ)` at a plain constructor, which is why the plain path
        // below is unchanged.
        let doms = ind.ctor_slot_domains(i);
        let fin = ind.recargs[i].domain.clone();
        debug_assert!(
            doms.iter().any(|d| d.is_some()) || fin == mach.syms.finord(s, m).expect("finord"),
            "rect: a plain constructor's fibre is not finord(m)"
        );
        let kf = Formula::and(p.clone(), bodies[i].clone());
        let k_p = and_left(p.clone(), bodies[i].clone());
        let k_body = and_right(p.clone(), bodies[i].clone());
        let mem_sig = Formula::mem(tsig.clone(), ind.summands[i].clone());
        let eq_a = Formula::eq(ta.clone(), mach.syms.inj(i, tsig.clone())?);
        let k_sig = syl(&k_body, &and_left(mem_sig.clone(), eq_a.clone()))?;
        let k_a = syl(&k_body, &and_right(mem_sig, eq_a))?;

        // The fibre at this tag is `finord(mᵢ)`.
        let k_acong = hyp_congr(env, &k_a, |q| ap.apply(fam.clone(), q))?;
        let fib_at = inst_all(&ind.fibre.fibre[i], std::slice::from_ref(&tsig))?;
        let k_fib = hyp_eq_trans(env, &k_acong, &syl(&k_sig, &fib_at)?)?;

        // `f`, retyped to that fibre.
        let k_mf = syl(&k_p, &p_mf)?;
        let (w_c, tf_c) = (w.clone(), tf.clone());
        let k_f = rewrite_under(
            env,
            &k_fib,
            move |q| Formula::mem(tf_c.clone(), s.fs.of(q, w_c.clone())),
            &k_mf,
        )?;

        // The fields, and their typings.
        let ys: Vec<Term> = (0..k)
            .map(|j| Telescope::comp_of(ap, &mach.proj, j, tsig.clone()))
            .collect();
        // What the constructor's `j`-th recursive slot *is*, read out of the
        // packed fibre function: the value `app(f, Injⱼ(•))` at a plain
        // constructor, and the restriction `f|ⱼ` at a general one — the same
        // projection [`super::step::Rx::fibre_apps`] chooses, at the other
        // grain.
        let brs: Vec<Option<std::rc::Rc<Branch>>> = doms
            .iter()
            .enumerate()
            .map(|(j, d)| match d {
                None => Some(None),
                Some(_) => Some(Some(mach.syms.branch(env, s, j)?)),
            })
            .collect::<Option<_>>()?;
        let ts: Vec<Term> = (0..m)
            .map(|j| match (&doms[j], &brs[j]) {
                (Some(a), Some(br)) => Some(br.of(tf.clone(), a.clone())),
                _ => Some(ap.apply(tf.clone(), mach.syms.inj(j, s.point())?)),
            })
            .collect::<Option<_>>()?;

        let mut atoms: Vec<Thm> = Vec::with_capacity(k + 2 * m);
        for j in 0..k {
            let mut a = ps.clone();
            a.push(tsig.clone());
            atoms.push(syl(&k_sig, &inst_all(&ind.telescopes[i].proj_mem[j], &a)?)?);
        }
        for j in 0..m {
            atoms.push(match &doms[j] {
                None => {
                    let rule = inst_all(
                        &mach.wt.app_mem,
                        &[fin.clone(), w.clone(), tf.clone(), mach.syms.inj(j, s.point())?],
                    )?;
                    let pt = under(&inj_pt_mem(mach, m, j)?, &kf);
                    hyp_mp(&a1i(&rule, kf.clone()), &hyp_and(&k_f, &pt)?)?
                }
                Some(_) => {
                    let bfs =
                        mach.syms.branch_in_funspace(env, s, &mach.wt.app_mem, m, j)?;
                    let mut a: Vec<Term> =
                        doms.iter().map(|d| d.clone().expect("general")).collect();
                    a.push(w.clone());
                    a.push(tf.clone());
                    syl(&k_f, &inst_all(&bfs, &a)?)?
                }
            });
        }
        // The induction hypotheses. At a plain slot `ihf` is read off at the
        // `m` fibre points; at a function-typed one it is kept **pointwise**
        // over `Aⱼ`, because that is the shape `rect_step` states and the shape
        // Lean's minor premise takes.
        for j in 0..m {
            let k_ih = syl(&k_p, &p_ih)?;
            let back = hyp_eq_symm(env, &k_fib)?;
            atoms.push(match &doms[j] {
                None => {
                    let pt = mach.syms.inj(j, s.point())?;
                    let at_pt = hyp_inst(&k_ih, std::slice::from_ref(&pt))?;
                    let pt_c = pt.clone();
                    let k_pt_mem = rewrite_under(
                        env,
                        &back,
                        move |q| Formula::mem(pt_c.clone(), q),
                        &under(&inj_pt_mem(mach, m, j)?, &kf),
                    )?;
                    hyp_mp(&at_pt, &k_pt_mem)?
                }
                Some(a) => {
                    let br = brs[j].clone().expect("a function-typed slot has a branch");
                    let zz = env.fresh_var();
                    let tz = Term::var(zz);
                    let mem_z = Formula::mem(tz.clone(), a.clone());
                    let kz = Formula::and(kf.clone(), mem_z.clone());
                    let kz_kf = and_left(kf.clone(), mem_z.clone());
                    let kz_z = and_right(kf.clone(), mem_z);

                    // `Injⱼ(z) ∈ Sum_m(A⃗)`, then retyped to `app(fam, a)`.
                    let mut a_args: Vec<Term> =
                        doms.iter().map(|d| d.clone().expect("general")).collect();
                    a_args.push(tz.clone());
                    let inj_z = mach.syms.inj(j, tz.clone())?;
                    let k_inj_mem = hyp_mp(
                        &a1i(&inst_all(mach.syms.inj_mem(m, j)?, &a_args)?, kz.clone()),
                        &kz_z,
                    )?;
                    let inj_c = inj_z.clone();
                    let k_pt_mem = rewrite_under(
                        env,
                        &syl(&kz_kf, &back)?,
                        move |q| Formula::mem(inj_c.clone(), q),
                        &k_inj_mem,
                    )?;
                    let at_pt =
                        hyp_inst(&syl(&kz_kf, &k_ih)?, std::slice::from_ref(&inj_z))?;
                    let k_phi = hyp_mp(&at_pt, &k_pt_mem)?;

                    // `app(f|ⱼ, z) = app(f, Injⱼ(z))`, so `φ` transports.
                    let br_at = inst_all(&br.app, &[tf.clone(), a.clone(), tz.clone()])?;
                    let k_br = hyp_eq_symm(
                        env,
                        &hyp_mp(&a1i(&br_at, kz.clone()), &kz_z)?,
                    )?;
                    let k_at = rewrite_under(env, &k_br, |q| phi.subst(zv, &q), &k_phi)?;
                    gen_under(zz, &kf, &uncurry(&k_at)?)?
                }
            });
        }

        // `rect_stepᵢ` at those fields.
        let k_rs = syl(&syl(&k_p, &p_hyp)?, &conj_proj(&parts, i)?)?;
        let mut insts = ys.clone();
        insts.extend(ts.iter().cloned());
        let k_rs_at = hyp_inst(&k_rs, &insts)?;
        let k_ctor = match hyp_conj(&atoms) {
            Some(prem) => hyp_mp(&k_rs_at, &prem)?,
            None => k_rs_at,
        };

        // `ctorᵢ(y⃗,t⃗) = ⟨a,f⟩`, by the two η rules and the tag equation.
        let tuple = Telescope::tuple_of(s, &ys);
        let mut eta_args = ps.clone();
        eta_args.push(tsig.clone());
        let k_tel = syl(&k_sig, &inst_all(&ind.telescopes[i].eta, &eta_args)?)?;
        if *k_tel.concl() != Formula::imp(kf.clone(), Formula::eq(tuple.clone(), tsig.clone())) {
            return None
        }
        let inj_i = mach.syms.inj_sym(i)?;
        let k_tel_inj = hyp_congr(env, &k_tel, move |q| Term::apply(inj_i, vec![q]))?;
        let k_a_back = hyp_eq_symm(env, &k_a)?;
        let k_tag = hyp_eq_trans(env, &k_tel_inj, &k_a_back)?;
        let eta = recarg_eta(env, mach, ind, i, &fs_ext)?;
        let k_fun = hyp_eq_symm(
            env,
            &hyp_mp(&a1i(&inst_all(&eta, &[w.clone(), tf.clone()])?, kf.clone()), &k_f)?,
        )?;
        // `⟨Injᵢ(tuple), recfun(t⃗)⟩ = ⟨Injᵢ(tuple), f⟩ = ⟨a, f⟩`: the recursive
        // slot first, so the tag rewrite lands on the already-finished pair.
        //
        // This *is* the structure η rule, and it is deliberately not exported.
        // It is stated at the existential witnesses `a`, `f` and `σᵢ` under this
        // case analysis's own context, so surfacing it means discharging them —
        // which is re-running the analysis with η as the goal, i.e.
        // `decl_rect` at a `φ` that mentions `z`. [`super::decl_proj`] is that,
        // and its `DeclProj::eta` is the export, stated `∀z` at terms a consumer
        // can name. Nothing is lost here; the right place was one layer up.
        let k_eq = {
            let sets = ap.sets.clone();
            let (sets2, head, tf_c) = (sets.clone(), mach.syms.inj(i, tuple.clone())?, tf.clone());
            let right = hyp_congr(env, &k_fun, move |q| sets.pair(head.clone(), q))?;
            let left = hyp_congr(env, &k_tag, move |q| sets2.pair(q, tf_c.clone()))?;
            hyp_eq_trans(env, &right, &left)?
        };

        let k_goal = rewrite_under(env, &k_eq, |q| phi.subst(zv, &q), &k_ctor)?;
        if *k_goal.concl() != Formula::imp(kf.clone(), goal.clone()) {
            return None
        }
        branches.push(hyp_ex_branch(sigvs[i], &k_goal, &p, &goal)?);
    }

    let body = hyp_disj_elim(&cases, &p, &branches)?;
    let over_f = gen_under(fv, &hm, &uncurry(&uncurry(&body)?)?)?;
    let over_a = gen_under(iv, &hyp, &uncurry(&over_f)?)?;
    if *over_a.concl() != Formula::imp(hyp.clone(), step_f) {
        return None
    }
    let out = syl(&over_a, &rule)?;
    if !crate::establishes(&out, &Formula::imp(hyp, goal_all)) {
        return None
    }
    Some(out)
}
