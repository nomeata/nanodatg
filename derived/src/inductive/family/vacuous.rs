//! **Emptiness at an index no constructor produces** — the negative polarity of
//! the non-vacuity discipline, in its strong form.
//!
//! # What this is for
//!
//! [`super::carrier`]'s inversion rule (I) already refutes *a given
//! constructor term* being in the carrier at the wrong index, and that is what
//! `INDEXED-DESIGN.md` §4.4 asks for. It is not the strongest statement
//! available, and the stronger one is what actually rules out a `good` that
//! returns `Idx` everywhere:
//!
//! ```text
//! ⊢ ∀z. ¬( z ∈ ind(p⃗, x⃗) )
//! ```
//!
//! for an index vector `x⃗` that **no** constructor's result index can equal.
//! An always-true `good` satisfies every membership theorem and every
//! inversion theorem whose constructor happens not to be applied; it cannot
//! satisfy this one.
//!
//! # What the caller owes, and why that is the right split
//!
//! One refutation per constructor:
//!
//! ```text
//! refutationsᵢ  :  ⊢ ∀y₀ … y_{kᵢ−1}. ¬( tup(x⃗) = tup(e⃗ᵢ(p⃗, y⃗)) )
//! ```
//!
//! — "constructor `i` cannot land at `x⃗`, whatever its fields are". That is
//! the only thing about the index *expressions* this file could not derive:
//! they are opaque `FnSym`s, and whether `Color.r` differs from `Color.b` is a
//! fact about the index types' own translation, not about the family. For
//! `RBTree` at `⟨Color.r, …⟩` the three refutations are one Kuratowski
//! injectivity plus the enum's tag distinctness each. Everything else — the
//! W-inversion, the ι at a *non-constructor* element of the skeleton, the tag
//! split, the `Gᵢ` unfolding — is here.
//!
//! # Why no induction is needed
//!
//! `tup(x⃗) ∈ app(goodrec, s)` is refutable at **every** `s ∈ W` directly, with
//! no appeal to the refutation holding at `s`'s children: `good`'s base-case
//! conjunct already forces `tup(x⃗) = tup(e⃗ᵢ(…))`. So what is needed is not
//! `w_rect` but only "every element of `W` is a `sup`" —
//! [`crate::wtype::w_inversion`], whose `closed(A,B,u)` antecedent the carrier
//! discharges. The recursion in the *statement* is real; the proof has none.
//!
//! # Interface
//!
//! [`empty_at_index`] — `⊢ ∀p⃗ ∀z. ¬(z ∈ ind(p⃗, x⃗))`, unconditional, at
//! caller-supplied index **terms** (not variables: the interesting instances
//! are closed).

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{
    gen_under, hyp_disj_elim, hyp_ex_branch, rewrite_under, under,
};
use crate::sigma::Telescope;
use crate::wrec::comp_of;
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, disj_of, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};

use super::carrier::IndexedCarrier;
use super::good::Good;
use super::goodstep::{branch_value, BranchFacts, GoodStep};
use super::gval::GoodValues;
use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// `⊢ ∀p⃗ ∀z. ¬(z ∈ ind(p⃗, x⃗))` — the family is **empty** at `x⃗`.
///
/// `xs` are the index terms, stated at the declaration's own **parameter
/// variables** (which is what everything else here is stated at, and what the
/// final generalisation closes over); `refutations[i]` must be
/// `⊢ ∀y⃗. ¬(tup(x⃗) = tup(e⃗ᵢ(p⃗, y⃗)))` with an **empty hypothesis set**, both of
/// which are checked against the rebuilt statement. `None` if any check fails.
#[allow(clippy::too_many_arguments)]
pub fn empty_at_index(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    spec: &IndexedDeclSpec,
    ix: &IndexSpace,
    gv: &GoodValues,
    gs: &GoodStep,
    good: &Good,
    ixc: &IndexedCarrier,
    rc: &Recursor,
    xs: &[Term],
    refutations: &[Thm],
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let n = spec.len();
    if xs.len() != spec.num_indices() || refutations.len() != n {
        return None
    }
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tup_x = IndexedDeclSpec::tup(s, xs);
    let carrier_x = ixc.ty_of(&ps, xs)?;
    let w = ind.wty.clone();
    let t = ix.target.clone();
    let fls = Formula::false_();

    // Each refutation says exactly what it must, and rests on nothing.
    for (i, r) in refutations.iter().enumerate() {
        let yvs: Vec<kernel::FreeVar> =
            (0..spec.base.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let want = yvs.iter().rev().fold(
            Formula::not(Formula::eq(
                tup_x.clone(),
                IndexedDeclSpec::tup(s, &spec.result_vec(i, &ps, &ys)?),
            )),
            |acc, v| Formula::forall(*v, acc),
        );
        if !r.hyps().is_empty() || *r.concl() != want {
            return None
        }
    }

    // ── the ambient: `z ∈ ind(p⃗,x⃗)` ─────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mem = Formula::mem(tz.clone(), carrier_x.clone());
    let mut ca = ps.clone();
    ca.extend(xs.iter().cloned());
    ca.push(tz.clone());
    let m_w = inst_all(&ixc.subset_w, &ca)?;
    let m_gd = inst_all(&ixc.good_of, &ca)?;

    // ── every element of `W` is a `sup` ─────────────────────────────────────
    let inversion = crate::wtype::w_inversion(env, &mach.wt)?;
    let inv_at = Thm::mp(
        &inst_all(
            &inversion,
            &[ind.tags.clone(), ind.fibre.fam.clone(), ind.bound.clone()],
        )?,
        &ind.closed,
    )?;
    let m_sup = syl(&m_w, &inst_all(&inv_at, std::slice::from_ref(&tz))?)?;

    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let fibre_a = ap.apply(ind.fibre.fam.clone(), ta.clone());
    let mem_ta = Formula::mem(ta.clone(), ind.tags.clone());
    let mem_tf = Formula::mem(tf.clone(), s.fs.of(fibre_a.clone(), w.clone()));
    let eq_z = Formula::eq(tz.clone(), ap.sets.pair(ta.clone(), tf.clone()));
    let inner = Formula::and(mem_tf.clone(), eq_z.clone());
    let ex_f = Formula::exists(fv, inner.clone());
    let body_a = Formula::and(mem_ta.clone(), ex_f.clone());
    if *m_sup.concl() != Formula::imp(mem.clone(), Formula::exists(av, body_a.clone())) {
        return None
    }

    // ── under `K1 = mem ∧ body_a` and `K2 = K1 ∧ inner` ─────────────────────
    let k1 = Formula::and(mem.clone(), body_a.clone());
    let k1_mem = and_left(mem.clone(), body_a.clone());
    let k1_body = and_right(mem.clone(), body_a);
    let k1_aa = syl(&k1_body, &and_left(mem_ta.clone(), ex_f.clone()))?;
    let k1_ex = syl(&k1_body, &and_right(mem_ta, ex_f))?;

    let k2 = Formula::and(k1.clone(), inner.clone());
    let k2_k1 = and_left(k1.clone(), inner.clone());
    let k2_inner = and_right(k1.clone(), inner);
    let k2_f = syl(&k2_inner, &and_left(mem_tf, eq_z.clone()))?;
    let k2_eqz = syl(&k2_inner, &and_right(Formula::mem(tf.clone(), s.fs.of(fibre_a.clone(), w.clone())), eq_z))?;
    let k2_aa = syl(&k2_k1, &k1_aa)?;
    let k2_gd = syl(&syl(&k2_k1, &k1_mem)?, &m_gd)?;

    // `tup(x⃗) ∈ app(goodrec, ⟨a,f⟩)`.
    let k2_gd2 = {
        let (tx, rec) = (tup_x.clone(), good.rec.clone());
        let ap_c = ap.clone();
        rewrite_under(
            env,
            &k2_eqz,
            move |v| Formula::mem(tx.clone(), ap_c.apply(rec.clone(), v)),
            &k2_gd,
        )?
    };

    // The W-recursor's ι at `⟨a,f⟩`, both hypotheses already discharged.
    let cmp = comp_of(rc.comp, good.rec.clone(), tf.clone(), fibre_a.clone());
    let k2_iota = hyp_mp(
        &a1i(&inst_all(&good.wrec_iota, &[ta.clone(), tf.clone()])?, k2.clone()),
        &hyp_and(&k2_aa, &k2_f)?,
    )?;
    let k2_in_e = {
        let tx = tup_x.clone();
        rewrite_under(env, &k2_iota, move |v| Formula::mem(tx.clone(), v), &k2_gd2)?
    };

    // The ih row is typed — `good.funspace` twice through the application rule.
    let k2_cmp = {
        let bv = env.fresh_var();
        let tb = Term::var(bv);
        let mem_b = Formula::mem(tb.clone(), fibre_a.clone());
        let kf = Formula::and(k2.clone(), mem_b.clone());
        let k_k2 = and_left(k2.clone(), mem_b.clone());
        let k_b = and_right(k2.clone(), mem_b);
        let k_fb = hyp_mp(
            &a1i(
                &inst_all(
                    &mach.wt.app_mem,
                    &[fibre_a.clone(), w.clone(), tf.clone(), tb.clone()],
                )?,
                kf.clone(),
            ),
            &hyp_and(&syl(&k_k2, &k2_f)?, &k_b)?,
        )?;
        let k_gr = hyp_mp(
            &a1i(
                &inst_all(
                    &mach.wt.app_mem,
                    &[w.clone(), t.clone(), good.rec.clone(), ap.apply(tf.clone(), tb)],
                )?,
                kf.clone(),
            ),
            &hyp_and(&under(&good.funspace, &kf), &k_fb)?,
        )?;
        let vals = gen_under(bv, &k2, &uncurry(&k_gr)?)?;
        let comp_typed = crate::wrec_typing::composite_typed(env, s, rc.comp, &rc.comp_ax)?;
        hyp_mp(
            &a1i(
                &inst_all(
                    &comp_typed,
                    &[good.rec.clone(), tf.clone(), fibre_a.clone(), t.clone()],
                )?,
                k2.clone(),
            ),
            &vals,
        )?
    };

    // ── split the tag, and refute each branch ───────────────────────────────
    let cx = Good::rx(env, mach, ind, gv, ix)?;
    let nj = mach.syms.no_junk(env, s, n)?;
    let mut nj_args: Vec<Term> = ind.summands.clone();
    nj_args.push(ta.clone());
    let nj_at = inst_all(&nj, &nj_args)?;
    let sigvs: Vec<kernel::FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
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
    if *nj_at.concl() != Formula::imp(Formula::mem(ta.clone(), ind.tags.clone()), disj_of(&disjuncts)?)
    {
        return None
    }
    let cases = syl(&k2_aa, &nj_at)?;

    let mut branches = Vec::with_capacity(n);
    for i in 0..n {
        let tsig = Term::var(sigvs[i]);
        let k3 = Formula::and(k2.clone(), bodies[i].clone());
        let k3_k2 = and_left(k2.clone(), bodies[i].clone());
        let k3_body = and_right(k2.clone(), bodies[i].clone());
        let mem_sig = Formula::mem(tsig.clone(), ind.summands[i].clone());
        let eq_a = Formula::eq(ta.clone(), mach.syms.inj(i, tsig.clone())?);
        let k3_sig = syl(&k3_body, &and_left(mem_sig.clone(), eq_a.clone()))?;
        let k3_a = syl(&k3_body, &and_right(mem_sig, eq_a))?;
        let k3_f = syl(&k3_k2, &k2_f)?;
        let k3_r = syl(&k3_k2, &k2_cmp)?;

        let k3_val = branch_value(
            env,
            &cx,
            &gs.steps,
            &gs.computes,
            i,
            &k3,
            BranchFacts {
                in_summand: &k3_sig,
                eq_tag: &k3_a,
                f_typed: &k3_f,
                r_typed: &k3_r,
            },
            &ta,
            &tf,
            &cmp,
            &tsig,
        )?;
        let k3_in_e = syl(&k3_k2, &k2_in_e)?;
        let k3_in_g = {
            let tx = tup_x.clone();
            rewrite_under(env, &k3_val, move |v| Formula::mem(tx.clone(), v), &k3_in_e)?
        };

        // Unfold `Gᵢ` and read the base-case equality out.
        let mut ga = ps.clone();
        ga.push(tsig.clone());
        ga.push(cmp.clone());
        ga.push(tup_x.clone());
        let matrix_atoms =
            GoodValues::matrix_atoms(env, mach, ind, spec, i, &ps, &tsig, &cmp, &tup_x)?;
        let matrix = GoodValues::matrix(env, mach, ind, spec, i, &ps, &tsig, &cmp, &tup_x)?;
        let k3_eq = syl(
            &syl(
                &syl(&k3_in_g, &iff_mp(&inst_all(&gv.axioms[i], &ga)?)?)?,
                &and_right(Formula::mem(tup_x.clone(), ix.idx.clone()), matrix),
            )?,
            &crate::conj_proj(&matrix_atoms, 0)?,
        )?;

        // The caller's refutation, at the payload's own components.
        let comps: Vec<Term> = (0..spec.base.ctors[i].args.len())
            .map(|j| Telescope::comp_of(ap, &mach.proj, j, tsig.clone()))
            .collect();
        let refut = inst_all(&refutations[i], &comps)?;
        let k3_false = hyp_mp(&a1i(&refut, k3.clone()), &k3_eq)?;
        branches.push(hyp_ex_branch(sigvs[i], &k3_false, &k2, &fls)?);
    }
    drop(cx);

    let k2_false = hyp_disj_elim(&cases, &k2, &branches)?;
    let k1_false = hyp_mp(&hyp_ex_branch(fv, &k2_false, &k1, &fls)?, &k1_ex)?;
    let m_false = hyp_mp(&hyp_ex_branch(av, &k1_false, &mem, &fls)?, &m_sup)?;
    let out = Thm::gen(zv, &m_false);
    if !out.hyps().is_empty() || *out.concl() != Formula::forall(zv, Formula::not(mem)) {
        return None
    }
    Some(crate::gen_all(&ind.params, &out))
}
