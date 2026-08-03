//! The general step is typed — (S3), `HYP → step_typed`, the first real
//! consumer of [`crate::isum::ISumSyms::no_junk`].
//!
//! # The argument
//!
//! `step_typed` hands us an arbitrary `a ∈ A` with `f ∈ fs(B(a), W)` and
//! `r ∈ fs(B(a), T)` and wants `app(e, ⟨a, ⟨f, r⟩⟩) ∈ T`. Nothing says `a` is
//! a constructor tag — **no_junk does**: it splits `a ∈ Sum_n(A⃗)` into `n`
//! cases `a = Injᵢ(σ)`, `σ ∈ Aᵢ`. In case `i` the fibre computes to
//! `Sum_{mᵢ}(A⃗)`, the two function-space memberships move to that domain and
//! (by `fs ⊆ 𝒫(prod)`) into the sets the `i`-th Replacement ranges over, the
//! step computes to `valᵢ(σ, f, r)` by (S1), each of that value's components
//! is typed — `compⱼ(σ)` by the telescope projection, which lands on
//! *exactly* `minor_typedᵢ`'s hypothesis instantiated at `yⱼ := compⱼ(σ)`,
//! and each recursive slot by whichever rule its spelling asks for — and
//! `minor_typedᵢ` closes the case.
//!
//! **The recursive slots are two shapes, one inference each.** A plain slot is
//! `app(f, Injⱼ(•)) ∈ W`, by the function-space application rule at a point of
//! the fibre; a function-typed one is `f|ⱼ ∈ fs(Aⱼ, W)`, by
//! [`crate::isum::ISumSyms::branch_in_funspace`]. That rule is stated at the
//! function-space membership this proof already holds rather than at the
//! pointwise condition [`crate::ext::lam_in_funspace_n`] asks for, which is why
//! the second shape costs one `syl` and not three lines — see
//! [`crate::isum::restrict`]'s header, where the choice is argued from all four
//! of its consumers at once.
//!
//! Note what makes the instantiation legitimate: `HYP`'s recursive-argument
//! slots quantify over the whole carrier `W` (see [`super::premise`]), so
//! they cover exactly the junk instantiations `∀f ∈ fs(B(a), W)` ranges
//! over. A `HYP` quantified over constructor images instead would leave this
//! proof stuck — that the derivation goes through *is* the match.
//!
//! This is the generalisation of `NatRec::step_typed`/`ListRec::step_typed`
//! with `no_junk` replacing the binary `sum_cases`; it is the one proof in
//! the skeleton with no hand-written ancestor at its actual shape, which is
//! why every intermediate is shape-checked.

use kernel::{Env, Formula, Term, Thm};

use crate::wrec::{hyp_congr, hyp_eq_trans};
use crate::{a1i, and_left, and_right, conj_proj, disj_of, hyp_and, hyp_mp, inst_all, syl, uncurry};

use super::rec_shared::{carry_back, gen_under, hyp_conj, hyp_disj_elim, hyp_ex_branch, hyp_inst, under};
use super::step::{Rx, StepSym};

/// `⊢ HYP → step_typed(A, B, U({A,T}), T, e)` at the working variables.
///
/// `computes` are the (S1) rules, each generalised over its `(σ, f, r)`;
/// `hyp_parts` the `minor_typedᵢ` conjuncts and `hyp` their conjunction,
/// built by [`super::premise`].
pub(super) fn step_typed_at(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    computes: &[Thm],
    hyp_parts: &[Formula],
    hyp: &Formula,
) -> Option<Thm> {
    let s = cx.s();
    let ap = cx.ap();
    let wt = &cx.mach.wt;
    let n = cx.n();
    let tags = cx.ind.tags.clone();
    let fam = cx.ind.fibre.fam.clone();
    let u = cx.ind.bound.clone();
    let w = cx.w();
    let t = cx.t.clone();
    let step = cx.step(syms);

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre_t = ap.apply(fam.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre_t.clone(), w.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre_t.clone(), t.clone()));
    let hm = Formula::and(hyp.clone(), ma.clone());
    let front = Formula::and(hm.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());

    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr.clone());
    let p_hm = syl(&p_front, &and_left(hm.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(hm.clone(), mf.clone()))?;
    let p_hyp = syl(&p_hm, &and_left(hyp.clone(), ma.clone()))?;
    let p_ma = syl(&p_hm, &and_right(hyp.clone(), ma.clone()))?;

    let triple = |x: &Term, y: &Term, z: &Term| {
        ap.apply(
            step.clone(),
            ap.sets.pair(x.clone(), ap.sets.pair(y.clone(), z.clone())),
        )
    };
    let goal = Formula::mem(triple(&ta, &tf, &tr), t.clone());

    // ── no_junk splits the tag ──────────────────────────────────────────────
    let nj = cx.mach.syms.no_junk(env, s, n)?;
    let mut nj_args: Vec<Term> = cx.ind.summands.clone();
    nj_args.push(ta.clone());
    let nj_at = inst_all(&nj, &nj_args)?;
    let sigvs: Vec<kernel::FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let bodies: Vec<Formula> = (0..n)
        .map(|i| {
            let tsig = Term::var(sigvs[i]);
            Some(Formula::and(
                Formula::mem(tsig.clone(), cx.summand(i)),
                Formula::eq(ta.clone(), cx.mach.syms.inj(i, tsig)?),
            ))
        })
        .collect::<Option<_>>()?;
    let disjuncts: Vec<Formula> =
        (0..n).map(|i| Formula::exists(sigvs[i], bodies[i].clone())).collect();
    let d = disj_of(&disjuncts)?;
    if *nj_at.concl() != Formula::imp(Formula::mem(ta.clone(), tags.clone()), d) {
        return None
    }
    let cases = syl(&p_ma, &nj_at)?;

    // `K → g ∈ fs(finord(mᵢ), cod)`, the fibre having been computed.
    let retype = |env: &mut Env,
                  k: &Formula,
                  k_fib: &Thm,
                  prem: &Thm,
                  dom: &Term,
                  cod: &Term,
                  g: &Term|
     -> Option<Thm> {
        let cod_c = cod.clone();
        let cong = hyp_congr(env, k_fib, move |q| s.fs.of(q, cod_c.clone()))?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            s.fs.of(fibre_t.clone(), cod.clone()),
            s.fs.of(dom.clone(), cod.clone()),
            hole,
            Formula::mem(g.clone(), Term::var(hole)),
        );
        hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &cong)?, prem)
    };
    // `K → g ∈ 𝒫(prod(dom, cod))`, from `K → g ∈ fs(dom, cod)`.
    let sub = |prem: &Thm, dom: &Term, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[dom.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };

    // ── the `n` branches ────────────────────────────────────────────────────
    let mut branches = Vec::with_capacity(n);
    for i in 0..n {
        let tsig = Term::var(sigvs[i]);
        let fibre = cx.fibre(i)?;
        // Which of this constructor's recursive slots are function-typed — the
        // same funnel `Rx::fibre_apps` and `minor_typed_at` read.
        let doms = cx.ind.rec_slot_domains(i);
        let k = Formula::and(p.clone(), bodies[i].clone());
        let k_p = and_left(p.clone(), bodies[i].clone());
        let k_body = and_right(p.clone(), bodies[i].clone());
        let mem_sig = Formula::mem(tsig.clone(), cx.summand(i));
        let eq_a = Formula::eq(ta.clone(), cx.mach.syms.inj(i, tsig.clone())?);
        let k_sig = syl(&k_body, &and_left(mem_sig.clone(), eq_a.clone()))?;
        let k_a = syl(&k_body, &and_right(mem_sig, eq_a))?;

        // The fibre at this tag is `finord(mᵢ)`.
        let k_acong = hyp_congr(env, &k_a, |q| ap.apply(fam.clone(), q))?;
        let fib_at = inst_all(&cx.ind.fibre.fibre[i], std::slice::from_ref(&tsig))?;
        let k_fib = hyp_eq_trans(env, &k_acong, &syl(&k_sig, &fib_at)?)?;

        // `f` and `r`, retyped to that fibre and widened to the Replacement's
        // ranges.
        let k_mf = syl(&k_p, &p_mf)?;
        let k_mr = syl(&k_p, &p_mr)?;
        let k_f = retype(env, &k, &k_fib, &k_mf, &fibre, &w, &tf)?;
        let k_r = retype(env, &k, &k_fib, &k_mr, &fibre, &t, &tr)?;
        let k_fw = sub(&k_f, &fibre, &w, &tf)?;
        let k_ft = sub(&k_r, &fibre, &t, &tr)?;

        // The step computes: rewrite the key's tag, then (S1).
        let k_tag = hyp_congr(env, &k_a, |q| triple(&q, &tf, &tr))?;
        let k_app = hyp_mp(
            &a1i(
                &inst_all(&computes[i], &[tsig.clone(), tf.clone(), tr.clone()])?,
                k.clone(),
            ),
            &hyp_and(&k_sig, &hyp_and(&k_fw, &k_ft)?)?,
        )?;
        let k_val = hyp_eq_trans(env, &k_tag, &k_app)?;

        // The value is in `T`, by `minor_typedᵢ` at the components.
        let k_mt = syl(&syl(&k_p, &p_hyp)?, &conj_proj(hyp_parts, i)?)?;
        let comps = cx.comps(i, &tsig);
        let f_apps = cx.fibre_apps(i, &tf)?;
        let r_apps = cx.fibre_apps(i, &tr)?;
        let mut insts = comps.clone();
        insts.extend(f_apps.iter().cloned());
        insts.extend(r_apps.iter().cloned());
        let k_mt_at = hyp_inst(&k_mt, &insts)?;

        let k_in_t = if insts.is_empty() {
            // A fully nullary constructor: `minor_typedᵢ` is the bare `sᵢ ∈ T`.
            k_mt_at
        } else {
            let mut atom_thms: Vec<Thm> = Vec::with_capacity(insts.len());
            for j in 0..cx.k(i) {
                let mut a = cx.ps.clone();
                a.push(tsig.clone());
                let pm = inst_all(&cx.tel(i).proj_mem[j], &a)?;
                atom_thms.push(syl(&k_sig, &pm)?);
            }
            // The `j`-th recursive slot's typing, at whichever of the two
            // shapes `minor_typedᵢ` states it: `app(g, Injⱼ(•)) ∈ cod` at a
            // plain slot, by the function-space application rule at a point of
            // the fibre; `g|ⱼ ∈ fs(Aⱼ, cod)` at a function-typed one, by
            // `branch_in_funspace` — **one inference either way**, because that
            // rule is stated at the function-space membership `step_typed`
            // already hands us and not at the pointwise condition the lambda's
            // own typing rule asks for.
            let fibre_atom = |env: &mut Env,
                              cod: &Term,
                              fun: &Term,
                              prem: &Thm,
                              j: usize|
             -> Option<Thm> {
                match doms.get(j).and_then(|d| d.as_ref()) {
                    None => {
                        let rule = inst_all(
                            &wt.app_mem,
                            &[fibre.clone(), cod.clone(), fun.clone(), cx.inj_pt(j)?],
                        )?;
                        let pt_mem = under(&cx.inj_pt_mem(i, j)?, &k);
                        hyp_mp(&a1i(&rule, k.clone()), &hyp_and(prem, &pt_mem)?)
                    }
                    Some(_) => {
                        let summands = &cx.ind.recargs.get(i)?.summands;
                        let rule = cx.mach.syms.branch_in_funspace(
                            env,
                            s,
                            &wt.app_mem,
                            summands.len(),
                            j,
                        )?;
                        let mut args = summands.clone();
                        args.push(cod.clone());
                        args.push(fun.clone());
                        syl(prem, &inst_all(&rule, &args)?)
                    }
                }
            };
            for j in 0..cx.m(i) {
                let th = fibre_atom(env, &w, &tf, &k_f, j)?;
                atom_thms.push(th);
            }
            for j in 0..cx.m(i) {
                let th = fibre_atom(env, &t, &tr, &k_r, j)?;
                atom_thms.push(th);
            }
            hyp_mp(&k_mt_at, &hyp_conj(&atom_thms)?)?
        };

        // Carry the membership back along the computation.
        let k_goal = carry_back(env, &k_val, &k_in_t, &t)?;
        branches.push(hyp_ex_branch(sigvs[i], &k_goal, &p, &goal)?);
    }

    let body = hyp_disj_elim(&cases, &p, &branches)?;

    // ── regeneralise into `step_typed`'s own shape ──────────────────────────
    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let over_f = gen_under(fv, &hm, &uncurry(&over_r)?)?;
    let out = gen_under(av, hyp, &uncurry(&over_f)?)?;
    if *out.concl()
        != Formula::imp(
            hyp.clone(),
            crate::wrec_total::step_typed(env, s, wt, &tags, &fam, &u, &t, &step),
        )
    {
        return None
    }
    Some(out)
}
