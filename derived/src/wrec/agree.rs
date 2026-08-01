//! **Step 3** — any two attempts agree wherever both are defined.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀z. (z ∈ W → ∀g ∀h. ((g ∈ Att ∧ h ∈ Att) →
//!             ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z)))))          [agreement]
//! ```
//!
//! [`agree_formula`] is the formula the induction runs at, exposed so a caller
//! can rebuild and compare it. Callers need none of the derivation below.
//!
//! # The shape of the argument
//!
//! Structural induction ([`crate::wtype::w_rect`]) at exactly that formula.
//! The induction step needs neither `a ∈ A` nor `f ∈ fs(B(a),W)`: the recursion
//! condition of an attempt already delivers the two facts used, namely that the
//! domain contains every subterm and that the value there is the step applied
//! to the composite. The induction hypothesis then equates the two composites
//! via [`super::compose_ext`], and the two equations close the triangle.
//!
//! This is the one step of the recursor's construction that is a genuine
//! induction, and it is why the phrasing choice recorded in [`super::attempts`]
//! matters: with the `app` phrasing the step is a chain of equations under one
//! ambient hypothesis, which is what the helpers in `hyp` are for.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry};

use super::hyp::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_inst, hyp_split};
use super::composite::agree_on;
use super::attempt::{att_of, indom};

/// The formula structural induction runs at:
///
/// ```text
/// φ(z) := ∀g ∀h. ((g ∈ Att ∧ h ∈ Att)
///                    → ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z)))
/// ```
///
/// `zv` is the variable it speaks about; `att` is the term `Att(A,B,u,T,e)`.
pub fn agree_formula(env: &mut Env, ap: &Apply, att: &Term, zv: kernel::FreeVar) -> Formula {
    let (gv, hv) = (env.fresh_var(), env.fresh_var());
    let (tg, th, tz) = (Term::var(gv), Term::var(hv), Term::var(zv));

    let atts = Formula::and(
        Formula::mem(tg.clone(), att.clone()),
        Formula::mem(th.clone(), att.clone()),
    );
    let indoms = Formula::and(indom(env, ap, &tg, &tz), indom(env, ap, &th, &tz));
    let eq = Formula::eq(
        ap.apply(tg, tz.clone()),
        ap.apply(th, tz),
    );
    Formula::forall(gv, Formula::forall(hv, Formula::imp(atts, Formula::imp(indoms, eq))))
}

/// **Any two attempts agree wherever both are defined.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
///       ∀z. (z ∈ W(A,B,u) →
///           ∀g ∀h. ((g ∈ Att ∧ h ∈ Att)
///                     → ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z)))))
/// ```
///
/// Structural induction ([`crate::wtype::w_rect`]) at exactly that formula.
/// The induction step needs neither `a ∈ A` nor `f ∈ fs(B(a),W)`: the recursion
/// condition of an attempt already delivers the two facts used, namely that the
/// domain contains every subterm and that the value there is the step applied
/// to the composite. The induction hypothesis then equates the two composites
/// via [`super::compose_ext`], and the two equations close the triangle.
#[allow(clippy::too_many_arguments)]
pub fn agreement(
    env: &mut Env,
    wt: &Wtype,
    comp_ext: &Thm,
    att: FnSym,
    att_ax: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (av, bv, uv, tv, ev) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tu, tt, te) = (
        Term::var(av),
        Term::var(bv),
        Term::var(uv),
        Term::var(tv),
        Term::var(ev),
    );
    let att_t = att_of(att, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone());
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());

    let zv = env.fresh_var();
    let phi = agree_formula(env, ap, &att_t, zv);

    // ── The induction step, at `a := pa`, `f := pf` ──────────────────────────
    let (pa, pf, pb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tpb) = (Term::var(pa), Term::var(pf), Term::var(pb));
    let fibre = ap.apply(tb.clone(), tpa.clone());
    let sup = ap.sets.pair(tpa.clone(), tpf.clone());

    let (gv, hv) = (env.fresh_var(), env.fresh_var());
    let (tg, th) = (Term::var(gv), Term::var(hv));

    let ih = Formula::forall(
        pb,
        Formula::imp(
            Formula::mem(tpb.clone(), fibre.clone()),
            phi.subst(zv, &ap.apply(tpf.clone(), tpb.clone())),
        ),
    );
    let atts = Formula::and(
        Formula::mem(tg.clone(), att_t.clone()),
        Formula::mem(th.clone(), att_t.clone()),
    );
    let indoms = Formula::and(
        indom(env, ap, &tg, &sup),
        indom(env, ap, &th, &sup),
    );

    let k1 = Formula::and(ih.clone(), atts.clone());
    let k = Formula::and(k1.clone(), indoms.clone());

    let k_k1 = and_left(k1.clone(), indoms.clone());
    let k_ih = syl(&k_k1, &and_left(ih.clone(), atts.clone()))?;
    let k_atts = syl(&k_k1, &and_right(ih.clone(), atts.clone()))?;
    let k_indoms = and_right(k1.clone(), indoms.clone());
    let (k_indg, k_indh) = hyp_split(&k_indoms)?;
    let (k_gatt, k_hatt) = hyp_split(&k_atts)?;

    // ── Unfold "is an attempt" into its recursion condition ──────────────────
    let rec_of = |env: &mut Env, k_mem: &Thm, t: &Term| -> Option<Thm> {
        let ax = inst_all(
            att_ax,
            &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone(), t.clone()],
        )?;
        let unfold = syl(k_mem, &iff_mp(&ax)?)?; // K → (t ∈ bound ∧ (sv ∧ rec))
        let (_, cond) = hyp_split(&unfold)?; // K → (sv ∧ rec)
        let _ = env;
        Some(hyp_split(&cond)?.1)
    };
    let k_recg = rec_of(env, &k_gatt, &tg)?;
    let k_rech = rec_of(env, &k_hatt, &th)?;

    // ── The two clauses of the recursion condition, at `⟨a,f⟩` ───────────────
    let clauses = |k_rec: &Thm, k_ind: &Thm| -> Option<(Thm, Thm)> {
        let at = hyp_inst(k_rec, &[tpa.clone(), tpf.clone()])?;
        hyp_split(&hyp_mp(&at, k_ind)?)
    };
    let (k_subg, k_eqg) = clauses(&k_recg, &k_indg)?;
    let (k_subh, k_eqh) = clauses(&k_rech, &k_indh)?;

    // ── The induction hypothesis equates the values on the fibre ─────────────
    let mem_b = Formula::mem(tpb.clone(), fibre.clone());
    let l_k = and_left(k.clone(), mem_b.clone());
    let l_b = and_right(k.clone(), mem_b.clone());

    let l_phi = hyp_mp(&hyp_inst(&syl(&l_k, &k_ih)?, std::slice::from_ref(&tpb))?, &l_b)?;
    let l_gh = hyp_inst(&l_phi, &[tg.clone(), th.clone()])?;
    let l_atts = syl(&l_k, &k_atts)?;
    let sub_at = |k_sub: &Thm| -> Option<Thm> {
        hyp_mp(&hyp_inst(&syl(&l_k, k_sub)?, std::slice::from_ref(&tpb))?, &l_b)
    };
    let l_ind = hyp_and(&sub_at(&k_subg)?, &sub_at(&k_subh)?)?;
    let l_val = hyp_mp(&hyp_mp(&l_gh, &l_atts)?, &l_ind)?;

    let per_b = uncurry(&l_val)?; // K → (b ∈ B(a) → app(g,f b) = app(h,f b))
    let (_, body) = per_b.concl().as_imp()?;
    let k_agree = Thm::mp(&Thm::ax_dist(pb, k.clone(), body)?, &Thm::gen(pb, &per_b))?;
    debug_assert_eq!(
        *k_agree.concl(),
        Formula::imp(k.clone(), agree_on(env, ap, &tg, &th, &tpf, &fibre)),
        "agreement: the fibre-wise agreement is not the one compose_ext wants"
    );

    // ── … hence the two composites, hence the two step values ────────────────
    let ext_at = inst_all(comp_ext, &[tg.clone(), th.clone(), tpf.clone(), fibre.clone()])?;
    let k_comp = syl(&k_agree, &ext_at)?;
    let ctx = |t: Term| {
        ap.apply(te.clone(), ap.sets.pair(tpa.clone(), ap.sets.pair(tpf.clone(), t)))
    };
    let k_step = hyp_congr(env, &k_comp, ctx)?;

    // ── app(g,⟨a,f⟩) = step_g = step_h = app(h,⟨a,f⟩) ────────────────────────
    let k_left = hyp_eq_trans(env, &k_eqg, &k_step)?;
    let k_right = hyp_eq_symm(env, &k_eqh)?;
    let k_goal = hyp_eq_trans(env, &k_left, &k_right)?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(
            k.clone(),
            Formula::eq(ap.apply(tg.clone(), sup.clone()), ap.apply(th.clone(), sup.clone()))
        ),
        "agreement: the induction step did not close"
    );

    // ── Reassemble into `φ(⟨a,f⟩)` ───────────────────────────────────────────
    let inner = uncurry(&k_goal)?; // (ih ∧ atts) → (indoms → eq)
    let curried = uncurry(&inner)?; // ih → (atts → (indoms → eq))
    let (_, body_gh) = curried.concl().as_imp()?;
    let all_h = Thm::mp(&Thm::ax_dist(hv, ih.clone(), body_gh)?, &Thm::gen(hv, &curried))?;
    let (_, body_g) = all_h.concl().as_imp()?;
    let all_gh = Thm::mp(&Thm::ax_dist(gv, ih.clone(), body_g)?, &Thm::gen(gv, &all_h))?;
    debug_assert_eq!(
        *all_gh.concl(),
        Formula::imp(ih.clone(), phi.subst(zv, &sup)),
        "agreement: the induction step is not φ(⟨a,f⟩)"
    );

    // ── Wrap in the two typing antecedents `w_rect` states it with ───────────
    let step = Thm::gen(
        pa,
        &a1i(
            &Thm::gen(
                pf,
                &a1i(
                    &all_gh,
                    Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), w_t.clone())),
                ),
            ),
            Formula::mem(tpa.clone(), ta.clone()),
        ),
    );
    debug_assert_eq!(
        *step.concl(),
        crate::wtype::ind_step(env, s, &w_t, &ta, &tb, zv, &phi),
        "agreement: the induction step is not the one w_rect asks for"
    );

    // ── Run the induction ────────────────────────────────────────────────────
    let rect = crate::wtype::w_rect(
        env,
        wt,
        &[av, bv, uv, tv, ev],
        crate::wtype::Params { a: av, b: bv, u: uv },
        zv,
        &phi,
    )?;
    let out = hyp_mp(&rect, &a1i(&step, rect.concl().as_imp()?.0))?;
    Some(gen_all(&[av, bv, uv, tv, ev], &out))
}
