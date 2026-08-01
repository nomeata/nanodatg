//! **Any two attempts agree**, by well-founded induction along `R`.
//!
//! # Interface
//!
//! ```text
//! agree_formula(z) := ∀g ∀h. ((g ∈ Att ∧ h ∈ Att) →
//!                       ((indom(g,z) ∧ indom(h,z)) → app(g,z) = app(h,z)))
//!
//! ⊢ ∀A ∀R ∀T ∀e ∀z. (z ∈ acc(A,R) → agree_formula(z))          [agreement]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # The argument
//!
//! [`crate::acc::acc_rect`] at `φ := agree_formula`, and nothing else. Its minor
//! premise gives, at a point `x ∈ A`, the hypothesis that **every** `R`-
//! predecessor of `x` inside `A` is accessible *and* satisfies `φ`; the
//! conclusion is `φ(x)`. So:
//!
//! 1. both attempts are defined at `x`, so both satisfy the recursion equation
//!    there — `app(g,x) = e(x)(•)(ih(g,A,R,x))` and likewise for `h`;
//! 2. `rec_cond`'s first clause says both are defined at every predecessor `y`
//!    of `x`, and the induction hypothesis at `y` then equates `app(g,y)` with
//!    `app(h,y)` — that is exactly [`super::ih::preds_agree`];
//! 3. [`super::ih::ih_ext`] turns that into `ih(g,A,R,x) = ih(h,A,R,x)`, one
//!    congruence carries it through the step, and transitivity closes the chain.
//!
//! **`y ∈ acc(A,R)` is not used.** [`crate::acc::acc_rect`]'s induction
//! hypothesis offers the conjunction `y ∈ acc(A,R) ∧ φ(y)` because Lean's
//! `Acc.rec` gives its minor premise both; this argument spends only the second
//! conjunct. The first is what the *totality* argument needs.
//!
//! # Why this is unconditional
//!
//! [`crate::wrec::agreement`] carries `closed(A,B,u)` — the W-type's bound
//! condition, without which `w_rect` does not apply. `acc_rect` has no such
//! antecedent ([`crate::acc`]), so neither does this. Nothing here assumes
//! `R ⊆ A × A` either: [`super::ih::preds_agree`] and
//! [`super::attempt::preds_indom`] both carry their own `y ∈ A` guard, so edges
//! leaving `A` are simply never looked at.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::acc::{acc_rect, ind_step, Params};
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::{
    and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};

use super::attempt::{att_of, attempt_bound, preds_indom, rec_cond};
use super::base::Base;
use super::ih::preds_agree;

/// `∀g ∀h. ((g ∈ Att ∧ h ∈ Att) → ((indom(g,z) ∧ indom(h,z)) →
/// app(g,z) = app(h,z)))` — "every two attempts defined at `z` agree there", as
/// a formula.
#[allow(clippy::too_many_arguments)]
pub fn agree_formula(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    a: &Term,
    r: &Term,
    t: &Term,
    e: &Term,
    z: &Term,
) -> Formula {
    let (gv, hv) = (env.fresh_var(), env.fresh_var());
    let (tg, th) = (Term::var(gv), Term::var(hv));
    let att_t = att_of(att, a.clone(), r.clone(), t.clone(), e.clone());
    let mem_both = Formula::and(
        Formula::mem(tg.clone(), att_t.clone()),
        Formula::mem(th.clone(), att_t),
    );
    let ind_g = b.indom(env, &tg, z);
    let ind_h = b.indom(env, &th, z);
    let eq = Formula::eq(b.app(&tg, z), b.app(&th, z));
    Formula::forall(
        gv,
        Formula::forall(
            hv,
            Formula::imp(mem_both, Formula::imp(Formula::and(ind_g, ind_h), eq)),
        ),
    )
}

/// The set of attempts at one fixed choice of `A, R, T, e`.
///
/// A view rather than eight loose arguments: the symbol, its characteristic
/// theorem and the four parameters are meaningless apart, and passing them
/// separately is how a derivation ends up unfolding one `Att` against another's
/// axiom. `ps` is `[A, R, T, e]`, in that order.
struct AttAt<'a> {
    /// The symbol `Att`.
    att: FnSym,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att ↔ …)`.
    att_ax: &'a Thm,
    /// The four parameters `A, R, T, e`.
    ps: &'a [Term],
}

impl AttAt<'_> {
    /// The term `Att(A,R,T,e)`.
    fn term(&self) -> Term {
        att_of(
            self.att,
            self.ps[0].clone(),
            self.ps[1].clone(),
            self.ps[2].clone(),
            self.ps[3].clone(),
        )
    }
}

/// From `⊢ K → g ∈ Att(A,R,T,e)` extract `⊢ K → rec_cond(A,R,e,g)`.
fn rec_cond_of(env: &mut Env, b: &Base, at: &AttAt, g: &Term, k_mem: &Thm) -> Option<Thm> {
    let (a, r, t, e) = (&at.ps[0], &at.ps[1], &at.ps[2], &at.ps[3]);
    let mut args = at.ps.to_vec();
    args.push(g.clone());
    let ax = inst_all(at.att_ax, &args)?;
    let sv = crate::funspace::is_single_valued(env, &b.s.ap.sets, g);
    let rc = rec_cond(env, b, a, r, e, g);
    let pow = Formula::mem(g.clone(), attempt_bound(b, a, r, t));
    let inner = Formula::and(sv.clone(), rc.clone());
    if *ax.concl()
        != Formula::iff(
            Formula::mem(g.clone(), at.term()),
            Formula::and(pow.clone(), inner.clone()),
        )
    {
        return None
    }
    let unfold = syl(k_mem, &iff_mp(&ax)?)?;
    let both = syl(&unfold, &and_right(pow, inner))?;
    syl(&both, &and_right(sv, rc))
}

/// `⊢ ∀A ∀R ∀T ∀e ∀z. (z ∈ acc(A,R) → agree_formula(z))` — **any two attempts
/// agree wherever both are defined**.
///
/// See the module header for the argument. Unconditional.
pub fn agreement(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    att_ax: &Thm,
) -> Option<Thm> {
    let (av, rv, tv, ev, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tt, te, tz) = (
        Term::var(av),
        Term::var(rv),
        Term::var(tv),
        Term::var(ev),
        Term::var(zv),
    );
    let phi = agree_formula(env, b, att, &ta, &tr, &tt, &te, &tz);
    let acc_t = b.acc_of(&ta, &tr);

    // ── The minor premise, proved at a fresh point `x` ──────────────────────
    let (xv, yv, gv, hv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tx, ty, tg, th) = (
        Term::var(xv),
        Term::var(yv),
        Term::var(gv),
        Term::var(hv),
    );

    let ih_f = {
        // `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ φ(y))))`, exactly as
        // `acc::ind_step` builds it.
        Formula::forall(
            yv,
            Formula::imp(
                Formula::mem(ty.clone(), ta.clone()),
                Formula::imp(
                    Formula::mem(b.edge(&ty, &tx), tr.clone()),
                    Formula::and(
                        Formula::mem(ty.clone(), acc_t.clone()),
                        phi.subst(zv, &ty),
                    ),
                ),
            ),
        )
    };
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let front = Formula::and(mem_xa.clone(), ih_f.clone());

    let att_t = att_of(att, ta.clone(), tr.clone(), tt.clone(), te.clone());
    let mem_g = Formula::mem(tg.clone(), att_t.clone());
    let mem_h = Formula::mem(th.clone(), att_t);
    let mem_both = Formula::and(mem_g.clone(), mem_h.clone());
    let ind_gx = b.indom(env, &tg, &tx);
    let ind_hx = b.indom(env, &th, &tx);
    let ind_both = Formula::and(ind_gx.clone(), ind_hx.clone());

    let mid = Formula::and(front.clone(), mem_both.clone());
    let k = Formula::and(mid.clone(), ind_both.clone());
    let k_mid = and_left(mid.clone(), ind_both.clone());
    let k_front = syl(&k_mid, &and_left(front.clone(), mem_both.clone()))?;
    let k_memboth = syl(&k_mid, &and_right(front.clone(), mem_both.clone()))?;
    let k_ih = syl(&k_front, &and_right(mem_xa.clone(), ih_f.clone()))?;
    let k_g = syl(&k_memboth, &and_left(mem_g.clone(), mem_h.clone()))?;
    let k_h = syl(&k_memboth, &and_right(mem_g, mem_h))?;
    let k_inds = and_right(mid, ind_both.clone());
    let k_ind_gx = syl(&k_inds, &and_left(ind_gx.clone(), ind_hx.clone()))?;
    let k_ind_hx = syl(&k_inds, &and_right(ind_gx, ind_hx))?;

    // ── Both attempts satisfy the recursion equation at `x` ─────────────────
    let ps = [ta.clone(), tr.clone(), tt.clone(), te.clone()];
    let att_at = AttAt { att, att_ax, ps: &ps };
    let each = |env: &mut Env, f: &Term, k_mem: &Thm, k_ind: &Thm| -> Option<(Thm, Thm)> {
        let rc = rec_cond_of(env, b, &att_at, f, k_mem)?;
        let at_x = syl(&rc, &Thm::ax_inst(rec_cond(env, b, &ta, &tr, &te, f), tx.clone())?)?;
        let fired = hyp_mp(&at_x, k_ind)?;
        let preds = preds_indom(env, b, &ta, &tr, f, &tx);
        let eqn = Formula::eq(
            b.app(f, &tx),
            b.step_at(&te, &tx, &b.ih_at(f, &ta, &tr, &tx)),
        );
        Some((
            syl(&fired, &and_left(preds.clone(), eqn.clone()))?,
            syl(&fired, &and_right(preds, eqn))?,
        ))
    };
    let (k_preds_g, k_eq_g) = each(env, &tg, &k_g, &k_ind_gx)?;
    let (k_preds_h, k_eq_h) = each(env, &th, &k_h, &k_ind_hx)?;

    // ── The two attempts agree on the predecessors of `x` ───────────────────
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, &tx), tr.clone());
    let l1 = Formula::and(k.clone(), mem_ya.clone());
    let l = Formula::and(l1.clone(), edge.clone());
    let l_l1 = and_left(l1.clone(), edge.clone());
    let l_k = syl(&l_l1, &and_left(k.clone(), mem_ya.clone()))?;
    let l_ya = syl(&l_l1, &and_right(k.clone(), mem_ya.clone()))?;
    let l_edge = and_right(l1, edge.clone());

    let at_pred = |env: &mut Env, k_preds: &Thm, f: &Term| -> Option<Thm> {
        let preds = preds_indom(env, b, &ta, &tr, f, &tx);
        let inst = Thm::ax_inst(preds, ty.clone())?;
        let step = syl(&syl(&l_k, k_preds)?, &inst)?;
        hyp_mp(&hyp_mp(&step, &l_ya)?, &l_edge)
    };
    let l_ind_gy = at_pred(env, &k_preds_g, &tg)?;
    let l_ind_hy = at_pred(env, &k_preds_h, &th)?;

    // The induction hypothesis at `y`, applied to `g` and `h`.
    let l_ihy = {
        let inst = Thm::ax_inst(ih_f.clone(), ty.clone())?;
        let step = syl(&syl(&l_k, &k_ih)?, &inst)?;
        hyp_mp(&hyp_mp(&step, &l_ya)?, &l_edge)?
    };
    let phi_y = phi.subst(zv, &ty);
    let l_phiy = syl(
        &l_ihy,
        &and_right(Formula::mem(ty.clone(), acc_t.clone()), phi_y.clone()),
    )?;
    let l_phiy_gh = {
        let a1 = Thm::ax_inst(phi_y.clone(), tg.clone())?;
        let (_, rest) = a1.concl().as_imp()?;
        let a2 = Thm::ax_inst(rest, th.clone())?;
        syl(&l_phiy, &syl(&a1, &a2)?)?
    };
    let l_memboth = syl(&l_k, &k_memboth)?;
    let l_agree_y = hyp_mp(
        &hyp_mp(&l_phiy_gh, &l_memboth)?,
        &hyp_and(&l_ind_gy, &l_ind_hy)?,
    )?;
    if *l_agree_y.concl()
        != Formula::imp(
            l,
            Formula::eq(b.app(&tg, &ty), b.app(&th, &ty)),
        )
    {
        return None
    }

    let k_pa_body = uncurry(&uncurry(&l_agree_y)?)?;
    let k_preds_agree = Thm::mp(
        &Thm::ax_dist(
            yv,
            k.clone(),
            Formula::imp(
                mem_ya,
                Formula::imp(edge, Formula::eq(b.app(&tg, &ty), b.app(&th, &ty))),
            ),
        )?,
        &Thm::gen(yv, &k_pa_body),
    )?;
    let want = preds_agree(env, &b.s, &tg, &th, &ta, &tr, &tx);
    if *k_preds_agree.concl() != Formula::imp(k.clone(), want) {
        return None
    }

    // ── Hence the two induction hypotheses are equal, and the values are ────
    let ie = inst_all(
        &b.ih_ext,
        &[tg.clone(), th.clone(), ta.clone(), tr.clone(), tx.clone()],
    )?;
    let k_ih_eq = syl(&k_preds_agree, &ie)?;
    let (te2, tx2) = (te.clone(), tx.clone());
    let bb = b;
    let k_step_eq = hyp_congr(env, &k_ih_eq, move |t| bb.step_at(&te2, &tx2, &t))?;
    let k_eq_h_rev = hyp_eq_symm(env, &k_eq_h)?;
    let chain = hyp_eq_trans(env, &k_eq_g, &k_step_eq)?;
    let out_body = hyp_eq_trans(env, &chain, &k_eq_h_rev)?;
    if *out_body.concl()
        != Formula::imp(k, Formula::eq(b.app(&tg, &tx), b.app(&th, &tx)))
    {
        return None
    }

    // ── Reassemble the minor premise ────────────────────────────────────────
    let curried = uncurry(&uncurry(&out_body)?)?; // front → (mem_both → (ind_both → eq))
    let inner = Formula::imp(
        mem_both,
        Formula::imp(
            ind_both,
            Formula::eq(b.app(&tg, &tx), b.app(&th, &tx)),
        ),
    );
    let over_h = Thm::mp(
        &Thm::ax_dist(hv, front.clone(), inner.clone())?,
        &Thm::gen(hv, &curried),
    )?;
    let over_g = Thm::mp(
        &Thm::ax_dist(gv, front.clone(), Formula::forall(hv, inner))?,
        &Thm::gen(gv, &over_h),
    )?;
    if *over_g.concl() != Formula::imp(front, phi.subst(zv, &tx)) {
        return None
    }
    let minor = Thm::gen(xv, &uncurry(&over_g)?);
    let want_minor = ind_step(env, &b.ac, &acc_t, &ta, &tr, zv, &phi);
    if *minor.concl() != want_minor {
        return None
    }

    // ── Fire `acc_rect` ─────────────────────────────────────────────────────
    let params: Vec<FreeVar> = vec![av, rv, tv, ev];
    let rect = acc_rect(env, &b.ac, &params, Params { a: av, r: rv }, zv, &phi)?;
    let out = Thm::mp(&rect, &minor)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(zv, Formula::imp(Formula::mem(tz, acc_t), phi)),
        "agreement: unexpected shape"
    );
    Some(gen_all(&params, &out))
}
