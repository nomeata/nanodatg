//! The **sandwich**: `a ⊆ b ⊆ c` and `a ≈ c` give `a ≈ b`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀b ∀c. (((a ⊆ b ∧ b ⊆ c) ∧ a ≈ c) → a ≈ b)      [equinumerous_sandwich]
//! ```
//!
//! with `⊆` `kernel::thm::subset` and `≈` `kernel::thm::equinumerous`. Nothing
//! is assumed and callers need no derivation.
//!
//! # Why this and not [`super::graph::schroeder_bernstein`]
//!
//! This is the form `crate::universe::inaccessibility` needs, and it is a
//! **cheaper** instance of [`super::csb_scheme`] than the set-graph one — not a
//! corollary of it.
//!
//! The consumer holds `y ⊆ U(x) ⊆ u` and a bijection `y ≈ u`, and wants
//! `y ≈ U(x)`. Read as Cantor–Schröder–Bernstein that is the injections
//! `y ↪ U(x)` (the inclusion) and `U(x) ↪ y` (the converse of the bijection,
//! restricted to `U(x)`). **Neither exists as a set in the consumer's hands.**
//! Getting them would be a Replacement each and eight clauses to prove about the
//! results. As *formulas* they are
//!
//! ```text
//! F(x,y)  :=  x ∈ a ∧ x = y
//! G(y,x)  :=  y ∈ b ∧ ⟨x,y⟩ ∈ e
//! ```
//!
//! — the inclusion and the converse-restriction, written down rather than built
//! — and the scheme takes formulas. So the whole cost here is the eight clauses,
//! and each is either a projection off the bijection `e` or two lines of
//! equality reasoning.
//!
//! # Where each hypothesis goes
//!
//! `a ⊆ b` is spent exactly once, in `DOM(F)`: the inclusion is only an
//! injection *into `b`* because `a` is inside `b`. `b ⊆ c` is spent exactly once,
//! in `TOT(G)`: the converse of `e` is only defined *on `b`* because `b` is
//! inside `e`'s range `c`. The bijection `e` supplies the other three `G`
//! clauses, and — note the crossing — `G`'s single-valuedness is `e`'s
//! *injectivity* and `G`'s injectivity is `e`'s *single-valuedness*, because `G`
//! is `e` read backwards. `F`'s totality, single-valuedness and injectivity are
//! properties of equality and need nothing at all.
//!
//! `e`'s totality is the one clause of the bijection that is **not** used: the
//! argument only ever runs `e` backwards.

use kernel::{Env, Formula, Term, Thm};

use crate::{
    a1i, and_intro_imp, and_left, and_right, conj_of, conj_proj, eq_symm_imp, exists_intro_imp,
    gen_all, hyp_and, hyp_mp, syl,
};

use super::bijection::{bijection_body, csb_clauses, csb_scheme};
use super::prereq::Csb;
use super::shared::{discharge, hyp_exists_mono, hyp_gen, inst_all_imp};

/// `⊢ ∀a ∀b ∀c. (((a ⊆ b ∧ b ⊆ c) ∧ a ≈ c) → a ≈ b)`.
///
/// The instance of [`csb_scheme`] at the inclusion `a ↪ b` and the converse of
/// the bijection `a ≈ c` restricted to `b`, both as formulas. See the module
/// header for why that is the cheap route and for where each hypothesis is
/// spent.
pub fn equinumerous_sandwich(env: &mut Env, s: &Csb) -> Option<Thm> {
    let (av, bvar, cvar, ev) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, te) =
        (Term::var(av), Term::var(bvar), Term::var(cvar), Term::var(ev));
    let (xv, bv, x2, y2, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tx, ty, tx2, ty2) = (Term::var(xv), Term::var(bv), Term::var(x2), Term::var(y2));

    // ── The two relations, and the hypothesis ───────────────────────────────
    let mem_x_a = Formula::mem(tx.clone(), ta.clone());
    let mem_y_b = Formula::mem(ty.clone(), tb.clone());
    let eq_xy = Formula::eq(tx.clone(), ty.clone());
    let pair_e = kernel::thm::pair_in(env, te.clone(), tx.clone(), ty.clone());
    let f_rel = Formula::and(mem_x_a.clone(), eq_xy.clone());
    let g_rel = Formula::and(mem_y_b.clone(), pair_e.clone());

    let sub_ab = kernel::thm::subset(env, ta.clone(), tb.clone());
    let sub_bc = kernel::thm::subset(env, tb.clone(), tc.clone());
    let equi_ac = kernel::thm::equinumerous(env, ta.clone(), tc.clone());
    let body = bijection_body(env, &te, &ta, &tc);
    let body_conj = conj_of(&body)?;
    debug_assert_eq!(
        Formula::exists(ev, body_conj.clone()),
        equi_ac,
        "equinumerous_sandwich: the bijection body is not the one `≈` is written with"
    );

    let hp = Formula::and(sub_ab.clone(), sub_bc.clone());
    let h = Formula::and(hp.clone(), equi_ac.clone());
    let w = Formula::and(h.clone(), body_conj.clone());
    let w_h = and_left(h.clone(), body_conj.clone());
    let w_body = and_right(h.clone(), body_conj.clone());
    let w_hp = syl(&w_h, &and_left(hp.clone(), equi_ac.clone()))?;
    let w_ab = syl(&w_hp, &and_left(sub_ab.clone(), sub_bc.clone()))?;
    let w_bc = syl(&w_hp, &and_right(sub_ab.clone(), sub_bc.clone()))?;
    let bij: Vec<Thm> =
        (0..5).map(|i| syl(&w_body, &conj_proj(&body, i)?)).collect::<Option<_>>()?;

    // ── `DOM(F)`: the inclusion lands in `b` — the only use of `a ⊆ b` ──────
    let fdom = {
        let p = Formula::and(w.clone(), f_rel.clone());
        let p_w = and_left(w.clone(), f_rel.clone());
        let p_f = and_right(w.clone(), f_rel.clone());
        let p_xa = syl(&p_f, &and_left(mem_x_a.clone(), eq_xy.clone()))?;
        let p_eq = syl(&p_f, &and_right(mem_x_a.clone(), eq_xy.clone()))?;
        let p_xb = hyp_mp(
            &hyp_mp(&a1i(&Thm::ax_inst(sub_ab.clone(), tx.clone())?, p.clone()), &syl(&p_w, &w_ab)?)?,
            &p_xa,
        )?;
        let carry =
            Thm::eq_leibniz(tx.clone(), ty.clone(), zv, Formula::mem(Term::var(zv), tb.clone()));
        let p_yb = hyp_mp(&hyp_mp(&a1i(&carry, p.clone()), &p_eq)?, &p_xb)?;
        hyp_gen(xv, &hyp_gen(bv, &crate::uncurry(&hyp_and(&p_xa, &p_yb)?)?)?)?
    };

    // ── `TOT(F)`, `SV(F)`, `INJ(F)`: properties of equality ─────────────────
    let ftot = {
        let p = Formula::and(w.clone(), mem_x_a.clone());
        let p_xa = and_right(w.clone(), mem_x_a.clone());
        let refl = and_intro_imp(mem_x_a.clone(), Formula::eq(tx.clone(), tx.clone()));
        let p_pair = hyp_mp(
            &hyp_mp(&a1i(&refl, p.clone()), &p_xa)?,
            &a1i(&Thm::eq_refl(tx.clone()), p.clone()),
        )?;
        let intro = exists_intro_imp(bv, f_rel.clone(), tx.clone())?;
        hyp_gen(xv, &crate::uncurry(&syl(&p_pair, &intro)?)?)?
    };

    let f2 = f_rel.subst(bv, &ty2);
    let fsv = {
        let both = Formula::and(f_rel.clone(), f2.clone());
        let p = Formula::and(w.clone(), both.clone());
        let p_1 = syl(&and_right(w.clone(), both.clone()), &and_left(f_rel.clone(), f2.clone()))?;
        let p_2 = syl(&and_right(w.clone(), both.clone()), &and_right(f_rel.clone(), f2.clone()))?;
        let p_eq1 = syl(&p_1, &and_right(mem_x_a.clone(), eq_xy.clone()))?;
        let p_eq2 =
            syl(&p_2, &and_right(mem_x_a.clone(), Formula::eq(tx.clone(), ty2.clone())))?;
        let p_yx = syl(&p_eq1, &eq_symm_imp(env, tx.clone(), ty.clone()))?;
        let carry = Thm::eq_leibniz(
            tx.clone(),
            ty2.clone(),
            zv,
            Formula::eq(ty.clone(), Term::var(zv)),
        );
        let out = hyp_mp(&hyp_mp(&a1i(&carry, p.clone()), &p_eq2)?, &p_yx)?;
        hyp_gen(xv, &hyp_gen(bv, &hyp_gen(y2, &crate::uncurry(&out)?)?)?)?
    };

    let f3 = f_rel.subst(xv, &tx2);
    let finj = {
        let both = Formula::and(f_rel.clone(), f3.clone());
        let p = Formula::and(w.clone(), both.clone());
        let p_1 = syl(&and_right(w.clone(), both.clone()), &and_left(f_rel.clone(), f3.clone()))?;
        let p_2 = syl(&and_right(w.clone(), both.clone()), &and_right(f_rel.clone(), f3.clone()))?;
        let eq_x2y = Formula::eq(tx2.clone(), ty.clone());
        let p_eq1 = syl(&p_1, &and_right(mem_x_a.clone(), eq_xy.clone()))?;
        let p_eq2 = syl(
            &p_2,
            &and_right(Formula::mem(tx2.clone(), ta.clone()), eq_x2y.clone()),
        )?;
        let p_yx2 = syl(&p_eq2, &eq_symm_imp(env, tx2.clone(), ty.clone()))?;
        let carry = Thm::eq_leibniz(
            ty.clone(),
            tx2.clone(),
            zv,
            Formula::eq(tx.clone(), Term::var(zv)),
        );
        let out = hyp_mp(&hyp_mp(&a1i(&carry, p.clone()), &p_yx2)?, &p_eq1)?;
        hyp_gen(xv, &hyp_gen(x2, &hyp_gen(bv, &crate::uncurry(&out)?)?)?)?
    };

    // ── `G`'s four clauses, all off the bijection `e` ────────────────────────
    let gdom = {
        let p_w = and_left(w.clone(), g_rel.clone());
        let p_g = and_right(w.clone(), g_rel.clone());
        let p_yb = syl(&p_g, &and_left(mem_y_b.clone(), pair_e.clone()))?;
        let p_pair = syl(&p_g, &and_right(mem_y_b.clone(), pair_e.clone()))?;
        let range = inst_all_imp(&body[0], &[tx.clone(), ty.clone()])?;
        let p_both = hyp_mp(&syl(&syl(&p_w, &bij[0])?, &range)?, &p_pair)?;
        let p_xa = syl(
            &p_both,
            &and_left(mem_x_a.clone(), Formula::mem(ty.clone(), tc.clone())),
        )?;
        hyp_gen(bv, &hyp_gen(xv, &crate::uncurry(&hyp_and(&p_yb, &p_xa)?)?)?)?
    };

    // The only use of `b ⊆ c`: `e` is onto `c`, so it is onto `b` too.
    let gtot = {
        let p = Formula::and(w.clone(), mem_y_b.clone());
        let p_w = and_left(w.clone(), mem_y_b.clone());
        let p_yb = and_right(w.clone(), mem_y_b.clone());
        let p_yc = hyp_mp(
            &hyp_mp(&a1i(&Thm::ax_inst(sub_bc.clone(), ty.clone())?, p.clone()), &syl(&p_w, &w_bc)?)?,
            &p_yb,
        )?;
        let onto = Thm::ax_inst(body[2].clone(), ty.clone())?;
        let p_ex = hyp_mp(&syl(&syl(&p_w, &bij[2])?, &onto)?, &p_yc)?;
        let mk = hyp_mp(&a1i(&and_intro_imp(mem_y_b.clone(), pair_e.clone()), p.clone()), &p_yb)?;
        let out = hyp_mp(&hyp_exists_mono(xv, &mk)?, &p_ex)?;
        hyp_gen(bv, &crate::uncurry(&out)?)?
    };

    let g2 = g_rel.subst(xv, &tx2);
    let gsv = {
        let both = Formula::and(g_rel.clone(), g2.clone());
        let p_w = and_left(w.clone(), both.clone());
        let p_1 = syl(&and_right(w.clone(), both.clone()), &and_left(g_rel.clone(), g2.clone()))?;
        let p_2 = syl(&and_right(w.clone(), both.clone()), &and_right(g_rel.clone(), g2.clone()))?;
        let pair2 = pair_e.subst(xv, &tx2);
        let p_p1 = syl(&p_1, &and_right(mem_y_b.clone(), pair_e.clone()))?;
        let p_p2 = syl(&p_2, &and_right(mem_y_b.clone(), pair2))?;
        let inj = inst_all_imp(&body[4], &[tx.clone(), tx2.clone(), ty.clone()])?;
        let out = hyp_mp(&syl(&syl(&p_w, &bij[4])?, &inj)?, &hyp_and(&p_p1, &p_p2)?)?;
        hyp_gen(bv, &hyp_gen(xv, &hyp_gen(x2, &crate::uncurry(&out)?)?)?)?
    };

    let g3 = g_rel.subst(bv, &ty2);
    let ginj = {
        let both = Formula::and(g_rel.clone(), g3.clone());
        let p_w = and_left(w.clone(), both.clone());
        let p_1 = syl(&and_right(w.clone(), both.clone()), &and_left(g_rel.clone(), g3.clone()))?;
        let p_2 = syl(&and_right(w.clone(), both.clone()), &and_right(g_rel.clone(), g3.clone()))?;
        let pair2 = pair_e.subst(bv, &ty2);
        let p_p1 = syl(&p_1, &and_right(mem_y_b.clone(), pair_e.clone()))?;
        let p_p2 = syl(
            &p_2,
            &and_right(Formula::mem(ty2.clone(), tb.clone()), pair2),
        )?;
        let sv = inst_all_imp(&body[3], &[tx.clone(), ty.clone(), ty2.clone()])?;
        let out = hyp_mp(&syl(&syl(&p_w, &bij[3])?, &sv)?, &hyp_and(&p_p1, &p_p2)?)?;
        hyp_gen(bv, &hyp_gen(y2, &hyp_gen(xv, &crate::uncurry(&out)?)?)?)?
    };

    // ── Feed the scheme, then discharge the bijection ───────────────────────
    let atoms = csb_clauses(env, &f_rel, &g_rel, xv, bv, &ta, &tb)?;
    let proved = [fdom, ftot, fsv, finj, gdom, gtot, gsv, ginj];
    for (i, t) in proved.iter().enumerate() {
        debug_assert_eq!(
            t.concl().as_imp()?.1,
            atoms[i],
            "equinumerous_sandwich: clause {i} is not the one the scheme asks for"
        );
    }
    let mut acc = proved[7].clone();
    for t in proved[..7].iter().rev() {
        acc = hyp_and(t, &acc)?;
    }
    let scheme = csb_scheme(env, s, &f_rel, &g_rel, xv, bv, &ta, &tb)?;
    let w_goal = syl(&acc, &scheme)?;

    let h_equi = and_right(hp.clone(), equi_ac.clone());
    let h_goal = discharge(ev, &h_equi, &w_goal)?;
    let out = gen_all(&[av, bvar, cvar], &h_goal);
    let want = Formula::forall(
        av,
        Formula::forall(
            bvar,
            Formula::forall(
                cvar,
                Formula::imp(h, kernel::thm::equinumerous(env, ta, tb)),
            ),
        ),
    );
    debug_assert_eq!(*out.concl(), want, "equinumerous_sandwich: wrong shape");
    Some(out)
}
