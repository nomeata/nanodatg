//! Three membership characterisations the sum and its eliminator are
//! assembled from. None of them mentions `A + B`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))                        [mem_bin_union_iff]
//! ⊢ ∀t ∀a ∀z. (z ∈ prod({t}, a) ↔ ∃y. (y ∈ a ∧ z = ⟨t,y⟩))         [tagged_copy_members]
//! ⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))                 [pair_in_product]
//! ```
//!
//! All three are unconditional biconditionals. Callers need none of the
//! derivations below; [`super::Sums`] stores the third as a field and consumes
//! the first two while building [`super::sum_members`].
//!
//! # Why each is needed in this form
//!
//! * [`crate::funspace::mem_bin_union`] already gives the two *introduction*
//!   halves of the first. What is wanted here is the elimination as well, so a
//!   disjunction can be read **off** a membership in the union rather than only
//!   put into one — `A + B` is a union, and case analysis on it is the point.
//! * A product over a singleton is a *tagged copy*: its members are exactly the
//!   pairs carrying that tag on the left. Stated for a general tag `t` so that
//!   the two halves of the sum are one instantiation each, at `∅` and at `1`.
//! * The product's own characterisation quantifies over the *components*, which
//!   is the wrong shape whenever the pair is already in hand — as it is
//!   everywhere the eliminator is built, because a function's graph is a set of
//!   pairs. Injectivity of the Kuratowski pair turns one shape into the other.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{hyp_mp2, hyp_syl, or_intro_left, or_intro_right, union_intro, Apply, Sets};
use crate::funspace::{bin_union, Product};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, singleton, syl,
};

use super::shared::{carry_elem, carry_eq_rhs, carry_mem, discharge};

/// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
///
/// [`crate::funspace::mem_bin_union`] gives the two introduction halves; what is
/// wanted here is the elimination as well, so the disjunction can be *read off*
/// a membership in the union rather than only put into one.
pub fn mem_bin_union_iff(env: &mut Env, sets: &Sets) -> Option<Thm> {
    let (u, v, z, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, tz, tw) = (Term::var(u), Term::var(v), Term::var(z), Term::var(w));
    let uv = Term::apply(sets.up, vec![tu.clone(), tv.clone()]);
    let un = bin_union(sets, tu.clone(), tv.clone());

    let mem_zu = Formula::mem(tz.clone(), tu.clone());
    let mem_zv = Formula::mem(tz.clone(), tv.clone());
    let goal = Formula::or(mem_zu.clone(), mem_zv.clone());

    // ── forward ──────────────────────────────────────────────────────────────
    // Under `W := w ∈ {u,v} ∧ z ∈ w`, the pair characterisation splits `w`.
    let mem_w_uv = Formula::mem(tw.clone(), uv.clone());
    let mem_zw = Formula::mem(tz.clone(), tw.clone());
    let big_w = Formula::and(mem_w_uv.clone(), mem_zw.clone());
    let w_disj = syl(
        &and_left(mem_w_uv.clone(), mem_zw.clone()),
        &iff_mp(&inst_all(&sets.up_ax, &[tu.clone(), tv.clone(), tw.clone()])?)?,
    )?;
    let w_zw = and_right(mem_w_uv, mem_zw.clone());

    // Each case assumption `w = u` / `w = v` arrives as the antecedent
    // `hyp_or_elim` supplies, so the rewrite has to happen one implication deep.
    let under_case = |eq: Formula| syl(&w_zw, &Thm::ax_k(mem_zw.clone(), eq));

    let leib_u = carry_mem(env, tz.clone(), tw.clone(), tu.clone());
    let case_u = Formula::eq(tw.clone(), tu.clone());
    let w_left = hyp_mp2(&a1i(&leib_u, big_w.clone()), &under_case(case_u)?).ok()?;
    let w_left = hyp_syl(&w_left, &a1i(&or_intro_left(mem_zu.clone(), mem_zv.clone()), big_w.clone()))?;

    let leib_v = carry_mem(env, tz.clone(), tw.clone(), tv.clone());
    let case_v = Formula::eq(tw.clone(), tv.clone());
    let w_right = hyp_mp2(&a1i(&leib_v, big_w.clone()), &under_case(case_v)?).ok()?;
    let w_right = hyp_syl(&w_right, &a1i(&or_intro_right(mem_zu.clone(), mem_zv.clone()), big_w.clone()))?;

    let w_goal = hyp_or_elim(&w_disj, &w_left, &w_right)?;
    let ex_goal = exists_elim_imp(w, &Thm::gen(w, &w_goal), &goal)?;
    let un_inst = inst_all(&sets.un_ax, &[uv.clone(), tz.clone()])?;
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(tz.clone(), un.clone()), Formula::exists(w, big_w)),
        "mem_bin_union_iff: the Union axiom has an unexpected shape"
    );
    let fwd = syl(&iff_mp(&un_inst)?, &ex_goal)?;

    // ── backward ─────────────────────────────────────────────────────────────
    // The two introduction halves, glued under the disjunction itself.
    let (u_in, v_in) = crate::upair_members(&sets.up_ax, &tu, &tv)?;
    let into_u = union_intro(env, sets, uv.clone(), tu.clone(), tz.clone()).ok()?;
    let l = syl(&hyp_and(&a1i(&u_in, mem_zu.clone()), &imp_refl(mem_zu.clone()))?, &into_u)?;
    let into_v = union_intro(env, sets, uv, tv.clone(), tz.clone()).ok()?;
    let r = syl(&hyp_and(&a1i(&v_in, mem_zv.clone()), &imp_refl(mem_zv.clone()))?, &into_v)?;

    let bwd = hyp_or_elim(&imp_refl(goal.clone()), &a1i(&l, goal.clone()), &a1i(&r, goal.clone()))?;

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(tz, un), goal),
        "mem_bin_union_iff: unexpected shape"
    );
    Some(gen_all(&[u, v, z], &out))
}

/// `⊢ ∀t ∀a ∀z. (z ∈ prod({t}, a) ↔ ∃y. (y ∈ a ∧ z = ⟨t,y⟩))`.
///
/// A product over a singleton is a *tagged copy*: its members are exactly the
/// pairs with the tag on the left. Stated for a general tag `t`, so that both
/// halves of the sum are one instantiation each.
pub fn tagged_copy_members(env: &mut Env, sets: &Sets, mem_sing: &Thm, p: &Product) -> Option<Thm> {
    let (t, a, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, ta, tz) = (Term::var(t), Term::var(a), Term::var(z));
    let st = singleton(sets.up, tt.clone());
    let prod_t = p.of(st.clone(), ta.clone());

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));

    // The two conditions: what the product gives, and what we want instead.
    let inner = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(tz.clone(), sets.pair(tx.clone(), ty.clone())),
    );
    let src_body = Formula::and(Formula::mem(tx.clone(), st.clone()), Formula::exists(y, inner.clone()));
    let src = Formula::exists(x, src_body.clone());
    let tgt_body = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(tz.clone(), sets.pair(tt.clone(), ty.clone())),
    );
    let tgt = Formula::exists(y, tgt_body.clone());

    let prod_at = inst_all(&p.prod_ax, &[st.clone(), ta.clone(), tz.clone()])?;
    debug_assert_eq!(
        *prod_at.concl(),
        Formula::iff(Formula::mem(tz.clone(), prod_t.clone()), src.clone()),
        "tagged_copy_members: the product's membership condition has an unexpected shape"
    );

    // ── forward ──────────────────────────────────────────────────────────────
    // Under `E := x ∈ {t} ∧ ∃y. …`, then `F := E ∧ (y ∈ a ∧ z = ⟨x,y⟩)`.
    let ms = mem_sing;
    let e_xt = syl(
        &and_left(Formula::mem(tx.clone(), st.clone()), Formula::exists(y, inner.clone())),
        &iff_mp(&inst_all(ms, &[tt.clone(), tx.clone()])?)?,
    )?;
    let f = Formula::and(src_body.clone(), inner.clone());
    let f_e = and_left(src_body.clone(), inner.clone());
    let f_inner = and_right(src_body.clone(), inner.clone());
    let f_ya = syl(
        &f_inner,
        &and_left(Formula::mem(ty.clone(), ta.clone()), Formula::eq(tz.clone(), sets.pair(tx.clone(), ty.clone()))),
    )?;
    let f_eq = syl(
        &f_inner,
        &and_right(Formula::mem(ty.clone(), ta.clone()), Formula::eq(tz.clone(), sets.pair(tx.clone(), ty.clone()))),
    )?;
    let f_xt = syl(&f_e, &e_xt)?;

    // `x = t` rewrites `⟨x,y⟩` to `⟨t,y⟩` on the right of the equation.
    let w = env.fresh_var();
    let pair_congr = mpd_const(
        &Thm::eq_leibniz(
            tx.clone(),
            tt.clone(),
            w,
            Formula::eq(sets.pair(tx.clone(), ty.clone()), sets.pair(Term::var(w), ty.clone())),
        ),
        &Thm::eq_refl(sets.pair(tx.clone(), ty.clone())),
    )?;
    let f_pair_eq = hyp_mp(&a1i(&pair_congr, f.clone()), &f_xt)?;
    let carry = carry_eq_rhs(env, tz.clone(), sets.pair(tx.clone(), ty.clone()), sets.pair(tt.clone(), ty.clone()));
    let f_z_eq = hyp_mp(&hyp_mp(&a1i(&carry, f.clone()), &f_pair_eq)?, &f_eq)?;
    let f_tgt = syl(&hyp_and(&f_ya, &f_z_eq)?, &exists_intro_imp(y, tgt_body.clone(), ty.clone())?)?;

    let e_tgt = discharge(y, &and_right(Formula::mem(tx.clone(), st.clone()), Formula::exists(y, inner.clone())), &f_tgt)?;
    let src_tgt = exists_elim_imp(x, &Thm::gen(x, &e_tgt), &tgt)?;
    let fwd = syl(&iff_mp(&prod_at)?, &src_tgt)?;

    // ── backward ─────────────────────────────────────────────────────────────
    // Witness `x := t`: the tag is in its own singleton, and the inner
    // existential is the hypothesis itself.
    let t_in_st = Thm::mp(&iff_mpr(&inst_all(ms, &[tt.clone(), tt.clone()])?)?, &Thm::eq_refl(tt.clone()))?;
    let g_inner = exists_intro_imp(y, tgt_body.clone(), ty.clone())?;
    let g_pair = hyp_and(&a1i(&t_in_st, tgt_body.clone()), &g_inner)?;
    let g_src = syl(&g_pair, &exists_intro_imp(x, src_body, tt.clone())?)?;
    let bwd = syl(&exists_elim_imp(y, &Thm::gen(y, &g_src), &src)?, &iff_mpr(&prod_at)?)?;

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(tz, prod_t), tgt),
        "tagged_copy_members: unexpected shape"
    );
    Some(gen_all(&[t, a, z], &out))
}

/// `⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))`.
pub fn pair_in_product(env: &mut Env, ap: &Apply, p: &Product) -> Option<Thm> {
    let (a, t, u, v) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tt, tu, tv) = (Term::var(a), Term::var(t), Term::var(u), Term::var(v));
    let pair_uv = ap.sets.pair(tu.clone(), tv.clone());
    let prod_t = p.of(ta.clone(), tt.clone());

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let inner_body = Formula::and(
        Formula::mem(ty.clone(), tt.clone()),
        Formula::eq(pair_uv.clone(), ap.sets.pair(tx.clone(), ty.clone())),
    );
    let inner = Formula::exists(y, inner_body.clone());
    let outer_body = Formula::and(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let cond = Formula::exists(x, outer_body.clone());

    let mem_ua = Formula::mem(tu.clone(), ta.clone());
    let mem_vt = Formula::mem(tv.clone(), tt.clone());
    let goal = Formula::and(mem_ua.clone(), mem_vt.clone());

    let prod_at = inst_all(&p.prod_ax, &[ta.clone(), tt.clone(), pair_uv.clone()])?;
    debug_assert_eq!(
        *prod_at.concl(),
        Formula::iff(Formula::mem(pair_uv.clone(), prod_t.clone()), cond.clone()),
        "pair_in_product: the product's membership condition has an unexpected shape"
    );

    // ── forward ──────────────────────────────────────────────────────────────
    // Under `F := (x ∈ A ∧ ∃y. …) ∧ (y ∈ T ∧ ⟨u,v⟩ = ⟨x,y⟩)`.
    let f = Formula::and(outer_body.clone(), inner_body.clone());
    let f_outer = and_left(outer_body.clone(), inner_body.clone());
    let f_inner = and_right(outer_body.clone(), inner_body.clone());
    let f_xa = syl(&f_outer, &and_left(Formula::mem(tx.clone(), ta.clone()), inner.clone()))?;
    let f_yt = syl(
        &f_inner,
        &and_left(Formula::mem(ty.clone(), tt.clone()), Formula::eq(pair_uv.clone(), ap.sets.pair(tx.clone(), ty.clone()))),
    )?;
    let f_eq = syl(
        &f_inner,
        &and_right(Formula::mem(ty.clone(), tt.clone()), Formula::eq(pair_uv.clone(), ap.sets.pair(tx.clone(), ty.clone()))),
    )?;

    let inj = inst_all(&ap.pair_inj, &[tu.clone(), tv.clone(), tx.clone(), ty.clone()])?;
    let f_conj = syl(&f_eq, &inj)?;
    let (e_ux, e_vy) = (Formula::eq(tu.clone(), tx.clone()), Formula::eq(tv.clone(), ty.clone()));
    let f_ux = syl(&f_conj, &and_left(e_ux.clone(), e_vy.clone()))?;
    let f_vy = syl(&f_conj, &and_right(e_ux, e_vy))?;

    let f_xu = syl(&f_ux, &eq_symm_imp(env, tu.clone(), tx.clone()))?;
    let f_yv = syl(&f_vy, &eq_symm_imp(env, tv.clone(), ty.clone()))?;
    let carry_a = carry_elem(env, tx.clone(), tu.clone(), ta.clone());
    let f_ua = hyp_mp(&hyp_mp(&a1i(&carry_a, f.clone()), &f_xu)?, &f_xa)?;
    let carry_t = carry_elem(env, ty.clone(), tv.clone(), tt.clone());
    let f_vt = hyp_mp(&hyp_mp(&a1i(&carry_t, f.clone()), &f_yv)?, &f_yt)?;
    let f_goal = hyp_and(&f_ua, &f_vt)?;

    let outer_goal = discharge(y, &and_right(Formula::mem(tx.clone(), ta.clone()), inner.clone()), &f_goal)?;
    let fwd = syl(&iff_mp(&prod_at)?, &exists_elim_imp(x, &Thm::gen(x, &outer_goal), &goal)?)?;

    // ── backward ─────────────────────────────────────────────────────────────
    // Witnesses `x := u` and `y := v`, with the equation reflexivity.
    // The inner existential is the one that survives substituting `x := u`, so
    // its body has to be built at `u` rather than at the bound `x`.
    let inner_body_u = Formula::and(
        Formula::mem(ty.clone(), tt.clone()),
        Formula::eq(pair_uv.clone(), ap.sets.pair(tu.clone(), ty.clone())),
    );
    debug_assert_eq!(inner_body_u, inner_body.subst(x, &tu), "pair_in_product: substitution drift");
    let g_vt = and_right(mem_ua.clone(), mem_vt.clone());
    let g_refl = a1i(&Thm::eq_refl(pair_uv.clone()), goal.clone());
    let g_inner = syl(&hyp_and(&g_vt, &g_refl)?, &exists_intro_imp(y, inner_body_u, tv.clone())?)?;
    let g_ua = and_left(mem_ua, mem_vt);
    let bwd = syl(
        &syl(&hyp_and(&g_ua, &g_inner)?, &exists_intro_imp(x, outer_body, tu.clone())?)?,
        &iff_mpr(&prod_at)?,
    )?;

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(pair_uv, prod_t), goal),
        "pair_in_product: unexpected shape"
    );
    Some(gen_all(&[a, t, u, v], &out))
}
