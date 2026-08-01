//! The successor `succ(n) = n ∪ {n}`, and the two facts that let `ω` be carved
//! out of a Tarski universe at all.
//!
//! # Interface
//!
//! Writing `Trans(q)` for [`crate::empty::transitive`], the exports are
//!
//! ```text
//! ⊢ ∀n ∀z. (z ∈ ⋃{n,{n}} ↔ (z ∈ n ∨ z = n))        [mem_union_succ]
//! ⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))         [successor — introduces `succ`]
//! ⊢ ∀q. (Trans(q) → succ(q) ⊆ 𝒫q)                  [succ_subset_pow]
//! ⊢ ∀q. (Trans(q) → Trans(succ(q)))                [trans_succ]
//! ⊢ Trans(∅)                                       [trans_empty]
//! ```
//!
//! `succ` is an implicit definition rather than the abbreviation `⋃{n,{n}}`, so
//! that its characteristic theorem *is* the membership condition — the only
//! thing about `succ` any derivation downstream uses. Callers need none of the
//! derivations below.
//!
//! # Why the two transitivity lemmas are the crux
//!
//! `ω` is cut out of the Tarski universe `u` around `∅`, and that requires `u`
//! to be closed under the operation being iterated. `u` **is** closed under `𝒫`
//! ([`crate::empty::universe_power_closed`]) but it is *not* closed under
//! `n ↦ n ∪ {n}` by any route that the first three Tarski clauses supply: see
//! the module documentation of [`crate::recursion`] for the two obstructions
//! that motivated the detour below. Both have since been removed —
//! [`crate::universe::universe_union_closed`] proves `⋃a ∈ u` and
//! [`crate::universe::universe_pairing`] proves pairing closure — so the detour
//! is now an economy rather than a necessity, and the derivations here are
//! unaffected either way.
//!
//! The way through is that closure is only needed **at transitive sets**. If
//! `n` is transitive then every member of `n` is a subset of `n`, so
//! `succ(n) ⊆ 𝒫n` ([`succ_subset_pow`]), and `𝒫n ∈ u` plus Tarski's second
//! clause puts `succ(n)` back into `u`. [`trans_succ`] is what propagates the
//! transitivity along the induction, and [`trans_empty`] is its base case. Every
//! von Neumann natural is transitive, so nothing is lost — and the transitivity
//! is carried in the separation condition defining `ω` rather than assumed,
//! which is what makes the argument non-circular. See
//! [`crate::recursion::omega_exists`].

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Sets};
use crate::separation::{or_intro_left, or_intro_right};
use crate::{
    a1i, and_intro, and_left, and_right, com12, define_by_membership, eq_symm_imp,
    exists_elim_imp, exists_intro, gen_all, hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr,
    imp_mono_r, imp_refl, inst_all, mpd_const, singleton, syl, uncurry,
};

/// `⊢ ∀n ∀z. (z ∈ ⋃{n,{n}} ↔ (z ∈ n ∨ z = n))`.
///
/// `n ∪ {n}` spelled out through the Union and Pairing characterisations. The
/// forward half is a case analysis on which member of `{n,{n}}` the witness is;
/// the backward half witnesses the union's existential at `n` and at `{n}`
/// respectively.
pub fn mem_union_succ(env: &mut Env, sets: &Sets, mem_sing: &Thm) -> Option<Thm> {
    let (n, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, tz, ty) = (Term::var(n), Term::var(z), Term::var(y));
    let sn = singleton(sets.up, tn.clone());
    let p = Term::apply(sets.up, vec![tn.clone(), sn.clone()]);
    let u = sets.union_of(p.clone());

    let mem_zn = Formula::mem(tz.clone(), tn.clone());
    let eq_zn = Formula::eq(tz.clone(), tn.clone());
    let goal = Formula::or(mem_zn.clone(), eq_zn.clone());

    let un_inst = inst_all(&sets.un_ax, &[p.clone(), tz.clone()])?;
    let mem_yp = Formula::mem(ty.clone(), p.clone());
    let mem_zy = Formula::mem(tz.clone(), ty.clone());
    let b = Formula::and(mem_yp.clone(), mem_zy.clone());
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(tz.clone(), u.clone()), Formula::exists(y, b.clone())),
        "mem_union_succ: the Union axiom has an unexpected shape"
    );

    // ── forward: a member of ⋃{n,{n}} lies in `n` or is `n` ──────────────────
    let b_yp = and_left(mem_yp.clone(), mem_zy.clone());
    let b_zy = and_right(mem_yp, mem_zy);
    let b_disj = syl(&b_yp, &iff_mp(&inst_all(&sets.up_ax, &[tn.clone(), sn.clone(), ty.clone()])?)?)?;

    let eq_yn = Formula::eq(ty.clone(), tn.clone());
    let eq_ysn = Formula::eq(ty.clone(), sn.clone());

    // Case `y = n`: `z ∈ y` is `z ∈ n`.
    let w1 = env.fresh_var();
    let leib1 = Thm::eq_leibniz(ty.clone(), tn.clone(), w1, Formula::mem(tz.clone(), Term::var(w1)));
    let b_case1 = syl(&b_zy, &com12(&leib1)?)?;
    let case1 = syl(&b_case1, &imp_mono_r(&or_intro_left(mem_zn.clone(), eq_zn.clone()), eq_yn)?)?;

    // Case `y = {n}`: `z ∈ {n}`, so `z = n`.
    let ms_at = inst_all(mem_sing, &[tn.clone(), tz.clone()])?;
    let w2 = env.fresh_var();
    let leib2 = Thm::eq_leibniz(ty.clone(), sn.clone(), w2, Formula::mem(tz.clone(), Term::var(w2)));
    let b_in_sn = syl(&b_zy, &com12(&leib2)?)?;
    let b_case2 = syl(&b_in_sn, &imp_mono_r(&iff_mp(&ms_at)?, eq_ysn.clone())?)?;
    let case2 = syl(&b_case2, &imp_mono_r(&or_intro_right(mem_zn.clone(), eq_zn.clone()), eq_ysn)?)?;

    let b_goal = hyp_or_elim(&b_disj, &case1, &case2)?;
    let ex_goal = exists_elim_imp(y, &Thm::gen(y, &b_goal), &goal)?;
    let fwd = syl(&iff_mp(&un_inst)?, &ex_goal)?;

    // ── backward: `n` and `{n}` are both members of `{n,{n}}` ────────────────
    let (n_in_p, sn_in_p) = crate::upair_members(&sets.up_ax, &tn, &sn)?;
    let ui_n = union_intro(env, sets, p.clone(), tn.clone(), tz.clone())?;
    let bwd_l = syl(&hyp_and(&a1i(&n_in_p, mem_zn.clone()), &imp_refl(mem_zn.clone()))?, &ui_n)?;
    let ui_sn = union_intro(env, sets, p, sn, tz.clone())?;
    let bwd_r = syl(&hyp_and(&a1i(&sn_in_p, eq_zn.clone()), &iff_mpr(&ms_at)?)?, &ui_sn)?;
    let bwd = hyp_or_elim(
        &imp_refl(goal.clone()),
        &a1i(&bwd_l, goal.clone()),
        &a1i(&bwd_r, goal.clone()),
    )?;

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(tz, u), goal),
        "mem_union_succ: unexpected shape"
    );
    Some(gen_all(&[n, z], &out))
}

/// The successor symbol `succ`, with
/// `⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))`.
///
/// An implicit definition rather than the abbreviation `⋃{n,{n}}`, so that the
/// characteristic theorem *is* the membership condition — which is the only
/// thing about `succ` any derivation below uses. Existence is
/// [`mem_union_succ`]; uniqueness is Extensionality, via
/// [`crate::define_by_membership`].
pub fn successor(env: &mut Env, sets: &Sets, mem_sing: &Thm) -> Option<(FnSym, Thm)> {
    let mus = mem_union_succ(env, sets, mem_sing)?;
    let (n, z) = (env.fresh_var(), env.fresh_var());
    let (tn, tz) = (Term::var(n), Term::var(z));
    let u = sets.union_of(Term::apply(sets.up, vec![tn.clone(), singleton(sets.up, tn.clone())]));

    let phi = Formula::or(Formula::mem(tz.clone(), tn.clone()), Formula::eq(tz.clone(), tn.clone()));
    let at_n = inst_all(&mus, std::slice::from_ref(&tn))?;

    let sv = env.fresh_var();
    let p = Formula::forall(z, Formula::iff(Formula::mem(tz, Term::var(sv)), phi.clone()));
    let existence = exists_intro(sv, p, u, &at_n)?;
    define_by_membership(env, &[n], &existence, z, &phi)
}

// ─────────────────────────────────────────────────────────────────────────────
// Successor and transitivity.
//
// These two lemmas are what let `ω` be carved out of Tarski's universe at all:
// the universe is closed under `𝒫` but not under `⋃`, so the only way in is to
// show that at a *transitive* argument the successor lands inside a power set
// the universe already has. See the module documentation.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀q. (Trans(q) → succ(q) ⊆ 𝒫q)`.
///
/// A member of `succ(q)` is a member of `q` — hence, by transitivity, a subset
/// of `q` — or is `q` itself, which is a subset of `q` by reflexivity. Either
/// way it is a member of `𝒫q`.
pub fn succ_subset_pow(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    succ: FnSym,
    succ_ax: &Thm,
) -> Option<Thm> {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let trans = crate::empty::transitive(env, &tq);
    let sq = Term::apply(succ, vec![tq.clone()]);
    let pq = Term::apply(pow, vec![tq.clone()]);

    let (z, b, hole) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tz, tb) = (Term::var(z), Term::var(b));

    // `sub_hole(·) := ∀b. (b ∈ · → b ∈ q)`, so that Leibniz can move the hole.
    let sub_hole = Formula::forall(
        b,
        Formula::imp(Formula::mem(tb.clone(), Term::var(hole)), Formula::mem(tb.clone(), tq.clone())),
    );
    let sub_z = sub_hole.subst(hole, &tz);
    debug_assert_eq!(
        sub_z,
        kernel::thm::subset(env, tz.clone(), tq.clone()),
        "succ_subset_pow: the subset formula is not the one the Power axiom uses"
    );

    let mem_zq = Formula::mem(tz.clone(), tq.clone());
    let eq_zq = Formula::eq(tz.clone(), tq.clone());
    let mem_zp = Formula::mem(tz.clone(), pq.clone());
    let pow_at = inst_all(pow_ax, &[tq.clone(), tz.clone()])?;
    debug_assert_eq!(
        *pow_at.concl(),
        Formula::iff(mem_zp.clone(), sub_z.clone()),
        "succ_subset_pow: the Power axiom has an unexpected shape"
    );

    // ── `z ∈ q`: transitivity makes `z` a subset ─────────────────────────────
    let trans_z = Thm::ax_inst(trans.clone(), tz.clone())?;
    let (_, trans_z_body) = trans_z.concl().as_imp()?;
    let trans_zb = syl(&trans_z, &Thm::ax_inst(trans_z_body, tb.clone())?)?;

    let k = Formula::and(trans.clone(), mem_zq.clone());
    let k_trans = and_left(trans.clone(), mem_zq.clone());
    let k_zq = and_right(trans.clone(), mem_zq.clone());
    let mem_bz = Formula::mem(tb.clone(), tz.clone());
    let l_k = and_left(k.clone(), mem_bz.clone());
    let l_bz = and_right(k.clone(), mem_bz.clone());
    let l_pair = hyp_and(&l_bz, &syl(&l_k, &k_zq)?)?;
    let l_bq = hyp_mp(&syl(&l_k, &syl(&k_trans, &trans_zb)?)?, &l_pair)?;
    let k_sub = Thm::mp(
        &Thm::ax_dist(b, k.clone(), Formula::imp(mem_bz, Formula::mem(tb.clone(), tq.clone())))?,
        &Thm::gen(b, &uncurry(&l_bq)?),
    )?;
    debug_assert_eq!(*k_sub.concl(), Formula::imp(k.clone(), sub_z.clone()));
    let case_mem = uncurry(&syl(&k_sub, &iff_mpr(&pow_at)?)?)?;

    // ── `z = q`: `q ⊆ q` carried back along the equation ─────────────────────
    let q_sub_q = Thm::gen(b, &imp_refl(Formula::mem(tb, tq.clone())));
    debug_assert_eq!(*q_sub_q.concl(), sub_hole.subst(hole, &tq));
    let leib = Thm::eq_leibniz(tq.clone(), tz.clone(), hole, sub_hole);
    let qz_sub = mpd_const(&leib, &q_sub_q)?;
    let zq_sub = syl(&eq_symm_imp(env, tz.clone(), tq.clone()), &qz_sub)?;
    let case_eq = a1i(&syl(&zq_sub, &iff_mpr(&pow_at)?)?, trans.clone());

    // ── Combine over `z ∈ succ(q) → (z ∈ q ∨ z = q)` ─────────────────────────
    let mem_zs = Formula::mem(tz.clone(), sq.clone());
    let h = Formula::and(trans.clone(), mem_zs.clone());
    let h_trans = and_left(trans.clone(), mem_zs.clone());
    let succ_at = inst_all(succ_ax, &[tq.clone(), tz.clone()])?;
    debug_assert_eq!(
        *succ_at.concl(),
        Formula::iff(mem_zs.clone(), Formula::or(mem_zq, eq_zq)),
        "succ_subset_pow: the successor axiom has an unexpected shape"
    );
    let h_disj = syl(&and_right(trans.clone(), mem_zs.clone()), &iff_mp(&succ_at)?)?;
    let h_goal = hyp_or_elim(
        &h_disj,
        &syl(&h_trans, &case_mem)?,
        &syl(&and_left(trans.clone(), mem_zs.clone()), &case_eq)?,
    )?;
    debug_assert_eq!(*h_goal.concl(), Formula::imp(h, mem_zp.clone()));

    let out = Thm::mp(
        &Thm::ax_dist(z, trans.clone(), Formula::imp(mem_zs, mem_zp))?,
        &Thm::gen(z, &uncurry(&h_goal)?),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(trans, kernel::thm::subset(env, sq, pq)),
        "succ_subset_pow: unexpected shape"
    );
    Some(Thm::gen(q, &out))
}

/// `⊢ ∀q. (Trans(q) → Trans(succ(q)))`.
///
/// A member of a member of `q ∪ {q}` is either a member of a member of `q` —
/// caught by transitivity — or a member of `q`. Both land in `q`, hence in
/// `q ∪ {q}`.
pub fn trans_succ(env: &mut Env, succ: FnSym, succ_ax: &Thm) -> Option<Thm> {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let trans = crate::empty::transitive(env, &tq);
    let sq = Term::apply(succ, vec![tq.clone()]);

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));

    let mem_ba = Formula::mem(tb.clone(), ta.clone());
    let mem_as = Formula::mem(ta.clone(), sq.clone());
    let mem_aq = Formula::mem(ta.clone(), tq.clone());
    let eq_aq = Formula::eq(ta.clone(), tq.clone());
    let mem_bq = Formula::mem(tb.clone(), tq.clone());
    let mem_bs = Formula::mem(tb.clone(), sq.clone());

    // `⊢ b ∈ q → b ∈ succ(q)`, the shared tail of both cases.
    let succ_b = inst_all(succ_ax, &[tq.clone(), tb.clone()])?;
    let b_up = syl(&or_intro_left(mem_bq.clone(), Formula::eq(tb.clone(), tq.clone())), &iff_mpr(&succ_b)?)?;

    // `⊢ Trans(q) → ((b ∈ a ∧ a ∈ q) → b ∈ q)`.
    let trans_a = Thm::ax_inst(trans.clone(), ta.clone())?;
    let (_, trans_a_body) = trans_a.concl().as_imp()?;
    let trans_ab = syl(&trans_a, &Thm::ax_inst(trans_a_body, tb.clone())?)?;

    let inner = Formula::and(mem_ba.clone(), mem_as.clone());
    let k = Formula::and(trans.clone(), inner.clone());
    let k_trans = and_left(trans.clone(), inner.clone());
    let k_inner = and_right(trans.clone(), inner.clone());
    let k_ba = syl(&k_inner, &and_left(mem_ba.clone(), mem_as.clone()))?;
    let k_as = syl(&k_inner, &and_right(mem_ba.clone(), mem_as.clone()))?;

    let succ_a = inst_all(succ_ax, &[tq.clone(), ta.clone()])?;
    let k_disj = syl(&k_as, &iff_mp(&succ_a)?)?;

    // Case `a ∈ q`: transitivity.
    let l_k = and_left(k.clone(), mem_aq.clone());
    let l_aq = and_right(k.clone(), mem_aq.clone());
    let l_pair = hyp_and(&syl(&l_k, &k_ba)?, &l_aq)?;
    let l_bq = hyp_mp(&syl(&l_k, &syl(&k_trans, &trans_ab)?)?, &l_pair)?;
    let case_mem = syl(&uncurry(&l_bq)?, &imp_mono_r(&b_up, mem_aq.clone())?)?;

    // Case `a = q`: rewrite `b ∈ a` along the equation.
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(ta.clone(), tq.clone(), hole, Formula::mem(tb.clone(), Term::var(hole)));
    let k_case_eq = syl(&k_ba, &com12(&leib)?)?;
    let case_eq = syl(&k_case_eq, &imp_mono_r(&b_up, eq_aq)?)?;

    let k_goal = hyp_or_elim(&k_disj, &case_mem, &case_eq)?;
    debug_assert_eq!(*k_goal.concl(), Formula::imp(k, mem_bs.clone()));

    let body = uncurry(&k_goal)?;
    let all_b = Thm::mp(
        &Thm::ax_dist(b, trans.clone(), Formula::imp(inner.clone(), mem_bs.clone()))?,
        &Thm::gen(b, &body),
    )?;
    let inner_all = Formula::forall(b, Formula::imp(inner, mem_bs));
    let all_a =
        Thm::mp(&Thm::ax_dist(a, trans.clone(), inner_all)?, &Thm::gen(a, &all_b))?;
    debug_assert_eq!(
        *all_a.concl(),
        Formula::imp(trans, crate::empty::transitive(env, &sq)),
        "trans_succ: unexpected shape"
    );
    Some(Thm::gen(q, &all_a))
}

/// `⊢ Trans(∅)` — the empty set is transitive, vacuously.
///
/// `empty_ax` must be a proof `⊢ ∀z. ¬(z ∈ e)`; the term `e` is read off it, so
/// a caller cannot slip in something else.
pub fn trans_empty(env: &mut Env, empty_ax: &Thm) -> Option<Thm> {
    let probe = env.fresh_var();
    let (mem_probe, fls) = inst_all(empty_ax, &[Term::var(probe)])?.concl().as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (lhs, zero) = mem_probe.as_mem()?;
    if lhs != Term::var(probe) || zero.occurs_free(probe) {
        return None
    }

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let not_a_in_zero = inst_all(empty_ax, std::slice::from_ref(&ta))?;
    let mem_ba = Formula::mem(tb.clone(), ta.clone());
    let mem_az = Formula::mem(ta, zero.clone());
    let absurd = syl(&not_a_in_zero, &crate::ex_falso(Formula::mem(tb, zero.clone())))?;
    let out = Thm::gen(av, &Thm::gen(bv, &syl(&and_right(mem_ba, mem_az), &absurd)?));
    debug_assert_eq!(
        *out.concl(),
        crate::empty::transitive(env, &zero),
        "trans_empty: unexpected shape"
    );
    Some(out)
}
