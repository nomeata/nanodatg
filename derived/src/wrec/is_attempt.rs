//! **Steps 5 and 6** — the recursor is itself an attempt, and hence ι holds on
//! its domain.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → rec_cond(B,e,wrec))          [wrec_rec_cond]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → wrec ∈ Att)                [wrec_is_attempt]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. ∅ ∈ Att                                      [empty_attempt]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀a ∀f. (indom(wrec, ⟨a,f⟩) →
//!           app(wrec, ⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩)))  [iota_on_domain]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why step 6 is in this file
//!
//! [`iota_on_domain`] is **the whole of ι except for the guard**, and it is
//! exactly [`wrec_rec_cond`] with the subterm clause dropped — twenty lines of
//! projection off its immediate predecessor, with no separate argument of its
//! own. Putting an interface between the two would document nothing, so they
//! stay together. Stating it separately at all is what makes the remaining
//! obligation precise: the ι rule is this theorem with `indom(wrec, ⟨a,f⟩)`
//! discharged from `a ∈ A` and `f ∈ fs(B(a), W)`, which is **totality** and
//! nothing else — [`crate::wrec_total::totality`].
//!
//! [`empty_attempt`] is here because it is what makes `Att` non-empty and hence
//! `wrec` meaningful before totality: `∅` satisfies every clause vacuously.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funspace::is_single_valued;
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

use super::hyp::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim, hyp_inst, hyp_split, split_and};
use super::composite::agree_on;
use super::attempt::{indom, indom_intro, rec_cond};

/// **The recursion equation already holds on the recursor's own domain.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → rec_cond(wrec(A,B,u,T,e)))
/// ```
///
/// A point of `dom wrec` lies in `dom g` for some attempt `g`. Everything then
/// transfers: the subterms are in `dom g`, hence in `dom wrec`
/// ([`super::attempt_indom_wrec`]); and `wrec` takes `g`'s value at every one of them
/// ([`super::wrec_value`]), so the two composites are equal ([`super::compose_ext`]) and
/// `g`'s own recursion equation is `wrec`'s.
#[allow(clippy::too_many_arguments)]
pub fn wrec_rec_cond(
    env: &mut Env,
    wt: &Wtype,
    comp: FnSym,
    comp_ext: &Thm,
    att: FnSym,
    att_ax: &Thm,
    wrec: FnSym,
    members: &Thm,
    value: &Thm,
    mono: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, te) = (args[0].clone(), args[1].clone(), args[2].clone(), args[4].clone());
    let f_t = Term::apply(wrec, args.clone());
    let c = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let (pa, pf, pb, gv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tpa, tpf, tpb, tg, ty) = (
        Term::var(pa),
        Term::var(pf),
        Term::var(pb),
        Term::var(gv),
        Term::var(yv),
    );
    let fibre = ap.apply(tb.clone(), tpa.clone());
    let w = ap.sets.pair(tpa.clone(), tpf.clone());
    let fb = ap.apply(tpf.clone(), tpb.clone());

    // ── H := closed ∧ indom(F, ⟨a,f⟩) ───────────────────────────────────────
    let ind_f_w = indom(env, ap, &f_t, &w);
    let h = Formula::and(c.clone(), ind_f_w.clone());
    let h_c = and_left(c.clone(), ind_f_w.clone());
    let h_ex = and_right(c.clone(), ind_f_w);

    // ── N := H ∧ ⟨⟨a,f⟩,y⟩ ∈ F ──────────────────────────────────────────────
    let pair_wy = ap.sets.pair(w.clone(), ty.clone());
    let mem_wy_f = Formula::mem(pair_wy.clone(), f_t.clone());
    let n = Formula::and(h.clone(), mem_wy_f.clone());
    let n_h = and_left(h.clone(), mem_wy_f.clone());
    let n_pf = and_right(h.clone(), mem_wy_f);
    let n_c = syl(&n_h, &h_c)?;

    let mut with_pair = args.clone();
    with_pair.push(pair_wy.clone());
    let n_exg = syl(&n_pf, &iff_mp(&inst_all(members, &with_pair)?)?)?;

    // ── M := N ∧ (g ∈ Att ∧ ⟨⟨a,f⟩,y⟩ ∈ g) ──────────────────────────────────
    let gg = Formula::and(
        Formula::mem(tg.clone(), Term::apply(att, args.clone())),
        Formula::mem(pair_wy, tg.clone()),
    );
    let m = Formula::and(n.clone(), gg.clone());
    let m_n = and_left(n.clone(), gg.clone());
    let m_gg = and_right(n.clone(), gg.clone());
    let m_c = syl(&m_n, &n_c)?;
    let (m_gatt, m_gpair) = hyp_split(&m_gg)?;
    let intro = indom_intro(env, ap, &tg, &w, &ty)?;
    let m_indg = syl(&m_gpair, &intro)?;

    // `g`'s own recursion condition, at `⟨a,f⟩`.
    let mut with_g = args.clone();
    with_g.push(tg.clone());
    let ax = inst_all(att_ax, &with_g)?;
    let (_, cond) = hyp_split(&syl(&m_gatt, &iff_mp(&ax)?)?)?;
    let m_recg = hyp_split(&cond)?.1;
    let (m_subg, m_eqg) = hyp_split(&hyp_mp(
        &hyp_inst(&m_recg, &[tpa.clone(), tpf.clone()])?,
        &m_indg,
    )?)?;

    // The two transfer lemmas, specialised to this `g`.
    let m_val = hyp_mp(
        &hyp_inst(&syl(&m_c, &inst_all(value, &args)?)?, std::slice::from_ref(&tg))?,
        &m_gatt,
    )?;
    let m_mono = syl(&m_gatt, &inst_all(mono, &with_g)?)?;

    // ── Per subterm: P := M ∧ b ∈ B(a) ──────────────────────────────────────
    let mem_b = Formula::mem(tpb.clone(), fibre.clone());
    let p_m = and_left(m.clone(), mem_b.clone());
    let p_b = and_right(m.clone(), mem_b.clone());
    let p_indg = hyp_mp(
        &hyp_inst(&syl(&p_m, &m_subg)?, std::slice::from_ref(&tpb))?,
        &p_b,
    )?;
    let p_indf = hyp_mp(
        &hyp_inst(&syl(&p_m, &m_mono)?, std::slice::from_ref(&fb))?,
        &p_indg,
    )?;
    let p_val = hyp_mp(
        &hyp_inst(&syl(&p_m, &m_val)?, std::slice::from_ref(&fb))?,
        &p_indg,
    )?;
    let p_sym = hyp_eq_symm(env, &p_val)?;

    let gen_over_b = |t: &Thm| -> Option<Thm> {
        let curried = uncurry(t)?;
        let (_, body) = curried.concl().as_imp()?;
        Thm::mp(&Thm::ax_dist(pb, m.clone(), body)?, &Thm::gen(pb, &curried))
    };
    let m_sub_f = gen_over_b(&p_indf)?;
    let m_agree = gen_over_b(&p_sym)?;
    debug_assert_eq!(
        *m_agree.concl(),
        Formula::imp(m.clone(), agree_on(env, ap, &tg, &f_t, &tpf, &fibre)),
        "wrec_rec_cond: the fibre-wise agreement is not the one compose_ext wants"
    );

    // ── … so the two step values agree, and `g`'s equation is `F`'s ─────────
    let ext_at = inst_all(comp_ext, &[tg.clone(), f_t.clone(), tpf.clone(), fibre.clone()])?;
    let m_comp = syl(&m_agree, &ext_at)?;
    let ctx = |t: Term| {
        ap.apply(te.clone(), ap.sets.pair(tpa.clone(), ap.sets.pair(tpf.clone(), t)))
    };
    let m_step = hyp_congr(env, &m_comp, ctx)?;
    let m_fw = hyp_mp(&hyp_inst(&m_val, std::slice::from_ref(&w))?, &m_indg)?;
    let m_right = hyp_eq_trans(env, &m_eqg, &m_step)?;
    let m_eq_f = hyp_eq_trans(env, &m_fw, &m_right)?;
    let m_goal = hyp_and(&m_sub_f, &m_eq_f)?;

    // ── Discharge the two witnesses, then generalise ────────────────────────
    let n_goal = hyp_exists_elim(gv, &m_goal, &n_exg)?;
    let h_goal = hyp_exists_elim(yv, &n_goal, &h_ex)?;

    let per_f = uncurry(&h_goal)?;
    let (_, bf) = per_f.concl().as_imp()?;
    let all_f = Thm::mp(&Thm::ax_dist(pf, c.clone(), bf)?, &Thm::gen(pf, &per_f))?;
    let (_, ba) = all_f.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(pa, c.clone(), ba)?, &Thm::gen(pa, &all_f))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(c, rec_cond(env, ap, comp, &tb, &te, &f_t)),
        "wrec_rec_cond: unexpected shape"
    );
    Some(gen_all(&vars, &out))
}

/// **The recursor is an attempt.**
/// `⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → wrec(A,B,u,T,e) ∈ Att(A,B,u,T,e))`
///
/// The three clauses assembled: [`super::wrec_subset_prod`] (so it is in the power
/// set Separation carves from), [`super::wrec_single_valued`], [`wrec_rec_cond`].
#[allow(clippy::too_many_arguments)]
pub fn wrec_is_attempt(
    env: &mut Env,
    wt: &Wtype,
    att_ax: &Thm,
    wrec: FnSym,
    subset_prod: &Thm,
    sv_thm: &Thm,
    rec_thm: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt) = (args[0].clone(), args[1].clone(), args[2].clone(), args[3].clone());
    let f_t = Term::apply(wrec, args.clone());
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let prod_t = s.prod.of(w_t, tt);
    let c = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let pow_at = inst_all(&s.pow_ax, &[prod_t, f_t.clone()])?;
    let in_pow = Thm::mp(&iff_mpr(&pow_at)?, &inst_all(subset_prod, &args)?)?;

    let body = hyp_and(
        &a1i(&in_pow, c.clone()),
        &hyp_and(&inst_all(sv_thm, &args)?, &inst_all(rec_thm, &args)?)?,
    )?;

    let mut with_f = args.clone();
    with_f.push(f_t);
    let out = syl(&body, &iff_mpr(&inst_all(att_ax, &with_f)?)?)?;
    Some(gen_all(&vars, &out))
}

/// **The empty set is an attempt.** `⊢ ∀A ∀B ∀u ∀T ∀e. ∅ ∈ Att(A,B,u,T,e)`
///
/// Non-vacuity for everything above: `Att` is inhabited, so the union defining
/// `wrec` is a union over a non-empty family, and the attempt condition is not
/// one no set satisfies. All three clauses hold because `∅` has no members —
/// `∅ ⊆ anything`, a graph with no pairs is single-valued, and the recursion
/// condition is guarded by `indom(∅, ·)`, which is refutable.
///
/// It is the *weak* form of non-vacuity, and deliberately labelled as such: it
/// says nothing about `wrec` being non-empty. See the closing notes.
pub fn empty_attempt(
    env: &mut Env,
    wt: &Wtype,
    comp: FnSym,
    att_ax: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt, te) = (
        args[0].clone(),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
        args[4].clone(),
    );
    let e_t = wt.empty();
    let prod_t = s.prod.of(wt.of(ta, tb.clone(), tu), tt);

    // ── `∅ ∈ 𝒫(prod(W,T))` ──────────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let not_in = inst_all(&ap.empty_ax, std::slice::from_ref(&tz))?;
    let sub = Thm::gen(
        zv,
        &syl(&not_in, &crate::ex_falso(Formula::mem(tz, prod_t.clone())))?,
    );
    let pow_at = inst_all(&s.pow_ax, &[prod_t, e_t.clone()])?;
    let in_pow = Thm::mp(&iff_mpr(&pow_at)?, &sub)?;

    // ── `sv(∅)`: a graph with no pairs is single-valued ──────────────────────
    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));
    let p1 = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), e_t.clone());
    let p2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), e_t.clone());
    let eq = Formula::eq(ty.clone(), ty2.clone());
    let refute = inst_all(&ap.empty_ax, &[ap.sets.pair(tx, ty.clone())])?;
    let sv = Thm::gen(
        xv,
        &Thm::gen(
            yv,
            &Thm::gen(
                y2v,
                &syl(&and_left(p1, p2), &syl(&refute, &crate::ex_falso(eq))?)?,
            ),
        ),
    );
    debug_assert_eq!(
        *sv.concl(),
        is_single_valued(env, &ap.sets, &e_t),
        "empty_attempt: sv(∅) has the wrong shape"
    );

    // ── `rec_cond(∅)`: the guard `indom(∅, ⟨a,f⟩)` is refutable ──────────────
    let (pa, pf, y0) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));
    let w = ap.sets.pair(tpa.clone(), tpf.clone());

    let rc = rec_cond(env, ap, comp, &tb, &te, &e_t);
    let opened = {
        let one = Thm::ax_inst(rc.clone(), tpa.clone())?.concl().as_imp()?.1;
        Thm::ax_inst(one, tpf.clone())?.concl().as_imp()?.1
    };
    let (head, conj) = opened.as_imp()?;
    let all_not = Thm::gen(
        y0,
        &inst_all(&ap.empty_ax, &[ap.sets.pair(w, Term::var(y0))])?,
    );
    let refuted = crate::mp_const(&all_not, Formula::false_());
    if *refuted.concl() != Formula::imp(head.clone(), Formula::false_()) {
        return None
    }
    let rec = Thm::gen(
        pa,
        &Thm::gen(pf, &syl(&refuted, &crate::ex_falso(conj))?),
    );
    debug_assert_eq!(*rec.concl(), rc, "empty_attempt: rec_cond(∅) has the wrong shape");

    let mut with_e = args.clone();
    with_e.push(e_t);
    let out = Thm::mp(
        &iff_mpr(&inst_all(att_ax, &with_e)?)?,
        &crate::and_intro(&in_pow, &crate::and_intro(&sv, &rec)),
    )?;
    Some(gen_all(&vars, &out))
}

/// **The ι equation, guarded by membership in the domain.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
///       ∀a ∀f. (indom(wrec(…), ⟨a,f⟩) →
///           app(wrec(…), ⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec(…),f,B(a))⟩⟩)))
/// ```
///
/// This is the *whole* of ι except for the guard, and it is exactly what
/// [`wrec_rec_cond`] proves with the subterm clause dropped. Stating it
/// separately makes the remaining obligation precise: the ι rule is this
/// theorem with `indom(wrec, ⟨a,f⟩)` discharged from `a ∈ A` and
/// `f ∈ fs(B(a), W)`, which is **totality** and nothing else.
pub fn iota_on_domain(env: &mut Env, s: &Sums, rec_thm: &Thm) -> Option<Thm> {
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu) = (args[0].clone(), args[1].clone(), args[2].clone());
    let c = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));

    let at = hyp_inst(&inst_all(rec_thm, &args)?, &[tpa, tpf.clone()])?;
    let (_, imp) = at.concl().as_imp()?;
    let (_, conj) = imp.as_imp()?;
    let (sub, eq) = split_and(&conj)?;
    let dropped = crate::funcs::hyp_syl(&at, &a1i(&and_right(sub, eq), c.clone()))?;

    let (_, bf) = dropped.concl().as_imp()?;
    let all_f = Thm::mp(&Thm::ax_dist(pf, c.clone(), bf)?, &Thm::gen(pf, &dropped))?;
    let (_, ba) = all_f.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(pa, c, ba)?, &Thm::gen(pa, &all_f))?;
    Some(gen_all(&vars, &out))
}
