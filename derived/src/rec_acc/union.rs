//! **The recursor is the union of all attempts.**
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀T ∀e. accrec(A,R,T,e) = ⋃ Att(A,R,T,e)                [rec_symbol]
//! ⊢ ∀A ∀R ∀T ∀e ∀p. (p ∈ accrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))         [rec_members]
//! ⊢ ∀A ∀R ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ accrec)  [attempt_subset_rec]
//! ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att →
//!       ∀x. (indom(g,x) → indom(accrec,x)))               [attempt_indom_rec]
//! ⊢ ∀A ∀R ∀T ∀e. accrec ⊆ prod(acc(A,R),T)                 [rec_subset_prod]
//! ⊢ ∀A ∀R ∀T ∀e. sv(accrec)                              [rec_single_valued]
//! ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att →
//!       ∀x. (indom(g,x) → app(accrec,x) = app(g,x)))               [rec_value]
//! ```
//!
//! with [`rec_of`] building the term. Callers need none of the derivations
//! below.
//!
//! # Every one of these is unconditional
//!
//! The corresponding [`crate::wrec`] theorems — `wrec_single_valued`,
//! `wrec_value` — carry `closed(A,B,u)`, because they rest on `wrec`'s
//! agreement, which rests on `w_rect`, which carries it. [`super::agreement`]
//! rests on [`crate::acc::acc_rect`], which has no such antecedent, so the whole
//! layer here is antecedent-free. What is *not* free is totality; see
//! [`super::total`].
//!
//! # Why an explicit definition and not a `define` with an `∃!` premise
//!
//! `accrec(A,R,T,e) := ⋃ Att(A,R,T,e)` is a term, so [`crate::define_abbrev`]
//! introduces it for nothing. The unique-existence statement — "the unique
//! function on `acc(A,R)` satisfying ι" — is then a *theorem* about this symbol
//! rather than the premise of its introduction, which is strictly more
//! informative. It is the same choice [`crate::wrec`] makes, and like there it
//! is not yet derived.
//!
//! # What the union costs
//!
//! One move repeated: a pair of `accrec` comes from *some* attempt, and there is
//! no deduction theorem to discharge that witness with, so each result is an
//! application of `hyp_exists_elim`. The interesting one is
//! [`rec_single_valued`]: two pairs over the same point come from two attempts,
//! that point lies in `acc(A,R)` because every attempt is inside
//! `prod(acc(A,R),T)`, and [`super::agreement`] equates the two values — which
//! is where the induction is spent.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funspace::is_single_valued;
use crate::wrec::{hyp_eq_symm, hyp_eq_trans, hyp_exists_elim};
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};

use super::attempt::indom_intro;
use super::base::Base;
use super::shared::{as_iff, hyp_exists_mono, hyp_inst, hyp_split, split_and};

/// Introduce `accrec(A,R,T,e) := ⋃ Att(A,R,T,e)`, with
/// `⊢ ∀A ∀R ∀T ∀e. accrec(A,R,T,e) = ⋃ Att(A,R,T,e)`.
///
/// An **explicit** definition, so it costs nothing: the `∃!` obligation of
/// [`kernel::thm::define`] is [`crate::exists_unique_eq`].
pub fn rec_symbol(env: &mut Env, b: &Base, att: FnSym) -> Option<(FnSym, Thm)> {
    if att.arity() != 4 {
        return None
    }
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let body = b.s.ap.sets.union_of(Term::apply(att, args));
    crate::define_abbrev(env, &vars, &body)
}

/// The term `accrec(A,R,T,e)`.
pub fn rec_of(rec: FnSym, a: Term, r: Term, t: Term, e: Term) -> Term {
    Term::apply(rec, vec![a, r, t, e])
}

/// `⊢ ∀A ∀R ∀T ∀e ∀p. (p ∈ accrec(…) ↔ ∃g. (g ∈ Att(…) ∧ p ∈ g))` — the Union
/// axiom, read across the defining equation.
pub fn rec_members(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    rec: FnSym,
    rec_def: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let pv = env.fresh_var();
    let tp = Term::var(pv);

    let att_t = Term::apply(att, args.clone());
    let f_t = Term::apply(rec, args.clone());
    let un_t = b.s.ap.sets.union_of(att_t.clone());

    let def = inst_all(rec_def, &args)?;
    if *def.concl() != Formula::eq(f_t.clone(), un_t.clone()) {
        return None
    }
    let un = inst_all(&b.s.ap.sets.un_ax, &[att_t, tp.clone()])?;

    let hole = env.fresh_var();
    let (_, rhs) = as_iff(un.concl())?;
    let carry = Thm::eq_leibniz(
        un_t,
        f_t,
        hole,
        Formula::iff(Formula::mem(tp, Term::var(hole)), rhs),
    );
    let out = Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &def)?)?, &un)?;
    let mut all = Thm::gen(pv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// `⊢ ∀A ∀R ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ accrec(…))` — every attempt is
/// included in the recursor. One existential introduction.
pub fn attempt_subset_rec(env: &mut Env, att: FnSym, members: &Thm) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (gv, pv) = (env.fresh_var(), env.fresh_var());
    let (tg, tp) = (Term::var(gv), Term::var(pv));

    let att_t = Term::apply(att, args.clone());
    let body = Formula::and(
        Formula::mem(tg.clone(), att_t),
        Formula::mem(tp.clone(), tg.clone()),
    );
    let intro = exists_intro_imp(gv, body, tg)?;

    let mut a = args.clone();
    a.push(tp);
    let at = inst_all(members, &a)?;
    let out = syl(&intro, &iff_mpr(&at)?)?;

    let mut all = Thm::gen(gv, &Thm::gen(pv, &out));
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// `⊢ ∀A ∀R ∀T ∀e. accrec(…) ⊆ prod(acc(A,R), T)` — the recursor is a set of
/// pairs over `acc(A,R)`, with values in `T`.
///
/// Inherited from the attempts one member at a time.
pub fn rec_subset_prod(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    att_ax: &Thm,
    rec: FnSym,
    members: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt) = (args[0].clone(), args[1].clone(), args[2].clone());
    let prod_t = b.s.prod.of(b.acc_of(&ta, &tr), tt);
    let f_t = Term::apply(rec, args.clone());

    let (gv, pv) = (env.fresh_var(), env.fresh_var());
    let (tg, tp) = (Term::var(gv), Term::var(pv));
    let mem_prod = Formula::mem(tp.clone(), prod_t.clone());

    let k_att = Formula::mem(tg.clone(), Term::apply(att, args.clone()));
    let k_pg = Formula::mem(tp.clone(), tg.clone());
    let k = Formula::and(k_att.clone(), k_pg.clone());

    let mut a = args.clone();
    a.push(tg.clone());
    let ax = inst_all(att_ax, &a)?;
    let k_bound = hyp_split(&syl(&and_left(k_att.clone(), k_pg.clone()), &iff_mp(&ax)?)?)?.0;
    let pow_at = inst_all(&b.s.pow_ax, &[prod_t, tg])?;
    let k_sub = syl(&k_bound, &iff_mp(&pow_at)?)?;
    let k_goal = hyp_mp(
        &hyp_inst(&k_sub, std::slice::from_ref(&tp))?,
        &and_right(k_att, k_pg),
    )?;
    if *k_goal.concl() != Formula::imp(k, mem_prod.clone()) {
        return None
    }

    let elim = crate::exists_elim_imp(gv, &Thm::gen(gv, &k_goal), &mem_prod)?;
    let mut c = args.clone();
    c.push(tp.clone());
    let out = syl(&iff_mp(&inst_all(members, &c)?)?, &elim)?;
    if *out.concl() != Formula::imp(Formula::mem(tp, f_t), mem_prod) {
        return None
    }

    let mut all = Thm::gen(pv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// **The recursor is a function.** `⊢ ∀A ∀R ∀T ∀e. sv(accrec(A,R,T,e))`.
///
/// A pair of `accrec` comes from some attempt, so two pairs over the same point
/// come from two attempts `g` and `h`. That point lies in `acc(A,R)`, because
/// every attempt is included in `prod(acc(A,R),T)`; [`super::agreement`] then
/// equates `app(g,x)` with `app(h,x)`, and each attempt being single-valued
/// identifies its own `app` with the value it carries.
///
/// **Unconditional**, unlike [`crate::wrec::wrec_single_valued`].
#[allow(clippy::too_many_arguments)]
pub fn rec_single_valued(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    att_ax: &Thm,
    rec: FnSym,
    members: &Thm,
    agree: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt) = (args[0].clone(), args[1].clone(), args[2].clone());

    let f_t = Term::apply(rec, args.clone());
    let acc_t = b.acc_of(&ta, &tr);
    let prod_t = b.s.prod.of(acc_t.clone(), tt.clone());

    let (xv, yv, y2v, gv, hv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tx, ty, ty2, tg, th) = (
        Term::var(xv),
        Term::var(yv),
        Term::var(y2v),
        Term::var(gv),
        Term::var(hv),
    );
    let pair1 = b.s.ap.sets.pair(tx.clone(), ty.clone());
    let pair2 = b.s.ap.sets.pair(tx.clone(), ty2.clone());

    // ── H := ⟨x,y⟩ ∈ F ∧ ⟨x,y′⟩ ∈ F ─────────────────────────────────────────
    let p1 = Formula::mem(pair1.clone(), f_t.clone());
    let p2 = Formula::mem(pair2.clone(), f_t.clone());
    let h = Formula::and(p1.clone(), p2.clone());
    let h_p1 = and_left(p1.clone(), p2.clone());
    let h_p2 = and_right(p1, p2);

    let mem_of = |p: &Term| -> Option<Thm> {
        let mut a = args.clone();
        a.push(p.clone());
        inst_all(members, &a)
    };
    let h_exg = syl(&h_p1, &iff_mp(&mem_of(&pair1)?)?)?;
    let h_exh = syl(&h_p2, &iff_mp(&mem_of(&pair2)?)?)?;

    let gg = Formula::and(
        Formula::mem(tg.clone(), Term::apply(att, args.clone())),
        Formula::mem(pair1.clone(), tg.clone()),
    );
    let hh = Formula::and(
        Formula::mem(th.clone(), Term::apply(att, args.clone())),
        Formula::mem(pair2, th.clone()),
    );

    // ── M := (H ∧ Gg) ∧ Hh ──────────────────────────────────────────────────
    let hg = Formula::and(h.clone(), gg.clone());
    let m = Formula::and(hg.clone(), hh.clone());
    let m_hg = and_left(hg.clone(), hh.clone());
    let m_hh = and_right(hg, hh);
    let m_gg = syl(&m_hg, &and_right(h.clone(), gg.clone()))?;
    let (m_gatt, m_gpair) = hyp_split(&m_gg)?;
    let (m_hatt, m_hpair) = hyp_split(&m_hh)?;

    let unfold = |k_mem: &Thm, t: &Term| -> Option<(Thm, Thm)> {
        let mut a = args.clone();
        a.push(t.clone());
        let ax = inst_all(att_ax, &a)?;
        let (bound, cond) = hyp_split(&syl(k_mem, &iff_mp(&ax)?)?)?;
        Some((bound, hyp_split(&cond)?.0))
    };
    let (m_gbound, m_svg) = unfold(&m_gatt, &tg)?;
    let (_, m_svh) = unfold(&m_hatt, &th)?;

    // ── x ∈ acc(A,R), because `g ⊆ prod(acc,T)` ─────────────────────────────
    let pow_at = inst_all(&b.s.pow_ax, &[prod_t, tg.clone()])?;
    let m_sub = syl(&m_gbound, &iff_mp(&pow_at)?)?;
    let m_inprod = hyp_mp(&hyp_inst(&m_sub, std::slice::from_ref(&pair1))?, &m_gpair)?;
    let pip = inst_all(
        &b.s.pair_in_prod,
        &[acc_t.clone(), tt.clone(), tx.clone(), ty.clone()],
    )?;
    let (_, rhs) = as_iff(pip.concl())?;
    let (in_acc, in_t) = split_and(&rhs)?;
    let m_xacc = syl(&syl(&m_inprod, &iff_mp(&pip)?)?, &and_left(in_acc, in_t))?;

    // ── The two attempts agree at `x` ───────────────────────────────────────
    let agr_at = inst_all(agree, &args)?;
    let agr_x = Thm::mp(&Thm::ax_inst(agr_at.concl().clone(), tx.clone())?, &agr_at)?;
    let m_phi = hyp_mp(&a1i(&agr_x, m.clone()), &m_xacc)?;
    let m_gh = hyp_inst(&m_phi, &[tg.clone(), th.clone()])?;
    let intro_g = indom_intro(env, b, &tg, &tx, &ty)?;
    let intro_h = indom_intro(env, b, &th, &tx, &ty2)?;
    let m_ind = hyp_and(&syl(&m_gpair, &intro_g)?, &syl(&m_hpair, &intro_h)?)?;
    let m_eq = hyp_mp(&hyp_mp(&m_gh, &hyp_and(&m_gatt, &m_hatt)?)?, &m_ind)?;

    // ── … and each is its own value there ───────────────────────────────────
    let value = |sv: &Thm, pair: &Thm, t: &Term, pt: &Term, val: &Term| -> Option<Thm> {
        let ap_at = inst_all(&b.app_of_graph, &[t.clone(), pt.clone(), val.clone()])?;
        hyp_mp(&a1i(&ap_at, m.clone()), &hyp_and(sv, pair)?)
    };
    let m_gy = value(&m_svg, &m_gpair, &tg, &tx, &ty)?;
    let m_hy2 = value(&m_svh, &m_hpair, &th, &tx, &ty2)?;

    let sym = hyp_eq_symm(env, &m_gy)?;
    let step = hyp_eq_trans(env, &sym, &m_eq)?;
    let m_goal = hyp_eq_trans(env, &step, &m_hy2)?;
    if *m_goal.concl() != Formula::imp(m, Formula::eq(ty.clone(), ty2.clone())) {
        return None
    }

    // ── Discharge the two witnesses ─────────────────────────────────────────
    let hg_exh = syl(&and_left(h.clone(), gg), &h_exh)?;
    let inner = hyp_exists_elim(hv, &m_goal, &hg_exh)?;
    let h_goal = hyp_exists_elim(gv, &inner, &h_exg)?;
    if *h_goal.concl() != Formula::imp(h, Formula::eq(ty.clone(), ty2.clone())) {
        return None
    }

    let out = gen_all(&[xv, yv, y2v], &h_goal);
    if *out.concl() != is_single_valued(env, &b.s.ap.sets, &f_t) {
        return None
    }
    Some(gen_all(&vars, &out))
}

/// **The recursor takes each attempt's value.**
///
/// ```text
/// ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(accrec,x) = app(g,x)))
/// ```
///
/// The bridge every remaining step crosses: it lets a fact proved about *some*
/// attempt be read as a fact about the union. `indom(g,x)` produces a pair
/// `⟨x,y⟩ ∈ g`; single-valuedness of `g` makes `y` its value there, the pair is
/// in `accrec` too, and [`rec_single_valued`] makes `y` its value as well.
#[allow(clippy::too_many_arguments)]
pub fn rec_value(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    att_ax: &Thm,
    rec: FnSym,
    subset: &Thm,
    sv_thm: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let f_t = Term::apply(rec, args.clone());

    let (gv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tx, ty) = (Term::var(gv), Term::var(xv), Term::var(yv));

    let g_att = Formula::mem(tg.clone(), Term::apply(att, args.clone()));
    let in_dom = b.indom(env, &tg, &tx);
    let h = Formula::and(g_att.clone(), in_dom.clone());
    let h_att = and_left(g_att.clone(), in_dom.clone());
    let h_ex = and_right(g_att, in_dom.clone());

    // ── N := H ∧ ⟨x,y⟩ ∈ g ──────────────────────────────────────────────────
    let pair = b.s.ap.sets.pair(tx.clone(), ty.clone());
    let mem_pg = Formula::mem(pair.clone(), tg.clone());
    let n = Formula::and(h.clone(), mem_pg.clone());
    let n_h = and_left(h.clone(), mem_pg.clone());
    let n_pg = and_right(h.clone(), mem_pg);
    let n_att = syl(&n_h, &h_att)?;

    let mut a = args.clone();
    a.push(tg.clone());
    let ax = inst_all(att_ax, &a)?;
    let (_, cond) = hyp_split(&syl(&n_att, &iff_mp(&ax)?)?)?;
    let n_svg = hyp_split(&cond)?.0;

    // `app(g,x) = y`.
    let ap_g = inst_all(&b.app_of_graph, &[tg.clone(), tx.clone(), ty.clone()])?;
    let n_gy = hyp_mp(&a1i(&ap_g, n.clone()), &hyp_and(&n_svg, &n_pg)?)?;

    // `⟨x,y⟩ ∈ accrec`, which is single-valued, so `app(accrec,x) = y`.
    let mut c = args.clone();
    c.push(tg.clone());
    c.push(pair);
    let sub_at = inst_all(subset, &c)?;
    let n_pf = hyp_mp(&a1i(&sub_at, n.clone()), &hyp_and(&n_att, &n_pg)?)?;
    let n_svf = a1i(&inst_all(sv_thm, &args)?, n.clone());
    let ap_f = inst_all(&b.app_of_graph, &[f_t.clone(), tx.clone(), ty.clone()])?;
    let n_fy = hyp_mp(&a1i(&ap_f, n.clone()), &hyp_and(&n_svf, &n_pf)?)?;

    let n_gy_sym = hyp_eq_symm(env, &n_gy)?;
    let n_goal = hyp_eq_trans(env, &n_fy, &n_gy_sym)?;
    if *n_goal.concl()
        != Formula::imp(n, Formula::eq(b.app(&f_t, &tx), b.app(&tg, &tx)))
    {
        return None
    }

    let h_goal = hyp_exists_elim(yv, &n_goal, &h_ex)?;
    let per_x = uncurry(&h_goal)?; // g ∈ Att → (indom(g,x) → …)
    let (_, bx) = per_x.concl().as_imp()?;
    let g_att2 = Formula::mem(tg.clone(), Term::apply(att, args.clone()));
    let out = Thm::mp(&Thm::ax_dist(xv, g_att2, bx)?, &Thm::gen(xv, &per_x))?;
    let mut all = Thm::gen(gv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(accrec,x)))` — the
/// domain of the recursor contains every attempt's domain.
pub fn attempt_indom_rec(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    rec: FnSym,
    subset: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let f_t = Term::apply(rec, args.clone());

    let (gv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tx, ty) = (Term::var(gv), Term::var(xv), Term::var(yv));
    let k = Formula::mem(tg.clone(), Term::apply(att, args.clone()));

    let pair = b.s.ap.sets.pair(tx.clone(), ty.clone());
    let mut a = args.clone();
    a.push(tg.clone());
    a.push(pair);
    let per_y = uncurry(&inst_all(subset, &a)?)?;
    let (_, by) = per_y.concl().as_imp()?;
    let all_y = Thm::mp(&Thm::ax_dist(yv, k.clone(), by)?, &Thm::gen(yv, &per_y))?;
    let mono = hyp_exists_mono(yv, &all_y)?;
    if *mono.concl()
        != Formula::imp(
            k.clone(),
            Formula::imp(b.indom(env, &tg, &tx), b.indom(env, &f_t, &tx)),
        )
    {
        return None
    }

    let (_, bx) = mono.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(xv, k, bx)?, &Thm::gen(xv, &mono))?;
    let mut all = Thm::gen(gv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}
