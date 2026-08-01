//! **Step 4** — the recursor is the union of all attempts.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e. wrec(A,B,u,T,e) = ⋃ Att(A,B,u,T,e)            [wrec_symbol]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀p. (p ∈ wrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))         [wrec_members]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ wrec)   [attempt_subset_wrec]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g. (g ∈ Att →
//!       ∀x. (indom(g,x) → indom(wrec,x)))                  [attempt_indom_wrec]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. wrec ⊆ prod(W,T)                         [wrec_subset_prod]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → sv(wrec))             [wrec_single_valued]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(wrec,x) = app(g,x))))   [wrec_value]
//! ```
//!
//! with [`wrec_of`] building the term. Callers need none of the derivations
//! below.
//!
//! # Why an explicit definition and not a `define` with an `∃!` premise
//!
//! `wrec(A,B,u,T,e) := ⋃ Att(A,B,u,T,e)` is a term, so
//! [`crate::define_abbrev`] introduces it for nothing. The unique-existence
//! statement that `INDUCTIVES.md`'s route 2 wants — "the unique function on `W`
//! satisfying ι" — is then a *theorem* about this symbol rather than the premise
//! of its introduction, which is strictly more informative: a caller that
//! prefers the implicit form can feed the theorem to [`kernel::thm::define`].
//! That theorem is not yet derived; see the closing notes on [`crate::wrec`].
//!
//! # What the union costs
//!
//! Everything here is one move repeated: a pair of `wrec` comes from *some*
//! attempt, and there is no deduction theorem to discharge that witness with,
//! so each result is an application of `hyp_exists_elim`. The
//! interesting one is [`wrec_single_valued`]: two pairs over the same point come
//! from two attempts `g` and `h`, that point lies in `W` because every attempt
//! is included in `prod(W,T)`, and [`super::agree`] then equates `app(g,x)`
//! with `app(h,x)` — which is where step 3 is spent.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::funspace::is_single_valued;
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, inst_all, syl, uncurry,
};

use super::hyp::{as_iff, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim, hyp_inst, hyp_split, split_and};
use super::attempt::{indom, indom_intro};

/// Introduce `wrec(A,B,u,T,e) := ⋃ Att(A,B,u,T,e)`, with
/// `⊢ ∀A ∀B ∀u ∀T ∀e. wrec(A,B,u,T,e) = ⋃ Att(A,B,u,T,e)`.
///
/// An **explicit** definition, so it costs nothing: the `∃!` obligation of
/// [`kernel::thm::define`] is [`crate::exists_unique_eq`]. The unique-existence
/// statement that characterises the recursor is then a *theorem* rather than
/// the definition's premise — see the module header.
pub fn wrec_symbol(env: &mut Env, s: &Sums, att: FnSym) -> Option<(FnSym, Thm)> {
    if att.arity() != 5 {
        return None
    }
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let body = s.ap.sets.union_of(Term::apply(att, args));
    crate::define_abbrev(env, &vars, &body)
}

/// The term `wrec(A,B,u,T,e)`.
pub fn wrec_of(wrec: FnSym, a: Term, b: Term, u: Term, t: Term, e: Term) -> Term {
    Term::apply(wrec, vec![a, b, u, t, e])
}

/// `⊢ ∀A ∀B ∀u ∀T ∀e ∀p. (p ∈ wrec(…) ↔ ∃g. (g ∈ Att(…) ∧ p ∈ g))` — the
/// Union axiom, read across the defining equation.
pub fn wrec_members(
    env: &mut Env,
    s: &Sums,
    att: FnSym,
    wrec: FnSym,
    wrec_def: &Thm,
) -> Option<Thm> {
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let pv = env.fresh_var();
    let tp = Term::var(pv);

    let att_t = Term::apply(att, args.clone());
    let f_t = Term::apply(wrec, args.clone());
    let un_t = s.ap.sets.union_of(att_t.clone());

    let def = inst_all(wrec_def, &args)?;
    if *def.concl() != Formula::eq(f_t.clone(), un_t.clone()) {
        return None
    }
    let un = inst_all(&s.ap.sets.un_ax, &[att_t, tp.clone()])?;

    // Rewrite `⋃Att` back to `wrec(…)` inside the biconditional.
    let hole = env.fresh_var();
    let (_, rhs) = as_iff(un.concl())?;
    let carry = Thm::eq_leibniz(
        un_t,
        f_t.clone(),
        hole,
        Formula::iff(Formula::mem(tp.clone(), Term::var(hole)), rhs),
    );
    let out = Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &def)?)?, &un)?;
    let mut all = Thm::gen(pv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// **The recursor is a function.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → sv(wrec(A,B,u,T,e)))
/// ```
///
/// A pair of `wrec` comes from some attempt, so two pairs over the same point
/// come from two attempts `g` and `h`. That point lies in `W`, because every
/// attempt is included in `prod(W,T)`; [`super::agreement`] then equates `app(g,x)`
/// with `app(h,x)`, and each attempt being single-valued identifies its own
/// `app` with the value it carries.
#[allow(clippy::too_many_arguments)]
pub fn wrec_single_valued(
    env: &mut Env,
    wt: &Wtype,
    att: FnSym,
    att_ax: &Thm,
    wrec: FnSym,
    members: &Thm,
    agree: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt) = (args[0].clone(), args[1].clone(), args[2].clone(), args[3].clone());

    let f_t = Term::apply(wrec, args.clone());
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let prod_t = s.prod.of(w_t.clone(), tt.clone());
    let c = crate::wtype::closed(env, s, &ta, &tb, &tu);

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
    let pair1 = ap.sets.pair(tx.clone(), ty.clone());
    let pair2 = ap.sets.pair(tx.clone(), ty2.clone());

    // ── H := closed ∧ (⟨x,y⟩ ∈ F ∧ ⟨x,y′⟩ ∈ F) ──────────────────────────────
    let p1 = Formula::mem(pair1.clone(), f_t.clone());
    let p2 = Formula::mem(pair2.clone(), f_t.clone());
    let pairs = Formula::and(p1.clone(), p2.clone());
    let h = Formula::and(c.clone(), pairs.clone());
    let h_c = and_left(c.clone(), pairs.clone());
    let h_pairs = and_right(c.clone(), pairs.clone());
    let h_p1 = syl(&h_pairs, &and_left(p1.clone(), p2.clone()))?;
    let h_p2 = syl(&h_pairs, &and_right(p1, p2))?;

    // ── Each pair comes from an attempt ──────────────────────────────────────
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
        Formula::mem(pair2.clone(), th.clone()),
    );

    // ── M := (H ∧ Gg) ∧ Hh ──────────────────────────────────────────────────
    let hg = Formula::and(h.clone(), gg.clone());
    let m = Formula::and(hg.clone(), hh.clone());
    let m_hg = and_left(hg.clone(), hh.clone());
    let m_hh = and_right(hg.clone(), hh.clone());
    let m_h = syl(&m_hg, &and_left(h.clone(), gg.clone()))?;
    let m_gg = syl(&m_hg, &and_right(h.clone(), gg.clone()))?;
    let m_c = syl(&m_h, &h_c)?;
    let (m_gatt, m_gpair) = hyp_split(&m_gg)?;
    let (m_hatt, m_hpair) = hyp_split(&m_hh)?;

    // `g ∈ Att` unfolds to its power-set bound and its single-valuedness.
    let unfold = |k_mem: &Thm, t: &Term| -> Option<(Thm, Thm)> {
        let mut a = args.clone();
        a.push(t.clone());
        let ax = inst_all(att_ax, &a)?;
        let (bound, cond) = hyp_split(&syl(k_mem, &iff_mp(&ax)?)?)?;
        Some((bound, hyp_split(&cond)?.0))
    };
    let (m_gbound, m_svg) = unfold(&m_gatt, &tg)?;
    let (_, m_svh) = unfold(&m_hatt, &th)?;

    // ── x ∈ W, because `g ⊆ prod(W,T)` ───────────────────────────────────────
    let pow_at = inst_all(&s.pow_ax, &[prod_t.clone(), tg.clone()])?;
    let m_sub = syl(&m_gbound, &iff_mp(&pow_at)?)?;
    let m_inprod = hyp_mp(&hyp_inst(&m_sub, std::slice::from_ref(&pair1))?, &m_gpair)?;
    let pip = inst_all(
        &s.pair_in_prod,
        &[w_t.clone(), tt.clone(), tx.clone(), ty.clone()],
    )?;
    let (_, rhs) = as_iff(pip.concl())?;
    let (in_w, in_t) = split_and(&rhs)?;
    let m_xw = syl(&syl(&m_inprod, &iff_mp(&pip)?)?, &and_left(in_w, in_t))?;

    // ── The two attempts agree at `x` ────────────────────────────────────────
    let agr_at = inst_all(agree, &args)?;
    let m_phi = hyp_mp(&hyp_inst(&syl(&m_c, &agr_at)?, std::slice::from_ref(&tx))?, &m_xw)?;
    let m_gh = hyp_inst(&m_phi, &[tg.clone(), th.clone()])?;
    let intro_g = indom_intro(env, ap, &tg, &tx, &ty)?;
    let intro_h = indom_intro(env, ap, &th, &tx, &ty2)?;
    let m_ind = hyp_and(&syl(&m_gpair, &intro_g)?, &syl(&m_hpair, &intro_h)?)?;
    let m_eq = hyp_mp(&hyp_mp(&m_gh, &hyp_and(&m_gatt, &m_hatt)?)?, &m_ind)?;

    // ── … and each is its own value there ────────────────────────────────────
    let value = |sv: &Thm, pair: &Thm, t: &Term, pt: &Term, val: &Term| -> Option<Thm> {
        let ap_at = inst_all(&wt.app_pair, &[t.clone(), pt.clone(), val.clone()])?;
        hyp_mp(&a1i(&ap_at, m.clone()), &hyp_and(sv, pair)?)
    };
    let m_gy = value(&m_svg, &m_gpair, &tg, &tx, &ty)?;
    let m_hy2 = value(&m_svh, &m_hpair, &th, &tx, &ty2)?;

    let sym = hyp_eq_symm(env, &m_gy)?;
    let step = hyp_eq_trans(env, &sym, &m_eq)?;
    let m_goal = hyp_eq_trans(env, &step, &m_hy2)?;
    debug_assert_eq!(
        *m_goal.concl(),
        Formula::imp(m.clone(), Formula::eq(ty.clone(), ty2.clone())),
        "wrec_single_valued: the two values were not identified"
    );

    // ── Discharge the two witnesses ─────────────────────────────────────────
    let hg_exh = syl(&and_left(h.clone(), gg.clone()), &h_exh)?;
    let inner = hyp_exists_elim(hv, &m_goal, &hg_exh)?;
    let h_goal = hyp_exists_elim(gv, &inner, &h_exg)?;
    debug_assert_eq!(
        *h_goal.concl(),
        Formula::imp(h.clone(), Formula::eq(ty.clone(), ty2.clone())),
        "wrec_single_valued: the witnesses were not discharged"
    );

    // ── Generalise into `sv(F)` ─────────────────────────────────────────────
    let body = uncurry(&h_goal)?; // closed → ((⟨x,y⟩∈F ∧ ⟨x,y′⟩∈F) → y = y′)
    let (_, b0) = body.concl().as_imp()?;
    let l2 = Thm::mp(&Thm::ax_dist(y2v, c.clone(), b0)?, &Thm::gen(y2v, &body))?;
    let (_, b1) = l2.concl().as_imp()?;
    let l1 = Thm::mp(&Thm::ax_dist(yv, c.clone(), b1)?, &Thm::gen(yv, &l2))?;
    let (_, b2) = l1.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(xv, c.clone(), b2)?, &Thm::gen(xv, &l1))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(c, is_single_valued(env, &ap.sets, &f_t)),
        "wrec_single_valued: unexpected shape"
    );
    Some(gen_all(&vars, &out))
}

/// `⊢ ∀A ∀B ∀u ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ wrec(…))` — every attempt
/// is included in the recursor. One existential introduction.
pub fn attempt_subset_wrec(
    env: &mut Env,
    att: FnSym,
    members: &Thm,
) -> Option<Thm> {
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (gv, pv) = (env.fresh_var(), env.fresh_var());
    let (tg, tp) = (Term::var(gv), Term::var(pv));

    let att_t = Term::apply(att, args.clone());
    let body = Formula::and(
        Formula::mem(tg.clone(), att_t.clone()),
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

/// `⊢ ∀A ∀B ∀u ∀T ∀e. wrec(…) ⊆ prod(W(A,B,u), T)` — the recursor is a set of
/// pairs over `W`, with values in `T`.
///
/// No bound hypothesis: this is inherited from the attempts one at a time.
pub fn wrec_subset_prod(
    env: &mut Env,
    wt: &Wtype,
    att: FnSym,
    att_ax: &Thm,
    wrec: FnSym,
    members: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt) = (args[0].clone(), args[1].clone(), args[2].clone(), args[3].clone());
    let w_t = wt.of(ta, tb, tu);
    let prod_t = s.prod.of(w_t, tt);
    let f_t = Term::apply(wrec, args.clone());

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
    let pow_at = inst_all(&s.pow_ax, &[prod_t, tg])?;
    let k_sub = syl(&k_bound, &iff_mp(&pow_at)?)?;
    let k_goal = hyp_mp(
        &hyp_inst(&k_sub, std::slice::from_ref(&tp))?,
        &and_right(k_att, k_pg),
    )?;
    debug_assert_eq!(*k_goal.concl(), Formula::imp(k, mem_prod.clone()));

    let elim = crate::exists_elim_imp(gv, &Thm::gen(gv, &k_goal), &mem_prod)?;
    let mut b = args.clone();
    b.push(tp.clone());
    let out = syl(&iff_mp(&inst_all(members, &b)?)?, &elim)?;
    debug_assert_eq!(*out.concl(), Formula::imp(Formula::mem(tp, f_t), mem_prod));

    let mut all = Thm::gen(pv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}

/// **The recursor takes each attempt's value.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
///       ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(wrec(…),x) = app(g,x))))
/// ```
///
/// The bridge every remaining step crosses: it is what lets a fact proved about
/// *some* attempt be read as a fact about the union. `indom(g,x)` produces a
/// pair `⟨x,y⟩ ∈ g`; single-valuedness of `g` makes `y` its value there, the
/// pair is in `wrec` too, and single-valuedness of `wrec` — which is
/// [`wrec_single_valued`], hence the bound hypothesis — makes `y` its value as
/// well.
#[allow(clippy::too_many_arguments)]
pub fn wrec_value(
    env: &mut Env,
    wt: &Wtype,
    att: FnSym,
    att_ax: &Thm,
    wrec: FnSym,
    subset: &Thm,
    sv_thm: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu) = (args[0].clone(), args[1].clone(), args[2].clone());
    let f_t = Term::apply(wrec, args.clone());
    let c = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let (gv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tx, ty) = (Term::var(gv), Term::var(xv), Term::var(yv));

    let g_att = Formula::mem(tg.clone(), Term::apply(att, args.clone()));
    let in_dom = indom(env, ap, &tg, &tx);
    let h0 = Formula::and(c.clone(), g_att.clone());
    let h = Formula::and(h0.clone(), in_dom.clone());

    let h_h0 = and_left(h0.clone(), in_dom.clone());
    let h_c = syl(&h_h0, &and_left(c.clone(), g_att.clone()))?;
    let h_att = syl(&h_h0, &and_right(c.clone(), g_att.clone()))?;
    let h_ex = and_right(h0.clone(), in_dom.clone());

    // ── N := H ∧ ⟨x,y⟩ ∈ g ──────────────────────────────────────────────────
    let pair = ap.sets.pair(tx.clone(), ty.clone());
    let mem_pg = Formula::mem(pair.clone(), tg.clone());
    let n = Formula::and(h.clone(), mem_pg.clone());
    let n_h = and_left(h.clone(), mem_pg.clone());
    let n_pg = and_right(h.clone(), mem_pg.clone());
    let n_c = syl(&n_h, &h_c)?;
    let n_att = syl(&n_h, &h_att)?;

    let mut a = args.clone();
    a.push(tg.clone());
    let ax = inst_all(att_ax, &a)?;
    let (_, cond) = hyp_split(&syl(&n_att, &iff_mp(&ax)?)?)?;
    let n_svg = hyp_split(&cond)?.0;

    // `app(g,x) = y`.
    let ap_g = inst_all(&wt.app_pair, &[tg.clone(), tx.clone(), ty.clone()])?;
    let n_gy = hyp_mp(&a1i(&ap_g, n.clone()), &hyp_and(&n_svg, &n_pg)?)?;

    // `⟨x,y⟩ ∈ wrec(…)`, and `wrec(…)` is single-valued, so `app(F,x) = y`.
    let mut b = args.clone();
    b.push(tg.clone());
    b.push(pair.clone());
    let sub_at = inst_all(subset, &b)?;
    let n_pf = hyp_mp(&a1i(&sub_at, n.clone()), &hyp_and(&n_att, &n_pg)?)?;
    let n_svf = syl(&n_c, &inst_all(sv_thm, &args)?)?;
    let ap_f = inst_all(&wt.app_pair, &[f_t.clone(), tx.clone(), ty.clone()])?;
    let n_fy = hyp_mp(&a1i(&ap_f, n.clone()), &hyp_and(&n_svf, &n_pf)?)?;

    let n_gy_sym = hyp_eq_symm(env, &n_gy)?;
    let n_goal = hyp_eq_trans(env, &n_fy, &n_gy_sym)?;
    debug_assert_eq!(
        *n_goal.concl(),
        Formula::imp(
            n,
            Formula::eq(ap.apply(f_t.clone(), tx.clone()), ap.apply(tg.clone(), tx.clone()))
        ),
        "wrec_value: the two values were not identified"
    );

    let h_goal = hyp_exists_elim(yv, &n_goal, &h_ex)?;

    // ── Generalise ──────────────────────────────────────────────────────────
    let per_x = uncurry(&h_goal)?; // (closed ∧ g ∈ Att) → (indom(g,x) → …)
    let (_, bx) = per_x.concl().as_imp()?;
    let all_x = Thm::mp(&Thm::ax_dist(xv, h0.clone(), bx)?, &Thm::gen(xv, &per_x))?;
    let per_g = uncurry(&all_x)?; // closed → (g ∈ Att → ∀x. …)
    let (_, bg) = per_g.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(gv, c, bg)?, &Thm::gen(gv, &per_g))?;
    Some(gen_all(&vars, &out))
}

/// From `⊢ H → ∀v. (φ → ψ)` infer `⊢ H → (∃v. φ → ∃v. ψ)` — existential
/// monotonicity under a hypothesis.
///
/// `∃v. φ` is `¬∀v. ¬φ`, so this is the contrapositive of
/// `∀v. ¬ψ → ∀v. ¬φ`, which is proved pointwise under the extra hypothesis
/// `∀v. ¬ψ` and then generalised.
fn hyp_exists_mono(v: kernel::FreeVar, h_all: &Thm) -> Option<Thm> {
    let (h, all) = h_all.concl().as_imp()?;
    let tv = Term::var(v);
    let (_, body) = Thm::ax_inst(all.clone(), tv.clone())?.concl().as_imp()?;
    let (phi, psi) = body.as_imp()?;

    let all_not_psi = Formula::forall(v, Formula::not(psi));
    let all_not_phi = Formula::forall(v, Formula::not(phi.clone()));
    let j = Formula::and(h.clone(), all_not_psi.clone());

    let j_h = and_left(h.clone(), all_not_psi.clone());
    let j_all = and_right(h, all_not_psi.clone());
    let j_imp = syl(&syl(&j_h, h_all)?, &Thm::ax_inst(all, tv.clone())?)?;
    let j_npsi = syl(&j_all, &Thm::ax_inst(all_not_psi.clone(), tv)?)?;
    let j_nphi = crate::funcs::hyp_syl(&j_imp, &j_npsi)?;

    let j_gen = Thm::mp(&Thm::ax_dist(v, j, Formula::not(phi))?, &Thm::gen(v, &j_nphi))?;
    syl(&uncurry(&j_gen)?, &crate::contrapos_imp(all_not_psi, all_not_phi))
}

/// `⊢ ∀A ∀B ∀u ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(wrec(…),x)))` —
/// the domain of the recursor contains every attempt's domain.
pub fn attempt_indom_wrec(
    env: &mut Env,
    ap: &Apply,
    att: FnSym,
    wrec: FnSym,
    subset: &Thm,
) -> Option<Thm> {
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let f_t = Term::apply(wrec, args.clone());

    let (gv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tx, ty) = (Term::var(gv), Term::var(xv), Term::var(yv));
    let k = Formula::mem(tg.clone(), Term::apply(att, args.clone()));

    let pair = ap.sets.pair(tx.clone(), ty.clone());
    let mut a = args.clone();
    a.push(tg.clone());
    a.push(pair);
    let per_y = uncurry(&inst_all(subset, &a)?)?; // g ∈ Att → (⟨x,y⟩ ∈ g → ⟨x,y⟩ ∈ F)
    let (_, by) = per_y.concl().as_imp()?;
    let all_y = Thm::mp(&Thm::ax_dist(yv, k.clone(), by)?, &Thm::gen(yv, &per_y))?;
    let mono = hyp_exists_mono(yv, &all_y)?;
    debug_assert_eq!(
        *mono.concl(),
        Formula::imp(
            k.clone(),
            Formula::imp(indom(env, ap, &tg, &tx), indom(env, ap, &f_t, &tx))
        ),
        "attempt_indom_wrec: unexpected shape"
    );

    let (_, bx) = mono.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(xv, k, bx)?, &Thm::gen(xv, &mono))?;
    let mut all = Thm::gen(gv, &out);
    for v in vars.iter().rev() {
        all = Thm::gen(*v, &all);
    }
    Some(all)
}
