//! **The recursor is itself an attempt**, and the ι rule on its domain.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀T ∀e. rec_cond(A,R,e,accrec(A,R,T,e))                [rec_rec_cond]
//! ⊢ ∀A ∀R ∀T ∀e. accrec(A,R,T,e) ∈ Att(A,R,T,e)               [rec_is_attempt]
//! ⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) →
//!       app(accrec,x) = app(app(app(e,x),•), ih(accrec,A,R,x)))  [iota_on_domain]
//! ```
//!
//! All three **unconditional**. Callers need none of the derivations below.
//!
//! # The argument
//!
//! Every point of `accrec`'s domain is a point of *some* attempt `g`'s domain.
//! There:
//!
//! * `g`'s own `rec_cond` puts every `R`-predecessor of `x` in `g`'s domain, and
//!   [`super::union::attempt_indom_rec`] pushes that up to `accrec`'s;
//! * `g` and `accrec` agree wherever `g` is defined
//!   ([`super::union::rec_value`]), so in particular on the predecessors of `x`,
//!   so [`super::ih::ih_ext`] equates the two induction hypotheses, and one
//!   congruence carries `g`'s recursion equation onto `accrec`.
//!
//! That is the whole of ι **on the domain**. Turning it into the unguarded rule
//! is [`super::total`], and that is where the one surviving hypothesis —
//! `step_typed` — is spent.
//!
//! # Why this file proves nothing on its own
//!
//! Everything here would still hold if `accrec` were `∅`: `indom(∅,x)` is never
//! satisfied, so [`iota_on_domain`] would be vacuous and [`rec_is_attempt`]
//! would be [`super::attempt::empty_attempt`]. The content is supplied by
//! [`super::total`] (which makes the domain all of `acc(A,R)`) and by
//! [`super::witness`] (which fires ι closed, at a concrete instance, with both
//! sides computed). This is the same division of labour, and the same hazard,
//! that [`crate::wrec`] records.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim};
use crate::{
    and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl,
    uncurry,
};

use super::attempt::{att_of, attempt_bound, indom_intro, preds_indom, rec_cond};
use super::base::Base;
use super::ih::preds_agree;
use super::shared::{hyp_inst, hyp_split};

/// The three symbols the recursor development is stated over, in one view.
///
/// Grouped rather than passed loose because building `Att` from one development
/// and `accrec` from another yields two recursors whose theorems cannot be
/// chained — the hazard `RECURSOR-DESIGN.md` §7.4 records three times over. A
/// caller that holds a `Syms` holds a matched set.
#[derive(Clone, Copy)]
pub struct Syms<'a> {
    /// The symbol `Att(A,R,T,e)`.
    pub att: FnSym,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att ↔ …)`.
    pub att_ax: &'a Thm,
    /// The symbol `accrec(A,R,T,e)`.
    pub rec: FnSym,
}

/// The bundle of union-layer theorems this file consumes.
///
/// Passed as a struct because all five travel together and getting two of them
/// from different developments would silently prove things about two recursors.
pub struct UnionFacts<'a> {
    /// `⊢ ∀A ∀R ∀T ∀e. accrec ⊆ prod(acc(A,R),T)`.
    pub subset_prod: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. sv(accrec)`.
    pub single_valued: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(accrec,x) = app(g,x)))`.
    pub value: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(accrec,x)))`.
    pub indom: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀p. (p ∈ accrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))`.
    pub members: &'a Thm,
}

/// `⊢ ∀A ∀R ∀T ∀e. rec_cond(A,R,e,accrec(A,R,T,e))` — **the union satisfies the
/// recursion condition**.
///
/// See the module header for the argument.
pub fn rec_rec_cond(
    env: &mut Env,
    b: &Base,
    att: FnSym,
    att_ax: &Thm,
    rec: FnSym,
    u: &UnionFacts,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, te) = (args[0].clone(), args[1].clone(), args[3].clone());
    let f_t = Term::apply(rec, args.clone());
    let att_t = Term::apply(att, args.clone());

    let (xv, wv, gv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tx, tw, tg, ty) = (
        Term::var(xv),
        Term::var(wv),
        Term::var(gv),
        Term::var(yv),
    );

    // `H := indom(accrec,x)`, spelled with our own witness variable so the two
    // existential eliminations below can discharge it.
    let pair_xw = b.s.ap.sets.pair(tx.clone(), tw.clone());
    let h = Formula::exists(wv, Formula::mem(pair_xw.clone(), f_t.clone()));
    if h != b.indom(env, &f_t, &tx) {
        return None
    }

    let mem_rec = Formula::mem(pair_xw.clone(), f_t.clone());
    let n1 = Formula::and(h.clone(), mem_rec.clone());
    let g_att = Formula::mem(tg.clone(), att_t.clone());
    let mem_g = Formula::mem(pair_xw, tg.clone());
    let from_g = Formula::and(g_att.clone(), mem_g.clone());
    let n = Formula::and(n1.clone(), from_g.clone());

    let n_from = and_right(n1.clone(), from_g.clone());
    let n_att = syl(&n_from, &and_left(g_att.clone(), mem_g.clone()))?;
    let n_memg = syl(&n_from, &and_right(g_att.clone(), mem_g))?;
    let n_indg = syl(&n_memg, &indom_intro(env, b, &tg, &tx, &tw)?)?;

    // `g`'s own recursion condition, fired at `x`.
    let ax = {
        let mut a = args.clone();
        a.push(tg.clone());
        inst_all(att_ax, &a)?
    };
    let (_, cond) = hyp_split(&syl(&n_att, &iff_mp(&ax)?)?)?;
    let n_rc = hyp_split(&cond)?.1;
    let rc_g = rec_cond(env, b, &ta, &tr, &te, &tg);
    let n_at_x = hyp_mp(&syl(&n_rc, &Thm::ax_inst(rc_g, tx.clone())?)?, &n_indg)?;
    let preds_g = preds_indom(env, b, &ta, &tr, &tg, &tx);
    let eqn_g = Formula::eq(
        b.app(&tg, &tx),
        b.step_at(&te, &tx, &b.ih_at(&tg, &ta, &tr, &tx)),
    );
    let n_preds_g = syl(&n_at_x, &and_left(preds_g.clone(), eqn_g.clone()))?;
    let n_eq_g = syl(&n_at_x, &and_right(preds_g, eqn_g))?;

    // `g ∈ Att → ∀x′. (indom(g,x′) → …)`, at `y`, for both bridges.
    let bridge = |thm: &Thm, at: &Term| -> Option<Thm> {
        let t = {
            let mut a = args.clone();
            a.push(tg.clone());
            inst_all(thm, &a)?
        };
        hyp_inst(&syl(&n_att, &t)?, std::slice::from_ref(at))
    };
    let n_indbridge = bridge(u.indom, &ty)?;
    let n_valbridge = bridge(u.value, &ty)?;

    // ── Under `L := (N ∧ y ∈ A) ∧ ⟨y,x⟩ ∈ R` ────────────────────────────────
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, &tx), tr.clone());
    let l1 = Formula::and(n.clone(), mem_ya.clone());
    let l_l1 = and_left(l1.clone(), edge.clone());
    let l_n = syl(&l_l1, &and_left(n.clone(), mem_ya.clone()))?;
    let l_ya = syl(&l_l1, &and_right(n.clone(), mem_ya.clone()))?;
    let l_edge = and_right(l1, edge.clone());

    let l_indg_y = {
        let at_y = hyp_inst(&syl(&l_n, &n_preds_g)?, std::slice::from_ref(&ty))?;
        hyp_mp(&hyp_mp(&at_y, &l_ya)?, &l_edge)?
    };
    let l_indrec_y = hyp_mp(&syl(&l_n, &n_indbridge)?, &l_indg_y)?;
    let l_val_y = hyp_mp(&syl(&l_n, &n_valbridge)?, &l_indg_y)?;
    let l_agree_y = hyp_eq_symm(env, &l_val_y)?;

    // `preds_indom(A,R,accrec,x)`.
    let n_preds_rec = Thm::mp(
        &Thm::ax_dist(
            yv,
            n.clone(),
            Formula::imp(
                mem_ya.clone(),
                Formula::imp(edge.clone(), b.indom(env, &f_t, &ty)),
            ),
        )?,
        &Thm::gen(yv, &uncurry(&uncurry(&l_indrec_y)?)?),
    )?;
    if *n_preds_rec.concl()
        != Formula::imp(n.clone(), preds_indom(env, b, &ta, &tr, &f_t, &tx))
    {
        return None
    }

    // `preds_agree(g,accrec,A,R,x)`, hence the two induction hypotheses agree.
    let n_pa = Thm::mp(
        &Thm::ax_dist(
            yv,
            n.clone(),
            Formula::imp(
                mem_ya,
                Formula::imp(edge, Formula::eq(b.app(&tg, &ty), b.app(&f_t, &ty))),
            ),
        )?,
        &Thm::gen(yv, &uncurry(&uncurry(&l_agree_y)?)?),
    )?;
    if *n_pa.concl()
        != Formula::imp(n.clone(), preds_agree(env, &b.s, &tg, &f_t, &ta, &tr, &tx))
    {
        return None
    }
    let ie = inst_all(
        &b.ih_ext,
        &[tg.clone(), f_t.clone(), ta.clone(), tr.clone(), tx.clone()],
    )?;
    let n_ih_eq = syl(&n_pa, &ie)?;
    let (te2, tx2) = (te.clone(), tx.clone());
    let bb = b;
    let n_step_eq = hyp_congr(env, &n_ih_eq, move |t| bb.step_at(&te2, &tx2, &t))?;

    // `app(accrec,x) = app(g,x) = step(ih(g)) = step(ih(accrec))`.
    let n_val_x = {
        let t = {
            let mut a = args.clone();
            a.push(tg.clone());
            inst_all(u.value, &a)?
        };
        let at_x = hyp_inst(&syl(&n_att, &t)?, std::slice::from_ref(&tx))?;
        hyp_mp(&at_x, &n_indg)?
    };
    let chain = hyp_eq_trans(env, &n_val_x, &n_eq_g)?;
    let n_eqn = hyp_eq_trans(env, &chain, &n_step_eq)?;
    let goal_eq = Formula::eq(
        b.app(&f_t, &tx),
        b.step_at(&te, &tx, &b.ih_at(&f_t, &ta, &tr, &tx)),
    );
    if *n_eqn.concl() != Formula::imp(n.clone(), goal_eq.clone()) {
        return None
    }

    let n_goal = hyp_and(&n_preds_rec, &n_eqn)?;

    // ── Discharge the two witnesses ─────────────────────────────────────────
    let n1_exg = syl(
        &and_right(h.clone(), mem_rec.clone()),
        &iff_mp(&{
            let mut a = args.clone();
            a.push(b.s.ap.sets.pair(tx.clone(), tw.clone()));
            inst_all(u.members, &a)?
        })?,
    )?;
    let n1_goal = hyp_exists_elim(gv, &n_goal, &n1_exg)?;
    let h_goal = hyp_exists_elim(wv, &n1_goal, &imp_refl(h.clone()))?;

    let out = Thm::gen(xv, &h_goal);
    if *out.concl() != rec_cond(env, b, &ta, &tr, &te, &f_t) {
        return None
    }
    Some(gen_all(&vars, &out))
}

/// `⊢ ∀A ∀R ∀T ∀e. accrec(A,R,T,e) ∈ Att(A,R,T,e)` — **the recursor is the
/// greatest attempt**.
///
/// Its three clauses are [`super::union::rec_subset_prod`],
/// [`super::union::rec_single_valued`] and [`rec_rec_cond`].
pub fn rec_is_attempt(env: &mut Env, b: &Base, sy: Syms, u: &UnionFacts, rc: &Thm) -> Option<Thm> {
    let (att, att_ax, rec) = (sy.att, sy.att_ax, sy.rec);
    let (subset_prod, sv) = (u.subset_prod, u.single_valued);
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (
        args[0].clone(),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
    );
    let f_t = Term::apply(rec, args.clone());

    let bound = attempt_bound(b, &ta, &tr, &tt);
    let pow_at = inst_all(
        &b.s.pow_ax,
        &[b.s.prod.of(b.acc_of(&ta, &tr), tt.clone()), f_t.clone()],
    )?;
    let in_pow = Thm::mp(&iff_mpr(&pow_at)?, &inst_all(subset_prod, &args)?)?;
    if *in_pow.concl() != Formula::mem(f_t.clone(), bound) {
        return None
    }

    let cond = crate::and_intro(&inst_all(sv, &args)?, &inst_all(rc, &args)?);
    let at = {
        let mut a = args.clone();
        a.push(f_t.clone());
        inst_all(att_ax, &a)?
    };
    let out = Thm::mp(&iff_mpr(&at)?, &crate::and_intro(&in_pow, &cond))?;
    if *out.concl() != Formula::mem(f_t, att_of(att, ta, tr, tt, te)) {
        return None
    }
    Some(gen_all(&vars, &out))
}

/// **ι on the recursor's domain.**
///
/// ```text
/// ⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) →
///       app(accrec,x) = app(app(app(e,x),•), ih(accrec,A,R,x)))
/// ```
///
/// The second clause of [`rec_rec_cond`], and nothing more. The guard
/// `indom(accrec,x)` is discharged by [`super::total`] at every
/// `x ∈ acc(A,R)`; it is stated separately because that discharge is the only
/// place a hypothesis on `e` is needed.
pub fn iota_on_domain(env: &mut Env, b: &Base, rec: FnSym, rc: &Thm) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, te) = (args[0].clone(), args[1].clone(), args[3].clone());
    let f_t = Term::apply(rec, args.clone());

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let at = inst_all(rc, &args)?;
    let at_x = Thm::mp(&Thm::ax_inst(at.concl().clone(), tx.clone())?, &at)?;

    let preds = preds_indom(env, b, &ta, &tr, &f_t, &tx);
    let eqn = Formula::eq(
        b.app(&f_t, &tx),
        b.step_at(&te, &tx, &b.ih_at(&f_t, &ta, &tr, &tx)),
    );
    let out = Thm::gen(xv, &syl(&at_x, &and_right(preds, eqn.clone()))?);
    if *out.concl()
        != Formula::forall(xv, Formula::imp(b.indom(env, &f_t, &tx), eqn))
    {
        return None
    }
    Some(gen_all(&vars, &out))
}
