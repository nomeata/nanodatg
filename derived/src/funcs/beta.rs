//! Lambda graphs and beta reduction.
//!
//! # Interface
//!
//! For a unary function symbol `t`, with `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }`:
//!
//! ```text
//! ⊢ ∀A ∀y. (y ∈ lam(A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(x)⟩))   [lambda — introduces `lam`]
//! ⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))              [beta_conditional]
//! ```
//!
//! Callers need neither derivation.
//!
//! [`lambda`] is Replacement at its cheapest: the relation is `y = term`, so the
//! `∃!` premise is [`crate::exists_unique_eq`] and costs nothing. The domain
//! stays a parameter, so one symbol serves every domain.
//!
//! # The membership antecedent is not removable
//!
//! A set-theoretic function has a set domain, and off it `app(f,a)` is `∅` — see
//! [`crate::funcs::app_off_domain`], which is the complementary half. On the
//! domain the argument is:
//!
//! * `⟨a, t(a)⟩ ∈ lam(A)`, witnessed by `x := a`, which in particular makes the
//!   collection inhabited — so `Apply::coll_ax`, the conditional form this
//!   derivation matches on, applies *without* assuming anything about `t(a)`
//!   itself;
//! * conversely `⟨a,y⟩ ∈ lam(A)` forces `y = t(a)`, by injectivity of the
//!   Kuratowski pair;
//! * so `coll(lam(A), a)` and `{t(a)}` have the same members, hence are equal;
//! * and `app` strips the union off a singleton.
//!
//! Beta reduction never paid for the inhabitation antecedent `coll` used to
//! carry: what had to be inhabited was the *collection*, not the value, and on
//! the domain the collection contains `t(a)` whatever `t(a)` is.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mpr, imp_refl, inst_all, singleton, syl,
};
use super::logic::hyp_syl;
use super::apply::Apply;

/// The graph `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }` of a unary function symbol,
/// with `⊢ ∀A ∀y. (y ∈ lam(A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(x)⟩))`.
///
/// Replacement, at its cheapest: the relation is `y = term`, so the `∃!`
/// premise is [`crate::exists_unique_eq`] and costs nothing. The domain stays a
/// parameter, so one symbol serves every domain.
pub fn lambda(env: &mut Env, ap: &Apply, t: FnSym) -> Option<(FnSym, Thm)> {
    if t.arity() != 1 {
        return None
    }
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (t_a, tx) = (Term::var(av), Term::var(x));
    let pair = ap.sets.pair(tx.clone(), Term::apply(t, vec![tx.clone()]));

    let (y, phi, exu) = crate::exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&t_a))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), t_a.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, t_a), phi));
    crate::define_by_membership(env, &[av], &img, y, &cond)
}

/// `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))` — beta reduction.
///
/// The membership antecedent is not removable: a set-theoretic function has a
/// set domain, and off it `app(f,a)` is `∅` — see [`crate::funcs::app_off_domain`], which is
/// the complementary half. On the domain the argument is:
///
/// * `⟨a, t(a)⟩ ∈ lam(A)`, witnessed by `x := a`, which in particular makes the
///   collection inhabited — so [`Apply::coll_ax`], the conditional form this
///   derivation matches on, applies *without* assuming anything about `t(a)`
///   itself;
/// * conversely `⟨a,y⟩ ∈ lam(A)` forces `y = t(a)`, by injectivity of the
///   Kuratowski pair;
/// * so `coll(lam(A), a)` and `{t(a)}` have the same members, hence are equal;
/// * and `app` strips the union off a singleton.
pub fn beta_conditional(env: &mut Env, ap: &Apply, t: FnSym, lam: FnSym, lam_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (av, a, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t_a, ta, tx, ty) = (Term::var(av), Term::var(a), Term::var(x), Term::var(y));

    let lam_t = Term::apply(lam, vec![t_a.clone()]);
    let val = Term::apply(t, vec![ta.clone()]); // t(a)
    let tx_val = Term::apply(t, vec![tx.clone()]); // t(x)
    let h = Formula::mem(ta.clone(), t_a.clone()); // a ∈ A

    let pair_ay = ap.sets.pair(ta.clone(), ty.clone()); // ⟨a,y⟩
    let pair_aval = ap.sets.pair(ta.clone(), val.clone()); // ⟨a,t(a)⟩
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone()); // ⟨x,t(x)⟩

    // ── ⟨a,t(a)⟩ ∈ lam(A), by taking x := a in the image condition ───────────
    let lam_at_val = inst_all(lam_ax, &[t_a.clone(), pair_aval.clone()])?;
    let body_val = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_aval.clone(), pair_x.clone()));
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(pair_aval.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(x, body_val, ta.clone())?)?;
    let h_in_lam = syl(&h_ex, &iff_mpr(&lam_at_val)?)?; // H → ⟨a,t(a)⟩ ∈ lam(A)

    // ── The collection is inhabited, so `coll_ax` applies ────────────────────
    let mem_pair_y = Formula::mem(pair_ay.clone(), lam_t.clone());
    let h_ne = syl(&h_in_lam, &exists_intro_imp(y, mem_pair_y.clone(), val.clone())?)?;
    let coll_here = inst_all(&ap.coll_ax, &[lam_t.clone(), ta.clone()])?;
    let h_coll = syl(&h_ne, &coll_here)?; // H → ∀y. (y ∈ coll ↔ ⟨a,y⟩ ∈ lam(A))

    // ── ⟨a,y⟩ ∈ lam(A) ↔ y = t(a) ────────────────────────────────────────────
    let eq_y_val = Formula::eq(ty.clone(), val.clone());
    // ←: rewrite the membership just established along `y = t(a)`.
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(w)), lam_t.clone()),
    );
    let bwd = syl(&h_in_lam, &com12(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &carry)?)?)?;

    // →: the image condition plus injectivity of ⟨·,·⟩.
    let lam_at_y = inst_all(lam_ax, &[t_a.clone(), pair_ay.clone()])?;
    let k = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let k_eq = and_right(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let inj = inst_all(&ap.pair_inj, &[ta.clone(), ty.clone(), tx.clone(), tx_val.clone()])?;
    let k_conj = syl(&k_eq, &inj)?;
    let (e_ax, e_yt) = (Formula::eq(ta.clone(), tx.clone()), Formula::eq(ty.clone(), tx_val.clone()));
    let k_ax = syl(&k_conj, &and_left(e_ax.clone(), e_yt.clone()))?;
    let k_ytx = syl(&k_conj, &and_right(e_ax, e_yt))?;
    // a = x → t(a) = t(x)
    let w2 = env.fresh_var();
    let congr = crate::mpd_const(
        &Thm::eq_leibniz(
            ta.clone(),
            tx.clone(),
            w2,
            Formula::eq(val.clone(), Term::apply(t, vec![Term::var(w2)])),
        ),
        &Thm::eq_refl(val.clone()),
    )?;
    let k_txta = syl(&syl(&k_ax, &congr)?, &eq_symm_imp(env, val.clone(), tx_val.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(tx_val.clone(), val.clone(), w3, Formula::eq(ty.clone(), Term::var(w3)));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&carry2, k), &k_txta)?, &k_ytx)?;
    let fwd = syl(&crate::iff_mp(&lam_at_y)?, &exists_elim_imp(x, &Thm::gen(x, &k_goal), &eq_y_val)?)?;

    // ── coll(lam(A), a) and {t(a)} have the same members ─────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(lam_t.clone(), ta.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let coll_at_y = Formula::forall(y, Formula::iff(mem_yc.clone(), mem_pair_y));
    let h_iff_y = syl(&h_coll, &Thm::ax_inst(coll_at_y, ty.clone())?)?;
    let (h_c_lam, h_lam_c) = (hyp_iff_mp(&h_iff_y)?, hyp_iff_mpr(&h_iff_y)?);
    let h_c_sing = hyp_syl(&hyp_syl(&h_c_lam, &a1i(&fwd, h.clone()))?, &a1i(&iff_mpr(&ms)?, h.clone()))?;
    let h_sing_c = hyp_syl(&hyp_syl(&a1i(&crate::iff_mp(&ms)?, h.clone()), &bwd)?, &h_lam_c)?;
    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let h_same = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── app(lam(A),a) = ⋃coll = ⋃{t(a)} = t(a) ───────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = crate::mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?; // H → ⋃coll = ⋃{t(a)}

    let app_term = ap.apply(lam_t.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[lam_t, ta.clone()])?; // ⊢ app = ⋃coll
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_term, val)),
        "beta_conditional: unexpected shape"
    );
    Some(gen_all(&[av, a], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// The **parameterised** forms: a body symbol `t(p⃗, x)` with `k` parameters in
// front of the bound variable, and the graph `lam(p⃗, A)` it generates.
//
// `lambda`/`beta_conditional` above take a *unary* body symbol, which is enough
// whenever the body mentions nothing but the bound variable. It is not enough
// for a **curried** function — `λh. λt. c h t`, whose inner body depends on `h`
// as well — nor for a lambda whose domain varies with an outer parameter. Both
// occur in [`crate::wlist_fun`], where Lean's `List.cons` is interpreted as a
// nest of three graphs.
//
// These are line-for-line the two derivations above with the prefix `p⃗` threaded
// through `t`'s and `lam`'s argument lists; at `k = 0` they reduce to exactly
// the unary versions. They were originally private to the checker's backend and
// were moved here when a second caller appeared.
// ─────────────────────────────────────────────────────────────────────────────
/// The graph `lam(p⃗, A) = { ⟨x, t(p⃗, x)⟩ : x ∈ A }`, with
/// `⊢ ∀p⃗ ∀A ∀y. (y ∈ lam(p⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(p⃗,x)⟩))`.
///
/// The `k = 0` case is [`lambda`].
pub fn lambda_n(env: &mut Env, ap: &Apply, t: FnSym) -> Option<(FnSym, Thm)> {
    let k = (t.arity() as usize).checked_sub(1)?;
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (t_a, tx) = (Term::var(av), Term::var(x));

    let mut targs = pts.clone();
    targs.push(tx.clone());
    let pair = ap.sets.pair(tx.clone(), Term::apply(t, targs));

    let (y, phi, exu) = crate::exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = crate::inst_all(&repl, std::slice::from_ref(&t_a))?;
    let premise = Thm::gen(x, &crate::a1i(&exu, Formula::mem(tx.clone(), t_a.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, t_a), phi));
    let mut params = ps;
    params.push(av);
    crate::define_by_membership(env, &params, &img, y, &cond)
}

/// `⊢ ∀p⃗ ∀A ∀a. (a ∈ A → app(lam(p⃗,A), a) = t(p⃗,a))` — beta reduction.
///
/// The `k = 0` case is [`beta_conditional`]; see there for the
/// argument. Only the argument lists of `t` and `lam` differ.
pub fn beta_conditional_n(env: &mut Env, ap: &Apply, t: FnSym, lam: FnSym, lam_ax: &Thm) -> Option<Thm> {
    use super::logic::hyp_syl;
    use crate::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and,
        hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, singleton, syl,
    };

    let k = (t.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, a, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t_a, ta, tx, ty) = (Term::var(av), Term::var(a), Term::var(x), Term::var(y));

    // `t(p⃗, ·)` and `lam(p⃗, ·)`, the only places the extra parameters show up.
    let t_at = |arg: Term| {
        let mut v = pts.clone();
        v.push(arg);
        Term::apply(t, v)
    };
    let lam_t = {
        let mut v = pts.clone();
        v.push(t_a.clone());
        Term::apply(lam, v)
    };
    let lam_inst = |thm: &Thm, extra: &[Term]| {
        let mut v = pts.clone();
        v.extend_from_slice(extra);
        inst_all(thm, &v)
    };

    let val = t_at(ta.clone()); // t(p⃗, a)
    let tx_val = t_at(tx.clone()); // t(p⃗, x)
    let h = Formula::mem(ta.clone(), t_a.clone()); // a ∈ A

    let pair_ay = ap.sets.pair(ta.clone(), ty.clone());
    let pair_aval = ap.sets.pair(ta.clone(), val.clone());
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone());

    // ── ⟨a,t(a)⟩ ∈ lam(A), by taking x := a in the image condition ───────────
    let lam_at_val = lam_inst(lam_ax, &[t_a.clone(), pair_aval.clone()])?;
    let body_val = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_aval.clone(), pair_x.clone()));
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(pair_aval.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(x, body_val, ta.clone())?)?;
    let h_in_lam = syl(&h_ex, &iff_mpr(&lam_at_val)?)?;

    // ── The collection is inhabited, so `coll_ax` applies ────────────────────
    let mem_pair_y = Formula::mem(pair_ay.clone(), lam_t.clone());
    let h_ne = syl(&h_in_lam, &exists_intro_imp(y, mem_pair_y.clone(), val.clone())?)?;
    let coll_here = inst_all(&ap.coll_ax, &[lam_t.clone(), ta.clone()])?;
    let h_coll = syl(&h_ne, &coll_here)?;

    // ── ⟨a,y⟩ ∈ lam(A) ↔ y = t(a) ────────────────────────────────────────────
    let eq_y_val = Formula::eq(ty.clone(), val.clone());
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(w)), lam_t.clone()),
    );
    let bwd = syl(&h_in_lam, &com12(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &carry)?)?)?;

    let lam_at_y = lam_inst(lam_ax, &[t_a.clone(), pair_ay.clone()])?;
    let kf = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let k_eq = and_right(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let inj = inst_all(&ap.pair_inj, &[ta.clone(), ty.clone(), tx.clone(), tx_val.clone()])?;
    let k_conj = syl(&k_eq, &inj)?;
    let (e_ax, e_yt) = (Formula::eq(ta.clone(), tx.clone()), Formula::eq(ty.clone(), tx_val.clone()));
    let k_ax = syl(&k_conj, &and_left(e_ax.clone(), e_yt.clone()))?;
    let k_ytx = syl(&k_conj, &and_right(e_ax, e_yt))?;
    let w2 = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(ta.clone(), tx.clone(), w2, Formula::eq(val.clone(), t_at(Term::var(w2)))),
        &Thm::eq_refl(val.clone()),
    )?;
    let k_txta = syl(&syl(&k_ax, &congr)?, &eq_symm_imp(env, val.clone(), tx_val.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(tx_val.clone(), val.clone(), w3, Formula::eq(ty.clone(), Term::var(w3)));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&carry2, kf), &k_txta)?, &k_ytx)?;
    let fwd = syl(&iff_mp(&lam_at_y)?, &exists_elim_imp(x, &Thm::gen(x, &k_goal), &eq_y_val)?)?;

    // ── coll(lam(A), a) and {t(a)} have the same members ─────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(lam_t.clone(), ta.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let coll_at_y = Formula::forall(y, Formula::iff(mem_yc.clone(), mem_pair_y));
    let h_iff_y = syl(&h_coll, &Thm::ax_inst(coll_at_y, ty.clone())?)?;
    let (h_c_lam, h_lam_c) = (hyp_iff_mp(&h_iff_y)?, hyp_iff_mpr(&h_iff_y)?);
    let h_c_sing = hyp_syl(&hyp_syl(&h_c_lam, &a1i(&fwd, h.clone()))?, &a1i(&iff_mpr(&ms)?, h.clone()))?;
    let h_sing_c = hyp_syl(&hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &bwd)?, &h_lam_c)?;
    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let h_same = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── app(lam(A),a) = ⋃coll = ⋃{t(a)} = t(a) ───────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_term = ap.apply(lam_t.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[lam_t, ta.clone()])?;
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, Formula::eq(app_term, val)) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(a);
    Some(gen_all(&all, &out))
}

