//! Extensionality for Replacement images and lambda graphs, with a **parameter
//! prefix** on each side.
//!
//! # Interface
//!
//! For symbols carrying a prefix `p⃗` of length `k` and `q⃗` of length `k'` —
//! `img`/`img'` any Replacement images, `lam`/`lam'` the graphs
//! [`crate::funcs::lambda_n`] builds over body symbols `t`/`t'` — the exports
//! are
//!
//! ```text
//! ⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g(x) = g'(x))) → img(p⃗,A) = img'(q⃗,A')))
//!                                                                  [image_ext_n]
//!
//! ⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(p⃗,x) = t'(q⃗,x)))
//!                              → lam(p⃗,A) = lam'(q⃗,A')))            [lam_ext_n]
//! ```
//!
//! [`image_ext_n`] leaves the prefixes **free** rather than generalising them:
//! the caller allocated those variables and quantifies them along with
//! everything else at the end. It also takes the binder `x` and the two body
//! *terms* `g`/`g'` directly, since a fibre image's element term need not be a
//! bare symbol application; `lam_ext_n` is the instance at
//! `g(x) := ⟨x, t(p⃗,x)⟩`, and it does generalise `p⃗` and `q⃗`.
//!
//! The two prefixes need not have the same length: the two lambdas being
//! compared come from unrelated skeletons.
//!
//! # Why the prefix, and why a second copy of [`super::lam_cong`]
//!
//! A Lean lambda body is an open expression, so the body symbol a graph is
//! built over generally carries one parameter per *hole* of the body's skeleton
//! in addition to the binder — see [`crate::funcs::beta`] and
//! [`super::dprod_n`], which face the same thing for the dependent product. A
//! symbol's arity is fixed and there is no way inside the object language to
//! specialise an arity-`k+1` symbol to an arity-`1` one, so
//! [`super::lam_cong`] cannot be *instantiated* at a prefixed body: it has to
//! be re-run with the prefix threaded through the argument lists.
//!
//! Nothing else changes. No step of the argument ever takes the body term
//! apart — it only quotes it — so the extra parameters ride along untouched,
//! and **at `k = k' = 0` this is [`super::lam_cong`] on the nose**. Read
//! [`super::lam_cong`]'s header for *why* Extensionality rather than congruence
//! is what relates two graphs; this file adds only the plumbing.
//!
//! Nothing here is trusted. Like everything outside `kernel/`, these can only
//! reach a [`Thm`] through the kernel's primitive rules, so a mistake yields
//! `None` — hence a reported gap — rather than a false theorem. Both functions
//! check their final conclusion against the statement above regardless, in
//! release as well as debug, and both check the characteristic axioms they are
//! handed against the shape they must have: a mismatch would still be sound but
//! would prove something about the wrong sets, and silently.
//!
//! Both also require every theorem handed in to be **unconditional**. A [`Thm`]
//! is a sequent `Γ ⊢ φ`, and the shape checks just described compare `concl()`,
//! which is what the theorem would say *if* `Γ` were discharged; [`Thm::mp`]
//! then unions the two sides' `Γ`s without comment. So a `Thm::assume` of
//! exactly the closed formula [`crate::funcs::lambda_n`] produces would satisfy
//! every pin here and leave its own antecedent sitting in the `Γ` of a result
//! whose header says `⊢`. [`crate::all_unconditional`] is the guard.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

/// `f(prefix⃗, arg)`.
fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(arg);
    Term::apply(f, v)
}

/// The instantiation list `prefix⃗, A, y` for a graph's characteristic axiom.
fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
    let mut v = prefix.to_vec();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g(x) = g'(x))) → img(p⃗,A) = img'(q⃗,A')))`
/// — extensionality for Replacement images, with a parameter prefix on each
/// side.
///
/// The `k = k' = 0` case is [`super::image_ext`]; the prefixes are left *free*
/// here rather than generalised, so that the caller — which allocated them —
/// can quantify them along with everything else at the end.
///
/// The two axioms are checked against the shape they must have rather than
/// assumed: a mismatch would still be sound but would prove something about the
/// wrong sets, and silently, so it returns `None` instead. They must also be
/// **unconditional** — the shape check reads `concl()`, so it cannot see an
/// open `Γ`, and the header above promises a bare `⊢`.
#[allow(clippy::too_many_arguments)]
pub fn image_ext_n(
    env: &mut Env,
    x: FreeVar,
    pts: &[Term],
    g1: &Term,
    img: FnSym,
    img_ax: &Thm,
    qts: &[Term],
    g2: &Term,
    img2: FnSym,
    img2_ax: &Thm,
) -> Option<Thm> {
    if img.arity() as usize != pts.len() + 1 || img2.arity() as usize != qts.len() + 1 {
        return None
    }
    if !crate::all_unconditional(&[img_ax, img2_ax]) {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let (av, av2, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    // The bodies are the caller's terms, so they have to be kept clear of the
    // variables this derivation binds — otherwise the quantifiers below would
    // capture an occurrence and the conclusion would say something else.
    for v in [av, av2, y] {
        if g1.occurs_free(v) || g2.occurs_free(v) {
            return None
        }
    }

    let img_t = at(img, pts, ta.clone());
    let img2_t = at(img2, qts, ta2.clone());

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(g1.clone(), g2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    let eq_y1 = Formula::eq(ty.clone(), g1.clone());
    let eq_y2 = Formula::eq(ty.clone(), g2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), img_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), img2_t.clone());

    let img_at_y = inst_all(img_ax, &inst2(pts, &ta, &ty))?;
    if *img_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let img2_at_y = inst_all(img2_ax, &inst2(qts, &ta2, &ty))?;
    if *img2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of img(p⃗,A) is a member of img'(q⃗,A') ─────────────
    let k = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    let k_gg = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k.clone()), &k_dom)?, &k_xa)?;
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(g1.clone(), g2.clone(), w2, Formula::eq(ty.clone(), Term::var(w2)));
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k), &k_gg)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    let fwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?), &Formula::imp(h.clone(), ex2.clone()))?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&img2_at_y)?, h.clone()),
    )?;

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_gg = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_gg_symm = syl(&j_gg, &eq_symm_imp(env, g1.clone(), g2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(g2.clone(), g1.clone(), w4, Formula::eq(ty.clone(), Term::var(w4)));
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j), &j_gg_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?), &Formula::imp(h.clone(), ex1.clone()))?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&img_at_y)?, h.clone()),
    )?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(&Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?, &Thm::gen(y, &h_iff))?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[img_t.clone(), img2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(img_t, img2_t))) {
        return None
    }
    Some(gen_all(&[av, av2], &out))
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(p⃗,x) = t'(q⃗,x))) → lam(p⃗,A) = lam'(q⃗,A')))`
/// — lambda graph extensionality, with a parameter prefix on each side.
///
/// The `k = k' = 0` case is [`super::lam_ext`], and this is that derivation
/// with the two prefixes threaded through the argument lists of `t`/`lam` and
/// `t2`/`lam2`. Nothing else changes: the argument never takes those terms
/// apart, it only quotes them, so the extra parameters ride along untouched.
/// The prefixes need not have the same length — the two lambdas being compared
/// have independent skeletons.
///
/// `lam_ax`/`lam2_ax` must be what [`crate::funcs::lambda_n`] produces for
/// `t`/`t2`; that is checked, not assumed, and both must additionally be
/// **unconditional**. The shape check compares `concl()` and so is blind to an
/// open `Γ`, which [`Thm::mp`] would then union into the theorem this header
/// states as `⊢`.
///
/// As everywhere outside `kernel/`, a mistake here can only produce `None`, and
/// hence a reported gap. The final shape is checked regardless.
#[allow(clippy::too_many_arguments)]
pub fn lam_ext_n(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    t2: FnSym,
    lam2: FnSym,
    lam2_ax: &Thm,
) -> Option<Thm> {
    let k = (t.arity() as usize).checked_sub(1)?;
    let k2 = (t2.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 || lam2.arity() as usize != k2 + 1 {
        return None
    }
    if !crate::all_unconditional(&[lam_ax, lam2_ax]) {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..k2).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, av2, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    let lam_t = at(lam, &pts, ta.clone()); // lam(p⃗, A)
    let lam2_t = at(lam2, &qts, ta2.clone()); // lam'(q⃗, A')
    let val1 = at(t, &pts, tx.clone()); // t(p⃗, x)
    let val2 = at(t2, &qts, tx.clone()); // t'(q⃗, x)
    let pair1 = ap.sets.pair(tx.clone(), val1.clone()); // ⟨x, t(p⃗,x)⟩
    let pair2 = ap.sets.pair(tx.clone(), val2.clone()); // ⟨x, t'(q⃗,x)⟩

    // The two hypotheses, and their conjunction `H`.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(Formula::mem(tx.clone(), ta.clone()), Formula::eq(val1.clone(), val2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let eq_y1 = Formula::eq(ty.clone(), pair1.clone());
    let eq_y2 = Formula::eq(ty.clone(), pair2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), lam_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), lam2_t.clone());

    // Both characteristic axioms must have exactly the shape `lambda_n` gives,
    // or the derivation below would be about the wrong sets. Checked, not
    // `debug_assert`ed: this runs in release.
    let lam_at_y = inst_all(lam_ax, &inst2(&pts, &ta, &ty))?;
    if *lam_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let lam2_at_y = inst_all(lam2_ax, &inst2(&qts, &ta2, &ty))?;
    if *lam2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of lam(p⃗,A) is a member of lam'(q⃗,A') ─────────────
    let k_f = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    let k_tt = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k_f.clone()), &k_dom)?, &k_xa)?;
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(
        val1.clone(),
        val2.clone(),
        w2,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w2))),
    );
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k_f), &k_tt)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    let fwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?), &Formula::imp(h.clone(), ex2.clone()))?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&lam2_at_y)?, h.clone()),
    )?;

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_tt = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_tt_symm = syl(&j_tt, &eq_symm_imp(env, val1.clone(), val2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(
        val2.clone(),
        val1.clone(),
        w4,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w4))),
    );
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j), &j_tt_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?), &Formula::imp(h.clone(), ex1.clone()))?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&lam_at_y)?, h.clone()),
    )?;

    // ── Same members, hence equal ───────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(&Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?, &Thm::gen(y, &h_iff))?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[lam_t.clone(), lam2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(lam_t, lam2_t))) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    all.push(av2);
    Some(gen_all(&all, &out))
}
