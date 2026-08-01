//! Dependent-product extensionality, with a **parameter prefix** on each side.
//!
//! # Interface
//!
//! For two fibre symbols `b` of arity `k+1` and `b'` of arity `k'+1`, with
//! `img`/`img'` their Replacement images and `dprod`/`dprod'` the dependent
//! products [`super::dprod_n`] carves out of the corresponding function spaces,
//! the single export is
//!
//! ```text
//! ⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(p⃗,x) = b'(q⃗,x)))
//!                              → dprod(p⃗,A) = dprod'(q⃗,A')))     [dprod_ext_n]
//! ```
//!
//! The two prefixes are independent and need not have the same length: the two
//! `Π` types being compared have unrelated fibre skeletons. Callers need
//! nothing below the statement.
//!
//! The four symbols and their two axioms are handed in as the tuples
//! `(b, img, img_ax, dprod, dprod_def)`; **every one of the axioms is rebuilt
//! from the symbols and compared** before anything rests on it, so a mismatched
//! fibre, image or product is refused with `None` rather than silently
//! described.
//!
//! # Why the prefix, and why a second copy of [`super::pi_cong`]
//!
//! This is the `k = k' = 0` construction [`super::pi_cong`] with the two
//! prefixes threaded through the argument lists, for the same reason
//! [`super::dprod_n`] exists at all: a Lean `Π` body is an open expression, so
//! its fibre symbol generally carries one parameter per hole of the body's
//! skeleton in addition to the binder, and a symbol's arity is fixed. Nothing
//! else changes — no step of the argument takes the fibre term apart — and **at
//! `k = k' = 0` this is [`super::pi_cong`] on the nose**.
//!
//! Read [`super::pi_cong`]'s header for *why* Extensionality rather than
//! congruence is what relates two dependent products: two `Π`s whose bodies
//! have different shapes are built over different, unrelated symbols, so
//! congruence over sub-terms relates nothing at all.
//!
//! Nothing here is trusted. A mistake yields `None` — hence a reported gap —
//! rather than a false theorem, and the final conclusion is checked against the
//! statement above in release as well as debug.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::funspace::Funspace;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry};

use super::dprod_n::section_n;
use super::lam_cong_n::image_ext_n;
use super::shared::{curry, hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_leibniz};

/// `f(prefix⃗, arg)`.
fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(arg);
    Term::apply(f, v)
}

/// The instantiation list `prefix⃗, A, f`.
fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
    let mut v = prefix.to_vec();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(p⃗,x) = b'(q⃗,x))) → dprod(p⃗,A) = dprod'(q⃗,A')))`
/// — dependent product extensionality, with a parameter prefix on each side.
///
/// The `k = k' = 0` case is [`super::dprod_ext`]. This is what a `pi_cong` rule
/// needs for two dependent `Π` types whose bodies have *different* shapes: the
/// head symbols are then different and unrelated, so congruence over sub-terms
/// relates nothing — exactly the position [`super::lam_cong`] is in, and
/// settled the same way, by Extensionality.
///
/// `a` is `(b, img, img_ax, dprod, dprod_def)` for the left-hand product and
/// `b` the same for the right. The two defining axioms are rebuilt from the
/// symbols handed in and compared, so a mismatched fibre or product is refused
/// rather than silently described.
#[allow(clippy::too_many_arguments)]
pub fn dprod_ext_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    a: (FnSym, FnSym, &Thm, FnSym, &Thm),
    b: (FnSym, FnSym, &Thm, FnSym, &Thm),
) -> Option<Thm> {
    let (bs, img, img_ax, dprod, dprod_def) = a;
    let (bs2, img2, img2_ax, dprod2, dprod2_def) = b;
    let np = (bs.arity() as usize).checked_sub(1)?;
    let nq = (bs2.arity() as usize).checked_sub(1)?;
    if img.arity() as usize != np + 1 || dprod.arity() as usize != np + 1 {
        return None
    }
    if img2.arity() as usize != nq + 1 || dprod2.arity() as usize != nq + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..nq).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();

    let x = env.fresh_var();
    let tx = Term::var(x);
    let bx = at(bs, &pts, tx.clone());
    let b2x = at(bs2, &qts, tx.clone());

    // ⊢ ∀A ∀A'. (A = A' → (PW → img(p⃗,A) = img'(q⃗,A'))), the fibre images.
    let img_ext = image_ext_n(env, x, &pts, &bx, img, img_ax, &qts, &b2x, img2, img2_ax)?;

    let (av, av2, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tf) = (Term::var(av), Term::var(av2), Term::var(f));

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), b2x.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());
    let h_dom = and_left(eq_dom.clone(), pointwise.clone());
    let h_pw = and_right(eq_dom.clone(), pointwise.clone());

    // ── The function space the product is carved out of ──────────────────────
    let h_img = curry(&inst_all(&img_ext, &[ta.clone(), ta2.clone()])?)?;
    let u = ap.sets.union_of(at(img, &pts, ta.clone()));
    let u2 = ap.sets.union_of(at(img2, &qts, ta2.clone()));
    let w0 = env.fresh_var();
    let h_u = hyp_congr(&h_img, w0, &u, &ap.sets.union_of(Term::var(w0)))?;

    let fs_t = fsp.of(ta.clone(), u.clone());
    let fs_mid = fsp.of(ta2.clone(), u.clone());
    let fs2_t = fsp.of(ta2.clone(), u2.clone());
    let w1 = env.fresh_var();
    let h_fs1 = hyp_congr(&h_dom, w1, &fs_t, &fsp.of(Term::var(w1), u.clone()))?;
    let w2 = env.fresh_var();
    let h_fs2 = hyp_congr(&h_u, w2, &fs_mid, &fsp.of(ta2.clone(), Term::var(w2)))?;
    let h_fs = hyp_eq_trans(env, &h_fs1, &h_fs2)?;

    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let mem_fs2 = Formula::mem(tf.clone(), fs2_t.clone());
    let w3 = env.fresh_var();
    let h_mem_fwd = hyp_leibniz(&h_fs, w3, &Formula::mem(tf.clone(), Term::var(w3)))?;
    let w4 = env.fresh_var();
    let h_mem_bwd = hyp_leibniz(&hyp_eq_symm(env, &h_fs)?, w4, &Formula::mem(tf.clone(), Term::var(w4)))?;

    // ── The section condition, rebuilt at our own `x` so it can be opened ────
    let sec = section_n(env, ap, bs, &pts, &ta, &tf);
    let sec2 = section_n(env, ap, bs2, &qts, &ta2, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    let sec2_body = Formula::imp(mem_xa2.clone(), Formula::mem(app_fx.clone(), b2x.clone()));
    if sec != Formula::forall(x, sec_body.clone()) || sec2 != Formula::forall(x, sec2_body.clone()) {
        return None
    }

    // Forward, under `M := (H ∧ sec) ∧ x ∈ A'`. Both hypotheses are stated over
    // `A`, so the first move is to bring `x` back there.
    let k = Formula::and(h.clone(), sec.clone());
    let k_h = and_left(h.clone(), sec.clone());
    let k_sec = and_right(h.clone(), sec.clone());
    let m_k = and_left(k.clone(), mem_xa2.clone());
    let m_xa2 = and_right(k.clone(), mem_xa2.clone());
    let m_h = syl(&m_k, &k_h)?;
    let m_dom = syl(&m_h, &h_dom)?;
    let w5 = env.fresh_var();
    let m_to_a = hyp_leibniz(&hyp_eq_symm(env, &m_dom)?, w5, &Formula::mem(tx.clone(), Term::var(w5)))?;
    let m_xa = hyp_mp(&m_to_a, &m_xa2)?;
    let m_bb = hyp_mp(&syl(&syl(&m_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &m_xa)?;
    let m_app = hyp_mp(&syl(&syl(&m_k, &k_sec)?, &Thm::ax_inst(sec.clone(), tx.clone())?)?, &m_xa)?;
    let w6 = env.fresh_var();
    let m_goal = hyp_mp(&hyp_leibniz(&m_bb, w6, &Formula::mem(app_fx.clone(), Term::var(w6)))?, &m_app)?;
    // `x` is bound in `K`, so it generalises out from under it.
    let k_sec2 = Thm::mp(&Thm::ax_dist(x, k.clone(), sec2_body.clone())?, &Thm::gen(x, &uncurry(&m_goal)?))?;
    let h_sec_fwd = uncurry(&k_sec2)?;

    // Backward, under `N := (H ∧ sec') ∧ x ∈ A`, the mirror image.
    let j = Formula::and(h.clone(), sec2.clone());
    let j_h = and_left(h.clone(), sec2.clone());
    let j_sec2 = and_right(h.clone(), sec2.clone());
    let n_j = and_left(j.clone(), mem_xa.clone());
    let n_xa = and_right(j.clone(), mem_xa.clone());
    let n_h = syl(&n_j, &j_h)?;
    let w7 = env.fresh_var();
    let n_xa2 = hyp_mp(&hyp_leibniz(&syl(&n_h, &h_dom)?, w7, &Formula::mem(tx.clone(), Term::var(w7)))?, &n_xa)?;
    let n_bb = hyp_mp(&syl(&syl(&n_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &n_xa)?;
    let n_app2 = hyp_mp(&syl(&syl(&n_j, &j_sec2)?, &Thm::ax_inst(sec2.clone(), tx.clone())?)?, &n_xa2)?;
    let w8 = env.fresh_var();
    let n_goal =
        hyp_mp(&hyp_leibniz(&hyp_eq_symm(env, &n_bb)?, w8, &Formula::mem(app_fx.clone(), Term::var(w8)))?, &n_app2)?;
    let j_sec = Thm::mp(&Thm::ax_dist(x, j.clone(), sec_body.clone())?, &Thm::gen(x, &uncurry(&n_goal)?))?;
    let h_sec_bwd = uncurry(&j_sec)?;

    // ── The two membership conditions agree ──────────────────────────────────
    let l = Formula::and(mem_fs.clone(), sec.clone());
    let l2 = Formula::and(mem_fs2.clone(), sec2.clone());

    let p_h = and_left(h.clone(), l.clone());
    let p_l = and_right(h.clone(), l.clone());
    let p_mem = hyp_mp(&syl(&p_h, &h_mem_fwd)?, &syl(&p_l, &and_left(mem_fs.clone(), sec.clone()))?)?;
    let p_sec = hyp_mp(&syl(&p_h, &h_sec_fwd)?, &syl(&p_l, &and_right(mem_fs.clone(), sec.clone()))?)?;
    let h_l_fwd = uncurry(&hyp_and(&p_mem, &p_sec)?)?;

    let q_h = and_left(h.clone(), l2.clone());
    let q_l = and_right(h.clone(), l2.clone());
    let q_mem = hyp_mp(&syl(&q_h, &h_mem_bwd)?, &syl(&q_l, &and_left(mem_fs2.clone(), sec2.clone()))?)?;
    let q_sec = hyp_mp(&syl(&q_h, &h_sec_bwd)?, &syl(&q_l, &and_right(mem_fs2.clone(), sec2.clone()))?)?;
    let h_l_bwd = uncurry(&hyp_and(&q_mem, &q_sec)?)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let (dp_t, dp2_t) = (at(dprod, &pts, ta.clone()), at(dprod2, &qts, ta2.clone()));
    let (mem_dp, mem_dp2) = (Formula::mem(tf.clone(), dp_t.clone()), Formula::mem(tf.clone(), dp2_t.clone()));

    let dp_at = inst_all(dprod_def, &inst2(&pts, &ta, &tf))?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }
    let dp2_at = inst_all(dprod2_def, &inst2(&qts, &ta2, &tf))?;
    if *dp2_at.concl() != Formula::iff(mem_dp2.clone(), l2) {
        return None
    }

    let h_fwd = hyp_syl(&hyp_syl(&a1i(&iff_mp(&dp_at)?, h.clone()), &h_l_fwd)?, &a1i(&iff_mpr(&dp2_at)?, h.clone()))?;
    let h_bwd = hyp_syl(&hyp_syl(&a1i(&iff_mp(&dp2_at)?, h.clone()), &h_l_bwd)?, &a1i(&iff_mpr(&dp_at)?, h.clone()))?;
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_f = Thm::mp(&Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_dp2))?, &Thm::gen(f, &h_iff))?;
    let h_eq = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), dp2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(dp_t, dp2_t))) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    all.push(av2);
    Some(gen_all(&all, &out))
}
