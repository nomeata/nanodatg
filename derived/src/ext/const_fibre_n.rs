//! A dependent product over a **constant fibre** is the function space, with a
//! parameter prefix on the fibre.
//!
//! # Interface
//!
//! For a fibre symbol `b` of arity `k+1`, `img` its Replacement image and
//! `dprod` the dependent product [`super::dprod_n`] carves out, the single
//! export is
//!
//! ```text
//! ⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))
//!                                                       [dprod_const_fibre_n]
//! ```
//!
//! **No inhabitation antecedent, and the empty domain is included**: at
//! `A := ∅` the hypothesis is vacuous and both sides are the same set. See
//! [`super::const_fibre`]'s header for why the obvious route through
//! `⋃img(A) = B` is *false* at `A = ∅` and is avoided here too.
//!
//! `app_mem` and `retarget` are the two `b`-independent lemmas the argument
//! consumes — [`super::funspace_app_mem`] and [`super::funspace_retarget`] —
//! taken as parameters rather than derived here, so that a caller with many
//! fibres derives them once. `img_ax` and `dprod_def` are rebuilt from the
//! symbols and compared before anything rests on them.
//!
//! # Why the prefix, and why a second copy of [`super::const_fibre`]
//!
//! This is [`super::dprod_const_fibre`] with the prefix threaded through the
//! argument lists of `b`, `img` and `dprod`, for the reason
//! [`super::dprod_n`]'s header gives: a Lean `Π` body is an open expression, so
//! its fibre symbol carries one parameter per hole of the body's skeleton, and
//! a symbol's arity is fixed. Nothing else changes — the argument never takes
//! the fibre term apart — and **at `k = 0` this is
//! [`super::dprod_const_fibre`] on the nose**.
//!
//! Nothing here is trusted. A mistake yields `None` — hence a reported gap —
//! rather than a false theorem, and the final conclusion is checked against the
//! statement above in release as well as debug.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{union_intro, Apply};
use crate::funspace::Funspace;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all,
    syl, uncurry,
};

use super::dprod_n::section_n;
use super::shared::{hyp_eq_symm, hyp_leibniz};

/// `f(p⃗, arg)`.
fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(arg);
    Term::apply(f, v)
}

/// `⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))` — a
/// dependent product over a **constant fibre** is the function space.
///
/// The `k = 0` case is [`super::dprod_const_fibre`], and this is that
/// derivation with the prefix threaded through the argument lists of `b`, `img`
/// and `dprod`; nothing else changes, because the argument never takes those
/// terms apart. The two `b`-independent lemmas it consumes — `app_mem`
/// ([`super::funspace_app_mem`]) and `retarget`
/// ([`super::funspace_retarget`]) — are parameters rather than being re-derived
/// per fibre, which is the only other difference.
///
/// No inhabitation antecedent, and the empty domain is included: see the unary
/// original for why the obvious route through `⋃img(A) = B` is *false* at
/// `A = ∅` and is avoided.
#[allow(clippy::too_many_arguments)]
pub fn dprod_const_fibre_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    b: FnSym,
    img: FnSym,
    img_ax: &Thm,
    dprod: FnSym,
    dprod_def: &Thm,
    app_mem: &Thm,
    retarget: &Thm,
) -> Option<Thm> {
    let np = (b.arity() as usize).checked_sub(1)?;
    if img.arity() as usize != np + 1 || dprod.arity() as usize != np + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();

    let (av, bigb, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tbb, tf) = (Term::var(av), Term::var(bigb), Term::var(f));
    let x = env.fresh_var();
    let tx = Term::var(x);

    // The hypothesis: the fibre is constantly `B` on `A`.
    let bx = at(b, &pts, tx.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), tbb.clone())));

    // The two sets being compared, and the condition `dprod` is defined by.
    let img_t = at(img, &pts, ta.clone());
    let u = ap.sets.union_of(img_t.clone());
    let fs_b = fsp.of(ta.clone(), tbb.clone());
    let mem_fs_u = Formula::mem(tf.clone(), fsp.of(ta.clone(), u.clone()));
    let mem_fs_b = Formula::mem(tf.clone(), fs_b.clone());
    let sec = section_n(env, ap, b, &pts, &ta, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    if sec != Formula::forall(x, sec_body.clone()) {
        return None
    }
    let l = Formula::and(mem_fs_u.clone(), sec.clone());

    let dp_t = at(dprod, &pts, ta.clone());
    let mem_dp = Formula::mem(tf.clone(), dp_t.clone());
    let mut dargs = pts.clone();
    dargs.push(ta.clone());
    dargs.push(tf.clone());
    let dp_at = inst_all(dprod_def, &dargs)?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }

    // The two "values land here" hypotheses `funspace_retarget` consumes.
    let vi_b_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), tbb.clone()));
    let vi_u_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), u.clone()));

    // ── ←: a function into `B` is a section of the constant fibration ────────
    let kf = Formula::and(h.clone(), mem_fs_b.clone());
    let k_h = and_left(h.clone(), mem_fs_b.clone());
    let k_fs = and_right(h.clone(), mem_fs_b.clone());

    let m = Formula::and(kf.clone(), mem_xa.clone());
    let m_k = and_left(kf.clone(), mem_xa.clone());
    let m_xa = and_right(kf.clone(), mem_xa.clone());

    let am_at = inst_all(app_mem, &[ta.clone(), tbb.clone(), tf.clone(), tx.clone()])?;
    let m_app_b = hyp_mp(&a1i(&am_at, m.clone()), &hyp_and(&syl(&m_k, &k_fs)?, &m_xa)?)?;
    let m_fibre = hyp_mp(&syl(&syl(&m_k, &k_h)?, &Thm::ax_inst(h.clone(), tx.clone())?)?, &m_xa)?;
    let w1 = env.fresh_var();
    let m_sec_body = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &m_fibre)?, w1, &Formula::mem(app_fx.clone(), Term::var(w1)))?,
        &m_app_b,
    )?;
    let k_sec = Thm::mp(&Thm::ax_dist(x, kf.clone(), sec_body.clone())?, &Thm::gen(x, &uncurry(&m_sec_body)?))?;

    // `b(p⃗,x) ∈ img(p⃗,A)` for `x ∈ A`, so a value in `b(p⃗,x)` is a value in `⋃img(p⃗,A)`.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body =
        Formula::and(Formula::mem(tx2.clone(), ta.clone()), Formula::eq(bx.clone(), at(b, &pts, tx2)));
    let mut gargs = pts.clone();
    gargs.push(ta.clone());
    gargs.push(bx.clone());
    let img_at = inst_all(img_ax, &gargs)?;
    if *img_at.concl() != Formula::iff(Formula::mem(bx.clone(), img_t.clone()), Formula::exists(x2, img_body.clone()))
    {
        return None
    }
    let m_witness = hyp_and(&m_xa, &a1i(&Thm::eq_refl(bx.clone()), m.clone()))?;
    let m_img = syl(&syl(&m_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?, &iff_mpr(&img_at)?)?;
    let intro = union_intro(env, &ap.sets, img_t, bx, app_fx.clone())?;
    let m_app_u = syl(&hyp_and(&m_img, &m_sec_body)?, &intro)?;
    let k_vi_u = Thm::mp(&Thm::ax_dist(x, kf.clone(), vi_u_body)?, &Thm::gen(x, &uncurry(&m_app_u)?))?;

    let rt_u = inst_all(retarget, &[ta.clone(), tbb.clone(), u.clone(), tf.clone()])?;
    let k_fs_u = hyp_mp(&a1i(&rt_u, kf.clone()), &hyp_and(&k_fs, &k_vi_u)?)?;
    let k_dp = hyp_mp(&a1i(&iff_mpr(&dp_at)?, kf.clone()), &hyp_and(&k_fs_u, &k_sec)?)?;
    let bwd = uncurry(&k_dp)?;

    // ── →: a section of a constant fibration is a function into `B` ─────────
    let j = Formula::and(h.clone(), mem_dp.clone());
    let j_h = and_left(h.clone(), mem_dp.clone());
    let j_dp = and_right(h.clone(), mem_dp.clone());
    let j_l = hyp_mp(&a1i(&iff_mp(&dp_at)?, j.clone()), &j_dp)?;
    let j_fs_u = syl(&j_l, &and_left(mem_fs_u.clone(), sec.clone()))?;
    let j_sec = syl(&j_l, &and_right(mem_fs_u, sec.clone()))?;

    let n = Formula::and(j.clone(), mem_xa.clone());
    let n_j = and_left(j.clone(), mem_xa.clone());
    let n_xa = and_right(j.clone(), mem_xa);
    let n_app_bx = hyp_mp(&syl(&syl(&n_j, &j_sec)?, &Thm::ax_inst(sec, tx.clone())?)?, &n_xa)?;
    let n_fibre = hyp_mp(&syl(&syl(&n_j, &j_h)?, &Thm::ax_inst(h.clone(), tx)?)?, &n_xa)?;
    let w2 = env.fresh_var();
    let n_app_b =
        hyp_mp(&hyp_leibniz(&n_fibre, w2, &Formula::mem(app_fx.clone(), Term::var(w2)))?, &n_app_bx)?;
    if *n_app_b.concl() != Formula::imp(n, Formula::mem(app_fx, tbb.clone())) {
        return None
    }
    let j_vi_b = Thm::mp(&Thm::ax_dist(x, j.clone(), vi_b_body)?, &Thm::gen(x, &uncurry(&n_app_b)?))?;

    let rt_b = inst_all(retarget, &[ta, u, tbb, tf])?;
    let fwd = uncurry(&hyp_mp(&a1i(&rt_b, j.clone()), &hyp_and(&j_fs_u, &j_vi_b)?)?)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let all_f = Thm::mp(&Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_fs_b))?, &Thm::gen(f, &hyp_and(&fwd, &bwd)?))?;
    let out = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), fs_b.clone()])?)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(h, Formula::eq(dp_t, fs_b)) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(bigb);
    Some(gen_all(&all, &out))
}
