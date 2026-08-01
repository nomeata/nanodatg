//! Extensionality for the dependent product: the checker's `pi_cong`.
//!
//! # Interface
//!
//! With `dprod` and `dprod'` the [`crate::ext::DProd`]s over fibre symbols `b`
//! and `b'` (built over the *same* [`crate::funcs::Apply`] and
//! [`crate::funspace::Funspace`] — a second one would give unrelated symbols and
//! nothing would compose), the exports are
//!
//! ```text
//! ⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(x) = b'(x))) → dprod(A) = dprod'(A')))  [dprod_ext]
//! ⊢ ∀A. ((∀x. (x ∈ A → b(x) = b'(x))) → dprod(A) = dprod'(A))                 [dprod_ext_same_domain]
//! ```
//!
//! the second being the form the checker calls. Callers need none of the
//! derivation below.
//!
//! # Why extensionality, and the route
//!
//! `pi_cong` is in the same position `lam_cong` was: `⟦Π(x:A). B(x)⟧` is a
//! `dprod` whose head symbol is chosen by the *shape of the body*, so two
//! interpretations of provably-equal Π-types are built by two unrelated symbols
//! and plain congruence over sub-terms relates nothing. Extensionality does, and
//! the route runs through the pieces `dprod` is assembled from:
//!
//!   1. `⋃img(A) = ⋃img'(A')` — [`crate::ext::image_ext`] on the fibre images,
//!      then congruence for `⋃`, which is an ordinary function symbol;
//!   2. `fs(A, ⋃img(A)) = fs(A', ⋃img'(A'))` — congruence for `fs`, twice;
//!   3. the separation condition `∀x ∈ A. app(f,x) ∈ b(x)` agrees pointwise, so
//!      the two carved sets have the same members;
//!   4. Extensionality.
//!
//! Step 3 is the only one that is not pure congruence, and it is exactly the
//! same two-way argument `image_ext` runs: the domain equation moves `x` across,
//! the pointwise hypothesis is stated over `A` so `x` has to be moved *back*
//! before it applies, and the fibre equation carries membership.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::funspace::Funspace;
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};
use super::shared::{curry, hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_leibniz, same_domain};
use super::dprod::{base_of, is_section, DProd};
use super::lam_cong::image_ext;

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(x) = b'(x))) → dprod(A) = dprod'(A')))`
/// — dependent product extensionality.
///
/// `dp` must be the [`DProd`] built over `ap`, `fsp` and the unary fibre symbol
/// `b`, and `dp2` the one built over the same `ap` and `fsp` with fibre `b2`; a
/// second `Apply` or `Funspace` would give unrelated symbols and nothing would
/// compose. Both are checked: the fibre images are checked by [`image_ext`], and
/// the two defining axioms are rebuilt from `b`, `b2` and the function space and
/// compared, so a mismatched `DProd` is refused rather than silently described.
pub fn dprod_ext(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    b: FnSym,
    dp: &DProd,
    b2: FnSym,
    dp2: &DProd,
) -> Option<Thm> {
    if b.arity() != 1 || b2.arity() != 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let x = env.fresh_var();
    let tx = Term::var(x);
    let bx = Term::apply(b, vec![tx.clone()]); // b(x)
    let b2x = Term::apply(b2, vec![tx.clone()]); // b'(x)

    // ⊢ ∀A ∀A'. (A = A' → (PW → img(A) = img'(A'))), the fibre images.
    let img_ext = image_ext(env, x, &bx, dp.img, &dp.img_ax, &b2x, dp2.img, &dp2.img_ax)?;

    let (av, av2, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tf) = (Term::var(av), Term::var(av2), Term::var(f));

    // The two hypotheses, and their conjunction `H` — the same `PW` that
    // `image_ext` states, so its conclusion applies to `H` unchanged.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), b2x.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());
    let h_dom = and_left(eq_dom.clone(), pointwise.clone());
    let h_pw = and_right(eq_dom.clone(), pointwise.clone());

    // ── 1 & 2: the function space the product is carved out of ───────────────
    let h_img = curry(&inst_all(&img_ext, &[ta.clone(), ta2.clone()])?)?;
    let (u, u2) = (base_of(ap, dp.img, &ta), base_of(ap, dp2.img, &ta2));
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
    let h_mem_bwd =
        hyp_leibniz(&hyp_eq_symm(env, &h_fs)?, w4, &Formula::mem(tf.clone(), Term::var(w4)))?;

    // ── 3: the section condition, rebuilt at our own `x` so it can be opened ──
    let sec = is_section(env, ap, b, &ta, &tf);
    let sec2 = is_section(env, ap, b2, &ta2, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    let sec2_body = Formula::imp(mem_xa2.clone(), Formula::mem(app_fx.clone(), b2x.clone()));
    debug_assert_eq!(sec, Formula::forall(x, sec_body.clone()), "dprod_ext: section shape drift");
    debug_assert_eq!(sec2, Formula::forall(x, sec2_body.clone()), "dprod_ext: section shape drift");

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
    let m_to_a =
        hyp_leibniz(&hyp_eq_symm(env, &m_dom)?, w5, &Formula::mem(tx.clone(), Term::var(w5)))?;
    let m_xa = hyp_mp(&m_to_a, &m_xa2)?;
    let m_bb = hyp_mp(
        &syl(&syl(&m_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?,
        &m_xa,
    )?;
    let m_app =
        hyp_mp(&syl(&syl(&m_k, &k_sec)?, &Thm::ax_inst(sec.clone(), tx.clone())?)?, &m_xa)?;
    let w6 = env.fresh_var();
    let m_goal = hyp_mp(
        &hyp_leibniz(&m_bb, w6, &Formula::mem(app_fx.clone(), Term::var(w6)))?,
        &m_app,
    )?;
    // `x` is bound in `K`, so it generalises out from under it.
    let k_sec2 =
        Thm::mp(&Thm::ax_dist(x, k.clone(), sec2_body.clone())?, &Thm::gen(x, &uncurry(&m_goal)?))?;
    let h_sec_fwd = uncurry(&k_sec2)?;

    // Backward, under `N := (H ∧ sec') ∧ x ∈ A`, the mirror image: `x` moves
    // *into* `A'` to use the section hypothesis, and the fibre equation is
    // turned around to carry membership back.
    let j = Formula::and(h.clone(), sec2.clone());
    let j_h = and_left(h.clone(), sec2.clone());
    let j_sec2 = and_right(h.clone(), sec2.clone());
    let n_j = and_left(j.clone(), mem_xa.clone());
    let n_xa = and_right(j.clone(), mem_xa.clone());
    let n_h = syl(&n_j, &j_h)?;
    let w7 = env.fresh_var();
    let n_xa2 = hyp_mp(
        &hyp_leibniz(&syl(&n_h, &h_dom)?, w7, &Formula::mem(tx.clone(), Term::var(w7)))?,
        &n_xa,
    )?;
    let n_bb = hyp_mp(
        &syl(&syl(&n_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?,
        &n_xa,
    )?;
    let n_app2 =
        hyp_mp(&syl(&syl(&n_j, &j_sec2)?, &Thm::ax_inst(sec2.clone(), tx.clone())?)?, &n_xa2)?;
    let w8 = env.fresh_var();
    let n_goal = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &n_bb)?, w8, &Formula::mem(app_fx.clone(), Term::var(w8)))?,
        &n_app2,
    )?;
    let j_sec =
        Thm::mp(&Thm::ax_dist(x, j.clone(), sec_body.clone())?, &Thm::gen(x, &uncurry(&n_goal)?))?;
    let h_sec_bwd = uncurry(&j_sec)?;

    // ── The two membership conditions agree ──────────────────────────────────
    let l = Formula::and(mem_fs.clone(), sec.clone());
    let l2 = Formula::and(mem_fs2.clone(), sec2.clone());

    let p_h = and_left(h.clone(), l.clone());
    let p_l = and_right(h.clone(), l.clone());
    let p_mem = hyp_mp(
        &syl(&p_h, &h_mem_fwd)?,
        &syl(&p_l, &and_left(mem_fs.clone(), sec.clone()))?,
    )?;
    let p_sec = hyp_mp(
        &syl(&p_h, &h_sec_fwd)?,
        &syl(&p_l, &and_right(mem_fs.clone(), sec.clone()))?,
    )?;
    let h_l_fwd = uncurry(&hyp_and(&p_mem, &p_sec)?)?;

    let q_h = and_left(h.clone(), l2.clone());
    let q_l = and_right(h.clone(), l2.clone());
    let q_mem = hyp_mp(
        &syl(&q_h, &h_mem_bwd)?,
        &syl(&q_l, &and_left(mem_fs2.clone(), sec2.clone()))?,
    )?;
    let q_sec = hyp_mp(
        &syl(&q_h, &h_sec_bwd)?,
        &syl(&q_l, &and_right(mem_fs2.clone(), sec2.clone()))?,
    )?;
    let h_l_bwd = uncurry(&hyp_and(&q_mem, &q_sec)?)?;

    // ── 4: same members, hence equal ─────────────────────────────────────────
    let (dp_t, dp2_t) = (dp.of(ta.clone()), dp2.of(ta2.clone()));
    let (mem_dp, mem_dp2) =
        (Formula::mem(tf.clone(), dp_t.clone()), Formula::mem(tf.clone(), dp2_t.clone()));

    let dp_at = inst_all(&dp.dprod_def, &[ta.clone(), tf.clone()])?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }
    let dp2_at = inst_all(&dp2.dprod_def, &[ta2.clone(), tf.clone()])?;
    if *dp2_at.concl() != Formula::iff(mem_dp2.clone(), l2) {
        return None
    }

    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&dp_at)?, h.clone()), &h_l_fwd)?,
        &a1i(&iff_mpr(&dp2_at)?, h.clone()),
    )?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&dp2_at)?, h.clone()), &h_l_bwd)?,
        &a1i(&iff_mpr(&dp_at)?, h.clone()),
    )?;
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_f = Thm::mp(
        &Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_dp2))?,
        &Thm::gen(f, &h_iff),
    )?;
    let h_eq = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), dp2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(dp_t, dp2_t))),
        "dprod_ext: unexpected shape"
    );
    Some(gen_all(&[av, av2], &out))
}

/// `⊢ ∀A. ((∀x. (x ∈ A → b(x) = b'(x))) → dprod(A) = dprod'(A))` — the
/// same-domain corollary, the form `pi_cong` will call when only the fibres
/// moved.
///
/// Takes the theorem [`dprod_ext`] produces and instantiates both domains at the
/// same variable, discharging `A = A` by reflexivity — exactly as
/// [`crate::ext::lam_ext_same_domain`] does, and by the same code.
///
/// Returns `None` if `dprod_ext_thm` is not of the shape [`dprod_ext`] produces.
pub fn dprod_ext_same_domain(env: &mut Env, dprod_ext_thm: &Thm) -> Option<Thm> {
    same_domain(env, dprod_ext_thm)
}
