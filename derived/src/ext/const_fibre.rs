//! A dependent product over a constant fibre **is** the function space.
//!
//! # Interface
//!
//! For the [`crate::ext::DProd`] over a unary fibre symbol `b`,
//!
//! ```text
//! ⊢ ∀A ∀B. ((∀x. (x ∈ A → b(x) = B)) → dprod(A) = fs(A,B))   [dprod_const_fibre]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why the checker needs it
//!
//! Lean's `Π` is interpreted two ways: `fs(⟦A⟧,⟦B⟧)` when the body does not
//! mention the binder, `dprod` when it does. Two *equal* Π-types can be
//! interpreted each way — one body mentions the binder vacuously, the other does
//! not — and then congruence has nothing to work with, because the two sides are
//! built by unrelated symbols. This is what bridges them.
//!
//! # The route, and the empty domain
//!
//! It does **not** go through `⋃img(A) = B`. That equation is true only when `A`
//! is inhabited — `⋃img(∅) = ∅` whatever the fibre — so it would force an
//! inhabitation antecedent, and the empty domain is not a case worth losing:
//! nothing in `f ∈ fs(∅,B)` depends on `B` (a function on `∅` is a subset of
//! `prod(∅,B) = ∅` and is total vacuously), so the theorem holds there too, with
//! `B` arbitrary and `⋃img(∅)` nowhere near it.
//!
//! What is used instead is that the function space only constrains a function
//! through its values, so the codomain may be swapped for any set the values
//! happen to land in ([`crate::ext::funspace_retarget`]) — and on an empty
//! domain there are no values, so the swap is unconditional and both directions
//! go through vacuously. The fibre equation is used only pointwise, never as an
//! equation between codomains.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Apply};
use crate::funspace::{Funspace, Product};
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};
use super::shared::{hyp_eq_symm, hyp_leibniz};
use super::dprod::{base_of, is_section, DProd};
use super::app::{app_of_pair, funspace_app_mem};
use super::retarget::{funspace_retarget, values_in};

/// `⊢ ∀A ∀B. ((∀x. (x ∈ A → b(x) = B)) → dprod(A) = fs(A,B))` — a dependent
/// product over a constant fibre **is** the function space.
///
/// This is what lets the checker relate the two interpretations of a Π-type
/// whose body mentions the binder only vacuously: one side is a `dprod` over a
/// fibre symbol, the other a plain `fs`, and no congruence relates them because
/// the head symbols are different and unrelated.
///
/// Both directions run through [`funspace_retarget`], and the fibre equation is
/// used only pointwise:
///
/// * `f ∈ dprod(A)` gives `f ∈ fs(A,⋃img(A))` and `app(f,x) ∈ b(x)` for `x ∈ A`;
///   the hypothesis turns the latter into `app(f,x) ∈ B`, and the codomain is
///   retargeted to `B`.
/// * `f ∈ fs(A,B)` gives `app(f,x) ∈ B` ([`funspace_app_mem`]), hence
///   `app(f,x) ∈ b(x)` — which is the section condition — and hence
///   `app(f,x) ∈ ⋃img(A)`, since `b(x)` is a member of the fibre image; the
///   codomain is retargeted to `⋃img(A)`.
///
/// **No inhabitation antecedent, and the empty domain is included.** The obvious
/// route — `⋃img(A) = B`, then congruence for `fs` — is *false* for `A = ∅`,
/// where `⋃img(∅) = ∅` while `B` is arbitrary; it is avoided entirely, and
/// nothing above ever compares the two codomains as sets. When `A` has no
/// members both directions hold vacuously, which is correct: `fs(∅,B)` is `{∅}`
/// for every `B`.
///
/// `dp` must be the [`DProd`] built over `ap`, `fsp` and the unary fibre symbol
/// `b`, and `p` the product `fsp` was carved out of. All of that is checked: the
/// fibre image's and the product's characteristic theorems are rebuilt from the
/// symbols handed in and compared, so a mismatched stack is refused rather than
/// silently described.
pub fn dprod_const_fibre(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    b: FnSym,
    dp: &DProd,
) -> Option<Thm> {
    if b.arity() != 1 {
        return None
    }
    let app_pair = app_of_pair(env, ap)?;
    let app_mem = funspace_app_mem(env, ap, p, fsp, &app_pair)?;
    let retarget = funspace_retarget(env, ap, p, fsp, &app_pair)?;
    let ext = Thm::ax_extensionality(env);

    let (av, bigb, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tbb, tf) = (Term::var(av), Term::var(bigb), Term::var(f));
    let x = env.fresh_var();
    let tx = Term::var(x);

    // The hypothesis: the fibre is constantly `B` on `A`.
    let bx = Term::apply(b, vec![tx.clone()]);
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), tbb.clone())));

    // The two sets being compared, and the condition `dprod` is defined by.
    let img_t = Term::apply(dp.img, vec![ta.clone()]);
    let u = base_of(ap, dp.img, &ta);
    let fs_b = fsp.of(ta.clone(), tbb.clone());
    let mem_fs_u = Formula::mem(tf.clone(), fsp.of(ta.clone(), u.clone()));
    let mem_fs_b = Formula::mem(tf.clone(), fs_b.clone());
    let sec = is_section(env, ap, b, &ta, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    debug_assert_eq!(sec, Formula::forall(x, sec_body.clone()), "dprod_const_fibre: shape drift");
    let l = Formula::and(mem_fs_u.clone(), sec.clone());

    let dp_t = dp.of(ta.clone());
    let mem_dp = Formula::mem(tf.clone(), dp_t.clone());
    let dp_at = inst_all(&dp.dprod_def, &[ta.clone(), tf.clone()])?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }

    // The two "values land here" hypotheses `funspace_retarget` consumes.
    let vi_b_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), tbb.clone()));
    let vi_u_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), u.clone()));
    debug_assert_eq!(
        Formula::forall(x, vi_b_body.clone()),
        values_in(env, ap, &ta, &tbb, &tf),
        "dprod_const_fibre: shape drift"
    );
    debug_assert_eq!(
        Formula::forall(x, vi_u_body.clone()),
        values_in(env, ap, &ta, &u, &tf),
        "dprod_const_fibre: shape drift"
    );

    // ── ←: a function into `B` is a section of the constant fibration ────────
    let k = Formula::and(h.clone(), mem_fs_b.clone());
    let k_h = and_left(h.clone(), mem_fs_b.clone());
    let k_fs = and_right(h.clone(), mem_fs_b.clone());

    let m = Formula::and(k.clone(), mem_xa.clone());
    let m_k = and_left(k.clone(), mem_xa.clone());
    let m_xa = and_right(k.clone(), mem_xa.clone());

    let am_at = inst_all(&app_mem, &[ta.clone(), tbb.clone(), tf.clone(), tx.clone()])?;
    let m_app_b =
        hyp_mp(&a1i(&am_at, m.clone()), &hyp_and(&syl(&m_k, &k_fs)?, &m_xa)?)?;
    let m_fibre =
        hyp_mp(&syl(&syl(&m_k, &k_h)?, &Thm::ax_inst(h.clone(), tx.clone())?)?, &m_xa)?;
    let w1 = env.fresh_var();
    let m_sec_body = hyp_mp(
        &hyp_leibniz(
            &hyp_eq_symm(env, &m_fibre)?,
            w1,
            &Formula::mem(app_fx.clone(), Term::var(w1)),
        )?,
        &m_app_b,
    )?;
    let k_sec = Thm::mp(
        &Thm::ax_dist(x, k.clone(), sec_body.clone())?,
        &Thm::gen(x, &uncurry(&m_sec_body)?),
    )?;

    // `b(x) ∈ img(A)` for `x ∈ A`, so a value in `b(x)` is a value in `⋃img(A)`.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body = Formula::and(
        Formula::mem(tx2.clone(), ta.clone()),
        Formula::eq(bx.clone(), Term::apply(b, vec![tx2])),
    );
    let img_at = inst_all(&dp.img_ax, &[ta.clone(), bx.clone()])?;
    if *img_at.concl()
        != Formula::iff(
            Formula::mem(bx.clone(), img_t.clone()),
            Formula::exists(x2, img_body.clone()),
        )
    {
        return None
    }
    let m_witness = hyp_and(&m_xa, &a1i(&Thm::eq_refl(bx.clone()), m.clone()))?;
    let m_img = syl(
        &syl(&m_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?,
        &iff_mpr(&img_at)?,
    )?;
    let intro = union_intro(env, &ap.sets, img_t, bx, app_fx.clone()).ok()?;
    let m_app_u = syl(&hyp_and(&m_img, &m_sec_body)?, &intro)?;
    let k_vi_u = Thm::mp(
        &Thm::ax_dist(x, k.clone(), vi_u_body)?,
        &Thm::gen(x, &uncurry(&m_app_u)?),
    )?;

    let rt_u = inst_all(&retarget, &[ta.clone(), tbb.clone(), u.clone(), tf.clone()])?;
    let k_fs_u = hyp_mp(&a1i(&rt_u, k.clone()), &hyp_and(&k_fs, &k_vi_u)?)?;
    let k_dp = hyp_mp(&a1i(&iff_mpr(&dp_at)?, k.clone()), &hyp_and(&k_fs_u, &k_sec)?)?;
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
    let n_app_bx =
        hyp_mp(&syl(&syl(&n_j, &j_sec)?, &Thm::ax_inst(sec, tx.clone())?)?, &n_xa)?;
    let n_fibre = hyp_mp(&syl(&syl(&n_j, &j_h)?, &Thm::ax_inst(h.clone(), tx)?)?, &n_xa)?;
    let w2 = env.fresh_var();
    let n_app_b = hyp_mp(
        &hyp_leibniz(&n_fibre, w2, &Formula::mem(app_fx.clone(), Term::var(w2)))?,
        &n_app_bx,
    )?;
    debug_assert_eq!(
        *n_app_b.concl(),
        Formula::imp(n, Formula::mem(app_fx, tbb.clone())),
        "dprod_const_fibre: the pointwise step has an unexpected shape"
    );
    let j_vi_b =
        Thm::mp(&Thm::ax_dist(x, j.clone(), vi_b_body)?, &Thm::gen(x, &uncurry(&n_app_b)?))?;

    let rt_b = inst_all(&retarget, &[ta.clone(), u, tbb, tf])?;
    let fwd = uncurry(&hyp_mp(&a1i(&rt_b, j.clone()), &hyp_and(&j_fs_u, &j_vi_b)?)?)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let all_f = Thm::mp(
        &Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_fs_b))?,
        &Thm::gen(f, &hyp_and(&fwd, &bwd)?),
    )?;
    let out = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), fs_b.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(dp_t, fs_b)),
        "dprod_const_fibre: unexpected shape"
    );
    Some(gen_all(&[av, bigb], &out))
}
