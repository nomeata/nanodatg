//! Lean's lambda typing rule: a lambda graph is a member of the dependent
//! product over its fibres.
//!
//! # Interface
//!
//! Write `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }` for the graph
//! [`crate::funcs::lambda`] builds over a unary body symbol `t`, and
//!
//! ```text
//! body_in(A,C)       :=  ∀x. (x ∈ A → t(x) ∈ C)      [body_in]
//! body_in_fibre(A)   :=  ∀x. (x ∈ A → t(x) ∈ b(x))   [body_in_fibre]
//! ```
//!
//! Then the exports are
//!
//! ```text
//! ⊢ ∀A ∀C. (body_in(A,C) → lam(A) ∈ fs(A,C))     [lam_in_funspace]
//! ⊢ ∀A. (body_in_fibre(A) → lam(A) ∈ dprod(A))   [lam_in_dprod]
//! ```
//!
//! the second being the rule itself. **Neither carries an inhabitation
//! antecedent or any condition on `A`**: at `A := ∅` both hypotheses are vacuous
//! and both conclusions hold. Callers need none of the derivations below.
//!
//! # The shape of the argument
//!
//! `dprod_ax` is unconditional, so [`lam_in_dprod`] reduces to the two clauses
//! of `L`:
//!
//!   1. `lam(A) ∈ fs(A, ⋃img(A))`, i.e. the graph really is a function;
//!   2. `∀x ∈ A. app(lam(A), x) ∈ b(x)`, which
//!      [`crate::funcs::beta_conditional`] turns into the hypothesis itself.
//!
//! Clause 1 is the work, and it is worth stating on its own because nothing in
//! it mentions the fibres: that is [`lam_in_funspace`], for *any* codomain the
//! body lands in, and [`lam_in_dprod`] applies it at `C := ⋃img(A)`, which the
//! hypothesis reaches because `b(x)` is a member of the fibre image whenever
//! `x ∈ A`.
//!
//! The three clauses of `isfun(lam(A))` come from different places. Totality is
//! the graph's characteristic axiom read forwards — `⟨x,t(x)⟩ ∈ lam(A)` for
//! `x ∈ A`, witnessed by `x` itself. The subset clause is the same axiom read
//! backwards: a member of the graph *is* a pair `⟨x,t(x)⟩` with `x ∈ A`.
//! Single-valuedness is the only one that needs [`crate::pairs::opair_inj`], and
//! it is the only one that needs **no hypothesis at all** — a graph over a
//! function symbol cannot relate one point to two values whatever the codomain.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Apply};
use crate::funspace::{is_single_valued, Funspace, Product};
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, mpd_const, syl, uncurry,
};
use super::shared::{discharge, hyp_eq_symm, hyp_leibniz, isfun_parts};
use super::dprod::{base_of, is_section, DProd};

/// `∀x. (x ∈ a → t(x) ∈ c)` — the body lands in `c` at every point of `a`.
///
/// The hypothesis [`lam_in_funspace`] consumes. Note this is *not*
/// [`crate::ext::values_in`]: that one speaks of `app(f,x)` for a function `f` given as a
/// set, this one of `t(x)` for the body symbol the graph is built from. The two
/// meet only through beta reduction.
pub fn body_in(env: &mut Env, t: FnSym, a: &Term, c: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(Term::apply(t, vec![tx]), c.clone()),
        ),
    )
}

/// `∀x. (x ∈ a → t(x) ∈ b(x))` — the body lands in the *fibre*, pointwise.
///
/// The hypothesis of Lean's lambda typing rule, and what [`lam_in_dprod`]
/// consumes. The dependent counterpart of [`body_in`].
pub fn body_in_fibre(env: &mut Env, t: FnSym, b: FnSym, a: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(Term::apply(t, vec![tx.clone()]), Term::apply(b, vec![tx])),
        ),
    )
}

/// `⊢ ⟨p,q⟩ ∈ lam(a) → q = t(p)` — the graph relates `p` to nothing but `t(p)`.
///
/// A member of the graph is `⟨u,t(u)⟩` for some `u ∈ a`, and injectivity of the
/// Kuratowski pair gives `p = u` and `q = t(u)` at once; congruence for `t`
/// closes the gap. The same argument [`crate::funspace::identity_graph`] runs
/// for the identity, with `t` in place of the diagonal.
///
/// `lam_ax` is *checked* against the shape [`crate::funcs::lambda`] produces for
/// `t`: a mismatched pair would still be sound but would describe the wrong
/// graph, so it returns `None`.
#[allow(clippy::too_many_arguments)]
fn lam_pair_val(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    a: &Term,
    pt: &Term,
    q: &Term,
) -> Option<Thm> {
    let lam_a = Term::apply(lam, vec![a.clone()]);
    let pair_pq = ap.sets.pair(pt.clone(), q.clone());
    let at_pair = inst_all(lam_ax, &[a.clone(), pair_pq.clone()])?;

    let u = env.fresh_var();
    let tu = Term::var(u);
    let tu_val = Term::apply(t, vec![tu.clone()]);
    let mem_ua = Formula::mem(tu.clone(), a.clone());
    let eq_pairs = Formula::eq(pair_pq.clone(), ap.sets.pair(tu.clone(), tu_val.clone()));
    let f = Formula::and(mem_ua.clone(), eq_pairs.clone());
    if *at_pair.concl()
        != Formula::iff(Formula::mem(pair_pq, lam_a), Formula::exists(u, f.clone()))
    {
        return None
    }

    let inj = inst_all(&ap.pair_inj, &[pt.clone(), q.clone(), tu.clone(), tu_val.clone()])?;
    let f_conj = syl(&and_right(mem_ua, eq_pairs), &inj)?;
    let (e_pu, e_qt) = (Formula::eq(pt.clone(), tu.clone()), Formula::eq(q.clone(), tu_val.clone()));
    let f_pu = syl(&f_conj, &and_left(e_pu.clone(), e_qt.clone()))?;
    let f_qt = syl(&f_conj, &and_right(e_pu, e_qt))?;

    // `p = u → t(p) = t(u)`, turned around, carries `q = t(u)` to `q = t(p)`.
    let tp_val = Term::apply(t, vec![pt.clone()]);
    let w = env.fresh_var();
    let cong = mpd_const(
        &Thm::eq_leibniz(
            pt.clone(),
            tu.clone(),
            w,
            Formula::eq(tp_val.clone(), Term::apply(t, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(tp_val.clone()),
    )?;
    let f_back = syl(&syl(&f_pu, &cong)?, &eq_symm_imp(env, tp_val.clone(), tu_val.clone()))?;
    let w2 = env.fresh_var();
    let carry =
        Thm::eq_leibniz(tu_val, tp_val.clone(), w2, Formula::eq(q.clone(), Term::var(w2)));
    let f_goal = hyp_mp(&hyp_mp(&a1i(&carry, f), &f_back)?, &f_qt)?;

    let goal = Formula::eq(q.clone(), tp_val);
    syl(&iff_mp(&at_pair)?, &exists_elim_imp(u, &Thm::gen(u, &f_goal), &goal)?)
}

/// `⊢ sv(lam(a))` — a lambda graph is single-valued, **with no hypothesis**.
///
/// Two applications of [`lam_pair_val`]: both values at `x` equal `t(x)`, hence
/// each other. Nothing here mentions a codomain, which is why this clause
/// survives the codomain being chosen only later.
fn lam_single_valued(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    a: &Term,
) -> Option<Thm> {
    let lam_a = Term::apply(lam, vec![a.clone()]);
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));
    let tx_val = Term::apply(t, vec![tx.clone()]);

    let m1 = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), lam_a.clone());
    let m2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), lam_a.clone());
    let h = Formula::and(m1.clone(), m2.clone());

    let e1 = lam_pair_val(env, ap, t, lam, lam_ax, a, &tx, &ty)?;
    let e2 = lam_pair_val(env, ap, t, lam, lam_ax, a, &tx, &ty2)?;
    let h_y1 = syl(&and_left(m1.clone(), m2.clone()), &e1)?;
    let h_y2 = syl(&and_right(m1, m2), &e2)?;

    let h_back = syl(&h_y2, &eq_symm_imp(env, ty2.clone(), tx_val.clone()))?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(tx_val, ty2, w, Formula::eq(ty, Term::var(w)));
    let out = gen_all(&[x, y, y2], &hyp_mp(&hyp_mp(&a1i(&leib, h), &h_back)?, &h_y1)?);
    debug_assert_eq!(
        *out.concl(),
        is_single_valued(env, &ap.sets, &lam_a),
        "lam_single_valued: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀A ∀C. ((∀x. (x ∈ A → t(x) ∈ C)) → lam(A) ∈ fs(A,C))` — a lambda graph is
/// a function into any codomain its body lands in.
///
/// All three clauses of `isfun`:
///
/// * **subset** — a member of `lam(A)` is a pair `⟨x,t(x)⟩` with `x ∈ A`, and
///   the hypothesis puts `t(x)` in `C`, so the pair is in `prod(A,C)`;
/// * **totality** — `⟨x,t(x)⟩ ∈ lam(A)` for every `x ∈ A`, witnessed by `x`
///   itself in the graph's characteristic axiom, and again `t(x) ∈ C`;
/// * **single-valuedness** — [`lam_single_valued`], which needs no hypothesis.
///
/// The hypothesis is used only in the first two, and only through `t(x) ∈ C`.
/// There is **no inhabitation antecedent and no condition on `A`**: on an empty
/// domain all three clauses hold vacuously, so this says `lam(∅) ∈ fs(∅,C)` for
/// every `C`.
///
/// `lam`/`lam_ax` must be the graph symbol and characteristic theorem
/// [`crate::funcs::lambda`] produces for the unary body symbol `t`, `p` the
/// product `fsp` was carved out of, and `ap` the application apparatus over the
/// same [`crate::funcs::Sets`]. All of that is checked rather than assumed.
pub fn lam_in_funspace(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
) -> Option<Thm> {
    if t.arity() != 1 || lam.arity() != 1 {
        return None
    }
    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let lam_t = Term::apply(lam, vec![ta.clone()]);

    let x = env.fresh_var();
    let tx = Term::var(x);
    let tx_val = Term::apply(t, vec![tx.clone()]); // t(x)
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone()); // ⟨x,t(x)⟩
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    // The hypothesis, rebuilt at our own `x` so that it can be opened.
    let h_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), tc.clone()));
    let h = Formula::forall(x, h_body.clone());
    debug_assert_eq!(h, body_in(env, t, &ta, &tc), "lam_in_funspace: shape drift");

    let (isfun, sub, total, sv) = isfun_parts(env, ap, p, &ta, &tc, &lam_t)?;

    // ── Single-valued, outright ──────────────────────────────────────────────
    let sv_thm = lam_single_valued(env, ap, t, lam, lam_ax, &ta)?;
    if *sv_thm.concl() != sv {
        return None
    }
    let h_sv = a1i(&sv_thm, h.clone());

    // ── Total on `A`, with `t(x)` as the value at `x` ────────────────────────
    let y = env.fresh_var();
    let ty = Term::var(y);
    let tot_body = Formula::and(
        Formula::mem(ty.clone(), tc.clone()),
        Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), lam_t.clone()),
    );
    if total
        != Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::exists(y, tot_body.clone())))
    {
        return None
    }

    let k = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_val = hyp_mp(&syl(&k_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &k_xa)?;

    // `⟨x,t(x)⟩ ∈ lam(A)`, by taking the image's witness to be `x` itself.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body = Formula::and(
        Formula::mem(tx2.clone(), ta.clone()),
        Formula::eq(pair_x.clone(), ap.sets.pair(tx2.clone(), Term::apply(t, vec![tx2]))),
    );
    let lam_at_pair = inst_all(lam_ax, &[ta.clone(), pair_x.clone()])?;
    if *lam_at_pair.concl()
        != Formula::iff(
            Formula::mem(pair_x.clone(), lam_t.clone()),
            Formula::exists(x2, img_body.clone()),
        )
    {
        return None
    }
    let k_witness = hyp_and(&k_xa, &a1i(&Thm::eq_refl(pair_x.clone()), k.clone()))?;
    let k_pair = syl(
        &syl(&k_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?,
        &iff_mpr(&lam_at_pair)?,
    )?;

    let k_ex = syl(
        &hyp_and(&k_val, &k_pair)?,
        &exists_intro_imp(y, tot_body.clone(), tx_val.clone())?,
    )?;
    let h_total = Thm::mp(
        &Thm::ax_dist(x, h.clone(), Formula::imp(mem_xa.clone(), Formula::exists(y, tot_body)))?,
        &Thm::gen(x, &uncurry(&k_ex)?),
    )?;
    debug_assert_eq!(
        *h_total.concl(),
        Formula::imp(h.clone(), total),
        "lam_in_funspace: the totality clause has an unexpected shape"
    );

    // ── The graph sits inside `prod(A,C)` ────────────────────────────────────
    let z = env.fresh_var();
    let tz = Term::var(z);
    let mem_z_lam = Formula::mem(tz.clone(), lam_t.clone());
    let mem_z_prod = Formula::mem(tz.clone(), p.of(ta.clone(), tc.clone()));
    if sub != Formula::forall(z, Formula::imp(mem_z_lam.clone(), mem_z_prod.clone())) {
        return None
    }

    let eq_z_pair = Formula::eq(tz.clone(), pair_x.clone());
    let z_body = Formula::and(mem_xa.clone(), eq_z_pair.clone());
    let lam_at_z = inst_all(lam_ax, &[ta.clone(), tz.clone()])?;
    if *lam_at_z.concl() != Formula::iff(mem_z_lam.clone(), Formula::exists(x, z_body.clone())) {
        return None
    }

    let m = Formula::and(h.clone(), mem_z_lam.clone());
    let m_h = and_left(h.clone(), mem_z_lam.clone());
    let m_zl = and_right(h.clone(), mem_z_lam.clone());
    let m_ex = syl(&m_zl, &iff_mp(&lam_at_z)?)?;

    let n_m = and_left(m.clone(), z_body.clone());
    let n_body = and_right(m.clone(), z_body.clone());
    let n_xa = syl(&n_body, &and_left(mem_xa.clone(), eq_z_pair.clone()))?;
    let n_zeq = syl(&n_body, &and_right(mem_xa.clone(), eq_z_pair))?;
    let n_h = syl(&n_m, &m_h)?;
    let n_val = hyp_mp(&syl(&n_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &n_xa)?;

    let inner_body = Formula::and(
        Formula::mem(ty.clone(), tc.clone()),
        Formula::eq(tz.clone(), ap.sets.pair(tx.clone(), ty.clone())),
    );
    let outer = Formula::and(mem_xa.clone(), Formula::exists(y, inner_body.clone()));
    let prod_at_z = inst_all(&p.prod_ax, &[ta.clone(), tc.clone(), tz.clone()])?;
    if *prod_at_z.concl() != Formula::iff(mem_z_prod.clone(), Formula::exists(x, outer.clone())) {
        return None
    }

    let n_inner =
        syl(&hyp_and(&n_val, &n_zeq)?, &exists_intro_imp(y, inner_body, tx_val)?)?;
    let n_goal = syl(
        &syl(&hyp_and(&n_xa, &n_inner)?, &exists_intro_imp(x, outer, tx)?)?,
        &iff_mpr(&prod_at_z)?,
    )?;
    let m_goal = discharge(x, &m_ex, &n_goal)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_z_lam, mem_z_prod))?,
        &Thm::gen(z, &uncurry(&m_goal)?),
    )?;
    debug_assert_eq!(
        *h_sub.concl(),
        Formula::imp(h.clone(), sub),
        "lam_in_funspace: the subset clause has an unexpected shape"
    );

    // ── The three clauses, reassembled ───────────────────────────────────────
    let fs_t = fsp.of(ta.clone(), tc.clone());
    let mem_fs = Formula::mem(lam_t.clone(), fs_t.clone());
    let fs_at = inst_all(&fsp.fs_ax, &[ta.clone(), tc.clone(), lam_t])?;
    if *fs_at.concl() != Formula::iff(mem_fs.clone(), isfun) {
        return None
    }
    let out = syl(&hyp_and(&h_sub, &hyp_and(&h_total, &h_sv)?)?, &iff_mpr(&fs_at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, mem_fs),
        "lam_in_funspace: unexpected shape"
    );
    Some(gen_all(&[av, cv], &out))
}

/// `⊢ ∀A. ((∀x. (x ∈ A → t(x) ∈ b(x))) → lam(A) ∈ dprod(A))` — **Lean's lambda
/// typing rule**: a lambda whose body lands in the fibre pointwise is a member
/// of the dependent product.
///
/// `dprod_ax` is unconditional, so this reduces to the two clauses of `L`:
///
/// * `lam(A) ∈ fs(A, ⋃img(A))` — [`lam_in_funspace`] at `C := ⋃img(A)`, whose
///   hypothesis is reached from this one because `b(x)` is a member of the fibre
///   image whenever `x ∈ A`, so a value in `b(x)` is a value in `⋃img(A)`;
/// * `∀x ∈ A. app(lam(A),x) ∈ b(x)` — [`crate::funcs::beta_conditional`] turns
///   `app(lam(A),x)` into `t(x)` on the domain, and the hypothesis is then
///   applied verbatim. The membership antecedent beta reduction carries is
///   exactly the one the section condition supplies.
///
/// **No inhabitation antecedent and no condition on `A`**: `lam(∅) ∈ dprod(∅)`
/// holds with the hypothesis vacuous.
///
/// `beta` must be what [`crate::funcs::beta_conditional`] produces for `t` and
/// `lam`, and `lam_fs` what [`lam_in_funspace`] produces for the same pair;
/// `dp` must be the [`DProd`] built over `ap`, `fsp` and the unary fibre symbol
/// `b`. All of that is checked, so a mismatched stack is refused rather than
/// silently described.
#[allow(clippy::too_many_arguments)]
pub fn lam_in_dprod(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    t: FnSym,
    lam: FnSym,
    b: FnSym,
    dp: &DProd,
    beta: &Thm,
    lam_fs: &Thm,
) -> Option<Thm> {
    if t.arity() != 1 || lam.arity() != 1 || b.arity() != 1 {
        return None
    }
    let av = env.fresh_var();
    let ta = Term::var(av);
    let lam_t = Term::apply(lam, vec![ta.clone()]);
    let img_t = Term::apply(dp.img, vec![ta.clone()]);
    let u = base_of(ap, dp.img, &ta);

    let x = env.fresh_var();
    let tx = Term::var(x);
    let tx_val = Term::apply(t, vec![tx.clone()]); // t(x)
    let bx = Term::apply(b, vec![tx.clone()]); // b(x)
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    let h_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), bx.clone()));
    let h = Formula::forall(x, h_body.clone());
    debug_assert_eq!(h, body_in_fibre(env, t, b, &ta), "lam_in_dprod: shape drift");

    let k = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_fibre = hyp_mp(&syl(&k_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &k_xa)?;

    // ── The values land in `⋃img(A)`, since `b(x) ∈ img(A)` ──────────────────
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
    let k_witness = hyp_and(&k_xa, &a1i(&Thm::eq_refl(bx.clone()), k.clone()))?;
    let k_img = syl(
        &syl(&k_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?,
        &iff_mpr(&img_at)?,
    )?;
    let intro = union_intro(env, &ap.sets, img_t, bx.clone(), tx_val.clone())?;
    let k_in_u = syl(&hyp_and(&k_img, &k_fibre)?, &intro)?;

    let u_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), u.clone()));
    let h_body_u =
        Thm::mp(&Thm::ax_dist(x, h.clone(), u_body.clone())?, &Thm::gen(x, &uncurry(&k_in_u)?))?;
    debug_assert_eq!(
        *h_body_u.concl(),
        Formula::imp(h.clone(), body_in(env, t, &ta, &u)),
        "lam_in_dprod: the codomain step has an unexpected shape"
    );

    let fs_t = fsp.of(ta.clone(), u.clone());
    let mem_fs = Formula::mem(lam_t.clone(), fs_t.clone());
    let lam_fs_at = inst_all(lam_fs, &[ta.clone(), u.clone()])?;
    if *lam_fs_at.concl() != Formula::imp(Formula::forall(x, u_body), mem_fs.clone()) {
        return None
    }
    let h_fs = syl(&h_body_u, &lam_fs_at)?;

    // ── The section condition, from beta reduction ───────────────────────────
    let app_t = ap.apply(lam_t.clone(), tx.clone());
    let beta_at = inst_all(beta, &[ta.clone(), tx.clone()])?;
    if *beta_at.concl()
        != Formula::imp(mem_xa.clone(), Formula::eq(app_t.clone(), tx_val.clone()))
    {
        return None
    }
    let k_beta = syl(&k_xa, &beta_at)?;
    let w = env.fresh_var();
    let k_sec_body = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &k_beta)?, w, &Formula::mem(Term::var(w), bx.clone()))?,
        &k_fibre,
    )?;
    let sec_body = Formula::imp(mem_xa, Formula::mem(app_t, bx));
    let sec = is_section(env, ap, b, &ta, &lam_t);
    if sec != Formula::forall(x, sec_body.clone()) {
        return None
    }
    let h_sec =
        Thm::mp(&Thm::ax_dist(x, h.clone(), sec_body)?, &Thm::gen(x, &uncurry(&k_sec_body)?))?;

    // ── `L(lam(A))` is exactly what `dprod` is defined by ────────────────────
    let dp_t = dp.of(ta.clone());
    let mem_dp = Formula::mem(lam_t, dp_t);
    let dp_at = inst_all(&dp.dprod_def, &[ta, Term::apply(lam, vec![Term::var(av)])])?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), Formula::and(mem_fs, sec)) {
        return None
    }
    let out = hyp_mp(&a1i(&iff_mpr(&dp_at)?, h.clone()), &hyp_and(&h_fs, &h_sec)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, mem_dp),
        "lam_in_dprod: unexpected shape"
    );
    Some(Thm::gen(av, &out))
}
