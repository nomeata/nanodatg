//! **Lean's lambda typing rule**, with a parameter prefix on the lambda and an
//! independent one on the fibre.
//!
//! # Interface
//!
//! Write `lam(p⃗,A) = { ⟨x, t(p⃗,x)⟩ : x ∈ A }` for the graph
//! [`crate::funcs::lambda_n`] builds over a body symbol `t` of arity `k+1`, and
//! let `b` be a fibre symbol of arity `k'+1` with `img`/`dprod` the image and
//! dependent product [`super::dprod_n`] builds over it. The exports are
//!
//! ```text
//! body_in_n(p⃗,A,C)  :=  ∀x. (x ∈ A → t(p⃗,x) ∈ C)             [body_in_n]
//!
//! ⊢ ⟨q₀,q⟩ ∈ lam(p⃗,a) → q = t(p⃗,q₀)                        [lam_pair_val_n]
//! ⊢ sv(lam(p⃗,a))                                        [lam_single_valued_n]
//! ⊢ ∀p⃗ ∀A ∀C. (body_in_n(p⃗,A,C) → lam(p⃗,A) ∈ fs(A,C))
//!                                                          [lam_in_funspace_n]
//! ⊢ ∀p⃗ ∀q⃗ ∀A. ((∀x. (x ∈ A → t(p⃗,x) ∈ b(q⃗,x))) → lam(p⃗,A) ∈ dprod(q⃗,A))
//!                                                             [lam_in_dprod_n]
//! ```
//!
//! the last being the rule itself. `sv` is
//! [`crate::funspace::is_single_valued`], and the first two are stated for a
//! *given* prefix `p⃗`, domain `a` and points `q₀`/`q`, since that is how the
//! last two consume them.
//!
//! **No inhabitation antecedent and no condition on `A`**: at `A := ∅` all
//! three clauses of `isfun` hold vacuously, and `lam(p⃗,∅) ∈ dprod(q⃗,∅)` holds
//! with the hypothesis vacuous. Callers need nothing below these statements.
//!
//! Everything handed in is *checked* rather than assumed. `lam_ax` must be what
//! [`crate::funcs::lambda_n`] produces for `t`; in [`lam_in_dprod_n`], `beta`
//! must be what [`crate::funcs::beta_conditional_n`] produces for the same pair
//! and `lam_fs` what [`lam_in_funspace_n`] does, and `img`/`dprod` and their
//! axioms what [`super::image_symbol_n`]/[`super::dprod_symbol_n`] produce for
//! `b`. A mismatched stack is refused with `None` rather than silently
//! described.
//!
//! **And every theorem handed in must be unconditional.** A [`Thm`] is a
//! sequent `Γ ⊢ φ`, so the shape pins above — which all compare `concl()` —
//! say nothing about `Γ`, while [`Thm::mp`] silently unions the two sides'
//! `Γ`s. A `Thm::assume` of exactly the closed formula [`crate::funcs::lambda_n`]
//! produces would pass every pin, every `gen` would succeed, and the exports
//! above would come back as `{φ} ⊢ ∀p⃗ ∀A ∀C. (…)` out of functions whose
//! headers say `⊢` outright. So each entry additionally requires
//! [`crate::all_unconditional`] of the theorems it consumes — the caller's, and
//! the [`Apply`]/[`Product`]/[`Funspace`] fields that are themselves documented
//! `⊢ …`. This is not a test-only concern: `mini/src/interp.rs` calls
//! [`lam_in_funspace_n`] in shipped code, `mini` holds `Γ`-carrying theorems by
//! design, and it is exempt from the boundary rule that keeps `Thm::assume` out
//! of shipped code.
//!
//! # Why the prefixes, and why a second copy of [`super::lam_typing`]
//!
//! A Lean lambda body and a Lean `Π` body are both open expressions, so each
//! decomposes into a skeleton plus its maximal binder-free subterms, and the
//! symbol built from it carries one parameter per hole in addition to the
//! binder. A symbol's arity is fixed, so [`super::lam_typing`] cannot be
//! *instantiated* at a prefixed body — it has to be re-run with the prefixes
//! threaded through the argument lists. Nothing else changes, and **at
//! `k = k' = 0` this is [`super::lam_typing`] on the nose**.
//!
//! [`lam_in_dprod_n`] threads **two independent** prefixes: the lambda's `p⃗`
//! and the `Π`'s `q⃗` are the holes of two unrelated skeletons, and there is no
//! reason for them even to have the same length.
//!
//! Read [`super::lam_typing`]'s header for the shape of the argument — which of
//! the three clauses of `isfun` comes from where, and why single-valuedness is
//! the one that needs no hypothesis at all.
//!
//! Nothing here is trusted. A mistake yields `None` — hence a reported gap —
//! rather than a false theorem, and every conclusion is checked against the
//! statement above in release as well as debug.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{union_intro, Apply};
use crate::funspace::{is_single_valued, Funspace, Product};
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, mpd_const, syl, uncurry,
};

use super::dprod_n::{inst_at, section_n, sym_at};
use super::shared::{discharge, hyp_eq_symm, hyp_leibniz, isfun_parts};

/// `∀x. (x ∈ a → t(p⃗,x) ∈ c)` — the body lands in `c` at every point of `a`,
/// at a **given** parameter prefix.
///
/// The hypothesis [`lam_in_funspace_n`] consumes, once its own `∀p⃗ ∀A ∀C` have
/// been instantiated. The `k = 0` case is [`super::body_in`], and this exists
/// for the same reason that one does: a caller has to *build* the antecedent to
/// discharge it, and rebuilding it by hand at the call site is a second chance
/// to disagree about which argument list `t` takes.
pub fn body_in_n(env: &mut Env, t: FnSym, pts: &[Term], a: &Term, c: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(sym_at(t, pts, tx), c.clone()),
        ),
    )
}

/// `⊢ ⟨q₀,q⟩ ∈ lam(p⃗,a) → q = t(p⃗,q₀)` — the graph relates `q₀` to nothing but
/// `t(p⃗,q₀)`.
///
/// The `k = 0` case is [`super::lam_typing`]'s private `lam_pair_val`.
/// `lam_ax` is *checked* against the shape [`crate::funcs::lambda_n`] produces
/// for `t`, and it — like [`Apply::pair_inj`], the one apparatus theorem this
/// consumes — must be **unconditional**; see the module header for why the
/// shape pin alone is not enough.
#[allow(clippy::too_many_arguments)]
pub fn lam_pair_val_n(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    pts: &[Term],
    a: &Term,
    pt: &Term,
    q: &Term,
) -> Option<Thm> {
    // The pins below all read `concl()`, which says nothing about the sequent's
    // `Γ`; the `mp`s that follow would union it into a result labelled `⊢`.
    if !crate::all_unconditional(&[lam_ax, &ap.pair_inj]) {
        return None
    }
    let lam_a = sym_at(lam, pts, a.clone());
    let pair_pq = ap.sets.pair(pt.clone(), q.clone());
    let at_pair = inst_all(lam_ax, &inst_at(pts, a, &pair_pq))?;

    let u = env.fresh_var();
    let tu = Term::var(u);
    let tu_val = sym_at(t, pts, tu.clone());
    let mem_ua = Formula::mem(tu.clone(), a.clone());
    let eq_pairs = Formula::eq(pair_pq.clone(), ap.sets.pair(tu.clone(), tu_val.clone()));
    let f = Formula::and(mem_ua.clone(), eq_pairs.clone());
    if *at_pair.concl() != Formula::iff(Formula::mem(pair_pq, lam_a), Formula::exists(u, f.clone())) {
        return None
    }

    let inj = inst_all(&ap.pair_inj, &[pt.clone(), q.clone(), tu.clone(), tu_val.clone()])?;
    let f_conj = syl(&and_right(mem_ua, eq_pairs), &inj)?;
    let (e_pu, e_qt) = (Formula::eq(pt.clone(), tu.clone()), Formula::eq(q.clone(), tu_val.clone()));
    let f_pu = syl(&f_conj, &and_left(e_pu.clone(), e_qt.clone()))?;
    let f_qt = syl(&f_conj, &and_right(e_pu, e_qt))?;

    // `q₀ = u → t(p⃗,q₀) = t(p⃗,u)`, turned around, carries `q = t(p⃗,u)` to
    // `q = t(p⃗,q₀)`.
    let tp_val = sym_at(t, pts, pt.clone());
    let w = env.fresh_var();
    let cong = mpd_const(
        &Thm::eq_leibniz(
            pt.clone(),
            tu.clone(),
            w,
            Formula::eq(tp_val.clone(), sym_at(t, pts, Term::var(w))),
        ),
        &Thm::eq_refl(tp_val.clone()),
    )?;
    let f_back = syl(&syl(&f_pu, &cong)?, &eq_symm_imp(env, tp_val.clone(), tu_val.clone()))?;
    let w2 = env.fresh_var();
    let carry = Thm::eq_leibniz(tu_val, tp_val.clone(), w2, Formula::eq(q.clone(), Term::var(w2)));
    let f_goal = hyp_mp(&hyp_mp(&a1i(&carry, f), &f_back)?, &f_qt)?;

    let goal = Formula::eq(q.clone(), tp_val);
    syl(&iff_mp(&at_pair)?, &exists_elim_imp(u, &Thm::gen(u, &f_goal), &goal)?)
}

/// `⊢ sv(lam(p⃗,a))` — a lambda graph is single-valued, **with no hypothesis**.
///
/// The `k = 0` case is [`super::lam_typing`]'s private `lam_single_valued`. The
/// conclusion is compared against
/// [`crate::funspace::is_single_valued`]'s own assembly of the statement, in
/// release as well as debug — and `lam_ax` is additionally required to be
/// **unconditional**, since "with no hypothesis" is exactly what the header
/// claims and a conclusion pin cannot see the sequent's `Γ`.
pub fn lam_single_valued_n(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    pts: &[Term],
    a: &Term,
) -> Option<Thm> {
    // Redundant with [`lam_pair_val_n`]'s own guard, and stated anyway: this is
    // a public entry, and the header's "with no hypothesis" has to be true of
    // the sequent and not only of the formula.
    if !crate::all_unconditional(&[lam_ax, &ap.pair_inj]) {
        return None
    }
    let lam_a = sym_at(lam, pts, a.clone());
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));
    let tx_val = sym_at(t, pts, tx.clone());

    let m1 = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), lam_a.clone());
    let m2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), lam_a.clone());
    let h = Formula::and(m1.clone(), m2.clone());

    let e1 = lam_pair_val_n(env, ap, t, lam, lam_ax, pts, a, &tx, &ty)?;
    let e2 = lam_pair_val_n(env, ap, t, lam, lam_ax, pts, a, &tx, &ty2)?;
    let h_y1 = syl(&and_left(m1.clone(), m2.clone()), &e1)?;
    let h_y2 = syl(&and_right(m1, m2), &e2)?;

    let h_back = syl(&h_y2, &eq_symm_imp(env, ty2.clone(), tx_val.clone()))?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(tx_val, ty2, w, Formula::eq(ty, Term::var(w)));
    let out = gen_all(&[x, y, y2], &hyp_mp(&hyp_mp(&a1i(&leib, h), &h_back)?, &h_y1)?);
    // Not a `debug_assert`: this is the statement the caller relies on.
    let want = is_single_valued(env, &ap.sets, &lam_a);
    (*out.concl() == want).then_some(out)
}

/// `⊢ ∀p⃗ ∀A ∀C. ((∀x. (x ∈ A → t(p⃗,x) ∈ C)) → lam(p⃗,A) ∈ fs(A,C))` — a lambda
/// graph is a function into any codomain its body lands in.
///
/// The `k = 0` case is [`super::lam_in_funspace`]; see there for the argument.
/// Only the argument lists of `t` and `lam` differ.
///
/// **No inhabitation antecedent and no condition on `A`**: on an empty domain
/// all three clauses of `isfun` hold vacuously.
///
/// `lam_ax` and the apparatus theorems this consumes — [`Apply::pair_inj`],
/// [`Product::prod_ax`], [`Funspace::fs_ax`] — must all be **unconditional**.
/// That guard is load-bearing rather than decorative: `mini/src/interp.rs`'s
/// `lam_typing_fs` calls this entry in shipped code with a caller-supplied
/// `lam_ax`, `mini` traffics in `Γ ⊢ φ` sequents by design, and it is exempt
/// from the boundary rule that keeps [`Thm::assume`] out of shipped code. A
/// hypothetical `lam_ax` with the *right* conclusion passes every shape pin in
/// this function, and the result would then be `Γ ⊢ ∀p⃗ ∀A ∀C. (…)` under a
/// header that promises `⊢`.
pub fn lam_in_funspace_n(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[lam_ax, &ap.pair_inj, &p.prod_ax, &fsp.fs_ax]) {
        return None
    }
    let k = (t.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 {
        return None
    }
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|v| Term::var(*v)).collect();

    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let lam_t = sym_at(lam, &pts, ta.clone());

    let x = env.fresh_var();
    let tx = Term::var(x);
    let tx_val = sym_at(t, &pts, tx.clone()); // t(p⃗,x)
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone()); // ⟨x,t(p⃗,x)⟩
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    // The hypothesis, rebuilt at our own `x` so that it can be opened.
    let h_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), tc.clone()));
    let h = Formula::forall(x, h_body);
    debug_assert_eq!(h, body_in_n(env, t, &pts, &ta, &tc), "lam_in_funspace_n: shape drift");

    let (isfun, sub, total, sv) = isfun_parts(env, ap, p, &ta, &tc, &lam_t)?;

    // ── Single-valued, outright ──────────────────────────────────────────────
    let sv_thm = lam_single_valued_n(env, ap, t, lam, lam_ax, &pts, &ta)?;
    if *sv_thm.concl() != sv {
        return None
    }
    let h_sv = a1i(&sv_thm, h.clone());

    // ── Total on `A`, with `t(p⃗,x)` as the value at `x` ──────────────────────
    let y = env.fresh_var();
    let ty = Term::var(y);
    let tot_body = Formula::and(
        Formula::mem(ty.clone(), tc.clone()),
        Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), lam_t.clone()),
    );
    if total != Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::exists(y, tot_body.clone()))) {
        return None
    }

    let kf = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_val = hyp_mp(&syl(&k_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &k_xa)?;

    // `⟨x,t(p⃗,x)⟩ ∈ lam(p⃗,A)`, by taking the image's witness to be `x` itself.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body = Formula::and(
        Formula::mem(tx2.clone(), ta.clone()),
        Formula::eq(pair_x.clone(), ap.sets.pair(tx2.clone(), sym_at(t, &pts, tx2))),
    );
    let lam_at_pair = inst_all(lam_ax, &inst_at(&pts, &ta, &pair_x))?;
    if *lam_at_pair.concl()
        != Formula::iff(Formula::mem(pair_x.clone(), lam_t.clone()), Formula::exists(x2, img_body.clone()))
    {
        return None
    }
    let k_witness = hyp_and(&k_xa, &a1i(&Thm::eq_refl(pair_x.clone()), kf.clone()))?;
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
    if *h_total.concl() != Formula::imp(h.clone(), total) {
        return None
    }

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
    let lam_at_z = inst_all(lam_ax, &inst_at(&pts, &ta, &tz))?;
    if *lam_at_z.concl() != Formula::iff(mem_z_lam.clone(), Formula::exists(x, z_body.clone())) {
        return None
    }

    let m = Formula::and(h.clone(), mem_z_lam.clone());
    let m_h = and_left(h.clone(), mem_z_lam.clone());
    let m_zl = and_right(h.clone(), mem_z_lam.clone());
    let m_ex = syl(&m_zl, &iff_mp(&lam_at_z)?)?;

    let n_m = and_left(m.clone(), z_body.clone());
    let n_body = and_right(m, z_body);
    let n_xa = syl(&n_body, &and_left(mem_xa.clone(), eq_z_pair.clone()))?;
    let n_zeq = syl(&n_body, &and_right(mem_xa.clone(), eq_z_pair))?;
    let n_h = syl(&n_m, &m_h)?;
    let n_val = hyp_mp(&syl(&n_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &n_xa)?;

    let inner_body = Formula::and(
        Formula::mem(ty.clone(), tc.clone()),
        Formula::eq(tz.clone(), ap.sets.pair(tx.clone(), ty)),
    );
    let outer = Formula::and(mem_xa, Formula::exists(y, inner_body.clone()));
    let prod_at_z = inst_all(&p.prod_ax, &[ta.clone(), tc.clone(), tz])?;
    if *prod_at_z.concl() != Formula::iff(mem_z_prod.clone(), Formula::exists(x, outer.clone())) {
        return None
    }

    let n_inner = syl(&hyp_and(&n_val, &n_zeq)?, &exists_intro_imp(y, inner_body, tx_val)?)?;
    let n_goal = syl(
        &syl(&hyp_and(&n_xa, &n_inner)?, &exists_intro_imp(x, outer, tx)?)?,
        &iff_mpr(&prod_at_z)?,
    )?;
    let m_goal = discharge(x, &m_ex, &n_goal)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_z_lam, mem_z_prod))?,
        &Thm::gen(z, &uncurry(&m_goal)?),
    )?;
    if *h_sub.concl() != Formula::imp(h.clone(), sub) {
        return None
    }

    // ── The three clauses, reassembled ───────────────────────────────────────
    let fs_t = fsp.of(ta.clone(), tc.clone());
    let mem_fs = Formula::mem(lam_t.clone(), fs_t);
    let fs_at = inst_all(&fsp.fs_ax, &[ta, tc, lam_t])?;
    if *fs_at.concl() != Formula::iff(mem_fs.clone(), isfun) {
        return None
    }
    let out = syl(&hyp_and(&h_sub, &hyp_and(&h_total, &h_sv)?)?, &iff_mpr(&fs_at)?)?;
    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, mem_fs) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(cv);
    Some(gen_all(&all, &out))
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A. ((∀x. (x ∈ A → t(p⃗,x) ∈ b(q⃗,x))) → lam(p⃗,A) ∈ dprod(q⃗,A))`
/// — **Lean's lambda typing rule**, with a parameter prefix on the lambda and
/// an independent one on the fibre.
///
/// The `k = k' = 0` case is [`super::lam_in_dprod`]; see there for the
/// argument. Only the argument lists differ, and the two prefixes are
/// independent because the lambda's skeleton and the `Π`'s fibre skeleton are.
///
/// **No inhabitation antecedent and no condition on `A`**:
/// `lam(p⃗,∅) ∈ dprod(q⃗,∅)` holds with the hypothesis vacuous.
///
/// `lambda` is `(t, lam, beta, lam_fs)` and `fibre` is
/// `(b, img, img_ax, dprod, dprod_def)`. `beta` must be what
/// [`crate::funcs::beta_conditional_n`] produces for `t`/`lam` and `lam_fs`
/// what [`lam_in_funspace_n`] produces for the same pair; `img`/`dprod` and
/// their axioms must be what
/// [`super::image_symbol_n`]/[`super::dprod_symbol_n`] produce for `b`. All of
/// that is checked, so a mismatched stack is refused rather than silently
/// described.
///
/// All four caller-supplied theorems, and the [`crate::funcs::Sets::un_ax`]
/// this consumes through [`crate::funcs::union_intro`], must be
/// **unconditional**. The shape pins below read `concl()` only, so without this
/// a premise proved under an open hypothesis would ride through every one of
/// them and reappear as the `Γ` of a theorem the header states as `⊢`.
pub fn lam_in_dprod_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    lambda: (FnSym, FnSym, &Thm, &Thm),
    fibre: (FnSym, FnSym, &Thm, FnSym, &Thm),
) -> Option<Thm> {
    let (t, lam, beta, lam_fs) = lambda;
    let (b, img, img_ax, dprod, dprod_def) = fibre;
    if !crate::all_unconditional(&[beta, lam_fs, img_ax, dprod_def, &ap.sets.un_ax]) {
        return None
    }
    let np = (t.arity() as usize).checked_sub(1)?;
    let nq = (b.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != np + 1 {
        return None
    }
    if img.arity() as usize != nq + 1 || dprod.arity() as usize != nq + 1 {
        return None
    }
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..nq).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|v| Term::var(*v)).collect();
    let qts: Vec<Term> = qs.iter().map(|v| Term::var(*v)).collect();

    let av = env.fresh_var();
    let ta = Term::var(av);
    let lam_t = sym_at(lam, &pts, ta.clone());
    let img_t = sym_at(img, &qts, ta.clone());
    let u = ap.sets.union_of(img_t.clone());

    let x = env.fresh_var();
    let tx = Term::var(x);
    let tx_val = sym_at(t, &pts, tx.clone()); // t(p⃗,x)
    let bx = sym_at(b, &qts, tx.clone()); // b(q⃗,x)
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    // The hypothesis, rebuilt at our own `x` so that it can be opened.
    let h_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), bx.clone()));
    let h = Formula::forall(x, h_body);

    let kf = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_fibre = hyp_mp(&syl(&k_h, &Thm::ax_inst(h.clone(), tx.clone())?)?, &k_xa)?;

    // ── The values land in `⋃img(q⃗,A)`, since `b(q⃗,x) ∈ img(q⃗,A)` ───────────
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body = Formula::and(
        Formula::mem(tx2.clone(), ta.clone()),
        Formula::eq(bx.clone(), sym_at(b, &qts, tx2)),
    );
    let img_at = inst_all(img_ax, &inst_at(&qts, &ta, &bx))?;
    if *img_at.concl()
        != Formula::iff(Formula::mem(bx.clone(), img_t.clone()), Formula::exists(x2, img_body.clone()))
    {
        return None
    }
    let k_witness = hyp_and(&k_xa, &a1i(&Thm::eq_refl(bx.clone()), kf))?;
    let k_img = syl(
        &syl(&k_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?,
        &iff_mpr(&img_at)?,
    )?;
    let intro = union_intro(env, &ap.sets, img_t, bx.clone(), tx_val.clone()).ok()?;
    let k_in_u = syl(&hyp_and(&k_img, &k_fibre)?, &intro)?;

    let u_body = Formula::imp(mem_xa.clone(), Formula::mem(tx_val.clone(), u.clone()));
    let h_body_u = Thm::mp(&Thm::ax_dist(x, h.clone(), u_body.clone())?, &Thm::gen(x, &uncurry(&k_in_u)?))?;

    let fs_t = fsp.of(ta.clone(), u.clone());
    let mem_fs = Formula::mem(lam_t.clone(), fs_t);
    let mut fargs = pts.clone();
    fargs.push(ta.clone());
    fargs.push(u);
    let lam_fs_at = inst_all(lam_fs, &fargs)?;
    if *lam_fs_at.concl() != Formula::imp(Formula::forall(x, u_body), mem_fs.clone()) {
        return None
    }
    let h_fs = syl(&h_body_u, &lam_fs_at)?;

    // ── The section condition, from beta reduction ───────────────────────────
    let app_t = ap.apply(lam_t.clone(), tx.clone());
    let mut bargs = pts;
    bargs.push(ta.clone());
    bargs.push(tx.clone());
    let beta_at = inst_all(beta, &bargs)?;
    if *beta_at.concl() != Formula::imp(mem_xa.clone(), Formula::eq(app_t.clone(), tx_val.clone())) {
        return None
    }
    let k_beta = syl(&k_xa, &beta_at)?;
    let w = env.fresh_var();
    let k_sec_body = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &k_beta)?, w, &Formula::mem(Term::var(w), bx.clone()))?,
        &k_fibre,
    )?;
    let sec_body = Formula::imp(mem_xa, Formula::mem(app_t, bx));
    let sec = section_n(env, ap, b, &qts, &ta, &lam_t);
    if sec != Formula::forall(x, sec_body.clone()) {
        return None
    }
    let h_sec = Thm::mp(&Thm::ax_dist(x, h.clone(), sec_body)?, &Thm::gen(x, &uncurry(&k_sec_body)?))?;

    // ── `L(lam(p⃗,A))` is exactly what `dprod` is defined by ─────────────────
    let dp_t = sym_at(dprod, &qts, ta.clone());
    let mem_dp = Formula::mem(lam_t.clone(), dp_t);
    let dp_at = inst_all(dprod_def, &inst_at(&qts, &ta, &lam_t))?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), Formula::and(mem_fs, sec)) {
        return None
    }
    let out = hyp_mp(&a1i(&iff_mpr(&dp_at)?, h.clone()), &hyp_and(&h_fs, &h_sec)?)?;
    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, mem_dp) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    Some(gen_all(&all, &out))
}
