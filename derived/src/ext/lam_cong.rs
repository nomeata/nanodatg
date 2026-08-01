//! Extensionality for Replacement images, and hence for lambda graphs.
//!
//! # Interface
//!
//! Write `img(A) = { g(x) : x ∈ A }` for any symbol introduced as a
//! Replacement image, i.e. one carrying
//!
//! ```text
//! ⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = g(x)))
//! ```
//!
//! and `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }` for the lambda graph
//! [`crate::funcs::lambda`] builds, which is that shape at
//! `g(x) := ⟨x, t(x)⟩`. The exports are
//!
//! ```text
//! ⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g(x) = g'(x))) → img(A) = img'(A')))  [image_ext]
//! ⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A')))  [lam_ext]
//! ⊢ ∀A. ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A))                 [lam_ext_same_domain]
//! ```
//!
//! the last being the form the checker's `lam_cong` actually calls. Callers
//! need none of the derivations below; those three statements are the whole
//! contract.
//!
//! # Why this is not congruence
//!
//! `⟦λx:A. b⟧` is interpreted as a *set* — the graph — not as a syntactic
//! binder, so "equal domains and pointwise equal bodies give equal lambdas" is
//! not an instance of congruence over sub-terms: the two graphs are built by
//! *different* function symbols, and no amount of `congr_arg` relates `lam(A)`
//! to `lam'(A')`. What does relate them is Extensionality — the two graphs have
//! the same members, so they are the same set.
//!
//! A member of the left is `⟨x, t(x)⟩` for some `x ∈ A`. Under the two
//! hypotheses `A = A'` and `∀x ∈ A. ⟨x,t(x)⟩ = ⟨x,t'(x)⟩`, that same `x`
//! witnesses membership in the right: `x ∈ A'` by Leibniz on the domains, and
//! the body equation is applied directly. The converse direction is the mirror
//! image, needing symmetry of `=` twice: once to get `x ∈ A` from `x ∈ A'`
//! (which is what makes the pointwise hypothesis, stated over `A`, applicable),
//! and once to turn the body equation around.
//!
//! Nothing in that argument mentions the ordered pair, which is why the general
//! form [`image_ext`] is what is proved and [`lam_ext`] is an instance of it,
//! plus one step of Leibniz to strengthen the stated hypothesis
//! `∀x ∈ A. t(x) = t'(x)` into the pointwise equation of the pairs — the pair
//! is a *term composition* (`upair(upair(x,x), upair(x, ·))`), so congruence for
//! it is a single `eq_leibniz` with the hole in the right place rather than a
//! separate lemma. [`crate::ext::DProd`]'s fibre image is the other instance,
//! and it is what makes [`crate::ext::dprod_ext`] possible.
//!
//! Everything runs in the `⊢ H → φ` style, with `H` the conjunction of the two
//! hypotheses; there is no deduction theorem, so the implication is assembled
//! rather than discharged.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, forall_mono,
    gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_mono_r, inst_all, mpd_const, syl, uncurry,
};
use super::shared::same_domain;

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g(x) = g'(x))) → img(A) = img'(A')))`
/// — extensionality for Replacement images.
///
/// `img`/`img_ax` and `img2`/`img2_ax` must be a unary symbol and a theorem
///
/// ```text
/// ⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = g(x)))
/// ```
///
/// with `g` the term supplied as `g1`, written in terms of the variable `x`,
/// and correspondingly for the primed side. Both [`crate::funcs::lambda`] and
/// [`crate::ext::image_symbol`] produce exactly that pair, at `g(x) := ⟨x, t(x)⟩` and
/// `g(x) := b(x)` respectively.
///
/// The two axioms are *checked* against that shape rather than assumed: a
/// mismatch would still be sound but would prove something about the wrong
/// sets, and silently, so it returns `None` instead.
#[allow(clippy::too_many_arguments)]
pub fn image_ext(
    env: &mut Env,
    x: FreeVar,
    g1: &Term,
    img: FnSym,
    img_ax: &Thm,
    g2: &Term,
    img2: FnSym,
    img2_ax: &Thm,
) -> Option<Thm> {
    if img.arity() != 1 || img2.arity() != 1 {
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

    let img_t = Term::apply(img, vec![ta.clone()]); // img(A)
    let img2_t = Term::apply(img2, vec![ta2.clone()]); // img'(A')

    // The two hypotheses, and their conjunction `H`.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(g1.clone(), g2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    // The two membership conditions, exactly as Replacement states them.
    let eq_y1 = Formula::eq(ty.clone(), g1.clone());
    let eq_y2 = Formula::eq(ty.clone(), g2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), img_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), img2_t.clone());

    let img_at_y = inst_all(img_ax, &[ta.clone(), ty.clone()])?;
    if *img_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let img2_at_y = inst_all(img2_ax, &[ta2.clone(), ty.clone()])?;
    if *img2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of img(A) is a member of img'(A') ──────────────────
    // Under `K := H ∧ (x ∈ A ∧ y = g(x))`, the same `x` witnesses the
    // right-hand condition.
    let k = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    // K → g(x) = g'(x): the pointwise hypothesis at this very `x`.
    let k_gg = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    // K → x ∈ A', by Leibniz along `A = A'`.
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k.clone()), &k_dom)?, &k_xa)?;
    // K → y = g'(x), by Leibniz along the body equation.
    let w2 = env.fresh_var();
    let carry_val =
        Thm::eq_leibniz(g1.clone(), g2.clone(), w2, Formula::eq(ty.clone(), Term::var(w2)));
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k.clone()), &k_gg)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    // Discharge the witness: `⊢ H → ((∃x. body₁) → ∃x. body₂)`.
    let fwd_ex = com12(&exists_elim_imp(
        x,
        &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?),
        &Formula::imp(h.clone(), ex2.clone()),
    )?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&img2_at_y)?, h.clone()),
    )?;
    debug_assert_eq!(
        *h_fwd.concl(),
        Formula::imp(h.clone(), Formula::imp(mem_y1.clone(), mem_y2.clone())),
        "image_ext: the forward half has an unexpected shape"
    );

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    // J → x ∈ A. Needed *before* the pointwise hypothesis can be used, since it
    // is stated over `A`.
    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_gg = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_gg_symm = syl(&j_gg, &eq_symm_imp(env, g1.clone(), g2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 =
        Thm::eq_leibniz(g2.clone(), g1.clone(), w4, Formula::eq(ty.clone(), Term::var(w4)));
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j.clone()), &j_gg_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex = com12(&exists_elim_imp(
        x,
        &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?),
        &Formula::imp(h.clone(), ex1.clone()),
    )?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&img_at_y)?, h.clone()),
    )?;
    debug_assert_eq!(
        *h_bwd.concl(),
        Formula::imp(h.clone(), Formula::imp(mem_y2.clone(), mem_y1.clone())),
        "image_ext: the backward half has an unexpected shape"
    );

    // ── Same members, hence equal ────────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?,
        &Thm::gen(y, &h_iff),
    )?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[img_t.clone(), img2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(img_t, img2_t))),
        "image_ext: unexpected shape"
    );
    Some(gen_all(&[av, av2], &out))
}

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A')))`
/// — lambda graph extensionality.
///
/// `lam`/`lam_ax` and `lam2`/`lam2_ax` must be the graph symbol and
/// characteristic theorem produced by [`crate::funcs::lambda`] for the unary
/// body symbols `t` and `t2` respectively.
///
/// The Extensionality argument itself is [`image_ext`], at `g(x) := ⟨x,t(x)⟩`;
/// all that is left here is that `image_ext`'s hypothesis is the pointwise
/// equation of the *pairs* while this lemma's is the pointwise equation of the
/// *bodies*, and the first follows from the second by congruence in the pair's
/// second component. So this strengthens the hypothesis and hands the rest over.
///
/// Returns `None` if any symbol has the wrong arity or a step fails to line up.
#[allow(clippy::too_many_arguments)]
pub fn lam_ext(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    t2: FnSym,
    lam2: FnSym,
    lam2_ax: &Thm,
) -> Option<Thm> {
    if t.arity() != 1 || t2.arity() != 1 || lam.arity() != 1 || lam2.arity() != 1 {
        return None
    }
    let x = env.fresh_var();
    let tx = Term::var(x);
    let val1 = Term::apply(t, vec![tx.clone()]); // t(x)
    let val2 = Term::apply(t2, vec![tx.clone()]); // t'(x)
    let pair1 = ap.sets.pair(tx.clone(), val1.clone()); // ⟨x, t(x)⟩
    let pair2 = ap.sets.pair(tx.clone(), val2.clone()); // ⟨x, t'(x)⟩

    // ⊢ ∀A ∀A'. (A = A' → ((∀x ∈ A. ⟨x,t(x)⟩ = ⟨x,t'(x)⟩) → lam(A) = lam'(A')))
    let general = image_ext(env, x, &pair1, lam, lam_ax, &pair2, lam2, lam2_ax)?;

    let (av, av2) = (env.fresh_var(), env.fresh_var());
    let (ta, ta2) = (Term::var(av), Term::var(av2));
    let inst = inst_all(&general, &[ta.clone(), ta2.clone()])?;

    // ⊢ t(x) = t'(x) → ⟨x,t(x)⟩ = ⟨x,t'(x)⟩. The pair is a term composition, so
    // congruence in its second component is Leibniz with the hole there.
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val1.clone(),
        val2.clone(),
        w,
        Formula::eq(pair1.clone(), ap.sets.pair(tx.clone(), Term::var(w))),
    );
    let cong = mpd_const(&carry, &Thm::eq_refl(pair1.clone()))?;

    // Lift it under `x ∈ A` and under the `∀x`, giving the hypothesis swap.
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mono = forall_mono(x, &Thm::gen(x, &imp_mono_r(&cong, mem_xa.clone())?))?;

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let out = hyp_syl(&a1i(&mono, eq_dom.clone()), &inst)?;

    let pointwise =
        Formula::forall(x, Formula::imp(mem_xa, Formula::eq(val1.clone(), val2.clone())));
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            eq_dom,
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(lam, vec![ta]), Term::apply(lam2, vec![ta2]))
            )
        ),
        "lam_ext: unexpected shape"
    );
    Some(gen_all(&[av, av2], &out))
}

/// `⊢ ∀A. ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A))` — the same-domain
/// corollary, which is the form the checker's `lam_cong` calls.
///
/// Takes the theorem [`lam_ext`] produces and instantiates both domains at the
/// same variable, discharging `A = A` by reflexivity. Passing the derived
/// theorem rather than re-deriving it means a caller that needs both forms pays
/// for the derivation once.
///
/// Returns `None` if `lam_ext_thm` is not of the shape [`lam_ext`] produces.
pub fn lam_ext_same_domain(env: &mut Env, lam_ext_thm: &Thm) -> Option<Thm> {
    same_domain(env, lam_ext_thm)
}
