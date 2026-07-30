//! Extensionality for Replacement images: lambda graphs, and the dependent
//! product.
//!
//! `⟦λx:A. b⟧` is interpreted as the *graph* `{ ⟨x, t(x)⟩ : x ∈ A }`
//! ([`crate::funcs::lambda`]), which is a set, not a syntactic binder. So the
//! checker's `lam_cong` rule — "equal domains and pointwise equal bodies give
//! equal lambdas" — is not an instance of congruence over sub-terms: the two
//! graphs are built by *different* function symbols, and no amount of
//! `congr_arg` relates `lam(A)` to `lam'(A')`.
//!
//! What does relate them is Extensionality: the two graphs have the same
//! members, so they are the same set. That is [`lam_ext`], and the same-domain
//! specialisation the checker actually calls is [`lam_ext_same_domain`].
//!
//! # The shape of the argument, and what it does not depend on
//!
//! Both `lam` and `lam'` come with a characteristic axiom of the form
//!
//! ```text
//! ⊢ ∀A ∀y. (y ∈ lam(A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(x)⟩))
//! ```
//!
//! so a member of the left is `⟨x, t(x)⟩` for some `x ∈ A`. Under the two
//! hypotheses `A = A'` and `∀x ∈ A. ⟨x,t(x)⟩ = ⟨x,t'(x)⟩`, that same `x`
//! witnesses membership in the right: `x ∈ A'` by Leibniz on the domains, and
//! the body equation is applied directly. The converse direction is the mirror
//! image, needing symmetry of `=` twice: once to get `x ∈ A` from `x ∈ A'`
//! (which is what makes the pointwise hypothesis, stated over `A`, applicable),
//! and once to turn the body equation around.
//!
//! Nothing in that argument mentions the ordered pair. It works for *any*
//! symbol defined as a Replacement image `{ g(x) : x ∈ A }`, and that general
//! form is [`image_ext`]. [`lam_ext`] is the instance at `g(x) := ⟨x, t(x)⟩`,
//! plus one step of Leibniz to strengthen its stated hypothesis
//! `∀x ∈ A. t(x) = t'(x)` into the pointwise equation of the pairs — the pair
//! is a *term composition* (`upair(upair(x,x), upair(x, ·))`), so congruence for
//! it is a single `eq_leibniz` with the hole in the right place rather than a
//! separate lemma. [`DProd`]'s fibre image is the other instance, and it is what
//! makes [`dprod_ext`] possible.
//!
//! Everything runs in the `⊢ H → φ` style the rest of this crate uses, with
//! `H` the conjunction of the two hypotheses; there is no deduction theorem, so
//! the implication is assembled rather than discharged.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, Apply};
use crate::funspace::Funspace;
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, forall_mono,
    gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_mono_r, inst_all, mpd_const, syl, uncurry,
};

// ─────────────────────────────────────────────────────────────────────────────
// Reasoning about equations under a fixed hypothesis.
//
// The `⊢ H → φ` idiom has no equality toolkit of its own: `eq_trans`, `eq_symm`
// and `congr_arg` all consume a *proved* equation, and every equation below is
// only available under `H`. These four are the missing half, and each is a
// single Leibniz step plus plumbing.
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ P → (Q → R)` infer `⊢ (P ∧ Q) → R` — the converse of
/// [`crate::uncurry`].
fn curry(t: &Thm) -> Option<Thm> {
    let (p, rest) = t.concl().as_imp()?;
    let (q, _) = rest.as_imp()?;
    let h = Formula::and(p.clone(), q.clone());
    let hp = and_left(p.clone(), q.clone());
    let hq = and_right(p, q);
    hyp_mp(&hyp_mp(&a1i(t, h), &hp)?, &hq)
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])` — Leibniz under a
/// hypothesis.
fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ H → a = b` infer `⊢ H → c[a/w] = c[b/w]` — congruence under a
/// hypothesis, for a term `c` with the hole `w`.
///
/// `lhs` must be `c[a/w]`; that is checked rather than assumed, since a term
/// cannot be substituted into from outside the kernel and the caller therefore
/// has to supply the substituted form itself. Returns `None` if it does not
/// match, which is exactly the case where the hole is in the wrong place.
fn hyp_congr(h_eq: &Thm, w: FreeVar, lhs: &Term, c: &Term) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    let leib = Thm::eq_leibniz(a, b, w, Formula::eq(lhs.clone(), c.clone()));
    let (ante, _) = leib.concl().as_imp()?.1.as_imp()?;
    if ante != Formula::eq(lhs.clone(), lhs.clone()) {
        return None
    }
    syl(h_eq, &mpd_const(&leib, &Thm::eq_refl(lhs.clone()))?)
}

/// From `⊢ H → a = b` and `⊢ H → b = c` infer `⊢ H → a = c`.
fn hyp_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
    let (h, e1) = ab.concl().as_imp()?;
    let (_, e2) = bc.concl().as_imp()?;
    let (a, b1) = e1.as_eq()?;
    let (b2, c) = e2.as_eq()?;
    if b1 != b2 {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(b1, c, w, Formula::eq(a, Term::var(w)));
    hyp_mp(&hyp_mp(&a1i(&leib, h), bc)?, ab)
}

/// From `⊢ H → a = b` infer `⊢ H → b = a`.
fn hyp_eq_symm(env: &mut Env, h_eq: &Thm) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    syl(h_eq, &eq_symm_imp(env, a, b))
}

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
/// [`image_symbol`] produce exactly that pair, at `g(x) := ⟨x, t(x)⟩` and
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

/// `⊢ ∀A. (P(A, A) → f(A) = g(A))`, from `⊢ ∀A ∀A'. (A = A' → (P(A,A') → …))`.
///
/// Shared by [`lam_ext_same_domain`] and [`dprod_ext_same_domain`], which
/// differ only in what the theorem handed in says.
fn same_domain(env: &mut Env, thm: &Thm) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let inst = inst_all(thm, &[ta.clone(), ta.clone()])?;
    let (ante, _) = inst.concl().as_imp()?;
    // The antecedent must be the reflexive equation the instantiation created;
    // anything else means this is not a conclusion of the expected shape.
    if ante != Formula::eq(ta.clone(), ta.clone()) {
        return None
    }
    let out = Thm::mp(&inst, &Thm::eq_refl(ta))?;
    debug_assert!(out.concl().as_imp().is_some(), "same_domain: unexpected shape");
    Some(Thm::gen(a, &out))
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

// ─────────────────────────────────────────────────────────────────────────────
// The dependent product.
//
// `⟦Π(x:A). B(x)⟧` is currently an opaque symbol in the checker, which is why
// `pi_cong` gaps. What it should denote is
//
//     dprod(A) = { f ∈ fs(A, ⋃{b(x) : x ∈ A}) : ∀x ∈ A. app(f,x) ∈ b(x) }
//
// — the functions on `A` whose value at each `x` lands in the fibre `b(x)`. The
// codomain has to be *some* set containing every fibre, and `⋃{b(x) : x ∈ A}`
// is the cheapest one: it is a Replacement image followed by a union, both
// total, so it costs no side condition.
//
// # The default the definition used to carry
//
// The dependent product really can be empty — take any `x ∈ A` with `b(x)`
// empty — so [`crate::funcs::separation_nonempty`], which needs its result
// inhabited, did not apply. The way out was the one
// [`crate::funspace::funspace`] and [`crate::funcs::collection`] also took:
// define the disjunctive condition
//
//     f ∈ dprod(A)  ↔  L(f)  ∨  (¬∃g. L(g)  ∧  f ∈ fs(A, ⋃img(A)))
//
// so that the symbol was total, with the intended condition recoverable only
// under the antecedent `∃g. L(g)` — and, unlike the function space, there was
// no canonical section available to discharge it, so `dprod_ax` was an
// implication nobody could use.
//
// `∅` removes the whole construction. [`crate::funcs::separation_full`] carves
// the set out whether or not anything is in it, so [`dprod_symbol`] defines
// `L(f)` directly and [`dprod_members`] reads
//
//     ⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))
//
// with no antecedent. [`dprod_subset_funspace`] is unchanged.
// ─────────────────────────────────────────────────────────────────────────────

/// The Replacement image `img(A) = { b(x) : x ∈ A }`, with
/// `⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))`.
///
/// Replacement at its cheapest, exactly as [`crate::funcs::lambda`]: the
/// relation is `w = b(x)`, so the `∃!` premise is
/// [`crate::exists_unique_eq`] and costs nothing. `b` must be unary.
pub fn image_symbol(env: &mut Env, b: FnSym) -> Option<(FnSym, Thm)> {
    if b.arity() != 1 {
        return None
    }
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(x));
    let bx = Term::apply(b, vec![tx.clone()]);

    let (w, phi, exu) = crate::exists_unique_eq(env, &[], &bx);
    let repl = Thm::ax_replacement(env, x, w, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    crate::define_by_membership(env, &[av], &img, w, &cond)
}

/// The dependent product `dprod(A) = Π(x:A). b(x)`, for a unary fibre symbol
/// `b`, together with everything proved about it.
pub struct DProd {
    /// `img(A) = { b(x) : x ∈ A }`.
    pub img: FnSym,
    /// `⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))`.
    pub img_ax: Thm,
    /// The symbol itself.
    pub dprod: FnSym,
    /// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))` — the defining axiom, which is now the
    /// intended condition and nothing else.
    pub dprod_def: Thm,
    /// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))`, where `L(f)` is
    /// `f ∈ fs(A,⋃img(A)) ∧ ∀x. (x ∈ A → app(f,x) ∈ b(x))` — the same
    /// statement, with [`dprod_members`] having rebuilt `L` independently and
    /// checked it against the defining axiom.
    pub dprod_ax: Thm,
    /// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`.
    pub dprod_sub: Thm,
}

impl DProd {
    /// Introduce `img` and `dprod` and prove both lemmas about them.
    ///
    /// `fsp` must be the function space built over `ap.sets`, or the terms will
    /// not compose: every symbol here is a definitional extension, so a second
    /// `Sets` would give a second, unrelated pairing operation.
    pub fn new(env: &mut Env, ap: &Apply, fsp: &Funspace, b: FnSym) -> Option<DProd> {
        let (img, img_ax) = image_symbol(env, b)?;
        let (dprod, dprod_def) = dprod_symbol(env, ap, fsp, img, b)?;
        let dprod_ax = dprod_members(env, ap, fsp, img, b, dprod, &dprod_def)?;
        let dprod_sub = dprod_subset_funspace(env, ap, fsp, img, b, dprod, &dprod_def)?;
        Some(DProd { img, img_ax, dprod, dprod_def, dprod_ax, dprod_sub })
    }

    /// The term `dprod(A)`.
    pub fn of(&self, a: Term) -> Term { Term::apply(self.dprod, vec![a]) }
}

/// The base set `⋃ img(A)` — a superset of every fibre `b(x)` for `x ∈ A`.
fn base_of(ap: &Apply, img: FnSym, a: &Term) -> Term {
    ap.sets.union_of(Term::apply(img, vec![a.clone()]))
}

/// `∀x. (x ∈ A → app(f,x) ∈ b(x))` — `f` is a section of the fibration.
pub fn is_section(env: &mut Env, ap: &Apply, b: FnSym, a: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx.clone()), Term::apply(b, vec![tx])),
        ),
    )
}

/// The membership condition defined: `L(f) := f ∈ fs(A,⋃img(A)) ∧ section(f)`,
/// together with the function space term it is carved out of.
fn dprod_cond(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    a: &Term,
    f: FreeVar,
) -> (Formula, Term) {
    let tf = Term::var(f);
    let fs_t = fsp.of(a.clone(), base_of(ap, img, a));
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    (Formula::and(mem_fs, is_section(env, ap, b, a, &tf)), fs_t)
}

/// Introduce `dprod(A) = Π(x:A). b(x)`, with
/// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))`.
///
/// One call to [`crate::funcs::separation_full`] and nothing else: the
/// condition it carves by, `f ∈ fs(A,⋃img(A)) ∧ section(f)`, *is* `L(f)` on the
/// nose, so there is not even a shape to convert. See the section comment for
/// the default disjunct this replaces.
pub fn dprod_symbol(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
) -> Option<(FnSym, Thm)> {
    if b.arity() != 1 || img.arity() != 1 {
        return None
    }
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);
    debug_assert_eq!(l, Formula::and(mem_fs, psi.clone()), "dprod: condition shape drift");

    let existence = crate::funcs::separation_full(env, f, &psi, &fs_t, &ap.empty_ax)?;
    let sv = env.fresh_var();
    debug_assert_eq!(
        *existence.concl(),
        Formula::exists(
            sv,
            Formula::forall(f, Formula::iff(Formula::mem(tf, Term::var(sv)), l.clone()))
        ),
        "dprod: Separation has an unexpected shape"
    );

    crate::define_by_membership(env, &[av], &existence, f, &l)
}

/// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))` — the members of the dependent product are
/// the sections, **unconditionally**.
///
/// This used to be conditional on `∃g. L(g)`, that being the hypothesis under
/// which [`dprod_symbol`]'s default disjunct was dead — and, unlike the
/// function space, no canonical section was available to discharge it. There is
/// no default any more, so the statement is exactly the defining axiom, and
/// what this function adds is the *check*: it rebuilds `L(f)` from
/// [`is_section`] and the function space independently and refuses unless
/// `dp_def` characterises `dprod(A)` by precisely that.
pub fn dprod_members(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, _) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let dp_t = Term::apply(dp, vec![ta]);
    let expected = Formula::forall(
        av,
        Formula::forall(f, Formula::iff(Formula::mem(tf, dp_t), l)),
    );
    if *dp_def.concl() != expected {
        return None
    }
    Some(dp_def.clone())
}

/// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`.
///
/// A member of `dprod(A)` satisfies `L`, whose left conjunct is membership in
/// the function space. (This was already unconditional when `dprod` carried a
/// default disjunct — the default was chosen to be the function space itself
/// precisely so that it would be. Now there is only one case.)
pub fn dprod_subset_funspace(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);

    let l_mem = and_left(mem_fs.clone(), psi);
    debug_assert_eq!(*l_mem.concl(), Formula::imp(l.clone(), mem_fs), "dprod_subset: shape drift");

    let dp_at_f = inst_all(dp_def, &[ta.clone(), tf.clone()])?;
    let dp_t = Term::apply(dp, vec![ta.clone()]);
    debug_assert_eq!(
        *dp_at_f.concl(),
        Formula::iff(Formula::mem(tf, dp_t.clone()), l),
        "dprod's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&dp_at_f)?, &l_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, dp_t, fs_t),
        "dprod_subset_funspace: unexpected shape"
    );
    Some(gen_all(&[av], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Extensionality for the dependent product.
//
// `pi_cong` is in the same position `lam_cong` was: `⟦Π(x:A). B(x)⟧` is a
// `dprod` whose head symbol is chosen by the *shape of the body*, so two
// interpretations of provably-equal Π-types are built by two unrelated symbols
// and plain congruence over sub-terms relates nothing. Extensionality does, and
// the route runs through the pieces `dprod` is assembled from:
//
//   1. `⋃img(A) = ⋃img'(A')` — `image_ext` on the fibre images, then congruence
//      for `⋃`, which is an ordinary function symbol;
//   2. `fs(A, ⋃img(A)) = fs(A', ⋃img'(A'))` — congruence for `fs`, twice;
//   3. the separation condition `∀x ∈ A. app(f,x) ∈ b(x)` agrees pointwise, so
//      the two carved sets have the same members;
//   4. Extensionality.
//
// Step 3 is the only one that is not pure congruence, and it is exactly the
// same two-way argument `image_ext` runs: the domain equation moves `x` across,
// the pointwise hypothesis is stated over `A` so `x` has to be moved *back*
// before it applies, and the fibre equation carries membership.
// ─────────────────────────────────────────────────────────────────────────────

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
/// [`lam_ext_same_domain`] does, and by the same code.
///
/// Returns `None` if `dprod_ext_thm` is not of the shape [`dprod_ext`] produces.
pub fn dprod_ext_same_domain(env: &mut Env, dprod_ext_thm: &Thm) -> Option<Thm> {
    same_domain(env, dprod_ext_thm)
}

// ─────────────────────────────────────────────────────────────────────────────
// Congruence for the function space.
//
// The non-dependent Π is `fs(a,b)`, whose arguments are the interpretations of
// the domain and codomain — so unlike `dprod` and `lam`, the head symbol does
// *not* depend on the body's shape and there is nothing to prove beyond
// congruence. What is not immediate is only the *form*: `crate::congr` consumes
// two proved equations and yields a proved equation, whereas `pi_cong` needs the
// universally quantified implication, which a Hilbert system has to assemble.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → f(a,b) = f(a',b')))`, for any binary
/// function symbol.
fn congr2_imp(env: &mut Env, f: FnSym) -> Option<Thm> {
    if f.arity() != 2 {
        return None
    }
    let (a, a2, b, b2) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tb, tb2) = (Term::var(a), Term::var(a2), Term::var(b), Term::var(b2));

    let e1 = Formula::eq(ta.clone(), ta2.clone());
    let e2 = Formula::eq(tb.clone(), tb2.clone());
    let h_e1 = and_left(e1.clone(), e2.clone());
    let h_e2 = and_right(e1.clone(), e2.clone());

    let lhs = Term::apply(f, vec![ta.clone(), tb.clone()]);
    let mid = Term::apply(f, vec![ta2.clone(), tb.clone()]);
    let rhs = Term::apply(f, vec![ta2.clone(), tb2.clone()]);

    let w1 = env.fresh_var();
    let step1 = hyp_congr(&h_e1, w1, &lhs, &Term::apply(f, vec![Term::var(w1), tb.clone()]))?;
    let w2 = env.fresh_var();
    let step2 = hyp_congr(&h_e2, w2, &mid, &Term::apply(f, vec![ta2.clone(), Term::var(w2)]))?;

    let out = uncurry(&hyp_eq_trans(env, &step1, &step2)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(e1, Formula::imp(e2, Formula::eq(lhs, rhs))),
        "congr2_imp: unexpected shape"
    );
    Some(gen_all(&[a, a2, b, b2], &out))
}

/// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))` — the
/// non-dependent function space respects equality of its domain and codomain.
///
/// Two Leibniz steps and a transitivity, via [`congr2_imp`]. This is the
/// companion to [`dprod_ext`] for the case where the Π-type's body does not
/// depend on the bound variable and the checker's interpretation is a plain
/// `fs`.
pub fn fs_cong(env: &mut Env, fsp: &Funspace) -> Option<Thm> { congr2_imp(env, fsp.fs) }
