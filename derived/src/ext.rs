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
//!
//! # The two typing rules
//!
//! The last two sections are not about extensionality at all; they are the
//! membership facts Lean's λ and Π rules interpret to, and they live here
//! because they are about `dprod` and nothing else has it. [`lam_in_dprod`] is
//! the λ rule — a lambda graph whose body lands in the fibre pointwise is a
//! member of the dependent product — resting on [`lam_in_funspace`], which is
//! the codomain-agnostic half. [`dprod_in_universe_of`] is the Π rule as far as
//! `U(x)`'s *proved* closure properties reach, with the one missing ingredient
//! carried as an explicit antecedent, and [`dprod_in_universe`] is the instance
//! where that antecedent discharges itself.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, union_intro, Apply};
use crate::funspace::{is_function, is_single_valued, is_total, Funspace, Product};
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

// ─────────────────────────────────────────────────────────────────────────────
// A dependent product over a constant fibre is the function space.
//
// The checker interprets Lean's `Π` two ways: `fs(⟦A⟧,⟦B⟧)` when the body does
// not mention the binder, `dprod` when it does. Two *equal* Π-types can be
// interpreted each way — one body mentions the binder vacuously, the other does
// not — and then congruence has nothing to work with, because the two sides are
// built by unrelated symbols. What bridges them is that a dependent product over
// a constant fibre *is* the function space, which is [`dprod_const_fibre`].
//
// The route does **not** go through `⋃img(A) = B`. That equation is true only
// when `A` is inhabited — `⋃img(∅) = ∅` whatever the fibre — so it would force
// an inhabitation antecedent, and the empty domain is not a case worth losing:
// nothing in `f ∈ fs(∅,B)` depends on `B` (a function on `∅` is a subset of
// `prod(∅,B) = ∅` and is total vacuously), so the theorem holds there too, with
// `B` arbitrary and `⋃img(∅)` nowhere near it.
//
// What is used instead is that the function space only constrains a function
// through its values, so the codomain may be swapped for any set the values
// happen to land in ([`funspace_retarget`]) — and on an empty domain there are
// no values, so the swap is unconditional and both directions go through
// vacuously. The value of a function at a point is [`app_of_pair`], which is
// what connects the graph the function space talks about to the `app` the
// section condition talks about.
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
///
/// A private copy of the combinator [`crate::funspace`] keeps privately too, on
/// the same reasoning it gives: reading formulas apart produces no `Thm`, so a
/// duplicate is safe, and a derivation this long should not break when a
/// neighbouring module reshapes its own helpers.
fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    crate::empty::hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — [`crate::inst_all`] in implication form, for a
/// quantified formula that is only available under a hypothesis.
fn inst_all_imp(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = Thm::ax_inst(phi.clone(), ts.first()?.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}

/// `⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)` — the value of a
/// single-valued graph at a point it relates.
///
/// `app(f,x)` is `⋃{ y' : ⟨x,y'⟩ ∈ f }`, so this is the same argument
/// [`crate::funcs::beta_conditional`] runs for lambda graphs, with
/// single-valuedness in place of injectivity of the Kuratowski pair: the
/// collection has `y` as a member, single-valuedness forces every member to
/// equal `y`, so the collection is `{y}` and the union strips it off.
///
/// Unlike beta reduction this needs no membership antecedent — `⟨x,y⟩ ∈ f` is
/// already the statement that `x` is in the domain — which is what makes it
/// usable against a function given only as a member of a function space.
pub fn app_of_pair(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (f, x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tx, ty, tz) = (Term::var(f), Term::var(x), Term::var(y), Term::var(z));

    let sv = is_single_valued(env, &ap.sets, &tf);
    let mem_pair = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), tf.clone());
    let h = Formula::and(sv.clone(), mem_pair.clone());
    let h_sv = and_left(sv.clone(), mem_pair.clone());
    let h_pair = and_right(sv.clone(), mem_pair.clone());

    let coll_t = ap.coll_of(tf.clone(), tx.clone());
    let sing = crate::singleton(ap.sets.up, ty.clone());
    let mem_zc = Formula::mem(tz.clone(), coll_t.clone());
    let mem_zs = Formula::mem(tz.clone(), sing.clone());
    let mem_pair_z = Formula::mem(ap.sets.pair(tx.clone(), tz.clone()), tf.clone());
    let eq_zy = Formula::eq(tz.clone(), ty.clone());

    // The two characterisations this rests on, checked rather than assumed.
    let coll_at = inst_all(&ap.coll_members, &[tf.clone(), tx.clone(), tz.clone()])?;
    if *coll_at.concl() != Formula::iff(mem_zc.clone(), mem_pair_z.clone()) {
        return None
    }
    let ms = inst_all(&ap.mem_sing, &[ty.clone(), tz.clone()])?;
    if *ms.concl() != Formula::iff(mem_zs.clone(), eq_zy.clone()) {
        return None
    }

    // ── H → (⟨x,z⟩ ∈ f → z = y), single-valuedness at ⟨x,z⟩ and ⟨x,y⟩ ────────
    let sv_at = inst_all_imp(&sv, &[tx.clone(), tz.clone(), ty.clone()])?;
    let sv_body = Formula::imp(Formula::and(mem_pair_z.clone(), mem_pair.clone()), eq_zy.clone());
    if *sv_at.concl() != Formula::imp(sv.clone(), sv_body) {
        return None
    }
    let k_h = and_left(h.clone(), mem_pair_z.clone());
    let k_pz = and_right(h.clone(), mem_pair_z.clone());
    let k_conj = hyp_and(&k_pz, &syl(&k_h, &h_pair)?)?;
    let h_z_eq = uncurry(&hyp_mp(&syl(&syl(&k_h, &h_sv)?, &sv_at)?, &k_conj)?)?;

    // ── coll(f,x) and {y} have the same members ──────────────────────────────
    let fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&coll_at)?, h.clone()), &h_z_eq)?,
        &a1i(&iff_mpr(&ms)?, h.clone()),
    )?;

    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        ty.clone(),
        tz.clone(),
        w,
        Formula::mem(ap.sets.pair(tx.clone(), Term::var(w)), tf.clone()),
    );
    let h_eq_pair =
        syl(&h_pair, &com12(&syl(&eq_symm_imp(env, tz.clone(), ty.clone()), &carry)?)?)?;
    let bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &h_eq_pair)?,
        &a1i(&iff_mpr(&coll_at)?, h.clone()),
    )?;

    let h_all = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::iff(mem_zc, mem_zs))?,
        &Thm::gen(z, &hyp_and(&fwd, &bwd)?),
    )?;
    let h_coll_eq = syl(&h_all, &inst_all(&ext, &[coll_t.clone(), sing.clone()])?)?;

    // ── app(f,x) = ⋃coll(f,x) = ⋃{y} = y ─────────────────────────────────────
    let ucoll = ap.sets.union_of(coll_t.clone());
    let using = ap.sets.union_of(sing.clone());
    let app_t = ap.apply(tf.clone(), tx.clone());

    let w2 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(
            coll_t,
            sing,
            w2,
            Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w2))),
        ),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_def = inst_all(&ap.app_ax, &[tf, tx])?;
    let w3 = env.fresh_var();
    let carry3 =
        Thm::eq_leibniz(ucoll, using.clone(), w3, Formula::eq(app_t.clone(), Term::var(w3)));
    let h_app_using =
        hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w4 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, ty.clone(), w4, Formula::eq(app_t.clone(), Term::var(w4))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&ty))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_t, ty)),
        "app_of_pair: unexpected shape"
    );
    Some(gen_all(&[f, x, y], &out))
}

/// The three clauses of `isfun(f)`, as the formulas this module reasons with,
/// checked against [`crate::funspace::is_function`]'s own assembly of them.
///
/// Returns `None` if they do not agree — which would mean the function space is
/// characterised by something other than what is taken apart below, and the
/// projections would then be about the wrong conjuncts.
fn isfun_parts(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    a: &Term,
    b: &Term,
    f: &Term,
) -> Option<(Formula, Formula, Formula, Formula)> {
    let sub = kernel::thm::subset(env, f.clone(), p.of(a.clone(), b.clone()));
    let total = is_total(env, &ap.sets, a, b, f);
    let sv = is_single_valued(env, &ap.sets, f);
    let isfun = is_function(env, &ap.sets, p, a, b, f);
    if isfun != Formula::and(sub.clone(), Formula::and(total.clone(), sv.clone())) {
        return None
    }
    Some((isfun, sub, total, sv))
}

/// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)` — a function's
/// values lie in its codomain.
///
/// Totality supplies *some* `y ∈ b` with `⟨x,y⟩ ∈ f`, and [`app_of_pair`] —
/// single-valuedness being the other clause of `isfun` — identifies that `y` as
/// `app(f,x)`. The membership antecedent is genuine: off the domain `app(f,x)`
/// is `∅` (see [`crate::funcs::app_off_domain`]), which need not be in `b`.
///
/// `p` and `fsp` must be the product and function space `fs` was built from,
/// and `ap` the application apparatus over the same [`crate::funcs::Sets`];
/// `app_pair` must be what [`app_of_pair`] produces for that `ap`. All of that
/// is checked rather than assumed.
pub fn funspace_app_mem(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    app_pair: &Thm,
) -> Option<Thm> {
    let (av, bv, f, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tx) = (Term::var(av), Term::var(bv), Term::var(f), Term::var(x));

    let mem_fs = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::and(mem_fs.clone(), mem_xa.clone());

    let (isfun, sub, total, sv) = isfun_parts(env, ap, p, &ta, &tb, &tf)?;
    let fs_at = inst_all(&fsp.fs_ax, &[ta.clone(), tb.clone(), tf.clone()])?;
    if *fs_at.concl() != Formula::iff(mem_fs.clone(), isfun) {
        return None
    }

    let rest = Formula::and(total.clone(), sv.clone());
    let h_isfun = syl(&and_left(mem_fs.clone(), mem_xa.clone()), &iff_mp(&fs_at)?)?;
    let h_rest = syl(&h_isfun, &and_right(sub, rest))?;
    let h_total = syl(&h_rest, &and_left(total.clone(), sv.clone()))?;
    let h_sv = syl(&h_rest, &and_right(total.clone(), sv.clone()))?;
    let h_xa = and_right(mem_fs, mem_xa);

    // ── H → ∃y. (y ∈ b ∧ ⟨x,y⟩ ∈ f), totality at this `x` ────────────────────
    let y = env.fresh_var();
    let ty = Term::var(y);
    let mem_yb = Formula::mem(ty.clone(), tb.clone());
    let mem_pair = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), tf.clone());
    let body = Formula::and(mem_yb.clone(), mem_pair.clone());
    let h_ex = hyp_mp(&syl(&h_total, &Thm::ax_inst(total, tx.clone())?)?, &h_xa)?;
    debug_assert_eq!(
        *h_ex.concl(),
        Formula::imp(h.clone(), Formula::exists(y, body.clone())),
        "funspace_app_mem: the totality clause has an unexpected shape"
    );

    // ── That `y` is `app(f,x)`, so `app(f,x) ∈ b` ────────────────────────────
    let j = Formula::and(h.clone(), body.clone());
    let j_h = and_left(h.clone(), body.clone());
    let j_body = and_right(h.clone(), body);
    let j_yb = syl(&j_body, &and_left(mem_yb.clone(), mem_pair.clone()))?;
    let j_pair = syl(&j_body, &and_right(mem_yb, mem_pair.clone()))?;
    let j_sv = syl(&j_h, &h_sv)?;

    let app_t = ap.apply(tf.clone(), tx.clone());
    let ap_at = inst_all(app_pair, &[tf, tx, ty.clone()])?;
    if *ap_at.concl()
        != Formula::imp(Formula::and(sv, mem_pair), Formula::eq(app_t.clone(), ty.clone()))
    {
        return None
    }
    let j_eq = hyp_mp(&a1i(&ap_at, j), &hyp_and(&j_sv, &j_pair)?)?;
    let w = env.fresh_var();
    let j_goal = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &j_eq)?, w, &Formula::mem(Term::var(w), tb.clone()))?,
        &j_yb,
    )?;

    let out = discharge(y, &h_ex, &j_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(app_t, tb)),
        "funspace_app_mem: unexpected shape"
    );
    Some(gen_all(&[av, bv, f, x], &out))
}

/// `∀x. (x ∈ a → app(f,x) ∈ c)` — every value `f` takes on `a` lies in `c`.
///
/// The constant-fibre counterpart of [`is_section`], and the hypothesis
/// [`funspace_retarget`] swaps a codomain under.
pub fn values_in(env: &mut Env, ap: &Apply, a: &Term, c: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx), c.clone()),
        ),
    )
}

/// `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ (∀x. (x ∈ a → app(f,x) ∈ c))) → f ∈ fs(a,c))`
/// — the codomain of a function space may be replaced by any set the function's
/// values lie in.
///
/// All three clauses of `isfun` move across. Single-valuedness does not mention
/// the codomain at all. Totality does, and needs the value the old codomain
/// supplies to be recognised as `app(f,x)`, which is [`app_of_pair`]. The subset
/// clause is the same step once more: a member of `f` is a pair `⟨x,y⟩` with
/// `x ∈ a` and `y ∈ b`, and `y` is again `app(f,x)`, so it is in `c` and the
/// pair is in `prod(a,c)`.
///
/// **No inhabitation anywhere**, and that is the point: on an empty domain the
/// hypothesis is vacuous and so is every clause, so this says `fs(∅,b)` and
/// `fs(∅,c)` have the same members for *any* `b` and `c` — which is exactly the
/// degenerate case that a route through `⋃img(A) = B` would have lost.
pub fn funspace_retarget(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    app_pair: &Thm,
) -> Option<Thm> {
    let (av, bv, cv, f) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, tf) = (Term::var(av), Term::var(bv), Term::var(cv), Term::var(f));
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));

    // The hypothesis, rebuilt at our own `x` so that it can be opened.
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let app_t = ap.apply(tf.clone(), tx.clone());
    let vi_body = Formula::imp(mem_xa.clone(), Formula::mem(app_t.clone(), tc.clone()));
    let vi = Formula::forall(x, vi_body.clone());
    debug_assert_eq!(vi, values_in(env, ap, &ta, &tc, &tf), "funspace_retarget: shape drift");

    let mem_fs_b = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));
    let mem_fs_c = Formula::mem(tf.clone(), fsp.of(ta.clone(), tc.clone()));
    let h = Formula::and(mem_fs_b.clone(), vi.clone());

    let (isfun_b, sub_b, total_b, sv) = isfun_parts(env, ap, p, &ta, &tb, &tf)?;
    let (isfun_c, sub_c, total_c, sv_c) = isfun_parts(env, ap, p, &ta, &tc, &tf)?;
    if sv != sv_c {
        return None
    }
    let fs_at_b = inst_all(&fsp.fs_ax, &[ta.clone(), tb.clone(), tf.clone()])?;
    if *fs_at_b.concl() != Formula::iff(mem_fs_b.clone(), isfun_b) {
        return None
    }
    let fs_at_c = inst_all(&fsp.fs_ax, &[ta.clone(), tc.clone(), tf.clone()])?;
    if *fs_at_c.concl() != Formula::iff(mem_fs_c, isfun_c) {
        return None
    }

    let rest_b = Formula::and(total_b.clone(), sv.clone());
    let h_isfun = syl(&and_left(mem_fs_b.clone(), vi.clone()), &iff_mp(&fs_at_b)?)?;
    let h_sub_b = syl(&h_isfun, &and_left(sub_b.clone(), rest_b.clone()))?;
    let h_rest = syl(&h_isfun, &and_right(sub_b.clone(), rest_b))?;
    let h_total_b = syl(&h_rest, &and_left(total_b.clone(), sv.clone()))?;
    let h_sv = syl(&h_rest, &and_right(total_b.clone(), sv.clone()))?;
    let h_vi = and_right(mem_fs_b, vi.clone());

    // The instance of [`app_of_pair`] every clause below cashes in.
    let pair_xy = ap.sets.pair(tx.clone(), ty.clone());
    let mem_pair = Formula::mem(pair_xy.clone(), tf.clone());
    let ap_at = inst_all(app_pair, &[tf.clone(), tx.clone(), ty.clone()])?;
    if *ap_at.concl()
        != Formula::imp(
            Formula::and(sv.clone(), mem_pair.clone()),
            Formula::eq(app_t.clone(), ty.clone()),
        )
    {
        return None
    }

    // ── Totality, with the value moved into `c` ──────────────────────────────
    let mem_yb = Formula::mem(ty.clone(), tb.clone());
    let mem_yc = Formula::mem(ty.clone(), tc.clone());
    let body_b = Formula::and(mem_yb.clone(), mem_pair.clone());
    let body_c = Formula::and(mem_yc.clone(), mem_pair.clone());

    let k = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_ex_b = hyp_mp(
        &syl(&syl(&k_h, &h_total_b)?, &Thm::ax_inst(total_b, tx.clone())?)?,
        &k_xa,
    )?;
    debug_assert_eq!(
        *k_ex_b.concl(),
        Formula::imp(k.clone(), Formula::exists(y, body_b.clone())),
        "funspace_retarget: the totality clause has an unexpected shape"
    );
    let k_app_c =
        hyp_mp(&syl(&syl(&k_h, &h_vi)?, &Thm::ax_inst(vi.clone(), tx.clone())?)?, &k_xa)?;

    let j = Formula::and(k.clone(), body_b.clone());
    let j_k = and_left(k.clone(), body_b.clone());
    let j_body = and_right(k.clone(), body_b.clone());
    let j_pair = syl(&j_body, &and_right(mem_yb.clone(), mem_pair.clone()))?;
    let j_sv = syl(&j_k, &syl(&k_h, &h_sv)?)?;
    let j_eq = hyp_mp(&a1i(&ap_at, j), &hyp_and(&j_sv, &j_pair)?)?;
    let w1 = env.fresh_var();
    let j_yc = hyp_mp(
        &hyp_leibniz(&j_eq, w1, &Formula::mem(Term::var(w1), tc.clone()))?,
        &syl(&j_k, &k_app_c)?,
    )?;
    let j_ex_c = syl(
        &hyp_and(&j_yc, &j_pair)?,
        &exists_intro_imp(y, body_c.clone(), ty.clone())?,
    )?;
    let k_ex_c = discharge(y, &k_ex_b, &j_ex_c)?;
    let h_total_c = Thm::mp(
        &Thm::ax_dist(x, h.clone(), Formula::imp(mem_xa.clone(), Formula::exists(y, body_c)))?,
        &Thm::gen(x, &uncurry(&k_ex_c)?),
    )?;
    debug_assert_eq!(
        *h_total_c.concl(),
        Formula::imp(h.clone(), total_c),
        "funspace_retarget: the new totality clause has an unexpected shape"
    );

    // ── The graph sits inside `prod(a,c)` ────────────────────────────────────
    let mem_zf = Formula::mem(tz.clone(), tf.clone());
    let mem_z_prod_c = Formula::mem(tz.clone(), p.of(ta.clone(), tc.clone()));
    let eq_z_pair = Formula::eq(tz.clone(), pair_xy);

    let m = Formula::and(h.clone(), mem_zf.clone());
    let m_h = and_left(h.clone(), mem_zf.clone());
    let m_zf = and_right(h.clone(), mem_zf.clone());
    let m_zprod =
        hyp_mp(&syl(&syl(&m_h, &h_sub_b)?, &Thm::ax_inst(sub_b, tz.clone())?)?, &m_zf)?;
    let prod_at_b = inst_all(&p.prod_ax, &[ta.clone(), tb.clone(), tz.clone()])?;
    let inner_b = Formula::exists(y, Formula::and(mem_yb.clone(), eq_z_pair.clone()));
    let outer_b = Formula::and(mem_xa.clone(), inner_b.clone());
    if *prod_at_b.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), p.of(ta.clone(), tb.clone())),
            Formula::exists(x, outer_b.clone()),
        )
    {
        return None
    }
    let m_ex = syl(&m_zprod, &iff_mp(&prod_at_b)?)?;

    let n = Formula::and(m.clone(), outer_b.clone());
    let n_m = and_left(m.clone(), outer_b.clone());
    let n_outer = and_right(m.clone(), outer_b.clone());
    let n_xa = syl(&n_outer, &and_left(mem_xa.clone(), inner_b.clone()))?;
    let n_inner = syl(&n_outer, &and_right(mem_xa.clone(), inner_b))?;

    let body_pair_b = Formula::and(mem_yb.clone(), eq_z_pair.clone());
    let pf = Formula::and(n.clone(), body_pair_b.clone());
    let p_n = and_left(n.clone(), body_pair_b.clone());
    let p_body = and_right(n, body_pair_b);
    let p_zeq = syl(&p_body, &and_right(mem_yb, eq_z_pair.clone()))?;
    let p_zf = syl(&p_n, &syl(&n_m, &m_zf)?)?;
    let w2 = env.fresh_var();
    let p_pair_f = hyp_mp(
        &hyp_leibniz(&p_zeq, w2, &Formula::mem(Term::var(w2), tf.clone()))?,
        &p_zf,
    )?;
    let p_sv = syl(&p_n, &syl(&n_m, &syl(&m_h, &h_sv)?)?)?;
    let p_eq = hyp_mp(&a1i(&ap_at, pf), &hyp_and(&p_sv, &p_pair_f)?)?;

    let p_xa = syl(&p_n, &n_xa)?;
    let p_vi = syl(&p_n, &syl(&n_m, &syl(&m_h, &h_vi)?)?)?;
    let p_app_c = hyp_mp(&syl(&p_vi, &Thm::ax_inst(vi, tx.clone())?)?, &p_xa)?;
    let w3 = env.fresh_var();
    let p_yc =
        hyp_mp(&hyp_leibniz(&p_eq, w3, &Formula::mem(Term::var(w3), tc.clone()))?, &p_app_c)?;

    let body_pair_c = Formula::and(mem_yc.clone(), eq_z_pair);
    let inner_c = Formula::exists(y, body_pair_c.clone());
    let outer_c = Formula::and(mem_xa, inner_c.clone());
    let p_inner_c =
        syl(&hyp_and(&p_yc, &p_zeq)?, &exists_intro_imp(y, body_pair_c, ty)?)?;
    let p_outer_c = syl(
        &hyp_and(&p_xa, &p_inner_c)?,
        &exists_intro_imp(x, outer_c.clone(), tx)?,
    )?;
    let prod_at_c = inst_all(&p.prod_ax, &[ta.clone(), tc.clone(), tz.clone()])?;
    if *prod_at_c.concl() != Formula::iff(mem_z_prod_c.clone(), Formula::exists(x, outer_c)) {
        return None
    }
    let p_goal = syl(&p_outer_c, &iff_mpr(&prod_at_c)?)?;

    let n_goal = discharge(y, &n_inner, &p_goal)?;
    let m_goal = discharge(x, &m_ex, &n_goal)?;
    let h_sub_c = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_zf, mem_z_prod_c))?,
        &Thm::gen(z, &uncurry(&m_goal)?),
    )?;
    debug_assert_eq!(
        *h_sub_c.concl(),
        Formula::imp(h.clone(), sub_c),
        "funspace_retarget: the new subset clause has an unexpected shape"
    );

    // ── The three clauses, reassembled ───────────────────────────────────────
    let out = syl(&hyp_and(&h_sub_c, &hyp_and(&h_total_c, &h_sv)?)?, &iff_mpr(&fs_at_c)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tf, fsp.of(ta, tc))),
        "funspace_retarget: unexpected shape"
    );
    Some(gen_all(&[av, bv, cv, f], &out))
}

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
    let intro = union_intro(env, &ap.sets, img_t, bx, app_fx.clone())?;
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

// ─────────────────────────────────────────────────────────────────────────────
// Lean's lambda typing rule: a lambda graph is a member of the dependent
// product over its fibres.
//
// `⟦λx:A. e⟧` is the graph `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }` and `⟦Π(x:A). B x⟧`
// is `dprod(A)`, so the rule the checker needs is
//
//     (∀x ∈ A. t(x) ∈ b(x))  →  lam(A) ∈ dprod(A)
//
// and `dprod_ax` — unconditional — reduces it to the two clauses of `L`:
//
//   1. `lam(A) ∈ fs(A, ⋃img(A))`, i.e. the graph really is a function;
//   2. `∀x ∈ A. app(lam(A), x) ∈ b(x)`, which `beta_conditional` turns into the
//      hypothesis itself.
//
// Clause 1 is the work, and it is worth stating on its own: nothing in it
// mentions the fibres. [`lam_in_funspace`] proves `lam(A) ∈ fs(A,C)` for *any*
// codomain the body lands in, and [`lam_in_dprod`] applies it at
// `C := ⋃img(A)`, which the hypothesis reaches because `b(x)` is a member of
// the fibre image whenever `x ∈ A`.
//
// The three clauses of `isfun(lam(A))` come from different places. Totality is
// the graph's characteristic axiom read forwards — `⟨x,t(x)⟩ ∈ lam(A)` for
// `x ∈ A`, witnessed by `x` itself. The subset clause is the same axiom read
// backwards: a member of the graph *is* a pair `⟨x,t(x)⟩` with `x ∈ A`.
// Single-valuedness is the only one that needs [`crate::pairs::opair_inj`], and
// it is the only one that needs **no hypothesis at all** — a graph over a
// function symbol cannot relate one point to two values whatever the codomain.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀x. (x ∈ a → t(x) ∈ c)` — the body lands in `c` at every point of `a`.
///
/// The hypothesis [`lam_in_funspace`] consumes. Note this is *not*
/// [`values_in`]: that one speaks of `app(f,x)` for a function `f` given as a
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

// ─────────────────────────────────────────────────────────────────────────────
// Lean's Π typing rule: a dependent product lands in a universe.
//
// Everything above the base set is already available, and each step is one of
// the two closure properties `crate::universe` proves for `U(x)`:
//
//     dprod(A) ⊆ fs(A, ⋃img(A))          — `DProd::dprod_sub`, unconditional
//     fs(a,b)  ⊆ 𝒫(prod(a,b))            — `funspace_subset_pow_prod`
//     prod(a,b) ⊆ 𝒫𝒫(a ∪ b)              — `product_subset_pow_pow`
//
// so `crate::funspace::funspace_in_universe_of` already carries the middle two
// and [`dprod_in_universe_of`] adds the first with one more `C₂`. What is left
// is a **single** membership: `(A ∪ ⋃img(A)) ∈ U(c)`.
//
// # What is missing, exactly
//
// The form the checker wants is
//
//     (A ∈ U(c) ∧ ∀x ∈ A. b(x) ∈ U(c))  →  dprod(A) ∈ U(c)
//
// and it is **not** delivered here. Discharging `(A ∪ ⋃img(A)) ∈ U(c)` from
// that hypothesis needs three things `U(x)` is not known to have:
//
//   * closure under Replacement, to put `img(A) = { b(x) : x ∈ A }` in `U(c)`;
//   * closure under `⋃`, to put `⋃img(A)` there — `C₂` gives subsets of
//     members, never members of members, and Tarski's universes are not
//     transitive (see `Thm::ax_empty`'s note);
//   * closure under binary union — equivalently under pairing, since `a ∪ b` is
//     `⋃{a,b}` — which is the obstruction
//     [`crate::funspace::funspace_in_universe_of`] already carries, and which
//     needs the inaccessibility clause: `{a,b} ⊆ U(c)`, so `{a,b} ∈ U(c)`
//     unless `{a,b} ≈ U(c)`. Inaccessibility for `U(x)` is open — see
//     [`crate::universe::inaccessibility_reduction`] and the Cantor–Schröder–
//     Bernstein argument it reduces to.
//
// No axiom is added to route around any of it. What *is* delivered is the
// reduction — [`dprod_in_universe_of`], which is exactly as strong as
// `funspace_in_universe_of` and no weaker — together with the one instance
// whose antecedent discharges itself: at `c := A ∪ ⋃img(A)` the antecedent
// becomes `x ∈ U(x)`, which is [`crate::universe::mem_least_universe`]. So
// [`dprod_in_universe`] is **unconditional**. It is the dependent analogue of
// `funspace_in_universe`, and reached by the same move: not by closing `U`
// under the union, but by choosing the universe *after* the union is formed.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀c. ((A ∪ ⋃img(A)) ∈ U(c) → dprod(A) ∈ U(c))` — the dependent product
/// lands in any universe its base set does.
///
/// `dprod(A)` is a subset of `fs(A, ⋃img(A))` outright ([`DProd::dprod_sub`],
/// unconditional), so `C₂` — closure under subsets of members — carries it in
/// as soon as the function space is there, and that is
/// [`crate::funspace::funspace_in_universe_of`] verbatim. **The antecedent is
/// the same one that lemma carries**; nothing is lost and nothing new is
/// assumed. See the section comment for why it cannot be discharged from
/// `A ∈ U(c)` and `∀x ∈ A. b(x) ∈ U(c)`.
///
/// `c2` must be `⊢ ∀x. C₂(U(x))`
/// ([`crate::universe::least_universe_closed_sub`]) and `fs_in_u`
/// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))`, for the same `lu` and the
/// same `fsp`; `dp` must be the [`DProd`] built over `ap` and `fsp`. All of that
/// is checked — the two theorems are rebuilt at our own terms and compared — so
/// a mismatched stack is refused rather than silently described.
pub fn dprod_in_universe_of(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    dp: &DProd,
    lu: FnSym,
    c2: &Thm,
    fs_in_u: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let w = Term::apply(lu, vec![tc.clone()]); // U(c)

    let u = base_of(ap, dp.img, &ta); // ⋃img(A)
    let un = crate::funspace::bin_union(&ap.sets, ta.clone(), u.clone()); // A ∪ ⋃img(A)
    let fs_t = fsp.of(ta.clone(), u.clone());
    let dp_t = dp.of(ta.clone());
    let h = Formula::mem(un, w.clone());

    // `H → fs(A,⋃img(A)) ∈ U(c)`, which is the whole of the function-space chain.
    let fs_at = inst_all(fs_in_u, &[ta.clone(), u, tc.clone()])?;
    if *fs_at.concl() != Formula::imp(h.clone(), Formula::mem(fs_t.clone(), w.clone())) {
        return None
    }

    // `C₂(U(c))`, and the subset step it licenses.
    let c2_at = inst_all(c2, std::slice::from_ref(&tc))?;
    if *c2_at.concl() != crate::universe::closed_sub(env, &w) {
        return None
    }
    let sc = crate::funspace::sub_closed(&c2_at, &fs_t, &dp_t)?;

    let sub = inst_all(&dp.dprod_sub, std::slice::from_ref(&ta))?;
    if *sub.concl() != kernel::thm::subset(env, dp_t.clone(), fs_t) {
        return None
    }

    let out = hyp_mp(&syl(&fs_at, &sc)?, &a1i(&sub, h.clone()))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(dp_t, w)),
        "dprod_in_universe_of: unexpected shape"
    );
    Some(gen_all(&[av, cv], &out))
}

/// `⊢ ∀A. dprod(A) ∈ U(A ∪ ⋃img(A))` — **unconditional**: every dependent
/// product lands in a universe, named explicitly.
///
/// [`dprod_in_universe_of`] does the work; all that is left is to instantiate
/// its universe parameter at the very set its antecedent is about. The
/// antecedent then reads `(A ∪ ⋃img(A)) ∈ U(A ∪ ⋃img(A))`, which is
/// [`crate::universe::mem_least_universe`], and it discharges itself.
///
/// This is the dependent analogue of
/// [`crate::funspace::funspace_in_universe`], and it is reached the same way:
/// the binary union that blocks the general form is not closed over but stepped
/// around, by choosing the universe after the union has been formed. What it
/// does *not* give is membership in a universe fixed in advance — going from
/// `U(A ∪ ⋃img(A))` to a prescribed `U(c)` needs `U(c)` to be a universe, whose
/// inaccessibility clause is open, and is in any case what
/// [`dprod_in_universe_of`] already states directly.
pub fn dprod_in_universe(
    env: &mut Env,
    ap: &Apply,
    dp: &DProd,
    lu: FnSym,
    mem_lu: &Thm,
    general: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let av = env.fresh_var();
    let ta = Term::var(av);
    let un = crate::funspace::bin_union(&ap.sets, ta.clone(), base_of(ap, dp.img, &ta));
    let w = Term::apply(lu, vec![un.clone()]);

    let self_mem = inst_all(mem_lu, std::slice::from_ref(&un))?;
    if *self_mem.concl() != Formula::mem(un.clone(), w.clone()) {
        return None
    }

    let inst = inst_all(general, &[ta.clone(), un])?;
    let out = Thm::mp(&inst, &self_mem)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(dp.of(ta), w),
        "dprod_in_universe: unexpected shape"
    );
    Some(Thm::gen(av, &out))
}
