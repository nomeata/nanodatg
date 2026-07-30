//! Extensionality for lambda graphs.
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
//! # The shape of the argument
//!
//! Both `lam` and `lam'` come with a characteristic axiom of the form
//!
//! ```text
//! ⊢ ∀A ∀y. (y ∈ lam(A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(x)⟩))
//! ```
//!
//! so a member of the left is `⟨x, t(x)⟩` for some `x ∈ A`. Under the two
//! hypotheses `A = A'` and `∀x ∈ A. t(x) = t'(x)`, that same `x` witnesses
//! membership in the right: `x ∈ A'` by Leibniz on the domains, and
//! `⟨x, t(x)⟩ = ⟨x, t'(x)⟩` by Leibniz on the second component — the ordered
//! pair is a *term composition* (`upair(upair(x,x), upair(x, ·))`), so
//! congruence for it is a single `eq_leibniz` with the hole in the right place
//! rather than a separate lemma.
//!
//! The converse direction is the mirror image, needing symmetry of `=` twice:
//! once to get `x ∈ A` from `x ∈ A'` (which is what makes the pointwise
//! hypothesis, stated over `A`, applicable), and once to turn `t(x) = t'(x)`
//! around.
//!
//! Everything runs in the `⊢ H → φ` style the rest of this crate uses, with
//! `H` the conjunction of the two hypotheses; there is no deduction theorem, so
//! the implication is assembled rather than discharged.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{cases, hyp_mp2, hyp_syl, or_intro_left, or_intro_right, Apply};
use crate::funspace::Funspace;
use crate::{
    a1i, and_left, and_right, com12, contrapos, eq_symm_imp, exists_elim_imp, exists_intro_imp,
    gen_all, hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all, syl, uncurry,
};

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A')))`
/// — lambda graph extensionality.
///
/// `lam`/`lam_ax` and `lam2`/`lam2_ax` must be the graph symbol and
/// characteristic theorem produced by [`crate::funcs::lambda`] for the unary
/// body symbols `t` and `t2` respectively. The `debug_assert`s below pin that:
/// if either axiom has a different shape the derivation would still be sound
/// but would prove something about the wrong sets, and silently.
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
    let ext = Thm::ax_extensionality(env);
    let (av, av2, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    let lam_t = Term::apply(lam, vec![ta.clone()]); // lam(A)
    let lam2_t = Term::apply(lam2, vec![ta2.clone()]); // lam'(A')
    let val1 = Term::apply(t, vec![tx.clone()]); // t(x)
    let val2 = Term::apply(t2, vec![tx.clone()]); // t'(x)
    let pair1 = ap.sets.pair(tx.clone(), val1.clone()); // ⟨x, t(x)⟩
    let pair2 = ap.sets.pair(tx.clone(), val2.clone()); // ⟨x, t'(x)⟩

    // The two hypotheses, and their conjunction `H`.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let pointwise = Formula::forall(
        x,
        Formula::imp(Formula::mem(tx.clone(), ta.clone()), Formula::eq(val1.clone(), val2.clone())),
    );
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    // The two membership conditions, exactly as `lambda` states them.
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

    let lam_at_y = inst_all(lam_ax, &[ta.clone(), ty.clone()])?;
    debug_assert_eq!(
        *lam_at_y.concl(),
        Formula::iff(mem_y1.clone(), ex1.clone()),
        "lam_ext: the first graph's characteristic axiom has an unexpected shape"
    );
    let lam2_at_y = inst_all(lam2_ax, &[ta2.clone(), ty.clone()])?;
    debug_assert_eq!(
        *lam2_at_y.concl(),
        Formula::iff(mem_y2.clone(), ex2.clone()),
        "lam_ext: the second graph's characteristic axiom has an unexpected shape"
    );

    // ── Forward: a member of lam(A) is a member of lam'(A') ──────────────────
    // Under `K := H ∧ (x ∈ A ∧ y = ⟨x,t(x)⟩)`, the same `x` witnesses the
    // right-hand condition.
    let k = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    // K → t(x) = t'(x): the pointwise hypothesis at this very `x`.
    let k_tt = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    // K → x ∈ A', by Leibniz along `A = A'`.
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k.clone()), &k_dom)?, &k_xa)?;
    // K → y = ⟨x, t'(x)⟩. The pair is a term composition, so congruence in its
    // second component is Leibniz with the hole there.
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(
        val1.clone(),
        val2.clone(),
        w2,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w2))),
    );
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k.clone()), &k_tt)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    // Discharge the witness: `⊢ H → ((∃x. body₁) → ∃x. body₂)`.
    let fwd_ex = com12(&exists_elim_imp(
        x,
        &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?),
        &Formula::imp(h.clone(), ex2.clone()),
    )?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&lam2_at_y)?, h.clone()),
    )?;
    debug_assert_eq!(
        *h_fwd.concl(),
        Formula::imp(h.clone(), Formula::imp(mem_y1.clone(), mem_y2.clone())),
        "lam_ext: the forward half has an unexpected shape"
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

    let j_tt = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_tt_symm = syl(&j_tt, &eq_symm_imp(env, val1.clone(), val2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(
        val2.clone(),
        val1.clone(),
        w4,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w4))),
    );
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j.clone()), &j_tt_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex = com12(&exists_elim_imp(
        x,
        &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?),
        &Formula::imp(h.clone(), ex1.clone()),
    )?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&lam_at_y)?, h.clone()),
    )?;
    debug_assert_eq!(
        *h_bwd.concl(),
        Formula::imp(h.clone(), Formula::imp(mem_y2.clone(), mem_y1.clone())),
        "lam_ext: the backward half has an unexpected shape"
    );

    // ── Same members, hence equal ────────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?,
        &Thm::gen(y, &h_iff),
    )?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[lam_t.clone(), lam2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(lam_t, lam2_t))),
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
    let a = env.fresh_var();
    let ta = Term::var(a);
    let inst = inst_all(lam_ext_thm, &[ta.clone(), ta.clone()])?;
    let (ante, _) = inst.concl().as_imp()?;
    // The antecedent must be the reflexive equation the instantiation created;
    // anything else means this is not a `lam_ext` conclusion.
    if ante != Formula::eq(ta.clone(), ta.clone()) {
        return None
    }
    let out = Thm::mp(&inst, &Thm::eq_refl(ta))?;
    debug_assert!(out.concl().as_imp().is_some(), "lam_ext_same_domain: unexpected shape");
    Some(Thm::gen(a, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Small combinators, copied rather than imported.
//
// The neighbouring modules keep these private, and `funspace` already keeps its
// own copies for the same reason: a derivation this long should not break when
// one of them is reshaped. Reading formulas apart is untrusted and safe — no
// `Thm` is produced by any of it.
// ─────────────────────────────────────────────────────────────────────────────

/// Decompose `φ ↔ ψ` into its two implication halves.
fn split_iff(iff: &Formula) -> Option<(Formula, Formula)> {
    let (inner, _) = iff.as_imp()?;
    let (fwd, nb) = inner.as_imp()?;
    let (bwd, _) = nb.as_imp()?;
    Some((fwd, bwd))
}

/// From `⊢ K → ψ`, `⊢ K → (l ∨ r)` and `⊢ K → (r → ¬ψ)` infer `⊢ K → l`.
fn or_resolve_left(k_psi: &Thm, k_disj: &Thm, k_r_np: &Thm) -> Option<Thm> {
    let (k, disj) = k_disj.concl().as_imp()?;
    let (nl, r) = disj.as_imp()?;
    let (l, _) = nl.as_imp()?;
    let (_, psi) = k_psi.concl().as_imp()?;

    let bridge = a1i(&crate::syl_imp(nl.clone(), r, Formula::not(psi.clone())), k.clone());
    let k_nl_np = hyp_mp(&hyp_mp(&bridge, k_disj)?, k_r_np)?;
    let k_nl_psi = syl(k_psi, &Thm::ax_k(psi, nl.clone()))?;
    let k_nl_false = hyp_mp2(&k_nl_np, &k_nl_psi)?;
    let bridge2 = a1i(&crate::syl_imp(nl, Formula::false_(), l.clone()), k.clone());
    let k_nl_l = hyp_mp(&hyp_mp(&bridge2, &k_nl_false)?, &a1i(&crate::ex_falso(l), k))?;
    crate::hyp_or_same(&k_nl_l)
}

/// From `⊢ H → ∀z. (φ(z) ↔ χ(z))` and `⊢ H → ∃s ∀z. (z ∈ s ↔ φ(z))` infer
/// `⊢ H → ∃s ∀z. (z ∈ s ↔ χ(z))`.
fn retarget(z: FreeVar, sv: FreeVar, h_iff: &Thm, h_ex: &Thm) -> Option<Thm> {
    let (h, all_iff) = h_iff.concl().as_imp()?;
    let iff_at_z = Thm::ax_inst(all_iff.clone(), Term::var(z))?;
    let (_, iff) = iff_at_z.concl().as_imp()?;
    let (fwd, _) = split_iff(&iff)?;
    let (phi, chi) = fwd.as_imp()?;

    let ts = Term::var(sv);
    let mem_zs = Formula::mem(Term::var(z), ts.clone());
    let p_phi = Formula::forall(z, Formula::iff(mem_zs.clone(), phi));
    let p_chi = Formula::forall(z, Formula::iff(mem_zs.clone(), chi.clone()));
    debug_assert_eq!(
        h_ex.concl().as_imp()?.1,
        Formula::exists(sv, p_phi.clone()),
        "retarget: the existential has an unexpected shape"
    );

    let j = Formula::and(h.clone(), p_phi.clone());
    let j_iff1 =
        syl(&and_right(h.clone(), p_phi.clone()), &Thm::ax_inst(p_phi.clone(), Term::var(z))?)?;
    let j_iff2 = syl(&and_left(h.clone(), p_phi.clone()), &syl(h_iff, &iff_at_z)?)?;
    let j_fwd = hyp_syl(&crate::hyp_iff_mp(&j_iff1)?, &crate::hyp_iff_mp(&j_iff2)?)?;
    let j_bwd = hyp_syl(&crate::hyp_iff_mpr(&j_iff2)?, &crate::hyp_iff_mpr(&j_iff1)?)?;
    let j_iff = hyp_and(&j_fwd, &j_bwd)?;
    let j_q = Thm::mp(&Thm::ax_dist(z, j, Formula::iff(mem_zs, chi))?, &Thm::gen(z, &j_iff))?;

    let ex_chi = Formula::exists(sv, p_chi.clone());
    let h_p_ex = hyp_syl(&uncurry(&j_q)?, &a1i(&exists_intro_imp(sv, p_chi, ts)?, h.clone()))?;
    let elim =
        exists_elim_imp(sv, &Thm::gen(sv, &com12(&h_p_ex)?), &Formula::imp(h.clone(), ex_chi))?;
    hyp_mp(&syl(h_ex, &elim)?, &imp_refl(h))
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
// # Why the definition carries a default, again
//
// The dependent product really can be empty — take any `x ∈ A` with `b(x)`
// empty — so the only Separation available here
// ([`crate::funcs::separation_nonempty`]) does not apply, for exactly the
// reason spelled out in [`crate::funspace`]: without `∅` there is no way to
// name the set that `dprod(A)` should be when there are no sections at all.
// The way out is the same one [`crate::funspace::funspace`] and
// [`crate::funcs::collection`] take — define the disjunctive condition
//
//     f ∈ dprod(A)  ↔  L(f)  ∨  (¬∃g. L(g)  ∧  f ∈ fs(A, ⋃img(A)))
//
// so the symbol is total. When a section exists the second disjunct is dead and
// the intended condition is recovered ([`dprod_members`]); when none does, the
// set degenerates to the whole function space, which is harmless because
// [`dprod_subset_funspace`] — the unconditional half — holds either way.
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
    /// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ (L(f) ∨ (¬∃g. L(g) ∧ f ∈ fs(A,⋃img(A)))))` —
    /// the raw defining axiom, default disjunct and all.
    pub dprod_def: Thm,
    /// `⊢ ∀A. ((∃g. L(g)) → ∀f. (f ∈ dprod(A) ↔ L(f)))`, where `L(f)` is
    /// `f ∈ fs(A,⋃img(A)) ∧ ∀x. (x ∈ A → app(f,x) ∈ b(x))`.
    pub dprod_ax: Thm,
    /// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))` — unconditional.
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

/// The membership condition actually defined, and its ingredients:
/// `(L, NE, φ)` where `L(f)` is `f ∈ fs(A,⋃img(A)) ∧ section(f)`, `NE` is
/// `∃f. L(f)`, and `φ(f) := L(f) ∨ (¬NE ∧ f ∈ fs(A,⋃img(A)))`.
fn dprod_cond(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    a: &Term,
    f: FreeVar,
) -> (Formula, Formula, Formula, Term) {
    let tf = Term::var(f);
    let fs_t = fsp.of(a.clone(), base_of(ap, img, a));
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let l = Formula::and(mem_fs.clone(), is_section(env, ap, b, a, &tf));
    let ne = Formula::exists(f, l.clone());
    let rgt = Formula::and(Formula::not(ne.clone()), mem_fs);
    let phi = Formula::or(l.clone(), rgt);
    (l, ne, phi, fs_t)
}

/// Introduce `dprod(A) = Π(x:A). b(x)`; see the section comment for why the
/// defining condition carries a default disjunct.
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

    let (l, ne, phi, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);
    let rgt = Formula::and(Formula::not(ne.clone()), mem_fs.clone());
    debug_assert_eq!(l, Formula::and(mem_fs.clone(), psi.clone()), "dprod: condition shape drift");

    // ── There is a section: Separation applies, and the default is dead ──────
    // `separation_nonempty` produces exactly `NE → ∃s ∀f. (f ∈ s ↔ L(f))`,
    // since `L(f)` *is* the carved condition `f ∈ fs ∧ ψ(f)`.
    let sep = crate::funcs::separation_nonempty(env, f, &psi, &fs_t)?;
    debug_assert_eq!(sep.concl().as_imp()?.0, ne, "dprod: Separation's antecedent has drifted");

    let ne_l_phi = a1i(&or_intro_left(l.clone(), rgt.clone()), ne.clone());
    let k = Formula::and(ne.clone(), phi.clone());
    let k_r_np = a1i(&and_left(Formula::not(ne.clone()), mem_fs.clone()), k);
    let k_l = or_resolve_left(
        &and_left(ne.clone(), phi.clone()),
        &and_right(ne.clone(), phi.clone()),
        &k_r_np,
    )?;
    let ne_phi_l = uncurry(&k_l)?;
    let ne_all = Thm::mp(
        &Thm::ax_dist(f, ne.clone(), Formula::iff(l.clone(), phi.clone()))?,
        &Thm::gen(f, &hyp_and(&ne_l_phi, &ne_phi_l)?),
    )?;
    let sv = env.fresh_var();
    let pos = retarget(f, sv, &ne_all, &sep)?;

    // ── There is none: the condition degenerates to `f ∈ fs(A,⋃img(A))` ──────
    let nne = Formula::not(ne.clone());
    let nne_nl = contrapos(&exists_intro_imp(f, l.clone(), tf.clone())?)?;
    let k2_nl = syl(&and_left(nne.clone(), phi.clone()), &nne_nl)?;
    let k2_r = hyp_mp(&and_right(nne.clone(), phi.clone()), &k2_nl)?;
    let nne_phi_mem = uncurry(&syl(&k2_r, &and_right(nne.clone(), mem_fs.clone()))?)?;
    let k3_r = hyp_and(
        &and_left(nne.clone(), mem_fs.clone()),
        &and_right(nne.clone(), mem_fs.clone()),
    )?;
    let nne_mem_phi = uncurry(&syl(&k3_r, &or_intro_right(l, rgt))?)?;
    let nne_all = Thm::mp(
        &Thm::ax_dist(f, nne.clone(), Formula::iff(mem_fs, phi.clone()))?,
        &Thm::gen(f, &hyp_and(&nne_mem_phi, &nne_phi_mem)?),
    )?;
    let sv2 = env.fresh_var();
    let p_s = Formula::forall(f, Formula::iff(Formula::mem(tf, Term::var(sv2)), phi.clone()));
    let neg = syl(&nne_all, &exists_intro_imp(sv2, p_s, fs_t)?)?;

    let existence = cases(&pos, &neg)?;
    crate::define_by_membership(env, &[av], &existence, f, &phi)
}

/// `⊢ ∀A. ((∃g. L(g)) → ∀f. (f ∈ dprod(A) ↔ L(f)))` — the members of the
/// dependent product are the sections.
///
/// The antecedent is the default disjunct being dead, and it cannot be dropped:
/// without an empty set there is no way to name the set `Π(x:A). b(x)` should
/// be when there are no sections at all. Compare
/// [`crate::funspace::funspace_members`], which carries the same antecedent for
/// the same reason.
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

    let (l, ne, phi, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t);
    let rgt = Formula::and(Formula::not(ne.clone()), mem_fs.clone());

    // `NE → (φ → L)`: the second disjunct carries `¬NE`, which `NE` refutes.
    let k = Formula::and(ne.clone(), phi.clone());
    let k_r_np = a1i(&and_left(Formula::not(ne.clone()), mem_fs), k);
    let k_l = or_resolve_left(
        &and_left(ne.clone(), phi.clone()),
        &and_right(ne.clone(), phi.clone()),
        &k_r_np,
    )?;
    let ne_phi_l = uncurry(&k_l)?;
    let ne_l_phi = a1i(&or_intro_left(l.clone(), rgt), ne.clone());

    let dp_at_f = inst_all(dp_def, &[ta.clone(), tf.clone()])?;
    let dp_t = Term::apply(dp, vec![ta.clone()]);
    debug_assert_eq!(
        *dp_at_f.concl(),
        Formula::iff(Formula::mem(tf.clone(), dp_t.clone()), phi),
        "dprod's defining axiom has an unexpected shape"
    );
    let mem_dp = Formula::mem(tf, dp_t);
    let ne_d_l = hyp_syl(&a1i(&iff_mp(&dp_at_f)?, ne.clone()), &ne_phi_l)?;
    let ne_l_d = hyp_syl(&ne_l_phi, &a1i(&iff_mpr(&dp_at_f)?, ne.clone()))?;

    let out = Thm::mp(
        &Thm::ax_dist(f, ne, Formula::iff(mem_dp, l))?,
        &Thm::gen(f, &hyp_and(&ne_d_l, &ne_l_d)?),
    )?;
    Some(gen_all(&[av], &out))
}

/// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`.
///
/// **Unconditional**, and that is the point of choosing the function space
/// itself as the default: a member of `dprod(A)` satisfies one disjunct or the
/// other, and each puts it in `fs(A, ⋃img(A))` — the first as the left conjunct
/// of `L`, the second outright.
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

    let (l, ne, phi, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);

    let l_mem = and_left(mem_fs.clone(), psi);
    debug_assert_eq!(*l_mem.concl(), Formula::imp(l, mem_fs.clone()), "dprod_subset: shape drift");
    let r_mem = and_right(Formula::not(ne), mem_fs.clone());
    let phi_mem = hyp_or_elim(
        &imp_refl(phi.clone()),
        &a1i(&l_mem, phi.clone()),
        &a1i(&r_mem, phi.clone()),
    )?;

    let dp_at_f = inst_all(dp_def, &[ta.clone(), tf.clone()])?;
    let dp_t = Term::apply(dp, vec![ta.clone()]);
    debug_assert_eq!(
        *dp_at_f.concl(),
        Formula::iff(Formula::mem(tf, dp_t.clone()), phi),
        "dprod's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&dp_at_f)?, &phi_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, dp_t, fs_t),
        "dprod_subset_funspace: unexpected shape"
    );
    Some(gen_all(&[av], &out))
}
