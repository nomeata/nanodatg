//! Separation, derived from the Replacement scheme.
//!
//! Separation is not one of the target theory's axioms — it is derivable from
//! Replacement, and per the project guideline anything constructible
//! conservatively is constructed rather than added.
//!
//! # What is derivable here, and what is not
//!
//! The standard route runs Replacement at the *choice relation*
//!
//! ```text
//! ψ(x, y) := (φ(x) ∧ y = x) ∨ (¬φ(x) ∧ y = u)
//! ```
//!
//! whose `∃!y` premise holds outright ([`choice_relation_unique`]), so long as
//! some default value `u` is available. When `u` can be chosen *inside* `a` and
//! satisfying `φ`, the image of `a` under `ψ` is exactly `{z ∈ a : φ(z)}` and
//! Separation follows with no further ingredients — that is
//! [`separation_nonvacuous`], and it needs neither Union nor an empty set.
//!
//! The remaining case is the vacuous one: when *no* element of `a` satisfies
//! `φ`, the separated set has no members, so producing it means producing an
//! empty set. **That is where the derivation genuinely stops.** An empty set is
//! not derivable from the axioms this kernel provides:
//!
//! * Separation itself yields one ([`empty_from_separation`] derives
//!   `∀z. z ∉ sep(a)` from a Separation axiom for a refutable condition), so
//!   assuming Separation to get it would be circular.
//! * Replacement cannot: the image of `a` under a total relation is empty only
//!   when `a` is.
//! * Regularity cannot on its own: a minimal element of `t` is empty only when
//!   `t` is transitive, and every non-empty transitive set already contains `∅`.
//! * Pairing, Union and Power all send non-empty sets to non-empty sets.
//!
//! The gap is not an artefact of this derivation; it is a genuine
//! independence. Build the sets generated from a `ℤ`-indexed membership chain
//! (`n = {n − 1}`, no least element, so nothing bottoms out at `∅`) by pairing,
//! union, *relative* power set — the set of non-empty subsets — and
//! replacement. Ranking each generated set one above the maximum of its
//! members keeps `∈` acyclic and well founded on every set, so Regularity
//! holds; Extensionality holds by construction; and every operation sends
//! non-empty sets to non-empty sets, so `∀x ∃y. y ∈ x` holds too. That
//! structure models Extensionality, Pairing, Union, Power, Replacement and
//! Regularity, and has no empty set. Hence no derivation from these axioms can
//! produce one, and Separation — which yields one immediately — is
//! underivable. Closing the gap needs a new axiom (Infinity is the usual
//! source), not more proof engineering.
//!
//! What this module therefore delivers is the whole derivation *relative to* an
//! empty set, with the dependency stated honestly as an antecedent rather than
//! smuggled in as an axiom: [`separation_existence`] proves
//!
//! ```text
//! ⊢ ∀a ∀e. (∀z. ¬(z ∈ e)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))
//! ```
//!
//! and [`separation`] turns a proof of `∀z. ¬(z ∈ e)` — once the theory has
//! one, e.g. from an Infinity axiom — into the defined symbol `sep_φ` with its
//! characteristic property, by conservative definitional extension.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, clavius, com12, contrapos, contrapos_imp, define_by_membership,
    eq_symm_imp, ex_falso, exists_elim_imp, exists_intro_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr,
    hyp_mp, hyp_or_elim, imp_mono_r, imp_refl, inst_all, mp_const, syl, syl_imp, uncurry,
};

// ─────────────────────────────────────────────────────────────────────────────
// Small propositional helpers.
//
// These are the shapes this derivation needs repeatedly and that the core
// toolkit does not already provide. They are ordinary derived rules: each is
// built from the kernel primitives via the combinators in the parent module.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ l → (l ∨ r)`.
///
/// `l ∨ r` is `¬l → r`, so this says a true left disjunct makes the antecedent
/// absurd; the consequent then follows by ex falso.
pub fn or_intro_left(l: Formula, r: Formula) -> Thm {
    let mono = imp_mono_r(&ex_falso(r), l).expect("or_intro_left: monotonicity applies");
    com12(&mono).expect("or_intro_left: com12 applies")
}

/// `⊢ r → (l ∨ r)`. Plain weakening, since `l ∨ r` is `¬l → r`.
pub fn or_intro_right(l: Formula, r: Formula) -> Thm { Thm::ax_k(r, Formula::not(l)) }

/// Syllogism under a fixed hypothesis: from `⊢ H → (a → b)` and
/// `⊢ H → (b → c)` infer `⊢ H → (a → c)`.
pub fn hyp_syl(hab: &Thm, hbc: &Thm) -> Option<Thm> {
    let (h, ab) = hab.concl().as_imp()?;
    let (a, b) = ab.as_imp()?;
    let (h2, bc) = hbc.concl().as_imp()?;
    let (b2, c) = bc.as_imp()?;
    if h != h2 || b != b2 {
        return None
    }
    let s = a1i(&syl_imp(a, b, c), h);
    hyp_mp(&hyp_mp(&s, hab)?, hbc)
}

/// From `⊢ H → ¬a` infer `⊢ H → (a → χ)`, for any `χ`.
pub fn hyp_ex_falso(h_not: &Thm, target: Formula) -> Option<Thm> {
    let (h, a_false) = h_not.concl().as_imp()?;
    let (a, f) = a_false.as_imp()?;
    if f != Formula::false_() {
        return None
    }
    let mono = imp_mono_r(&ex_falso(target), a)?;
    hyp_mp(&a1i(&mono, h), h_not)
}

// ─────────────────────────────────────────────────────────────────────────────
// The choice relation and its ∃! premise.
// ─────────────────────────────────────────────────────────────────────────────

/// The relation `ψ(x, y) := (φ(x) ∧ y = x) ∨ (¬φ(x) ∧ y = u)` fed to
/// Replacement.
///
/// It is *total and functional* whatever `φ` does: every `x` is sent either to
/// itself or to the default `u`. That is the whole trick — Replacement demands
/// a genuine function, and a bare `φ(x) ∧ y = x` is not one.
pub fn choice_relation(x: FreeVar, phi: &Formula, y: FreeVar, u: &Term) -> Formula {
    let ty = Term::var(y);
    Formula::or(
        Formula::and(phi.clone(), Formula::eq(ty.clone(), Term::var(x))),
        Formula::and(Formula::not(phi.clone()), Formula::eq(ty, u.clone())),
    )
}

/// `⊢ ∃!y. ψ(x, y)` for the choice relation, in the exact shape the kernel's
/// [`kernel::thm::exists_unique`] (and hence Replacement's premise) produces.
///
/// The proof is a case analysis on `φ(x)`: with `φ(x)` the unique value is `x`,
/// without it the unique value is `u`. Neither case needs any set-theoretic
/// input — this is pure propositional and equality reasoning. Since there is no
/// deduction theorem, the case split is run as Clavius' law over
/// `⊢ φ(x) → E` and `⊢ ¬φ(x) → E`.
pub fn choice_relation_unique(
    env: &mut Env,
    x: FreeVar,
    phi: &Formula,
    y: FreeVar,
    u: &Term,
) -> Option<Thm> {
    if x == y || phi.occurs_free(y) || u.occurs_free(y) || u.occurs_free(x) {
        return None
    }
    let (tx, ty) = (Term::var(x), Term::var(y));
    let psi = choice_relation(x, phi, y, u);

    let y2 = env.fresh_var();
    let ty2 = Term::var(y2);
    let uniq =
        Formula::forall(y2, Formula::imp(psi.subst(y, &ty2), Formula::eq(ty2.clone(), ty.clone())));
    let body = Formula::and(psi.clone(), uniq);
    let goal = Formula::exists(y, body.clone());

    let nf = Formula::not(phi.clone());

    // The two disjuncts of `ψ` at the uniqueness variable `y₂`.
    let l2 = Formula::and(phi.clone(), Formula::eq(ty2.clone(), tx.clone()));
    let r2 = Formula::and(nf.clone(), Formula::eq(ty2.clone(), u.clone()));
    let disj2 = Formula::or(l2, r2);
    debug_assert_eq!(psi.subst(y, &ty2), disj2, "choice relation does not substitute as expected");

    // ── Case φ(x): the witness is `x` ────────────────────────────────────────
    let l1 = Formula::and(phi.clone(), Formula::eq(tx.clone(), tx.clone()));
    let r1 = Formula::and(nf.clone(), Formula::eq(tx.clone(), u.clone()));
    let f_l1 = hyp_and(&imp_refl(phi.clone()), &a1i(&Thm::eq_refl(tx.clone()), phi.clone()))?;
    let f_psi = syl(&f_l1, &or_intro_left(l1, r1))?;
    debug_assert_eq!(*f_psi.concl(), Formula::imp(phi.clone(), psi.subst(y, &tx)));

    // Uniqueness, under `Z := φ(x) ∧ ψ[y₂/y]`.
    let z = Formula::and(phi.clone(), disj2.clone());
    let eq2x = Formula::eq(ty2.clone(), tx.clone());
    let z_disj = and_right(phi.clone(), disj2.clone());
    let z_left = a1i(&and_right(phi.clone(), eq2x.clone()), z.clone());
    // The right disjunct carries `¬φ(x)`, which the hypothesis contradicts.
    let f_r2_false = com12(&and_left(nf.clone(), Formula::eq(ty2.clone(), u.clone())))?;
    let z_r2_false = syl(&and_left(phi.clone(), disj2.clone()), &f_r2_false)?;
    let z_right = hyp_ex_falso(&z_r2_false, eq2x.clone())?;
    let f_imp = uncurry(&hyp_or_elim(&z_disj, &z_left, &z_right)?)?;
    let dist = Thm::ax_dist(y2, phi.clone(), Formula::imp(disj2.clone(), eq2x))?;
    let f_uniq = Thm::mp(&dist, &Thm::gen(y2, &f_imp))?;

    let f_body = hyp_and(&f_psi, &f_uniq)?;
    let f_goal = syl(&f_body, &exists_intro_imp(y, body.clone(), tx.clone())?)?;
    debug_assert_eq!(*f_goal.concl(), Formula::imp(phi.clone(), goal.clone()));

    // ── Case ¬φ(x): the witness is `u` ───────────────────────────────────────
    let l1u = Formula::and(phi.clone(), Formula::eq(u.clone(), tx.clone()));
    let r1u = Formula::and(nf.clone(), Formula::eq(u.clone(), u.clone()));
    let nf_r1 = hyp_and(&imp_refl(nf.clone()), &a1i(&Thm::eq_refl(u.clone()), nf.clone()))?;
    let nf_psi = syl(&nf_r1, &or_intro_right(l1u, r1u))?;
    debug_assert_eq!(*nf_psi.concl(), Formula::imp(nf.clone(), psi.subst(y, u)));

    let z2 = Formula::and(nf.clone(), disj2.clone());
    let eq2u = Formula::eq(ty2.clone(), u.clone());
    let z2_disj = and_right(nf.clone(), disj2.clone());
    let z2_right = a1i(&and_right(nf.clone(), eq2u.clone()), z2.clone());
    // The left disjunct carries `φ(x)`, which the hypothesis contradicts.
    let z2_nf = and_left(nf.clone(), disj2.clone());
    let z2_l2_f = a1i(&and_left(phi.clone(), Formula::eq(ty2.clone(), tx.clone())), z2.clone());
    let z2_left = hyp_ex_falso(&hyp_syl(&z2_l2_f, &z2_nf)?, eq2u.clone())?;
    let nf_imp = uncurry(&hyp_or_elim(&z2_disj, &z2_left, &z2_right)?)?;
    let dist2 = Thm::ax_dist(y2, nf.clone(), Formula::imp(disj2, eq2u))?;
    let nf_uniq = Thm::mp(&dist2, &Thm::gen(y2, &nf_imp))?;

    let nf_body = hyp_and(&nf_psi, &nf_uniq)?;
    let nf_goal = syl(&nf_body, &exists_intro_imp(y, body, u.clone())?)?;
    debug_assert_eq!(*nf_goal.concl(), Formula::imp(nf, goal.clone()));

    // ── Combine the cases ────────────────────────────────────────────────────
    let not_goal_to_goal = syl(&contrapos(&f_goal)?, &nf_goal)?;
    let out = Thm::mp(&clavius(goal.clone()), &not_goal_to_goal)?;
    debug_assert_eq!(*out.concl(), goal, "choice_relation_unique produced an unexpected shape");
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// The image of `a` under the choice relation is the separated subset.
// ─────────────────────────────────────────────────────────────────────────────

/// The membership condition Separation is after: `y ∈ a ∧ φ(y)`.
fn separated(x: FreeVar, phi: &Formula, y: FreeVar, a: FreeVar) -> Formula {
    let ty = Term::var(y);
    Formula::and(Formula::mem(ty.clone(), Term::var(a)), phi.subst(x, &ty))
}

/// Replacement's image condition, `∃x. (x ∈ a ∧ ψ(x, y))`, in exactly the shape
/// [`Thm::ax_replacement`] builds it.
fn image(x: FreeVar, a: FreeVar, psi: &Formula) -> Formula {
    Formula::exists(x, Formula::and(Formula::mem(Term::var(x), Term::var(a)), psi.clone()))
}

/// `⊢ (y ∈ a ∧ φ(y)) → ∃x. (x ∈ a ∧ ψ(x, y))`.
///
/// Everything Separation wants is in the image: an element of `a` satisfying
/// `φ` is its own witness, taking the left disjunct of `ψ`.
pub fn image_backward(x: FreeVar, phi: &Formula, y: FreeVar, a: FreeVar, u: &Term) -> Option<Thm> {
    let (tx, ty, ta) = (Term::var(x), Term::var(y), Term::var(a));
    let psi = choice_relation(x, phi, y, u);
    let good = separated(x, phi, y, a);
    let phi_y = phi.subst(x, &ty);

    // The disjuncts of `ψ(y, y)`, i.e. `ψ` with the domain variable at `y`.
    let left = Formula::and(phi_y.clone(), Formula::eq(ty.clone(), ty.clone()));
    let right = Formula::and(Formula::not(phi_y.clone()), Formula::eq(ty.clone(), u.clone()));

    let good_mem = and_left(Formula::mem(ty.clone(), ta.clone()), phi_y.clone());
    let good_phi = and_right(Formula::mem(ty.clone(), ta.clone()), phi_y);
    let good_refl = a1i(&Thm::eq_refl(ty.clone()), good.clone());
    let good_left = hyp_and(&good_phi, &good_refl)?;
    let good_psi = syl(&good_left, &or_intro_left(left, right))?;
    let good_body = hyp_and(&good_mem, &good_psi)?;

    let body = Formula::and(Formula::mem(tx, ta), psi);
    let intro = exists_intro_imp(x, body, ty)?;
    let out = syl(&good_body, &intro)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(good, image(x, a, &choice_relation(x, phi, y, u))),
        "image_backward produced an unexpected shape"
    );
    Some(out)
}

/// `⊢ (u ∈ a ∧ φ(u)) → (∃x. (x ∈ a ∧ ψ(x, y)) → (y ∈ a ∧ φ(y)))`.
///
/// Conversely nothing *but* the separated elements is in the image — provided
/// the default value `u` is itself one of them, which is precisely the
/// hypothesis. Without it the image would contain the junk value `u`, and this
/// is the step that would fail.
pub fn image_forward(
    env: &mut Env,
    x: FreeVar,
    phi: &Formula,
    y: FreeVar,
    a: FreeVar,
    u: FreeVar,
) -> Option<Thm> {
    if x == y || x == a || x == u || y == a || y == u || a == u {
        return None
    }
    if phi.occurs_free(y) || phi.occurs_free(a) || phi.occurs_free(u) {
        return None
    }
    let (tx, ty, ta, tu) = (Term::var(x), Term::var(y), Term::var(a), Term::var(u));
    let psi = choice_relation(x, phi, y, &tu);
    let good = separated(x, phi, y, a);
    let phi_u = phi.subst(x, &tu);

    // `H`: the default value is an element of `a` satisfying `φ`.
    let h = Formula::and(Formula::mem(tu.clone(), ta.clone()), phi_u.clone());
    // `C`: the body of the image existential, at a free `x`.
    let c = Formula::and(Formula::mem(tx.clone(), ta.clone()), psi.clone());
    // Work under `W := C ∧ H`.
    let w = Formula::and(c.clone(), h.clone());

    let left = Formula::and(phi.clone(), Formula::eq(ty.clone(), tx.clone()));
    let right = Formula::and(Formula::not(phi.clone()), Formula::eq(ty.clone(), tu.clone()));

    let w_c = and_left(c.clone(), h.clone());
    let w_h = and_right(c.clone(), h.clone());
    let w_disj = syl(&w_c, &and_right(Formula::mem(tx.clone(), ta.clone()), psi.clone()))?;
    let w_xa = syl(&w_c, &and_left(Formula::mem(tx.clone(), ta.clone()), psi))?;

    // ── Case `φ(x) ∧ y = x`: the element is `x` itself ───────────────────────
    let v = Formula::and(w.clone(), left.clone());
    let v_w = and_left(w.clone(), left.clone());
    let v_left = and_right(w.clone(), left.clone());
    let v_xa = syl(&v_w, &w_xa)?;
    let v_yx = syl(&v_left, &and_right(phi.clone(), Formula::eq(ty.clone(), tx.clone())))?;
    let v_xy = syl(&v_yx, &eq_symm_imp(env, ty.clone(), tx.clone()))?;
    let v_phix = syl(&v_left, &and_left(phi.clone(), Formula::eq(ty.clone(), tx.clone())))?;

    let w1 = env.fresh_var();
    let leib_mem = Thm::eq_leibniz(tx.clone(), ty.clone(), w1, Formula::mem(Term::var(w1), ta.clone()));
    let v_ya = hyp_mp(&hyp_mp(&a1i(&leib_mem, v.clone()), &v_xy)?, &v_xa)?;
    let leib_phi = Thm::eq_leibniz(tx.clone(), ty.clone(), x, phi.clone());
    let v_phiy = hyp_mp(&hyp_mp(&a1i(&leib_phi, v.clone()), &v_xy)?, &v_phix)?;
    let w_left = uncurry(&hyp_and(&v_ya, &v_phiy)?)?;

    // ── Case `¬φ(x) ∧ y = u`: the element is the default `u` ─────────────────
    let v2 = Formula::and(w.clone(), right.clone());
    let v2_w = and_left(w.clone(), right.clone());
    let v2_right = and_right(w.clone(), right.clone());
    let v2_h = syl(&v2_w, &w_h)?;
    let v2_ua = syl(&v2_h, &and_left(Formula::mem(tu.clone(), ta.clone()), phi_u.clone()))?;
    let v2_phiu = syl(&v2_h, &and_right(Formula::mem(tu.clone(), ta.clone()), phi_u))?;
    let v2_yu = syl(&v2_right, &and_right(Formula::not(phi.clone()), Formula::eq(ty.clone(), tu.clone())))?;
    let v2_uy = syl(&v2_yu, &eq_symm_imp(env, ty.clone(), tu.clone()))?;

    let w2 = env.fresh_var();
    let leib_mem_u = Thm::eq_leibniz(tu.clone(), ty.clone(), w2, Formula::mem(Term::var(w2), ta.clone()));
    let v2_ya = hyp_mp(&hyp_mp(&a1i(&leib_mem_u, v2.clone()), &v2_uy)?, &v2_ua)?;
    let leib_phi_u = Thm::eq_leibniz(tu.clone(), ty.clone(), x, phi.clone());
    let v2_phiy = hyp_mp(&hyp_mp(&a1i(&leib_phi_u, v2.clone()), &v2_uy)?, &v2_phiu)?;
    let w_right = uncurry(&hyp_and(&v2_ya, &v2_phiy)?)?;

    // ── Combine, then discharge the image existential ────────────────────────
    let w_good = hyp_or_elim(&w_disj, &w_left, &w_right)?;
    debug_assert_eq!(*w_good.concl(), Formula::imp(w, good.clone()));
    let c_h_good = uncurry(&w_good)?;
    let target = Formula::imp(h.clone(), good.clone());
    let ex = exists_elim_imp(x, &Thm::gen(x, &c_h_good), &target)?;
    let out = com12(&ex)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::imp(image(x, a, &choice_relation(x, phi, y, &tu)), good)),
        "image_forward produced an unexpected shape"
    );
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// Separation, in the case where the condition is satisfied somewhere.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a. (∃u. (u ∈ a ∧ φ(u))) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`.
///
/// Separation for the non-vacuous case, from Replacement alone — no Union, no
/// Power set, and above all no empty set. A witness `u` of the condition is
/// used as the default value of the choice relation, so the junk the relation
/// produces at the elements *failing* `φ` is a value that belongs in the answer
/// anyway.
///
/// This is the whole of Separation except for the case where nothing in `a`
/// satisfies `φ`; see the module documentation for why that case is not
/// reachable from the axioms this kernel has.
pub fn separation_nonvacuous(env: &mut Env, x: FreeVar, phi: &Formula) -> Option<Thm> {
    let (a, y, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (h, g) = separation_goal(env, x, phi, y, a, u)?;
    let h_g = separation_core(env, x, phi, y, a, u, &h, &g)?;

    // Discharge the witness: `∃u. H(u)` gives the goal, `u` being absent from it.
    let ex = exists_elim_imp(u, &Thm::gen(u, &h_g), &g)?;
    let out = Thm::gen(a, &ex);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(a, Formula::imp(Formula::exists(u, h), g)),
        "separation_nonvacuous produced an unexpected shape"
    );
    Some(out)
}

/// The hypothesis `u ∈ a ∧ φ(u)` and the goal
/// `∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`, built once so every step agrees on their
/// exact shape.
fn separation_goal(
    env: &mut Env,
    x: FreeVar,
    phi: &Formula,
    y: FreeVar,
    a: FreeVar,
    u: FreeVar,
) -> Option<(Formula, Formula)> {
    let (ta, tu) = (Term::var(a), Term::var(u));
    let h = Formula::and(Formula::mem(tu.clone(), ta), phi.subst(x, &tu));
    let s = env.fresh_var();
    let good = separated(x, phi, y, a);
    let body = Formula::forall(y, Formula::iff(Formula::mem(Term::var(y), Term::var(s)), good));
    Some((h, Formula::exists(s, body)))
}

/// `⊢ (u ∈ a ∧ φ(u)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`.
///
/// The heart of the derivation: instantiate Replacement at the choice relation,
/// discharge its `∃!` premise, and identify the resulting image with the
/// separated set by [`image_forward`] and [`image_backward`].
#[allow(clippy::too_many_arguments)]
fn separation_core(
    env: &mut Env,
    x: FreeVar,
    phi: &Formula,
    y: FreeVar,
    a: FreeVar,
    u: FreeVar,
    h: &Formula,
    g: &Formula,
) -> Option<Thm> {
    let (ty, ta, tu) = (Term::var(y), Term::var(a), Term::var(u));
    let psi = choice_relation(x, phi, y, &tu);
    let good = separated(x, phi, y, a);

    // ── Replacement at the choice relation ───────────────────────────────────
    let uniq = choice_relation_unique(env, x, phi, y, &tu)?;
    let repl = Thm::ax_replacement(env, x, y, psi.clone())?;
    let repl = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &a1i(&uniq, Formula::mem(Term::var(x), ta.clone())));
    let ex_image = Thm::mp(&repl, &premise)?;

    // ── Rewrite the image condition into the separation condition ────────────
    let b = env.fresh_var();
    let tb = Term::var(b);
    let img = image(x, a, &psi);
    let p_b = Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), tb.clone()), img.clone()));
    debug_assert_eq!(*ex_image.concl(), Formula::exists(b, p_b.clone()));

    let k = Formula::and(p_b.clone(), h.clone());
    let k_iff = syl(&and_left(p_b.clone(), h.clone()), &Thm::ax_inst(p_b.clone(), ty.clone())?)?;
    let k_h = and_right(p_b.clone(), h.clone());
    let k_img_good = syl(&k_h, &image_forward(env, x, phi, y, a, u)?)?;
    let k_good_img = a1i(&image_backward(x, phi, y, a, &tu)?, k.clone());

    let fwd = hyp_syl(&hyp_iff_mp(&k_iff)?, &k_img_good)?;
    let bwd = hyp_syl(&k_good_img, &hyp_iff_mpr(&k_iff)?)?;
    let k_iff_good = hyp_and(&fwd, &bwd)?;

    // `y` is bound in `P(b)` and absent from `H`, so it can be generalised.
    let iff_good = Formula::iff(Formula::mem(ty, tb.clone()), good);
    let k_q = Thm::mp(&Thm::ax_dist(y, k, iff_good.clone())?, &Thm::gen(y, &k_iff_good))?;
    let p_h_q = uncurry(&k_q)?;

    // ── Feed the rewritten set back into the goal's existential ──────────────
    let q_b = Formula::forall(y, iff_good);
    // The goal's binder variable is invisible — alpha-equivalent formulas are
    // syntactically equal — so a fresh one rebuilds exactly the same `G`.
    let s = env.fresh_var();
    let body =
        Formula::forall(y, Formula::iff(Formula::mem(Term::var(y), Term::var(s)), separated(x, phi, y, a)));
    debug_assert_eq!(*g, Formula::exists(s, body.clone()));
    debug_assert_eq!(q_b, body.subst(s, &tb));

    let q_to_g = exists_intro_imp(s, body, tb)?;
    let p_h_g = syl(&p_h_q, &imp_mono_r(&q_to_g, h.clone())?)?;
    let ex_to_hg = exists_elim_imp(b, &Thm::gen(b, &p_h_g), &Formula::imp(h.clone(), g.clone()))?;
    let out = Thm::mp(&ex_to_hg, &ex_image)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h.clone(), g.clone()));
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// Separation relative to an empty set.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a ∀e. (∀z. ¬(z ∈ e)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`.
///
/// The full content of the Separation scheme, with its one missing ingredient
/// carried as an explicit antecedent instead of assumed. Nothing is added to
/// the theory: this is a theorem of the axioms as they stand.
///
/// The two cases are glued with Clavius' law rather than an appeal to excluded
/// middle: `⊢ A → G` contraposes to `⊢ ¬G → ¬A`, which chains with
/// `⊢ ¬A → G` to `⊢ ¬G → G`.
pub fn separation_existence(env: &mut Env, x: FreeVar, phi: &Formula) -> Option<Thm> {
    let (a, y) = (env.fresh_var(), env.fresh_var());
    let thm = separation_existence_at(env, x, phi, a, y)?;
    Some(Thm::gen(a, &thm))
}

/// `⊢ ∀e. (∀z. ¬(z ∈ e)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`, for a caller-chosen
/// parameter `a` and element variable `y`.
///
/// Split out so [`separation`] can hand the very same `a` and `y` to
/// [`crate::define_by_membership`], which needs them to match to the symbol.
fn separation_existence_at(
    env: &mut Env,
    x: FreeVar,
    phi: &Formula,
    a: FreeVar,
    y: FreeVar,
) -> Option<Thm> {
    let u = env.fresh_var();
    let ty = Term::var(y);
    let (h, g) = separation_goal(env, x, phi, y, a, u)?;
    let good = separated(x, phi, y, a);

    // ── The condition holds somewhere: Replacement does the work ─────────────
    let h_g = separation_core(env, x, phi, y, a, u, &h, &g)?;
    let big_a = Formula::exists(u, h.clone());
    let a_g = exists_elim_imp(u, &Thm::gen(u, &h_g), &g)?;
    debug_assert_eq!(*a_g.concl(), Formula::imp(big_a.clone(), g.clone()));

    // ── The condition holds nowhere: the empty set is the answer ─────────────
    let (e, z) = (env.fresh_var(), env.fresh_var());
    let te = Term::var(e);
    let emp = Formula::forall(z, Formula::not(Formula::mem(Term::var(z), te.clone())));
    let na = Formula::not(big_a.clone());
    let kb = Formula::and(emp.clone(), na.clone());

    // `y ∈ e` is absurd, so it implies anything.
    let kb_not_mem = syl(&and_left(emp.clone(), na.clone()), &Thm::ax_inst(emp.clone(), ty.clone())?)?;
    let kb_fwd = hyp_ex_falso(&kb_not_mem, good.clone())?;
    // Conversely a separated element would witness `A`, which `¬A` refutes.
    let good_to_a = exists_intro_imp(u, h.clone(), ty.clone())?;
    debug_assert_eq!(*good_to_a.concl(), Formula::imp(good.clone(), big_a.clone()));
    let kb_good_false = hyp_syl(&a1i(&good_to_a, kb.clone()), &and_right(emp.clone(), na))?;
    let kb_bwd = hyp_ex_falso(&kb_good_false, Formula::mem(ty.clone(), te.clone()))?;

    let iff_e = Formula::iff(Formula::mem(ty.clone(), te.clone()), good.clone());
    let kb_all = Thm::mp(&Thm::ax_dist(y, kb, iff_e)?, &Thm::gen(y, &hyp_and(&kb_fwd, &kb_bwd)?))?;

    let s = env.fresh_var();
    let body = Formula::forall(y, Formula::iff(Formula::mem(ty, Term::var(s)), good));
    debug_assert_eq!(g, Formula::exists(s, body.clone()));
    let na_g = uncurry(&syl(&kb_all, &exists_intro_imp(s, body, te)?)?)?;

    // ── Glue the cases together ──────────────────────────────────────────────
    let emp_ng_na =
        hyp_mp(&a1i(&contrapos_imp(big_a, g.clone()), emp.clone()), &a1i(&a_g, emp.clone()))?;
    let emp_g = syl(&hyp_syl(&emp_ng_na, &na_g)?, &clavius(g.clone()))?;
    debug_assert_eq!(*emp_g.concl(), Formula::imp(emp, g));
    Some(Thm::gen(e, &emp_g))
}

/// Introduce the separated subset `sep_φ(a)` with
/// `⊢ ∀a ∀z. (z ∈ sep_φ(a) ↔ (z ∈ a ∧ φ(z)))`, given a proof
/// `⊢ ∀z. ¬(z ∈ e)` that some set `e` is empty.
///
/// Existence is [`separation_existence`] discharged at `e`; uniqueness is
/// Extensionality, via [`crate::define_by_membership`]. The empty set is read
/// off the supplied theorem and the theorem is checked to say exactly what it
/// must, so a caller cannot slip in something else.
///
/// **This is the only entry point that needs an ingredient the kernel does not
/// yet supply.** See the module documentation: no proof of `∀z. ¬(z ∈ e)` is
/// derivable from the current axioms, so this function is presently
/// uncallable — deliberately so, rather than papering over the gap with an
/// axiom.
pub fn separation(env: &mut Env, x: FreeVar, phi: &Formula, empty: &Thm) -> Option<(FnSym, Thm)> {
    // Read the empty set's term off the theorem, by instantiating at a probe
    // variable and insisting the result is exactly `¬(w ∈ e)`.
    let w = env.fresh_var();
    let (mem, f) = inst_all(empty, &[Term::var(w)])?.concl().as_imp()?;
    if f != Formula::false_() {
        return None
    }
    let (probe, e) = mem.as_mem()?;
    if probe != Term::var(w) || e.occurs_free(w) {
        return None
    }

    let (a, y) = (env.fresh_var(), env.fresh_var());
    let rel = separation_existence_at(env, x, phi, a, y)?;
    let inst = inst_all(&rel, std::slice::from_ref(&e))?;
    let (expected, _) = inst.concl().as_imp()?;
    if expected != *empty.concl() {
        return None
    }
    let existence = Thm::mp(&inst, empty)?;
    define_by_membership(env, &[a], &existence, y, &separated(x, phi, y, a))
}

/// `⊢ ∀a. (∀a′ ∀z. (z ∈ sep(a′) ↔ (z ∈ a′ ∧ ¬(z = z)))) → ∀z. ¬(z ∈ sep(a))`.
///
/// Separation at a refutable condition *is* the empty set. This records, inside
/// the system, why the gap left by [`separation`] cannot be closed by appealing
/// to Separation itself: the empty set and the Separation scheme stand or fall
/// together, so an empty set has to come from elsewhere.
pub fn empty_from_separation(env: &mut Env, sep: FnSym) -> Option<Thm> {
    if sep.arity() != 1 {
        return None
    }
    let (a, z) = (env.fresh_var(), env.fresh_var());
    let (ta, tz) = (Term::var(a), Term::var(z));
    let sa = Term::apply(sep, vec![ta.clone()]);

    let refl = Formula::eq(tz.clone(), tz.clone());
    let good = Formula::and(Formula::mem(tz.clone(), ta), Formula::not(refl.clone()));
    let inner = Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), sa.clone()), good.clone()));
    let ax = Formula::forall(a, inner.clone());

    // Peel both quantifiers off the hypothesis.
    let ax_inner = Thm::ax_inst(ax.clone(), Term::var(a))?;
    let ax_iff = syl(&ax_inner, &Thm::ax_inst(inner, tz.clone())?)?;

    let ax_good = hyp_iff_mp(&ax_iff)?;
    let ax_ne = hyp_syl(
        &ax_good,
        &a1i(&and_right(Formula::mem(tz.clone(), Term::var(a)), Formula::not(refl.clone())), ax.clone()),
    )?;
    // `¬(z = z)` is refuted by reflexivity.
    let ax_absurd = hyp_syl(&ax_ne, &a1i(&mp_const(&Thm::eq_refl(tz.clone()), Formula::false_()), ax.clone()))?;

    let not_mem = Formula::not(Formula::mem(tz, sa));
    let all_z = Thm::mp(&Thm::ax_dist(z, ax.clone(), not_mem.clone())?, &Thm::gen(z, &ax_absurd))?;
    debug_assert_eq!(*all_z.concl(), Formula::imp(ax, Formula::forall(z, not_mem)));
    Some(Thm::gen(a, &all_z))
}
