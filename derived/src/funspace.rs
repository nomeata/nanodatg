//! Cartesian products, function spaces, and the fact the tutorial needs:
//! `(a → a) ∈ U(a)`.
//!
//! # Why the product is built from Replacement, not Separation
//!
//! The textbook construction cuts `a × b` out of `𝒫𝒫(a ∪ b)` by Separation.
//! That is not available here: the only Separation this development has is
//! [`crate::separation::separation_nonvacuous`] (equivalently
//! [`crate::funcs::separation_nonempty`]), which requires the *result* to be
//! inhabited, because the empty set is not derivable from these axioms (see the
//! module docs of [`crate::separation`]). And `a × b` really can be empty — in
//! any model with an empty set, `∅ × b = ∅` — so no inhabitation witness exists
//! to supply.
//!
//! So the product is assembled from Replacement instead, where every step is
//! *total* and no inhabitation is needed:
//!
//! ```text
//! row(x, b) := { ⟨x,y⟩ : y ∈ b }        — Replacement along y ↦ ⟨x,y⟩
//! fam(a, b) := { row(x,b) : x ∈ a }     — Replacement along x ↦ row(x,b)
//! prod(a, b) := ⋃ fam(a, b)
//! ```
//!
//! Both Replacement instances have the trivial `∃!` premise `∃!v. v = t`, which
//! [`crate::exists_unique_eq`] discharges for free, and the final union is an
//! explicit definition. The characteristic property
//! `z ∈ prod(a,b) ↔ ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩))` therefore holds
//! **unconditionally** — no inhabitation antecedent anywhere.
//!
//! # Where an antecedent does survive: the function space
//!
//! The function space *is* carved out of a power set by a condition, and there
//! the empty set bites: `a → b` is empty when `a` is inhabited and `b` is not,
//! so Separation is genuinely unavailable. The symbol `fs(a,b)` is therefore
//! defined by the same total-by-default trick [`crate::funcs::collection`] uses
//! — the defining condition carries an extra disjunct that fires only when
//! there are no functions at all, and then degenerates to `𝒫(prod(a,b))`. Two
//! consequences:
//!
//! * [`funspace_members`] — that `fs(a,b)` has exactly the functions as members
//!   — is conditional on there being one.
//! * [`funspace_subset_pow_prod`] — that `fs(a,b) ⊆ 𝒫(prod(a,b))` — is
//!   **unconditional**, because the default is itself a subset of
//!   `𝒫(prod(a,b))`. That is the half the universe argument needs, so the
//!   payoff [`funspace_in_universe`] carries no side condition.
//!
//! # The chain to `(a → a) ∈ U(a)`
//!
//! | step | lemma |
//! |---|---|
//! | `a ∈ U(a)` | [`crate::universe::mem_least_universe`] |
//! | `y ∈ U(x) → 𝒫y ∈ U(x)` | [`pow_closed`] |
//! | `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` | [`product_subset_pow_pow`] |
//! | `a ∪ a = a` | [`crate::union_singleton`] |
//! | `fs(a,b) ⊆ 𝒫(prod(a,b))` | [`funspace_subset_pow_prod`] |
//! | `fs(a,a) ∈ U(a)` | [`funspace_in_universe`] |
//!
//! Only the single-argument case lands: `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` needs
//! `a ∪ b ∈ U(a)` to continue, and binary union is not among the closure
//! properties proved for `U(x)`. At `b = a` the union collapses — `a ∪ a` is
//! `⋃{a}`, which is `a` — and the chain goes through.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{cases, hyp_mp2, hyp_syl, or_intro_left, or_intro_right, union_intro, Sets};
use crate::{
    a1i, and_intro, and_left, and_right, com12, contrapos, define_by_membership, eq_symm,
    eq_symm_imp, exists_elim_imp, exists_intro_imp, exists_mono, exists_unique_eq, gen_all,
    hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all,
    singleton, syl, uncurry, upair_members,
};

// ─────────────────────────────────────────────────────────────────────────────
// Small combinators.
//
// Private copies rather than imports: the neighbouring modules keep these
// private too, and a derivation this long should not break when one of them is
// reshaped. Reading formulas apart is untrusted and safe — no `Thm` is produced
// by any of it.
// ─────────────────────────────────────────────────────────────────────────────

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    Thm::mp(&Thm::mp(&s, t)?, &imp_refl(h))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// Decompose `φ ↔ ψ` into its two implication halves.
fn split_iff(iff: &Formula) -> Option<(Formula, Formula)> {
    let (inner, _) = iff.as_imp()?;
    let (fwd, nb) = inner.as_imp()?;
    let (bwd, _) = nb.as_imp()?;
    Some((fwd, bwd))
}

/// From `⊢ K → ψ`, `⊢ K → (l ∨ r)` and `⊢ K → (r → ¬ψ)` infer `⊢ K → l`.
///
/// The right disjunct is refuted by `ψ`, so the disjunction collapses onto its
/// left half. (A copy of the helper in [`crate::funcs`], which keeps it
/// private.)
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
///
/// Swapping a membership condition for a provably equivalent one inside an
/// existential. (Again a copy of [`crate::funcs`]'s private helper.)
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
    let j_fwd = hyp_syl(&hyp_iff_mp(&j_iff1)?, &hyp_iff_mp(&j_iff2)?)?;
    let j_bwd = hyp_syl(&hyp_iff_mpr(&j_iff2)?, &hyp_iff_mpr(&j_iff1)?)?;
    let j_iff = hyp_and(&j_fwd, &j_bwd)?;
    let j_q = Thm::mp(&Thm::ax_dist(z, j, Formula::iff(mem_zs, chi))?, &Thm::gen(z, &j_iff))?;

    let ex_chi = Formula::exists(sv, p_chi.clone());
    let h_p_ex = hyp_syl(&uncurry(&j_q)?, &a1i(&exists_intro_imp(sv, p_chi, ts)?, h.clone()))?;
    let elim =
        exists_elim_imp(sv, &Thm::gen(sv, &com12(&h_p_ex)?), &Formula::imp(h.clone(), ex_chi))?;
    hyp_mp(&syl(h_ex, &elim)?, &imp_refl(h))
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// Instantiate the body of `∃v. φ` at `t`, as a *formula* operation. `∃` is
/// `¬∀¬`.
fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (_, body) = Thm::ax_inst(all_not, t.clone())?.concl().as_imp()?;
    let (body, fls2) = body.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// `⊢ u = v → (t ∈ u → t ∈ v)` — carry a membership across an equation.
fn carry_mem(env: &mut Env, t: Term, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::mem(t, Term::var(w)))
}

/// `⊢ u = v → (u ∈ t → v ∈ t)` — carry an element across an equation.
fn carry_elem(env: &mut Env, u: Term, v: Term, t: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::mem(Term::var(w), t))
}

// ─────────────────────────────────────────────────────────────────────────────
// The membership conditions, built in one place.
//
// Every lemma below has to rebuild these formulas to state itself, and they
// have to agree on the nose — alpha-equivalent formulas are syntactically
// equal, so a fresh bound variable each time is harmless, but a different
// *shape* is not.
// ─────────────────────────────────────────────────────────────────────────────

/// `∃y. (y ∈ b ∧ z = ⟨x,y⟩)` — the membership condition of `row(x,b)`.
fn row_cond(env: &mut Env, sets: &Sets, x: &Term, b: &Term, z: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    Formula::exists(
        y,
        Formula::and(
            Formula::mem(ty.clone(), b.clone()),
            Formula::eq(z.clone(), sets.pair(x.clone(), ty)),
        ),
    )
}

/// `∃x. (x ∈ a ∧ w = row(x,b))` — the membership condition of `fam(a,b)`.
fn fam_cond(env: &mut Env, row: FnSym, a: &Term, b: &Term, w: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::exists(
        x,
        Formula::and(
            Formula::mem(tx.clone(), a.clone()),
            Formula::eq(w.clone(), Term::apply(row, vec![tx, b.clone()])),
        ),
    )
}

/// `∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩))` — the membership condition of
/// `prod(a,b)`.
pub fn product_cond(env: &mut Env, sets: &Sets, a: &Term, b: &Term, z: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let inner = row_cond(env, sets, &tx, b, z);
    Formula::exists(x, Formula::and(Formula::mem(tx, a.clone()), inner))
}

// ─────────────────────────────────────────────────────────────────────────────
// The Cartesian product.
// ─────────────────────────────────────────────────────────────────────────────

/// The product `prod(a,b) = a × b`, with the two auxiliary symbols it is built
/// from.
pub struct Product {
    /// `row(x,b) = { ⟨x,y⟩ : y ∈ b }`.
    pub row: FnSym,
    /// `⊢ ∀x ∀b ∀v. (v ∈ row(x,b) ↔ ∃y. (y ∈ b ∧ v = ⟨x,y⟩))`.
    pub row_ax: Thm,
    /// `fam(a,b) = { row(x,b) : x ∈ a }`.
    pub fam: FnSym,
    /// `⊢ ∀a ∀b ∀w. (w ∈ fam(a,b) ↔ ∃x. (x ∈ a ∧ w = row(x,b)))`.
    pub fam_ax: Thm,
    /// `prod(a,b) = ⋃ fam(a,b)`.
    pub prod: FnSym,
    /// `⊢ ∀a ∀b. prod(a,b) = ⋃ fam(a,b)`.
    pub prod_def: Thm,
    /// `⊢ ∀a ∀b ∀z. (z ∈ prod(a,b) ↔ ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩)))`.
    pub prod_ax: Thm,
}

impl Product {
    /// The term `prod(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.prod, vec![a, b]) }
}

/// Introduce `prod(a,b) = a × b` and prove its characteristic property.
///
/// Unconditional: see the module docs for why Separation is not the route.
pub fn product(env: &mut Env, sets: &Sets) -> Option<Product> {
    let (row, row_ax) = row_symbol(env, sets)?;
    let (fam, fam_ax) = fam_symbol(env, row)?;

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let fam_term = sets.union_of(Term::apply(fam, vec![Term::var(a), Term::var(b)]));
    let (prod, prod_def) = crate::define_abbrev(env, &[a, b], &fam_term)?;

    let prod_ax = product_members(env, sets, row, &row_ax, fam, &fam_ax, prod, &prod_def)?;
    Some(Product { row, row_ax, fam, fam_ax, prod, prod_def, prod_ax })
}

/// `row(x,b) = { ⟨x,y⟩ : y ∈ b }`, by Replacement along `y ↦ ⟨x,y⟩`.
///
/// The `∃!` premise is `∃!v. v = ⟨x,y⟩`, which [`crate::exists_unique_eq`]
/// supplies for nothing — a term denotes a unique object.
fn row_symbol(env: &mut Env, sets: &Sets) -> Option<(FnSym, Thm)> {
    let (x, b, u) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tb, tu) = (Term::var(x), Term::var(b), Term::var(u));

    let pair = sets.pair(tx, tu.clone());
    let (v, phi, exu) = exists_unique_eq(env, &[], &pair);

    let repl = Thm::ax_replacement(env, u, v, phi.clone())?;
    let repl_b = inst_all(&repl, std::slice::from_ref(&tb))?;
    let premise = Thm::gen(u, &a1i(&exu, Formula::mem(tu.clone(), tb.clone())));
    let img = Thm::mp(&repl_b, &premise)?;

    let cond = Formula::exists(u, Formula::and(Formula::mem(tu, tb), phi));
    define_by_membership(env, &[x, b], &img, v, &cond)
}

/// `fam(a,b) = { row(x,b) : x ∈ a }`, by Replacement along `x ↦ row(x,b)`.
fn fam_symbol(env: &mut Env, row: FnSym) -> Option<(FnSym, Thm)> {
    let (a, b, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx) = (Term::var(a), Term::var(b), Term::var(x));

    let row_term = Term::apply(row, vec![tx.clone(), tb]);
    let (w, phi, exu) = exists_unique_eq(env, &[], &row_term);

    let repl = Thm::ax_replacement(env, x, w, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    define_by_membership(env, &[a, b], &img, w, &cond)
}

/// `⊢ ∀a ∀b ∀z. (z ∈ prod(a,b) ↔ ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩)))`.
///
/// Unfolding `⋃fam(a,b)`: a member of the union lies in some `row(x,b)` with
/// `x ∈ a`, and that is exactly a pair `⟨x,y⟩` with `y ∈ b`. Both directions
/// are a witness-shuffle; the only content is that the two existentials
/// compose.
#[allow(clippy::too_many_arguments)]
fn product_members(
    env: &mut Env,
    sets: &Sets,
    row: FnSym,
    row_ax: &Thm,
    fam: FnSym,
    fam_ax: &Thm,
    prod: FnSym,
    prod_def: &Thm,
) -> Option<Thm> {
    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));

    let fam_t = Term::apply(fam, vec![ta.clone(), tb.clone()]);
    let ufam = sets.union_of(fam_t.clone());
    let prod_t = Term::apply(prod, vec![ta.clone(), tb.clone()]);

    let goal = product_cond(env, sets, &ta, &tb, &tz);
    let mem_prod = Formula::mem(tz.clone(), prod_t.clone());

    // `z ∈ prod(a,b) ↔ z ∈ ⋃fam(a,b)`, from the defining equation.
    let pdef = inst_all(prod_def, &[ta.clone(), tb.clone()])?;
    let p2u = Thm::mp(&carry_mem(env, tz.clone(), prod_t.clone(), ufam.clone()), &pdef)?;
    let u2p = Thm::mp(
        &carry_mem(env, tz.clone(), ufam.clone(), prod_t.clone()),
        &eq_symm(env, &pdef)?,
    )?;

    // ── Forward ──────────────────────────────────────────────────────────────
    let (w, x) = (env.fresh_var(), env.fresh_var());
    let (tw, tx) = (Term::var(w), Term::var(x));
    let row_t = Term::apply(row, vec![tx.clone(), tb.clone()]);

    let mem_wf = Formula::mem(tw.clone(), fam_t.clone());
    let mem_zw = Formula::mem(tz.clone(), tw.clone());
    // `W := w ∈ fam(a,b) ∧ z ∈ w`.
    let big_w = Formula::and(mem_wf.clone(), mem_zw.clone());
    let w_fam = and_left(mem_wf.clone(), mem_zw.clone());
    let w_zw = and_right(mem_wf.clone(), mem_zw.clone());

    let fam_at_w = inst_all(fam_ax, &[ta.clone(), tb.clone(), tw.clone()])?;
    let w_ex = syl(&w_fam, &iff_mp(&fam_at_w)?)?;

    // `E := x ∈ a ∧ w = row(x,b)`, under `V := W ∧ E`.
    let e = Formula::and(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), row_t.clone()));
    debug_assert_eq!(
        *w_ex.concl(),
        Formula::imp(big_w.clone(), fam_cond(env, row, &ta, &tb, &tw)),
        "fam_ax has an unexpected membership condition"
    );
    let v = Formula::and(big_w.clone(), e.clone());
    let v_w = and_left(big_w.clone(), e.clone());
    let v_e = and_right(big_w.clone(), e.clone());
    let v_xa = syl(
        &v_e,
        &and_left(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), row_t.clone())),
    )?;
    let v_eq = syl(
        &v_e,
        &and_right(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), row_t.clone())),
    )?;
    let v_zw = syl(&v_w, &w_zw)?;

    // `w = row(x,b)` carries `z ∈ w` into `z ∈ row(x,b)`.
    let carry = carry_mem(env, tz.clone(), tw.clone(), row_t.clone());
    let v_z_row = hyp_mp(&hyp_mp(&a1i(&carry, v.clone()), &v_eq)?, &v_zw)?;

    let row_at_z = inst_all(row_ax, &[tx.clone(), tb.clone(), tz.clone()])?;
    let inner = row_cond(env, sets, &tx, &tb, &tz);
    debug_assert_eq!(
        *row_at_z.concl(),
        Formula::iff(Formula::mem(tz.clone(), row_t.clone()), inner.clone()),
        "row_ax has an unexpected membership condition"
    );
    let v_inner = syl(&v_z_row, &iff_mp(&row_at_z)?)?;

    let body = Formula::and(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    debug_assert_eq!(goal, Formula::exists(x, body.clone()), "product_cond has an unexpected shape");
    let v_goal = syl(&hyp_and(&v_xa, &v_inner)?, &exists_intro_imp(x, body, tx.clone())?)?;

    let w_goal = discharge(x, &w_ex, &v_goal)?;
    let ex_to_goal = exists_elim_imp(w, &Thm::gen(w, &w_goal), &goal)?;

    let un_inst = inst_all(&sets.un_ax, &[fam_t.clone(), tz.clone()])?;
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(tz.clone(), ufam.clone()), Formula::exists(w, big_w.clone())),
        "the Union axiom has an unexpected shape"
    );
    let fwd = syl(&syl(&p2u, &iff_mp(&un_inst)?)?, &ex_to_goal)?;

    // ── Backward ─────────────────────────────────────────────────────────────
    let e2 = Formula::and(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let e2_xa = and_left(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let e2_inner = and_right(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let e2_z_row = syl(&e2_inner, &iff_mpr(&row_at_z)?)?;

    // `row(x,b) ∈ fam(a,b)`, witnessed by `x` itself. The witness variable must
    // be a *fresh* one: binding `x` here would abstract the `x` in the fixed
    // left-hand side `row(x,b)` as well, which is a different formula.
    let fam_at_row = inst_all(fam_ax, &[ta.clone(), tb.clone(), row_t.clone()])?;
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let fam_body = Formula::and(
        Formula::mem(tx2.clone(), ta.clone()),
        Formula::eq(row_t.clone(), Term::apply(row, vec![tx2, tb.clone()])),
    );
    let e2_fam_ex = syl(
        &hyp_and(&e2_xa, &a1i(&Thm::eq_refl(row_t.clone()), e2.clone()))?,
        &exists_intro_imp(x2, fam_body, tx.clone())?,
    )?;
    let e2_row_fam = syl(&e2_fam_ex, &iff_mpr(&fam_at_row)?)?;

    let intro = union_intro(env, sets, fam_t.clone(), row_t.clone(), tz.clone())?;
    let e2_ufam = syl(&hyp_and(&e2_row_fam, &e2_z_row)?, &intro)?;
    let e2_prod = syl(&e2_ufam, &u2p)?;

    let bwd = exists_elim_imp(x, &Thm::gen(x, &e2_prod), &mem_prod)?;
    debug_assert_eq!(*bwd.concl(), Formula::imp(goal.clone(), mem_prod.clone()));

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(*out.concl(), Formula::iff(mem_prod, goal), "product_members: unexpected shape");
    Some(gen_all(&[a, b, z], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Binary union, and the Kuratowski pair as a member of a double power set.
// ─────────────────────────────────────────────────────────────────────────────

/// The binary union `a ∪ b`, as `⋃{a,b}`.
///
/// A composition of existing symbols, so no definitional extension and no proof
/// obligation — the same economy [`crate::singleton`] and [`crate::opair`] get.
pub fn bin_union(sets: &Sets, a: Term, b: Term) -> Term {
    sets.union_of(Term::apply(sets.up, vec![a, b]))
}

/// `⊢ ∀u ∀v ∀c. ((u ∈ c ∧ v ∈ c) → {u,v} ⊆ c)`.
///
/// A member of `{u,v}` is `u` or `v`, and both are in `c`. Serves for
/// singletons too, since `{u}` is `{u,u}`.
pub fn upair_subset(env: &mut Env, sets: &Sets) -> Option<Thm> {
    let (u, v, c, s) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, tc, ts) = (Term::var(u), Term::var(v), Term::var(c), Term::var(s));
    let uv = Term::apply(sets.up, vec![tu.clone(), tv.clone()]);

    let mem_uc = Formula::mem(tu.clone(), tc.clone());
    let mem_vc = Formula::mem(tv.clone(), tc.clone());
    let mem_sc = Formula::mem(ts.clone(), tc.clone());
    let mem_s = Formula::mem(ts.clone(), uv.clone());

    // `H := u ∈ c ∧ v ∈ c`, and `K := H ∧ s ∈ {u,v}`.
    let h = Formula::and(mem_uc.clone(), mem_vc.clone());
    let k_h = and_left(h.clone(), mem_s.clone());
    let k_s = and_right(h.clone(), mem_s.clone());
    let k_disj = syl(&k_s, &iff_mp(&inst_all(&sets.up_ax, &[tu.clone(), tv.clone(), ts.clone()])?)?)?;

    // `⊢ u ∈ c → (s = u → s ∈ c)`: symmetry then Leibniz, antecedents swapped.
    let leib_u = carry_elem(env, tu.clone(), ts.clone(), tc.clone());
    let side_u = com12(&syl(&eq_symm_imp(env, ts.clone(), tu.clone()), &leib_u)?)?;
    let k_left = syl(&syl(&k_h, &and_left(mem_uc.clone(), mem_vc.clone()))?, &side_u)?;

    let leib_v = carry_elem(env, tv.clone(), ts.clone(), tc.clone());
    let side_v = com12(&syl(&eq_symm_imp(env, ts.clone(), tv.clone()), &leib_v)?)?;
    let k_right = syl(&syl(&k_h, &and_right(mem_uc, mem_vc))?, &side_v)?;

    let h_imp = uncurry(&hyp_or_elim(&k_disj, &k_left, &k_right)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(s, h.clone(), Formula::imp(mem_s, mem_sc))?,
        &Thm::gen(s, &h_imp),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, uv, tc)),
        "upair_subset: unexpected shape"
    );
    Some(gen_all(&[u, v, c], &out))
}

/// `⊢ ∀a ∀b ∀x. (x ∈ a → x ∈ a ∪ b)` and `⊢ ∀a ∀b ∀y. (y ∈ b → y ∈ a ∪ b)`.
pub fn mem_bin_union(env: &mut Env, sets: &Sets) -> Option<(Thm, Thm)> {
    let (a, b, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx) = (Term::var(a), Term::var(b), Term::var(x));
    let ab = Term::apply(sets.up, vec![ta.clone(), tb.clone()]);
    let (a_in, b_in) = upair_members(&sets.up_ax, &ta, &tb)?;

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let intro_a = union_intro(env, sets, ab.clone(), ta.clone(), tx.clone())?;
    let left = syl(&hyp_and(&a1i(&a_in, mem_xa.clone()), &imp_refl(mem_xa))?, &intro_a)?;

    let mem_xb = Formula::mem(tx.clone(), tb.clone());
    let intro_b = union_intro(env, sets, ab, tb.clone(), tx.clone())?;
    let right = syl(&hyp_and(&a1i(&b_in, mem_xb.clone()), &imp_refl(mem_xb))?, &intro_b)?;

    let un = bin_union(sets, ta.clone(), tb.clone());
    debug_assert_eq!(
        *left.concl(),
        Formula::imp(Formula::mem(tx.clone(), ta), Formula::mem(tx.clone(), un.clone()))
    );
    debug_assert_eq!(
        *right.concl(),
        Formula::imp(Formula::mem(tx.clone(), tb), Formula::mem(tx, un))
    );
    Some((gen_all(&[a, b, x], &left), gen_all(&[a, b, x], &right)))
}

/// `⊢ ∀x ∀y ∀c. ((x ∈ c ∧ y ∈ c) → ⟨x,y⟩ ∈ 𝒫𝒫c)`.
///
/// The Kuratowski pair `⟨x,y⟩` is `{{x},{x,y}}`: both members are subsets of
/// `c`, hence members of `𝒫c`, hence the pair is a subset of `𝒫c` and so a
/// member of `𝒫𝒫c`. Three applications of [`upair_subset`], each cashed in
/// through the Power Set characterisation.
pub fn pair_in_pow_pow(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    up_sub: &Thm,
) -> Option<Thm> {
    let (x, y, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tc) = (Term::var(x), Term::var(y), Term::var(c));

    let sx = singleton(sets.up, tx.clone());
    let xy = Term::apply(sets.up, vec![tx.clone(), ty.clone()]);
    let pair = crate::opair(sets.up, tx.clone(), ty.clone());
    let pc = Term::apply(pow, vec![tc.clone()]);
    let ppc = Term::apply(pow, vec![pc.clone()]);

    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    let mem_yc = Formula::mem(ty.clone(), tc.clone());
    let h = Formula::and(mem_xc.clone(), mem_yc.clone());
    let h_x = and_left(mem_xc.clone(), mem_yc.clone());
    let h_y = and_right(mem_xc, mem_yc);

    // `H → {x} ∈ 𝒫c`
    let us_xx = inst_all(up_sub, &[tx.clone(), tx.clone(), tc.clone()])?;
    let h_sx_sub = hyp_mp(&a1i(&us_xx, h.clone()), &hyp_and(&h_x, &h_x)?)?;
    let h_sx_in = syl(&h_sx_sub, &iff_mpr(&inst_all(pow_ax, &[tc.clone(), sx.clone()])?)?)?;

    // `H → {x,y} ∈ 𝒫c`
    let us_xy = inst_all(up_sub, &[tx.clone(), ty.clone(), tc.clone()])?;
    let h_xy_sub = hyp_mp(&a1i(&us_xy, h.clone()), &hyp_and(&h_x, &h_y)?)?;
    let h_xy_in = syl(&h_xy_sub, &iff_mpr(&inst_all(pow_ax, &[tc, xy.clone()])?)?)?;

    // `H → ⟨x,y⟩ ⊆ 𝒫c`, and hence `H → ⟨x,y⟩ ∈ 𝒫𝒫c`.
    let us_pair = inst_all(up_sub, &[sx, xy, pc.clone()])?;
    let h_pair_sub = hyp_mp(&a1i(&us_pair, h.clone()), &hyp_and(&h_sx_in, &h_xy_in)?)?;
    let out = syl(&h_pair_sub, &iff_mpr(&inst_all(pow_ax, &[pc, pair.clone()])?)?)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(pair, ppc)),
        "pair_in_pow_pow: unexpected shape"
    );
    Some(gen_all(&[x, y, c], &out))
}

/// `⊢ ∀a ∀b. prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` — step 3 of the chain.
///
/// A member of the product is a pair `⟨x,y⟩` with `x ∈ a` and `y ∈ b`; both
/// components are then in `a ∪ b`, and [`pair_in_pow_pow`] does the rest.
pub fn product_subset_pow_pow(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    p: &Product,
    pair_pp: &Thm,
    mem_left: &Thm,
    mem_right: &Thm,
) -> Option<Thm> {
    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));

    let un = bin_union(sets, ta.clone(), tb.clone());
    let ppu = Term::apply(pow, vec![Term::apply(pow, vec![un.clone()])]);
    let prod_t = p.of(ta.clone(), tb.clone());
    let goal = Formula::mem(tz.clone(), ppu.clone());

    let pair_xy = sets.pair(tx.clone(), ty.clone());
    let y_body = Formula::and(
        Formula::mem(ty.clone(), tb.clone()),
        Formula::eq(tz.clone(), pair_xy.clone()),
    );
    let inner = Formula::exists(y, y_body.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let e = Formula::and(mem_xa.clone(), inner.clone());

    let prod_at_z = inst_all(&p.prod_ax, &[ta.clone(), tb.clone(), tz.clone()])?;
    debug_assert_eq!(
        *prod_at_z.concl(),
        Formula::iff(Formula::mem(tz.clone(), prod_t.clone()), Formula::exists(x, e.clone())),
        "the product's membership condition has an unexpected shape"
    );

    // `F := E ∧ (y ∈ b ∧ z = ⟨x,y⟩)`.
    let f = Formula::and(e.clone(), y_body.clone());
    let f_e = and_left(e.clone(), y_body.clone());
    let f_y = and_right(e.clone(), y_body.clone());
    let f_xa = syl(&f_e, &and_left(mem_xa.clone(), inner.clone()))?;
    let f_yb = syl(
        &f_y,
        &and_left(Formula::mem(ty.clone(), tb.clone()), Formula::eq(tz.clone(), pair_xy.clone())),
    )?;
    let f_eq = syl(
        &f_y,
        &and_right(Formula::mem(ty.clone(), tb.clone()), Formula::eq(tz.clone(), pair_xy.clone())),
    )?;

    let f_x_un = syl(&f_xa, &inst_all(mem_left, &[ta.clone(), tb.clone(), tx.clone()])?)?;
    let f_y_un = syl(&f_yb, &inst_all(mem_right, &[ta.clone(), tb.clone(), ty.clone()])?)?;
    let pp = inst_all(pair_pp, &[tx, ty, un])?;
    let f_pair_in = hyp_mp(&a1i(&pp, f.clone()), &hyp_and(&f_x_un, &f_y_un)?)?;

    // Transport along `z = ⟨x,y⟩`.
    let leib = carry_elem(env, pair_xy.clone(), tz.clone(), ppu.clone());
    let f_symm = syl(&f_eq, &eq_symm_imp(env, tz.clone(), pair_xy))?;
    let f_goal = hyp_mp(&hyp_mp(&a1i(&leib, f), &f_symm)?, &f_pair_in)?;

    let e_goal = discharge(y, &and_right(mem_xa, inner), &f_goal)?;
    let z_goal = syl(&iff_mp(&prod_at_z)?, &exists_elim_imp(x, &Thm::gen(x, &e_goal), &goal)?)?;

    let out = Thm::gen(z, &z_goal);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, prod_t, ppu),
        "product_subset_pow_pow: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// The function space.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀x. (x ∈ a → ∃y. (y ∈ b ∧ ⟨x,y⟩ ∈ f))` — `f` is total on `a`, with values
/// in `b`.
pub fn is_total(env: &mut Env, sets: &Sets, a: &Term, b: &Term, f: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let body = Formula::and(
        Formula::mem(ty.clone(), b.clone()),
        Formula::mem(sets.pair(tx.clone(), ty), f.clone()),
    );
    Formula::forall(x, Formula::imp(Formula::mem(tx, a.clone()), Formula::exists(y, body)))
}

/// `∀x ∀y ∀y′. ((⟨x,y⟩ ∈ f ∧ ⟨x,y′⟩ ∈ f) → y = y′)` — `f` is single-valued.
pub fn is_single_valued(env: &mut Env, sets: &Sets, f: &Term) -> Formula {
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));
    let hyp = Formula::and(
        Formula::mem(sets.pair(tx.clone(), ty.clone()), f.clone()),
        Formula::mem(sets.pair(tx, ty2.clone()), f.clone()),
    );
    Formula::forall(
        x,
        Formula::forall(y, Formula::forall(y2, Formula::imp(hyp, Formula::eq(ty, ty2)))),
    )
}

/// `f ⊆ prod(a,b) ∧ (f total on a ∧ f single-valued)` — "`f` is a function from
/// `a` to `b`", as a formula.
pub fn is_function(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    a: &Term,
    b: &Term,
    f: &Term,
) -> Formula {
    let sub = kernel::thm::subset(env, f.clone(), p.of(a.clone(), b.clone()));
    Formula::and(sub, graph_condition(env, sets, a, b, f))
}

/// `f total on a ∧ f single-valued` — the half of [`is_function`] that
/// Separation carves with.
fn graph_condition(env: &mut Env, sets: &Sets, a: &Term, b: &Term, f: &Term) -> Formula {
    Formula::and(is_total(env, sets, a, b, f), is_single_valued(env, sets, f))
}

/// The function space `fs(a,b) = a → b`.
pub struct Funspace {
    /// The symbol itself.
    pub fs: FnSym,
    /// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ (isfun(f) ∨ (¬∃g. isfun(g) ∧ f ∈ 𝒫prod(a,b))))`
    /// — the raw defining axiom, default disjunct and all.
    pub fs_def: Thm,
    /// `⊢ ∀a ∀b. ((∃g. isfun(g)) → ∀f. (f ∈ fs(a,b) ↔ isfun(f)))`.
    pub fs_ax: Thm,
    /// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))` — unconditional.
    pub fs_sub: Thm,
}

impl Funspace {
    /// The term `fs(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.fs, vec![a, b]) }
}

/// The membership condition actually defined, and its two ingredients:
/// `(L, NE, φ)` where `L(f)` is [`is_function`], `NE` is `∃f. L(f)`, and
/// `φ(f) := L(f) ∨ (¬NE ∧ f ∈ 𝒫prod(a,b))`.
fn funspace_cond(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    p: &Product,
    a: &Term,
    b: &Term,
    f: FreeVar,
) -> (Formula, Formula, Formula) {
    let tf = Term::var(f);
    let pp = Term::apply(pow, vec![p.of(a.clone(), b.clone())]);
    let l = is_function(env, sets, p, a, b, &tf);
    let ne = Formula::exists(f, l.clone());
    let rgt = Formula::and(Formula::not(ne.clone()), Formula::mem(tf, pp));
    let phi = Formula::or(l.clone(), rgt);
    (l, ne, phi)
}

/// Introduce `fs(a,b) = a → b`.
///
/// **Why the definition carries a default.** The function space is carved out
/// of `𝒫(prod(a,b))` by a condition, and the only Separation available needs
/// the result to be inhabited — but `a → b` really is empty when `a` is
/// inhabited and `b` is not, so no witness can be produced. The way out is the
/// one [`crate::funcs::collection`] takes: define the *disjunctive* condition
///
/// ```text
/// f ∈ fs(a,b)  ↔  isfun(f)  ∨  (¬∃g. isfun(g)  ∧  f ∈ 𝒫prod(a,b))
/// ```
///
/// so the symbol is total. When there is a function the second disjunct is
/// dead and the intended condition is recovered ([`funspace_members`]); when
/// there is none the set degenerates to `𝒫(prod(a,b))`, which is harmless
/// because everything downstream only uses [`funspace_subset_pow_prod`], and
/// that holds either way.
pub fn funspace(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    p: &Product,
) -> Option<(FnSym, Thm)> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let prod_t = p.of(ta.clone(), tb.clone());
    let pp = Term::apply(pow, vec![prod_t.clone()]);
    let (l, ne, phi) = funspace_cond(env, sets, pow, p, &ta, &tb, f);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()), "funspace: condition shape drift");

    let mem_pp = Formula::mem(tf.clone(), pp.clone());
    let rgt = Formula::and(Formula::not(ne.clone()), mem_pp.clone());
    let sep_cond = Formula::and(mem_pp.clone(), psi.clone());

    // `f ∈ 𝒫prod(a,b) ↔ f ⊆ prod(a,b)`, the only difference between the shape
    // Separation produces and the shape the lemma is stated in.
    let pow_at_f = inst_all(pow_ax, &[prod_t, tf.clone()])?;
    let l_to_sep = hyp_and(
        &syl(&and_left(sub.clone(), psi.clone()), &iff_mpr(&pow_at_f)?)?,
        &and_right(sub, psi.clone()),
    )?;
    let sep_to_l = hyp_and(
        &syl(&and_left(mem_pp.clone(), psi.clone()), &iff_mp(&pow_at_f)?)?,
        &and_right(mem_pp.clone(), psi.clone()),
    )?;

    // ── There is a function: Separation applies, and the default is dead ─────
    let sep = crate::funcs::separation_nonempty(env, f, &psi, &pp)?;
    let ne_ex = syl(&exists_mono(f, &Thm::gen(f, &l_to_sep))?, &sep)?;

    let ne_fwd = a1i(&syl(&sep_to_l, &or_intro_left(l.clone(), rgt.clone()))?, ne.clone());
    let k = Formula::and(ne.clone(), phi.clone());
    let k_r_np = a1i(&and_left(Formula::not(ne.clone()), mem_pp.clone()), k.clone());
    let k_l = or_resolve_left(
        &and_left(ne.clone(), phi.clone()),
        &and_right(ne.clone(), phi.clone()),
        &k_r_np,
    )?;
    let ne_bwd = uncurry(&syl(&k_l, &l_to_sep)?)?;
    let ne_all = Thm::mp(
        &Thm::ax_dist(f, ne.clone(), Formula::iff(sep_cond, phi.clone()))?,
        &Thm::gen(f, &hyp_and(&ne_fwd, &ne_bwd)?),
    )?;
    let sv = env.fresh_var();
    let pos = retarget(f, sv, &ne_all, &ne_ex)?;

    // ── There is none: the condition degenerates to `f ∈ 𝒫prod(a,b)` ─────────
    let nne = Formula::not(ne.clone());
    let nne_nl = contrapos(&exists_intro_imp(f, l.clone(), tf.clone())?)?;
    let k2_nl = syl(&and_left(nne.clone(), phi.clone()), &nne_nl)?;
    let k2_r = hyp_mp(&and_right(nne.clone(), phi.clone()), &k2_nl)?;
    let nne_phi_mem = uncurry(&syl(&k2_r, &and_right(nne.clone(), mem_pp.clone()))?)?;
    let k3_r = hyp_and(
        &and_left(nne.clone(), mem_pp.clone()),
        &and_right(nne.clone(), mem_pp.clone()),
    )?;
    let nne_mem_phi = uncurry(&syl(&k3_r, &or_intro_right(l, rgt))?)?;
    let nne_all = Thm::mp(
        &Thm::ax_dist(f, nne.clone(), Formula::iff(mem_pp.clone(), phi.clone()))?,
        &Thm::gen(f, &hyp_and(&nne_mem_phi, &nne_phi_mem)?),
    )?;
    let sv2 = env.fresh_var();
    let p_s = Formula::forall(
        f,
        Formula::iff(Formula::mem(tf, Term::var(sv2)), phi.clone()),
    );
    let neg = syl(&nne_all, &exists_intro_imp(sv2, p_s, pp)?)?;

    let existence = cases(&pos, &neg)?;
    define_by_membership(env, &[a, b], &existence, f, &phi)
}

/// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))` — step 6 of the chain.
///
/// **Unconditional**, and that is the point of choosing `𝒫(prod(a,b))` as the
/// default in [`funspace`]: a member of `fs(a,b)` satisfies one disjunct or the
/// other, and each puts it in `𝒫(prod(a,b))` — the first because a function is
/// a subset of the product, the second outright.
pub fn funspace_subset_pow_prod(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    p: &Product,
    fs: FnSym,
    fs_def: &Thm,
) -> Option<Thm> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let prod_t = p.of(ta.clone(), tb.clone());
    let pp = Term::apply(pow, vec![prod_t.clone()]);
    let (l, ne, phi) = funspace_cond(env, sets, pow, p, &ta, &tb, f);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    let mem_pp = Formula::mem(tf.clone(), pp.clone());
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()));

    let pow_at_f = inst_all(pow_ax, &[prod_t, tf.clone()])?;
    let l_mem = syl(&and_left(sub, psi), &iff_mpr(&pow_at_f)?)?;
    let r_mem = and_right(Formula::not(ne), mem_pp.clone());
    let phi_mem = hyp_or_elim(
        &imp_refl(phi.clone()),
        &a1i(&l_mem, phi.clone()),
        &a1i(&r_mem, phi.clone()),
    )?;

    let fs_at_f = inst_all(fs_def, &[ta.clone(), tb.clone(), tf.clone()])?;
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    debug_assert_eq!(
        *fs_at_f.concl(),
        Formula::iff(Formula::mem(tf.clone(), fs_t.clone()), phi),
        "funspace's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&fs_at_f)?, &phi_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, fs_t, pp),
        "funspace_subset_pow_prod: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ ∀a ∀b. ((∃g. isfun(g)) → ∀f. (f ∈ fs(a,b) ↔ isfun(f)))` — the members of
/// the function space are the functions.
///
/// The antecedent is the default disjunct of [`funspace`] being dead, and it
/// cannot be dropped: without an empty set there is no way to name the set that
/// `a → b` should be when there are no functions at all. Compare
/// [`crate::funcs::collection`], which carries the same kind of antecedent for
/// the same reason.
pub fn funspace_members(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    p: &Product,
    fs: FnSym,
    fs_def: &Thm,
) -> Option<Thm> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let pp = Term::apply(pow, vec![p.of(ta.clone(), tb.clone())]);
    let (l, ne, phi) = funspace_cond(env, sets, pow, p, &ta, &tb, f);
    let mem_pp = Formula::mem(tf.clone(), pp);
    let rgt = Formula::and(Formula::not(ne.clone()), mem_pp.clone());

    // `NE → (φ → L)`: the second disjunct carries `¬NE`, which `NE` refutes.
    let k = Formula::and(ne.clone(), phi.clone());
    let k_r_np = a1i(&and_left(Formula::not(ne.clone()), mem_pp), k);
    let k_l = or_resolve_left(
        &and_left(ne.clone(), phi.clone()),
        &and_right(ne.clone(), phi.clone()),
        &k_r_np,
    )?;
    let ne_phi_l = uncurry(&k_l)?;
    let ne_l_phi = a1i(&or_intro_left(l.clone(), rgt), ne.clone());

    let fs_at_f = inst_all(fs_def, &[ta.clone(), tb.clone(), tf.clone()])?;
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    let mem_fs = Formula::mem(tf, fs_t);
    let ne_c_l = hyp_syl(&a1i(&iff_mp(&fs_at_f)?, ne.clone()), &ne_phi_l)?;
    let ne_l_c = hyp_syl(&ne_l_phi, &a1i(&iff_mpr(&fs_at_f)?, ne.clone()))?;

    let out = Thm::mp(
        &Thm::ax_dist(f, ne, Formula::iff(mem_fs, l))?,
        &Thm::gen(f, &hyp_and(&ne_c_l, &ne_l_c)?),
    )?;
    Some(gen_all(&[a, b], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Closure properties of `U(x)`, from the two clauses that *are* proved for it.
//
// `crate::universe::universe_power_closed` proves the same thing from
// `is_universe(u)`, which is not available for `U(x)` — its third clause is
// open (see `crate::universe::inaccessibility_reduction`). What is available is
// `C₂(U(x))` and `C₃(U(x))` separately, and those two are all the argument ever
// used, so it is rerun here against them.
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ C₂(u)`, i.e. `⊢ ∀y ∈ u. ∀z ⊆ y. z ∈ u`, infer
/// `⊢ big ∈ u → (small ⊆ big → small ∈ u)`.
pub fn sub_closed(c2: &Thm, big: &Term, small: &Term) -> Option<Thm> {
    let at_big = Thm::mp(&Thm::ax_inst(c2.concl().clone(), big.clone())?, c2)?;
    let (_, all_sub) = at_big.concl().as_imp()?;
    syl(&at_big, &Thm::ax_inst(all_sub, small.clone())?)
}

/// From `⊢ C₂(u)` and `⊢ C₃(u)` infer `⊢ ∀y. (y ∈ u → 𝒫y ∈ u)`.
///
/// Neither clause suffices alone. `C₃` puts *some* `p ∈ u` above every subset
/// of `y`, so `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the member `p`, back
/// into `u`. Inaccessibility is never touched.
pub fn pow_closed(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    u: &Term,
    c2: &Thm,
    c3: &Thm,
) -> Option<Thm> {
    let y = env.fresh_var();
    let ty = Term::var(y);
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let h = Formula::mem(ty.clone(), u.clone());
    let goal = Formula::mem(pow_y.clone(), u.clone());

    // `C₃` at `y`, with its witness `p` and the clause it satisfies read off.
    let c3_y = Thm::mp(&Thm::ax_inst(c3.concl().clone(), ty.clone())?, c3)?;
    let (h_chk, ex_p) = c3_y.concl().as_imp()?;
    if h_chk != h {
        return None
    }
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    debug_assert_eq!(ex_p, Formula::exists(p, bp.clone()), "C₃'s ∃p did not reopen");
    let (p_in_u, all_sub_p) = split_and(&bp)?;

    // ── Under `L := (y ∈ u) ∧ (p ∈ u ∧ ∀z ⊆ y. z ∈ p)` ───────────────────────
    let l = Formula::and(h.clone(), bp.clone());
    let l_bp = and_right(h.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all = syl(&l_bp, &and_right(p_in_u.clone(), all_sub_p.clone()))?;

    // `L → 𝒫y ⊆ p`: a member of `𝒫y` is a subset of `y`, and those are in `p`.
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l_v_sub_p = syl(&l_all, &Thm::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_step = hyp_syl(&a1i(&iff_mp(&pw_at_v)?, l.clone()), &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = Thm::mp(&Thm::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l.clone(), kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // `C₂` at `p` and then at `𝒫y`.
    let c2_pw = sub_closed(c2, &tp, &pow_y)?;
    let l_goal = hyp_mp(&hyp_mp(&a1i(&c2_pw, l), &l_p_in_u)?, &l_sub)?;

    let h_goal = discharge(p, &c3_y, &l_goal)?;
    debug_assert_eq!(*h_goal.concl(), Formula::imp(h, goal), "pow_closed: unexpected shape");
    Some(Thm::gen(y, &h_goal))
}

impl Funspace {
    /// Introduce `fs` and prove both lemmas about it.
    pub fn new(
        env: &mut Env,
        sets: &Sets,
        pow: FnSym,
        pow_ax: &Thm,
        p: &Product,
    ) -> Option<Funspace> {
        let (fs, fs_def) = funspace(env, sets, pow, pow_ax, p)?;
        let fs_ax = funspace_members(env, sets, pow, p, fs, &fs_def)?;
        let fs_sub = funspace_subset_pow_prod(env, sets, pow, pow_ax, p, fs, &fs_def)?;
        Some(Funspace { fs, fs_def, fs_ax, fs_sub })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The payoff.
// ─────────────────────────────────────────────────────────────────────────────

/// The ambient apparatus: pairing, union, power set and the canonical universe
/// operator, with the facts about `U(x)` that the chain consumes.
///
/// Assembled once and passed around, because each piece is a *definitional
/// extension*: building it twice would introduce two different symbols and the
/// theorems would not compose.
pub struct Space {
    /// Pairing and union.
    pub sets: Sets,
    /// The power set symbol.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// `⊢ ∀c. ⋃{c} = c` — what collapses `a ∪ a` to `a`.
    pub union_sing: Thm,
    /// `U(x)`, the least universe containing `x`.
    pub lu: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
    pub lu_ax: Thm,
    /// `⊢ ∀x. x ∈ U(x)`.
    pub mem_lu: Thm,
    /// `⊢ ∀x. C₂(U(x))`.
    pub c2: Thm,
    /// `⊢ ∀x. C₃(U(x))`.
    pub c3: Thm,
}

impl Space {
    /// Build everything, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Space> {
        let sets = Sets::new(env);
        let (pow, pow_ax) = crate::power(env);
        let union_sing = crate::union_singleton(env, sets.up, &sets.up_ax, sets.un, &sets.un_ax)?;
        let (lu, lu_ax) = crate::universe::least_universe(env)?;
        let mem_lu = crate::universe::mem_least_universe(env, lu, &lu_ax)?;
        let c2 = crate::universe::least_universe_closed_sub(env, lu, &lu_ax)?;
        let c3 = crate::universe::least_universe_closed_pow(env, lu, &lu_ax, pow, &pow_ax)?;
        Some(Space { sets, pow, pow_ax, union_sing, lu, lu_ax, mem_lu, c2, c3 })
    }

    /// The term `U(x)`.
    pub fn universe_of(&self, x: Term) -> Term { Term::apply(self.lu, vec![x]) }
}

/// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` — the general form, with the
/// one missing ingredient carried as an explicit antecedent.
///
/// Everything above `a ∪ b` is available: two power sets, the inclusion
/// [`product_subset_pow_pow`], one more power set, and
/// [`funspace_subset_pow_prod`], each cashed in through [`pow_closed`] or
/// [`sub_closed`]. What is *not* available is `a ∪ b ∈ U(c)` from `a ∈ U(c)`
/// and `b ∈ U(c)`: that is closure under binary unions, equivalently under
/// pairing, and neither follows from `C₂ ∧ C₃` — the only two clauses
/// [`crate::universe`] proves for `U(x)`. Getting it from the *third* clause
/// (`{a,b} ⊆ u`, so inaccessibility gives `{a,b} ∈ u` unless `{a,b} ≈ u`) needs
/// `is_universe(U(x))`, whose inaccessibility clause is open — see
/// [`crate::universe::inaccessibility_reduction`] and the Cantor–Schröder–
/// Bernstein argument it reduces to. So the antecedent stays, rather than being
/// smuggled in as an axiom.
pub fn funspace_in_universe_of(
    env: &mut Env,
    s: &Space,
    p: &Product,
    prod_pp: &Thm,
    fs: &Funspace,
) -> Option<Thm> {
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc) = (Term::var(a), Term::var(b), Term::var(c));
    let w = s.universe_of(tc.clone());

    let c2 = inst_all(&s.c2, std::slice::from_ref(&tc))?;
    let c3 = inst_all(&s.c3, std::slice::from_ref(&tc))?;
    let pc = pow_closed(env, s.pow, &s.pow_ax, &w, &c2, &c3)?;

    // `H := (a ∪ b) ∈ U(c)`, and two power sets above it.
    let un = bin_union(&s.sets, ta.clone(), tb.clone());
    let pu = Term::apply(s.pow, vec![un.clone()]);
    let ppu = Term::apply(s.pow, vec![pu.clone()]);
    let h_pu = inst_all(&pc, std::slice::from_ref(&un))?;
    let h = h_pu.concl().as_imp()?.0;
    debug_assert_eq!(h, Formula::mem(un, w.clone()));
    let h_ppu = syl(&h_pu, &inst_all(&pc, std::slice::from_ref(&pu))?)?;

    // `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` pulls the product in.
    let prod_t = p.of(ta.clone(), tb.clone());
    let prod_sub = inst_all(prod_pp, &[ta.clone(), tb.clone()])?;
    let h_prod = hyp_mp(
        &syl(&h_ppu, &sub_closed(&c2, &ppu, &prod_t)?)?,
        &a1i(&prod_sub, h.clone()),
    )?;

    // One more power set, then `fs(a,b) ⊆ 𝒫(prod(a,b))`.
    let pprod = Term::apply(s.pow, vec![prod_t.clone()]);
    let h_pprod = syl(&h_prod, &inst_all(&pc, std::slice::from_ref(&prod_t))?)?;
    let fs_t = fs.of(ta.clone(), tb.clone());
    let fs_sub = inst_all(&fs.fs_sub, &[ta.clone(), tb.clone()])?;
    let out = hyp_mp(
        &syl(&h_pprod, &sub_closed(&c2, &pprod, &fs_t)?)?,
        &a1i(&fs_sub, h.clone()),
    )?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(fs_t, w)),
        "funspace_in_universe_of: unexpected shape"
    );
    Some(gen_all(&[a, b, c], &out))
}

/// `⊢ ∀a. fs(a,a) ∈ U(a)` — **the payoff**: the function space `a → a` lands in
/// the least universe containing `a`.
///
/// This is what the tutorial's `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` needs: `⟦Sort 0⟧` is
/// a constant `P` and `⟦Sort (u+1)⟧` is `U(⟦Sort u⟧)`, so the goal is
/// `(P → P) ∈ U(P)`.
///
/// [`funspace_in_universe_of`] does the work; all that is left is to discharge
/// its antecedent at `b = c = a`, where it reads `(a ∪ a) ∈ U(a)`. And `a ∪ a`
/// is `⋃{a,a}` — that is, `⋃{a}` — which [`crate::union_singleton`] equates
/// with `a`, while `a ∈ U(a)` is [`crate::universe::mem_least_universe`]. The
/// binary union that blocks the general case simply disappears.
pub fn funspace_in_universe(
    env: &mut Env,
    s: &Space,
    fs: &Funspace,
    general: &Thm,
) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let w = s.universe_of(ta.clone());

    let uaa = bin_union(&s.sets, ta.clone(), ta.clone());
    debug_assert_eq!(
        uaa,
        s.sets.union_of(singleton(s.sets.up, ta.clone())),
        "a ∪ a is not ⋃{{a}}"
    );
    let eq_uaa = inst_all(&s.union_sing, std::slice::from_ref(&ta))?;
    debug_assert_eq!(*eq_uaa.concl(), Formula::eq(uaa.clone(), ta.clone()));

    // `⋃{a} ∈ U(a)`, by moving `a ∈ U(a)` across the equation.
    let a_in = inst_all(&s.mem_lu, std::slice::from_ref(&ta))?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ta.clone(),
        uaa,
        hole,
        Formula::mem(Term::var(hole), w.clone()),
    );
    let un_in = Thm::mp(&Thm::mp(&leib, &eq_symm(env, &eq_uaa)?)?, &a_in)?;

    let inst = inst_all(general, &[ta.clone(), ta.clone(), ta.clone()])?;
    let out = Thm::mp(&inst, &un_in)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(fs.of(ta.clone(), ta), w),
        "funspace_in_universe: unexpected shape"
    );
    Some(Thm::gen(a, &out))
}

/// The whole development: every symbol, every theorem, and the payoff.
pub struct Development {
    /// Pairing, union, power set, `U(x)`.
    pub space: Space,
    /// The Cartesian product.
    pub product: Product,
    /// `⊢ ∀a ∀b. prod(a,b) ⊆ 𝒫𝒫(a ∪ b)`.
    pub prod_sub: Thm,
    /// The function space.
    pub funspace: Funspace,
    /// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))`.
    pub in_universe_of: Thm,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    pub in_universe: Thm,
}

impl Development {
    /// Build it all.
    pub fn new(env: &mut Env) -> Option<Development> {
        let space = Space::new(env)?;
        let product = product(env, &space.sets)?;
        let up_sub = upair_subset(env, &space.sets)?;
        let pair_pp = pair_in_pow_pow(env, &space.sets, space.pow, &space.pow_ax, &up_sub)?;
        let (ml, mr) = mem_bin_union(env, &space.sets)?;
        let prod_sub = product_subset_pow_pow(
            env,
            &space.sets,
            space.pow,
            &product,
            &pair_pp,
            &ml,
            &mr,
        )?;
        let funspace = Funspace::new(env, &space.sets, space.pow, &space.pow_ax, &product)?;
        let in_universe_of =
            funspace_in_universe_of(env, &space, &product, &prod_sub, &funspace)?;
        let in_universe = funspace_in_universe(env, &space, &funspace, &in_universe_of)?;
        Some(Development { space, product, prod_sub, funspace, in_universe_of, in_universe })
    }
}
