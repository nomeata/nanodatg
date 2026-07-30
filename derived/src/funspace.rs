//! Cartesian products, function spaces, and the fact the tutorial needs:
//! `(a → a) ∈ U(a)`.
//!
//! # Why the product is built from Replacement, not Separation
//!
//! The textbook construction cuts `a × b` out of `𝒫𝒫(a ∪ b)` by Separation.
//! When this was written the only Separation available was
//! [`crate::separation::separation_nonvacuous`] (equivalently
//! [`crate::funcs::separation_nonempty`]), which requires the *result* to be
//! inhabited — and `a × b` really can be empty, so no witness could be
//! supplied. So the product is assembled from Replacement instead, where every
//! step is *total* and no inhabitation is needed:
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
//! # The function space, and the antecedent that used to survive
//!
//! The function space *is* carved out of a power set by a condition, and `a → b`
//! is empty when `a` is inhabited and `b` is not. For as long as Separation
//! needed its result inhabited, `fs(a,b)` had to be defined by the same
//! total-by-default trick [`crate::funcs::collection`] used — an extra
//! disjunct firing only when there were no functions at all, degenerating to
//! `𝒫(prod(a,b))` — and [`funspace_members`] was conditional on
//! `∃g. isfun(g)`, dischargeable only on the diagonal via the identity
//! function.
//!
//! `∅` removes all of that. [`crate::funcs::separation_full`] produces the
//! separated set whether or not it is inhabited, so [`funspace`] defines the
//! intended condition outright and
//!
//! ```text
//! ⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))
//! ```
//!
//! holds with no antecedent, for every `a` and `b` rather than only on the
//! diagonal. [`funspace_subset_pow_prod`] is unchanged (it was already
//! unconditional), and [`funspace_diagonal_members`] survives as the `b := a`
//! instance the universe argument quotes.
//!
//! # The chain to `(a → a) ∈ U(a)`
//!
//! | step | lemma |
//! |---|---|
//! | `a ∈ U(a)` | [`crate::universe::mem_least_universe`] |
//! | `y ∈ U(x) → 𝒫y ∈ U(x)` | [`pow_closed`] |
//! | `(y ∈ U(x) ∧ z ⊆ y) → z ∈ U(x)` | [`sub_closed`] |
//! | `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` | [`product_subset_pow_pow`] |
//! | `fs(a,b) ⊆ 𝒫(prod(a,b))` | [`funspace_subset_pow_prod`] |
//! | `f ∈ fs(a,b) ↔ isfun(f)` | [`funspace_members`] |
//! | `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)` | [`funspace_in_universe_of`] |
//! | `a ∪ a = a` | [`crate::union_singleton`] |
//! | `fs(a,a) ∈ U(a)` | [`funspace_in_universe`] |
//!
//! **What the two-argument case is missing, exactly.** Everything above
//! `a ∪ b` goes through, which is why [`funspace_in_universe_of`] is stated in
//! full with `(a ∪ b) ∈ U(c)` as its antecedent. Discharging that antecedent
//! from `a ∈ U(c)` and `b ∈ U(c)` is closure of `U(c)` under binary unions —
//! equivalently under pairing, since `a ∪ b` is `⋃{a,b}` — and that does *not*
//! follow from the two clauses [`crate::universe`] proves for `U(x)`. It would
//! follow from the third, inaccessibility (`{a,b} ⊆ u`, so `{a,b} ∈ u` unless
//! `{a,b} ≈ u`), but inaccessibility for `U(x)` is open: see
//! [`crate::universe::inaccessibility_reduction`], where what remains is
//! Cantor–Schröder–Bernstein. No axiom is added to route around this; the
//! antecedent is simply carried.
//!
//! At `b = c = a` the antecedent becomes `(a ∪ a) ∈ U(a)`, and `a ∪ a` is
//! `⋃{a,a}` — that is, `⋃{a}`, which [`crate::union_singleton`] equates with
//! `a`. So the binary union disappears rather than having to be closed over,
//! and [`funspace_in_universe`] is unconditional. That is the case the tutorial
//! needs.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, union_intro, Sets};
use crate::{
    a1i, and_intro, and_left, and_right, com12, define_by_membership, eq_symm,
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
    /// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the defining axiom, which is
    /// now the intended condition and nothing else.
    pub fs_def: Thm,
    /// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the same statement, with
    /// [`funspace_members`] having rebuilt `isfun` independently and checked it
    /// against the defining axiom.
    pub fs_ax: Thm,
    /// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))`.
    pub fs_sub: Thm,
}

impl Funspace {
    /// Introduce `fs` and prove both lemmas about it.
    ///
    /// `empty` must be a proof `⊢ ∀z. ¬(z ∈ e)` — [`Space::empty_ax`] is one.
    /// It is consumed by Separation and appears in none of the results.
    pub fn new(
        env: &mut Env,
        sets: &Sets,
        pow: FnSym,
        pow_ax: &Thm,
        p: &Product,
        empty: &Thm,
    ) -> Option<Funspace> {
        let (fs, fs_def) = funspace(env, sets, pow, pow_ax, p, empty)?;
        let fs_ax = funspace_members(env, sets, p, fs, &fs_def)?;
        let fs_sub = funspace_subset_pow_prod(env, sets, pow, pow_ax, p, fs, &fs_def)?;
        Some(Funspace { fs, fs_def, fs_ax, fs_sub })
    }

    /// The term `fs(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.fs, vec![a, b]) }
}

/// Introduce `fs(a,b) = a → b`, with
/// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))`.
///
/// **The condition defined is the intended one.** The function space is carved
/// out of `𝒫(prod(a,b))` by a condition, and `a → b` really is empty when `a`
/// is inhabited and `b` is not — so for as long as Separation needed its result
/// to be inhabited, the symbol could only be made total by a default disjunct,
///
/// ```text
/// f ∈ fs(a,b)  ↔  isfun(f)  ∨  (¬∃g. isfun(g)  ∧  f ∈ 𝒫prod(a,b))
/// ```
///
/// with the intended condition recoverable only under the antecedent
/// `∃g. isfun(g)`. With `∅` in hand [`crate::funcs::separation_full`] produces
/// the set outright, empty or not, and the disjunct is gone.
///
/// The only work left is cosmetic: Separation carves by `f ∈ 𝒫prod(a,b) ∧ ψ`
/// and the lemma is stated with `f ⊆ prod(a,b) ∧ ψ`, so the two are swapped
/// inside the existential using the Power Set characterisation.
pub fn funspace(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    p: &Product,
    empty: &Thm,
) -> Option<(FnSym, Thm)> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let prod_t = p.of(ta.clone(), tb.clone());
    let pp = Term::apply(pow, vec![prod_t.clone()]);
    let l = is_function(env, sets, p, &ta, &tb, &tf);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()), "funspace: condition shape drift");

    let mem_pp = Formula::mem(tf.clone(), pp.clone());
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
        &and_right(mem_pp, psi.clone()),
    )?;

    let sep = crate::funcs::separation_full(env, f, &psi, &pp, empty)?;

    // Swap the carved condition for `isfun` inside the existential.
    let sv = env.fresh_var();
    let mem_fs = Formula::mem(tf.clone(), Term::var(sv));
    let p_s = Formula::forall(f, Formula::iff(mem_fs.clone(), sep_cond));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(sv, p_s.clone()),
        "funspace: Separation has an unexpected shape"
    );

    let p_inst = Thm::ax_inst(p_s.clone(), tf.clone())?;
    let p_fwd = hyp_syl(&hyp_iff_mp(&p_inst)?, &a1i(&sep_to_l, p_s.clone()))?;
    let p_bwd = hyp_syl(&a1i(&l_to_sep, p_s.clone()), &hyp_iff_mpr(&p_inst)?)?;
    let p_q = Thm::mp(
        &Thm::ax_dist(f, p_s.clone(), Formula::iff(mem_fs, l.clone()))?,
        &Thm::gen(f, &hyp_and(&p_fwd, &p_bwd)?),
    )?;
    let existence = Thm::mp(&exists_mono(sv, &Thm::gen(sv, &p_q))?, &sep)?;

    define_by_membership(env, &[a, b], &existence, f, &l)
}

/// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))` — step 6 of the chain.
///
/// A member of `fs(a,b)` is a function, and a function is a subset of the
/// product, hence a member of its power set. (This was already unconditional
/// when `fs` carried a default disjunct — the default was chosen to be
/// `𝒫(prod(a,b))` precisely so that it would be. Now there is only one case.)
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
    let l = is_function(env, sets, p, &ta, &tb, &tf);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()));

    let pow_at_f = inst_all(pow_ax, &[prod_t, tf.clone()])?;
    let l_mem = syl(&and_left(sub, psi), &iff_mpr(&pow_at_f)?)?;

    let fs_at_f = inst_all(fs_def, &[ta.clone(), tb.clone(), tf.clone()])?;
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    debug_assert_eq!(
        *fs_at_f.concl(),
        Formula::iff(Formula::mem(tf.clone(), fs_t.clone()), l),
        "funspace's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&fs_at_f)?, &l_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, fs_t, pp),
        "funspace_subset_pow_prod: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the members of the function space
/// are the functions, **unconditionally**.
///
/// This used to be conditional on `∃g. isfun(g)`, that being the hypothesis
/// under which [`funspace`]'s default disjunct was dead. There is no default
/// any more, so the statement is exactly the defining axiom — and what this
/// function adds is the *check*: it rebuilds `isfun(f)` from
/// [`is_function`] independently and refuses unless `fs_def` characterises
/// `fs(a,b)` by precisely that. A symbol defined by some other condition would
/// give a true theorem about the wrong set, silently, and that is what the
/// comparison rules out.
pub fn funspace_members(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    fs: FnSym,
    fs_def: &Thm,
) -> Option<Thm> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let l = is_function(env, sets, p, &ta, &tb, &tf);
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(f, Formula::iff(Formula::mem(tf, fs_t), l)),
        ),
    );
    if *fs_def.concl() != expected {
        return None
    }
    Some(fs_def.clone())
}

// ─────────────────────────────────────────────────────────────────────────────
// The identity function.
//
// This used to be load-bearing: [`funspace_members`] carried an inhabitation
// antecedent, and `id(a)` was the only thing that could discharge it — on the
// diagonal, which is why `fs(a,a)` was characterised and `fs(a,b)` was not.
// With `∅` the antecedent is gone and the identity is no longer needed for
// that. It is kept because it is the canonical inhabitant of `fs(a,a)` and the
// only concrete function this development builds, so it is what a test can use
// to check that the function space is not accidentally empty.
// ─────────────────────────────────────────────────────────────────────────────

/// `id(a) = { ⟨x,x⟩ : x ∈ a }`, with
/// `⊢ ∀a ∀z. (z ∈ id(a) ↔ ∃x. (x ∈ a ∧ z = ⟨x,x⟩))`.
///
/// Replacement at its cheapest, exactly as [`crate::funcs::lambda`]: the
/// relation is `z = ⟨x,x⟩`, so the `∃!` premise is [`crate::exists_unique_eq`]
/// and costs nothing.
pub fn identity_graph(env: &mut Env, sets: &Sets) -> Option<(FnSym, Thm)> {
    let (a, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(a), Term::var(x));

    let pair = sets.pair(tx.clone(), tx.clone());
    let (z, phi, exu) = exists_unique_eq(env, &[], &pair);

    let repl = Thm::ax_replacement(env, x, z, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    define_by_membership(env, &[a], &img, z, &cond)
}

/// `⊢ ⟨x,y⟩ ∈ id(a) → y = x` — the identity graph relates nothing but equals.
///
/// The pair is `⟨u,u⟩` for some `u ∈ a`, and injectivity of the Kuratowski pair
/// gives `x = u` and `y = u` at once.
#[allow(clippy::too_many_arguments)]
fn identity_pair_eq(
    env: &mut Env,
    sets: &Sets,
    id: FnSym,
    id_ax: &Thm,
    pair_inj: &Thm,
    a: &Term,
    x: &Term,
    y: &Term,
) -> Option<Thm> {
    let id_a = Term::apply(id, vec![a.clone()]);
    let pair_xy = sets.pair(x.clone(), y.clone());
    let at_pair = inst_all(id_ax, &[a.clone(), pair_xy.clone()])?;

    let u = env.fresh_var();
    let tu = Term::var(u);
    let pair_uu = sets.pair(tu.clone(), tu.clone());
    let mem_ua = Formula::mem(tu.clone(), a.clone());
    let eq_pairs = Formula::eq(pair_xy.clone(), pair_uu);
    let f = Formula::and(mem_ua.clone(), eq_pairs.clone());
    debug_assert_eq!(
        *at_pair.concl(),
        Formula::iff(Formula::mem(pair_xy, id_a), Formula::exists(u, f.clone())),
        "the identity graph's membership condition has an unexpected shape"
    );

    let inj = inst_all(pair_inj, &[x.clone(), y.clone(), tu.clone(), tu.clone()])?;
    let f_conj = syl(&and_right(mem_ua, eq_pairs), &inj)?;
    let (e_xu, e_yu) = (Formula::eq(x.clone(), tu.clone()), Formula::eq(y.clone(), tu.clone()));
    let f_xu = syl(&f_conj, &and_left(e_xu.clone(), e_yu.clone()))?;
    let f_yu = syl(&f_conj, &and_right(e_xu, e_yu))?;

    // `u = x` turns `y = u` into `y = x`.
    let f_ux = syl(&f_xu, &eq_symm_imp(env, x.clone(), tu.clone()))?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(tu, x.clone(), w, Formula::eq(y.clone(), Term::var(w)));
    let f_goal = hyp_mp(&hyp_mp(&a1i(&leib, f), &f_ux)?, &f_yu)?;

    let goal = Formula::eq(y.clone(), x.clone());
    syl(&iff_mp(&at_pair)?, &exists_elim_imp(u, &Thm::gen(u, &f_goal), &goal)?)
}

/// `⊢ ∀a. isfun(id(a))` — the identity graph is a function from `a` to `a`.
///
/// All three clauses: it is a set of pairs from `a × a`; it is total, since
/// `⟨x,x⟩ ∈ id(a)` for every `x ∈ a`; and it is single-valued, since
/// [`identity_pair_eq`] forces every value at `x` to be `x`.
pub fn identity_is_function(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    id: FnSym,
    id_ax: &Thm,
    pair_inj: &Thm,
) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let id_a = Term::apply(id, vec![ta.clone()]);
    let prod_aa = p.of(ta.clone(), ta.clone());

    let (t, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, tx, ty) = (Term::var(t), Term::var(x), Term::var(y));
    let pair_xx = sets.pair(tx.clone(), tx.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    // ── id(a) ⊆ prod(a,a) ────────────────────────────────────────────────────
    let e = Formula::and(mem_xa.clone(), Formula::eq(tt.clone(), pair_xx.clone()));
    let body_y = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(tt.clone(), sets.pair(tx.clone(), ty.clone())),
    );
    debug_assert_eq!(body_y.subst(y, &tx), e, "the inner witness does not substitute to E");

    let e_inner = exists_intro_imp(y, body_y.clone(), tx.clone())?;
    let e_xa = and_left(mem_xa.clone(), Formula::eq(tt.clone(), pair_xx.clone()));
    let prod_body = Formula::and(mem_xa.clone(), Formula::exists(y, body_y));
    let e_prod_cond =
        syl(&hyp_and(&e_xa, &e_inner)?, &exists_intro_imp(x, prod_body, tx.clone())?)?;

    let prod_at_t = inst_all(&p.prod_ax, &[ta.clone(), ta.clone(), tt.clone()])?;
    let e_in_prod = syl(&e_prod_cond, &iff_mpr(&prod_at_t)?)?;
    let id_at_t = inst_all(id_ax, &[ta.clone(), tt.clone()])?;
    let mem_t_prod = Formula::mem(tt.clone(), prod_aa.clone());
    let sub = Thm::gen(
        t,
        &syl(
            &iff_mp(&id_at_t)?,
            &exists_elim_imp(x, &Thm::gen(x, &e_in_prod), &mem_t_prod)?,
        )?,
    );
    debug_assert_eq!(
        *sub.concl(),
        kernel::thm::subset(env, id_a.clone(), prod_aa),
        "identity_is_function: the subset clause has an unexpected shape"
    );

    // ── total on `a`, with `x` its own value ─────────────────────────────────
    let u = env.fresh_var();
    let tu = Term::var(u);
    let body_u = Formula::and(
        Formula::mem(tu.clone(), ta.clone()),
        Formula::eq(pair_xx.clone(), sets.pair(tu.clone(), tu)),
    );
    let x_pair = hyp_and(
        &imp_refl(mem_xa.clone()),
        &a1i(&Thm::eq_refl(pair_xx.clone()), mem_xa.clone()),
    )?;
    let id_at_pair = inst_all(id_ax, &[ta.clone(), pair_xx])?;
    let x_in_id = syl(
        &syl(&x_pair, &exists_intro_imp(u, body_u, tx.clone())?)?,
        &iff_mpr(&id_at_pair)?,
    )?;

    let body_t = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::mem(sets.pair(tx.clone(), ty), id_a.clone()),
    );
    let total = Thm::gen(
        x,
        &syl(
            &hyp_and(&imp_refl(mem_xa), &x_in_id)?,
            &exists_intro_imp(y, body_t, tx.clone())?,
        )?,
    );
    debug_assert_eq!(
        *total.concl(),
        is_total(env, sets, &ta, &ta, &id_a),
        "identity_is_function: the totality clause has an unexpected shape"
    );

    // ── single-valued: every value at `x` is `x` ─────────────────────────────
    let (y1, y2) = (env.fresh_var(), env.fresh_var());
    let (ty1, ty2) = (Term::var(y1), Term::var(y2));
    let m1 = Formula::mem(sets.pair(tx.clone(), ty1.clone()), id_a.clone());
    let m2 = Formula::mem(sets.pair(tx.clone(), ty2.clone()), id_a.clone());
    let h = Formula::and(m1.clone(), m2.clone());

    let e1 = identity_pair_eq(env, sets, id, id_ax, pair_inj, &ta, &tx, &ty1)?;
    let e2 = identity_pair_eq(env, sets, id, id_ax, pair_inj, &ta, &tx, &ty2)?;
    let h_y1x = syl(&and_left(m1.clone(), m2.clone()), &e1)?;
    let h_y2x = syl(&and_right(m1, m2), &e2)?;

    let h_xy2 = syl(&h_y2x, &eq_symm_imp(env, ty2.clone(), tx.clone()))?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(tx, ty2, w, Formula::eq(ty1, Term::var(w)));
    let sv = gen_all(&[x, y1, y2], &hyp_mp(&hyp_mp(&a1i(&leib, h), &h_xy2)?, &h_y1x)?);
    debug_assert_eq!(
        *sv.concl(),
        is_single_valued(env, sets, &id_a),
        "identity_is_function: the single-valuedness clause has an unexpected shape"
    );

    let out = and_intro(&sub, &and_intro(&total, &sv));
    debug_assert_eq!(
        *out.concl(),
        is_function(env, sets, p, &ta, &ta, &id_a),
        "identity_is_function: unexpected shape"
    );
    Some(Thm::gen(a, &out))
}

/// `⊢ ∀a. ∃f. isfun(f)` — the diagonal function space is inhabited.
///
/// The witness is `id(a)`. This is exactly the antecedent
/// [`funspace_members`] carries, so it is what makes that lemma usable.
pub fn diagonal_inhabited(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    id: FnSym,
    id_fun: &Thm,
) -> Option<Thm> {
    let (a, f) = (env.fresh_var(), env.fresh_var());
    let ta = Term::var(a);
    let id_a = Term::apply(id, vec![ta.clone()]);
    let phi = is_function(env, sets, p, &ta, &ta, &Term::var(f));
    let witness = inst_all(id_fun, std::slice::from_ref(&ta))?;
    Some(Thm::gen(a, &crate::exists_intro(f, phi, id_a, &witness)?))
}

/// `⊢ ∀a ∀f. (f ∈ fs(a,a) ↔ isfun(f))` — [`funspace_members`] on the diagonal.
///
/// Once the general lemma became unconditional this is a plain instantiation:
/// the two arguments of `fs` are set equal and the result re-quantified. It is
/// kept because it is the statement the universe argument and the tutorial
/// quote, and because it pins that `fs(a,a)` has exactly the functions `a → a`
/// as members, no more and no less.
pub fn funspace_diagonal_members(env: &mut Env, fs_ax: &Thm) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let inst = inst_all(fs_ax, &[ta.clone(), ta])?;
    Some(Thm::gen(a, &inst))
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
    /// `∅`, with no members; see [`crate::empty::empty`].
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)` — what makes Separation, and hence [`funspace`],
    /// unconditional.
    pub empty_ax: Thm,
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
    /// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d))`.
    pub pair_inj: Thm,
}

impl Space {
    /// Build everything, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Space> {
        let sets = Sets::new(env);
        let (pow, pow_ax) = crate::power(env);
        let union_sing = crate::union_singleton(env, sets.up, &sets.up_ax, sets.un, &sets.un_ax)?;
        let (empty, empty_ax) = crate::empty::empty(env);
        let (lu, lu_ax) = crate::universe::least_universe(env)?;
        let mem_lu = crate::universe::mem_least_universe(env, lu, &lu_ax)?;
        let c2 = crate::universe::least_universe_closed_sub(env, lu, &lu_ax)?;
        let c3 = crate::universe::least_universe_closed_pow(env, lu, &lu_ax, pow, &pow_ax)?;

        let mem_sing = crate::mem_singleton(env, sets.up, &sets.up_ax)?;
        let sing_inj = crate::singleton_inj(env, sets.up, &mem_sing)?;
        let fst = crate::opair_fst(env, sets.up, &sets.up_ax, &mem_sing, &sing_inj)?;
        let snd = crate::pairs::opair_snd(env, sets.up, &sets.up_ax, &mem_sing, &fst)?;
        let pair_inj = crate::pairs::opair_inj(env, sets.up, &fst, &snd)?;

        Some(Space { sets, pow, pow_ax, union_sing, empty, empty_ax, lu, lu_ax, mem_lu, c2, c3, pair_inj })
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
    /// `id(a) = { ⟨x,x⟩ : x ∈ a }`.
    pub id: FnSym,
    /// `⊢ ∀a ∀z. (z ∈ id(a) ↔ ∃x. (x ∈ a ∧ z = ⟨x,x⟩))`.
    pub id_ax: Thm,
    /// `⊢ ∀a. isfun(id(a))`.
    pub id_fun: Thm,
    /// `⊢ ∀a ∀f. (f ∈ fs(a,a) ↔ isfun(f))` — the `b := a` instance of
    /// [`Funspace::fs_ax`], which is itself unconditional.
    pub diagonal_members: Thm,
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
        let funspace =
            Funspace::new(env, &space.sets, space.pow, &space.pow_ax, &product, &space.empty_ax)?;

        let (id, id_ax) = identity_graph(env, &space.sets)?;
        let id_fun =
            identity_is_function(env, &space.sets, &product, id, &id_ax, &space.pair_inj)?;
        let diagonal_members = funspace_diagonal_members(env, &funspace.fs_ax)?;

        let in_universe_of =
            funspace_in_universe_of(env, &space, &product, &prod_sub, &funspace)?;
        let in_universe = funspace_in_universe(env, &space, &funspace, &in_universe_of)?;
        Some(Development {
            space,
            product,
            prod_sub,
            funspace,
            id,
            id_ax,
            id_fun,
            diagonal_members,
            in_universe_of,
            in_universe,
        })
    }
}
