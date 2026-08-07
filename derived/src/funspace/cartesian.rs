//! The Cartesian product `prod(a,b) = a × b`, built from Replacement.
//!
//! # Interface
//!
//! With `product_cond(a,b,z) := ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩))`, the
//! export is
//!
//! ```text
//! ⊢ ∀a ∀b ∀z. (z ∈ prod(a,b) ↔ product_cond(a,b,z))     [Product::prod_ax]
//! ```
//!
//! **unconditionally** — no inhabitation antecedent anywhere. [`product`]
//! introduces the symbol and proves it; [`Product`] carries it together with the
//! two auxiliary symbols and their own characteristic theorems. Callers need
//! none of the derivation below.
//!
//! # Why Replacement and not Separation
//!
//! The textbook construction cuts `a × b` out of `𝒫𝒫(a ∪ b)` by Separation.
//! When this was written the only Separation available was
//! [`crate::separation::separation_nonvacuous`] (equivalently
//! [`crate::funcs::separation_nonempty`]), which requires the *result* to be
//! inhabited — and `a × b` really can be empty, so no witness could be supplied.
//! So the product is assembled from Replacement instead, where every step is
//! *total* and no inhabitation is needed:
//!
//! ```text
//! row(x, b)  := { ⟨x,y⟩ : y ∈ b }        — Replacement along y ↦ ⟨x,y⟩
//! fam(a, b)  := { row(x,b) : x ∈ a }     — Replacement along x ↦ row(x,b)
//! prod(a, b) := ⋃ fam(a, b)
//! ```
//!
//! Both Replacement instances have the trivial `∃!` premise `∃!v. v = t`, which
//! [`crate::exists_unique_eq`] discharges for free, and the final union is an
//! explicit definition. `∅` has since made Separation unconditional, so the
//! detour is no longer forced — but it costs nothing and it is what is here.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Sets};
use crate::{
    a1i, and_intro, and_left, and_right, define_by_membership, eq_symm, exists_elim_imp,
    exists_intro_imp, exists_unique_eq, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl,
};
use super::glue::{carry_mem, discharge};

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
#[derive(Clone)]
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

    let intro = union_intro(env, sets, fam_t.clone(), row_t.clone(), tz.clone()).ok()?;
    let e2_ufam = syl(&hyp_and(&e2_row_fam, &e2_z_row)?, &intro)?;
    let e2_prod = syl(&e2_ufam, &u2p)?;

    let bwd = exists_elim_imp(x, &Thm::gen(x, &e2_prod), &mem_prod)?;
    debug_assert_eq!(*bwd.concl(), Formula::imp(goal.clone(), mem_prod.clone()));

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(*out.concl(), Formula::iff(mem_prod, goal), "product_members: unexpected shape");
    Some(gen_all(&[a, b, z], &out))
}
