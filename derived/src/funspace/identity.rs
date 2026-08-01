//! The identity function `id(a) = { ⟨x,x⟩ : x ∈ a }`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀z. (z ∈ id(a) ↔ ∃x. (x ∈ a ∧ z = ⟨x,x⟩))   [identity_graph — introduces `id`]
//! ⊢ ∀a. isfun(a, a, id(a))                         [identity_is_function]
//! ⊢ ∀a. ∃f. isfun(a, a, f)                         [diagonal_inhabited]
//! ⊢ ∀a ∀f. (f ∈ fs(a,a) ↔ isfun(a, a, f))          [funspace_diagonal_members]
//! ```
//!
//! Callers need none of the derivations below. `id` is Replacement at its
//! cheapest, exactly as [`crate::funcs::lambda`]: the relation is `z = ⟨x,x⟩`,
//! so the `∃!` premise is [`crate::exists_unique_eq`] and costs nothing.
//!
//! # Why this is kept
//!
//! It used to be load-bearing: [`crate::funspace::funspace_members`] carried an
//! inhabitation antecedent, and `id(a)` was the only thing that could discharge
//! it — on the diagonal, which is why `fs(a,a)` was characterised and `fs(a,b)`
//! was not. With `∅` the antecedent is gone and the identity is no longer needed
//! for that; [`funspace_diagonal_members`] is now a plain instantiation.
//!
//! It is kept because it is the canonical inhabitant of `fs(a,a)` and the only
//! concrete function this development builds, so it is what a test can use to
//! check that the function space is not accidentally empty — and because
//! [`funspace_diagonal_members`] is the statement the universe argument and the
//! tutorial quote.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::{
    a1i, and_intro, and_left, and_right, define_by_membership, eq_symm_imp, exists_elim_imp,
    exists_intro_imp, exists_unique_eq, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl,
    inst_all, syl,
};
use super::cartesian::Product;
use super::space::{is_function, is_single_valued, is_total};

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
/// [`crate::funspace::funspace_members`] carries, so it is what makes that lemma usable.
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

/// `⊢ ∀a ∀f. (f ∈ fs(a,a) ↔ isfun(f))` — [`crate::funspace::funspace_members`] on the diagonal.
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
