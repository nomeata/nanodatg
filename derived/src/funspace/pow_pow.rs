//! The binary union, and the product inside a double power set.
//!
//! # Interface
//!
//! `bin_union(a,b)` is the *term* `⋃{a,b}` — a composition of existing symbols,
//! so no definitional extension and no proof obligation, the same economy
//! [`crate::singleton`] and [`crate::opair`] get. Writing `a ∪ b` for it, the
//! exports are
//!
//! ```text
//! ⊢ ∀u ∀v ∀c. ((u ∈ c ∧ v ∈ c) → {u,v} ⊆ c)              [upair_subset]
//! ⊢ ∀a ∀b ∀x. (x ∈ a → x ∈ a ∪ b)  and  the `b` half     [mem_bin_union]
//! ⊢ ∀x ∀y ∀c. ((x ∈ c ∧ y ∈ c) → ⟨x,y⟩ ∈ 𝒫𝒫c)            [pair_in_pow_pow]
//! ⊢ ∀a ∀b. prod(a,b) ⊆ 𝒫𝒫(a ∪ b)                         [product_subset_pow_pow]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! [`upair_subset`] serves for singletons too, since `{u}` is `{u,u}`. The
//! Kuratowski pair `⟨x,y⟩` is `{{x},{x,y}}`, so both its members are subsets of
//! `c`, hence members of `𝒫c`, hence the pair is a subset of `𝒫c` and so a
//! member of `𝒫𝒫c` — three applications of [`upair_subset`], each cashed in
//! through the Power Set characterisation. [`product_subset_pow_pow`] is then
//! one step: a member of the product is a pair whose components are in `a` and
//! `b`, hence both in `a ∪ b`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Sets};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, gen_all, hyp_and, hyp_mp,
    hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all, singleton, syl, uncurry, upair_members,
};
use super::glue::{carry_elem, discharge};
use super::cartesian::Product;

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
    let intro_a = union_intro(env, sets, ab.clone(), ta.clone(), tx.clone()).ok()?;
    let left = syl(&hyp_and(&a1i(&a_in, mem_xa.clone()), &imp_refl(mem_xa))?, &intro_a)?;

    let mem_xb = Formula::mem(tx.clone(), tb.clone());
    let intro_b = union_intro(env, sets, ab, tb.clone(), tx.clone()).ok()?;
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
