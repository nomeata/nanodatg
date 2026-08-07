//! Closure under **Replacement**: the image `{ b(x) : x ∈ A }` of a member.
//!
//! # Interface
//!
//! Writing `img(A)` for the Replacement image [`crate::ext::image_symbol`]
//! builds from a unary fibre symbol `b`, and
//!
//! ```text
//! fibres_in(A,u) := ∀x. (x ∈ A → b(x) ∈ u)      [fibres_in]
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ fibres_in(A,u))) → img(A) ∈ u)
//!                                                        [universe_replacement]
//! ⊢ ∀c ∀A. ((A ∈ U(c) ∧ fibres_in(A,U(c))) → img(A) ∈ U(c))
//!                                                   [least_universe_replacement]
//! ```
//!
//! The second carries no hypothesis about `U(c)`. Callers need none of the
//! derivations below.
//!
//! # The argument
//!
//! `img(A)` is a subset of `u` — every member is some `b(x)` with `x ∈ A`, and
//! those are in `u` by hypothesis — and it is the **surjective image** of the
//! member `A` under the relation
//!
//! ```text
//! R(x,w) := x ∈ A ∧ w = b(x)
//! ```
//!
//! whose three clauses cost nothing: `DOM` is a projection, `SV` is
//! transitivity of equality, and `ONTO` is the *forward* half of `img`'s own
//! characteristic property. So [`crate::cantor::image_in_universe`] applies,
//! and this is Replacement closure with no `⋃`, no power set and no pairing.
//!
//! Note what is **not** needed: the fibres need not be distinct, `b` need not
//! be injective, and `A` need not be inhabited. `C₂` and `C₄` do all the work,
//! inside `image_in_universe`; `C₁` is not used here at all.
//!
//! # How this fails
//!
//! Both entries take symbols and theorems from their caller, and the split
//! follows that boundary. A **decline** is the contract working: a symbol of the
//! wrong arity, or a caller-supplied `img_ax` / `replacement` that — rebuilt at
//! our own terms and compared — is about some other stack. An **assembly
//! failure** is the derivation checking its own work: the three clauses of `R`
//! are built here from a relation built here, and [`crate::cantor::r_dom`],
//! [`crate::cantor::r_sv`] and [`crate::cantor::r_onto`] spell the very same
//! formulas, so a mismatch means one of the two spellings drifted.
//!
//! # What it is for
//!
//! Together with [`super::universe_union_closed`] and
//! [`super::universe_bin_union`] this discharges the antecedent of
//! [`crate::ext::dprod_in_universe_of`], which is `(A ∪ ⋃img(A)) ∈ U(c)` — see
//! [`crate::ext::dprod_in_universe_pair`] for the assembled dependent `Π`
//! typing rule.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::cantor::{image_in_universe, r_dom, r_onto, r_sv};
use crate::err::{DResult, Operand};
use crate::prim;
use crate::rules::{com12, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry};
use crate::{a1i, and_left, and_right, assembly, decline, eq_symm_imp, gen_all};

use super::closure::least_universe_transfer;
use super::least::{in_all_universes, least_universe_mem};
use super::predicate::is_universe;
use super::union::{discharge, hyp_gen};

/// `∀x. (x ∈ A → b(x) ∈ u)` — every fibre of the family `b` over `A` is a
/// member of `u`.
///
/// The typing side condition on the family, and the only hypothesis
/// [`universe_replacement`] adds to `A ∈ u`. It is a condition on `A`, `b` and
/// `u` alone — no quantification over function spaces, and nothing a caller
/// does not already have when it writes down a dependent product.
pub fn fibres_in(env: &mut Env, b: FnSym, a: &Term, u: &Term) -> Formula {
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    Formula::forall(
        xv,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(Term::apply(b, vec![tx]), u.clone()),
        ),
    )
}

/// `⊢ x = t → (y = t → x = y)` — two things equal to a third are equal.
///
/// Shared with [`super::replacement_n`], which runs the same argument at a
/// prefixed fibre and needs `SV` for the same relation.
pub(super) fn eq_both_imp(env: &mut Env, x: &Term, y: &Term, t: &Term) -> DResult<Thm> {
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(t.clone(), y.clone(), w, Formula::eq(x.clone(), Term::var(w)));
    com12(&syl(&eq_symm_imp(env, y.clone(), t.clone()), &leib)?)
}

/// `⊢ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ fibres_in(A,u))) → img(A) ∈ u)` —
/// **every universe is closed under Replacement**.
///
/// [`crate::cantor::image_in_universe`] at `I := A`, `S := img(A)` and
/// `R(x,w) := x ∈ A ∧ w = b(x)`. `img_ax` must be
/// `⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))` for the symbols handed in;
/// it is rebuilt here and compared, so a mismatch is **declined**.
pub fn universe_replacement(
    env: &mut Env,
    empty: &Thm,
    img: FnSym,
    img_ax: &Thm,
    b: FnSym,
) -> DResult<Thm> {
    if img.arity() != 1 || b.arity() != 1 {
        return Err(decline!("the image or the fibre symbol is not unary"))
    }
    let (uv, av, xv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tx, tw) = (Term::var(uv), Term::var(av), Term::var(xv), Term::var(wv));
    let img_a = Term::apply(img, vec![ta.clone()]);
    let bx = Term::apply(b, vec![tx.clone()]);

    // `R(x,w) := x ∈ A ∧ w = b(x)`, and `img`'s characteristic property in
    // exactly that shape.
    let x_in_a = Formula::mem(tx.clone(), ta.clone());
    let r = Formula::and(x_in_a.clone(), Formula::eq(tw.clone(), bx.clone()));
    let img_at = inst_all(img_ax, &[ta.clone(), tw.clone()])?;
    if *img_at.concl()
        != Formula::iff(
            Formula::mem(tw.clone(), img_a.clone()),
            Formula::exists(xv, r.clone()),
        )
    {
        return Err(decline!(
            "the image axiom is not the characteristic property of this image symbol at this fibre symbol"
        ))
    }

    let fib = fibres_in(env, b, &ta, &tu);
    let univ_u = is_universe(env, &tu);
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let rest = Formula::and(a_in_u.clone(), fib.clone());
    let h = Formula::and(univ_u.clone(), rest.clone());
    let h_univ = and_left(univ_u.clone(), rest.clone());
    let h_rest = and_right(univ_u, rest);
    let h_a = syl(&h_rest, &and_left(a_in_u.clone(), fib.clone()))?;
    let h_fib = syl(&h_rest, &and_right(a_in_u, fib.clone()))?;

    // ── `img(A) ⊆ u` ─────────────────────────────────────────────────────────
    let w_in_img = Formula::mem(tw.clone(), img_a.clone());
    let g = Formula::and(h.clone(), w_in_img.clone());
    let g_h = and_left(h.clone(), w_in_img.clone());
    let g_w = and_right(h.clone(), w_in_img);
    let g_ex = syl(&g_w, &iff_mp(&img_at)?)?;

    let g1 = Formula::and(g.clone(), r.clone());
    let g1_g = and_left(g.clone(), r.clone());
    let g1_r = and_right(g.clone(), r.clone());
    let g1_xa = syl(&g1_r, &and_left(x_in_a.clone(), Formula::eq(tw.clone(), bx.clone())))?;
    let g1_eq = syl(&g1_r, &and_right(x_in_a, Formula::eq(tw.clone(), bx.clone())))?;
    let g1_bx = hyp_mp(
        &syl(&syl(&g1_g, &syl(&g_h, &h_fib)?)?, &prim::ax_inst(fib.clone(), tx.clone())?)?,
        &g1_xa,
    )?;
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        bx.clone(),
        tw.clone(),
        hole,
        Formula::mem(Term::var(hole), tu.clone()),
    );
    let g1_sym = syl(&g1_eq, &eq_symm_imp(env, tw.clone(), bx.clone()))?;
    let g1_w_in_u = hyp_mp(&hyp_mp(&a1i(&carry, g1.clone()), &g1_sym)?, &g1_bx)?;
    let g_w_in_u = discharge(xv, &g_ex, &g1_w_in_u)?;
    let h_sub = hyp_gen(wv, &uncurry(&g_w_in_u)?)?;
    debug_assert_eq!(
        *h_sub.concl(),
        Formula::imp(h.clone(), kernel::thm::subset(env, img_a.clone(), tu.clone())),
        "img(A) ⊆ u has the wrong shape"
    );

    // ── The three clauses of `R`, all of which hold outright ─────────────────
    let dom = r_dom(&r, xv, wv, &ta);
    let dom_thm = Thm::gen(
        xv,
        &Thm::gen(wv, &and_left(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), bx.clone()))),
    );
    if *dom_thm.concl() != dom {
        return Err(assembly!(
            "universe_replacement: the DOM clause of the Replacement relation",
            Operand::thm("dom_thm", &dom_thm),
            Operand::formula("dom", &dom),
        ))
    }

    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let sv = r_sv(&r, xv, wv, cv)?;
    let r_c = r.subst(wv, &tc);
    let d = Formula::and(r.clone(), r_c.clone());
    let d_eq1 = syl(
        &and_left(r.clone(), r_c.clone()),
        &and_right(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), bx.clone())),
    )?;
    let d_eq2 = syl(
        &and_right(r.clone(), r_c),
        &and_right(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tc.clone(), bx.clone())),
    )?;
    let both = eq_both_imp(env, &tw, &tc, &bx)?;
    let d_eq = hyp_mp(&hyp_mp(&a1i(&both, d.clone()), &d_eq1)?, &d_eq2)?;
    debug_assert_eq!(
        *d_eq.concl(),
        Formula::imp(d, Formula::eq(tw.clone(), tc)),
        "SV for the Replacement relation did not reach the equation"
    );
    let sv_thm = Thm::gen(xv, &Thm::gen(wv, &Thm::gen(cv, &d_eq)));
    if *sv_thm.concl() != sv {
        return Err(assembly!(
            "universe_replacement: the SV clause of the Replacement relation",
            Operand::thm("sv_thm", &sv_thm),
            Operand::formula("sv", &sv),
        ))
    }

    let onto = r_onto(&r, xv, wv, &img_a);
    let onto_thm = Thm::gen(wv, &iff_mp(&img_at)?);
    if *onto_thm.concl() != onto {
        return Err(assembly!(
            "universe_replacement: the ONTO clause of the Replacement relation",
            Operand::thm("onto_thm", &onto_thm),
            Operand::formula("onto", &onto),
        ))
    }

    // ── Regularity, at `I := A` ──────────────────────────────────────────────
    let iiu = image_in_universe(env, empty, &tu, &ta, &img_a, xv, wv, &r)?;
    let want = Formula::imp(
        Formula::and(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(ta.clone(), tu.clone()),
                    kernel::thm::subset(env, img_a.clone(), tu.clone()),
                ),
            ),
            Formula::and(dom, Formula::and(sv, onto)),
        ),
        Formula::mem(img_a.clone(), tu.clone()),
    );
    if *iiu.concl() != want {
        return Err(assembly!(
            "universe_replacement: image_in_universe did not state regularity at our own terms",
            Operand::thm("iiu", &iiu),
            Operand::formula("want", &want),
        ))
    }
    let out = hyp_mp(
        &a1i(&iiu, h.clone()),
        &hyp_and(
            &hyp_and(&h_univ, &hyp_and(&h_a, &h_sub)?)?,
            &hyp_and(
                &a1i(&dom_thm, h.clone()),
                &hyp_and(&a1i(&sv_thm, h.clone()), &a1i(&onto_thm, h.clone()))?,
            )?,
        )?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(img_a, tu)),
        "universe_replacement: wrong shape"
    );
    Ok(gen_all(&[uv, av], &out))
}

/// `⊢ ∀c ∀A. ((A ∈ U(c) ∧ fibres_in(A,U(c))) → img(A) ∈ U(c))` — **`U(c)` is
/// closed under Replacement**, with no hypothesis at all.
///
/// The transfer through the intersection, with one extra step over
/// [`super::least_universe_pairing`]: the fibre condition itself has to be
/// moved into the ambient universe, which is [`least_universe_transfer`] once
/// per fibre, under the `∀x` that `x` does not escape.
pub fn least_universe_replacement(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    img: FnSym,
    b: FnSym,
    replacement: &Thm,
) -> DResult<Thm> {
    if lu.arity() != 1 || img.arity() != 1 || b.arity() != 1 {
        return Err(decline!("the least-universe, image or fibre symbol is not unary"))
    }
    let (cv, av, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tx) = (Term::var(cv), Term::var(av), Term::var(xv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let img_a = Term::apply(img, vec![ta.clone()]);
    let bx = Term::apply(b, vec![tx.clone()]);

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let fib_w = fibres_in(env, b, &ta, &w);
    let h = Formula::and(a_in_w.clone(), fib_w.clone());
    let h_a = and_left(a_in_w.clone(), fib_w.clone());
    let h_fib = and_right(a_in_w, fib_w.clone());

    // A universe `u` containing `c`, held fixed until the very end.
    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let amb = Formula::and(univ_u.clone(), c_in_u.clone());

    let n = Formula::and(h.clone(), amb.clone());
    let n_h = and_left(h.clone(), amb.clone());
    let n_amb = and_right(h.clone(), amb.clone());
    let n_univ = syl(&n_amb, &and_left(univ_u, c_in_u))?;

    let transfer_a = least_universe_transfer(env, lu_ax, &tc, &ta, &tu)?;
    let n_a = hyp_mp(&hyp_mp(&a1i(&transfer_a, n.clone()), &syl(&n_h, &h_a)?)?, &n_amb)?;

    // Each fibre transfers on its own, under a `∀x` that `u` does not enter.
    let x_in_a = Formula::mem(tx.clone(), ta.clone());
    let k = Formula::and(n.clone(), x_in_a.clone());
    let k_n = and_left(n.clone(), x_in_a.clone());
    let k_x = and_right(n.clone(), x_in_a);
    let k_bx_w = hyp_mp(
        &syl(&syl(&k_n, &syl(&n_h, &h_fib)?)?, &prim::ax_inst(fib_w, tx.clone())?)?,
        &k_x,
    )?;
    let transfer_b = least_universe_transfer(env, lu_ax, &tc, &bx, &tu)?;
    let k_bx_u = hyp_mp(
        &hyp_mp(&a1i(&transfer_b, k.clone()), &k_bx_w)?,
        &syl(&k_n, &n_amb)?,
    )?;
    let n_fib = hyp_gen(xv, &uncurry(&k_bx_u)?)?;
    let fib_u = fibres_in(env, b, &ta, &tu);
    if *n_fib.concl() != Formula::imp(n.clone(), fib_u.clone()) {
        return Err(assembly!(
            "least_universe_replacement: the fibre condition moved into the ambient universe",
            Operand::thm("n_fib", &n_fib),
            Operand::formula("fib_u", &fib_u),
        ))
    }

    let at = inst_all(replacement, &[tu.clone(), ta.clone()])?;
    if *at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(Formula::mem(ta.clone(), tu.clone()), fib_u),
            ),
            Formula::mem(img_a.clone(), tu.clone()),
        )
    {
        return Err(decline!(
            "the replacement premise is not universe closure for this image and fibre symbol"
        ))
    }
    let n_img = hyp_mp(&a1i(&at, n.clone()), &hyp_and(&n_univ, &hyp_and(&n_a, &n_fib)?)?)?;

    let h_phi = prim::mp(
        &prim::ax_dist(uv, h.clone(), Formula::imp(amb, Formula::mem(img_a.clone(), tu)))?,
        &Thm::gen(uv, &uncurry(&n_img)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tc, &img_a)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let out = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tc, &img_a)?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(img_a, w)),
        "least_universe_replacement: wrong shape"
    );
    Ok(gen_all(&[cv, av], &out))
}
