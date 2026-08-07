//! Closure under **Replacement**, for a fibre family carrying a **parameter
//! prefix**: the image `{ b(q⃗,x) : x ∈ A }` of a member.
//!
//! # Interface
//!
//! For a fibre symbol `b` of arity `k+1` and the Replacement image
//! `img(q⃗,A) = { b(q⃗,x) : x ∈ A }` of arity `k+1` — what
//! `checker`'s `image_symbol_n` builds, and what
//! [`crate::ext::image_symbol`] builds at `k = 0` — writing
//!
//! ```text
//! fibres_in_n(q⃗,A,u) := ∀x. (x ∈ A → b(q⃗,x) ∈ u)          [fibres_in_n]
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ ∀q⃗ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ fibres_in_n(q⃗,A,u))) → img(q⃗,A) ∈ u)
//!                                                      [universe_replacement_n]
//! ⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres_in_n(q⃗,A,U(c))) → img(q⃗,A) ∈ U(c))
//!                                                 [least_universe_replacement_n]
//! ```
//!
//! The second carries no hypothesis about `U(c)`. Callers need none of the
//! derivation.
//!
//! # Why a prefixed copy exists at all
//!
//! [`super::replacement`] states exactly these two theorems for a **unary** `b`,
//! and the argument below is that argument with `b(x)` replaced by `b(q⃗,x)`
//! throughout — nothing else changes, because neither
//! [`crate::cantor::image_in_universe`] nor the transfer through the
//! intersection ever takes the fibre term apart. What forces the copy is that
//! `b` is a *symbol* of a fixed arity, not a term: a `Π` whose fibre skeleton
//! mentions ambient parameters has `b: k+1`, and there is no way to specialise
//! an arity-`k+1` symbol to an arity-`1` one inside the object language. So the
//! prefix is threaded through the argument lists and universally quantified at
//! the end, exactly as `checker`'s `image_symbol_n`, `dprod_symbol_n`,
//! `lam_in_dprod_n` and `dprod_const_fibre_n` thread theirs.
//!
//! **At `k = 0` this coincides with [`super::replacement`] on the nose** — same
//! statement, same proof — and the test
//! `the_nullary_prefix_reproduces_the_unary_replacement_rule` pins that, so the
//! two cannot drift.
//!
//! # How this fails
//!
//! As in [`super::replacement`], and along the same boundary. A **decline** is
//! the contract working: a fibre symbol with no argument to take an image over,
//! an image symbol whose arity does not match the prefix, or a caller-supplied
//! `img_ax` / `replacement` that — rebuilt at our own terms and compared — is
//! about some other stack. An **assembly failure** is the derivation checking
//! its own work: the three clauses of `R`, the transferred fibre condition, and
//! the two final statements, all of which are built here from terms built here.
//! Those last two are checked unconditionally rather than by `debug_assert`,
//! because they are what the caller relies on and a release build must not skip
//! them.
//!
//! # What it is for
//!
//! [`crate::ext::dprod_universe_n`]'s n-ary `Π` typing rule, whose antecedent
//! `(A ∪ ⋃img(q⃗,A)) ∈ U(c)` this discharges together with
//! [`super::universe_union_closed`] and [`super::universe_bin_union`]. That rule
//! is the one `checker`'s `Pi` clause declines for today; see the header there.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::cantor::{image_in_universe, r_dom, r_onto, r_sv};
use crate::err::{imported, DResult, Operand};
use crate::prim;
use crate::rules::{hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry};
use crate::{a1i, and_left, and_right, assembly, decline, eq_symm_imp, gen_all};

use super::closure::least_universe_transfer;
use super::least::{in_all_universes, least_universe_mem};
use super::predicate::is_universe;
use super::replacement::eq_both_imp;
use super::union::{discharge, hyp_gen};

/// `f(q⃗, arg)` — a symbol applied to the parameter prefix and one argument.
fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(arg);
    Term::apply(f, v)
}

/// The instantiation list `q⃗, a, b`.
fn inst_at(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
    let mut v = prefix.to_vec();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// `∀x. (x ∈ A → b(q⃗,x) ∈ u)` — every fibre of the family `b` at the parameters
/// `q⃗`, taken over `A`, is a member of `u`.
///
/// The prefixed [`super::fibres_in`], with which it agrees at an empty prefix
/// (bound variables are de Bruijn, so the two formulas are equal, not merely
/// alpha-equivalent). This is the typing side condition the `Π` rule adds to
/// `A ∈ u`, and it is a condition on `A`, `b`, `q⃗` and `u` alone.
pub fn fibres_in_n(env: &mut Env, b: FnSym, prefix: &[Term], a: &Term, u: &Term) -> Formula {
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    Formula::forall(
        xv,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(at(b, prefix, tx), u.clone()),
        ),
    )
}

/// `⊢ ∀q⃗ ∀u ∀A. ((is_universe(u) ∧ (A ∈ u ∧ fibres_in_n(q⃗,A,u))) → img(q⃗,A) ∈ u)`
/// — **every universe is closed under Replacement**, at a prefixed fibre.
///
/// [`crate::cantor::image_in_universe`] at `I := A`, `S := img(q⃗,A)` and
/// `R(x,w) := x ∈ A ∧ w = b(q⃗,x)`, whose three clauses cost nothing: `DOM` is a
/// projection, `SV` is transitivity of equality, and `ONTO` is the forward half
/// of `img`'s own characteristic property. No `⋃`, no power set, no pairing, and
/// `C₁` is not used at all.
///
/// `img_ax` must be `⊢ ∀q⃗ ∀A ∀w. (w ∈ img(q⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(q⃗,x)))` for
/// the symbols handed in — what `checker`'s `image_symbol_n` produces. It is
/// rebuilt here at our own terms and compared, so a foreign stack is **declined**
/// rather than turned into a theorem about something else.
pub fn universe_replacement_n(
    env: &mut Env,
    empty: &Thm,
    img: FnSym,
    img_ax: &Thm,
    b: FnSym,
) -> DResult<Thm> {
    let k = match (b.arity() as usize).checked_sub(1) {
        Some(k) => k,
        None =>
            return Err(decline!(
                "the fibre symbol is nullary, so it has no argument to take the image over"
            )),
    };
    if img.arity() as usize != k + 1 {
        return Err(decline!("the image symbol's arity does not match the fibre symbol's"))
    }
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();

    let (uv, av, xv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tx, tw) = (Term::var(uv), Term::var(av), Term::var(xv), Term::var(wv));
    let img_a = at(img, &qts, ta.clone());
    let bx = at(b, &qts, tx.clone());

    // `R(x,w) := x ∈ A ∧ w = b(q⃗,x)`, and `img`'s characteristic property in
    // exactly that shape.
    let x_in_a = Formula::mem(tx.clone(), ta.clone());
    let r = Formula::and(x_in_a.clone(), Formula::eq(tw.clone(), bx.clone()));
    let img_at = inst_all(img_ax, &inst_at(&qts, &ta, &tw))?;
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

    let fib = fibres_in_n(env, b, &qts, &ta, &tu);
    let univ_u = is_universe(env, &tu);
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let rest = Formula::and(a_in_u.clone(), fib.clone());
    let h = Formula::and(univ_u.clone(), rest.clone());
    let h_univ = and_left(univ_u.clone(), rest.clone());
    let h_rest = and_right(univ_u, rest);
    let h_a = syl(&h_rest, &and_left(a_in_u.clone(), fib.clone()))?;
    let h_fib = syl(&h_rest, &and_right(a_in_u, fib.clone()))?;

    // ── `img(q⃗,A) ⊆ u` ───────────────────────────────────────────────────────
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
        "img(q⃗,A) ⊆ u has the wrong shape"
    );

    // ── The three clauses of `R`, all of which hold outright ─────────────────
    let dom = r_dom(&r, xv, wv, &ta);
    let dom_thm = Thm::gen(
        xv,
        &Thm::gen(
            wv,
            &and_left(Formula::mem(tx.clone(), ta.clone()), Formula::eq(tw.clone(), bx.clone())),
        ),
    );
    if *dom_thm.concl() != dom {
        return Err(assembly!(
            "universe_replacement_n: the DOM clause of the Replacement relation",
            Operand::thm("dom_thm", &dom_thm),
            Operand::formula("dom", &dom),
        ))
    }

    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let sv = imported("crate::cantor::r_sv", r_sv(&r, xv, wv, cv))?;
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
            "universe_replacement_n: the SV clause of the Replacement relation",
            Operand::thm("sv_thm", &sv_thm),
            Operand::formula("sv", &sv),
        ))
    }

    let onto = r_onto(&r, xv, wv, &img_a);
    let onto_thm = Thm::gen(wv, &iff_mp(&img_at)?);
    if *onto_thm.concl() != onto {
        return Err(assembly!(
            "universe_replacement_n: the ONTO clause of the Replacement relation",
            Operand::thm("onto_thm", &onto_thm),
            Operand::formula("onto", &onto),
        ))
    }

    // ── Regularity, at `I := A` ──────────────────────────────────────────────
    let iiu = imported(
        "crate::cantor::image_in_universe",
        image_in_universe(env, empty, &tu, &ta, &img_a, xv, wv, &r),
    )?;
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
            "universe_replacement_n: image_in_universe did not state regularity at our own terms",
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
    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    let want_out = Formula::imp(h, Formula::mem(img_a, tu));
    if *out.concl() != want_out {
        return Err(assembly!(
            "universe_replacement_n: the assembled closure statement",
            Operand::thm("out", &out),
            Operand::formula("want_out", &want_out),
        ))
    }
    let mut all = qs;
    all.push(uv);
    all.push(av);
    Ok(gen_all(&all, &out))
}

/// `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres_in_n(q⃗,A,U(c))) → img(q⃗,A) ∈ U(c))` —
/// **`U(c)` is closed under Replacement**, with no hypothesis at all.
///
/// The transfer through the intersection, with one extra step over
/// [`super::least_universe_pairing`]: the fibre condition itself has to be moved
/// into the ambient universe, which is [`least_universe_transfer`] once per
/// fibre, under the `∀x` that `x` does not escape. The prefix rides along in the
/// argument lists and is generalised at the end; it never enters the argument.
///
/// `replacement` must be what [`universe_replacement_n`] produced for the same
/// `img` and `b`; it is rebuilt and compared.
pub fn least_universe_replacement_n(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    img: FnSym,
    b: FnSym,
    replacement: &Thm,
) -> DResult<Thm> {
    let k = match (b.arity() as usize).checked_sub(1) {
        Some(k) => k,
        None =>
            return Err(decline!(
                "the fibre symbol is nullary, so it has no argument to take the image over"
            )),
    };
    if lu.arity() != 1 || img.arity() as usize != k + 1 {
        return Err(decline!(
            "the least-universe symbol is not unary, or the image symbol's arity does not match the fibre symbol's"
        ))
    }
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();

    let (cv, av, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tx) = (Term::var(cv), Term::var(av), Term::var(xv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let img_a = at(img, &qts, ta.clone());
    let bx = at(b, &qts, tx.clone());

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let fib_w = fibres_in_n(env, b, &qts, &ta, &w);
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
    let kf = Formula::and(n.clone(), x_in_a.clone());
    let k_n = and_left(n.clone(), x_in_a.clone());
    let k_x = and_right(n.clone(), x_in_a);
    let k_bx_w = hyp_mp(
        &syl(&syl(&k_n, &syl(&n_h, &h_fib)?)?, &prim::ax_inst(fib_w, tx.clone())?)?,
        &k_x,
    )?;
    let transfer_b = least_universe_transfer(env, lu_ax, &tc, &bx, &tu)?;
    let k_bx_u = hyp_mp(
        &hyp_mp(&a1i(&transfer_b, kf.clone()), &k_bx_w)?,
        &syl(&k_n, &n_amb)?,
    )?;
    let n_fib = hyp_gen(xv, &uncurry(&k_bx_u)?)?;
    let fib_u = fibres_in_n(env, b, &qts, &ta, &tu);
    if *n_fib.concl() != Formula::imp(n.clone(), fib_u.clone()) {
        return Err(assembly!(
            "least_universe_replacement_n: the fibre condition moved into the ambient universe",
            Operand::thm("n_fib", &n_fib),
            Operand::formula("fib_u", &fib_u),
        ))
    }

    let at_thm = inst_all(replacement, &inst_at(&qts, &tu, &ta))?;
    if *at_thm.concl()
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
    let n_img = hyp_mp(&a1i(&at_thm, n.clone()), &hyp_and(&n_univ, &hyp_and(&n_a, &n_fib)?)?)?;

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
    // Not a `debug_assert`: this is the statement the caller relies on.
    let want_out = Formula::imp(h, Formula::mem(img_a, w));
    if *out.concl() != want_out {
        return Err(assembly!(
            "least_universe_replacement_n: the assembled closure statement",
            Operand::thm("out", &out),
            Operand::formula("want_out", &want_out),
        ))
    }
    let mut all = qs;
    all.push(cv);
    all.push(av);
    Ok(gen_all(&all, &out))
}
