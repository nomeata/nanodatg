//! **Function extensionality for set-functions**: two members of the same
//! function space that agree pointwise are the same set.
//!
//! # Interface
//!
//! With `pointwise(a,f,g) := ∀x. (x ∈ a → app(f,x) = app(g,x))`, which is
//! [`pointwise`], the export is
//!
//! ```text
//! ⊢ ∀a ∀b ∀f ∀g. ((f ∈ fs(a,b) ∧ (g ∈ fs(a,b) ∧ pointwise(a,f,g))) → f = g)
//!                                                              [funspace_ext]
//! ```
//!
//! Callers need none of the derivation below. `app` is
//! [`crate::funcs::Apply`]'s and `fs` is [`crate::funspace::Funspace`]'s; the
//! hypothesis is right-nested, which is the shape [`crate::and_left`] and
//! [`crate::and_right`] take apart.
//!
//! **No inhabitation antecedent, and no condition on `a` or `b`.** At `a := ∅`
//! the pointwise hypothesis is vacuous and the conclusion still holds, because
//! both functions are then subsets of `prod(∅,b)`, which has no members. See
//! "The empty domain" below.
//!
//! # Why this rather than the eta form
//!
//! The statement two consumers asked for is the eta equation
//! `f ∈ fs(A,B) → f = lam(A, λx. app(f,x))`, and that is
//! [`crate::ext::Eta`] — derived from this one, in the neighbouring file. It is
//! *this* lemma that is stated first because it is the one that is symbol-free:
//! the eta form names a particular graph symbol, and neither consumer's lambda
//! **is** that symbol. `checker/src/tg.rs` interprets `λx:A. b` as a graph
//! `lam_C(h⃗,⟦A⟧)` minted per declaration, and the mini port will do the same,
//! so an eta lemma about one fixed graph would have to be bridged by
//! [`crate::ext::lam_ext`] before either could use it. Pointwise agreement is
//! the hypothesis both of them can actually produce — a recursive
//! definitional-equality call yields exactly `⟦b⟧ = app(⟦e⟧,x)` under `x ∈ ⟦A⟧`
//! — so the general form is what gets consumed and the eta form is the
//! corollary. `TgBackend::eta`'s admission text names the same thing: *"eta
//! (needs a function-extensionality lemma)"*.
//!
//! # The shape of the argument
//!
//! Extensionality on the two graphs, one inclusion each way, and the inclusions
//! are the *same* derivation with `f` and `g` exchanged — so it is written once
//! as the private `inclusion` and run twice.
//!
//! The direction that bites is that a member of `f` determines its value:
//!
//! * `z ∈ f` and `f ⊆ prod(a,b)` make `z` a pair `⟨x,y⟩` with `x ∈ a`, `y ∈ b`;
//! * `f`'s **single-valuedness** — which is a clause of `f ∈ fs(a,b)`, not a
//!   separate assumption — turns `⟨x,y⟩ ∈ f` into `app(f,x) = y`, via
//!   [`crate::ext::app_of_pair`];
//! * the hypothesis moves that to `app(g,x) = y`;
//! * `g`'s **totality** supplies some `⟨x,y′⟩ ∈ g`, and single-valuedness of
//!   `g` identifies `y′` as `app(g,x)`, hence as `y`;
//! * so `⟨x,y⟩ ∈ g`, and `z = ⟨x,y⟩`.
//!
//! Every clause of `isfun` is used, and each of them comes out of the
//! membership hypothesis rather than being assumed alongside it. That is the
//! whole reason the statement takes `f ∈ fs(a,b)` for both sides instead of a
//! bare pair of graphs: a graph that is not single-valued has an `app` that
//! says nothing about it, and pointwise agreement of two such graphs is no
//! information at all.
//!
//! # The empty domain
//!
//! At `a := ∅` the pointwise hypothesis is `∀x. (x ∈ ∅ → …)`, which is vacuous,
//! and the conclusion is still `f = g` — correctly, since `f, g ⊆ prod(∅,b)`
//! and nothing is in that product ([`crate::wtype::empty_product`]). The
//! derivation needs no case split for it: the forward direction opens
//! `z ∈ prod(∅,b)` into `∃x. (x ∈ ∅ ∧ …)` and never reaches the pointwise step.
//! [`crate::wtype::empty_funspace`] proves the same thing by the shorter route
//! `f ∈ fs(∅,x) → f = ∅`; this lemma agrees with it and does not use it.
//!
//! Nothing here is trusted. Every theorem handed in is checked — conclusion
//! pinned *and* hypothesis set required to be empty — so a mismatched stack
//! yields `None`, hence a reported gap, rather than a theorem about the wrong
//! symbols.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{Funspace, Product};
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry};
use super::shared::{discharge, hyp_eq_symm, hyp_eq_trans, hyp_leibniz, isfun_parts};

/// `∀x. (x ∈ a → app(f,x) = app(g,x))` — `f` and `g` agree at every point of
/// `a`.
///
/// The hypothesis [`funspace_ext`] consumes. Note it speaks of `app`, not of a
/// body symbol: it is [`crate::ext::values_in`]'s equational sibling, and the
/// counterpart for graphs given by a term — the pointwise premise of
/// [`crate::ext::lam_ext_same_domain`] — meets it only through beta reduction.
pub fn pointwise(env: &mut Env, ap: &Apply, a: &Term, f: &Term, g: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::eq(ap.apply(f.clone(), tx.clone()), ap.apply(g.clone(), tx)),
        ),
    )
}

/// `⊢ ∀a ∀b ∀f ∀g. ((f ∈ fs(a,b) ∧ (g ∈ fs(a,b) ∧ pointwise(a,f,g))) → f = g)`
/// — two functions of the same space that agree pointwise are equal.
///
/// See the module header for the argument. `p` and `fsp` must be the product
/// and function space built over `ap.sets`, and `app_pair` must be what
/// [`crate::ext::app_of_pair`] produces for that `ap`; all of that is checked
/// rather than assumed, and every theorem handed in is additionally required to
/// be hypothesis-free.
pub fn funspace_ext(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    app_pair: &Thm,
) -> Option<Thm> {
    if !app_pair.hyps().is_empty() || !fsp.fs_ax.hyps().is_empty() || !p.prod_ax.hyps().is_empty() {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let (av, bv, fv, gv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tg) = (Term::var(av), Term::var(bv), Term::var(fv), Term::var(gv));

    // The pointwise hypothesis, rebuilt at our own `x` so that it can be opened,
    // and checked against the exported spelling.
    let x = env.fresh_var();
    let tx = Term::var(x);
    let (app_fx, app_gx) = (ap.apply(tf.clone(), tx.clone()), ap.apply(tg.clone(), tx.clone()));
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let pw =
        Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(app_fx.clone(), app_gx.clone())));
    if pw != pointwise(env, ap, &ta, &tf, &tg) {
        return None
    }

    let mem_f = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));
    let mem_g = Formula::mem(tg.clone(), fsp.of(ta.clone(), tb.clone()));
    let rest = Formula::and(mem_g.clone(), pw.clone());
    let h = Formula::and(mem_f.clone(), rest.clone());

    let h_mem_f = and_left(mem_f.clone(), rest.clone());
    let h_rest = and_right(mem_f, rest);
    let h_mem_g = syl(&h_rest, &and_left(mem_g.clone(), pw.clone()))?;
    let h_pw = syl(&h_rest, &and_right(mem_g, pw.clone()))?;

    // ── The three clauses of `isfun`, for each side ──────────────────────────
    let (sub_f, total_f, sv_f) = clauses(env, ap, p, fsp, &ta, &tb, &tf, &h_mem_f)?;
    let (sub_g, total_g, sv_g) = clauses(env, ap, p, fsp, &ta, &tb, &tg, &h_mem_g)?;

    // ── The hypothesis, turned round for the second inclusion ────────────────
    // `app(f,x) = app(g,x)` at a point gives `app(g,x) = app(f,x)` there, and
    // `x` is not free in `H`, so it re-generalises.
    let k = Formula::and(h.clone(), mem_xa.clone());
    let k_h = and_left(h.clone(), mem_xa.clone());
    let k_xa = and_right(h.clone(), mem_xa.clone());
    let k_eq = hyp_mp(&syl(&syl(&k_h, &h_pw)?, &Thm::ax_inst(pw, tx)?)?, &k_xa)?;
    if *k_eq.concl() != Formula::imp(k, Formula::eq(app_fx.clone(), app_gx.clone())) {
        return None
    }
    let h_pw_sym = Thm::mp(
        &Thm::ax_dist(x, h.clone(), Formula::imp(mem_xa, Formula::eq(app_gx, app_fx)))?,
        &Thm::gen(x, &uncurry(&hyp_eq_symm(env, &k_eq)?)?),
    )?;

    // ── One inclusion each way, at a shared `z` ──────────────────────────────
    let z = env.fresh_var();
    let tz = Term::var(z);
    let fwd = inclusion(
        env,
        Inclusion {
            ap,
            p,
            app_pair,
            h: &h,
            a: &ta,
            b: &tb,
            z: &tz,
            src: &tf,
            tgt: &tg,
            sub_src: &sub_f,
            sv_src: &sv_f,
            sv_tgt: &sv_g,
            total_tgt: &total_g,
            pw: &h_pw,
        },
    )?;
    let bwd = inclusion(
        env,
        Inclusion {
            ap,
            p,
            app_pair,
            h: &h,
            a: &ta,
            b: &tb,
            z: &tz,
            src: &tg,
            tgt: &tf,
            sub_src: &sub_g,
            sv_src: &sv_g,
            sv_tgt: &sv_f,
            total_tgt: &total_f,
            pw: &h_pw_sym,
        },
    )?;

    // ── Same members, hence the same set ─────────────────────────────────────
    let mem_zf = Formula::mem(tz.clone(), tf.clone());
    let mem_zg = Formula::mem(tz.clone(), tg.clone());
    let h_iff = hyp_and(&uncurry(&fwd)?, &uncurry(&bwd)?)?;
    let h_all =
        Thm::mp(&Thm::ax_dist(z, h.clone(), Formula::iff(mem_zf, mem_zg))?, &Thm::gen(z, &h_iff))?;
    let out = syl(&h_all, &inst_all(&ext, &[tf.clone(), tg.clone()])?)?;

    // Not a `debug_assert`: this is the statement consumers rely on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, Formula::eq(tf, tg)) {
        return None
    }
    Some(gen_all(&[av, bv, fv, gv], &out))
}

/// The consequent of a `⊢ H → φ`, which is how every clause below is carried.
fn consequent(t: &Thm) -> Option<Formula> { t.concl().as_imp().map(|(_, phi)| phi) }

/// The three clauses of `isfun(f)` as `⊢ H → …`, from `⊢ H → f ∈ fs(a,b)`.
///
/// Returns `(H → f ⊆ prod(a,b), H → total(a,b,f), H → sv(f))`, or `None` if
/// `fsp` is not characterised by [`crate::funspace::is_function`] over this
/// product — in which case the projections would be about the wrong conjuncts.
#[allow(clippy::too_many_arguments)]
fn clauses(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    fsp: &Funspace,
    a: &Term,
    b: &Term,
    f: &Term,
    h_mem: &Thm,
) -> Option<(Thm, Thm, Thm)> {
    let (isfun, sub, total, sv) = isfun_parts(env, ap, p, a, b, f)?;
    let fs_at = inst_all(&fsp.fs_ax, &[a.clone(), b.clone(), f.clone()])?;
    if *fs_at.concl() != Formula::iff(Formula::mem(f.clone(), fsp.of(a.clone(), b.clone())), isfun)
    {
        return None
    }
    let graph = Formula::and(total.clone(), sv.clone());
    let h_isfun = syl(h_mem, &iff_mp(&fs_at)?)?;
    let h_sub = syl(&h_isfun, &and_left(sub.clone(), graph.clone()))?;
    let h_graph = syl(&h_isfun, &and_right(sub, graph))?;
    let h_total = syl(&h_graph, &and_left(total.clone(), sv.clone()))?;
    let h_sv = syl(&h_graph, &and_right(total, sv))?;
    Some((h_sub, h_total, h_sv))
}

/// Everything one run of [`inclusion`] needs; a struct only because the
/// argument list would otherwise be fourteen positional references.
///
/// `sub_src`, `sv_src`, `sv_tgt`, `total_tgt` and `pw` are all of the form
/// `⊢ H → φ` over the same `h`, and the formulas they carry are read off their
/// own conclusions rather than rebuilt.
struct Inclusion<'a> {
    ap: &'a Apply,
    p: &'a Product,
    app_pair: &'a Thm,
    h: &'a Formula,
    a: &'a Term,
    b: &'a Term,
    z: &'a Term,
    src: &'a Term,
    tgt: &'a Term,
    sub_src: &'a Thm,
    sv_src: &'a Thm,
    sv_tgt: &'a Thm,
    total_tgt: &'a Thm,
    pw: &'a Thm,
}

/// `⊢ (H ∧ z ∈ src) → z ∈ tgt` — one half of Extensionality.
///
/// This is the whole of the argument; [`funspace_ext`] runs it twice with the
/// two sides exchanged, at a shared `z` so that the two halves compose into a
/// single biconditional.
fn inclusion(env: &mut Env, i: Inclusion<'_>) -> Option<Thm> {
    let Inclusion { ap, p, app_pair, h, a, b, z, src, tgt, .. } = i;
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));

    let mem_z_src = Formula::mem(z.clone(), src.clone());
    let mem_z_tgt = Formula::mem(z.clone(), tgt.clone());
    let mem_xa = Formula::mem(tx.clone(), a.clone());
    let mem_yb = Formula::mem(ty.clone(), b.clone());
    let pair_xy = ap.sets.pair(tx.clone(), ty.clone());
    let eq_z_pair = Formula::eq(z.clone(), pair_xy.clone());
    let inner = Formula::exists(y, Formula::and(mem_yb.clone(), eq_z_pair.clone()));
    let outer = Formula::and(mem_xa.clone(), inner.clone());

    let prod_at = inst_all(&p.prod_ax, &[a.clone(), b.clone(), z.clone()])?;
    if *prod_at.concl()
        != Formula::iff(
            Formula::mem(z.clone(), p.of(a.clone(), b.clone())),
            Formula::exists(x, outer.clone()),
        )
    {
        return None
    }

    // ── M: the hypothesis, plus a member of the source ───────────────────────
    let m = Formula::and(h.clone(), mem_z_src.clone());
    let m_h = and_left(h.clone(), mem_z_src.clone());
    let m_zsrc = and_right(h.clone(), mem_z_src.clone());
    let m_zprod = hyp_mp(
        &syl(&syl(&m_h, i.sub_src)?, &Thm::ax_inst(consequent(i.sub_src)?, z.clone())?)?,
        &m_zsrc,
    )?;
    let m_ex = syl(&m_zprod, &iff_mp(&prod_at)?)?;

    // ── N, P: the member really is a pair ⟨x,y⟩ with x ∈ a and y ∈ b ─────────
    let n = Formula::and(m.clone(), outer.clone());
    let n_m = and_left(m.clone(), outer.clone());
    let n_outer = and_right(m, outer);
    let n_xa = syl(&n_outer, &and_left(mem_xa.clone(), inner.clone()))?;
    let n_inner = syl(&n_outer, &and_right(mem_xa, inner))?;

    let body = Formula::and(mem_yb.clone(), eq_z_pair.clone());
    let pf = Formula::and(n.clone(), body.clone());
    let p_n = and_left(n.clone(), body.clone());
    let p_body = and_right(n, body);
    let p_zeq = syl(&p_body, &and_right(mem_yb, eq_z_pair))?;
    let p_h = syl(&p_n, &syl(&n_m, &m_h)?)?;
    let p_zsrc = syl(&p_n, &syl(&n_m, &m_zsrc)?)?;
    let p_xa = syl(&p_n, &n_xa)?;

    let w1 = env.fresh_var();
    let p_pair_src =
        hyp_mp(&hyp_leibniz(&p_zeq, w1, &Formula::mem(Term::var(w1), src.clone()))?, &p_zsrc)?;

    // ── app(src,x) = y, then app(tgt,x) = y ──────────────────────────────────
    let app_src_x = ap.apply(src.clone(), tx.clone());
    let app_tgt_x = ap.apply(tgt.clone(), tx.clone());
    let ap_src = inst_all(app_pair, &[src.clone(), tx.clone(), ty.clone()])?;
    if *ap_src.concl()
        != Formula::imp(
            Formula::and(consequent(i.sv_src)?, Formula::mem(pair_xy, src.clone())),
            Formula::eq(app_src_x.clone(), ty.clone()),
        )
    {
        return None
    }
    let p_src_eq_y =
        hyp_mp(&a1i(&ap_src, pf.clone()), &hyp_and(&syl(&p_h, i.sv_src)?, &p_pair_src)?)?;

    let p_pw_at =
        hyp_mp(&syl(&syl(&p_h, i.pw)?, &Thm::ax_inst(consequent(i.pw)?, tx.clone())?)?, &p_xa)?;
    if *p_pw_at.concl() != Formula::imp(pf.clone(), Formula::eq(app_src_x, app_tgt_x.clone())) {
        return None
    }
    let p_pw_sym = hyp_eq_symm(env, &p_pw_at)?;
    let p_tgt_eq_y = hyp_eq_trans(env, &p_pw_sym, &p_src_eq_y)?;

    // ── Totality of the target supplies a pair, which must be that one ───────
    let mem_y2b = Formula::mem(ty2.clone(), b.clone());
    let pair_xy2 = ap.sets.pair(tx.clone(), ty2.clone());
    let mem_pair2 = Formula::mem(pair_xy2.clone(), tgt.clone());
    let body2 = Formula::and(mem_y2b.clone(), mem_pair2.clone());
    let p_ex2 = hyp_mp(
        &syl(&syl(&p_h, i.total_tgt)?, &Thm::ax_inst(consequent(i.total_tgt)?, tx.clone())?)?,
        &p_xa,
    )?;
    if *p_ex2.concl() != Formula::imp(pf.clone(), Formula::exists(y2, body2.clone())) {
        return None
    }

    let q = Formula::and(pf.clone(), body2.clone());
    let q_p = and_left(pf.clone(), body2.clone());
    let q_body = and_right(pf, body2);
    let q_pair2 = syl(&q_body, &and_right(mem_y2b, mem_pair2))?;
    let ap_tgt = inst_all(app_pair, &[tgt.clone(), tx.clone(), ty2.clone()])?;
    if *ap_tgt.concl()
        != Formula::imp(
            Formula::and(consequent(i.sv_tgt)?, Formula::mem(pair_xy2, tgt.clone())),
            Formula::eq(app_tgt_x, ty2.clone()),
        )
    {
        return None
    }
    let q_sv_tgt = syl(&q_p, &syl(&p_h, i.sv_tgt)?)?;
    let q_tgt_eq_y2 = hyp_mp(&a1i(&ap_tgt, q), &hyp_and(&q_sv_tgt, &q_pair2)?)?;

    // `y′ = app(tgt,x) = y`, so the pair totality supplied is `⟨x,y⟩` itself.
    let q_y2_eq_tgt = hyp_eq_symm(env, &q_tgt_eq_y2)?;
    let q_y2_eq_y = hyp_eq_trans(env, &q_y2_eq_tgt, &syl(&q_p, &p_tgt_eq_y)?)?;
    let w2 = env.fresh_var();
    let q_pair_tgt = hyp_mp(
        &hyp_leibniz(
            &q_y2_eq_y,
            w2,
            &Formula::mem(ap.sets.pair(tx.clone(), Term::var(w2)), tgt.clone()),
        )?,
        &q_pair2,
    )?;
    let w3 = env.fresh_var();
    let q_zeq = hyp_eq_symm(env, &syl(&q_p, &p_zeq)?)?;
    let q_goal = hyp_mp(
        &hyp_leibniz(&q_zeq, w3, &Formula::mem(Term::var(w3), tgt.clone()))?,
        &q_pair_tgt,
    )?;

    // ── The three witnesses, discharged outwards ─────────────────────────────
    let p_goal = discharge(y2, &p_ex2, &q_goal)?;
    let n_goal = discharge(y, &n_inner, &p_goal)?;
    let out = discharge(x, &m_ex, &n_goal)?;
    if *out.concl() != Formula::imp(Formula::and(h.clone(), mem_z_src), mem_z_tgt) {
        return None
    }
    Some(out)
}
