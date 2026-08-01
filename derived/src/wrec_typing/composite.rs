//! The composite is a function into `T`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀f ∀d ∀x ∀y. (⟨x,y⟩ ∈ comp(g,f,d) → y = app(g, app(f,x)))
//!                                                          [composite_value]
//! ⊢ ∀g ∀f ∀d. sv(comp(g,f,d))                      [composite_single_valued]
//! ⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d), b) = app(g, app(f,b)))
//!                                                            [composite_app]
//! ⊢ ∀g ∀f ∀d ∀T. ((∀b. (b ∈ d → app(g, app(f,b)) ∈ T)) → comp(g,f,d) ∈ fs(d,T))
//!                                                          [composite_typed]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Everything here is unconditional in `g` and `f`
//!
//! Neither needs `f` to be a function, nor `g`, nor `d` to be `f`'s domain.
//! `comp` is a Replacement image along `b ↦ ⟨b, app(g,app(f,b))⟩`
//! ([`crate::wrec::compose`]), so it is a function on `d` **whatever it
//! composes** — single-valuedness is injectivity of the Kuratowski pair and
//! nothing else. Only the *codomain* needs a hypothesis, and
//! [`composite_typed`]'s is the weakest one that names `T`.
//!
//! [`composite_app`] is the one an inductive with a **non-empty fibre** needs.
//! `Bool.rec` never asked for it: every fibre of an enumeration is `∅`, so
//! [`crate::wrec_unit::comp_empty_domain`] collapses the composite and the ι
//! rule's right-hand side loses its recursive call. `N.rec` cannot avoid it —
//! the `succ` fibre is `1`, the subterm family is the one-point graph
//! `{⟨•,n⟩}`, and the recursive call *is* `app(comp(wrec,{⟨•,n⟩},1), •)`.
//!
//! # Non-vacuity
//!
//! [`composite_typed`]'s hypothesis is not one no set satisfies: `tests/wrec.rs`
//! discharges it at `d := ∅`, where it is vacuous, and reads off
//! `⊢ comp(g,f,∅) ∈ fs(∅,T)` for arbitrary `g`, `f` and `T`.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::funspace::{is_function, is_single_valued, is_total};
use crate::sums::Sums;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim};
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    imp_refl, inst_all, syl, uncurry,
};

/// `⊢ ∀g ∀f ∀d ∀x ∀y. (⟨x,y⟩ ∈ comp(g,f,d) → y = app(g, app(f,x)))` — **the
/// composite has exactly the values its Replacement puts there**.
///
/// A pair of `comp(g,f,d)` comes from some `b ∈ d` with `⟨x,y⟩ = ⟨b, g(f b)⟩`;
/// [`crate::pairs::opair_inj`] splits that into `x = b` and `y = g(f b)`, and
/// congruence carries the first into the second. Single-valuedness of the
/// composite is this lemma twice over.
pub fn composite_value(env: &mut Env, ap: &Apply, comp: FnSym, comp_ax: &Thm) -> Option<Thm> {
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let (tg, tf, td, tx, ty) = (
        Term::var(vars[0]),
        Term::var(vars[1]),
        Term::var(vars[2]),
        Term::var(vars[3]),
        Term::var(vars[4]),
    );
    let out = composite_value_at(env, ap, comp, comp_ax, &tg, &tf, &td, &tx, &ty)?;
    Some(gen_all(&vars, &out))
}

/// [`composite_value`] at the caller's terms, which is how the two uses below
/// need it: `⊢ ⟨x,y⟩ ∈ comp(g,f,d) → y = app(g, app(f,x))`.
#[allow(clippy::too_many_arguments)]
fn composite_value_at(
    env: &mut Env,
    ap: &Apply,
    comp: FnSym,
    comp_ax: &Thm,
    g: &Term,
    f: &Term,
    d: &Term,
    x: &Term,
    y: &Term,
) -> Option<Thm> {
    let c_t = comp_of(comp, g.clone(), f.clone(), d.clone());
    let pxy = ap.sets.pair(x.clone(), y.clone());
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let val_b = ap.apply(g.clone(), ap.apply(f.clone(), tb.clone()));
    let val_x = ap.apply(g.clone(), ap.apply(f.clone(), x.clone()));

    let mem_bd = Formula::mem(tb.clone(), d.clone());
    let eq_pair = Formula::eq(pxy.clone(), ap.sets.pair(tb.clone(), val_b.clone()));
    let body = Formula::and(mem_bd.clone(), eq_pair.clone());
    let head = Formula::mem(pxy.clone(), c_t.clone());

    let ax = inst_all(comp_ax, &[g.clone(), f.clone(), d.clone(), pxy])?;
    if *ax.concl() != Formula::iff(head.clone(), Formula::exists(bv, body.clone())) {
        return None
    }

    // Under `N := ⟨x,y⟩ ∈ comp(g,f,d) ∧ (b ∈ d ∧ ⟨x,y⟩ = ⟨b, g(f b)⟩)`.
    let n_body = and_right(head.clone(), body.clone());
    let n_eq = syl(&n_body, &and_right(mem_bd, eq_pair))?;
    let n_conj = syl(
        &n_eq,
        &inst_all(&ap.pair_inj, &[x.clone(), y.clone(), tb.clone(), val_b.clone()])?,
    )?;
    let eq_xb = Formula::eq(x.clone(), tb.clone());
    let eq_yv = Formula::eq(y.clone(), val_b);
    let n_xb = syl(&n_conj, &and_left(eq_xb.clone(), eq_yv.clone()))?;
    let n_yv = syl(&n_conj, &and_right(eq_xb, eq_yv))?;

    let n_val = hyp_congr(env, &n_xb, |t| ap.apply(g.clone(), ap.apply(f.clone(), t)))?;
    let n_val_symm = hyp_eq_symm(env, &n_val)?;
    let n_out = hyp_eq_trans(env, &n_yv, &n_val_symm)?;

    let out = hyp_exists_elim(bv, &n_out, &iff_mp(&ax)?)?;
    if *out.concl() != Formula::imp(head, Formula::eq(y.clone(), val_x)) {
        return None
    }
    Some(out)
}

/// `⊢ ∀g ∀f ∀d. sv(comp(g,f,d))` — **the composite is single-valued**,
/// whatever it composes.
///
/// [`composite_value`] twice: both values at `x` are forced to be
/// `app(g, app(f,x))`, so they are equal to each other. No hypothesis at all —
/// `comp` is a Replacement image along `b ↦ ⟨b, g(f b)⟩`, and the Kuratowski
/// pair's injectivity is the whole argument.
pub fn composite_single_valued(
    env: &mut Env,
    ap: &Apply,
    comp: FnSym,
    comp_ax: &Thm,
) -> Option<Thm> {
    let (gv, fv, dv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tf, td) = (Term::var(gv), Term::var(fv), Term::var(dv));
    let c_t = comp_of(comp, tg.clone(), tf.clone(), td.clone());

    // The formula this has to come out as, with the very variables
    // `is_single_valued` picks — so the shape is matched, not hoped for.
    let want = is_single_valued(env, &ap.sets, &c_t);
    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));

    let m1 = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), c_t.clone());
    let m2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), c_t.clone());

    let v1 = composite_value_at(env, ap, comp, comp_ax, &tg, &tf, &td, &tx, &ty)?;
    let v2 = composite_value_at(env, ap, comp, comp_ax, &tg, &tf, &td, &tx, &ty2)?;
    let h1 = syl(&and_left(m1.clone(), m2.clone()), &v1)?;
    let h2 = syl(&and_right(m1, m2), &v2)?;
    let h2s = hyp_eq_symm(env, &h2)?;
    let out = hyp_eq_trans(env, &h1, &h2s)?;

    let sv = gen_all(&[xv, yv, y2v], &out);
    if *sv.concl() != want {
        return None
    }
    Some(gen_all(&[gv, fv, dv], &sv))
}

/// **The composite computes**:
///
/// ```text
/// ⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d), b) = app(g, app(f,b)))
/// ```
///
/// The counterpart of [`crate::wrec_unit::comp_empty_domain`] for a fibre that
/// is **not** empty. `Bool.rec` never needed it: every fibre of an enumeration
/// is `∅`, so the composite collapses to `∅` and the ι rule's right-hand side
/// loses its recursive call altogether. `N.rec` cannot avoid it — the `succ`
/// fibre is `1`, the composite is the one-point graph `{⟨•, app(wrec,n)⟩}`, and
/// the recursive call is exactly `app(comp, •)`.
///
/// Unconditional in `g`, `f` and `d` apart from `b ∈ d`, which is genuine:
/// off `d` the composite relates nothing and `app` returns `∅`.
///
/// Two ingredients and no induction: the pair `⟨b, g(f b)⟩` is a member of the
/// composite whenever `b ∈ d` (read straight off [`crate::wrec::compose`]'s
/// membership condition, with `b` as its own witness), and
/// [`composite_single_valued`] lets [`crate::ext::app_of_pair`] read the value
/// back off that pair.
pub fn composite_app(env: &mut Env, ap: &Apply, comp: FnSym, comp_ax: &Thm) -> Option<Thm> {
    let (gv, fv, dv, bv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tf, td, tb) = (Term::var(gv), Term::var(fv), Term::var(dv), Term::var(bv));
    let c_t = comp_of(comp, tg.clone(), tf.clone(), td.clone());
    let val = |t: &Term| ap.apply(tg.clone(), ap.apply(tf.clone(), t.clone()));
    let pair_b = ap.sets.pair(tb.clone(), val(&tb));
    let mem_bd = Formula::mem(tb.clone(), td.clone());

    // ── `b ∈ d → ⟨b, g(f b)⟩ ∈ comp(g,f,d)`, with `b` its own witness ───────
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    let body = Formula::and(
        Formula::mem(tw.clone(), td.clone()),
        Formula::eq(pair_b.clone(), ap.sets.pair(tw.clone(), val(&tw))),
    );
    let ax = inst_all(comp_ax, &[tg.clone(), tf.clone(), td.clone(), pair_b.clone()])?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(pair_b.clone(), c_t.clone()),
            Formula::exists(wv, body.clone()),
        )
    {
        return None
    }
    let at_b = hyp_and(
        &imp_refl(mem_bd.clone()),
        &a1i(&Thm::eq_refl(pair_b.clone()), mem_bd.clone()),
    )?;
    let h_ex = syl(&at_b, &exists_intro_imp(wv, body, tb.clone())?)?;
    let h_mem = syl(&h_ex, &iff_mpr(&ax)?)?;

    // ── …and its value is what the pair says it is ──────────────────────────
    let sv = inst_all(
        &composite_single_valued(env, ap, comp, comp_ax)?,
        &[tg.clone(), tf.clone(), td.clone()],
    )?;
    let aop = inst_all(
        &crate::ext::app_of_pair(env, ap)?,
        &[c_t.clone(), tb.clone(), val(&tb)],
    )?;
    let out = hyp_mp(
        &a1i(&aop, mem_bd.clone()),
        &hyp_and(&a1i(&sv, mem_bd.clone()), &h_mem)?,
    )?;
    if *out.concl()
        != Formula::imp(mem_bd, Formula::eq(ap.apply(c_t, tb.clone()), val(&tb)))
    {
        return None
    }
    Some(gen_all(&[gv, fv, dv, bv], &out))
}

/// **The composite is a function into any set its values land in.**
///
/// ```text
/// ⊢ ∀g ∀f ∀d ∀T. ((∀b. (b ∈ d → app(g, app(f,b)) ∈ T)) → comp(g,f,d) ∈ fs(d,T))
/// ```
///
/// The three clauses of [`crate::funspace::is_function`] over
/// [`crate::wrec::compose`]'s membership condition:
///
/// * **inclusion in `prod(d,T)`** — a member of the composite is `⟨b, g(f b)⟩`
///   with `b ∈ d`, and the hypothesis puts `g(f b)` in `T`;
/// * **totality on `d`** — the same condition read backwards, at the witness
///   `b := x`, needs no hypothesis beyond `x ∈ d`;
/// * **single-valuedness** — [`composite_value`], twice.
///
/// Only the first clause uses the hypothesis. That is why the statement is
/// phrased with the *values* typed rather than with `f ∈ fs(d,X)` and
/// `g ∈ fs(X,T)`: the recursor's use has `g := wrec`, which is not yet known
/// to be a function space member — that is the very thing step 4 is trying to
/// prove — but whose values at the relevant points are already in `T`, because
/// `wrec ⊆ prod(W,T)`.
pub fn composite_typed(env: &mut Env, s: &Sums, comp: FnSym, comp_ax: &Thm) -> Option<Thm> {
    let ap = &s.ap;
    let (gv, fv, dv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tf, td, tt) = (Term::var(gv), Term::var(fv), Term::var(dv), Term::var(tv));
    let c_t = comp_of(comp, tg.clone(), tf.clone(), td.clone());
    let prod_t = s.prod.of(td.clone(), tt.clone());
    let val = |t: &Term| ap.apply(tg.clone(), ap.apply(tf.clone(), t.clone()));

    // `H := ∀b. (b ∈ d → app(g, app(f,b)) ∈ T)`.
    let hb = env.fresh_var();
    let thb = Term::var(hb);
    let hyp = Formula::forall(
        hb,
        Formula::imp(
            Formula::mem(thb.clone(), td.clone()),
            Formula::mem(val(&thb), tt.clone()),
        ),
    );

    // ── Clause 1: `comp(g,f,d) ⊆ prod(d,T)` ─────────────────────────────────
    let (pv, bv) = (env.fresh_var(), env.fresh_var());
    let (tp, tb) = (Term::var(pv), Term::var(bv));
    let pair_b = ap.sets.pair(tb.clone(), val(&tb));
    let mem_bd = Formula::mem(tb.clone(), td.clone());
    let eq_pb = Formula::eq(tp.clone(), pair_b.clone());
    let body = Formula::and(mem_bd.clone(), eq_pb.clone());
    let mem_pc = Formula::mem(tp.clone(), c_t.clone());

    let ax_p = inst_all(comp_ax, &[tg.clone(), tf.clone(), td.clone(), tp.clone()])?;
    if *ax_p.concl() != Formula::iff(mem_pc.clone(), Formula::exists(bv, body.clone())) {
        return None
    }

    let k = Formula::and(hyp.clone(), mem_pc.clone());
    let k_h = and_left(hyp.clone(), mem_pc.clone());
    let k_ex = syl(&and_right(hyp.clone(), mem_pc.clone()), &iff_mp(&ax_p)?)?;

    let m = Formula::and(k.clone(), body.clone());
    let m_body = and_right(k.clone(), body.clone());
    let m_bd = syl(&m_body, &and_left(mem_bd.clone(), eq_pb.clone()))?;
    let m_peq = syl(&m_body, &and_right(mem_bd, eq_pb))?;
    let m_h = syl(&and_left(k.clone(), body.clone()), &k_h)?;

    let m_val = hyp_mp(&syl(&m_h, &Thm::ax_inst(hyp.clone(), tb.clone())?)?, &m_bd)?;
    let pip = inst_all(&s.pair_in_prod, &[td.clone(), tt.clone(), tb.clone(), val(&tb)])?;
    let m_pair = hyp_mp(&a1i(&iff_mpr(&pip)?, m.clone()), &hyp_and(&m_bd, &m_val)?)?;

    let m_symm = hyp_eq_symm(env, &m_peq)?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        pair_b,
        tp.clone(),
        hole,
        Formula::mem(Term::var(hole), prod_t.clone()),
    );
    let m_in = hyp_mp(&hyp_mp(&a1i(&leib, m), &m_symm)?, &m_pair)?;
    let k_in = hyp_exists_elim(bv, &m_in, &k_ex)?;

    let incl = uncurry(&k_in)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(
            pv,
            hyp.clone(),
            Formula::imp(mem_pc, Formula::mem(tp, prod_t.clone())),
        )?,
        &Thm::gen(pv, &incl),
    )?;
    debug_assert_eq!(
        *h_sub.concl(),
        Formula::imp(hyp.clone(), kernel::thm::subset(env, c_t.clone(), prod_t)),
        "composite_typed: the inclusion clause has the wrong shape"
    );

    // ── Clause 2: totality on `d` ───────────────────────────────────────────
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let px = ap.sets.pair(tx.clone(), val(&tx));
    let mem_xd = Formula::mem(tx.clone(), td.clone());
    let k2 = Formula::and(hyp.clone(), mem_xd.clone());
    let k2_h = and_left(hyp.clone(), mem_xd.clone());
    let k2_xd = and_right(hyp.clone(), mem_xd.clone());
    let k2_val = hyp_mp(&syl(&k2_h, &Thm::ax_inst(hyp.clone(), tx.clone())?)?, &k2_xd)?;

    let ax_px = inst_all(comp_ax, &[tg.clone(), tf.clone(), td.clone(), px.clone()])?;
    let body_x = Formula::and(
        Formula::mem(tb.clone(), td.clone()),
        Formula::eq(px.clone(), ap.sets.pair(tb.clone(), val(&tb))),
    );
    if *ax_px.concl()
        != Formula::iff(
            Formula::mem(px.clone(), c_t.clone()),
            Formula::exists(bv, body_x.clone()),
        )
    {
        return None
    }
    let k2_wit = hyp_and(&k2_xd, &a1i(&Thm::eq_refl(px.clone()), k2.clone()))?;
    let k2_ex = syl(&k2_wit, &exists_intro_imp(bv, body_x, tx.clone())?)?;
    let k2_mem = syl(&k2_ex, &iff_mpr(&ax_px)?)?;

    let y_body = Formula::and(
        Formula::mem(ty.clone(), tt.clone()),
        Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), c_t.clone()),
    );
    let k2_out = syl(
        &hyp_and(&k2_val, &k2_mem)?,
        &exists_intro_imp(yv, y_body.clone(), val(&tx))?,
    )?;
    let tot = uncurry(&k2_out)?;
    let h_tot = Thm::mp(
        &Thm::ax_dist(
            xv,
            hyp.clone(),
            Formula::imp(mem_xd, Formula::exists(yv, y_body)),
        )?,
        &Thm::gen(xv, &tot),
    )?;
    debug_assert_eq!(
        *h_tot.concl(),
        Formula::imp(hyp.clone(), is_total(env, &ap.sets, &td, &tt, &c_t)),
        "composite_typed: the totality clause has the wrong shape"
    );

    // ── Clause 3: single-valuedness, with no hypothesis at all ──────────────
    let (sx, sy, sy2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tsx, tsy, tsy2) = (Term::var(sx), Term::var(sy), Term::var(sy2));
    let v_y = composite_value_at(env, ap, comp, comp_ax, &tg, &tf, &td, &tsx, &tsy)?;
    let v_y2 = composite_value_at(env, ap, comp, comp_ax, &tg, &tf, &td, &tsx, &tsy2)?;
    let m1 = Formula::mem(ap.sets.pair(tsx.clone(), tsy.clone()), c_t.clone());
    let m2 = Formula::mem(ap.sets.pair(tsx.clone(), tsy2.clone()), c_t.clone());
    let s1 = syl(&and_left(m1.clone(), m2.clone()), &v_y)?;
    let s2 = syl(&and_right(m1, m2), &v_y2)?;
    let s2_symm = hyp_eq_symm(env, &s2)?;
    let sv_body = hyp_eq_trans(env, &s1, &s2_symm)?;
    let sv = Thm::gen(sx, &Thm::gen(sy, &Thm::gen(sy2, &sv_body)));
    debug_assert_eq!(
        *sv.concl(),
        is_single_valued(env, &ap.sets, &c_t),
        "composite_typed: sv(comp) has the wrong shape"
    );

    // ── The three clauses, across the function space's membership condition ─
    let isfun = hyp_and(&h_sub, &hyp_and(&h_tot, &a1i(&sv, hyp.clone()))?)?;
    debug_assert_eq!(
        *isfun.concl(),
        Formula::imp(
            hyp.clone(),
            is_function(env, &ap.sets, &s.prod, &td, &tt, &c_t)
        ),
        "composite_typed: isfun has the wrong shape"
    );
    let fs_at = inst_all(&s.fs.fs_ax, &[td.clone(), tt.clone(), c_t.clone()])?;
    let out = syl(&isfun, &iff_mpr(&fs_at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::mem(c_t, s.fs.of(td, tt))),
        "composite_typed: unexpected shape"
    );
    Some(gen_all(&[gv, fv, dv, tv], &out))
}
