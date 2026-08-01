//! The **one-point function** `{⟨a,b⟩}`: the graph that relates `a` to `b` and
//! nothing else.
//!
//! # Interface
//!
//! Writing `sv(f)` for [`crate::funspace::is_single_valued`] and `{a}` for the
//! singleton, the exports are
//!
//! ```text
//! ⊢ ∀a ∀b ∀x ∀y. (⟨x,y⟩ ∈ {⟨a,b⟩} → (x = a ∧ y = b))   [point_pairs]
//! ⊢ ∀a ∀b. sv({⟨a,b⟩})                                  [point_sv]
//! ⊢ ∀a ∀b. app({⟨a,b⟩}, a) = b                          [point_app]
//! ⊢ ∀a ∀b ∀T. (b ∈ T → {⟨a,b⟩} ∈ fs({a}, T))            [point_in_funspace]
//! ```
//!
//! Only the last carries a hypothesis, and it is the one a caller has anyway:
//! a function into `T` must take a value in `T`. [`PointFun`] bundles all four.
//! Callers need none of the derivations.
//!
//! # Why it is wanted
//!
//! Twice, in the same construction. `INDUCTIVES.md`'s translation gives a
//! constructor with **one recursive argument** the W-type element
//!
//! ```text
//! succ n := ⟨inr •, {⟨•, n⟩}⟩
//! ```
//!
//! whose second component is the function out of the one-element fibre `1 = {•}`
//! taking the value `n` — that is `{⟨•,n⟩}`, and
//! [`crate::wtype::Wtype::sup_mem`] wants it in `fs(1, W)`, which is
//! [`point_in_funspace`] at `a := •`. And the fibre family itself is built by
//! `rec₊` out of two constant functions on `1`, each of which is again a
//! one-point graph. So the same lemma pays for the constructor and for the
//! family it is indexed by.
//!
//! [`crate::wrec_unit::singleton_attempt`] proves the same three clauses inline
//! for one specific pair; nothing there is reusable, because the pair is fixed
//! and the target is `{V}`. This is the general statement.
//!
//! # Non-vacuity
//!
//! [`point_app`] is what stops the interface from being about a set with no
//! values: it is an *equation*, at fresh `a` and `b`, so `{⟨a,b⟩}` is a graph
//! that actually computes. `tests/point_fun.rs` pins all four conclusions and
//! checks that the two sides of [`point_app`] are different terms.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{is_function, is_single_valued, is_total};
use crate::sums::Sums;
use crate::wrec::{hyp_eq_symm, hyp_eq_trans};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, imp_refl, inst_all, singleton, syl, uncurry,
};

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
fn hyp_gen(v: FreeVar, t: &Thm) -> Option<Thm> {
    let (h, body) = t.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h, body)?, &Thm::gen(v, t))
}

/// Everything this file derives, at fresh universally quantified variables.
pub struct PointFun {
    /// `⊢ ∀a ∀b ∀x ∀y. (⟨x,y⟩ ∈ {⟨a,b⟩} → (x = a ∧ y = b))`.
    pub pairs: Thm,
    /// `⊢ ∀a ∀b. sv({⟨a,b⟩})`.
    pub sv: Thm,
    /// `⊢ ∀a ∀b. app({⟨a,b⟩}, a) = b`.
    pub app: Thm,
    /// `⊢ ∀a ∀b ∀T. (b ∈ T → {⟨a,b⟩} ∈ fs({a}, T))`.
    pub in_fs: Thm,
}

impl PointFun {
    /// Derive all four, over a caller-supplied [`Sums`] — so that the pairing,
    /// product, function space and `app` are the *same* symbols everything else
    /// is stated over.
    ///
    /// `app_pair` must be [`crate::ext::app_of_pair`],
    /// `⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)`; it is a field of
    /// [`crate::wtype::Wtype`].
    pub fn over(env: &mut Env, s: &Sums, app_pair: &Thm) -> Option<PointFun> {
        let pairs = point_pairs(env, &s.ap)?;
        let sv = point_sv(env, &s.ap, &pairs)?;
        let app = point_app(env, &s.ap, app_pair, &sv)?;
        let in_fs = point_in_funspace(env, s, &sv)?;
        Some(PointFun { pairs, sv, app, in_fs })
    }

    /// The term `{⟨a,b⟩}`.
    pub fn of(s: &Sums, a: Term, b: Term) -> Term {
        singleton(s.ap.sets.up, s.ap.sets.pair(a, b))
    }
}

/// `⊢ ∀a ∀b ∀x ∀y. (⟨x,y⟩ ∈ {⟨a,b⟩} → (x = a ∧ y = b))` — the graph relates
/// nothing but `a` to `b`.
///
/// Membership in a singleton is an equation, and the Kuratowski pair is
/// injective; there is nothing else to it.
pub fn point_pairs(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let (av, bv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx, ty) = (Term::var(av), Term::var(bv), Term::var(xv), Term::var(yv));
    let p = ap.sets.pair(ta.clone(), tb.clone());
    let q = ap.sets.pair(tx.clone(), ty.clone());

    let ms = inst_all(&ap.mem_sing, &[p.clone(), q.clone()])?;
    let inj = inst_all(&ap.pair_inj, &[tx.clone(), ty.clone(), ta.clone(), tb.clone()])?;
    let out = syl(&iff_mp(&ms)?, &inj)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::mem(q, singleton(ap.sets.up, p)),
            Formula::and(Formula::eq(tx, ta), Formula::eq(ty, tb))
        ),
        "point_fun: point_pairs has the wrong shape"
    );
    Some(gen_all(&[av, bv, xv, yv], &out))
}

/// `⊢ ∀a ∀b. sv({⟨a,b⟩})` — a one-point graph is single-valued.
///
/// Both values at `x` are forced to be `b` by [`point_pairs`], so they are
/// equal to each other.
pub fn point_sv(env: &mut Env, ap: &Apply, pairs: &Thm) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let g = singleton(ap.sets.up, ap.sets.pair(ta.clone(), tb.clone()));

    let (xv, y1v, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty1, ty2) = (Term::var(xv), Term::var(y1v), Term::var(y2v));
    let m1 = Formula::mem(ap.sets.pair(tx.clone(), ty1.clone()), g.clone());
    let m2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), g.clone());

    let value = |y: &Term| -> Option<Thm> {
        let at = inst_all(pairs, &[ta.clone(), tb.clone(), tx.clone(), y.clone()])?;
        syl(
            &at,
            &and_right(
                Formula::eq(tx.clone(), ta.clone()),
                Formula::eq(y.clone(), tb.clone()),
            ),
        )
    };
    let h_y1 = syl(&and_left(m1.clone(), m2.clone()), &value(&ty1)?)?;
    let h_y2 = syl(&and_right(m1, m2), &value(&ty2)?)?;
    let h_b_y2 = hyp_eq_symm(env, &h_y2)?;
    let body = hyp_eq_trans(env, &h_y1, &h_b_y2)?;

    let sv = gen_all(&[xv, y1v, y2v], &body);
    debug_assert_eq!(
        *sv.concl(),
        is_single_valued(env, &ap.sets, &g),
        "point_fun: point_sv has the wrong shape"
    );
    Some(gen_all(&[av, bv], &sv))
}

/// `⊢ ∀a ∀b. app({⟨a,b⟩}, a) = b` — **the one-point graph computes**.
///
/// [`crate::ext::app_of_pair`] at the pair the singleton contains; the
/// single-valuedness premise is [`point_sv`], and the membership premise is
/// reflexivity.
///
/// No membership antecedent survives, unlike
/// [`crate::funcs::beta_conditional`]: `⟨a,b⟩ ∈ {⟨a,b⟩}` already says `a` is in
/// the domain.
pub fn point_app(env: &mut Env, ap: &Apply, app_pair: &Thm, sv: &Thm) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let p = ap.sets.pair(ta.clone(), tb.clone());
    let g = singleton(ap.sets.up, p.clone());

    let p_in_g = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[p.clone(), p.clone()])?)?,
        &Thm::eq_refl(p),
    )?;
    let sv_ab = inst_all(sv, &[ta.clone(), tb.clone()])?;
    let out = Thm::mp(
        &inst_all(app_pair, &[g.clone(), ta.clone(), tb.clone()])?,
        &and_intro(&sv_ab, &p_in_g),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(ap.apply(g, ta.clone()), tb.clone()),
        "point_fun: point_app has the wrong shape"
    );
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀a ∀b ∀T. (b ∈ T → {⟨a,b⟩} ∈ fs({a}, T))` — **the typing rule**.
///
/// All three clauses of [`crate::funspace::is_function`]:
///
/// * `{⟨a,b⟩} ⊆ {a} × T` — one point, and `⟨a,b⟩` is in the product because
///   `a ∈ {a}` and `b ∈ T`;
/// * total on `{a}` — the only member of `{a}` is `a`, and `b` is its value;
/// * single-valued — [`point_sv`], which needs no hypothesis.
///
/// The antecedent `b ∈ T` is genuine and is used exactly in the first two
/// clauses: nothing else supplies a codomain.
pub fn point_in_funspace(env: &mut Env, s: &Sums, sv: &Thm) -> Option<Thm> {
    let ap = &s.ap;
    let up = ap.sets.up;
    let (av, bv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt) = (Term::var(av), Term::var(bv), Term::var(tv));
    let p = ap.sets.pair(ta.clone(), tb.clone());
    let g = singleton(up, p.clone());
    let dom = singleton(up, ta.clone());
    let prod_t = s.prod.of(dom.clone(), tt.clone());
    let h = Formula::mem(tb.clone(), tt.clone()); // the hypothesis `b ∈ T`

    // `⊢ a ∈ {a}` and `⊢ ⟨a,b⟩ ∈ {⟨a,b⟩}`, both by reflexivity.
    let a_in_dom = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[ta.clone(), ta.clone()])?)?,
        &Thm::eq_refl(ta.clone()),
    )?;
    let p_in_g = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[p.clone(), p.clone()])?)?,
        &Thm::eq_refl(p.clone()),
    )?;

    // ── `H → ⟨a,b⟩ ∈ {a} × T` ───────────────────────────────────────────────
    let in_prod = syl(
        &hyp_and(&a1i(&a_in_dom, h.clone()), &imp_refl(h.clone()))?,
        &iff_mpr(&inst_all(
            &s.pair_in_prod,
            &[dom.clone(), tt.clone(), ta.clone(), tb.clone()],
        )?)?,
    )?;

    // ── `H → {⟨a,b⟩} ⊆ {a} × T` ─────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    // `z ∈ {⟨a,b⟩} → (⟨a,b⟩ ∈ {a}×T → z ∈ {a}×T)`, then swapped.
    let hole = env.fresh_var();
    let z_step = syl(
        &syl(
            &iff_mp(&inst_all(&ap.mem_sing, &[p.clone(), tz.clone()])?)?,
            &eq_symm_imp(env, tz.clone(), p.clone()),
        )?,
        &Thm::eq_leibniz(
            p.clone(),
            tz.clone(),
            hole,
            Formula::mem(Term::var(hole), prod_t.clone()),
        ),
    )?;
    let sub_at_z = syl(&in_prod, &crate::com12(&z_step)?)?;
    let sub = hyp_gen(zv, &sub_at_z)?;
    debug_assert_eq!(
        *sub.concl(),
        Formula::imp(h.clone(), kernel::thm::subset(env, g.clone(), prod_t)),
        "point_fun: the inclusion has the wrong shape"
    );

    // ── `H → is_total({a}, T, {⟨a,b⟩})` ─────────────────────────────────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let k = Formula::mem(tx.clone(), dom.clone()); // `x ∈ {a}`
    // Under `K`, `x = a`, so `⟨x,b⟩ ∈ {⟨a,b⟩}` — with no hypothesis on `T`.
    let hole = env.fresh_var();
    let k_mem = hyp_mp(
        &syl(
            &syl(
                &iff_mp(&inst_all(&ap.mem_sing, &[ta.clone(), tx.clone()])?)?,
                &eq_symm_imp(env, tx.clone(), ta.clone()),
            )?,
            &Thm::eq_leibniz(
                ta.clone(),
                tx.clone(),
                hole,
                Formula::mem(ap.sets.pair(Term::var(hole), tb.clone()), g.clone()),
            ),
        )?,
        &a1i(&p_in_g, k.clone()),
    )?;
    // `(H ∧ K) → (b ∈ T ∧ ⟨x,b⟩ ∈ {⟨a,b⟩})`, then witness `y := b`.
    let both = Formula::and(h.clone(), k.clone());
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let body = Formula::and(
        Formula::mem(ty.clone(), tt.clone()),
        Formula::mem(ap.sets.pair(tx.clone(), ty), g.clone()),
    );
    let conj = hyp_and(
        &and_left(h.clone(), k.clone()),
        &syl(&and_right(h.clone(), k.clone()), &k_mem)?,
    )?;
    debug_assert_eq!(
        *conj.concl(),
        Formula::imp(both, body.clone().subst(yv, &tb)),
        "point_fun: the totality witness does not substitute"
    );
    let ex = syl(&conj, &exists_intro_imp(yv, body, tb.clone())?)?;
    let total = hyp_gen(xv, &uncurry(&ex)?)?;
    debug_assert_eq!(
        *total.concl(),
        Formula::imp(h.clone(), is_total(env, &ap.sets, &dom, &tt, &g)),
        "point_fun: the totality clause has the wrong shape"
    );

    // ── the conjunction, and the function space ─────────────────────────────
    let sv_h = a1i(&inst_all(sv, &[ta.clone(), tb.clone()])?, h.clone());
    let isfun = hyp_and(&sub, &hyp_and(&total, &sv_h)?)?;
    debug_assert_eq!(
        *isfun.concl(),
        Formula::imp(h.clone(), is_function(env, &ap.sets, &s.prod, &dom, &tt, &g)),
        "point_fun: isfun has the wrong shape"
    );
    let out = syl(
        &isfun,
        &iff_mpr(&inst_all(&s.fs.fs_ax, &[dom.clone(), tt.clone(), g.clone()])?)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(g, s.fs.of(dom, tt))),
        "point_fun: point_in_funspace has the wrong shape"
    );
    Some(gen_all(&[av, bv, tv], &out))
}
