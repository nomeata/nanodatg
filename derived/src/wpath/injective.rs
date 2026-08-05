//! **P4** — the code determines the tree.
//!
//! # Interface
//!
//! ```text
//! sub_paths(w,w′) := ∀q. (⟨w,q⟩ ∈ paths → ⟨w′,q⟩ ∈ paths)         [sub_paths]
//!
//! ⊢ ∀A ∀B ∀u ∀Q. ((closed(A,B,u) ∧ amb(A,B,Q))
//!       → ∀w. (w ∈ W → ∀w′. (w′ ∈ W → (sub_paths(w,w′) → w = w′))))
//!                                                           [paths_injective]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # One inclusion, not two — and that halves the proof
//!
//! The statement a consumer wants is *"equal codes, equal trees"*, and the
//! obvious way to it is an equivalence hypothesis `∀q. (… ↔ …)`. **The
//! *inclusion* suffices**: if every labelled path of `w` is one of `w′`, then
//! already `w = w′`, and the converse inclusion never has to be established.
//! `image_in_universe`'s single-valuedness clause then follows from the
//! biconditional it actually gets, in one line.
//!
//! That is not a presentational choice. Under the equivalence the children step
//! has to be run in both directions, at two different nodes, and the whole
//! argument doubles; under the inclusion it is run once.
//!
//! # The induction
//!
//! [`crate::wtype::w_rect`] at
//!
//! ```text
//! φ(w) := ∀w′. (w′ ∈ W → (sub_paths(w,w′) → w = w′))
//! ```
//!
//! Given `w = ⟨a,f⟩` and `w′ ∈ W`, [`crate::wtype::w_inversion`] writes
//! `w′ = ⟨a′,f′⟩`, and then:
//!
//! * **the tag.** `⟨w, ⟨∅,a⟩⟩ ∈ paths` by the root rule, hence
//!   `⟨w′, ⟨∅,a⟩⟩ ∈ paths`, and [`super::root_label`] reads `a = a′` off it;
//! * **the children.** For `b ∈ B(a)` and a labelled path `⟨s,x⟩` of `f(b)`,
//!   the step rule makes `⟨⟨b,s⟩,x⟩` a path of `w`, hence of `w′`, and
//!   [`super::step_premise`] hands it back as a path of `f′(b)` — so
//!   `sub_paths(f(b), f′(b))`, and the induction hypothesis gives
//!   `f(b) = f′(b)`;
//! * **the node.** [`crate::ext::funspace_ext`] turns that into `f = f′`, and
//!   the Kuratowski pair does the rest.
//!
//! The entry `q` has to be *known* to be a pair before the step rule applies,
//! and that is why [`super::paths_subset`] is an input: `q` is a member of
//! `prod(Q,A)` because `⟨f(b),q⟩` is a member of the ambient product, and the
//! product's characteristic property splits it.
//!
//! **Nothing in this file mentions a fibre's size, a stage, or `ω`.** The
//! induction is over the tree, the paths are finite by construction, and the
//! only ambient facts used are the three in [`super::amb`].

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ext::{funspace_ext, pointwise};
use crate::funspace::discharge;
use crate::recursion::hyp::{hyp_eq_symm, hyp_eq_trans};
use crate::sums::Sums;
use crate::wtype::{ind_step, is_sup, w_rect, Params, Wtype};
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};

use super::condition::{path_closed, At};
use super::shared::{gen_under, hyp_inst, hyp_inst_mp, hyp_leibniz};

/// `∀q. (⟨w,q⟩ ∈ paths → ⟨w′,q⟩ ∈ paths)` — "every labelled path of `w` is one
/// of `w′`".
pub fn sub_paths(env: &mut Env, s: &Sums, at: &At, ps: &Term, w: &Term, w2: &Term) -> Formula {
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    Formula::forall(
        qv,
        Formula::imp(
            Formula::mem(at.pair(s, w.clone(), tq.clone()), ps.clone()),
            Formula::mem(at.pair(s, w2.clone(), tq), ps.clone()),
        ),
    )
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, npsi) = inner.as_imp()?;
    let (psi, fls2) = npsi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// Everything the induction step needs, threaded rather than re-derived.
struct Kit<'a> {
    s: Sums,
    at: At,
    ps: Term,
    h: Formula,
    /// `⊢ H → path_root(paths)`.
    h_root: Thm,
    /// `⊢ H → path_step(paths)`.
    h_step: Thm,
    /// `⊢ H → ∀a ∀f ∀x. (⟨⟨a,f⟩,⟨∅,x⟩⟩ ∈ paths → x = a)`.
    h_label: Thm,
    /// `⊢ H → ∀a ∀f ∀b ∀s ∀x. (…)`.
    h_prem: Thm,
    /// `⊢ closed → ∀w. (w ∈ W → is_sup(w))`.
    inv_w: Thm,
    paths_sub: &'a Thm,
    wt: &'a Wtype,
    fun_ext: Thm,
    /// `⊢ H → closed(A,B,u)`.
    h_closed: Thm,
}

/// **P4, injectivity of the code on `W`.**
///
/// `intro`, `inversion`, `label` and `prem` must be [`super::paths_intro`],
/// [`crate::wtype::w_inversion`], [`super::root_label`] and
/// [`super::step_premise`] over the same `paths`; `paths_sub` is
/// [`super::paths_subset`]. Every input is required hypothesis-free, and each
/// is checked at the conclusion it is used through.
#[allow(clippy::too_many_arguments)]
pub fn paths_injective(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    paths_sub: &Thm,
    intro: &Thm,
    inversion: &Thm,
    label: &Thm,
    prem: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[paths_sub, intro, inversion, label, prem]) {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ps = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);

    let closed = wt.closed_at(env, &at.a, &at.b, &at.u);
    let ambient = super::intro::amb(env, &s, &at);
    let h = Formula::and(closed.clone(), ambient.clone());
    let h_closed = and_left(closed.clone(), ambient);

    // ── the motive ──────────────────────────────────────────────────────────
    let zv = env.fresh_var();
    let phi = phi_at(env, &s, &at, &ps, &Term::var(zv));

    // ── the pieces, instantiated at these four parameters ───────────────────
    let intro_at =
        inst_all(intro, &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()])?;
    let closure = path_closed(env, &s, &at, &ps);
    if *intro_at.concl() != Formula::imp(h.clone(), closure.clone()) {
        return None
    }
    let (root_ps, step_ps) = split_and(&closure)?;
    let kit = Kit {
        s: s.clone(),
        at: at.clone(),
        ps: ps.clone(),
        h: h.clone(),
        h_root: syl(&intro_at, &and_left(root_ps.clone(), step_ps.clone()))?,
        h_step: syl(&intro_at, &and_right(root_ps, step_ps))?,
        h_label: inst_all(label, &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()])?,
        h_prem: inst_all(prem, &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()])?,
        inv_w: inst_all(inversion, &[at.a.clone(), at.b.clone(), at.u.clone()])?,
        paths_sub,
        wt,
        fun_ext: funspace_ext(env, &s.ap, &s.prod, &s.fs, &wt.app_pair)?,
        h_closed: h_closed.clone(),
    };

    let h_ind = induction_step(env, &kit, zv, &phi)?;
    let want = ind_step(env, &s, &at.w, &at.a, &at.b, zv, &phi);
    if *h_ind.concl() != Formula::imp(h.clone(), want) {
        return None
    }

    // ── `w_rect` at the motive ──────────────────────────────────────────────
    let rect = w_rect(env, wt, &[av, bv, uv, qv], Params { a: av, b: bv, u: uv }, zv, &phi)?;
    let out = hyp_mp(&hyp_mp(&a1i(&rect, h.clone()), &h_closed)?, &h_ind)?;
    let wv = env.fresh_var();
    let body = Formula::imp(
        Formula::mem(Term::var(wv), at.w.clone()),
        phi_at(env, &s, &at, &ps, &Term::var(wv)),
    );
    if *out.concl() != Formula::imp(h, Formula::forall(wv, body)) {
        return None
    }
    Some(gen_all(&[av, bv, uv, qv], &out))
}

/// `∀w′. (w′ ∈ W → (sub_paths(t,w′) → t = w′))` — the motive at a term.
fn phi_at(env: &mut Env, s: &Sums, at: &At, ps: &Term, t: &Term) -> Formula {
    let w2v = env.fresh_var();
    let tw2 = Term::var(w2v);
    let sub = sub_paths(env, s, at, ps, t, &tw2);
    Formula::forall(
        w2v,
        Formula::imp(
            Formula::mem(tw2.clone(), at.w.clone()),
            Formula::imp(sub, Formula::eq(t.clone(), tw2)),
        ),
    )
}

/// `⊢ H → ind_step(φ)` — the whole of the induction step.
fn induction_step(env: &mut Env, kit: &Kit<'_>, zv: FreeVar, phi: &Formula) -> Option<Thm> {
    let (s, at, ps, h) = (&kit.s, &kit.at, &kit.ps, &kit.h);
    let (a2, f2, w2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tw2) = (Term::var(a2), Term::var(f2), Term::var(w2v));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let node = at.pair(s, ta.clone(), tf.clone());

    // ── the five nested hypotheses ──────────────────────────────────────────
    let g_a = Formula::mem(ta.clone(), at.a.clone());
    let g_f = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), at.w.clone()));
    let bvv = env.fresh_var();
    let tbv = Term::var(bvv);
    let g_ih = Formula::forall(
        bvv,
        Formula::imp(
            Formula::mem(tbv.clone(), fibre.clone()),
            phi_at(env, s, at, ps, &s.ap.apply(tf.clone(), tbv.clone())),
        ),
    );
    let g_w2 = Formula::mem(tw2.clone(), at.w.clone());
    let g_sub = sub_paths(env, s, at, ps, &node, &tw2);

    let k1 = Formula::and(h.clone(), g_a.clone());
    let k2 = Formula::and(k1.clone(), g_f.clone());
    let k3 = Formula::and(k2.clone(), g_ih.clone());
    let k4 = Formula::and(k3.clone(), g_w2.clone());
    let k5 = Formula::and(k4.clone(), g_sub.clone());

    // Projections down to `K5`.
    let p4 = and_left(k4.clone(), g_sub.clone());
    let p3 = syl(&p4, &and_left(k3.clone(), g_w2.clone()))?;
    let p2 = syl(&p3, &and_left(k2.clone(), g_ih.clone()))?;
    let p1 = syl(&p2, &and_left(k1.clone(), g_f.clone()))?;
    let k5_h = syl(&p1, &and_left(h.clone(), g_a.clone()))?;
    let k5_a = syl(&p1, &and_right(h.clone(), g_a.clone()))?;
    let k5_f = syl(&p2, &and_right(k1.clone(), g_f.clone()))?;
    let k5_ih = syl(&p3, &and_right(k2.clone(), g_ih.clone()))?;
    let k5_w2 = syl(&p4, &and_right(k3.clone(), g_w2.clone()))?;
    let k5_sub = and_right(k4.clone(), g_sub.clone());
    let k5_closed = syl(&k5_h, &kit.h_closed)?;

    // ── `w′ = ⟨a′,f′⟩` ──────────────────────────────────────────────────────
    let (a3, f3) = (env.fresh_var(), env.fresh_var());
    let (ta3, tf3) = (Term::var(a3), Term::var(f3));
    let inv_inner = |a_t: &Term, f_t: &Term| {
        Formula::and(
            Formula::mem(
                f_t.clone(),
                s.fs.of(s.ap.apply(at.b.clone(), a_t.clone()), at.w.clone()),
            ),
            Formula::eq(tw2.clone(), at.pair(s, a_t.clone(), f_t.clone())),
        )
    };
    let inv_matrix = |a_t: &Term| {
        Formula::and(
            Formula::mem(a_t.clone(), at.a.clone()),
            Formula::exists(f3, inv_inner(a_t, &tf3)),
        )
    };
    if Formula::exists(a3, inv_matrix(&ta3)) != is_sup(env, s, &at.w, &at.a, &at.b, &tw2) {
        return None
    }
    let k5_ex = hyp_inst_mp(&syl(&k5_closed, &kit.inv_w)?, &tw2, &k5_w2)?;

    let m1 = Formula::and(k5.clone(), inv_matrix(&ta3));
    let m1_ex = syl(
        &and_right(k5.clone(), inv_matrix(&ta3)),
        &and_right(
            Formula::mem(ta3.clone(), at.a.clone()),
            Formula::exists(f3, inv_inner(&ta3, &tf3)),
        ),
    )?;
    let m2 = Formula::and(m1.clone(), inv_inner(&ta3, &tf3));
    let m2_inner = and_right(m1.clone(), inv_inner(&ta3, &tf3));
    let (i_f, i_eq) = split_and(&inv_inner(&ta3, &tf3))?;
    let m2_f3 = syl(&m2_inner, &and_left(i_f.clone(), i_eq.clone()))?;
    let m2_eq = syl(&m2_inner, &and_right(i_f, i_eq))?;

    // Everything above, projected into `M2`.
    let down = syl(&and_left(m1.clone(), inv_inner(&ta3, &tf3)), &and_left(k5.clone(), inv_matrix(&ta3)))?;
    let m2_h = syl(&down, &k5_h)?;
    let m2_a = syl(&down, &k5_a)?;
    let m2_f = syl(&down, &k5_f)?;
    let m2_ih = syl(&down, &k5_ih)?;
    let m2_sub = syl(&down, &k5_sub)?;

    // ── the tag ─────────────────────────────────────────────────────────────
    let root_entry = at.pair(s, s.zero(), ta.clone());
    let m2_a_eq = {
        let at_f = hyp_inst(&hyp_inst(&syl(&m2_h, &kit.h_root)?, &ta)?, &tf)?;
        let in_w = hyp_mp(&at_f, &hyp_and(&m2_a, &m2_f)?)?;
        let in_w2 = hyp_mp(&hyp_inst(&m2_sub, &root_entry)?, &in_w)?;
        let hole = env.fresh_var();
        let moved = hyp_mp(
            &hyp_leibniz(
                &m2_eq,
                hole,
                &Formula::mem(at.pair(s, Term::var(hole), root_entry.clone()), ps.clone()),
            )?,
            &in_w2,
        )?;
        let lab = hyp_inst(
            &hyp_inst(&hyp_inst(&syl(&m2_h, &kit.h_label)?, &ta3)?, &tf3)?,
            &ta,
        )?;
        hyp_mp(&lab, &moved)?
    };

    // ── the children ────────────────────────────────────────────────────────
    let n = Formula::and(m2.clone(), Formula::mem(tbv.clone(), fibre.clone()));
    let n_m2 = and_left(m2.clone(), Formula::mem(tbv.clone(), fibre.clone()));
    let n_b = and_right(m2.clone(), Formula::mem(tbv.clone(), fibre.clone()));
    let child = s.ap.apply(tf.clone(), tbv.clone());
    let child3 = s.ap.apply(tf3.clone(), tbv.clone());
    let n_sub_children = children(env, kit, &Ctx {
        n: n.clone(),
        n_m2: n_m2.clone(),
        n_b: n_b.clone(),
        ta: ta.clone(),
        tf: tf.clone(),
        tbv: tbv.clone(),
        m2_eq: m2_eq.clone(),
        m2_sub: m2_sub.clone(),
        m2_h: m2_h.clone(),
        m2_a: m2_a.clone(),
        m2_f: m2_f.clone(),
        child: child.clone(),
        child3: child3.clone(),
        ta3: ta3.clone(),
        tf3: tf3.clone(),
    })?;

    // ── the induction hypothesis, at `b` ────────────────────────────────────
    let n_pointwise_at = {
        let ih_at = hyp_mp(&hyp_inst(&syl(&n_m2, &m2_ih)?, &tbv)?, &n_b)?;
        // `f′(b) ∈ W`, through `a = a′`.
        let b_in3 = {
            let hole = env.fresh_var();
            hyp_mp(
                &hyp_leibniz(
                    &syl(&n_m2, &m2_a_eq)?,
                    hole,
                    &Formula::mem(tbv.clone(), s.ap.apply(at.b.clone(), Term::var(hole))),
                )?,
                &n_b,
            )?
        };
        let app_mem = inst_all(
            &kit.wt.app_mem,
            &[
                s.ap.apply(at.b.clone(), ta3.clone()),
                at.w.clone(),
                tf3.clone(),
                tbv.clone(),
            ],
        )?;
        let child_in_w = hyp_mp(
            &a1i(&app_mem, n.clone()),
            &hyp_and(&syl(&n_m2, &m2_f3)?, &b_in3)?,
        )?;
        hyp_mp(&hyp_mp(&hyp_inst(&ih_at, &child3)?, &child_in_w)?, &n_sub_children)?
    };

    // ── pointwise, then `f = f′` ────────────────────────────────────────────
    let m2_pw = {
        let body = Formula::imp(
            Formula::mem(tbv.clone(), fibre.clone()),
            Formula::eq(child.clone(), child3.clone()),
        );
        let g = gen_under(bvv, &m2, &body, &uncurry(&n_pointwise_at)?)?;
        if *g.concl() != Formula::imp(m2.clone(), pointwise(env, &s.ap, &fibre, &tf, &tf3)) {
            return None
        }
        g
    };
    let m2_f3_at_a = {
        let hole = env.fresh_var();
        let back = hyp_eq_symm(env, &m2_a_eq)?;
        hyp_mp(
            &hyp_leibniz(
                &back,
                hole,
                &Formula::mem(
                    tf3.clone(),
                    s.fs.of(s.ap.apply(at.b.clone(), Term::var(hole)), at.w.clone()),
                ),
            )?,
            &m2_f3,
        )?
    };
    let m2_f_eq = {
        let ext = inst_all(
            &kit.fun_ext,
            &[fibre.clone(), at.w.clone(), tf.clone(), tf3.clone()],
        )?;
        hyp_mp(
            &a1i(&ext, m2.clone()),
            &hyp_and(&m2_f, &hyp_and(&m2_f3_at_a, &m2_pw)?)?,
        )?
    };

    // ── the node, and the conclusion ────────────────────────────────────────
    let m2_goal = {
        let hole = env.fresh_var();
        let step1 = hyp_mp(
            &hyp_leibniz(
                &m2_a_eq,
                hole,
                &Formula::eq(node.clone(), at.pair(s, Term::var(hole), tf.clone())),
            )?,
            &a1i(&Thm::eq_refl(node.clone()), m2.clone()),
        )?;
        let hole2 = env.fresh_var();
        let step2 = hyp_mp(
            &hyp_leibniz(
                &m2_f_eq,
                hole2,
                &Formula::eq(node.clone(), at.pair(s, ta3.clone(), Term::var(hole2))),
            )?,
            &step1,
        )?;
        let back = hyp_eq_symm(env, &m2_eq)?;
        hyp_eq_trans(env, &step2, &back)?
    };
    if *m2_goal.concl() != Formula::imp(m2, Formula::eq(node.clone(), tw2.clone())) {
        return None
    }

    let m1_goal = discharge(f3, &m1_ex, &m2_goal)?;
    let k5_goal = discharge(a3, &k5_ex, &m1_goal)?;

    // ── close the five hypotheses ───────────────────────────────────────────
    let step_w2 = uncurry(&uncurry(&k5_goal)?)?;
    let (_, body_w2) = step_w2.concl().as_imp()?;
    let k3_phi = gen_under(w2v, &k3, &body_w2, &step_w2)?;
    if *k3_phi.concl() != Formula::imp(k3, phi_at(env, s, at, ps, &node)) {
        return None
    }
    let step_f = uncurry(&uncurry(&k3_phi)?)?;
    let (_, body_f) = step_f.concl().as_imp()?;
    let k1_all = gen_under(f2, &k1, &body_f, &step_f)?;
    let step_a = uncurry(&k1_all)?;
    let (_, body_a) = step_a.concl().as_imp()?;
    let _ = zv;
    let _ = phi;
    gen_under(a2, h, &body_a, &step_a)
}

/// The context the children step runs in.
struct Ctx {
    n: Formula,
    n_m2: Thm,
    n_b: Thm,
    ta: Term,
    tf: Term,
    tbv: Term,
    m2_eq: Thm,
    m2_sub: Thm,
    m2_h: Thm,
    m2_a: Thm,
    m2_f: Thm,
    child: Term,
    child3: Term,
    ta3: Term,
    tf3: Term,
}

/// `⊢ N → sub_paths(f(b), f′(b))`.
fn children(env: &mut Env, kit: &Kit<'_>, c: &Ctx) -> Option<Thm> {
    let (s, at, ps) = (&kit.s, &kit.at, &kit.ps);
    let q2 = env.fresh_var();
    let tq = Term::var(q2);
    let mem_q = Formula::mem(at.pair(s, c.child.clone(), tq.clone()), ps.clone());
    let goal = Formula::mem(at.pair(s, c.child3.clone(), tq.clone()), ps.clone());

    let n2 = Formula::and(c.n.clone(), mem_q.clone());
    let n2_n = and_left(c.n.clone(), mem_q.clone());
    let n2_q = and_right(c.n.clone(), mem_q.clone());

    // `q ∈ prod(Q,A)`, from the ambient product.
    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let n2_in_qa = {
        let bnd = syl(
            &n2_q,
            &inst_all(
                kit.paths_sub,
                &[
                    at.a.clone(),
                    at.b.clone(),
                    at.u.clone(),
                    at.q.clone(),
                    at.pair(s, c.child.clone(), tq.clone()),
                ],
            )?,
        )?;
        let split = inst_all(
            &s.pair_in_prod,
            &[at.w.clone(), qa.clone(), c.child.clone(), tq.clone()],
        )?;
        syl(
            &syl(&bnd, &iff_mp(&split)?)?,
            &and_right(
                Formula::mem(c.child.clone(), at.w.clone()),
                Formula::mem(tq.clone(), qa.clone()),
            ),
        )?
    };

    // `q = ⟨s,x⟩`, by Replacement's characterisation of the product.
    let (s3, x3) = (env.fresh_var(), env.fresh_var());
    let (ts3, tx3) = (Term::var(s3), Term::var(x3));
    let q_inner = |s_t: &Term, x_t: &Term| {
        Formula::and(
            Formula::mem(x_t.clone(), at.a.clone()),
            Formula::eq(tq.clone(), at.pair(s, s_t.clone(), x_t.clone())),
        )
    };
    let q_matrix = |s_t: &Term| {
        Formula::and(
            Formula::mem(s_t.clone(), at.q.clone()),
            Formula::exists(x3, q_inner(s_t, &tx3)),
        )
    };
    let prod_at = inst_all(&s.prod.prod_ax, &[at.q.clone(), at.a.clone(), tq.clone()])?;
    if *prod_at.concl()
        != Formula::iff(
            Formula::mem(tq.clone(), qa.clone()),
            Formula::exists(s3, q_matrix(&ts3)),
        )
    {
        return None
    }
    let n2_ex = syl(&n2_in_qa, &iff_mp(&prod_at)?)?;

    let n3 = Formula::and(n2.clone(), q_matrix(&ts3));
    let n3_ex = syl(
        &and_right(n2.clone(), q_matrix(&ts3)),
        &and_right(
            Formula::mem(ts3.clone(), at.q.clone()),
            Formula::exists(x3, q_inner(&ts3, &tx3)),
        ),
    )?;
    let n4 = Formula::and(n3.clone(), q_inner(&ts3, &tx3));
    let n4_inner = and_right(n3.clone(), q_inner(&ts3, &tx3));
    let (qi_x, qi_eq) = split_and(&q_inner(&ts3, &tx3))?;
    let n4_qeq = syl(&n4_inner, &and_right(qi_x, qi_eq))?;

    let to_n2 = syl(
        &and_left(n3.clone(), q_inner(&ts3, &tx3)),
        &and_left(n2.clone(), q_matrix(&ts3)),
    )?;
    let to_n = syl(&to_n2, &n2_n)?;

    // The premise, with `q` spelled as a pair.
    let entry = at.pair(s, ts3.clone(), tx3.clone());
    let n4_prem = {
        let hole = env.fresh_var();
        hyp_mp(
            &hyp_leibniz(
                &n4_qeq,
                hole,
                &Formula::mem(at.pair(s, c.child.clone(), Term::var(hole)), ps.clone()),
            )?,
            &syl(&to_n2, &n2_q)?,
        )?
    };

    // The step rule at this node, then the inclusion, then `step_premise`.
    let path = at.pair(s, c.tbv.clone(), ts3.clone());
    let out_entry = at.pair(s, path.clone(), tx3.clone());
    let n4_at_node = {
        let mut cur = syl(&syl(&to_n, &c.n_m2)?, &c.m2_h)?;
        cur = syl(&cur, &kit.h_step)?;
        for t in [&c.ta, &c.tf, &c.tbv, &ts3, &tx3] {
            cur = hyp_inst(&cur, t)?;
        }
        hyp_mp(
            &cur,
            &hyp_and(
                &hyp_and(&syl(&syl(&to_n, &c.n_m2)?, &c.m2_a)?, &syl(&syl(&to_n, &c.n_m2)?, &c.m2_f)?)?,
                &hyp_and(&syl(&to_n, &c.n_b)?, &n4_prem)?,
            )?,
        )?
    };
    let n4_at_w2 = hyp_mp(
        &hyp_inst(&syl(&syl(&to_n, &c.n_m2)?, &c.m2_sub)?, &out_entry)?,
        &n4_at_node,
    )?;
    let n4_at_node3 = {
        let hole = env.fresh_var();
        hyp_mp(
            &hyp_leibniz(
                &syl(&syl(&to_n, &c.n_m2)?, &c.m2_eq)?,
                hole,
                &Formula::mem(at.pair(s, Term::var(hole), out_entry.clone()), ps.clone()),
            )?,
            &n4_at_w2,
        )?
    };
    let n4_child3 = {
        let (a3t, f3t) = (c.ta3.clone(), c.tf3.clone());
        let mut cur = syl(&syl(&syl(&to_n, &c.n_m2)?, &c.m2_h)?, &kit.h_prem)?;
        for t in [&a3t, &f3t, &c.tbv, &ts3, &tx3] {
            cur = hyp_inst(&cur, t)?;
        }
        hyp_mp(&cur, &n4_at_node3)?
    };
    // and back from `⟨s,x⟩` to `q`.
    let n4_goal = {
        let back = hyp_eq_symm(env, &n4_qeq)?;
        let hole = env.fresh_var();
        hyp_mp(
            &hyp_leibniz(
                &back,
                hole,
                &Formula::mem(at.pair(s, c.child3.clone(), Term::var(hole)), ps.clone()),
            )?,
            &n4_child3,
        )?
    };
    if *n4_goal.concl() != Formula::imp(n4, goal.clone()) {
        return None
    }
    let _ = entry;

    let n3_goal = discharge(x3, &n3_ex, &n4_goal)?;
    let n2_goal = discharge(s3, &n2_ex, &n3_goal)?;
    let body = Formula::imp(mem_q, goal);
    let out = gen_under(q2, &c.n, &body, &uncurry(&n2_goal)?)?;
    if *out.concl()
        != Formula::imp(
            c.n.clone(),
            sub_paths(env, s, at, ps, &c.child, &c.child3),
        )
    {
        return None
    }
    Some(out)
}

