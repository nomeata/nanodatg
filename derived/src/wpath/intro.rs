//! **P1** — `paths` is itself closed under the two path rules.
//!
//! # Interface
//!
//! ```text
//! amb(A,B,Q) := ∅ ∈ Q ∧ ((∀a. (a ∈ A → ∀b. (b ∈ B(a) → b ∈ Q)))
//!                        ∧ (∀x ∀y. ((x ∈ Q ∧ y ∈ Q) → ⟨x,y⟩ ∈ Q)))    [amb]
//!
//! ⊢ ∀A ∀B ∀u ∀Q. ((closed(A,B,u) ∧ amb(A,B,Q))
//!                     → path_closed(A,B,u,Q, paths(A,B,u,Q)))     [paths_intro]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # The two antecedents, and what each is for
//!
//! `closed(A,B,u)` is the W-type's bound hypothesis, and it is spent in exactly
//! one place: [`crate::wtype::sup_mem`], to know that the *node* `⟨a,f⟩` a rule
//! speaks about is a member of `W` at all. At `u := U(c)` it is discharged
//! outright by [`crate::bound::least_universe_closed`], with no condition on the
//! fibres.
//!
//! [`amb`] is spent on the other component: a rule's conclusion has to be a
//! member of the ambient `prod(W, prod(Q,A))`, so the *path* it names has to be
//! in `Q`. The root path is `∅`, hence `∅ ∈ Q`; a step path is `⟨b,s⟩` with `b`
//! in a fibre and `s` a path already placed, hence the fibre clause and binary
//! pairing.
//!
//! **Binary pairing is the whole of the size demand, and that is the point.**
//! [`crate::cumul::tower_closed_bnd`] needs a `B(a)`-indexed *function* to land
//! in one stage — [`crate::cumul::bnd`], refutable at an infinite fibre —
//! because it places the node `⟨a,f⟩`, whose second component is a function on
//! the whole fibre. Here nothing but one fibre element at a time is ever paired,
//! so the demand on `Q` does not grow with the fibre.
//!
//! # Why this is the expensive half
//!
//! [`super::paths_induction`] reads one conjunct off the definition.
//! Establishing the rules *for `paths` itself* is the other direction of the
//! intersection: the conclusion has to be shown to lie in **every** closed
//! `C ⊆ Bnd` at once, which is [`super::paths_induction`] used to move the
//! premise `⟨f(b), ⟨s,x⟩⟩ ∈ paths` into that `C` before `C`'s own closure
//! applies. It is the same argument as [`crate::acc::acc_intro`]'s, one rule
//! larger.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl,
};

use super::condition::{path_closed, path_cond, path_root, path_step, At};
use super::shared::{gen_under, hyp_inst, hyp_inst_mp};

/// `∅ ∈ Q ∧ ((∀a ∈ A. ∀b ∈ B(a). b ∈ Q) ∧ (∀x ∀y. ((x ∈ Q ∧ y ∈ Q) → ⟨x,y⟩ ∈ Q)))`
/// — everything [`paths_intro`] asks of the ambient set.
///
/// Three facts, **none of them about size**: the ambient set holds the empty
/// path, holds every fibre element, and is closed under the Kuratowski pair.
/// A consumer discharges them at whatever `Q` it has; `crate::cumul`'s tower
/// satisfies all three at any fibre whatsoever.
pub fn amb(env: &mut Env, s: &Sums, at: &At) -> Formula {
    let (av, bv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx, ty) =
        (Term::var(av), Term::var(bv), Term::var(xv), Term::var(yv));

    let empty = Formula::mem(s.zero(), at.q.clone());
    let fibres = Formula::forall(
        av,
        Formula::imp(
            Formula::mem(ta.clone(), at.a.clone()),
            Formula::forall(
                bv,
                Formula::imp(
                    Formula::mem(tb.clone(), s.ap.apply(at.b.clone(), ta)),
                    Formula::mem(tb, at.q.clone()),
                ),
            ),
        ),
    );
    let pairing = Formula::forall(
        xv,
        Formula::forall(
            yv,
            Formula::imp(
                Formula::and(
                    Formula::mem(tx.clone(), at.q.clone()),
                    Formula::mem(ty.clone(), at.q.clone()),
                ),
                Formula::mem(at.pair(s, tx, ty), at.q.clone()),
            ),
        ),
    );
    Formula::and(empty, Formula::and(fibres, pairing))
}

/// **P1, the two introduction rules, at `paths` itself.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀Q. ((closed(A,B,u) ∧ amb(A,B,Q)) → path_closed(…, paths(…)))
/// ```
///
/// `paths_ax` must be [`super::paths_symbol`]'s defining biconditional,
/// `paths_ind` [`super::paths_induction`] and `paths_sub`
/// [`super::paths_subset`], all over `paths`; all three are checked at their
/// conclusions **and** for an empty hypothesis set, since this header promises
/// `⊢ …` and a `Γ` on any of them would ride through the syllogism chain.
pub fn paths_intro(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    paths_ax: &Thm,
    paths_ind: &Thm,
    paths_sub: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[paths_ax, paths_ind, paths_sub]) {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ps = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);

    let closed = wt.closed_at(env, &at.a, &at.b, &at.u);
    let ambient = amb(env, &s, &at);
    let h = Formula::and(closed.clone(), ambient.clone());
    let h_closed = and_left(closed.clone(), ambient.clone());
    let h_amb = and_right(closed, ambient.clone());
    // `amb` is `∅ ∈ Q ∧ (fibres ∧ pairing)`; take it apart at its own shape.
    let (empty_q, rest) = split_and(&ambient)?;
    let (fibres_q, pairing_q) = split_and(&rest)?;
    let h_empty = syl(&h_amb, &and_left(empty_q.clone(), rest.clone()))?;
    let h_rest = syl(&h_amb, &and_right(empty_q, rest))?;
    let h_fibres = syl(&h_rest, &and_left(fibres_q.clone(), pairing_q.clone()))?;
    let h_pairing = syl(&h_rest, &and_right(fibres_q, pairing_q))?;

    let root = root_rule(env, wt, &s, &at, &ps, &h, &h_closed, &h_empty, paths_ax)?;
    let step = step_rule(
        env,
        wt,
        &s,
        &at,
        &ps,
        &h,
        &h_closed,
        &h_fibres,
        &h_pairing,
        paths_ax,
        paths_ind,
        paths_sub,
    )?;

    let out = hyp_and(&root, &step)?;
    let want = path_closed(env, &s, &at, &ps);
    if *out.concl() != Formula::imp(h, want) {
        return None
    }
    Some(gen_all(&[av, bv, uv, qv], &out))
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

/// `⊢ H → ⟨a,f⟩ ∈ W`, under `K := H ∧ (a ∈ A ∧ f ∈ fs(B(a),W))`.
fn node_in_w(
    wt: &Wtype,
    at: &At,
    k_closed: &Thm,
    k_a: &Thm,
    k_f: &Thm,
    ta: &Term,
    tf: &Term,
) -> Option<Thm> {
    let sm = inst_all(&wt.sup_mem, &[at.a.clone(), at.b.clone(), at.u.clone()])?;
    let outer = syl(k_closed, &sm)?;
    let at_a = hyp_inst_mp(&outer, ta, k_a)?;
    hyp_inst_mp(&at_a, tf, k_f)
}

/// `⊢ K → ⟨x,y⟩ ∈ prod(c,d)` from `⊢ K → x ∈ c` and `⊢ K → y ∈ d`.
fn pair_in(
    s: &Sums,
    c: &Term,
    d: &Term,
    x: &Term,
    y: &Term,
    kx: &Thm,
    ky: &Thm,
) -> Option<Thm> {
    let ax = inst_all(&s.pair_in_prod, &[c.clone(), d.clone(), x.clone(), y.clone()])?;
    hyp_mp(&crate::a1i(&iff_mpr(&ax)?, kx.concl().as_imp()?.0), &hyp_and(kx, ky)?)
}

/// `⊢ K → x ∈ c` and `⊢ K → y ∈ d` from `⊢ K → ⟨x,y⟩ ∈ prod(c,d)`.
fn pair_parts(
    s: &Sums,
    c: &Term,
    d: &Term,
    x: &Term,
    y: &Term,
    k_pair: &Thm,
) -> Option<(Thm, Thm)> {
    let ax = inst_all(&s.pair_in_prod, &[c.clone(), d.clone(), x.clone(), y.clone()])?;
    let both = syl(k_pair, &iff_mp(&ax)?)?;
    let l = Formula::mem(x.clone(), c.clone());
    let r = Formula::mem(y.clone(), d.clone());
    Some((syl(&both, &and_left(l.clone(), r.clone()))?, syl(&both, &and_right(l, r))?))
}

/// `⊢ K → p ∈ paths` from `⊢ K → p ∈ Bnd` and `⊢ K → path_cond(p)`.
#[allow(clippy::too_many_arguments)]
fn into_paths(
    env: &mut Env,
    s: &Sums,
    at: &At,
    ps: &Term,
    paths_ax: &Thm,
    tp: &Term,
    k_bnd: &Thm,
    k_cond: &Thm,
) -> Option<Thm> {
    let cond = path_cond(env, s, at, tp);
    let ax = inst_all(
        paths_ax,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tp.clone()],
    )?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(tp.clone(), ps.clone()),
            Formula::and(Formula::mem(tp.clone(), at.bnd.clone()), cond),
        )
    {
        return None
    }
    syl(&hyp_and(k_bnd, k_cond)?, &iff_mpr(&ax)?)
}

/// `⊢ H → path_root(paths)`.
#[allow(clippy::too_many_arguments)]
fn root_rule(
    env: &mut Env,
    wt: &Wtype,
    s: &Sums,
    at: &At,
    ps: &Term,
    h: &Formula,
    h_closed: &Thm,
    h_empty: &Thm,
    paths_ax: &Thm,
) -> Option<Thm> {
    let (av2, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av2), Term::var(fv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let mem_a = Formula::mem(ta.clone(), at.a.clone());
    let mem_f = Formula::mem(tf.clone(), s.fs.of(fibre, at.w.clone()));
    let guard = Formula::and(mem_a.clone(), mem_f.clone());
    let k = Formula::and(h.clone(), guard.clone());
    let k_h = and_left(h.clone(), guard.clone());
    let k_g = and_right(h.clone(), guard.clone());
    let k_a = syl(&k_g, &and_left(mem_a.clone(), mem_f.clone()))?;
    let k_f = syl(&k_g, &and_right(mem_a, mem_f))?;
    let k_closed = syl(&k_h, h_closed)?;
    let k_empty = syl(&k_h, h_empty)?;

    let node = at.pair(s, ta.clone(), tf.clone());
    let entry = at.pair(s, s.zero(), ta.clone());
    let p = at.pair(s, node.clone(), entry.clone());

    // ── the conclusion is a member of the ambient product ───────────────────
    let k_node = node_in_w(wt, at, &k_closed, &k_a, &k_f, &ta, &tf)?;
    let k_entry = pair_in(s, &at.q, &at.a, &s.zero(), &ta, &k_empty, &k_a)?;
    let k_bnd = pair_in(
        s,
        &at.w,
        &s.prod.of(at.q.clone(), at.a.clone()),
        &node,
        &entry,
        &k_node,
        &k_entry,
    )?;

    // ── and of every closed `C ⊆ Bnd` ───────────────────────────────────────
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let g = Formula::and(
        kernel::thm::subset(env, tc.clone(), at.bnd.clone()),
        path_closed(env, s, at, &tc),
    );
    let m = Formula::and(k.clone(), g.clone());
    let m_k = and_left(k.clone(), g.clone());
    let m_g = and_right(k.clone(), g.clone());
    let (sub_c, closed_c) = split_and(&g)?;
    let m_closed_c = syl(&m_g, &and_right(sub_c, closed_c.clone()))?;
    let (root_c, step_c) = split_and(&closed_c)?;
    let m_root = syl(&m_closed_c, &and_left(root_c, step_c))?;
    let m_a = syl(&m_k, &k_a)?;
    let m_f = syl(&m_k, &k_f)?;
    let m_in_c = {
        let at_a = hyp_inst(&m_root, &ta)?;
        let at_f = hyp_inst(&at_a, &tf)?;
        hyp_mp(&at_f, &hyp_and(&m_a, &m_f)?)?
    };
    if *m_in_c.concl() != Formula::imp(m, Formula::mem(p.clone(), tc.clone())) {
        return None
    }
    let k_cond = gen_under(
        cv,
        &k,
        &Formula::imp(g, Formula::mem(p.clone(), tc)),
        &crate::uncurry(&m_in_c)?,
    )?;
    let k_paths = into_paths(env, s, at, ps, paths_ax, &p, &k_bnd, &k_cond)?;
    let body = Formula::imp(guard, Formula::mem(p, ps.clone()));
    let h_f = gen_under(fv, h, &body, &crate::uncurry(&k_paths)?)?;
    let (_, inner) = h_f.concl().as_imp()?;
    let out = gen_under(av2, h, &inner, &h_f)?;
    let want = path_root(env, s, at, ps);
    (*out.concl() == Formula::imp(h.clone(), want)).then_some(out)
}

/// `⊢ H → path_step(paths)`.
#[allow(clippy::too_many_arguments)]
fn step_rule(
    env: &mut Env,
    wt: &Wtype,
    s: &Sums,
    at: &At,
    ps: &Term,
    h: &Formula,
    h_closed: &Thm,
    h_fibres: &Thm,
    h_pairing: &Thm,
    paths_ax: &Thm,
    paths_ind: &Thm,
    paths_sub: &Thm,
) -> Option<Thm> {
    let (av2, fv, bv2, sv, xv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tf, tb, ts, tx) =
        (Term::var(av2), Term::var(fv), Term::var(bv2), Term::var(sv), Term::var(xv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let mem_a = Formula::mem(ta.clone(), at.a.clone());
    let mem_f = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), at.w.clone()));
    let node_f = Formula::and(mem_a.clone(), mem_f.clone());

    let entry = at.pair(s, ts.clone(), tx.clone());
    let child = at.pair(s, s.ap.apply(tf.clone(), tb.clone()), entry.clone());
    let mem_b = Formula::mem(tb.clone(), fibre);
    let mem_child = Formula::mem(child.clone(), ps.clone());
    let prem = Formula::and(mem_b.clone(), mem_child.clone());
    let guard = Formula::and(node_f.clone(), prem.clone());

    let k = Formula::and(h.clone(), guard.clone());
    let k_h = and_left(h.clone(), guard.clone());
    let k_g = and_right(h.clone(), guard.clone());
    let k_node = syl(&k_g, &and_left(node_f.clone(), prem.clone()))?;
    let k_prem = syl(&k_g, &and_right(node_f, prem))?;
    let k_a = syl(&k_node, &and_left(mem_a.clone(), mem_f.clone()))?;
    let k_f = syl(&k_node, &and_right(mem_a, mem_f))?;
    let k_b = syl(&k_prem, &and_left(mem_b, mem_child.clone()))?;
    let k_child = syl(&k_prem, &and_right(Formula::mem(tb.clone(), s.ap.apply(at.b.clone(), ta.clone())), mem_child))?;
    let k_closed = syl(&k_h, h_closed)?;
    let k_fibres = syl(&k_h, h_fibres)?;
    let k_pairing = syl(&k_h, h_pairing)?;

    let node = at.pair(s, ta.clone(), tf.clone());
    let path = at.pair(s, tb.clone(), ts.clone());
    let out_entry = at.pair(s, path.clone(), tx.clone());
    let p = at.pair(s, node.clone(), out_entry.clone());

    // ── the path is in `Q` and the label in `A` ─────────────────────────────
    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let k_child_bnd = syl(
        &k_child,
        &inst_all(
            paths_sub,
            &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), child.clone()],
        )?,
    )?;
    let (_, k_entry) = pair_parts(
        s,
        &at.w,
        &qa,
        &s.ap.apply(tf.clone(), tb.clone()),
        &entry,
        &k_child_bnd,
    )?;
    let (k_s, k_x) = pair_parts(s, &at.q, &at.a, &ts, &tx, &k_entry)?;
    let k_b_in_q = hyp_inst_mp(&hyp_inst_mp(&k_fibres, &ta, &k_a)?, &tb, &k_b)?;
    let k_path = {
        let two = hyp_inst(&hyp_inst(&k_pairing, &tb)?, &ts)?;
        hyp_mp(&two, &hyp_and(&k_b_in_q, &k_s)?)?
    };

    let k_node_w = node_in_w(wt, at, &k_closed, &k_a, &k_f, &ta, &tf)?;
    let k_out_entry = pair_in(s, &at.q, &at.a, &path, &tx, &k_path, &k_x)?;
    let k_bnd = pair_in(s, &at.w, &qa, &node, &out_entry, &k_node_w, &k_out_entry)?;

    // ── and of every closed `C ⊆ Bnd` ───────────────────────────────────────
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let g = Formula::and(
        kernel::thm::subset(env, tc.clone(), at.bnd.clone()),
        path_closed(env, s, at, &tc),
    );
    let m = Formula::and(k.clone(), g.clone());
    let m_k = and_left(k.clone(), g.clone());
    let m_g = and_right(k.clone(), g.clone());
    let (sub_c, closed_c) = split_and(&g)?;
    let m_closed_c = syl(&m_g, &and_right(sub_c, closed_c.clone()))?;
    let (root_c, step_c) = split_and(&closed_c)?;
    let m_step = syl(&m_closed_c, &and_right(root_c, step_c))?;

    // `paths ⊆ C` moves the premise into `C`.
    let ind_at = inst_all(
        paths_ind,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tc.clone()],
    )?;
    let m_sub = syl(&m_g, &ind_at)?;
    let m_child_c = hyp_inst_mp(&m_sub, &child, &syl(&m_k, &k_child)?)?;

    let m_a = syl(&m_k, &k_a)?;
    let m_f = syl(&m_k, &k_f)?;
    let m_b = syl(&m_k, &k_b)?;
    let m_in_c = {
        let mut cur = m_step;
        for t in [&ta, &tf, &tb, &ts, &tx] {
            cur = hyp_inst(&cur, t)?;
        }
        hyp_mp(
            &cur,
            &hyp_and(&hyp_and(&m_a, &m_f)?, &hyp_and(&m_b, &m_child_c)?)?,
        )?
    };
    if *m_in_c.concl() != Formula::imp(m, Formula::mem(p.clone(), tc.clone())) {
        return None
    }
    let k_cond = gen_under(
        cv,
        &k,
        &Formula::imp(g, Formula::mem(p.clone(), tc)),
        &crate::uncurry(&m_in_c)?,
    )?;

    let k_paths = into_paths(env, s, at, ps, paths_ax, &p, &k_bnd, &k_cond)?;
    let mut cur = crate::uncurry(&k_paths)?;
    for v in [xv, sv, bv2, fv, av2] {
        let (_, body) = cur.concl().as_imp()?;
        cur = gen_under(v, h, &body, &cur)?;
    }
    let want = path_step(env, s, at, ps);
    (*cur.concl() == Formula::imp(h.clone(), want)).then_some(cur)
}
