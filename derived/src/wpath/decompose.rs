//! **P3 at a node** — the two consequences of inversion that a consumer wants.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀Q. ((closed ∧ amb) →
//!       ∀a ∀f ∀x. (⟨⟨a,f⟩, ⟨∅,x⟩⟩ ∈ paths → x = a))              [root_label]
//!
//! ⊢ ∀A ∀B ∀u ∀Q. ((closed ∧ amb) →
//!       ∀a ∀f ∀b ∀s ∀x. (⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩ ∈ paths
//!                            → ⟨app(f,b), ⟨s,x⟩⟩ ∈ paths))     [step_premise]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What these say
//!
//! [`root_label`] is *"the label at the root of a tree is its own tag"* and
//! [`step_premise`] is *"a path that starts with `b` is a path in the `b`-th
//! subtree"*. Together they are the whole of what [`super::paths_injective`]
//! reads off a code, and they are the reason that proof is one induction rather
//! than an induction interleaved with two case analyses.
//!
//! # Both are one case analysis over [`super::path_arises`], and one branch dies
//!
//! Inversion hands back a disjunction, and in each theorem exactly one disjunct
//! survives. What kills the other is always the same fact — **a Kuratowski pair
//! is not `∅`** ([`super::shared::pair_not_empty`]): the root rule's path is
//! `∅` and the step rule's is `⟨b,s⟩`, so the two rules can never produce the
//! same entry. That single inequality is what makes the code readable at all; a
//! path encoding whose root marker were itself a pair would need a different
//! argument here, and there is no other place in this module where the *shape*
//! of the path terms is used.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funspace::discharge;
use crate::recursion::hyp::{hyp_eq_symm, hyp_eq_trans};
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    and_left, and_right, ex_falso, gen_all, hyp_or_elim, inst_all, syl, uncurry,
};

use super::condition::At;
use super::inversion::{
    arises_root, arises_step, root_inner, root_matrix, step_inner, step_matrix, step_matrix_b,
    step_matrix_f,
};
use super::shared::{gen_under, hyp_inst_mp, hyp_leibniz, pair_not_empty};

/// From `⊢ H → ⟨c,d⟩ = ⟨c′,d′⟩` infer `⊢ H → c = c′` and `⊢ H → d = d′`.
fn parts(
    sup_inj: &Thm,
    h_eq: &Thm,
    c: &Term,
    d: &Term,
    c2: &Term,
    d2: &Term,
) -> Option<(Thm, Thm)> {
    let at = inst_all(sup_inj, &[c.clone(), d.clone(), c2.clone(), d2.clone()])?;
    let both = syl(h_eq, &at)?;
    let (l, r) = (Formula::eq(c.clone(), c2.clone()), Formula::eq(d.clone(), d2.clone()));
    Some((syl(&both, &and_left(l.clone(), r.clone()))?, syl(&both, &and_right(l, r))?))
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

/// The shared preamble: the parameters, `H`, `paths` and inversion at `p`.
struct Setup {
    s: Sums,
    at: At,
    ps: Term,
    h: Formula,
    inv: Thm,
    sup_inj: Thm,
    ne: Thm,
    params: [FreeVar; 4],
}

impl Setup {
    fn new(env: &mut Env, wt: &Wtype, paths: FnSym, inversion: &Thm) -> Option<Setup> {
        if !inversion.hyps().is_empty() {
            return None
        }
        let s = wt.sums.clone();
        let (av, bv, uv, qv) =
            (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
        let ps =
            Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
        let closed = wt.closed_at(env, &at.a, &at.b, &at.u);
        let ambient = super::intro::amb(env, &s, &at);
        let h = Formula::and(closed, ambient);
        let inv = inst_all(
            inversion,
            &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()],
        )?;
        let ne = pair_not_empty(env, &s)?;
        Some(Setup {
            s,
            at,
            ps,
            h,
            inv,
            sup_inj: wt.sup_inj.clone(),
            ne,
            params: [av, bv, uv, qv],
        })
    }

    /// `⊢ (H ∧ p ∈ paths) → path_arises(p)`, with the two conjunct projections.
    fn arises_at(&self, env: &mut Env, p: &Term) -> Option<(Formula, Thm, Thm)> {
        let mem_p = Formula::mem(p.clone(), self.ps.clone());
        let k = Formula::and(self.h.clone(), mem_p.clone());
        let k_h = and_left(self.h.clone(), mem_p.clone());
        let k_p = and_right(self.h.clone(), mem_p);
        let arises = hyp_inst_mp(&syl(&k_h, &self.inv)?, p, &k_p)?;
        let _ = env;
        Some((k, arises, k_h))
    }
}

/// **`⊢ ⟨⟨a,f⟩, ⟨∅,x⟩⟩ ∈ paths → x = a`** — the root of a tree is labelled by
/// its own tag.
///
/// `inversion` must be [`super::paths_inversion`] over `paths`; it is checked
/// at its conclusion and for an empty hypothesis set.
pub fn root_label(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    inversion: &Thm,
) -> Option<Thm> {
    let st = Setup::new(env, wt, paths, inversion)?;
    let (s, at) = (st.s.clone(), st.at.clone());
    let (a2, f2, x2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tx) = (Term::var(a2), Term::var(f2), Term::var(x2));
    let node = at.pair(&s, ta.clone(), tf.clone());
    let entry = at.pair(&s, s.zero(), tx.clone());
    let p = at.pair(&s, node.clone(), entry.clone());
    let chi = Formula::eq(tx.clone(), ta.clone());

    let (k, k_arises, _) = st.arises_at(env, &p)?;

    // ── the root disjunct: the two nodes are the same, so the labels are ────
    let left = {
        let (wa, wf) = (env.fresh_var(), env.fresh_var());
        let (twa, twf) = (Term::var(wa), Term::var(wf));
        let disj = arises_root(env, &s, &at, &p);
        let k2 = Formula::and(k.clone(), disj.clone());
        let k2_ex = and_right(k.clone(), disj.clone());
        if Formula::exists(wa, root_matrix(&s, &at, &p, &twa, wf)) != disj {
            return None
        }

        let matrix = root_matrix(&s, &at, &p, &twa, wf);
        let l1 = Formula::and(k2.clone(), matrix.clone());
        let (m_a, m_exf) = split_and(&matrix)?;
        let l1_ex = syl(&and_right(k2.clone(), matrix.clone()), &and_right(m_a, m_exf))?;

        let inner = root_inner(&s, &at, &p, &twa, &twf);
        let l2 = Formula::and(l1.clone(), inner.clone());
        let (i_f, i_eq) = split_and(&inner)?;
        let l2_eq = syl(&and_right(l1.clone(), inner.clone()), &and_right(i_f, i_eq))?;

        let node2 = at.pair(&s, twa.clone(), twf.clone());
        let entry2 = at.pair(&s, s.zero(), twa.clone());
        let (l2_node, l2_entry) =
            parts(&st.sup_inj, &l2_eq, &node, &entry, &node2, &entry2)?;
        let (l2_a, _) = parts(&st.sup_inj, &l2_node, &ta, &tf, &twa, &twf)?;
        let (_, l2_x) = parts(&st.sup_inj, &l2_entry, &s.zero(), &tx, &s.zero(), &twa)?;
        let back = hyp_eq_symm(env, &l2_a)?;
        let l2_chi = hyp_eq_trans(env, &l2_x, &back)?;
        if *l2_chi.concl() != Formula::imp(l2, chi.clone()) {
            return None
        }

        let l1_chi = discharge(wf, &l1_ex, &l2_chi)?;
        uncurry(&discharge(wa, &k2_ex, &l1_chi)?)?
    };

    // ── the step disjunct: `⟨∅,x⟩` would be `⟨⟨b,s⟩,x′⟩`, and `∅` is no pair ─
    let right = step_branch_absurd(env, &st, &p, &node, &s.zero(), &tx, &chi)?;

    let out = hyp_or_elim(&k_arises, &left, &right)?;
    let mem_p = Formula::mem(p, st.ps.clone());
    if *out.concl() != Formula::imp(k, chi.clone()) {
        return None
    }
    close(env, &st, &uncurry(&out)?, &[x2, f2, a2], &Formula::imp(mem_p, chi))
}

/// **`⊢ ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩ ∈ paths → ⟨app(f,b), ⟨s,x⟩⟩ ∈ paths`** — a path
/// through `b` is a path in the `b`-th subtree.
pub fn step_premise(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    inversion: &Thm,
) -> Option<Thm> {
    let st = Setup::new(env, wt, paths, inversion)?;
    let (s, at) = (st.s.clone(), st.at.clone());
    let (a2, f2, b2, s2, x2) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tf, tb, ts, tx) =
        (Term::var(a2), Term::var(f2), Term::var(b2), Term::var(s2), Term::var(x2));
    let node = at.pair(&s, ta.clone(), tf.clone());
    let path = at.pair(&s, tb.clone(), ts.clone());
    let entry = at.pair(&s, path.clone(), tx.clone());
    let p = at.pair(&s, node.clone(), entry.clone());
    let chi = Formula::mem(
        at.pair(
            &s,
            s.ap.apply(tf.clone(), tb.clone()),
            at.pair(&s, ts.clone(), tx.clone()),
        ),
        st.ps.clone(),
    );

    let (k, k_arises, _) = st.arises_at(env, &p)?;

    // ── the root disjunct: `⟨b,s⟩` would be `∅` ─────────────────────────────
    let left = {
        let (wa, wf) = (env.fresh_var(), env.fresh_var());
        let (twa, twf) = (Term::var(wa), Term::var(wf));
        let disj = arises_root(env, &s, &at, &p);
        let k2 = Formula::and(k.clone(), disj.clone());
        let k2_ex = and_right(k.clone(), disj.clone());
        if Formula::exists(wa, root_matrix(&s, &at, &p, &twa, wf)) != disj {
            return None
        }
        let matrix = root_matrix(&s, &at, &p, &twa, wf);
        let l1 = Formula::and(k2.clone(), matrix.clone());
        let (m_a, m_exf) = split_and(&matrix)?;
        let l1_ex = syl(&and_right(k2.clone(), matrix.clone()), &and_right(m_a, m_exf))?;

        let inner = root_inner(&s, &at, &p, &twa, &twf);
        let (i_f, i_eq) = split_and(&inner)?;
        let l2_eq = syl(&and_right(l1.clone(), inner.clone()), &and_right(i_f, i_eq))?;
        let node2 = at.pair(&s, twa.clone(), twf.clone());
        let entry2 = at.pair(&s, s.zero(), twa.clone());
        let (_, l2_entry) = parts(&st.sup_inj, &l2_eq, &node, &entry, &node2, &entry2)?;
        let (l2_path, _) = parts(&st.sup_inj, &l2_entry, &path, &tx, &s.zero(), &twa)?;
        let l2_chi = syl(
            &syl(&l2_path, &inst_all(&st.ne, &[tb.clone(), ts.clone()])?)?,
            &ex_falso(chi.clone()),
        )?;
        let l1_chi = discharge(wf, &l1_ex, &l2_chi)?;
        uncurry(&discharge(wa, &k2_ex, &l1_chi)?)?
    };

    // ── the step disjunct: the five components agree, so the premise moves ──
    let right = {
        let (wa, wf, wb, ws, wx) = (
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
        );
        let (twa, twf, twb, tws, twx) =
            (Term::var(wa), Term::var(wf), Term::var(wb), Term::var(ws), Term::var(wx));
        let disj = arises_step(env, &s, &at, &st.ps, &p);
        let k2 = Formula::and(k.clone(), disj.clone());
        let k2_ex = and_right(k.clone(), disj.clone());
        if Formula::exists(wa, step_matrix(&s, &at, &st.ps, &p, &twa, wf, wb, ws, wx)) != disj {
            return None
        }

        // Peel the five binders, keeping the hypothesis chain.
        let m_a = step_matrix(&s, &at, &st.ps, &p, &twa, wf, wb, ws, wx);
        let l1 = Formula::and(k2.clone(), m_a.clone());
        let (pa, exf) = split_and(&m_a)?;
        let l1_ex = syl(&and_right(k2.clone(), m_a.clone()), &and_right(pa, exf))?;

        let m_f = step_matrix_f(&s, &at, &st.ps, &p, &twa, &twf, wb, ws, wx);
        let l2 = Formula::and(l1.clone(), m_f.clone());
        let (pf, exb) = split_and(&m_f)?;
        let l2_ex = syl(&and_right(l1.clone(), m_f.clone()), &and_right(pf, exb))?;

        let m_b = step_matrix_b(&s, &at, &st.ps, &p, &twa, &twf, &twb, ws, wx);
        let l3 = Formula::and(l2.clone(), m_b.clone());
        let (pb, exs) = split_and(&m_b)?;
        let l3_ex = syl(&and_right(l2.clone(), m_b.clone()), &and_right(pb, exs))?;

        let inner_s = Formula::exists(
            wx,
            step_inner(&s, &at, &st.ps, &p, &twa, &twf, &twb, &tws, &twx),
        );
        let l4 = Formula::and(l3.clone(), inner_s.clone());
        let l4_ex = and_right(l3.clone(), inner_s.clone());

        let inner = step_inner(&s, &at, &st.ps, &p, &twa, &twf, &twb, &tws, &twx);
        let l5 = Formula::and(l4.clone(), inner.clone());
        let (i_mem, i_eq) = split_and(&inner)?;
        let l5_in = syl(&and_right(l4.clone(), inner.clone()), &and_left(i_mem.clone(), i_eq.clone()))?;
        let l5_eq = syl(&and_right(l4.clone(), inner.clone()), &and_right(i_mem, i_eq))?;

        // The five component equations.
        let node2 = at.pair(&s, twa.clone(), twf.clone());
        let path2 = at.pair(&s, twb.clone(), tws.clone());
        let entry2 = at.pair(&s, path2.clone(), twx.clone());
        let (l5_node, l5_entry) =
            parts(&st.sup_inj, &l5_eq, &node, &entry, &node2, &entry2)?;
        let (_, l5_f) = parts(&st.sup_inj, &l5_node, &ta, &tf, &twa, &twf)?;
        let (l5_path, l5_x) = parts(&st.sup_inj, &l5_entry, &path, &tx, &path2, &twx)?;
        let (l5_b, l5_s) = parts(&st.sup_inj, &l5_path, &tb, &ts, &twb, &tws)?;

        // Rewrite the premise's four components back to the caller's terms.
        let mut cur = l5_in;
        for (h_eq, hole_at) in [
            (&l5_f, 0usize),
            (&l5_b, 1),
            (&l5_s, 2),
            (&l5_x, 3),
        ] {
            let back = hyp_eq_symm(env, h_eq)?;
            let hole = env.fresh_var();
            let th = Term::var(hole);
            let (rf, rb, rs, rx) = match hole_at {
                0 => (th.clone(), twb.clone(), tws.clone(), twx.clone()),
                1 => (tf.clone(), th.clone(), tws.clone(), twx.clone()),
                2 => (tf.clone(), tb.clone(), th.clone(), twx.clone()),
                _ => (tf.clone(), tb.clone(), ts.clone(), th.clone()),
            };
            let body = Formula::mem(
                at.pair(&s, s.ap.apply(rf, rb), at.pair(&s, rs, rx)),
                st.ps.clone(),
            );
            cur = crate::hyp_mp(&hyp_leibniz(&back, hole, &body)?, &cur)?;
        }
        if *cur.concl() != Formula::imp(l5, chi.clone()) {
            return None
        }

        let l4_chi = discharge(wx, &l4_ex, &cur)?;
        let l3_chi = discharge(ws, &l3_ex, &l4_chi)?;
        let l2_chi = discharge(wb, &l2_ex, &l3_chi)?;
        let l1_chi = discharge(wf, &l1_ex, &l2_chi)?;
        uncurry(&discharge(wa, &k2_ex, &l1_chi)?)?
    };

    let out = hyp_or_elim(&k_arises, &left, &right)?;
    let mem_p = Formula::mem(p, st.ps.clone());
    if *out.concl() != Formula::imp(k, chi.clone()) {
        return None
    }
    close(env, &st, &uncurry(&out)?, &[x2, s2, b2, f2, a2], &Formula::imp(mem_p, chi))
}

/// The step disjunct, in the theorem where it is absurd: the entry `⟨∅,x⟩`
/// would have to be `⟨⟨b,s⟩,x′⟩`, and `∅` is not a pair.
#[allow(clippy::too_many_arguments)]
fn step_branch_absurd(
    env: &mut Env,
    st: &Setup,
    p: &Term,
    node: &Term,
    e1: &Term,
    e2: &Term,
    chi: &Formula,
) -> Option<Thm> {
    let (s, at) = (st.s.clone(), st.at.clone());
    let (wa, wf, wb, ws, wx) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (twa, twf, twb, tws, twx) =
        (Term::var(wa), Term::var(wf), Term::var(wb), Term::var(ws), Term::var(wx));
    let mem_p = Formula::mem(p.clone(), st.ps.clone());
    let k = Formula::and(st.h.clone(), mem_p);
    let disj = arises_step(env, &s, &at, &st.ps, p);
    let k2 = Formula::and(k.clone(), disj.clone());
    let k2_ex = and_right(k, disj.clone());
    if Formula::exists(wa, step_matrix(&s, &at, &st.ps, p, &twa, wf, wb, ws, wx)) != disj {
        return None
    }

    let m_a = step_matrix(&s, &at, &st.ps, p, &twa, wf, wb, ws, wx);
    let l1 = Formula::and(k2.clone(), m_a.clone());
    let (pa, exf) = split_and(&m_a)?;
    let l1_ex = syl(&and_right(k2.clone(), m_a.clone()), &and_right(pa, exf))?;

    let m_f = step_matrix_f(&s, &at, &st.ps, p, &twa, &twf, wb, ws, wx);
    let l2 = Formula::and(l1.clone(), m_f.clone());
    let (pf, exb) = split_and(&m_f)?;
    let l2_ex = syl(&and_right(l1.clone(), m_f.clone()), &and_right(pf, exb))?;

    let m_b = step_matrix_b(&s, &at, &st.ps, p, &twa, &twf, &twb, ws, wx);
    let l3 = Formula::and(l2.clone(), m_b.clone());
    let (pb, exs) = split_and(&m_b)?;
    let l3_ex = syl(&and_right(l2.clone(), m_b.clone()), &and_right(pb, exs))?;

    let inner_s =
        Formula::exists(wx, step_inner(&s, &at, &st.ps, p, &twa, &twf, &twb, &tws, &twx));
    let l4 = Formula::and(l3.clone(), inner_s.clone());
    let l4_ex = and_right(l3.clone(), inner_s.clone());

    let inner = step_inner(&s, &at, &st.ps, p, &twa, &twf, &twb, &tws, &twx);
    let (i_mem, i_eq) = split_and(&inner)?;
    let l5_eq = syl(&and_right(l4.clone(), inner.clone()), &and_right(i_mem, i_eq))?;

    let node2 = at.pair(&s, twa.clone(), twf.clone());
    let path2 = at.pair(&s, twb.clone(), tws.clone());
    let entry2 = at.pair(&s, path2.clone(), twx.clone());
    let entry = at.pair(&s, e1.clone(), e2.clone());
    let (_, l5_entry) = parts(&st.sup_inj, &l5_eq, node, &entry, &node2, &entry2)?;
    // `⟨∅,x⟩ = ⟨⟨b,s⟩,x′⟩` gives `∅ = ⟨b,s⟩`, which `pair_not_empty` refuses.
    let (zero_eq, _) = parts(&st.sup_inj, &l5_entry, e1, e2, &path2, &twx)?;
    let flip = hyp_eq_symm(env, &zero_eq)?;
    let bottom = syl(&flip, &inst_all(&st.ne, &[twb.clone(), tws.clone()])?)?;
    let l5_chi = syl(&bottom, &ex_falso(chi.clone()))?;

    let l4_chi = discharge(wx, &l4_ex, &l5_chi)?;
    let l3_chi = discharge(ws, &l3_ex, &l4_chi)?;
    let l2_chi = discharge(wb, &l2_ex, &l3_chi)?;
    let l1_chi = discharge(wf, &l1_ex, &l2_chi)?;
    uncurry(&discharge(wa, &k2_ex, &l1_chi)?)
}

/// Quantify the finished implication over its own variables and over the four
/// parameters.
fn close(
    env: &mut Env,
    st: &Setup,
    thm: &Thm,
    vars: &[FreeVar],
    body: &Formula,
) -> Option<Thm> {
    let _ = env;
    let mut cur = thm.clone();
    let mut b = body.clone();
    for v in vars {
        cur = gen_under(*v, &st.h, &b, &cur)?;
        b = cur.concl().as_imp()?.1;
    }
    Some(gen_all(&st.params, &cur))
}
