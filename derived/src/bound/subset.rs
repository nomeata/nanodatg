//! **Step 2** — a function into a universe is a *subset* of it.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ⊆ u)
//!                                                    [funspace_subset_universe]
//! ⊢ ∀x ∀u ∀f ∀p. (f ∈ fs(x,u) → (p ∈ f → ∃q ∃r. (q ∈ x ∧ (r ∈ u ∧ p = ⟨q,r⟩))))
//!                                                              [funspace_pairs]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Where `C₁` is spent
//!
//! [`funspace_pairs`] is pure bookkeeping: `f ∈ fs(x,u)` gives `f ⊆ prod(x,u)`,
//! and the product's membership condition names the two components. The content
//! is in [`funspace_subset_universe`], and it is exactly one use of `ax_tarski`'s
//! **`C₁`** (transitivity, added 2026-07-31): a member of `f` is a pair `⟨q,r⟩`
//! with `q ∈ x ∈ u` and `r ∈ u`, and without `C₁` there is nothing putting `q`
//! into `u`. Countermodel B at the end of [`crate::universe`] refutes the
//! statement under the older four-clause axiom, so this is the one place in the
//! chain where the new clause is load-bearing.
//!
//! With both components in `u`, [`super::universe_opair`] closes it.

use kernel::{Env, Formula, Term, Thm};
use crate::sums::Sums;
use crate::universe::is_universe;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, opair,
    syl, uncurry,
};

use super::shared::{hyp_inst_mp, hyp_leibniz, open_exists, split_and};

/// `⊢ ∀x ∀u ∀f. (f ∈ fs(x,u) → ∀p. (p ∈ f → ∃q. (q ∈ x ∧ ∃r. (r ∈ u ∧ p = ⟨q,r⟩))))`
/// — a function is a set of ordered pairs, with its components where they
/// belong.
///
/// Nothing about universes: this is the first conjunct of `isfun`
/// (`f ⊆ prod(x,u)`) followed by the membership condition of the product, and
/// it is what both [`funspace_subset_universe`] and [`crate::bound::funspace_mem_universe`]
/// read `f` apart with.
pub fn funspace_pairs(env: &mut Env, s: &Sums) -> Option<Thm> {
    let up = s.ap.sets.up;
    let (xv, uv, fv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tu, tf, tp) = (Term::var(xv), Term::var(uv), Term::var(fv), Term::var(pv));

    let h = Formula::mem(tf.clone(), s.fs.of(tx.clone(), tu.clone()));
    let fs_at = inst_all(&s.fs.fs_ax, &[tx.clone(), tu.clone(), tf.clone()])?;
    let to_isfun = iff_mp(&fs_at)?;
    if to_isfun.concl().as_imp()?.0 != h {
        return None
    }
    let isfun = to_isfun.concl().as_imp()?.1;
    let (sub_prod, graph) = split_and(&isfun)?;
    let prod_t = s.prod.of(tx.clone(), tu.clone());
    if sub_prod != kernel::thm::subset(env, tf.clone(), prod_t) {
        return None
    }
    let h_sub = syl(&to_isfun, &and_left(sub_prod, graph))?;

    // `L := H ∧ p ∈ f`, and the product's membership condition read off.
    let p_in_f = Formula::mem(tp.clone(), tf.clone());
    let l_h = and_left(h.clone(), p_in_f.clone());
    let l_p = and_right(h.clone(), p_in_f.clone());
    let l_in_prod = hyp_inst_mp(&syl(&l_h, &h_sub)?, &tp, &l_p)?;
    let prod_at = inst_all(&s.prod.prod_ax, &[tx.clone(), tu.clone(), tp.clone()])?;
    let l_ex = syl(&l_in_prod, &iff_mp(&prod_at)?)?;
    let ex_outer = l_ex.concl().as_imp()?.1;

    // The shape is checked against a hand-built copy, so a caller reading the
    // statement off this documentation is reading the truth.
    let (qv, rv) = (env.fresh_var(), env.fresh_var());
    let (tq, tr) = (Term::var(qv), Term::var(rv));
    let want = Formula::exists(
        qv,
        Formula::and(
            Formula::mem(tq.clone(), tx.clone()),
            Formula::exists(
                rv,
                Formula::and(
                    Formula::mem(tr.clone(), tu.clone()),
                    Formula::eq(tp.clone(), opair(up, tq, tr)),
                ),
            ),
        ),
    );
    if ex_outer != want {
        return None
    }

    let out = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::imp(p_in_f.clone(), ex_outer.clone()))?,
        &Thm::gen(pv, &uncurry(&l_ex)?),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::forall(pv, Formula::imp(p_in_f, ex_outer))),
        "funspace_pairs: wrong shape"
    );
    Some(gen_all(&[xv, uv, fv], &out))
}

/// [`funspace_pairs`] at `x`, `u` and `f`, with its statement rebuilt and
/// compared — so a caller that hands over some other theorem gets a rejection.
pub(super) fn funspace_pairs_at(
    env: &mut Env,
    pairs: &Thm,
    s: &Sums,
    x: &Term,
    u: &Term,
    f: &Term,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let inst = inst_all(pairs, &[x.clone(), u.clone(), f.clone()])?;
    let (pv, qv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tr) = (Term::var(pv), Term::var(qv), Term::var(rv));
    let ex = Formula::exists(
        qv,
        Formula::and(
            Formula::mem(tq.clone(), x.clone()),
            Formula::exists(
                rv,
                Formula::and(
                    Formula::mem(tr.clone(), u.clone()),
                    Formula::eq(tp.clone(), opair(up, tq, tr)),
                ),
            ),
        ),
    );
    let want = Formula::imp(
        Formula::mem(f.clone(), s.fs.of(x.clone(), u.clone())),
        Formula::forall(pv, Formula::imp(Formula::mem(tp, f.clone()), ex)),
    );
    if *inst.concl() != want {
        return None
    }
    Some(inst)
}

/// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ⊆ u)`.
///
/// A member `p` of `f` lies in `prod(x,u)`, so it is `⟨q,r⟩` with `q ∈ x` and
/// `r ∈ u`. `q ∈ u` because `x ∈ u` and `u` is transitive — `C₁`, via
/// `mem_mem` — and then `⟨q,r⟩ ∈ u` by [`crate::bound::universe_opair`]. Without `C₁` the
/// statement is false: countermodel B at the end of [`crate::universe`] has a
/// member `{ω}` of `M` whose own member `ω` is not in `M`.
///
/// `mem_mem` must be [`crate::universe::universe_mem_mem`] and `pair` the
/// output of [`crate::bound::universe_opair`]; both statements are rebuilt and compared.
pub fn funspace_subset_universe(
    env: &mut Env,
    s: &Sums,
    pairs: &Thm,
    mem_mem: &Thm,
    pair: &Thm,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let (uv, xv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tx, tf) = (Term::var(uv), Term::var(xv), Term::var(fv));

    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let f_in_fs = Formula::mem(tf.clone(), s.fs.of(tx.clone(), tu.clone()));
    let mems = Formula::and(x_in_u.clone(), f_in_fs.clone());
    let h = Formula::and(univ_u.clone(), mems.clone());

    let h_univ = and_left(univ_u.clone(), mems.clone());
    let h_mems = and_right(univ_u, mems);
    let h_x = syl(&h_mems, &and_left(x_in_u, f_in_fs.clone()))?;
    let h_f = syl(&h_mems, &and_right(Formula::mem(tx.clone(), tu.clone()), f_in_fs))?;

    // ── Every member of `f` is a pair, by [`funspace_pairs`] ─────────────────
    let pairs_at = funspace_pairs_at(env, pairs, s, &tx, &tu, &tf)?;
    let h_pairs = syl(&h_f, &pairs_at)?;

    // ── `L := H ∧ p ∈ f` ─────────────────────────────────────────────────────
    let pv = env.fresh_var();
    let tp = Term::var(pv);
    let p_in_f = Formula::mem(tp.clone(), tf.clone());
    let p_in_u = Formula::mem(tp.clone(), tu.clone());
    let l = Formula::and(h.clone(), p_in_f.clone());
    let l_h = and_left(h.clone(), p_in_f.clone());
    let l_p = and_right(h.clone(), p_in_f.clone());

    let l_ex = hyp_inst_mp(&syl(&l_h, &h_pairs)?, &tp, &l_p)?;
    let ex_outer = l_ex.concl().as_imp()?.1;

    // ── Open both existentials ──────────────────────────────────────────────
    let (qv, rv) = (env.fresh_var(), env.fresh_var());
    let (tq, tr) = (Term::var(qv), Term::var(rv));
    let e1 = open_exists(&ex_outer, &tq)?;
    let m = Formula::and(l.clone(), e1.clone());
    let m_l = and_left(l.clone(), e1.clone());
    let m_e1 = and_right(l.clone(), e1.clone());
    let (q_in_x, ex_inner) = split_and(&e1)?;
    let m_q = syl(&m_e1, &and_left(q_in_x.clone(), ex_inner.clone()))?;
    let m_ex = syl(&m_e1, &and_right(q_in_x, ex_inner.clone()))?;

    let e2 = open_exists(&ex_inner, &tr)?;
    let n = Formula::and(m.clone(), e2.clone());
    let n_m = and_left(m.clone(), e2.clone());
    let n_e2 = and_right(m.clone(), e2.clone());
    let (r_in_u, p_eq) = split_and(&e2)?;
    if p_eq != Formula::eq(tp.clone(), opair(up, tq.clone(), tr.clone())) {
        return None
    }
    let n_r = syl(&n_e2, &and_left(r_in_u.clone(), p_eq.clone()))?;
    let n_eq = syl(&n_e2, &and_right(r_in_u, p_eq))?;

    // ── `q ∈ u` by `C₁`, then `⟨q,r⟩ ∈ u`, then `p ∈ u` ──────────────────────
    let n_l = syl(&n_m, &m_l)?;
    let n_h = syl(&n_l, &l_h)?;
    let n_univ = syl(&n_h, &h_univ)?;
    let n_x = syl(&n_h, &h_x)?;
    let n_q = syl(&n_m, &m_q)?;

    let mm_at = inst_all(mem_mem, &[tu.clone(), tx.clone(), tq.clone()])?;
    if *mm_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(tx.clone(), tu.clone()),
                    Formula::mem(tq.clone(), tx.clone()),
                ),
            ),
            Formula::mem(tq.clone(), tu.clone()),
        )
    {
        return None
    }
    let n_q_u = hyp_mp(&a1i(&mm_at, n.clone()), &hyp_and(&n_univ, &hyp_and(&n_x, &n_q)?)?)?;

    let pair_at = inst_all(pair, &[tu.clone(), tq.clone(), tr.clone()])?;
    let kur = opair(up, tq.clone(), tr.clone());
    if *pair_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(tq.clone(), tu.clone()),
                    Formula::mem(tr.clone(), tu.clone()),
                ),
            ),
            Formula::mem(kur.clone(), tu.clone()),
        )
    {
        return None
    }
    let n_kur = hyp_mp(&a1i(&pair_at, n.clone()), &hyp_and(&n_univ, &hyp_and(&n_q_u, &n_r)?)?)?;

    let w = env.fresh_var();
    let n_eq_sym = syl(&n_eq, &eq_symm_imp(env, tp.clone(), kur))?;
    let n_p_u =
        hyp_mp(&hyp_leibniz(&n_eq_sym, w, &Formula::mem(Term::var(w), tu.clone()))?, &n_kur)?;
    debug_assert_eq!(*n_p_u.concl(), Formula::imp(n, p_in_u.clone()), "the pair is not `p`");

    // ── Discharge the two witnesses, then generalise over `p` ────────────────
    let m_goal = crate::funspace::discharge(rv, &m_ex, &n_p_u)?;
    let l_goal = crate::funspace::discharge(qv, &l_ex, &m_goal)?;
    let out = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::imp(p_in_f, p_in_u))?,
        &Thm::gen(pv, &uncurry(&l_goal)?),
    )?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, tf, tu)),
        "funspace_subset_universe: wrong shape"
    );
    Some(gen_all(&[uv, xv, fv], &out))
}
