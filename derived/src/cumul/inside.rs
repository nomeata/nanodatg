//! **The tower inside a universe** — steps (c) and (e) of the route in
//! [`crate::cumul`].
//!
//! # Interface
//!
//! Writing `S` for the seed, `Vₙ` for `app(iter(S),n)`, `T` for `tower(S)` and
//! `U(c)` for [`crate::universe::least_universe`], [`Inside`] carries
//!
//! ```text
//! ⊢ ∀n. (n ∈ ω → ⟨n, Vₙ⟩ ∈ iter(S))                     [Inside::graph_pair]
//! ⊢ ∀c. (S ∈ U(c) → T ⊆ U(c))                           [Inside::tower_subset]
//! ⊢ ∀c. (S ∈ U(c) → iter(S) ∈ fs(ω, U(c)))              [Inside::iter_in_fs]
//! ⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))              [Inside::tower_mem]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # `ω ∈ U(c)` is spent once, and this is where
//!
//! [`Inside::tower_subset`] is free: a member of `T` is a member of some `Vₙ`,
//! every `Vₙ` is a member of `U(c)` ([`super::stages_in_universe`]), and `U(c)`
//! is transitive. It says nothing about size.
//!
//! [`Inside::tower_mem`] is the size statement, and `T` is a union of `ω`-many
//! members of `U(c)`, which is a member only if `ω` itself is small enough. The
//! route:
//!
//! ```text
//! iter(S) ∈ fs(ω, U(c))                R1–R3 of crate::recursion::rec_fn
//! iter(S) ∈ U(c)                       crate::bound::least_universe_funspace_mem
//!                                         — the ONLY use of `ω ∈ U(c)`
//! ⋃⋃⋃iter(S) ∈ U(c)                    three ⋃-closures
//! T ⊆ ⋃⋃⋃iter(S)                       crate::funcs::snd_in_union2
//! T ∈ U(c)                             C₂, "a subset of a member is a member"
//! ```
//!
//! No Replacement instance and no image symbol: `iter(S)` is *already* the set
//! of pairs `⟨n,Vₙ⟩`, so `Vₙ ∈ ⋃⋃iter(S)` is [`crate::funcs::snd_in_union2`]
//! and one more `⋃` reaches the members of the stages. This is what the closing
//! note of [`crate::cumul`] predicted, and it went through as predicted.
//!
//! # The one lemma that had to be added
//!
//! [`Inside::graph_pair`] — `⟨n, Vₙ⟩ ∈ iter(S)`. The recursion theorem states
//! totality as `∀n ∈ ω. ∃b. ⟨n,b⟩ ∈ iter(S)` (R3) and the value as
//! `app(iter(S),n)`, and nothing in [`crate::recursion`] connects the two in
//! this direction. Single-valuedness (R2) plus
//! [`crate::recursion::Rec::app_of_graph`] does it in five lines, and both
//! [`Inside::iter_in_fs`] and the `T ⊆ ⋃⋃⋃iter(S)` step consume it.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{snd_in_union2, union_intro};
use crate::funspace::discharge;
use crate::recursion::Rec;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl,
};

use super::stages::Stages;
use super::step::curry;

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])`.
fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// The tower's relation to a universe holding the seed.
pub struct Inside {
    /// `⊢ ∀n. (n ∈ ω → ⟨n, Vₙ⟩ ∈ iter(S))`.
    pub graph_pair: Thm,
    /// `⊢ ∀c. (S ∈ U(c) → ∀z. (z ∈ T → z ∈ U(c)))` — **step (c)**.
    pub tower_subset: Thm,
    /// `⊢ ∀c. (S ∈ U(c) → iter(S) ∈ fs(ω, U(c)))`.
    pub iter_in_fs: Thm,
    /// `⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))` — **step (e)**.
    pub tower_mem: Thm,
}

impl Inside {
    /// Derive all four.
    ///
    /// `stages_in_universe` must be [`super::stages_in_universe`],
    /// `transitive`, `union` and `sub` the `∀c` forms of `C₁`, `⋃`-closure and
    /// `C₂` at the same `lu`, and `fs_mem` must be
    /// [`crate::bound::least_universe_funspace_mem`].
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        r: &Rec,
        s: &Sums,
        st: &Stages,
        lu: FnSym,
        stages_in_universe: &Thm,
        transitive: &Thm,
        union: &Thm,
        sub: &Thm,
        fs_mem: &Thm,
    ) -> Option<Inside> {
        let graph_pair = graph_pair(env, r, st)?;
        let tower_subset = tower_subset(env, r, st, lu, stages_in_universe, transitive)?;
        let iter_in_fs = iter_in_fs(env, r, s, st, lu, stages_in_universe, &graph_pair)?;
        let tower_mem =
            tower_mem(env, r, s, st, lu, &iter_in_fs, &graph_pair, union, sub, fs_mem)?;
        Some(Inside { graph_pair, tower_subset, iter_in_fs, tower_mem })
    }
}

/// `⊢ ∀n. (n ∈ ω → ⟨n, Vₙ⟩ ∈ iter(S))` — the graph contains its own values.
///
/// R3 gives *some* `b` with `⟨n,b⟩ ∈ iter(S)`; R2 and
/// [`crate::recursion::Rec::app_of_graph`] identify it as `app(iter(S),n)`.
pub fn graph_pair(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let it = st.rec.set();
    let single = Thm::mp(&st.rec.spec.proj(1)?, &st.rec.iter_ax)?;
    let total = Thm::mp(&st.rec.spec.proj(2)?, &st.rec.iter_ax)?;

    let (nv, bv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, tb, tz) = (Term::var(nv), Term::var(bv), Term::var(zv));
    let vn = st.v(r, tn.clone());
    let n_om = Formula::mem(tn.clone(), r.omega());

    let h_ex = inst_all(&total, std::slice::from_ref(&tn))?;
    let pair_nb = Formula::mem(r.pair(tn.clone(), tb.clone()), it.clone());
    if *h_ex.concl() != Formula::imp(n_om.clone(), Formula::exists(bv, pair_nb.clone())) {
        return None
    }

    let j = Formula::and(n_om.clone(), pair_nb.clone());
    let j_pair = and_right(n_om.clone(), pair_nb.clone());
    let aog = inst_all(&r.app_of_graph, &[it.clone(), tn.clone(), tb.clone()])?;
    let j_eq = hyp_mp(
        &hyp_mp(&a1i(&curry(&aog)?, j.clone()), &a1i(&single, j.clone()))?,
        &j_pair,
    )?;
    let j_eq_s = syl(&j_eq, &eq_symm_imp(env, vn.clone(), tb.clone()))?;
    let goal = Formula::mem(r.pair(tn.clone(), vn.clone()), it.clone());
    let j_goal = hyp_mp(
        &hyp_leibniz(&j_eq_s, zv, &Formula::mem(r.pair(tn.clone(), tz), it))?,
        &j_pair,
    )?;
    if *j_goal.concl() != Formula::imp(j, goal.clone()) {
        return None
    }
    let out = discharge(bv, &h_ex, &j_goal)?;
    if *out.concl() != Formula::imp(n_om, goal) {
        return None
    }
    Some(Thm::gen(nv, &out))
}

/// `⊢ ∀c. (S ∈ U(c) → ∀z. (z ∈ T → z ∈ U(c)))` — **step (c)**.
fn tower_subset(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    lu: FnSym,
    stages_in_universe: &Thm,
    transitive: &Thm,
) -> Option<Thm> {
    let (cv, zv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tz, tn) = (Term::var(cv), Term::var(zv), Term::var(nv));
    let u = Term::apply(lu, vec![tc.clone()]);
    let tower = st.tower_set();
    let vn = st.v(r, tn.clone());

    let h = Formula::mem(Term::var(st.seed), u.clone());
    let z_t = Formula::mem(tz.clone(), tower.clone());
    let j1 = Formula::and(h.clone(), z_t.clone());
    let j1_h = and_left(h.clone(), z_t.clone());
    let j1_z = and_right(h.clone(), z_t.clone());

    let members = inst_all(&st.tower.members, std::slice::from_ref(&tz))?;
    let j1_ex = hyp_mp(&a1i(&iff_mp(&members)?, j1.clone()), &j1_z)?;

    let body = Formula::and(
        Formula::mem(tn.clone(), r.omega()),
        Formula::mem(tz.clone(), vn.clone()),
    );
    if *j1_ex.concl() != Formula::imp(j1.clone(), Formula::exists(nv, body.clone())) {
        return None
    }

    let j2 = Formula::and(j1.clone(), body.clone());
    let j2_j1 = and_left(j1.clone(), body.clone());
    let j2_body = and_right(j1.clone(), body.clone());
    let j2_n = syl(
        &j2_body,
        &and_left(
            Formula::mem(tn.clone(), r.omega()),
            Formula::mem(tz.clone(), vn.clone()),
        ),
    )?;
    let j2_zv = syl(
        &j2_body,
        &and_right(Formula::mem(tn.clone(), r.omega()), Formula::mem(tz.clone(), vn.clone())),
    )?;
    let siu = inst_all(stages_in_universe, &[tc.clone(), tn.clone()])?;
    let j2_vn = hyp_mp(
        &hyp_mp(&a1i(&siu, j2.clone()), &j2_n)?,
        &syl(&j2_j1, &j1_h)?,
    )?;
    let trans_at = inst_all(transitive, &[tc.clone(), vn.clone()])?;
    let j2_goal = hyp_mp(
        &hyp_inst(&hyp_mp(&a1i(&trans_at, j2.clone()), &j2_vn)?, std::slice::from_ref(&tz))?,
        &j2_zv,
    )?;

    let j1_goal = discharge(nv, &j1_ex, &j2_goal)?;
    let out = Thm::mp(
        &Thm::ax_dist(zv, h.clone(), Formula::imp(z_t, Formula::mem(tz, u.clone())))?,
        &Thm::gen(zv, &curry(&j1_goal)?),
    )?;
    if *out.concl() != Formula::imp(h, kernel::thm::subset(env, tower, u)) {
        return None
    }
    Some(Thm::gen(cv, &out))
}

/// `⊢ ∀c. (S ∈ U(c) → iter(S) ∈ fs(ω, U(c)))`.
fn iter_in_fs(
    env: &mut Env,
    r: &Rec,
    s: &Sums,
    st: &Stages,
    lu: FnSym,
    stages_in_universe: &Thm,
    graph_pair: &Thm,
) -> Option<Thm> {
    let it = st.rec.set();
    let om = r.omega();
    let single = Thm::mp(&st.rec.spec.proj(1)?, &st.rec.iter_ax)?;
    let pairs = Thm::mp(&st.rec.spec.proj(0)?, &st.rec.iter_ax)?;

    let (cv, pv, av, bv, xv, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tc, tp, ta, tb) = (Term::var(cv), Term::var(pv), Term::var(av), Term::var(bv));
    let (tx, tz) = (Term::var(xv), Term::var(zv));
    let u = Term::apply(lu, vec![tc.clone()]);
    let h = Formula::mem(Term::var(st.seed), u.clone());

    // ── R1 plus `b = Vₐ`: every member of the graph is in `prod(ω, U(c))` ────
    let p_it = Formula::mem(tp.clone(), it.clone());
    let k1 = Formula::and(h.clone(), p_it.clone());
    let k1_h = and_left(h.clone(), p_it.clone());
    let k1_p = and_right(h.clone(), p_it.clone());
    let k1_ex = hyp_mp(
        &a1i(&inst_all(&pairs, std::slice::from_ref(&tp))?, k1.clone()),
        &k1_p,
    )?;

    let eq_p = Formula::eq(tp.clone(), r.pair(ta.clone(), tb.clone()));
    let inner = Formula::and(Formula::mem(ta.clone(), om.clone()), Formula::exists(bv, eq_p.clone()));
    if *k1_ex.concl() != Formula::imp(k1.clone(), Formula::exists(av, inner.clone())) {
        return None
    }

    let k2 = Formula::and(k1.clone(), inner.clone());
    let k2_k1 = and_left(k1.clone(), inner.clone());
    let k2_inner = and_right(k1.clone(), inner.clone());
    let k2_a = syl(
        &k2_inner,
        &and_left(Formula::mem(ta.clone(), om.clone()), Formula::exists(bv, eq_p.clone())),
    )?;
    let k2_ex_b = syl(
        &k2_inner,
        &and_right(Formula::mem(ta.clone(), om.clone()), Formula::exists(bv, eq_p.clone())),
    )?;

    let k3 = Formula::and(k2.clone(), eq_p.clone());
    let k3_k2 = and_left(k2.clone(), eq_p.clone());
    let k3_eq = and_right(k2.clone(), eq_p.clone());
    let k3_p = syl(&k3_k2, &syl(&k2_k1, &k1_p)?)?;
    let k3_a = syl(&k3_k2, &k2_a)?;
    let k3_h = syl(&k3_k2, &syl(&k2_k1, &k1_h)?)?;

    // `⟨a,b⟩ ∈ iter(S)`, hence `Vₐ = b`, hence `b ∈ U(c)`.
    let k3_pair = hyp_mp(
        &hyp_leibniz(&k3_eq, zv, &Formula::mem(tz.clone(), it.clone()))?,
        &k3_p,
    )?;
    let aog = inst_all(&r.app_of_graph, &[it.clone(), ta.clone(), tb.clone()])?;
    let k3_eqv = hyp_mp(
        &hyp_mp(&a1i(&curry(&aog)?, k3.clone()), &a1i(&single, k3.clone()))?,
        &k3_pair,
    )?;
    let siu = inst_all(stages_in_universe, &[tc.clone(), ta.clone()])?;
    let k3_va = hyp_mp(&hyp_mp(&a1i(&siu, k3.clone()), &k3_a)?, &k3_h)?;
    let k3_b = hyp_mp(
        &hyp_leibniz(&k3_eqv, zv, &Formula::mem(tz.clone(), u.clone()))?,
        &k3_va,
    )?;

    // Assemble the product's membership condition and discharge both witnesses.
    let inner_prod =
        Formula::and(Formula::mem(tb.clone(), u.clone()), eq_p.clone());
    let outer_prod = Formula::and(
        Formula::mem(ta.clone(), om.clone()),
        Formula::exists(bv, inner_prod.clone()),
    );
    let k3_inner = hyp_and(&k3_b, &k3_eq)?;
    let k3_outer = syl(
        &hyp_and(&k3_a, &syl(&k3_inner, &exists_intro_imp(bv, inner_prod, tb.clone())?)?)?,
        &exists_intro_imp(av, outer_prod.clone(), ta.clone())?,
    )?;
    let k2_outer = discharge(bv, &k2_ex_b, &k3_outer)?;
    let k1_outer = discharge(av, &k1_ex, &k2_outer)?;

    let prod_at = inst_all(&s.prod.prod_ax, &[om.clone(), u.clone(), tp.clone()])?;
    let k1_prod = hyp_mp(&a1i(&iff_mpr(&prod_at)?, k1.clone()), &k1_outer)?;
    let prod_t = s.prod.of(om.clone(), u.clone());
    let h_sub = Thm::mp(
        &Thm::ax_dist(
            pv,
            h.clone(),
            Formula::imp(p_it, Formula::mem(tp.clone(), prod_t.clone())),
        )?,
        &Thm::gen(pv, &curry(&k1_prod)?),
    )?;

    // ── R3 plus `graph_pair`: totality with values in `U(c)` ────────────────
    let vx = st.v(r, tx.clone());
    let x_om = Formula::mem(tx.clone(), om.clone());
    let l1 = Formula::and(h.clone(), x_om.clone());
    let l1_h = and_left(h.clone(), x_om.clone());
    let l1_x = and_right(h.clone(), x_om.clone());
    let l1_pair = hyp_mp(
        &a1i(&inst_all(graph_pair, std::slice::from_ref(&tx))?, l1.clone()),
        &l1_x,
    )?;
    let siu_x = inst_all(stages_in_universe, &[tc.clone(), tx.clone()])?;
    let l1_vx = hyp_mp(&hyp_mp(&a1i(&siu_x, l1.clone()), &l1_x)?, &l1_h)?;
    let tot_body = Formula::and(
        Formula::mem(tz.clone(), u.clone()),
        Formula::mem(r.pair(tx.clone(), tz.clone()), it.clone()),
    );
    let l1_tot = syl(
        &hyp_and(&l1_vx, &l1_pair)?,
        &exists_intro_imp(zv, tot_body.clone(), vx)?,
    )?;
    let h_total = Thm::mp(
        &Thm::ax_dist(
            xv,
            h.clone(),
            Formula::imp(x_om, Formula::exists(zv, tot_body.clone())),
        )?,
        &Thm::gen(xv, &curry(&l1_tot)?),
    )?;
    if *h_total.concl()
        != Formula::imp(
            h.clone(),
            crate::funspace::is_total(env, &s.ap.sets, &om, &u, &it),
        )
    {
        return None
    }

    // ── The three clauses, and the function space ───────────────────────────
    let fs_at = inst_all(&s.fs.fs_ax, &[om.clone(), u.clone(), it.clone()])?;
    let (_, isfun) = iff_mp(&fs_at)?.concl().as_imp()?;
    let graph = Formula::and(
        crate::funspace::is_total(env, &s.ap.sets, &om, &u, &it),
        crate::funspace::is_single_valued(env, &s.ap.sets, &it),
    );
    let sub_prod = kernel::thm::subset(env, it.clone(), prod_t);
    if isfun != Formula::and(sub_prod.clone(), graph.clone()) {
        return None
    }
    if *h_sub.concl() != Formula::imp(h.clone(), sub_prod) {
        return None
    }
    let h_isfun = hyp_and(&h_sub, &hyp_and(&h_total, &a1i(&single, h.clone()))?)?;
    let out = hyp_mp(&a1i(&iff_mpr(&fs_at)?, h.clone()), &h_isfun)?;
    if *out.concl() != Formula::imp(h, Formula::mem(it, s.fs.of(om, u))) {
        return None
    }
    Some(Thm::gen(cv, &out))
}

/// `⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))` — **step (e)**.
#[allow(clippy::too_many_arguments)]
fn tower_mem(
    env: &mut Env,
    r: &Rec,
    s: &Sums,
    st: &Stages,
    lu: FnSym,
    iter_in_fs: &Thm,
    graph_pair: &Thm,
    union: &Thm,
    sub: &Thm,
    fs_mem: &Thm,
) -> Option<Thm> {
    let it = st.rec.set();
    let om = r.omega();
    let tower = st.tower_set();
    let sets = &s.ap.sets;

    let (cv, zv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tz, tn) = (Term::var(cv), Term::var(zv), Term::var(nv));
    let u = Term::apply(lu, vec![tc.clone()]);

    let s_in = Formula::mem(Term::var(st.seed), u.clone());
    let om_in = Formula::mem(om.clone(), u.clone());
    let h = Formula::and(s_in.clone(), om_in.clone());
    let h_s = and_left(s_in.clone(), om_in.clone());
    let h_om = and_right(s_in, om_in);

    // `iter(S) ∈ U(c)` — the single place `ω ∈ U(c)` is used.
    let h_fs = syl(&h_s, &inst_all(iter_in_fs, std::slice::from_ref(&tc))?)?;
    let fs_mem_at = inst_all(fs_mem, &[tc.clone(), om.clone(), it.clone()])?;
    let h_it = hyp_mp(&a1i(&curry(&fs_mem_at)?, h.clone()), &h_om)?;
    let h_it = hyp_mp(&h_it, &h_fs)?;

    // Three `⋃`-closures.
    let u1 = sets.union_of(it.clone());
    let u2 = sets.union_of(u1.clone());
    let u3 = sets.union_of(u2.clone());
    let step_up = |x: &Term, hx: &Thm| -> Option<Thm> {
        hyp_mp(&a1i(&inst_all(union, &[tc.clone(), x.clone()])?, h.clone()), hx)
    };
    let h_u1 = step_up(&it, &h_it)?;
    let h_u2 = step_up(&u1, &h_u1)?;
    let h_u3 = step_up(&u2, &h_u2)?;

    // `T ⊆ ⋃⋃⋃iter(S)`.
    let snd = snd_in_union2(env, sets)?;
    let z_t = Formula::mem(tz.clone(), tower.clone());
    let j1 = Formula::and(h.clone(), z_t.clone());
    let j1_z = and_right(h.clone(), z_t.clone());
    let members = inst_all(&st.tower.members, std::slice::from_ref(&tz))?;
    let j1_ex = hyp_mp(&a1i(&iff_mp(&members)?, j1.clone()), &j1_z)?;

    let vn = st.v(r, tn.clone());
    let body = Formula::and(
        Formula::mem(tn.clone(), om.clone()),
        Formula::mem(tz.clone(), vn.clone()),
    );
    if *j1_ex.concl() != Formula::imp(j1.clone(), Formula::exists(nv, body.clone())) {
        return None
    }
    let j2 = Formula::and(j1.clone(), body.clone());
    let j2_body = and_right(j1.clone(), body.clone());
    let j2_n = syl(
        &j2_body,
        &and_left(Formula::mem(tn.clone(), om.clone()), Formula::mem(tz.clone(), vn.clone())),
    )?;
    let j2_zv = syl(
        &j2_body,
        &and_right(Formula::mem(tn.clone(), om.clone()), Formula::mem(tz.clone(), vn.clone())),
    )?;
    let j2_pair = hyp_mp(
        &a1i(&inst_all(graph_pair, std::slice::from_ref(&tn))?, j2.clone()),
        &j2_n,
    )?;
    let snd_at = inst_all(&snd, &[it.clone(), tn.clone(), vn.clone()])?;
    let j2_vn_u2 = hyp_mp(&a1i(&snd_at, j2.clone()), &j2_pair)?;
    let ui = union_intro(env, sets, u2.clone(), vn.clone(), tz.clone())?;
    let j2_goal = hyp_mp(&a1i(&ui, j2.clone()), &hyp_and(&j2_vn_u2, &j2_zv)?)?;

    let j1_goal = discharge(nv, &j1_ex, &j2_goal)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(
            zv,
            h.clone(),
            Formula::imp(z_t, Formula::mem(tz.clone(), u3.clone())),
        )?,
        &Thm::gen(zv, &curry(&j1_goal)?),
    )?;
    if *h_sub.concl() != Formula::imp(h.clone(), kernel::thm::subset(env, tower.clone(), u3.clone())) {
        return None
    }

    // `C₂`: a subset of a member is a member.
    let sub_at = inst_all(sub, &[tc.clone(), u3.clone()])?;
    let out = hyp_mp(&hyp_inst(&hyp_mp(&a1i(&sub_at, h.clone()), &h_u3)?, std::slice::from_ref(&tower))?, &h_sub)?;
    if *out.concl() != Formula::imp(h, Formula::mem(tower, u)) {
        return None
    }
    Some(Thm::gen(cv, &out))
}

