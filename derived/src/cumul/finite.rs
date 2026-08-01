//! **`bnd` is a finiteness predicate**: it holds of `∅` and of every singleton,
//! and it is closed under binary union.
//!
//! # Interface
//!
//! Writing `bnd` for [`super::bounded::bnd`] — the property "a family indexed by
//! this set, with all its values in the tower `T`, has all of them in a *single*
//! stage `Vₚ`" — the exports are
//!
//! ```text
//! ⊢ bnd(∅)                                                    [bnd_empty]
//! ⊢ ∀e. bnd({e})                                              [bnd_singleton]
//! ⊢ ∀x ∀y. ((bnd(x) ∧ bnd(y)) → bnd(x ∪ y))                   [bnd_bin_union]
//! ```
//!
//! all at a free seed `S`, so each is really `∀S`. Callers need none of the
//! derivations below.
//!
//! # What this is for
//!
//! [`super::tower_closed_bnd`] asks `bnd(B(a))` of every fibre, and
//! [`super::bounded`] supplies it for `B(a) ∈ ω`. The fibres the *general*
//! inductive translation produces are not von Neumann naturals: a constructor
//! with `m` recursive arguments gets `finord(m) = Sum_m(1,…,1)`, a nest of
//! binary sums with `m` elements. These three lemmas are what closes that gap —
//! a set with `m` explicitly named elements is a union of `m` singletons, and
//! `bnd` is a predicate that survives being built up that way.
//! [`mod@super::finord`] does the building.
//!
//! # Why this is the right shape, and what it is not
//!
//! The obvious generalisation of "finite" is *equinumerous to a natural*: a
//! surjection `h ∈ fs(k, X)` with `k ∈ ω`. That is a fine notion and it does
//! imply `bnd(X)` — but only via a lemma this development would have to add
//! first, since `bnd(k)` speaks of `app(g,b)` and transporting it along `h`
//! needs the *composite* `g ∘ h` as a set, i.e. a Replacement instance. And
//! then `finord(m)` would have to be shown equinumerous to `m`, which means
//! exhibiting the graph `{⟨0,Inj_0 •⟩ … ⟨m-1,Inj_{m-1} •⟩}` and proving it
//! single-valued — `O(m²)` distinctness facts about *von Neumann numerals*,
//! which this development has no cheap source for.
//!
//! Going through the finite-set formers instead needs none of that. Neither
//! route weakens the hypothesis past what is true: `bnd(k)` is refutable for an
//! infinite `k` — at `k := ω` take `g := iter(S)`, whose values `Vₙ` all lie in
//! `T` with no common stage — so no `Fin` built out of it can admit an
//! infinitely branching `W`.
//!
//! # The one idea
//!
//! [`super::Stages::directed`]. `bnd_bin_union` gets a stage from each side and
//! has to merge them, and merging is exactly what directedness does without an
//! order on `ω`. That is the whole content; the length below is the cost of
//! moving three existential witnesses through a Hilbert system, and
//! [`crate::funspace::discharge`] does each in one line.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funspace::discharge;
use crate::funspace::pow_pow::mem_bin_union;
use crate::recursion::Rec;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, ex_falso, exists_intro, exists_intro_imp,
    hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, inst_all, syl,
};

use super::bounded::bounded_at;
use super::stages::Stages;
use super::step::{curry, mem_bin_union_elim};

/// The pieces of `bnd(k)` at one fixed triple of bound variables.
///
/// `gv` is free while a derivation is in progress and generalised at the end;
/// `bv` and `pv` are only ever used as binders, and [`Formula::forall`] closes
/// over them, so which variables these are is invisible in the result.
struct Bnd<'a> {
    r: &'a Rec,
    st: &'a Stages,
    gv: FreeVar,
    bv: FreeVar,
    pv: FreeVar,
}

impl<'a> Bnd<'a> {
    fn new(env: &mut Env, r: &'a Rec, st: &'a Stages) -> Bnd<'a> {
        Bnd { r, st, gv: env.fresh_var(), bv: env.fresh_var(), pv: env.fresh_var() }
    }

    /// `app(g,t)`, the family's value at `t`.
    fn g(&self, t: Term) -> Term { self.r.apply(Term::var(self.gv), t) }

    /// `Vₜ`.
    fn v(&self, t: Term) -> Term { self.st.v(self.r, t) }

    /// `∀b. (b ∈ k → g(b) ∈ c)`, the shape both the hypothesis and the
    /// conclusion of `bnd` have.
    fn all_in(&self, k: &Term, c: &Term) -> Formula {
        Formula::forall(
            self.bv,
            Formula::imp(
                Formula::mem(Term::var(self.bv), k.clone()),
                Formula::mem(self.g(Term::var(self.bv)), c.clone()),
            ),
        )
    }

    /// `∀b. (b ∈ k → g(b) ∈ T)`.
    fn hyp(&self, k: &Term) -> Formula { self.all_in(k, &self.st.tower_set()) }

    /// `p ∈ ω ∧ ∀b. (b ∈ k → g(b) ∈ Vₚ)`, the body of the existential.
    fn body(&self, k: &Term, p: &Term) -> Formula {
        Formula::and(
            Formula::mem(p.clone(), self.r.omega()),
            self.all_in(k, &self.v(p.clone())),
        )
    }

    /// `∃p. (p ∈ ω ∧ ∀b. (b ∈ k → g(b) ∈ Vₚ))`.
    fn ex(&self, k: &Term) -> Formula {
        Formula::exists(self.pv, self.body(k, &Term::var(self.pv)))
    }

    /// `bnd(k)` — the same formula [`bounded_at`] builds.
    fn all(&self, env: &mut Env, k: &Term) -> Formula {
        bounded_at(env, self.r, self.st, k, self.gv, self.bv, self.pv)
    }
}

/// `⊢ bnd(∅)` — **nothing to bound**.
///
/// The claim `∀b. (b ∈ ∅ → g(b) ∈ V₀)` is vacuous and `0 ∈ ω`, so `p := 0`
/// serves. This is [`super::bounded`]'s base case, stated on its own because
/// [`mod@super::finord`] needs it at `finord(0)`, which is a *symbol* and not
/// a von Neumann numeral.
pub fn bnd_empty(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let d = Bnd::new(env, r, st);
    let zero = r.zero();
    let tb = Term::var(d.bv);

    let vacuous = Thm::gen(
        d.bv,
        &syl(
            &inst_all(&r.core().empty_ax, std::slice::from_ref(&tb))?,
            &ex_falso(Formula::mem(d.g(tb.clone()), d.v(zero.clone()))),
        )?,
    );
    if *vacuous.concl() != d.all_in(&zero, &d.v(zero.clone())) {
        return None
    }
    let witness = and_intro(&r.core().zero_mem, &vacuous);
    let ex = exists_intro(d.pv, d.body(&zero, &Term::var(d.pv)), zero.clone(), &witness)?;
    let out = Thm::gen(d.gv, &a1i(&ex, d.hyp(&zero)));

    let expected = d.all(env, &zero);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// `⊢ ∀e. bnd({e})` — **one point needs one stage**.
///
/// `e ∈ {e}`, so the hypothesis puts `g(e)` in `T` and the tower's membership
/// condition names a stage holding it; every `b ∈ {e}` *is* `e`, so that one
/// stage is the bound. No merge, and hence no directedness.
pub fn bnd_singleton(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let d = Bnd::new(env, r, st);
    let (ev, nv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (te, tn, tb) = (Term::var(ev), Term::var(nv), Term::var(d.bv));
    let sing = crate::singleton(r.ap.sets.up, te.clone());

    let mem_sing = &r.core().mem_sing;
    let h = d.hyp(&sing);

    // `e ∈ {e}`, then `g(e) ∈ T`, then a stage holding it.
    let e_in = Thm::mp(
        &iff_mpr(&inst_all(mem_sing, &[te.clone(), te.clone()])?)?,
        &Thm::eq_refl(te.clone()),
    )?;
    let h_ge = hyp_mp(&Thm::ax_inst(h.clone(), te.clone())?, &a1i(&e_in, h.clone()))?;
    let h_ex = syl(&h_ge, &iff_mp(&inst_all(&st.tower.members, &[d.g(te.clone())])?)?)?;

    // `J := H ∧ (n ∈ ω ∧ g(e) ∈ Vₙ)`.
    let e2 = Formula::and(
        Formula::mem(tn.clone(), r.omega()),
        Formula::mem(d.g(te.clone()), d.v(tn.clone())),
    );
    if *h_ex.concl() != Formula::imp(h.clone(), Formula::exists(nv, e2.clone())) {
        return None
    }
    let j = Formula::and(h.clone(), e2.clone());
    let j_e2 = and_right(h.clone(), e2.clone());
    let j_n = syl(
        &j_e2,
        &and_left(
            Formula::mem(tn.clone(), r.omega()),
            Formula::mem(d.g(te.clone()), d.v(tn.clone())),
        ),
    )?;
    let j_gn = syl(
        &j_e2,
        &and_right(
            Formula::mem(tn.clone(), r.omega()),
            Formula::mem(d.g(te.clone()), d.v(tn.clone())),
        ),
    )?;

    // `b ∈ {e} → b = e → e = b`, and Leibniz carries `g(e) ∈ Vₙ` to `g(b) ∈ Vₙ`.
    let b_eq = syl(
        &iff_mp(&inst_all(mem_sing, &[te.clone(), tb.clone()])?)?,
        &eq_symm_imp(env, tb.clone(), te.clone()),
    )?;
    let leib = Thm::eq_leibniz(
        te.clone(),
        tb.clone(),
        wv,
        Formula::mem(d.g(Term::var(wv)), d.v(tn.clone())),
    );
    let jb = Formula::and(j.clone(), Formula::mem(tb.clone(), sing.clone()));
    let jb_gb = hyp_mp(
        &hyp_mp(
            &a1i(&syl(&b_eq, &leib)?, jb.clone()),
            &and_right(j.clone(), Formula::mem(tb.clone(), sing.clone())),
        )?,
        &syl(&and_left(j.clone(), Formula::mem(tb.clone(), sing.clone())), &j_gn)?,
    )?;
    let j_cov = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), sing.clone()),
                Formula::mem(d.g(tb.clone()), d.v(tn.clone())),
            ),
        )?,
        &Thm::gen(d.bv, &curry(&jb_gb)?),
    )?;

    let j_goal = syl(
        &hyp_and(&j_n, &j_cov)?,
        &exists_intro_imp(d.pv, d.body(&sing, &Term::var(d.pv)), tn.clone())?,
    )?;
    let h_goal = discharge(nv, &h_ex, &j_goal)?;
    let out = Thm::gen(ev, &Thm::gen(d.gv, &h_goal));

    let expected = Formula::forall(ev, d.all(env, &sing));
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// `⊢ ∀x ∀y. ((bnd(x) ∧ bnd(y)) → bnd(x ∪ y))` — **two bounded sets have a
/// bounded union**.
///
/// Each side hands back a stage and [`super::Stages::directed`] merges them;
/// [`mem_bin_union_elim`] then sends every member of the union to one side or
/// the other.
pub fn bnd_bin_union(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let d = Bnd::new(env, r, st);
    let sets = r.ap.sets.clone();
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (pv2, qv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let (tp, tq, tt, tb) = (Term::var(pv2), Term::var(qv), Term::var(tv), Term::var(d.bv));
    let om = r.omega();
    let un = crate::funspace::bin_union(&sets, tx.clone(), ty.clone());

    let (bu_left, bu_right) = mem_bin_union(env, &sets)?;
    let bu_elim = mem_bin_union_elim(env, &sets)?;

    let bnd_x = d.all(env, &tx);
    let bnd_y = d.all(env, &ty);
    let k = Formula::and(bnd_x.clone(), bnd_y.clone());
    let h = d.hyp(&un);
    let j0 = Formula::and(k.clone(), h.clone());
    let j0_k = and_left(k.clone(), h.clone());
    let j0_h = and_right(k.clone(), h.clone());

    // `H` restricted to each side, through the two union introductions.
    let restrict = |side: &Thm, s: &Term| -> Option<Thm> {
        let into = inst_all(side, &[tx.clone(), ty.clone(), tb.clone()])?;
        let at_b = syl(&j0_h, &Thm::ax_inst(h.clone(), tb.clone())?)?;
        let body = crate::separation::hyp_syl(&a1i(&into, j0.clone()), &at_b)?;
        Thm::mp(
            &Thm::ax_dist(
                d.bv,
                j0.clone(),
                Formula::imp(
                    Formula::mem(tb.clone(), s.clone()),
                    Formula::mem(d.g(tb.clone()), st.tower_set()),
                ),
            )?,
            &Thm::gen(d.bv, &body),
        )
    };
    let j0_hx = restrict(&bu_left, &tx)?;
    let j0_hy = restrict(&bu_right, &ty)?;
    if *j0_hx.concl() != Formula::imp(j0.clone(), d.hyp(&tx))
        || *j0_hy.concl() != Formula::imp(j0.clone(), d.hyp(&ty))
    {
        return None
    }

    // The two stages.
    let use_bnd = |side: &Thm, which: &Thm, bnd_s: &Formula| -> Option<Thm> {
        let at_g = syl(which, &Thm::ax_inst(bnd_s.clone(), Term::var(d.gv))?)?;
        hyp_mp(&syl(&j0_k, &at_g)?, side)
    };
    let j0_ex_p = use_bnd(&j0_hx, &and_left(bnd_x.clone(), bnd_y.clone()), &bnd_x)?;
    let j0_ex_q = use_bnd(&j0_hy, &and_right(bnd_x.clone(), bnd_y.clone()), &bnd_y)?;

    let e1 = d.body(&tx, &tp);
    let e2 = d.body(&ty, &tq);
    if *j0_ex_p.concl() != Formula::imp(j0.clone(), Formula::exists(pv2, e1.clone()))
        || *j0_ex_q.concl() != Formula::imp(j0.clone(), Formula::exists(qv, e2.clone()))
    {
        return None
    }

    // `J1 := J0 ∧ e1`, `J2 := J1 ∧ e2`.
    let j1 = Formula::and(j0.clone(), e1.clone());
    let j1_j0 = and_left(j0.clone(), e1.clone());
    let j1_e1 = and_right(j0.clone(), e1.clone());
    let j2 = Formula::and(j1.clone(), e2.clone());
    let j2_j1 = and_left(j1.clone(), e2.clone());
    let j2_e2 = and_right(j1.clone(), e2.clone());

    let p_om = Formula::mem(tp.clone(), om.clone());
    let q_om = Formula::mem(tq.clone(), om.clone());
    let cov_x = d.all_in(&tx, &d.v(tp.clone()));
    let cov_y = d.all_in(&ty, &d.v(tq.clone()));
    let j2_p = syl(&j2_j1, &syl(&j1_e1, &and_left(p_om.clone(), cov_x.clone()))?)?;
    let j2_cx = syl(&j2_j1, &syl(&j1_e1, &and_right(p_om.clone(), cov_x.clone()))?)?;
    let j2_q = syl(&j2_e2, &and_left(q_om.clone(), cov_y.clone()))?;
    let j2_cy = syl(&j2_e2, &and_right(q_om, cov_y.clone()))?;

    // The merge.
    let dir_at = inst_all(&st.directed, std::slice::from_ref(&tp))?;
    let j2_inner = hyp_mp(&a1i(&dir_at, j2.clone()), &j2_p)?;
    let (_, all_m) = j2_inner.concl().as_imp()?;
    let j2_dir = hyp_mp(&syl(&j2_inner, &Thm::ax_inst(all_m, tq.clone())?)?, &j2_q)?;
    let sub_pt = kernel::thm::subset(env, d.v(tp.clone()), d.v(tt.clone()));
    let sub_qt = kernel::thm::subset(env, d.v(tq.clone()), d.v(tt.clone()));
    let e3 = Formula::and(
        Formula::mem(tt.clone(), om.clone()),
        Formula::and(sub_pt.clone(), sub_qt.clone()),
    );
    if *j2_dir.concl() != Formula::imp(j2.clone(), Formula::exists(tv, e3.clone())) {
        return None
    }

    // `J3 := J2 ∧ e3` — the merged stage covers both sides, hence the union.
    let j3 = Formula::and(j2.clone(), e3.clone());
    let j3_j2 = and_left(j2.clone(), e3.clone());
    let j3_e3 = and_right(j2.clone(), e3.clone());
    let t_om = Formula::mem(tt.clone(), om.clone());
    let subs = Formula::and(sub_pt.clone(), sub_qt.clone());
    let j3_t = syl(&j3_e3, &and_left(t_om.clone(), subs.clone()))?;
    let j3_subs = syl(&j3_e3, &and_right(t_om, subs))?;
    let j3_pt = syl(&j3_subs, &and_left(sub_pt.clone(), sub_qt.clone()))?;
    let j3_qt = syl(&j3_subs, &and_right(sub_pt.clone(), sub_qt.clone()))?;

    // `J4 := J3 ∧ b ∈ x ∪ y`, and the case split on which side `b` is on.
    let b_in = Formula::mem(tb.clone(), un.clone());
    let j4 = Formula::and(j3.clone(), b_in.clone());
    let j4_j3 = and_left(j3.clone(), b_in.clone());
    let j4_b = and_right(j3.clone(), b_in.clone());
    let disj = hyp_mp(
        &a1i(&inst_all(&bu_elim, &[tx.clone(), ty.clone(), tb.clone()])?, j4.clone()),
        &j4_b,
    )?;

    let side = |cov: &Thm, into: &Thm, s: &Term, stage: &Term, sub: &Formula| -> Option<Thm> {
        let cov_b = syl(
            &syl(&j4_j3, &syl(&j3_j2, cov)?)?,
            &Thm::ax_inst(d.all_in(s, &d.v(stage.clone())), tb.clone())?,
        )?;
        let up = syl(&syl(&j4_j3, into)?, &Thm::ax_inst(sub.clone(), d.g(tb.clone()))?)?;
        crate::separation::hyp_syl(&cov_b, &up)
    };
    let left = side(&j2_cx, &j3_pt, &tx, &tp, &sub_pt)?;
    let right = side(&j2_cy, &j3_qt, &ty, &tq, &sub_qt)?;
    let cases = hyp_or_elim(&disj, &left, &right)?;

    let j3_cov = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j3.clone(),
            Formula::imp(b_in, Formula::mem(d.g(tb.clone()), d.v(tt.clone()))),
        )?,
        &Thm::gen(d.bv, &curry(&cases)?),
    )?;
    if *j3_cov.concl() != Formula::imp(j3.clone(), d.all_in(&un, &d.v(tt.clone()))) {
        return None
    }

    let j3_goal = syl(
        &hyp_and(&j3_t, &j3_cov)?,
        &exists_intro_imp(d.pv, d.body(&un, &Term::var(d.pv)), tt.clone())?,
    )?;
    let j2_goal = discharge(tv, &j2_dir, &j3_goal)?;
    let j1_goal = discharge(qv, &syl(&j1_j0, &j0_ex_q)?, &j2_goal)?;
    let j0_goal = discharge(pv2, &j0_ex_p, &j1_goal)?;

    let out = Thm::gen(
        xv,
        &Thm::gen(
            yv,
            &Thm::mp(
                &Thm::ax_dist(d.gv, k.clone(), Formula::imp(h.clone(), d.ex(&un)))?,
                &Thm::gen(d.gv, &curry(&j0_goal)?),
            )?,
        ),
    );

    let expected = Formula::forall(
        xv,
        Formula::forall(yv, Formula::imp(k, d.all(env, &un))),
    );
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
