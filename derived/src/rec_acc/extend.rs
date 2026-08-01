//! **The one-point extension** `G := accrec ∪ {⟨x,V⟩}`, and that it is an
//! attempt.
//!
//! # Interface
//!
//! With `V := app(app(app(e,x),•), ih(accrec,A,R,x))`, `q := ⟨x,V⟩`,
//! `G := accrec(A,R,T,e) ∪ {q}` and
//!
//! ```text
//! K := (step_typed(A,R,T,e) ∧ x ∈ A)
//!        ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ indom(accrec,y))))
//! ```
//!
//! — the second conjunct being exactly [`crate::acc::acc_rect`]'s induction
//! hypothesis at `φ(z) := indom(accrec,z)` — this file derives, at
//! caller-supplied `A, R, T, e, x`:
//!
//! ```text
//! ⊢ ∀z. (z ∈ G ↔ (z ∈ accrec ∨ z = q))                         [ext_members]
//! ⊢ ∀u. (⟨x,u⟩ ∈ G → u = V)                            [value_at_new_point]
//! ⊢ sv(G)                                               [ext_single_valued]
//! ⊢ ∀z. (z ∈ accrec → z ∈ G)                              [rec_subset_ext]
//! ⊢ ∀y. (indom(accrec,y) → indom(G,y))                         [ext_indom]
//! ⊢ ∀y. (indom(accrec,y) → app(G,y) = app(accrec,y))             [ext_app]
//! ⊢ app(G,x) = V                                                [ext_at_x]
//! ⊢ K → x ∈ acc(A,R)                                          [ext_x_in_acc]
//! ⊢ K → V ∈ T                                              [ext_value_typed]
//! ⊢ K → G ⊆ prod(acc(A,R),T)                                     [ext_bound]
//! ⊢ K → rec_cond(A,R,e,G)                                     [ext_rec_cond]
//! ⊢ K → G ∈ Att(A,R,T,e)                                  [ext_is_attempt]
//! ```
//!
//! **Seven of the twelve are unconditional**, which is the whole reason this
//! file is separate from [`super::total`]: the extension is a legitimate object
//! whatever `e` does, and `K` is spent only on the three clauses of being an
//! attempt.
//!
//! # `sv(G)` needs no case analysis, and that is the load-bearing observation
//!
//! The obvious worry is that `x` might already be in `accrec`'s domain, in which
//! case `G` has two values there. It does not: [`super::iota_on_domain`] forces
//! the old value to **be** `V` — not merely to be compatible with it — so
//! `value_at_new_point` holds outright and the four cases of single-valuedness
//! collapse to three with no appeal to excluded middle. `crate::wrec_extend`
//! records the same finding for `W`; it is the one place where getting the
//! design wrong costs a whole extra case split, and it is why
//! [`super::is_attempt::iota_on_domain`] is stated before totality rather than
//! after.
//!
//! # What `K` is actually spent on
//!
//! * `x ∈ A` and the induction hypothesis give `x ∈ acc(A,R)`, by
//!   [`crate::acc::acc_intro`] — the introduction rule, whose unconditionality
//!   is what makes this whole module free of a bound;
//! * `step_typed` gives `V ∈ T`, via [`super::ih::ih_typed`]. This is the
//!   hypothesis `INDUCTIVES.md` records as unavoidable: totality is not free,
//!   because `e` is an arbitrary set and nothing forces its values into `T`;
//! * the induction hypothesis gives, at the new point, that every predecessor is
//!   already in `accrec`'s domain, which is what `rec_cond`'s first clause needs
//!   there.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{hyp_syl, or_intro_left, or_intro_right};
use crate::funspace::{bin_union, is_single_valued};
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim};
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl,
    inst_all, singleton, syl, uncurry,
};

use super::attempt::{att_of, attempt_bound, indom_intro, preds_indom, rec_cond};
use super::base::Base;
use super::ih::{ih_bound, preds_agree, preds_typed};
use super::is_attempt::UnionFacts;
use super::shared::{gen_under, hyp_inst, hyp_leibniz, iff_trans, or_right_cong};

/// `∀x. (x ∈ acc(A,R) → ∀i. (i ∈ ih_bound(A,T) → app(app(app(e,x),•),i) ∈ T))`
/// — **the typing side condition on the step**, as a formula.
///
/// The analogue of [`crate::wrec_total::step_typed`], and unavoidable for the
/// same reason: `e` is an arbitrary set, so nothing forces the step's value into
/// the target. Note the induction-hypothesis slot ranges over the whole power
/// set [`super::ih::ih_bound`] and not over a function space — see there for why
/// that is both weaker to assume and enough.
pub fn step_typed(env: &mut Env, b: &Base, a: &Term, r: &Term, t: &Term, e: &Term) -> Formula {
    let (xv, iv) = (env.fresh_var(), env.fresh_var());
    let (tx, ti) = (Term::var(xv), Term::var(iv));
    Formula::forall(
        xv,
        Formula::imp(
            Formula::mem(tx.clone(), b.acc_of(a, r)),
            Formula::forall(
                iv,
                Formula::imp(
                    Formula::mem(ti.clone(), ih_bound(&b.s, a, t)),
                    Formula::mem(b.step_at(e, &tx, &ti), t.clone()),
                ),
            ),
        ),
    )
}

/// The one-point extension, and everything the recursion argument needs about
/// it, at fixed `A, R, T, e, x`.
///
/// Held as a struct because the terms `V`, `q` and `G` are rebuilt by every
/// lemma below and a look-alike would refuse to compose.
pub struct Ext<'a> {
    /// The shared apparatus.
    pub b: &'a Base,
    /// The set of attempts.
    pub att: FnSym,
    /// Its characteristic theorem.
    pub att_ax: &'a Thm,
    /// The recursor symbol.
    pub rec: FnSym,
    /// The union-layer theorems.
    pub facts: &'a UnionFacts<'a>,
    /// `⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) → app(accrec,x) = …)`.
    pub iota_dom: &'a Thm,
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
    pub bin: &'a Thm,
    /// The four parameters `A, R, T, e`.
    pub ps: Vec<Term>,
    /// The point being added.
    pub x: Term,
}

impl Ext<'_> {
    /// The hypothesis half of the house rule for every theorem this view
    /// carries: `att_ax`, `iota_dom`, `bin`, the five [`UnionFacts`], and the
    /// [`Base`]'s own fields.
    ///
    /// Seven of the twelve results in this file are advertised
    /// **unconditional**, and the other five carry exactly `K` and nothing else
    /// — that "and nothing else" is a claim about the sequent, not just about
    /// the formula. Every entry below therefore refuses a view carrying a
    /// hypothetical theorem before taking a step; the fields are `pub`, so the
    /// check belongs at each entry rather than only at construction.
    pub fn inputs_unconditional(&self) -> bool {
        self.b.all_unconditional()
            && self.facts.all_unconditional()
            && crate::all_unconditional(&[self.att_ax, self.iota_dom, self.bin])
    }

    /// The term `accrec(A,R,T,e)`.
    pub fn rec_t(&self) -> Term { Term::apply(self.rec, self.ps.clone()) }

    /// The value `V := app(app(app(e,x),•), ih(accrec,A,R,x))`.
    pub fn value(&self) -> Term {
        let rec_t = self.rec_t();
        self.b.step_at(
            &self.ps[3],
            &self.x,
            &self.b.ih_at(&rec_t, &self.ps[0], &self.ps[1], &self.x),
        )
    }

    /// The new pair `q := ⟨x,V⟩`.
    pub fn q(&self) -> Term { self.b.s.ap.sets.pair(self.x.clone(), self.value()) }

    /// The extension `G := accrec ∪ {q}`.
    pub fn g(&self) -> Term {
        bin_union(
            &self.b.s.ap.sets,
            self.rec_t(),
            singleton(self.b.s.ap.sets.up, self.q()),
        )
    }

    /// `⊢ z ∈ G ↔ (z ∈ accrec ∨ z = q)`, at the caller's `z`.
    ///
    /// The gate for [`Ext::rec_subset_ext`] and [`Ext::new_point_in_ext`] too,
    /// which are this biconditional in one direction each.
    pub fn ext_members(&self, z: &Term) -> Option<Thm> {
        if !self.inputs_unconditional() {
            return None
        }
        let at = inst_all(
            self.bin,
            &[
                self.rec_t(),
                singleton(self.b.s.ap.sets.up, self.q()),
                z.clone(),
            ],
        )?;
        let ms = inst_all(&self.b.s.ap.mem_sing, &[self.q(), z.clone()])?;
        let mem_rec = Formula::mem(z.clone(), self.rec_t());
        iff_trans(&at, &or_right_cong(&ms, &mem_rec)?)
    }

    /// `⊢ z ∈ accrec → z ∈ G`.
    pub fn rec_subset_ext(&self, z: &Term) -> Option<Thm> {
        let mem_rec = Formula::mem(z.clone(), self.rec_t());
        let eq = Formula::eq(z.clone(), self.q());
        syl(
            &or_intro_left(mem_rec, eq),
            &iff_mpr(&self.ext_members(z)?)?,
        )
    }

    /// `⊢ z = q → z ∈ G`.
    pub fn new_point_in_ext(&self, z: &Term) -> Option<Thm> {
        let mem_rec = Formula::mem(z.clone(), self.rec_t());
        let eq = Formula::eq(z.clone(), self.q());
        syl(
            &or_intro_right(mem_rec, eq),
            &iff_mpr(&self.ext_members(z)?)?,
        )
    }

    /// `⊢ sv(accrec)`, at these parameters.
    fn sv_rec(&self) -> Option<Thm> { inst_all(self.facts.single_valued, &self.ps) }

    /// `⊢ ∀u. (⟨x,u⟩ ∈ G → u = V)` — **the old value is already `V`**.
    ///
    /// See the module header: this is what removes the case split from
    /// [`Ext::ext_single_valued`]. Unconditional, so the view's own theorems
    /// must be — chiefly `iota_dom`, which is where the old value is forced to
    /// *be* `V`.
    pub fn value_at_new_point(&self, env: &mut Env) -> Option<Thm> {
        if !self.inputs_unconditional() {
            return None
        }
        let uv = env.fresh_var();
        let tu = Term::var(uv);
        let v = self.value();
        let pair = self.b.s.ap.sets.pair(self.x.clone(), tu.clone());
        let goal = Formula::eq(tu.clone(), v.clone());

        let h = Formula::mem(pair.clone(), self.g());
        let h_disj = syl(&imp_refl(h.clone()), &iff_mp(&self.ext_members(&pair)?)?)?;

        // Left: the pair was already in `accrec`, whose value at `x` is `V`.
        let mem_rec = Formula::mem(pair.clone(), self.rec_t());
        let m = Formula::and(h.clone(), mem_rec.clone());
        let m_mem = and_right(h.clone(), mem_rec.clone());
        let m_ind = syl(
            &m_mem,
            &indom_intro(env, self.b, &self.rec_t(), &self.x, &tu)?,
        )?;
        let aog = inst_all(
            &self.b.app_of_graph,
            &[self.rec_t(), self.x.clone(), tu.clone()],
        )?;
        let m_val = hyp_mp(
            &a1i(&aog, m.clone()),
            &hyp_and(&a1i(&self.sv_rec()?, m.clone()), &m_mem)?,
        )?;
        let iota = inst_all(self.iota_dom, &self.ps)?;
        let iota_x = Thm::mp(&Thm::ax_inst(iota.concl().clone(), self.x.clone())?, &iota)?;
        let m_iota = hyp_mp(&a1i(&iota_x, m.clone()), &m_ind)?;
        let m_val_sym = hyp_eq_symm(env, &m_val)?;
        let m_goal = hyp_eq_trans(env, &m_val_sym, &m_iota)?;
        if *m_goal.concl() != Formula::imp(m, goal.clone()) {
            return None
        }
        let left = uncurry(&m_goal)?;

        // Right: the pair *is* `q`, so `u = V` by injectivity.
        let pi = inst_all(
            &self.b.s.ap.pair_inj,
            &[self.x.clone(), tu.clone(), self.x.clone(), v.clone()],
        )?;
        let right = a1i(
            &syl(
                &pi,
                &and_right(
                    Formula::eq(self.x.clone(), self.x.clone()),
                    goal.clone(),
                ),
            )?,
            h.clone(),
        );

        let out = hyp_or_elim(&h_disj, &left, &right)?;
        if *out.concl() != Formula::imp(h, goal) {
            return None
        }
        Some(Thm::gen(uv, &out))
    }

    /// `⊢ sv(G)` — **the extension is a function**, unconditionally.
    ///
    /// `vanp` must be [`Ext::value_at_new_point`] and must itself be
    /// unconditional; the conclusion is pinned in release against a rebuilt
    /// `is_single_valued(G)`.
    pub fn ext_single_valued(&self, env: &mut Env, vanp: &Thm) -> Option<Thm> {
        if !self.inputs_unconditional() || !vanp.hyps().is_empty() {
            return None
        }
        let (pv, uv, u2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tp, tu, tu2) = (Term::var(pv), Term::var(uv), Term::var(u2v));
        let g = self.g();
        let v = self.value();

        let pair1 = self.b.s.ap.sets.pair(tp.clone(), tu.clone());
        let pair2 = self.b.s.ap.sets.pair(tp.clone(), tu2.clone());
        let m1 = Formula::mem(pair1.clone(), g.clone());
        let m2 = Formula::mem(pair2.clone(), g.clone());
        let h = Formula::and(m1.clone(), m2.clone());
        let h_m1 = and_left(m1.clone(), m2.clone());
        let h_m2 = and_right(m1, m2);
        let goal = Formula::eq(tu.clone(), tu2.clone());

        // `⟨p,u⟩ = q → p = x` and `… → u = V`, and likewise for the second pair.
        let inj = |a: &Term, bb: &Term| -> Option<(Thm, Thm)> {
            let pi = inst_all(
                &self.b.s.ap.pair_inj,
                &[a.clone(), bb.clone(), self.x.clone(), v.clone()],
            )?;
            let l = Formula::eq(a.clone(), self.x.clone());
            let r = Formula::eq(bb.clone(), v.clone());
            Some((
                syl(&pi, &and_left(l.clone(), r.clone()))?,
                syl(&pi, &and_right(l, r))?,
            ))
        };

        // Case 1: `⟨p,u⟩ = q`. Then `p = x`, `u = V`, and `⟨x,u′⟩ ∈ G`, so
        // `u′ = V` too.
        let eq1 = Formula::eq(pair1.clone(), self.q());
        let k1 = Formula::and(h.clone(), eq1.clone());
        let k1_eq = and_right(h.clone(), eq1.clone());
        let (inj_p, inj_u) = inj(&tp, &tu)?;
        let k1_px = syl(&k1_eq, &inj_p)?;
        let k1_uv = syl(&k1_eq, &inj_u)?;
        let k1_m2 = syl(&and_left(h.clone(), eq1), &h_m2)?;
        let moved = hyp_leibniz(env, &k1_px, |w| {
            Formula::mem(self.b.s.ap.sets.pair(w, tu2.clone()), g.clone())
        })?;
        let k1_m2x = hyp_mp(&moved, &k1_m2)?;
        let k1_u2v = hyp_mp(
            &a1i(
                &Thm::mp(&Thm::ax_inst(vanp.concl().clone(), tu2.clone())?, vanp)?,
                k1.clone(),
            ),
            &k1_m2x,
        )?;
        let k1_sym = hyp_eq_symm(env, &k1_u2v)?;
        let k1_goal = hyp_eq_trans(env, &k1_uv, &k1_sym)?;
        if *k1_goal.concl() != Formula::imp(k1, goal.clone()) {
            return None
        }
        let case1 = uncurry(&k1_goal)?;

        // Case 2: `⟨p,u⟩ ∈ accrec`.
        let mem1 = Formula::mem(pair1.clone(), self.rec_t());
        let k2 = Formula::and(h.clone(), mem1.clone());
        let k2_h = and_left(h.clone(), mem1.clone());
        let k2_mem1 = and_right(h.clone(), mem1);
        let k2_disj2 = syl(
            &syl(&k2_h, &h_m2)?,
            &iff_mp(&self.ext_members(&pair2)?)?,
        )?;

        //   2a: `⟨p,u′⟩ ∈ accrec` too — plain single-valuedness of `accrec`.
        let sv_rec = self.sv_rec()?;
        let sv_at = {
            let a1 = Thm::mp(&Thm::ax_inst(sv_rec.concl().clone(), tp.clone())?, &sv_rec)?;
            let a2 = Thm::mp(&Thm::ax_inst(a1.concl().clone(), tu.clone())?, &a1)?;
            Thm::mp(&Thm::ax_inst(a2.concl().clone(), tu2.clone())?, &a2)?
        };
        let mem2 = Formula::mem(pair2.clone(), self.rec_t());
        let j = Formula::and(k2.clone(), mem2.clone());
        let j_both = hyp_and(
            &syl(&and_left(k2.clone(), mem2.clone()), &k2_mem1)?,
            &and_right(k2.clone(), mem2),
        )?;
        let case2a = uncurry(&hyp_mp(&a1i(&sv_at, j.clone()), &j_both)?)?;

        //   2b: `⟨p,u′⟩ = q` — then `p = x`, `u′ = V`, and `⟨x,u⟩ ∈ G`.
        let eq2 = Formula::eq(pair2.clone(), self.q());
        let j2 = Formula::and(k2.clone(), eq2.clone());
        let j2_eq = and_right(k2.clone(), eq2);
        let (inj_p2, inj_u2) = inj(&tp, &tu2)?;
        let j2_px = syl(&j2_eq, &inj_p2)?;
        let j2_u2v = syl(&j2_eq, &inj_u2)?;
        let j2_m1 = syl(
            &syl(&and_left(k2.clone(), Formula::eq(pair2, self.q())), &k2_mem1)?,
            &self.rec_subset_ext(&pair1)?,
        )?;
        let moved2 = hyp_leibniz(env, &j2_px, |w| {
            Formula::mem(self.b.s.ap.sets.pair(w, tu.clone()), g.clone())
        })?;
        let j2_m1x = hyp_mp(&moved2, &j2_m1)?;
        let j2_uv = hyp_mp(
            &a1i(
                &Thm::mp(&Thm::ax_inst(vanp.concl().clone(), tu.clone())?, vanp)?,
                j2.clone(),
            ),
            &j2_m1x,
        )?;
        let j2_sym = hyp_eq_symm(env, &j2_u2v)?;
        let j2_goal = hyp_eq_trans(env, &j2_uv, &j2_sym)?;
        if *j2_goal.concl() != Formula::imp(j2, goal.clone()) {
            return None
        }
        let case2b = uncurry(&j2_goal)?;

        let case2 = uncurry(&hyp_or_elim(&k2_disj2, &case2a, &case2b)?)?;
        let h_disj1 = syl(&h_m1, &iff_mp(&self.ext_members(&pair1)?)?)?;
        let out = hyp_or_elim(&h_disj1, &case2, &case1)?;
        if *out.concl() != Formula::imp(h, goal) {
            return None
        }

        let all = gen_all(&[pv, uv, u2v], &out);
        if *all.concl() != is_single_valued(env, &self.b.s.ap.sets, &g) {
            return None
        }
        Some(all)
    }

    /// `⊢ indom(accrec,y) → indom(G,y)`, at the caller's `y`.
    pub fn ext_indom(&self, env: &mut Env, y: &Term) -> Option<Thm> {
        if !self.inputs_unconditional() {
            return None
        }
        let wv = env.fresh_var();
        let tw = Term::var(wv);
        let pair = self.b.s.ap.sets.pair(y.clone(), tw.clone());
        let body = syl(
            &self.rec_subset_ext(&pair)?,
            &indom_intro(env, self.b, &self.g(), y, &tw)?,
        )?;
        let ex = crate::exists_elim_imp(
            wv,
            &Thm::gen(wv, &body),
            &self.b.indom(env, &self.g(), y),
        )?;
        if *ex.concl()
            != Formula::imp(
                self.b.indom(env, &self.rec_t(), y),
                self.b.indom(env, &self.g(), y),
            )
        {
            return None
        }
        Some(ex)
    }

    /// `⊢ indom(accrec,y) → app(G,y) = app(accrec,y)` — **`G` extends `accrec`
    /// as a function**, at the caller's `y`.
    ///
    /// `sv_g` must be [`Ext::ext_single_valued`], unconditional.
    pub fn ext_app(&self, env: &mut Env, y: &Term, sv_g: &Thm) -> Option<Thm> {
        if !self.inputs_unconditional() || !sv_g.hyps().is_empty() {
            return None
        }
        let wv = env.fresh_var();
        let tw = Term::var(wv);
        let pair = self.b.s.ap.sets.pair(y.clone(), tw.clone());
        let h = self.b.indom(env, &self.rec_t(), y);
        let mem = Formula::mem(pair.clone(), self.rec_t());
        let m = Formula::and(h.clone(), mem.clone());
        let m_mem = and_right(h.clone(), mem);

        let aog_r = inst_all(&self.b.app_of_graph, &[self.rec_t(), y.clone(), tw.clone()])?;
        let m_r = hyp_mp(
            &a1i(&aog_r, m.clone()),
            &hyp_and(&a1i(&self.sv_rec()?, m.clone()), &m_mem)?,
        )?;
        let m_ing = syl(&m_mem, &self.rec_subset_ext(&pair)?)?;
        let aog_g = inst_all(&self.b.app_of_graph, &[self.g(), y.clone(), tw.clone()])?;
        let m_g = hyp_mp(
            &a1i(&aog_g, m.clone()),
            &hyp_and(&a1i(sv_g, m.clone()), &m_ing)?,
        )?;
        let m_r_sym = hyp_eq_symm(env, &m_r)?;
        let m_goal = hyp_eq_trans(env, &m_g, &m_r_sym)?;
        if *m_goal.concl()
            != Formula::imp(
                m,
                Formula::eq(self.b.app(&self.g(), y), self.b.app(&self.rec_t(), y)),
            )
        {
            return None
        }
        hyp_exists_elim(wv, &m_goal, &imp_refl(h))
    }

    /// `⊢ app(G,x) = V` — the extension computes at the new point.
    ///
    /// `sv_g` must be [`Ext::ext_single_valued`], unconditional.
    pub fn ext_at_x(&self, sv_g: &Thm) -> Option<Thm> {
        if !self.inputs_unconditional() || !sv_g.hyps().is_empty() {
            return None
        }
        let v = self.value();
        let mem = Thm::mp(&self.new_point_in_ext(&self.q())?, &Thm::eq_refl(self.q()))?;
        let aog = inst_all(&self.b.app_of_graph, &[self.g(), self.x.clone(), v.clone()])?;
        let out = Thm::mp(&aog, &crate::and_intro(sv_g, &mem))?;
        if *out.concl() != Formula::eq(self.b.app(&self.g(), &self.x), v) {
            return None
        }
        Some(out)
    }
}

/// The induction step's hypothesis, as one formula:
///
/// ```text
/// K := (step_typed(A,R,T,e) ∧ x ∈ A)
///        ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ indom(accrec,y))))
/// ```
///
/// Left-nested, and built in one place, because every lemma below rebuilds it
/// and they must agree on the nose. The second conjunct is
/// [`crate::acc::acc_rect`]'s induction hypothesis at `φ(z) := indom(accrec,z)`.
pub fn hypothesis(env: &mut Env, e: &Ext, x: &Term) -> Formula {
    let b = e.b;
    let (ta, tr, tt, te) = (&e.ps[0], &e.ps[1], &e.ps[2], &e.ps[3]);
    let st = step_typed(env, b, ta, tr, tt, te);
    let mem_xa = Formula::mem(x.clone(), ta.clone());

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let ihd = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::imp(
                Formula::mem(b.edge(&ty, x), tr.clone()),
                Formula::and(
                    Formula::mem(ty.clone(), b.acc_of(ta, tr)),
                    b.indom(env, &e.rec_t(), &ty),
                ),
            ),
        ),
    );
    Formula::and(Formula::and(st, mem_xa), ihd)
}

/// The three projections out of [`hypothesis`].
fn split_k(env: &mut Env, e: &Ext, x: &Term) -> Option<(Thm, Thm, Thm)> {
    let k = hypothesis(env, e, x);
    let (front, ihd) = super::shared::split_and(&k)?;
    let (st, mem_xa) = super::shared::split_and(&front)?;
    let k_front = and_left(front.clone(), ihd.clone());
    Some((
        syl(&k_front, &and_left(st.clone(), mem_xa.clone()))?,
        syl(&k_front, &and_right(st, mem_xa))?,
        and_right(front, ihd),
    ))
}

/// `⊢ K → x ∈ acc(A,R)` — the new point is accessible.
///
/// [`crate::acc::acc_intro`] at `x`, whose two premises are `K`'s second
/// conjunct and the left half of its third. Unconditional there, so nothing is
/// carried — and `K` must be the *only* antecedent, so the view's theorems
/// (`e.b.ac.acc_intro` above all) must carry no `Γ`.
pub fn ext_x_in_acc(env: &mut Env, e: &Ext, x: &Term) -> Option<Thm> {
    if !e.inputs_unconditional() {
        return None
    }
    let b = e.b;
    let (ta, tr) = (e.ps[0].clone(), e.ps[1].clone());
    let (_, k_xa, k_ihd) = split_k(env, e, x)?;
    let k = hypothesis(env, e, x);

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, x), tr.clone());
    let mem_yacc = Formula::mem(ty.clone(), b.acc_of(&ta, &tr));
    let ind = b.indom(env, &e.rec_t(), &ty);

    let at_y = hyp_inst(&k_ihd, std::slice::from_ref(&ty))?;
    let body = hyp_syl(
        &hyp_syl(&a1i(&imp_refl(mem_ya.clone()), k.clone()), &at_y)?,
        &a1i(
            &crate::imp_mono_r(&and_left(mem_yacc.clone(), ind), edge.clone())?,
            k.clone(),
        ),
    )?;
    let k_preds = gen_under(yv, &body)?;
    if *k_preds.concl()
        != Formula::imp(
            k.clone(),
            crate::acc::preds_in(env, b.s.ap.sets.up, &ta, &tr, &b.acc_of(&ta, &tr), x),
        )
    {
        return None
    }
    let intro = inst_all(&b.ac.acc_intro, &[ta.clone(), tr.clone(), x.clone()])?;
    let out = syl(&hyp_and(&k_xa, &k_preds)?, &intro)?;
    if *out.concl() != Formula::imp(k, Formula::mem(x.clone(), b.acc_of(&ta, &tr))) {
        return None
    }
    Some(out)
}

/// `⊢ ∀y. (indom(accrec,y) → app(accrec,y) ∈ T)` — values of the recursor lie in
/// the target.
///
/// Unconditional, and read straight off [`super::union::rec_subset_prod`]: a
/// pair of `accrec` lies in `prod(acc(A,R),T)`, and single-valuedness makes its
/// second component the value.
pub fn rec_value_typed(env: &mut Env, e: &Ext) -> Option<Thm> {
    if !e.inputs_unconditional() {
        return None
    }
    let b = e.b;
    let (ta, tr, tt) = (e.ps[0].clone(), e.ps[1].clone(), e.ps[2].clone());
    let (yv, wv) = (env.fresh_var(), env.fresh_var());
    let (ty, tw) = (Term::var(yv), Term::var(wv));
    let rec_t = e.rec_t();

    let h = b.indom(env, &rec_t, &ty);
    let pair = b.s.ap.sets.pair(ty.clone(), tw.clone());
    let mem = Formula::mem(pair.clone(), rec_t.clone());
    let m = Formula::and(h.clone(), mem.clone());
    let m_mem = and_right(h.clone(), mem);

    let sub = inst_all(e.facts.subset_prod, &e.ps)?;
    let m_inprod = hyp_mp(
        &a1i(
            &Thm::mp(&Thm::ax_inst(sub.concl().clone(), pair.clone())?, &sub)?,
            m.clone(),
        ),
        &m_mem,
    )?;
    let pip = inst_all(
        &b.s.pair_in_prod,
        &[b.acc_of(&ta, &tr), tt.clone(), ty.clone(), tw.clone()],
    )?;
    let m_wt = syl(
        &syl(&m_inprod, &iff_mp(&pip)?)?,
        &and_right(
            Formula::mem(ty.clone(), b.acc_of(&ta, &tr)),
            Formula::mem(tw.clone(), tt.clone()),
        ),
    )?;
    let aog = inst_all(&b.app_of_graph, &[rec_t.clone(), ty.clone(), tw.clone()])?;
    let sv = inst_all(e.facts.single_valued, &e.ps)?;
    let m_val = hyp_mp(
        &a1i(&aog, m.clone()),
        &hyp_and(&a1i(&sv, m.clone()), &m_mem)?,
    )?;
    let m_val_sym = crate::wrec::hyp_eq_symm(env, &m_val)?;
    let m_goal = hyp_mp(
        &hyp_leibniz(env, &m_val_sym, |z| Formula::mem(z, tt.clone()))?,
        &m_wt,
    )?;
    if *m_goal.concl() != Formula::imp(m, Formula::mem(b.app(&rec_t, &ty), tt.clone())) {
        return None
    }
    let out = hyp_exists_elim(wv, &m_goal, &imp_refl(h))?;
    Some(Thm::gen(yv, &out))
}

/// `⊢ K → V ∈ T` — **where `step_typed` is spent**.
///
/// The chain is: the induction hypothesis puts every predecessor of `x` in
/// `accrec`'s domain, [`rec_value_typed`] puts their values in `T`, so
/// [`super::ih::ih_typed`] puts `ih(accrec,A,R,x)` in `ih_bound(A,T)`, and
/// `step_typed` at the accessible point `x` types the step.
///
/// `rvt` must be [`rec_value_typed`], unconditional: `K` is what this theorem
/// advertises as its one antecedent.
pub fn ext_value_typed(env: &mut Env, e: &Ext, x: &Term, rvt: &Thm) -> Option<Thm> {
    if !e.inputs_unconditional() || !rvt.hyps().is_empty() {
        return None
    }
    let b = e.b;
    let (ta, tr, tt, te) = (
        e.ps[0].clone(),
        e.ps[1].clone(),
        e.ps[2].clone(),
        e.ps[3].clone(),
    );
    let k = hypothesis(env, e, x);
    let (k_st, _, k_ihd) = split_k(env, e, x)?;
    let rec_t = e.rec_t();

    // `K → preds_typed(accrec,A,R,T,x)`.
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, x), tr.clone());
    let mem_yacc = Formula::mem(ty.clone(), b.acc_of(&ta, &tr));
    let ind_y = b.indom(env, &rec_t, &ty);

    let at_y = hyp_inst(&k_ihd, std::slice::from_ref(&ty))?;
    let rvt_y = Thm::mp(&Thm::ax_inst(rvt.concl().clone(), ty.clone())?, rvt)?;
    let tail = a1i(
        &crate::imp_mono_r(
            &syl(&and_right(mem_yacc, ind_y), &rvt_y)?,
            edge.clone(),
        )?,
        k.clone(),
    );
    let body = hyp_syl(
        &hyp_syl(&a1i(&imp_refl(mem_ya.clone()), k.clone()), &at_y)?,
        &tail,
    )?;
    let k_pt = gen_under(yv, &body)?;
    if *k_pt.concl()
        != Formula::imp(
            k.clone(),
            preds_typed(env, &b.s, &rec_t, &ta, &tr, &tt, x),
        )
    {
        return None
    }

    // `K → ih(accrec,A,R,x) ∈ ih_bound(A,T)`, then `step_typed` at `x`.
    let it = inst_all(
        &b.ih_typed,
        &[rec_t.clone(), ta.clone(), tr.clone(), tt.clone(), x.clone()],
    )?;
    let k_ih = syl(&k_pt, &it)?;
    let k_xacc = ext_x_in_acc(env, e, x)?;
    let st_x = hyp_inst(&k_st, std::slice::from_ref(x))?;
    let k_inner = hyp_mp(&st_x, &k_xacc)?;
    let out = hyp_mp(
        &hyp_inst(&k_inner, &[b.ih_at(&rec_t, &ta, &tr, x)])?,
        &k_ih,
    )?;
    if *out.concl() != Formula::imp(k, Formula::mem(e.value(), tt)) {
        return None
    }
    let _ = te;
    Some(out)
}

/// `⊢ K → G ⊆ prod(acc(A,R),T)` — the extension stays inside the bound.
///
/// `vt` must be [`ext_value_typed`], and must be unconditional: it already
/// carries `K` inside its conclusion, which is honest; a `Γ` on top would not
/// be.
pub fn ext_bound(env: &mut Env, e: &Ext, x: &Term, vt: &Thm) -> Option<Thm> {
    if !e.inputs_unconditional() || !vt.hyps().is_empty() {
        return None
    }
    let b = e.b;
    let (ta, tr, tt) = (e.ps[0].clone(), e.ps[1].clone(), e.ps[2].clone());
    let k = hypothesis(env, e, x);
    let prod_t = b.s.prod.of(b.acc_of(&ta, &tr), tt.clone());

    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let mem_g = Formula::mem(tz.clone(), e.g());
    let goal = Formula::mem(tz.clone(), prod_t.clone());
    let kk = Formula::and(k.clone(), mem_g.clone());
    let kk_k = and_left(k.clone(), mem_g.clone());
    let kk_g = and_right(k.clone(), mem_g);
    let kk_disj = syl(&kk_g, &iff_mp(&e.ext_members(&tz)?)?)?;

    // Left: it came from `accrec`, which is inside the product.
    let sub = inst_all(e.facts.subset_prod, &e.ps)?;
    let left = a1i(
        &Thm::mp(&Thm::ax_inst(sub.concl().clone(), tz.clone())?, &sub)?,
        kk.clone(),
    );

    // Right: it *is* `q = ⟨x,V⟩`, and both components are typed.
    let k_xacc = ext_x_in_acc(env, e, x)?;
    let k_vt = vt.clone();
    let pip = inst_all(
        &b.s.pair_in_prod,
        &[b.acc_of(&ta, &tr), tt, x.clone(), e.value()],
    )?;
    let kk_q = syl(
        &hyp_and(
            &syl(&kk_k, &k_xacc)?,
            &syl(&kk_k, &k_vt)?,
        )?,
        &iff_mpr(&pip)?,
    )?;
    let eqz = Formula::eq(tz.clone(), e.q());
    let l = Formula::and(kk.clone(), eqz.clone());
    let kk_qz = crate::wrec::hyp_eq_symm(env, &and_right(kk.clone(), eqz.clone()))?;
    let l_q = syl(&and_left(kk.clone(), eqz), &kk_q)?;
    let l_goal = hyp_mp(
        &hyp_leibniz(env, &kk_qz, |w| Formula::mem(w, prod_t.clone()))?,
        &l_q,
    )?;
    if *l_goal.concl() != Formula::imp(l, goal.clone()) {
        return None
    }
    let right = uncurry(&l_goal)?;

    let kk_goal = hyp_or_elim(&kk_disj, &left, &right)?;
    if *kk_goal.concl() != Formula::imp(kk, goal.clone()) {
        return None
    }
    let body = uncurry(&kk_goal)?;
    let out = gen_under(zv, &body)?;
    if *out.concl() != Formula::imp(k, kernel::thm::subset(env, e.g(), prod_t)) {
        return None
    }
    Some(out)
}

/// The common core of [`ext_rec_cond`]'s two cases.
///
/// From "every `R`-predecessor of `z` inside `A` is in `accrec`'s domain" and
/// "`app(G,z)` is the step at `accrec`'s induction hypothesis", conclude the two
/// clauses of `rec_cond` at `z`. Written once because the old points and the new
/// point differ only in where those two facts come from.
fn core(env: &mut Env, e: &Ext, z: &Term, sv_g: &Thm, h: &Formula, h_preds: &Thm, h_eqn: &Thm) -> Option<Thm> {
    let b = e.b;
    let (ta, tr, te) = (e.ps[0].clone(), e.ps[1].clone(), e.ps[3].clone());
    let rec_t = e.rec_t();
    let g = e.g();

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, z), tr.clone());
    let ind_y = b.indom(env, &rec_t, &ty);

    let at_y = hyp_inst(h_preds, std::slice::from_ref(&ty))?;

    // First clause: predecessors are in `G`'s domain.
    let to_g = a1i(
        &crate::imp_mono_r(
            &crate::imp_mono_r(&e.ext_indom(env, &ty)?, edge.clone())?,
            mem_ya.clone(),
        )?,
        h.clone(),
    );
    let h_preds_g = gen_under(yv, &hyp_mp(&to_g, &at_y)?)?;
    if *h_preds_g.concl() != Formula::imp(h.clone(), preds_indom(env, b, &ta, &tr, &g, z)) {
        return None
    }

    // Second clause: the two induction hypotheses agree, so the step does.
    let app_eq = e.ext_app(env, &ty, sv_g)?;
    let flip = crate::eq_symm_imp(env, b.app(&g, &ty), b.app(&rec_t, &ty));
    let to_agree = a1i(
        &crate::imp_mono_r(
            &crate::imp_mono_r(&syl(&app_eq, &flip)?, edge.clone())?,
            mem_ya.clone(),
        )?,
        h.clone(),
    );
    let h_pa = gen_under(yv, &hyp_mp(&to_agree, &at_y)?)?;
    if *h_pa.concl()
        != Formula::imp(h.clone(), preds_agree(env, &b.s, &rec_t, &g, &ta, &tr, z))
    {
        return None
    }
    let _ = ind_y;
    let ie = inst_all(
        &b.ih_ext,
        &[rec_t.clone(), g.clone(), ta.clone(), tr.clone(), z.clone()],
    )?;
    let h_ih = syl(&h_pa, &ie)?;
    let (te2, z2) = (te.clone(), z.clone());
    let bb = b;
    let h_step = hyp_congr(env, &h_ih, move |t| bb.step_at(&te2, &z2, &t))?;
    let h_final = hyp_eq_trans(env, h_eqn, &h_step)?;
    hyp_and(&h_preds_g, &h_final)
}

/// `⊢ K → rec_cond(A,R,e,G)` — **the extension satisfies the recursion
/// condition**.
///
/// Two cases at a point `z` of `G`'s domain, both routed through [`core`]:
/// either `z` was already in `accrec`'s domain — and then `accrec`'s own
/// `rec_cond` supplies both premises — or `z = x`, and then the induction
/// hypothesis supplies the first and [`Ext::ext_at_x`] the second, since `V`
/// *is* the step at `accrec`'s induction hypothesis.
///
/// `sv_g` ([`Ext::ext_single_valued`]) and `rec_rc`
/// ([`super::is_attempt::rec_rec_cond`]) must both be unconditional; `K` is the
/// one antecedent this theorem advertises.
#[allow(clippy::too_many_arguments)]
pub fn ext_rec_cond(
    env: &mut Env,
    e: &Ext,
    x: &Term,
    sv_g: &Thm,
    rec_rc: &Thm,
) -> Option<Thm> {
    if !e.inputs_unconditional() || !crate::all_unconditional(&[sv_g, rec_rc]) {
        return None
    }
    let b = e.b;
    let (ta, tr, te) = (e.ps[0].clone(), e.ps[1].clone(), e.ps[3].clone());
    let k = hypothesis(env, e, x);
    let (_, _, k_ihd) = split_k(env, e, x)?;
    let rec_t = e.rec_t();
    let g = e.g();

    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let ind_gz = b.indom(env, &g, &tz);
    let goal = Formula::and(
        preds_indom(env, b, &ta, &tr, &g, &tz),
        Formula::eq(b.app(&g, &tz), b.step_at(&te, &tz, &b.ih_at(&g, &ta, &tr, &tz))),
    );

    // ── Case A: `z` is already in `accrec`'s domain ─────────────────────────
    let ind_rz = b.indom(env, &rec_t, &tz);
    let ha = Formula::and(k.clone(), ind_rz.clone());
    let ha_ind = and_right(k.clone(), ind_rz.clone());
    let rc_at = {
        let at = inst_all(rec_rc, &e.ps)?;
        Thm::mp(&Thm::ax_inst(at.concl().clone(), tz.clone())?, &at)?
    };
    let ha_fired = hyp_mp(&a1i(&rc_at, ha.clone()), &ha_ind)?;
    let preds_r = preds_indom(env, b, &ta, &tr, &rec_t, &tz);
    let eqn_r = Formula::eq(
        b.app(&rec_t, &tz),
        b.step_at(&te, &tz, &b.ih_at(&rec_t, &ta, &tr, &tz)),
    );
    let ha_preds = syl(&ha_fired, &and_left(preds_r.clone(), eqn_r.clone()))?;
    let ha_eqr = syl(&ha_fired, &and_right(preds_r, eqn_r))?;
    let ha_app = hyp_mp(&a1i(&e.ext_app(env, &tz, sv_g)?, ha.clone()), &ha_ind)?;
    let ha_eqn = hyp_eq_trans(env, &ha_app, &ha_eqr)?;
    let case_a = uncurry(&core(env, e, &tz, sv_g, &ha, &ha_preds, &ha_eqn)?)?;

    // ── Case B: `z = x` ─────────────────────────────────────────────────────
    let eq_zx = Formula::eq(tz.clone(), x.clone());
    let hb = Formula::and(k.clone(), eq_zx.clone());
    let hb_eq = and_right(k.clone(), eq_zx.clone());
    let hb_k = and_left(k.clone(), eq_zx);
    // At `x` itself: the induction hypothesis, and `app(G,x) = V`.
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge_x = Formula::mem(b.edge(&ty, x), tr.clone());
    let mem_yacc = Formula::mem(ty.clone(), b.acc_of(&ta, &tr));
    let ind_y = b.indom(env, &rec_t, &ty);
    let at_y = hyp_inst(&k_ihd, std::slice::from_ref(&ty))?;
    let drop_acc = a1i(
        &crate::imp_mono_r(
            &crate::imp_mono_r(&and_right(mem_yacc, ind_y), edge_x)?,
            mem_ya,
        )?,
        k.clone(),
    );
    let k_preds_x = gen_under(yv, &hyp_mp(&drop_acc, &at_y)?)?;
    if *k_preds_x.concl()
        != Formula::imp(k.clone(), preds_indom(env, b, &ta, &tr, &rec_t, x))
    {
        return None
    }
    let k_eqn_x = a1i(&e.ext_at_x(sv_g)?, k.clone());
    let k_core_x = core(env, e, x, sv_g, &k, &k_preds_x, &k_eqn_x)?;
    let hb_core = syl(&hb_k, &k_core_x)?;
    // Carry it back along `z = x`, through one Leibniz at an explicit hole.
    let hole = env.fresh_var();
    let tw_hole = Term::var(hole);
    let goal_hole = Formula::and(
        preds_indom(env, b, &ta, &tr, &g, &tw_hole),
        Formula::eq(
            b.app(&g, &tw_hole),
            b.step_at(&te, &tw_hole, &b.ih_at(&g, &ta, &tr, &tw_hole)),
        ),
    );
    let leib = Thm::eq_leibniz(x.clone(), tz.clone(), hole, goal_hole);
    let hb_x_eq_z = crate::wrec::hyp_eq_symm(env, &hb_eq)?;
    let hb_goal = hyp_mp(&hyp_mp(&a1i(&leib, hb.clone()), &hb_x_eq_z)?, &hb_core)?;
    if *hb_goal.concl() != Formula::imp(hb, goal.clone()) {
        return None
    }
    let case_b = uncurry(&hb_goal)?;

    // ── The two cases exhaust `G`'s domain ──────────────────────────────────
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    let pair = b.s.ap.sets.pair(tz.clone(), tw.clone());
    let hz = Formula::and(k.clone(), ind_gz.clone());
    let hz_k = and_left(k.clone(), ind_gz.clone());
    let mem_pair_g = Formula::mem(pair.clone(), g.clone());
    let n = Formula::and(hz.clone(), mem_pair_g.clone());
    let n_pair = and_right(hz.clone(), mem_pair_g.clone());
    let n_k = syl(&and_left(hz.clone(), mem_pair_g), &hz_k)?;
    let n_disj = syl(&n_pair, &iff_mp(&e.ext_members(&pair)?)?)?;

    let n_left = hyp_syl(
        &a1i(&indom_intro(env, b, &rec_t, &tz, &tw)?, n.clone()),
        &syl(&n_k, &case_a)?,
    )?;
    let n_right = {
        let pi = inst_all(
            &b.s.ap.pair_inj,
            &[tz.clone(), tw.clone(), x.clone(), e.value()],
        )?;
        let to_eq = syl(
            &pi,
            &and_left(
                Formula::eq(tz.clone(), x.clone()),
                Formula::eq(tw.clone(), e.value()),
            ),
        )?;
        hyp_syl(&a1i(&to_eq, n.clone()), &syl(&n_k, &case_b)?)?
    };
    let n_goal = hyp_or_elim(&n_disj, &n_left, &n_right)?;
    if *n_goal.concl() != Formula::imp(n, goal.clone()) {
        return None
    }
    let hz_goal = hyp_exists_elim(wv, &n_goal, &and_right(k.clone(), ind_gz.clone()))?;
    if *hz_goal.concl() != Formula::imp(hz, goal.clone()) {
        return None
    }
    let out = gen_under(zv, &uncurry(&hz_goal)?)?;
    if *out.concl() != Formula::imp(k, rec_cond(env, b, &ta, &tr, &te, &g)) {
        return None
    }
    Some(out)
}

/// `⊢ K → G ∈ Att(A,R,T,e)` — **the extension is an attempt**.
///
/// All three theorem arguments must be unconditional; the membership is pinned
/// in release against `att_of(e.att, …)`, so a foreign biconditional cannot
/// relabel the result as being about `Att`.
pub fn ext_is_attempt(
    env: &mut Env,
    e: &Ext,
    x: &Term,
    bound: &Thm,
    sv_g: &Thm,
    rc: &Thm,
) -> Option<Thm> {
    if !e.inputs_unconditional() || !crate::all_unconditional(&[bound, sv_g, rc]) {
        return None
    }
    let b = e.b;
    let (ta, tr, tt, te) = (
        e.ps[0].clone(),
        e.ps[1].clone(),
        e.ps[2].clone(),
        e.ps[3].clone(),
    );
    let k = hypothesis(env, e, x);
    let g = e.g();

    let pow_at = inst_all(
        &b.s.pow_ax,
        &[b.s.prod.of(b.acc_of(&ta, &tr), tt.clone()), g.clone()],
    )?;
    let k_pow = syl(bound, &iff_mpr(&pow_at)?)?;
    if *k_pow.concl() != Formula::imp(k.clone(), Formula::mem(g.clone(), attempt_bound(b, &ta, &tr, &tt)))
    {
        return None
    }
    let k_cond = hyp_and(&a1i(sv_g, k.clone()), rc)?;
    let at = inst_all(e.att_ax, &[ta.clone(), tr.clone(), tt.clone(), te.clone(), g.clone()])?;
    let out = syl(&hyp_and(&k_pow, &k_cond)?, &iff_mpr(&at)?)?;
    if *out.concl()
        != Formula::imp(k, Formula::mem(g, att_of(e.att, ta, tr, tt, te)))
    {
        return None
    }
    Some(out)
}

