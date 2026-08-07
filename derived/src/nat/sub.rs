//! **Truncated subtraction on `ω`**: the predecessor, `sub`, and the zero test.
//!
//! # Interface
//!
//! ```text
//! pred(n)     the predecessor, with pred(0) = 0
//! sub(x,y)    x ∸ y, truncated at 0
//! iszero(n)   sub(1, n) — `succ 0` at 0 and `0` at every successor
//!
//! ⊢ pred(0) = 0                                                [Sub::pred_zero]
//! ⊢ ∀n. (n ∈ ω → pred(succ n) = n)                             [Sub::pred_succ]
//! ⊢ ∀n. (n ∈ ω → pred n ∈ ω)                                    [Sub::pred_mem]
//!
//! ⊢ ∀x. sub(x, 0) = x                                          [Sub::sub_zero]
//! ⊢ ∀x ∀y. (y ∈ ω → sub(x, succ y) = pred(sub(x,y)))           [Sub::sub_succ]
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → sub(x,y) ∈ ω))                     [Sub::sub_mem]
//! ⊢ ∀y. (y ∈ ω → sub(0, y) = 0)                                [Sub::zero_sub]
//! ⊢ ∀x ∀y. (y ∈ ω → sub(pred x, y) = pred(sub(x,y)))           [Sub::sub_pred]
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω →
//!        sub(succ x, succ y) = sub(x,y)))                 [Sub::sub_succ_succ]
//!
//! ⊢ iszero(0) = succ 0                                       [Sub::iszero_zero]
//! ⊢ ∀n. (n ∈ ω → iszero(succ n) = 0)                         [Sub::iszero_succ]
//! ⊢ ∀n. (n ∈ ω → iszero n ∈ ω)                                [Sub::iszero_mem]
//! ```
//!
//! # Why the predecessor needs the accumulator, and `add` did not
//!
//! [`crate::nat::prim_rec`] gives `f(x, succ n) = g(x, f(x,n))`: the step sees
//! the *parameter* and the *value so far*, and **not the index `n`**. `pred` is
//! the smallest operation that needs the index — `pred(succ n) = n` reads
//! nothing else — so it cannot be written as a `prim_rec` step directly. That is
//! the same wall [`crate::nat::apparatus`] hits for `natrec` and
//! [`crate::nat::prim`] hits for a parametric step, and the answer is the same
//! one: **put what the step needs into the state**. Iterate on the pair
//!
//! ```text
//! pp(x, 0)      = ⟨0, 0⟩
//! pp(x, succ n) = ⟨succ(p1(pp(x,n))), p1(pp(x,n))⟩
//! ```
//!
//! whose first component *is* the index ([`Sub::pp_fst`], one induction), and
//! read the predecessor off the second. The parameter `x` is unused — `pred` is
//! unary — and `pred` is taken at `x := 0`.
//!
//! `sub` then needs nothing new: its step `a ↦ pred a` mentions neither the
//! index nor the parameter, so it is a plain [`crate::nat::prim_rec`] with the
//! first argument carried along.
//!
//! # Why truncated subtraction is the right primitive for a *comparison*
//!
//! `x ≤ y` iff `x ∸ y = 0`, and the eight binary recursion equations a
//! comparison needs are then **equations about `sub`**, provable by ordinary
//! induction. The alternative — an order relation, its totality, and a
//! characteristic function of a formula — needs a linear order on `ω` that
//! `derived/` does not have, and turns every recursion equation into a
//! classical case split on a disjunction. Nothing below is a disjunction and
//! nothing below is a negation; every step is an equation between terms of `ω`,
//! which is what makes it cost the same as [`crate::nat::add`].

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{define_abbrev, eq_symm, inst_all, inst_self};

use super::apparatus::Nat;
use super::glue::{congr1, gen_all, induct, induct_step, Chain};
use super::prim::{prim_rec, PrimRec};

/// Truncated subtraction on `ω` and everything proved about it.
pub struct Sub {
    /// The paired recursion `pp(x,n) = ⟨n, pred n⟩` the predecessor is read off.
    pub pp: PrimRec,
    /// `⊢ ∀n. (n ∈ ω → p1(pp(0,n)) = n)` — the state really carries the index.
    pub pp_fst: Thm,
    /// The symbol `pred(n)`.
    pub pred: FnSym,
    /// `⊢ ∀n. pred(n) = p2(pp(0,n))`.
    pub pred_ax: Thm,
    /// `⊢ pred(0) = 0`.
    pub pred_zero: Thm,
    /// `⊢ ∀n. (n ∈ ω → pred(succ n) = n)`.
    pub pred_succ: Thm,
    /// `⊢ ∀n. (n ∈ ω → pred n ∈ ω)`.
    pub pred_mem: Thm,
    /// The recursion `sub` was built from; `sub` is `rec.sym`.
    pub rec: PrimRec,
    /// `⊢ ∀x. sub(x, 0) = x`.
    pub sub_zero: Thm,
    /// `⊢ ∀x ∀y. (y ∈ ω → sub(x, succ y) = pred(sub(x,y)))`.
    pub sub_succ: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → sub(x,y) ∈ ω))`.
    pub sub_mem: Thm,
    /// `⊢ ∀y. (y ∈ ω → sub(0, y) = 0)`.
    pub zero_sub: Thm,
    /// `⊢ ∀x ∀y. (y ∈ ω → sub(pred x, y) = pred(sub(x,y)))`.
    pub sub_pred: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → sub(succ x, succ y) = sub(x,y)))`.
    pub sub_succ_succ: Thm,
    /// The symbol `iszero(n)`.
    pub iszero: FnSym,
    /// `⊢ ∀n. iszero(n) = sub(succ 0, n)`.
    pub iszero_ax: Thm,
    /// `⊢ iszero(0) = succ 0`.
    pub iszero_zero: Thm,
    /// `⊢ ∀n. (n ∈ ω → iszero(succ n) = 0)`.
    pub iszero_succ: Thm,
    /// `⊢ ∀n. (n ∈ ω → iszero n ∈ ω)`.
    pub iszero_mem: Thm,
}

impl Sub {
    /// The term `pred(t)`.
    pub fn pred_of(&self, t: Term) -> Term { Term::apply(self.pred, vec![t]) }

    /// The term `sub(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { self.rec.of(a, b) }

    /// The term `iszero(t)`.
    pub fn iszero_of(&self, t: Term) -> Term { Term::apply(self.iszero, vec![t]) }

    /// `⊢ sub(a,b) ∈ ω` from `⊢ a ∈ ω` and `⊢ b ∈ ω`.
    pub fn mem_at(&self, a: &Thm, b: &Thm) -> DResult<Thm> {
        let (ta, _) = a.concl().mem_parts()?;
        let (tb, _) = b.concl().mem_parts()?;
        prim::mp(&prim::mp(&inst_all(&self.sub_mem, &[ta, tb])?, a)?, b)
    }

    /// `⊢ pred(a) ∈ ω` from `⊢ a ∈ ω`.
    pub fn pred_mem_at(&self, a: &Thm) -> DResult<Thm> {
        let (ta, _) = a.concl().mem_parts()?;
        prim::mp(&inst_all(&self.pred_mem, std::slice::from_ref(&ta))?, a)
    }

    /// `⊢ sub(a, succ b) = pred(sub(a,b))` from `⊢ b ∈ ω`.
    pub fn succ_at(&self, a: &Term, b_om: &Thm) -> DResult<Thm> {
        let (b, _) = b_om.concl().mem_parts()?;
        prim::mp(&inst_all(&self.sub_succ, &[a.clone(), b])?, b_om)
    }

    /// `⊢ sub(a, 0) = a`.
    pub fn zero_at(&self, a: &Term) -> DResult<Thm> {
        inst_all(&self.sub_zero, std::slice::from_ref(a))
    }

    /// `⊢ pred(succ a) = a` from `⊢ a ∈ ω`.
    pub fn pred_succ_at(&self, a_om: &Thm) -> DResult<Thm> {
        let (a, _) = a_om.concl().mem_parts()?;
        prim::mp(&inst_all(&self.pred_succ, std::slice::from_ref(&a))?, a_om)
    }

    /// Define `pred`, `sub` and `iszero`, and derive everything above.
    pub fn new(env: &mut Env, nat: &Nat) -> DResult<Sub> {
        let zero = nat.zero();
        let one = nat.succ_of(zero.clone());
        let (p1, p2) = (nat.p1, nat.p2);
        let p1_of = |t: Term| Term::apply(p1, vec![t]);
        let p2_of = |t: Term| Term::apply(p2, vec![t]);
        let succ_sym = nat.core().succ;

        // ── the predecessor, with the index carried in the accumulator ───────
        let pp = {
            let z = zero.clone();
            prim_rec(
                env,
                nat,
                |_x| nat.pair(z.clone(), z.clone()),
                |_x, a| {
                    let fst = Term::apply(p1, vec![a.clone()]);
                    nat.pair(nat.succ_of(fst.clone()), fst)
                },
            )?
        };

        let nv = env.fresh_var();
        let tn = Term::var(nv);
        let pp_at = |n: &Term| pp.of(zero.clone(), n.clone());
        let (pred, pred_ax) = define_abbrev(env, &[nv], &p2_of(pp_at(&tn)))?;
        let pred_of = |t: Term| Term::apply(pred, vec![t]);

        // `pred(0) = p2(pp(0,0)) = p2(⟨0,0⟩) = 0`.
        let pp_zero = inst_all(&pp.at_zero, std::slice::from_ref(&zero))?;
        let pred_zero = {
            let unfold = inst_all(&pred_ax, std::slice::from_ref(&zero))?;
            let strip = inst_all(&nat.p2_pair, &[zero.clone(), zero.clone()])?;
            Chain::from(unfold).then(congr1(env, p2, &pp_zero)?).then(strip).done(env)?
        };

        // `⊢ ∀n. (n ∈ ω → p1(pp(0,n)) = n)` — the one induction the predecessor
        // costs, and the whole content of "the accumulator remembers the index".
        let pp_fst = {
            let phi = Formula::eq(p1_of(pp_at(&tn)), tn.clone());
            let base = {
                let strip = inst_all(&nat.p1_pair, &[zero.clone(), zero.clone()])?;
                Chain::from(congr1(env, p1, &pp_zero)?).then(strip).done(env)?
            };
            let step = induct_step(nat.core(), nv, &phi, |n_om, ih| {
                let adv =
                    prim::mp(&inst_all(&pp.at_succ, &[zero.clone(), tn.clone()])?, n_om)?;
                let inner = p1_of(pp_at(&tn));
                let strip =
                    inst_all(&nat.p1_pair, &[nat.succ_of(inner.clone()), inner.clone()])?;
                Chain::from(congr1(env, p1, &adv)?)
                    .then(strip)
                    .then(congr1(env, succ_sym, ih)?)
                    .done(env)
            })?;
            induct(env, nat.core(), nv, &phi, &base, &step)?
        };

        // `pred(succ n) = p2(⟨succ(p1(pp(0,n))), p1(pp(0,n))⟩) = p1(pp(0,n)) = n`.
        let n_om = nat.in_omega(tn.clone());
        let h_n = assuming(n_om.clone());
        let pred_succ = {
            let sn = nat.succ_of(tn.clone());
            let unfold = inst_all(&pred_ax, std::slice::from_ref(&sn))?;
            let adv = prim::mp(&inst_all(&pp.at_succ, &[zero.clone(), tn.clone()])?, &h_n)?;
            let inner = p1_of(pp_at(&tn));
            let strip = inst_all(&nat.p2_pair, &[nat.succ_of(inner.clone()), inner])?;
            let fst = prim::mp(&inst_all(&pp_fst, std::slice::from_ref(&tn))?, &h_n)?;
            let out = Chain::from(unfold)
                .then(congr1(env, p2, &adv)?)
                .then(strip)
                .then(fst)
                .done(env)?;
            gen_all(&[nv], &discharge(&n_om, &out))?
        };

        let pred_mem = {
            let phi = nat.in_omega(pred_of(tn.clone()));
            let base = {
                let back = eq_symm(env, &pred_zero)?;
                mem_rewrite(env, nat, &back, nat.zero_mem())?
            };
            let step = induct_step(nat.core(), nv, &phi, |n_om2, _ih| {
                let at = prim::mp(&inst_all(&pred_succ, std::slice::from_ref(&tn))?, n_om2)?;
                let back = eq_symm(env, &at)?;
                mem_rewrite(env, nat, &back, n_om2)
            })?;
            induct(env, nat.core(), nv, &phi, &base, &step)?
        };

        // ── truncated subtraction: a plain parametric recursion ──────────────
        let rec = prim_rec(env, nat, |x| x.clone(), |_x, a| Term::apply(pred, vec![a.clone()]))?;
        let sub_zero = rec.at_zero.clone();
        let sub_succ = rec.at_succ.clone();
        let sub_of = |a: &Term, b: &Term| rec.of(a.clone(), b.clone());

        let (xv, yv) = (env.fresh_var(), env.fresh_var());
        let (tx, ty) = (Term::var(xv), Term::var(yv));
        let x_om = nat.in_omega(tx.clone());
        let hx = assuming(x_om.clone());

        let sub_mem = {
            let phi = nat.in_omega(sub_of(&tx, &ty));
            let base = {
                let back = eq_symm(env, &inst_all(&sub_zero, std::slice::from_ref(&tx))?)?;
                mem_rewrite(env, nat, &back, &hx)?
            };
            let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
                let (s, _) = ih.concl().mem_parts()?;
                let pm = prim::mp(&inst_all(&pred_mem, std::slice::from_ref(&s))?, ih)?;
                let eq = prim::mp(&inst_all(&sub_succ, &[tx.clone(), ty.clone()])?, y_om)?;
                let back = eq_symm(env, &eq)?;
                mem_rewrite(env, nat, &back, &pm)
            })?;
            let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
            let at_y = inst_self(yv, &all)?;
            gen_all(&[xv, yv], &discharge(&x_om, &at_y))?
        };

        let zero_sub = {
            let phi = Formula::eq(sub_of(&zero, &ty), zero.clone());
            let base = inst_all(&sub_zero, std::slice::from_ref(&zero))?;
            let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
                let eq = prim::mp(&inst_all(&sub_succ, &[zero.clone(), ty.clone()])?, y_om)?;
                Chain::from(eq)
                    .then(congr1(env, pred, ih)?)
                    .then(pred_zero.clone())
                    .done(env)
            })?;
            induct(env, nat.core(), yv, &phi, &base, &step)?
        };

        // `sub(pred x, y) = pred(sub(x,y))` — `pred` slides through on the left,
        // truncation and all. No hypothesis on `x`: the recursion runs on `y`.
        let sub_pred = {
            let px = pred_of(tx.clone());
            let phi = Formula::eq(sub_of(&px, &ty), pred_of(sub_of(&tx, &ty)));
            let base = Chain::from(inst_all(&sub_zero, std::slice::from_ref(&px))?)
                .then_rev(congr1(
                    env,
                    pred,
                    &inst_all(&sub_zero, std::slice::from_ref(&tx))?,
                )?)
                .done(env)?;
            let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
                let l = prim::mp(&inst_all(&sub_succ, &[px.clone(), ty.clone()])?, y_om)?;
                let r = prim::mp(&inst_all(&sub_succ, &[tx.clone(), ty.clone()])?, y_om)?;
                Chain::from(l)
                    .then(congr1(env, pred, ih)?)
                    .then_rev(congr1(env, pred, &r)?)
                    .done(env)
            })?;
            let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
            gen_all(&[xv], &all)?
        };

        // `sub(succ x, succ y) = sub(x,y)` — one `succ` cancels off each side.
        let sub_succ_succ = {
            let sx = nat.succ_of(tx.clone());
            let phi =
                Formula::eq(sub_of(&sx, &nat.succ_of(ty.clone())), sub_of(&tx, &ty));
            let base = {
                let l = prim::mp(
                    &inst_all(&sub_succ, &[sx.clone(), zero.clone()])?,
                    nat.zero_mem(),
                )?;
                let strip =
                    congr1(env, pred, &inst_all(&sub_zero, std::slice::from_ref(&sx))?)?;
                let ps = prim::mp(&inst_all(&pred_succ, std::slice::from_ref(&tx))?, &hx)?;
                Chain::from(l)
                    .then(strip)
                    .then(ps)
                    .then_rev(inst_all(&sub_zero, std::slice::from_ref(&tx))?)
                    .done(env)?
            };
            let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
                let sy = nat.succ_of(ty.clone());
                let sy_mem = nat.succ_mem_at(y_om)?;
                let l = prim::mp(&inst_all(&sub_succ, &[sx.clone(), sy])?, &sy_mem)?;
                let r = prim::mp(&inst_all(&sub_succ, &[tx.clone(), ty.clone()])?, y_om)?;
                Chain::from(l).then(congr1(env, pred, ih)?).then_rev(r).done(env)
            })?;
            let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
            let at_y = inst_self(yv, &all)?;
            gen_all(&[xv, yv], &discharge(&x_om, &at_y))?
        };

        // ── the zero test ────────────────────────────────────────────────────
        let (iszero, iszero_ax) = define_abbrev(env, &[nv], &sub_of(&one, &tn))?;
        let iszero_of = |t: Term| Term::apply(iszero, vec![t]);
        let iszero_zero = Chain::from(inst_all(&iszero_ax, std::slice::from_ref(&zero))?)
            .then(inst_all(&sub_zero, std::slice::from_ref(&one))?)
            .done(env)?;

        let iszero_succ = {
            let phi = Formula::eq(iszero_of(nat.succ_of(tn.clone())), zero.clone());
            let base = {
                let unfold = inst_all(&iszero_ax, std::slice::from_ref(&one))?;
                let peel = prim::mp(
                    &inst_all(&sub_succ, &[one.clone(), zero.clone()])?,
                    nat.zero_mem(),
                )?;
                let strip =
                    congr1(env, pred, &inst_all(&sub_zero, std::slice::from_ref(&one))?)?;
                let ps = prim::mp(&inst_all(&pred_succ, std::slice::from_ref(&zero))?, nat.zero_mem())?;
                Chain::from(unfold).then(peel).then(strip).then(ps).done(env)?
            };
            let step = induct_step(nat.core(), nv, &phi, |n_om2, ih| {
                let sn = nat.succ_of(tn.clone());
                let sn_mem = nat.succ_mem_at(n_om2)?;
                let unfold = inst_all(&iszero_ax, std::slice::from_ref(&nat.succ_of(sn.clone())))?;
                let peel = prim::mp(&inst_all(&sub_succ, &[one.clone(), sn.clone()])?, &sn_mem)?;
                let refold =
                    eq_symm(env, &inst_all(&iszero_ax, std::slice::from_ref(&sn))?)?;
                Chain::from(unfold)
                    .then(peel)
                    .then(congr1(env, pred, &refold)?)
                    .then(congr1(env, pred, ih)?)
                    .then(pred_zero.clone())
                    .done(env)
            })?;
            induct(env, nat.core(), nv, &phi, &base, &step)?
        };

        let iszero_mem = {
            let one_mem = nat.succ_mem_at(nat.zero_mem())?;
            let m = prim::mp(
                &prim::mp(&inst_all(&sub_mem, &[one.clone(), tn.clone()])?, &one_mem)?,
                &h_n,
            )?;
            let back = eq_symm(env, &inst_all(&iszero_ax, std::slice::from_ref(&tn))?)?;
            let out = mem_rewrite(env, nat, &back, &m)?;
            gen_all(&[nv], &discharge(&n_om, &out))?
        };

        Ok(Sub {
            pp,
            pp_fst,
            pred,
            pred_ax,
            pred_zero,
            pred_succ,
            pred_mem,
            rec,
            sub_zero,
            sub_succ,
            sub_mem,
            zero_sub,
            sub_pred,
            sub_succ_succ,
            iszero,
            iszero_ax,
            iszero_zero,
            iszero_succ,
            iszero_mem,
        })
    }
}

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ ω` infer `Γ ∪ Δ ⊢ b ∈ ω`.
fn mem_rewrite(env: &mut Env, nat: &Nat, ab: &Thm, a_mem: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), nat.omega());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    prim::mp(&prim::mp(&leib, ab)?, a_mem)
}
