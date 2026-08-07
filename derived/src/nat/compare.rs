//! **Comparison on `ω`**: `ble`, `blt` and `beq`, with the binary recursion
//! equations a certified evaluator runs on.
//!
//! # Interface
//!
//! ```text
//! ble(x,y) := iszero(sub(x,y))          1 if x ≤ y, else 0
//! blt(x,y) := iszero(sub(succ x, y))    1 if x < y, else 0
//! beq(x,y) := mul(ble(x,y), ble(y,x))   1 if x = y, else 0
//!
//! ── the eight comparison equations, all under x ∈ ω, y ∈ ω ──────────────
//! ⊢ ble(double  x, double  y) = ble(x,y)                    [Compare::ble_dd]
//! ⊢ ble(double  x, double1 y) = ble(x,y)                    [Compare::ble_d1]
//! ⊢ ble(double1 x, double  y) = blt(x,y)                    [Compare::ble_1d]
//! ⊢ ble(double1 x, double1 y) = ble(x,y)                    [Compare::ble_11]
//! ⊢ blt(double  x, double  y) = blt(x,y)                    [Compare::blt_dd]
//! ⊢ blt(double  x, double1 y) = ble(x,y)                    [Compare::blt_d1]
//! ⊢ blt(double1 x, double  y) = blt(x,y)                    [Compare::blt_1d]
//! ⊢ blt(double1 x, double1 y) = blt(x,y)                    [Compare::blt_11]
//!
//! ── and the four for equality ───────────────────────────────────────────
//! ⊢ beq(double  x, double  y) = beq(x,y)                    [Compare::beq_dd]
//! ⊢ beq(double  x, double1 y) = 0                           [Compare::beq_d1]
//! ⊢ beq(double1 x, double  y) = 0                           [Compare::beq_1d]
//! ⊢ beq(double1 x, double1 y) = beq(x,y)                    [Compare::beq_11]
//!
//! ── the ends, where one side is the numeral 0 ───────────────────────────
//! ⊢ ∀y. (y ∈ ω → ble(0, y) = succ 0)                   [Compare::ble_zero_l]
//! ⊢ ∀x. (x ∈ ω → ble(double  x, 0) = ble(x, 0))         [Compare::ble_d_zero]
//! ⊢ ∀x. (x ∈ ω → ble(double1 x, 0) = 0)                [Compare::ble_d1_zero]
//! ⊢ ∀x. (x ∈ ω → blt(x, 0) = 0)                        [Compare::blt_zero_r]
//! ⊢ ∀y. (y ∈ ω → blt(0, double  y) = blt(0, y))         [Compare::blt_zero_d]
//! ⊢ ∀y. (y ∈ ω → blt(0, double1 y) = succ 0)           [Compare::blt_zero_d1]
//! ⊢ beq(0,0) = succ 0                                 [Compare::beq_zero_zero]
//! ⊢ ∀y. (y ∈ ω → beq(0, double  y) = beq(0, y))         [Compare::beq_zero_d]
//! ⊢ ∀y. (y ∈ ω → beq(0, double1 y) = 0)                [Compare::beq_zero_d1]
//! ⊢ ∀x. (x ∈ ω → beq(double  x, 0) = beq(x, 0))         [Compare::beq_d_zero]
//! ⊢ ∀x. (x ∈ ω → beq(double1 x, 0) = 0)                [Compare::beq_d1_zero]
//! ```
//!
//! # Why the accumulator, and where it went
//!
//! Comparison is the one arithmetic operation on the binary shape that is not a
//! fold: `add` combines the two least significant bits and recurses, but a `≤`
//! decided at the least significant bit can be overturned by *any* higher bit.
//! Coq's answer is `Pos.compare_cont`, which threads an accumulator saying what
//! to return if every remaining bit agrees; the state is three-valued and one
//! pass suffices.
//!
//! Here the accumulator is **`ble` versus `blt`**, exactly as `add` versus
//! `addc` is the carry:
//!
//! ```text
//! ble (2x+1) (2y) = blt x y        blt (2x) (2y+1) = ble x y
//! ```
//!
//! and every other case stays in its own state. Two symbols, eight equations,
//! one pass over the bits — the same shape as [`crate::nat::binary`]'s eight,
//! and it costs the same.
//!
//! # Why there is no order relation here, and no truth value
//!
//! The obvious reading of "`x ≤ y`" is a *relation*, and the obvious way to make
//! a function of it is a characteristic function of a formula. That route needs
//! a linear order on `ω` — reflexivity, transitivity, totality, and the
//! exclusivity of `<` and `≥` — none of which `derived/` has, and it turns each
//! of the equations above into a classical case split on a disjunction.
//!
//! Truncated subtraction avoids all of it. `x ≤ y` iff `x ∸ y = 0`, so `ble` is
//! `iszero ∘ sub` and every equation above is an **equation between terms of
//! `ω`**, proved by the same equational induction the rest of the module uses.
//! Nothing below is a disjunction, a negation, or a case split. The one place
//! the order genuinely shows through is [`Compare::sub_gap`] — `x ≤ y` and
//! `y < x` cannot both hold — and even that is stated as an equation
//! (`iszero(…) = 0`) and proved by a double induction that never mentions a
//! disjunction.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{com12, define_abbrev, eq_symm, inst_all};

use super::add::Add;
use super::apparatus::Nat;
use super::binary::Binary;
use super::glue::{congr1, congr2_l, congr2_r, gen_all, induct, induct_step, Chain};
use super::mul::Mul;
use super::sub::Sub;

/// Comparison on `ω` and everything proved about it.
pub struct Compare {
    /// `⊢ ∀x. (x ∈ ω → double(succ x) = succ(succ(double x)))`.
    pub double_succ: Thm,
    /// `⊢ ∀w. (w ∈ ω → pred(pred(double w)) = double(pred w))`.
    pub pred_pred_double: Thm,
    /// `⊢ ∀n. (n ∈ ω → iszero(double n) = iszero n)`.
    pub iszero_double: Thm,
    /// `⊢ ∀n. (n ∈ ω → iszero(pred(double n)) = iszero n)`.
    pub iszero_pred_double: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → sub(double x, double y) = double(sub(x,y))))`.
    pub sub_dd: Thm,
    /// `… sub(double x, double1 y) = pred(double(sub(x,y)))`.
    pub sub_d1: Thm,
    /// `… sub(double1 x, double y) = pred(double(sub(succ x, y)))`.
    pub sub_1d: Thm,
    /// `… sub(double1 x, double1 y) = double(sub(x,y))`.
    pub sub_11: Thm,
    /// `⊢ ∀a ∀b. (a ∈ ω → (b ∈ ω →
    ///        mul(iszero a, iszero b) = iszero(add(a,b))))` — a product of two
    /// zero tests is the zero test of the sum, which is what makes `beq` a
    /// conjunction without a conjunction.
    pub iszero_add: Thm,
    /// `⊢ ∀u. (u ∈ ω → ∀v. (v ∈ ω →
    ///        iszero(add(sub(u,v), sub(succ v, u))) = 0))` — **`x ≤ y` and
    /// `y < x` cannot both hold**, stated as an equation.
    pub sub_gap: Thm,

    /// The symbol `ble(x,y)`.
    pub ble: FnSym,
    /// `⊢ ∀x ∀y. ble(x,y) = iszero(sub(x,y))`.
    pub ble_ax: Thm,
    /// The symbol `blt(x,y)`.
    pub blt: FnSym,
    /// `⊢ ∀x ∀y. blt(x,y) = iszero(sub(succ x, y))`.
    pub blt_ax: Thm,
    /// The symbol `beq(x,y)`.
    pub beq: FnSym,
    /// `⊢ ∀x ∀y. beq(x,y) = mul(ble(x,y), ble(y,x))`.
    pub beq_ax: Thm,

    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → ble(double x, double y) = ble(x,y)))`.
    pub ble_dd: Thm,
    /// `… ble(double x, double1 y) = ble(x,y)`.
    pub ble_d1: Thm,
    /// `… ble(double1 x, double y) = blt(x,y)`.
    pub ble_1d: Thm,
    /// `… ble(double1 x, double1 y) = ble(x,y)`.
    pub ble_11: Thm,
    /// `… blt(double x, double y) = blt(x,y)`.
    pub blt_dd: Thm,
    /// `… blt(double x, double1 y) = ble(x,y)`.
    pub blt_d1: Thm,
    /// `… blt(double1 x, double y) = blt(x,y)`.
    pub blt_1d: Thm,
    /// `… blt(double1 x, double1 y) = blt(x,y)`.
    pub blt_11: Thm,
    /// `… beq(double x, double y) = beq(x,y)`.
    pub beq_dd: Thm,
    /// `… beq(double x, double1 y) = 0`.
    pub beq_d1: Thm,
    /// `… beq(double1 x, double y) = 0`.
    pub beq_1d: Thm,
    /// `… beq(double1 x, double1 y) = beq(x,y)`.
    pub beq_11: Thm,

    /// `⊢ ∀y. (y ∈ ω → ble(0, y) = succ 0)`.
    pub ble_zero_l: Thm,
    /// `⊢ ∀x. (x ∈ ω → ble(double x, 0) = ble(x, 0))`.
    pub ble_d_zero: Thm,
    /// `⊢ ∀x. (x ∈ ω → ble(double1 x, 0) = 0)`.
    pub ble_d1_zero: Thm,
    /// `⊢ ∀x. (x ∈ ω → blt(x, 0) = 0)`.
    pub blt_zero_r: Thm,
    /// `⊢ ∀y. (y ∈ ω → blt(0, double y) = blt(0, y))`.
    pub blt_zero_d: Thm,
    /// `⊢ ∀y. (y ∈ ω → blt(0, double1 y) = succ 0)`.
    pub blt_zero_d1: Thm,
    /// `⊢ beq(0,0) = succ 0`.
    pub beq_zero_zero: Thm,
    /// `⊢ ∀y. (y ∈ ω → beq(0, double y) = beq(0, y))`.
    pub beq_zero_d: Thm,
    /// `⊢ ∀y. (y ∈ ω → beq(0, double1 y) = 0)`.
    pub beq_zero_d1: Thm,
    /// `⊢ ∀x. (x ∈ ω → beq(double x, 0) = beq(x, 0))`.
    pub beq_d_zero: Thm,
    /// `⊢ ∀x. (x ∈ ω → beq(double1 x, 0) = 0)`.
    pub beq_d1_zero: Thm,
}

impl Compare {
    /// The term `ble(a,b)`.
    pub fn ble_of(&self, a: Term, b: Term) -> Term { Term::apply(self.ble, vec![a, b]) }

    /// The term `blt(a,b)`.
    pub fn blt_of(&self, a: Term, b: Term) -> Term { Term::apply(self.blt, vec![a, b]) }

    /// The term `beq(a,b)`.
    pub fn beq_of(&self, a: Term, b: Term) -> Term { Term::apply(self.beq, vec![a, b]) }

    /// Define the three symbols and derive everything above.
    pub fn new(
        env: &mut Env,
        nat: &Nat,
        ad: &Add,
        bin: &Binary,
        mul: &Mul,
        sb: &Sub,
    ) -> DResult<Compare> {
        let zero = nat.zero();
        let one = nat.succ_of(zero.clone());
        let succ_sym = nat.core().succ;
        let pred = sb.pred;
        let iszero = sb.iszero;
        let sub_sym = sb.rec.sym;
        let mul_sym = mul.pr.sym;
        let (dbl, dbl1) = (bin.double, bin.double1);

        let (xv, yv) = (env.fresh_var(), env.fresh_var());
        let (tx, ty) = (Term::var(xv), Term::var(yv));
        let (x_om, y_om) = (nat.in_omega(tx.clone()), nat.in_omega(ty.clone()));
        let (hx, hy) = (assuming(x_om.clone()), assuming(y_om.clone()));

        let d = |t: &Term| Term::apply(dbl, vec![t.clone()]);
        let d1 = |t: &Term| Term::apply(dbl1, vec![t.clone()]);
        let sub_of = |a: &Term, b: &Term| Term::apply(sub_sym, vec![a.clone(), b.clone()]);
        let iz = |t: &Term| Term::apply(iszero, vec![t.clone()]);
        let pr = |t: &Term| Term::apply(pred, vec![t.clone()]);

        // ── `double` at a successor: two `succ`s, and no induction ───────────
        let double_succ = {
            let up = eq_symm(
                env,
                &prim::mp(&inst_all(&bin.succ_double1, std::slice::from_ref(&tx))?, &hx)?,
            )?;
            let down =
                congr1(env, succ_sym, &inst_all(&bin.succ_double, std::slice::from_ref(&tx))?)?;
            let out = Chain::from(up).then_rev(down).done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let double_succ_at = |env: &mut Env, om: &Thm| -> DResult<Thm> {
            let _ = env;
            let (t, _) = om.concl().mem_parts()?;
            prim::mp(&inst_all(&double_succ, std::slice::from_ref(&t))?, om)
        };

        // ── `pred(pred(2w)) = 2·pred w` — the one step `sub_dd` needs ────────
        let pred_pred_double = {
            let phi = Formula::eq(pr(&pr(&d(&tx))), d(&pr(&tx)));
            let base = {
                let d0 = Chain::from(congr1(env, dbl, &sb.pred_zero)?)
                    .then(bin.double_zero.clone())
                    .done(env)?;
                let inner = congr1(env, pred, &bin.double_zero)?;
                Chain::from(congr1(env, pred, &inner)?)
                    .then(congr1(env, pred, &sb.pred_zero)?)
                    .then(sb.pred_zero.clone())
                    .then_rev(d0)
                    .done(env)?
            };
            let step = induct_step(nat.core(), xv, &phi, |w_om, _ih| {
                let ds = double_succ_at(env, w_om)?;
                let dw_mem = prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&tx))?, w_om)?;
                let sdw_mem = nat.succ_mem_at(&dw_mem)?;
                let peel1 = sb.pred_succ_at(&sdw_mem)?;
                let peel2 = sb.pred_succ_at(&dw_mem)?;
                let rhs = congr1(env, dbl, &sb.pred_succ_at(w_om)?)?;
                let once = congr1(env, pred, &ds)?;
                let lifted = congr1(env, pred, &once)?;
                Chain::from(lifted)
                    .then(congr1(env, pred, &peel1)?)
                    .then(peel2)
                    .then_rev(rhs)
                    .done(env)
            })?;
            induct(env, nat.core(), xv, &phi, &base, &step)?
        };

        // ── the zero test collapses a doubling ───────────────────────────────
        let iszero_double = {
            let phi = Formula::eq(iz(&d(&tx)), iz(&tx));
            let base = congr1(env, iszero, &bin.double_zero)?;
            let step = induct_step(nat.core(), xv, &phi, |w_om, _ih| {
                let ds = double_succ_at(env, w_om)?;
                let dw_mem = prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&tx))?, w_om)?;
                let sdw_mem = nat.succ_mem_at(&dw_mem)?;
                let (sdw, _) = sdw_mem.concl().mem_parts()?;
                let l = prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&sdw))?, &sdw_mem)?;
                let r = prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?, w_om)?;
                Chain::from(congr1(env, iszero, &ds)?).then(l).then_rev(r).done(env)
            })?;
            induct(env, nat.core(), xv, &phi, &base, &step)?
        };
        let iszero_pred_double = {
            let phi = Formula::eq(iz(&pr(&d(&tx))), iz(&tx));
            let base = {
                let inner = congr1(env, pred, &bin.double_zero)?;
                Chain::from(congr1(env, iszero, &inner)?)
                    .then(congr1(env, iszero, &sb.pred_zero)?)
                    .done(env)?
            };
            let step = induct_step(nat.core(), xv, &phi, |w_om, _ih| {
                let ds = double_succ_at(env, w_om)?;
                let dw_mem = prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&tx))?, w_om)?;
                let sdw_mem = nat.succ_mem_at(&dw_mem)?;
                let peel = sb.pred_succ_at(&sdw_mem)?;
                let (dw, _) = dw_mem.concl().mem_parts()?;
                let l = prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&dw))?, &dw_mem)?;
                let r = prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?, w_om)?;
                let once = congr1(env, pred, &ds)?;
                let lifted = congr1(env, iszero, &once)?;
                Chain::from(lifted)
                    .then(congr1(env, iszero, &peel)?)
                    .then(l)
                    .then_rev(r)
                    .done(env)
            })?;
            induct(env, nat.core(), xv, &phi, &base, &step)?
        };

        // ── the four binary shapes of `sub` ──────────────────────────────────
        let dx_mem = prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&tx))?, &hx)?;
        let dy_mem = prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&ty))?, &hy)?;
        let sx_mem = nat.succ_mem_at(&hx)?;
        let close2 = |t: &Thm| gen_all(&[xv, yv], &discharge(&x_om, &discharge(&y_om, t)));

        let sub_dd = {
            let phi = Formula::eq(sub_of(&d(&tx), &d(&ty)), d(&sub_of(&tx, &ty)));
            let base = {
                let l = congr2_r(env, sub_sym, &d(&tx), &bin.double_zero)?;
                let z = sb.zero_at(&d(&tx))?;
                let r = congr1(env, dbl, &sb.zero_at(&tx)?)?;
                Chain::from(l).then(z).then_rev(r).done(env)?
            };
            let step = induct_step(nat.core(), yv, &phi, |w_om, ih| {
                let ds = double_succ_at(env, w_om)?;
                let dw_mem =
                    prim::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&ty))?, w_om)?;
                let sdw_mem = nat.succ_mem_at(&dw_mem)?;
                let xy_mem = sb.mem_at(&hx, w_om)?;
                let l = congr2_r(env, sub_sym, &d(&tx), &ds)?;
                let peel1 = sb.succ_at(&d(&tx), &sdw_mem)?;
                let peel2 = congr1(env, pred, &sb.succ_at(&d(&tx), &dw_mem)?)?;
                let once = congr1(env, pred, ih)?;
                let lift = congr1(env, pred, &once)?;
                let (s, _) = xy_mem.concl().mem_parts()?;
                let collapse =
                    prim::mp(&inst_all(&pred_pred_double, std::slice::from_ref(&s))?, &xy_mem)?;
                let rhs = congr1(env, dbl, &sb.succ_at(&tx, w_om)?)?;
                Chain::from(l)
                    .then(peel1)
                    .then(peel2)
                    .then(lift)
                    .then(collapse)
                    .then_rev(rhs)
                    .done(env)
            })?;
            let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
            let at_y = crate::rules::inst_self(yv, &all)?;
            gen_all(&[xv, yv], &discharge(&x_om, &at_y))?
        };
        let dd_at = |env: &mut Env, a: &Thm, b: &Thm| -> DResult<Thm> {
            let _ = env;
            let (ta, _) = a.concl().mem_parts()?;
            let (tb, _) = b.concl().mem_parts()?;
            prim::mp(&prim::mp(&inst_all(&sub_dd, &[ta, tb])?, a)?, b)
        };

        let sub_d1 = {
            let l = congr2_r(env, sub_sym, &d(&tx), &inst_all(&bin.double1_ax, std::slice::from_ref(&ty))?)?;
            let peel = sb.succ_at(&d(&tx), &dy_mem)?;
            let at = dd_at(env, &hx, &hy)?;
            let inner = congr1(env, pred, &at)?;
            close2(&Chain::from(l).then(peel).then(inner).done(env)?)?
        };
        let sub_11 = {
            let l = congr2_l(
                env,
                sub_sym,
                &inst_all(&bin.double1_ax, std::slice::from_ref(&tx))?,
                &d1(&ty),
            )?;
            let r = congr2_r(
                env,
                sub_sym,
                &nat.succ_of(d(&tx)),
                &inst_all(&bin.double1_ax, std::slice::from_ref(&ty))?,
            )?;
            let strip = {
                let (a, _) = dx_mem.concl().mem_parts()?;
                let (b, _) = dy_mem.concl().mem_parts()?;
                prim::mp(
                    &prim::mp(&inst_all(&sb.sub_succ_succ, &[a, b])?, &dx_mem)?,
                    &dy_mem,
                )?
            };
            close2(&Chain::from(l).then(r).then(strip).then(dd_at(env, &hx, &hy)?).done(env)?)?
        };
        let sub_1d = {
            // `double1 x = pred(double(succ x))`, from `succ(double1 x) = double(succ x)`.
            let d1x_mem = prim::mp(&inst_all(&bin.double1_mem, std::slice::from_ref(&tx))?, &hx)?;
            let raw = prim::mp(&inst_all(&bin.succ_double1, std::slice::from_ref(&tx))?, &hx)?;
            let flipped = eq_symm(env, &raw)?;
            let up = congr1(env, pred, &flipped)?;
            let peel = sb.pred_succ_at(&d1x_mem)?;
            let joined = Chain::from(up).then(peel).done(env)?;
            let as_pred = eq_symm(env, &joined)?;
            let l = congr2_l(env, sub_sym, &as_pred, &d(&ty))?;
            let slide = {
                let (b, _) = dy_mem.concl().mem_parts()?;
                prim::mp(
                    &inst_all(&sb.sub_pred, &[d(&nat.succ_of(tx.clone())), b])?,
                    &dy_mem,
                )?
            };
            let at = dd_at(env, &sx_mem, &hy)?;
            let inner = congr1(env, pred, &at)?;
            close2(&Chain::from(l).then(slide).then(inner).done(env)?)?
        };

        // ── a product of zero tests is the zero test of the sum ──────────────
        let iszero_add = {
            let phi = Formula::eq(
                Term::apply(mul_sym, vec![iz(&tx), iz(&ty)]),
                iz(&ad.of(tx.clone(), ty.clone())),
            );
            let izy_mem = prim::mp(&inst_all(&sb.iszero_mem, std::slice::from_ref(&ty))?, &hy)?;
            let base = {
                let l = congr2_l(env, mul_sym, &sb.iszero_zero, &iz(&ty))?;
                let one_l = {
                    let (t, _) = izy_mem.concl().mem_parts()?;
                    prim::mp(&inst_all(&mul.mul_one_l, std::slice::from_ref(&t))?, &izy_mem)?
                };
                let r = congr1(
                    env,
                    iszero,
                    &prim::mp(&inst_all(&ad.add_zero_l, std::slice::from_ref(&ty))?, &hy)?,
                )?;
                Chain::from(l).then(one_l).then_rev(r).done(env)?
            };
            let step = induct_step(nat.core(), xv, &phi, |a_om, _ih| {
                let l = congr2_l(
                    env,
                    mul_sym,
                    &prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?, a_om)?,
                    &iz(&ty),
                )?;
                let zero_l = {
                    let (t, _) = izy_mem.concl().mem_parts()?;
                    prim::mp(&inst_all(&mul.mul_zero_l, std::slice::from_ref(&t))?, &izy_mem)?
                };
                let ab_mem = ad.mem_at(a_om, &hy)?;
                let (ab, _) = ab_mem.concl().mem_parts()?;
                let r = Chain::from(congr1(
                    env,
                    iszero,
                    &prim::mp(&inst_all(&ad.add_succ_l, &[tx.clone(), ty.clone()])?, &hy)?,
                )?)
                .then(prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&ab))?, &ab_mem)?)
                .done(env)?;
                Chain::from(l).then(zero_l).then_rev(r).done(env)
            })?;
            let all = induct(env, nat.core(), xv, &phi, &base, &step)?;
            let at_x = crate::rules::inst_self(xv, &all)?;
            // The induction runs on `a` while `b ∈ ω` is the standing
            // assumption, so discharging in place would state the antecedents
            // `b` first. `com12` puts them back in the order the header claims,
            // which is the order every caller instantiates in.
            let swapped = com12(&discharge(&y_om, &at_x))?;
            gen_all(&[xv, yv], &swapped)?
        };

        // ── `x ≤ y` and `y < x` cannot both hold, as an equation ─────────────
        let sub_gap = {
            let gap = |u: &Term, v: &Term| {
                iz(&ad.of(sub_of(u, v), sub_of(&nat.succ_of(v.clone()), u)))
            };
            let inner = |u: &Term| {
                Formula::forall(
                    yv,
                    Formula::imp(y_om.clone(), Formula::eq(gap(u, &ty), zero.clone())),
                )
            };
            let phi = inner(&tx);
            // `u = 0`: `add(0, succ v) = succ v`, and the zero test of a
            // successor is `0`.
            let base = {
                let sy_mem = nat.succ_mem_at(&hy)?;
                let (sy, _) = sy_mem.concl().mem_parts()?;
                let l = congr2_l(
                    env,
                    ad.add,
                    &prim::mp(&inst_all(&sb.zero_sub, std::slice::from_ref(&ty))?, &hy)?,
                    &sub_of(&sy, &zero),
                )?;
                let r = congr2_r(env, ad.add, &zero, &sb.zero_at(&sy)?)?;
                let collapse =
                    prim::mp(&inst_all(&ad.add_zero_l, std::slice::from_ref(&sy))?, &sy_mem)?;
                let sum = Chain::from(l).then(r).then(collapse).done(env)?;
                let out = Chain::from(congr1(env, iszero, &sum)?)
                    .then(prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&ty))?, &hy)?)
                    .done(env)?;
                gen_all(&[yv], &discharge(&y_om, &out))?
            };
            let step = induct_step(nat.core(), xv, &phi, |u_om, ih| {
                let su = nat.succ_of(tx.clone());
                let su_mem = nat.succ_mem_at(u_om)?;
                let psi = Formula::eq(gap(&su, &ty), zero.clone());
                // `v = 0`: `add(succ u, sub(succ 0, succ u)) = add(succ u, 0)`.
                let inner_base = {
                    let strip = {
                        let (u, _) = u_om.concl().mem_parts()?;
                        let cancel = prim::mp(
                            &prim::mp(
                                &inst_all(&sb.sub_succ_succ, &[zero.clone(), u])?,
                                nat.zero_mem(),
                            )?,
                            u_om,
                        )?;
                        Chain::from(cancel)
                            .then(prim::mp(
                                &inst_all(&sb.zero_sub, std::slice::from_ref(&tx))?,
                                u_om,
                            )?)
                            .done(env)?
                    };
                    let sum = Chain::from(congr2_l(env, ad.add, &sb.zero_at(&su)?, &sub_of(&one, &su))?)
                        .then(congr2_r(env, ad.add, &su, &strip)?)
                        .then(inst_all(&ad.add_zero, std::slice::from_ref(&su))?)
                        .done(env)?;
                    Chain::from(congr1(env, iszero, &sum)?)
                        .then(prim::mp(
                            &inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?,
                            u_om,
                        )?)
                        .done(env)?
                };
                let inner_step = induct_step(nat.core(), yv, &psi, |v_om, _inner_ih| {
                    let sv = nat.succ_of(ty.clone());
                    let sv_mem = nat.succ_mem_at(v_om)?;
                    let (u, _) = u_om.concl().mem_parts()?;
                    let (v, _) = v_om.concl().mem_parts()?;
                    let cancel_l = prim::mp(
                        &prim::mp(&inst_all(&sb.sub_succ_succ, &[u.clone(), v])?, u_om)?,
                        v_om,
                    )?;
                    let cancel_r = prim::mp(
                        &prim::mp(&inst_all(&sb.sub_succ_succ, &[sv.clone(), u.clone()])?, &sv_mem)?,
                        u_om,
                    )?;
                    let sum = Chain::from(congr2_l(
                        env,
                        ad.add,
                        &cancel_l,
                        &sub_of(&nat.succ_of(sv.clone()), &su),
                    )?)
                    .then(congr2_r(env, ad.add, &sub_of(&tx, &ty), &cancel_r)?)
                    .done(env)?;
                    let outer = prim::mp(&inst_all(ih, std::slice::from_ref(&ty))?, v_om)?;
                    Chain::from(congr1(env, iszero, &sum)?).then(outer).done(env)
                })?;
                let all_v = induct(env, nat.core(), yv, &psi, &inner_base, &inner_step)?;
                let _ = su_mem;
                Ok(all_v)
            })?;
            induct(env, nat.core(), xv, &phi, &base, &step)?
        };

        // ── the three symbols ────────────────────────────────────────────────
        let (ble, ble_ax) = define_abbrev(env, &[xv, yv], &iz(&sub_of(&tx, &ty)))?;
        let ble_of = |a: &Term, b: &Term| Term::apply(ble, vec![a.clone(), b.clone()]);
        let (blt, blt_ax) =
            define_abbrev(env, &[xv, yv], &iz(&sub_of(&nat.succ_of(tx.clone()), &ty)))?;
        let _ = blt;
        let (beq, beq_ax) = define_abbrev(
            env,
            &[xv, yv],
            &Term::apply(mul_sym, vec![ble_of(&tx, &ty), ble_of(&ty, &tx)]),
        )?;

        // Each comparison equation: unfold, rewrite the difference, collapse the
        // zero test, refold. Four links, no induction.
        let unfold_ble = |env: &mut Env, a: &Term, b: &Term| -> DResult<Thm> {
            let _ = env;
            inst_all(&ble_ax, &[a.clone(), b.clone()])
        };
        let unfold_blt = |env: &mut Env, a: &Term, b: &Term| -> DResult<Thm> {
            let _ = env;
            inst_all(&blt_ax, &[a.clone(), b.clone()])
        };
        let z1_at = |env: &mut Env, m: &Thm| -> DResult<Thm> {
            let _ = env;
            let (t, _) = m.concl().mem_parts()?;
            prim::mp(&inst_all(&iszero_double, std::slice::from_ref(&t))?, m)
        };
        let z2_at = |env: &mut Env, m: &Thm| -> DResult<Thm> {
            let _ = env;
            let (t, _) = m.concl().mem_parts()?;
            prim::mp(&inst_all(&iszero_pred_double, std::slice::from_ref(&t))?, m)
        };
        let sub_at = |thm: &Thm, a: &Thm, b: &Thm| -> DResult<Thm> {
            let (ta, _) = a.concl().mem_parts()?;
            let (tb, _) = b.concl().mem_parts()?;
            prim::mp(&prim::mp(&inst_all(thm, &[ta, tb])?, a)?, b)
        };

        let xy_mem = sb.mem_at(&hx, &hy)?;
        let sxy_mem = sb.mem_at(&sx_mem, &hy)?;

        let ble_dd = {
            let out = Chain::from(unfold_ble(env, &d(&tx), &d(&ty))?)
                .then(congr1(env, iszero, &sub_at(&sub_dd, &hx, &hy)?)?)
                .then(z1_at(env, &xy_mem)?)
                .then_rev(unfold_ble(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let ble_d1 = {
            let out = Chain::from(unfold_ble(env, &d(&tx), &d1(&ty))?)
                .then(congr1(env, iszero, &sub_at(&sub_d1, &hx, &hy)?)?)
                .then(z2_at(env, &xy_mem)?)
                .then_rev(unfold_ble(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let ble_1d = {
            let out = Chain::from(unfold_ble(env, &d1(&tx), &d(&ty))?)
                .then(congr1(env, iszero, &sub_at(&sub_1d, &hx, &hy)?)?)
                .then(z2_at(env, &sxy_mem)?)
                .then_rev(unfold_blt(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let ble_11 = {
            let out = Chain::from(unfold_ble(env, &d1(&tx), &d1(&ty))?)
                .then(congr1(env, iszero, &sub_at(&sub_11, &hx, &hy)?)?)
                .then(z1_at(env, &xy_mem)?)
                .then_rev(unfold_ble(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };

        // `blt` at a `double` is `ble` at the `double1` one above it, which is
        // exactly the accumulator changing state.
        let shift_d = congr2_l(
            env,
            sub_sym,
            &inst_all(&bin.succ_double, std::slice::from_ref(&tx))?,
            &d(&ty),
        )?;
        let shift_d_1 = congr2_l(
            env,
            sub_sym,
            &inst_all(&bin.succ_double, std::slice::from_ref(&tx))?,
            &d1(&ty),
        )?;
        let shift_d1 = prim::mp(&inst_all(&bin.succ_double1, std::slice::from_ref(&tx))?, &hx)?;

        let blt_dd = {
            let out = Chain::from(unfold_blt(env, &d(&tx), &d(&ty))?)
                .then(congr1(env, iszero, &shift_d)?)
                .then(congr1(env, iszero, &sub_at(&sub_1d, &hx, &hy)?)?)
                .then(z2_at(env, &sxy_mem)?)
                .then_rev(unfold_blt(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let blt_d1 = {
            let out = Chain::from(unfold_blt(env, &d(&tx), &d1(&ty))?)
                .then(congr1(env, iszero, &shift_d_1)?)
                .then(congr1(env, iszero, &sub_at(&sub_11, &hx, &hy)?)?)
                .then(z1_at(env, &xy_mem)?)
                .then_rev(unfold_ble(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let blt_1d = {
            let shift = congr2_l(env, sub_sym, &shift_d1, &d(&ty))?;
            let out = Chain::from(unfold_blt(env, &d1(&tx), &d(&ty))?)
                .then(congr1(env, iszero, &shift)?)
                .then(congr1(env, iszero, &sub_at(&sub_dd, &sx_mem, &hy)?)?)
                .then(z1_at(env, &sxy_mem)?)
                .then_rev(unfold_blt(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let blt_11 = {
            let shift = congr2_l(env, sub_sym, &shift_d1, &d1(&ty))?;
            let out = Chain::from(unfold_blt(env, &d1(&tx), &d1(&ty))?)
                .then(congr1(env, iszero, &shift)?)
                .then(congr1(env, iszero, &sub_at(&sub_d1, &sx_mem, &hy)?)?)
                .then(z2_at(env, &sxy_mem)?)
                .then_rev(unfold_blt(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };

        // ── the ends ─────────────────────────────────────────────────────────
        let ble_zero_l = {
            let out = Chain::from(unfold_ble(env, &zero, &ty)?)
                .then(congr1(
                    env,
                    iszero,
                    &prim::mp(&inst_all(&sb.zero_sub, std::slice::from_ref(&ty))?, &hy)?,
                )?)
                .then(sb.iszero_zero.clone())
                .done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };
        let ble_d_zero = {
            let out = Chain::from(unfold_ble(env, &d(&tx), &zero)?)
                .then(congr1(env, iszero, &sb.zero_at(&d(&tx))?)?)
                .then(z1_at(env, &hx)?)
                .then_rev(
                    Chain::from(unfold_ble(env, &tx, &zero)?)
                        .then(congr1(env, iszero, &sb.zero_at(&tx)?)?)
                        .done(env)?,
                )
                .done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let ble_d1_zero = {
            let (dx, _) = dx_mem.concl().mem_parts()?;
            let out = Chain::from(unfold_ble(env, &d1(&tx), &zero)?)
                .then(congr1(env, iszero, &sb.zero_at(&d1(&tx))?)?)
                .then_rev(congr1(
                    env,
                    iszero,
                    &inst_all(&bin.succ_double, std::slice::from_ref(&tx))?,
                )?)
                .then(prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&dx))?, &dx_mem)?)
                .done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let blt_zero_r = {
            let out = Chain::from(unfold_blt(env, &tx, &zero)?)
                .then(congr1(env, iszero, &sb.zero_at(&nat.succ_of(tx.clone()))?)?)
                .then(prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?, &hx)?)
                .done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let blt_zero_d = {
            let at = prim::mp(
                &prim::mp(&inst_all(&blt_dd, &[zero.clone(), ty.clone()])?, nat.zero_mem())?,
                &hy,
            )?;
            // Read `blt(0, double y) → blt(double 0, double y)`, not the other
            // way: the equation to reach is stated at the numeral `0`, and
            // `blt_dd` is stated at `double 0`.
            let raw = congr2_l(env, blt, &bin.double_zero, &d(&ty))?;
            let fix = eq_symm(env, &raw)?;
            let out = Chain::from(fix).then(at).done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };
        let blt_zero_d1 = {
            let at = prim::mp(
                &prim::mp(&inst_all(&blt_d1, &[zero.clone(), ty.clone()])?, nat.zero_mem())?,
                &hy,
            )?;
            let raw = congr2_l(env, blt, &bin.double_zero, &d1(&ty))?;
            let fix = eq_symm(env, &raw)?;
            let tail = prim::mp(&inst_all(&ble_zero_l, std::slice::from_ref(&ty))?, &hy)?;
            let out = Chain::from(fix).then(at).then(tail).done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };

        // ── equality ─────────────────────────────────────────────────────────
        let unfold_beq = |env: &mut Env, a: &Term, b: &Term| -> DResult<Thm> {
            let _ = env;
            inst_all(&beq_ax, &[a.clone(), b.clone()])
        };
        // `mul(A,B) = mul(A',B')` from `⊢ A = A'` and `⊢ B = B'`. The middle term
        // is read off the two premises rather than passed: a caller that spells
        // it out has to spell the *rewritten* left component, and getting that
        // wrong is a `Thm::mp` failure two hundred lines away.
        let pair_congr = |env: &mut Env, l: &Thm, r: &Thm| -> DResult<Thm> {
            let (_, a2) = l.concl().eq_parts()?;
            let (b1, _) = r.concl().eq_parts()?;
            Chain::from(congr2_l(env, mul_sym, l, &b1)?)
                .then(congr2_r(env, mul_sym, &a2, r)?)
                .done(env)
        };
        let beq_dd = {
            let l = sub_at(&ble_dd, &hx, &hy)?;
            let r = sub_at(&ble_dd, &hy, &hx)?;
            let mid = pair_congr(env, &l, &r)?;
            let out = Chain::from(unfold_beq(env, &d(&tx), &d(&ty))?)
                .then(mid)
                .then_rev(unfold_beq(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        let beq_11 = {
            let l = sub_at(&ble_11, &hx, &hy)?;
            let r = sub_at(&ble_11, &hy, &hx)?;
            let mid = pair_congr(env, &l, &r)?;
            let out = Chain::from(unfold_beq(env, &d1(&tx), &d1(&ty))?)
                .then(mid)
                .then_rev(unfold_beq(env, &tx, &ty)?)
                .done(env)?;
            close2(&out)?
        };
        // The mixed cases: `x ≤ y` times `y < x`, which `sub_gap` says is `0`.
        // `iszero_add` turns the product of the two zero tests into the zero
        // test of the sum, which is the shape `sub_gap` is stated in.
        let gap_at = |env: &mut Env, u_om: &Thm, v_om: &Thm| -> DResult<Thm> {
            let _ = env;
            let (u, _) = u_om.concl().mem_parts()?;
            let (v, _) = v_om.concl().mem_parts()?;
            let inner = prim::mp(&inst_all(&sub_gap, std::slice::from_ref(&u))?, u_om)?;
            prim::mp(&inst_all(&inner, std::slice::from_ref(&v))?, v_om)
        };
        let fold_at = |env: &mut Env, u_om: &Thm, v_om: &Thm| -> DResult<Thm> {
            let _ = env;
            let a_mem = sb.mem_at(u_om, v_om)?;
            let b_mem = sb.mem_at(&nat.succ_mem_at(v_om)?, u_om)?;
            let (pa, _) = a_mem.concl().mem_parts()?;
            let (pb, _) = b_mem.concl().mem_parts()?;
            prim::mp(&prim::mp(&inst_all(&iszero_add, &[pa, pb])?, &a_mem)?, &b_mem)
        };

        let beq_d1 = {
            // `beq(2x, 2y+1) = mul(ble x y, blt y x) = iszero(x∸y + (y+1)∸x) = 0`.
            let l = sub_at(&ble_d1, &hx, &hy)?;
            let r = sub_at(&ble_1d, &hy, &hx)?;
            let mid = pair_congr(env, &l, &r)?;
            let el = unfold_ble(env, &tx, &ty)?;
            let er = unfold_blt(env, &ty, &tx)?;
            let expand = pair_congr(env, &el, &er)?;
            let out = Chain::from(unfold_beq(env, &d(&tx), &d1(&ty))?)
                .then(mid)
                .then(expand)
                .then(fold_at(env, &hx, &hy)?)
                .then(gap_at(env, &hx, &hy)?)
                .done(env)?;
            close2(&out)?
        };
        let beq_1d = {
            // The same with the roles swapped, so the sum needs one `add_comm`
            // before `sub_gap` recognises it.
            let l = sub_at(&ble_1d, &hx, &hy)?;
            let r = sub_at(&ble_d1, &hy, &hx)?;
            let mid = pair_congr(env, &l, &r)?;
            let el = unfold_blt(env, &tx, &ty)?;
            let er = unfold_ble(env, &ty, &tx)?;
            let expand = pair_congr(env, &el, &er)?;
            let sxy = sb.mem_at(&sx_mem, &hy)?;
            let yx = sb.mem_at(&hy, &hx)?;
            let (pa, _) = sxy.concl().mem_parts()?;
            let (pb, _) = yx.concl().mem_parts()?;
            let fold =
                prim::mp(&prim::mp(&inst_all(&iszero_add, &[pa.clone(), pb.clone()])?, &sxy)?, &yx)?;
            let swap = congr1(
                env,
                iszero,
                &prim::mp(&prim::mp(&inst_all(&ad.add_comm, &[pa, pb])?, &sxy)?, &yx)?,
            )?;
            let out = Chain::from(unfold_beq(env, &d1(&tx), &d(&ty))?)
                .then(mid)
                .then(expand)
                .then(fold)
                .then(swap)
                .then(gap_at(env, &hy, &hx)?)
                .done(env)?;
            close2(&out)?
        };

        let ble_zero_at = |env: &mut Env, m: &Thm| -> DResult<Thm> {
            let _ = env;
            let (t, _) = m.concl().mem_parts()?;
            prim::mp(&inst_all(&ble_zero_l, std::slice::from_ref(&t))?, m)
        };
        let one_mem = nat.succ_mem_at(nat.zero_mem())?;
        let beq_zero_zero = {
            let l = ble_zero_at(env, nat.zero_mem())?;
            let mid = Chain::from(congr2_l(env, mul_sym, &l, &ble_of(&zero, &zero))?)
                .then(congr2_r(env, mul_sym, &one, &l)?)
                .done(env)?;
            let collapse =
                prim::mp(&inst_all(&mul.mul_one_l, std::slice::from_ref(&one))?, &one_mem)?;
            Chain::from(unfold_beq(env, &zero, &zero)?).then(mid).then(collapse).done(env)?
        };
        let beq_zero_d = {
            let ld = ble_zero_at(env, &dy_mem)?;
            let rd = prim::mp(&inst_all(&ble_d_zero, std::slice::from_ref(&ty))?, &hy)?;
            let l = ble_zero_at(env, &hy)?;
            let out = Chain::from(unfold_beq(env, &zero, &d(&ty))?)
                .then(congr2_l(env, mul_sym, &ld, &ble_of(&d(&ty), &zero))?)
                .then(congr2_r(env, mul_sym, &one, &rd)?)
                .then_rev(
                    Chain::from(unfold_beq(env, &zero, &ty)?)
                        .then(congr2_l(env, mul_sym, &l, &ble_of(&ty, &zero))?)
                        .done(env)?,
                )
                .done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };
        let beq_zero_d1 = {
            let d1y_mem = prim::mp(&inst_all(&bin.double1_mem, std::slice::from_ref(&ty))?, &hy)?;
            let ld = ble_zero_at(env, &d1y_mem)?;
            let rd = prim::mp(&inst_all(&ble_d1_zero, std::slice::from_ref(&ty))?, &hy)?;
            let out = Chain::from(unfold_beq(env, &zero, &d1(&ty))?)
                .then(congr2_l(env, mul_sym, &ld, &ble_of(&d1(&ty), &zero))?)
                .then(congr2_r(env, mul_sym, &one, &rd)?)
                .then(inst_all(&mul.mul_zero, std::slice::from_ref(&one))?)
                .done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };
        let beq_d_zero = {
            let ld = prim::mp(&inst_all(&ble_d_zero, std::slice::from_ref(&tx))?, &hx)?;
            let rd = ble_zero_at(env, &dx_mem)?;
            let r = ble_zero_at(env, &hx)?;
            let out = Chain::from(unfold_beq(env, &d(&tx), &zero)?)
                .then(congr2_l(env, mul_sym, &ld, &ble_of(&zero, &d(&tx)))?)
                .then(congr2_r(env, mul_sym, &ble_of(&tx, &zero), &rd)?)
                .then_rev(
                    Chain::from(unfold_beq(env, &tx, &zero)?)
                        .then(congr2_r(env, mul_sym, &ble_of(&tx, &zero), &r)?)
                        .done(env)?,
                )
                .done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let beq_d1_zero = {
            let d1x_mem = prim::mp(&inst_all(&bin.double1_mem, std::slice::from_ref(&tx))?, &hx)?;
            let ld = prim::mp(&inst_all(&ble_d1_zero, std::slice::from_ref(&tx))?, &hx)?;
            let rd = ble_zero_at(env, &d1x_mem)?;
            let out = Chain::from(unfold_beq(env, &d1(&tx), &zero)?)
                .then(congr2_l(env, mul_sym, &ld, &ble_of(&zero, &d1(&tx)))?)
                .then(congr2_r(env, mul_sym, &zero, &rd)?)
                .then(prim::mp(&inst_all(&mul.mul_zero_l, std::slice::from_ref(&one))?, &one_mem)?)
                .done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };

        Ok(Compare {
            double_succ,
            pred_pred_double,
            iszero_double,
            iszero_pred_double,
            sub_dd,
            sub_d1,
            sub_1d,
            sub_11,
            iszero_add,
            sub_gap,
            ble,
            ble_ax,
            blt,
            blt_ax,
            beq,
            beq_ax,
            ble_dd,
            ble_d1,
            ble_1d,
            ble_11,
            blt_dd,
            blt_d1,
            blt_1d,
            blt_11,
            beq_dd,
            beq_d1,
            beq_1d,
            beq_11,
            ble_zero_l,
            ble_d_zero,
            ble_d1_zero,
            blt_zero_r,
            blt_zero_d,
            blt_zero_d1,
            beq_zero_zero,
            beq_zero_d,
            beq_zero_d1,
            beq_d_zero,
            beq_d1_zero,
        })
    }
}
