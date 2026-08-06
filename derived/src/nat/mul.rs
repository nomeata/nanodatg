//! **Multiplication on `ω`**, its two Peano equations, and its binary
//! recursion equations.
//!
//! # Interface
//!
//! ```text
//! ── the Peano equations, definitional ───────────────────────────────────
//! ⊢ ∀x. mul(x, 0) = 0                                            [Mul::mul_zero]
//! ⊢ ∀x ∀y. (y ∈ ω → mul(x, succ y) = add(mul(x,y), x))           [Mul::mul_succ]
//!
//! ── typing and distributivity ───────────────────────────────────────────
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → mul(x,y) ∈ ω))                       [Mul::mul_mem]
//! ⊢ ∀x ∀y ∀z. (x ∈ ω → (y ∈ ω → (z ∈ ω →
//!        mul(x, add(y,z)) = add(mul(x,y), mul(x,z)))))            [Mul::mul_dist]
//!
//! ── the binary recursion equations ──────────────────────────────────────
//! ⊢ … mul(x, double  y) = double(mul x y)                      [Mul::mul_double]
//! ⊢ … mul(x, double1 y) = add(double(mul x y), x)             [Mul::mul_double1]
//! ```
//!
//! # Why there are two equations and not four
//!
//! Addition decomposes **both** arguments a bit at a time, so it has four cases
//! (times two for the carry). Multiplication decomposes only the *second*: the
//! first is carried along whole and added in whenever a bit is set. That is
//! schoolbook long multiplication, and it is why the certificate is Θ(bits²)
//! rather than Θ(bits) — one Θ(bits) addition per set bit. Isabelle measures
//! the same shape at the same cost (`2b² − b − 1` rewrites at `b` bits, 8127 at
//! 64), and neither system puts Karatsuba on the kernel-checked path.
//!
//! # Where the content is
//!
//! [`Mul::mul_dist`], and it is the only real induction here besides typing.
//! Both binary equations are two rewrites over it:
//! `mul(x, double y) = mul(x, add(y,y)) = add(mul x y, mul x y) = double(mul x y)`.
//! Distributivity is doing the work that a bespoke `mul(x, 2y) = 2·mul(x,y)`
//! induction would otherwise do, and it is worth having on its own account.
//!
//! `mul` itself comes from [`crate::nat::prim_rec`], because its step
//! `a ↦ add(a, x)` mentions the parameter and so cannot be the fixed unary
//! symbol [`crate::recursion::recursion`] demands.

use kernel::{Env, Formula, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::{eq_symm, gen_all, inst_all, inst_self};

use super::add::Add;
use super::apparatus::Nat;
use super::binary::Binary;
use super::glue::{congr2_l, congr2_r, induct, induct_step, Chain};
use super::prim::{prim_rec, PrimRec};

/// Multiplication on `ω`.
pub struct Mul {
    /// The recursion `mul` was built from; `mul` is `pr.sym`.
    pub pr: PrimRec,
    /// `⊢ ∀x. mul(x, 0) = 0`.
    pub mul_zero: Thm,
    /// `⊢ ∀x ∀y. (y ∈ ω → mul(x, succ y) = add(mul(x,y), x))`.
    pub mul_succ: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → mul(x,y) ∈ ω))`.
    pub mul_mem: Thm,
    /// `⊢ ∀x ∀y ∀z. (x ∈ ω → (y ∈ ω → (z ∈ ω →
    ///        mul(x, add(y,z)) = add(mul(x,y), mul(x,z)))))`.
    pub mul_dist: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → mul(x, double y) = double(mul x y)))`.
    pub mul_double: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → mul(x, double1 y) = add(double(mul x y), x)))`.
    pub mul_double1: Thm,
}

impl Mul {
    /// The term `mul(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { self.pr.of(a, b) }

    /// `⊢ mul(a,b) ∈ ω` from `⊢ a ∈ ω` and `⊢ b ∈ ω`.
    pub fn mem_at(&self, a: &Thm, b: &Thm) -> Option<Thm> {
        let (ta, _) = a.concl().as_mem()?;
        let (tb, _) = b.concl().as_mem()?;
        Thm::mp(&Thm::mp(&inst_all(&self.mul_mem, &[ta, tb])?, a)?, b)
    }

    /// Build `mul` and derive everything above.
    pub fn new(env: &mut Env, nat: &Nat, ad: &Add, bin: &Binary) -> Option<Mul> {
        let zero = nat.zero();
        let add_sym = ad.add;
        let pr = prim_rec(env, nat, |_x| zero.clone(), |x, a| {
            Term::apply(add_sym, vec![a.clone(), x.clone()])
        })?;
        let mul_zero = pr.at_zero.clone();
        let mul_succ = pr.at_succ.clone();

        let (xv, yv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tz) = (Term::var(xv), Term::var(yv), Term::var(zv));
        // No `z ∈ ω` here: the induction on `z` supplies it at the one place it
        // is read, and hoisting it would be a hypothesis nothing discharges.
        let (x_om, y_om) = (nat.in_omega(tx.clone()), nat.in_omega(ty.clone()));
        let (hx, hy) = (assuming(x_om.clone()), assuming(y_om.clone()));
        let mul = |a: &Term, b: &Term| pr.of(a.clone(), b.clone());
        let succ_at = |a: &Term, b_om: &Thm| -> Option<Thm> {
            let (b, _) = b_om.concl().as_mem()?;
            Thm::mp(&inst_all(&mul_succ, &[a.clone(), b])?, b_om)
        };

        // ── typing ───────────────────────────────────────────────────────────
        let mul_mem = {
            let phi = nat.in_omega(mul(&tx, &ty));
            let base = {
                let back = eq_symm(env, &inst_all(&mul_zero, std::slice::from_ref(&tx))?)?;
                mem_rewrite(env, nat, &back, nat.zero_mem())?
            };
            let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
                let m = ad.mem_at(ih, &hx)?;
                let back = eq_symm(env, &succ_at(&tx, y_om)?)?;
                mem_rewrite(env, nat, &back, &m)
            })?;
            let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
            let at_y = inst_self(yv, &all)?;
            gen_all(&[xv, yv], &discharge(&x_om, &at_y))
        };
        let mem_at = |a: &Thm, b: &Thm| -> Option<Thm> {
            let (ta, _) = a.concl().as_mem()?;
            let (tb, _) = b.concl().as_mem()?;
            Thm::mp(&Thm::mp(&inst_all(&mul_mem, &[ta, tb])?, a)?, b)
        };

        // ── distributivity, the one real induction ───────────────────────────
        let mul_dist = {
            let yz = ad.of(ty.clone(), tz.clone());
            let phi = Formula::eq(
                mul(&tx, &yz),
                ad.of(mul(&tx, &ty), mul(&tx, &tz)),
            );
            // Base: `mul(x, add(y,0)) = mul(x,y) = add(mul(x,y), mul(x,0))`.
            let base = {
                let l = congr2_r(env, pr.sym, &tx, &inst_all(&ad.add_zero, std::slice::from_ref(&ty))?)?;
                let r0 = congr2_r(env, add_sym, &mul(&tx, &ty), &inst_all(&mul_zero, std::slice::from_ref(&tx))?)?;
                let r1 = inst_all(&ad.add_zero, std::slice::from_ref(&mul(&tx, &ty)))?;
                let r = Chain::from(r0).then(r1).done(env)?;
                Chain::from(l).then_rev(r).done(env)?
            };
            let step = induct_step(nat.core(), zv, &phi, |z_om2, ih| {
                let yz_mem = ad.mem_at(&hy, z_om2)?;
                let xz_mem = mem_at(&hx, z_om2)?;
                let bump = Thm::mp(&inst_all(&ad.add_succ, &[ty.clone(), tz.clone()])?, z_om2)?;
                let unfold = congr2_r(env, pr.sym, &tx, &bump)?;
                let peel = succ_at(&tx, &yz_mem)?;
                let inner = congr2_l(env, add_sym, ih, &tx)?;
                let assoc = {
                    let at = inst_all(
                        &ad.add_assoc,
                        &[mul(&tx, &ty), mul(&tx, &tz), tx.clone()],
                    )?;
                    Thm::mp(&Thm::mp(&at, &xz_mem)?, &hx)?
                };
                let refold = congr2_r(env, add_sym, &mul(&tx, &ty), &succ_at(&tx, z_om2)?)?;
                Chain::from(unfold).then(peel).then(inner).then(assoc).then_rev(refold).done(env)
            })?;
            let all = induct(env, nat.core(), zv, &phi, &base, &step)?;
            let at_z = inst_self(zv, &all)?;
            gen_all(
                &[xv, yv, zv],
                &discharge(&x_om, &discharge(&y_om, &at_z)),
            )
        };
        let dist_at = |a: &Thm, b: &Thm, c: &Thm| -> Option<Thm> {
            let (ta, _) = a.concl().as_mem()?;
            let (tb, _) = b.concl().as_mem()?;
            let (tc, _) = c.concl().as_mem()?;
            let at = inst_all(&mul_dist, &[ta, tb, tc])?;
            Thm::mp(&Thm::mp(&Thm::mp(&at, a)?, b)?, c)
        };

        // ── the two binary equations ─────────────────────────────────────────
        let close = |t: &Thm| {
            gen_all(&[xv, yv], &discharge(&x_om, &discharge(&y_om, t)))
        };
        let mul_double = {
            let unfold =
                congr2_r(env, pr.sym, &tx, &inst_all(&bin.double_ax, std::slice::from_ref(&ty))?)?;
            let dist = dist_at(&hx, &hy, &hy)?;
            let fold = eq_symm(
                env,
                &inst_all(&bin.double_ax, std::slice::from_ref(&mul(&tx, &ty)))?,
            )?;
            close(&Chain::from(unfold).then(dist).then(fold).done(env)?)
        };
        let mul_double1 = {
            let unfold =
                congr2_r(env, pr.sym, &tx, &inst_all(&bin.double1_ax, std::slice::from_ref(&ty))?)?;
            let dy_mem =
                Thm::mp(&inst_all(&bin.double_mem, std::slice::from_ref(&ty))?, &hy)?;
            let peel = succ_at(&tx, &dy_mem)?;
            let raw_double = {
                let at = inst_all(&mul_double, &[tx.clone(), ty.clone()])?;
                Thm::mp(&Thm::mp(&at, &hx)?, &hy)?
            };
            let inner = congr2_l(env, add_sym, &raw_double, &tx)?;
            close(&Chain::from(unfold).then(peel).then(inner).done(env)?)
        };

        Some(Mul { pr, mul_zero, mul_succ, mul_mem, mul_dist, mul_double, mul_double1 })
    }
}

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ ω` infer `Γ ∪ Δ ⊢ b ∈ ω`.
fn mem_rewrite(env: &mut Env, nat: &Nat, ab: &Thm, a_mem: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), nat.omega());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    Thm::mp(&Thm::mp(&leib, ab)?, a_mem)
}
