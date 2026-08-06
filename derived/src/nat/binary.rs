//! **The binary view of the same `ω`**: `double`, `double1`, `addc`, the
//! numeral encoding, and the eight binary recursion equations for addition.
//!
//! # Interface
//!
//! ```text
//! double(x)  := add(x,x)        double1(x) := succ(double(x))
//! addc(x,y)  := succ(add(x,y))
//!
//! ── typing and the two ends ─────────────────────────────────────────────
//! ⊢ ∀x. (x ∈ ω → double(x) ∈ ω)                          [Binary::double_mem]
//! ⊢ ∀x. (x ∈ ω → double1(x) ∈ ω)                        [Binary::double1_mem]
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → addc(x,y) ∈ ω))               [Binary::addc_mem]
//! ⊢ double(0) = 0                                       [Binary::double_zero]
//! ⊢ double1(0) = succ(0)                               [Binary::double1_zero]
//!
//! ── the successor, on the binary shape: Θ(trailing ones), never Θ(value) ─
//! ⊢ ∀x. succ(double x) = double1 x                      [Binary::succ_double]
//! ⊢ ∀x. (x ∈ ω → succ(double1 x) = double(succ x))     [Binary::succ_double1]
//!
//! ── the eight binary recursion equations, all under x ∈ ω, y ∈ ω ────────
//! ⊢ add (double  x) (double  y) = double  (add  x y)          [Binary::add_dd]
//! ⊢ add (double  x) (double1 y) = double1 (add  x y)          [Binary::add_d1]
//! ⊢ add (double1 x) (double  y) = double1 (add  x y)          [Binary::add_1d]
//! ⊢ add (double1 x) (double1 y) = double  (addc x y)          [Binary::add_11]
//! ⊢ addc(double  x) (double  y) = double1 (add  x y)         [Binary::addc_dd]
//! ⊢ addc(double  x) (double1 y) = double  (addc x y)         [Binary::addc_d1]
//! ⊢ addc(double1 x) (double  y) = double  (addc x y)         [Binary::addc_1d]
//! ⊢ addc(double1 x) (double1 y) = double1 (addc x y)         [Binary::addc_11]
//!
//! ── the two ends of the recursion ──────────────────────────────────────
//! ⊢ ∀x. addc(x, 0) = succ x                             [Binary::addc_zero_r]
//! ⊢ ∀y. (y ∈ ω → addc(0, y) = succ y)                   [Binary::addc_zero_l]
//! ```
//!
//! # There is no second type, and no valuation map
//!
//! `double` and `double1` are further **defined symbols on `ω`**. A numeral is
//! a term of `ω` built from them, `succ` is the same `succ`, and `add` is the
//! same `add` whose Peano equations [`crate::nat::Add`] proves. So there is
//! nothing to relate: no `B`, no `val : B → ω`, no injectivity obligation, no
//! canonicity side condition carried into every lemma. Coq relates `positive`
//! to `nat` through `Pos.to_nat` and Isabelle relates `num` to `nat` through
//! `numeral` because in both systems the digit strings are a *datatype*; here
//! they are notation for elements of the one carrier, and the relating
//! theorems are simply absent.
//!
//! # The numeral encoding, and the size of `2⁶⁴`
//!
//! ```text
//! num(0)   = 0
//! num(2k)  = double  (num k)        k ≥ 1
//! num(2k+1)= double1 (num k)        k ≥ 0
//! ```
//!
//! Least significant bit outermost, terminated at `0`, and **canonical**: the
//! innermost constructor of a non-zero numeral is a `double1`, so there are no
//! leading zeros. `num(1) = double1(0)`, `num(2) = double(double1(0))`, and
//!
//! ```text
//! num(2⁶⁴) = double(double(…double(double1(0))…))       64 nested `double`
//! ```
//!
//! which is **66 term nodes** against 1.8 × 10¹⁹ for the `succ`-tower. That is
//! the whole point of the second view, and [`crate::nat::eval`] is where it is
//! spent.
//!
//! # Why `addc` exists
//!
//! Without it the carry case `add (double1 x) (double1 y)` produces
//! `double (succ (add x y))`, and the `succ` has to be pushed back down through
//! the numeral it wraps. Coq's `Pos.add`/`Pos.add_carry` pair moves the carry
//! into the *control state* instead, and that is what `addc` is: eight
//! equations rather than four, and the recursion stays one pass over the bits.
//! `addc` is **not** a new recursion — it is `succ ∘ add`, so every one of its
//! equations is one `succ` rewrite away from the corresponding `add` one.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{define_abbrev, eq_symm, inst_all};

use super::add::Add;
use super::apparatus::Nat;
use super::glue::{congr1, congr2_r, gen_all, Chain};

/// The binary view of `ω`.
pub struct Binary {
    /// `double(x) := add(x,x)`.
    pub double: FnSym,
    /// `⊢ ∀x. double(x) = add(x,x)`.
    pub double_ax: Thm,
    /// `double1(x) := succ(double(x))`.
    pub double1: FnSym,
    /// `⊢ ∀x. double1(x) = succ(double(x))`.
    pub double1_ax: Thm,
    /// `addc(x,y) := succ(add(x,y))`.
    pub addc: FnSym,
    /// `⊢ ∀x ∀y. addc(x,y) = succ(add(x,y))`.
    pub addc_ax: Thm,

    /// `⊢ ∀x. (x ∈ ω → double(x) ∈ ω)`.
    pub double_mem: Thm,
    /// `⊢ ∀x. (x ∈ ω → double1(x) ∈ ω)`.
    pub double1_mem: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → addc(x,y) ∈ ω))`.
    pub addc_mem: Thm,
    /// `⊢ double(0) = 0`.
    pub double_zero: Thm,
    /// `⊢ double1(0) = succ(0)`.
    pub double1_zero: Thm,
    /// `⊢ ∀x. succ(double x) = double1 x`.
    pub succ_double: Thm,
    /// `⊢ ∀x. (x ∈ ω → succ(double1 x) = double(succ x))`.
    pub succ_double1: Thm,

    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(double x, double y) = double(add x y)))`.
    pub add_dd: Thm,
    /// `… add(double x, double1 y) = double1(add x y)`.
    pub add_d1: Thm,
    /// `… add(double1 x, double y) = double1(add x y)`.
    pub add_1d: Thm,
    /// `… add(double1 x, double1 y) = double(addc x y)`.
    pub add_11: Thm,
    /// `… addc(double x, double y) = double1(add x y)`.
    pub addc_dd: Thm,
    /// `… addc(double x, double1 y) = double(addc x y)`.
    pub addc_d1: Thm,
    /// `… addc(double1 x, double y) = double(addc x y)`.
    pub addc_1d: Thm,
    /// `… addc(double1 x, double1 y) = double1(addc x y)`.
    pub addc_11: Thm,

    /// `⊢ ∀x. addc(x, 0) = succ x`.
    pub addc_zero_r: Thm,
    /// `⊢ ∀y. (y ∈ ω → addc(0, y) = succ y)`.
    pub addc_zero_l: Thm,
}

impl Binary {
    /// The term `double(t)`.
    pub fn double_of(&self, t: Term) -> Term { Term::apply(self.double, vec![t]) }

    /// The term `double1(t)`.
    pub fn double1_of(&self, t: Term) -> Term { Term::apply(self.double1, vec![t]) }

    /// The term `addc(a,b)`.
    pub fn addc_of(&self, a: Term, b: Term) -> Term { Term::apply(self.addc, vec![a, b]) }

    /// The numeral for `n`: `0`, or a nest of `double`/`double1` over
    /// `double1(0)`, least significant bit outermost.
    pub fn numeral(&self, nat: &Nat, n: u128) -> Term {
        if n == 0 {
            return nat.zero()
        }
        let inner = self.numeral(nat, n >> 1);
        if n & 1 == 1 {
            self.double1_of(inner)
        } else {
            self.double_of(inner)
        }
    }

    /// Define the three symbols and derive everything above.
    pub fn new(env: &mut Env, nat: &Nat, ad: &Add) -> DResult<Binary> {
        let succ_sym = nat.core().succ;
        let (xv, yv) = (env.fresh_var(), env.fresh_var());
        let (tx, ty) = (Term::var(xv), Term::var(yv));

        let (double, double_ax) = define_abbrev(env, &[xv], &ad.of(tx.clone(), tx.clone()))?;
        let dbl = |t: &Term| Term::apply(double, vec![t.clone()]);
        let (double1, double1_ax) = define_abbrev(env, &[xv], &nat.succ_of(dbl(&tx)))?;
        let dbl1 = |t: &Term| Term::apply(double1, vec![t.clone()]);
        let (addc, addc_ax) =
            define_abbrev(env, &[xv, yv], &nat.succ_of(ad.of(tx.clone(), ty.clone())))?;

        let zero = nat.zero();
        let x_om = nat.in_omega(tx.clone());
        let y_om = nat.in_omega(ty.clone());
        let hx = assuming(x_om.clone());
        let hy = assuming(y_om.clone());

        // ── typing ───────────────────────────────────────────────────────────
        let double_mem = {
            let m = ad.mem_at(&hx, &hx)?;
            let back = eq_symm(env, &inst_all(&double_ax, std::slice::from_ref(&tx))?)?;
            let out = mem_rewrite(env, nat, &back, &m)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let double1_mem = {
            let dm = prim::mp(&inst_all(&double_mem, std::slice::from_ref(&tx))?, &hx)?;
            let sm = nat.succ_mem_at(&dm)?;
            let back = eq_symm(env, &inst_all(&double1_ax, std::slice::from_ref(&tx))?)?;
            let out = mem_rewrite(env, nat, &back, &sm)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };
        let addc_mem = {
            let m = nat.succ_mem_at(&ad.mem_at(&hx, &hy)?)?;
            let back = eq_symm(env, &inst_all(&addc_ax, &[tx.clone(), ty.clone()])?)?;
            let out = mem_rewrite(env, nat, &back, &m)?;
            gen_all(
                &[xv, yv],
                &discharge(&x_om, &discharge(&y_om, &out)),
            )?
        };

        // ── the two ends ─────────────────────────────────────────────────────
        let double_zero = Chain::from(inst_all(&double_ax, std::slice::from_ref(&zero))?)
            .then(inst_all(&ad.add_zero, std::slice::from_ref(&zero))?)
            .done(env)?;
        let double1_zero = Chain::from(inst_all(&double1_ax, std::slice::from_ref(&zero))?)
            .then(congr1(env, succ_sym, &double_zero)?)
            .done(env)?;

        // ── the successor on the binary shape ────────────────────────────────
        let succ_double = {
            let ax = inst_all(&double1_ax, std::slice::from_ref(&tx))?;
            gen_all(&[xv], &eq_symm(env, &ax)?)?
        };
        let succ_double1 = {
            // succ(double1 x) = succ(succ(double x))
            let up = congr1(env, succ_sym, &inst_all(&double1_ax, std::slice::from_ref(&tx))?)?;
            // double(succ x) = add(succ x, succ x) = succ(add(succ x, x))
            //               = succ(succ(add(x,x))) = succ(succ(double x))
            let sx = nat.succ_of(tx.clone());
            let d_ax = inst_all(&double_ax, std::slice::from_ref(&sx))?;
            let step1 = prim::mp(&inst_all(&ad.add_succ, &[sx.clone(), tx.clone()])?, &hx)?;
            let step2 = prim::mp(&inst_all(&ad.add_succ_l, &[tx.clone(), tx.clone()])?, &hx)?;
            let refold = eq_symm(env, &inst_all(&double_ax, std::slice::from_ref(&tx))?)?;
            let inner =
                Chain::from(step2).then(congr1(env, succ_sym, &refold)?).done(env)?;
            let down = Chain::from(d_ax)
                .then(step1)
                .then(congr1(env, succ_sym, &inner)?)
                .done(env)?;
            let out = Chain::from(up).then_rev(down).done(env)?;
            gen_all(&[xv], &discharge(&x_om, &out))?
        };

        // ── the eight binary recursion equations ─────────────────────────────
        let add_sym = ad.add;
        let dy_mem = prim::mp(&inst_all(&double_mem, std::slice::from_ref(&ty))?, &hy)?;
        let d1x_mem = prim::mp(&inst_all(&double1_mem, std::slice::from_ref(&tx))?, &hx)?;
        let xy_mem = ad.mem_at(&hx, &hy)?;
        let close = |t: &Thm| {
            gen_all(&[xv, yv], &discharge(&x_om, &discharge(&y_om, t)))
        };

        // add(double x, double y) = add(add(x,x), add(y,y))
        //                         = add(add(x,y), add(x,y)) = double(add x y)
        let add_dd = {
            let unfold_x = inst_all(&double_ax, std::slice::from_ref(&tx))?;
            let unfold_y = inst_all(&double_ax, std::slice::from_ref(&ty))?;
            let l = crate::rules::congr_arg(
                env,
                add_sym,
                &[dbl(&tx), dbl(&ty)],
                0,
                &unfold_x,
            )?;
            let r = congr2_r(env, add_sym, &ad.of(tx.clone(), tx.clone()), &unfold_y)?;
            let shuffle = {
                let at = inst_all(&ad.add_shuffle, &[tx.clone(), tx.clone(), ty.clone(), ty.clone()])?;
                prim::mp(&prim::mp(&prim::mp(&at, &hx)?, &hy)?, &hy)?
            };
            let fold = eq_symm(
                env,
                &inst_all(&double_ax, std::slice::from_ref(&ad.of(tx.clone(), ty.clone())))?,
            )?;
            close(&Chain::from(l).then(r).then(shuffle).then(fold).done(env)?)?
        };
        let raw_dd = prim::mp(
            &prim::mp(&inst_all(&add_dd, &[tx.clone(), ty.clone()])?, &hx)?,
            &hy,
        )?;

        // add(double x, double1 y) = add(double x, succ(double y))
        //   = succ(add(double x, double y)) = succ(double(add x y)) = double1(add x y)
        let raw_d1 = {
            let unfold = congr2_r(
                env,
                add_sym,
                &dbl(&tx),
                &inst_all(&double1_ax, std::slice::from_ref(&ty))?,
            )?;
            let peel = prim::mp(&inst_all(&ad.add_succ, &[dbl(&tx), dbl(&ty)])?, &dy_mem)?;
            let fold = eq_symm(
                env,
                &inst_all(&double1_ax, std::slice::from_ref(&ad.of(tx.clone(), ty.clone())))?,
            )?;
            Chain::from(unfold)
                .then(peel)
                .then(congr1(env, succ_sym, &raw_dd)?)
                .then(fold)
                .done(env)?
        };
        let add_d1 = close(&raw_d1)?;

        // add(double1 x, double y) = add(double y, double1 x) = double1(add y x)
        //                          = double1(add x y)
        let raw_1d = {
            let comm = {
                let at = inst_all(&ad.add_comm, &[dbl1(&tx), dbl(&ty)])?;
                prim::mp(&prim::mp(&at, &d1x_mem)?, &dy_mem)?
            };
            let flip = {
                let at = inst_all(&add_d1, &[ty.clone(), tx.clone()])?;
                prim::mp(&prim::mp(&at, &hy)?, &hx)?
            };
            let inner = {
                let at = inst_all(&ad.add_comm, &[ty.clone(), tx.clone()])?;
                prim::mp(&prim::mp(&at, &hy)?, &hx)?
            };
            Chain::from(comm)
                .then(flip)
                .then(congr1(env, double1, &inner)?)
                .done(env)?
        };
        let add_1d = close(&raw_1d)?;

        // add(double1 x, double1 y) = succ(add(double1 x, double y))
        //   = succ(double1(add x y)) = double(succ(add x y)) = double(addc x y)
        let raw_11 = {
            let unfold = congr2_r(
                env,
                add_sym,
                &dbl1(&tx),
                &inst_all(&double1_ax, std::slice::from_ref(&ty))?,
            )?;
            let peel = prim::mp(&inst_all(&ad.add_succ, &[dbl1(&tx), dbl(&ty)])?, &dy_mem)?;
            let carry = {
                let xy = ad.of(tx.clone(), ty.clone());
                prim::mp(&inst_all(&succ_double1, std::slice::from_ref(&xy))?, &xy_mem)?
            };
            let fold = eq_symm(env, &inst_all(&addc_ax, &[tx.clone(), ty.clone()])?)?;
            Chain::from(unfold)
                .then(peel)
                .then(congr1(env, succ_sym, &raw_1d)?)
                .then(carry)
                .then(congr1(env, double, &fold)?)
                .done(env)?
        };
        let add_11 = close(&raw_11)?;

        // The four carrying equations: one `succ` rewrite each.
        let addc_dd = {
            let unfold = inst_all(&addc_ax, &[dbl(&tx), dbl(&ty)])?;
            let fold = eq_symm(
                env,
                &inst_all(&double1_ax, std::slice::from_ref(&ad.of(tx.clone(), ty.clone())))?,
            )?;
            close(
                &Chain::from(unfold)
                    .then(congr1(env, succ_sym, &raw_dd)?)
                    .then(fold)
                    .done(env)?,
            )?
        };
        let addc_d1 = {
            let unfold = inst_all(&addc_ax, &[dbl(&tx), dbl1(&ty)])?;
            let xy = ad.of(tx.clone(), ty.clone());
            let carry = prim::mp(&inst_all(&succ_double1, std::slice::from_ref(&xy))?, &xy_mem)?;
            let fold = eq_symm(env, &inst_all(&addc_ax, &[tx.clone(), ty.clone()])?)?;
            close(
                &Chain::from(unfold)
                    .then(congr1(env, succ_sym, &raw_d1)?)
                    .then(carry)
                    .then(congr1(env, double, &fold)?)
                    .done(env)?,
            )?
        };
        let addc_1d = {
            let unfold = inst_all(&addc_ax, &[dbl1(&tx), dbl(&ty)])?;
            let xy = ad.of(tx.clone(), ty.clone());
            let carry = prim::mp(&inst_all(&succ_double1, std::slice::from_ref(&xy))?, &xy_mem)?;
            let fold = eq_symm(env, &inst_all(&addc_ax, &[tx.clone(), ty.clone()])?)?;
            close(
                &Chain::from(unfold)
                    .then(congr1(env, succ_sym, &raw_1d)?)
                    .then(carry)
                    .then(congr1(env, double, &fold)?)
                    .done(env)?,
            )?
        };
        let addc_11 = {
            let unfold = inst_all(&addc_ax, &[dbl1(&tx), dbl1(&ty)])?;
            let fold = eq_symm(
                env,
                &inst_all(
                    &double1_ax,
                    std::slice::from_ref(&Term::apply(addc, vec![tx.clone(), ty.clone()])),
                )?,
            )?;
            let inner = congr1(env, succ_sym, &raw_11)?;
            close(&Chain::from(unfold).then(inner).then(fold).done(env)?)?
        };

        // ── the two ends of the recursion ────────────────────────────────────
        let addc_zero_r = {
            let unfold = inst_all(&addc_ax, &[tx.clone(), zero.clone()])?;
            let base = inst_all(&ad.add_zero, std::slice::from_ref(&tx))?;
            gen_all(
                &[xv],
                &Chain::from(unfold).then(congr1(env, succ_sym, &base)?).done(env)?,
            )?
        };
        let addc_zero_l = {
            let unfold = inst_all(&addc_ax, &[zero.clone(), ty.clone()])?;
            let base = prim::mp(&inst_all(&ad.add_zero_l, std::slice::from_ref(&ty))?, &hy)?;
            let out = Chain::from(unfold).then(congr1(env, succ_sym, &base)?).done(env)?;
            gen_all(&[yv], &discharge(&y_om, &out))?
        };

        Ok(Binary {
            double,
            double_ax,
            double1,
            double1_ax,
            addc,
            addc_ax,
            double_mem,
            double1_mem,
            addc_mem,
            double_zero,
            double1_zero,
            succ_double,
            succ_double1,
            add_dd,
            add_d1,
            add_1d,
            add_11,
            addc_dd,
            addc_d1,
            addc_1d,
            addc_11,
            addc_zero_r,
            addc_zero_l,
        })
    }
}

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ ω` infer `Γ ∪ Δ ⊢ b ∈ ω`.
fn mem_rewrite(env: &mut Env, nat: &Nat, ab: &Thm, a_mem: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    let x: FreeVar = env.fresh_var();
    let phi = Formula::mem(Term::var(x), nat.omega());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    prim::mp(&prim::mp(&leib, ab)?, a_mem)
}
