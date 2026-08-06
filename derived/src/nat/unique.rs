//! **The bridge**: any operation satisfying the two Peano equations *is* `add`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀f. ( (∀x. (x ∈ ω → app(app(f,x), 0) = x))
//!       → ((∀x. (x ∈ ω → ∀y. (y ∈ ω →
//!              app(app(f,x), succ y) = succ(app(app(f,x), y)))))
//!       → ∀x. (x ∈ ω → ∀y. (y ∈ ω → app(app(f,x), y) = add(x,y)))))
//! ```
//!
//! [`uniqueness`], and it is the reason the fast implementation can be
//! connected to *someone else's* definition without inspecting how that
//! definition was written.
//!
//! # Why this is the whole bridge
//!
//! A checker meets addition as a set `f` — the interpretation of whatever
//! declaration the input called `add` — compiled through whatever
//! `brecOn`/`below`/`match` nest its author used. It cannot compare that set
//! with [`crate::nat::Add::add`] syntactically and must not simply trust a
//! name, which is what Lean's kernel does (`type_checker.cpp` builds
//! `mk_constant({"Nat","add"})` and never checks the environment's `Nat.add` is
//! the prelude's).
//!
//! What it *can* do is derive the two Peano equations for `f` from `f`'s own
//! definition by δ and ι, and then instantiate this theorem. From that moment
//! every fact about `add` — including every numeral computed by
//! [`crate::nat::Eval`] — transfers to `f` in **two instantiations and one
//! transitivity**, at any numeral, at any size. The transfer cost does not grow
//! with the numeral, because the theorem is universally quantified and proved
//! once.
//!
//! # What it does not assume, and this is not an oversight
//!
//! There is **no typing hypothesis on `f`.** It need not be a function, a set
//! of pairs, or anything at all: the statement only ever reads `f` through
//! `app`, so `app(app(f,x),y)` is a term whatever `f` is, and the induction
//! never needs to know more. Adding `f ∈ fs(ω, fs(ω,ω))` would be an antecedent
//! the derivation does not read and a caller would have to discharge — for
//! Lean's `Nat.add` that means proving a function-space membership before the
//! bridge can fire, which is real work bought for nothing.
//!
//! Symmetrically, both premises are stated **only on `ω`**. `f` may do anything
//! it likes off the carrier and the conclusion is silent there, which is the
//! most a checker could honestly claim about a set it did not build.
//!
//! # The proof
//!
//! One induction on the second argument, four lines. `add`'s own equations are
//! definitional ([`crate::nat::Add`]), so the base is `f(x,0) = x = add(x,0)`
//! and the step is `f(x, succ y) = succ(f(x,y)) = succ(add(x,y)) = add(x,succ y)`.
//! It is Coq's `NDefOps.def_add_add` verbatim, and it is cheap for the same
//! reason: it uses only the abstract equations and never the definition of
//! either side.

use kernel::{Env, Formula, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::inst_all;

use super::add::Add;
use super::apparatus::Nat;
use super::glue::{congr1, gen_all, induct, induct_step, Chain};

/// The three formulas the bridge is stated in, at a caller-supplied `f`.
pub struct Spec {
    /// `∀x. (x ∈ ω → app(app(f,x), 0) = x)`.
    pub base: Formula,
    /// `∀x. (x ∈ ω → ∀y. (y ∈ ω → app(app(f,x), succ y) = succ(app(app(f,x), y))))`.
    pub step: Formula,
    /// `∀x. (x ∈ ω → ∀y. (y ∈ ω → app(app(f,x), y) = add(x,y)))`.
    pub agrees: Formula,
}

impl Spec {
    /// Build the three formulas at the term `f`, using `xv`/`yv` as the bound
    /// variables — the same ones the derivation quantifies, so that a caller
    /// pinning the shape rebuilds exactly what [`uniqueness`] produces.
    pub fn at(
        nat: &Nat,
        ad: &Add,
        f: &Term,
        xv: kernel::FreeVar,
        yv: kernel::FreeVar,
    ) -> Spec {
        let (tx, ty) = (Term::var(xv), Term::var(yv));
        let fx = nat.apply(f.clone(), tx.clone());
        let at = |y: Term| nat.apply(fx.clone(), y);
        let x_om = nat.in_omega(tx.clone());
        let y_om = nat.in_omega(ty.clone());
        let base =
            Formula::forall(xv, Formula::imp(x_om.clone(), Formula::eq(at(nat.zero()), tx.clone())));
        let inner_step = Formula::eq(at(nat.succ_of(ty.clone())), nat.succ_of(at(ty.clone())));
        let step = Formula::forall(
            xv,
            Formula::imp(
                x_om.clone(),
                Formula::forall(yv, Formula::imp(y_om.clone(), inner_step)),
            ),
        );
        let agrees = Formula::forall(
            xv,
            Formula::imp(
                x_om,
                Formula::forall(
                    yv,
                    Formula::imp(y_om, Formula::eq(at(ty.clone()), ad.of(tx, ty))),
                ),
            ),
        );
        Spec { base, step, agrees }
    }
}

/// `⊢ ∀f. (base(f) → (step(f) → agrees(f)))` — **the uniqueness bridge**.
pub fn uniqueness(env: &mut Env, nat: &Nat, ad: &Add) -> DResult<Thm> {
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let spec = Spec::at(nat, ad, &tf, xv, yv);

    let h_base = assuming(spec.base.clone());
    let h_step = assuming(spec.step.clone());
    let x_om = nat.in_omega(tx.clone());
    let h_x = assuming(x_om.clone());

    let fx = nat.apply(tf.clone(), tx.clone());
    let at = |y: Term| nat.apply(fx.clone(), y);
    let phi = Formula::eq(at(ty.clone()), ad.of(tx.clone(), ty.clone()));
    let succ_sym = nat.core().succ;

    // Base: `f(x,0) = x` and `add(x,0) = x`, so the two agree at `0`.
    let f_zero = prim::mp(&inst_all(&h_base, std::slice::from_ref(&tx))?, &h_x)?;
    let add_zero = inst_all(&ad.add_zero, std::slice::from_ref(&tx))?;
    let base = Chain::from(f_zero).then_rev(add_zero).done(env)?;

    // Step: `f(x, succ y) = succ(f(x,y)) = succ(add(x,y)) = add(x, succ y)`.
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        let at_x = prim::mp(&inst_all(&h_step, std::slice::from_ref(&tx))?, &h_x)?;
        let f_succ = prim::mp(&inst_all(&at_x, std::slice::from_ref(&ty))?, y_om)?;
        let add_succ = prim::mp(&inst_all(&ad.add_succ, &[tx.clone(), ty.clone()])?, y_om)?;
        Chain::from(f_succ).then(congr1(env, succ_sym, ih)?).then_rev(add_succ).done(env)
    })?;

    let all_y = induct(env, nat.core(), yv, &phi, &base, &step)?;
    let over_x = prim::gen(xv, &discharge(&x_om, &all_y))?;
    debug_assert_eq!(*over_x.concl(), spec.agrees, "uniqueness: the conclusion has the wrong shape");
    let discharged = discharge(&spec.base, &discharge(&spec.step, &over_x));
    gen_all(&[fv], &discharged)
}

/// `⊢ ∀x ∀f. (app(f,0) = x
///        → ((∀y. (y ∈ ω → app(f, succ y) = succ(app(f,y))))
///        → ∀y. (y ∈ ω → app(f,y) = add(x,y))))`
/// — **the pointwise bridge**, and the one that carries the non-vacuity.
///
/// [`uniqueness`] with the first argument already supplied. It is the honest
/// primitive of the two: `f` here is a *unary* set, which is what
/// `app(F, x)` is once a checker has fixed the numeral it is working at, and
/// the two-argument form follows by instantiating `f := app(F,x)` and
/// distributing the `∀x`.
///
/// **`x` carries no hypothesis.** `add`'s two equations hold at an arbitrary
/// first argument (the recursion runs on the second), so the bridge does too,
/// and requiring `x ∈ ω` would be an antecedent nothing reads.
///
/// The premises are satisfiable, and the witness costs nothing:
/// [`crate::nat::Add::iter_base`] and [`crate::nat::Add::iter_step`] *are* the
/// two premises at `f := ait(x)`. `derived/tests/nat.rs` discharges them and
/// reads the conclusion off, which is what rules out a bridge whose antecedent
/// no set satisfies.
pub fn uniqueness_pointwise(env: &mut Env, nat: &Nat, ad: &Add) -> DResult<Thm> {
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let (xv, yv) = (ad.iter_var, env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let succ_sym = nat.core().succ;
    let at = |y: Term| nat.apply(tf.clone(), y);

    let p_base = Formula::eq(at(nat.zero()), tx.clone());
    let p_step = Formula::forall(
        yv,
        Formula::imp(
            nat.in_omega(ty.clone()),
            Formula::eq(at(nat.succ_of(ty.clone())), nat.succ_of(at(ty.clone()))),
        ),
    );
    let h_base = assuming(p_base.clone());
    let h_step = assuming(p_step.clone());
    let phi = Formula::eq(at(ty.clone()), ad.of(tx.clone(), ty.clone()));

    let base = {
        let add_zero = inst_all(&ad.add_zero, std::slice::from_ref(&tx))?;
        Chain::from(h_base.clone()).then_rev(add_zero).done(env)?
    };
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        let f_succ = prim::mp(&inst_all(&h_step, std::slice::from_ref(&ty))?, y_om)?;
        let add_succ = prim::mp(&inst_all(&ad.add_succ, &[tx.clone(), ty.clone()])?, y_om)?;
        Chain::from(f_succ).then(congr1(env, succ_sym, ih)?).then_rev(add_succ).done(env)
    })?;
    let all_y = induct(env, nat.core(), yv, &phi, &base, &step)?;
    let discharged = discharge(&p_base, &discharge(&p_step, &all_y));
    gen_all(&[xv, fv], &discharged)
}

/// The bridge fired at one operation: from `⊢ base(f)` and `⊢ step(f)` and two
/// memberships, `⊢ app(app(f,a), b) = add(a,b)`.
///
/// Two instantiations, two `mp`s for the premises and two more for the
/// memberships — **independent of how large `a` and `b` are**, which is the
/// property the whole bridge exists for.
pub fn transfer(
    bridge: &Thm,
    f: &Term,
    base: &Thm,
    step: &Thm,
    a_mem: &Thm,
    b_mem: &Thm,
) -> DResult<Thm> {
    let (a, _) = a_mem.concl().mem_parts()?;
    let (b, _) = b_mem.concl().mem_parts()?;
    let at_f = inst_all(bridge, std::slice::from_ref(f))?;
    let agrees = prim::mp(&prim::mp(&at_f, base)?, step)?;
    let at_a = prim::mp(&inst_all(&agrees, std::slice::from_ref(&a))?, a_mem)?;
    prim::mp(&inst_all(&at_a, std::slice::from_ref(&b))?, b_mem)
}
