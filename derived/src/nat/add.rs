//! **Addition on `ω`**, its two Peano equations, and the four facts the binary
//! view runs on.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀x ∀y. add(x,y) = app(ait(x), y)                                [Add::add_ax]
//!
//! ── the Peano equations, which are what a bridge attaches to ─────────────
//! ⊢ ∀x. add(x, 0) = x                                            [Add::add_zero]
//! ⊢ ∀x ∀y. (y ∈ ω → add(x, succ y) = succ(add(x,y)))             [Add::add_succ]
//!
//! ── typing, and the mirrored equations ──────────────────────────────────
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) ∈ ω))                       [Add::add_mem]
//! ⊢ ∀y. (y ∈ ω → add(0, y) = y)                                 [Add::add_zero_l]
//! ⊢ ∀x ∀y. (y ∈ ω → add(succ x, y) = succ(add(x,y)))            [Add::add_succ_l]
//!
//! ── commutativity, associativity, and the exchange law ──────────────────
//! ⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) = add(y,x)))                [Add::add_comm]
//! ⊢ ∀x ∀y ∀z. (y ∈ ω → (z ∈ ω →
//!        add(add(x,y),z) = add(x, add(y,z))))                   [Add::add_assoc]
//! ⊢ ∀a ∀b ∀c ∀d. (b ∈ ω → (c ∈ ω → (d ∈ ω →
//!        add(add(a,b), add(c,d)) = add(add(a,c), add(b,d)))))   [Add::add_shuffle]
//! ```
//!
//! # Why `add` is defined by iterating `succ`, and not by the recursor
//!
//! [`crate::nat::Nat::natrec`] takes its step as a *set*, and the step here is
//! "apply `succ`" — writing that as a set means building a function on `ω` by
//! Replacement before any arithmetic exists. [`crate::recursion::recursion`]
//! takes its step as a **function symbol**, and `succ` is one, so `add` is one
//! call to a theorem that was already there:
//!
//! ```text
//! ait(x) := the f with f(0) = x and f(succ n) = succ(f n)
//! add(x,y) := app(ait(x), y)
//! ```
//!
//! Both Peano equations are then *definitional* — [`Add::add_zero`] is the
//! recursion theorem's base and [`Add::add_succ`] is its step, with one
//! abbreviation unfolded on each side. **Nothing is proved by induction to get
//! them.** That matters for the bridge: the equations a user-supplied `add`
//! would have to satisfy are exactly the two this `add` satisfies by
//! construction, so the uniqueness argument runs on the recursor and not on
//! anything about how either side was written.
//!
//! # Where the inductions are
//!
//! Five, and no more: [`Add::add_mem`], [`Add::add_zero_l`],
//! [`Add::add_succ_l`], [`Add::add_comm`], [`Add::add_assoc`]. The exchange law
//! [`Add::add_shuffle`] is five rewrites over those and no induction of its
//! own, and it is the one the binary view actually spends —
//! `add(x+x, y+y) = add(x+y, x+y)` is its instance at `a,b,c,d := x,x,y,y`,
//! which is `double x + double y = double (x+y)`.
//!
//! The asymmetry in the hypotheses is not sloppiness and is worth keeping:
//! [`Add::add_succ_l`] and [`Add::add_assoc`] hold with their *first* argument
//! completely unconstrained, because the recursion runs on the second. A
//! consumer that carries `x ∈ ω` around when it does not have to pays for it at
//! every numeral.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::recursion::theorem::recursion;
use crate::{define_abbrev, eq_symm, gen_all, inst_all, inst_self};

use super::apparatus::Nat;
use super::glue::{congr1, congr2_l, congr2_r, induct, induct_step, Chain};

/// Addition on `ω` and everything proved about it.
pub struct Add {
    /// The iteration symbol `ait(x)` — `succ` iterated from `x`.
    pub ait: FnSym,
    /// The symbol `add(x,y)`.
    pub add: FnSym,
    /// `⊢ ∀x ∀y. add(x,y) = app(ait(x), y)`.
    pub add_ax: Thm,
    /// `⊢ app(ait(x), 0) = x`, at the free `x` the symbol was defined over —
    /// the recursion theorem's own base, kept so that
    /// [`crate::nat::unique`] has a witness that its bridge is not vacuous.
    pub iter_base: Thm,
    /// `⊢ ∀y. (y ∈ ω → app(ait(x), succ y) = succ(app(ait(x), y)))`, likewise.
    pub iter_step: Thm,
    /// The variable `x` that [`Add::iter_base`] and [`Add::iter_step`] are
    /// stated at.
    pub iter_var: FreeVar,
    /// `⊢ ∀x. add(x, 0) = x`.
    pub add_zero: Thm,
    /// `⊢ ∀x ∀y. (y ∈ ω → add(x, succ y) = succ(add(x,y)))`.
    pub add_succ: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) ∈ ω))`.
    pub add_mem: Thm,
    /// `⊢ ∀y. (y ∈ ω → add(0, y) = y)`.
    pub add_zero_l: Thm,
    /// `⊢ ∀x ∀y. (y ∈ ω → add(succ x, y) = succ(add(x,y)))`.
    pub add_succ_l: Thm,
    /// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) = add(y,x)))`.
    pub add_comm: Thm,
    /// `⊢ ∀x ∀y ∀z. (y ∈ ω → (z ∈ ω → add(add(x,y),z) = add(x, add(y,z))))`.
    pub add_assoc: Thm,
    /// `⊢ ∀a ∀b ∀c ∀d. (b ∈ ω → (c ∈ ω → (d ∈ ω →
    ///        add(add(a,b), add(c,d)) = add(add(a,c), add(b,d)))))` — and `a`
    /// really is unconstrained; see [`add_shuffle`].
    pub add_shuffle: Thm,
}

impl Add {
    /// The term `add(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.add, vec![a, b]) }

    /// `⊢ add(a,b) ∈ ω` from `⊢ a ∈ ω` and `⊢ b ∈ ω`.
    pub fn mem_at(&self, a: &Thm, b: &Thm) -> Option<Thm> {
        let (ta, _) = a.concl().as_mem()?;
        let (tb, _) = b.concl().as_mem()?;
        let at = inst_all(&self.add_mem, &[ta, tb])?;
        Thm::mp(&Thm::mp(&at, a)?, b)
    }

    /// Define `add` and derive everything above.
    pub fn new(env: &mut Env, nat: &Nat) -> Option<Add> {
        let succ_sym = nat.core().succ;
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let it = recursion(env, &nat.rec, succ_sym, &tx, &[xv])?;
        let ait = it.iter;

        let yv = env.fresh_var();
        let ty = Term::var(yv);
        let body = nat.apply(Term::apply(ait, vec![tx.clone()]), ty.clone());
        let (add, add_ax) = define_abbrev(env, &[xv, yv], &body)?;
        let of = |a: &Term, b: &Term| Term::apply(add, vec![a.clone(), b.clone()]);

        // ── the two Peano equations, both definitional ───────────────────────
        let zero = nat.zero();
        let unfold = |a: &Term, b: &Term| inst_all(&add_ax, &[a.clone(), b.clone()]);
        let add_zero = {
            let u = unfold(&tx, &zero)?;
            gen_all(&[xv], &Chain::from(u).then(it.base.clone()).done(env)?)
        };
        let add_succ = {
            let y_om = nat.in_omega(ty.clone());
            let assumed = Thm::assume(y_om.clone());
            let stepped = Thm::mp(&inst_all(&it.step, std::slice::from_ref(&ty))?, &assumed)?;
            let refold = eq_symm(env, &unfold(&tx, &ty)?)?;
            let out = Chain::from(unfold(&tx, &nat.succ_of(ty.clone()))?)
                .then(stepped)
                .then(congr1(env, succ_sym, &refold)?)
                .done(env)?;
            gen_all(&[xv, yv], &Thm::implies_intr(&y_om, &out))
        };

        let mut a = Add {
            ait,
            add,
            add_ax,
            iter_base: it.base.clone(),
            iter_step: it.step.clone(),
            iter_var: xv,
            add_zero,
            add_succ,
            add_mem: Thm::eq_refl(tx.clone()),
            add_zero_l: Thm::eq_refl(tx.clone()),
            add_succ_l: Thm::eq_refl(tx.clone()),
            add_comm: Thm::eq_refl(tx.clone()),
            add_assoc: Thm::eq_refl(tx.clone()),
            add_shuffle: Thm::eq_refl(tx.clone()),
        };
        let _ = &of;
        a.add_mem = add_mem(env, nat, &a, xv, yv)?;
        a.add_zero_l = add_zero_l(env, nat, &a, yv)?;
        a.add_succ_l = add_succ_l(env, nat, &a, xv, yv)?;
        a.add_comm = add_comm(env, nat, &a, xv, yv)?;
        a.add_assoc = add_assoc(env, nat, &a, xv, yv)?;
        a.add_shuffle = add_shuffle(env, nat, &a)?;
        Some(a)
    }

    /// `⊢ add(a, 0) = a`, at a term.
    fn zero_at(&self, a: &Term) -> Option<Thm> {
        inst_all(&self.add_zero, std::slice::from_ref(a))
    }

    /// `⊢ add(a, succ b) = succ(add(a,b))` from `⊢ b ∈ ω`.
    fn succ_at(&self, a: &Term, b_om: &Thm) -> Option<Thm> {
        let (b, _) = b_om.concl().as_mem()?;
        Thm::mp(&inst_all(&self.add_succ, &[a.clone(), b])?, b_om)
    }

    /// `⊢ add(succ a, b) = succ(add(a,b))` from `⊢ b ∈ ω`.
    fn succ_l_at(&self, a: &Term, b_om: &Thm) -> Option<Thm> {
        let (b, _) = b_om.concl().as_mem()?;
        Thm::mp(&inst_all(&self.add_succ_l, &[a.clone(), b])?, b_om)
    }

    /// `⊢ add(add(a,b),c) = add(a, add(b,c))` from `⊢ b ∈ ω` and `⊢ c ∈ ω`.
    fn assoc_at(&self, a: &Term, b_om: &Thm, c_om: &Thm) -> Option<Thm> {
        let (b, _) = b_om.concl().as_mem()?;
        let (c, _) = c_om.concl().as_mem()?;
        let at = inst_all(&self.add_assoc, &[a.clone(), b, c])?;
        Thm::mp(&Thm::mp(&at, b_om)?, c_om)
    }

    /// `⊢ add(a,b) = add(b,a)` from `⊢ a ∈ ω` and `⊢ b ∈ ω`.
    fn comm_at(&self, a_om: &Thm, b_om: &Thm) -> Option<Thm> {
        let (a, _) = a_om.concl().as_mem()?;
        let (b, _) = b_om.concl().as_mem()?;
        let at = inst_all(&self.add_comm, &[a, b])?;
        Thm::mp(&Thm::mp(&at, a_om)?, b_om)
    }
}

/// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) ∈ ω))`.
fn add_mem(env: &mut Env, nat: &Nat, a: &Add, xv: FreeVar, yv: FreeVar) -> Option<Thm> {
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let x_om = nat.in_omega(tx.clone());
    let assumed = Thm::assume(x_om.clone());
    let phi = nat.in_omega(a.of(tx.clone(), ty.clone()));

    // Base: `⊢ x = add(x,0)` turns the assumption `x ∈ ω` into `add(x,0) ∈ ω`.
    let back = eq_symm(env, &a.zero_at(&tx)?)?;
    let base = mem_rewrite(env, nat, &back, &assumed)?;
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        let eq = eq_symm(env, &a.succ_at(&tx, y_om)?)?; // succ(add(x,y)) = add(x, succ y)
        let succ_mem = nat.succ_mem_at(ih)?;
        mem_rewrite(env, nat, &eq, &succ_mem)
    })?;
    let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
    let at_y = inst_self(yv, &all)?;
    Some(gen_all(&[xv, yv], &Thm::implies_intr(&x_om, &at_y)))
}

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ ω` infer `Γ ∪ Δ ⊢ b ∈ ω`.
fn mem_rewrite(env: &mut Env, nat: &Nat, ab: &Thm, a_mem: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), nat.omega());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    Thm::mp(&Thm::mp(&leib, ab)?, a_mem)
}

/// `⊢ ∀y. (y ∈ ω → add(0, y) = y)`.
fn add_zero_l(env: &mut Env, nat: &Nat, a: &Add, yv: FreeVar) -> Option<Thm> {
    let ty = Term::var(yv);
    let zero = nat.zero();
    let phi = Formula::eq(a.of(zero.clone(), ty.clone()), ty.clone());
    let base = a.zero_at(&zero)?;
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        let s = a.succ_at(&zero, y_om)?;
        Some(Chain::from(s).then(congr1(env, nat.core().succ, ih)?).done(env)?)
    })?;
    induct(env, nat.core(), yv, &phi, &base, &step)
}

/// `⊢ ∀x ∀y. (y ∈ ω → add(succ x, y) = succ(add(x,y)))`.
fn add_succ_l(env: &mut Env, nat: &Nat, a: &Add, xv: FreeVar, yv: FreeVar) -> Option<Thm> {
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let succ_sym = nat.core().succ;
    let sx = nat.succ_of(tx.clone());
    let phi = Formula::eq(a.of(sx.clone(), ty.clone()), nat.succ_of(a.of(tx.clone(), ty.clone())));

    // Base: both sides are `succ x`.
    let base = Chain::from(a.zero_at(&sx)?)
        .then_rev(congr1(env, succ_sym, &a.zero_at(&tx)?)?)
        .done(env)?;
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        Some(
            Chain::from(a.succ_at(&sx, y_om)?)
                .then(congr1(env, succ_sym, ih)?)
                .then_rev(congr1(env, succ_sym, &a.succ_at(&tx, y_om)?)?)
                .done(env)?,
        )
    })?;
    let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
    Some(gen_all(&[xv], &all))
}

/// `⊢ ∀x ∀y. (x ∈ ω → (y ∈ ω → add(x,y) = add(y,x)))`.
fn add_comm(env: &mut Env, nat: &Nat, a: &Add, xv: FreeVar, yv: FreeVar) -> Option<Thm> {
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let x_om = nat.in_omega(tx.clone());
    let assumed = Thm::assume(x_om.clone());
    let succ_sym = nat.core().succ;
    let phi = Formula::eq(a.of(tx.clone(), ty.clone()), a.of(ty.clone(), tx.clone()));

    let base = Chain::from(a.zero_at(&tx)?)
        .then_rev(Thm::mp(&inst_all(&a.add_zero_l, std::slice::from_ref(&tx))?, &assumed)?)
        .done(env)?;
    let step = induct_step(nat.core(), yv, &phi, |y_om, ih| {
        Some(
            Chain::from(a.succ_at(&tx, y_om)?)
                .then(congr1(env, succ_sym, ih)?)
                .then_rev(a.succ_l_at(&ty, &assumed)?)
                .done(env)?,
        )
    })?;
    let all = induct(env, nat.core(), yv, &phi, &base, &step)?;
    let at_y = inst_self(yv, &all)?;
    Some(gen_all(&[xv, yv], &Thm::implies_intr(&x_om, &at_y)))
}

/// `⊢ ∀x ∀y ∀z. (y ∈ ω → (z ∈ ω → add(add(x,y),z) = add(x, add(y,z))))`.
fn add_assoc(env: &mut Env, nat: &Nat, a: &Add, xv: FreeVar, yv: FreeVar) -> Option<Thm> {
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let y_om = nat.in_omega(ty.clone());
    let assumed = Thm::assume(y_om.clone());
    let succ_sym = nat.core().succ;
    let xy = a.of(tx.clone(), ty.clone());
    let phi = Formula::eq(a.of(xy.clone(), tz.clone()), a.of(tx.clone(), a.of(ty.clone(), tz.clone())));

    let base = Chain::from(a.zero_at(&xy)?)
        .then_rev(congr2_r(env, a.add, &tx, &a.zero_at(&ty)?)?)
        .done(env)?;
    let step = induct_step(nat.core(), zv, &phi, |z_om, ih| {
        let yz_mem = a.mem_at(&assumed, z_om)?;
        Some(
            Chain::from(a.succ_at(&xy, z_om)?)
                .then(congr1(env, succ_sym, ih)?)
                .then_rev(a.succ_at(&tx, &yz_mem)?)
                .then_rev(congr2_r(env, a.add, &tx, &a.succ_at(&ty, z_om)?)?)
                .done(env)?,
        )
    })?;
    let all = induct(env, nat.core(), zv, &phi, &base, &step)?;
    let at_z = inst_self(zv, &all)?;
    Some(gen_all(&[xv, yv, zv], &Thm::implies_intr(&y_om, &at_z)))
}

/// `⊢ ∀a ∀b ∀c ∀d. (b ∈ ω → (c ∈ ω → (d ∈ ω →
///        add(add(a,b), add(c,d)) = add(add(a,c), add(b,d)))))`.
///
/// Five rewrites over associativity and commutativity, no induction. This is
/// the whole content of `double x + double y = double (x + y)`.
fn add_shuffle(env: &mut Env, nat: &Nat, ad: &Add) -> Option<Thm> {
    let (av, bv, cv, dv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(av), Term::var(bv), Term::var(cv), Term::var(dv));
    // `a` carries **no** hypothesis: every lemma this proof spends leaves its
    // first argument free (the recursion runs on the second), and commutativity
    // is used only on `b` and `c`. Stating `a ∈ ω` here would be an antecedent
    // the derivation never reads, and a consumer would pay for it at every
    // numeral.
    let (hb, hc, hd) =
        (nat.in_omega(tb.clone()), nat.in_omega(tc.clone()), nat.in_omega(td.clone()));
    let (b_om, c_om, d_om) =
        (Thm::assume(hb.clone()), Thm::assume(hc.clone()), Thm::assume(hd.clone()));
    let cd_mem = ad.mem_at(&c_om, &d_om)?;
    let bd_mem = ad.mem_at(&b_om, &d_om)?;

    let bc = congr2_l(env, ad.add, &ad.comm_at(&b_om, &c_om)?, &td)?;
    let swap = congr2_r(env, ad.add, &ta, &bc)?;
    let out = Chain::from(ad.assoc_at(&ta, &b_om, &cd_mem)?)
        // add(a, add(b, add(c,d))) → add(a, add(add(b,c), d))
        .then_rev(congr2_r(env, ad.add, &ta, &ad.assoc_at(&tb, &c_om, &d_om)?)?)
        // add(b,c) → add(c,b)
        .then(swap)
        // add(add(c,b), d) → add(c, add(b,d))
        .then(congr2_r(env, ad.add, &ta, &ad.assoc_at(&tc, &b_om, &d_om)?)?)
        // add(a, add(c, add(b,d))) → add(add(a,c), add(b,d))
        .then_rev(ad.assoc_at(&ta, &c_om, &bd_mem)?)
        .done(env)?;

    let discharged =
        Thm::implies_intr(&hb, &Thm::implies_intr(&hc, &Thm::implies_intr(&hd, &out)));
    Some(gen_all(&[av, bv, cv, dv], &discharged))
}
