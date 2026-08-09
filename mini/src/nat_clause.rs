//! **The `Nat` clause's apparatus** — `ω` and its arithmetic, over *this*
//! `Interp`'s own tower.
//!
//! # Interface
//!
//! ```text
//! Interp::nat_clause()        -> Option<Rc<NatClause>>
//! NatClause::numeral(n)       the term num(n)
//! NatClause::mem(env, n)      -> ⊢ num(n) ∈ ω
//! ```
//!
//! # Why it is lazy, and why it is separate from [`crate::direct::Direct`]
//!
//! `Direct::build` runs on the first constant taking a direct clause and `Eq`
//! occurs in most exports; this is `Nat`'s, and `Nat` occurs in **two** of the
//! ninety-one tutorial exports. What it builds is `ω` with a recursor, addition
//! by iteration, the binary view, multiplication, subtraction and the three
//! comparisons — the whole of `derived/src/nat/` — so an export that never
//! mentions `Nat` must not pay for any of it. That is the same
//! lazy-with-a-failure-flag shape [`Interp::direct`](crate::interp::Interp::direct)
//! and [`crate::acc`] have, for the same reason.
//!
//! # One tower, and it is the caller's
//!
//! [`derived::nat::Nat::new`] mints its own [`Tower`](derived::tower::Tower) —
//! a fresh chain of definitional extensions, hence a second `1`, `•`, `app`,
//! `∅`, pairing and `ω`. Using it here would not be a type error: `⊢ ω ∈ U₁`
//! would simply be a membership in a `U₁` no interpretation mentions, and
//! `⟦Nat.zero⟧ = 0` would name an `∅` nothing else does, and both would sit in
//! the store looking correct. [`derived::nat::Nat::over`] takes the tower this
//! `Interp` already committed to, which makes `nat.u1.set` *the same term* as
//! [`Interp::sort(1)`](crate::interp::Interp::sort) rather than one that prints
//! the same.
//!
//! This is the hazard `MINI-HANDOFF.md` §2 records the project paying 54 ι
//! sites for, and the reason `crate::acc` states at length why the *one* place
//! that does re-mint is safe. Here the two would meet on the first
//! `⟦Nat.zero⟧`.
//!
//! # Everything below is memoised on the value, not on the term
//!
//! [`derived::nat::Eval`] caches `num(n) ∈ ω` on `n`, which is what keeps the
//! side conditions Θ(bits) rather than Θ(bits²). The evaluator is therefore
//! held here and reused across the whole file rather than minted per literal —
//! a fresh `Eval` per use site would be correct and would throw the memo away
//! at every one.

use std::rc::Rc;

use kernel::{Env, Term, Thm};

use derived::nat::{Add, Binary, Compare, Eval, Mul, Nat, Sub};

use crate::interp::Interp;

/// `ω`, its arithmetic, and the evaluator that runs on numerals.
pub struct NatClause {
    /// `ω`, `0`, `succ`, `natrec` and the two ι rules.
    pub nat: Nat,
    /// `add`, by iterated `succ`.
    pub add: Add,
    /// `double`, `double1`, `addc` and the numeral encoding.
    pub bin: Binary,
    /// Multiplication.
    pub mul: Mul,
    /// `pred` and truncated subtraction.
    pub sub: Sub,
    /// `ble`, `blt`, `beq`.
    pub cmp: Compare,
}

impl NatClause {
    /// Build the whole apparatus over the tower the caller already has.
    pub fn build(env: &mut Env, tower: Rc<derived::tower::Tower>) -> Option<NatClause> {
        let nat = Nat::over(env, tower).ok()?;
        let add = Add::new(env, &nat).ok()?;
        let bin = Binary::new(env, &nat, &add).ok()?;
        let mul = Mul::new(env, &nat, &add, &bin).ok()?;
        let sub = Sub::new(env, &nat).ok()?;
        let cmp = Compare::new(env, &nat, &add, &bin, &mul, &sub).ok()?;
        Some(NatClause { nat, add, bin, mul, sub, cmp })
    }

    /// An evaluator over this apparatus, with every operation enabled.
    ///
    /// Short-lived by construction — it borrows the apparatus — so the memo it
    /// carries is per call rather than per file. See [`Interp::nat_eval`],
    /// which is the entry point that matters and which threads one.
    pub fn eval(&self) -> Eval<'_> {
        let mut e = Eval::with_mul(&self.nat, &self.add, &self.bin, &self.mul);
        e.enable_compare(&self.cmp);
        e
    }

    /// The numeral term for `n` — `num(2⁶⁴)` is 66 nodes, not 2⁶⁴ of anything.
    pub fn numeral(&self, n: u128) -> Term { self.bin.numeral(&self.nat, n) }

    /// `⊢ num(n) ∈ ω`.
    pub fn mem(&self, env: &mut Env, n: u128) -> Option<Thm> {
        self.eval().mem(env, n).ok()
    }
}

impl Interp {
    /// The `Nat` clause's apparatus, over this `Interp`'s own tower.
    ///
    /// Built on first use and then shared: two uses of `Nat` at different `σ`
    /// — and every literal in the file — must name **one** `ω`, or a
    /// definitional equality between them would need a theorem where
    /// reflexivity should do.
    pub fn nat_clause(&mut self) -> Option<Rc<NatClause>> {
        if self.nat.is_none() && !self.nat_failed {
            let tower = Rc::clone(&self.prelude.tower);
            self.nat = NatClause::build(&mut self.env, tower).map(Rc::new);
            self.nat_failed = self.nat.is_none();
        }
        self.nat.clone()
    }
}
