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

#[cfg(test)]
pub(crate) mod tests_support {
    use crate::env::{Declaration, Environment};
    use crate::expr::{forall, konst, sort, Level, Name};

    pub(crate) fn no_levels() -> std::rc::Rc<[Level]> { Vec::new().into() }

    /// `Nat` as the exports declare it.
    pub(crate) fn nat_env() -> Environment {
        let n = Name::simple("Nat");
        let one = Level::zero().succ();
        let ty = sort(one);
        let zero_ty = konst(n, no_levels());
        let succ_ty = forall(konst(n, no_levels()), konst(n, no_levels()));
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: n,
                lparams: vec![],
                num_params: 0,
                ty,
                ctors: vec![
                    (Name::str(&n, "zero"), zero_ty),
                    (Name::str(&n, "succ"), succ_ty),
                ],
            },
        )
        .expect("Nat is accepted");
        env
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::tests_support::{nat_env, no_levels};
    use crate::expr::{konst, Name};
    use crate::kernel::Checker;

    fn nm(s: &str) -> Name { Name::simple(s) }


    /// `⟦Nat⟧` is `ω`, `⟦Nat.zero⟧` is `0`, and both typings are the
    /// apparatus's own — the *same terms*, not ones that print alike.
    #[test]
    fn the_carrier_is_omega_and_zero_is_the_empty_set() {
        let env = nat_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let n = nm("Nat");

        let t = c.infer_type(&konst(n, no_levels())).expect("infer ⟦Nat⟧");
        let carrier = t.tm.clone().expect("⟦Nat⟧ has a term");
        let z = c.infer_type(&konst(Name::str(&n, "zero"), no_levels())).expect("infer ⟦Nat.zero⟧");
        let zero = z.tm.clone().expect("⟦Nat.zero⟧ has a term");

        let nc = c.interp().expect("threaded").nat_clause().expect("the ω apparatus");
        assert_eq!(carrier, nc.nat.omega(), "⟦Nat⟧ is not this Interp's ω");
        assert_eq!(zero, nc.nat.zero(), "⟦Nat.zero⟧ is not 0");
        assert!(t.ev.thm().is_some(), "⟦Nat⟧ has no typing: {:?}", t.ev);
        assert!(z.ev.thm().is_some(), "⟦Nat.zero⟧ has no typing: {:?}", z.ev);
    }

    /// **The literal is binary, at widths that can tell.**
    ///
    /// `0` and `1` cannot separate the two encodings — one node either way —
    /// so the pins that carry the claim are `11`, the first value the retired
    /// `natLit > 10` guard refused, and `2⁶⁴ − 1`, the largest a `u64` holds.
    /// Unary would be `2n+1` nodes: 23 and 3.7 × 10¹⁹.
    #[test]
    fn a_literal_is_interpreted_through_the_binary_view() {
        let env = nat_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);

        for (n, nodes) in [(0u128, 1u64), (1, 2), (11, 5), (u128::from(u64::MAX), 65), (1u128 << 64, 66)] {
            let t = c.infer_type(&crate::expr::nat_lit(n)).expect("infer a literal");
            let tm = t.tm.clone().unwrap_or_else(|| panic!("⟦natLit {n}⟧ has no term"));
            let mem = t
                .ev
                .thm()
                .unwrap_or_else(|| panic!("⟦natLit {n}⟧ has no typing: {:?}", t.ev))
                .clone();
            let nc = c.interp().expect("threaded").nat_clause().expect("the ω apparatus");
            assert_eq!(tm, nc.numeral(n), "⟦natLit {n}⟧ is not num({n})");
            assert_eq!(
                *mem.concl(),
                kernel::Formula::mem(tm, nc.nat.omega()),
                "⟦natLit {n}⟧ is not typed in ω"
            );
            assert_eq!(
                derived::nat::numeral_size(n),
                nodes,
                "num({n}) is not {nodes} nodes — the encoding moved"
            );
        }
    }

    /// **`whnf` peels one `succ`, with a certificate, at a width unary cannot
    /// reach.**
    ///
    /// This is the measurement the whole clause exists for. At `2⁶⁴ − 1` the
    /// successor path does not merely cost more — `NAT-REPRESENTATION.md`
    /// §1.3.2 measured a *55296*-deep tower producing no verdict in 600 s — so
    /// a fallback to it would present as a hang and this test would time out
    /// rather than fail. The `Ev::Proved` assertion is what makes it fail
    /// instead: an acceptance-only reduction would still return the right
    /// expression.
    #[test]
    fn whnf_peels_a_successor_off_a_literal_with_a_certificate() {
        let env = nat_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);

        for n in [1u128, 11, u128::from(u64::MAX), 1u128 << 64] {
            let e = crate::expr::nat_lit(n);
            let t = c.infer_type(&e).expect("infer the literal");
            let tm = t.tm.clone().expect("the literal has a term");
            let (to, conv) =
                c.whnf_conv(&e, Some(tm.clone()), &crate::ev::Gap::NoEndpoint).expect("whnf");

            // The reduct is `Nat.succ (natLit (n−1))`, syntactically.
            let want = crate::expr::app(
                konst(Name::str(&nm("Nat"), "succ"), no_levels()),
                crate::expr::nat_lit(n - 1),
            );
            assert_eq!(to, want, "whnf on natLit {n} did not peel one succ");

            // …and the leg is a *theorem*, not an absence.
            let thm = conv
                .ev
                .thm()
                .unwrap_or_else(|| panic!("natLit {n} reduced without a certificate: {:?}", conv.ev))
                .clone();
            let nc = c.interp().expect("threaded").nat_clause().expect("the ω apparatus");
            let (lhs, _) = thm.concl().as_eq().expect("the leg is an equation");
            assert_eq!(lhs, nc.numeral(n), "the leg is not about num({n})");
        }
    }

    /// **Zero is the one width where the step is still reflexivity**, and that
    /// is a fact about the clause rather than a special case in it: `num(0)`
    /// *is* `0` and `⟦Nat.zero⟧` *is* `0`, because one clause put both there.
    #[test]
    fn the_literal_zero_and_the_constructor_are_one_term() {
        let env = nat_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let lit = c.infer_type(&crate::expr::nat_lit(0)).expect("infer natLit 0");
        let ctor = c
            .infer_type(&konst(Name::str(&nm("Nat"), "zero"), no_levels()))
            .expect("infer ⟦Nat.zero⟧");
        assert_eq!(lit.tm, ctor.tm, "⟦natLit 0⟧ and ⟦Nat.zero⟧ are different terms");
    }
}

#[cfg(test)]
mod guard_tests {
    use super::tests_support::*;
    use crate::expr::{konst, Name};
    use crate::kernel::{Checker, Lhs, DEFEQ_MAX_DEPTH};
    use crate::interp::Interp;

    /// **A literal pair is decided by value, not by peeling.**
    ///
    /// `whnf` turns `natLit n` into `Nat.succ (natLit (n−1))`, so a `def_eq`
    /// that reduces first meets the two literals again one smaller, and
    /// `assert_def_eq_as` ↔ `def_eq_struct` recurse **one stack frame per unit
    /// of the literal**. At `55296` — `Nat.isValidChar`'s, and `init-prelude`'s
    /// declaration 96 — that is a stack overflow in seconds.
    ///
    /// The widths are chosen to separate: `0` and `1` are decided by *any*
    /// implementation, and `55296` is decided only by one that does not peel.
    /// The unequal pair matters as much as the equal one — peeling decides it
    /// after `min(a,b)` levels, so a fast path that only short-circuits
    /// *equal* literals would still die here.
    #[test]
    fn a_literal_pair_is_decided_by_value_and_not_by_peeling() {
        let env = nat_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        for n in [0u128, 1, 11, 55296, 1u128 << 64] {
            let e = crate::expr::nat_lit(n);
            c.assert_is_def_eq(&e, &e).unwrap_or_else(|m| panic!("natLit {n} ≠ itself: {m}"));
        }
        // …and distinct literals are refused, also without peeling.
        for (a, b) in [(0u128, 1u128), (11, 12), (55296, 55295), (1u128 << 64, 1u128 << 63)] {
            let (ea, eb) = (crate::expr::nat_lit(a), crate::expr::nat_lit(b));
            assert!(
                c.assert_is_def_eq(&ea, &eb).is_err(),
                "natLit {a} and natLit {b} were accepted as definitionally equal"
            );
        }
    }

    /// **The recursion is bounded, and the bound is a rejection.**
    ///
    /// A stack overflow is the one failure mode neither `timeout` nor
    /// `ulimit -v` catches — it aborts with no verdict and no counter, and it
    /// took a core dump to find out which two functions were on the stack. So
    /// the depth is bounded and the bound reports.
    ///
    /// The fixture is a right-nested spine deeper than the bound, compared
    /// with itself: there is no identity short-circuit, so the `App`/`App` arm
    /// descends every level. `Lhs::Type` keeps `infer_type` out of it, so what
    /// is measured is the `def_eq` recursion and nothing else.
    #[test]
    fn def_eq_recursion_is_bounded_and_says_so() {
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let env = nat_env();
                let mut ip = Interp::new();
                let mut c = Checker::threaded(&env, &mut ip);
                let f = konst(Name::str(&Name::simple("Nat"), "succ"), no_levels());
                let mut deep = konst(Name::str(&Name::simple("Nat"), "zero"), no_levels());
                for _ in 0..(DEFEQ_MAX_DEPTH + 50) {
                    deep = crate::expr::app(f, deep);
                }
                c.assert_def_eq_as(&deep, None, &deep, None, Lhs::Type).err()
            })
            .expect("spawn")
            .join()
            .expect("the guard must not abort the process");
        let msg = handle.expect("a term past the bound must be rejected, not accepted");
        assert!(
            msg.contains(&DEFEQ_MAX_DEPTH.to_string()),
            "the rejection does not name the bound: {msg}"
        );
    }
}
