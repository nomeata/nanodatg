//! **The certified evaluator**, and the meter that counts what it costs.
//!
//! # Interface
//!
//! ```text
//! Eval::numeral(n)                the term num(n)
//! Eval::mem(env, n)     -> ⊢ num(n) ∈ ω
//! Eval::succ(env, n)    -> ⊢ succ(num n)      = num(n+1)
//! Eval::add(env, a, b)  -> ⊢ add(num a, num b)  = num(a+b)
//! Eval::addc(env, a, b) -> ⊢ addc(num a, num b) = num(a+b+1)
//! Eval::inferences()              primitive kernel rule applications so far
//! ```
//!
//! Every theorem it returns is unconditional and is about the *defined* symbols
//! `add`, `addc`, `succ` on `ω` — there is no second representation and nothing
//! is assumed about the arguments beyond what [`Eval::mem`] proves.
//!
//! # Why the meter is here and not a wrapper around the kernel
//!
//! `kernel/` must not grow, so it has no counter and cannot acquire one. The
//! honest alternative is to count at the only place that knows: this module
//! calls the kernel's **primitive rules directly** — `ax_inst`, `mp`,
//! `eq_refl`, `eq_leibniz` — through the six one-line wrappers below, each of
//! which ticks once per primitive it applies. Nothing in this file reaches a
//! `Thm` by any other route, so [`Eval::inferences`] is an exact count and not
//! an estimate. It deliberately does **not** call `crate::eq_trans` and
//! friends, whose costs would then have to be looked up and would drift.
//!
//! The count covers the whole certificate the evaluator builds, including the
//! `num(k) ∈ ω` side conditions every instantiation needs. It does **not**
//! cover [`crate::nat::Nat::new`] / [`crate::nat::Add::new`] /
//! [`crate::nat::Binary::new`], which are built once per environment and shared
//! by every numeral thereafter — a fixed cost, not a per-numeral one.
//!
//! # The shape of the recursion, and what it costs
//!
//! `add` and `addc` recurse together on the bits of both arguments, one bit per
//! level, and terminate when either argument reaches `0`:
//!
//! ```text
//! add  0 b = b        add  a 0 = a
//! addc 0 b = succ b   addc a 0 = succ a
//! add  (double  x) (double  y) = double  (add  x y)     …and six more
//! ```
//!
//! so the recursion depth is `min(bits a, bits b)` plus, at the base, one
//! `succ` whose own cascade is bounded by the trailing ones of what it wraps.
//! Every level spends a **fixed** number of kernel inferences: two
//! instantiations of one universally quantified equation, two `mp`s for the
//! `∈ ω` side conditions, one congruence and one transitivity. The count is
//! therefore Θ(bits) with a small constant, and **not** a function of the
//! value — which is the entire claim the binary view exists to make.
//!
//! `Eval::mem` is memoised on the value. Without it the side conditions alone
//! would be Θ(bits²), since each of the Θ(bits) levels asks for a membership
//! proof that is itself Θ(bits) deep.

use std::collections::HashMap;

use kernel::{Env, FnSym, Formula, Term, Thm};

use super::add::Add;
use super::apparatus::Nat;
use super::binary::Binary;
use super::mul::Mul;

/// A count of primitive kernel rule applications.
#[derive(Default, Clone, Copy, Debug)]
pub struct Meter(u64);

impl Meter {
    /// The count so far.
    pub fn get(self) -> u64 { self.0 }
}

/// The evaluator: numerals, their membership proofs, and the three operations.
pub struct Eval<'a> {
    nat: &'a Nat,
    add_ap: &'a Add,
    bin: &'a Binary,
    mul_ap: Option<&'a Mul>,
    mem_cache: HashMap<u128, Thm>,
    meter: Meter,
}

impl<'a> Eval<'a> {
    /// Start an evaluator over an apparatus built once.
    pub fn new(nat: &'a Nat, add_ap: &'a Add, bin: &'a Binary) -> Eval<'a> {
        Eval { nat, add_ap, bin, mul_ap: None, mem_cache: HashMap::new(), meter: Meter::default() }
    }

    /// The same, with multiplication available to [`Eval::mul`].
    pub fn with_mul(nat: &'a Nat, add_ap: &'a Add, bin: &'a Binary, mul_ap: &'a Mul) -> Eval<'a> {
        let mut e = Eval::new(nat, add_ap, bin);
        e.mul_ap = Some(mul_ap);
        e
    }

    /// Primitive kernel rule applications performed so far.
    pub fn inferences(&self) -> u64 { self.meter.get() }

    /// Reset the counter, so that one measurement does not include another.
    pub fn reset(&mut self) { self.meter = Meter::default() }

    /// The numeral term for `n`.
    pub fn numeral(&self, n: u128) -> Term { self.bin.numeral(self.nat, n) }

    // ── the six metered primitives ───────────────────────────────────────────

    /// `⊢ φ[t⃗/x⃗]` from `⊢ ∀x⃗. φ`. Two primitives per term.
    fn inst(&mut self, thm: &Thm, ts: &[Term]) -> Option<Thm> {
        let mut cur = thm.clone();
        for t in ts {
            let step = Thm::ax_inst(cur.concl().clone(), t.clone())?;
            self.meter.0 += 1;
            cur = Thm::mp(&step, &cur)?;
            self.meter.0 += 1;
        }
        Some(cur)
    }

    /// Modus ponens. One primitive.
    fn mp(&mut self, imp: &Thm, arg: &Thm) -> Option<Thm> {
        let out = Thm::mp(imp, arg)?;
        self.meter.0 += 1;
        Some(out)
    }

    /// `⊢ a = c` from `⊢ a = b` and `⊢ b = c`. Three primitives.
    fn trans(&mut self, env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
        let (a, b1) = ab.concl().as_eq()?;
        let (b2, c) = bc.concl().as_eq()?;
        if b1 != b2 {
            return None
        }
        let x = env.fresh_var();
        let leib = Thm::eq_leibniz(b1, c, x, Formula::eq(a, Term::var(x)));
        self.meter.0 += 1;
        let step = Thm::mp(&leib, bc)?;
        self.meter.0 += 1;
        let out = Thm::mp(&step, ab)?;
        self.meter.0 += 1;
        Some(out)
    }

    /// `⊢ b = a` from `⊢ a = b`. Four primitives.
    fn symm(&mut self, env: &mut Env, ab: &Thm) -> Option<Thm> {
        let (a, b) = ab.concl().as_eq()?;
        let x = env.fresh_var();
        let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
        self.meter.0 += 1;
        let step = Thm::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(a);
        self.meter.0 += 1;
        let out = Thm::mp(&step, &refl)?;
        self.meter.0 += 1;
        Some(out)
    }

    /// `⊢ f(a) = f(b)` from `⊢ a = b`, at a unary symbol. Four primitives.
    fn congr1(&mut self, env: &mut Env, f: FnSym, ab: &Thm) -> Option<Thm> {
        let (a, b) = ab.concl().as_eq()?;
        let x = env.fresh_var();
        let lhs = Term::apply(f, vec![a.clone()]);
        let phi = Formula::eq(lhs.clone(), Term::apply(f, vec![Term::var(x)]));
        let leib = Thm::eq_leibniz(a, b, x, phi);
        self.meter.0 += 1;
        let step = Thm::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(lhs);
        self.meter.0 += 1;
        let out = Thm::mp(&step, &refl)?;
        self.meter.0 += 1;
        Some(out)
    }

    /// `⊢ f(a,r) = f(b,r)` from `⊢ a = b`, at a binary symbol. Four primitives.
    fn congr2_l(&mut self, env: &mut Env, f: FnSym, ab: &Thm, r: &Term) -> Option<Thm> {
        let (a, b) = ab.concl().as_eq()?;
        let x = env.fresh_var();
        let lhs = Term::apply(f, vec![a.clone(), r.clone()]);
        let phi = Formula::eq(lhs.clone(), Term::apply(f, vec![Term::var(x), r.clone()]));
        let leib = Thm::eq_leibniz(a, b, x, phi);
        self.meter.0 += 1;
        let step = Thm::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(lhs);
        self.meter.0 += 1;
        let out = Thm::mp(&step, &refl)?;
        self.meter.0 += 1;
        Some(out)
    }

    // ── the evaluator proper ─────────────────────────────────────────────────

    /// `⊢ num(n) ∈ ω`, memoised on the value.
    ///
    /// The environment is threaded but only reaches the recursive call; it is
    /// kept because every other method here takes one and a membership proof
    /// that did not would be the odd one out at every call site — and because
    /// a future rule needing a fresh variable would otherwise change the
    /// signature of everything that calls it.
    #[allow(clippy::only_used_in_recursion)]
    pub fn mem(&mut self, env: &mut Env, n: u128) -> Option<Thm> {
        if let Some(t) = self.mem_cache.get(&n) {
            return Some(t.clone())
        }
        let out = if n == 0 {
            self.nat.zero_mem().clone()
        } else {
            let inner = self.mem(env, n >> 1)?;
            let half = self.numeral(n >> 1);
            let rule =
                if n & 1 == 1 { &self.bin.double1_mem } else { &self.bin.double_mem };
            let at = self.inst(&rule.clone(), std::slice::from_ref(&half))?;
            self.mp(&at, &inner)?
        };
        self.mem_cache.insert(n, out.clone());
        Some(out)
    }

    /// `⊢ succ(num n) = num(n+1)`.
    ///
    /// Θ(number of trailing ones of `n`), and `O(1)` on an even argument —
    /// Isabelle's `Suc_numeral`/`BitM` interface, with the same cost.
    pub fn succ(&mut self, env: &mut Env, n: u128) -> Option<Thm> {
        if n == 0 {
            // `succ(0) = double1(0) = num(1)`, read off `double1(0) = succ(0)`.
            return self.symm(env, &self.bin.double1_zero.clone())
        }
        let half = self.numeral(n >> 1);
        if n & 1 == 0 {
            // `succ(double h) = double1 h`.
            return self.inst(&self.bin.succ_double.clone(), std::slice::from_ref(&half))
        }
        // `succ(double1 h) = double(succ h) = double(num(h+1))`.
        let h_mem = self.mem(env, n >> 1)?;
        let at = self.inst(&self.bin.succ_double1.clone(), std::slice::from_ref(&half))?;
        let peel = self.mp(&at, &h_mem)?;
        let rec = self.succ(env, n >> 1)?;
        let lifted = self.congr1(env, self.bin.double, &rec)?;
        self.trans(env, &peel, &lifted)
    }

    /// `⊢ add(num a, num b) = num(a+b)`.
    pub fn add(&mut self, env: &mut Env, a: u128, b: u128) -> Option<Thm> {
        self.combine(env, a, b, false)
    }

    /// `⊢ addc(num a, num b) = num(a+b+1)`.
    pub fn addc(&mut self, env: &mut Env, a: u128, b: u128) -> Option<Thm> {
        self.combine(env, a, b, true)
    }

    /// The one recursion behind both, `carry` selecting `addc` over `add`.
    fn combine(&mut self, env: &mut Env, a: u128, b: u128, carry: bool) -> Option<Thm> {
        // ── the two ends ─────────────────────────────────────────────────────
        if a == 0 || b == 0 {
            let (other, side) = if a == 0 { (b, true) } else { (a, false) };
            let term = self.numeral(other);
            let base = match (carry, side) {
                // `add(0,b) = b`, under `b ∈ ω`.
                (false, true) => {
                    let at =
                        self.inst(&self.add_ap.add_zero_l.clone(), std::slice::from_ref(&term))?;
                    let m = self.mem(env, other)?;
                    self.mp(&at, &m)?
                }
                // `add(a,0) = a`, unconditionally.
                (false, false) =>
                    self.inst(&self.add_ap.add_zero.clone(), std::slice::from_ref(&term))?,
                // `addc(0,b) = succ b`, under `b ∈ ω`.
                (true, true) => {
                    let at =
                        self.inst(&self.bin.addc_zero_l.clone(), std::slice::from_ref(&term))?;
                    let m = self.mem(env, other)?;
                    self.mp(&at, &m)?
                }
                // `addc(a,0) = succ a`, unconditionally.
                (true, false) =>
                    self.inst(&self.bin.addc_zero_r.clone(), std::slice::from_ref(&term))?,
            };
            if !carry {
                return Some(base)
            }
            let bump = self.succ(env, other)?;
            return self.trans(env, &base, &bump)
        }

        // ── one bit off each side ────────────────────────────────────────────
        let (ha, hb) = (a >> 1, b >> 1);
        let (ta, tb) = (self.numeral(ha), self.numeral(hb));
        let (a_odd, b_odd) = (a & 1 == 1, b & 1 == 1);

        // Which equation fires, and whether the recursive call carries.
        let (rule, wrapper, sub_carry) = match (carry, a_odd, b_odd) {
            (false, false, false) => (&self.bin.add_dd, self.bin.double, false),
            (false, false, true) => (&self.bin.add_d1, self.bin.double1, false),
            (false, true, false) => (&self.bin.add_1d, self.bin.double1, false),
            (false, true, true) => (&self.bin.add_11, self.bin.double, true),
            (true, false, false) => (&self.bin.addc_dd, self.bin.double1, false),
            (true, false, true) => (&self.bin.addc_d1, self.bin.double, true),
            (true, true, false) => (&self.bin.addc_1d, self.bin.double, true),
            (true, true, true) => (&self.bin.addc_11, self.bin.double1, true),
        };
        let rule = rule.clone();
        let at = self.inst(&rule, &[ta, tb])?;
        let a_mem = self.mem(env, ha)?;
        let b_mem = self.mem(env, hb)?;
        let peel = {
            let half = self.mp(&at, &a_mem)?;
            self.mp(&half, &b_mem)?
        };
        let rec = self.combine(env, ha, hb, sub_carry)?;
        let lifted = self.congr1(env, wrapper, &rec)?;
        self.trans(env, &peel, &lifted)
    }
}

/// The number of nodes in a term — `1` for a variable, `1 +` the children for
/// an application.
///
/// The kernel keeps `TermData` private, so this is computed the only way a
/// consumer can: by rebuilding the term from a known recipe and counting as it
/// goes. [`numeral_size`] is the instance that matters.
pub fn numeral_size(n: u128) -> u64 {
    if n == 0 {
        return 1
    }
    1 + numeral_size(n >> 1)
}

impl Eval<'_> {
    /// `⊢ mul(num a, num b) = num(a·b)`.
    ///
    /// Schoolbook: the recursion decomposes only the **second** argument, and
    /// every set bit of it costs one Θ(bits) addition. Θ(bits²) overall, which
    /// is what Isabelle's `2b² − b − 1` measures for the same algorithm.
    ///
    /// Requires the evaluator to have been built with [`Eval::with_mul`].
    pub fn mul(&mut self, env: &mut Env, a: u128, b: u128) -> Option<Thm> {
        let m = self.mul_ap?;
        let a_num = self.numeral(a);
        if b == 0 {
            return self.inst(&m.mul_zero.clone(), std::slice::from_ref(&a_num))
        }
        let half = b >> 1;
        let h_num = self.numeral(half);
        let a_mem = self.mem(env, a)?;
        let h_mem = self.mem(env, half)?;
        let rule = if b & 1 == 1 { m.mul_double1.clone() } else { m.mul_double.clone() };
        let at = self.inst(&rule, &[a_num.clone(), h_num])?;
        let peel = {
            let one = self.mp(&at, &a_mem)?;
            self.mp(&one, &h_mem)?
        };

        // `double(mul(A,H))` normalised to the numeral for `2·a·half`.
        let rec = self.mul(env, a, half)?;
        let mut doubled = self.congr1(env, self.bin.double, &rec)?;
        if a * half == 0 {
            // `double(0)` is *not* the numeral for `0`; `num` has no leading
            // zeros, so the doubling has to be collapsed rather than left.
            let collapse = self.bin.double_zero.clone();
            self.meter.0 += 1; // the theorem is reused, not rebuilt; count the link
            doubled = self.trans(env, &doubled, &collapse)?;
        }
        if b & 1 == 0 {
            return self.trans(env, &peel, &doubled)
        }
        // Odd: one addition of the carried first argument.
        let lifted = self.congr2_l(env, self.add_ap.add, &doubled, &a_num)?;
        let sum = self.add(env, 2 * a * half, a)?;
        let tail = self.trans(env, &lifted, &sum)?;
        self.trans(env, &peel, &tail)
    }
}
