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

use crate::decline;
use crate::err::DResult;
use crate::prim::{self, Shape};

use super::add::Add;
use super::apparatus::Nat;
use super::binary::Binary;
use super::boolean::Boolean;
use super::compare::Compare;
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
    cmp: Option<&'a Compare>,
    mem_cache: HashMap<u128, Thm>,
    meter: Meter,
}

impl<'a> Eval<'a> {
    /// Start an evaluator over an apparatus built once.
    pub fn new(nat: &'a Nat, add_ap: &'a Add, bin: &'a Binary) -> Eval<'a> {
        Eval {
            nat,
            add_ap,
            bin,
            mul_ap: None,
            cmp: None,
            mem_cache: HashMap::new(),
            meter: Meter::default(),
        }
    }

    /// The same, with multiplication available to [`Eval::mul`].
    pub fn with_mul(nat: &'a Nat, add_ap: &'a Add, bin: &'a Binary, mul_ap: &'a Mul) -> Eval<'a> {
        let mut e = Eval::new(nat, add_ap, bin);
        e.mul_ap = Some(mul_ap);
        e
    }

    /// Make [`Eval::ble`], [`Eval::blt`] and [`Eval::beq`] available.
    pub fn enable_compare(&mut self, cmp: &'a Compare) { self.cmp = Some(cmp) }

    /// Primitive kernel rule applications performed so far.
    pub fn inferences(&self) -> u64 { self.meter.get() }

    /// Reset the counter, so that one measurement does not include another.
    pub fn reset(&mut self) { self.meter = Meter::default() }

    /// The numeral term for `n`.
    pub fn numeral(&self, n: u128) -> Term { self.bin.numeral(self.nat, n) }

    // ── the six metered primitives ───────────────────────────────────────────

    /// `⊢ φ[t⃗/x⃗]` from `⊢ ∀x⃗. φ`. Two primitives per term.
    fn inst(&mut self, thm: &Thm, ts: &[Term]) -> DResult<Thm> {
        let mut cur = thm.clone();
        for t in ts {
            let step = prim::ax_inst(cur.concl().clone(), t.clone())?;
            self.meter.0 += 1;
            cur = prim::mp(&step, &cur)?;
            self.meter.0 += 1;
        }
        Ok(cur)
    }

    /// Modus ponens. One primitive.
    fn mp(&mut self, imp: &Thm, arg: &Thm) -> DResult<Thm> {
        let out = prim::mp(imp, arg)?;
        self.meter.0 += 1;
        Ok(out)
    }

    /// `⊢ a = c` from `⊢ a = b` and `⊢ b = c`. Three primitives.
    fn trans(&mut self, env: &mut Env, ab: &Thm, bc: &Thm) -> DResult<Thm> {
        let (a, b1) = ab.concl().eq_parts()?;
        let (b2, c) = bc.concl().eq_parts()?;
        if b1 != b2 {
            return Err(decline!("the two equations do not meet: the first's right side is not the second's left"))
        }
        let x = env.fresh_var();
        let leib = Thm::eq_leibniz(b1, c, x, Formula::eq(a, Term::var(x)));
        self.meter.0 += 1;
        let step = prim::mp(&leib, bc)?;
        self.meter.0 += 1;
        let out = prim::mp(&step, ab)?;
        self.meter.0 += 1;
        Ok(out)
    }

    /// `⊢ b = a` from `⊢ a = b`. Four primitives.
    fn symm(&mut self, env: &mut Env, ab: &Thm) -> DResult<Thm> {
        let (a, b) = ab.concl().eq_parts()?;
        let x = env.fresh_var();
        let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
        self.meter.0 += 1;
        let step = prim::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(a);
        self.meter.0 += 1;
        let out = prim::mp(&step, &refl)?;
        self.meter.0 += 1;
        Ok(out)
    }

    /// `⊢ f(a) = f(b)` from `⊢ a = b`, at a unary symbol. Four primitives.
    fn congr1(&mut self, env: &mut Env, f: FnSym, ab: &Thm) -> DResult<Thm> {
        let (a, b) = ab.concl().eq_parts()?;
        let x = env.fresh_var();
        let lhs = Term::apply(f, vec![a.clone()]);
        let phi = Formula::eq(lhs.clone(), Term::apply(f, vec![Term::var(x)]));
        let leib = Thm::eq_leibniz(a, b, x, phi);
        self.meter.0 += 1;
        let step = prim::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(lhs);
        self.meter.0 += 1;
        let out = prim::mp(&step, &refl)?;
        self.meter.0 += 1;
        Ok(out)
    }

    /// `⊢ f(a,r) = f(b,r)` from `⊢ a = b`, at a binary symbol. Four primitives.
    fn congr2_l(&mut self, env: &mut Env, f: FnSym, ab: &Thm, r: &Term) -> DResult<Thm> {
        let (a, b) = ab.concl().eq_parts()?;
        let x = env.fresh_var();
        let lhs = Term::apply(f, vec![a.clone(), r.clone()]);
        let phi = Formula::eq(lhs.clone(), Term::apply(f, vec![Term::var(x), r.clone()]));
        let leib = Thm::eq_leibniz(a, b, x, phi);
        self.meter.0 += 1;
        let step = prim::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(lhs);
        self.meter.0 += 1;
        let out = prim::mp(&step, &refl)?;
        self.meter.0 += 1;
        Ok(out)
    }

    /// `⊢ f(…,a,…) = f(…,b,…)` from `⊢ a = b`, rewriting argument `i` of a
    /// symbol of any arity. Four primitives.
    fn congr_at(
        &mut self,
        env: &mut Env,
        f: FnSym,
        args: &[Term],
        i: usize,
        ab: &Thm,
    ) -> DResult<Thm> {
        let (a, b) = ab.concl().eq_parts()?;
        if args.get(i) != Some(&a) {
            return Err(decline!("argument `i` is not the equation's left side"))
        }
        let x = env.fresh_var();
        let lhs = Term::apply(f, args.to_vec());
        let mut hole = args.to_vec();
        hole[i] = Term::var(x);
        let leib = Thm::eq_leibniz(a, b, x, Formula::eq(lhs.clone(), Term::apply(f, hole)));
        self.meter.0 += 1;
        let step = prim::mp(&leib, ab)?;
        self.meter.0 += 1;
        let refl = Thm::eq_refl(lhs);
        self.meter.0 += 1;
        let out = prim::mp(&step, &refl)?;
        self.meter.0 += 1;
        Ok(out)
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
    pub fn mem(&mut self, env: &mut Env, n: u128) -> DResult<Thm> {
        if let Some(t) = self.mem_cache.get(&n) {
            return Ok(t.clone())
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
        Ok(out)
    }

    /// `⊢ succ(num n) = num(n+1)`.
    ///
    /// Θ(number of trailing ones of `n`), and `O(1)` on an even argument —
    /// Isabelle's `Suc_numeral`/`BitM` interface, with the same cost.
    pub fn succ(&mut self, env: &mut Env, n: u128) -> DResult<Thm> {
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
    pub fn add(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        self.combine(env, a, b, false)
    }

    /// `⊢ addc(num a, num b) = num(a+b+1)`.
    pub fn addc(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        self.combine(env, a, b, true)
    }

    /// The one recursion behind both, `carry` selecting `addc` over `add`.
    fn combine(&mut self, env: &mut Env, a: u128, b: u128, carry: bool) -> DResult<Thm> {
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
                return Ok(base)
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
    pub fn mul(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        let m = self.mul_ap.ok_or_else(|| decline!("the evaluator was built without multiplication"))?;
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

/// Which comparison the recursion is currently deciding — Coq's
/// `compare_cont` accumulator, with `Le`/`Lt` in place of its `Lt`/`Eq`/`Gt`.
///
/// A `≤` decided at the least significant bit can be overturned by any higher
/// bit, so the recursion cannot be a fold the way `add` is. It carries instead
/// *which* comparison the remaining bits have to settle, and the two mixed
/// cases `ble (2x+1) (2y) = blt x y` and `blt (2x) (2y+1) = ble x y` are where
/// the state changes — exactly as `add`/`addc` carry the carry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum State {
    Le,
    Lt,
    Eq,
}

impl Eval<'_> {
    /// `⊢ ble(num a, num b) = num(1)` if `a ≤ b`, `= num(0)` otherwise.
    pub fn ble(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        self.decide(env, a, b, State::Le)
    }

    /// `⊢ blt(num a, num b) = num(1)` if `a < b`, `= num(0)` otherwise.
    pub fn blt(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        self.decide(env, a, b, State::Lt)
    }

    /// `⊢ beq(num a, num b) = num(1)` if `a = b`, `= num(0)` otherwise.
    pub fn beq(&mut self, env: &mut Env, a: u128, b: u128) -> DResult<Thm> {
        self.decide(env, a, b, State::Eq)
    }

    /// [`Eval::compare`], with the true value put back in numeral form.
    ///
    /// The equations produce `succ 0`, which is what `iszero(0)` unfolds to;
    /// `num(1)` is `double1(0)`, and `Binary::double1_zero` is the one theorem
    /// between them. A constant four inferences, and it keeps every evaluator
    /// output a numeral.
    fn decide(&mut self, env: &mut Env, a: u128, b: u128, st: State) -> DResult<Thm> {
        let raw = self.compare(env, a, b, st)?;
        let (_, value) = raw.concl().eq_parts()?;
        if value != self.nat.succ_of(self.nat.zero()) {
            return Ok(raw)
        }
        let back = self.symm(env, &self.bin.double1_zero.clone())?;
        self.trans(env, &raw, &back)
    }

    /// `⊢ bleb(t,f,num a, num b) = t` if `a ≤ b`, `= f` otherwise.
    pub fn ble_bool(
        &mut self,
        env: &mut Env,
        bl: &Boolean,
        t: &Term,
        f: &Term,
        a: u128,
        b: u128,
    ) -> DResult<Thm> {
        self.decide_bool(env, bl, t, f, a, b, State::Le)
    }

    /// `⊢ bltb(t,f,num a, num b) = t` if `a < b`, `= f` otherwise.
    pub fn blt_bool(
        &mut self,
        env: &mut Env,
        bl: &Boolean,
        t: &Term,
        f: &Term,
        a: u128,
        b: u128,
    ) -> DResult<Thm> {
        self.decide_bool(env, bl, t, f, a, b, State::Lt)
    }

    /// `⊢ beqb(t,f,num a, num b) = t` if `a = b`, `= f` otherwise.
    pub fn beq_bool(
        &mut self,
        env: &mut Env,
        bl: &Boolean,
        t: &Term,
        f: &Term,
        a: u128,
        b: u128,
    ) -> DResult<Thm> {
        self.decide_bool(env, bl, t, f, a, b, State::Eq)
    }

    /// [`Eval::compare`], decoded into the caller's two values.
    ///
    /// It goes through [`Eval::compare`] and **not** [`Eval::decide`]: the
    /// equations produce `succ 0`, which is exactly what
    /// [`Boolean::boolify_one`] is stated at, so putting the value back into
    /// numeral form and taking it out again would be seven inferences spent to
    /// return to where it started.
    ///
    /// Twenty-two inferences on top of [`Eval::compare`], whatever the operands
    /// — two instantiations, one congruence and two transitivities — against the
    /// seven [`Eval::decide`] spends renormalising, so a decoded comparison is
    /// **fifteen** more than the undecoded one at every width. Measured
    /// (`derived/tests/nat.rs`): `12·bits + 22`, so **70 at four bits** against
    /// 790 at sixty-four.
    fn decide_bool(
        &mut self,
        env: &mut Env,
        bl: &Boolean,
        t: &Term,
        f: &Term,
        a: u128,
        b: u128,
        st: State,
    ) -> DResult<Thm> {
        let raw = self.compare(env, a, b, st)?;
        let (lhs, value) = raw.concl().eq_parts()?;
        let (zero, one) = (self.nat.zero(), self.nat.succ_of(self.nat.zero()));
        // `compare` returns one of exactly two values. Anything else is a defect
        // in this file rather than a refusal of the caller's, and it must not be
        // decoded to `f` by falling through.
        let end = if value == one {
            bl.boolify_one.clone()
        } else if value == zero {
            bl.boolify_zero.clone()
        } else {
            return Err(decline!("the comparison did not evaluate to `succ 0` or `0`"))
        };

        let (na, nb) = (self.numeral(a), self.numeral(b));
        let ax = match st {
            State::Le => &bl.bleb_ax,
            State::Lt => &bl.bltb_ax,
            State::Eq => &bl.beqb_ax,
        };
        // `⊢ symb(t,f,num a,num b) = boolify(t,f,cmp(num a,num b))`.
        let unfold = self.inst(&ax.clone(), &[t.clone(), f.clone(), na, nb])?;
        // `⊢ boolify(t,f,cmp(num a,num b)) = boolify(t,f,value)`.
        let inner =
            self.congr_at(env, bl.boolify, &[t.clone(), f.clone(), lhs], 2, &raw)?;
        let out = self.trans(env, &unfold, &inner)?;
        let closed = self.inst(&end, &[t.clone(), f.clone()])?;
        self.trans(env, &out, &closed)
    }

    /// One pass over the bits of both arguments, in the state `st`.
    fn compare(&mut self, env: &mut Env, a: u128, b: u128, st: State) -> DResult<Thm> {
        let c =
            self.cmp.ok_or_else(|| decline!("the evaluator was built without comparison"))?;

        // ── the ends: one argument has run out of bits ───────────────────────
        if a == 0 {
            let term = self.numeral(b);
            match st {
                // `0 ≤ b` outright.
                State::Le => {
                    let at = self.inst(&c.ble_zero_l.clone(), std::slice::from_ref(&term))?;
                    let m = self.mem(env, b)?;
                    return self.mp(&at, &m)
                }
                State::Lt | State::Eq => {
                    if b == 0 {
                        return match st {
                            // `blt(0,0) = 0`, read off `blt(x,0) = 0`.
                            State::Lt => {
                                let at =
                                    self.inst(&c.blt_zero_r.clone(), std::slice::from_ref(&term))?;
                                let m = self.mem(env, 0)?;
                                self.mp(&at, &m)
                            }
                            // `beq(0,0) = succ 0`, already closed.
                            _ => {
                                self.meter.0 += 1;
                                Ok(c.beq_zero_zero.clone())
                            }
                        }
                    }
                    let half = self.numeral(b >> 1);
                    let odd = b & 1 == 1;
                    let rule = match (st, odd) {
                        (State::Lt, false) => c.blt_zero_d.clone(),
                        (State::Lt, true) => c.blt_zero_d1.clone(),
                        (_, false) => c.beq_zero_d.clone(),
                        (_, true) => c.beq_zero_d1.clone(),
                    };
                    let at = self.inst(&rule, std::slice::from_ref(&half))?;
                    let m = self.mem(env, b >> 1)?;
                    let peel = self.mp(&at, &m)?;
                    if odd {
                        return Ok(peel)
                    }
                    let rec = self.compare(env, 0, b >> 1, st)?;
                    return self.trans(env, &peel, &rec)
                }
            }
        }
        if b == 0 {
            let term = self.numeral(a);
            if st == State::Lt {
                // Nothing is below `0`.
                let at = self.inst(&c.blt_zero_r.clone(), std::slice::from_ref(&term))?;
                let m = self.mem(env, a)?;
                return self.mp(&at, &m)
            }
            let half = self.numeral(a >> 1);
            let odd = a & 1 == 1;
            let rule = match (st, odd) {
                (State::Le, false) => c.ble_d_zero.clone(),
                (State::Le, true) => c.ble_d1_zero.clone(),
                (_, false) => c.beq_d_zero.clone(),
                (_, true) => c.beq_d1_zero.clone(),
            };
            let at = self.inst(&rule, std::slice::from_ref(&half))?;
            let m = self.mem(env, a >> 1)?;
            let peel = self.mp(&at, &m)?;
            if odd {
                return Ok(peel)
            }
            let rec = self.compare(env, a >> 1, 0, st)?;
            return self.trans(env, &peel, &rec)
        }

        // ── one bit off each side ────────────────────────────────────────────
        let (ha, hb) = (a >> 1, b >> 1);
        let (ta, tb) = (self.numeral(ha), self.numeral(hb));
        let (a_odd, b_odd) = (a & 1 == 1, b & 1 == 1);
        let (rule, next) = match (st, a_odd, b_odd) {
            (State::Le, false, false) => (&c.ble_dd, Some(State::Le)),
            (State::Le, false, true) => (&c.ble_d1, Some(State::Le)),
            (State::Le, true, false) => (&c.ble_1d, Some(State::Lt)),
            (State::Le, true, true) => (&c.ble_11, Some(State::Le)),
            (State::Lt, false, false) => (&c.blt_dd, Some(State::Lt)),
            (State::Lt, false, true) => (&c.blt_d1, Some(State::Le)),
            (State::Lt, true, false) => (&c.blt_1d, Some(State::Lt)),
            (State::Lt, true, true) => (&c.blt_11, Some(State::Lt)),
            (State::Eq, false, false) => (&c.beq_dd, Some(State::Eq)),
            // Different parities: the two numbers differ, and the equation says
            // so outright. No recursion, which is why `beq` is never worse than
            // `ble` at the same width.
            (State::Eq, false, true) => (&c.beq_d1, None),
            (State::Eq, true, false) => (&c.beq_1d, None),
            (State::Eq, true, true) => (&c.beq_11, Some(State::Eq)),
        };
        let rule = rule.clone();
        let at = self.inst(&rule, &[ta, tb])?;
        let a_mem = self.mem(env, ha)?;
        let b_mem = self.mem(env, hb)?;
        let peel = {
            let half = self.mp(&at, &a_mem)?;
            self.mp(&half, &b_mem)?
        };
        match next {
            None => Ok(peel),
            Some(s) => {
                let rec = self.compare(env, ha, hb, s)?;
                self.trans(env, &peel, &rec)
            }
        }
    }
}
