//! `ω` as a type of natural numbers, and the arithmetic on it.
//!
//! Every test pins the **exact** conclusion of the lemma it covers, rebuilt
//! from the kernel's formula constructors, and the fixtures are chosen so that
//! no axis a theorem is supposed to distinguish is the identity on them.

use derived::nat::{Add, Nat};
use kernel::{Env, Formula, Term};

fn fixture(env: &mut Env) -> (Nat, Add) {
    let nat = Nat::new(env).expect("the ω apparatus");
    let add = Add::new(env, &nat).expect("addition");
    (nat, add)
}

/// The apparatus builds at all, and `ω` is in the first universe.
#[test]
fn omega_is_a_set_of_the_first_universe() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    assert!(nat.omega_mem().hyps().is_empty());
    assert_eq!(*nat.omega_mem().concl(), Formula::mem(nat.omega(), nat.u1.set.clone()));
    assert_eq!(*nat.zero_mem().concl(), Formula::mem(nat.zero(), nat.omega()));
}

/// `⊢ ∀c ∀g. natrec(c,g,0) = c`.
#[test]
fn the_recursor_computes_at_zero() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let (cv, gv) = (env.fresh_var(), env.fresh_var());
    let (c, g) = (Term::var(cv), Term::var(gv));
    let want = Formula::forall(
        cv,
        Formula::forall(gv, Formula::eq(nat.natrec_of(c.clone(), g, nat.zero()), c)),
    );
    assert!(nat.iota_zero.hyps().is_empty());
    assert_eq!(*nat.iota_zero.concl(), want, "ι at zero has the wrong shape");
}

/// `⊢ ∀c ∀g ∀n. (n ∈ ω → natrec(c,g,succ n) = app(app(g,n), natrec(c,g,n)))`.
#[test]
fn the_recursor_computes_at_a_successor() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let (cv, gv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (c, g, n) = (Term::var(cv), Term::var(gv), Term::var(nv));
    let lhs = nat.natrec_of(c.clone(), g.clone(), nat.succ_of(n.clone()));
    let rhs = nat.apply(
        nat.apply(g.clone(), n.clone()),
        nat.natrec_of(c.clone(), g.clone(), n.clone()),
    );
    assert_ne!(lhs, rhs, "the ι rule would be reflexivity");
    let want = Formula::forall(
        cv,
        Formula::forall(
            gv,
            Formula::forall(nv, Formula::imp(nat.in_omega(n), Formula::eq(lhs, rhs))),
        ),
    );
    assert!(nat.iota_succ.hyps().is_empty());
    assert_eq!(*nat.iota_succ.concl(), want, "ι at a successor has the wrong shape");
}

/// The two Peano equations for `add`, at the exact shape a bridge attaches to.
#[test]
fn addition_satisfies_the_peano_equations() {
    let mut env = Env::new();
    let (nat, add) = fixture(&mut env);
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (x, y) = (Term::var(xv), Term::var(yv));

    let want_zero = Formula::forall(xv, Formula::eq(add.of(x.clone(), nat.zero()), x.clone()));
    assert!(add.add_zero.hyps().is_empty());
    assert_eq!(*add.add_zero.concl(), want_zero);

    let lhs = add.of(x.clone(), nat.succ_of(y.clone()));
    let rhs = nat.succ_of(add.of(x.clone(), y.clone()));
    assert_ne!(lhs, rhs, "add_succ would be reflexivity");
    let want_succ = Formula::forall(
        xv,
        Formula::forall(yv, Formula::imp(nat.in_omega(y), Formula::eq(lhs, rhs))),
    );
    assert!(add.add_succ.hyps().is_empty());
    assert_eq!(*add.add_succ.concl(), want_succ);
}

/// Commutativity, associativity and the exchange law are unconditional
/// theorems, and none of them is reflexivity.
#[test]
fn the_ring_facts_are_unconditional() {
    let mut env = Env::new();
    let (_nat, add) = fixture(&mut env);
    for t in [&add.add_mem, &add.add_zero_l, &add.add_succ_l, &add.add_comm, &add.add_assoc,
              &add.add_shuffle] {
        assert!(t.hyps().is_empty(), "an arithmetic lemma kept a hypothesis");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The binary view builds, and each of the eight recursion equations relates
/// two visibly different terms.
#[test]
fn the_binary_recursion_equations_are_not_reflexivity() {
    let mut env = Env::new();
    let (nat, add) = fixture(&mut env);
    let bin = derived::nat::Binary::new(&mut env, &nat, &add).expect("the binary view");
    for t in [&bin.add_dd, &bin.add_d1, &bin.add_1d, &bin.add_11,
              &bin.addc_dd, &bin.addc_d1, &bin.addc_1d, &bin.addc_11] {
        assert!(t.hyps().is_empty(), "a binary equation kept a hypothesis");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The evaluator, and the measurement that is the point of the binary view.
// ─────────────────────────────────────────────────────────────────────────────

use derived::nat::{numeral_size, Binary, Eval};

fn full(env: &mut Env) -> (Nat, Add, Binary) {
    let nat = Nat::new(env).expect("the ω apparatus");
    let add = Add::new(env, &nat).expect("addition");
    let bin = Binary::new(env, &nat, &add).expect("the binary view");
    (nat, add, bin)
}

/// Addition is computed correctly at values chosen so that no axis is the
/// identity: carry against no carry, equal against unequal bit lengths, and
/// zero on each side. Three-element cases where an order or a nesting is being
/// pinned — two would pass under a swap.
#[test]
fn addition_computes_at_numerals() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mut ev = Eval::new(&nat, &add, &bin);

    // (a, b): no carry / carry / carry cascade / unequal widths / zero both sides.
    for (a, b) in [(0u128, 0u128), (0, 7), (7, 0), (1, 1), (2, 1), (1, 2), (3, 1), (5, 10),
                   (7, 1), (255, 1), (170, 85), (171, 85), (12345, 6789), (1, 65536)] {
        let thm = ev.add(&mut env, a, b).unwrap_or_else(|e| panic!("add {a} {b}: {e}"));
        assert!(thm.hyps().is_empty(), "add {a} {b} kept a hypothesis");
        let want = Formula::eq(
            derived::nat::Add::of(&add, ev.numeral(a), ev.numeral(b)),
            ev.numeral(a + b),
        );
        assert_eq!(*thm.concl(), want, "add {a} {b} computed the wrong numeral");
        let _ = &nat;
    }
}

/// `addc` is `succ ∘ add` at every one of the same points.
#[test]
fn addition_with_carry_computes_at_numerals() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mut ev = Eval::new(&nat, &add, &bin);
    for (a, b) in [(0u128, 0u128), (0, 7), (7, 0), (1, 1), (3, 1), (255, 1), (170, 85),
                   (171, 85), (12345, 6789)] {
        let thm = ev.addc(&mut env, a, b).unwrap_or_else(|e| panic!("addc {a} {b}: {e}"));
        assert!(thm.hyps().is_empty());
        let want =
            Formula::eq(bin.addc_of(ev.numeral(a), ev.numeral(b)), ev.numeral(a + b + 1));
        assert_eq!(*thm.concl(), want, "addc {a} {b} computed the wrong numeral");
    }
}

/// The successor peels exactly one bit off an even numeral and cascades only
/// through trailing ones.
#[test]
fn the_successor_computes_on_the_binary_shape() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mut ev = Eval::new(&nat, &add, &bin);
    for n in [0u128, 1, 2, 3, 7, 8, 255, 256, 65535, 12345] {
        let thm = ev.succ(&mut env, n).unwrap_or_else(|e| panic!("succ {n}: {e}"));
        assert!(thm.hyps().is_empty());
        let want = Formula::eq(nat.succ_of(ev.numeral(n)), ev.numeral(n + 1));
        assert_eq!(*thm.concl(), want, "succ {n} computed the wrong numeral");
    }
}

/// **The measurable.** The numeral for `2⁶⁴` is 66 nodes, and the certificate
/// for `add` at two 64-bit numerals costs a number of kernel inferences that
/// grows with the *bit length* and not with the value.
///
/// The doubling check is the one that matters: squaring both arguments — one
/// extra bit — must add a bounded amount, not double the work. A construction
/// that had accidentally kept a unary step would fail here and nowhere else.
#[test]
fn the_certificate_scales_with_bit_length_and_not_with_value() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mut ev = Eval::new(&nat, &add, &bin);

    assert_eq!(numeral_size(1u128 << 64), 66, "the numeral for 2⁶⁴ is 66 nodes");
    assert_eq!(numeral_size(u64::MAX as u128), 65);
    // **The widths that separate.** `0` and `1` cannot tell the binary encoding
    // from the unary one — both are one node either way — so the pins that
    // carry the claim are `11`, the first value the old `natLit > 10` guard
    // refused, and `2⁶⁴`. Unary would be 12 and 1.8 × 10¹⁹ nodes.
    assert_eq!(numeral_size(0), 1, "num(0) is the term `0`");
    assert_eq!(numeral_size(1), 2);
    assert_eq!(numeral_size(11), 5, "num(11) = double1(double1(double(double1(0))))");
    assert_eq!(numeral_size(10), 5);

    // Two 64-bit numerals, all ones on both sides: every level carries.
    let (a, b) = (u64::MAX as u128, u64::MAX as u128);
    ev.reset();
    let thm = ev.add(&mut env, a, b).expect("add at two 64-bit numerals");
    let at64 = ev.inferences();
    assert!(thm.hyps().is_empty());
    assert_eq!(
        *thm.concl(),
        Formula::eq(add.of(ev.numeral(a), ev.numeral(b)), ev.numeral(a + b)),
    );

    // Half the bits: the cost must fall by about half, not by a factor of 2³².
    let (c, d) = (u32::MAX as u128, u32::MAX as u128);
    let mut ev2 = Eval::new(&nat, &add, &bin);
    ev2.add(&mut env, c, d).expect("add at two 32-bit numerals");
    let at32 = ev2.inferences();

    // One more bit at the top.
    let mut ev3 = Eval::new(&nat, &add, &bin);
    ev3.add(&mut env, 2 * a + 1, 2 * b + 1).expect("add at two 65-bit numerals");
    let at65 = ev3.inferences();

    // **The sharp form, and it has to be sharp.** A merely-ordinal check —
    // "64 bits costs less than four times 32 bits" — passes under a Θ(bits²)
    // certificate too, which is exactly the failure mode this measurement
    // exists to rule out. So compare *second differences*: under a cost
    // linear in the bit width the 32-bit gap must be 32 times the one-bit
    // gap, and under any quadratic term it cannot be.
    let per_bit = (at65 - at64) as i64;
    let over_32 = (at64 - at32) as i64;
    assert!(
        (over_32 - 32 * per_bit).abs() <= (at64 / 20) as i64,
        "cost is not linear in the bit width: 32 bits cost {over_32} more, \
         one bit costs {per_bit}, at 64 bits the total is {at64}"
    );
    assert!(at64 > at32, "the 64-bit certificate should cost more than the 32-bit one");
    let _ = &nat;

    eprintln!("MEASURED  num(2^64) = {} nodes", numeral_size(1u128 << 64));
    eprintln!("MEASURED  add at two 64-bit numerals = {at64} kernel inferences");
    eprintln!("MEASURED  add at two 32-bit numerals = {at32} kernel inferences");
    eprintln!("MEASURED  add at two 65-bit numerals = {at65} kernel inferences");
}

// ─────────────────────────────────────────────────────────────────────────────
// The uniqueness bridge.
// ─────────────────────────────────────────────────────────────────────────────

/// **Non-vacuity of the bridge.** Its two premises are satisfiable: the
/// iteration `ait(x)` behind `add` satisfies them by construction, so
/// discharging both yields the conclusion outright. A bridge whose antecedent
/// no set satisfied would prove nothing, and it would pass every shape test.
#[test]
fn the_pointwise_bridge_has_a_witness() {
    let mut env = Env::new();
    let (nat, add) = fixture(&mut env);
    let bridge = derived::nat::uniqueness_pointwise(&mut env, &nat, &add).expect("bridge");
    assert!(bridge.hyps().is_empty());

    // `f := ait(x)` at the very `x` the two premises are stated at.
    let x = Term::var(add.iter_var);
    let f = kernel::Term::apply(add.ait, vec![x.clone()]);
    let at = derived::inst_all(&bridge, &[x.clone(), f.clone()]).expect("instantiate");
    let after_base = kernel::Thm::mp(&at, &add.iter_base).expect("the base premise");
    let agrees = kernel::Thm::mp(&after_base, &add.iter_step).expect("the step premise");
    assert!(agrees.hyps().is_empty(), "the witness left a hypothesis");

    let yv = env.fresh_var();
    let y = Term::var(yv);
    let want = Formula::forall(
        yv,
        Formula::imp(
            nat.in_omega(y.clone()),
            Formula::eq(nat.apply(f, y.clone()), add.of(x, y)),
        ),
    );
    // `Formula::forall` closes over its variable, so which fresh one the
    // bridge happened to use is invisible in the finished formula.
    assert_eq!(*agrees.concl(), want, "the witness produced the wrong conclusion");
}

/// The two-argument bridge: any `f` read through `app` twice that satisfies the
/// two Peano equations on `ω` agrees with `add` there, with no typing
/// hypothesis on `f` at all.
#[test]
fn the_bridge_is_stated_at_an_arbitrary_operation() {
    let mut env = Env::new();
    let (nat, add) = fixture(&mut env);
    let bridge = derived::nat::uniqueness(&mut env, &nat, &add).expect("bridge");
    assert!(bridge.hyps().is_empty());
    assert!(kernel::thm::debug_locally_closed(bridge.concl()));

    // Firing it costs the same however large the numerals are: instantiate,
    // discharge the two premises, discharge the two memberships.
    let bin = Binary::new(&mut env, &nat, &add).expect("the binary view");
    let mut ev = Eval::new(&nat, &add, &bin);
    let small = ev.mem(&mut env, 3).expect("3 ∈ ω");
    let huge = ev.mem(&mut env, 1u128 << 64).expect("2⁶⁴ ∈ ω");
    let fv = env.fresh_var();
    let f = Term::var(fv);
    let spec = derived::nat::Spec::at(&nat, &add, &f, env.fresh_var(), env.fresh_var());
    let base = kernel::Thm::assume(spec.base.clone());
    let step = kernel::Thm::assume(spec.step.clone());
    let out = derived::nat::transfer(&bridge, &f, &base, &step, &small, &huge)
        .expect("the bridge fires at a 64-bit numeral");
    let want = Formula::eq(
        nat.apply(nat.apply(f, ev.numeral(3)), ev.numeral(1u128 << 64)),
        add.of(ev.numeral(3), ev.numeral(1u128 << 64)),
    );
    assert_eq!(*out.concl(), want, "the bridge transferred the wrong equation");
    assert_eq!(out.hyps().len(), 2, "only the two Peano equations should remain");
}

/// [`prim_rec`] really recurses: at `c(x) := x` and `g(x,a) := succ(a)` it
/// reproduces `add`'s two equations, and neither equation is reflexivity.
#[test]
fn parametric_primitive_recursion_computes() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let succ = nat.core().succ;
    let pr = derived::nat::prim_rec(
        &mut env,
        &nat,
        |x| x.clone(),
        |_x, a| kernel::Term::apply(succ, vec![a.clone()]),
    )
    .expect("primitive recursion");
    assert!(pr.at_zero.hyps().is_empty() && pr.at_succ.hyps().is_empty());

    let (xv, nv) = (env.fresh_var(), env.fresh_var());
    let (x, n) = (Term::var(xv), Term::var(nv));
    assert_eq!(
        *pr.at_zero.concl(),
        Formula::forall(xv, Formula::eq(pr.of(x.clone(), nat.zero()), x.clone()))
    );
    let lhs = pr.of(x.clone(), nat.succ_of(n.clone()));
    let rhs = nat.succ_of(pr.of(x.clone(), n.clone()));
    assert_ne!(lhs, rhs, "the step equation would be reflexivity");
    assert_eq!(
        *pr.at_succ.concl(),
        Formula::forall(
            xv,
            Formula::forall(nv, Formula::imp(nat.in_omega(n), Formula::eq(lhs, rhs)))
        )
    );
}

/// Multiplication: the two Peano equations, distributivity and the two binary
/// equations all build, and none of them is reflexivity.
#[test]
fn multiplication_has_both_equation_sets() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mul = derived::nat::Mul::new(&mut env, &nat, &add, &bin).expect("multiplication");
    for t in [&mul.mul_zero, &mul.mul_succ, &mul.mul_mem, &mul.mul_dist, &mul.mul_double,
              &mul.mul_double1] {
        assert!(t.hyps().is_empty(), "a multiplication lemma kept a hypothesis");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (x, y) = (Term::var(xv), Term::var(yv));
    assert_eq!(
        *mul.mul_zero.concl(),
        Formula::forall(xv, Formula::eq(mul.of(x.clone(), nat.zero()), nat.zero()))
    );
    let lhs = mul.of(x.clone(), nat.succ_of(y.clone()));
    let rhs = add.of(mul.of(x.clone(), y.clone()), x.clone());
    assert_ne!(lhs, rhs, "mul_succ would be reflexivity");
    assert_eq!(
        *mul.mul_succ.concl(),
        Formula::forall(
            xv,
            Formula::forall(yv, Formula::imp(nat.in_omega(y), Formula::eq(lhs, rhs)))
        )
    );
}

/// Multiplication computes at numerals, at points where no axis is the
/// identity: zero on each side, one on each side, powers of two, and two
/// values whose product needs a carry at every level.
#[test]
fn multiplication_computes_at_numerals() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mul = derived::nat::Mul::new(&mut env, &nat, &add, &bin).expect("multiplication");
    let mut ev = Eval::with_mul(&nat, &add, &bin, &mul);
    for (a, b) in [(0u128, 0u128), (0, 5), (5, 0), (1, 1), (1, 7), (7, 1), (2, 3), (3, 2),
                   (6, 7), (255, 255), (12345, 6789), (1u128 << 20, 3)] {
        let thm = ev.mul(&mut env, a, b).unwrap_or_else(|e| panic!("mul {a} {b}: {e}"));
        assert!(thm.hyps().is_empty(), "mul {a} {b} kept a hypothesis");
        let want = Formula::eq(mul.of(ev.numeral(a), ev.numeral(b)), ev.numeral(a * b));
        assert_eq!(*thm.concl(), want, "mul {a} {b} computed the wrong numeral");
    }

    // Schoolbook: quadratic in the bit length, still flat in the value.
    let mut e1 = Eval::with_mul(&nat, &add, &bin, &mul);
    e1.mul(&mut env, u16::MAX as u128, u16::MAX as u128).expect("16-bit product");
    let at16 = e1.inferences();
    let mut e2 = Eval::with_mul(&nat, &add, &bin, &mul);
    e2.mul(&mut env, u32::MAX as u128, u32::MAX as u128).expect("32-bit product");
    let at32 = e2.inferences();
    assert!(at32 < 6 * at16, "doubling the bit length cost more than quadratic");
    eprintln!("MEASURED  mul at two 16-bit numerals = {at16} kernel inferences");
    eprintln!("MEASURED  mul at two 32-bit numerals = {at32} kernel inferences");
}

// ─────────────────────────────────────────────────────────────────────────────
// The hypothesis gap: every theorem this module exports owes `⊢`.
//
// `derived::nat` is the **only** module in `derived/` that introduces a
// hypothesis — `derived::discharge`'s only importers are its seven files — so
// it is the only module where a theorem can leave carrying an undischarged
// assumption under an unconditional label. Nothing inside `derived/src/nat/`
// checks `hyps()`: the guarantee is the consumer half, which `discharge.rs`'s
// own header names, and this is where the consumer half is spent.
//
// The three tests below are exhaustive **by construction**: each destructures
// its bundle with a pattern that names every field and has no `..`, so adding a
// field to `Nat`, `Add`, `Binary`, `Mul` or `PrimRec` fails to compile until the
// new field is either listed as a theorem to check or explicitly named as
// something else. A `for t in [...]` loop does not have that property, and the
// difference is not hypothetical: the loops above never look at
// `Binary::double_zero` or `Binary::double1_zero`, and a mutation that gave
// `double_zero` a hypothesis while leaving its conclusion identical was caught
// here and nowhere else.
// ─────────────────────────────────────────────────────────────────────────────

use derived::all_unconditional;
use derived::nat::{Mul, PrimRec};
use kernel::Thm;

/// Every theorem `Nat` exports is unconditional, including the ones reached
/// through an accessor rather than a field.
#[test]
fn the_omega_apparatus_exports_nothing_hypothetical() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let Nat {
        rec: _,
        tower: _,
        u1: _,
        proj: _,
        p1: _,
        p1_pair,
        p2: _,
        p2_pair,
        nstep: _,
        nstep_ax,
        nstep_triple,
        nit: _,
        nit_base,
        nit_step,
        natrec: _,
        natrec_ax,
        invariant,
        iota_zero,
        iota_succ,
    } = &nat;
    let fields: [&Thm; 10] = [
        p1_pair, p2_pair, nstep_ax, nstep_triple, nit_base, nit_step, natrec_ax, invariant,
        iota_zero, iota_succ,
    ];
    assert!(all_unconditional(&fields), "a `Nat` field carries a hypothesis");
    // The Peano facts and `ω ∈ U₁` arrive through accessors, so a field sweep
    // alone would miss them.
    let reached: [&Thm; 5] =
        [nat.zero_mem(), nat.succ_mem(), nat.succ_ne_zero(), nat.succ_inj(), nat.omega_mem()];
    assert!(all_unconditional(&reached), "a `Nat` accessor returns a hypothetical theorem");
}

/// The same for `Add`, `Binary` and `Mul` — the three bundles a consumer
/// instantiates.
#[test]
fn the_arithmetic_bundles_export_nothing_hypothetical() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let mul = Mul::new(&mut env, &nat, &add, &bin).expect("multiplication");

    let Add {
        ait: _,
        add: _,
        add_ax,
        iter_base,
        iter_step,
        iter_var: _,
        add_zero,
        add_succ,
        add_mem,
        add_zero_l,
        add_succ_l,
        add_comm,
        add_assoc,
        add_shuffle,
    } = &add;
    let add_fields: [&Thm; 11] = [
        add_ax, iter_base, iter_step, add_zero, add_succ, add_mem, add_zero_l, add_succ_l,
        add_comm, add_assoc, add_shuffle,
    ];
    assert!(all_unconditional(&add_fields), "an `Add` field carries a hypothesis");

    let Binary {
        double: _,
        double_ax,
        double1: _,
        double1_ax,
        addc: _,
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
    } = &bin;
    let bin_fields: [&Thm; 20] = [
        double_ax, double1_ax, addc_ax, double_mem, double1_mem, addc_mem, double_zero,
        double1_zero, succ_double, succ_double1, add_dd, add_d1, add_1d, add_11, addc_dd,
        addc_d1, addc_1d, addc_11, addc_zero_r, addc_zero_l,
    ];
    assert!(all_unconditional(&bin_fields), "a `Binary` field carries a hypothesis");

    let Mul {
        pr,
        mul_zero,
        mul_succ,
        mul_mem,
        mul_dist,
        mul_double,
        mul_double1,
        mul_zero_l,
        mul_one_l,
    } = &mul;
    let PrimRec { sym: _, def, at_zero, at_succ, invariant } = pr;
    let mul_fields: [&Thm; 12] = [
        def, at_zero, at_succ, invariant, mul_zero, mul_succ, mul_mem, mul_dist, mul_double,
        mul_double1, mul_zero_l, mul_one_l,
    ];
    assert!(all_unconditional(&mul_fields), "a `Mul` field carries a hypothesis");
}

/// The two bridges and the evaluator's own outputs, which are what a checker
/// ends up holding.
#[test]
fn the_bridges_and_the_evaluator_export_nothing_hypothetical() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);
    let bridge = derived::nat::uniqueness(&mut env, &nat, &add).expect("the bridge");
    let pointwise =
        derived::nat::uniqueness_pointwise(&mut env, &nat, &add).expect("the pointwise bridge");
    assert!(all_unconditional(&[&bridge, &pointwise]), "a bridge carries a hypothesis");

    let mut ev = Eval::new(&nat, &add, &bin);
    let n = 1u128 << 64;
    let outs = [
        ev.mem(&mut env, n).expect("membership"),
        ev.succ(&mut env, n).expect("successor"),
        ev.add(&mut env, n, n - 1).expect("addition"),
        ev.addc(&mut env, n, n - 1).expect("addition with carry"),
    ];
    assert!(
        all_unconditional(&outs.iter().collect::<Vec<_>>()),
        "the evaluator returned a hypothetical theorem"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Comparison: `ble`, `blt`, `beq`, and the measurement that is the point.
// ─────────────────────────────────────────────────────────────────────────────

use derived::nat::{Compare, Sub};

fn cmp_fixture(env: &mut Env) -> (Nat, Add, Binary, Mul, Sub, Compare) {
    let nat = Nat::new(env).expect("the ω apparatus");
    let add = Add::new(env, &nat).expect("addition");
    let bin = Binary::new(env, &nat, &add).expect("the binary view");
    let mul = Mul::new(env, &nat, &add, &bin).expect("multiplication");
    let sb = Sub::new(env, &nat).expect("truncated subtraction");
    let cmp = Compare::new(env, &nat, &add, &bin, &mul, &sb).expect("comparison");
    (nat, add, bin, mul, sb, cmp)
}

/// `pred` and `sub` compute, and neither equation is reflexivity.
#[test]
fn truncated_subtraction_satisfies_its_equations() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let sb = Sub::new(&mut env, &nat).expect("truncated subtraction");
    let Sub {
        pp,
        pp_fst,
        pred: _,
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
        iszero: _,
        iszero_ax,
        iszero_zero,
        iszero_succ,
        iszero_mem,
    } = &sb;
    let PrimRec { sym: _, def: pp_def, at_zero: pp0, at_succ: pps, invariant: ppi } = pp;
    let PrimRec { sym: _, def: sd, at_zero: sz, at_succ: ss, invariant: si } = rec;
    let fields: [&Thm; 19] = [
        pp_fst, pred_ax, pred_zero, pred_succ, pred_mem, sub_zero, sub_succ, sub_mem, zero_sub,
        sub_pred, sub_succ_succ, iszero_ax, iszero_zero, iszero_succ, iszero_mem, pp_def, pp0,
        pps, ppi,
    ];
    assert!(all_unconditional(&fields), "a `Sub` field carries a hypothesis");
    assert!(all_unconditional(&[sd, sz, ss, si]), "a `Sub::rec` field carries a hypothesis");

    let nv = env.fresh_var();
    let n = Term::var(nv);
    assert_eq!(*pred_zero.concl(), Formula::eq(sb.pred_of(nat.zero()), nat.zero()));
    let lhs = sb.pred_of(nat.succ_of(n.clone()));
    assert_ne!(lhs, n, "pred_succ would be reflexivity");
    assert_eq!(
        *pred_succ.concl(),
        Formula::forall(nv, Formula::imp(nat.in_omega(n.clone()), Formula::eq(lhs, n.clone())))
    );
}

/// The twelve binary recursion equations build, and none is reflexivity.
#[test]
fn the_comparison_equations_are_not_reflexivity() {
    let mut env = Env::new();
    let (_nat, _add, _bin, _mul, _sb, c) = cmp_fixture(&mut env);
    for t in [
        &c.ble_dd, &c.ble_d1, &c.ble_1d, &c.ble_11, &c.blt_dd, &c.blt_d1, &c.blt_1d, &c.blt_11,
        &c.beq_dd, &c.beq_d1, &c.beq_1d, &c.beq_11, &c.ble_zero_l, &c.ble_d_zero,
        &c.ble_d1_zero, &c.blt_zero_r, &c.blt_zero_d, &c.blt_zero_d1, &c.beq_zero_zero,
        &c.beq_zero_d, &c.beq_zero_d1, &c.beq_d_zero, &c.beq_d1_zero, &c.sub_gap,
        &c.iszero_add, &c.sub_dd, &c.sub_d1, &c.sub_1d, &c.sub_11,
    ] {
        assert!(t.hyps().is_empty(), "a comparison lemma kept a hypothesis");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The three comparisons decide correctly, at every pair below 20 and at a few
/// larger ones. **Bounded**: nothing here exceeds five bits, so a mistake that
/// made the recursion unary would blow the timeout at a value of 19, not 2⁶⁴.
#[test]
fn comparison_computes_at_small_numerals() {
    let mut env = Env::new();
    let (nat, add, bin, mul, _sb, c) = cmp_fixture(&mut env);
    let mut ev = Eval::with_mul(&nat, &add, &bin, &mul);
    ev.enable_compare(&c);
    let t = ev.numeral(1);
    let f = ev.numeral(0);
    for a in 0u128..20 {
        for b in 0u128..20 {
            let want_le = if a <= b { t.clone() } else { f.clone() };
            let want_lt = if a < b { t.clone() } else { f.clone() };
            let want_eq = if a == b { t.clone() } else { f.clone() };
            for (thm, want, name, sym) in [
                (ev.ble(&mut env, a, b), want_le, "ble", c.ble),
                (ev.blt(&mut env, a, b), want_lt, "blt", c.blt),
                (ev.beq(&mut env, a, b), want_eq, "beq", c.beq),
            ] {
                let thm = thm.unwrap_or_else(|e| panic!("{name} {a} {b}: {e}"));
                assert!(thm.hyps().is_empty(), "{name} {a} {b} kept a hypothesis");
                let lhs = Term::apply(sym, vec![ev.numeral(a), ev.numeral(b)]);
                assert_eq!(
                    *thm.concl(),
                    Formula::eq(lhs, want),
                    "{name} {a} {b} decided the wrong way"
                );
            }
        }
    }
}

/// **The measurement.** The cost of a comparison certificate is linear in the
/// *bit length* and flat in the value.
///
/// The widths are walked in increasing order and each is printed, so an
/// implementation that had gone unary would exhaust the timeout at four bits
/// with the earlier lines already on the record rather than at sixty-four with
/// nothing.
///
/// The assertion is on **second differences**, not on a threshold. "64 bits
/// costs under four times 32 bits" passes under a quadratic implementation,
/// because 4 is exactly the quadratic ratio at a doubling; the gap from 1 bit to
/// 33 bits being 32 times the gap from 1 bit to 2 bits does not.
#[test]
fn the_comparison_certificate_scales_with_bit_length_and_not_with_value() {
    let mut env = Env::new();
    let (nat, add, bin, mul, _sb, c) = cmp_fixture(&mut env);

    let at = |env: &mut Env, w: u32| -> u64 {
        let mut ev = Eval::with_mul(&nat, &add, &bin, &mul);
        ev.enable_compare(&c);
        let n = (1u128 << w) - 1;
        ev.ble(env, n, n).expect("ble at equal all-ones numerals");
        let got = ev.inferences();
        eprintln!("MEASURED  ble at two {w}-bit numerals = {got} kernel inferences");
        got
    };
    let mut cost = Vec::new();
    for w in [1u32, 2, 4, 8, 16, 32, 64] {
        cost.push((w, at(&mut env, w)));
    }

    // One bit of width, priced from the smallest step there is.
    let one_bit = cost[1].1 - cost[0].1;
    // Thirty-one further bits, priced the same way: 2 → 33 would need a 33-bit
    // point, so use 1 → 32 and divide by the 31 bits between them.
    let thirty_one = cost[5].1 - cost[0].1;
    assert!(
        thirty_one * 4 >= one_bit * 31 * 3 && thirty_one * 3 <= one_bit * 31 * 4,
        "the per-bit cost is not constant: one bit costs {one_bit}, thirty-one cost \
         {thirty_one} (a linear implementation gives {}, a quadratic one gives far more)",
        one_bit * 31
    );
    // And doubling the width doubles the *increment*, which a quadratic
    // implementation cannot do.
    let d_16_32 = cost[5].1 - cost[4].1;
    let d_32_64 = cost[6].1 - cost[5].1;
    assert!(
        d_32_64 * 3 <= d_16_32 * 7 && d_32_64 * 7 >= d_16_32 * 3,
        "the increment from 32 to 64 bits ({d_32_64}) is not about twice the increment \
         from 16 to 32 ({d_16_32})"
    );

    // Flat in the value: two 64-bit numerals of very different magnitude and
    // bit pattern cost the same.
    let mut e1 = Eval::with_mul(&nat, &add, &bin, &mul);
    e1.enable_compare(&c);
    e1.ble(&mut env, u64::MAX as u128, u64::MAX as u128).expect("ble at 2⁶⁴−1");
    let mut e2 = Eval::with_mul(&nat, &add, &bin, &mul);
    e2.enable_compare(&c);
    e2.ble(&mut env, 0xAAAA_AAAA_AAAA_AAAAu128, 0xAAAA_AAAA_AAAA_AAABu128)
        .expect("ble at an alternating 64-bit pattern");
    eprintln!("MEASURED  ble 2⁶⁴−1 2⁶⁴−1 = {} kernel inferences", e1.inferences());
    eprintln!("MEASURED  ble alternating 64-bit = {} kernel inferences", e2.inferences());

    // `beq` and `blt` at the two demands `init-prelude` actually makes.
    let mut e3 = Eval::with_mul(&nat, &add, &bin, &mul);
    e3.enable_compare(&c);
    e3.ble(&mut env, 55297, 4294967296).expect("isValidChar_UInt32");
    eprintln!("MEASURED  ble 55297 4294967296 = {} kernel inferences", e3.inferences());
    let mut e4 = Eval::with_mul(&nat, &add, &bin, &mul);
    e4.enable_compare(&c);
    let thm = e4.beq(&mut env, 1u128 << 64, 1u128 << 64).expect("USize.size_eq");
    eprintln!("MEASURED  beq 2⁶⁴ 2⁶⁴ = {} kernel inferences", e4.inferences());
    assert!(thm.hyps().is_empty());
    assert_eq!(
        *thm.concl(),
        Formula::eq(
            Term::apply(c.beq, vec![e4.numeral(1u128 << 64), e4.numeral(1u128 << 64)]),
            e4.numeral(1)
        )
    );
    let _ = &nat;
}

/// **Peeling one `succ` off a numeral costs bits, never the value** — the
/// measurement `whnf`'s literal arm rests on.
///
/// A checker that reduces `natLit n` to `Nat.succ (natLit (n−1))` owes the
/// equation `num(n) = succ(num(n−1))`, and [`Eval::succ`] is it. What makes
/// that a *step* rather than a program is that its cost is Θ(trailing ones of
/// `n`) — so the sharp form is the one below: `succ` at an **even** numeral
/// costs the same at 16, 32, 64 and 100 bits, because no digit past the last
/// one is touched. No implementation whose cost depends on the value can
/// satisfy that, and a unary one could not even be run at `2¹⁰⁰`.
///
/// The all-ones row is the other end: every digit carries, and the cost rises
/// with the bit length and not faster. Both rows are needed — the even row
/// alone would pass under an implementation that had no recursion at all, and
/// the odd row alone would pass under a quadratic one.
///
/// **Measured: 2 inferences flat on the even row, and `13·bits + 1` on the
/// all-ones row** (209/417/833 at 16/32/64). The even row is the sharp one and
/// it is sharp against more than unary: a `succ` routed through `add(n, 1)`
/// would be Θ(bits) at *every* argument and would fail it, while still looking
/// perfectly fast next to a successor tower. That is the shape a silent
/// fallback takes once the obvious one is ruled out.
#[test]
fn peeling_a_successor_costs_bits_and_not_the_value() {
    let mut env = Env::new();
    let (nat, add, bin) = full(&mut env);

    let cost = |env: &mut Env, n: u128| -> u64 {
        let mut ev = Eval::new(&nat, &add, &bin);
        let thm = ev.succ(env, n).expect("succ at a numeral");
        assert!(thm.hyps().is_empty());
        assert_eq!(
            *thm.concl(),
            Formula::eq(nat.succ_of(ev.numeral(n)), ev.numeral(n + 1)),
            "succ did not conclude `succ(num n) = num(n+1)`"
        );
        ev.inferences()
    };

    // Even, at four widths. The numerals differ — 17, 33, 65 and 101 nodes —
    // so this is not four runs on one term.
    let even: Vec<u64> = [16u32, 32, 64, 100].iter().map(|b| cost(&mut env, 1u128 << b)).collect();
    assert_eq!(
        even.iter().collect::<std::collections::BTreeSet<_>>().len(),
        1,
        "succ on an even numeral is not constant across widths: {even:?}"
    );
    assert!(even[0] > 0, "succ cost nothing at all, which cannot be a certificate");

    // All ones: every digit carries. Linear in the width, checked on second
    // differences so that a quadratic term cannot hide — the same sharp form
    // `the_certificate_scales_with_bit_length_and_not_with_value` uses.
    let ones = |b: u32| -> u128 { (1u128 << b) - 1 };
    let (at16, at32, at64) =
        (cost(&mut env, ones(16)), cost(&mut env, ones(32)), cost(&mut env, ones(64)));
    let per_bit_low = (at32 - at16) as i64 / 16;
    let per_bit_high = (at64 - at32) as i64 / 32;
    assert_eq!(
        per_bit_low, per_bit_high,
        "carrying costs more per bit at 64 bits than at 32: {at16}/{at32}/{at64}"
    );
    assert!(at64 > even[0], "the all-ones case should cost more than the even one");

    eprintln!("MEASURED  succ at an even numeral (2^16 … 2^100) = {} inferences, flat", even[0]);
    eprintln!("MEASURED  succ at all-ones 16/32/64 bits = {at16}/{at32}/{at64} inferences");
}
