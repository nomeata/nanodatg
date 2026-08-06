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
        let thm = ev.add(&mut env, a, b).unwrap_or_else(|| panic!("add {a} {b}"));
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
        let thm = ev.addc(&mut env, a, b).unwrap_or_else(|| panic!("addc {a} {b}"));
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
        let thm = ev.succ(&mut env, n).unwrap_or_else(|| panic!("succ {n}"));
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

    assert!(at64 < 4 * at32, "cost at 64 bits ({at64}) is not linear in the bit length ({at32} at 32)");
    assert!(at64 > at32, "the 64-bit certificate should cost more than the 32-bit one");

    // One more bit at the top must cost a bounded amount more, not twice.
    let mut ev3 = Eval::new(&nat, &add, &bin);
    ev3.add(&mut env, 2 * a + 1, 2 * b + 1).expect("add at two 65-bit numerals");
    let at65 = ev3.inferences();
    assert!(
        at65 - at64 < at64 / 8,
        "one extra bit cost {} inferences against {at64} for the whole 64-bit sum",
        at65 - at64
    );
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
