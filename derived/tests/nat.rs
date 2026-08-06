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
