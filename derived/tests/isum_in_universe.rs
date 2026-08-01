//! `⊢ ∀c. finord(m) ∈ U(c)` — the finite-ordinal fibre is a member of every
//! universe.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the point.** `Σ(m) ∈ U(c)` is just as true of an empty
//! `Σ(m)` inside a `U(c)` that holds everything, so
//! [`the_fibre_placed_in_the_universe_has_three_elements`] shows the set has
//! three provably distinct members and the universe is not everything.

use kernel::{Env, Formula, Term, Thm};

use derived::isum::{finord_in_universe, finords_in_universe, ISumSyms, SumClosure};
use derived::sums::Sums;
use derived::tower::Tower;
use derived::inst_all;

/// A formula with no free variables — an *unconditional*, closed statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// The tower is the one place all four closure ingredients already sit on a
/// single chain of definitional extensions, so it is what the apparatus is
/// built over here.
fn build(env: &mut Env, upto: usize) -> (Tower, SumClosure, ISumSyms) {
    let t = Tower::new(env).expect("Tower::new");
    let clo = SumClosure::new(
        env,
        &t.sums,
        t.space.lu,
        &t.empty_in,
        &t.pairing,
        &t.product,
        &t.bin_union,
    )
    .expect("SumClosure::new");
    let mut syms = ISumSyms::new();
    let s = t.sums.clone();
    syms.ensure(env, &s, upto).expect("the sum symbols");
    (t, clo, syms)
}

/// The two facts the fold is built out of, at the shapes the header states.
#[test]
fn the_apparatus_holds_the_two_base_memberships() {
    let mut env = Env::new();
    let (t, clo, _) = build(&mut env, 0);
    let s = &t.sums;

    let c = env.fresh_var();
    let u = Term::apply(t.space.lu, vec![Term::var(c)]);
    assert_eq!(*clo.empty.concl(), Formula::forall(c, Formula::mem(s.zero(), u.clone())));
    assert_eq!(*clo.unit.concl(), Formula::forall(c, Formula::mem(s.unit(), u)));
    assert!(clo.empty.hyps().is_empty() && clo.unit.hyps().is_empty());

    // `1 ∈ U(c)` is not an assumption: it is `{∅} ∈ U(c)`, one pairing step
    // above `∅ ∈ U(c)`, and the two are different sets.
    assert_eq!(s.unit(), derived::singleton(s.ap.sets.up, s.zero()));
    assert_ne!(s.unit(), s.zero());
}

/// `⊢ ∀c. Sum_m(1,…,1) ∈ U(c)`, at every arity from `0` to `3`, rebuilt from
/// the kernel's constructors and with nothing left over.
#[test]
fn the_finite_ordinal_is_a_member_of_every_universe() {
    let mut env = Env::new();
    let (t, clo, syms) = build(&mut env, 3);
    let s = t.sums.clone();

    for m in 0..=3 {
        let th = finord_in_universe(&mut env, &clo, &s, &syms, m).expect("finord_in_universe");
        assert!(th.hyps().is_empty(), "m = {m}: a hypothesis survived");
        assert!(closed(th.concl()), "m = {m}: not a closed statement");

        let c = env.fresh_var();
        let u = Term::apply(t.space.lu, vec![Term::var(c)]);
        let sigma = syms.finord(&s, m).expect("finord");
        assert_eq!(*th.concl(), Formula::forall(c, Formula::mem(sigma, u)), "m = {m}");
    }

    // `finord(0)` is the *symbol* `Sum_0()`, not the term `∅`, so the unfolding
    // at the end of the derivation is doing work even at the empty arity.
    assert_ne!(syms.finord(&s, 0).expect("finord 0"), s.zero());
    // And it is not the term `1` at `m = 1` either.
    assert_ne!(syms.finord(&s, 1).expect("finord 1"), s.unit());
}

/// The `Vec` form is the singular one at each count, and shares the apparatus
/// rather than rebuilding it.
#[test]
fn the_declaration_form_agrees_with_the_single_one() {
    let mut env = Env::new();
    let (t, clo, syms) = build(&mut env, 3);
    let s = t.sums.clone();

    let counts = [2usize, 0, 3, 1, 2];
    let many =
        finords_in_universe(&mut env, &clo, &s, &syms, &counts).expect("finords_in_universe");
    assert_eq!(many.len(), counts.len());
    for (th, &m) in many.iter().zip(counts.iter()) {
        let one = finord_in_universe(&mut env, &clo, &s, &syms, m).expect("finord_in_universe");
        assert_eq!(th.concl(), one.concl(), "m = {m}");
        assert!(th.hyps().is_empty());
    }
    // An empty declaration asks for nothing and gets nothing.
    assert!(finords_in_universe(&mut env, &clo, &s, &syms, &[])
        .expect("the empty declaration")
        .is_empty());
}

/// **Non-vacuity.** The set placed in `U(c)` has three provably distinct
/// elements, and `U(c)` is not a set everything belongs to.
#[test]
fn the_fibre_placed_in_the_universe_has_three_elements() {
    let mut env = Env::new();
    let (t, clo, syms) = build(&mut env, 3);
    let s = t.sums.clone();

    let th = finord_in_universe(&mut env, &clo, &s, &syms, 3).expect("finord_in_universe");
    let omega = t.omega();
    let u = Term::apply(t.space.lu, vec![omega.clone()]);
    let sigma = syms.finord(&s, 3).expect("finord 3");

    // The theorem at a concrete seed.
    let at = inst_all(&th, std::slice::from_ref(&omega)).expect("instantiate");
    assert_eq!(*at.concl(), Formula::mem(sigma.clone(), u.clone()));
    assert!(at.hyps().is_empty());

    // Three points of it, from the injections' membership rule at `• ∈ 1`.
    let summands = vec![s.unit(); 3];
    let points: Vec<Term> = (0..3)
        .map(|i| {
            let mut args = summands.clone();
            args.push(s.point());
            let mem = Thm::mp(
                &inst_all(syms.inj_mem(3, i).expect("inj_mem"), &args).expect("instantiate"),
                &s.unit_mem,
            )
            .expect("mp");
            let p = syms.inj(i, s.point()).expect("Inj_i(•)");
            assert_eq!(*mem.concl(), Formula::mem(p.clone(), sigma.clone()));
            assert!(mem.hyps().is_empty());
            p
        })
        .collect();

    // And they are pairwise distinct, so `Σ(3)` did not collapse to a point.
    for i in 0..3 {
        for j in 0..3 {
            if i == j {
                continue
            }
            let d = syms.inj_distinct(&mut env, &s, i, j).expect("inj_distinct");
            let at = inst_all(&d, &[s.point(), s.point()]).expect("instantiate");
            assert_eq!(
                *at.concl(),
                Formula::not(Formula::eq(points[i].clone(), points[j].clone()))
            );
            assert!(at.hyps().is_empty());
        }
    }

    // The universe is not everything: it does not contain itself.
    let no_self = inst_all(&t.no_self_mem, std::slice::from_ref(&u)).expect("instantiate");
    assert_eq!(*no_self.concl(), Formula::not(Formula::mem(u.clone(), u.clone())));
    // …and the fibre is a different term from the universe holding it.
    assert_ne!(sigma, u);
}

/// A stack that does not fit together is refused rather than described.
#[test]
fn the_apparatus_refuses_a_foreign_stack() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");

    // The pairing lemma where the product closure belongs.
    assert!(SumClosure::new(
        &mut env,
        &t.sums,
        t.space.lu,
        &t.empty_in,
        &t.pairing,
        &t.pairing,
        &t.bin_union,
    )
    .is_none());

    // A universe operator of the wrong arity.
    let binary = env.declare(2);
    assert!(SumClosure::new(
        &mut env,
        &t.sums,
        binary,
        &t.empty_in,
        &t.pairing,
        &t.product,
        &t.bin_union,
    )
    .is_none());

    // A *hypothetical* closure lemma. `Thm::assume` is exempt from the boundary
    // rule in test code precisely so that this guard can be pinned: without it
    // the `Γ` would ride through `mp` into a `∀c` conclusion.
    let hypothetical = Thm::assume(t.empty_in.concl().clone());
    assert!(!hypothetical.hyps().is_empty());
    assert!(SumClosure::new(
        &mut env,
        &t.sums,
        t.space.lu,
        &hypothetical,
        &t.pairing,
        &t.product,
        &t.bin_union,
    )
    .is_none());
}

/// One apparatus serves one `Sums`. A second family is refused rather than
/// answered out of the first one's theorems.
#[test]
fn a_second_family_is_refused() {
    let mut env = Env::new();
    let (t, clo, syms) = build(&mut env, 2);
    let s1 = t.sums.clone();
    assert!(clo.is_over(&s1));

    // A second, independent sum construction: a different `sum` symbol, so a
    // closure lemma about the first says nothing about its nests.
    let s2 = Sums::new(&mut env).expect("a second Sums");
    assert_ne!(s1.sum, s2.sum);
    assert!(!clo.is_over(&s2));
    assert!(finord_in_universe(&mut env, &clo, &s2, &syms, 2).is_none());
    assert!(finords_in_universe(&mut env, &clo, &s2, &syms, &[0, 1]).is_none());

    // And an arity the symbol cache has not reached is refused, not invented.
    assert!(finord_in_universe(&mut env, &clo, &s1, &syms, 5).is_none());
}
