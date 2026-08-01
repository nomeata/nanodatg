//! The finite set `{a₀, …, a_{m-1}}` as a chain of binary unions — the
//! codomain [`derived::recarg`] types its branches against.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** [`FinSet::mem`] alone would hold of the
//! universe and [`FinSet::subset`] alone would hold of `∅`;
//! [`the_chain_is_not_empty`] shows the two cannot both be about the empty set.

use kernel::{Env, Formula, Term};

use derived::finset::FinSet;
use derived::sums::Sums;
use derived::{inst_all, singleton};

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

#[test]
fn every_element_is_in_the_chain() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");

    let elems: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let chain = FinSet::of(&s, &elems);
    for i in 0..3 {
        let th = fin.mem(&s, &elems, i).expect("membership");
        assert_eq!(*th.concl(), Formula::mem(elems[i].clone(), chain.clone()));
    }
    assert!(fin.mem(&s, &elems, 3).is_none(), "out of range");
}

#[test]
fn the_empty_chain_is_the_empty_set() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");
    assert_eq!(FinSet::of(&s, &[]), s.zero());
    assert!(
        fin.subset(&mut env, &s, &[], &s.unit()).is_none(),
        "the inclusion has no antecedent at m = 0 and is not stated"
    );
}

#[test]
fn the_chain_is_included_in_anything_holding_its_elements() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");

    let (a, b) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let t = Term::var(env.fresh_var());
    let sub = fin.subset(&mut env, &s, &[a.clone(), b.clone()], &t).expect("inclusion");

    let expected = Formula::imp(
        Formula::and(
            Formula::mem(a.clone(), t.clone()),
            Formula::mem(b.clone(), t.clone()),
        ),
        kernel::thm::subset(&mut env, FinSet::of(&s, &[a, b]), t),
    );
    assert_eq!(*sub.concl(), expected);
}

/// The two exports contradict each other on `∅`, so neither is vacuous: `a` is
/// in the chain, and if the chain were `∅` that would refute `¬(a ∈ ∅)`.
#[test]
fn the_chain_is_not_empty() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");

    let a = Term::var(env.fresh_var());
    let mem = fin.mem(&s, std::slice::from_ref(&a), 0).expect("a ∈ {a} ∪ ∅");
    assert_eq!(*mem.concl(), Formula::mem(a.clone(), FinSet::of(&s, std::slice::from_ref(&a))));
    assert_ne!(FinSet::of(&s, std::slice::from_ref(&a)), s.zero(), "the chain is not the term ∅");

    // The chain is a union of a singleton, so its element is recoverable.
    let sing = singleton(s.ap.sets.up, a.clone());
    assert_ne!(sing, s.zero());

    // And `∅` really has no members, so the two statements are about different
    // sets — the membership above is not vacuously true of everything.
    let no_mem = inst_all(&s.ap.empty_ax, std::slice::from_ref(&a)).expect("¬(a ∈ ∅)");
    assert_eq!(*no_mem.concl(), Formula::not(Formula::mem(a, s.zero())));
    assert!(closed(&Formula::not(Formula::mem(s.unit(), s.zero()))));
}
