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

// ─────────────────────────────────────────────────────────────────────────────
// The same chain over **arbitrary parts** — what `#37`'s general
// recursive-argument function needs, where the parts are ranges rather than
// singletons.
// ─────────────────────────────────────────────────────────────────────────────

/// `fin(a⃗)` **is** the chain at the singletons — literally the same term, not
/// merely a provably equal one. Every constructor term in the project is built
/// from `FinSet::of`, so this is the equation that says the general chain costs
/// the degenerate spelling nothing.
#[test]
fn the_singleton_chain_is_the_general_chain() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let elems: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let parts: Vec<Term> =
        elems.iter().map(|a| singleton(s.ap.sets.up, a.clone())).collect();
    assert_eq!(FinSet::of(&s, &elems), FinSet::chain(&s, &parts));
    assert_eq!(FinSet::chain(&s, &[]), s.zero());
}

/// `⊢ Uⱼ ⊆ chain(U⃗)` at three *distinct* parts — three, because the walk is one
/// left-injection plus `j` right-injections and `j = 2` is the first index that
/// composes two of the latter.
#[test]
fn every_part_is_included_in_the_chain() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");

    let parts: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let chain = FinSet::chain(&s, &parts);
    for j in 0..3 {
        let th = fin.part(&mut env, &s, &parts, j).expect("inclusion");
        assert_eq!(
            *th.concl(),
            kernel::thm::subset(&mut env, parts[j].clone(), chain.clone())
        );
        assert!(th.hyps().is_empty(), "a part's inclusion is unconditional");
    }
    assert!(fin.part(&mut env, &s, &parts, 3).is_none(), "out of range");
}

/// `⊢ (U₀ ⊆ T ∧ (… ∧ U_{m-1} ⊆ T)) → chain(U⃗) ⊆ T`, and — with the previous
/// test — the chain is pinned between the parts and any set containing them.
#[test]
fn the_chain_is_included_in_anything_containing_its_parts() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let fin = FinSet::new(&mut env, &s).expect("finset");

    let parts: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let t = Term::var(env.fresh_var());
    let out = fin.parts_subset(&mut env, &s, &parts, &t).expect("inclusion");

    let atoms: Vec<Formula> = parts
        .iter()
        .map(|u| kernel::thm::subset(&mut env, u.clone(), t.clone()))
        .collect();
    let want = Formula::imp(
        derived::conj_of(&atoms).expect("hypothesis"),
        kernel::thm::subset(&mut env, FinSet::chain(&s, &parts), t.clone()),
    );
    assert!(derived::establishes(&out, &want));
    assert!(
        fin.parts_subset(&mut env, &s, &[], &t).is_none(),
        "the inclusion has no antecedent at m = 0 and is not stated"
    );
}
