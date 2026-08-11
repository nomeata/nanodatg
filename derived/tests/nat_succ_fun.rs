//! `succ` as an element of `fs(ω,ω)` — [`derived::nat::SuccFun`].
//!
//! Three pins, and each is a statement a consumer rests on rather than a
//! restatement of the code: the graph is **in the function space**, applying it
//! **computes `succ`**, and both are **unconditional** in the sequent as well as
//! in the formula.
//!
//! The typing is what `⟦Nat.succ⟧` needs to be a *constant of type `Nat → Nat`*
//! at all, and the β rule is what an ι step at `Nat.succ n` contracts with.

use derived::nat::{Nat, SuccFun};
use kernel::{Env, Formula, Term};

fn fixture() -> (Env, Nat, SuccFun) {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let sf = SuccFun::over(&mut env, &nat).expect("the successor graph");
    (env, nat, sf)
}

/// `⊢ lam(ω) ∈ fs(ω,ω)`, resting on nothing.
///
/// The function space is pinned as `nat.tower.sums.fs` rather than rebuilt:
/// the whole point of reading it off the tower is that it is the *same* symbol
/// the interpretation uses for `⟦α → β⟧`, and a test that minted its own would
/// pass while the checker's `⟦Nat.succ⟧` sat in a set nothing else mentions.
#[test]
fn the_successor_graph_is_a_function_from_omega_to_omega() {
    let (_env, nat, sf) = fixture();
    let omega = nat.omega();
    let want =
        Formula::mem(sf.term.clone(), nat.tower.sums.fs.of(omega.clone(), omega));
    assert!(sf.in_funspace.hyps().is_empty(), "the typing rests on an assumption");
    assert_eq!(*sf.in_funspace.concl(), want, "the successor graph's typing has the wrong shape");
}

/// `⊢ ∀n. (n ∈ ω → app(lam(ω), n) = succ(n))`.
///
/// Stated at the apparatus's own `succ_of` and `apply`, so a β rule that
/// computed some *other* unary operation could not satisfy it.
#[test]
fn applying_the_successor_graph_computes_succ() {
    let (mut env, nat, sf) = fixture();
    let nv = env.fresh_var();
    let n = Term::var(nv);
    let want = Formula::forall(
        nv,
        Formula::imp(
            Formula::mem(n.clone(), nat.omega()),
            Formula::eq(nat.apply(sf.term.clone(), n.clone()), nat.succ_of(n)),
        ),
    );
    assert!(sf.beta.hyps().is_empty(), "the β rule rests on an assumption");
    assert_eq!(*sf.beta.concl(), want, "the successor graph's β rule has the wrong shape");
}

/// The graph is `lam` at `ω` and at nothing else.
///
/// A weak pin on its own; it is here because the two theorems above are stated
/// at `sf.term`, so a `term` that had drifted from the domain the theorems were
/// instantiated at would make both of them vacuously self-consistent.
#[test]
fn the_graph_term_is_the_lambda_at_omega() {
    let (_env, nat, sf) = fixture();
    assert_eq!(sf.term, Term::apply(sf.lam, vec![nat.omega()]));
}
