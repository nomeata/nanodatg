//! The recursor's typing rule — [`derived::nat::natrec_mem`].
//!
//! Every assertion rebuilds the formula it expects from the kernel's own
//! constructors, and the fixtures are chosen so that no axis the theorem is
//! supposed to distinguish is the identity on them: the motive is a *variable*,
//! so `app(C,0)`, `app(C,x)` and `app(C,succ x)` are three different terms and
//! a proof that had collapsed the fibre could not satisfy the shape below.
//!
//! Bound variables are closed to de Bruijn indices by `Formula::forall`, so a
//! statement rebuilt here with the test's own fresh variables is *the same
//! formula* as the one the construction built with its own — which is why the
//! whole conclusion can be compared with one `assert_eq!` rather than taken
//! apart.

use derived::nat::{natrec_mem, Nat};
use kernel::{Env, Formula, Term, Thm};

/// The apparatus, and three fresh variables standing for the motive, the base
/// and the step.
fn fixture() -> (Env, Nat, Term, Term, Term) {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let (cf, cv, gv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    (env, nat, Term::var(cf), Term::var(cv), Term::var(gv))
}

/// `c ∈ app(C,0) ∧ ∀x ∀v. ((x ∈ ω ∧ v ∈ app(C,x)) → app(app(g,x),v) ∈ app(C, succ x))`.
fn premises(env: &mut Env, nat: &Nat, cfam: &Term, c: &Term, g: &Term) -> Formula {
    let fibre = |t: Term| nat.apply(cfam.clone(), t);
    let (x, v) = (env.fresh_var(), env.fresh_var());
    let (tx, tv) = (Term::var(x), Term::var(v));
    let base = Formula::mem(c.clone(), fibre(nat.zero()));
    let step = Formula::forall(
        x,
        Formula::forall(
            v,
            Formula::imp(
                Formula::and(nat.in_omega(tx.clone()), Formula::mem(tv.clone(), fibre(tx.clone()))),
                Formula::mem(
                    nat.apply(nat.apply(g.clone(), tx.clone()), tv),
                    fibre(nat.succ_of(tx)),
                ),
            ),
        ),
    );
    Formula::and(base, step)
}

/// `∀n. (n ∈ ω → natrec(c,g,n) ∈ app(C,n))`.
fn conclusion(env: &mut Env, nat: &Nat, cfam: &Term, c: &Term, g: &Term) -> Formula {
    let n = env.fresh_var();
    let tn = Term::var(n);
    Formula::forall(
        n,
        Formula::imp(
            nat.in_omega(tn.clone()),
            Formula::mem(nat.natrec_of(c.clone(), g.clone(), tn.clone()), nat.apply(cfam.clone(), tn)),
        ),
    )
}

/// The exact conclusion, rebuilt.
#[test]
fn the_typing_rule_has_the_stated_shape() {
    let (mut env, nat, cfam, c, g) = fixture();
    let thm = natrec_mem(&mut env, &nat, &cfam, &c, &g).expect("the typing rule");
    assert!(thm.hyps().is_empty(), "the typing rule must be unconditional");

    let want_ante = premises(&mut env, &nat, &cfam, &c, &g);
    let want_concl = conclusion(&mut env, &nat, &cfam, &c, &g);
    assert_eq!(*thm.concl(), Formula::imp(want_ante, want_concl));
}

/// **The fibre really moves.** `app(C,0)`, `app(C,x)` and `app(C, succ x)` are
/// three different terms, so the rule above is not secretly about one fixed
/// set — a version stated at a constant motive would not carry `Nat.rec`.
#[test]
fn the_motive_is_dependent() {
    let (mut env, nat, cfam, _, _) = fixture();
    let x = Term::var(env.fresh_var());
    let fibre = |t: Term| nat.apply(cfam.clone(), t);
    let (f0, fx, fs) = (fibre(nat.zero()), fibre(x.clone()), fibre(nat.succ_of(x)));
    assert_ne!(f0, fx);
    assert_ne!(fx, fs);
    assert_ne!(f0, fs);
}

/// **It fires.** Assuming the two premises a checker would build, the rule
/// discharges to the typing of the recursor at every `n ∈ ω` — so the
/// antecedent is a shape a caller can actually produce, not one no theorem
/// meets.
#[test]
fn the_rule_discharges_against_its_own_premises() {
    let (mut env, nat, cfam, c, g) = fixture();
    let thm = natrec_mem(&mut env, &nat, &cfam, &c, &g).expect("the typing rule");
    let ante = premises(&mut env, &nat, &cfam, &c, &g);
    let want = conclusion(&mut env, &nat, &cfam, &c, &g);
    let fired = Thm::mp(&thm, &Thm::assume(ante.clone())).expect("the rule fires");
    assert_eq!(*fired.concl(), want);
    assert_eq!(fired.hyps(), &[ante][..], "exactly the premises assumed, and nothing else");
}

/// The two ι rules are what the proof is made of, and neither is reflexivity —
/// a `natrec` that computed to itself would make the rule above vacuous work.
#[test]
fn the_iota_rules_the_proof_rests_on_are_not_reflexivity() {
    let mut env = Env::new();
    let nat = Nat::new(&mut env).expect("the ω apparatus");
    let (cv, gv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (c, g, n) = (Term::var(cv), Term::var(gv), Term::var(nv));
    assert_ne!(nat.natrec_of(c.clone(), g.clone(), nat.zero()), c.clone());
    assert_ne!(
        nat.natrec_of(c.clone(), g.clone(), nat.succ_of(n.clone())),
        nat.apply(nat.apply(g.clone(), n.clone()), nat.natrec_of(c, g, n)),
    );
}
