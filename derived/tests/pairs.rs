//! The characteristic property of the Kuratowski ordered pair.
//!
//! Every assertion here pins the *exact* conclusion, not merely something
//! equivalent to it: the whole point of the locally nameless representation is
//! that alpha-equivalent formulas are syntactically equal, so a lemma that is
//! only derivably-the-right-thing would break the next derivation that consumes
//! it, far from where the mistake was made.

use derived::pairs::{opair_inj, opair_snd};
use kernel::{Env, FnSym, Formula, Term, Thm};

/// The common prelude: `upair` and the two singleton lemmas, plus `opair_fst`.
fn prelude() -> (Env, FnSym, Thm, Thm, Thm) {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, up, &up_ax).expect("mem_singleton");
    let sing_inj = derived::singleton_inj(&mut env, up, &mem_sing).expect("singleton_inj");
    let fst = derived::opair_fst(&mut env, up, &up_ax, &mem_sing, &sing_inj).expect("opair_fst");
    (env, up, up_ax, mem_sing, fst)
}

/// Four fresh constants to instantiate the quantifiers at.
fn constants(env: &mut Env) -> (Term, Term, Term, Term) {
    let (a, b, c, d) = (env.declare(0), env.declare(0), env.declare(0), env.declare(0));
    (Term::apply(a, vec![]), Term::apply(b, vec![]), Term::apply(c, vec![]), Term::apply(d, vec![]))
}

/// The second component of a Kuratowski pair is determined by the pair.
#[test]
fn opair_second_component() {
    let (mut env, up, up_ax, mem_sing, fst) = prelude();
    let snd = opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).expect("opair_snd derivation");
    assert!(kernel::thm::debug_locally_closed(snd.concl()), "opair_snd has a dangling bound variable");

    let (ta, tb, tc, td) = constants(&mut env);
    let inst = derived::inst_all(&snd, &[ta.clone(), tb.clone(), tc.clone(), td.clone()]).expect("instantiate");

    let expected = Formula::imp(
        Formula::eq(derived::opair(up, ta, tb.clone()), derived::opair(up, tc, td.clone())),
        Formula::eq(tb, td),
    );
    assert_eq!(*inst.concl(), expected, "opair_snd has the wrong shape");
}

/// The statement really is four nested `∀`s, not something that merely
/// instantiates to the right thing at four arguments.
#[test]
fn opair_snd_is_fully_quantified() {
    let (mut env, up, up_ax, mem_sing, fst) = prelude();
    let snd = opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).expect("opair_snd derivation");

    let mut cur = snd.concl().clone();
    for i in 0..4 {
        assert!(cur.is_forall(), "quantifier {i} is missing");
        let t = Term::apply(env.declare(0), vec![]);
        cur = Thm::ax_inst(cur, t).expect("instantiate").concl().as_imp().expect("instance").1;
    }
    // What is left under the four quantifiers is the implication itself.
    assert!(cur.as_imp().is_some(), "the body should be an implication");
}

/// The degenerate quadruples, where the two components of a pair coincide, are
/// the ones the nested case analysis exists for. Check the lemma still applies
/// when instantiated at repeated constants.
#[test]
fn opair_snd_handles_degenerate_pairs() {
    let (mut env, up, up_ax, mem_sing, fst) = prelude();
    let snd = opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).expect("opair_snd derivation");

    let (ta, _tb, tc, _td) = constants(&mut env);
    // ⟨a,a⟩ = ⟨c,c⟩ → a = c
    let inst = derived::inst_all(&snd, &[ta.clone(), ta.clone(), tc.clone(), tc.clone()]).expect("instantiate");
    let expected = Formula::imp(
        Formula::eq(derived::opair(up, ta.clone(), ta.clone()), derived::opair(up, tc.clone(), tc.clone())),
        Formula::eq(ta, tc),
    );
    assert_eq!(*inst.concl(), expected);
}

/// Both components at once — the lemma the function-graph construction needs.
#[test]
fn opair_is_injective() {
    let (mut env, up, up_ax, mem_sing, fst) = prelude();
    let snd = opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).expect("opair_snd derivation");
    let inj = opair_inj(&mut env, up, &fst, &snd).expect("opair_inj derivation");
    assert!(kernel::thm::debug_locally_closed(inj.concl()), "opair_inj has a dangling bound variable");

    let (ta, tb, tc, td) = constants(&mut env);
    let inst = derived::inst_all(&inj, &[ta.clone(), tb.clone(), tc.clone(), td.clone()]).expect("instantiate");

    let expected = Formula::imp(
        Formula::eq(derived::opair(up, ta.clone(), tb.clone()), derived::opair(up, tc.clone(), td.clone())),
        Formula::and(Formula::eq(ta, tc), Formula::eq(tb, td)),
    );
    assert_eq!(*inst.concl(), expected, "opair_inj has the wrong shape");
}

/// The conjunction is a real one: both halves come back out with `and_elim`,
/// which is what any consumer of the lemma will do.
#[test]
fn opair_inj_conjuncts_are_recoverable() {
    let (mut env, up, up_ax, mem_sing, fst) = prelude();
    let snd = opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).expect("opair_snd derivation");
    let inj = opair_inj(&mut env, up, &fst, &snd).expect("opair_inj derivation");

    let (ta, tb, tc, td) = constants(&mut env);
    let inst = derived::inst_all(&inj, &[ta.clone(), tb.clone(), tc.clone(), td.clone()]).expect("instantiate");
    let (hyp, conj) = inst.concl().as_imp().expect("an implication");

    // Under the hypothesis, project out each component.
    let left = derived::syl(&inst, &derived::and_left(
        Formula::eq(ta.clone(), tc.clone()),
        Formula::eq(tb.clone(), td.clone()),
    ))
    .expect("left projection");
    let right = derived::syl(&inst, &derived::and_right(
        Formula::eq(ta.clone(), tc.clone()),
        Formula::eq(tb.clone(), td.clone()),
    ))
    .expect("right projection");

    assert_eq!(conj, Formula::and(Formula::eq(ta.clone(), tc.clone()), Formula::eq(tb.clone(), td.clone())));
    assert_eq!(*left.concl(), Formula::imp(hyp.clone(), Formula::eq(ta, tc)));
    assert_eq!(*right.concl(), Formula::imp(hyp, Formula::eq(tb, td)));
}
