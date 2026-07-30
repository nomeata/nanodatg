//! Independent check of opair_inj's statement, written without reference to
//! the agent's own tests.
use kernel::{Env, Formula, Term};

#[test]
fn independent_opair_inj_statement() {
    let mut env = Env::new();
    let (up, up_ax) = derived::upair(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, up, &up_ax).unwrap();
    let sing_inj = derived::singleton_inj(&mut env, up, &mem_sing).unwrap();
    let fst = derived::opair_fst(&mut env, up, &up_ax, &mem_sing, &sing_inj).unwrap();
    let snd = derived::pairs::opair_snd(&mut env, up, &up_ax, &mem_sing, &fst).unwrap();
    let inj = derived::pairs::opair_inj(&mut env, up, &fst, &snd).unwrap();

    // Build the expected statement from scratch, four distinct constants.
    let cs: Vec<Term> = (0..4).map(|_| Term::apply(env.declare(0), vec![])).collect();
    let (a, b, c, d) = (cs[0].clone(), cs[1].clone(), cs[2].clone(), cs[3].clone());

    let got = derived::inst_all(&inj, &[a.clone(), b.clone(), c.clone(), d.clone()]).unwrap();
    let expected = Formula::imp(
        Formula::eq(derived::opair(up, a.clone(), b.clone()), derived::opair(up, c.clone(), d.clone())),
        Formula::and(Formula::eq(a, c), Formula::eq(b, d)),
    );
    assert_eq!(*got.concl(), expected, "opair_inj is not the statement it claims");

    // Sanity: the hypothesis is NOT trivially true, i.e. the theorem is not
    // vacuous. <a,b> and <c,d> for distinct constants are distinct terms.
    let (lhs, _) = got.concl().as_imp().unwrap();
    let (l, r) = lhs.as_eq().unwrap();
    assert_ne!(l, r, "the antecedent is a triviality — the theorem would say nothing");
}
