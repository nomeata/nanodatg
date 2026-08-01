//! The choice function, and the evidence that naming it says anything.
//!
//! Every assertion here compares a derived theorem against a formula rebuilt
//! from the constructors, so that "it returned `Some`" is never mistaken for
//! "it proved the right thing".

use derived::choice;
use derived::funcs::Apply;
use kernel::{Env, Formula, Term, Thm};

/// Build the whole apparatus once: pairing, union, `∅`, `app`, and the two
/// bridge theorems.
fn setup(env: &mut Env) -> (Apply, Thm, Thm, Thm) {
    let ap = Apply::new(env).expect("build the application apparatus");
    let opair_desc =
        choice::opair_described(env, &ap.sets, &ap.mem_sing).expect("described pair = built pair");
    let bridge = choice::pair_in_bridge(env, &ap.sets, &opair_desc).expect("pair-in bridge");
    let app_pair = derived::ext::app_of_pair(env, &ap).expect("app_of_pair");
    (ap, opair_desc, bridge, app_pair)
}

#[test]
fn described_pair_is_the_constructed_pair() {
    let mut env = Env::new();
    let (ap, opair_desc, _, _) = setup(&mut env);

    let (a, b, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tp) = (Term::var(a), Term::var(b), Term::var(p));
    let is_op = kernel::thm::is_opair(&mut env, tp.clone(), ta.clone(), tb.clone());
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                p,
                Formula::iff(is_op, Formula::eq(tp, derived::opair(ap.sets.up, ta, tb))),
            ),
        ),
    );
    assert_eq!(*opair_desc.concl(), want, "opair_described has the wrong conclusion");
}

#[test]
fn pair_in_bridges_to_membership() {
    let mut env = Env::new();
    let (ap, _, bridge, _) = setup(&mut env);

    let (f, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tb) = (Term::var(f), Term::var(a), Term::var(b));
    let described = kernel::thm::pair_in(&mut env, tf.clone(), ta.clone(), tb.clone());
    let built = Formula::mem(ap.sets.pair(ta, tb), tf);
    let want = Formula::forall(
        f,
        Formula::forall(a, Formula::forall(b, Formula::iff(described, built))),
    );
    assert_eq!(*bridge.concl(), want, "pair_in_bridge has the wrong conclusion");
}

/// `⊢ ∃f. IsChoiceFn(f, u)` at an arbitrary term is exactly the axiom
/// instantiated, and nothing more.
#[test]
fn a_choice_function_exists_on_any_set() {
    let mut env = Env::new();
    let u = Term::apply(env.declare(0), vec![]);
    let thm = choice::choice_fn_existence(&mut env, &u).expect("instantiate ax_choice");

    let f = env.fresh_var();
    let want = Formula::exists(f, kernel::thm::is_choice_fn(&mut env, Term::var(f), u));
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀x ∃f. IsChoiceFn(f, U(x))` — the thesis's `ε`, as closely as this can be
/// named: one choice function per universe, chosen after the universe.
#[test]
fn a_choice_function_exists_on_a_universe() {
    let mut env = Env::new();
    let (lu, _lu_ax) = derived::universe::least_universe(&mut env).expect("define U");
    let thm = choice::choice_fn_on_universe(&mut env, lu).expect("choice on U(x)");

    let (x, f) = (env.fresh_var(), env.fresh_var());
    let u = Term::apply(lu, vec![Term::var(x)]);
    let want = Formula::forall(
        x,
        Formula::exists(f, kernel::thm::is_choice_fn(&mut env, Term::var(f), u)),
    );
    assert_eq!(*thm.concl(), want);
}

/// The lemma a caller needs:
/// `⊢ ∀f ∀u ∀x. (IsChoiceFn(f,u) → ((x ∈ u ∧ ∃w. w ∈ x) → app(f,x) ∈ x))`.
#[test]
fn a_choice_function_picks_a_member() {
    let mut env = Env::new();
    let (ap, _, bridge, app_pair) = setup(&mut env);
    let thm = choice::choice_app(&mut env, &ap, &bridge, &app_pair).expect("choice_app");

    let (f, u, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tu, tx) = (Term::var(f), Term::var(u), Term::var(x));
    let hyp = kernel::thm::is_choice_fn(&mut env, tf.clone(), tu.clone());
    let guard = Formula::and(
        Formula::mem(tx.clone(), tu),
        kernel::thm::nonempty(&mut env, tx.clone()),
    );
    let concl = Formula::mem(ap.apply(tf, tx.clone()), tx);
    let want = Formula::forall(
        f,
        Formula::forall(
            u,
            Formula::forall(x, Formula::imp(hyp, Formula::imp(guard, concl))),
        ),
    );
    assert_eq!(*thm.concl(), want, "choice_app has the wrong conclusion");
}

/// **Non-vacuity.** `⊢ ∃f. (IsChoiceFn(f, {{∅}}) ∧ app(f,{∅}) = ∅)`.
///
/// The conjunct on the right is what makes this more than "the hypothesis is
/// satisfiable": the first three clauses of `IsChoiceFn` leave `app(f,{∅})`
/// completely undetermined, so the equation can only come from the choice
/// clause.
#[test]
fn the_hypothesis_is_satisfiable_and_says_something() {
    let mut env = Env::new();
    let (ap, _, bridge, app_pair) = setup(&mut env);
    let main = choice::choice_app(&mut env, &ap, &bridge, &app_pair).expect("choice_app");
    let thm = choice::choice_nonvacuous(&mut env, &ap, &main).expect("non-vacuity");

    let empty = Term::apply(ap.empty, vec![]);
    let s_empty = derived::singleton(ap.sets.up, empty.clone());
    let ss_empty = derived::singleton(ap.sets.up, s_empty.clone());

    let f = env.fresh_var();
    let tf = Term::var(f);
    let hyp = kernel::thm::is_choice_fn(&mut env, tf.clone(), ss_empty);
    let eq = Formula::eq(ap.apply(tf, s_empty), empty);
    let want = Formula::exists(f, Formula::and(hyp, eq));
    assert_eq!(*thm.concl(), want, "choice_nonvacuous has the wrong conclusion");
}
