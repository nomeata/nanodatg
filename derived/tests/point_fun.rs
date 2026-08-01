//! The one-point function `{⟨a,b⟩}`.
//!
//! Each test rebuilds the expected formula from the kernel's own constructors,
//! so a theorem with the right name and the wrong shape fails here.
//!
//! **Non-vacuity.** The three typing clauses would all hold of a graph with no
//! values, so [`the_one_point_graph_computes`] pins the *equation*
//! `app({⟨a,b⟩}, a) = b` and checks its two sides are different terms — which
//! is what says the graph relates something to something.

use kernel::{Env, Formula, Term};

use derived::point_fun::PointFun;
use derived::sums::Sums;
use derived::wtype::Wtype;

fn build(env: &mut Env) -> (Sums, PointFun) {
    let wt = Wtype::new(env).expect("W-type");
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("point functions");
    (wt.sums, pf)
}

#[test]
fn a_one_point_graph_relates_nothing_else() {
    let mut env = Env::new();
    let (s, pf) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(pf.pairs.concl()));

    let (a, b, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx, ty) = (Term::var(a), Term::var(b), Term::var(x), Term::var(y));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                x,
                Formula::forall(
                    y,
                    Formula::imp(
                        Formula::mem(
                            s.ap.sets.pair(tx.clone(), ty.clone()),
                            PointFun::of(&s, ta.clone(), tb.clone()),
                        ),
                        Formula::and(Formula::eq(tx, ta), Formula::eq(ty, tb)),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*pf.pairs.concl(), want);
}

#[test]
fn a_one_point_graph_is_single_valued() {
    let mut env = Env::new();
    let (s, pf) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(pf.sv.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let g = PointFun::of(&s, ta, tb);
    let want = Formula::forall(
        a,
        Formula::forall(b, derived::funspace::is_single_valued(&mut env, &s.ap.sets, &g)),
    );
    assert_eq!(*pf.sv.concl(), want);
}

/// The non-vacuity check: the graph *computes*, and its two sides differ.
#[test]
fn the_one_point_graph_computes() {
    let mut env = Env::new();
    let (s, pf) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(pf.app.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let g = PointFun::of(&s, ta.clone(), tb.clone());
    let lhs = s.ap.apply(g, ta);
    assert_ne!(lhs, tb, "app({{⟨a,b⟩}},a) and b must be different terms");
    let want = Formula::forall(a, Formula::forall(b, Formula::eq(lhs, tb)));
    assert_eq!(*pf.app.concl(), want);
}

#[test]
fn a_one_point_graph_is_a_function_on_a_singleton() {
    let mut env = Env::new();
    let (s, pf) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(pf.in_fs.concl()));

    let (a, b, t) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt) = (Term::var(a), Term::var(b), Term::var(t));
    let g = PointFun::of(&s, ta.clone(), tb.clone());
    let dom = derived::singleton(s.ap.sets.up, ta);
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                t,
                Formula::imp(
                    Formula::mem(tb, tt.clone()),
                    Formula::mem(g, s.fs.of(dom, tt)),
                ),
            ),
        ),
    );
    assert_eq!(*pf.in_fs.concl(), want);
}
