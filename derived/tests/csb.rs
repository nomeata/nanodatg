//! Cantor–Schröder–Bernstein: the fixed point, the bijection, and the two
//! instances.

use kernel::{Env, Formula, Term};

use derived::csb;

/// The Knaster–Tarski fixed point exists, and its statement is the one
/// [`csb::fixed`] builds — at variables of the *caller's* choosing, which is
/// what lets [`csb::bijection`] consume it.
#[test]
fn fixpoint_exists_and_has_the_stated_shape() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);

    let (a, b, f, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tg) = (Term::var(a), Term::var(b), Term::var(f), Term::var(g));
    let (xv, bv) = (env.fresh_var(), env.fresh_var());
    let (tx, tbv) = (Term::var(xv), Term::var(bv));

    let fr = kernel::thm::pair_in(&mut env, tf, tx.clone(), tbv.clone());
    let gr = kernel::thm::pair_in(&mut env, tg, tbv, tx);

    let thm = csb::csb_fixpoint(&mut env, &empty_ax, &fr, &gr, xv, bv, &ta, &tb)
        .expect("Knaster-Tarski");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert!(thm.hyps().is_empty(), "the fixed point is unconditional");

    // Rebuilt with fresh working variables: the conclusion must not depend on
    // which ones the derivation happened to mint.
    let cset = env.fresh_var();
    let (dv, wv) = (env.fresh_var(), env.fresh_var());
    let want = csb::fixed(&fr, &gr, xv, bv, dv, wv, &Term::var(cset), &ta, &tb).expect("shape");
    assert_eq!(*thm.concl(), Formula::exists(cset, want), "the fixed point has the wrong shape");
}

/// Monotonicity is what Knaster–Tarski runs on, and it holds of *any* two
/// relations — the theorem below has no hypothesis on `F` or `G` at all.
#[test]
fn the_operator_is_monotone_unconditionally() {
    let mut env = Env::new();
    let (a, b, s, t) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, ts, tt) = (Term::var(a), Term::var(b), Term::var(s), Term::var(t));
    let (xv, bv) = (env.fresh_var(), env.fresh_var());

    // Two relations with nothing whatever assumed about them, and not even set
    // relations: `F(x,y) := x ∈ y` and `G(y,x) := y = x`.
    let fr = Formula::mem(Term::var(xv), Term::var(bv));
    let gr = Formula::eq(Term::var(bv), Term::var(xv));

    let (dv, wv) = (env.fresh_var(), env.fresh_var());
    let mono = csb::step_monotone(&mut env, &fr, &gr, xv, bv, dv, wv, &ts, &tt, &ta, &tb)
        .expect("monotone");
    assert!(mono.hyps().is_empty());

    let sub = kernel::thm::subset(&mut env, ts.clone(), tt.clone());
    let want = Formula::imp(
        sub,
        Formula::imp(
            csb::step(&fr, &gr, xv, bv, dv, wv, &ts, &ta, &tb).expect("Φ(s)"),
            csb::step(&fr, &gr, xv, bv, dv, wv, &tt, &ta, &tb).expect("Φ(t)"),
        ),
    );
    assert_eq!(*mono.concl(), want, "monotonicity has the wrong shape");
}

/// The scheme itself, at two set relations: it produces a theorem, that theorem
/// is unconditional apart from the eight clauses, and its conclusion is
/// `kernel::thm::equinumerous` on the nose.
#[test]
fn the_scheme_produces_a_bijection() {
    let mut env = Env::new();
    let s = csb::Csb::new(&mut env).expect("prerequisites");

    let (a, b, f, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tg) = (Term::var(a), Term::var(b), Term::var(f), Term::var(g));
    let (xv, bv) = (env.fresh_var(), env.fresh_var());
    let (tx, tbv) = (Term::var(xv), Term::var(bv));

    let fr = kernel::thm::pair_in(&mut env, tf, tx.clone(), tbv.clone());
    let gr = kernel::thm::pair_in(&mut env, tg, tbv, tx);

    let thm = csb::csb_scheme(&mut env, &s, &fr, &gr, xv, bv, &ta, &tb).expect("CSB scheme");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert!(thm.hyps().is_empty(), "the scheme is unconditional");

    let atoms = csb::csb_clauses(&mut env, &fr, &gr, xv, bv, &ta, &tb).expect("clauses");
    let want = Formula::imp(
        derived::conj_of(&atoms).expect("hypothesis"),
        kernel::thm::equinumerous(&mut env, ta, tb),
    );
    assert_eq!(*thm.concl(), want, "the scheme has the wrong shape");
}

/// The set-graph form, and the check that its two halves are the
/// [`csb::injection`] a caller would build for itself.
#[test]
fn two_injections_make_a_bijection() {
    let mut env = Env::new();
    let s = csb::Csb::new(&mut env).expect("prerequisites");
    let thm = csb::schroeder_bernstein(&mut env, &s).expect("CSB");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert!(thm.hyps().is_empty(), "CSB is unconditional");

    let (a, b, f, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tg) = (Term::var(a), Term::var(b), Term::var(f), Term::var(g));
    let want = Formula::imp(
        Formula::and(
            csb::injection(&mut env, &tf, &ta, &tb).expect("f injects"),
            csb::injection(&mut env, &tg, &tb, &ta).expect("g injects"),
        ),
        kernel::thm::equinumerous(&mut env, ta, tb),
    );
    let mut cur = thm.clone();
    for v in [a, b, f, g] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want, "CSB has the wrong shape");
}

/// The sandwich — the form `crate::universe::inaccessibility` needs.
#[test]
fn a_sandwiched_set_is_equinumerous_with_the_filling() {
    let mut env = Env::new();
    let s = csb::Csb::new(&mut env).expect("prerequisites");
    let thm = csb::equinumerous_sandwich(&mut env, &s).expect("sandwich");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert!(thm.hyps().is_empty(), "the sandwich is unconditional");

    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc) = (Term::var(a), Term::var(b), Term::var(c));
    let want = Formula::imp(
        Formula::and(
            Formula::and(
                kernel::thm::subset(&mut env, ta.clone(), tb.clone()),
                kernel::thm::subset(&mut env, tb.clone(), tc.clone()),
            ),
            kernel::thm::equinumerous(&mut env, ta.clone(), tc),
        ),
        kernel::thm::equinumerous(&mut env, ta, tb),
    );
    let mut cur = thm.clone();
    for v in [a, b, c] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want, "the sandwich has the wrong shape");
}

/// **The measurable**: `is_universe(U(x))`. It was open for exactly one clause,
/// and Cantor–Schröder–Bernstein is that clause.
#[test]
fn the_least_universe_is_a_universe() {
    use derived::universe as uni;
    let mut env = Env::new();
    let s = csb::Csb::new(&mut env).expect("prerequisites");
    let (pow, pow_ax) = derived::power(&mut env);
    let (lu, lu_ax) = uni::least_universe(&mut env).expect("define U");

    let c4 = uni::least_universe_inaccessible(&mut env, &s, lu, &lu_ax).expect("C₄ for U(x)");
    assert!(c4.hyps().is_empty(), "C₄ is unconditional");

    let thm = uni::least_universe_is_universe(&mut env, &s, lu, &lu_ax, pow, &pow_ax)
        .expect("is_universe(U(x))");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));
    assert!(thm.hyps().is_empty(), "nothing is assumed");

    let x = env.fresh_var();
    let w = Term::apply(lu, vec![Term::var(x)]);
    let reopened = derived::inst_self(x, &thm).expect("reopen");
    assert_eq!(
        *reopened.concl(),
        uni::is_universe(&mut env, &w),
        "is_universe(U(x)) has the wrong shape"
    );

    // And the two facts that were waiting on it: the tower is a tower of
    // universes, and `U(x)` is now a legitimate witness for Tarski's axiom.
    let mem_u = uni::mem_least_universe(&mut env, lu, &lu_ax).expect("x ∈ U(x)");
    let step = uni::tower_step(&mut env, lu, &mem_u).expect("U(x) ∈ U(U(x))");
    assert!(step.hyps().is_empty());
}
