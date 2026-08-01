//! `π₁` and `π₂` as term-formers, and their two computation rules.
//!
//! **Non-vacuity.** Both rules are equations at fresh variables whose two sides
//! are different terms, and the pair of them is checked *together*: `π₁` and
//! `π₂` of the **same** pair give its two **different** components, so no
//! constant operation satisfies the interface. The η rule is then checked to be
//! about the same pair rather than about a reassembled one.

use kernel::{Env, Formula, Term};

use derived::funcs::Apply;
use derived::point_fun::PointFun;
use derived::proj::Proj;
use derived::wtype::Wtype;

struct Fix {
    ap: Apply,
    pj: Proj,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let ap = wt.sums.ap.clone();
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("one-point graph");
    let pj = Proj::new(env, &ap, &pf).expect("projections");
    Fix { ap, pj }
}

#[test]
fn the_first_projection_computes() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.pj.fst.concl()));

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (a, b) = (Term::var(av), Term::var(bv));
    let pair = f.ap.sets.pair(a.clone(), b.clone());
    let lhs = f.pj.fst_of(&f.ap, pair);
    assert_ne!(lhs, a, "fst would be reflexivity");
    let want = Formula::forall(av, Formula::forall(bv, Formula::eq(lhs, a)));
    assert_eq!(*f.pj.fst.concl(), want);
}

#[test]
fn the_second_projection_computes() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.pj.snd.concl()));

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (a, b) = (Term::var(av), Term::var(bv));
    let pair = f.ap.sets.pair(a.clone(), b.clone());
    let lhs = f.pj.snd_of(&f.ap, pair);
    assert_ne!(lhs, b, "snd would be reflexivity");
    let want = Formula::forall(av, Formula::forall(bv, Formula::eq(lhs, b)));
    assert_eq!(*f.pj.snd.concl(), want);
}

/// The two projections applied to the *same* pair give its two *different*
/// components — which no constant operation could do.
#[test]
fn the_projections_are_different_operations() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (a, b) = (Term::var(av), Term::var(bv));
    let pair = f.ap.sets.pair(a.clone(), b.clone());
    let (l, r) = (f.pj.fst_of(&f.ap, pair.clone()), f.pj.snd_of(&f.ap, pair));
    assert_ne!(l, r);
    assert_ne!(a, b);

    let at_fst = derived::inst_all(&f.pj.fst, &[a.clone(), b.clone()]).expect("fst");
    let at_snd = derived::inst_all(&f.pj.snd, &[a.clone(), b.clone()]).expect("snd");
    assert_eq!(*at_fst.concl(), Formula::eq(l, a));
    assert_eq!(*at_snd.concl(), Formula::eq(r, b));
}

/// `⟨π₁ p, π₂ p⟩ = p` — the thesis's η rule, at a pair.
#[test]
fn the_eta_rule_reassembles_the_pair() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.pj.eta.concl()));

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (a, b) = (Term::var(av), Term::var(bv));
    let pair = f.ap.sets.pair(a, b);
    let lhs = f.ap.sets.pair(
        f.pj.fst_of(&f.ap, pair.clone()),
        f.pj.snd_of(&f.ap, pair.clone()),
    );
    assert_ne!(lhs, pair, "eta would be reflexivity");
    let want = Formula::forall(av, Formula::forall(bv, Formula::eq(lhs, pair)));
    assert_eq!(*f.pj.eta.concl(), want);
}

/// `⋂⟨a,b⟩ = {a}`, the one Extensionality the first projection rests on.
#[test]
fn the_intersection_of_a_pair_is_the_first_singleton() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (a, b) = (Term::var(av), Term::var(bv));
    let pair = f.ap.sets.pair(a.clone(), b);
    let want = Formula::forall(
        av,
        Formula::forall(
            bv,
            Formula::eq(
                f.pj.inter_of(pair),
                derived::singleton(f.ap.sets.up, a),
            ),
        ),
    );
    assert_eq!(*f.pj.inter_pair.concl(), want);
}
