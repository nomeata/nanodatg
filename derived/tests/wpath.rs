//! **The path code of a W-type**, checked at the terms.
//!
//! Every theorem in [`derived::wpath`] is asserted to *derive*, to rest on
//! nothing, and to have the conclusion its header advertises — the conclusions
//! are rebuilt here from the exported formula builders rather than read off the
//! theorems, so a change to either side is a failure rather than a silent drift.

use kernel::{Env, Formula, Term};

use derived::wpath::{
    path_arises, path_closed, paths_induction, paths_intro, paths_inversion, paths_subset,
    paths_symbol, At,
};
use derived::wtype::Wtype;

/// The whole chain, over one apparatus.
#[test]
fn the_path_relation_and_its_three_rules_derive() {
    let mut env = Env::new();
    let wt = Wtype::new(&mut env).expect("the W-type apparatus");

    let (paths, paths_ax) = paths_symbol(&mut env, &wt).expect("one Separation");
    assert!(paths_ax.hyps().is_empty(), "the defining biconditional rests on nothing");

    let sub = paths_subset(&mut env, &wt, paths, &paths_ax).expect("paths ⊆ Bnd");
    assert!(sub.hyps().is_empty());

    let ind = paths_induction(&mut env, &wt, paths, &paths_ax).expect("P2");
    assert!(ind.hyps().is_empty());

    let intro = paths_intro(&mut env, &wt, paths, &paths_ax, &ind, &sub).expect("P1");
    assert!(intro.hyps().is_empty());

    let inv = paths_inversion(&mut env, &wt, paths, &ind, &sub, &intro).expect("P3");
    assert!(inv.hyps().is_empty());

    let rl = derived::wpath::root_label(&mut env, &wt, paths, &inv).expect("root_label");
    assert!(rl.hyps().is_empty());
    let sp = derived::wpath::step_premise(&mut env, &wt, paths, &inv).expect("step_premise");
    assert!(sp.hyps().is_empty());

    let winv = derived::wtype::w_inversion(&mut env, &wt).expect("W3");
    let inj = derived::wpath::paths_injective(
        &mut env, &wt, paths, &sub, &intro, &winv, &rl, &sp,
    )
    .expect("P4 — the code determines the tree");
    assert!(inj.hyps().is_empty());

    // The conclusion, rebuilt: `∀A∀B∀u∀Q. ((closed ∧ amb) → path_closed(paths))`.
    let (av, bv, uv, qv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(&wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ps = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
    let s = wt.sums.clone();
    let closed = wt.closed_at(&mut env, &at.a, &at.b, &at.u);
    let ambient = derived::wpath::amb(&mut env, &s, &at);
    let want = Formula::forall(
        av,
        Formula::forall(
            bv,
            Formula::forall(
                uv,
                Formula::forall(
                    qv,
                    Formula::imp(
                        Formula::and(closed, ambient),
                        path_closed(&mut env, &s, &at, &ps),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*intro.concl(), want, "P1's conclusion is the one the header states");

    // And P3's, at the same terms.
    let pv = env.fresh_var();
    let tp = Term::var(pv);
    let closed2 = wt.closed_at(&mut env, &at.a, &at.b, &at.u);
    let ambient2 = derived::wpath::amb(&mut env, &s, &at);
    let want_inv = Formula::forall(
        av,
        Formula::forall(
            bv,
            Formula::forall(
                uv,
                Formula::forall(
                    qv,
                    Formula::imp(
                        Formula::and(closed2, ambient2),
                        Formula::forall(
                            pv,
                            Formula::imp(
                                Formula::mem(tp.clone(), ps.clone()),
                                path_arises(&mut env, &s, &at, &ps, &tp),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*inv.concl(), want_inv, "P3's conclusion is the one the header states");
}
