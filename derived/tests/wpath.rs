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

    // ── the theorem ────────────────────────────────────────────────────────
    let tower = derived::tower::Tower::new(&mut env).expect("the tower");
    let wt2 = derived::wtype::Wtype::over(&mut env, tower.sums.clone()).expect("W over the tower");
    let (p2, p2_ax) = paths_symbol(&mut env, &wt2).expect("paths, over the tower's apparatus");
    let sub2 = paths_subset(&mut env, &wt2, p2, &p2_ax).expect("paths ⊆ Bnd");
    let ind2 = paths_induction(&mut env, &wt2, p2, &p2_ax).expect("P2");
    let intro2 = paths_intro(&mut env, &wt2, p2, &p2_ax, &ind2, &sub2).expect("P1");
    let inv2 = paths_inversion(&mut env, &wt2, p2, &ind2, &sub2, &intro2).expect("P3");
    let rl2 = derived::wpath::root_label(&mut env, &wt2, p2, &inv2).expect("root_label");
    let sp2 = derived::wpath::step_premise(&mut env, &wt2, p2, &inv2).expect("step_premise");
    let winv2 = derived::wtype::w_inversion(&mut env, &wt2).expect("W3");
    let inj2 = derived::wpath::paths_injective(
        &mut env, &wt2, p2, &sub2, &intro2, &winv2, &rl2, &sp2,
    )
    .expect("P4");
    let csb = derived::csb::Csb::new(&mut env).expect("CSB");
    let is_u = derived::universe::least_universe_is_universe(
        &mut env,
        &csb,
        tower.space.lu,
        &tower.space.lu_ax,
        tower.space.pow,
        &tower.space.pow_ax,
    )
    .expect("is_universe(U(x))");
    let thm = derived::wpath::w_in_universe_paths(
        &mut env,
        &wt2,
        p2,
        &sub2,
        &inj2,
        tower.space.lu,
        &is_u,
        &tower.product,
        &tower.pow,
    )
    .expect("W(A,B,u) ∈ U(d) — at an arbitrary fibre family");
    assert!(thm.hyps().is_empty(), "the theorem rests on nothing");

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

/// **The tower is a legal path ambient** — and it is discharged from the *cheap*
/// half of `Fin⁺`, the clause that survives when `bnd` goes.
///
/// This is the non-vacuity check that matters: `w_in_universe_paths`' antecedent
/// contains one genuinely new clause, [`derived::wpath::amb`], and without a
/// witness a reader cannot tell whether it is satisfiable at the `Q` a consumer
/// would actually supply. It is, at `Q := tower(S)`, from
/// `∀a ∈ A. B(a) ⊆ S` alone.
#[test]
fn the_tower_satisfies_the_path_ambient_at_any_fibre() {
    let mut env = Env::new();
    let chain = derived::cumul::Chain::new(&mut env).expect("the chain");
    let thm = derived::cumul::tower_amb(&mut env, &chain).expect("amb(A,B,T)");
    assert!(thm.hyps().is_empty(), "rests on nothing");

    // The conclusion, rebuilt: `∀A ∀B. ((∀a ∈ A. B(a) ⊆ S) → amb(A,B,T))`.
    let s = chain.wt.sums.clone();
    let (av, bv, uv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(
        &chain.wt,
        Term::var(av),
        Term::var(bv),
        Term::var(uv),
        chain.st.tower_set(),
    );
    let a1 = env.fresh_var();
    let hyp = Formula::forall(
        a1,
        Formula::imp(
            Formula::mem(Term::var(a1), at.a.clone()),
            kernel::thm::subset(
                &mut env,
                s.ap.apply(at.b.clone(), Term::var(a1)),
                Term::var(chain.st.seed),
            ),
        ),
    );
    let want = Formula::forall(
        av,
        Formula::forall(
            bv,
            Formula::imp(hyp, derived::wpath::amb(&mut env, &s, &at)),
        ),
    );
    assert_eq!(*thm.concl(), want, "the bridge states what its header says");

    // **And the chain carries it**, at the same statement — the standing
    // `tower_amb` entry point and [`derived::cumul::Paths`]' field are one
    // derivation over one `Chain::assemble`, not two that happen to agree.
    assert_eq!(
        *chain.paths.tower_amb.concl(),
        *thm.concl(),
        "`Chain::paths.tower_amb` is the same theorem the free function returns"
    );
}

/// **The chain mints `paths` once and carries the theorem** — the assembly
/// [`derived::cumul::Paths`] exists for.
///
/// The conclusion is rebuilt here from the exported formula builders at the
/// chain's own `W` and `U(·)`, so a `Paths` accidentally built over a second
/// apparatus is a failure rather than a theorem about somebody else's W-type.
///
/// This is the *consumer-side* half of the wpath landing: without it the
/// derivation is reachable only by a caller who mints its own `paths`, which is
/// the shape SCOPING.md §14.6 step 1 names.
#[test]
fn the_chain_carries_the_path_route_at_its_own_terms() {
    let mut env = Env::new();
    let chain = derived::cumul::Chain::new(&mut env).expect("the chain");
    let p = &chain.paths;
    assert!(p.w_in_universe.hyps().is_empty(), "the theorem rests on nothing");
    assert!(p.tower_amb.hyps().is_empty());
    assert!(p.is_universe.hyps().is_empty());

    let s = chain.wt.sums.clone();
    let lu = chain.lu();
    let (av, bv, uv, qv, dv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let at = At::new(&chain.wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ud = Term::apply(lu, vec![Term::var(dv)]);
    let closed = chain.wt.closed_at(&mut env, &at.a, &at.b, &at.u);
    let ambient = derived::wpath::amb(&mut env, &s, &at);
    let sub_w = kernel::thm::subset(&mut env, at.w.clone(), ud.clone());
    let want = Formula::imp(
        Formula::and(
            Formula::and(closed, ambient),
            Formula::and(
                Formula::and(sub_w, Formula::mem(at.q.clone(), ud.clone())),
                Formula::mem(at.a.clone(), ud.clone()),
            ),
        ),
        Formula::mem(at.w.clone(), ud),
    );
    let want = [dv, qv, uv, bv, av].iter().fold(want, |f, v| Formula::forall(*v, f));
    assert_eq!(
        *p.w_in_universe.concl(),
        want,
        "the chain's own `w_in_universe_paths`, over the chain's own `W` and `U(·)`"
    );

    // The symbol is this chain's, and there is exactly one of it: the two
    // theorems that mention `paths` mention the *same* application.
    let ps = Term::apply(p.sym, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
    assert_eq!(
        *p.subset.concl(),
        {
            let pv = env.fresh_var();
            let tp = Term::var(pv);
            let bnd = s.prod.of(at.w.clone(), s.prod.of(at.q.clone(), at.a.clone()));
            let body = Formula::forall(
                pv,
                Formula::imp(Formula::mem(tp.clone(), ps.clone()), Formula::mem(tp, bnd)),
            );
            [qv, uv, bv, av].iter().fold(body, |f, v| Formula::forall(*v, f))
        },
        "`paths ⊆ prod(W, prod(Q,A))` at the chain's own symbol"
    );
}
