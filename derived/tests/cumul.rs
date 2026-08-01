//! The cumulative hierarchy over a seed, checked step by step.
//!
//! Every test pins the **exact** conclusion of the lemma it covers, rebuilt
//! independently from the kernel's formula constructors.

use derived::cumul::{mem_bin_union_elim, subset_trans, Step};
use derived::funcs::Sets;
use derived::funspace::bin_union;
use kernel::{Env, Formula, Term};

fn base(env: &mut Env) -> (Sets, kernel::FnSym, kernel::Thm) {
    let sets = Sets::new(env);
    let (pow, pow_ax) = derived::power(env);
    (sets, pow, pow_ax)
}

/// `⊢ ∀a ∀b ∀c. ((a ⊆ b ∧ b ⊆ c) → a ⊆ c)`.
#[test]
fn inclusion_is_transitive() {
    let mut env = Env::new();
    let thm = subset_trans(&mut env).expect("subset_trans");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc) = (Term::var(a), Term::var(b), Term::var(c));
    let ab = kernel::thm::subset(&mut env, ta.clone(), tb.clone());
    let bc = kernel::thm::subset(&mut env, tb, tc.clone());
    let ac = kernel::thm::subset(&mut env, ta, tc);
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(c, Formula::imp(Formula::and(ab, bc), ac)),
        ),
    );
    assert_eq!(*thm.concl(), expected, "subset_trans has the wrong shape");
}

/// `⊢ ∀a ∀b ∀z. (z ∈ a ∪ b → (z ∈ a ∨ z ∈ b))` — the elimination half of the
/// binary union, which `crate::funspace::pow_pow` proves only in the two
/// introduction directions.
#[test]
fn a_member_of_a_binary_union_is_a_member_of_one_side() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let thm = mem_bin_union_elim(&mut env, &sets).expect("mem_bin_union_elim");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), bin_union(&sets, ta.clone(), tb.clone())),
                    Formula::or(Formula::mem(tz.clone(), ta), Formula::mem(tz, tb)),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "mem_bin_union_elim has the wrong shape");
}

/// The step operator `G(x) = x ∪ 𝒫x`, its defining equation and its four
/// membership rules, each at its exact statement.
#[test]
fn the_step_operator_and_its_rules() {
    let mut env = Env::new();
    let (sets, pow, pow_ax) = base(&mut env);
    let step = Step::new(&mut env, &sets, pow, &pow_ax).expect("Step");
    for t in [&step.g_ax, &step.mem, &step.sub, &step.elim, &step.mono] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
    assert_eq!(step.g.arity(), 1);

    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
    let powx = Term::apply(pow, vec![tx.clone()]);
    let gx = step.of(tx.clone());
    let gy = step.of(ty.clone());

    // `⊢ ∀x. G(x) = x ∪ 𝒫x`, and `G(x)` really is a new symbol.
    assert_eq!(
        *step.g_ax.concl(),
        Formula::forall(x, Formula::eq(gx.clone(), bin_union(&sets, tx.clone(), powx))),
        "the defining equation has the wrong shape"
    );
    assert_ne!(gx, tx, "G(x) must not be the term x");

    let mem_zx = Formula::mem(tz.clone(), tx.clone());
    let mem_zgx = Formula::mem(tz.clone(), gx.clone());
    let sub_zx = kernel::thm::subset(&mut env, tz.clone(), tx.clone());

    assert_eq!(
        *step.mem.concl(),
        Formula::forall(x, Formula::forall(z, Formula::imp(mem_zx.clone(), mem_zgx.clone()))),
        "G's membership rule has the wrong shape"
    );
    assert_eq!(
        *step.sub.concl(),
        Formula::forall(x, Formula::forall(z, Formula::imp(sub_zx.clone(), mem_zgx.clone()))),
        "G's subset rule has the wrong shape"
    );
    assert_eq!(
        *step.elim.concl(),
        Formula::forall(
            x,
            Formula::forall(z, Formula::imp(mem_zgx, Formula::or(mem_zx, sub_zx)))
        ),
        "G's elimination rule has the wrong shape"
    );
    assert_eq!(
        *step.mono.concl(),
        Formula::forall(
            x,
            Formula::forall(
                y,
                Formula::imp(
                    kernel::thm::subset(&mut env, tx, ty),
                    kernel::thm::subset(&mut env, gx, gy),
                )
            )
        ),
        "G's monotonicity has the wrong shape"
    );
}

/// The stages themselves: the two recursion equations, the tower's membership
/// condition, and the three inclusion facts, each at its exact statement.
#[test]
fn the_stages_increase_and_are_directed() {
    let mut env = Env::new();
    let r = derived::recursion::Rec::new(&mut env).expect("Rec");
    let (pow, pow_ax) = derived::power(&mut env);
    let step = Step::new(&mut env, &r.ap.sets, pow, &pow_ax).expect("Step");
    let st = derived::cumul::Stages::new(&mut env, &r, step).expect("Stages");
    for t in [&st.incr, &st.zero_least, &st.directed, &st.rec.base, &st.rec.step] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    let s = Term::var(st.seed);
    let v = |t: Term| st.v(&r, t);
    let om = r.omega();

    // `⊢ V₀ = S` — the base of the recursion really is the seed.
    assert_eq!(*st.rec.base.concl(), Formula::eq(v(r.zero()), s));

    // `⊢ ∀n. (n ∈ ω → Vₙ ⊆ V₍succ n₎)`.
    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(
        *st.incr.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), om.clone()),
                kernel::thm::subset(&mut env, v(tn.clone()), v(r.succ_of(tn.clone()))),
            )
        ),
        "the chain does not increase in the shape claimed"
    );

    // `⊢ ∀m. (m ∈ ω → V₀ ⊆ Vₘ)`.
    let m = env.fresh_var();
    let tm = Term::var(m);
    assert_eq!(
        *st.zero_least.concl(),
        Formula::forall(
            m,
            Formula::imp(
                Formula::mem(tm.clone(), om.clone()),
                kernel::thm::subset(&mut env, v(r.zero()), v(tm.clone())),
            )
        ),
        "zero_least has the wrong shape"
    );

    // `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ ω → ∃p. (p ∈ ω ∧ (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ))))`.
    let p = env.fresh_var();
    let tp = Term::var(p);
    let inner = Formula::and(
        Formula::mem(tp.clone(), om.clone()),
        Formula::and(
            kernel::thm::subset(&mut env, v(tn.clone()), v(tp.clone())),
            kernel::thm::subset(&mut env, v(tm.clone()), v(tp)),
        ),
    );
    assert_eq!(
        *st.directed.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn, om.clone()),
                Formula::forall(
                    m,
                    Formula::imp(Formula::mem(tm, om), Formula::exists(p, inner))
                )
            )
        ),
        "directedness has the wrong shape"
    );
}

/// `⊢ ∀k. (k ∈ ω → bnd(k))` — a function out of a natural number lands in a
/// single stage. The finite-branching hypothesis, at its exact statement.
#[test]
fn a_function_out_of_a_natural_lands_in_one_stage() {
    let mut env = Env::new();
    let r = derived::recursion::Rec::new(&mut env).expect("Rec");
    let (pow, pow_ax) = derived::power(&mut env);
    let step = Step::new(&mut env, &r.ap.sets, pow, &pow_ax).expect("Step");
    let st = derived::cumul::Stages::new(&mut env, &r, step).expect("Stages");
    let thm = derived::cumul::bounded(&mut env, &r, &st).expect("bounded");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (k, g, b, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let tk = Term::var(k);
    let expected = Formula::forall(
        k,
        Formula::imp(
            Formula::mem(tk.clone(), r.omega()),
            derived::cumul::bounded_at(&mut env, &r, &st, &tk, g, b, p),
        ),
    );
    assert_eq!(*thm.concl(), expected, "bounded has the wrong shape");

    // Non-vacuity: the hypothesis and the conclusion are not the same formula —
    // `T` and `Vₚ` are different terms, so this is not reflexivity in disguise.
    let tp = Term::var(p);
    assert_ne!(st.tower_set(), st.v(&r, tp), "the tower and a stage must differ");
}

/// The three stage-arithmetic lemmas the `sup` closure is assembled from.
#[test]
fn stage_arithmetic() {
    let mut env = Env::new();
    let r = derived::recursion::Rec::new(&mut env).expect("Rec");
    let (pow, pow_ax) = derived::power(&mut env);
    let step = Step::new(&mut env, &r.ap.sets, pow, &pow_ax).expect("Step");
    let st = derived::cumul::Stages::new(&mut env, &r, step).expect("Stages");

    let mem_tower = derived::cumul::mem_tower(&mut env, &r, &st).expect("mem_tower");
    let sub_in = derived::cumul::sub_in_stage(&mut env, &r, &st).expect("sub_in_stage");
    let pair_in =
        derived::cumul::pair_in_stage(&mut env, &r, &st, &sub_in).expect("pair_in_stage");
    for t in [&mem_tower, &sub_in, &pair_in] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    let (p, z, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tz, tx, ty) = (Term::var(p), Term::var(z), Term::var(x), Term::var(y));
    let om = r.omega();
    let vp = st.v(&r, tp.clone());
    let vsp = st.v(&r, r.succ_of(tp.clone()));
    let vssp = st.v(&r, r.succ_of(r.succ_of(tp.clone())));
    let p_om = Formula::mem(tp.clone(), om);

    assert_eq!(
        *mem_tower.concl(),
        Formula::forall(
            p,
            Formula::imp(
                p_om.clone(),
                Formula::forall(
                    z,
                    Formula::imp(
                        Formula::mem(tz.clone(), vp.clone()),
                        Formula::mem(tz.clone(), st.tower_set()),
                    )
                )
            )
        ),
        "mem_tower has the wrong shape"
    );
    assert_eq!(
        *sub_in.concl(),
        Formula::forall(
            p,
            Formula::imp(
                p_om.clone(),
                Formula::forall(
                    z,
                    Formula::imp(
                        kernel::thm::subset(&mut env, tz.clone(), vp.clone()),
                        Formula::mem(tz, vsp),
                    )
                )
            )
        ),
        "sub_in_stage has the wrong shape"
    );
    assert_eq!(
        *pair_in.concl(),
        Formula::forall(
            p,
            Formula::imp(
                p_om,
                Formula::forall(
                    x,
                    Formula::forall(
                        y,
                        Formula::imp(
                            Formula::and(
                                Formula::mem(tx.clone(), vp.clone()),
                                Formula::mem(ty.clone(), vp),
                            ),
                            Formula::mem(derived::opair(r.ap.sets.up, tx, ty), vssp),
                        )
                    )
                )
            )
        ),
        "pair_in_stage has the wrong shape"
    );
}

/// The whole apparatus over **one** chain of definitional extensions: the
/// tower's power set and binary union closure, the recursion's `ω`, and the
/// cumulative hierarchy built from both. Then
/// `⊢ ∀c ∀n. (n ∈ ω → (S ∈ U(c) → Vₙ ∈ U(c)))`.
#[test]
fn the_stages_stay_inside_any_universe_holding_the_seed() {
    let mut env = Env::new();
    let t = derived::tower::Tower::new(&mut env).expect("Tower");

    // Everything the universe half needs, cloned off the tower before its
    // `Peano` is moved into the `Rec`.
    let (lu, pow) = (t.space.lu, t.space.pow);
    let (pow_ax, pow_all, bu_all) = (t.space.pow_ax.clone(), t.pow.clone(), t.bin_union.clone());
    let ap = t.sums.ap.clone();
    let derived::tower::Tower { peano, .. } = t;
    let app_of_graph = derived::recursion::app_of_graph(&mut env, &ap).expect("app_of_graph");
    let r = derived::recursion::Rec { ap, peano, app_of_graph };

    let step = Step::new(&mut env, &r.ap.sets, pow, &pow_ax).expect("Step");
    let st = derived::cumul::Stages::new(&mut env, &r, step).expect("Stages");
    let thm = derived::cumul::stages_in_universe(&mut env, &r, &st, lu, pow, &pow_all, &bu_all)
        .expect("stages_in_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (c, n) = (env.fresh_var(), env.fresh_var());
    let (tc, tn) = (Term::var(c), Term::var(n));
    let u = Term::apply(lu, vec![tc]);
    let s = Term::var(st.seed);
    let expected = Formula::forall(
        c,
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), r.omega()),
                Formula::imp(
                    Formula::mem(s, u.clone()),
                    Formula::mem(st.v(&r, tn), u),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "stages_in_universe has the wrong shape");
}

/// **Step (b)** — `⊢ closed(A,B,T)` under `A ⊆ S` and `∀a ∈ A. (B(a) ⊆ S ∧ B(a) ∈ ω)`.
///
/// Built over [`derived::cumul::Chain`], i.e. over the *one* chain of
/// definitional extensions that carries the universe tower and the cumulative
/// hierarchy at once; `Chain::new` returning `Some` is itself the check that
/// every symbol downstream is the same symbol.
#[test]
fn the_tower_is_closed_under_sup() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    assert!(kernel::thm::debug_locally_closed(c.tower_closed.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let seed = Term::var(c.st.seed);
    let tower = c.st.tower_set();
    let om = c.r.omega();

    let x = env.fresh_var();
    let tx = Term::var(x);
    let fibre = c.r.apply(tb.clone(), tx.clone());
    let hyp = Formula::and(
        kernel::thm::subset(&mut env, ta.clone(), seed.clone()),
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), ta.clone()),
                Formula::and(
                    kernel::thm::subset(&mut env, fibre.clone(), seed),
                    Formula::mem(fibre, om),
                ),
            ),
        ),
    );
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::imp(hyp, derived::wtype::closed(&mut env, &c.wt.sums, &ta, &tb, &tower)),
        ),
    );
    assert_eq!(*c.tower_closed.concl(), expected, "tower_closed has the wrong shape");

    // Non-vacuity: `closed(A,B,T)` really mentions the tower, not the bound.
    assert_ne!(tower, Term::apply(c.lu(), vec![ta]), "the tower must not be a universe term");
}

/// **Steps (c) and (e)** — the tower is a *subset* of any universe holding the
/// seed, and a *member* of any universe that also holds `ω`.
#[test]
fn the_tower_sits_inside_a_universe() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    let inside = &c.inside;
    for t in [&inside.graph_pair, &inside.tower_subset, &inside.iter_in_fs, &inside.tower_mem] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    let (cv, n) = (env.fresh_var(), env.fresh_var());
    let (tc, tn) = (Term::var(cv), Term::var(n));
    let u = Term::apply(c.lu(), vec![tc]);
    let seed = Term::var(c.st.seed);
    let tower = c.st.tower_set();
    let om = c.r.omega();
    let iter = c.st.rec.set();
    let s_in = Formula::mem(seed, u.clone());

    // `⊢ ∀n. (n ∈ ω → ⟨n, Vₙ⟩ ∈ iter(S))`.
    assert_eq!(
        *inside.graph_pair.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), om.clone()),
                Formula::mem(c.r.pair(tn.clone(), c.st.v(&c.r, tn)), iter.clone()),
            )
        ),
        "graph_pair has the wrong shape"
    );

    // `⊢ ∀c. (S ∈ U(c) → T ⊆ U(c))` — step (c).
    assert_eq!(
        *inside.tower_subset.concl(),
        Formula::forall(
            cv,
            Formula::imp(s_in.clone(), kernel::thm::subset(&mut env, tower.clone(), u.clone()))
        ),
        "tower_subset has the wrong shape"
    );

    // `⊢ ∀c. (S ∈ U(c) → iter(S) ∈ fs(ω, U(c)))`.
    assert_eq!(
        *inside.iter_in_fs.concl(),
        Formula::forall(
            cv,
            Formula::imp(
                s_in.clone(),
                Formula::mem(iter, c.wt.sums.fs.of(om.clone(), u.clone())),
            )
        ),
        "iter_in_fs has the wrong shape"
    );

    // `⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))` — step (e), and the `ω ∈ U(c)`
    // in that antecedent is the whole size content of the argument.
    assert_eq!(
        *inside.tower_mem.concl(),
        Formula::forall(
            cv,
            Formula::imp(
                Formula::and(s_in, Formula::mem(om, u.clone())),
                Formula::mem(tower.clone(), u.clone()),
            )
        ),
        "tower_mem has the wrong shape"
    );

    // Non-vacuity: membership and inclusion are different claims about `T`.
    assert_ne!(
        Formula::mem(tower.clone(), u.clone()),
        kernel::thm::subset(&mut env, tower, u),
        "the two conclusions must not coincide"
    );
}

/// **Steps (d) and (f)** — the W-type is a subset of the tower, and hence a
/// member of any universe that holds the seed and `ω`.
#[test]
fn the_wtype_is_a_member_of_a_universe() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    for t in [&c.wmem.w_sub_tower, &c.wmem.w_in_universe] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    let (a, b, cv, dv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(cv), Term::var(dv));
    let (uc, ud) = (Term::apply(c.lu(), vec![tc]), Term::apply(c.lu(), vec![td]));
    let seed = Term::var(c.st.seed);
    let tower = c.st.tower_set();
    let w = c.wt.of(ta.clone(), tb.clone(), uc.clone());

    // `Fin(A,B)` is exactly `tower_closed`'s antecedent, rebuilt from it.
    let fin = derived::inst_all(&c.tower_closed, &[ta, tb])
        .expect("instantiate tower_closed")
        .concl()
        .as_imp()
        .expect("an implication")
        .0;
    let h1 = Formula::and(fin, Formula::mem(seed.clone(), uc));

    assert_eq!(
        *c.wmem.w_sub_tower.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    cv,
                    Formula::imp(
                        h1.clone(),
                        kernel::thm::subset(&mut env, w.clone(), tower),
                    )
                )
            )
        ),
        "w_sub_tower has the wrong shape"
    );

    let size = Formula::and(
        Formula::mem(seed, ud.clone()),
        Formula::mem(c.r.omega(), ud.clone()),
    );
    assert_eq!(
        *c.wmem.w_in_universe.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    cv,
                    Formula::forall(
                        dv,
                        Formula::imp(Formula::and(h1, size), Formula::mem(w, ud))
                    )
                )
            )
        ),
        "w_in_universe has the wrong shape"
    );
}

/// **Step (g), the deliverable** — `⊢ ⟦N⟧ ∈ U₁` at closed terms, and the
/// witness that says it is not a statement about a one-element set.
#[test]
fn the_naturals_are_a_member_of_the_first_universe() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    let n = derived::cumul::NatUniverse::new(&mut env, &c).expect("NatUniverse");

    for t in [
        &n.one_is_succ_zero,
        &n.one_in_omega,
        &n.tags_in_u1,
        &n.seed_in_bound,
        &n.seed_in_u1,
        &n.fin,
        &n.nat_in_u1,
    ] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
        assert!(t.hyps().is_empty(), "every step must be unconditional");
    }

    let s = &c.wt.sums;
    let (zero, one) = (s.zero(), s.unit());

    // `⊢ 1 = succ 0` — the one Extensionality in the chain.
    assert_eq!(
        *n.one_is_succ_zero.concl(),
        Formula::eq(one.clone(), c.r.succ_of(zero)),
        "one_is_succ_zero has the wrong shape"
    );
    assert_eq!(*n.one_in_omega.concl(), Formula::mem(one, c.r.omega()));

    // **`⊢ ⟦N⟧ ∈ U₁`** — `N = W(1+1, B, U(1+1))` and `U₁ = U(ω)`, both closed.
    let u1 = c.u1.set.clone();
    assert_eq!(u1, Term::apply(c.lu(), vec![c.r.omega()]), "U₁ must be U(ω)");
    assert_eq!(
        *n.nat_in_u1.concl(),
        Formula::mem(n.nat.ty.clone(), u1.clone()),
        "N ∈ U₁ has the wrong shape"
    );
    assert_eq!(
        n.nat.ty,
        c.wt.of(
            n.nat.tags.clone(),
            n.nat.fam.clone(),
            Term::apply(c.lu(), vec![n.nat.tags.clone()])
        ),
        "the set that is a member of U₁ must be W(1+1, B, U(1+1))"
    );

    // Non-vacuity: `N` has two provably distinct elements, so `N ∈ U₁` is not
    // a statement about the empty set or a singleton — and the bound `U(1+1)`
    // is *not* the universe `N` lives in, which is the correction this chain
    // was built around.
    assert!(kernel::thm::debug_locally_closed(n.nat.zero.concl()));
    assert_eq!(*n.nat.zero.concl(), Formula::mem(n.nat.zero_t.clone(), n.nat.ty.clone()));
    let m = env.fresh_var();
    let tm = Term::var(m);
    assert_eq!(
        *n.nat.succ.concl(),
        Formula::forall(
            m,
            Formula::imp(
                Formula::mem(tm.clone(), n.nat.ty.clone()),
                Formula::mem(derived::wnat::Nat::succ_term(&c.wt, tm.clone()), n.nat.ty.clone()),
            )
        )
    );
    assert_eq!(
        *n.nat.zero_ne_succ.concl(),
        Formula::forall(
            m,
            Formula::not(Formula::eq(
                n.nat.zero_t.clone(),
                derived::wnat::Nat::succ_term(&c.wt, tm)
            ))
        )
    );
    assert_ne!(u1, Term::apply(c.lu(), vec![n.nat.tags.clone()]), "the two universes differ");
}

/// **`Chain::over`** — the same chain, over an ambient signature the caller
/// built for itself, and the enumerations in `U₁` on top of it.
///
/// This is what the checker does, rehearsed here at the smallest scale that can
/// fail. The point is not that the theorems exist — `Chain::new` already proves
/// them — but that they come out **at the caller's own symbols**: a `W` minted
/// by a second `Wtype` is a different `W`, and nothing downstream would notice.
/// So the tower, the `Sums`, the `Wtype` and the `Bound` are all assembled here
/// by hand, in the order a client would, and every conclusion is checked
/// against terms rebuilt from *those*.
#[test]
fn the_chain_can_be_built_over_a_callers_own_signature() {
    use derived::bound::Bound;
    use derived::sums::Sums;
    use derived::tower::Tower;
    use derived::wtype::Wtype;

    let mut env = Env::new();
    let tower = Tower::new(&mut env).expect("tower");
    // A *second* `Sums` over the tower's own pairing, power set, product and
    // function space — exactly what a client with its own sum types has, and
    // not the one the tower carries.
    let sums = Sums::over(
        &mut env,
        tower.sums.ap.clone(),
        tower.space.pow,
        tower.space.pow_ax.clone(),
        tower.sums.prod.clone(),
        tower.sums.fs.clone(),
    )
    .expect("caller's Sums");
    let wt = Wtype::over(&mut env, sums).expect("caller's Wtype");
    let bnd = Bound::over(&mut env, &wt, tower.space.lu, tower.space.lu_ax.clone())
        .expect("caller's Bound");

    let c = derived::cumul::Chain::over(&mut env, &tower, &wt, &bnd).expect("Chain::over");
    assert_eq!(c.lu(), tower.space.lu, "the chain must use the caller's U(·)");
    assert_eq!(c.u1.set, tower.level(1), "U₁ must be the tower's own level 1");

    // `N` over the caller's apparatus, and the membership at *that* `N`.
    let cases = derived::sums::Cases::new(&mut env, &wt.sums).expect("cases");
    let pf = derived::point_fun::PointFun::over(&mut env, &wt.sums, &wt.app_pair).expect("pf");
    let empty_u = derived::enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("empty_u");
    let nat = derived::wnat::Nat::over(&mut env, &wt, &bnd, &cases, &pf, &empty_u).expect("Nat");
    let m = derived::cumul::NatMem::over(&mut env, &c, &nat).expect("NatMem::over");
    assert!(m.nat_in_u1.hyps().is_empty(), "N ∈ U₁ must be unconditional");
    assert_eq!(
        *m.nat_in_u1.concl(),
        Formula::mem(nat.ty.clone(), tower.level(1)),
        "the membership must be about the caller's own N"
    );
    assert_eq!(
        nat.ty,
        wt.of(nat.tags.clone(), nat.fam.clone(), Term::apply(tower.space.lu, vec![nat.tags.clone()])),
        "the caller's N must be W(1+1, B, U(1+1)) over the caller's W"
    );

    // The three enumerations, at the same terms `derived::enums` builds.
    let mem = derived::enums::enum_mem(&mut env, &wt, &bnd, &empty_u).expect("enum_mem");
    let inj = derived::enums::enum_inj(&mut env, &wt).expect("enum_inj");
    let e0 = derived::enums::enum0(&wt, &bnd);
    let e1 = derived::enums::enum1(&wt, &bnd, &mem).expect("enum1");
    let e2 = derived::enums::enum2(&wt, &bnd, &mem, &inj).expect("enum2");

    let zero_u1 = derived::cumul::zero_in_u1(&c);
    let one_u1 = derived::cumul::unit_in_u1(&c).expect("1 ∈ U₁");
    assert_eq!(*one_u1.concl(), Formula::mem(wt.sums.unit(), tower.level(1)));

    for (ty, tags, tin) in [
        (&e0, wt.sums.zero(), &zero_u1),
        (&e1.ty, e1.tags.clone(), &one_u1),
        (&e2.ty, e2.tags.clone(), &m.tags_in_u1),
    ] {
        let t = derived::cumul::enum_in_u1(&mut env, &c, &tags, tin).expect("enum ∈ U₁");
        assert!(t.hyps().is_empty(), "enum ∈ U₁ must be unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
        assert_eq!(*t.concl(), Formula::mem(ty.clone(), tower.level(1)));
        assert_eq!(
            *ty,
            wt.of(tags.clone(), wt.empty(), Term::apply(tower.space.lu, vec![tags.clone()])),
            "the set in U₁ must be W(A, ∅, U(A))"
        );
        // The universe it lives in is **not** its own bound; that membership is
        // refutable, and confusing the two is the error `crate::cumul`'s closing
        // note is about.
        assert_ne!(tower.level(1), Term::apply(tower.space.lu, vec![tags]));
    }

    // `Bool` really has two elements, so `enum(1+1) ∈ U₁` is not about a
    // singleton.
    assert_eq!(*e2.fst.concl(), Formula::mem(e2.fst_t.clone(), e2.ty.clone()));
    assert_eq!(*e2.snd.concl(), Formula::mem(e2.snd_t.clone(), e2.ty.clone()));
    assert_eq!(*e2.distinct.concl(), Formula::not(Formula::eq(e2.fst_t, e2.snd_t)));
}

/// **The guards on `Chain::over`.** A `Wtype` from a different signature than
/// the tower is the mistake the constructor exists to make impossible, and it
/// is not visible in the types — so it is checked, and the check is tested.
#[test]
fn the_chain_refuses_a_signature_it_was_not_given() {
    use derived::bound::Bound;
    use derived::tower::Tower;
    use derived::wtype::Wtype;

    let mut env = Env::new();
    let tower = Tower::new(&mut env).expect("tower");
    // A wholly independent `Wtype`: its own pairing, its own power set, its own
    // everything. Every theorem about it is about other symbols.
    let alien = Wtype::new(&mut env).expect("an unrelated Wtype");
    let alien_bnd = Bound::new(&mut env, &alien).expect("an unrelated Bound");
    assert!(
        derived::cumul::Chain::over(&mut env, &tower, &alien, &alien_bnd).is_none(),
        "a Wtype from another signature must be refused"
    );

    // The sharper case, which the pairing and `U(·)` comparisons cannot see: a
    // `Bound` built over a **second `Wtype` sharing this one's `Sums` and
    // `U(·)`**. Every symbol the other three comparisons look at agrees; only
    // the `W` differs, and `sup_mem`/`w_inversion` are exactly the fields that
    // are about it. A `Chain` accepting this would carry W1 and W3 stated at a
    // `W` that is not its own `wt`'s.
    let sums = derived::sums::Sums::over(
        &mut env,
        tower.sums.ap.clone(),
        tower.space.pow,
        tower.space.pow_ax.clone(),
        tower.sums.prod.clone(),
        tower.sums.fs.clone(),
    )
    .expect("caller's Sums");
    let wt1 = Wtype::over(&mut env, sums.clone()).expect("first Wtype");
    let wt2 = Wtype::over(&mut env, sums).expect("second Wtype over the same Sums");
    assert_ne!(wt1.w, wt2.w, "two Wtypes are two W symbols");
    assert_eq!(wt1.sums.ap.sets.up, wt2.sums.ap.sets.up, "but one pairing");
    let bnd2 = Bound::over(&mut env, &wt2, tower.space.lu, tower.space.lu_ax.clone())
        .expect("a Bound over the second Wtype");
    assert_eq!(bnd2.w, wt2.w);
    assert!(
        derived::cumul::Chain::over(&mut env, &tower, &wt1, &bnd2).is_none(),
        "a Bound whose W1/W3 are about another W must be refused"
    );
    // And the coherent pair is still accepted.
    let bnd1 = Bound::over(&mut env, &wt1, tower.space.lu, tower.space.lu_ax.clone())
        .expect("a Bound over the first Wtype");
    assert!(derived::cumul::Chain::over(&mut env, &tower, &wt1, &bnd1).is_some());
}

/// **`NatMem::over` reads its input's `Γ`, not only its conclusion.**
///
/// `Nat`'s theorem fields are `pub`, so "the right conclusion" is not the same
/// as "the right theorem": `Thm::assume(φ)` has conclusion `φ` and hypothesis
/// `φ`. `finite_branching` consumes the fibre equations through `hyp_mp`, which
/// unions the hypothesis sets, so such an input would ride all the way into
/// `nat_in_u1` — a `{φ} ⊢ N ∈ U₁` presented, by a struct whose documentation
/// says `⊢ N ∈ U₁`, to the checker. A conclusion comparison cannot see it,
/// which is the whole point.
///
/// This is `Thm::assume` used the way `ci/check-boundary.sh` exempts test code
/// to allow: to pin a guard that exists for hypothetical theorems.
#[test]
fn the_witness_refuses_a_hypothetical_input() {
    use kernel::Thm;

    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("chain");
    let wt = c.wt.clone();
    let bnd = c.bound.clone();
    let cases = derived::sums::Cases::new(&mut env, &wt.sums).expect("cases");
    let pf = derived::point_fun::PointFun::over(&mut env, &wt.sums, &wt.app_pair).expect("pf");
    let empty_u = derived::enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("empty_u");
    let honest =
        derived::wnat::Nat::over(&mut env, &wt, &bnd, &cases, &pf, &empty_u).expect("Nat");

    // The honest `Nat` goes through, and everything it yields is unconditional.
    let m = derived::cumul::NatMem::over(&mut env, &c, &honest).expect("the honest witness");
    assert!(m.is_unconditional());
    assert!(m.nat_in_u1.hyps().is_empty());

    // The same conclusions, one of them assumed rather than derived.
    let mut faked = honest;
    let phi = faked.fibre_zero.concl().clone();
    faked.fibre_zero = Thm::assume(phi.clone());
    assert_eq!(*faked.fibre_zero.concl(), phi, "the conclusion is identical …");
    assert_eq!(faked.fibre_zero.hyps(), &[phi], "… and only Γ differs");

    assert!(
        derived::cumul::NatMem::over(&mut env, &c, &faked).is_none(),
        "a hypothetical fibre equation must not become an unconditional N ∈ U₁"
    );
}

/// **`bnd` is a finiteness predicate** — it holds of `∅`, of every singleton,
/// and is closed under binary union.
///
/// These three are what let a fibre that is *not* a von Neumann natural still
/// bound the tower, and they are stated at their exact conclusions: each is
/// rebuilt here from [`derived::cumul::bnd`], which is the same formula
/// `tower_closed_bnd` carries.
#[test]
fn bnd_is_closed_under_the_finite_set_formers() {
    let mut env = Env::new();
    let r = derived::recursion::Rec::new(&mut env).expect("Rec");
    let (pow, pow_ax) = derived::power(&mut env);
    let step = Step::new(&mut env, &r.ap.sets, pow, &pow_ax).expect("Step");
    let st = derived::cumul::Stages::new(&mut env, &r, step).expect("Stages");

    let empty = derived::cumul::finite::bnd_empty(&mut env, &r, &st).expect("bnd_empty");
    let sing = derived::cumul::finite::bnd_singleton(&mut env, &r, &st).expect("bnd_singleton");
    let union = derived::cumul::finite::bnd_bin_union(&mut env, &r, &st).expect("bnd_bin_union");
    for t in [&empty, &sing, &union] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
        assert!(t.hyps().is_empty(), "the finiteness lemmas rest on nothing");
    }

    let zero = r.zero();
    assert_eq!(
        *empty.concl(),
        derived::cumul::bnd(&mut env, &r, &st, &zero),
        "bnd_empty has the wrong shape"
    );

    let e = env.fresh_var();
    let one = derived::singleton(r.ap.sets.up, Term::var(e));
    let one_bnd = derived::cumul::bnd(&mut env, &r, &st, &one);
    assert_eq!(*sing.concl(), Formula::forall(e, one_bnd), "bnd_singleton has the wrong shape");

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let un = bin_union(&r.ap.sets, tx.clone(), ty.clone());
    let hyp = Formula::and(
        derived::cumul::bnd(&mut env, &r, &st, &tx),
        derived::cumul::bnd(&mut env, &r, &st, &ty),
    );
    assert_eq!(
        *union.concl(),
        Formula::forall(
            x,
            Formula::forall(y, Formula::imp(hyp, derived::cumul::bnd(&mut env, &r, &st, &un))),
        ),
        "bnd_bin_union has the wrong shape"
    );

    // Non-vacuity: `bnd(k)` is not a formula that ignores `k` — the three
    // conclusions are about three different sets and are three different
    // formulas.
    assert_ne!(
        derived::cumul::bnd(&mut env, &r, &st, &zero),
        derived::cumul::bnd(&mut env, &r, &st, &un),
        "bnd must depend on the set it bounds"
    );
}

/// **The bridge** — `⊢ bnd(finord(m))` at each concrete arity, so the general
/// inductive translation's fibres satisfy `tower_closed_bnd`'s hypothesis.
///
/// `finord(m)` is `Sum_m(1,…,1)`, which has `m` elements and is **not** the von
/// Neumann numeral `m`; `finord(m) ∈ ω` is false, which is what made this the
/// blocker. Both halves are pinned: the set equation the argument goes through
/// and the `bnd` it produces.
#[test]
fn the_general_translations_fibre_bounds_the_tower() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    let s = c.wt.sums.clone();
    let mut syms = derived::isum::ISumSyms::new();
    syms.ensure(&mut env, &s, 3).expect("ensure");

    for m in 0..=3 {
        let sigma = syms.finord(&s, m).expect("finord");
        let eq = derived::cumul::finord_is_explicit(&mut env, &c.r, &s, &syms, m)
            .expect("finord_is_explicit");
        let thm = derived::cumul::bnd_finord(&mut env, &c.r, &c.st, &s, &syms, m)
            .expect("bnd_finord");
        assert!(eq.hyps().is_empty() && thm.hyps().is_empty(), "both rest on nothing");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));

        let (lhs, _) = eq.concl().as_eq().expect("an equation");
        assert_eq!(lhs, sigma, "the equation must be about finord(m)");
        assert_eq!(
            *thm.concl(),
            derived::cumul::bnd(&mut env, &c.r, &c.st, &sigma),
            "bnd_finord has the wrong shape at m = {m}"
        );
    }

    // Non-vacuity, and the whole point: `finord(1)` is not the term `1`, and
    // `finord(m) ∈ ω` is not what was proved.
    assert_ne!(syms.finord(&s, 1).expect("finord"), s.unit(), "finord(1) is 1 + 0, not {{∅}}");
    let two = syms.finord(&s, 2).expect("finord");
    assert_ne!(
        derived::cumul::bnd(&mut env, &c.r, &c.st, &two),
        Formula::mem(two, c.r.omega()),
        "the hypothesis discharged is bnd, not membership in ω"
    );
}

/// **The general form of steps (d) and (f)**, at the exact statements two
/// consumers are written against.
///
/// `Fin⁺(A,B)` is rebuilt here from [`derived::cumul::fin_bnd`] rather than
/// read off `tower_closed_bnd`, so this checks that a consumer who *states* the
/// hypothesis gets the one the theorem carries.
#[test]
fn the_wtype_membership_at_the_general_fibre_condition() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    for t in [&c.wmem.w_sub_tower_bnd, &c.wmem.w_in_universe_bnd, &c.tower_closed_bnd] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
        assert!(t.hyps().is_empty(), "the general statements rest on nothing");
    }

    let (a, b, cv, dv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(cv), Term::var(dv));
    let (uc, ud) = (Term::apply(c.lu(), vec![tc]), Term::apply(c.lu(), vec![td]));
    let seed = Term::var(c.st.seed);
    let tower = c.st.tower_set();
    let w = c.wt.of(ta.clone(), tb.clone(), uc.clone());

    let fin = derived::cumul::fin_bnd(&mut env, &c.r, &c.st, &seed, &ta, &tb);
    assert_eq!(
        *c.tower_closed_bnd.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::imp(
                    fin.clone(),
                    derived::wtype::closed(&mut env, &c.wt.sums, &ta, &tb, &tower),
                ),
            ),
        ),
        "tower_closed_bnd has the wrong shape"
    );

    let h1 = Formula::and(fin, Formula::mem(seed.clone(), uc));
    assert_eq!(
        *c.wmem.w_sub_tower_bnd.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    cv,
                    Formula::imp(h1.clone(), kernel::thm::subset(&mut env, w.clone(), tower)),
                ),
            ),
        ),
        "w_sub_tower_bnd has the wrong shape"
    );

    let size = Formula::and(
        Formula::mem(seed.clone(), ud.clone()),
        Formula::mem(c.r.omega(), ud.clone()),
    );
    assert_eq!(
        *c.wmem.w_in_universe_bnd.concl(),
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    cv,
                    Formula::forall(
                        dv,
                        Formula::imp(Formula::and(h1, size), Formula::mem(w, ud)),
                    ),
                ),
            ),
        ),
        "w_in_universe_bnd has the wrong shape"
    );

    // Non-vacuity: the general hypothesis is genuinely weaker — the two `Fin`s
    // are different formulas, and the `∈ ω` one is the antecedent of
    // `tower_closed`, which is the *other* theorem.
    let fin_omega = derived::inst_all(&c.tower_closed, &[ta.clone(), tb.clone()])
        .expect("instantiate tower_closed")
        .concl()
        .as_imp()
        .expect("an implication")
        .0;
    assert_ne!(
        fin_omega,
        derived::cumul::fin_bnd(&mut env, &c.r, &c.st, &seed, &ta, &tb),
        "Fin and Fin⁺ must not be the same formula"
    );
}

/// **The general statement composes** — `⊢ ⟦N⟧ ∈ U₁` again, this time out of
/// `w_in_universe_bnd` rather than `w_in_universe`.
///
/// This is the consumer's path walked end to end at terms that already exist:
/// take the `∈ ω` fibre condition `crate::wnat` discharges, weaken it to
/// `bnd(B(a))` with `bounded`, and feed it to the general theorem. The result is
/// the *same* theorem `NatUniverse` produces, so nothing about the
/// generalisation costs the specialised consumers anything.
#[test]
fn the_general_membership_statement_reproves_the_naturals_in_u1() {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    let nu = derived::cumul::NatUniverse::new(&mut env, &c).expect("NatUniverse");
    let seed = nu.seed.clone();
    let (tags, fam) = (nu.nat.tags.clone(), nu.nat.fam.clone());
    let om = c.r.omega();

    // `bounded` at the concrete seed: the seed is a free variable everywhere in
    // `cumul`, so a statement about it is really `∀S`.
    let bounded_here = derived::inst_all(
        &kernel::Thm::gen(c.st.seed, &c.bounded),
        std::slice::from_ref(&seed),
    )
    .expect("bounded at the seed");

    // `Fin(A,B) → Fin⁺(A,B)`, at these terms: `B(a) ∈ ω → bnd(B(a))` under the
    // `a ∈ A →` and under the `∀a`.
    let av = env.fresh_var();
    let ta = Term::var(av);
    let k = c.r.apply(fam.clone(), ta.clone());
    let k_sub = kernel::thm::subset(&mut env, k.clone(), seed.clone());
    let k_om = Formula::mem(k.clone(), om.clone());
    let a_in = Formula::mem(ta, tags.clone());
    let strengthen = derived::hyp_and(
        &derived::and_left(k_sub.clone(), k_om.clone()),
        &derived::syl(
            &derived::and_right(k_sub, k_om),
            &derived::inst_all(&bounded_here, std::slice::from_ref(&k)).expect("bnd at B(a)"),
        )
        .expect("syl"),
    )
    .expect("hyp_and");
    let under_all = derived::forall_mono(
        av,
        &kernel::Thm::gen(av, &derived::imp_mono_r(&strengthen, a_in).expect("imp_mono_r")),
    )
    .expect("forall_mono");

    let fin_plus = derived::and_intro(
        &derived::and_elim_left(&nu.fin).expect("A ⊆ S"),
        &kernel::Thm::mp(&under_all, &derived::and_elim_right(&nu.fin).expect("the fibres"))
            .expect("mp"),
    );
    assert_eq!(
        *fin_plus.concl(),
        derived::cumul::fin_bnd(&mut env, &c.r, &c.st, &seed, &tags, &fam),
        "the weakened hypothesis is not Fin⁺"
    );

    let at = derived::inst_all(
        &kernel::Thm::gen(c.st.seed, &c.wmem.w_in_universe_bnd),
        &[seed, tags.clone(), fam, tags, om],
    )
    .expect("w_in_universe_bnd at the concrete terms");
    let out = kernel::Thm::mp(
        &at,
        &derived::and_intro(
            &derived::and_intro(&fin_plus, &nu.seed_in_bound),
            &derived::and_intro(&nu.seed_in_u1, &c.u1.omega_mem),
        ),
    )
    .expect("mp");

    assert!(out.hyps().is_empty(), "the general route also rests on nothing");
    assert_eq!(
        *out.concl(),
        Formula::mem(nu.nat.ty.clone(), c.u1.set.clone()),
        "the general route must land on ⟦N⟧ ∈ U₁"
    );
    assert_eq!(*out.concl(), *nu.nat_in_u1.concl(), "the two routes must agree");
}
