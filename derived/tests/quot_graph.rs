//! **The curried-relation seam, and the quotient's formation theorem** —
//! `derived/src/quot/graph.rs` and `derived/src/quot/universe.rs`.
//!
//! # What these close
//!
//! Every theorem in `derived/src/quot/` takes `R` as a *set of pairs*, while
//! Lean's `r : α → α → Prop` interprets curried — `⟦r⟧ ∈ fs(A, fs(A, U₀))`, with
//! "`r x y` holds" spelled `• ∈ app(app(⟦r⟧,x),y)`. So until `rel_graph` there
//! was no Lean-side term the quotient machinery could be applied to at all. The
//! two headline tests here are therefore not about the bridge in isolation but
//! about the two theorems that consume it:
//!
//! * **`Quot.sound` at Lean's `r`** — `pair_in_graph` composed with
//!   `Quotient::sound`;
//! * **`Quot.lift`'s hypothesis at Lean's `r`** — `graph_pair` turning the
//!   curried certificate into `rcompat`, which `compat_closure` already accepts.
//!
//! One bridge per direction, and each has exactly one consumer.
//!
//! # Non-vacuity
//!
//! A graph conversion is easy to satisfy by accident: a constantly-empty
//! `rel_graph` satisfies "membership implies the relation", and a constantly-`A²`
//! one satisfies the converse. Both directions are therefore pinned at a
//! **concrete** relation over a **three-element** carrier — `finord(3)`, whose
//! injections are pairwise distinct — with `r` relating `e₀` to `e₁` and nothing
//! else:
//!
//! ```text
//! ⟨e₀,e₁⟩ ∈ rel_graph      ¬(⟨e₁,e₀⟩ ∈ rel_graph)      ¬(⟨e₀,e₀⟩ ∈ rel_graph)
//! ```
//!
//! The middle one is the pair-ordering claim: a construction that swapped `u`
//! and `v` in the condition proves the converse relation and fails there. The
//! third rules out the diagonal, and the untouched `e₂` rules out `A²`.

use kernel::{Env, Formula, Term, Thm};

use derived::funcs::app_off_domain;
use derived::isum::ISumSyms;
use derived::point_fun::PointFun;
use derived::quot::{
    graph_pair, graph_subset, holds, pair_in_graph, quot_in_universe, quot_subset_pow,
    Quotient, RelGraph,
};
use derived::sums::Sums;
use derived::tower::Tower;
use derived::{
    and_left, and_right, conj_of, eq_symm, gen_all, hyp_and, hyp_mp, imp_refl, inst_all,
    notnot_intro, syl, uncurry,
};

/// A formula with no free variables.
fn closed_f(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// From `⊢ x = y` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp")
}

/// From `⊢ y = x` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// Everything the tests share: the quotient, the graph symbol, and a
/// three-element carrier with pairwise-distinct elements.
struct Fix {
    tow: Tower,
    q: Quotient,
    graph: kernel::FnSym,
    graph_ax: Thm,
    pf: PointFun,
    off: Thm,
    syms: ISumSyms,
    /// `finord(3)`.
    carrier: Term,
    /// `Inj₀(•)`, `Inj₁(•)`, `Inj₂(•)`.
    e: [Term; 3],
}

fn fixture(env: &mut Env) -> Fix {
    // One signature: the tower mints the `Sums`, and the quotient joins it
    // rather than starting a second one — otherwise `U(·)`'s closure clauses
    // speak about a different power set and `quot_in_universe` refuses.
    let tow = Tower::new(env).expect("a tower");
    let q = Quotient::over(env, tow.sums.clone()).expect("the quotient over the tower's sums");
    let s = q.sums.clone();
    // The symbol comes from the **apparatus**, not from a second mint: one
    // `rel_graph` per `Env`, as the header claims.
    let (graph, graph_ax) = (q.rel_graph, q.rel_graph_ax.clone());
    let app_pair = derived::ext::app_of_pair(env, &s.ap).expect("app of a pair");
    let pf = PointFun::over(env, &s, &app_pair).expect("the one-point function");
    let off = app_off_domain(env, &s.ap).expect("application off the domain");
    let mut syms = ISumSyms::new();
    syms.ensure(env, &s, 3).expect("three summands");
    let carrier = syms.finord(&s, 3).expect("finord(3)");
    let e = [
        syms.inj(0, s.point()).expect("Inj₀"),
        syms.inj(1, s.point()).expect("Inj₁"),
        syms.inj(2, s.point()).expect("Inj₂"),
    ];
    Fix { tow, q, graph, graph_ax, pf, off, syms, carrier, e }
}

impl Fix {
    fn s(&self) -> &Sums { &self.q.sums }
    fn rg(&self) -> RelGraph<'_> {
        RelGraph { s: &self.q.sums, graph: self.graph, graph_ax: &self.graph_ax }
    }
    /// `⊢ Injⱼ(•) ∈ finord(3)`.
    fn mem(&self, j: usize) -> Thm {
        let s = self.s();
        let mut args = vec![s.unit(); 3];
        args.push(s.point());
        Thm::mp(
            &inst_all(self.syms.inj_mem(3, j).expect("inj_mem"), &args).expect("instantiate"),
            &s.unit_mem,
        )
        .expect("mp")
    }
    /// `⊢ ¬(Injᵢ(•) = Injⱼ(•))`.
    fn distinct(&self, env: &mut Env, i: usize, j: usize) -> Thm {
        let s = self.s().clone();
        let ne = self.syms.inj_distinct(env, &s, i, j).expect("the injections differ");
        inst_all(&ne, &[s.point(), s.point()]).expect("at •")
    }
    /// `⊢ app({⟨p,q⟩}, a) = ∅`, given `⊢ ¬(a = p)`.
    fn app_off(&self, env: &mut Env, p: &Term, q: &Term, a: &Term, ne: &Thm) -> Thm {
        let s = self.s().clone();
        let f = PointFun::of(&s, p.clone(), q.clone());
        let yv = env.fresh_var();
        let ty = Term::var(yv);
        // `⟨a,y⟩ ∈ {⟨p,q⟩} → (a = p ∧ y = q)`, refuted by `¬(a = p)`.
        let pairs =
            inst_all(&self.pf.pairs, &[p.clone(), q.clone(), a.clone(), ty.clone()])
                .expect("point_pairs");
        let (l, r) = (
            Formula::eq(a.clone(), p.clone()),
            Formula::eq(ty.clone(), q.clone()),
        );
        let no = syl(&syl(&pairs, &and_left(l, r)).expect("syl"), ne).expect("refuted");
        let all_not = Thm::gen(yv, &no);
        let no_ex = Thm::mp(&notnot_intro(all_not.concl().clone()), &all_not).expect("¬∃");
        let at = inst_all(&self.off, &[f, a.clone()]).expect("app_off_domain");
        Thm::mp(&at, &no_ex).expect("mp")
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The three statements
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_graph_has_the_three_shapes_the_header_advertises() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.s().clone();
    let g = f.rg();

    let (av, rv, uv, vv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tu, tv) = (Term::var(av), Term::var(rv), Term::var(uv), Term::var(vv));
    let p = s.ap.sets.pair(tu.clone(), tv.clone());
    let mem_g = Formula::mem(p.clone(), g.of(&ta, &tr));

    // The apparatus carries the same three theorems, so a consumer needs no
    // second mint and canonicality is structural rather than a convention.
    let out = graph_pair(&mut env, &g).expect("read the relation off a member");
    assert_eq!(*f.q.graph_pair.concl(), *out.concl(), "Quotient carries graph_pair");
    assert_eq!(
        *out.concl(),
        gen4(&[av, rv, uv, vv], Formula::imp(mem_g.clone(), holds(&s, &tr, &tu, &tv))),
        "⊢ ∀A ∀r ∀u ∀v. (⟨u,v⟩ ∈ rel_graph(A,r) → • ∈ app(app(r,u),v))",
    );
    assert!(out.hyps().is_empty() && closed_f(out.concl()));

    let into = pair_in_graph(&mut env, &g).expect("put a related pair in");
    assert_eq!(*f.q.pair_in_graph.concl(), *into.concl(), "…and pair_in_graph");
    let want_ante = conj_of(&[
        Formula::mem(tu.clone(), ta.clone()),
        Formula::mem(tv.clone(), ta.clone()),
        holds(&s, &tr, &tu, &tv),
    ])
    .expect("three atoms");
    assert_eq!(
        *into.concl(),
        gen4(&[av, rv, uv, vv], Formula::imp(want_ante, mem_g)),
        "⊢ ∀A ∀r ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ • ∈ app(app(r,u),v))) → ⟨u,v⟩ ∈ rel_graph(A,r))",
    );
    assert!(into.hyps().is_empty() && closed_f(into.concl()));

    let sub = graph_subset(&mut env, &g).expect("the graph is a relation on A");
    assert_eq!(*f.q.graph_subset.concl(), *sub.concl(), "…and graph_subset");
    let want_sub = kernel::thm::subset(&mut env, g.of(&ta, &tr), s.prod.of(ta.clone(), ta));
    assert_eq!(*sub.concl(), Formula::forall(av, Formula::forall(rv, want_sub)));
    assert!(sub.hyps().is_empty() && closed_f(sub.concl()));

    // A hypothetical `graph_ax` is refused at the door, not composed.
    let fake = Thm::assume(f.graph_ax.concl().clone());
    let bad = RelGraph { s: &s, graph: f.graph, graph_ax: &fake };
    assert!(graph_pair(&mut env, &bad).is_none());
    assert!(pair_in_graph(&mut env, &bad).is_none());
    assert!(graph_subset(&mut env, &bad).is_none());
}

/// `∀a ∀b ∀c ∀d. φ`.
fn gen4(vs: &[kernel::FreeVar], phi: Formula) -> Formula {
    vs.iter().rev().fold(phi, |acc, v| Formula::forall(*v, acc))
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity: both directions, at a concrete relation over three elements
// ─────────────────────────────────────────────────────────────────────────────

/// **The pair-ordering claim.** `r` relates `e₀` to `e₁` and nothing else, over
/// a three-element carrier. The graph contains `⟨e₀,e₁⟩`; it does **not**
/// contain `⟨e₁,e₀⟩`, which is what a construction that swapped `u` and `v`
/// would prove instead, nor `⟨e₀,e₀⟩`, which rules out the diagonal and `A²`.
#[test]
fn the_graph_is_the_relation_and_not_its_converse() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.s().clone();
    let g = f.rg();
    let (one, zero) = (s.unit(), s.zero());
    let (e0, e1, e2) = (f.e[0].clone(), f.e[1].clone(), f.e[2].clone());

    // `r := {⟨e₀, {⟨e₁, 1⟩}⟩}` — the inner function is `{⟨e₁,1⟩}`.
    let inner = PointFun::of(&s, e1.clone(), one.clone());
    let r = PointFun::of(&s, e0.clone(), inner.clone());
    let graph_t = g.of(&f.carrier, &r);

    // ── forward: `• ∈ app(app(r,e₀),e₁)`, hence `⟨e₀,e₁⟩ ∈ rel_graph` ───────
    let outer_at = inst_all(&f.pf.app, &[e0.clone(), inner.clone()]).expect("app(r,e₀) = inner");
    let inner_at = inst_all(&f.pf.app, &[e1.clone(), one.clone()]).expect("app(inner,e₁) = 1");
    // `• ∈ 1` carried back along the two computations.
    let step = rw_back(&mut env, &inner_at, |t| Formula::mem(s.point(), t), &s.unit_mem);
    let (r_c, e1_c, s_c) = (r.clone(), e1.clone(), s.clone());
    let related = rw_back(
        &mut env,
        &outer_at,
        move |t| Formula::mem(s_c.point(), s_c.ap.apply(t, e1_c.clone())),
        &step,
    );
    assert_eq!(*related.concl(), holds(&s, &r_c, &e0, &e1));

    let into = pair_in_graph(&mut env, &g).expect("the forward bridge");
    let at = inst_all(&into, &[f.carrier.clone(), r.clone(), e0.clone(), e1.clone()])
        .expect("at the concrete data");
    let hyps = derived::and_intro(
        &f.mem(0),
        &derived::and_intro(&f.mem(1), &related),
    );
    let in_graph = Thm::mp(&at, &hyps).expect("the three atoms are the antecedent");
    assert_eq!(
        *in_graph.concl(),
        Formula::mem(s.ap.sets.pair(e0.clone(), e1.clone()), graph_t.clone()),
        "⊢ ⟨e₀,e₁⟩ ∈ rel_graph(finord(3), r)",
    );
    assert!(in_graph.hyps().is_empty() && closed_f(in_graph.concl()));

    // ── backward: the converse pair is **not** in the graph ────────────────
    let out = graph_pair(&mut env, &g).expect("the backward bridge");
    let ne_10 = f.distinct(&mut env, 1, 0);
    // `app(r,e₁) = ∅` (off `r`'s domain), so `app(app(r,e₁),e₀) = ∅`.
    let off_r = f.app_off(&mut env, &e0, &inner, &e1, &ne_10);
    let empty_app = inst_all(
        &derived::wtype::app_of_empty(&mut env, &s).expect("app(∅,a) = ∅"),
        std::slice::from_ref(&e0),
    )
    .expect("app(∅,e₀) = ∅");
    let no_self = inst_all(&s.ap.empty_ax, std::slice::from_ref(&s.point())).expect("¬(• ∈ ∅)");
    let back1 = rw_back(&mut env, &empty_app, |t| Formula::not(Formula::mem(s.point(), t)), &no_self);
    let (e0_c, s_c) = (e0.clone(), s.clone());
    let not_rel = rw_back(
        &mut env,
        &off_r,
        move |t| Formula::not(Formula::mem(s_c.point(), s_c.ap.apply(t, e0_c.clone()))),
        &back1,
    );
    assert_eq!(*not_rel.concl(), Formula::not(holds(&s, &r, &e1, &e0)));

    let at_rev = inst_all(&out, &[f.carrier.clone(), r.clone(), e1.clone(), e0.clone()])
        .expect("at the reversed pair");
    let refuted = syl(&at_rev, &not_rel).expect("the reversed pair is refuted");
    assert_eq!(
        *refuted.concl(),
        Formula::not(Formula::mem(s.ap.sets.pair(e1.clone(), e0.clone()), graph_t.clone())),
        "⊢ ¬(⟨e₁,e₀⟩ ∈ rel_graph(finord(3), r)) — the graph is not the converse",
    );
    assert!(refuted.hyps().is_empty() && closed_f(refuted.concl()));

    // ── the diagonal, and the untouched third element ──────────────────────
    let ne_01 = f.distinct(&mut env, 0, 1);
    let off_inner = f.app_off(&mut env, &e1, &one, &e0, &ne_01);
    let no_self2 = inst_all(&s.ap.empty_ax, std::slice::from_ref(&s.point())).expect("¬(• ∈ ∅)");
    let (r_d, e0_d) = (r.clone(), e0.clone());
    let not_diag_rel = {
        let base = rw_back(
            &mut env,
            &off_inner,
            |t| Formula::not(Formula::mem(s.point(), t)),
            &no_self2,
        );
        let outer = inst_all(&f.pf.app, &[e0.clone(), inner.clone()]).expect("app(r,e₀) = inner");
        let s_d = s.clone();
        rw_back(
            &mut env,
            &outer,
            move |t| Formula::not(Formula::mem(s_d.point(), s_d.ap.apply(t, e0_d.clone()))),
            &base,
        )
    };
    let at_diag = inst_all(&out, &[f.carrier.clone(), r_d.clone(), e0.clone(), e0.clone()])
        .expect("at the diagonal pair");
    let no_diag = syl(&at_diag, &not_diag_rel).expect("the diagonal is refuted");
    assert_eq!(
        *no_diag.concl(),
        Formula::not(Formula::mem(s.ap.sets.pair(e0.clone(), e0.clone()), graph_t.clone())),
        "⊢ ¬(⟨e₀,e₀⟩ ∈ rel_graph(…)) — not the diagonal, and not A²",
    );

    // The three carrier elements really are three.
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        assert!(f.syms.inj_distinct(&mut env, &s, i, j).is_some());
    }
    assert_ne!(e0, e2);
    assert_ne!(e1, e2);
    assert_ne!(zero, one);
}

// ─────────────────────────────────────────────────────────────────────────────
// The two consumers
// ─────────────────────────────────────────────────────────────────────────────

/// **`Quot.sound` at Lean's curried `r`.** `Quotient::sound` wants
/// `⟨a,b⟩ ∈ R`; the checker holds `• ∈ app(app(⟦r⟧,a),b)`. Composed with
/// `pair_in_graph`, the theorem the wiring actually needs falls out:
///
/// ```text
/// ⊢ ∀A ∀r ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ • ∈ app(app(r,a),b)))
///                     → class(A, rel_graph(A,r), a) = class(A, rel_graph(A,r), b))
/// ```
#[test]
fn quot_sound_composes_with_the_curried_relation() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.s().clone();
    let g = f.rg();

    let (av, rv, a1, b1) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, taa, tbb) = (Term::var(av), Term::var(rv), Term::var(a1), Term::var(b1));
    let graph_t = g.of(&ta, &tr);

    let into = pair_in_graph(&mut env, &g).expect("the forward bridge");
    let at_bridge = inst_all(&into, &[ta.clone(), tr.clone(), taa.clone(), tbb.clone()])
        .expect("at the working variables");
    let at_sound = inst_all(&f.q.sound, &[ta.clone(), graph_t.clone(), taa.clone(), tbb.clone()])
        .expect("sound at R := rel_graph(A,r)");

    // `sound`'s antecedent is `a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R)`; the bridge's
    // conclusion is its third conjunct, so the two meet after one reassembly.
    let (mem_a, mem_b, rel) = (
        Formula::mem(taa.clone(), ta.clone()),
        Formula::mem(tbb.clone(), ta.clone()),
        holds(&s, &tr, &taa, &tbb),
    );
    let h = conj_of(&[mem_a.clone(), mem_b.clone(), rel.clone()]).expect("three atoms");
    let h_a = derived::conj_proj(&[mem_a.clone(), mem_b.clone(), rel.clone()], 0).expect("a ∈ A");
    let h_b = derived::conj_proj(&[mem_a.clone(), mem_b.clone(), rel.clone()], 1).expect("b ∈ A");
    let h_g = syl(&imp_refl(h.clone()), &at_bridge).expect("⟨a,b⟩ ∈ rel_graph(A,r)");
    let assembled = hyp_and(&h_a, &hyp_and(&h_b, &h_g).expect("and")).expect("and");
    let out = syl(&assembled, &at_sound).expect("into sound");

    let cls = |x: &Term| {
        Term::apply(f.q.class, vec![ta.clone(), graph_t.clone(), x.clone()])
    };
    assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(cls(&taa), cls(&tbb))),
        "Quot.sound, with Lean's `r` in the antecedent",
    );
    assert!(out.hyps().is_empty());
    let closed = gen_all(&[av, rv, a1, b1], &out);
    assert!(closed_f(closed.concl()));
}

/// **`Quot.lift`'s hypothesis at Lean's curried `r`.** The other direction:
/// Lean's `h : ∀ a b, r a b → f a = f b` arrives curried, and
/// `Quotient::compat_closure` consumes `rcompat(A,R,f)` with `⟨a,b⟩ ∈ R`.
/// `graph_pair` is what converts it, and this derives
///
/// ```text
/// ⊢ ∀A ∀r ∀f. (leanh(A,r,f) → rcompat(A, rel_graph(A,r), f))
/// ```
///
/// at `rcompat`'s own formula, rebuilt from `derived`'s constructor so the two
/// cannot drift.
#[test]
fn the_lift_hypothesis_converts_from_the_curried_relation() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.s().clone();
    let g = f.rg();

    let (av, rv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tf) = (Term::var(av), Term::var(rv), Term::var(fv));
    let graph_t = g.of(&ta, &tr);
    let want = derived::quot::rcompat(&mut env, &s, &ta, &graph_t, &tf);

    // Lean's hypothesis, at the curried relation.
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let eq_f = Formula::eq(s.ap.apply(tf.clone(), tx.clone()), s.ap.apply(tf.clone(), ty.clone()));
    let curried_body = Formula::imp(
        conj_of(&[
            Formula::mem(tx.clone(), ta.clone()),
            Formula::mem(ty.clone(), ta.clone()),
            holds(&s, &tr, &tx, &ty),
        ])
        .expect("three atoms"),
        eq_f.clone(),
    );
    let leanh = Formula::forall(xv, Formula::forall(yv, curried_body.clone()));

    // Under `leanh` and `rcompat`'s own antecedent, convert and apply.
    let pair_atoms = [
        Formula::mem(tx.clone(), ta.clone()),
        Formula::mem(ty.clone(), ta.clone()),
        Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), graph_t.clone()),
    ];
    let set_h = conj_of(&pair_atoms).expect("three atoms");
    let k_lean = and_left(leanh.clone(), set_h.clone());
    let k_set = and_right(leanh.clone(), set_h.clone());

    let out_bridge = graph_pair(&mut env, &g).expect("the backward bridge");
    let at_bridge = inst_all(&out_bridge, &[ta.clone(), tr.clone(), tx.clone(), ty.clone()])
        .expect("at the working variables");
    let k_rel = syl(
        &syl(&k_set, &derived::conj_proj(&pair_atoms, 2).expect("the pair")).expect("syl"),
        &at_bridge,
    )
    .expect("the curried relation holds");
    let k_x = syl(&k_set, &derived::conj_proj(&pair_atoms, 0).expect("x ∈ A")).expect("syl");
    let k_y = syl(&k_set, &derived::conj_proj(&pair_atoms, 1).expect("y ∈ A")).expect("syl");

    // `leanh` instantiated at `x`, `y`, then discharged.
    let mut inner = imp_refl(leanh.clone());
    for t in [tx.clone(), ty.clone()] {
        let (_, all) = inner.concl().as_imp().expect("an implication");
        inner = syl(&inner, &Thm::ax_inst(all, t).expect("inst")).expect("syl");
    }
    assert_eq!(*inner.concl(), Formula::imp(leanh.clone(), curried_body.clone()));
    let k_inner = syl(&k_lean, &inner).expect("under the context");
    let k_eq = hyp_mp(
        &k_inner,
        &hyp_and(&k_x, &hyp_and(&k_y, &k_rel).expect("and")).expect("and"),
    )
    .expect("the equation");

    let mut body = uncurry(&k_eq).expect("peel the context");
    for v in [yv, xv] {
        let (h, phi) = body.concl().as_imp().expect("an implication");
        body = Thm::mp(&Thm::ax_dist(v, h, phi).expect("dist"), &Thm::gen(v, &body))
            .expect("generalise under the hypothesis");
    }
    assert_eq!(
        *body.concl(),
        Formula::imp(leanh, want),
        "⊢ leanh(A,r,f) → rcompat(A, rel_graph(A,r), f)",
    );
    assert!(body.hyps().is_empty());
    let closed = gen_all(&[av, rv, fv], &body);
    assert!(closed_f(closed.concl()));

    // …and `compat_closure` accepts what came out, so the chain reaches `lift`.
    let cc = inst_all(&f.q.compat_closure, &[ta, graph_t, tf]).expect("compat_closure");
    assert_eq!(
        cc.concl().as_imp().expect("an implication").0,
        body.concl().as_imp().expect("an implication").1,
        "rcompat at the graph is exactly what compat_closure consumes",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The formation theorem
// ─────────────────────────────────────────────────────────────────────────────

/// **`⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))`**, and it is not vacuous: at a
/// concrete carrier the antecedent is dischargeable and the quotient of a
/// three-element set really lands in `U₁`.
///
/// Nothing about `R` is used, which the statement shows by quantifying over it
/// with no hypothesis at all.
#[test]
fn the_quotient_of_a_small_carrier_is_small() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.s().clone();
    let tow = &f.tow;

    // The tower must be over *this* signature, or the guards refuse — which is
    // the point of handing the two closure clauses in rather than building them.
    assert_eq!(tow.sums.ap.sets.up, s.ap.sets.up, "one pairing");
    assert_eq!(tow.sums.pow, s.pow, "one power set");

    let out = quot_in_universe(
        &mut env,
        &s,
        f.q.class,
        f.q.quot,
        &f.q.quot_ax,
        tow.space.lu,
        &tow.pow,
        &tow.sub,
    )
    .expect("the formation theorem");

    let (av, rv, cv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc) = (Term::var(av), Term::var(rv), Term::var(cv));
    let u_c = Term::apply(tow.space.lu, vec![tc.clone()]);
    let quot_t = Term::apply(f.q.quot, vec![ta.clone(), tr.clone()]);
    assert_eq!(
        *out.concl(),
        gen4(
            &[av, rv, cv],
            Formula::imp(
                Formula::mem(ta.clone(), u_c.clone()),
                Formula::mem(quot_t, u_c),
            ),
        ),
    );
    assert!(out.hyps().is_empty() && closed_f(out.concl()));

    // The subset half, on its own.
    let sub = quot_subset_pow(&mut env, &s, f.q.class, f.q.quot, &f.q.quot_ax)
        .expect("quot(A,R) ⊆ 𝒫A");
    assert!(sub.hyps().is_empty() && closed_f(sub.concl()));

    // ── non-vacuity: a concrete carrier, and a real rung ───────────────────
    //
    // `finord(3) ∈ U₁` by `isum::finord_in_universe`, so the antecedent is
    // dischargeable and the conclusion is about a quotient of a set with three
    // provably distinct elements — not about `∅` and not under a hypothesis
    // nothing satisfies.
    let rung = tow.at(1).expect("rung 1");
    let clo = derived::isum::SumClosure::new(
        &mut env,
        &s,
        tow.space.lu,
        &tow.empty_in,
        &tow.pairing,
        &tow.product,
        &tow.bin_union,
    )
    .expect("the sum closure");
    let small = inst_all(
        &derived::isum::finord_in_universe(&mut env, &clo, &s, &f.syms, 3)
            .expect("⊢ ∀c. finord(3) ∈ U(c)"),
        std::slice::from_ref(&rung.seed),
    )
    .expect("at rung 1's seed");
    assert_eq!(*small.concl(), Formula::mem(f.carrier.clone(), rung.set.clone()));

    let rel = Term::var(env.fresh_var());
    let at = inst_all(&out, &[f.carrier.clone(), rel.clone(), rung.seed.clone()])
        .expect("at the concrete carrier and rung 1");
    let fired = Thm::mp(&at, &small).expect("the carrier is small");
    assert_eq!(
        *fired.concl(),
        Formula::mem(
            Term::apply(f.q.quot, vec![f.carrier.clone(), rel]),
            rung.set.clone()
        ),
        "⊢ quot(finord(3), R) ∈ U₁, at any R",
    );
    assert!(fired.hyps().is_empty());

    // A closure theorem about somebody else's power set is refused, not used.
    let other = Tower::new(&mut env).expect("a second tower");
    assert_ne!(other.space.lu, tow.space.lu, "two towers, two U(·)");
    assert!(
        quot_in_universe(
            &mut env,
            &s,
            f.q.class,
            f.q.quot,
            &f.q.quot_ax,
            tow.space.lu,
            &other.pow,
            &tow.sub,
        )
        .is_none(),
        "a foreign closure clause was accepted",
    );
    let fake = Thm::assume(tow.pow.concl().clone());
    assert!(
        quot_in_universe(
            &mut env, &s, f.q.class, f.q.quot, &f.q.quot_ax, tow.space.lu, &fake, &tow.sub,
        )
        .is_none(),
        "a hypothetical closure clause was accepted",
    );
}
