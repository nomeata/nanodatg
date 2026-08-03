//! **The edge proposition *is* the relation's own value** —
//! `ep(rel_graph(A,r), y, x) = app(app(r,y),x)`.
//!
//! # The consumer, and the obligation it discharges
//!
//! `Acc.rec` at `u₁ ≥ 1` needs its typing refined from [`crate::rec_acc`]'s
//! fixed target `T` down to Lean's motive, which is a second `acc_rect` at
//! `φ(z) := app(accrec,z) ∈ app(app(C̄,z),•)`. That induction's step applies the
//! minor premise `ē` at the induction hypothesis, and Lean's type for it is
//! `∀ y (hy : r y x), C y (h y hy)` — so the checker owes the identification of
//! *its* proof-set `⟦r y x⟧` with the one [`super::ih`] builds the rows of
//! ([`super::ih::ep_of`]). `MINI-HANDOFF.md` §25 item 3 names it and says
//! nothing states it.
//!
//! # Why this is `derived/`'s and not the checker's
//!
//! §25 left the question open on the grounds that the equation "is stated in
//! `derived`'s vocabulary on one side and mini's on the other". **Measured, it
//! is not: both sides are `derived`'s.** `R̄` is not a checker-side term — it is
//! [`crate::quot::graph`]'s `rel_graph(A,r)`, a symbol of this crate — and
//! `⟦r y x⟧` is `app(app(r,y),x)`, which the same file already names
//! [`holds`](crate::quot::graph::holds) at the curried interpretation. So the
//! whole equation is `∀A ∀r ∀y ∀x. …` over set variables, with no interpreted
//! term in it anywhere, and the checker's only job is to instantiate it.
//!
//! The one genuinely interpretation-flavoured input is *"`⟦r y x⟧` is a truth
//! value"*, and that is a **hypothesis**, not a step: `⟦Prop⟧` is
//! [`crate::anchor::falsity::truth_values`], the same `U₀` the tower hands back
//! ([`Tower::u0`](crate::tower::Tower::u0) is literally that term), so
//! `app(app(r,y),x) ∈ ⟦Prop⟧` is what a caller holding `r : α → α → Prop`
//! already has and is stated here in this crate's own vocabulary.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀r ∀y ∀x. ((y ∈ A ∧ (x ∈ A ∧ app(app(r,y),x) ∈ ⟦Prop⟧))
//!                   → ep(rel_graph(A,r), y, x) = app(app(r,y),x))
//! ```
//!
//! The antecedent is `pair_in_graph`'s own, one atom longer and in its order —
//! deliberately, because the caller that owes this equation is the caller that
//! owes that theorem, and it assembles the conjunction once.
//!
//! # Both bridges, and it is the only place that wants both
//!
//! §24's rule is *which side of the implication the consumer stands on*. Here
//! the consumer stands on **both**, because an equality of two sets is two
//! inclusions:
//!
//! | direction | what is held | bridge |
//! |---|---|---|
//! | `z ∈ ep(R̄,y,x) → z ∈ ⟦r y x⟧` | the pair, out of `edge_prop` | [`graph_pair`](crate::quot::graph::graph_pair) |
//! | `z ∈ ⟦r y x⟧ → z ∈ ep(R̄,y,x)` | the pair is owed | [`pair_in_graph`](crate::quot::graph::pair_in_graph) |
//!
//! That is what §25 item 1 predicted for this one statement and it is the only
//! statement in the project for which it holds: every other consumer of the
//! graph is an implication and stands on one side of it.
//!
//! **And the two directions do not cost the same.** The forward one is
//! *unconditional* — `edge_prop` hands over `z ∈ 1` and the pair, `graph_pair`
//! turns the pair into `• ∈ ⟦r y x⟧`, and [`Sums::unit_eta`](crate::sums::Sums) turns `z ∈ 1` into
//! `z = •`; the hypotheses are never touched. All three atoms of the antecedent
//! are spent in the **backward** direction only: `y ∈ A` and `x ∈ A` by
//! `pair_in_graph`, and `⟦r y x⟧ ∈ ⟦Prop⟧` by
//! [`crate::anchor::falsity::prop_subsingleton`], which is
//! what recovers `z = •` from `z ∈ ⟦r y x⟧` — the step with no analogue on the
//! way out, because a conditional singleton's subsingleton-ness is visible in
//! its own defining biconditional and an arbitrary truth value's is not.
//!
//! # Non-vacuity
//!
//! An equation between two sets is refutable by exhibiting a member of one that
//! is not a member of the other, so there is no `f := ∅` reading to rule out.
//! What *is* worth ruling out is the antecedent being unsatisfiable, and
//! `tests/rec_acc.rs` does it by instantiating at a relation that genuinely
//! holds and one that genuinely does not, and reading `1` and `0` off the two
//! results — three cases and not two, because a pair `⟨y,x⟩` outside `A × A`
//! is a third: the graph is a subset of `A²`, so the equation is *false* there
//! unless `⟦r y x⟧` is empty, and that is exactly what `y ∈ A` and `x ∈ A` buy.
//!
//! # The four input checks are a second layer, and that was measured
//!
//! `tests/rec_acc.rs`'s refusal test was mutated against each guard in turn.
//! **Only [`crate::all_unconditional`] is load-bearing**: a hypothetical input
//! rides its `Γ` through every [`Thm::mp`] below into a theorem still labelled
//! `⊢ …`, and nothing else notices. The three *shape* checks — on `ep_ax`,
//! `graph_pair` and `pair_in_graph` — fail no test when removed, because the
//! derivation is already self-checking: the very next step against each of
//! them is a [`crate::syl`] or [`crate::hyp_mp`] whose own
//! shape agreement is release-live and rejects a foreign pairing, a swapped
//! bridge pair and a permuted antecedent alike.
//!
//! They are **kept** rather than deleted, and the reason is which layer is
//! *intentional*. Each check owns exactly one input and fires before anything
//! is spent on it, so a misuse is a `None` that names the argument; the `syl`
//! failures are incidental to the route this proof happens to take and a
//! refactor could walk out from under them. The final `debug_assert_eq!` is
//! not a substitute — it is compiled out of release, which is where a
//! `Γ`-carrying input would do its damage.
//!
//! # Nothing here is an axiom
//!
//! One [`Thm::ax_extensionality`], two Leibniz rewrites, the two graph bridges,
//! `edge_prop`, `prop_subsingleton` and the unit type's two facts. No new
//! symbol.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::anchor::falsity::{prop_subsingleton, truth_values};
use crate::quot::graph::RelGraph;
use crate::{
    a1i, all_unconditional, and_left, and_right, conj_of, conj_proj, eq_symm_imp, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

use super::ih::ep_of;

/// `⊢ ∀A ∀r ∀y ∀x. ((y ∈ A ∧ (x ∈ A ∧ app(app(r,y),x) ∈ ⟦Prop⟧))
/// → ep(rel_graph(A,r), y, x) = app(app(r,y),x))`.
///
/// `ep` and `ep_ax` are [`super::ih::edge_prop`]'s pair — on a [`super::Base`]
/// they are the `ep` / `ep_ax` fields — and `graph_pair` / `pair_in_graph` are
/// [`crate::quot::graph`]'s, over the same [`RelGraph`]. All four are taken
/// rather than rederived: the caller that wants this equation holds every one
/// of them already, and rederiving `pair_in_graph` here would mint a second
/// certificate for a theorem the caller is also going to use directly.
///
/// Refuses unless all four are unconditional and each instantiates to the
/// theorem *of this symbol over this pairing* — two symbols minted over
/// different `Sums` give two unrelated `⟨y,x⟩`, and then nothing here is about
/// the caller's relation.
pub fn edge_is_relation_value(
    env: &mut Env,
    g: &RelGraph<'_>,
    ep: FnSym,
    ep_ax: &Thm,
    graph_pair: &Thm,
    pair_in_graph: &Thm,
) -> Option<Thm> {
    if !all_unconditional(&[ep_ax, graph_pair, pair_in_graph]) {
        return None
    }
    let s = g.s;
    let ap = &s.ap;

    let (av, rv, yv, xv, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (a, r, y, x, z) =
        (Term::var(av), Term::var(rv), Term::var(yv), Term::var(xv), Term::var(zv));

    let graph = g.of(&a, &r);
    let edge = ep_of(ep, graph.clone(), y.clone(), x.clone());
    let value = ap.apply(ap.apply(r.clone(), y.clone()), x.clone());
    let pt = s.point();
    let one = s.unit();

    let pair_mem = Formula::mem(ap.sets.pair(y.clone(), x.clone()), graph.clone());
    let mem_ze = Formula::mem(z.clone(), edge.clone());
    let mem_z1 = Formula::mem(z.clone(), one.clone());
    let mem_zv = Formula::mem(z.clone(), value.clone());
    let holds = Formula::mem(pt.clone(), value.clone());

    // ── the three inputs, each pinned at the instance this proof uses ────────
    let at = inst_all(ep_ax, &[graph.clone(), y.clone(), x.clone(), z.clone()])?;
    if *at.concl() != Formula::iff(mem_ze.clone(), Formula::and(mem_z1.clone(), pair_mem.clone())) {
        return None
    }
    let gp = inst_all(graph_pair, &[a.clone(), r.clone(), y.clone(), x.clone()])?;
    if *gp.concl() != Formula::imp(pair_mem.clone(), holds.clone()) {
        return None
    }
    let atoms = [
        Formula::mem(y.clone(), a.clone()),
        Formula::mem(x.clone(), a.clone()),
        Formula::mem(value.clone(), truth_values(s)),
    ];
    let pig_ante = conj_of(&[atoms[0].clone(), atoms[1].clone(), holds.clone()])?;
    let pig = inst_all(pair_in_graph, &[a.clone(), r.clone(), y.clone(), x.clone()])?;
    if *pig.concl() != Formula::imp(pig_ante, pair_mem.clone()) {
        return None
    }
    let h = conj_of(&atoms)?;

    // ── forward: `z ∈ ep(R̄,y,x) → z ∈ ⟦r y x⟧`, with no hypothesis at all ───
    let split = iff_mp(&at)?;
    let k_z1 = syl(&split, &and_left(mem_z1.clone(), pair_mem.clone()))?;
    let k_holds = syl(&syl(&split, &and_right(mem_z1.clone(), pair_mem.clone()))?, &gp)?;
    let unit_eta = inst_all(&s.unit_eta, std::slice::from_ref(&z))?;
    let k_pt_z = syl(&syl(&k_z1, &unit_eta)?, &eq_symm_imp(env, z.clone(), pt.clone()))?;
    let w = env.fresh_var();
    let into_value = Formula::mem(Term::var(w), value.clone());
    // `⊢ • = z → (• ∈ ⟦r y x⟧ → z ∈ ⟦r y x⟧)`.
    let leib = Thm::eq_leibniz(pt.clone(), z.clone(), w, into_value.clone());
    let fwd = hyp_mp(&hyp_mp(&a1i(&leib, mem_ze.clone()), &k_pt_z)?, &k_holds)?;

    // ── backward: under `H ∧ (z ∈ ⟦r y x⟧)`, put the pair into the graph ─────
    let hk = Formula::and(h.clone(), mem_zv.clone());
    let hk_h = and_left(h.clone(), mem_zv.clone());
    let hk_zv = and_right(h.clone(), mem_zv.clone());
    let hk_ya = syl(&hk_h, &conj_proj(&atoms, 0)?)?;
    let hk_xa = syl(&hk_h, &conj_proj(&atoms, 1)?)?;
    let hk_prop = syl(&hk_h, &conj_proj(&atoms, 2)?)?;

    // Proof irrelevance at `⟦r y x⟧` is what pins `z` to the point; this is the
    // step the forward direction has no analogue of.
    let irrel = inst_all(&prop_subsingleton(env, s)?, &[value.clone(), z.clone()])?;
    let hk_z_pt = hyp_mp(&a1i(&irrel, hk.clone()), &hyp_and(&hk_prop, &hk_zv)?)?;
    let hk_pt_z = syl(&hk_z_pt, &eq_symm_imp(env, z.clone(), pt.clone()))?;
    // `⊢ z = • → (z ∈ ⟦r y x⟧ → • ∈ ⟦r y x⟧)`, and the same rewrite into `1`.
    let leib_back = Thm::eq_leibniz(z.clone(), pt.clone(), w, into_value);
    let hk_holds = hyp_mp(&hyp_mp(&a1i(&leib_back, hk.clone()), &hk_z_pt)?, &hk_zv)?;
    let leib_one = Thm::eq_leibniz(pt.clone(), z.clone(), w, Formula::mem(Term::var(w), one));
    let hk_z1 = hyp_mp(
        &hyp_mp(&a1i(&leib_one, hk.clone()), &hk_pt_z)?,
        &a1i(&s.unit_mem, hk.clone()),
    )?;
    let hk_pair = hyp_mp(&a1i(&pig, hk.clone()), &hyp_and(&hk_ya, &hyp_and(&hk_xa, &hk_holds)?)?)?;
    let hk_ze = hyp_mp(&a1i(&iff_mpr(&at)?, hk), &hyp_and(&hk_z1, &hk_pair)?)?;
    let bwd = uncurry(&hk_ze)?;

    // ── Extensionality ──────────────────────────────────────────────────────
    let iff_z = Formula::iff(mem_ze, mem_zv);
    let both = hyp_and(&a1i(&fwd, h.clone()), &bwd)?;
    let all_z = Thm::mp(&Thm::ax_dist(zv, h.clone(), iff_z)?, &Thm::gen(zv, &both))?;
    let ext = inst_all(&Thm::ax_extensionality(env), &[edge.clone(), value.clone()])?;
    let out = syl(&all_z, &ext)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(edge, value)),
        "edge_is_relation_value: unexpected shape"
    );
    Some(gen_all(&[av, rv, yv, xv], &out))
}
