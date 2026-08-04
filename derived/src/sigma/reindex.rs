//! **A function on a telescope's argument, transported to the telescope** —
//! `pull(g, D) = { ⟨q, app(g, π₁ q)⟩ : q ∈ D }`.
//!
//! # The consumer, and the obligation it discharges
//!
//! `#37`'s general fibre makes a constructor's function-typed recursive
//! argument land in `fs(Σ(z::γⱼ), ind(p⃗))` —
//! [`Ctor::mem`](crate::inductive::Ctor) says exactly that, over
//! [`carrier::fibre_summands`](crate::inductive::carrier::fibre_summands)'s
//! `Aⱼ = Σ(z::γⱼ)`, which is [`Telescope::ty_of`]. **That is not the domain
//! Lean's arrow interprets to.** A field `children : Bool → RTree` interprets
//! over `⟦Bool⟧` itself, while `Σ(z::[Bool])` is a set of *pairs* `⟨b,•⟩`,
//! because a telescope of length `k` bottoms out at `1` so that `k = 0` is not
//! a special case. Different domains, and the constructor cannot be applied
//! until one is carried to the other.
//!
//! **What the caller holds is a `dprod`, not an `fs`, and this header said
//! otherwise.** `MINI-DESIGN` §12 retired the function-space clause from the
//! interpretation: `⟦∀x:α. β⟧` is `dprod` at every `α`, and for a
//! *non-dependent* arrow it is a `dprod` at a **constant fibre**. So the
//! caller's `⟦children⟧` is a member of `dprod(⟦Bool⟧)` and not of
//! `fs(⟦Bool⟧, ind)`, and this file's `reindex_in_funspace` is not applicable
//! to it directly: what stands between them is
//! [`crate::ext::dprod_const_fibre_n`], which says exactly that a `dprod` over
//! a constant fibre **is** the function space — a theorem this crate stores and
//! nothing reads. Whether the composition `dprod_const_fibre_n` then
//! `reindex_in_funspace` gets built is a later question and **its consumer is
//! not yet reached**; what is corrected here is the claim about what mini
//! holds, not the derivation below, which is about `fs` on both sides and is
//! unaffected.
//!
//! `MINI-HANDOFF.md` §26 item 2 measured this and named it: *"`derived/`'s
//! widening made the **carrier** expressible; it did not make the declaration
//! translatable."* This file is the missing step, and it is the direction the
//! constructor needs: **pull a function on `β₀(p⃗)` back along the telescope**,
//! so that the caller's `⟦children⟧` becomes a member of `fs(Σ(z::γ), ind)`.
//!
//! # It is `isum::restrict` at a different reindexing map
//!
//! [`Branch`](crate::isum::Branch) precomposes with `Injⱼ`; this precomposes
//! with `comp₀ = π₁`. Nothing else differs, so the same three existing pieces
//! do the work and no Replacement argument is written twice:
//!
//! | fact | from |
//! |---|---|
//! | `app(pull(g,D), q) = app(g, π₁ q)` for `q ∈ D` | [`crate::funcs::beta_conditional_n`] |
//! | `pull(g,D) ∈ fs(D,S)` when the body lands in `S` | [`crate::ext::lam_in_funspace_n`] |
//! | `π₁ q ∈ β₀(p⃗)` for `q ∈ T(p⃗)` | [`Telescope::proj_mem`]`[0]` |
//!
//! The third is the one that replaces `ISumSyms::inj_mem`, and it is the whole
//! reason the telescope had to export its projections as *memberships* rather
//! than only as term-formers.
//!
//! # Interface
//!
//! Writing `T(p⃗)` for [`Telescope::ty`] and `β₀(p⃗)` for the single argument
//! type:
//!
//! ```text
//! ⊢ ∀g ∀D ∀q. (q ∈ D → app(pull(g,D), q) = app(g, π₁ q))              [Reindex::app]
//! ⊢ ∀p⃗ ∀S ∀g. (g ∈ fs(β₀(p⃗), S) → pull(g, T(p⃗)) ∈ fs(T(p⃗), S))  [reindex_in_funspace]
//! ⊢ ∀p⃗ ∀g ∀b. (b ∈ β₀(p⃗) → app(pull(g, T(p⃗)), ⟨b,•⟩) = app(g, b))  [reindex_at_tuple]
//! ```
//!
//! [`Reindex::of`] is the term. **The domain is a parameter**, not read off
//! `g` — there is no domain operator in this crate — which is
//! [`Branch`](crate::isum::Branch)'s choice for the same reason and keeps the
//! operation total.
//!
//! [`reindex_at_tuple`] is the rule an ι rule wants, and note what it does
//! *not* carry: **no typing hypothesis on `g`**. The computation rule holds at
//! an arbitrary `g`, because `⟨b,•⟩ ∈ T(p⃗)` comes from [`Telescope::intro`] and
//! `π₁⟨b,•⟩ = b` from [`Proj::fst`] — neither asks anything of `g`. That is
//! what makes the pulled function *agree with the field it was pulled from* at
//! every point Lean can name, and hence what the recursor's ι rule would use to
//! decide which `g` the pack holds.
//!
//! # Depth one, and exactly why
//!
//! `k = 1` is a real restriction and it is stated rather than hidden: the guard
//! is `betas.len() == 1`. At `k ≥ 2` the map is not a reindexing at all but an
//! **uncurrying** — Lean's field is a `dprod` nest, one level per `∀z::γ`, and
//! `sup` wants one function out of the packed `Σ`. `SCOPING.md` §12.3 states
//! the general shape. The body abbreviation generalises for free (it would be
//! `app(…app(g, comp₀ q)…, comp_{k-1} q)`, still one arity-2
//! [`crate::define_abbrev`]); what does **not** is the typing, because
//! `Telescope::proj_mem[i]` lands in `βᵢ(p⃗, comp₀ q, …, comp_{i-1} q)`, whose
//! dependence on the earlier components no nest of `fs` can express. So `k ≥ 2`
//! needs the dprod nest, and it is not built here.
//!
//! **And it has no witness.** `SCOPING.md` §12.1's census over all of
//! `vendor/arena-tests` finds exactly two `good/` declarations with a recursive
//! field under a `∀`: `RTree.node` at depth 1, and `Acc.intro` at depth 2 —
//! which takes the thesis's direct `acc` clause and never reaches a W-type. The
//! remaining depth-1s (`indNeg.mk`, `indNegReducible.mk`, `reflOccInIndex.mk`)
//! are `bad/` only. So depth 2 is unreachable today by measurement, not by
//! hope, and building it here would be sizing a construction by a shape nothing
//! asks for.
//!
//! # `push`, the inverse — built, in [`super::push`]
//!
//! **This section declined `push` four times for want of a consumer, and the
//! fourth decline was the round the consumer arrived.** It is now built next
//! door: `push(t, B) = { ⟨b, app(t, ⟨b,•⟩)⟩ : b ∈ B }`, the same shape as this
//! file with [`Telescope::intro`] where [`Telescope::proj_mem`] stands, and its
//! consumer is `mini/src/rec_dep.rs`'s `PUSH` decline — a **minor premise
//! quantifies the side this file's `pull` produces**, so it has to carry its
//! own bound `t` the other way before Lean's minor premise can be applied to
//! it.
//!
//! Two things this section said about it did not survive contact, and both are
//! about the round trip rather than about `push`:
//!
//! * **The direction.** "`push(pull(g)) = g`" is a theorem about a `g` no
//!   consumer binds. What the minor premise needs is
//!   `pull(push(t, β₀(p⃗)), T(p⃗)) = t`, and that direction is *not* the same
//!   derivation read backwards.
//! * **"one [`crate::ext::funspace_ext`] over the two computation rules"** was
//!   right about the extensionality and short by two facts. The consumer's
//!   direction reduces at an arbitrary `q ∈ T(p⃗)` rather than at a tuple, so
//!   it needs [`Telescope::proj_mem`]`[0]` to discharge `push`'s *conditional*
//!   computation rule and [`Telescope::eta`] to turn `⟨π₁ q, •⟩` back into `q`
//!   — three equations chained, where the declined direction would have been
//!   [`reindex_at_tuple`] and nothing else.
//!
//! [`reindex_at_tuple`] remains this file's own computation rule, and the
//! caller-side question this section used to leave open — whether an ι whose
//! right-hand side mentions `pull(g, T(p⃗))` can be reconciled with Lean's
//! β-reduced term at `g` — is answered by
//! [`push_pull_roundtrip`](super::push::push_pull_roundtrip), which is that
//! reconciliation.
//!
//! # The other round trip, built at the next consumer
//!
//! **`push(pull(g, T(p⃗)), β₀(p⃗)) = g`** stood here as declined *"because
//! nothing binds a `g` on `β₀(p⃗)` and needs it back"*, and something does: the
//! **ι rule at a use site**, which holds Lean's own `⟦f⟧`, hands
//! [`crate::inductive::DepRecursor`]'s ι the pulled function its recursive
//! binder is quantified at, and has to recognise the pushed pull in the
//! right-hand side as the `⟦f⟧` Lean's own right-hand side names. It is
//! [`pull_push_roundtrip`](super::push::pull_push_roundtrip), in
//! [`super::push`], and the size this section gave it — one
//! [`crate::ext::funspace_ext`] over [`reindex_at_tuple`] pointwise — is the
//! size it turned out to be, which is the one estimate in this section that
//! survived contact.
//!
//! # Non-vacuity
//!
//! [`reindex_in_funspace`] alone is satisfied by `pull(g,D) := ∅` on an empty
//! `T(p⃗)`. [`reindex_at_tuple`] rules that out: it says the pulled function
//! *computes*, at every tuple the telescope's own introduction rule can build,
//! to the value the original took at that tuple's component. `tests/sigma.rs`
//! pins both and instantiates the computation rule at **three** distinct
//! arguments — two would be satisfied by a pulled function that swapped its two
//! arguments' values, and that the component comes back out *unpermuted* is the
//! whole content of the reindexing.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`], one [`crate::funcs::lambda_n`], and the
//! telescope's own introduction and projection rules. No new symbol beyond the
//! two the lambda apparatus mints.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ext::lam_in_funspace_n;
use crate::funcs::{beta_conditional_n, lambda_n};
use crate::proj::Proj;
use crate::sums::Sums;
use crate::wrec::hyp_eq_trans;
use crate::{
    a1i, and_left, and_right, congr_arg, define_abbrev, eq_symm, gen_all, hyp_and, hyp_mp,
    inst_all, syl, uncurry,
};

use super::Telescope;

/// The reindexing operator: the body abbreviation, the lambda graph, and the
/// two facts about them stated without the abbreviation.
///
/// **Independent of the telescope** — `π₁ q` mentions neither the argument
/// types nor `k` — so one of these serves every declaration in a run, exactly
/// as one [`Branch`](crate::isum::Branch) per depth serves every arity. Only
/// [`reindex_in_funspace`] is keyed by a particular [`Telescope`].
pub struct Reindex {
    /// `P(g,q) = app(g, π₁ q)`, arity 2 — the lambda's body. Exposed only
    /// because [`Reindex::graph_ax`] and [`Reindex::lam_in_funspace`] are
    /// stated over it.
    pub body: FnSym,
    /// `⊢ ∀g ∀q. P(g,q) = app(g, π₁ q)`.
    pub body_ax: Thm,
    /// `pull(g, D) = { ⟨q, P(g,q)⟩ : q ∈ D }`, arity 2.
    pub graph: FnSym,
    /// `⊢ ∀g ∀D ∀y. (y ∈ pull(g,D) ↔ ∃q. (q ∈ D ∧ y = ⟨q, P(g,q)⟩))`.
    pub graph_ax: Thm,
    /// `⊢ ∀g ∀D ∀q. (q ∈ D → app(pull(g,D), q) = app(g, π₁ q))` — the
    /// abbreviation already unfolded.
    pub app: Thm,
    /// `⊢ ∀g ∀D ∀S. ((∀q. (q ∈ D → P(g,q) ∈ S)) → pull(g,D) ∈ fs(D,S))` — the
    /// raw lambda typing rule, over the body symbol.
    /// [`reindex_in_funspace`] is what consumers want.
    pub lam_in_funspace: Thm,
}

impl Reindex {
    /// Mint the two symbols and derive [`Reindex::app`].
    pub fn new(env: &mut Env, s: &Sums, proj: &Proj) -> Option<Reindex> {
        let ap = &s.ap;
        let (gv, qv) = (env.fresh_var(), env.fresh_var());
        let (tg, tq) = (Term::var(gv), Term::var(qv));
        let value = ap.apply(tg, proj.fst_of(ap, tq));
        let (body, body_ax) = define_abbrev(env, &[gv, qv], &value)?;
        let (graph, graph_ax) = lambda_n(env, ap, body)?;
        let beta = beta_conditional_n(env, ap, body, graph, &graph_ax)?;
        let lam_in_funspace = lam_in_funspace_n(env, ap, &s.prod, &s.fs, body, graph, &graph_ax)?;

        // ── unfold `P` out of the computation rule ──────────────────────────
        let (gv, dv, qv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tg, td, tq) = (Term::var(gv), Term::var(dv), Term::var(qv));
        let at = inst_all(&beta, &[tg.clone(), td.clone(), tq.clone()])?;
        let unfold = inst_all(&body_ax, &[tg.clone(), tq.clone()])?;
        let mem_q = Formula::mem(tq.clone(), td.clone());
        let out = hyp_eq_trans(env, &at, &a1i(&unfold, mem_q.clone()))?;
        let want = Formula::imp(
            mem_q,
            Formula::eq(
                ap.apply(Term::apply(graph, vec![tg.clone(), td]), tq.clone()),
                ap.apply(tg, proj.fst_of(ap, tq)),
            ),
        );
        if *out.concl() != want {
            return None
        }
        Some(Reindex {
            body,
            body_ax,
            graph,
            graph_ax,
            app: gen_all(&[gv, dv, qv], &out),
            lam_in_funspace,
        })
    }

    /// The term `pull(g, D)`.
    pub fn of(&self, g: Term, d: Term) -> Term { Term::apply(self.graph, vec![g, d]) }
}

/// `⊢ ∀A ∀B ∀f ∀x. ((f ∈ fs(A,B) ∧ x ∈ A) → app(f,x) ∈ B)` — the statement
/// [`reindex_in_funspace`] and [`super::push::push_in_funspace`] require of the
/// `app_mem` they are handed.
///
/// Rebuilt rather than assumed, for the reason
/// [`crate::isum::restrict`]'s twin gives: `app_mem` arrives as a bare `&Thm`
/// and is `mp`-ed against below, so a theorem with a sequent hypothesis would
/// ride into a result this file states `⊢ …`.
///
/// Shared with [`super::push`] rather than written twice, so that the two
/// inverse operations cannot come to require different `app_mem`s.
pub(super) fn app_mem_stmt(env: &mut Env, s: &Sums) -> Formula {
    let vs: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let (ta, tb, tf, tx) =
        (Term::var(vs[0]), Term::var(vs[1]), Term::var(vs[2]), Term::var(vs[3]));
    let body = Formula::imp(
        Formula::and(
            Formula::mem(tf.clone(), s.fs.of(ta.clone(), tb.clone())),
            Formula::mem(tx.clone(), ta),
        ),
        Formula::mem(s.ap.apply(tf, tx), tb),
    );
    vs.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc))
}

/// `⊢ ∀p⃗ ∀S ∀g. (g ∈ fs(β₀(p⃗), S) → pull(g, T(p⃗)) ∈ fs(T(p⃗), S))` — **a
/// function on the telescope's argument is a function on the telescope**.
///
/// `app_mem` must be [`crate::ext::funspace_app_mem`] over the same [`Sums`];
/// it is checked. `None` unless `tel` has depth exactly one — see the module
/// header for why `k ≥ 2` is an uncurrying and not this.
///
/// Two steps and no case analysis, mirroring
/// [`branch_in_funspace`](crate::isum::branch_in_funspace): `π₁ q ∈ β₀(p⃗)` for
/// `q ∈ T(p⃗)` ([`Telescope::proj_mem`]`[0]`) puts `app(g, π₁ q)` in `S`, which
/// is the body condition [`crate::ext::lam_in_funspace_n`] asks for.
pub fn reindex_in_funspace(
    env: &mut Env,
    s: &Sums,
    proj: &Proj,
    tel: &Telescope,
    rx: &Reindex,
    app_mem: &Thm,
) -> Option<Thm> {
    if tel.betas.len() != 1 || tel.proj_mem.len() != 1 {
        return None
    }
    let want = app_mem_stmt(env, s);
    if !crate::establishes(app_mem, &want) {
        return None
    }
    let ap = &s.ap;
    let ps: Vec<Term> = tel.outer.iter().map(|v| Term::var(*v)).collect();
    let beta0 = Term::apply(tel.betas[0], ps.clone());
    let ty = tel.ty.clone();

    let (sv, gv, qv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, tg, tq) = (Term::var(sv), Term::var(gv), Term::var(qv));

    let h = Formula::mem(tg.clone(), s.fs.of(beta0.clone(), ts.clone()));
    let mem_q = Formula::mem(tq.clone(), ty.clone());
    let k = Formula::and(h.clone(), mem_q.clone());
    let k_h = and_left(h.clone(), mem_q.clone());
    let k_q = and_right(h.clone(), mem_q.clone());

    // `q ∈ T(p⃗) → π₁ q ∈ β₀(p⃗)`, then `app(g, π₁ q) ∈ S`.
    let comp = Telescope::comp_of(ap, proj, 0, tq.clone());
    let mut pm_args = ps.clone();
    pm_args.push(tq.clone());
    let k_comp = syl(&k_q, &inst_all(&tel.proj_mem[0], &pm_args)?)?;
    let am = inst_all(app_mem, &[beta0.clone(), ts.clone(), tg.clone(), comp.clone()])?;
    let k_val = hyp_mp(&a1i(&am, k.clone()), &hyp_and(&k_h, &k_comp)?)?;

    // …which is `P(g,q) ∈ S`, the body condition.
    let bx = inst_all(&rx.body_ax, &[tg.clone(), tq.clone()])?;
    let body_q = Term::apply(rx.body, vec![tg.clone(), tq.clone()]);
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ap.apply(tg.clone(), comp),
        body_q.clone(),
        hole,
        Formula::mem(Term::var(hole), ts.clone()),
    );
    let k_body = hyp_mp(&a1i(&Thm::mp(&leib, &eq_symm(env, &bx)?)?, k.clone()), &k_val)?;

    // Generalise over `q` under `h`, and feed the lambda's own typing rule.
    let inner = Formula::imp(mem_q, Formula::mem(body_q, ts.clone()));
    let h_all =
        Thm::mp(&Thm::ax_dist(qv, h.clone(), inner)?, &Thm::gen(qv, &uncurry(&k_body)?))?;
    let rule = inst_all(&rx.lam_in_funspace, &[tg.clone(), ty.clone(), ts.clone()])?;
    let out = syl(&h_all, &rule)?;

    let want =
        Formula::imp(h, Formula::mem(rx.of(tg, ty.clone()), s.fs.of(ty, ts)));
    if *out.concl() != want {
        return None
    }
    let mut quant = tel.outer.clone();
    quant.push(sv);
    quant.push(gv);
    Some(gen_all(&quant, &out))
}

/// `⊢ ∀p⃗ ∀g ∀b. (b ∈ β₀(p⃗) → app(pull(g, T(p⃗)), ⟨b,•⟩) = app(g, b))` — **the
/// pulled function agrees with the one it was pulled from**, at every tuple.
///
/// Unconditional in `g`: neither [`Telescope::intro`] nor [`Proj::fst`] asks
/// anything of it, so this is a statement about the *operation* and not about
/// well-typed inputs. That is what distinguishes it from
/// [`crate::recarg::RecArg::general`]'s computation rules, which cannot be
/// unconditional because they compute *through* a dispatcher whose branches
/// must be functions.
///
/// `None` unless `tel` has depth exactly one, or `rx` was minted over `tel`'s
/// own projections — a second `Proj` means a second `π₁` and then nothing here
/// is about the caller's telescope, which the rebuilt conclusion catches.
pub fn reindex_at_tuple(
    env: &mut Env,
    s: &Sums,
    proj: &Proj,
    tel: &Telescope,
    rx: &Reindex,
) -> Option<Thm> {
    if tel.betas.len() != 1 {
        return None
    }
    let ap = &s.ap;
    let ps: Vec<Term> = tel.outer.iter().map(|v| Term::var(*v)).collect();
    let beta0 = Term::apply(tel.betas[0], ps.clone());
    let ty = tel.ty.clone();

    let (gv, bv) = (env.fresh_var(), env.fresh_var());
    let (tg, tb) = (Term::var(gv), Term::var(bv));
    let tup = Telescope::tuple_of(s, std::slice::from_ref(&tb));
    let mem_b = Formula::mem(tb.clone(), beta0);

    // `b ∈ β₀(p⃗) → ⟨b,•⟩ ∈ T(p⃗)`, then the computation rule at that tuple.
    let mut intro_args = ps;
    intro_args.push(tb.clone());
    let intro = inst_all(&tel.intro, &intro_args)?;
    if *intro.concl() != Formula::imp(mem_b.clone(), Formula::mem(tup.clone(), ty.clone())) {
        return None
    }
    let at = inst_all(&rx.app, &[tg.clone(), ty.clone(), tup.clone()])?;
    let chain = syl(&intro, &at)?;

    // `π₁⟨b,•⟩ = b`, under the same hypothesis.
    let fst = inst_all(&proj.fst, &[tb.clone(), s.point()])?;
    let comp = Telescope::comp_of(ap, proj, 0, tup.clone());
    let cong = congr_arg(env, ap.app, &[tg.clone(), comp], 1, &fst)?;
    let out = hyp_eq_trans(env, &chain, &a1i(&cong, mem_b.clone()))?;

    let want = Formula::imp(
        mem_b,
        Formula::eq(ap.apply(rx.of(tg.clone(), ty), tup), ap.apply(tg, tb)),
    );
    if *out.concl() != want {
        return None
    }
    let mut quant = tel.outer.clone();
    quant.push(gv);
    quant.push(bv);
    Some(gen_all(&quant, &out))
}
