//! **A function on the telescope, transported to the telescope's argument** —
//! `push(t, B) = { ⟨b, app(t, ⟨b,•⟩)⟩ : b ∈ B }`, the inverse of
//! [`super::reindex`]'s `pull`.
//!
//! # The consumer, and the obligation it discharges
//!
//! [`reindex`](super::reindex) carries a function *into* the fibre summand,
//! which is the direction a **constructor** needs: `zoneb`'s nest bottom holds
//! `g ∈ dprod(b, ⟦γ⟧)` and hands [`Ctor::mem`](crate::inductive::Ctor) the
//! pulled `pull(g, T(p⃗))`. A **minor premise quantifies the other side**:
//! [`dep_minor`](crate::inductive::motive::dep_minor) and
//! [`rect_step`](crate::inductive::rect::rect_step) bind a function-typed
//! recursive slot at `fs(Aⱼ, W)` over the fibre summand `Aⱼ = Σ(z::γⱼ)`, a set
//! of *tuples*, while Lean's minor premise binds the same field at
//! `⟦γ → T p⃗⟧`, which `MINI-DESIGN` §12's one-clause `Π` makes `dprod` at a
//! constant fibre over `⟦γ⟧ = β₀(p⃗)`. To *apply* Lean's minor premise to the
//! slot it has bound, a caller must carry the bound `t` the other way — and
//! then show that the constructor built from the carried function is the
//! constructor it started with, which is the round trip.
//!
//! `mini/src/rec_dep.rs`'s `PUSH` decline states the two theorems this file
//! exports, in exactly this spelling, and that decline is what this file
//! closes.
//!
//! # Interface
//!
//! Writing `T(p⃗)` for [`Telescope::ty`] and `β₀(p⃗)` for the single argument
//! type, and with `pull` [`super::reindex`]'s:
//!
//! ```text
//! ⊢ ∀t ∀B ∀b. (b ∈ B → app(push(t,B), b) = app(t, ⟨b,•⟩))                [Push::app]
//! ⊢ ∀p⃗ ∀S ∀t. (t ∈ fs(T(p⃗),S) → push(t, β₀(p⃗)) ∈ fs(β₀(p⃗), S))       [push_in_funspace]
//! ⊢ ∀p⃗ ∀S ∀t. (t ∈ fs(T(p⃗),S) → pull(push(t, β₀(p⃗)), T(p⃗)) = t)      [push_pull_roundtrip]
//! ```
//!
//! [`Push::of`] is the term. **The domain is a parameter**, not read off `t`,
//! for [`Reindex`]'s reason: there is no domain operator in this crate, and
//! taking it as an argument keeps the operation total.
//!
//! [`Push::app`] is telescope-*independent* — `⟨b,•⟩` mentions neither the
//! argument types nor `k` — so one [`Push`] serves every declaration in a run,
//! exactly as one [`Reindex`] does. Only the two keyed theorems below mention a
//! particular [`Telescope`].
//!
//! # The round trip is the consumer's direction, and it is not the cheap one
//!
//! [`super::reindex`]'s decline sized the round trip as `push(pull(g)) = g`
//! and as *one* [`crate::ext::funspace_ext`]. Both halves needed correcting on
//! contact with the consumer:
//!
//! * **The direction is the other one.** A minor premise binds `t` on the
//!   telescope and pushes it; what has to come back is
//!   `pull(push(t, β₀(p⃗)), T(p⃗)) = t`. `push(pull(g)) = g` is a theorem about
//!   a `g` the minor premise never binds, and nothing asks for it — see
//!   *"What is declined, by name"* below.
//! * **The two directions cost differently, and the equation is used in both
//!   of its directions here.** `push(pull(g)) = g` would be
//!   [`crate::sigma::reindex_at_tuple`] pointwise and nothing else. The
//!   direction the consumer wants reduces at `q` rather than at `⟨b,•⟩`, so it
//!   needs `π₁ q ∈ β₀(p⃗)` ([`Telescope::proj_mem`]`[0]`) to fire `push`'s
//!   *conditional* computation rule, and then [`Telescope::eta`] to turn
//!   `⟨π₁ q, •⟩` back into `q` — two facts the `at_tuple` direction gets for
//!   free from [`Telescope::intro`] and [`Proj::fst`]. Three equations chained
//!   under one hypothesis, not one.
//!
//! # `Push` is also the λ-introduction mini's induction hypothesis needs
//!
//! Downstream of the round trip, `mini`'s walk holds `derived`'s induction
//! hypothesis atom, which at a function-typed slot is **pointwise**
//! ([`ih_at_motive`](crate::inductive::motive::ih_at_motive)):
//! `∀z. (z ∈ Aⱼ → app(v,z) ∈ app(C, app(t,z)))`. What Lean's minor premise
//! wants in that position is a member of `⟦∀z:γ, C (f z)⟧`, a **`dprod`** over
//! `β₀(p⃗)` at a genuinely dependent fibre. That step is a λ-introduction and
//! not a rewrite — `v` carries no `fs` typing in `dep_minor`, so
//! [`push_in_funspace`] cannot fire on it — and it is **not** exported from
//! here, because it already exists: [`crate::ext::lam_in_dprod_n`] takes
//! exactly the quadruple `(body, graph, beta, lam_in_funspace)` this struct
//! stores, which is why [`Push::beta`] is a public field where [`Reindex`]
//! keeps only the unfolded [`Push::app`]-shaped form. Fed `Push`'s quadruple
//! and the caller's own fibre stack it yields
//!
//! ```text
//! ⊢ ∀v ∀A. ((∀z. (z ∈ A → app(v,⟨z,•⟩) ∈ b(q⃗,z))) → push(v,A) ∈ dprod(q⃗,A))
//! ```
//!
//! so the λ-graph the introduction needs **is** `push` itself. See *"What mini
//! must bring"* below for the rest of that quadruple's other half.
//!
//! # What mini must bring
//!
//! For the round trip: a [`Telescope`] of depth one, a [`Reindex`] and a
//! [`Push`] over its own [`Sums`], [`crate::ext::funspace_app_mem`], and
//! [`crate::ext::funspace_ext`]. All four are checked here, not assumed.
//!
//! For the induction hypothesis: its own fibre stack
//! `(b, img, img_ax, dprod, dprod_def)` for `⟦∀z:γ, C (f z)⟧` — which
//! `interp` already builds for any `Π` — and the pointwise body condition,
//! which is `derived`'s ih atom instantiated at `⟨z,•⟩` (well-typed by
//! [`Telescope::intro`]) with one Leibniz step over [`Push::app`] to turn
//! `app(t, ⟨z,•⟩)` into `app(push(t, β₀(p⃗)), z)`, the argument its own fibre
//! symbol is stated at.
//!
//! # What is declined, by name
//!
//! **The other round trip, `push(pull(g, T(p⃗)), β₀(p⃗)) = g`** — one
//! [`crate::ext::funspace_ext`] over [`crate::sigma::reindex_at_tuple`]
//! pointwise, and genuinely the cheap direction, which is what
//! [`super::reindex`]'s decline sized. **Nothing binds a `g` on `β₀(p⃗)` and
//! needs it back.** A consumer would be a site that starts from Lean's own
//! function and returns to it; the constructor path starts there and *stops* at
//! the pulled function ([`crate::inductive::Ctor`] asks no more of it), and the
//! recursor path starts from the telescope's side, which is the direction built
//! here.
//!
//! # Depth one, and exactly why
//!
//! The guard is `betas.len() == 1`, and it is [`super::reindex`]'s guard for
//! [`super::reindex`]'s reason: at `k ≥ 2` the map is a **currying**, not a
//! reindexing, and its typing needs the `dprod` nest that no nest of `fs` can
//! express, because `βᵢ(p⃗, y₀ … y_{i-1})` depends on the earlier components.
//! `SCOPING.md` §12.1's census finds no corpus witness above depth one.
//!
//! # Non-vacuity
//!
//! [`push_in_funspace`] alone is satisfied by `push(t,B) := ∅` at an empty
//! `β₀(p⃗)`. [`Push::app`] rules that out: the pushed function *computes*, at
//! every point of the domain, to the value the original took at that point's
//! tuple. `tests/sigma.rs` pins it at **three** distinct arguments — two would
//! be satisfied by a push that swapped its two arguments' values — and pins the
//! round trip, which is the statement that no information is lost either way.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`], one [`crate::funcs::lambda_n`], the
//! telescope's own introduction, projection and η rules, and the caller's
//! function extensionality. No new symbol beyond the two the lambda apparatus
//! mints.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ext::{lam_in_funspace_n, pointwise};
use crate::funcs::{beta_conditional_n, lambda_n};
use crate::proj::Proj;
use crate::sums::Sums;
use crate::wrec::hyp_eq_trans;
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm, gen_all, hyp_and, hyp_mp, imp_refl,
    inst_all, syl, uncurry,
};

use super::reindex::{app_mem_stmt, reindex_in_funspace, Reindex};
use super::shared::hyp_congr;
use super::Telescope;

/// The push operator: the body abbreviation, the lambda graph, and the facts
/// about them that consumers state without the abbreviation.
///
/// **Independent of the telescope** — `⟨b,•⟩` mentions neither the argument
/// types nor `k` — so one of these serves every declaration in a run. Only
/// [`push_in_funspace`] and [`push_pull_roundtrip`] are keyed by a particular
/// [`Telescope`].
pub struct Push {
    /// `Q(t,b) = app(t, ⟨b,•⟩)`, arity 2 — the lambda's body.
    pub body: FnSym,
    /// `⊢ ∀t ∀b. Q(t,b) = app(t, ⟨b,•⟩)`.
    pub body_ax: Thm,
    /// `push(t, B) = { ⟨b, Q(t,b)⟩ : b ∈ B }`, arity 2.
    pub graph: FnSym,
    /// `⊢ ∀t ∀B ∀y. (y ∈ push(t,B) ↔ ∃b. (b ∈ B ∧ y = ⟨b, Q(t,b)⟩))`.
    pub graph_ax: Thm,
    /// `⊢ ∀t ∀B ∀b. (b ∈ B → app(push(t,B), b) = Q(t,b))` — the computation
    /// rule **over the body symbol**, which is the form
    /// [`crate::ext::lam_in_dprod_n`] pins; [`Push::app`] is the same fact with
    /// `Q` unfolded, and is what everything else wants.
    pub beta: Thm,
    /// `⊢ ∀t ∀B ∀b. (b ∈ B → app(push(t,B), b) = app(t, ⟨b,•⟩))`.
    pub app: Thm,
    /// `⊢ ∀t ∀A ∀C. ((∀b. (b ∈ A → Q(t,b) ∈ C)) → push(t,A) ∈ fs(A,C))` — the
    /// raw lambda typing rule. [`push_in_funspace`] is what consumers want,
    /// and [`crate::ext::lam_in_dprod_n`] is what the dependent fibre wants.
    pub lam_in_funspace: Thm,
}

impl Push {
    /// Mint the two symbols and derive [`Push::app`].
    pub fn new(env: &mut Env, s: &Sums) -> Option<Push> {
        let ap = &s.ap;
        let (tv, bv) = (env.fresh_var(), env.fresh_var());
        let (tt, tb) = (Term::var(tv), Term::var(bv));
        // The tuple is spelled by the telescope's own packer, so that a change
        // to how a depth-one telescope packs its argument breaks the build here
        // rather than at a caller.
        let value = ap.apply(tt, Telescope::tuple_of(s, std::slice::from_ref(&tb)));
        let (body, body_ax) = define_abbrev(env, &[tv, bv], &value)?;
        let (graph, graph_ax) = lambda_n(env, ap, body)?;
        let beta = beta_conditional_n(env, ap, body, graph, &graph_ax)?;
        let lam_in_funspace = lam_in_funspace_n(env, ap, &s.prod, &s.fs, body, graph, &graph_ax)?;

        // ── unfold `Q` out of the computation rule ──────────────────────────
        let (tv, dv, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tt, td, tb) = (Term::var(tv), Term::var(dv), Term::var(bv));
        let at = inst_all(&beta, &[tt.clone(), td.clone(), tb.clone()])?;
        let unfold = inst_all(&body_ax, &[tt.clone(), tb.clone()])?;
        let mem_b = Formula::mem(tb.clone(), td.clone());
        let out = hyp_eq_trans(env, &at, &a1i(&unfold, mem_b.clone()))?;
        let want = Formula::imp(
            mem_b,
            Formula::eq(
                ap.apply(Term::apply(graph, vec![tt.clone(), td]), tb.clone()),
                ap.apply(tt, Telescope::tuple_of(s, std::slice::from_ref(&tb))),
            ),
        );
        if *out.concl() != want {
            return None
        }
        Some(Push {
            body,
            body_ax,
            graph,
            graph_ax,
            beta,
            app: gen_all(&[tv, dv, bv], &out),
            lam_in_funspace,
        })
    }

    /// The term `push(t, B)`.
    pub fn of(&self, t: Term, b: Term) -> Term { Term::apply(self.graph, vec![t, b]) }
}

/// `⊢ ∀p⃗ ∀S ∀t. (t ∈ fs(T(p⃗), S) → push(t, β₀(p⃗)) ∈ fs(β₀(p⃗), S))` — **a
/// function on the telescope is a function on the telescope's argument**.
///
/// `app_mem` must be [`crate::ext::funspace_app_mem`] over the same [`Sums`];
/// it is checked. `None` unless `tel` has depth exactly one — see the module
/// header for why `k ≥ 2` is a currying and not this.
///
/// The mirror of [`crate::sigma::reindex_in_funspace`], with
/// [`Telescope::intro`] where [`Telescope::proj_mem`]`[0]` stands there:
/// `⟨b,•⟩ ∈ T(p⃗)` for `b ∈ β₀(p⃗)` puts `app(t, ⟨b,•⟩)` in `S`, which is the
/// body condition [`crate::ext::lam_in_funspace_n`] asks for.
pub fn push_in_funspace(
    env: &mut Env,
    s: &Sums,
    tel: &Telescope,
    px: &Push,
    app_mem: &Thm,
) -> Option<Thm> {
    if tel.betas.len() != 1 {
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

    let (sv, tv, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, tt, tb) = (Term::var(sv), Term::var(tv), Term::var(bv));
    let tup = Telescope::tuple_of(s, std::slice::from_ref(&tb));

    let h = Formula::mem(tt.clone(), s.fs.of(ty.clone(), ts.clone()));
    let mem_b = Formula::mem(tb.clone(), beta0.clone());
    let k = Formula::and(h.clone(), mem_b.clone());
    let k_h = and_left(h.clone(), mem_b.clone());
    let k_b = and_right(h.clone(), mem_b.clone());

    // `b ∈ β₀(p⃗) → ⟨b,•⟩ ∈ T(p⃗)`, then `app(t, ⟨b,•⟩) ∈ S`.
    //
    // The shape comparison on `intro` is a **specification pin**, not a
    // reachable failure: it is the one mechanical link between this file's
    // `⟨b,•⟩` and the tuple a depth-one [`Telescope`] introduces.
    let mut intro_args = ps.clone();
    intro_args.push(tb.clone());
    let intro = inst_all(&tel.intro, &intro_args)?;
    if *intro.concl() != Formula::imp(mem_b.clone(), Formula::mem(tup.clone(), ty.clone())) {
        return None
    }
    let k_tup = syl(&k_b, &intro)?;
    let am = inst_all(app_mem, &[ty.clone(), ts.clone(), tt.clone(), tup.clone()])?;
    let k_val = hyp_mp(&a1i(&am, k.clone()), &hyp_and(&k_h, &k_tup)?)?;

    // …which is `Q(t,b) ∈ S`, the body condition.
    let bx = inst_all(&px.body_ax, &[tt.clone(), tb.clone()])?;
    let body_b = Term::apply(px.body, vec![tt.clone(), tb.clone()]);
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ap.apply(tt.clone(), tup),
        body_b.clone(),
        hole,
        Formula::mem(Term::var(hole), ts.clone()),
    );
    let k_body = hyp_mp(&a1i(&Thm::mp(&leib, &eq_symm(env, &bx)?)?, k.clone()), &k_val)?;

    // Generalise over `b` under `h`, and feed the lambda's own typing rule.
    let inner = Formula::imp(mem_b, Formula::mem(body_b, ts.clone()));
    let h_all =
        Thm::mp(&Thm::ax_dist(bv, h.clone(), inner)?, &Thm::gen(bv, &uncurry(&k_body)?))?;
    let rule = inst_all(&px.lam_in_funspace, &[tt.clone(), beta0.clone(), ts.clone()])?;
    let out = syl(&h_all, &rule)?;

    let want = Formula::imp(h, Formula::mem(px.of(tt, beta0.clone()), s.fs.of(beta0, ts)));
    if *out.concl() != want {
        return None
    }
    let mut quant = tel.outer.clone();
    quant.push(sv);
    quant.push(tv);
    Some(gen_all(&quant, &out))
}

/// `⊢ ∀a ∀b ∀f ∀g. ((f ∈ fs(a,b) ∧ (g ∈ fs(a,b) ∧ pointwise(a,f,g))) → f = g)`
/// — the statement [`push_pull_roundtrip`] requires of the `fun_ext` it is
/// handed.
///
/// Rebuilt rather than assumed, for [`app_mem_stmt`]'s reason: `fun_ext`
/// arrives as a bare `&Thm` and is `mp`-ed against, so a theorem with a sequent
/// hypothesis would ride into a result this file states `⊢ …`.
fn fun_ext_stmt(env: &mut Env, s: &Sums) -> Formula {
    let vs: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let (ta, tb, tf, tg) =
        (Term::var(vs[0]), Term::var(vs[1]), Term::var(vs[2]), Term::var(vs[3]));
    let space = s.fs.of(ta.clone(), tb.clone());
    let pw = pointwise(env, &s.ap, &ta, &tf, &tg);
    let body = Formula::imp(
        Formula::and(
            Formula::mem(tf.clone(), space.clone()),
            Formula::and(Formula::mem(tg.clone(), space), pw),
        ),
        Formula::eq(tf, tg),
    );
    vs.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc))
}

/// `⊢ ∀p⃗ ∀S ∀t. (t ∈ fs(T(p⃗), S) → pull(push(t, β₀(p⃗)), T(p⃗)) = t)` — **the
/// round trip**: pushing a function off the telescope and pulling it back
/// returns it.
///
/// This is the theorem a minor premise's caller needs, and the direction it
/// needs: it binds `t` on `fs(Aⱼ, W)`, hands Lean's minor the pushed function,
/// and then holds a constructor built from `pull(push(t, β₀(p⃗)), T(p⃗))` where
/// the obligation names one built from `t`.
///
/// `rx` and `px` must be minted over the same [`Sums`] as `tel`, `app_mem` must
/// be [`crate::ext::funspace_app_mem`] and `fun_ext`
/// [`crate::ext::funspace_ext`]; all four are checked, the last two by rebuilt
/// statement and the first two by the conclusion comparison below. `None`
/// unless `tel` has depth exactly one.
///
/// Three equations chained under `q ∈ T(p⃗)`, and none of them under the typing
/// hypothesis — the pointwise agreement is unconditional in `t`, and `h` is
/// spent only on the two `fs` memberships [`crate::ext::funspace_ext`] asks
/// for:
///
/// | step | from |
/// |---|---|
/// | `app(pull(push(t,β₀),T), q) = app(push(t,β₀), π₁ q)` | [`Reindex::app`](super::reindex::Reindex::app) |
/// | `app(push(t,β₀), π₁ q) = app(t, ⟨π₁ q, •⟩)` | [`Push::app`] at [`Telescope::proj_mem`]`[0]` |
/// | `app(t, ⟨π₁ q, •⟩) = app(t, q)` | [`Telescope::eta`] |
///
/// Eight arguments because both operators, both keyed theorems' inputs and the
/// extensionality are all checked here rather than assumed; bundling them would
/// hide which of them is the one a caller got wrong.
#[allow(clippy::too_many_arguments)]
pub fn push_pull_roundtrip(
    env: &mut Env,
    s: &Sums,
    proj: &Proj,
    tel: &Telescope,
    rx: &Reindex,
    px: &Push,
    app_mem: &Thm,
    fun_ext: &Thm,
) -> Option<Thm> {
    if tel.betas.len() != 1 {
        return None
    }
    let want = fun_ext_stmt(env, s);
    if !crate::establishes(fun_ext, &want) {
        return None
    }
    let typing_push = push_in_funspace(env, s, tel, px, app_mem)?;
    let typing_pull = reindex_in_funspace(env, s, proj, tel, rx, app_mem)?;

    let ap = &s.ap;
    let ps: Vec<Term> = tel.outer.iter().map(|v| Term::var(*v)).collect();
    let beta0 = Term::apply(tel.betas[0], ps.clone());
    let ty = tel.ty.clone();

    let (sv, tv) = (env.fresh_var(), env.fresh_var());
    let (ts, tt) = (Term::var(sv), Term::var(tv));
    let pushed = px.of(tt.clone(), beta0.clone());
    let pulled = rx.of(pushed.clone(), ty.clone());
    let h = Formula::mem(tt.clone(), s.fs.of(ty.clone(), ts.clone()));

    // ── `h → pushed ∈ fs(β₀,S)`, hence `h → pulled ∈ fs(T,S)` ───────────────
    let mut targs = ps.clone();
    targs.push(ts.clone());
    targs.push(tt.clone());
    let k_push = inst_all(&typing_push, &targs)?;
    let mut rargs = ps.clone();
    rargs.push(ts.clone());
    rargs.push(pushed.clone());
    let k_pull = syl(&k_push, &inst_all(&typing_pull, &rargs)?)?;

    // ── The three equations, under `q ∈ T(p⃗)` and nothing else ──────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let mem_q = Formula::mem(tq.clone(), ty.clone());
    let comp = Telescope::comp_of(ap, proj, 0, tq.clone());

    let e1 = inst_all(&rx.app, &[pushed.clone(), ty.clone(), tq.clone()])?;
    let mut pm_args = ps.clone();
    pm_args.push(tq.clone());
    let e2 = syl(
        &inst_all(&tel.proj_mem[0], &pm_args)?,
        &inst_all(&px.app, &[tt.clone(), beta0, comp.clone()])?,
    )?;
    let e3 = {
        let eta = inst_all(&tel.eta, &pm_args)?;
        let tt2 = tt.clone();
        hyp_congr(env, &eta, move |x| ap.apply(tt2.clone(), x))?
    };
    let e12 = hyp_eq_trans(env, &e1, &e2)?;
    let chain = hyp_eq_trans(env, &e12, &e3)?;
    if *chain.concl()
        != Formula::imp(
            mem_q,
            Formula::eq(ap.apply(pulled.clone(), tq.clone()), ap.apply(tt.clone(), tq)),
        )
    {
        return None
    }
    let pw = Thm::gen(qv, &chain);
    if *pw.concl() != pointwise(env, ap, &ty, &pulled, &tt) {
        return None
    }

    // ── Function extensionality on the two members of `fs(T,S)` ─────────────
    let fx = inst_all(fun_ext, &[ty.clone(), ts, pulled.clone(), tt.clone()])?;
    let all = hyp_and(&k_pull, &hyp_and(&imp_refl(h.clone()), &a1i(&pw, h.clone()))?)?;
    let out = hyp_mp(&a1i(&fx, h.clone()), &all)?;

    let want = Formula::imp(h, Formula::eq(pulled, tt));
    if *out.concl() != want {
        return None
    }
    let mut quant = tel.outer.clone();
    quant.push(sv);
    quant.push(tv);
    Some(gen_all(&quant, &out))
}
