//! **Graph extensionality for set-functions**: a member of a function space
//! *is* the lambda-graph of its own application.
//!
//! # Interface
//!
//! [`Eta`] introduces one symbol and proves four theorems about it. Writing
//! `graph(f,A)` for the symbol — which is [`crate::funcs::lambda_n`]'s graph
//! over the body `λx. app(f,x)`, i.e. the `lam(A, λx. app(f,x))` a caller means
//! when it asks for eta — they are
//!
//! ```text
//! ⊢ ∀f ∀A ∀z. (z ∈ graph(f,A) ↔ ∃x. (x ∈ A ∧ z = ⟨x, app(f,x)⟩))    [graph_ax]
//! ⊢ ∀f ∀A ∀a. (a ∈ A → app(graph(f,A), a) = app(f,a))                   [beta]
//! ⊢ ∀f ∀A ∀C. ((∀x. (x ∈ A → app(f,x) ∈ C)) → graph(f,A) ∈ fs(A,C))
//!                                                               [in_funspace]
//! ⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))                             [eta]
//! ```
//!
//! The last is the one that was asked for. Callers need none of the derivation
//! below; [`Eta::of`] builds the term `graph(f,A)`.
//!
//! # The spelling, and why the argument order is `graph(f, A)`
//!
//! The requested form was `f = lam(A, λx. app(f,x))`, written as if `lam` took
//! a function as its second argument. It cannot: a graph symbol is introduced
//! by Replacement over a *body symbol*, and a symbol's arity is fixed, so the
//! body `λx. app(f,x)` becomes the parameter `f` in front of the binder — which
//! is exactly [`crate::funcs::lambda_n`]'s parameter prefix, and exactly why
//! that prefixed form exists ([`crate::ext::lam_typing_n`]'s header gives the
//! general argument). The body symbol here is `app` itself, taken at arity 2,
//! so **no new body symbol is declared**: `graph` is `lambda_n` applied to
//! `Apply::app`, and `graph(f,A)` is `{ ⟨x, app(f,x)⟩ : x ∈ A }` on the nose.
//!
//! The `∀A ∀B ∀f` order of the eta theorem is the requested one and matches
//! [`crate::ext::funspace_app_mem`]; the `∀f ∀A` order of the other three is
//! forced, being prefix-then-domain as `lambda_n` produces them.
//!
//! # What it is derived from
//!
//! Not from Extensionality on the two graphs directly — from
//! [`crate::ext::funspace_ext`], the pointwise function extensionality in the
//! neighbouring file, which is where the real work is and where the caution
//! about single-valuedness is discharged. Given that, eta is three short steps:
//!
//! | step | lemma |
//! |---|---|
//! | `f ∈ fs(A,B) → ∀x ∈ A. app(f,x) ∈ B` | [`crate::ext::funspace_app_mem`] |
//! | that, so `graph(f,A) ∈ fs(A,B)` | [`crate::ext::lam_in_funspace_n`] |
//! | `∀x ∈ A. app(f,x) = app(graph(f,A),x)` | [`crate::funcs::beta_conditional_n`] |
//! | the two of them agree pointwise, so they are equal | [`crate::ext::funspace_ext`] |
//!
//! Every one of those already existed; nothing about graphs, products or
//! single-valuedness is rebuilt here.
//!
//! # A consumer with its own graph symbol
//!
//! `checker/src/tg.rs` and the mini-kernel port interpret `λx:A. b` as a graph
//! `lam_C(h⃗,⟦A⟧)` minted per declaration, which is **not** this `graph`. Such a
//! consumer should go to [`crate::ext::funspace_ext`] directly rather than
//! bridge to this theorem: it already has `lam_C(h⃗,A) ∈ fs(A,B)` from
//! [`crate::ext::lam_in_funspace_n`] and `app(lam_C(h⃗,A),x) = t(h⃗,x)` from
//! [`crate::funcs::beta_conditional_n`], and its recursive definitional-equality
//! call supplies `t(h⃗,x) = app(f,x)` on the domain — which is the pointwise
//! hypothesis, assembled from pieces it holds anyway. This file is that same
//! composition at the one body symbol every function has, namely its own `app`.
//!
//! # The empty domain
//!
//! At `A := ∅` the equation reads `f = graph(f,∅)`, and both sides are `∅`:
//! `f ∈ fs(∅,B)` forces `f = ∅` ([`crate::wtype::empty_funspace`]) and the
//! graph over an empty domain collects nothing. Nothing special happens in the
//! derivation — the pointwise hypothesis is vacuous and
//! [`crate::ext::funspace_ext`] does not need it there — and the equation is
//! *not* reflexivity even so, since `graph(f,∅)` is a symbol application and
//! `f` is not. `⊢ ∅ ∈ fs(∅,S)` is [`crate::wtype::empty_is_a_function`], so the
//! antecedent discharges and the instance is a closed theorem; `tests/fun_ext.rs`
//! pins it.
//!
//! Nothing here is trusted. Every theorem handed in is checked — conclusion
//! pinned *and* hypothesis set required to be empty — so a mismatched stack
//! yields `None` rather than a theorem about the wrong symbols.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{beta_conditional_n, lambda_n, Apply};
use crate::funspace::{Funspace, Product};
use crate::{
    a1i, eq_symm_imp, gen_all, hyp_and, hyp_mp, imp_refl, inst_all, syl, uncurry,
};
use super::fun_ext::pointwise;
use super::lam_typing_n::lam_in_funspace_n;

/// The graph `graph(f,A) = { ⟨x, app(f,x)⟩ : x ∈ A }`, with the eta equation
/// and the two facts it is derived through.
///
/// See the module header for the four statements. The symbol is a definitional
/// extension over `ap`'s application, so an `Eta` built against one
/// [`crate::funcs::Apply`] says nothing about any other.
#[derive(Clone)]
pub struct Eta {
    /// The symbol itself, of arity 2: the function first, the domain second.
    pub graph: FnSym,
    /// `⊢ ∀f ∀A ∀z. (z ∈ graph(f,A) ↔ ∃x. (x ∈ A ∧ z = ⟨x, app(f,x)⟩))`.
    pub graph_ax: Thm,
    /// `⊢ ∀f ∀A ∀a. (a ∈ A → app(graph(f,A), a) = app(f,a))` — beta reduction
    /// over the graph, which on the domain is the identity on values.
    pub beta: Thm,
    /// `⊢ ∀f ∀A ∀C. ((∀x. (x ∈ A → app(f,x) ∈ C)) → graph(f,A) ∈ fs(A,C))`.
    pub in_funspace: Thm,
    /// `⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))` — **the eta equation**.
    pub eta: Thm,
}

impl Eta {
    /// Introduce `graph` and prove all four theorems.
    ///
    /// `p` and `fsp` must be the product and function space built over
    /// `ap.sets`; `fun_ext` must be what [`crate::ext::funspace_ext`] produces
    /// for that stack and `app_mem` what [`crate::ext::funspace_app_mem`] does.
    /// All of that is checked rather than assumed, and both theorems handed in
    /// must be hypothesis-free.
    pub fn new(
        env: &mut Env,
        ap: &Apply,
        p: &Product,
        fsp: &Funspace,
        fun_ext: &Thm,
        app_mem: &Thm,
    ) -> Option<Eta> {
        if !fun_ext.hyps().is_empty() || !app_mem.hyps().is_empty() {
            return None
        }
        let (graph, graph_ax) = lambda_n(env, ap, ap.app)?;
        let beta = beta_conditional_n(env, ap, ap.app, graph, &graph_ax)?;
        let in_funspace = lam_in_funspace_n(env, ap, p, fsp, ap.app, graph, &graph_ax)?;
        let eta = funspace_eta(env, ap, fsp, graph, &beta, &in_funspace, fun_ext, app_mem)?;
        Some(Eta { graph, graph_ax, beta, in_funspace, eta })
    }

    /// The term `graph(f, A)`.
    pub fn of(&self, f: Term, a: Term) -> Term { Term::apply(self.graph, vec![f, a]) }
}

/// `⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))` — **the eta equation**.
///
/// A member of a function space is the lambda-graph of its own application.
/// See the module header for the four-line chain; the substance is in
/// [`crate::ext::funspace_ext`], and this is the composition.
///
/// Every theorem handed in is pinned against the statement it is supposed to
/// be, so a mismatched stack yields `None`.
#[allow(clippy::too_many_arguments)]
pub fn funspace_eta(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    graph: FnSym,
    beta: &Thm,
    in_funspace: &Thm,
    fun_ext: &Thm,
    app_mem: &Thm,
) -> Option<Thm> {
    if !beta.hyps().is_empty()
        || !in_funspace.hyps().is_empty()
        || !fun_ext.hyps().is_empty()
        || !app_mem.hyps().is_empty()
    {
        return None
    }
    let (av, bv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(av), Term::var(bv), Term::var(fv));
    let g = Term::apply(graph, vec![tf.clone(), ta.clone()]);

    let h = Formula::mem(tf.clone(), fsp.of(ta.clone(), tb.clone()));

    let x = env.fresh_var();
    let tx = Term::var(x);
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let app_gx = ap.apply(g.clone(), tx.clone());

    // ── H → ∀x. (x ∈ A → app(f,x) ∈ B), the values of a function ─────────────
    let am = inst_all(app_mem, &[ta.clone(), tb.clone(), tf.clone(), tx.clone()])?;
    let values_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), tb.clone()));
    if *am.concl()
        != Formula::imp(
            Formula::and(h.clone(), mem_xa.clone()),
            Formula::mem(app_fx.clone(), tb.clone()),
        )
    {
        return None
    }
    let h_values = Thm::mp(
        &Thm::ax_dist(x, h.clone(), values_body.clone())?,
        &Thm::gen(x, &uncurry(&am)?),
    )?;

    // ── H → graph(f,A) ∈ fs(A,B), by the λ typing rule at C := B ─────────────
    let lam_fs = inst_all(in_funspace, &[tf.clone(), ta.clone(), tb.clone()])?;
    let mem_g = Formula::mem(g.clone(), fsp.of(ta.clone(), tb.clone()));
    if *lam_fs.concl() != Formula::imp(Formula::forall(x, values_body), mem_g.clone()) {
        return None
    }
    let h_mem_g = syl(&h_values, &lam_fs)?;

    // ── H → ∀x. (x ∈ A → app(f,x) = app(graph(f,A),x)), by beta ──────────────
    // Beta gives the equation the other way round, so it is turned about; the
    // hypothesis is not used at all, which is why `a1i` suffices.
    let bt = inst_all(beta, &[tf.clone(), ta.clone(), tx.clone()])?;
    if *bt.concl() != Formula::imp(mem_xa.clone(), Formula::eq(app_gx.clone(), app_fx.clone())) {
        return None
    }
    let bt_sym = syl(&bt, &eq_symm_imp(env, app_gx.clone(), app_fx.clone()))?;
    let pw_body = Formula::imp(mem_xa, Formula::eq(app_fx, app_gx));
    let h_pw = Thm::mp(
        &Thm::ax_dist(x, h.clone(), pw_body.clone())?,
        &Thm::gen(x, &a1i(&bt_sym, h.clone())),
    )?;

    // ── The two agree pointwise and live in the same space, so they are equal ─
    let pw = Formula::forall(x, pw_body);
    if pw != pointwise(env, ap, &ta, &tf, &g) {
        return None
    }
    let fe = inst_all(fun_ext, &[ta.clone(), tb.clone(), tf.clone(), g.clone()])?;
    if *fe.concl()
        != Formula::imp(
            Formula::and(h.clone(), Formula::and(mem_g, pw)),
            Formula::eq(tf.clone(), g.clone()),
        )
    {
        return None
    }
    let out = hyp_mp(
        &a1i(&fe, h.clone()),
        &hyp_and(&imp_refl(h.clone()), &hyp_and(&h_mem_g, &h_pw)?)?,
    )?;

    // Not a `debug_assert`: this is the statement consumers rely on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, Formula::eq(tf, g)) {
        return None
    }
    Some(gen_all(&[av, bv, fv], &out))
}
