//! **The projections `π₁` and `π₂`**, as set-theoretic term-formers.
//!
//! # Why they are primitives
//!
//! Carneiro's §5.1 fixes the menagerie that general inductive types reduce to,
//! and among its term-formers are
//!
//! ```text
//! e ::= … | Σx : e. e | … | (e, e) | π1 e | π2 e | …
//! ```
//!
//! with the ι rules `π₁(a,b) ≡ a`, `π₂(a,b) ≡ b` and the η rule
//! `(π₁ x, π₂ x) ≡ x`. So the thesis's answer to "how does a term take a packed
//! tuple apart" is **projections**, taken as primitive, not an existential
//! quantifier that says what the components would have been. `derived` had
//! neither: [`crate::opair_fst`] and [`crate::pairs::opair_snd`] are
//! *injectivity theorems* — `⟨a,b⟩ = ⟨c,d⟩ → a = c` — which let a proof compare
//! two pairs but never let a **term** mention a component. This file supplies
//! the term-formers.
//!
//! They are not new axioms. In a set theory the Kuratowski pair's components
//! are definable, and that is all that happens here.
//!
//! # The construction
//!
//! ```text
//! ⋂p     := { x ∈ ⋃p : ∀y. (y ∈ p → x ∈ y) }            Separation on ⋃p
//! π₁ p   := ⋃⋂p
//! π₂ p   := app({p}, π₁ p)
//! ```
//!
//! `π₁` is the textbook definition and its computation rule is one
//! Extensionality: `⋂⟨a,b⟩` is `{a}`, because `{a}` is itself a member of the
//! pair (so every member of the intersection is in it) and `a` is in both
//! members (so it is in the intersection).
//!
//! `π₂` is **not** the textbook definition. The usual one,
//! `⋃{ y ∈ ⋃p : ⋃p ≠ ⋂p → y ∉ ⋂p }`, needs a case split on `a = b` — the pair
//! `⟨a,a⟩` is `{{a}}`, where the "not in the intersection" clause would carve
//! out nothing. That split is avoided entirely by noticing that `{⟨a,b⟩}` *is*
//! a one-point function ([`crate::point_fun`]) whose value at `a` is `b`. So
//! once `π₁` is available, `π₂` is [`crate::point_fun::point_app`] and a
//! congruence, and the degenerate case is handled by the one-point graph's own
//! machinery rather than by hand.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀p ∀x. (x ∈ ⋂p ↔ (x ∈ ⋃p ∧ ∀y. (y ∈ p → x ∈ y)))       [Proj::inter_ax]
//! ⊢ ∀a ∀b. ⋂⟨a,b⟩ = {a}                                     [Proj::inter_pair]
//! ⊢ ∀a ∀b. π₁⟨a,b⟩ = a                                              [Proj::fst]
//! ⊢ ∀a ∀b. π₂⟨a,b⟩ = b                                              [Proj::snd]
//! ⊢ ∀a ∀b. ⟨π₁⟨a,b⟩, π₂⟨a,b⟩⟩ = ⟨a,b⟩                               [Proj::eta]
//! ```
//!
//! All unconditional. Nothing is claimed about `π₁`/`π₂` off the pairs: on a
//! set that is not a Kuratowski pair both return whatever the definitions
//! happen to give, which is exactly the thesis's situation too — its rules
//! `π₁(a,b) ≡ a` are stated at pairs and its η rule at a `p : Σx : α. β`, which
//! every element of a `Σ` is.
//!
//! # Non-vacuity
//!
//! [`Proj::fst`] and [`Proj::snd`] are equations whose two sides are visibly
//! different terms at fresh variables, and [`Proj::eta`] is not derivable from
//! a degenerate reading of either: `tests/proj.rs` checks that `π₁` and `π₂` of
//! the *same* pair give its two *different* components, so no constant function
//! satisfies the interface.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{union_intro, Apply};
use crate::point_fun::PointFun;
use crate::{
    a1i, and_right, gen_all, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, inst_all, opair, singleton, syl,
};

/// The projection symbols and everything derived about them.
pub struct Proj {
    /// The symbol `⋂p`.
    pub inter: FnSym,
    /// `⊢ ∀p ∀x. (x ∈ ⋂p ↔ (x ∈ ⋃p ∧ ∀y. (y ∈ p → x ∈ y)))`.
    pub inter_ax: Thm,
    /// `⊢ ∀a ∀b. ⋂⟨a,b⟩ = {a}`.
    pub inter_pair: Thm,
    /// `⊢ ∀a ∀b. π₁⟨a,b⟩ = a`.
    pub fst: Thm,
    /// `⊢ ∀a ∀b. π₂⟨a,b⟩ = b`.
    pub snd: Thm,
    /// `⊢ ∀a ∀b. ⟨π₁⟨a,b⟩, π₂⟨a,b⟩⟩ = ⟨a,b⟩` — the thesis's η rule, at a pair.
    pub eta: Thm,
}

/// The term `⋂p`.
pub fn inter_of(inter: FnSym, p: Term) -> Term { Term::apply(inter, vec![p]) }

/// The term `π₁ p = ⋃⋂p`.
pub fn fst_of(ap: &Apply, inter: FnSym, p: Term) -> Term {
    ap.sets.union_of(inter_of(inter, p))
}

/// The term `π₂ p = app({p}, π₁ p)`.
pub fn snd_of(ap: &Apply, inter: FnSym, p: Term) -> Term {
    let first = fst_of(ap, inter, p.clone());
    ap.apply(singleton(ap.sets.up, p), first)
}

impl Proj {
    /// The term `⋂p`.
    pub fn inter_of(&self, p: Term) -> Term { inter_of(self.inter, p) }

    /// The term `π₁ p = ⋃⋂p`.
    pub fn fst_of(&self, ap: &Apply, p: Term) -> Term { fst_of(ap, self.inter, p) }

    /// The term `π₂ p = app({p}, π₁ p)`.
    pub fn snd_of(&self, ap: &Apply, p: Term) -> Term { snd_of(ap, self.inter, p) }

    /// Introduce `⋂` and derive both computation rules.
    ///
    /// `pf` must be the [`PointFun`] built over the *same* [`Apply`]: `π₂` is
    /// its `point_app` and nothing else, so a second copy would speak of a
    /// different pairing.
    pub fn new(env: &mut Env, ap: &Apply, pf: &PointFun) -> Option<Proj> {
        let (inter, inter_ax) = intersection(env, ap)?;
        let inter_pair = inter_pair(env, ap, inter, &inter_ax)?;
        let fst = fst_pair(env, ap, inter, &inter_pair)?;
        let snd = snd_pair(env, ap, inter, pf, &fst)?;
        let eta = eta_pair(env, ap, inter, &fst, &snd)?;
        Some(Proj { inter, inter_ax, inter_pair, fst, snd, eta })
    }
}

/// `⋂p := { x ∈ ⋃p : ∀y. (y ∈ p → x ∈ y) }`, with
/// `⊢ ∀p ∀x. (x ∈ ⋂p ↔ (x ∈ ⋃p ∧ ∀y. (y ∈ p → x ∈ y)))`.
///
/// Separation on `⋃p`, which is the right bound: every member of every member
/// of `p` is there. For `p = ∅` this gives `⋂∅ = ∅` rather than the proper
/// class of all sets, which is the standard convention and the only one a
/// total operation can have.
fn intersection(env: &mut Env, ap: &Apply) -> Option<(FnSym, Thm)> {
    let (pv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tx, ty) = (Term::var(pv), Term::var(xv), Term::var(yv));
    let psi = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty, tp.clone()),
            Formula::mem(tx.clone(), Term::var(yv)),
        ),
    );
    let up = ap.sets.union_of(tp.clone());
    let existence = crate::funcs::separation_full(env, xv, &psi, &up, &ap.empty_ax).ok()?;
    let guard = Formula::and(Formula::mem(tx, up), psi);
    crate::define_by_membership(env, &[pv], &existence, xv, &guard)
}

/// `⊢ ∀a ∀b. ⋂⟨a,b⟩ = {a}` — **the intersection of a Kuratowski pair**.
///
/// One Extensionality. Forward: `{a}` is a member of `⟨a,b⟩ = {{a},{a,b}}`, so
/// anything in the intersection is in `{a}`. Backward: `a` is in `{a}` and in
/// `{a,b}`, which by the unordered pair's membership condition are the only two
/// members of `⟨a,b⟩`; and `a ∈ ⋃⟨a,b⟩` because `a ∈ {a} ∈ ⟨a,b⟩`.
fn inter_pair(env: &mut Env, ap: &Apply, inter_sym: FnSym, inter_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (av, bv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tx, ty) = (Term::var(av), Term::var(bv), Term::var(xv), Term::var(yv));
    let up = ap.sets.up;
    let sa = singleton(up, ta.clone());
    let sab = Term::apply(up, vec![ta.clone(), tb.clone()]);
    let pair = opair(up, ta.clone(), tb.clone());
    let inter = inter_of(inter_sym, pair.clone());

    // `{a} ∈ ⟨a,b⟩` and `{a,b} ∈ ⟨a,b⟩`.
    let (sa_in, _) = crate::upair_members(&ap.sets.up_ax, &sa, &sab)?;
    // `a ∈ {a}` and `a ∈ {a,b}`.
    let (a_in_sa, _) = crate::upair_members(&ap.sets.up_ax, &ta, &ta)?;
    let (a_in_sab, _) = crate::upair_members(&ap.sets.up_ax, &ta, &tb)?;

    let ax = inst_all(inter_ax, &[pair.clone(), tx.clone()])?;
    let body = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), pair.clone()),
            Formula::mem(tx.clone(), ty.clone()),
        ),
    );
    let mem_up = Formula::mem(tx.clone(), ap.sets.union_of(pair.clone()));
    if *ax.concl()
        != Formula::iff(
            Formula::mem(tx.clone(), inter.clone()),
            Formula::and(mem_up.clone(), body.clone()),
        )
    {
        return None
    }

    // ── Forward: `x ∈ ⋂⟨a,b⟩ → x ∈ {a}` ────────────────────────────────────
    let fwd = {
        let all = syl(&iff_mp(&ax)?, &and_right(mem_up.clone(), body.clone()))?;
        let at_sa = syl(&all, &Thm::ax_inst(body.clone(), sa.clone())?)?;
        hyp_mp(&at_sa, &a1i(&sa_in, Formula::mem(tx.clone(), inter.clone())))?
    };

    // ── Backward: `x ∈ {a} → x ∈ ⋂⟨a,b⟩` ───────────────────────────────────
    let bwd = {
        // `a ∈ ⋃⟨a,b⟩`, via `{a}`.
        let a_in_up = Thm::mp(
            &union_intro(env, &ap.sets, pair.clone(), sa.clone(), ta.clone()).ok()?,
            &crate::and_intro(&sa_in, &a_in_sa),
        )?;
        // `∀y. (y ∈ ⟨a,b⟩ → a ∈ y)`: the two members, one at a time.
        let ymem = Formula::mem(ty.clone(), pair.clone());
        let disj = iff_mp(&inst_all(&ap.sets.up_ax, &[sa.clone(), sab.clone(), ty.clone()])?)?;
        let leg = |env: &mut Env, v: &Term, mem: &Thm| -> Option<Thm> {
            let hole = env.fresh_var();
            let leib = Thm::eq_leibniz(
                v.clone(),
                ty.clone(),
                hole,
                Formula::mem(ta.clone(), Term::var(hole)),
            );
            let eq = Formula::eq(ty.clone(), v.clone());
            let back = syl(&crate::eq_symm_imp(env, ty.clone(), v.clone()), &leib)?;
            hyp_mp(&back, &a1i(mem, eq))
        };
        let l = leg(env, &sa, &a_in_sa)?;
        let r = leg(env, &sab, &a_in_sab)?;
        let at_y = hyp_or_elim(&disj, &a1i(&l, ymem.clone()), &a1i(&r, ymem.clone()))?;
        let all = Thm::gen(yv, &at_y);
        if *all.concl() != body.clone().subst(xv, &ta) {
            return None
        }
        // Now transport from `a` to `x` along `x = a`.
        let a_side = Thm::mp(
            &iff_mpr(&inst_all(inter_ax, &[pair.clone(), ta.clone()])?)?,
            &crate::and_intro(&a_in_up, &all),
        )?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            ta.clone(),
            tx.clone(),
            hole,
            Formula::mem(Term::var(hole), inter.clone()),
        );
        let x_eq_a = iff_mp(&inst_all(&ap.mem_sing, &[ta.clone(), tx.clone()])?)?;
        let a_eq_x = syl(&x_eq_a, &crate::eq_symm_imp(env, tx.clone(), ta.clone()))?;
        hyp_mp(
            &syl(&a_eq_x, &leib)?,
            &a1i(&a_side, Formula::mem(tx.clone(), sa.clone())),
        )?
    };

    let same = Thm::gen(xv, &crate::and_intro(&fwd, &bwd));
    let out = Thm::mp(&inst_all(&ext, &[inter.clone(), sa.clone()])?, &same)?;
    if *out.concl() != Formula::eq(inter, sa) {
        return None
    }
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀a ∀b. π₁⟨a,b⟩ = a` — **the first projection computes**.
///
/// [`inter_pair`] and [`crate::union_singleton`]: `⋃⋂⟨a,b⟩ = ⋃{a} = a`.
fn fst_pair(env: &mut Env, ap: &Apply, inter_sym: FnSym, inter_pair: &Thm) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let pair = opair(ap.sets.up, ta.clone(), tb.clone());
    let at = inst_all(inter_pair, &[ta.clone(), tb.clone()])?;
    let lift = congr_ctx(env, &at, |q| ap.sets.union_of(q))?;
    let us = inst_all(&ap.union_sing, std::slice::from_ref(&ta))?;
    let out = crate::eq_trans(env, &lift, &us)?;
    if *out.concl() != Formula::eq(fst_of(ap, inter_sym, pair), ta.clone()) {
        return None
    }
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀a ∀b. π₂⟨a,b⟩ = b` — **the second projection computes**.
///
/// `π₂ p` is `app({p}, π₁ p)`; rewriting `π₁⟨a,b⟩` to `a` leaves
/// `app({⟨a,b⟩}, a)`, which is [`crate::point_fun::point_app`]. No case split
/// on `a = b`: the one-point graph is single-valued whether or not the pair is
/// degenerate, so `{⟨a,a⟩}` computes just as `{⟨a,b⟩}` does.
fn snd_pair(env: &mut Env, ap: &Apply, inter_sym: FnSym, pf: &PointFun, fst: &Thm) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let pair = opair(ap.sets.up, ta.clone(), tb.clone());
    let sing = singleton(ap.sets.up, pair.clone());

    let at = inst_all(fst, &[ta.clone(), tb.clone()])?;
    let lift = congr_ctx(env, &at, |q| ap.apply(sing.clone(), q))?;
    let pa = inst_all(&pf.app, &[ta.clone(), tb.clone()])?;
    let out = crate::eq_trans(env, &lift, &pa)?;
    if *out.concl() != Formula::eq(snd_of(ap, inter_sym, pair), tb.clone()) {
        return None
    }
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀a ∀b. ⟨π₁⟨a,b⟩, π₂⟨a,b⟩⟩ = ⟨a,b⟩` — the thesis's η rule at a pair.
fn eta_pair(env: &mut Env, ap: &Apply, inter_sym: FnSym, fst: &Thm, snd: &Thm) -> Option<Thm> {
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let pair = opair(ap.sets.up, ta.clone(), tb.clone());
    let f = inst_all(fst, &[ta.clone(), tb.clone()])?;
    let s = inst_all(snd, &[ta.clone(), tb.clone()])?;
    let e1 = congr_ctx(env, &f, |q| {
        ap.sets.pair(q, snd_of(ap, inter_sym, pair.clone()))
    })?;
    let e2 = congr_ctx(env, &s, |q| ap.sets.pair(ta.clone(), q))?;
    let out = crate::eq_trans(env, &e1, &e2)?;
    if *out.concl()
        != Formula::eq(
            ap.sets.pair(fst_of(ap, inter_sym, pair.clone()), snd_of(ap, inter_sym, pair.clone())),
            pair,
        )
    {
        return None
    }
    Some(gen_all(&[av, bv], &out))
}

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
fn congr_ctx<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}
