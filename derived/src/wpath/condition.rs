//! The two closure rules, and the symbol they define.
//!
//! # Interface
//!
//! Writing `W` for `W(A,B,u)`, `B(a)` for `app(B,a)` and `Bnd` for the ambient
//! `prod(W, prod(Q,A))`, this file builds
//!
//! ```text
//! path_root(A,B,u,C)  := ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W))
//!                                    → ⟨⟨a,f⟩, ⟨∅,a⟩⟩ ∈ C)          [path_root]
//! path_step(A,B,u,C)  := ∀a ∀f ∀b ∀s ∀x.
//!        (((a ∈ A ∧ f ∈ fs(B(a),W)) ∧ (b ∈ B(a) ∧ ⟨app(f,b), ⟨s,x⟩⟩ ∈ C))
//!                                    → ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩ ∈ C)      [path_step]
//! path_closed(...,C)  := path_root(C) ∧ path_step(C)               [path_closed]
//! path_cond(...,p)    := ∀C. ((C ⊆ Bnd ∧ path_closed(C)) → p ∈ C)   [path_cond]
//!
//! paths(A,B,u,Q) := { p ∈ Bnd : path_cond(A,B,u,Q,p) }
//!
//! ⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths ↔ (p ∈ Bnd ∧ path_cond))            [paths_symbol]
//! ⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths → p ∈ Bnd)                          [paths_subset]
//! ```
//!
//! Callers need none of the derivations below. All four formulas are built here
//! in one place so that every file that mentions one builds *the same* formula:
//! they are compared syntactically throughout [`crate::wpath`], and a second
//! spelling would silently stop matching.
//!
//! # What `paths` is
//!
//! `⟨w, ⟨s,x⟩⟩ ∈ paths` reads *"`s` is a finite path in the tree `w`, and `x` is
//! the constructor label at the node `s` leads to"*. The root path is `∅` and
//! its label is the tree's own tag; a path into the `b`-th subtree is `⟨b,s⟩`
//! where `s` is a path in that subtree. Those are exactly [`path_root`] and
//! [`path_step`], and `paths` is the least set closed under both — the same
//! least-closed-set pattern as [`crate::wtype`] and [`crate::acc`], and one
//! Separation for the same reason: phrasing the intersection as a *condition*
//! over `C` rather than as `⋂{C ∈ 𝒫(Bnd) : …}` means `𝒫(Bnd)` is never needed.
//!
//! # Why the ambient `Q` is a parameter
//!
//! The paths themselves are `∅` and iterated Kuratowski pairs of members of the
//! fibres, so they need *some* set to live in, and which set that is, is not
//! this module's business: `Q` is a free parameter constrained only by
//! [`super::amb`] — `∅ ∈ Q`, every fibre is a subset of `Q`, and `Q` is closed
//! under pairing. Every consumer in this crate takes `Q := tower(S)`, whose
//! three facts are [`crate::cumul`]'s; a consumer with a different ambient set
//! pays nothing for that choice.
//!
//! **`Q` is not a size hypothesis and is not the W-type's bound.** It bounds the
//! *paths*, which are finite objects over the fibres, and never the trees. That
//! is the whole reason this route needs no condition on the fibres: a path is
//! one fibre element at a time, so `Q` is closed under *binary* pairing, where
//! the `ω`-tower's `sup`-closure needed a whole fibre-indexed function to land
//! in one stage — which is [`crate::cumul::bnd`], and is false at an infinite
//! fibre. See [`crate::wpath`]'s header.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{and_left, gen_all, iff_mp, inst_all, opair, syl};

/// The four terms every formula here is stated over, bundled so that a caller
/// spells them once.
///
/// `w` is `W(A,B,u)` and `bnd` is `prod(W, prod(Q,A))`; both are derived from
/// the other four and are carried so that no file rebuilds them differently.
#[derive(Clone)]
pub struct At {
    /// `A`, the tag set.
    pub a: Term,
    /// `B`, the fibre family.
    pub b: Term,
    /// `u`, the W-type's bound.
    pub u: Term,
    /// `Q`, the ambient set the paths live in.
    pub q: Term,
    /// `W(A,B,u)`.
    pub w: Term,
    /// `prod(W, prod(Q,A))` — the set `paths` is Separated out of.
    pub bnd: Term,
}

impl At {
    /// Assemble the derived terms from the four parameters.
    pub fn new(wt: &Wtype, a: Term, b: Term, u: Term, q: Term) -> At {
        let w = wt.of(a.clone(), b.clone(), u.clone());
        let bnd = wt.sums.prod.of(w.clone(), wt.sums.prod.of(q.clone(), a.clone()));
        At { a, b, u, q, w, bnd }
    }

    /// `⟨x,y⟩` over this apparatus' pairing.
    pub fn pair(&self, s: &Sums, x: Term, y: Term) -> Term { opair(s.ap.sets.up, x, y) }
}

/// `∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W)) → ⟨⟨a,f⟩, ⟨∅,a⟩⟩ ∈ C)` — the root rule.
///
/// "Every tree has the empty path, labelled by its own tag."
pub fn path_root(env: &mut Env, s: &Sums, at: &At, c: &Term) -> Formula {
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let guard = Formula::and(
        Formula::mem(ta.clone(), at.a.clone()),
        Formula::mem(tf.clone(), s.fs.of(fibre, at.w.clone())),
    );
    let node = at.pair(s, ta.clone(), tf);
    let entry = at.pair(s, s.zero(), ta);
    Formula::forall(
        av,
        Formula::forall(fv, Formula::imp(guard, Formula::mem(at.pair(s, node, entry), c.clone()))),
    )
}

/// `∀a ∀f ∀b ∀s ∀x. (((a ∈ A ∧ f ∈ fs(B(a),W)) ∧ (b ∈ B(a) ∧ ⟨f(b), ⟨s,x⟩⟩ ∈ C))
/// → ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩ ∈ C)` — the step rule.
///
/// "A path in the `b`-th subtree, prefixed by `b`, is a path in the tree, with
/// the same label."
pub fn path_step(env: &mut Env, s: &Sums, at: &At, c: &Term) -> Formula {
    let (av, fv, bv, sv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tb, ts, tx) =
        (Term::var(av), Term::var(fv), Term::var(bv), Term::var(sv), Term::var(xv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let node = Formula::and(
        Formula::mem(ta.clone(), at.a.clone()),
        Formula::mem(tf.clone(), s.fs.of(fibre.clone(), at.w.clone())),
    );
    let entry = at.pair(s, ts.clone(), tx.clone());
    let prem = Formula::and(
        Formula::mem(tb.clone(), fibre),
        Formula::mem(
            at.pair(s, s.ap.apply(tf.clone(), tb.clone()), entry),
            c.clone(),
        ),
    );
    let concl = Formula::mem(
        at.pair(
            s,
            at.pair(s, ta, tf),
            at.pair(s, at.pair(s, tb, ts), tx),
        ),
        c.clone(),
    );
    let body = Formula::imp(Formula::and(node, prem), concl);
    Formula::forall(
        av,
        Formula::forall(
            fv,
            Formula::forall(bv, Formula::forall(sv, Formula::forall(xv, body))),
        ),
    )
}

/// `path_root(C) ∧ path_step(C)` — "`C` is closed under both path rules".
pub fn path_closed(env: &mut Env, s: &Sums, at: &At, c: &Term) -> Formula {
    let root = path_root(env, s, at, c);
    let step = path_step(env, s, at, c);
    Formula::and(root, step)
}

/// `∀C. ((C ⊆ Bnd ∧ path_closed(C)) → p ∈ C)` — the condition Separation carves
/// `paths` out of `Bnd` with.
pub fn path_cond(env: &mut Env, s: &Sums, at: &At, p: &Term) -> Formula {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let guard = Formula::and(
        kernel::thm::subset(env, tc.clone(), at.bnd.clone()),
        path_closed(env, s, at, &tc),
    );
    Formula::forall(cv, Formula::imp(guard, Formula::mem(p.clone(), tc)))
}

/// Introduce `paths(A,B,u,Q) = { p ∈ prod(W, prod(Q,A)) : path_cond(p) }`, with
/// `⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths ↔ (p ∈ Bnd ∧ path_cond))`.
///
/// One Separation on the ambient product: existence is
/// [`crate::funcs::separation_full`], uniqueness is Extensionality via
/// [`crate::define_by_membership`]. The condition is an ordinary first-order
/// formula in `A`, `B`, `u`, `Q` and `C`, so `paths` is a genuine four-place
/// function symbol rather than a construction parameterised by a formula — the
/// same shape as [`crate::acc::acc_symbol`] and for the same reason.
///
/// `wt` supplies the pairing, the function space and the `W` symbol; every
/// theorem downstream is about *these*, so a second apparatus would produce a
/// second `⟨·,·⟩` and nothing would compose.
///
/// `None` when `wt`'s empty-set axiom carries a hypothesis: the symbol this
/// mints is asserted to satisfy its characteristic theorem outright, and a `Γ`
/// behind the existence proof would make that a lie.
pub fn paths_symbol(env: &mut Env, wt: &Wtype) -> Option<(FnSym, Thm)> {
    let s = wt.sums.clone();
    if !s.ap.empty_ax.hyps().is_empty() {
        return None
    }
    let (av, bv, uv, qv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(
        wt,
        Term::var(av),
        Term::var(bv),
        Term::var(uv),
        Term::var(qv),
    );
    let pv = env.fresh_var();
    let tp = Term::var(pv);

    let cond = path_cond(env, &s, &at, &tp);
    let existence = separation_full(env, pv, &cond, &at.bnd, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tp, at.bnd.clone()), cond);
    crate::define_by_membership(env, &[av, bv, uv, qv], &existence, pv, &guard)
}

/// `⊢ ∀A ∀B ∀u ∀Q ∀p. (p ∈ paths(A,B,u,Q) → p ∈ prod(W, prod(Q,A)))`.
///
/// The left conjunct of the defining biconditional, and nothing more. It is what
/// makes `paths` cheap in the same way [`crate::acc`] is cheap: there is a set
/// to carve out of, so no second bound is a parameter and the typing of every
/// member is free.
///
/// `paths_ax` must **establish** the defining biconditional — the conclusion is
/// pinned below and the sequent must be unconditional, since this header
/// promises `⊢ …` and [`crate::syl`] would otherwise carry a caller's `Γ` in.
pub fn paths_subset(env: &mut Env, wt: &Wtype, paths: FnSym, paths_ax: &Thm) -> Option<Thm> {
    if !paths_ax.hyps().is_empty() {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv, pv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let tp = Term::var(pv);

    let cond = path_cond(env, &s, &at, &tp);
    let mem_bnd = Formula::mem(tp.clone(), at.bnd.clone());
    let term = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
    let ax = inst_all(
        paths_ax,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tp.clone()],
    )?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(tp.clone(), term.clone()),
            Formula::and(mem_bnd.clone(), cond.clone()),
        )
    {
        return None
    }
    let out = syl(&iff_mp(&ax)?, &and_left(mem_bnd.clone(), cond))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(tp, term), mem_bnd),
        "paths_subset: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv, qv, pv], &out))
}
