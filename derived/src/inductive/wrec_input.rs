//! The **statements** of the two W-recursor theorems this module family takes
//! from its caller, rebuilt so that they can be pinned.
//!
//! # Why this file exists
//!
//! [`super::recursor::GenRecursor::build`] and
//! [`super::family::good::Good::build`] both accept
//! [`crate::wrec_total::iota`] and [`crate::wrec_total::wrec_funspace`] as bare
//! `&Thm`s. That is the right interface — every consumer of a declaration has
//! to run over the *same* [`Recursor`] apparatus, so the theorems are derived
//! once and passed down — but it means the two flagship entries of the general
//! recursor take caller-supplied theorems, and the house rule for that is: read
//! `hyps()`, and pin `concl()`.
//!
//! Reading `hyps()` is one line. Pinning `concl()` was the awkward half, because
//! the theorems are `∀A ∀B ∀u ∀T ∀e. …` over variables `wrec_total` invented
//! and did not hand back, so there was nothing to compare against. Rebuilding
//! the statement here removes the excuse: [`Formula::forall`] closes its body,
//! so a statement built over *fresh* variables is equal — not merely
//! α-equivalent, equal — to the one `wrec_total` returned.
//!
//! # What pinning buys, beyond the house rule
//!
//! A wrong `iota` or `funspace` did already fail closed: it dies at a kernel
//! join deep inside [`super::iota::iota_core`]. But it dies *after*
//! `GenRecursor::build` has minted one Replacement symbol per constructor into
//! the caller's `Env`, so a refusal left the environment permanently larger.
//! Pinning both statements before any symbol is created turns that into a plain
//! `None` with nothing leaked.
//!
//! # Nothing here is a theorem
//!
//! Both functions return a [`Formula`]. Building a formula proves nothing, and
//! a bug in this file can only reject a theorem that should have been accepted
//! — never accept one that should not have been.

use kernel::{Env, Formula, FreeVar, Term};

use crate::wrec_total::{premise, Recursor};
use crate::wtype::Wtype;

/// `∀x⃗. φ`, outermost first — the formula-level [`crate::gen_all`].
fn close_all(xs: &[FreeVar], body: Formula) -> Formula {
    xs.iter().rev().fold(body, |acc, x| Formula::forall(*x, acc))
}

/// The statement of [`crate::wrec_total::wrec_funspace`]:
///
/// ```text
/// ∀A ∀B ∀u ∀T ∀e. ((closed(A,B,u) ∧ step_typed(A,B,u,T,e))
///                     → wrec(A,B,u,T,e) ∈ fs(W(A,B,u), T))
/// ```
///
/// `wt` and `rc` must be the apparatus the theorem is expected to be over: the
/// `wrec` and `W` symbols come from *them*, so a theorem about a second
/// `Recursor`'s `wrec` fails the comparison on the symbol, which is the whole
/// point of comparing at all.
pub(crate) fn wrec_funspace_stmt(env: &mut Env, wt: &Wtype, rc: &Recursor) -> Formula {
    let s = &wt.sums;
    let vars: Vec<FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let w = wt.of(ps[0].clone(), ps[1].clone(), ps[2].clone());
    let rec = rc.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
    let body = Formula::imp(
        premise(env, wt, &ps),
        Formula::mem(rec, s.fs.of(w, ps[3].clone())),
    );
    close_all(&vars, body)
}

/// The hypothesis-free half of [`crate::wrec_total::iota`], at caller-supplied
/// `ps = [A, B, u, T, e]`:
///
/// ```text
/// ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a), W(A,B,u))) →
///     app(wrec,⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩))
/// ```
///
/// This is what is left once the theorem has been instantiated at the five
/// carrier terms and `mp`-ed against `closed ∧ step_typed`, which is how both
/// consumers use it — so it is also what a consumer that *stores* the fired
/// rule (`Good::wrec_iota`) has to pin its field against.
pub(crate) fn wrec_iota_body(env: &mut Env, wt: &Wtype, rc: &Recursor, ps: &[Term]) -> Formula {
    let s = &wt.sums;
    let ap = &s.ap;
    let w = wt.of(ps[0].clone(), ps[1].clone(), ps[2].clone());
    let rec = rc.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);

    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let fibre = ap.apply(ps[1].clone(), ta.clone());
    let guard = Formula::and(
        Formula::mem(ta.clone(), ps[0].clone()),
        Formula::mem(tf.clone(), s.fs.of(fibre.clone(), w)),
    );
    let eq = Formula::eq(
        ap.apply(rec.clone(), ap.sets.pair(ta.clone(), tf.clone())),
        crate::wrec::step_at(ap, rc.comp, &ps[4], &rec, &ta, &tf, &fibre),
    );
    Formula::forall(av, Formula::forall(fv, Formula::imp(guard, eq)))
}

/// The statement of [`crate::wrec_total::iota`]:
///
/// ```text
/// ∀A ∀B ∀u ∀T ∀e. ((closed(A,B,u) ∧ step_typed(A,B,u,T,e)) →
///     ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a), W(A,B,u))) →
///         app(wrec,⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩)))
/// ```
///
/// The inner `∀a ∀f` sits *under* the hypothesis, not outside it, and the
/// right-hand side is [`crate::wrec::step_at`] — the flat Kuratowski triple.
/// Both are load-bearing: this is the exact shape [`super::iota::iota_core`]
/// instantiates and fires, and a theorem that quantified the other way round
/// would be a different (and possibly weaker) statement.
pub(crate) fn wrec_iota_stmt(env: &mut Env, wt: &Wtype, rc: &Recursor) -> Formula {
    let vars: Vec<FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let inner = wrec_iota_body(env, wt, rc, &ps);
    let body = Formula::imp(premise(env, wt, &ps), inner);
    close_all(&vars, body)
}
