//! **A4** — the predecessors of an accessible point are accessible.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀y ∀z. (z ∈ acc(A,R) → ((y ∈ A ∧ ⟨y,z⟩ ∈ R) → y ∈ acc(A,R)))
//!                                                        [acc_pred_closed]
//! ```
//!
//! **Unconditional**, and it is [`crate::acc::acc_rect`] at the cheapest `φ`
//! this crate has yet run it at: the induction hypothesis `acc_rect` hands
//! back already contains `y ∈ acc(A,R)` as its *left* conjunct, so the whole
//! proof is one instantiation and one conjunction elimination. The `φ(y)`
//! half of the induction hypothesis is never used.
//!
//! # Why it is the converse of the introduction rule, and why it was missing
//!
//! [`crate::acc::acc_intro`] (**A1**) says `x` is accessible when *all* its
//! `A`-predecessors are; this is the converse, and together they say that
//! membership in `acc(A,R)` is exactly the step-closure condition. `acc` was
//! built with A0–A3 because the soundness argument needed induction over a
//! formula and nothing else. What wants A4 is the **recursor**: to instantiate
//! a step equation guarded by `c ∈ ih_bound(A,T)` at `c := ih(accrec,A,R,x)`
//! one has to know that `accrec`'s values on `x`'s predecessors land in `T`
//! ([`crate::rec_acc::preds_typed`]), and `accrec` is only known to be typed on
//! `acc(A,R)` — so the predecessors have to be put back inside it first. See
//! [`crate::rec_acc::bounded`].
//!
//! # The guard is a conjunction, and that is what makes the scheme apply
//!
//! `φ` may not have free occurrences of the induction variable other than
//! through `z`, and [`crate::acc::acc_rect`] additionally requires every free
//! variable of `φ` to be listed in `params`. Stating the lemma as
//! `∀y. (y ∈ A → …)` would need `y ∈ A` ambiently while `ind_step` is being
//! discharged, which a `Thm` cannot carry without putting it in `hyps()`. So
//! `y` is a **parameter** and its typing rides inside `φ` as
//! `φ(z) := ((y ∈ A ∧ ⟨y,z⟩ ∈ R) → y ∈ acc(A,R))`, which is why the exported
//! statement guards with a conjunction rather than two arrows.

use kernel::{Env, Formula, Term, Thm};

use crate::{and_left, and_right, gen_all, hyp_mp, syl, uncurry};

use super::apparatus::Acc;
use super::rect::{acc_rect, Params};

/// `⊢ ∀A ∀R ∀y ∀z. (z ∈ acc(A,R) → ((y ∈ A ∧ ⟨y,z⟩ ∈ R) → y ∈ acc(A,R)))`.
///
/// **A4**, the converse of [`crate::acc::acc_intro`]. Mints one fresh symbol,
/// for the subset [`acc_rect`] runs the induction at.
///
/// Returns `None` if `ac` carries a hypothetical theorem — [`acc_rect`] checks
/// that itself, and the header above advertises `⊢` with nothing on the left.
pub fn acc_pred_closed(env: &mut Env, ac: &Acc) -> Option<Thm> {
    let (av, rv, yv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, ty, tz) = (Term::var(av), Term::var(rv), Term::var(yv), Term::var(zv));
    let acc_t = ac.of(ta.clone(), tr.clone());

    // φ(z) := ((y ∈ A ∧ ⟨y,z⟩ ∈ R) → y ∈ acc(A,R)) — `y` is a parameter, so
    // its typing has to ride inside φ; see the header.
    let guard = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::mem(ac.edge(ty.clone(), tz), tr.clone()),
    );
    let y_acc = Formula::mem(ty.clone(), acc_t.clone());
    let phi = Formula::imp(guard, y_acc.clone());
    let rect = acc_rect(env, ac, &[av, rv, yv], Params { a: av, r: rv }, zv, &phi)?;

    // ── discharge `ind_step(φ)`, read off the scheme rather than rebuilt ─────
    let (ih, _) = rect.concl().as_imp()?;
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let (_, body) = Thm::ax_inst(ih.clone(), tx.clone())?.concl().as_imp()?;
    let (mem_xa, rest) = body.as_imp()?;
    let (ihyp, phi_x) = rest.as_imp()?;
    let (guard_x, _) = phi_x.as_imp()?;

    // Under `N := (x ∈ A ∧ ihyp) ∧ (y ∈ A ∧ ⟨y,x⟩ ∈ R)`, produce `y ∈ acc`.
    let front = Formula::and(mem_xa.clone(), ihyp.clone());
    let n_front = and_left(front.clone(), guard_x.clone());
    let n_ih = syl(&n_front, &and_right(mem_xa, ihyp.clone()))?;
    let n_guard = and_right(front, guard_x.clone());
    // `guard_x` is `φ`'s antecedent at `z := x`; rebuilt rather than taken
    // apart, because `Formula::and` is `¬(φ → ¬ψ)` and has no projection.
    let g_ya = Formula::mem(ty.clone(), ta.clone());
    let g_edge = Formula::mem(ac.edge(ty.clone(), tx.clone()), tr.clone());
    if guard_x != Formula::and(g_ya.clone(), g_edge.clone()) {
        return None
    }
    let n_ya = syl(&n_guard, &and_left(g_ya.clone(), g_edge.clone()))?;
    let n_edge = syl(&n_guard, &and_right(g_ya, g_edge))?;

    // The induction hypothesis at `y` gives `y ∈ acc(A,R) ∧ φ(y)`; the right
    // conjunct is not used.
    let ihyp_at_y = Thm::ax_inst(ihyp, ty.clone())?;
    let n_pair = hyp_mp(&hyp_mp(&syl(&n_ih, &ihyp_at_y)?, &n_ya)?, &n_edge)?;
    let n_acc = syl(&n_pair, &and_left(y_acc.clone(), phi.subst(zv, &ty)))?;
    if n_acc.concl().as_imp()?.1 != y_acc {
        return None
    }

    let minor = Thm::gen(xv, &uncurry(&uncurry(&n_acc)?)?);
    if *minor.concl() != ih {
        return None
    }
    let out = Thm::mp(&rect, &minor)?;
    Some(gen_all(&[av, rv, yv], &out))
}
