//! The two membership conditions, and the symbol they define.
//!
//! # Interface
//!
//! ```text
//! preds_in(A,R,C,x)  := ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ C))            [preds_in]
//! step_closed(A,R,C) := ∀x. (x ∈ A → (preds_in(A,R,C,x) → x ∈ C))     [step_closed]
//! acc_cond(A,R,z)    := ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C)    [acc_cond]
//!
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) ↔ (z ∈ A ∧ acc_cond(A,R,z)))              [acc_symbol]
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → z ∈ A)                                  [acc_subset]
//! ```
//!
//! Callers need none of the derivations below. All three formulas are built
//! here in one place so that every file that mentions one builds *the same*
//! formula — they are compared syntactically all over the development, and a
//! second spelling would silently stop matching.
//!
//! # Why there is no bound and no universe
//!
//! Carneiro's *The Type Theory of Lean* §6.2.2 defines `acc(A,R) ⊆ A` as "the
//! smallest set `C` such that if `y ∈ C` for all `y` such that `⟨y,x⟩ ∈ R`,
//! then `x ∈ C`". This is the same least-closed-set pattern as
//! [`crate::wtype`], with one decisive simplification: **`acc` is a subset of
//! `A` by definition**, so the set being intersected over is already given and
//! the Separation happens on `A` itself.
//!
//! `W` had no such set — `W_{x∈A} B(x)` is a set of trees, not a subset of
//! anything already named — which is why [`crate::wtype`] carries a bound `u`
//! as a parameter, why W1/W3/`w_rect` all carry `closed(A,B,u)` as an
//! antecedent, and why [`crate::bound`] and the `ω`-tower exist to discharge
//! it. None of that apparatus appears here: every theorem in [`crate::acc`] is
//! unconditional.
//!
//! # Why the intersection is a condition, not a set
//!
//! Exactly as in [`crate::wtype::condition`]: rendering "the intersection of
//! all closed subsets of `A`" as `⋂{C ∈ 𝒫A : step_closed(A,R,C)}` would need
//! `𝒫(A)` to exist as a set and then a Separation on it. Phrasing it as the
//! *condition* [`acc_cond`] — a universally quantified implication ranging over
//! `C`, evaluated inside a single Separation on `A` — keeps the whole
//! construction to **one** Separation, and `𝒫(A)` is never needed.
//!
//! # Why `x ∈ A` guards the closure condition
//!
//! The thesis leaves the range of `x` in the closure clause implicit. It has to
//! be `A`, and the reason is that `acc` is being carved out of `A`: without the
//! guard a "closed" `C` would be forced to contain every point outside `A` that
//! happens to have no `R`-predecessors in `A`, so no `C ⊆ A` could be closed at
//! all, [`acc_cond`] would hold vacuously, and `acc(A,R)` would come out as `A`
//! for every `R`. That the guarded definition does *not* do that is
//! [`crate::acc::acc_no_loops`], so the guard is doing real work.
//!
//! # `R ⊆ A × A` is not assumed
//!
//! The thesis introduces `acc` for a relation `R ⊆ A × A`. That hypothesis is
//! never taken here: `R` is an arbitrary set, and [`preds_in`] carries its own
//! `y ∈ A` guard so that edges from outside `A` are simply ignored. This is
//! strictly more general and costs nothing — at an `R` that does satisfy
//! `R ⊆ A × A` the `y ∈ A` guard is redundant and the definitions agree — and
//! it means a caller interpreting `acc_{α,r}` never has to prove a typing side
//! condition on `r` first.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::err::DResult;
use crate::funcs::separation_full;

use crate::rules::{iff_mp, inst_all, syl};
use crate::{and_left, decline, gen_all, opair};

/// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ C))` — "every `R`-predecessor of `x` inside
/// `A` lies in `C`", as a formula.
///
/// This is the induction hypothesis of the accessibility predicate, and it is
/// the one sub-formula that every file in [`crate::acc`] rebuilds, so it is
/// factored out rather than spelled inline.
pub fn preds_in(env: &mut Env, up: FnSym, a: &Term, r: &Term, c: &Term, x: &Term) -> Formula {
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), a.clone()),
            Formula::imp(
                Formula::mem(opair(up, ty.clone(), x.clone()), r.clone()),
                Formula::mem(ty, c.clone()),
            ),
        ),
    )
}

/// `∀x. (x ∈ A → (preds_in(A,R,C,x) → x ∈ C))` — "`C` is closed under the
/// accessibility step", as a formula.
///
/// The analogue of [`crate::wtype::closed`]. See the module header for why the
/// guard `x ∈ A` is present although the thesis omits it.
pub fn step_closed(env: &mut Env, up: FnSym, a: &Term, r: &Term, c: &Term) -> Formula {
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let body = preds_in(env, up, a, r, c, &tx);
    Formula::forall(
        xv,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::imp(body, Formula::mem(tx, c.clone())),
        ),
    )
}

/// `∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C)` — the condition Separation
/// carves `acc(A,R)` out of `A` with.
///
/// "`z` is in every step-closed subset of `A`", i.e. membership in the
/// intersection — written as a condition so that the intersection needs no
/// `𝒫(A)` and no indexed family, only one Separation.
pub fn acc_cond(env: &mut Env, up: FnSym, a: &Term, r: &Term, z: &Term) -> Formula {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let guard = Formula::and(
        kernel::thm::subset(env, tc.clone(), a.clone()),
        step_closed(env, up, a, r, &tc),
    );
    Formula::forall(cv, Formula::imp(guard, Formula::mem(z.clone(), tc)))
}

/// Introduce `acc(A,R) = { z ∈ A : ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C) }`,
/// with `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) ↔ (z ∈ A ∧ ∀C. …))`.
///
/// One Separation on `A`: existence is [`crate::funcs::separation_full`],
/// uniqueness is Extensionality via [`crate::define_by_membership`]. The
/// condition is an ordinary first-order formula in `A`, `R` and `C`, so `acc`
/// is a genuine binary function symbol rather than a construction parameterised
/// by a formula.
///
/// `empty_ax` is consumed by the Separation and does **not** appear in the
/// conclusion; see [`crate::funcs::separation_full`], which reads the empty
/// set's term off it and insists it says precisely `∀z. ¬(z ∈ e)`. It must also
/// be **unconditional**: the symbol this mints is asserted to satisfy its
/// characteristic theorem outright, and a `Γ` behind the existence proof would
/// make that a lie. Today a hypothetical one dies at [`kernel::thm::define`]
/// inside `separation_full` — but by accident, so the refusal is made explicit
/// here rather than left to a helper three layers down.
pub fn acc_symbol(env: &mut Env, up: FnSym, empty_ax: &Thm) -> DResult<(FnSym, Thm)> {
    if !empty_ax.hyps().is_empty() {
        return Err(decline!("the empty-set axiom carries hypotheses, which would ride into the symbol it defines"))
    }
    let (av, rv) = (env.fresh_var(), env.fresh_var());
    let (ta, tr) = (Term::var(av), Term::var(rv));
    let z = env.fresh_var();
    let tz = Term::var(z);

    let cond = acc_cond(env, up, &ta, &tr, &tz);
    let existence = separation_full(env, z, &cond, &ta, empty_ax)?;
    let guard = Formula::and(Formula::mem(tz, ta), cond);
    crate::rules::define_by_membership(env, &[av, rv], &existence, z, &guard)
}

/// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → z ∈ A)` — accessibility is a property of
/// members of `A`.
///
/// The left conjunct of the defining biconditional, and nothing more. This is
/// the statement that makes the whole module cheaper than [`crate::wtype`]:
/// there is a set to carve out of, so no bound is a parameter.
///
/// `acc_ax` must **establish** the defining biconditional at `acc`: the
/// conclusion is pinned below, and the sequent must be unconditional, since the
/// header here promises `⊢ …` and [`crate::syl`] would otherwise carry the
/// caller's `Γ` into it.
pub fn acc_subset(env: &mut Env, up: FnSym, acc: FnSym, acc_ax: &Thm) -> DResult<Thm> {
    if !acc_ax.hyps().is_empty() {
        return Err(decline!("the accessibility axiom carries hypotheses, which the syllogism below would union in"))
    }
    let (av, rv, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz) = (Term::var(av), Term::var(rv), Term::var(z));

    let cond = acc_cond(env, up, &ta, &tr, &tz);
    let mem_a = Formula::mem(tz.clone(), ta.clone());
    let at = inst_all(acc_ax, &[ta.clone(), tr.clone(), tz.clone()])?;
    let acc_t = Term::apply(acc, vec![ta, tr]);
    if *at.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), acc_t.clone()),
            Formula::and(mem_a.clone(), cond.clone()),
        )
    {
        return Err(decline!("the accessibility axiom is not the characteristic property of this acc symbol"))
    }
    let out = syl(&iff_mp(&at)?, &and_left(mem_a.clone(), cond))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(tz, acc_t), mem_a),
        "acc_subset: unexpected shape"
    );
    Ok(gen_all(&[av, rv, z], &out))
}
