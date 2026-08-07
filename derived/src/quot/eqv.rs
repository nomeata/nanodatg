//! The **equivalence closure** `∼` of a relation, as the intersection of all
//! equivalence relations on `A` that contain it.
//!
//! # Interface
//!
//! Writing `A²` for `prod(A,A)` and `⟨x,y⟩` for the Kuratowski pair,
//!
//! ```text
//! refl_A(E)   := ∀x. (x ∈ A → ⟨x,x⟩ ∈ E)                          [reflexive_on]
//! sym(E)      := ∀x ∀y. (⟨x,y⟩ ∈ E → ⟨y,x⟩ ∈ E)                   [symmetric]
//! trans(E)    := ∀x ∀y ∀z. ((⟨x,y⟩ ∈ E ∧ ⟨y,z⟩ ∈ E) → ⟨x,z⟩ ∈ E)  [transitive]
//! R|A ⊆ E     := ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → ⟨x,y⟩ ∈ E)
//!                                                                 [contains_rel]
//!
//! eqv_closed(A,R,E) := refl_A(E) ∧ (sym(E) ∧ (trans(E) ∧ R|A ⊆ E))
//! eqv_cond(A,R,p)   := ∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → p ∈ E)
//! eqv(A,R)          := { p ∈ A² : eqv_cond(A,R,p) }
//! ```
//!
//! and the theorems
//!
//! ```text
//! ⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) ↔ (p ∈ A² ∧ eqv_cond(A,R,p)))          [eqv_symbol]
//! ⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) → p ∈ A²)                              [eqv_subset]
//! ⊢ ∀A ∀R ∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → ∀p. (p ∈ eqv(A,R) → p ∈ E))
//!                                                                  [eqv_induction]
//! ⊢ ∀A ∀R ∀x. (x ∈ A → ⟨x,x⟩ ∈ eqv(A,R))                           [eqv_refl]
//! ⊢ ∀A ∀R ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,R) → ⟨y,x⟩ ∈ eqv(A,R))             [eqv_sym]
//! ⊢ ∀A ∀R ∀x ∀y ∀z. ((⟨x,y⟩ ∈ eqv(A,R) ∧ ⟨y,z⟩ ∈ eqv(A,R))
//!                        → ⟨x,z⟩ ∈ eqv(A,R))                       [eqv_trans]
//! ⊢ ∀A ∀R ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → ⟨x,y⟩ ∈ eqv(A,R)) [eqv_incl]
//! ⊢ ∀A ∀R. eqv_closed(A,R,eqv(A,R))                                [eqv_closed_self]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why the intersection is a condition, not a set
//!
//! Carneiro's clause (thesis §6.2, the quotient bullet list) says only "let `∼`
//! be the equivalence closure of `⟦Γ ⊢ R⟧γ`". The textbook rendering of that is
//! `⋂ { E ∈ 𝒫(A²) : E is an equivalence relation containing R }`, which needs
//! `𝒫(A²)` to exist as a set and then a Separation on it. Phrasing it as the
//! *condition* [`eqv_cond`] instead — a universally quantified implication
//! ranging over `E`, evaluated inside a single Separation on `A²` — keeps the
//! whole construction to **one** Separation, and no power set is needed. That is
//! exactly the trick [`crate::wtype::w_cond`] plays for the W-type, and it is
//! the only trick in this file.
//!
//! # Why no transitive-closure recursion is needed
//!
//! Reflexivity, symmetry, transitivity and "contains `R`" are all **Horn**
//! conditions: each says that certain pairs are in `E` whenever certain others
//! are. A conjunction of Horn conditions is preserved by arbitrary
//! intersections, so [`eqv_refl`], [`eqv_sym`], [`eqv_trans`] and [`eqv_incl`]
//! are each proved by fixing an arbitrary `E` in the family and reading the
//! corresponding clause off the guard. Nothing iterates, and there is no
//! ω-indexed union of relation powers anywhere.
//!
//! That is also why the *other* direction — [`eqv_induction`] — is the cheap
//! one here, unlike in [`crate::wtype`] where W1 is the expensive half: the
//! closure conditions are the intersection's own guard, so proving them costs
//! one instantiation each.
//!
//! # Non-vacuity
//!
//! Every theorem above is satisfied by `eqv(A,R) = A²`, which would collapse
//! every quotient to a point. The witness that it is not is
//! [`super::witness::eqv_of_empty`]: `eqv(A,∅)` is inside the diagonal, by
//! [`eqv_induction`] at the kernel of the identity function, so
//! `class(A,∅,x) = class(A,∅,y)` forces `x = y`. See
//! [`super::witness::class_injective_at_empty`] and `derived/tests/quot.rs`.
//!
//! # Hypothetical premises
//!
//! Every entry below refuses a premise carrying hypotheses, because every
//! theorem it returns is documented `⊢ …` and [`Thm::mp`] would otherwise carry
//! the caller's `Γ` into it silently. See [`super::apparatus`] for the full
//! argument and for the worked case that motivated the sweep.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{
    and_intro, and_left, and_right, com12, conj_of, conj_proj, define_by_membership, gen_all,
    hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl, uncurry,
};

use super::shared::{inst_formula, split_and, sums_unconditional};

/// `∀x. (x ∈ A → ⟨x,x⟩ ∈ E)` — `E` is reflexive on `A`, as a formula.
pub fn reflexive_on(env: &mut Env, s: &Sums, a: &Term, e: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(s.ap.sets.pair(tx.clone(), tx), e.clone()),
        ),
    )
}

/// `∀x ∀y. (⟨x,y⟩ ∈ E → ⟨y,x⟩ ∈ E)` — `E` is symmetric, as a formula.
pub fn symmetric(env: &mut Env, s: &Sums, e: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    Formula::forall(
        x,
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), e.clone()),
                Formula::mem(s.ap.sets.pair(ty, tx), e.clone()),
            ),
        ),
    )
}

/// `∀x ∀y ∀z. ((⟨x,y⟩ ∈ E ∧ ⟨y,z⟩ ∈ E) → ⟨x,z⟩ ∈ E)` — `E` is transitive.
pub fn transitive(env: &mut Env, s: &Sums, e: &Term) -> Formula {
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
    let hyp = Formula::and(
        Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), e.clone()),
        Formula::mem(s.ap.sets.pair(ty, tz.clone()), e.clone()),
    );
    Formula::forall(
        x,
        Formula::forall(
            y,
            Formula::forall(z, Formula::imp(hyp, Formula::mem(s.ap.sets.pair(tx, tz), e.clone()))),
        ),
    )
}

/// `∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → ⟨x,y⟩ ∈ E)` — `E` contains `R`
/// restricted to `A`.
///
/// The restriction is what keeps `eqv(A,R)` inside `A²` for a `R` that is not a
/// relation on `A` at all. Lean's `Quot` takes an arbitrary `r : α → α → Prop`,
/// so `⟦R⟧` need not be a subset of `⟦α⟧²` — the interpretation is a set of
/// pairs and nothing forces its components into `⟦α⟧`.
pub fn contains_rel(env: &mut Env, s: &Sums, a: &Term, r: &Term, e: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let pair = s.ap.sets.pair(tx.clone(), ty.clone());
    let hyp = Formula::and(
        Formula::mem(tx, a.clone()),
        Formula::and(Formula::mem(ty, a.clone()), Formula::mem(pair.clone(), r.clone())),
    );
    Formula::forall(x, Formula::forall(y, Formula::imp(hyp, Formula::mem(pair, e.clone()))))
}

/// The four closure clauses, in the order [`eqv_closed`] conjoins them.
///
/// Returned as a slice so that [`crate::conj_proj`] can pick one out by index;
/// the indices are 0 reflexive, 1 symmetric, 2 transitive, 3 contains `R`.
pub fn eqv_atoms(env: &mut Env, s: &Sums, a: &Term, r: &Term, e: &Term) -> Vec<Formula> {
    vec![
        reflexive_on(env, s, a, e),
        symmetric(env, s, e),
        transitive(env, s, e),
        contains_rel(env, s, a, r, e),
    ]
}

/// `refl_A(E) ∧ (sym(E) ∧ (trans(E) ∧ R|A ⊆ E))` — "`E` is an equivalence
/// relation on `A` containing `R`", as a formula.
pub fn eqv_closed(env: &mut Env, s: &Sums, a: &Term, r: &Term, e: &Term) -> Formula {
    conj_of(&eqv_atoms(env, s, a, r, e)).expect("four atoms")
}

/// `E ⊆ A² ∧ eqv_closed(A,R,E)` — the guard the intersection ranges over.
pub fn eqv_guard(env: &mut Env, s: &Sums, a: &Term, r: &Term, e: &Term) -> Formula {
    let sub = kernel::thm::subset(env, e.clone(), s.prod.of(a.clone(), a.clone()));
    Formula::and(sub, eqv_closed(env, s, a, r, e))
}

/// `∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → p ∈ E)` — the condition Separation
/// carves `eqv(A,R)` out of `A²` with.
pub fn eqv_cond(env: &mut Env, s: &Sums, a: &Term, r: &Term, p: &Term) -> Formula {
    let ev = env.fresh_var();
    let te = Term::var(ev);
    let guard = eqv_guard(env, s, a, r, &te);
    Formula::forall(ev, Formula::imp(guard, Formula::mem(p.clone(), te)))
}

/// Introduce `eqv(A,R) = { p ∈ A² : eqv_cond(A,R,p) }`, with
/// `⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) ↔ (p ∈ A² ∧ eqv_cond(A,R,p)))`.
///
/// One Separation on `prod(A,A)`, exactly as [`crate::wtype::w_symbol`] is one
/// Separation on the bound `u`. Existence is
/// [`crate::funcs::separation_full`] — unconditional, so `eqv(A,∅)` being a
/// mere diagonal is no obstacle — and uniqueness is Extensionality via
/// [`crate::define_by_membership`].
///
/// `s` must be unconditional throughout: Separation consumes `s.ap.empty_ax`,
/// and a hypothetical one would put the caller's `Γ` on the defining
/// biconditional that every other theorem in this module is derived from.
pub fn eqv_symbol(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    if !sums_unconditional(s) {
        return None
    }
    let (av, rv) = (env.fresh_var(), env.fresh_var());
    let (ta, tr) = (Term::var(av), Term::var(rv));
    let p = env.fresh_var();
    let tp = Term::var(p);

    let prod_aa = s.prod.of(ta.clone(), ta.clone());
    let cond = eqv_cond(env, s, &ta, &tr, &tp);
    let existence = separation_full(env, p, &cond, &prod_aa, &s.ap.empty_ax).ok()?;
    let guard = Formula::and(Formula::mem(tp, prod_aa), cond);
    define_by_membership(env, &[av, rv], &existence, p, &guard)
}

/// The defining biconditional, instantiated and split: the two halves of
/// `p ∈ eqv(A,R) ↔ (p ∈ A² ∧ eqv_cond(A,R,p))` together with the two
/// conjuncts, so every caller below reads them off one call.
///
/// Returns `(mem_prod, cond, p ∈ eqv → (mem_prod ∧ cond), (mem_prod ∧ cond) → p ∈ eqv)`.
pub(super) fn eqv_parts(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_ax: &Thm,
    a: &Term,
    r: &Term,
    p: &Term,
) -> Option<(Formula, Formula, Thm, Thm)> {
    let mem_prod = Formula::mem(p.clone(), s.prod.of(a.clone(), a.clone()));
    let cond = eqv_cond(env, s, a, r, p);
    let at = inst_all(eqv_ax, &[a.clone(), r.clone(), p.clone()])?;
    let mem_eqv = Formula::mem(p.clone(), Term::apply(eqv, vec![a.clone(), r.clone()]));
    if *at.concl() != Formula::iff(mem_eqv, Formula::and(mem_prod.clone(), cond.clone())) {
        return None
    }
    Some((mem_prod, cond, iff_mp(&at)?, iff_mpr(&at)?))
}

/// `⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) → p ∈ prod(A,A))` — the closure is a relation on
/// `A`.
///
/// The left conjunct of the defining biconditional, and nothing more. It is
/// what stops `eqv(A,R)` from inheriting pairs of `R` that reach outside `A`.
///
/// `eqv_ax` must **establish** the biconditional, not merely conclude it:
/// [`eqv_parts`] rebuilds and compares the conclusion, and the `hyps()` check
/// here is the other half, without which a hypothetical axiom would hand its
/// `Γ` straight to the `⊢`-labelled result.
pub fn eqv_subset(env: &mut Env, s: &Sums, eqv: FnSym, eqv_ax: &Thm) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax]) {
        return None
    }
    let (av, rv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tp) = (Term::var(av), Term::var(rv), Term::var(pv));
    let (mem_prod, cond, fwd, _) = eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &tp)?;
    let out = syl(&fwd, &and_left(mem_prod, cond))?;
    Some(gen_all(&[av, rv, pv], &out))
}

/// **Induction / minimality.**
/// `⊢ ∀A ∀R ∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → ∀p. (p ∈ eqv(A,R) → p ∈ E))`
///
/// Immediate from the definition: `E` is one of the sets being intersected, so
/// the condition carried by every member of `eqv(A,R)` applies at `E`. The whole
/// proof is one universal instantiation plus a swap of antecedents — the same
/// shape as [`crate::wtype::w_induction`].
///
/// This is the lemma that makes the closure *least* rather than merely *an*
/// equivalence relation, and it is what [`super::compat::compat_closure`] runs
/// on: compatibility with `R` propagates to compatibility with `∼` because the
/// kernel of a function is one of the `E`s.
///
/// `eqv_ax` must establish the biconditional: [`eqv_parts`] pins its
/// conclusion, and the `hyps()` check here keeps a caller's `Γ` out of the
/// induction principle every other consumer of the closure runs on.
pub fn eqv_induction(env: &mut Env, s: &Sums, eqv: FnSym, eqv_ax: &Thm) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax]) {
        return None
    }
    let (av, rv, ev, pv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, te, tp) = (Term::var(av), Term::var(rv), Term::var(ev), Term::var(pv));

    let (mem_prod, cond, fwd, _) = eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &tp)?;
    let to_cond = syl(&fwd, &and_right(mem_prod, cond.clone()))?;

    let guard = eqv_guard(env, s, &ta, &tr, &te);
    let mem_e = Formula::mem(tp.clone(), te);
    let mem_eqv = Formula::mem(tp.clone(), Term::apply(eqv, vec![ta.clone(), tr.clone()]));

    // The condition, instantiated at `E` — the entire content of the lemma.
    let cond_at = Thm::ax_inst(cond, Term::var(ev))?;
    let (_, body) = cond_at.concl().as_imp()?;
    if body != Formula::imp(guard.clone(), mem_e.clone()) {
        return None
    }

    let h_p = com12(&syl(&to_cond, &cond_at)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(pv, guard.clone(), Formula::imp(mem_eqv.clone(), mem_e.clone()))?,
        &Thm::gen(pv, &h_p),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(guard, Formula::forall(pv, Formula::imp(mem_eqv, mem_e))),
        "eqv_induction: unexpected shape"
    );
    Some(gen_all(&[av, rv, ev], &out))
}

/// The workhorse of the four closure lemmas.
///
/// Given a hypothesis `h`, a target pair `p`, and a builder that produces
/// `⊢ (h ∧ guard(E)) → p ∈ E` for a freshly chosen `E`, this generalises `E`
/// away and returns `⊢ h → eqv_cond(A,R,p)`. `h` must not mention `E`, which is
/// automatic because `E` is minted here.
fn under_every_closed(
    env: &mut Env,
    s: &Sums,
    a: &Term,
    r: &Term,
    h: &Formula,
    p: &Term,
    build: impl FnOnce(&mut Env, &Term, &[Formula], &Formula) -> Option<Thm>,
) -> Option<Thm> {
    let ev = env.fresh_var();
    let te = Term::var(ev);
    let atoms = eqv_atoms(env, s, a, r, &te);
    let sub = kernel::thm::subset(env, te.clone(), s.prod.of(a.clone(), a.clone()));
    let closed = conj_of(&atoms)?;
    let guard = Formula::and(sub, closed);

    let big = build(env, &te, &atoms, &guard)?;
    if *big.concl() != Formula::imp(
        Formula::and(h.clone(), guard.clone()),
        Formula::mem(p.clone(), te.clone()),
    ) {
        return None
    }
    let curried = uncurry(&big)?;
    let inner = Formula::imp(guard, Formula::mem(p.clone(), te));
    let out = Thm::mp(&Thm::ax_dist(ev, h.clone(), inner)?, &Thm::gen(ev, &curried))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h.clone(), eqv_cond(env, s, a, r, p)),
        "under_every_closed: the condition rebuilt differently"
    );
    Some(out)
}

/// `⊢ guard(E) → atoms[i]` — read one closure clause off the guard.
fn clause(atoms: &[Formula], guard: &Formula, i: usize) -> Option<Thm> {
    let (sub, closed) = split_and(guard)?;
    syl(&and_right(sub, closed), &conj_proj(atoms, i)?)
}

/// `⊢ ∀A ∀R ∀x. (x ∈ A → ⟨x,x⟩ ∈ eqv(A,R))` — the closure is reflexive on `A`.
///
/// Both premises must be unconditional. Their conclusions are pinned by the
/// kernel joins — `pair_in_prod` only composes at all if it is the pairing
/// biconditional, and [`eqv_parts`] rebuilds `eqv_ax` — but nothing downstream
/// looks at `Γ`, so it is read here.
pub fn eqv_refl(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_ax: &Thm,
    pair_in_prod: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax, pair_in_prod]) {
        return None
    }
    let (av, rv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx) = (Term::var(av), Term::var(rv), Term::var(xv));
    let pxx = s.ap.sets.pair(tx.clone(), tx.clone());
    let mem_a = Formula::mem(tx.clone(), ta.clone());

    // `x ∈ A → ⟨x,x⟩ ∈ A²`.
    let pip = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), tx.clone()])?;
    let doubled = hyp_and(&imp_refl(mem_a.clone()), &imp_refl(mem_a.clone()))?;
    let in_prod = syl(&doubled, &iff_mpr(&pip)?)?;

    // `x ∈ A → ⟨x,x⟩ ∈ E` for every closed `E ⊆ A²`.
    let in_cond = under_every_closed(env, s, &ta, &tr, &mem_a, &pxx, |_env, _te, atoms, guard| {
        let refl = clause(atoms, guard, 0)?;
        let step = syl(&refl, &Thm::ax_inst(atoms[0].clone(), tx.clone())?)?;
        // `guard → (x ∈ A → ⟨x,x⟩ ∈ E)`, curried against `x ∈ A ∧ guard`.
        curry_hyp_first(&step, &mem_a)
    })?;

    let out = syl(&hyp_and(&in_prod, &in_cond)?, &eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pxx)?.3)?;
    Some(gen_all(&[av, rv, xv], &out))
}

/// From `⊢ guard → (h → φ)` build `⊢ (h ∧ guard) → φ`.
fn curry_hyp_first(step: &Thm, h: &Formula) -> Option<Thm> {
    let (guard, rest) = step.concl().as_imp()?;
    let (h_chk, phi) = rest.as_imp()?;
    if h_chk != *h {
        return None
    }
    let big = Formula::and(h.clone(), guard.clone());
    let via = syl(&and_right(h.clone(), guard.clone()), step)?; // big → (h → φ)
    let out = hyp_mp(&via, &and_left(h.clone(), guard))?;
    debug_assert_eq!(*out.concl(), Formula::imp(big, phi), "curry_hyp_first: wrong shape");
    Some(out)
}

/// `⊢ ∀A ∀R ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,R) → ⟨y,x⟩ ∈ eqv(A,R))` — symmetry.
///
/// Both premises must be unconditional, for the reason given on [`eqv_refl`].
pub fn eqv_sym(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_ax: &Thm,
    pair_in_prod: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax, pair_in_prod]) {
        return None
    }
    let (av, rv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, ty) = (Term::var(av), Term::var(rv), Term::var(xv), Term::var(yv));
    let pxy = s.ap.sets.pair(tx.clone(), ty.clone());
    let pyx = s.ap.sets.pair(ty.clone(), tx.clone());

    let (mem_prod, cond, fwd, _) = eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pxy)?;
    let h = Formula::mem(pxy.clone(), Term::apply(eqv, vec![ta.clone(), tr.clone()]));
    let h_prod = syl(&fwd, &and_left(mem_prod.clone(), cond.clone()))?;
    let h_cond = syl(&fwd, &and_right(mem_prod, cond.clone()))?;

    // `⟨x,y⟩ ∈ A² → ⟨y,x⟩ ∈ A²`, by swapping the two memberships.
    let pip_xy = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), ty.clone()])?;
    let pip_yx = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), ty.clone(), tx.clone()])?;
    let (ma_x, ma_y) = (Formula::mem(tx.clone(), ta.clone()), Formula::mem(ty.clone(), ta.clone()));
    let swap = hyp_and(&and_right(ma_x.clone(), ma_y.clone()), &and_left(ma_x, ma_y))?;
    let h_prod_yx =
        syl(&h_prod, &syl(&iff_mp(&pip_xy)?, &syl(&swap, &iff_mpr(&pip_yx)?)?)?)?;

    let h_cond_yx =
        under_every_closed(env, s, &ta, &tr, &h, &pyx, |_env, te, atoms, guard| {
            // `(h ∧ guard) → ⟨x,y⟩ ∈ E`.
            let at_e = Thm::ax_inst(cond.clone(), te.clone())?;
            let via = syl(&and_left(h.clone(), guard.clone()), &syl(&h_cond, &at_e)?)?;
            let in_e = hyp_mp(&via, &and_right(h.clone(), guard.clone()))?;
            // `(h ∧ guard) → (⟨x,y⟩ ∈ E → ⟨y,x⟩ ∈ E)`.
            let sym = clause(atoms, guard, 1)?;
            let inst = inst_formula(&atoms[1], &[tx.clone(), ty.clone()])?;
            let step = syl(&and_right(h.clone(), guard.clone()), &syl(&sym, &inst)?)?;
            hyp_mp(&step, &in_e)
        })?;

    let out =
        syl(&hyp_and(&h_prod_yx, &h_cond_yx)?, &eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pyx)?.3)?;
    Some(gen_all(&[av, rv, xv, yv], &out))
}

/// `⊢ ∀A ∀R ∀x ∀y ∀z. ((⟨x,y⟩ ∈ eqv(A,R) ∧ ⟨y,z⟩ ∈ eqv(A,R)) → ⟨x,z⟩ ∈ eqv(A,R))`
/// — transitivity.
///
/// Both premises must be unconditional, for the reason given on [`eqv_refl`].
pub fn eqv_trans(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_ax: &Thm,
    pair_in_prod: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax, pair_in_prod]) {
        return None
    }
    let (av, rv, xv, yv, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tx, ty, tz) =
        (Term::var(av), Term::var(rv), Term::var(xv), Term::var(yv), Term::var(zv));
    let pxy = s.ap.sets.pair(tx.clone(), ty.clone());
    let pyz = s.ap.sets.pair(ty.clone(), tz.clone());
    let pxz = s.ap.sets.pair(tx.clone(), tz.clone());
    let eqv_t = Term::apply(eqv, vec![ta.clone(), tr.clone()]);

    let (mp_xy, cond_xy, fwd_xy, _) = eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pxy)?;
    let (mp_yz, cond_yz, fwd_yz, _) = eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pyz)?;
    let (m_xy, m_yz) = (
        Formula::mem(pxy.clone(), eqv_t.clone()),
        Formula::mem(pyz.clone(), eqv_t.clone()),
    );
    let h = Formula::and(m_xy.clone(), m_yz.clone());
    let left = and_left(m_xy.clone(), m_yz.clone());
    let right = and_right(m_xy, m_yz);

    // `h → ⟨x,z⟩ ∈ A²`: `x ∈ A` from the first pair, `z ∈ A` from the second.
    let (ma_x, ma_y, ma_z) = (
        Formula::mem(tx.clone(), ta.clone()),
        Formula::mem(ty.clone(), ta.clone()),
        Formula::mem(tz.clone(), ta.clone()),
    );
    let pip_xy = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), ty.clone()])?;
    let pip_yz = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), ty.clone(), tz.clone()])?;
    let pip_xz = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), tz.clone()])?;
    let h_x = syl(
        &syl(&left, &syl(&fwd_xy, &and_left(mp_xy.clone(), cond_xy.clone()))?)?,
        &syl(&iff_mp(&pip_xy)?, &and_left(ma_x.clone(), ma_y.clone()))?,
    )?;
    let h_z = syl(
        &syl(&right, &syl(&fwd_yz, &and_left(mp_yz.clone(), cond_yz.clone()))?)?,
        &syl(&iff_mp(&pip_yz)?, &and_right(ma_y, ma_z))?,
    )?;
    let h_prod_xz = syl(&hyp_and(&h_x, &h_z)?, &iff_mpr(&pip_xz)?)?;

    let h_cond_xy = syl(&left, &syl(&fwd_xy, &and_right(mp_xy, cond_xy.clone()))?)?;
    let h_cond_yz = syl(&right, &syl(&fwd_yz, &and_right(mp_yz, cond_yz.clone()))?)?;

    let h_cond_xz =
        under_every_closed(env, s, &ta, &tr, &h, &pxz, |_env, te, atoms, guard| {
            let hg_l = and_left(h.clone(), guard.clone());
            let hg_r = and_right(h.clone(), guard.clone());
            let mem_in = |hc: &Thm, c: &Formula| -> Option<Thm> {
                let at_e = Thm::ax_inst(c.clone(), te.clone())?;
                hyp_mp(&syl(&hg_l, &syl(hc, &at_e)?)?, &hg_r)
            };
            let in_xy = mem_in(&h_cond_xy, &cond_xy)?;
            let in_yz = mem_in(&h_cond_yz, &cond_yz)?;
            let both = hyp_and(&in_xy, &in_yz)?;
            let tr_clause = clause(atoms, guard, 2)?;
            let inst = inst_formula(&atoms[2], &[tx.clone(), ty.clone(), tz.clone()])?;
            let step = syl(&hg_r, &syl(&tr_clause, &inst)?)?;
            hyp_mp(&step, &both)
        })?;

    let out =
        syl(&hyp_and(&h_prod_xz, &h_cond_xz)?, &eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pxz)?.3)?;
    Some(gen_all(&[av, rv, xv, yv, zv], &out))
}

/// `⊢ ∀A ∀R ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → ⟨x,y⟩ ∈ eqv(A,R))` — the
/// closure contains `R` restricted to `A`.
///
/// Both premises must be unconditional, for the reason given on [`eqv_refl`].
pub fn eqv_incl(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_ax: &Thm,
    pair_in_prod: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_ax, pair_in_prod]) {
        return None
    }
    let (av, rv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, ty) = (Term::var(av), Term::var(rv), Term::var(xv), Term::var(yv));
    let pxy = s.ap.sets.pair(tx.clone(), ty.clone());

    let (ma_x, ma_y) = (Formula::mem(tx.clone(), ta.clone()), Formula::mem(ty.clone(), ta.clone()));
    let in_r = Formula::mem(pxy.clone(), tr.clone());
    let tail = Formula::and(ma_y.clone(), in_r.clone());
    let h = Formula::and(ma_x.clone(), tail.clone());

    let h_x = and_left(ma_x.clone(), tail.clone());
    let h_y = syl(&and_right(ma_x.clone(), tail.clone()), &and_left(ma_y.clone(), in_r))?;
    let pip = inst_all(pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), ty.clone()])?;
    let h_prod = syl(&hyp_and(&h_x, &h_y)?, &iff_mpr(&pip)?)?;

    let h_cond = under_every_closed(env, s, &ta, &tr, &h, &pxy, |_env, _te, atoms, guard| {
        let cl = clause(atoms, guard, 3)?;
        let inst = inst_formula(&atoms[3], &[tx.clone(), ty.clone()])?;
        let step = syl(&and_right(h.clone(), guard.clone()), &syl(&cl, &inst)?)?;
        hyp_mp(&step, &and_left(h.clone(), guard.clone()))
    })?;

    let out =
        syl(&hyp_and(&h_prod, &h_cond)?, &eqv_parts(env, s, eqv, eqv_ax, &ta, &tr, &pxy)?.3)?;
    Some(gen_all(&[av, rv, xv, yv], &out))
}

/// `⊢ ∀A ∀R. eqv_closed(A,R,eqv(A,R))` — the closure is itself an equivalence
/// relation on `A` containing `R`.
///
/// Nothing new: the four clauses are [`eqv_refl`], [`eqv_sym`], [`eqv_trans`]
/// and [`eqv_incl`] with their outer `∀A ∀R` stripped. It is stated because
/// together with [`eqv_induction`] it is what "closure" *means* — without it
/// `eqv` would merely be *some* set that every equivalence relation contains,
/// which `∅` also is.
///
/// All four clauses must be unconditional. Their conclusions are pinned by the
/// loop below, which rebuilds each atom and refuses a clause that has drifted;
/// the `hyps()` check is the half that loop cannot do, since `Thm::concl` says
/// nothing about `Γ` and `and_intro` would union all four.
pub fn eqv_closed_self(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    refl: &Thm,
    sym: &Thm,
    trans: &Thm,
    incl: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[refl, sym, trans, incl]) {
        return None
    }
    let (av, rv) = (env.fresh_var(), env.fresh_var());
    let (ta, tr) = (Term::var(av), Term::var(rv));
    let eqv_t = Term::apply(eqv, vec![ta.clone(), tr.clone()]);
    let atoms = eqv_atoms(env, s, &ta, &tr, &eqv_t);

    let parts = [refl, sym, trans, incl]
        .iter()
        .map(|t| inst_all(t, &[ta.clone(), tr.clone()]))
        .collect::<Option<Vec<_>>>()?;
    for (i, p) in parts.iter().enumerate() {
        if *p.concl() != atoms[i] {
            return None
        }
    }
    let mut acc = parts[3].clone();
    for p in parts[..3].iter().rev() {
        acc = and_intro(p, &acc);
    }
    debug_assert_eq!(*acc.concl(), conj_of(&atoms)?, "eqv_closed_self: wrong shape");
    Some(gen_all(&[av, rv], &acc))
}
