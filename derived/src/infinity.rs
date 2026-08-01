//! The axiom of Infinity, **derived** — in the primitive language of `∈`.
//!
//! # Interface
//!
//! Writing `0` for `∅` and `succ(n)` for `n ∪ {n}`, the exports are
//!
//! ```text
//! ⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))                    [infinity]
//!
//! ⊢ ∃I. ( ∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e))
//!       ∧ ∀n. (n ∈ I → ∃s. (s ∈ I ∧ ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n)))) )
//!                                                              [infinity_primitive]
//!
//! ⊢ ∀I. ((0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))
//!        → ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))                [inductive_two_members]
//!
//! ⊢ ∃I. ((0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))
//!        ∧ ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))                [infinity_nonvacuous]
//! ```
//!
//! and [`Infinity`] packages all three over one chain of definitional
//! extensions. Callers need none of the derivations below.
//!
//! **Nothing is asserted.** There is no `Thm::ax_infinity` and there never was:
//! the trusted base is Extensionality, Pairing, Union, Power, Regularity,
//! Replacement, Tarski's Axiom A and Choice, and Infinity is a *consequence* of
//! Tarski and Replacement. This module exists so that the fact has a name, a
//! statement in the standard form, and a test — the open TCB question was
//! whether it would have to be added as a ninth axiom, and it does not.
//!
//! # Which statement, and why
//!
//! [`infinity`] is the form in Jech, *Set Theory* (3rd millennium ed.), §1:
//!
//! > `∃S (∅ ∈ S ∧ (∀x ∈ S)(x ∪ {x} ∈ S))`
//!
//! and in Kunen, *Set Theory* (2011), I.2 Axiom 7:
//!
//! > `∃x (0 ∈ x ∧ ∀y ∈ x (S(y) ∈ x))`,  `S(y) := y ∪ {y}`
//!
//! — one existential, the base point as a *member* (not as a bounded
//! existential), successor-closure as a bounded universal, and no minimality
//! clause. The bounded quantifier `∀y ∈ x` unabbreviates to `∀y. (y ∈ x → …)`,
//! which is what [`crate::recursion::inductive`] builds, so [`infinity`] is
//! literally the displayed sentence with the two abbreviations `0` and `S`
//! spelled as the symbols this development already has.
//!
//! That is the *right* target and not quite a *sufficient* one. `∅` and `succ`
//! are symbols of a definitional extension, so `⊢ ∃I. (∅ ∈ I ∧ …)` is a
//! theorem of the extension, and reading it as "Infinity needs no axiom"
//! silently leans on conservativity. [`infinity_primitive`] removes that lean:
//! it is the same sentence with both abbreviations expanded back to their
//! defining conditions, so it contains **no function symbol at all** and is a
//! sentence of the pure language `{∈}` — which is what the axiom of a set
//! theory actually is, and what Kunen means when he notes that `0` and `S` are
//! eliminable. The expansions are the usual ones:
//!
//! ```text
//! 0 ∈ I         ⇝  ∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e))
//! succ(n) ∈ I   ⇝  ∃s. (s ∈ I ∧ ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n)))
//! ```
//!
//! Uniqueness of `e` and `s` is not asserted and is not needed — it is
//! Extensionality, and the existential form is what an eliminated definition
//! leaves behind.
//!
//! # Where it comes from
//!
//! Almost everywhere else. [`crate::recursion::omega_exists`] already proves
//!
//! ```text
//! ⊢ ∃m. (Ind(∅, m) ∧ ∀w. (Ind(∅, w) → ∀q. (q ∈ m → q ∈ w)))
//! ```
//!
//! — `ω` exists and is *least* — and `Ind(∅, m)` is, on the nose, the matrix of
//! Infinity. So [`infinity_from_least`] is one `and_left` under one
//! [`crate::exists_mono`]: **weakening a theorem that was already there**, by
//! discarding the minimality conjunct nobody asked Infinity for. It is worth
//! saying plainly that this is where the content is, and it is not here; the
//! work was done in [`crate::recursion::naturals`], whose header explains why
//! `ω` had to be separated at `Trans(q) ∧ …` (Tarski's universe is closed under
//! `𝒫` but not under `n ↦ n ∪ {n}`, so closure is taken only at transitive
//! sets, where `succ(n) ⊆ 𝒫n`).
//!
//! [`infinity_primitive`] is not free in the same way, but it is not deep
//! either: two existential introductions, at the witnesses `∅` and `succ(n)`,
//! whose side conditions are exactly the characteristic theorems `⊢ ∀z. ¬(z ∈ ∅)`
//! and `⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))`. The cost is the Hilbert
//! bookkeeping of pushing an implication under `∀n` and under `∃I`.
//!
//! [`infinity_from_least`] is kept separate from [`infinity`] so that the
//! weakening step can be tested against a premise it did not itself produce —
//! including a mismatched one, which it must reject: it rebuilds `Ind(∅, I)`
//! and refuses if the left conjunct of the premise is not it.
//!
//! # Why the power-set version is not this
//!
//! [`crate::empty::induction::inductive_set_exists`] proves
//! `⊢ ∀x ∃u. (x ∈ u ∧ ∀y ∈ u. 𝒫y ∈ u)` and its header calls that "Infinity,
//! derived". As a *bound* it does the same job, and it is what
//! [`crate::separation`]'s gap needed; as a *statement* it is a different one.
//! Its successor is `𝒫`, not `n ↦ n ∪ {n}`, and its base point is an arbitrary
//! `x`, not `∅`. Neither the von Neumann naturals nor Peano's axioms fall out
//! of it directly, and no textbook states Infinity that way. This module is the
//! statement the literature actually writes down.
//!
//! # Non-vacuity
//!
//! `∃I. …` is worthless if `I` could be trivial, and the matrix does not
//! obviously exclude it — read carelessly, a one-element `I` with `succ` acting
//! as the identity would satisfy it. [`inductive_two_members`] rules that out
//! for **every** inductive set, not just the witness that happens to be
//! produced: `0 ∈ I` and `succ(0) ∈ I` by the two conjuncts, and
//! `¬(0 = succ 0)` because `0 ∈ succ 0` (right disjunct of the successor
//! characterisation, at `0 = 0`) would transport along the equation to
//! `0 ∈ 0`, which [`crate::empty::no_self_mem`] refutes. So every set Infinity
//! asserts to exist has at least two members — and the same argument at
//! `succ^k(0)`, with [`crate::recursion::succ_inj`] and
//! [`crate::recursion::succ_ne_zero`], gives as many as one likes. Two is what
//! is derived here because two is what distinguishes a real inductive set from
//! a fixed point.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::empty::readers::{open_exists, split_and};
use crate::empty::no_self_mem;
use crate::funcs::Sets;
use crate::recursion::{inductive, omega_exists, successor};
use crate::separation::or_intro_right;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_intro_imp, exists_mono, hyp_and, hyp_mp,
    iff_mpr, imp_mono_r, imp_refl, inst_all, mem_singleton, mpd_const, syl,
};

// ─────────────────────────────────────────────────────────────────────────────
// The statements, as formulas.
// ─────────────────────────────────────────────────────────────────────────────

/// `IsEmpty(e) := ∀z. ¬(z ∈ e)` — what the symbol `∅` abbreviates.
pub fn is_empty_set(env: &mut Env, e: &Term) -> Formula {
    let z = env.fresh_var();
    Formula::forall(z, Formula::not(Formula::mem(Term::var(z), e.clone())))
}

/// `IsSucc(s, n) := ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n))` — what `succ(n)`, i.e.
/// `n ∪ {n}`, abbreviates.
pub fn is_successor_of(env: &mut Env, s: &Term, n: &Term) -> Formula {
    let z = env.fresh_var();
    let tz = Term::var(z);
    Formula::forall(
        z,
        Formula::iff(
            Formula::mem(tz.clone(), s.clone()),
            Formula::or(Formula::mem(tz.clone(), n.clone()), Formula::eq(tz, n.clone())),
        ),
    )
}

/// The matrix of [`infinity_primitive`] at a caller-supplied `I`:
///
/// ```text
/// ∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e))
/// ∧ ∀n. (n ∈ I → ∃s. (s ∈ I ∧ ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n))))
/// ```
///
/// No function symbol occurs in it — this is a formula of the language `{∈}`.
pub fn is_inductive_primitive(env: &mut Env, i: &Term) -> Formula {
    let (e, n, s) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (te, tn, ts) = (Term::var(e), Term::var(n), Term::var(s));

    let has_empty = Formula::exists(
        e,
        Formula::and(Formula::mem(te.clone(), i.clone()), is_empty_set(env, &te)),
    );
    let has_succ = Formula::forall(
        n,
        Formula::imp(
            Formula::mem(tn.clone(), i.clone()),
            Formula::exists(
                s,
                Formula::and(
                    Formula::mem(ts.clone(), i.clone()),
                    is_successor_of(env, &ts, &tn),
                ),
            ),
        ),
    );
    Formula::and(has_empty, has_succ)
}

/// `∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b)))` — `I` has at least two members.
pub fn two_members(env: &mut Env, i: &Term) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    Formula::exists(
        a,
        Formula::exists(
            b,
            Formula::and(
                Formula::mem(ta.clone(), i.clone()),
                Formula::and(
                    Formula::mem(tb.clone(), i.clone()),
                    Formula::not(Formula::eq(ta, tb)),
                ),
            ),
        ),
    )
}

/// Read `∅` off a proof `⊢ ∀z. ¬(z ∈ e)`, insisting it says exactly that and
/// that `e` does not mention the quantified variable.
///
/// The same probe [`crate::recursion::omega_exists`] uses, and for the same
/// reason: the term is *read* rather than passed alongside the theorem, so a
/// caller cannot hand in a symbol the theorem is not about.
fn zero_of(env: &mut Env, empty_ax: &Thm) -> Option<Term> {
    let probe = env.fresh_var();
    let (mem_probe, fls) = inst_all(empty_ax, &[Term::var(probe)])?.concl().as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (lhs, zero) = mem_probe.as_mem()?;
    if lhs != Term::var(probe) || zero.occurs_free(probe) {
        return None
    }
    Some(zero)
}

// ─────────────────────────────────────────────────────────────────────────────
// Infinity, in the form the literature states it.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))`, from `⊢ ∃m. Least(0, m)`.
///
/// Drop the minimality conjunct. `Least(0, m)` is `Ind(0, m) ∧ (m is contained
/// in every inductive set)`, and Infinity asks only for the left half, so this
/// is [`and_left`] generalised over the witness and pushed under the
/// existential by [`crate::exists_mono`].
///
/// The premise is checked, not trusted: the left conjunct of the opened body
/// must be exactly [`crate::recursion::inductive`] at the `succ` and `zero`
/// handed in, so a theorem about some other successor operation — the power-set
/// one of [`crate::empty::induction`], say — is rejected rather than relabelled.
pub fn infinity_from_least(
    env: &mut Env,
    succ: FnSym,
    zero: &Term,
    least_exists: &Thm,
) -> Option<Thm> {
    let i = env.fresh_var();
    let ti = Term::var(i);
    let body = open_exists(least_exists.concl(), &ti)?;
    let (ind, minimal) = split_and(&body)?;
    if ind != inductive(env, succ, zero, &ti) {
        return None
    }
    // ⊢ ∀I. ((Ind(0,I) ∧ Least-tail) → Ind(0,I)), then under the existential.
    let step = Thm::gen(i, &and_left(ind, minimal));
    let mono = exists_mono(i, &step)?;
    Thm::mp(&mono, least_exists)
}

/// `⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))` — **the axiom of Infinity, as a
/// theorem**, in the form of Jech §1 and Kunen I.2.
///
/// [`crate::recursion::omega_exists`] followed by [`infinity_from_least`].
pub fn infinity(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    succ: FnSym,
    succ_ax: &Thm,
    empty_ax: &Thm,
) -> Option<Thm> {
    let zero = zero_of(env, empty_ax)?;
    let least = omega_exists(env, pow, pow_ax, succ, succ_ax, empty_ax)?;
    infinity_from_least(env, succ, &zero, &least)
}

// ─────────────────────────────────────────────────────────────────────────────
// The same sentence with the two defined symbols eliminated.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∃I. (∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e)) ∧ ∀n. (n ∈ I → ∃s. (s ∈ I ∧ ∀z. (z ∈ s ↔ (z ∈ n ∨ z = n)))))`
/// — Infinity with `∅` and `succ` unabbreviated, so that no function symbol
/// occurs and the sentence lives in the pure language of `∈`.
///
/// Two existential introductions, at the witnesses `∅` and `succ(n)`, and the
/// obligations they leave are precisely `empty_ax` and `succ_ax` instantiated.
/// The bookkeeping is what a Hilbert system charges for pushing the resulting
/// implication under `∀n` (by [`Thm::ax_dist`], whose side condition holds
/// because `n` is fresh) and then under `∃I` (by [`crate::exists_mono`]).
pub fn infinity_primitive(
    env: &mut Env,
    succ: FnSym,
    succ_ax: &Thm,
    empty_ax: &Thm,
    infinity: &Thm,
) -> Option<Thm> {
    let zero = zero_of(env, empty_ax)?;
    let i = env.fresh_var();
    let ti = Term::var(i);
    let body = open_exists(infinity.concl(), &ti)?;
    let (has_zero, closed) = split_and(&body)?;
    if has_zero != Formula::mem(zero.clone(), ti.clone()) {
        return None
    }

    // ── `0 ∈ I  →  ∃e. (e ∈ I ∧ ∀z. ¬(z ∈ e))` ──────────────────────────────
    let e = env.fresh_var();
    let te = Term::var(e);
    let phi_e = Formula::and(Formula::mem(te.clone(), ti.clone()), is_empty_set(env, &te));
    // ⊢ (0 ∈ I ∧ ∀z. ¬(z ∈ 0)) → ∃e. …, and the left half is `empty_ax` itself.
    let intro_e = exists_intro_imp(e, phi_e.clone(), zero.clone())?;
    let pack_e = hyp_and(&imp_refl(has_zero.clone()), &a1i(empty_ax, has_zero.clone()))?;
    let part_zero = syl(&pack_e, &intro_e)?;

    // ── `∀n. (n ∈ I → succ n ∈ I)  →  ∀n. (n ∈ I → ∃s. …)` ──────────────────
    let (n, s) = (env.fresh_var(), env.fresh_var());
    let (tn, ts) = (Term::var(n), Term::var(s));
    let sn = Term::apply(succ, vec![tn.clone()]);
    let psi_s = Formula::and(
        Formula::mem(ts.clone(), ti.clone()),
        is_successor_of(env, &ts, &tn),
    );
    let mem_sn = Formula::mem(sn.clone(), ti.clone());
    let mem_n = Formula::mem(tn.clone(), ti.clone());

    let intro_s = exists_intro_imp(s, psi_s.clone(), sn.clone())?;
    let succ_inst = inst_all(succ_ax, std::slice::from_ref(&tn))?;
    let pack_s = hyp_and(&imp_refl(mem_sn.clone()), &a1i(&succ_inst, mem_sn.clone()))?;
    // ⊢ succ n ∈ I → ∃s. (s ∈ I ∧ IsSucc(s, n))
    let succ_to_ex = syl(&pack_s, &intro_s)?;

    // Under the hypothesis `closed`: instantiate at `n`, then weaken the
    // consequent through `succ_to_ex`.
    let inst_closed = Thm::ax_inst(closed.clone(), tn.clone())?;
    let bridge = a1i(&imp_mono_r(&succ_to_ex, mem_n.clone())?, closed.clone());
    let under_closed = hyp_mp(&bridge, &inst_closed)?;
    let goal_n = Formula::imp(mem_n, Formula::exists(s, psi_s));
    let dist = Thm::ax_dist(n, closed.clone(), goal_n)?;
    let part_succ = Thm::mp(&dist, &Thm::gen(n, &under_closed))?;

    // ── glue, then back under the existential ───────────────────────────────
    let left = syl(&and_left(has_zero.clone(), closed.clone()), &part_zero)?;
    let right = syl(&and_right(has_zero, closed), &part_succ)?;
    let both = hyp_and(&left, &right)?;
    let mono = exists_mono(i, &Thm::gen(i, &both))?;
    Thm::mp(&mono, infinity)
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ t ∈ succ(t)`.
///
/// The successor characterisation at `z := t`, whose right disjunct is `t = t`.
fn mem_succ_self(succ_ax: &Thm, t: &Term) -> Option<Thm> {
    // ⊢ t ∈ succ(t) ↔ (t ∈ t ∨ t = t)
    let inst = inst_all(succ_ax, &[t.clone(), t.clone()])?;
    let right = Thm::mp(
        &or_intro_right(
            Formula::mem(t.clone(), t.clone()),
            Formula::eq(t.clone(), t.clone()),
        ),
        &Thm::eq_refl(t.clone()),
    )?;
    Thm::mp(&iff_mpr(&inst)?, &right)
}

/// `⊢ ¬(t = succ(t))`.
///
/// `t ∈ succ(t)` by [`mem_succ_self`]; if `t` were `succ(t)` that would be
/// `t ∈ t`, which [`crate::empty::no_self_mem`] refutes.
fn succ_ne_self(
    env: &mut Env,
    succ: FnSym,
    succ_ax: &Thm,
    no_self: &Thm,
    t: &Term,
) -> Option<Thm> {
    let st = Term::apply(succ, vec![t.clone()]);
    let self_mem = mem_succ_self(succ_ax, t)?;
    let not_tt = inst_all(no_self, std::slice::from_ref(t))?;

    let x = env.fresh_var();
    // ⊢ succ t = t → (t ∈ succ t → t ∈ t)
    let leib = Thm::eq_leibniz(st.clone(), t.clone(), x, Formula::mem(t.clone(), Term::var(x)));
    // ⊢ t = succ t → (t ∈ succ t → t ∈ t)
    let flipped = syl(&eq_symm_imp(env, t.clone(), st), &leib)?;
    // ⊢ t = succ t → t ∈ t, then compose with ¬(t ∈ t).
    syl(&mpd_const(&flipped, &self_mem)?, &not_tt)
}

/// `⊢ ∀I. ((0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I)) → ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))`
/// — **every** inductive set has at least two members.
///
/// Stated for all `I` rather than for the witness [`infinity`] happens to
/// produce, so it rules out a trivial model of the statement rather than just
/// reporting on one particular set. The two members are `0` and `succ(0)`, and
/// they are distinct by [`succ_ne_self`].
pub fn inductive_two_members(
    env: &mut Env,
    succ: FnSym,
    succ_ax: &Thm,
    empty_ax: &Thm,
    no_self: &Thm,
) -> Option<Thm> {
    let zero = zero_of(env, empty_ax)?;
    let sz = Term::apply(succ, vec![zero.clone()]);

    let i = env.fresh_var();
    let ti = Term::var(i);
    let ind = inductive(env, succ, &zero, &ti);
    let (has_zero, closed) = split_and(&ind)?;

    // ⊢ Ind(0,I) → 0 ∈ I   and   ⊢ Ind(0,I) → succ 0 ∈ I
    let h_zero = and_left(has_zero.clone(), closed.clone());
    let h_closed = and_right(has_zero.clone(), closed.clone());
    let inst_closed = syl(&h_closed, &Thm::ax_inst(closed.clone(), zero.clone())?)?;
    let h_succ = hyp_mp(&inst_closed, &h_zero)?;

    // ⊢ Ind(0,I) → ¬(0 = succ 0)
    let distinct = a1i(&succ_ne_self(env, succ, succ_ax, no_self, &zero)?, ind.clone());
    let witness = hyp_and(&h_zero, &hyp_and(&h_succ, &distinct)?)?;

    // ∃b. (0 ∈ I ∧ (b ∈ I ∧ ¬(0 = b))), then ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b)))
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let chi_ab = Formula::and(
        Formula::mem(ta.clone(), ti.clone()),
        Formula::and(
            Formula::mem(tb.clone(), ti.clone()),
            Formula::not(Formula::eq(ta.clone(), tb.clone())),
        ),
    );
    let chi_zero_b = chi_ab.subst(a, &zero);
    let intro_b = exists_intro_imp(b, chi_zero_b, sz)?;
    let intro_a = exists_intro_imp(a, Formula::exists(b, chi_ab), zero)?;

    let full = syl(&syl(&witness, &intro_b)?, &intro_a)?;
    Some(Thm::gen(i, &full))
}

/// `⊢ ∃I. ((0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I)) ∧ ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))`
/// — Infinity with the non-vacuity carried inside the existential.
///
/// [`infinity`] and [`inductive_two_members`] do not compose by modus ponens —
/// one is an `∃`, the other a `∀` — so the conjunction is formed under the
/// quantifier. This is the statement to quote when the question is "could the
/// witness be trivial": it says the set Infinity produces is one that has two
/// distinct members, rather than saying that separately about all inductive
/// sets and leaving the reader to put the two together.
pub fn infinity_nonvacuous(env: &mut Env, infinity: &Thm, two: &Thm) -> Option<Thm> {
    let i = env.fresh_var();
    let ti = Term::var(i);
    let ind = open_exists(infinity.concl(), &ti)?;
    let step = Thm::mp(&Thm::ax_inst(two.concl().clone(), ti)?, two)?;
    let both = hyp_and(&imp_refl(ind), &step)?;
    let mono = exists_mono(i, &Thm::gen(i, &both))?;
    Thm::mp(&mono, infinity)
}

// ─────────────────────────────────────────────────────────────────────────────
// The bundle.
// ─────────────────────────────────────────────────────────────────────────────

/// Infinity in all three forms, over **one** chain of definitional extensions.
///
/// Building this twice would mint two unrelated pairings, two unrelated empty
/// sets and two unrelated successors, and a theorem about one would say nothing
/// about the other — the same hazard [`crate::recursion::OmegaCore`] exists to
/// avoid, and the reason [`Infinity::with_sets`] takes a caller-supplied
/// [`Sets`].
pub struct Infinity {
    /// Pairing and union.
    pub sets: Sets,
    /// The power set.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// `∅`, the zero.
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)`.
    pub empty_ax: Thm,
    /// `succ(n) = n ∪ {n}`.
    pub succ: FnSym,
    /// `⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))`.
    pub succ_ax: Thm,
    /// `⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))` — Jech §1, Kunen I.2.
    pub statement: Thm,
    /// The same sentence in the pure language of `∈`.
    pub primitive: Thm,
    /// `⊢ ∀I. (Ind(0,I) → ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))`.
    pub two_members: Thm,
    /// `⊢ ∃I. (Ind(0,I) ∧ ∃a ∃b. (a ∈ I ∧ (b ∈ I ∧ ¬(a = b))))`.
    pub nonvacuous: Thm,
}

impl Infinity {
    /// Derive everything over a **caller-supplied** [`Sets`], so the pairing can
    /// be shared with the rest of a development.
    pub fn with_sets(env: &mut Env, sets: Sets) -> Option<Infinity> {
        let mem_sing = mem_singleton(env, sets.up, &sets.up_ax)?;
        let no_self = no_self_mem(env, sets.up, &mem_sing)?;
        let (pow, pow_ax) = crate::power(env);
        let (empty, empty_ax) = crate::empty::empty(env);
        let (succ, succ_ax) = successor(env, &sets, &mem_sing)?;

        let statement = infinity(env, pow, &pow_ax, succ, &succ_ax, &empty_ax)?;
        let primitive = infinity_primitive(env, succ, &succ_ax, &empty_ax, &statement)?;
        let two_members = inductive_two_members(env, succ, &succ_ax, &empty_ax, &no_self)?;
        let nonvacuous = infinity_nonvacuous(env, &statement, &two_members)?;

        Some(Infinity {
            sets,
            pow,
            pow_ax,
            empty,
            empty_ax,
            succ,
            succ_ax,
            statement,
            primitive,
            two_members,
            nonvacuous,
        })
    }

    /// The same, minting a fresh [`Sets`].
    pub fn new(env: &mut Env) -> Option<Infinity> {
        let sets = Sets::new(env);
        Infinity::with_sets(env, sets)
    }

    /// The term `0`, i.e. `∅`.
    pub fn zero(&self) -> Term { Term::apply(self.empty, vec![]) }

    /// The term `succ(t)`.
    pub fn succ_of(&self, t: Term) -> Term { Term::apply(self.succ, vec![t]) }
}
