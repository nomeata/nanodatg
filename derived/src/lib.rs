//! Derived inference rules and conservative constructions.
//!
//! **Nothing here is trusted.** These are ordinary functions that can only
//! reach a [`Thm`] by calling the kernel's primitive rules, so a bug produces a
//! rejection or an unwanted-but-derivable theorem, never an underivable one.
//! They live outside `kernel/` so that proof-engineering convenience does not
//! inflate the crate that has to be correct.
//!
//! # Working without a deduction theorem
//!
//! The kernel is Hilbert style, because `Thm` must be a formula with no
//! context. A consequence is that there is no deduction theorem available as a
//! meta-rule: discharging an assumption would mean inducting over a stored
//! derivation, and derivations are deliberately never stored. So implications
//! have to be *built* from the `S` and `K` combinators rather than discharged.
//!
//! That is workable but verbose, which is exactly why this library exists:
//! [`imp_refl`], [`a1i`], [`mp_const`] and friends are the small change that
//! makes larger derivations tolerable to write.
//!
//! # Not tactics
//!
//! A tactic, in the LCF sense, is goal-directed: it takes a goal to subgoals
//! plus a validation, and runs backwards. Everything here runs *forwards*, from
//! theorems to theorems, and the crate also holds conservative constructions —
//! defined symbols together with their characteristic theorems — which are not
//! inference rules at all.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

// Larger constructions live in their own modules, so that each can be worked on
// (and reviewed) independently of the core toolkit below.
pub mod acc;
pub mod anchor;
pub mod bound;
pub mod cantor;
pub mod choice;
pub mod cumul;
pub mod empty;
pub mod enums;
pub mod ext;
pub mod fibre;
pub mod finset;
pub mod funcs;
pub mod funspace;
pub mod hyp;
pub mod inductive;
pub mod infinity;
pub mod isum;
pub mod pairs;
pub mod point_fun;
pub mod prelude;
pub mod proj;
pub mod prop;
pub mod quot;
pub mod rec_acc;
pub mod recarg;
pub mod recursion;
pub mod separation;
pub mod sigma;
pub mod skeleton;
pub mod sums;
pub mod tower;
pub mod twopoint;
pub mod universe;
pub mod wbool_rec;
pub mod wlist;
pub mod wlist_fun;
pub mod wlist_rec;
pub mod wnat;
pub mod wnat_rec;
pub mod wrec;
pub mod wrec_extend;
pub mod wrec_total;
pub mod wrec_typing;
pub mod wrec_unit;
pub mod wtype;

/// Indexed inductive families — `crate::inductive::family` under the name the
/// design and the checker-facing interface use.
///
/// It lives inside [`inductive`] because it consumes that module's private step
/// apparatus (the `good` recursion is the *same* Replacement/union/ι machinery
/// at a different value slot, `crate::inductive::step::Vals`), and it is
/// re-exported here because it is a construction in its own right and a
/// consumer should not have to know which module owns the step.
pub use inductive::family;

/// The house rule for a caller-supplied theorem: `thm` **establishes** `want`.
///
/// A [`Thm`] is a sequent `Γ ⊢ φ`, and it establishes `φ` only when `Γ` is
/// empty — `concl()` alone is what the theorem would say *if* its hypotheses
/// were discharged. So every public entry that takes a `&Thm` and hands back a
/// theorem documented `⊢ …` owes two checks, not one:
///
/// * `hyps().is_empty()` — otherwise [`Thm::mp`] silently unions the caller's
///   `Γ` into the result, which then carries an antecedent the header denies;
/// * `concl() == want` — otherwise the derivation runs on the wrong statement.
///
/// This helper is deliberately *not* a wrapper that computes `want` itself:
/// the pin is the valuable half, and which formula is being pinned has to stay
/// visible at the call site. All it removes is the repeated conjunction.
///
/// The companion for a *bundle* of theorems (a struct whose fields are each
/// documented `⊢ …`, pinned individually or by the struct's own constructor)
/// is [`all_unconditional`].
pub fn establishes(thm: &Thm, want: &Formula) -> bool {
    thm.hyps().is_empty() && *thm.concl() == *want
}

/// The hypothesis half of [`establishes`], for a bundle of theorems.
///
/// Use where a construction consumes an apparatus struct whose fields are
/// documented `⊢ …`: the conclusions are the struct's own business (its `over`
/// constructor pins them, or the derivation's kernel joins force them), but the
/// hypothesis leg is not checked anywhere else and a hypothetical field would
/// ride into the output under an unconditional label.
pub fn all_unconditional(thms: &[&Thm]) -> bool { thms.iter().all(|t| t.hyps().is_empty()) }

/// Derived: `⊢ φ → φ`.
///
/// The standard `S`/`K` derivation. Note there is no deduction theorem
/// available as a meta-rule here — that would require inducting over a
/// stored derivation, and derivations are deliberately not stored — so
/// implications have to be *built* from the combinators rather than
/// discharged from an assumption. This little library is what makes that
/// tolerable.
pub fn imp_refl(phi: Formula) -> Thm {
    let s = Thm::ax_s(phi.clone(), Formula::imp(phi.clone(), phi.clone()), phi.clone());
    let k1 = Thm::ax_k(phi.clone(), Formula::imp(phi.clone(), phi.clone()));
    let step = Thm::mp(&s, &k1).expect("imp_refl: S/K shapes line up by construction");
    let k2 = Thm::ax_k(phi.clone(), phi);
    Thm::mp(&step, &k2).expect("imp_refl: S/K shapes line up by construction")
}

/// Derived: from `⊢ φ` infer `⊢ ψ → φ` (weakening).
pub fn a1i(thm: &Thm, psi: Formula) -> Thm {
    let k = Thm::ax_k(thm.concl().clone(), psi);
    Thm::mp(&k, thm).expect("a1i: K shape lines up by construction")
}

/// Derived: from `⊢ φ` infer `⊢ (φ → χ) → χ`.
///
/// The workhorse for discharging a known fact against a hypothetical
/// implication, which is how "assume `h`, apply it to the thing we already
/// know" is expressed without a deduction theorem.
pub fn mp_const(phi_thm: &Thm, chi: Formula) -> Thm {
    let phi = phi_thm.concl().clone();
    let a = Formula::imp(phi.clone(), chi.clone());
    // S : (A → (φ → χ)) → ((A → φ) → (A → χ)), with A itself `φ → χ`.
    let s = Thm::ax_s(a.clone(), phi.clone(), chi);
    let refl = imp_refl(a.clone());
    let step = Thm::mp(&s, &refl).expect("mp_const: S shape lines up by construction");
    let a_to_phi = a1i(phi_thm, a);
    Thm::mp(&step, &a_to_phi).expect("mp_const: S shape lines up by construction")
}

/// Derived: from `⊢ φ` and `⊢ ψ` infer `⊢ φ ∧ ψ`.
///
/// `φ ∧ ψ` is `¬(φ → ¬ψ)`, i.e. `(φ → (ψ → ⊥)) → ⊥`. Apply the hypothesis
/// to `φ` to get `ψ → ⊥`, then to `ψ` to get `⊥`.
pub fn and_intro(phi: &Thm, psi: &Thm) -> Thm {
    let not_psi = Formula::not(psi.concl().clone());
    let h = Formula::imp(phi.concl().clone(), not_psi.clone());
    // ⊢ h → ¬ψ
    let h_to_notpsi = mp_const(phi, not_psi);
    // S : (h → (ψ → ⊥)) → ((h → ψ) → (h → ⊥))
    let s = Thm::ax_s(h.clone(), psi.concl().clone(), Formula::false_());
    let step = Thm::mp(&s, &h_to_notpsi).expect("and_intro: S shape lines up by construction");
    let h_to_psi = a1i(psi, h);
    Thm::mp(&step, &h_to_psi).expect("and_intro: S shape lines up by construction")
}

/// Derived existential introduction: from `⊢ φ[t/v]` infer `⊢ ∃v. φ`.
///
/// `∃v. φ` is `¬∀v. ¬φ`. Instantiating `∀v. ¬φ` at `t` yields `¬φ[t/v]`,
/// which contradicts the premise.
pub fn exists_intro(v: FreeVar, phi: Formula, t: Term, witness: &Thm) -> Option<Thm> {
    // The premise must actually be the instance claimed.
    if *witness.concl() != phi.subst(v, &t) {
        return None
    }
    let all_not = Formula::forall(v, Formula::not(phi));
    // ⊢ (∀v. ¬φ) → ¬φ[t/v]
    let inst = Thm::ax_inst(all_not.clone(), t)?;
    // S : (A → (φ[t] → ⊥)) → ((A → φ[t]) → (A → ⊥))
    let s = Thm::ax_s(all_not.clone(), witness.concl().clone(), Formula::false_());
    let step = Thm::mp(&s, &inst)?;
    let a_to_w = a1i(witness, all_not);
    Thm::mp(&step, &a_to_w)
}

/// Derived: from `⊢ a = b` infer `⊢ b = a`.
///
/// Take `φ(x) := (x = a)`. Leibniz gives `a = b → (a = a → b = a)`; discharge
/// the antecedent with reflexivity.
pub fn eq_symm(env: &mut Env, ab: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    let x = env.fresh_var();
    let phi = Formula::eq(Term::var(x), a.clone());
    let leib = Thm::eq_leibniz(a.clone(), b, x, phi);
    let step = Thm::mp(&leib, ab)?;
    Thm::mp(&step, &Thm::eq_refl(a))
}

/// Derived: from `⊢ a = b` and `⊢ b = c` infer `⊢ a = c`.
///
/// Take `φ(x) := (a = x)`. Leibniz on `b = c` gives
/// `b = c → (a = b → a = c)`.
pub fn eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
    let (a, b1) = ab.concl().as_eq()?;
    let (b2, c) = bc.concl().as_eq()?;
    if b1 != b2 {
        return None
    }
    let x = env.fresh_var();
    let phi = Formula::eq(a.clone(), Term::var(x));
    let leib = Thm::eq_leibniz(b1, c, x, phi);
    let step = Thm::mp(&leib, bc)?;
    Thm::mp(&step, ab)
}

/// Derived congruence: from `⊢ a = b` infer
/// `⊢ f(t₀..a..tₙ) = f(t₀..b..tₙ)`, replacing argument `idx`.
///
/// Take `φ(x) := f(..a..) = f(..x..)`. Leibniz on `a = b` turns
/// `f(..a..) = f(..a..)` (reflexivity) into `f(..a..) = f(..b..)`.
pub fn congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    if idx >= args.len() || args.get(idx) != Some(&a) {
        return None
    }
    let lhs = Term::apply(f, args.to_vec());

    let x = env.fresh_var();
    let mut hole = args.to_vec();
    hole[idx] = Term::var(x);
    let phi = Formula::eq(lhs.clone(), Term::apply(f, hole));

    let leib = Thm::eq_leibniz(a, b, x, phi);
    let step = Thm::mp(&leib, ab)?;
    Thm::mp(&step, &Thm::eq_refl(lhs))
}

/// Derived: congruence in every argument at once. Given `⊢ aᵢ = bᵢ` for each
/// position, infer `⊢ f(a₀..aₙ) = f(b₀..bₙ)` by rewriting one position at a
/// time and chaining with transitivity.
pub fn congr(env: &mut Env, f: FnSym, eqs: &[Thm]) -> Option<Thm> {
    let mut args: Vec<Term> = Vec::with_capacity(eqs.len());
    for e in eqs {
        args.push(e.concl().as_eq()?.0);
    }
    if args.len() != f.arity() as usize {
        return None
    }
    let mut acc = Thm::eq_refl(Term::apply(f, args.clone()));
    for (i, e) in eqs.iter().enumerate() {
        let step = congr_arg(env, f, &args, i, e)?;
        // Advance the running argument list to the rewritten form.
        args[i] = e.concl().as_eq()?.1;
        acc = eq_trans(env, &acc, &step)?;
    }
    Some(acc)
}

// ─────────────────────────────────────────────────────────────────────────────
// Conservative constructions.
//
// The guiding rule: if something can be *constructed* conservatively, construct
// it — never add it as a feature of the target logic. Everything below is
// obtained from the kernel's primitives plus `kernel::thm::define`, which is
// itself conservative (extension by definitions). None of it enlarges the
// trusted base.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀x⃗. ∃!y. y = t`, the trivial existence-and-uniqueness.
///
/// This is the workhorse behind explicit definitions. A *term* denotes a unique
/// object by construction, so whenever the thing being defined is already
/// expressible as a term, the conservativity obligation costs nothing — which
/// is why an explicit definition is always available for free, and only
/// implicit ones (defining a set by a property) need real work.
pub fn exists_unique_eq(env: &mut Env, xs: &[FreeVar], t: &Term) -> (FreeVar, Formula, Thm) {
    let y = env.fresh_var();
    let phi = Formula::eq(Term::var(y), t.clone());

    // Prove the ∃-body at the witness y := t.
    let refl = Thm::eq_refl(t.clone());
    let y2 = env.fresh_var();
    let uniq = Thm::gen(y2, &imp_refl(Formula::eq(Term::var(y2), t.clone())));
    let body_at_t = and_intro(&refl, &uniq);

    // Rebuild the ∃-body in the shape `kernel::thm::exists_unique` produces, so
    // the witness lines up exactly.
    let y3 = env.fresh_var();
    let u = Formula::forall(
        y3,
        Formula::imp(phi.subst(y, &Term::var(y3)), Formula::eq(Term::var(y3), Term::var(y))),
    );
    let body = Formula::and(phi.clone(), u);

    let ex = exists_intro(y, body, t.clone(), &body_at_t)
        .expect("exists_unique_eq: witness matches the ∃ body by construction");
    let all = xs.iter().rev().fold(ex, |acc, x| Thm::gen(*x, &acc));
    (y, phi, all)
}

/// Introduce an explicit definition `f(x⃗) := t(x⃗)` and return its defining
/// equation `⊢ ∀x⃗. f(x⃗) = t(x⃗)`.
///
/// Always available, always conservative: the `∃!` premise that
/// `kernel::thm::define` demands is discharged by [`exists_unique_eq`], which
/// holds for any term whatever. This is the cheap half of definitional
/// extension — the half that covers Lean's `def`, where a constant is simply an
/// abbreviation for its value.
/// # Precondition
///
/// Every free variable of `t` must be among `xs`. Otherwise the definition
/// would be **unsound**: `f() := g(a,b)` with `a`, `b` free yields
/// `⊢ ∀a ∀b. f = g(a,b)`, hence `g(a₁,b) = g(a₂,b)` for arbitrary `a₁, a₂`.
/// `kernel::thm::define` enforces this, and this function returns `None` when
/// it refuses rather than panicking, so callers that build terms dynamically
/// can fall back gracefully.
pub fn define_abbrev(env: &mut Env, xs: &[FreeVar], t: &Term) -> Option<(FnSym, Thm)> {
    let (y, phi, witness) = exists_unique_eq(env, xs, t);
    kernel::thm::define(env, xs, y, phi, &witness)
}

/// From `⊢ ∀x⃗. φ` and a list of terms, instantiate all the leading
/// quantifiers in order.
pub fn inst_all(thm: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = thm.clone();
    for t in ts {
        let step = Thm::ax_inst(cur.concl().clone(), t.clone())?;
        cur = Thm::mp(&step, &cur)?;
    }
    Some(cur)
}

// ─────────────────────────────────────────────────────────────────────────────
// Propositional toolkit.
//
// Everything below is derivable from the three Łukasiewicz axioms plus modus
// ponens. It exists because a Hilbert system has no deduction theorem to lean
// on: an implication has to be *assembled*, and without these it is unreadable.
// ─────────────────────────────────────────────────────────────────────────────

/// Syllogism: from `⊢ φ → ψ` and `⊢ ψ → χ` infer `⊢ φ → χ`.
pub fn syl(ab: &Thm, bc: &Thm) -> Option<Thm> {
    let (a, b1) = ab.concl().as_imp()?;
    let (b2, c) = bc.concl().as_imp()?;
    if b1 != b2 {
        return None
    }
    // S : (a → (b → c)) → ((a → b) → (a → c)), with `a → (b → c)` from weakening.
    let s = Thm::ax_s(a.clone(), b1, c);
    let weak = a1i(bc, a);
    let step = Thm::mp(&s, &weak)?;
    Thm::mp(&step, ab)
}

/// Monotonicity in the consequent: from `⊢ γ → δ` infer `⊢ (φ → γ) → (φ → δ)`.
pub fn imp_mono_r(gd: &Thm, phi: Formula) -> Option<Thm> {
    let (g, d) = gd.concl().as_imp()?;
    let s = Thm::ax_s(phi.clone(), g, d);
    let weak = a1i(gd, phi);
    Thm::mp(&s, &weak)
}

/// Swap antecedents: from `⊢ α → (β → γ)` infer `⊢ β → (α → γ)`.
pub fn com12(t: &Thm) -> Option<Thm> {
    let (a, rest) = t.concl().as_imp()?;
    let (b, c) = rest.as_imp()?;
    let s = Thm::ax_s(a.clone(), b.clone(), c);
    let step = Thm::mp(&s, t)?; // (α → β) → (α → γ)
    let k = Thm::ax_k(b, a); // β → (α → β)
    syl(&k, &step)
}

/// Ex falso: `⊢ ⊥ → φ`.
pub fn ex_falso(phi: Formula) -> Thm {
    // Contraposition with ψ := ⊥, whose negation `⊥ → ⊥` is reflexivity.
    let contra = Thm::ax_contra(phi.clone(), Formula::false_());
    let not_false = imp_refl(Formula::false_());
    let anti = a1i(&not_false, Formula::not(phi));
    Thm::mp(&contra, &anti).expect("ex_falso: shapes line up by construction")
}

/// Double-negation introduction: `⊢ φ → ¬¬φ`.
pub fn notnot_intro(phi: Formula) -> Thm {
    // `¬¬φ` is `(φ → ⊥) → ⊥`, so this is `imp_refl(φ → ⊥)` with its antecedents
    // swapped.
    let refl = imp_refl(Formula::not(phi));
    com12(&refl).expect("notnot_intro: com12 applies by construction")
}

/// Double-negation elimination: `⊢ ¬¬φ → φ`. Classical.
pub fn notnot_elim(phi: Formula) -> Thm {
    let contra = Thm::ax_contra(phi.clone(), Formula::not(Formula::not(phi.clone())));
    let anti = notnot_intro(Formula::not(phi));
    Thm::mp(&contra, &anti).expect("notnot_elim: shapes line up by construction")
}

/// Left conjunct: `⊢ (φ ∧ ψ) → φ`.
pub fn and_left(phi: Formula, psi: Formula) -> Thm {
    let conj = Formula::and(phi.clone(), psi.clone());
    let inner = Formula::imp(phi.clone(), Formula::not(psi.clone()));
    // ¬φ → (φ → ¬ψ): from ¬φ, i.e. φ → ⊥, weaken ⊥ up to ¬ψ.
    let notphi_to_inner = imp_mono_r(&ex_falso(Formula::not(psi.clone())), phi.clone())
        .expect("and_left: monotonicity applies");
    let notphi_to_nn = syl(&notphi_to_inner, &notnot_intro(inner)).expect("and_left: syllogism applies");
    let contra = Thm::ax_contra(phi, conj);
    Thm::mp(&contra, &notphi_to_nn).expect("and_left: contraposition applies")
}

/// Right conjunct: `⊢ (φ ∧ ψ) → ψ`.
pub fn and_right(phi: Formula, psi: Formula) -> Thm {
    let conj = Formula::and(phi.clone(), psi.clone());
    let inner = Formula::imp(phi.clone(), Formula::not(psi.clone()));
    // ¬ψ → (φ → ¬ψ) is just weakening.
    let k = Thm::ax_k(Formula::not(psi.clone()), phi);
    let notpsi_to_nn = syl(&k, &notnot_intro(inner)).expect("and_right: syllogism applies");
    let contra = Thm::ax_contra(psi, conj);
    Thm::mp(&contra, &notpsi_to_nn).expect("and_right: contraposition applies")
}

/// From `⊢ φ ∧ ψ` infer `⊢ φ`.
pub fn and_elim_left(t: &Thm) -> Option<Thm> {
    let (imp, _) = t.concl().as_imp()?; // φ ∧ ψ is ¬(φ → ¬ψ)
    let (phi, notpsi) = imp.as_imp()?;
    let (psi, _) = notpsi.as_imp()?;
    Thm::mp(&and_left(phi, psi), t)
}

/// From `⊢ φ ∧ ψ` infer `⊢ ψ`.
pub fn and_elim_right(t: &Thm) -> Option<Thm> {
    let (imp, _) = t.concl().as_imp()?;
    let (phi, notpsi) = imp.as_imp()?;
    let (psi, _) = notpsi.as_imp()?;
    Thm::mp(&and_right(phi, psi), t)
}

/// Forward direction of a biconditional: from `⊢ φ ↔ ψ` infer `⊢ φ → ψ`.
pub fn iff_mp(t: &Thm) -> Option<Thm> { and_elim_left(t) }

/// Reverse direction of a biconditional: from `⊢ φ ↔ ψ` infer `⊢ ψ → φ`.
pub fn iff_mpr(t: &Thm) -> Option<Thm> { and_elim_right(t) }

// ─────────────────────────────────────────────────────────────────────────────
// Quantifier toolkit.
//
// The awkward part of Hilbert-style FOL. `∃` is `¬∀¬`, so existential reasoning
// runs through contraposition and the distribution axiom, whose free-variable
// side condition has to be arranged rather than assumed.
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ α → (β → γ)` and `⊢ β` infer `⊢ α → γ`.
pub fn mpd_const(abc: &Thm, b: &Thm) -> Option<Thm> {
    let (a, rest) = abc.concl().as_imp()?;
    let (b_f, c) = rest.as_imp()?;
    if b_f != *b.concl() {
        return None
    }
    let s = Thm::ax_s(a.clone(), b_f, c);
    let step = Thm::mp(&s, abc)?;
    Thm::mp(&step, &a1i(b, a))
}

/// Contraposition as a rule: from `⊢ φ → ψ` infer `⊢ ¬ψ → ¬φ`.
pub fn contrapos(ab: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_imp()?;
    // ⊢ ¬ψ → ((φ → ψ) → ¬φ), then discharge the inner premise.
    let s = Thm::ax_s(a.clone(), b.clone(), Formula::false_());
    let k = Thm::ax_k(Formula::not(b), a);
    let chained = syl(&k, &s)?;
    mpd_const(&chained, ab)
}

/// Instantiate `∀x. φ` at the variable `x` itself, recovering `φ`.
///
/// Sound and trivial in a locally nameless representation: `forall` closes over
/// `x`, so opening at `x` is the inverse.
pub fn inst_self(x: FreeVar, all: &Thm) -> Option<Thm> {
    let step = Thm::ax_inst(all.concl().clone(), Term::var(x))?;
    Thm::mp(&step, all)
}

/// From `⊢ ∀x.(φ → ψ)` infer `⊢ ∀x. φ → ∀x. ψ`.
///
/// Both uses of the distribution axiom below are legitimate because their
/// antecedents are themselves `∀x`-quantified, so `x` is bound rather than free
/// in them. The side condition is *arranged*, not wished away.
pub fn forall_mono(x: FreeVar, all_imp: &Thm) -> Option<Thm> {
    let a = all_imp.concl().clone();
    // ⊢ A → (φ → ψ); instantiating a `∀x` at `x` itself just reopens the body.
    let a_to_body = Thm::ax_inst(a.clone(), Term::var(x))?;
    let (_, body) = a_to_body.concl().as_imp()?;
    let (phi, psi) = body.as_imp()?;

    let b = Formula::forall(x, phi.clone());
    let b_to_phi = Thm::ax_inst(b.clone(), Term::var(x))?;

    // A → (φ → ψ)  ⟹  φ → (A → ψ)  ⟹  B → (A → ψ)  ⟹  A → (B → ψ)
    let phi_to_apsi = com12(&a_to_body)?;
    let b_to_apsi = syl(&b_to_phi, &phi_to_apsi)?;
    let a_to_bpsi = com12(&b_to_apsi)?;

    let gen_bpsi = Thm::gen(x, &a_to_bpsi);
    let dist1 = Thm::ax_dist(x, a, Formula::imp(b.clone(), psi.clone()))?;
    let a_to_all = Thm::mp(&dist1, &gen_bpsi)?;
    let dist2 = Thm::ax_dist(x, b, psi)?;
    // `syl` yields the implication form `⊢ ∀x.(φ→ψ) → (∀x.φ → ∀x.ψ)`; discharge
    // its antecedent so the result matches the rule form this function promises.
    let implication = syl(&a_to_all, &dist2)?;
    Thm::mp(&implication, all_imp)
}

/// From `⊢ ∀x.(φ → ψ)` infer `⊢ ∃x. φ → ∃x. ψ`.
///
/// `∃` is `¬∀¬`, so this runs by contraposing the implication under the
/// quantifier, applying [`forall_mono`], and contraposing back.
pub fn exists_mono(x: FreeVar, all_imp: &Thm) -> Option<Thm> {
    let a_to_body = Thm::ax_inst(all_imp.concl().clone(), Term::var(x))?;
    let (_, body) = a_to_body.concl().as_imp()?;
    let (phi, psi) = body.as_imp()?;

    // ⊢ ∀x.(¬ψ → ¬φ)
    let contra_body = contrapos(&Thm::mp(&a_to_body, all_imp)?)?;
    let all_contra = Thm::gen(x, &contra_body);
    // ⊢ ∀x.¬ψ → ∀x.¬φ
    let mono = forall_mono(x, &all_contra)?;
    // Contraposing gives ⊢ ¬∀x.¬φ → ¬∀x.¬ψ, which is ⊢ ∃x.φ → ∃x.ψ.
    let out = contrapos(&mono)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::exists(x, phi), Formula::exists(x, psi)),
        "exists_mono produced an unexpected shape"
    );
    Some(out)
}

/// Existential elimination: from `⊢ ∃x. φ` and `⊢ ∀x.(φ → ψ)` with `x` not free
/// in `ψ`, infer `⊢ ψ`.
///
/// The classic awkward rule. Route: contrapose the body, distribute `¬ψ` in
/// (legal because `x` is not free in it — checked), contrapose back to get
/// `∃x.φ → ¬¬ψ`, discharge, and strip the double negation.
pub fn exists_elim(x: FreeVar, ex: &Thm, all_imp: &Thm, psi: &Formula) -> Option<Thm> {
    if psi.occurs_free(x) {
        // Without this the rule is unsound: it would let a witness-dependent
        // conclusion escape the scope of its witness.
        return None
    }
    let a_to_body = Thm::ax_inst(all_imp.concl().clone(), Term::var(x))?;
    let body = Thm::mp(&a_to_body, all_imp)?;
    let (phi, psi_chk) = body.concl().as_imp()?;
    if psi_chk != *psi {
        return None
    }

    // ⊢ ∀x.(¬ψ → ¬φ)
    let all_contra = Thm::gen(x, &contrapos(&body)?);
    // ⊢ ¬ψ → ∀x.¬φ, legal since x is not free in ¬ψ.
    let dist = Thm::ax_dist(x, Formula::not(psi.clone()), Formula::not(phi.clone()))?;
    let notpsi_to_all = Thm::mp(&dist, &all_contra)?;
    // ⊢ ¬∀x.¬φ → ¬¬ψ, i.e. ⊢ ∃x.φ → ¬¬ψ
    let ex_to_nn = contrapos(&notpsi_to_all)?;
    let nn = Thm::mp(&ex_to_nn, ex)?;
    Thm::mp(&notnot_elim(psi.clone()), &nn)
}

/// Generalise over several variables, outermost first.
pub fn gen_all(xs: &[FreeVar], thm: &Thm) -> Thm {
    xs.iter().rev().fold(thm.clone(), |acc, x| Thm::gen(*x, &acc))
}

// ─────────────────────────────────────────────────────────────────────────────
// Reasoning under a fixed hypothesis.
//
// The closest a Hilbert system gets to a deduction theorem. Fix a hypothesis
// `H` and work with theorems of the form `⊢ H → φ`; [`hyp_mp`] then behaves
// like modus ponens inside that context. Every multi-hypothesis derivation
// below is written this way, with `H` a conjunction of the assumptions.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ (a → b) → ((b → c) → (a → c))` — syllogism, internalised as a formula.
pub fn syl_imp(a: Formula, b: Formula, c: Formula) -> Thm {
    let s = Thm::ax_s(a.clone(), b.clone(), c.clone());
    let k = Thm::ax_k(Formula::imp(b.clone(), c.clone()), a.clone());
    // (b→c) → ((a→b) → (a→c)), then swap.
    let bc_first = syl(&k, &s).expect("syl_imp: shapes line up by construction");
    com12(&bc_first).expect("syl_imp: com12 applies by construction")
}

/// `⊢ (a → (b → c)) → (b → (a → c))` — antecedent swap, internalised.
pub fn com12_imp(a: Formula, b: Formula, c: Formula) -> Thm {
    let t = Formula::imp(a.clone(), Formula::imp(b.clone(), c.clone()));
    let s = Thm::ax_s(a.clone(), b.clone(), c.clone()); // T → ((a→b) → (a→c))
    let k = Thm::ax_k(b.clone(), a.clone()); // b → (a→b)
    let bridge = syl_imp(b.clone(), Formula::imp(a.clone(), b.clone()), Formula::imp(a, c.clone()));
    // Under hypothesis T: from (a→b)→(a→c) and b→(a→b), conclude b→(a→c).
    let step = hyp_mp(&a1i(&bridge, t.clone()), &a1i(&k, t.clone())).expect("com12_imp");
    hyp_mp(&step, &s).expect("com12_imp: final application")
}

/// Modus ponens under a fixed hypothesis: from `⊢ H → (φ → ψ)` and `⊢ H → φ`
/// infer `⊢ H → ψ`.
pub fn hyp_mp(h_imp: &Thm, h_arg: &Thm) -> Option<Thm> {
    let (h1, rest) = h_imp.concl().as_imp()?;
    let (phi, psi) = rest.as_imp()?;
    let (h2, phi2) = h_arg.concl().as_imp()?;
    if h1 != h2 || phi != phi2 {
        return None
    }
    let s = Thm::ax_s(h1, phi, psi);
    let step = Thm::mp(&s, h_imp)?;
    Thm::mp(&step, h_arg)
}

/// `⊢ x → (y → (x ∧ y))` — conjunction introduction, internalised.
pub fn and_intro_imp(x: Formula, y: Formula) -> Thm {
    // `x ∧ y` is `(x → (y → ⊥)) → ⊥`; call the antecedent `h`.
    let h = Formula::imp(x.clone(), Formula::not(y.clone()));
    // ⊢ x → (h → (y → ⊥)), by swapping `⊢ h → (x → (y → ⊥))` (reflexivity).
    let x_to_h_ny = com12(&imp_refl(h.clone())).expect("and_intro_imp: com12");
    // Turn the consequent `h → (y → ⊥)` into `y → (h → ⊥)`; `¬h` is exactly
    // `x ∧ y`, so composing gives the goal directly.
    let swap = com12_imp(h, y, Formula::false_());
    let _ = x;
    syl(&x_to_h_ny, &swap).expect("and_intro_imp: syllogism applies by construction")
}

/// From `⊢ H → φ` and `⊢ H → ψ` infer `⊢ H → (φ ∧ ψ)`.
pub fn hyp_and(hp: &Thm, hq: &Thm) -> Option<Thm> {
    let (h1, phi) = hp.concl().as_imp()?;
    let (h2, psi) = hq.concl().as_imp()?;
    if h1 != h2 {
        return None
    }
    let intro = and_intro_imp(phi, psi);
    hyp_mp(&hyp_mp(&a1i(&intro, h1), hp)?, hq)
}

/// The **right-nested conjunction** `φ₀ ∧ (φ₁ ∧ (… ∧ φ_{n-1}))`, or `None` for
/// the empty list.
///
/// Right-nesting is the shape [`and_left`]/[`and_right`] take apart and the one
/// [`crate::sigma::Telescope`] and [`crate::inductive`] state their hypotheses
/// in, so every projection below is a walk down the right spine.
pub fn conj_of(atoms: &[Formula]) -> Option<Formula> {
    atoms.iter().rev().cloned().reduce(|acc, h| Formula::and(h, acc))
}

/// `⊢ conj_of(atoms) → atoms[i]` — project one conjunct out of a right-nested
/// conjunction. `None` if `i` is out of range.
pub fn conj_proj(atoms: &[Formula], i: usize) -> Option<Thm> {
    let n = atoms.len();
    if i >= n {
        return None
    }
    let mut th = imp_refl(conj_of(atoms)?);
    for (j, hj) in atoms.iter().enumerate().take(i) {
        th = syl(&th, &and_right(hj.clone(), conj_of(&atoms[j + 1..])?))?;
    }
    if i + 1 < n {
        th = syl(&th, &and_left(atoms[i].clone(), conj_of(&atoms[i + 1..])?))?;
    }
    Some(th)
}

/// `⊢ conj_of(atoms) → conj_of(atoms[start..end])` — project a contiguous run.
///
/// `None` when the run is empty, which is the caller's signal that the
/// sub-conjunction does not exist and the theorem it would have fed is
/// unconditional.
pub fn conj_sub(atoms: &[Formula], start: usize, end: usize) -> Option<Thm> {
    if start >= end || end > atoms.len() {
        return None
    }
    let mut parts: Vec<Thm> = (start..end).map(|i| conj_proj(atoms, i)).collect::<Option<_>>()?;
    let mut acc = parts.pop()?;
    while let Some(p) = parts.pop() {
        acc = hyp_and(&p, &acc)?;
    }
    Some(acc)
}

/// From `⊢ H → (φ ↔ ψ)` infer `⊢ H → (φ → ψ)`.
pub fn hyp_iff_mp(t: &Thm) -> Option<Thm> {
    let (_h, iff) = t.concl().as_imp()?;
    let (fwd, bwd) = split_iff(&iff)?;
    syl(t, &and_left(fwd, bwd))
}

/// From `⊢ H → (φ ↔ ψ)` infer `⊢ H → (ψ → φ)`.
pub fn hyp_iff_mpr(t: &Thm) -> Option<Thm> {
    let (_h, iff) = t.concl().as_imp()?;
    let (fwd, bwd) = split_iff(&iff)?;
    syl(t, &and_right(fwd, bwd))
}

/// Decompose `φ ↔ ψ` into its two implication halves.
fn split_iff(iff: &Formula) -> Option<(Formula, Formula)> {
    // `a ∧ b` is `¬(a → ¬b)`, i.e. `(a → (b → ⊥)) → ⊥`.
    let (inner, _) = iff.as_imp()?;
    let (fwd, nb) = inner.as_imp()?;
    let (bwd, _) = nb.as_imp()?;
    Some((fwd, bwd))
}

/// From `⊢ A → (B → X)` infer `⊢ (A ∧ B) → X`.
///
/// The dual of [`uncurry`], and the way out of the one shape the
/// hypothesis-form combinators cannot produce directly: they all conclude
/// `⊢ H → φ`, so a goal `⊢ H → (X → φ)` is reached by working under
/// `H ∧ X` and currying at the end.
pub fn curry(imp2: &Thm) -> Option<Thm> {
    let (a, rest) = imp2.concl().as_imp()?;
    let (b, x) = rest.as_imp()?;
    let conj = Formula::and(a.clone(), b.clone());
    // `(A ∧ B) → A` and `(A ∧ B) → B`, then apply.
    let ha = and_left(a.clone(), b.clone());
    let hb = and_right(a, b);
    let out = hyp_mp(&syl(&ha, imp2)?, &hb)?;
    debug_assert_eq!(*out.concl(), Formula::imp(conj, x), "curry: wrong shape");
    Some(out)
}

/// The **right-nested disjunction** `φ₀ ∨ (φ₁ ∨ (… ∨ φ_{n-1}))`, or `None` for
/// the empty list. The dual of [`conj_of`].
pub fn disj_of(atoms: &[Formula]) -> Option<Formula> {
    atoms.iter().rev().cloned().reduce(|acc, h| Formula::or(h, acc))
}

/// `⊢ atoms[i] → disj_of(atoms)` — inject into one position of a right-nested
/// disjunction. `None` if `i` is out of range.
///
/// The mirror image of [`crate::isum::inj_of`]: `i` uses of
/// [`crate::funcs::or_intro_right`] and, unless `i` is last, one
/// [`crate::funcs::or_intro_left`].
pub fn disj_inject(atoms: &[Formula], i: usize) -> Option<Thm> {
    let n = atoms.len();
    if i >= n {
        return None
    }
    let mut th = if i + 1 == n {
        imp_refl(atoms[i].clone())
    } else {
        funcs::or_intro_left(atoms[i].clone(), disj_of(&atoms[i + 1..])?)
    };
    for j in (0..i).rev() {
        th = syl(&th, &funcs::or_intro_right(atoms[j].clone(), disj_of(&atoms[j + 1..])?))?;
    }
    Some(th)
}

/// From `⊢ A → (B → X)` infer `⊢ (A ∧ B) → X` — the true converse of
/// [`uncurry`].
///
/// [`uncurry`] and [`crate::cumul::curry`] are, despite their names, the same
/// rule in the same direction, so neither is an inverse of the other. Under the
/// hypothesis `A ∧ B`: [`and_left`] feeds `A` to the premise to get `B → X`, and
/// [`and_right`] supplies `B`. No `assume`, and hence nothing a consumer
/// confining `Thm::implies_intr` to one module would have to do itself.
pub fn conjoin(t: &Thm) -> Option<Thm> {
    let (a, rest) = t.concl().as_imp()?;
    let (b, _x) = rest.as_imp()?;
    let left = syl(&and_left(a.clone(), b.clone()), t)?;
    hyp_mp(&left, &and_right(a, b))
}

/// From `⊢ (A ∧ B) → X` infer `⊢ A → (B → X)`.
pub fn uncurry(and_imp: &Thm) -> Option<Thm> {
    let (conj, x) = and_imp.concl().as_imp()?;
    let (inner, _) = conj.as_imp()?;
    let (a, nb) = inner.as_imp()?;
    let (b, _) = nb.as_imp()?;
    let intro = and_intro_imp(a, b.clone()); // A → (B → (A∧B))
    let mono = imp_mono_r(and_imp, b)?; // (B → (A∧B)) → (B → X)
    let _ = x;
    syl(&intro, &mono)
}

// ─────────────────────────────────────────────────────────────────────────────
// Set-theoretic constructions.
// ─────────────────────────────────────────────────────────────────────────────

/// Introduce a set specified by a **membership condition**, given a proof that
/// such a set exists.
///
/// From `⊢ ∃s. ∀z. (z ∈ s ↔ φ(z))` this derives the corresponding `∃!` — the
/// uniqueness coming from Extensionality, since two sets with the same members
/// are equal — and hands it to `kernel::thm::define`, returning the new symbol
/// together with `⊢ ∀params ∀z. (z ∈ f(params) ↔ φ(z))`.
///
/// This is the shape every basic set construction takes: Pairing, Union and
/// Power Set all assert existence of a set with a prescribed membership
/// condition, and all get their uniqueness from Extensionality. Factoring it
/// out means each construction costs only its existence axiom.
///
/// `phi` may mention `params` and must mention `z` as the element variable.
pub fn define_by_membership(
    env: &mut Env,
    params: &[FreeVar],
    existence: &Thm,
    z: FreeVar,
    phi: &Formula,
) -> Option<(FnSym, Thm)> {
    let ext = Thm::ax_extensionality(env);
    let (p, q) = (env.fresh_var(), env.fresh_var());
    let (tp, tq, tz) = (Term::var(p), Term::var(q), Term::var(z));

    // P(s) := ∀z. (z ∈ s ↔ φ(z))
    let prop = |s: &Term| Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), s.clone()), phi.clone()));
    let (pp, pq) = (prop(&tp), prop(&tq));

    // Check the caller really handed us `∃s. P(s)` for this very φ.
    if *existence.concl() != Formula::exists(p, pp.clone()) {
        return None
    }

    // Work under H := P(p) ∧ P(q).
    let h = Formula::and(pp.clone(), pq.clone());
    let mem_p = Formula::mem(tz.clone(), tp.clone());
    let mem_q = Formula::mem(tz.clone(), tq.clone());

    let h_iff_p = syl(&and_left(pp.clone(), pq.clone()), &Thm::ax_inst(pp.clone(), tz.clone())?)?;
    let h_iff_q = syl(&and_right(pp.clone(), pq.clone()), &Thm::ax_inst(pq.clone(), tz.clone())?)?;

    // Compose the four halves of the two biconditionals into `z ∈ q ↔ z ∈ p`.
    let bridge = |a: Formula, b: Formula, c: Formula, ab: &Thm, bc: &Thm| -> Option<Thm> {
        let s = a1i(&syl_imp(a, b, c), h.clone());
        hyp_mp(&hyp_mp(&s, ab)?, bc)
    };
    let h_qp = bridge(mem_q.clone(), phi.clone(), mem_p.clone(), &hyp_iff_mp(&h_iff_q)?, &hyp_iff_mpr(&h_iff_p)?)?;
    let h_pq = bridge(mem_p.clone(), phi.clone(), mem_q.clone(), &hyp_iff_mp(&h_iff_p)?, &hyp_iff_mpr(&h_iff_q)?)?;
    let h_iff = hyp_and(&h_qp, &h_pq)?;

    // Generalise z and pull the quantifier in; z is not free in H.
    let dist = Thm::ax_dist(z, h.clone(), Formula::iff(mem_q.clone(), mem_p.clone()))?;
    let h_same = Thm::mp(&dist, &Thm::gen(z, &h_iff))?;

    // Extensionality closes it.
    let ext_inst = inst_all(&ext, &[tq.clone(), tp.clone()])?;
    let h_eq = syl(&h_same, &ext_inst)?;

    // ⊢ P(p) → (P(q) → q = p), quantify q back in, bundle with existence.
    let gen_q = Thm::gen(q, &uncurry(&h_eq)?);
    let dist_q = Thm::ax_dist(q, pp.clone(), Formula::imp(pq, Formula::eq(tq, tp)))?;
    let p_to_uniq = Thm::mp(&dist_q, &gen_q)?;
    let step = hyp_and(&imp_refl(pp.clone()), &p_to_uniq)?;
    let ex_uniq = Thm::mp(&exists_mono(p, &Thm::gen(p, &step))?, existence)?;

    let all = gen_all(params, &ex_uniq);
    kernel::thm::define(env, params, p, prop(&Term::var(p)), &all)
}

/// The unordered pair `{x, y}`, with
/// `⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))`.
///
/// Existence is Pairing; uniqueness is Extensionality, via
/// [`define_by_membership`].
pub fn upair(env: &mut Env) -> (FnSym, Thm) {
    let pairing = Thm::ax_pairing(env);
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
    let existence = inst_all(&pairing, &[tx.clone(), ty.clone()]).expect("upair: instantiate Pairing");
    let phi = Formula::or(Formula::eq(tz.clone(), tx), Formula::eq(tz, ty));
    define_by_membership(env, &[x, y], &existence, z, &phi).expect("upair: derivation is closed")
}

/// The union `⋃x`, with `⊢ ∀x ∀z. (z ∈ union(x) ↔ ∃y. (y ∈ x ∧ z ∈ y))`.
///
/// Free given [`define_by_membership`] — only the existence axiom differs.
pub fn union(env: &mut Env) -> (FnSym, Thm) {
    let ax = Thm::ax_union(env);
    let (x, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tz, ty) = (Term::var(x), Term::var(z), Term::var(y));
    let existence = inst_all(&ax, std::slice::from_ref(&tx)).expect("union: instantiate Union");
    let phi = Formula::exists(y, Formula::and(Formula::mem(ty.clone(), tx), Formula::mem(tz, ty)));
    define_by_membership(env, &[x], &existence, z, &phi).expect("union: derivation is closed")
}

/// The power set `𝒫x`, with `⊢ ∀x ∀z. (z ∈ power(x) ↔ z ⊆ x)`.
pub fn power(env: &mut Env) -> (FnSym, Thm) {
    let ax = Thm::ax_power(env);
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let existence = inst_all(&ax, std::slice::from_ref(&tx)).expect("power: instantiate Power");
    let phi = kernel::thm::subset(env, tz, tx);
    define_by_membership(env, &[x], &existence, z, &phi).expect("power: derivation is closed")
}

/// The singleton `{a}`, as the term `upair(a, a)`.
///
/// Note this introduces **no new definitional extension**: it is a composition
/// of an existing symbol, so there is nothing to prove and nothing added to the
/// signature. Constructing rather than extending is the cheaper option wherever
/// it is available.
pub fn singleton(upair_sym: FnSym, a: Term) -> Term { Term::apply(upair_sym, vec![a.clone(), a]) }

/// The Kuratowski ordered pair `⟨a, b⟩ = {{a}, {a, b}}`.
///
/// Also a pure composition — `upair(upair(a,a), upair(a,b))` — so again no new
/// symbol and no proof obligation. The *characteristic* property of ordered
/// pairs (that `⟨a,b⟩ = ⟨c,d⟩` iff `a = c` and `b = d`) is a separate lemma and
/// is genuine work; it is what the function-graph construction will need.
pub fn opair(upair_sym: FnSym, a: Term, b: Term) -> Term {
    Term::apply(upair_sym, vec![singleton(upair_sym, a.clone()), Term::apply(upair_sym, vec![a, b])])
}

/// Consequentia mirabilis (Clavius' law): `⊢ (¬φ → φ) → φ`.
///
/// Needed because `a ∨ b` is encoded as `¬a → b`, so a disjunction of a formula
/// with itself — which is what `{c} = upair(c,c)` produces — is exactly
/// `¬c → c`, and collapsing it to `c` is this law.
pub fn clavius(phi: Formula) -> Thm {
    let np = Formula::not(phi.clone());
    let b = Formula::imp(np.clone(), phi.clone()); // ¬φ → φ
    // ⊢ ¬φ → (B → φ), by swapping reflexivity of B.
    let a_to_b_phi = com12(&imp_refl(b.clone())).expect("clavius: com12");
    // ⊢ ¬φ → (φ → ⊥) is reflexivity, since ¬φ *is* φ → ⊥.
    let a_to_phi_false = imp_refl(np.clone());
    // Compose under the antecedent ¬φ to get ¬φ → (B → ⊥), i.e. ¬φ → ¬B.
    let bridge = a1i(&syl_imp(b.clone(), phi.clone(), Formula::false_()), np.clone());
    let a_to_nb = hyp_mp(&hyp_mp(&bridge, &a_to_b_phi).expect("clavius: bridge 1"), &a_to_phi_false)
        .expect("clavius: bridge 2");
    Thm::mp(&Thm::ax_contra(phi, b), &a_to_nb).expect("clavius: contraposition")
}

/// From `⊢ H → (φ ∨ φ)` infer `⊢ H → φ`.
pub fn hyp_or_same(t: &Thm) -> Option<Thm> {
    let (_h, disj) = t.concl().as_imp()?;
    let (nphi, phi) = disj.as_imp()?; // `φ ∨ φ` is `¬φ → φ`
    let (phi2, _) = nphi.as_imp()?;
    if phi != phi2 {
        return None
    }
    syl(t, &clavius(phi))
}

/// `⊢ φ[t/v] → ∃v. φ` — existential introduction in implication form.
pub fn exists_intro_imp(v: FreeVar, phi: Formula, t: Term) -> Option<Thm> {
    let inst = phi.subst(v, &t);
    let all_not = Formula::forall(v, Formula::not(phi));
    // ⊢ (∀v.¬φ) → ¬φ[t], contraposed, gives ⊢ ¬¬φ[t] → ¬∀v.¬φ.
    let step = contrapos(&Thm::ax_inst(all_not, t)?)?;
    syl(&notnot_intro(inst), &step)
}

/// `⊢ (∃v. φ) → ψ`, given `⊢ ∀v. (φ → ψ)` with `v` not free in `ψ`.
///
/// The implication form of [`exists_elim`]. The side condition is what stops a
/// conclusion depending on the witness from escaping the witness's scope.
pub fn exists_elim_imp(v: FreeVar, all_imp: &Thm, psi: &Formula) -> Option<Thm> {
    if psi.occurs_free(v) {
        return None
    }
    let body = Thm::mp(&Thm::ax_inst(all_imp.concl().clone(), Term::var(v))?, all_imp)?;
    let (phi, psi_chk) = body.concl().as_imp()?;
    if psi_chk != *psi {
        return None
    }
    let all_contra = Thm::gen(v, &contrapos(&body)?);
    let dist = Thm::ax_dist(v, Formula::not(psi.clone()), Formula::not(phi))?;
    let ex_to_nn = contrapos(&Thm::mp(&dist, &all_contra)?)?;
    syl(&ex_to_nn, &notnot_elim(psi.clone()))
}

/// `⊢ ∀c. ⋃{c} = c`.
///
/// Needed for application: `app(f,a)` is `⋃{y : ⟨a,y⟩ ∈ f}`, and when `f` is a
/// function and `a` is in its domain that collection is the singleton of the
/// value, so the union has to strip it back off.
pub fn union_singleton(env: &mut Env, up: FnSym, up_ax: &Thm, un: FnSym, un_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (c, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tz, ty) = (Term::var(c), Term::var(z), Term::var(y));

    let s = singleton(up, tc.clone()); // {c}
    let u = Term::apply(un, vec![s.clone()]); // ⋃{c}

    // ⊢ y ∈ {c} ↔ (y = c ∨ y = c)   and   ⊢ z ∈ ⋃{c} ↔ ∃y. (y ∈ {c} ∧ z ∈ y)
    let up_inst = inst_all(up_ax, &[tc.clone(), tc.clone(), ty.clone()])?;
    let un_inst = inst_all(un_ax, &[s.clone(), tz.clone()])?;

    let mem_u = Formula::mem(tz.clone(), u.clone());
    let mem_c = Formula::mem(tz.clone(), tc.clone());
    let body = Formula::and(Formula::mem(ty.clone(), s.clone()), Formula::mem(tz.clone(), ty.clone()));

    // ── forward: z ∈ ⋃{c} → z ∈ c ────────────────────────────────────────────
    // Under H := (y ∈ {c} ∧ z ∈ y): y = c, so z ∈ y gives z ∈ c.
    let h_in_s = and_left(Formula::mem(ty.clone(), s.clone()), Formula::mem(tz.clone(), ty.clone()));
    let h_disj = syl(&h_in_s, &iff_mp(&up_inst)?)?;
    let h_y_eq_c = hyp_or_same(&h_disj)?;
    let h_z_in_y = and_right(Formula::mem(ty.clone(), s), Formula::mem(tz.clone(), ty.clone()));
    // ⊢ y = c → (z ∈ y → z ∈ c)
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(ty, tc.clone(), w, Formula::mem(tz.clone(), Term::var(w)));
    let h_leib = a1i(&leib, body.clone());
    let h_z_in_c = hyp_mp(&hyp_mp(&h_leib, &h_y_eq_c)?, &h_z_in_y)?;

    let ex_to_c = exists_elim_imp(y, &Thm::gen(y, &h_z_in_c), &mem_c)?;
    let fwd = syl(&iff_mp(&un_inst)?, &ex_to_c)?;

    // ── backward: z ∈ c → z ∈ ⋃{c} ───────────────────────────────────────────
    // Witness y := c. First ⊢ c ∈ {c}, from `c = c` on the left disjunct.
    let refl_c = Thm::eq_refl(tc.clone());
    let disj_cc = a1i(&refl_c, Formula::not(Formula::eq(tc.clone(), tc.clone())));
    let up_at_c = inst_all(up_ax, &[tc.clone(), tc.clone(), tc.clone()])?;
    let c_in_s = Thm::mp(&iff_mpr(&up_at_c)?, &disj_cc)?;

    let h_c_in_s = a1i(&c_in_s, mem_c.clone());
    let h_z_in_c2 = imp_refl(mem_c.clone());
    let h_pair = hyp_and(&h_c_in_s, &h_z_in_c2)?;
    let intro = exists_intro_imp(y, body, tc.clone())?;
    let bwd = syl(&syl(&h_pair, &intro)?, &iff_mpr(&un_inst)?)?;

    // ── combine, generalise, apply Extensionality ────────────────────────────
    let iff = and_intro(&fwd, &bwd);
    debug_assert_eq!(*iff.concl(), Formula::iff(mem_u.clone(), mem_c.clone()));
    let all_z = Thm::gen(z, &iff);
    let ext_inst = inst_all(&ext, &[u, tc])?;
    let eq = Thm::mp(&ext_inst, &all_z)?;
    Some(Thm::gen(c, &eq))
}

/// `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)`.
///
/// `{a}` is `upair(a,a)`, so its membership condition is the degenerate
/// disjunction `z = a ∨ z = a`; collapsing it is Clavius' law one way and
/// weakening the other.
pub fn mem_singleton(env: &mut Env, up: FnSym, up_ax: &Thm) -> Option<Thm> {
    let (a, z) = (env.fresh_var(), env.fresh_var());
    let (ta, tz) = (Term::var(a), Term::var(z));
    let inst = inst_all(up_ax, &[ta.clone(), ta.clone(), tz.clone()])?;
    let eq = Formula::eq(tz.clone(), ta.clone());

    let fwd = syl(&iff_mp(&inst)?, &clavius(eq.clone()))?;
    // `z = a → (z = a ∨ z = a)` is weakening, since `∨` is `¬· → ·`.
    let bwd = syl(&Thm::ax_k(eq.clone(), Formula::not(eq)), &iff_mpr(&inst)?)?;

    let iff = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *iff.concl(),
        Formula::iff(Formula::mem(tz, singleton(up, ta.clone())), Formula::eq(Term::var(z), ta))
    );
    Some(gen_all(&[a, z], &iff))
}

/// `⊢ ∀a ∀c. ({a} = {c} → a = c)` — singletons are injective.
///
/// From the equation, Leibniz moves `a ∈ {a}` to `a ∈ {c}`; membership in a
/// singleton then gives `a = c`.
pub fn singleton_inj(env: &mut Env, up: FnSym, mem_sing: &Thm) -> Option<Thm> {
    let (a, c) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(a), Term::var(c));
    let (sa, sc) = (singleton(up, ta.clone()), singleton(up, tc.clone()));

    // ⊢ a ∈ {a}, from reflexivity.
    let ms_a = inst_all(mem_sing, &[ta.clone(), ta.clone()])?;
    let a_in_sa = Thm::mp(&iff_mpr(&ms_a)?, &Thm::eq_refl(ta.clone()))?;
    // ⊢ a ∈ {c} ↔ a = c
    let ms_c = inst_all(mem_sing, &[tc.clone(), ta.clone()])?;

    // Under H := {a} = {c}: Leibniz carries membership across.
    let h = Formula::eq(sa.clone(), sc.clone());
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(sa, sc, w, Formula::mem(ta.clone(), Term::var(w)));
    let h_in_sc = hyp_mp(&leib, &a1i(&a_in_sa, h))?;
    let h_eq = syl(&h_in_sc, &iff_mp(&ms_c)?)?;

    debug_assert_eq!(
        *h_eq.concl(),
        Formula::imp(Formula::eq(singleton(up, ta.clone()), singleton(up, tc.clone())), Formula::eq(ta, tc))
    );
    Some(gen_all(&[a, c], &h_eq))
}

/// `⊢ (φ → ψ) → (¬ψ → ¬φ)` — contraposition, internalised.
pub fn contrapos_imp(phi: Formula, psi: Formula) -> Thm { syl_imp(phi, psi, Formula::false_()) }

/// Case analysis under a hypothesis: from `⊢ H → (φ ∨ ψ)`, `⊢ H → (φ → χ)` and
/// `⊢ H → (ψ → χ)`, infer `⊢ H → χ`.
///
/// `φ ∨ ψ` is `¬φ → ψ`. Contraposing the first case gives `¬χ → ¬φ`; chaining
/// the disjunction with the second case gives `¬φ → χ`; together `¬χ → χ`,
/// which Clavius collapses.
pub fn hyp_or_elim(h_disj: &Thm, h_left: &Thm, h_right: &Thm) -> Option<Thm> {
    let (h, disj) = h_disj.concl().as_imp()?;
    let (nphi, psi) = disj.as_imp()?;
    let (phi, _) = nphi.as_imp()?;
    let (_, imp_l) = h_left.concl().as_imp()?;
    let (_, chi) = imp_l.as_imp()?;

    let under = |t: &Thm| a1i(t, h.clone());
    // ⊢ H → (¬χ → ¬φ)
    let h_nc_np = hyp_mp(&under(&contrapos_imp(phi.clone(), chi.clone())), h_left)?;
    // ⊢ H → (¬φ → χ)
    let bridge = under(&syl_imp(Formula::not(phi.clone()), psi, chi.clone()));
    let h_np_chi = hyp_mp(&hyp_mp(&bridge, h_disj)?, h_right)?;
    // ⊢ H → (¬χ → χ), then Clavius.
    let bridge2 = under(&syl_imp(Formula::not(chi.clone()), Formula::not(phi), chi.clone()));
    let h_nc_chi = hyp_mp(&hyp_mp(&bridge2, &h_nc_np)?, &h_np_chi)?;
    syl(&h_nc_chi, &clavius(chi))
}

/// `⊢ a ∈ {a, b}` and `⊢ b ∈ {a, b}` as a pair of theorems, for given terms.
pub fn upair_members(up_ax: &Thm, a: &Term, b: &Term) -> Option<(Thm, Thm)> {
    let at_a = inst_all(up_ax, &[a.clone(), b.clone(), a.clone()])?;
    // `a = a ∨ a = b` is `¬(a=a) → (a=b)`. Here the *left* disjunct is the true
    // one, so the antecedent is absurd and the implication holds by ex falso —
    // unlike the right-hand case below, where plain weakening suffices.
    let absurd = mp_const(&Thm::eq_refl(a.clone()), Formula::false_());
    let disj_a = syl(&absurd, &ex_falso(Formula::eq(a.clone(), b.clone())))?;
    let left = Thm::mp(&iff_mpr(&at_a)?, &disj_a)?;

    let at_b = inst_all(up_ax, &[a.clone(), b.clone(), b.clone()])?;
    // `b = a ∨ b = b` needs the *right* disjunct: `¬(b=a) → b=b` is weakening.
    let right = Thm::mp(&iff_mpr(&at_b)?, &a1i(&Thm::eq_refl(b.clone()), Formula::not(Formula::eq(b.clone(), a.clone()))))?;
    Some((left, right))
}

/// `⊢ a = b → b = a` — symmetry of equality, in implication form.
pub fn eq_symm_imp(env: &mut Env, a: Term, b: Term) -> Thm {
    let x = env.fresh_var();
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
    mpd_const(&leib, &Thm::eq_refl(a)).expect("eq_symm_imp: reflexivity discharges the antecedent")
}

/// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → a = c)` — the first component of the
/// Kuratowski pair is determined.
///
/// `{a}` is a member of `⟨a,b⟩`, so the equation carries it into `⟨c,d⟩`, where
/// it is either `{c}` (and singletons are injective) or `{c,d}` (and then `c`
/// is a member of `{a}`, so `c = a`).
pub fn opair_fst(env: &mut Env, up: FnSym, up_ax: &Thm, mem_sing: &Thm, sing_inj: &Thm) -> Option<Thm> {
    let (a, b, c, d) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(c), Term::var(d));

    let (sa, sc) = (singleton(up, ta.clone()), singleton(up, tc.clone()));
    let cd = Term::apply(up, vec![tc.clone(), td.clone()]);
    let (pab, pcd) = (opair(up, ta.clone(), tb.clone()), opair(up, tc.clone(), td.clone()));

    let h = Formula::eq(pab.clone(), pcd.clone());
    let goal = Formula::eq(ta.clone(), tc.clone());

    // ⊢ {a} ∈ ⟨a,b⟩, carried across the equation by Leibniz.
    let (sa_in_pab, _) = upair_members(up_ax, &sa, &Term::apply(up, vec![ta.clone(), tb.clone()]))?;
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(pab, pcd.clone(), w, Formula::mem(sa.clone(), Term::var(w)));
    let h_sa_in_pcd = hyp_mp(&carry, &a1i(&sa_in_pab, h.clone()))?;

    // ⊢ H → ({a} = {c} ∨ {a} = {c,d})
    let pcd_members = inst_all(up_ax, &[sc.clone(), cd.clone(), sa.clone()])?;
    let h_disj = syl(&h_sa_in_pcd, &iff_mp(&pcd_members)?)?;

    // Case 1: {a} = {c}. Singletons are injective.
    let case1 = a1i(&inst_all(sing_inj, &[ta.clone(), tc.clone()])?, h.clone());

    // Case 2: {a} = {c,d}. Then c ∈ {a}, so c = a.
    let h2 = Formula::eq(sa.clone(), cd.clone());
    let (c_in_cd, _) = upair_members(up_ax, &tc, &td)?;
    let h2_symm = eq_symm_imp(env, sa.clone(), cd.clone());
    let w2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(cd, sa.clone(), w2, Formula::mem(tc.clone(), Term::var(w2)));
    let h2_c_in_sa = hyp_mp(&syl(&h2_symm, &carry2)?, &a1i(&c_in_cd, h2.clone()))?;
    let h2_c_eq_a = syl(&h2_c_in_sa, &iff_mp(&inst_all(mem_sing, &[ta.clone(), tc.clone()])?)?)?;
    let h2_goal = syl(&h2_c_eq_a, &eq_symm_imp(env, tc.clone(), ta.clone()))?;
    let case2 = a1i(&h2_goal, h.clone());

    let out = hyp_or_elim(&h_disj, &case1, &case2)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal));
    Some(gen_all(&[a, b, c, d], &out))
}
