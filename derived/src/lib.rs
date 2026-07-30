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
pub fn define_abbrev(env: &mut Env, xs: &[FreeVar], t: &Term) -> (FnSym, Thm) {
    let (y, phi, witness) = exists_unique_eq(env, xs, t);
    kernel::thm::define(env, xs, y, phi, &witness).expect("define_abbrev: the ∃! witness is built to match")
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
