//! The crate's fallible rule toolkit, saying **why** it stopped.
//!
//! # Interface
//!
//! Every item here is the `DResult` form of the same-named function at the
//! crate root. `crate::syl` is `rules::syl(..).ok()`; this module is where the
//! implementation and its documentation live.
//!
//! ```text
//! syl, imp_mono_r, com12, mpd_const, contrapos, curry, uncurry, conjoin
//! inst_all, inst_self, forall_mono, exists_mono, exists_elim, exists_intro
//! eq_symm, eq_trans, congr, congr_arg
//! and_elim_left/right, iff_mp, iff_mpr, hyp_mp, hyp_syl, hyp_and, hyp_iff_mp/mpr
//! conj_of, conj_proj, conj_sub, disj_of, disj_inject, hyp_or_same, hyp_or_elim
//! define_abbrev, define_by_membership, union_singleton, mem_singleton
//! singleton_inj, opair_fst, upair_members, exists_intro_imp, exists_elim_imp
//! ```
//!
//! # Why this module exists, and when it should stop existing
//!
//! These functions used to sit at the crate root returning `Option`. They now
//! return [`crate::DResult`], so a failure names the site, and — when a kernel
//! primitive was the thing that refused — the operands it refused (see
//! [`crate::prim`]).
//!
//! The crate root still carries an `Option`-returning function of each name.
//! Those are **adaptors**, three lines each, of the form
//! `rules::foo(..).ok()`. They exist for exactly one reason: `mini/` and
//! `checker/` call `derived::syl(..)?` from inside functions that return
//! `Option`, and `?` cannot cross from `Result` to `Option`. Changing the
//! canonical paths would have broken both crates at ~1 400 call sites, and this
//! seat may not edit `mini/`.
//!
//! So the split is a **migration seam, not a design**. The endgame is one
//! commit: delete the adaptors from `lib.rs`, replace them with
//! `pub use rules::*;`, and fix up the consumers — at which point `crate::syl`
//! and `rules::syl` are the same function and this note goes away. Until then,
//! **new code inside `derived/` should import from here**, and the crate-root
//! name is for the two consumers that have not moved.
//!
//! # What the failures say
//!
//! Two kinds, and the distinction is the point (see [`crate::err`]):
//!
//! * a **decline** — this toolkit refusing input it cannot use: two
//!   implications that do not compose, a projection index past the end of a
//!   conjunction, an existential elimination whose conclusion mentions the
//!   witness. Each names itself, and the reason is what the guard was checking.
//! * an **assembly failure** — a kernel primitive handed bad data, produced by
//!   [`crate::prim`] rather than here. In this module those arise where a
//!   premise is not the shape its parameter name claims: `syl` on something
//!   that is not an implication reports `Formula::as_imp` with the offending
//!   formula, not a bare refusal.
//!
//! Nothing here re-labels an error it was handed: `?` propagates the innermost
//! reason unchanged.

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::{
    a1i, and_intro, and_intro_imp, and_left, and_right, clavius, contrapos_imp, eq_symm_imp,
    ex_falso, exists_unique_eq, funcs, gen_all, imp_refl, mp_const, notnot_elim, notnot_intro,
    opair, singleton, split_iff, syl_imp,
};
use crate::decline;
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

/// Derived existential introduction: from `⊢ φ[t/v]` infer `⊢ ∃v. φ`.
///
/// `∃v. φ` is `¬∀v. ¬φ`. Instantiating `∀v. ¬φ` at `t` yields `¬φ[t/v]`,
/// which contradicts the premise.
pub fn exists_intro(v: FreeVar, phi: Formula, t: Term, witness: &Thm) -> DResult<Thm> {
    // The premise must actually be the instance claimed.
    if *witness.concl() != phi.subst(v, &t) {
        return Err(decline!("the witness does not prove the instance the caller claimed"))
    }
    let all_not = Formula::forall(v, Formula::not(phi));
    // ⊢ (∀v. ¬φ) → ¬φ[t/v]
    let inst = prim::ax_inst(all_not.clone(), t)?;
    // S : (A → (φ[t] → ⊥)) → ((A → φ[t]) → (A → ⊥))
    let s = Thm::ax_s(all_not.clone(), witness.concl().clone(), Formula::false_());
    let step = prim::mp(&s, &inst)?;
    let a_to_w = a1i(witness, all_not);
    prim::mp(&step, &a_to_w)
}

/// Derived: from `⊢ a = b` infer `⊢ b = a`.
///
/// Take `φ(x) := (x = a)`. Leibniz gives `a = b → (a = a → b = a)`; discharge
/// the antecedent with reflexivity.
pub fn eq_symm(env: &mut Env, ab: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    let x = env.fresh_var();
    let phi = Formula::eq(Term::var(x), a.clone());
    let leib = Thm::eq_leibniz(a.clone(), b, x, phi);
    let step = prim::mp(&leib, ab)?;
    prim::mp(&step, &Thm::eq_refl(a))
}

/// Derived: from `⊢ a = b` and `⊢ b = c` infer `⊢ a = c`.
///
/// Take `φ(x) := (a = x)`. Leibniz on `b = c` gives
/// `b = c → (a = b → a = c)`.
pub fn eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> DResult<Thm> {
    let (a, b1) = ab.concl().eq_parts()?;
    let (b2, c) = bc.concl().eq_parts()?;
    if b1 != b2 {
        return Err(decline!("the two equations do not meet: the first's right side is not the second's left"))
    }
    let x = env.fresh_var();
    let phi = Formula::eq(a.clone(), Term::var(x));
    let leib = Thm::eq_leibniz(b1, c, x, phi);
    let step = prim::mp(&leib, bc)?;
    prim::mp(&step, ab)
}

/// Derived congruence: from `⊢ a = b` infer
/// `⊢ f(t₀..a..tₙ) = f(t₀..b..tₙ)`, replacing argument `idx`.
///
/// Take `φ(x) := f(..a..) = f(..x..)`. Leibniz on `a = b` turns
/// `f(..a..) = f(..a..)` (reflexivity) into `f(..a..) = f(..b..)`.
pub fn congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    if idx >= args.len() || args.get(idx) != Some(&a) {
        return Err(decline!("the rewritten position is out of range, or does not hold the equation's left side"))
    }
    let lhs = Term::apply(f, args.to_vec());

    let x = env.fresh_var();
    let mut hole = args.to_vec();
    hole[idx] = Term::var(x);
    let phi = Formula::eq(lhs.clone(), Term::apply(f, hole));

    let leib = Thm::eq_leibniz(a, b, x, phi);
    let step = prim::mp(&leib, ab)?;
    prim::mp(&step, &Thm::eq_refl(lhs))
}

/// Derived: congruence in every argument at once. Given `⊢ aᵢ = bᵢ` for each
/// position, infer `⊢ f(a₀..aₙ) = f(b₀..bₙ)` by rewriting one position at a
/// time and chaining with transitivity.
pub fn congr(env: &mut Env, f: FnSym, eqs: &[Thm]) -> DResult<Thm> {
    let mut args: Vec<Term> = Vec::with_capacity(eqs.len());
    for e in eqs {
        args.push(e.concl().eq_parts()?.0);
    }
    if args.len() != f.arity() as usize {
        return Err(decline!("the number of equations is not the symbol's arity"))
    }
    let mut acc = Thm::eq_refl(Term::apply(f, args.clone()));
    for (i, e) in eqs.iter().enumerate() {
        let step = congr_arg(env, f, &args, i, e)?;
        // Advance the running argument list to the rewritten form.
        args[i] = e.concl().eq_parts()?.1;
        acc = eq_trans(env, &acc, &step)?;
    }
    Ok(acc)
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
/// `kernel::thm::define` enforces this, and this function *declines* when it
/// refuses rather than panicking, so callers that build terms dynamically can
/// fall back gracefully.
pub fn define_abbrev(env: &mut Env, xs: &[FreeVar], t: &Term) -> DResult<(FnSym, Thm)> {
    let (y, phi, witness) = exists_unique_eq(env, xs, t);
    prim::define(env, xs, y, phi, &witness)
}

/// From `⊢ ∀x⃗. φ` and a list of terms, instantiate all the leading
/// quantifiers in order.
pub fn inst_all(thm: &Thm, ts: &[Term]) -> DResult<Thm> {
    let mut cur = thm.clone();
    for t in ts {
        let step = prim::ax_inst(cur.concl().clone(), t.clone())?;
        cur = prim::mp(&step, &cur)?;
    }
    Ok(cur)
}

/// Syllogism: from `⊢ φ → ψ` and `⊢ ψ → χ` infer `⊢ φ → χ`.
pub fn syl(ab: &Thm, bc: &Thm) -> DResult<Thm> {
    let (a, b1) = ab.concl().imp_parts()?;
    let (b2, c) = bc.concl().imp_parts()?;
    if b1 != b2 {
        return Err(decline!("the two implications do not compose: the first's consequent is not the second's antecedent"))
    }
    // S : (a → (b → c)) → ((a → b) → (a → c)), with `a → (b → c)` from weakening.
    let s = Thm::ax_s(a.clone(), b1, c);
    let weak = a1i(bc, a);
    let step = prim::mp(&s, &weak)?;
    prim::mp(&step, ab)
}

/// Monotonicity in the consequent: from `⊢ γ → δ` infer `⊢ (φ → γ) → (φ → δ)`.
pub fn imp_mono_r(gd: &Thm, phi: Formula) -> DResult<Thm> {
    let (g, d) = gd.concl().imp_parts()?;
    let s = Thm::ax_s(phi.clone(), g, d);
    let weak = a1i(gd, phi);
    prim::mp(&s, &weak)
}

/// Swap antecedents: from `⊢ α → (β → γ)` infer `⊢ β → (α → γ)`.
pub fn com12(t: &Thm) -> DResult<Thm> {
    let (a, rest) = t.concl().imp_parts()?;
    let (b, c) = rest.imp_parts()?;
    let s = Thm::ax_s(a.clone(), b.clone(), c);
    let step = prim::mp(&s, t)?; // (α → β) → (α → γ)
    let k = Thm::ax_k(b, a); // β → (α → β)
    syl(&k, &step)
}

/// From `⊢ φ ∧ ψ` infer `⊢ φ`.
pub fn and_elim_left(t: &Thm) -> DResult<Thm> {
    let (imp, _) = t.concl().imp_parts()?; // φ ∧ ψ is ¬(φ → ¬ψ)
    let (phi, notpsi) = imp.imp_parts()?;
    let (psi, _) = notpsi.imp_parts()?;
    prim::mp(&and_left(phi, psi), t)
}

/// From `⊢ φ ∧ ψ` infer `⊢ ψ`.
pub fn and_elim_right(t: &Thm) -> DResult<Thm> {
    let (imp, _) = t.concl().imp_parts()?;
    let (phi, notpsi) = imp.imp_parts()?;
    let (psi, _) = notpsi.imp_parts()?;
    prim::mp(&and_right(phi, psi), t)
}

/// Forward direction of a biconditional: from `⊢ φ ↔ ψ` infer `⊢ φ → ψ`.
pub fn iff_mp(t: &Thm) -> DResult<Thm> { and_elim_left(t) }

/// Reverse direction of a biconditional: from `⊢ φ ↔ ψ` infer `⊢ ψ → φ`.
pub fn iff_mpr(t: &Thm) -> DResult<Thm> { and_elim_right(t) }

/// From `⊢ α → (β → γ)` and `⊢ β` infer `⊢ α → γ`.
pub fn mpd_const(abc: &Thm, b: &Thm) -> DResult<Thm> {
    let (a, rest) = abc.concl().imp_parts()?;
    let (b_f, c) = rest.imp_parts()?;
    if b_f != *b.concl() {
        return Err(decline!("the minor premise is not the implication's inner antecedent"))
    }
    let s = Thm::ax_s(a.clone(), b_f, c);
    let step = prim::mp(&s, abc)?;
    prim::mp(&step, &a1i(b, a))
}

/// Contraposition as a rule: from `⊢ φ → ψ` infer `⊢ ¬ψ → ¬φ`.
pub fn contrapos(ab: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().imp_parts()?;
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
pub fn inst_self(x: FreeVar, all: &Thm) -> DResult<Thm> {
    let step = prim::ax_inst(all.concl().clone(), Term::var(x))?;
    prim::mp(&step, all)
}

/// From `⊢ ∀x.(φ → ψ)` infer `⊢ ∀x. φ → ∀x. ψ`.
///
/// Both uses of the distribution axiom below are legitimate because their
/// antecedents are themselves `∀x`-quantified, so `x` is bound rather than free
/// in them. The side condition is *arranged*, not wished away.
pub fn forall_mono(x: FreeVar, all_imp: &Thm) -> DResult<Thm> {
    let a = all_imp.concl().clone();
    // ⊢ A → (φ → ψ); instantiating a `∀x` at `x` itself just reopens the body.
    let a_to_body = prim::ax_inst(a.clone(), Term::var(x))?;
    let (_, body) = a_to_body.concl().imp_parts()?;
    let (phi, psi) = body.imp_parts()?;

    let b = Formula::forall(x, phi.clone());
    let b_to_phi = prim::ax_inst(b.clone(), Term::var(x))?;

    // A → (φ → ψ)  ⟹  φ → (A → ψ)  ⟹  B → (A → ψ)  ⟹  A → (B → ψ)
    let phi_to_apsi = com12(&a_to_body)?;
    let b_to_apsi = syl(&b_to_phi, &phi_to_apsi)?;
    let a_to_bpsi = com12(&b_to_apsi)?;

    let gen_bpsi = Thm::gen(x, &a_to_bpsi);
    let dist1 = prim::ax_dist(x, a, Formula::imp(b.clone(), psi.clone()))?;
    let a_to_all = prim::mp(&dist1, &gen_bpsi)?;
    let dist2 = prim::ax_dist(x, b, psi)?;
    // `syl` yields the implication form `⊢ ∀x.(φ→ψ) → (∀x.φ → ∀x.ψ)`; discharge
    // its antecedent so the result matches the rule form this function promises.
    let implication = syl(&a_to_all, &dist2)?;
    prim::mp(&implication, all_imp)
}

/// From `⊢ ∀x.(φ → ψ)` infer `⊢ ∃x. φ → ∃x. ψ`.
///
/// `∃` is `¬∀¬`, so this runs by contraposing the implication under the
/// quantifier, applying [`forall_mono`], and contraposing back.
pub fn exists_mono(x: FreeVar, all_imp: &Thm) -> DResult<Thm> {
    let a_to_body = prim::ax_inst(all_imp.concl().clone(), Term::var(x))?;
    let (_, body) = a_to_body.concl().imp_parts()?;
    let (phi, psi) = body.imp_parts()?;

    // ⊢ ∀x.(¬ψ → ¬φ)
    let contra_body = contrapos(&prim::mp(&a_to_body, all_imp)?)?;
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
    Ok(out)
}

/// Existential elimination: from `⊢ ∃x. φ` and `⊢ ∀x.(φ → ψ)` with `x` not free
/// in `ψ`, infer `⊢ ψ`.
///
/// The classic awkward rule. Route: contrapose the body, distribute `¬ψ` in
/// (legal because `x` is not free in it — checked), contrapose back to get
/// `∃x.φ → ¬¬ψ`, discharge, and strip the double negation.
pub fn exists_elim(x: FreeVar, ex: &Thm, all_imp: &Thm, psi: &Formula) -> DResult<Thm> {
    if psi.occurs_free(x) {
        // Without this the rule is unsound: it would let a witness-dependent
        // conclusion escape the scope of its witness.
        return Err(decline!("the conclusion mentions the witness variable, which the rule may not let escape"))
    }
    let a_to_body = prim::ax_inst(all_imp.concl().clone(), Term::var(x))?;
    let body = prim::mp(&a_to_body, all_imp)?;
    let (phi, psi_chk) = body.concl().imp_parts()?;
    if psi_chk != *psi {
        return Err(decline!("the instantiated body does not conclude the psi the caller stated"))
    }

    // ⊢ ∀x.(¬ψ → ¬φ)
    let all_contra = Thm::gen(x, &contrapos(&body)?);
    // ⊢ ¬ψ → ∀x.¬φ, legal since x is not free in ¬ψ.
    let dist = prim::ax_dist(x, Formula::not(psi.clone()), Formula::not(phi.clone()))?;
    let notpsi_to_all = prim::mp(&dist, &all_contra)?;
    // ⊢ ¬∀x.¬φ → ¬¬ψ, i.e. ⊢ ∃x.φ → ¬¬ψ
    let ex_to_nn = contrapos(&notpsi_to_all)?;
    let nn = prim::mp(&ex_to_nn, ex)?;
    prim::mp(&notnot_elim(psi.clone()), &nn)
}

/// Modus ponens under a fixed hypothesis: from `⊢ H → (φ → ψ)` and `⊢ H → φ`
/// infer `⊢ H → ψ`.
pub fn hyp_mp(h_imp: &Thm, h_arg: &Thm) -> DResult<Thm> {
    let (h1, rest) = h_imp.concl().imp_parts()?;
    let (phi, psi) = rest.imp_parts()?;
    let (h2, phi2) = h_arg.concl().imp_parts()?;
    if h1 != h2 || phi != phi2 {
        return Err(decline!("the two theorems are under different hypotheses, or the argument is not the antecedent"))
    }
    let s = Thm::ax_s(h1, phi, psi);
    let step = prim::mp(&s, h_imp)?;
    prim::mp(&step, h_arg)
}

/// Syllogism under a fixed hypothesis: from `⊢ H → (a → b)` and
/// `⊢ H → (b → c)` infer `⊢ H → (a → c)`.
///
/// The `⊢ H → φ` idiom's replacement for [`syl`], as [`hyp_mp`] is its
/// replacement for modus ponens. It is the most-called rule in the crate after
/// those two, and it had been written **twice** — `crate::separation::hyp_syl`
/// with the guard below and `crate::funcs::logic::hyp_syl` without it, the
/// latter leaving the same rejection to [`hyp_mp`] one frame further on. Both
/// spellings survive as `Option`-shaped adaptors over this one, so the ~200
/// call sites did not have to move; this is the version that says why.
pub fn hyp_syl(hab: &Thm, hbc: &Thm) -> DResult<Thm> {
    let (h, ab) = hab.concl().imp_parts()?;
    let (a, b) = ab.imp_parts()?;
    let (h2, bc) = hbc.concl().imp_parts()?;
    let (b2, c) = bc.imp_parts()?;
    if h != h2 || b != b2 {
        return Err(decline!("the two theorems are under different hypotheses, or the two implications do not compose"))
    }
    let s = a1i(&syl_imp(a, b, c), h);
    hyp_mp(&hyp_mp(&s, hab)?, hbc)
}

/// From `⊢ H → φ` and `⊢ H → ψ` infer `⊢ H → (φ ∧ ψ)`.
pub fn hyp_and(hp: &Thm, hq: &Thm) -> DResult<Thm> {
    let (h1, phi) = hp.concl().imp_parts()?;
    let (h2, psi) = hq.concl().imp_parts()?;
    if h1 != h2 {
        return Err(decline!("the two theorems are under different hypotheses"))
    }
    let intro = and_intro_imp(phi, psi);
    hyp_mp(&hyp_mp(&a1i(&intro, h1), hp)?, hq)
}

/// The **right-nested conjunction** `φ₀ ∧ (φ₁ ∧ (… ∧ φ_{n-1}))`. Declines on the
/// empty list, which has no conjunction.
///
/// Right-nesting is the shape [`and_left`]/[`and_right`] take apart and the one
/// [`crate::sigma::Telescope`] and [`crate::inductive`] state their hypotheses
/// in, so every projection below is a walk down the right spine.
pub fn conj_of(atoms: &[Formula]) -> DResult<Formula> {
    atoms.iter().rev().cloned().reduce(|acc, h| Formula::and(h, acc))
        .ok_or_else(|| decline!("the empty list has no conjunction"))
}

/// `⊢ conj_of(atoms) → atoms[i]` — project one conjunct out of a right-nested
/// conjunction. Declines if `i` is out of range.
pub fn conj_proj(atoms: &[Formula], i: usize) -> DResult<Thm> {
    let n = atoms.len();
    if i >= n {
        return Err(decline!("the projection index is past the end of the conjunction"))
    }
    let mut th = imp_refl(conj_of(atoms)?);
    for (j, hj) in atoms.iter().enumerate().take(i) {
        th = syl(&th, &and_right(hj.clone(), conj_of(&atoms[j + 1..])?))?;
    }
    if i + 1 < n {
        th = syl(&th, &and_left(atoms[i].clone(), conj_of(&atoms[i + 1..])?))?;
    }
    Ok(th)
}

/// `⊢ conj_of(atoms) → conj_of(atoms[start..end])` — project a contiguous run.
///
/// Declines when the run is empty, which is the caller's signal that the
/// sub-conjunction does not exist and the theorem it would have fed is
/// unconditional.
pub fn conj_sub(atoms: &[Formula], start: usize, end: usize) -> DResult<Thm> {
    if start >= end || end > atoms.len() {
        return Err(decline!("the sub-conjunction range is empty or runs past the end"))
    }
    let mut parts: Vec<Thm> = (start..end).map(|i| conj_proj(atoms, i)).collect::<DResult<_>>()?;
    let mut acc = parts.pop().ok_or_else(|| decline!("the sub-conjunction is empty"))?;
    while let Some(p) = parts.pop() {
        acc = hyp_and(&p, &acc)?;
    }
    Ok(acc)
}

/// From `⊢ H → (φ ↔ ψ)` infer `⊢ H → (φ → ψ)`.
pub fn hyp_iff_mp(t: &Thm) -> DResult<Thm> {
    let (_h, iff) = t.concl().imp_parts()?;
    let (fwd, bwd) = split_iff(&iff).ok_or_else(|| decline!("the consequent is not a biconditional"))?;
    syl(t, &and_left(fwd, bwd))
}

/// From `⊢ H → (φ ↔ ψ)` infer `⊢ H → (ψ → φ)`.
pub fn hyp_iff_mpr(t: &Thm) -> DResult<Thm> {
    let (_h, iff) = t.concl().imp_parts()?;
    let (fwd, bwd) = split_iff(&iff).ok_or_else(|| decline!("the consequent is not a biconditional"))?;
    syl(t, &and_right(fwd, bwd))
}

/// From `⊢ A → (B → X)` infer `⊢ (A ∧ B) → X`.
///
/// The dual of [`uncurry`], and the way out of the one shape the
/// hypothesis-form combinators cannot produce directly: they all conclude
/// `⊢ H → φ`, so a goal `⊢ H → (X → φ)` is reached by working under
/// `H ∧ X` and currying at the end.
pub fn curry(imp2: &Thm) -> DResult<Thm> {
    let (a, rest) = imp2.concl().imp_parts()?;
    let (b, x) = rest.imp_parts()?;
    let conj = Formula::and(a.clone(), b.clone());
    // `(A ∧ B) → A` and `(A ∧ B) → B`, then apply.
    let ha = and_left(a.clone(), b.clone());
    let hb = and_right(a, b);
    let out = hyp_mp(&syl(&ha, imp2)?, &hb)?;
    debug_assert_eq!(*out.concl(), Formula::imp(conj, x), "curry: wrong shape");
    Ok(out)
}

/// The **right-nested disjunction** `φ₀ ∨ (φ₁ ∨ (… ∨ φ_{n-1}))`. Declines on the
/// empty list, which has no disjunction. The dual of [`conj_of`].
pub fn disj_of(atoms: &[Formula]) -> DResult<Formula> {
    atoms.iter().rev().cloned().reduce(|acc, h| Formula::or(h, acc))
        .ok_or_else(|| decline!("the empty list has no disjunction"))
}

/// `⊢ atoms[i] → disj_of(atoms)` — inject into one position of a right-nested
/// disjunction. Declines if `i` is out of range.
///
/// The mirror image of [`crate::isum::inj_of`]: `i` uses of
/// [`crate::funcs::or_intro_right`] and, unless `i` is last, one
/// [`crate::funcs::or_intro_left`].
pub fn disj_inject(atoms: &[Formula], i: usize) -> DResult<Thm> {
    let n = atoms.len();
    if i >= n {
        return Err(decline!("the injection index is past the end of the disjunction"))
    }
    let mut th = if i + 1 == n {
        imp_refl(atoms[i].clone())
    } else {
        funcs::or_intro_left(atoms[i].clone(), disj_of(&atoms[i + 1..])?)
    };
    for j in (0..i).rev() {
        th = syl(&th, &funcs::or_intro_right(atoms[j].clone(), disj_of(&atoms[j + 1..])?))?;
    }
    Ok(th)
}

/// From `⊢ A → (B → X)` infer `⊢ (A ∧ B) → X` — the true converse of
/// [`uncurry`].
///
/// [`uncurry`] and [`crate::cumul::curry`] are, despite their names, the same
/// rule in the same direction, so neither is an inverse of the other. Under the
/// hypothesis `A ∧ B`: [`and_left`] feeds `A` to the premise to get `B → X`, and
/// [`and_right`] supplies `B`. No `assume`, and hence nothing a consumer
/// confining `Thm::implies_intr` to one module would have to do itself.
pub fn conjoin(t: &Thm) -> DResult<Thm> {
    let (a, rest) = t.concl().imp_parts()?;
    let (b, _x) = rest.imp_parts()?;
    let left = syl(&and_left(a.clone(), b.clone()), t)?;
    hyp_mp(&left, &and_right(a, b))
}

/// From `⊢ (A ∧ B) → X` infer `⊢ A → (B → X)`.
pub fn uncurry(and_imp: &Thm) -> DResult<Thm> {
    let (conj, x) = and_imp.concl().imp_parts()?;
    let (inner, _) = conj.imp_parts()?;
    let (a, nb) = inner.imp_parts()?;
    let (b, _) = nb.imp_parts()?;
    let intro = and_intro_imp(a, b.clone()); // A → (B → (A∧B))
    let mono = imp_mono_r(and_imp, b)?; // (B → (A∧B)) → (B → X)
    let _ = x;
    syl(&intro, &mono)
}

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
) -> DResult<(FnSym, Thm)> {
    let ext = Thm::ax_extensionality(env);
    let (p, q) = (env.fresh_var(), env.fresh_var());
    let (tp, tq, tz) = (Term::var(p), Term::var(q), Term::var(z));

    // P(s) := ∀z. (z ∈ s ↔ φ(z))
    let prop = |s: &Term| Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), s.clone()), phi.clone()));
    let (pp, pq) = (prop(&tp), prop(&tq));

    // Check the caller really handed us `∃s. P(s)` for this very φ.
    if *existence.concl() != Formula::exists(p, pp.clone()) {
        return Err(decline!("the existence premise is not the one this membership condition needs"))
    }

    // Work under H := P(p) ∧ P(q).
    let h = Formula::and(pp.clone(), pq.clone());
    let mem_p = Formula::mem(tz.clone(), tp.clone());
    let mem_q = Formula::mem(tz.clone(), tq.clone());

    let h_iff_p = syl(&and_left(pp.clone(), pq.clone()), &prim::ax_inst(pp.clone(), tz.clone())?)?;
    let h_iff_q = syl(&and_right(pp.clone(), pq.clone()), &prim::ax_inst(pq.clone(), tz.clone())?)?;

    // Compose the four halves of the two biconditionals into `z ∈ q ↔ z ∈ p`.
    let bridge = |a: Formula, b: Formula, c: Formula, ab: &Thm, bc: &Thm| -> DResult<Thm> {
        let s = a1i(&syl_imp(a, b, c), h.clone());
        hyp_mp(&hyp_mp(&s, ab)?, bc)
    };
    let h_qp = bridge(mem_q.clone(), phi.clone(), mem_p.clone(), &hyp_iff_mp(&h_iff_q)?, &hyp_iff_mpr(&h_iff_p)?)?;
    let h_pq = bridge(mem_p.clone(), phi.clone(), mem_q.clone(), &hyp_iff_mp(&h_iff_p)?, &hyp_iff_mpr(&h_iff_q)?)?;
    let h_iff = hyp_and(&h_qp, &h_pq)?;

    // Generalise z and pull the quantifier in; z is not free in H.
    let dist = prim::ax_dist(z, h.clone(), Formula::iff(mem_q.clone(), mem_p.clone()))?;
    let h_same = prim::mp(&dist, &Thm::gen(z, &h_iff))?;

    // Extensionality closes it.
    let ext_inst = inst_all(&ext, &[tq.clone(), tp.clone()])?;
    let h_eq = syl(&h_same, &ext_inst)?;

    // ⊢ P(p) → (P(q) → q = p), quantify q back in, bundle with existence.
    let gen_q = Thm::gen(q, &uncurry(&h_eq)?);
    let dist_q = prim::ax_dist(q, pp.clone(), Formula::imp(pq, Formula::eq(tq, tp)))?;
    let p_to_uniq = prim::mp(&dist_q, &gen_q)?;
    let step = hyp_and(&imp_refl(pp.clone()), &p_to_uniq)?;
    let ex_uniq = prim::mp(&exists_mono(p, &Thm::gen(p, &step))?, existence)?;

    let all = gen_all(params, &ex_uniq);
    prim::define(env, params, p, prop(&Term::var(p)), &all)
}

/// From `⊢ H → (φ ∨ φ)` infer `⊢ H → φ`.
pub fn hyp_or_same(t: &Thm) -> DResult<Thm> {
    let (_h, disj) = t.concl().imp_parts()?;
    let (nphi, phi) = disj.imp_parts()?; // `φ ∨ φ` is `¬φ → φ`
    let (phi2, _) = nphi.imp_parts()?;
    if phi != phi2 {
        return Err(decline!("the two sides of the disjunction are not the same formula"))
    }
    syl(t, &clavius(phi))
}

/// `⊢ φ[t/v] → ∃v. φ` — existential introduction in implication form.
pub fn exists_intro_imp(v: FreeVar, phi: Formula, t: Term) -> DResult<Thm> {
    let inst = phi.subst(v, &t);
    let all_not = Formula::forall(v, Formula::not(phi));
    // ⊢ (∀v.¬φ) → ¬φ[t], contraposed, gives ⊢ ¬¬φ[t] → ¬∀v.¬φ.
    let step = contrapos(&prim::ax_inst(all_not, t)?)?;
    syl(&notnot_intro(inst), &step)
}

/// `⊢ (∃v. φ) → ψ`, given `⊢ ∀v. (φ → ψ)` with `v` not free in `ψ`.
///
/// The implication form of [`exists_elim`]. The side condition is what stops a
/// conclusion depending on the witness from escaping the witness's scope.
pub fn exists_elim_imp(v: FreeVar, all_imp: &Thm, psi: &Formula) -> DResult<Thm> {
    if psi.occurs_free(v) {
        return Err(decline!("the conclusion mentions the witness variable, which the rule may not let escape"))
    }
    let body = prim::mp(&prim::ax_inst(all_imp.concl().clone(), Term::var(v))?, all_imp)?;
    let (phi, psi_chk) = body.concl().imp_parts()?;
    if psi_chk != *psi {
        return Err(decline!("the instantiated body does not conclude the psi the caller stated"))
    }
    let all_contra = Thm::gen(v, &contrapos(&body)?);
    let dist = prim::ax_dist(v, Formula::not(psi.clone()), Formula::not(phi))?;
    let ex_to_nn = contrapos(&prim::mp(&dist, &all_contra)?)?;
    syl(&ex_to_nn, &notnot_elim(psi.clone()))
}

/// `⊢ ∀c. ⋃{c} = c`.
///
/// Needed for application: `app(f,a)` is `⋃{y : ⟨a,y⟩ ∈ f}`, and when `f` is a
/// function and `a` is in its domain that collection is the singleton of the
/// value, so the union has to strip it back off.
pub fn union_singleton(env: &mut Env, up: FnSym, up_ax: &Thm, un: FnSym, un_ax: &Thm) -> DResult<Thm> {
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
    let c_in_s = prim::mp(&iff_mpr(&up_at_c)?, &disj_cc)?;

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
    let eq = prim::mp(&ext_inst, &all_z)?;
    Ok(Thm::gen(c, &eq))
}

/// `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)`.
///
/// `{a}` is `upair(a,a)`, so its membership condition is the degenerate
/// disjunction `z = a ∨ z = a`; collapsing it is Clavius' law one way and
/// weakening the other.
pub fn mem_singleton(env: &mut Env, up: FnSym, up_ax: &Thm) -> DResult<Thm> {
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
    Ok(gen_all(&[a, z], &iff))
}

/// `⊢ ∀a ∀c. ({a} = {c} → a = c)` — singletons are injective.
///
/// From the equation, Leibniz moves `a ∈ {a}` to `a ∈ {c}`; membership in a
/// singleton then gives `a = c`.
pub fn singleton_inj(env: &mut Env, up: FnSym, mem_sing: &Thm) -> DResult<Thm> {
    let (a, c) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(a), Term::var(c));
    let (sa, sc) = (singleton(up, ta.clone()), singleton(up, tc.clone()));

    // ⊢ a ∈ {a}, from reflexivity.
    let ms_a = inst_all(mem_sing, &[ta.clone(), ta.clone()])?;
    let a_in_sa = prim::mp(&iff_mpr(&ms_a)?, &Thm::eq_refl(ta.clone()))?;
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
    Ok(gen_all(&[a, c], &h_eq))
}

/// Case analysis under a hypothesis: from `⊢ H → (φ ∨ ψ)`, `⊢ H → (φ → χ)` and
/// `⊢ H → (ψ → χ)`, infer `⊢ H → χ`.
///
/// `φ ∨ ψ` is `¬φ → ψ`. Contraposing the first case gives `¬χ → ¬φ`; chaining
/// the disjunction with the second case gives `¬φ → χ`; together `¬χ → χ`,
/// which Clavius collapses.
pub fn hyp_or_elim(h_disj: &Thm, h_left: &Thm, h_right: &Thm) -> DResult<Thm> {
    let (h, disj) = h_disj.concl().imp_parts()?;
    let (nphi, psi) = disj.imp_parts()?;
    let (phi, _) = nphi.imp_parts()?;
    let (_, imp_l) = h_left.concl().imp_parts()?;
    let (_, chi) = imp_l.imp_parts()?;

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
pub fn upair_members(up_ax: &Thm, a: &Term, b: &Term) -> DResult<(Thm, Thm)> {
    let at_a = inst_all(up_ax, &[a.clone(), b.clone(), a.clone()])?;
    // `a = a ∨ a = b` is `¬(a=a) → (a=b)`. Here the *left* disjunct is the true
    // one, so the antecedent is absurd and the implication holds by ex falso —
    // unlike the right-hand case below, where plain weakening suffices.
    let absurd = mp_const(&Thm::eq_refl(a.clone()), Formula::false_());
    let disj_a = syl(&absurd, &ex_falso(Formula::eq(a.clone(), b.clone())))?;
    let left = prim::mp(&iff_mpr(&at_a)?, &disj_a)?;

    let at_b = inst_all(up_ax, &[a.clone(), b.clone(), b.clone()])?;
    // `b = a ∨ b = b` needs the *right* disjunct: `¬(b=a) → b=b` is weakening.
    let right = prim::mp(&iff_mpr(&at_b)?, &a1i(&Thm::eq_refl(b.clone()), Formula::not(Formula::eq(b.clone(), a.clone()))))?;
    Ok((left, right))
}

/// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → a = c)` — the first component of the
/// Kuratowski pair is determined.
///
/// `{a}` is a member of `⟨a,b⟩`, so the equation carries it into `⟨c,d⟩`, where
/// it is either `{c}` (and singletons are injective) or `{c,d}` (and then `c`
/// is a member of `{a}`, so `c = a`).
pub fn opair_fst(env: &mut Env, up: FnSym, up_ax: &Thm, mem_sing: &Thm, sing_inj: &Thm) -> DResult<Thm> {
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
    Ok(gen_all(&[a, b, c, d], &out))
}