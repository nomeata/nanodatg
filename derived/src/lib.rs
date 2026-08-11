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
pub mod csb;
pub mod ctx;
pub mod cumul;
pub mod discharge;
pub mod empty;
pub mod enums;
pub mod err;
pub mod ext;
pub mod fibre;
pub mod finset;
pub mod funcs;
pub mod funspace;
pub mod hyp;
pub mod inductive;
pub mod infinity;
pub mod isum;
pub mod nat;
pub mod pairs;
pub mod point_fun;
pub mod prelude;
pub mod prim;
pub mod rules;
pub mod proj;
pub mod prop;
pub mod quot;
pub mod ran;
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
pub mod wrec;
pub mod wrec_extend;
pub mod wrec_total;
pub mod wrec_typing;
pub mod wrec_unit;
pub mod wpath;
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

/// The failure type every fallible entry in this crate reports, and the
/// `Result` it travels in. See [`err`] for the `Declined`/`Assembly` split.
pub use err::{DResult, DerErr, Site};

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

/// `Option`-shaped adaptor over [`rules::exists_intro`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn exists_intro(v: FreeVar, phi: Formula, t: Term, witness: &Thm) -> Option<Thm> {
    rules::exists_intro(v, phi, t, witness).ok()
}

/// `Option`-shaped adaptor over [`rules::eq_symm`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn eq_symm(env: &mut Env, ab: &Thm) -> Option<Thm> {
    rules::eq_symm(env, ab).ok()
}

/// `Option`-shaped adaptor over [`rules::eq_trans`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
    rules::eq_trans(env, ab, bc).ok()
}

/// `Option`-shaped adaptor over [`rules::congr_arg`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm) -> Option<Thm> {
    rules::congr_arg(env, f, args, idx, ab).ok()
}

/// `Option`-shaped adaptor over [`rules::congr`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn congr(env: &mut Env, f: FnSym, eqs: &[Thm]) -> Option<Thm> {
    rules::congr(env, f, eqs).ok()
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

/// `Option`-shaped adaptor over [`rules::define_abbrev`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn define_abbrev(env: &mut Env, xs: &[FreeVar], t: &Term) -> Option<(FnSym, Thm)> {
    rules::define_abbrev(env, xs, t).ok()
}

/// `Option`-shaped adaptor over [`rules::inst_all`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn inst_all(thm: &Thm, ts: &[Term]) -> Option<Thm> {
    rules::inst_all(thm, ts).ok()
}

/// **Simultaneous term substitution**, `t[s⃗/x⃗]` — no symbol, no `Env`, no
/// definitional extension.
///
/// # Why this exists
///
/// `kernel::Term` exposes no `subst`, and the other way to obtain "a term with
/// a hole, filled in" is to **name the hole**: [`define_abbrev`] over `x⃗`, then
/// [`inst_all`] at `s⃗`, then read the equation's right-hand side. That works,
/// but it charges four things for a term:
///
/// * a **conservative-extension obligation** and a permanent signature entry,
///   for a symbol nobody wants to see;
/// * a **precondition** — `define_abbrev` refuses a body with a free variable
///   outside `x⃗` — which makes the abstraction prefix load-bearing;
/// * that prefix chosen **at build time with no retrofit**. A prefix that is
///   wrong but still *covers* the body's free variables is accepted silently:
///   the free-variable guard is the only check there is, and it cannot fire.
/// * `Option`, because of the precondition.
///
/// This has no precondition, mints nothing, and is **total**.
///
/// There is a **third** spelling and it is not this one: `Formula::subst` is
/// public, so `Formula::eq(t,t).subst(x,s).as_eq().0` substitutes one variable
/// in three calls. Folding that over a list is *sequential*, which is the one
/// thing it may not be — see below — and it is why this goes the long way
/// round.
///
/// # What this did *not* turn out to replace
///
/// A census of every `define_abbrev` call site (16 in `mini/src`, 25 in
/// `derived/src`; DECISIONS.md 2026-08-06) found **none** that this can retire.
/// Every one of them mints a symbol that is *wanted*: it is stored as durable
/// vocabulary, or the interpretation term is built on it, or — the case that
/// generalises — its defining equation is **spent as a rewrite** rather than
/// read off, which is how a fact derived about one side's term is carried onto
/// the other side's name, and how a binder can be closed while the facts under
/// it go on mentioning it through an opaque head. A substituted term has no
/// equation to rewrite along.
///
/// Nor does this remove the wrong-prefix hazard. All four of its recorded
/// instances were at wanted-symbol sites, so there was no prefix here to get
/// wrong instead. The hazard belongs to [`define_abbrev`] and stays with it.
///
/// So the honest scope is: use this where a term with a hole is *all* that is
/// wanted. The four costs listed above are not an argument against a symbol
/// that is doing one of the three jobs in the paragraph above this one.
///
/// # It is the same substitution, and that is checkable
///
/// ```text
/// define_abbrev(env, x⃗, t)  ⊢ ∀x⃗. f(x⃗) = t
/// inst_all(…, s⃗)            ⊢ f(s⃗) = t[s⃗/x⃗]      ← the RHS is the term
/// subst_term(t, x⃗ ↦ s⃗)                  t[s⃗/x⃗]
/// ```
///
/// Both go through the kernel's *same* `close`-then-`open` pair, reached the
/// same way — [`Thm::gen_checked`] closes, [`Thm::ax_inst`] opens — so the two
/// agree node for node. `tests/subst_term.rs` pins that against
/// `define_abbrev` + `inst_all` directly, including the case that separates
/// simultaneous from sequential substitution.
///
/// **Simultaneous, not sequential**, which is what makes it a drop-in.
/// Every `xᵢ` is closed *before* any `sⱼ` is opened, so an `sᵢ` that mentions
/// `xⱼ` keeps that variable free instead of having `sⱼ` substituted into it.
/// A fold of one-variable substitutions would not do this, and would differ
/// from what the `define_abbrev` sites compute.
///
/// # Why this is not a hole in the trusted base
///
/// A `Term` is inert. Only a [`Thm`] carries truth, and the one built here is
/// `⊢ t[s⃗/x⃗] = t[s⃗/x⃗]` — reflexivity, which is available for any term at all.
/// Nothing is asserted about the result that was not already available from
/// [`Thm::eq_refl`]. Capture is impossible for the reason [`Thm::ax_inst`]'s
/// own doc gives: the representation is locally nameless, so the abstraction
/// step accounts for binder depth and the side condition classical
/// presentations *check* has been **removed** instead.
///
/// # Totality
///
/// Each step is total at this call pattern, and the `expect`s say which
/// invariant makes it so:
///
/// * [`Thm::gen_checked`] refuses only when `x` is free in a hypothesis, and
///   [`Thm::eq_refl`] has none — this is the side condition being *met*, not
///   waived;
/// * [`Thm::ax_inst`] refuses only a non-`∀` formula, and the fold above just
///   built `n` of them;
/// * [`Thm::mp`] refuses only a shape mismatch, which `ax_inst` cannot produce;
/// * `as_eq` refuses only a non-equation, and reflexivity is one.
///
/// A panic here would therefore be a kernel change, not a caller error, which
/// is why this returns `Term` rather than `Option<Term>`. That is the second
/// thing it buys over `define_abbrev`: there is no failure branch for a caller
/// to get wrong, and no wrong prefix for it to get wrong either.
pub fn subst_term(t: &Term, subs: &[(FreeVar, Term)]) -> Term {
    // `x⃗` all closed first — reversed, so that `subs[0]` ends up outermost and
    // the instantiation order below matches the substitution order.
    let mut all = Thm::eq_refl(t.clone());
    for (x, _) in subs.iter().rev() {
        all = Thm::gen_checked(*x, &all).expect("subst_term: reflexivity has no hypotheses");
    }
    // …then `s⃗` opened, outermost first.
    let ss: Vec<Term> = subs.iter().map(|(_, s)| s.clone()).collect();
    let inst = inst_all(&all, &ss).expect("subst_term: a ∀-nest of the length just built");
    // `.0` and `.1` are the *same term* — this is a reflexivity, and a mutation
    // swapping them lives for that reason rather than for want of a test.
    inst.concl().as_eq().expect("subst_term: reflexivity is an equation").0
}

// ─────────────────────────────────────────────────────────────────────────────
// Propositional toolkit.
//
// Everything below is derivable from the three Łukasiewicz axioms plus modus
// ponens. It exists because a Hilbert system has no deduction theorem to lean
// on: an implication has to be *assembled*, and without these it is unreadable.
// ─────────────────────────────────────────────────────────────────────────────

/// `Option`-shaped adaptor over [`rules::syl`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn syl(ab: &Thm, bc: &Thm) -> Option<Thm> {
    rules::syl(ab, bc).ok()
}

/// `Option`-shaped adaptor over [`rules::imp_mono_r`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn imp_mono_r(gd: &Thm, phi: Formula) -> Option<Thm> {
    rules::imp_mono_r(gd, phi).ok()
}

/// `Option`-shaped adaptor over [`rules::com12`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn com12(t: &Thm) -> Option<Thm> {
    rules::com12(t).ok()
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

/// `Option`-shaped adaptor over [`rules::and_elim_left`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn and_elim_left(t: &Thm) -> Option<Thm> {
    rules::and_elim_left(t).ok()
}

/// `Option`-shaped adaptor over [`rules::and_elim_right`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn and_elim_right(t: &Thm) -> Option<Thm> {
    rules::and_elim_right(t).ok()
}

/// `Option`-shaped adaptor over [`rules::iff_mp`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn iff_mp(t: &Thm) -> Option<Thm> {
    rules::iff_mp(t).ok()
}

/// `Option`-shaped adaptor over [`rules::iff_mpr`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn iff_mpr(t: &Thm) -> Option<Thm> {
    rules::iff_mpr(t).ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Quantifier toolkit.
//
// The awkward part of Hilbert-style FOL. `∃` is `¬∀¬`, so existential reasoning
// runs through contraposition and the distribution axiom, whose free-variable
// side condition has to be arranged rather than assumed.
// ─────────────────────────────────────────────────────────────────────────────

/// `Option`-shaped adaptor over [`rules::mpd_const`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn mpd_const(abc: &Thm, b: &Thm) -> Option<Thm> {
    rules::mpd_const(abc, b).ok()
}

/// `Option`-shaped adaptor over [`rules::contrapos`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn contrapos(ab: &Thm) -> Option<Thm> {
    rules::contrapos(ab).ok()
}

/// `Option`-shaped adaptor over [`rules::inst_self`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn inst_self(x: FreeVar, all: &Thm) -> Option<Thm> {
    rules::inst_self(x, all).ok()
}

/// `Option`-shaped adaptor over [`rules::forall_mono`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn forall_mono(x: FreeVar, all_imp: &Thm) -> Option<Thm> {
    rules::forall_mono(x, all_imp).ok()
}

/// `Option`-shaped adaptor over [`rules::exists_mono`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn exists_mono(x: FreeVar, all_imp: &Thm) -> Option<Thm> {
    rules::exists_mono(x, all_imp).ok()
}

/// `Option`-shaped adaptor over [`rules::exists_elim`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn exists_elim(x: FreeVar, ex: &Thm, all_imp: &Thm, psi: &Formula) -> Option<Thm> {
    rules::exists_elim(x, ex, all_imp, psi).ok()
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

/// `Option`-shaped adaptor over [`rules::hyp_mp`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_mp(h_imp: &Thm, h_arg: &Thm) -> Option<Thm> {
    rules::hyp_mp(h_imp, h_arg).ok()
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

/// `Option`-shaped adaptor over [`rules::hyp_and`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_and(hp: &Thm, hq: &Thm) -> Option<Thm> {
    rules::hyp_and(hp, hq).ok()
}

/// `Option`-shaped adaptor over [`rules::conj_of`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn conj_of(atoms: &[Formula]) -> Option<Formula> {
    rules::conj_of(atoms).ok()
}

/// `Option`-shaped adaptor over [`rules::conj_proj`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn conj_proj(atoms: &[Formula], i: usize) -> Option<Thm> {
    rules::conj_proj(atoms, i).ok()
}

/// `Option`-shaped adaptor over [`rules::conj_sub`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn conj_sub(atoms: &[Formula], start: usize, end: usize) -> Option<Thm> {
    rules::conj_sub(atoms, start, end).ok()
}

/// `Option`-shaped adaptor over [`rules::hyp_iff_mp`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_iff_mp(t: &Thm) -> Option<Thm> {
    rules::hyp_iff_mp(t).ok()
}

/// `Option`-shaped adaptor over [`rules::hyp_iff_mpr`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_iff_mpr(t: &Thm) -> Option<Thm> {
    rules::hyp_iff_mpr(t).ok()
}

/// Decompose `φ ↔ ψ` into its two implication halves.
pub(crate) fn split_iff(iff: &Formula) -> Option<(Formula, Formula)> {
    // `a ∧ b` is `¬(a → ¬b)`, i.e. `(a → (b → ⊥)) → ⊥`.
    let (inner, _) = iff.as_imp()?;
    let (fwd, nb) = inner.as_imp()?;
    let (bwd, _) = nb.as_imp()?;
    Some((fwd, bwd))
}

/// `Option`-shaped adaptor over [`rules::curry`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn curry(imp2: &Thm) -> Option<Thm> {
    rules::curry(imp2).ok()
}

/// `Option`-shaped adaptor over [`rules::disj_of`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn disj_of(atoms: &[Formula]) -> Option<Formula> {
    rules::disj_of(atoms).ok()
}

/// `Option`-shaped adaptor over [`rules::disj_inject`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn disj_inject(atoms: &[Formula], i: usize) -> Option<Thm> {
    rules::disj_inject(atoms, i).ok()
}

/// `Option`-shaped adaptor over [`rules::conjoin`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn conjoin(t: &Thm) -> Option<Thm> {
    rules::conjoin(t).ok()
}

/// `Option`-shaped adaptor over [`rules::uncurry`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn uncurry(and_imp: &Thm) -> Option<Thm> {
    rules::uncurry(and_imp).ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Set-theoretic constructions.
// ─────────────────────────────────────────────────────────────────────────────

/// `Option`-shaped adaptor over [`rules::define_by_membership`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn define_by_membership(
    env: &mut Env,
    params: &[FreeVar],
    existence: &Thm,
    z: FreeVar,
    phi: &Formula,
) -> Option<(FnSym, Thm)> {
    rules::define_by_membership(env, params, existence, z, phi).ok()
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

/// `Option`-shaped adaptor over [`rules::hyp_or_same`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_or_same(t: &Thm) -> Option<Thm> {
    rules::hyp_or_same(t).ok()
}

/// `Option`-shaped adaptor over [`rules::exists_intro_imp`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn exists_intro_imp(v: FreeVar, phi: Formula, t: Term) -> Option<Thm> {
    rules::exists_intro_imp(v, phi, t).ok()
}

/// `Option`-shaped adaptor over [`rules::exists_elim_imp`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn exists_elim_imp(v: FreeVar, all_imp: &Thm, psi: &Formula) -> Option<Thm> {
    rules::exists_elim_imp(v, all_imp, psi).ok()
}

/// `Option`-shaped adaptor over [`rules::union_singleton`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn union_singleton(env: &mut Env, up: FnSym, up_ax: &Thm, un: FnSym, un_ax: &Thm) -> Option<Thm> {
    rules::union_singleton(env, up, up_ax, un, un_ax).ok()
}

/// `Option`-shaped adaptor over [`rules::mem_singleton`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn mem_singleton(env: &mut Env, up: FnSym, up_ax: &Thm) -> Option<Thm> {
    rules::mem_singleton(env, up, up_ax).ok()
}

/// `Option`-shaped adaptor over [`rules::singleton_inj`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn singleton_inj(env: &mut Env, up: FnSym, mem_sing: &Thm) -> Option<Thm> {
    rules::singleton_inj(env, up, mem_sing).ok()
}

/// `⊢ (φ → ψ) → (¬ψ → ¬φ)` — contraposition, internalised.
pub fn contrapos_imp(phi: Formula, psi: Formula) -> Thm { syl_imp(phi, psi, Formula::false_()) }

/// `Option`-shaped adaptor over [`rules::hyp_or_elim`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn hyp_or_elim(h_disj: &Thm, h_left: &Thm, h_right: &Thm) -> Option<Thm> {
    rules::hyp_or_elim(h_disj, h_left, h_right).ok()
}

/// `Option`-shaped adaptor over [`rules::upair_members`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn upair_members(up_ax: &Thm, a: &Term, b: &Term) -> Option<(Thm, Thm)> {
    rules::upair_members(up_ax, a, b).ok()
}

/// `⊢ a = b → b = a` — symmetry of equality, in implication form.
pub fn eq_symm_imp(env: &mut Env, a: Term, b: Term) -> Thm {
    let x = env.fresh_var();
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
    mpd_const(&leib, &Thm::eq_refl(a)).expect("eq_symm_imp: reflexivity discharges the antecedent")
}

/// `Option`-shaped adaptor over [`rules::opair_fst`], for `mini/` and
/// `checker/`. The reason is discarded here; see [`rules`].
pub fn opair_fst(env: &mut Env, up: FnSym, up_ax: &Thm, mem_sing: &Thm, sing_inj: &Thm) -> Option<Thm> {
    rules::opair_fst(env, up, up_ax, mem_sing, sing_inj).ok()
}
