//! Theorems, inference rules, and the axioms of Tarski–Grothendieck set theory.
//!
//! # Why Hilbert style
//!
//! `CLAUDE.md` requires that **`Thm` is a formula — no context, no hypothesis
//! list, no environment**. A natural-deduction kernel cannot satisfy that: its
//! judgement is `Γ ⊢ φ`, and every step would carry and compare a context. A
//! Hilbert system's judgement is just `⊢ φ`, so [`Thm`] wraps a single
//! [`Formula`] and nothing else.
//!
//! That is not merely aesthetic. It is what makes the definitional-equality
//! cache globally sound: a theorem here is valid absolutely, not relative to
//! some Lean local context, so a cached equality is reusable across the whole
//! development. It also means memory is O(live theorems) rather than O(proof
//! size) — derivations exist only as the transient history of API calls.
//!
//! # The trusted surface
//!
//! Everything marked "primitive rule" below is trusted: if one of them is
//! unsound, the system proves nothing. Everything marked "derived" is *not*
//! trusted in the same way — it is ordinary code that can only reach a `Thm` by
//! calling primitives, so a bug there yields a rejection or a wrong-but-derivable
//! theorem, never an underivable one.

use crate::term::{FnSym, Formula, FormulaData, FreeVar, Term, VarGen};

/// A proved formula.
///
/// The only way to obtain one is through the inference rules in this module.
/// The field is private and there is no public constructor, so a client cannot
/// forge a theorem — that is the whole LCF argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Thm {
    concl: Formula,
}

impl Thm {
    /// The formula this theorem asserts.
    pub fn concl(&self) -> &Formula { &self.concl }

    /// Internal: the single point at which a `Thm` comes into existence.
    /// Every use of this is a trusted step and should sit under a rule that
    /// documents why the conclusion is valid.
    fn mk(concl: Formula) -> Thm { Thm { concl } }
}

/// Whether a formula is locally closed. Exposed for the substitution tests.
pub fn debug_locally_closed(f: &Formula) -> bool { f.locally_closed(0) }

/// The signature: which function symbols exist, and a source of fresh variables.
///
/// Function symbols are introduced by **pure signature extension** — a new
/// symbol with *no* axioms constraining it. That is unconditionally
/// conservative: any model of the base theory expands to a model of the
/// extension by interpreting the new symbol arbitrarily, so nothing new becomes
/// provable in the base language, and in particular consistency is preserved.
/// No proof obligation, and no growth of the trusted base.
///
/// This is enough for the equational fragment of the Lean interpretation:
/// reflexivity, symmetry, transitivity and congruence hold for *any* function
/// symbols whatever, because they are consequences of the equality axioms
/// rather than of anything specific to sets. Rules that need the symbols to
/// actually *mean* something — beta reduction, above all — require defining
/// axioms and hence a conservativity obligation; see `kernel/README.md`.
#[derive(Debug, Default)]
pub struct Env {
    next_sym: u32,
    vars: VarGen,
}

impl Env {
    /// An empty signature.
    pub fn new() -> Self { Env { next_sym: 0, vars: VarGen::new() } }

    /// Introduce a fresh function symbol of the given arity, constrained by no
    /// axioms. Conservative by construction; see the type-level docs.
    pub fn declare(&mut self, arity: u32) -> FnSym {
        let id = self.next_sym;
        self.next_sym = self.next_sym.checked_add(1).expect("function symbol counter overflow");
        FnSym { id, arity }
    }

    /// A variable distinct from all others produced by this environment.
    pub fn fresh_var(&mut self) -> FreeVar { self.vars.fresh() }
}

// ─────────────────────────────────────────────────────────────────────────────
// Primitive rules — the trusted core.
//
// The propositional fragment is the standard Łukasiewicz axiomatisation, which
// is complete for classical propositional logic; the quantifier fragment adds
// instantiation and the distribution axiom; equality adds reflexivity and
// Leibniz. All are valid under the usual Tarskian semantics.
// ─────────────────────────────────────────────────────────────────────────────

impl Thm {
    /// Primitive rule (A1): `φ → (ψ → φ)`.
    pub fn ax_k(phi: Formula, psi: Formula) -> Thm {
        Thm::mk(Formula::imp(phi.clone(), Formula::imp(psi, phi)))
    }

    /// Primitive rule (A2): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`.
    pub fn ax_s(phi: Formula, psi: Formula, chi: Formula) -> Thm {
        let left = Formula::imp(phi.clone(), Formula::imp(psi.clone(), chi.clone()));
        let right = Formula::imp(Formula::imp(phi.clone(), psi), Formula::imp(phi, chi));
        Thm::mk(Formula::imp(left, right))
    }

    /// Primitive rule (A3), classical: `(¬φ → ¬ψ) → (ψ → φ)`.
    ///
    /// This is what makes the logic classical, which the target theory requires.
    pub fn ax_contra(phi: Formula, psi: Formula) -> Thm {
        let left = Formula::imp(Formula::not(phi.clone()), Formula::not(psi.clone()));
        Thm::mk(Formula::imp(left, Formula::imp(psi, phi)))
    }

    /// Primitive rule (A4), universal instantiation: `(∀x. φ) → φ[t/x]`.
    ///
    /// No "substitutable for" side condition is needed here, unlike in a named
    /// representation: `t` is locally closed by construction and the bound
    /// occurrences it replaces are de Bruijn indices, so capture is impossible.
    /// That side condition is exactly the one that classically goes wrong, and
    /// the representation has removed it rather than checked it.
    ///
    /// Returns `None` if `phi` is not universally quantified.
    pub fn ax_inst(phi: Formula, t: Term) -> Option<Thm> {
        let body = phi.instantiate(&t)?;
        Some(Thm::mk(Formula::imp(phi, body)))
    }

    /// Primitive rule (A5), distribution: `(∀x. (φ → ψ)) → (φ → ∀x. ψ)`,
    /// **provided `x` does not occur free in `φ`**.
    ///
    /// This is the other classic side condition, and here it is real and must be
    /// checked: without it one could derive `(∀x. x=x → P(x)) → (x=x → ∀x. P(x))`
    /// and generalise a variable that is still constrained. Returns `None` when
    /// the condition fails.
    pub fn ax_dist(x: FreeVar, phi: Formula, psi: Formula) -> Option<Thm> {
        if phi.occurs_free(x) {
            return None
        }
        let left = Formula::forall(x, Formula::imp(phi.clone(), psi.clone()));
        let right = Formula::imp(phi, Formula::forall(x, psi));
        Some(Thm::mk(Formula::imp(left, right)))
    }

    /// Primitive rule, modus ponens: from `⊢ φ → ψ` and `⊢ φ` infer `⊢ ψ`.
    ///
    /// Returns `None` if the premises do not line up — a mismatch is a bug in
    /// the untrusted caller, and rejecting is the correct response.
    pub fn mp(imp: &Thm, arg: &Thm) -> Option<Thm> {
        match imp.concl.data() {
            FormulaData::Imp(a, b) if *a == arg.concl => Some(Thm::mk(b.clone())),
            _ => None,
        }
    }

    /// Primitive rule, generalisation: from `⊢ φ` infer `⊢ ∀x. φ`.
    ///
    /// Unconditionally sound *because* `Thm` carries no hypotheses. In a system
    /// with contexts this would need `x ∉ FV(Γ)`; having no `Γ` is precisely
    /// what removes the side condition. This is the payoff of the context-free
    /// design showing up as a smaller trusted surface.
    pub fn gen(x: FreeVar, thm: &Thm) -> Thm { Thm::mk(Formula::forall(x, thm.concl.clone())) }

    /// Primitive rule, reflexivity of equality: `⊢ t = t`.
    pub fn eq_refl(t: Term) -> Thm { Thm::mk(Formula::eq(t.clone(), t)) }

    /// Primitive rule, Leibniz / substitution of equals:
    /// `⊢ a = b → (φ[a/x] → φ[b/x])`.
    ///
    /// Together with reflexivity this generates the whole equality theory —
    /// symmetry, transitivity and congruence are *derived* below rather than
    /// trusted.
    pub fn eq_leibniz(a: Term, b: Term, x: FreeVar, phi: Formula) -> Thm {
        let phi_a = phi.subst(x, &a);
        let phi_b = phi.subst(x, &b);
        Thm::mk(Formula::imp(Formula::eq(a, b), Formula::imp(phi_a, phi_b)))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The axioms of Tarski–Grothendieck set theory.
//
// Each is a primitive: it is asserted, not derived, and is part of the trusted
// base. Tarski's Axiom A is what supplies arbitrarily large inaccessible
// cardinals, which is what covers Lean's universe hierarchy.
// ─────────────────────────────────────────────────────────────────────────────

/// `q = {a}`, said without introducing a singleton symbol: `∀r. (r ∈ q ↔ r = a)`.
pub fn is_singleton(env: &mut Env, q: Term, a: Term) -> Formula {
    let r = env.fresh_var();
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q), Formula::eq(Term::var(r), a)))
}

/// `q = {a, b}`: `∀r. (r ∈ q ↔ (r = a ∨ r = b))`.
pub fn is_upair(env: &mut Env, q: Term, a: Term, b: Term) -> Formula {
    let r = env.fresh_var();
    let rhs = Formula::or(Formula::eq(Term::var(r), a), Formula::eq(Term::var(r), b));
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q), rhs))
}

/// `p = ⟨a, b⟩` in the Kuratowski sense, i.e. `p = {{a}, {a,b}}`, written as a
/// formula: `∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b}))`.
///
/// Describing pairs rather than introducing a pairing *symbol* is what lets
/// Tarski's axiom mention functions while the primitive signature stays `{∈,=}`.
pub fn is_opair(env: &mut Env, p: Term, a: Term, b: Term) -> Formula {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let left = is_singleton(env, tq.clone(), a.clone());
    let right = is_upair(env, tq.clone(), a, b);
    Formula::forall(q, Formula::iff(Formula::mem(tq, p), Formula::or(left, right)))
}

/// `⟨a, b⟩ ∈ f`: `∃p. (p ∈ f ∧ p = ⟨a,b⟩)`.
pub fn pair_in(env: &mut Env, f: Term, a: Term, b: Term) -> Formula {
    let p = env.fresh_var();
    let tp = Term::var(p);
    let is_pair = is_opair(env, tp.clone(), a, b);
    Formula::exists(p, Formula::and(Formula::mem(tp, f), is_pair))
}

/// `x ≈ m` — there is a bijection from `x` onto `m`.
///
/// Spelled out as: some `f` whose pairs all run from `x` to `m`, is total on
/// `x`, is onto `m`, is single-valued, and is injective. This is the disjunct
/// whose omission made the earlier Tarski axiom inconsistent, so it is written
/// out in full rather than approximated.
pub fn equinumerous(env: &mut Env, x: Term, m: Term) -> Formula {
    let f = env.fresh_var();
    let tf = Term::var(f);

    let (a1, b1) = (env.fresh_var(), env.fresh_var());
    let in_xm = {
        let p = pair_in(env, tf.clone(), Term::var(a1), Term::var(b1));
        let concl = Formula::and(Formula::mem(Term::var(a1), x.clone()), Formula::mem(Term::var(b1), m.clone()));
        Formula::forall(a1, Formula::forall(b1, Formula::imp(p, concl)))
    };

    let (a2, b2) = (env.fresh_var(), env.fresh_var());
    let total = {
        let p = pair_in(env, tf.clone(), Term::var(a2), Term::var(b2));
        Formula::forall(a2, Formula::imp(Formula::mem(Term::var(a2), x.clone()), Formula::exists(b2, p)))
    };

    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let onto = {
        let p = pair_in(env, tf.clone(), Term::var(a3), Term::var(b3));
        Formula::forall(b3, Formula::imp(Formula::mem(Term::var(b3), m.clone()), Formula::exists(a3, p)))
    };

    let (a4, b4, c4) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let single_valued = {
        let p1 = pair_in(env, tf.clone(), Term::var(a4), Term::var(b4));
        let p2 = pair_in(env, tf.clone(), Term::var(a4), Term::var(c4));
        let concl = Formula::eq(Term::var(b4), Term::var(c4));
        Formula::forall(a4, Formula::forall(b4, Formula::forall(c4, Formula::imp(Formula::and(p1, p2), concl))))
    };

    let (a5, b5, c5) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let injective = {
        let p1 = pair_in(env, tf.clone(), Term::var(a5), Term::var(c5));
        let p2 = pair_in(env, tf.clone(), Term::var(b5), Term::var(c5));
        let concl = Formula::eq(Term::var(a5), Term::var(b5));
        Formula::forall(a5, Formula::forall(b5, Formula::forall(c5, Formula::imp(Formula::and(p1, p2), concl))))
    };

    let body = Formula::and(in_xm, Formula::and(total, Formula::and(onto, Formula::and(single_valued, injective))));
    Formula::exists(f, body)
}

/// `x ⊆ y`, i.e. `∀z. z ∈ x → z ∈ y`.
pub fn subset(env: &mut Env, x: Term, y: Term) -> Formula {
    let z = env.fresh_var();
    Formula::forall(z, Formula::imp(Formula::mem(Term::var(z), x), Formula::mem(Term::var(z), y)))
}

impl Thm {
    /// Extensionality: `∀x ∀y. (∀z. z ∈ x ↔ z ∈ y) → x = y`.
    pub fn ax_extensionality(env: &mut Env) -> Thm {
        let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
        let same = Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), tx.clone()), Formula::mem(tz, ty.clone())));
        Thm::mk(Formula::forall(x, Formula::forall(y, Formula::imp(same, Formula::eq(tx, ty)))))
    }

    /// Pairing: `∀x ∀y ∃p ∀z. z ∈ p ↔ (z = x ∨ z = y)`.
    pub fn ax_pairing(env: &mut Env) -> Thm {
        let (x, y, p, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tp, tz) = (Term::var(x), Term::var(y), Term::var(p), Term::var(z));
        let rhs = Formula::or(Formula::eq(tz.clone(), tx), Formula::eq(tz.clone(), ty));
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tp), rhs));
        Thm::mk(Formula::forall(x, Formula::forall(y, Formula::exists(p, inner))))
    }

    /// Union: `∀x ∃u ∀z. z ∈ u ↔ ∃y. (y ∈ x ∧ z ∈ y)`.
    pub fn ax_union(env: &mut Env) -> Thm {
        let (x, u, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, tu, tz, ty) = (Term::var(x), Term::var(u), Term::var(z), Term::var(y));
        let witness = Formula::exists(y, Formula::and(Formula::mem(ty.clone(), tx), Formula::mem(tz.clone(), ty)));
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tu), witness));
        Thm::mk(Formula::forall(x, Formula::exists(u, inner)))
    }

    /// Power set: `∀x ∃p ∀z. z ∈ p ↔ z ⊆ x`.
    pub fn ax_power(env: &mut Env) -> Thm {
        let (x, p, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, tp, tz) = (Term::var(x), Term::var(p), Term::var(z));
        let sub = subset(env, tz.clone(), tx);
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tp), sub));
        Thm::mk(Formula::forall(x, Formula::exists(p, inner)))
    }

    /// Regularity: every non-empty set has an `∈`-minimal element.
    /// `∀x. (∃y. y ∈ x) → ∃y. (y ∈ x ∧ ¬∃z. (z ∈ y ∧ z ∈ x))`.
    pub fn ax_regularity(env: &mut Env) -> Thm {
        let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
        let nonempty = Formula::exists(y, Formula::mem(ty.clone(), tx.clone()));
        let clash = Formula::exists(z, Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz, tx.clone())));
        let minimal = Formula::exists(y, Formula::and(Formula::mem(ty, tx), Formula::not(clash)));
        Thm::mk(Formula::forall(x, Formula::imp(nonempty, minimal)))
    }

    /// Replacement, as a scheme. For a relation `φ(x, y)` supplied by the caller
    /// as a formula with two designated free variables:
    ///
    /// `∀a. (∀x. x ∈ a → ∃!y. φ) → ∃b ∀y. (y ∈ b ↔ ∃x. (x ∈ a ∧ φ))`
    ///
    /// Being a scheme, this is instantiated per-formula rather than quantified
    /// over relations, which first-order logic cannot do.
    pub fn ax_replacement(env: &mut Env, x: FreeVar, y: FreeVar, phi: Formula) -> Thm {
        let (a, b, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(a), Term::var(b));
        let (tx, ty) = (Term::var(x), Term::var(y));

        // ∃!y. φ  ≡  ∃y. (φ ∧ ∀y'. φ[y'/y] → y' = y)
        let uniq = Formula::forall(
            y2,
            Formula::imp(phi.subst(y, &Term::var(y2)), Formula::eq(Term::var(y2), ty.clone())),
        );
        let exists_unique = Formula::exists(y, Formula::and(phi.clone(), uniq));
        let hyp = Formula::forall(x, Formula::imp(Formula::mem(tx.clone(), ta.clone()), exists_unique));

        let image = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
        let concl = Formula::exists(b, Formula::forall(y, Formula::iff(Formula::mem(ty, tb), image)));

        Thm::mk(Formula::forall(a, Formula::imp(hyp, concl)))
    }

    // ── Tarski's Axiom A ─────────────────────────────────────────────────────
    //
    // An earlier version of this stated the inaccessibility clause as
    // `∀y. (y ⊆ u → y ∈ u)`, dropping the `y ≈ u` disjunct. That was
    // **inconsistent**: at `y := u` the derivable `u ⊆ u` forces `u ∈ u`, which
    // Regularity refutes. Weakening a disjunction by dropping a disjunct
    // *strengthens* the axiom. See `kernel/tests/tarski_regression.rs`.
    //
    // What follows is the standard Tarski–Grothendieck statement, with the
    // disjunct restored. Equinumerosity is spelled out as a first-order formula
    // over `∈` and `=` — ordered pairs are *described*, not introduced as
    // symbols — so this adds no primitives.

    /// Tarski's Axiom A: every set belongs to a Grothendieck universe.
    ///
    /// `∀x ∃u.  x ∈ u`
    /// ` ∧ (∀y ∈ u. ∀z ⊆ y. z ∈ u)`            — closed under subsets of members
    /// ` ∧ (∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p)`    — power sets stay inside
    /// ` ∧ (∀y ⊆ u. (y ≈ u ∨ y ∈ u))`          — inaccessibility
    ///
    /// This is what supplies arbitrarily large inaccessible cardinals, and
    /// hence what covers Lean's universe hierarchy. It is also the intended
    /// source of the empty set: a Grothendieck universe contains one, and
    /// without it Separation is not derivable from the other axioms.
    ///
    /// **Trusted.** Read it against a reference statement rather than against
    /// intuition; the previous version looked plausible and was contradictory.
    pub fn ax_tarski(env: &mut Env) -> Thm {
        let (x, u) = (env.fresh_var(), env.fresh_var());
        let (tx, tu) = (Term::var(x), Term::var(u));

        // ∀y ∈ u. ∀z ⊆ y. z ∈ u
        let (y1, z1) = (env.fresh_var(), env.fresh_var());
        let (ty1, tz1) = (Term::var(y1), Term::var(z1));
        let sub_z1y1 = subset(env, tz1.clone(), ty1.clone());
        let closed_sub = Formula::forall(
            y1,
            Formula::imp(
                Formula::mem(ty1, tu.clone()),
                Formula::forall(z1, Formula::imp(sub_z1y1, Formula::mem(tz1, tu.clone()))),
            ),
        );

        // ∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p
        let (y2, z2, p2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (ty2, tz2, tp2) = (Term::var(y2), Term::var(z2), Term::var(p2));
        let sub_z2y2 = subset(env, tz2.clone(), ty2.clone());
        let closed_pow = Formula::forall(
            y2,
            Formula::imp(
                Formula::mem(ty2, tu.clone()),
                Formula::exists(
                    p2,
                    Formula::and(
                        Formula::mem(tp2.clone(), tu.clone()),
                        Formula::forall(z2, Formula::imp(sub_z2y2, Formula::mem(tz2, tp2))),
                    ),
                ),
            ),
        );

        // ∀y ⊆ u. (y ≈ u ∨ y ∈ u)
        let y3 = env.fresh_var();
        let ty3 = Term::var(y3);
        let sub_y3u = subset(env, ty3.clone(), tu.clone());
        let equi = equinumerous(env, ty3.clone(), tu.clone());
        let inacc = Formula::forall(
            y3,
            Formula::imp(sub_y3u, Formula::or(equi, Formula::mem(ty3, tu.clone()))),
        );

        let body = Formula::and(
            Formula::mem(tx, tu),
            Formula::and(closed_sub, Formula::and(closed_pow, inacc)),
        );
        Thm::mk(Formula::forall(x, Formula::exists(u, body)))
    }

}

// ─────────────────────────────────────────────────────────────────────────────
// Conservative definitional extension.
// ─────────────────────────────────────────────────────────────────────────────

/// The statement `∃!y. φ`, spelled out as `∃y. (φ ∧ ∀y'. (φ[y'/y] → y' = y))`.
///
/// The choice of the fresh `y'` is invisible: the locally nameless
/// representation makes alpha-equivalent formulas *syntactically* equal, so two
/// calls with different fresh variables produce the same formula. That is what
/// lets [`define`] compare a caller's witness against the statement it expects
/// without any alpha-comparison.
pub fn exists_unique(env: &mut Env, y: FreeVar, phi: &Formula) -> Formula {
    let y2 = env.fresh_var();
    let uniq = Formula::forall(y2, Formula::imp(phi.subst(y, &Term::var(y2)), Formula::eq(Term::var(y2), Term::var(y))));
    Formula::exists(y, Formula::and(phi.clone(), uniq))
}

/// Universally quantify `body` over `xs`, outermost first.
fn close_all(xs: &[FreeVar], body: Formula) -> Formula {
    xs.iter().rev().fold(body, |acc, x| Formula::forall(*x, acc))
}

/// **Primitive: definitional extension.**
///
/// Given a proof of `⊢ ∀x⃗. ∃!y. φ(x⃗, y)`, introduce a fresh function symbol
/// `f` of arity `|x⃗|` and return its defining axiom `⊢ ∀x⃗. φ(x⃗, f(x⃗))`.
///
/// # Why this is conservative
///
/// This is the standard theorem on extension by definitions. Any model of the
/// base theory satisfies `∀x⃗ ∃!y. φ`, so it can be expanded — uniquely — to
/// interpret `f` as the function picking that `y`. Hence every model expands,
/// nothing new is provable in the base language, and consistency is preserved.
/// The existence-and-uniqueness premise is exactly what makes the expansion
/// well defined, which is why it is *required as a theorem* rather than
/// assumed: without uniqueness the symbol would be a choice function and the
/// extension would no longer be conservative.
///
/// Returns `None` if the witness does not prove precisely the expected
/// statement. Rejecting is right: a mismatch means the caller has not
/// discharged the obligation.
pub fn define(
    env: &mut Env,
    xs: &[FreeVar],
    y: FreeVar,
    phi: Formula,
    witness: &Thm,
) -> Option<(FnSym, Thm)> {
    // `y` must not be one of the parameters, or `f(x⃗)` would capture it.
    if xs.contains(&y) {
        return None
    }
    // Every free variable of `phi` must be a parameter or the defined variable.
    //
    // Without this the extension is **unsound**, not merely sloppy. Take
    // `xs = []` and `φ(y) := (y = v)` for a stray `v`. Then `∃!y. y = v` is
    // provable, and the defining axiom is `⊢ f = v` with `v` free. A free
    // variable in a context-free system is implicitly universally quantified,
    // and `gen` makes that explicit: `⊢ ∀v. f = v`. Instantiating twice gives
    // `f = c₁` and `f = c₂`, hence `c₁ = c₂` for arbitrary constants.
    //
    // The underlying error is that the witness proves "for each `v` there is a
    // unique `y`", so the `y` depends on `v` — but `f(x⃗)` has no `v` argument,
    // so the axiom claims a single `f` works for every `v`. That is strictly
    // stronger than what was proved.
    let mut fvs = Vec::new();
    phi.free_vars(&mut fvs);
    if fvs.iter().any(|v| *v != y && !xs.contains(v)) {
        return None
    }
    let expected = close_all(xs, exists_unique(env, y, &phi));
    if *witness.concl() != expected {
        return None
    }
    let arity = u32::try_from(xs.len()).ok()?;
    let f = env.declare(arity);
    let applied = Term::apply(f, xs.iter().map(|x| Term::var(*x)).collect());
    let axiom = close_all(xs, phi.subst(y, &applied));
    Some((f, Thm::mk_defining_axiom(axiom)))
}

impl Thm {
    /// Trusted: the defining axiom produced by [`define`]. Private to this
    /// module's definitional-extension path so it cannot be used to assert
    /// anything else.
    fn mk_defining_axiom(f: Formula) -> Thm { Thm::mk(f) }
}
