//! The exact formula of [`Thm::ax_tarski`], rebuilt from the constructors.
//!
//! # Why this shape of test
//!
//! `ax_tarski` is the axiom in this kernel with the worst history — an earlier
//! statement of its inaccessibility clause dropped the `y ≈ u` disjunct and was
//! outright **inconsistent** — and until now it had the weakest test of any
//! axiom: a well-formedness check plus a non-triviality check on
//! `equinumerous` (`rules.rs`), and a *grep over the source text* in
//! `tarski_regression.rs`. That grep has already failed once in the way greps
//! fail: a fifth clause (transitivity) was added to the axiom and every test in
//! the suite still passed, because no test compared against the axiom's actual
//! conclusion. A test that does not do that pins nothing.
//!
//! So this file follows `choice.rs`. Every assertion is against
//! `Thm::ax_tarski(&mut env).concl()`, and the formula it is compared with is
//! built here from `Formula` and `Term` constructors only. In particular it
//! does **not** call `kernel::thm::equinumerous`, `subset`, `is_opair`,
//! `is_singleton`, `is_upair` or `pair_in` — reusing the kernel's own builders
//! would make the comparison a tautology, which is exactly how a wrong clause
//! survives.
//!
//! # The reference statement
//!
//! Mizar's Tarski Axiom A, in the standard four clauses:
//!
//! ```text
//!   N ∈ M
//!   X ∈ M ∧ Y ⊆ X  →  Y ∈ M
//!   X ∈ M          →  ∃Z ∈ M. ∀Y ⊆ X. Y ∈ Z
//!   X ⊆ M          →  X ≈ M ∨ X ∈ M
//! ```
//!
//! plus the **transitivity** clause this project added on 2026-07-31,
//! `∀y ∈ u. ∀z ∈ y. z ∈ u`, which is what distinguishes a Grothendieck universe
//! from a bare Tarski one and which the empty-set derivation now depends on.
//! The axiom's own nesting is `x ∈ u ∧ (C₁ ∧ (C₂ ∧ (C₃ ∧ C₄)))` with
//! `C₁` transitivity, `C₂` subset-closure, `C₃` power-closure, `C₄`
//! inaccessibility, and that nesting is pinned here too: a re-association is a
//! different formula and this test says so.
//!
//! The locally nameless representation is what makes the comparison possible:
//! every quantifier closes over its variable, so two independently built copies
//! of the same closed formula are *syntactically* equal despite using different
//! fresh variables.

use kernel::{Env, Formula, Term, Thm};

// ─────────────────────────────────────────────────────────────────────────────
// Kuratowski pairs and inclusion, described from scratch.
// ─────────────────────────────────────────────────────────────────────────────

/// `q = {a}`: `∀r. (r ∈ q ↔ r = a)`.
fn singleton(env: &mut Env, q: &Term, a: &Term) -> Formula {
    let r = env.fresh_var();
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q.clone()), Formula::eq(Term::var(r), a.clone())))
}

/// `q = {a,b}`: `∀r. (r ∈ q ↔ (r = a ∨ r = b))`.
fn upair(env: &mut Env, q: &Term, a: &Term, b: &Term) -> Formula {
    let r = env.fresh_var();
    let rhs = Formula::or(Formula::eq(Term::var(r), a.clone()), Formula::eq(Term::var(r), b.clone()));
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q.clone()), rhs))
}

/// `p = ⟨a,b⟩ = {{a},{a,b}}`: `∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b}))`.
fn opair(env: &mut Env, p: &Term, a: &Term, b: &Term) -> Formula {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let left = singleton(env, &tq, a);
    let right = upair(env, &tq, a, b);
    Formula::forall(q, Formula::iff(Formula::mem(tq, p.clone()), Formula::or(left, right)))
}

/// `⟨a,b⟩ ∈ f`: `∃p. (p ∈ f ∧ p = ⟨a,b⟩)`.
fn pair_in(env: &mut Env, f: &Term, a: &Term, b: &Term) -> Formula {
    let p = env.fresh_var();
    let tp = Term::var(p);
    let is_pair = opair(env, &tp, a, b);
    Formula::exists(p, Formula::and(Formula::mem(tp, f.clone()), is_pair))
}

/// `x ⊆ y`: `∀z. (z ∈ x → z ∈ y)`.
fn included(env: &mut Env, x: &Term, y: &Term) -> Formula {
    let z = env.fresh_var();
    Formula::forall(z, Formula::imp(Formula::mem(Term::var(z), x.clone()), Formula::mem(Term::var(z), y.clone())))
}

// ─────────────────────────────────────────────────────────────────────────────
// `x ≈ m`, spelled out.
// ─────────────────────────────────────────────────────────────────────────────

/// `x ≈ m`: some `f` whose pairs run from `x` to `m`, total on `x`, onto `m`,
/// single-valued and injective — i.e. a bijection.
///
/// This is the disjunct whose omission made the earlier axiom inconsistent, so
/// it is written out conjunct by conjunct, in the axiom's own nesting
/// `in_xm ∧ (total ∧ (onto ∧ (single_valued ∧ injective)))`.
fn equinumerous(env: &mut Env, x: &Term, m: &Term) -> Formula {
    let f = env.fresh_var();
    let tf = Term::var(f);

    // ∀a ∀b. (⟨a,b⟩ ∈ f → (a ∈ x ∧ b ∈ m))
    let (a1, b1) = (env.fresh_var(), env.fresh_var());
    let in_xm = {
        let p = pair_in(env, &tf, &Term::var(a1), &Term::var(b1));
        let concl = Formula::and(Formula::mem(Term::var(a1), x.clone()), Formula::mem(Term::var(b1), m.clone()));
        Formula::forall(a1, Formula::forall(b1, Formula::imp(p, concl)))
    };

    // ∀a. (a ∈ x → ∃b. ⟨a,b⟩ ∈ f)
    let (a2, b2) = (env.fresh_var(), env.fresh_var());
    let total = {
        let p = pair_in(env, &tf, &Term::var(a2), &Term::var(b2));
        Formula::forall(a2, Formula::imp(Formula::mem(Term::var(a2), x.clone()), Formula::exists(b2, p)))
    };

    // ∀b. (b ∈ m → ∃a. ⟨a,b⟩ ∈ f)
    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let onto = {
        let p = pair_in(env, &tf, &Term::var(a3), &Term::var(b3));
        Formula::forall(b3, Formula::imp(Formula::mem(Term::var(b3), m.clone()), Formula::exists(a3, p)))
    };

    // ∀a ∀b ∀c. ((⟨a,b⟩ ∈ f ∧ ⟨a,c⟩ ∈ f) → b = c)
    let (a4, b4, c4) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let single_valued = {
        let p1 = pair_in(env, &tf, &Term::var(a4), &Term::var(b4));
        let p2 = pair_in(env, &tf, &Term::var(a4), &Term::var(c4));
        let concl = Formula::eq(Term::var(b4), Term::var(c4));
        Formula::forall(a4, Formula::forall(b4, Formula::forall(c4, Formula::imp(Formula::and(p1, p2), concl))))
    };

    // ∀a ∀b ∀c. ((⟨a,c⟩ ∈ f ∧ ⟨b,c⟩ ∈ f) → a = b)
    let (a5, b5, c5) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let injective = {
        let p1 = pair_in(env, &tf, &Term::var(a5), &Term::var(c5));
        let p2 = pair_in(env, &tf, &Term::var(b5), &Term::var(c5));
        let concl = Formula::eq(Term::var(a5), Term::var(b5));
        Formula::forall(a5, Formula::forall(b5, Formula::forall(c5, Formula::imp(Formula::and(p1, p2), concl))))
    };

    let body = Formula::and(in_xm, Formula::and(total, Formula::and(onto, Formula::and(single_valued, injective))));
    Formula::exists(f, body)
}

// ─────────────────────────────────────────────────────────────────────────────
// The five clauses.
// ─────────────────────────────────────────────────────────────────────────────

/// `C₁`, transitivity: `∀y. (y ∈ u → ∀z. (z ∈ y → z ∈ u))`.
///
/// `membership` selects the relation between `z` and `y`. With `false` the
/// clause reads `z ⊆ y`, which makes it *literally the same formula* as `C₂` —
/// that is the collapse this file's negative test rules out, and it would leave
/// the axiom exactly as weak as it was before transitivity was added.
fn clause_transitive(env: &mut Env, u: &Term, membership: bool) -> Formula {
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let rel = if membership { Formula::mem(tz.clone(), ty.clone()) } else { included(env, &tz, &ty) };
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::forall(z, Formula::imp(rel, Formula::mem(tz, u.clone()))),
        ),
    )
}

/// `C₂`, subset closure: `∀y. (y ∈ u → ∀z. (z ⊆ y → z ∈ u))`.
fn clause_closed_sub(env: &mut Env, u: &Term) -> Formula {
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let sub = included(env, &tz, &ty);
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::forall(z, Formula::imp(sub, Formula::mem(tz, u.clone()))),
        ),
    )
}

/// `C₃`, power closure: `∀y. (y ∈ u → ∃p. (p ∈ u ∧ ∀z. (z ⊆ y → z ∈ p)))`.
fn clause_closed_pow(env: &mut Env, u: &Term) -> Formula {
    let (y, z, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tz, tp) = (Term::var(y), Term::var(z), Term::var(p));
    let sub = included(env, &tz, &ty);
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::exists(
                p,
                Formula::and(
                    Formula::mem(tp.clone(), u.clone()),
                    Formula::forall(z, Formula::imp(sub, Formula::mem(tz, tp))),
                ),
            ),
        ),
    )
}

/// `C₄`, inaccessibility: `∀y. (y ⊆ u → (y ≈ u ∨ y ∈ u))`.
///
/// `disjunctive` controls whether the `y ≈ u` alternative is present. The
/// variant without it is the **historically inconsistent** statement — at
/// `y := u` the derivable `u ⊆ u` forces `u ∈ u`, which Regularity refutes; see
/// `tarski_regression.rs`, which derives that step. It is built here only so a
/// test can assert the axiom is *not* it.
fn clause_inaccessible(env: &mut Env, u: &Term, disjunctive: bool) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    let sub = included(env, &ty, u);
    let in_u = Formula::mem(ty.clone(), u.clone());
    let rhs = if disjunctive {
        let equi = equinumerous(env, &ty, u);
        Formula::or(equi, in_u)
    } else {
        in_u
    };
    Formula::forall(y, Formula::imp(sub, rhs))
}

/// `∀x ∃u. (x ∈ u ∧ (C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))))`, rebuilt.
fn expected_axiom(env: &mut Env, transitive_is_membership: bool, disjunctive: bool) -> Formula {
    let (x, u) = (env.fresh_var(), env.fresh_var());
    let (tx, tu) = (Term::var(x), Term::var(u));
    let body = Formula::and(
        Formula::mem(tx, tu.clone()),
        Formula::and(
            clause_transitive(env, &tu, transitive_is_membership),
            Formula::and(
                clause_closed_sub(env, &tu),
                Formula::and(clause_closed_pow(env, &tu), clause_inaccessible(env, &tu, disjunctive)),
            ),
        ),
    );
    Formula::forall(x, Formula::exists(u, body))
}

/// Split `φ ∧ ψ`, i.e. `¬(φ → ¬ψ)`, back into its two conjuncts.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (left, not_right) = inner.as_imp()?;
    let (right, fls2) = not_right.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((left, right))
}

// ─────────────────────────────────────────────────────────────────────────────
// The tests.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole formula: five clauses, the bijection spelled out, in the axiom's
/// own nesting.
#[test]
fn ax_tarski_is_exactly_the_reference_statement() {
    let mut env = Env::new();
    let expected = expected_axiom(&mut env, true, true);
    assert_eq!(
        *Thm::ax_tarski(&mut env).concl(),
        expected,
        "ax_tarski is not the formula this test rebuilt; if the axiom was changed deliberately, \
         change this test in the same commit and say why in the message — a clause was once added \
         to this axiom with no test noticing"
    );
}

/// `C₁` relates `z` to `y` by **membership**, not inclusion.
///
/// If it read `z ⊆ y` it would be the very same formula as `C₂`, the axiom
/// would have four distinct clauses again, and universes would stop being
/// transitive. That is not a cosmetic difference: `derived::empty` derives
/// `∃e ∀z. ¬(z ∈ e)` from exactly this clause (Regularity's minimal element of
/// a *transitive* set is empty), and `derived/src/universe.rs` records
/// countermodels showing `⋃`, binary union, products and function spaces are all
/// *refutable* without it. The empty-set axiom was deleted on the strength of
/// this clause, so silently weakening it removes a theorem the development now
/// depends on.
#[test]
fn ax_tarski_transitivity_is_membership_not_inclusion() {
    let mut env = Env::new();
    let collapsed = expected_axiom(&mut env, false, true);
    assert_ne!(
        *Thm::ax_tarski(&mut env).concl(),
        collapsed,
        "ax_tarski's transitivity clause reads `z ⊆ y` — that is a duplicate of the subset-closure \
         clause, leaves universes non-transitive, and breaks derived::empty"
    );
}

/// `C₄` really is the disjunction `y ≈ u ∨ y ∈ u`.
///
/// Dropping the `y ≈ u` disjunct *strengthens* the clause to `∀y ⊆ u. y ∈ u`,
/// and that is the historical **inconsistency**: `tarski_regression.rs` derives
/// `u ⊆ u` from the primitives and instantiates at `y := u` to get `u ∈ u`,
/// which Regularity refutes. That test shows the weakened clause explodes; this
/// one shows the axiom does not contain it.
#[test]
fn ax_tarski_inaccessibility_keeps_the_equinumerosity_disjunct() {
    let mut env = Env::new();
    let weakened = expected_axiom(&mut env, true, false);
    assert_ne!(
        *Thm::ax_tarski(&mut env).concl(),
        weakened,
        "ax_tarski's inaccessibility clause has lost its `y ≈ u` disjunct — at y := u that proves \
         `u ∈ u`, which Regularity refutes; the axiom is then inconsistent"
    );
}

/// The axiom quantifies `∀x ∃u`, in that order, over a **five**-fold
/// conjunction whose first conjunct is the atom `x ∈ u` and whose other four
/// are universally quantified clauses — checked by peeling the real conclusion
/// apart rather than by rebuilding it.
///
/// This is the assertion the old source-grep could not make. A sixth clause, or
/// a fifth silently dropped, fails here with a message naming the count.
#[test]
fn ax_tarski_has_five_clauses() {
    let mut env = Env::new();
    let ax = Thm::ax_tarski(&mut env);

    // ∀x, instantiated at an arbitrary constant.
    let c = Term::apply(env.declare(0), vec![]);
    let inst = Thm::ax_inst(ax.concl().clone(), c).expect("ax_tarski must start with ∀x");
    let (_, body) = inst.concl().as_imp().expect("instantiation is an implication");

    // ∃u, i.e. `(∀u. ¬…) → ⊥`.
    let (all_not, fls) = body.as_imp().expect("the body must be `∃u. …`");
    assert_eq!(fls, Formula::false_(), "the body of ∀x is not an existential");
    let d = env.fresh_var();
    let neg_body = Thm::ax_inst(all_not, Term::var(d))
        .expect("the existential must bind a single u")
        .concl()
        .as_imp()
        .expect("instantiation is an implication")
        .1;
    let (conj, fls2) = neg_body.as_imp().expect("`¬body` is `body → ⊥`");
    assert_eq!(fls2, Formula::false_());

    // `x ∈ u ∧ (C₁ ∧ (C₂ ∧ (C₃ ∧ C₄)))` — four nested `∧`s, five conjuncts.
    let mut rest = conj;
    let mut clauses = Vec::new();
    for _ in 0..4 {
        let (left, right) = split_and(&rest).unwrap_or_else(|| {
            panic!("ax_tarski's body has fewer than five conjuncts — a clause has been dropped")
        });
        clauses.push(left);
        rest = right;
    }
    clauses.push(rest);
    assert_eq!(clauses.len(), 5);

    assert!(clauses[0].as_mem().is_some(), "the first conjunct should be the atom `x ∈ u`");
    // A `∀` is not an `Imp`, so this also rules out a sixth conjunct hiding in
    // the tail: `split_and` could only succeed on an implication.
    for (i, cl) in clauses[1..].iter().enumerate() {
        assert!(cl.is_forall(), "clause C{} should be universally quantified, not a further conjunction", i + 1);
    }
}
