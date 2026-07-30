//! The canonical universe operator `U(x)` — the least Grothendieck universe
//! containing `x`.
//!
//! [`Thm::ax_tarski`] gives *existence* of a universe around every set, never
//! uniqueness, so it cannot be Skolemised by `kernel::thm::define` directly.
//! What is canonical is the **intersection** of all universes containing `x`:
//!
//! ```text
//! U(x) := { z ∈ u₀ : ∀u. (is_universe(u) ∧ x ∈ u) → z ∈ u }
//! ```
//!
//! for any `u₀` Tarski happens to hand over. Two things have to be said about
//! that description before it defines anything.
//!
//! * **It does not depend on `u₀`.** Under the hypothesis that `u₀` *is* a
//!   universe containing `x`, the side condition `z ∈ u₀` is implied by the
//!   body — instantiate the body at `u₀` — so the separated set satisfies
//!   `∀z. (z ∈ s ↔ ∀u. (is_universe(u) ∧ x ∈ u) → z ∈ u)`, in which `u₀` no
//!   longer occurs. That formula is what [`least_universe_existence`] proves,
//!   and it is why the operator is well defined rather than merely definable.
//! * **`∃!` follows from Extensionality**, via
//!   [`crate::define_by_membership`], which is what [`least_universe`] hands to
//!   the kernel.
//!
//! The separation used is [`crate::separation::separation_nonvacuous`], which
//! needs the separated set to be inhabited and in exchange needs no empty set
//! (none is derivable here; see `crate::separation`). The witness is `x`
//! itself: `x ∈ u` holds for *every* universe containing `x`, trivially, which
//! is [`mem_all_universes_self`] and also the lemma [`mem_least_universe`]
//! wants.
//!
//! # What is proved about `U(x)`
//!
//! | statement | where |
//! |---|---|
//! | `⊢ ∀x ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))` | [`least_universe_existence`] |
//! | `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))` | [`least_universe`] |
//! | `⊢ ∀x ∀u₀. ((x ∈ u₀ ∧ is_universe(u₀)) → ∀z. (z ∈ U(x) ↔ (z ∈ u₀ ∧ …)))` | [`least_universe_independent`] |
//! | `⊢ ∀x. x ∈ U(x)` | [`mem_least_universe`] |
//! | `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → 𝒫y ∈ u)` | [`universe_power_closed`] |
//! | `⊢ ∀x. C₂(U(x))` | [`least_universe_closed_sub`] |
//! | `⊢ ∀x. C₃(U(x))` | [`least_universe_closed_pow`] |
//! | `⊢ ∀x. (C₂(U(x)) ∧ C₃(U(x)))` | [`least_universe_closure`] |
//! | `⊢ ∀x. U(x) ∈ U(U(x))` | [`tower_step`] |
//!
//! The **third** clause of `is_universe` — inaccessibility — is *not* proved
//! for `U(x)`; see [`inaccessibility_reduction`], which derives exactly what
//! remains, and the note there for why the remainder is Cantor–Schröder–
//! Bernstein and not proof engineering. Consequently `is_universe(U(x))` itself
//! is **not** available, and neither is the claim that the tower
//! `x ∈ U(x) ∈ U(U(x)) ∈ ⋯` is a tower of *universes* — only that it is a
//! membership chain whose every link satisfies the two closure clauses.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, contrapos, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp, iff_mpr, imp_mono_r, imp_refl, inst_all,
    notnot_elim, syl, uncurry,
};
use crate::separation::hyp_syl;

// ─────────────────────────────────────────────────────────────────────────────
// Local readers and small combinators.
//
// Deliberately private copies rather than imports from `crate::empty`: this
// module should not break when a neighbouring derivation is reshaped. Reading a
// formula apart is untrusted and safe — no `Thm` is produced by any of it.
// ─────────────────────────────────────────────────────────────────────────────

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// Instantiate the body of `∀v. φ` at `t`, as a *formula* operation.
fn open_forall(phi: &Formula, t: &Term) -> Option<Formula> {
    let (_, body) = Thm::ax_inst(phi.clone(), t.clone())?.concl().as_imp()?;
    Some(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (body, fls2) = open_forall(&all_not, t)?.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    Thm::mp(&Thm::mp(&s, t)?, &imp_refl(h))
}

/// `⊢ (a ∧ b) → (b ∧ a)`.
fn and_comm_imp(a: Formula, b: Formula) -> Thm {
    hyp_and(&and_right(a.clone(), b.clone()), &and_left(a, b)).expect("and_comm_imp: shapes line up")
}

// ─────────────────────────────────────────────────────────────────────────────
// The universe predicate.
//
// Each clause is rebuilt exactly as `Thm::ax_tarski` builds it. That is checked
// rather than hoped for: `universe_body` is `debug_assert`ed against the axiom's
// own body in `tarski_at`, and `tests/universe.rs` asserts it independently.
// Alpha-equivalent formulas are syntactically equal here, so rebuilding with
// fresh bound variables reproduces the kernel's formula on the nose.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀y ∈ u. ∀z ⊆ y. z ∈ u` — closure under subsets of members.
pub fn closed_sub(env: &mut Env, u: &Term) -> Formula {
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let sub = kernel::thm::subset(env, tz.clone(), ty.clone());
    Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty, u.clone()),
            Formula::forall(z, Formula::imp(sub, Formula::mem(tz, u.clone()))),
        ),
    )
}

/// `∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p` — power sets stay inside.
pub fn closed_pow(env: &mut Env, u: &Term) -> Formula {
    let (y, z, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tz, tp) = (Term::var(y), Term::var(z), Term::var(p));
    let sub = kernel::thm::subset(env, tz.clone(), ty.clone());
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

/// `∀y ⊆ u. (y ≈ u ∨ y ∈ u)` — inaccessibility.
pub fn inaccessible(env: &mut Env, u: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    let sub = kernel::thm::subset(env, ty.clone(), u.clone());
    let equi = kernel::thm::equinumerous(env, ty.clone(), u.clone());
    Formula::forall(y, Formula::imp(sub, Formula::or(equi, Formula::mem(ty, u.clone()))))
}

/// `is_universe(u)` — the three closure clauses of Tarski's Axiom A, in the
/// axiom's own nesting: `C₂ ∧ (C₃ ∧ C₄)`.
///
/// The axiom's body is `x ∈ u ∧ is_universe(u)`, which is [`universe_body`];
/// splitting it that way is what lets the membership clause be varied (it is
/// what `x` is quantified over) while the universe-hood of `u` is a property of
/// `u` alone.
pub fn is_universe(env: &mut Env, u: &Term) -> Formula {
    let c2 = closed_sub(env, u);
    let c3 = closed_pow(env, u);
    let c4 = inaccessible(env, u);
    Formula::and(c2, Formula::and(c3, c4))
}

/// `x ∈ u ∧ is_universe(u)` — the body of Tarski's axiom, verbatim.
pub fn universe_body(env: &mut Env, x: &Term, u: &Term) -> Formula {
    let univ = is_universe(env, u);
    Formula::and(Formula::mem(x.clone(), u.clone()), univ)
}

/// Tarski's Axiom A at the term `x`: `⊢ ∃u. (x ∈ u ∧ is_universe(u))`, with the
/// existential's bound variable rebuilt as the caller's `u`.
///
/// This is [`Thm::ax_tarski`] instantiated and nothing more; the point of the
/// function is the `debug_assert`, which pins that [`is_universe`] really is
/// what the axiom asserts.
pub fn tarski_at(env: &mut Env, x: &Term, u: FreeVar) -> Option<Thm> {
    let ax = Thm::ax_tarski(env);
    let ex = inst_all(&ax, std::slice::from_ref(x))?;
    debug_assert_eq!(
        *ex.concl(),
        Formula::exists(u, universe_body(env, x, &Term::var(u))),
        "is_universe does not match the clauses of ax_tarski"
    );
    Some(ex)
}

// ─────────────────────────────────────────────────────────────────────────────
// The membership condition of the intersection.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u)` — "`z` lies in every universe
/// containing `x`". This is the membership condition of `U(x)`.
pub fn in_all_universes(env: &mut Env, x: &Term, z: &Term) -> Formula {
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ = is_universe(env, &tu);
    Formula::forall(
        u,
        Formula::imp(
            Formula::and(univ, Formula::mem(x.clone(), tu.clone())),
            Formula::mem(z.clone(), tu),
        ),
    )
}

/// `⊢ ∀u. ((is_universe(u) ∧ x ∈ u) → x ∈ u)`, i.e. `in_all_universes(x, x)`.
///
/// Trivial — it is `and_right` generalised — and it is what makes the whole
/// construction go through without an empty set: it is simultaneously the
/// inhabitation witness [`crate::separation::separation_nonvacuous`] demands
/// and the content of [`mem_least_universe`].
pub fn mem_all_universes_self(env: &mut Env, x: &Term) -> Thm {
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ = is_universe(env, &tu);
    let mem = Formula::mem(x.clone(), tu.clone());
    let out = Thm::gen(u, &and_right(univ, mem));
    debug_assert_eq!(*out.concl(), in_all_universes(env, x, x), "mem_all_universes_self: wrong shape");
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Existence of the intersection, independently of the universe Tarski hands us.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`, at a
/// caller-chosen parameter `x` and element variable `z`.
///
/// Split out from [`least_universe_existence`] so that [`least_universe`] can
/// hand the very same `x` and `z` to [`crate::define_by_membership`].
///
/// **Where `u₀` goes.** Separation is run inside a Tarski universe `u₀` for
/// `x`, so what it produces is `∀z. (z ∈ s ↔ (z ∈ u₀ ∧ φ(z)))`. The extra
/// conjunct is then *deleted*, because under the hypothesis that `u₀` is a
/// universe containing `x` the body `φ(z)` instantiated at `u₀` already gives
/// `z ∈ u₀`. The conclusion therefore does not mention `u₀`, which is exactly
/// the well-definedness obligation, and it is what lets the witness be
/// discharged by [`crate::exists_elim_imp`] at the end.
pub fn least_universe_existence_at(env: &mut Env, x: FreeVar, z: FreeVar) -> Option<Thm> {
    if x == z {
        return None
    }
    let (tx, tz) = (Term::var(x), Term::var(z));
    let phi = in_all_universes(env, &tx, &tz);

    // The goal, with its own witness variable.
    let s = env.fresh_var();
    let ts = Term::var(s);
    let goal_body = Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), ts.clone()), phi.clone()));
    let goal = Formula::exists(s, goal_body.clone());

    // ── Tarski's universe `u₀` around `x` ────────────────────────────────────
    let u0 = env.fresh_var();
    let tu0 = Term::var(u0);
    let ex_u0 = tarski_at(env, &tx, u0)?;
    let h = universe_body(env, &tx, &tu0);
    let univ_u0 = is_universe(env, &tu0);
    let x_in_u0 = Formula::mem(tx.clone(), tu0.clone());
    debug_assert_eq!(h, Formula::and(x_in_u0.clone(), univ_u0.clone()));

    // ── Separation inside `u₀`, at the condition `φ` ──────────────────────────
    let sep = crate::separation::separation_nonvacuous(env, z, &phi)?;
    let sep_u0 = inst_all(&sep, std::slice::from_ref(&tu0))?;

    let w = env.fresh_var();
    let tw = Term::var(w);
    let sep_body = Formula::and(Formula::mem(tw.clone(), tu0.clone()), phi.subst(z, &tw));
    let sep_ante = Formula::exists(w, sep_body.clone());
    let sep_prop = Formula::forall(
        z,
        Formula::iff(
            Formula::mem(tz.clone(), ts.clone()),
            Formula::and(Formula::mem(tz.clone(), tu0.clone()), phi.clone()),
        ),
    );
    debug_assert_eq!(
        *sep_u0.concl(),
        Formula::imp(sep_ante.clone(), Formula::exists(s, sep_prop.clone())),
        "separation_nonvacuous did not instantiate to the expected shape"
    );

    // `x` itself inhabits the condition, so Separation applies without an empty
    // set: `⊢ H → ∃w. (w ∈ u₀ ∧ φ(w))`.
    let h_x_in_u0 = and_left(x_in_u0.clone(), univ_u0.clone());
    let phi_x = mem_all_universes_self(env, &tx);
    debug_assert_eq!(*phi_x.concl(), phi.subst(z, &tx));
    let h_pair = hyp_and(&h_x_in_u0, &a1i(&phi_x, h.clone()))?;
    let h_ante = syl(&h_pair, &exists_intro_imp(w, sep_body, tx.clone())?)?;
    let h_ex_s = syl(&h_ante, &sep_u0)?;

    // ── Delete the `z ∈ u₀` conjunct, under `K := H ∧ P(s)` ───────────────────
    let k = Formula::and(h.clone(), sep_prop.clone());
    let k_h = and_left(h.clone(), sep_prop.clone());
    let k_p = and_right(h.clone(), sep_prop.clone());
    let k_iff = syl(&k_p, &Thm::ax_inst(sep_prop.clone(), tz.clone())?)?;

    // `K → (is_universe(u₀) ∧ x ∈ u₀)`, the antecedent `φ` wants at `u₀`.
    let k_univ = syl(&k_h, &and_comm_imp(x_in_u0.clone(), univ_u0.clone()))?;

    // Forward: drop the conjunct.
    let mem_u0 = Formula::mem(tz.clone(), tu0.clone());
    let k_fwd = hyp_syl(&hyp_iff_mp(&k_iff)?, &a1i(&and_right(mem_u0.clone(), phi.clone()), k.clone()))?;

    // Backward: `φ(z)` at `u₀` restores it.
    let phi_at_u0 = Thm::ax_inst(phi.clone(), tu0.clone())?;
    let l = Formula::and(k.clone(), phi.clone());
    let l_k = and_left(k.clone(), phi.clone());
    let l_phi = and_right(k.clone(), phi.clone());
    let l_imp = hyp_mp(&a1i(&phi_at_u0, l.clone()), &l_phi)?;
    let l_mem = hyp_mp(&l_imp, &syl(&l_k, &k_univ)?)?;
    let k_restore = uncurry(&hyp_and(&l_mem, &l_phi)?)?;
    let k_bwd = hyp_syl(&k_restore, &hyp_iff_mpr(&k_iff)?)?;

    let k_iff2 = hyp_and(&k_fwd, &k_bwd)?;
    let iff_f = Formula::iff(Formula::mem(tz.clone(), ts.clone()), phi.clone());
    debug_assert_eq!(*k_iff2.concl(), Formula::imp(k.clone(), iff_f.clone()));

    // `z` is bound in `P(s)` and absent from `H`, so it generalises.
    let k_all = Thm::mp(&Thm::ax_dist(z, k.clone(), iff_f)?, &Thm::gen(z, &k_iff2))?;
    let k_goal = syl(&k_all, &exists_intro_imp(s, goal_body, ts)?)?;

    // ── Discharge the separated set, then the universe ────────────────────────
    let h_goal_f = Formula::imp(h.clone(), goal.clone());
    let ex_sg = exists_elim_imp(s, &Thm::gen(s, &com12(&uncurry(&k_goal)?)?), &h_goal_f)?;
    let h_goal = hyp_contract(&syl(&h_ex_s, &ex_sg)?)?;
    let ex_ug = exists_elim_imp(u0, &Thm::gen(u0, &h_goal), &goal)?;
    let out = Thm::mp(&ex_ug, &ex_u0)?;
    debug_assert_eq!(*out.concl(), goal, "least_universe_existence_at produced an unexpected shape");
    Some(out)
}

/// `⊢ ∀x ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
///
/// The intersection of all universes containing `x` exists, for every `x`.
pub fn least_universe_existence(env: &mut Env) -> Option<Thm> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    Some(Thm::gen(x, &least_universe_existence_at(env, x, z)?))
}

// ─────────────────────────────────────────────────────────────────────────────
// The operator itself.
// ─────────────────────────────────────────────────────────────────────────────

/// Introduce `U(x)`, the least universe containing `x`, with
/// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
///
/// Existence is [`least_universe_existence_at`]; uniqueness is Extensionality,
/// via [`crate::define_by_membership`]. Nothing is added to the theory —
/// `kernel::thm::define` is conservative — and in particular Tarski's failure
/// to provide uniqueness is repaired by the construction rather than by an
/// appeal to choice.
pub fn least_universe(env: &mut Env) -> Option<(FnSym, Thm)> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let existence = least_universe_existence_at(env, x, z)?;
    let phi = in_all_universes(env, &Term::var(x), &Term::var(z));
    crate::define_by_membership(env, &[x], &existence, z, &phi)
}

/// `⊢ z ∈ U(a) ↔ ∀u. ((is_universe(u) ∧ a ∈ u) → z ∈ u)`, for given terms.
///
/// The characteristic property, ready to use at concrete terms rather than at
/// the defining variables.
pub fn least_universe_mem(lu_ax: &Thm, a: &Term, z: &Term) -> Option<Thm> {
    inst_all(lu_ax, &[a.clone(), z.clone()])
}

/// `⊢ ∀x ∀u₀. ((x ∈ u₀ ∧ is_universe(u₀))
///        → ∀z. (z ∈ U(x) ↔ (z ∈ u₀ ∧ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))))`
///
/// **Independence of `u₀`, as a theorem.** `U(x)` is *the* set the defining
/// description produces, whichever universe Tarski happens to hand over:
/// separating the intersection condition inside any universe `u₀ ∋ x`
/// whatsoever gives `U(x)` back. The extra conjunct is free in both directions
/// — the body instantiated at `u₀` already says `z ∈ u₀`.
///
/// [`least_universe_existence_at`] uses the same observation internally, to
/// keep `u₀` out of the existence statement. This states it in the form a
/// reader would want to check: two different choices of `u₀` describe the same
/// set, namely `U(x)`.
pub fn least_universe_independent(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> Option<Thm> {
    let (x, u0, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tu0, tz) = (Term::var(x), Term::var(u0), Term::var(z));
    let w = Term::apply(lu, vec![tx.clone()]);

    let univ_u0 = is_universe(env, &tu0);
    let x_in_u0 = Formula::mem(tx.clone(), tu0.clone());
    let h = universe_body(env, &tx, &tu0);
    debug_assert_eq!(h, Formula::and(x_in_u0.clone(), univ_u0.clone()));

    let phi_z = in_all_universes(env, &tx, &tz);
    let iff_z = least_universe_mem(lu_ax, &tx, &tz)?;
    let mem_u0 = Formula::mem(tz.clone(), tu0.clone());
    let z_in_w = Formula::mem(tz.clone(), w);

    // `H → (φ(z) → z ∈ u₀)`, the whole content of the deletion.
    let h_a = syl(&imp_refl(h.clone()), &and_comm_imp(x_in_u0, univ_u0))?;
    let h_phi_u0 = syl(&h_a, &com12(&Thm::ax_inst(phi_z.clone(), tu0)?)?)?;

    // Forward, under `L := H ∧ z ∈ U(x)`.
    let l_h = and_left(h.clone(), z_in_w.clone());
    let l_zw = and_right(h.clone(), z_in_w.clone());
    let l_phi = hyp_mp(&syl(&l_h, &a1i(&iff_mp(&iff_z)?, h.clone()))?, &l_zw)?;
    let l_u0 = hyp_mp(&syl(&l_h, &h_phi_u0)?, &l_phi)?;
    let h_fwd = uncurry(&hyp_and(&l_u0, &l_phi)?)?;

    // Backward: drop the conjunct and read the characteristic property back.
    let h_bwd = a1i(&syl(&and_right(mem_u0.clone(), phi_z.clone()), &iff_mpr(&iff_z)?)?, h.clone());

    let iff_f = Formula::iff(z_in_w, Formula::and(mem_u0, phi_z));
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    debug_assert_eq!(*h_iff.concl(), Formula::imp(h.clone(), iff_f.clone()));

    // `z` occurs nowhere in `H`, so it generalises.
    let out = Thm::mp(&Thm::ax_dist(z, h, iff_f)?, &Thm::gen(z, &h_iff))?;
    Some(gen_all(&[x, u0], &out))
}

/// `⊢ ∀x. x ∈ U(x)`.
///
/// Immediate from [`mem_all_universes_self`] and the characteristic property —
/// and worth stating separately, because it is what makes `U(x)` non-empty and
/// hence what made the whole construction possible without an empty set.
pub fn mem_least_universe(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let inst = least_universe_mem(lu_ax, &tx, &tx)?;
    let out = Thm::mp(&crate::iff_mpr(&inst)?, &mem_all_universes_self(env, &tx))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(tx.clone(), Term::apply(lu, vec![tx])),
        "mem_least_universe produced an unexpected shape"
    );
    Some(Thm::gen(x, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Closure clauses, for an arbitrary universe and then for `U(x)`.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ is_universe(u) → C₂(u)`, `⊢ is_universe(u) → C₃(u)`, and the clauses
/// themselves, for a given `u`.
///
/// The predicate is `C₂ ∧ (C₃ ∧ C₄)`, so projecting is two `and_left`s and an
/// `and_right`; doing it in one place keeps the nesting in one place too.
fn universe_clauses(env: &mut Env, u: &Term) -> Option<(Formula, Formula, Thm, Thm)> {
    let univ = is_universe(env, u);
    let (c2, rest) = split_and(&univ)?;
    let (c3, c4) = split_and(&rest)?;
    let to_c2 = and_left(c2.clone(), rest.clone());
    let to_c3 = syl(&and_right(c2.clone(), rest), &and_left(c3.clone(), c4))?;
    Some((c2, c3, to_c2, to_c3))
}

/// `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → 𝒫y ∈ u)` — a universe is closed under
/// power sets.
///
/// Neither closure clause does this alone. `C₃` puts *some* `p ∈ u` above every
/// subset of `y`, so `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the member
/// `p`, back into `u`. Inaccessibility is not needed, so the equinumerosity
/// formula never has to be unpacked.
///
/// (`crate::empty` proves the same thing in the shape its own decomposition of
/// Tarski's body wants. Restated here against [`is_universe`], which is the
/// form `U(x)` needs and the form that survives that module changing.)
pub fn universe_power_closed(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> Option<Thm> {
    let (u, y) = (env.fresh_var(), env.fresh_var());
    let (tu, ty) = (Term::var(u), Term::var(y));
    let univ_u = is_universe(env, &tu);
    let (c2_u, c3_u, to_c2, to_c3) = universe_clauses(env, &tu)?;

    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let goal = Formula::mem(pow_y.clone(), tu.clone());

    // `K := is_universe(u) ∧ y ∈ u`.
    let k = Formula::and(univ_u.clone(), y_in_u.clone());
    let k_univ = and_left(univ_u.clone(), y_in_u.clone());
    let k_y = and_right(univ_u, y_in_u);

    // `C₃` at `y`, with its witness `p` and the clause it satisfies read off.
    let c3_at_y = Thm::ax_inst(c3_u, ty.clone())?;
    let (_, c3_body) = c3_at_y.concl().as_imp()?;
    let (_, ex_p) = c3_body.as_imp()?;
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    debug_assert_eq!(ex_p, Formula::exists(p, bp.clone()), "C₃'s ∃p did not reopen");
    let (p_in_u, all_sub_p) = split_and(&bp)?;
    let k_ex_p = hyp_mp(&syl(&k_univ, &syl(&to_c3, &c3_at_y)?)?, &k_y)?;

    // ── Under `L := K ∧ (p ∈ u ∧ ∀z ⊆ y. z ∈ p)` ─────────────────────────────
    let l = Formula::and(k.clone(), bp.clone());
    let l_k = and_left(k.clone(), bp.clone());
    let l_bp = and_right(k.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all = syl(&l_bp, &and_right(p_in_u.clone(), all_sub_p.clone()))?;

    // `L → 𝒫y ⊆ p`: a member of `𝒫y` is a subset of `y`, and those are in `p`.
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l_v_sub_p = syl(&l_all, &Thm::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_step = hyp_syl(&a1i(&iff_mp(&pw_at_v)?, l.clone()), &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = Thm::mp(&Thm::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l, kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // `C₂` at `p` and then at `𝒫y`: a subset of the member `p` is a member.
    let c2_at_p = Thm::ax_inst(c2_u, tp)?;
    let (_, c2_body) = c2_at_p.concl().as_imp()?;
    let (_, all_sub_u) = c2_body.as_imp()?;
    let c2_pw = syl(&c2_at_p, &imp_mono_r(&Thm::ax_inst(all_sub_u, pow_y)?, p_in_u)?)?;
    let l_c2 = syl(&l_k, &syl(&k_univ, &to_c2)?)?;
    let l_goal = hyp_mp(&hyp_mp(&syl(&l_c2, &c2_pw)?, &l_p_in_u)?, &l_sub)?;

    // Discharge the witness `p`, then contract the duplicated `K`.
    let k_goal_f = Formula::imp(k.clone(), goal.clone());
    let ex_kg = exists_elim_imp(p, &Thm::gen(p, &com12(&uncurry(&l_goal)?)?), &k_goal_f)?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;
    debug_assert_eq!(*k_goal.concl(), Formula::imp(k, goal), "universe_power_closed: wrong shape");
    Some(gen_all(&[u, y], &k_goal))
}

/// `⊢ t ∈ U(x) → ((is_universe(u) ∧ x ∈ u) → t ∈ u)`.
///
/// Membership in the intersection transfers into any particular universe
/// containing `x`. Half of the characteristic property, and the half both
/// closure proofs use over and over.
pub fn least_universe_transfer(
    env: &mut Env,
    lu_ax: &Thm,
    x: &Term,
    t: &Term,
    u: &Term,
) -> Option<Thm> {
    let phi_t = in_all_universes(env, x, t);
    let iff_t = least_universe_mem(lu_ax, x, t)?;
    // The instance must be the characteristic property *for this `φ`* — a
    // caller passing an unrelated theorem gets a rejection, not a theorem.
    let (fwd, _) = split_and(iff_t.concl())?;
    if fwd.as_imp()?.1 != phi_t {
        return None
    }
    syl(&iff_mp(&iff_t)?, &Thm::ax_inst(phi_t, u.clone())?)
}

/// `⊢ ∀x. C₂(U(x))` — the intersection of all universes containing `x` is
/// closed under subsets of its members.
///
/// Pointwise: if `y ∈ U(x)` and `z ⊆ y`, then for each universe `u` containing
/// `x` we have `y ∈ u`, and `C₂(u)` puts `z` in `u` as well. Being in every
/// such `u` is exactly being in `U(x)`.
pub fn least_universe_closed_sub(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let sub_zy = kernel::thm::subset(env, tz.clone(), ty.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());

    // `H := y ∈ U(x) ∧ z ⊆ y`.
    let h = Formula::and(y_in_w.clone(), sub_zy.clone());
    let h_y = and_left(y_in_w.clone(), sub_zy.clone());
    let h_sub = and_right(y_in_w.clone(), sub_zy);

    // A universe `u` containing `x`, held fixed until the very end.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let a = Formula::and(univ_u.clone(), Formula::mem(tx.clone(), tu.clone()));
    let (c2_u, _, to_c2, _) = universe_clauses(env, &tu)?;

    // `N := H ∧ A`.
    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());

    let transfer = least_universe_transfer(env, lu_ax, &tx, &ty, &tu)?;
    let n_y_in_w = syl(&n_h, &h_y)?;
    let n_y_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_y_in_w)?, &n_a)?;

    // `C₂(u)` at `y`, then its inner `∀z` at `z`.
    let c2_at_y = Thm::ax_inst(c2_u, ty.clone())?;
    let (_, c2_body) = c2_at_y.concl().as_imp()?;
    let (_, all_sub_u) = c2_body.as_imp()?;
    let n_univ = syl(&n_a, &and_left(univ_u, Formula::mem(tx.clone(), tu.clone())))?;
    let n_c2 = syl(&n_univ, &to_c2)?;
    let n_all = hyp_mp(&syl(&n_c2, &c2_at_y)?, &n_y_in_u)?;
    let n_z_in_u =
        hyp_mp(&syl(&n_all, &Thm::ax_inst(all_sub_u, tz.clone())?)?, &syl(&n_h, &h_sub)?)?;

    // Generalise over `u`: it occurs nowhere in `H`.
    let h_a_z = uncurry(&n_z_in_u)?;
    let z_in_u = Formula::mem(tz.clone(), tu);
    let h_phi = Thm::mp(&Thm::ax_dist(u, h.clone(), Formula::imp(a, z_in_u))?, &Thm::gen(u, &h_a_z))?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h, in_all_universes(env, &tx, &tz)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let h_z_in_w = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tx, &tz)?)?)?;

    // Pull the two hypotheses back apart and quantify.
    let z_in_w = Formula::mem(tz, w.clone());
    let y_sub_z = uncurry(&h_z_in_w)?;
    let (_, inner) = y_sub_z.concl().as_imp()?;
    let (sub_f, _) = inner.as_imp()?;
    let out = Thm::gen(
        y,
        &Thm::mp(
            &Thm::ax_dist(z, y_in_w.clone(), Formula::imp(sub_f, z_in_w))?,
            &Thm::gen(z, &y_sub_z),
        )?,
    );
    debug_assert_eq!(*out.concl(), closed_sub(env, &w), "least_universe_closed_sub: wrong shape");
    Some(Thm::gen(x, &out))
}

/// `⊢ ∀x. C₃(U(x))` — the intersection of all universes containing `x` keeps
/// power sets inside.
///
/// The witness the clause asks for is `𝒫y` itself: it holds every subset of
/// `y` by definition, and it is in `U(x)` because every universe containing `x`
/// contains `y` and hence, by [`universe_power_closed`], contains `𝒫y`.
pub fn least_universe_closed_pow(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<Thm> {
    let upc = universe_power_closed(env, pow, pow_ax)?;

    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let h = Formula::mem(ty.clone(), w.clone());

    // A universe `u` containing `x`.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), x_in_u.clone());

    // `N := (y ∈ U(x)) ∧ A`.
    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());

    let transfer = least_universe_transfer(env, lu_ax, &tx, &ty, &tu)?;
    let n_y_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_h)?, &n_a)?;
    let n_univ = syl(&n_a, &and_left(univ_u, x_in_u))?;
    let upc_at = inst_all(&upc, &[tu.clone(), ty.clone()])?;
    let n_pow_in_u = hyp_mp(&a1i(&upc_at, n), &hyp_and(&n_univ, &n_y_in_u)?)?;

    // Generalise over `u`, then read the result back as membership in `U(x)`.
    let pow_in_u = Formula::mem(pow_y.clone(), tu);
    let h_phi = Thm::mp(
        &Thm::ax_dist(u, h.clone(), Formula::imp(a, pow_in_u))?,
        &Thm::gen(u, &uncurry(&n_pow_in_u)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tx, &pow_y)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let h_pow_in_w = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tx, &pow_y)?)?)?;

    // `⊢ ∀z. (z ⊆ y → z ∈ 𝒫y)`, the other half of what the clause demands.
    let sub_zy = kernel::thm::subset(env, tz.clone(), ty.clone());
    let all_sub = Thm::gen(z, &iff_mpr(&inst_all(pow_ax, &[ty.clone(), tz.clone()])?)?);
    debug_assert_eq!(
        *all_sub.concl(),
        Formula::forall(z, Formula::imp(sub_zy.clone(), Formula::mem(tz.clone(), pow_y.clone())))
    );

    let p = env.fresh_var();
    let tp = Term::var(p);
    let goal_body = Formula::and(
        Formula::mem(tp.clone(), w.clone()),
        Formula::forall(z, Formula::imp(sub_zy, Formula::mem(tz, tp))),
    );
    let h_pair = hyp_and(&h_pow_in_w, &a1i(&all_sub, h))?;
    let out = Thm::gen(y, &syl(&h_pair, &exists_intro_imp(p, goal_body, pow_y)?)?);
    debug_assert_eq!(*out.concl(), closed_pow(env, &w), "least_universe_closed_pow: wrong shape");
    Some(Thm::gen(x, &out))
}

/// `⊢ ∀x. (C₂(U(x)) ∧ C₃(U(x)))` — both closure clauses at once.
///
/// This is `is_universe(U(x))` minus its third conjunct: the predicate is
/// `C₂ ∧ (C₃ ∧ C₄)`, and what is proved here is `C₂ ∧ C₃`. See
/// [`inaccessibility_reduction`] for what stands between this and the whole
/// predicate.
pub fn least_universe_closure(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<Thm> {
    let c2 = least_universe_closed_sub(env, lu, lu_ax)?;
    let c3 = least_universe_closed_pow(env, lu, lu_ax, pow, pow_ax)?;
    let x = env.fresh_var();
    let tx = Term::var(x);
    let both = crate::and_intro(
        &inst_all(&c2, std::slice::from_ref(&tx))?,
        &inst_all(&c3, std::slice::from_ref(&tx))?,
    );
    let w = Term::apply(lu, vec![tx]);
    debug_assert_eq!(
        *both.concl(),
        Formula::and(closed_sub(env, &w), closed_pow(env, &w)),
        "least_universe_closure: wrong shape"
    );
    Some(Thm::gen(x, &both))
}

// ─────────────────────────────────────────────────────────────────────────────
// Inaccessibility: the clause that is not proved, and what it reduces to.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀x ∀y. ((y ⊆ U(x) ∧ ¬(y ∈ U(x)))
///        → ∃u. ((is_universe(u) ∧ x ∈ u) ∧ (y ≈ u ∧ ¬(y ∈ u))))`
///
/// **The third clause of [`is_universe`] is not proved for `U(x)`, and this is
/// exactly what remains.** Inaccessibility for `U(x)` asks that every
/// `y ⊆ U(x)` be either a member of `U(x)` or equinumerous with it. Suppose it
/// is not a member. Then — this theorem — some universe `u ∋ x` misses `y`, and
/// since `y ⊆ U(x) ⊆ u`, that `u`'s own inaccessibility forces `y ≈ u`.
///
/// So the goal `y ≈ U(x)` is available *for the wrong set*: we have a bijection
/// `y → u`, and `U(x) ⊆ u` with `y ⊆ U(x)`. Composing the inclusions gives
/// injections `y ↪ U(x)` and `U(x) ↪ u ≈ y`, and concluding `y ≈ U(x)` from
/// injections both ways is **Cantor–Schröder–Bernstein**. That is a genuine
/// piece of mathematics — the back-and-forth construction needs the recursion
/// theorem, hence `ω` and function graphs — and not a matter of assembling a
/// few more combinators, which is why the clause is left open here rather than
/// half-attempted. Note also that `equinumerous` is a spelled-out first-order
/// formula about a bijection *set*, so every step of that argument would have
/// to be done at the level of explicit graphs (`crate::funcs`).
///
/// Everything up to that point is proved here, and nothing is assumed.
pub fn inaccessibility_reduction(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let y = env.fresh_var();
    let ty = Term::var(y);
    let sub_y_w = kernel::thm::subset(env, ty.clone(), w.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());
    let h = Formula::and(sub_y_w.clone(), Formula::not(y_in_w.clone()));

    // The universe variable, and the clauses of a universe containing `x`.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), x_in_u.clone());
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let (c2_u, rest) = split_and(&univ_u)?;
    let (c3_u, c4_u) = split_and(&rest)?;
    let to_c4 = syl(&and_right(c2_u, rest.clone()), &and_right(c3_u, c4_u.clone()))?;

    // ── `H → ∃u. (A(u) ∧ ¬(y ∈ u))` ───────────────────────────────────────────
    //
    // Failing to be in the intersection means some universe misses it. `∃` is
    // `¬∀¬`, so this is the propositional `¬(A ∧ ¬B) → (A → B)` pushed under
    // the quantifier and contraposed.
    let taut = syl(
        &notnot_elim(Formula::imp(a.clone(), Formula::not(Formula::not(y_in_u.clone())))),
        &imp_mono_r(&notnot_elim(y_in_u.clone()), a.clone())?,
    )?;
    let witness_body = Formula::and(a.clone(), Formula::not(y_in_u.clone()));
    debug_assert_eq!(
        *taut.concl(),
        Formula::imp(Formula::not(witness_body.clone()), Formula::imp(a.clone(), y_in_u.clone()))
    );
    let not_phi_to_ex = contrapos(&crate::forall_mono(u, &Thm::gen(u, &taut))?)?;
    let phi_y = in_all_universes(env, &tx, &ty);
    debug_assert_eq!(
        *not_phi_to_ex.concl(),
        Formula::imp(Formula::not(phi_y.clone()), Formula::exists(u, witness_body.clone())),
        "the ¬∀ → ∃ step did not produce the expected shapes"
    );

    let h_not_in_w = and_right(sub_y_w.clone(), Formula::not(y_in_w.clone()));
    let h_not_phi = syl(&h_not_in_w, &contrapos(&iff_mpr(&least_universe_mem(lu_ax, &tx, &ty)?)?)?)?;
    let h_ex = syl(&h_not_phi, &not_phi_to_ex)?;

    // ── Under `M := H ∧ (A(u) ∧ ¬(y ∈ u))` ────────────────────────────────────
    let m = Formula::and(h.clone(), witness_body.clone());
    let m_h = and_left(h.clone(), witness_body.clone());
    let m_wit = and_right(h.clone(), witness_body.clone());
    let m_a = syl(&m_wit, &and_left(a.clone(), Formula::not(y_in_u.clone())))?;
    let m_not_y_in_u = syl(&m_wit, &and_right(a.clone(), Formula::not(y_in_u.clone())))?;

    // `M → y ⊆ u`, by composing `y ⊆ U(x)` with `U(x) ⊆ u`.
    let z = env.fresh_var();
    let tz = Term::var(z);
    let m_sub_w = syl(&m_h, &and_left(sub_y_w.clone(), Formula::not(y_in_w.clone())))?;
    let m_z_in_w = syl(&m_sub_w, &Thm::ax_inst(sub_y_w, tz.clone())?)?;
    let transfer_z = com12(&least_universe_transfer(env, lu_ax, &tx, &tz, &tu)?)?;
    let m_w_to_u = hyp_mp(&a1i(&transfer_z, m.clone()), &m_a)?;
    let m_step = hyp_syl(&m_z_in_w, &m_w_to_u)?;
    let m_sub_u = Thm::mp(
        &Thm::ax_dist(
            z,
            m.clone(),
            Formula::imp(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz, tu.clone())),
        )?,
        &Thm::gen(z, &m_step),
    )?;
    debug_assert_eq!(
        *m_sub_u.concl(),
        Formula::imp(m.clone(), kernel::thm::subset(env, ty.clone(), tu.clone())),
        "the composed inclusion is not the subset formula C₄ expects"
    );

    // `C₄(u)` at `y`, with `¬(y ∈ u)` selecting the equinumerosity disjunct.
    let c4_at_y = Thm::ax_inst(c4_u, ty.clone())?;
    let m_disj = hyp_mp(&syl(&syl(&m_a, &and_left(univ_u, x_in_u))?, &syl(&to_c4, &c4_at_y)?)?, &m_sub_u)?;
    let equi = kernel::thm::equinumerous(env, ty.clone(), tu.clone());
    debug_assert_eq!(
        *m_disj.concl(),
        Formula::imp(m.clone(), Formula::or(equi.clone(), y_in_u.clone())),
        "C₄ did not instantiate to the expected disjunction"
    );
    // `equi ∨ y ∈ u` is `¬equi → y ∈ u`; with `¬(y ∈ u)` that is `¬¬equi`.
    let m_nn = hyp_syl(&m_disj, &m_not_y_in_u)?;
    let m_equi = syl(&m_nn, &notnot_elim(equi.clone()))?;

    // ── Package the witness and discharge it ──────────────────────────────────
    let goal_body = Formula::and(a, Formula::and(equi, Formula::not(y_in_u)));
    let goal = Formula::exists(u, goal_body.clone());
    let m_goal = syl(
        &hyp_and(&m_a, &hyp_and(&m_equi, &m_not_y_in_u)?)?,
        &exists_intro_imp(u, goal_body, tu)?,
    )?;
    let h_goal_f = Formula::imp(h.clone(), goal.clone());
    let h_goal = hyp_contract(&syl(
        &h_ex,
        &exists_elim_imp(u, &Thm::gen(u, &com12(&uncurry(&m_goal)?)?), &h_goal_f)?,
    )?)?;
    debug_assert_eq!(*h_goal.concl(), Formula::imp(h, goal), "inaccessibility_reduction: wrong shape");
    Some(gen_all(&[x, y], &h_goal))
}

/// `⊢ ∀x. U(x) ∈ U(U(x))` — the step that stacks the tower `U₀ ∈ U₁ ∈ ⋯`.
///
/// A one-line corollary: [`mem_least_universe`] at the term `U(x)`. What it
/// does *not* say is that the tower is strictly increasing in universe-hood —
/// that needs `is_universe(U(x))`, whose third clause is open (see
/// [`inaccessibility_reduction`]).
pub fn tower_step(env: &mut Env, lu: FnSym, mem_lu: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let ux = Term::apply(lu, vec![tx]);
    let inst = inst_all(mem_lu, std::slice::from_ref(&ux))?;
    debug_assert_eq!(
        *inst.concl(),
        Formula::mem(ux.clone(), Term::apply(lu, vec![ux])),
        "tower_step produced an unexpected shape"
    );
    Some(Thm::gen(x, &inst))
}
