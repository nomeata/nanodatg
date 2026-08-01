//! **A non-indexed class-(S) carrier is a conditional singleton** — the general
//! `[⋁ᵢ ∃y⃗ᵢ. ⋀ⱼ yⱼ ∈ βᵢⱼ]` clause, derived once here so that no consumer has
//! to assemble a disjunction of existentials for itself.
//!
//! # What this closes
//!
//! [`super::le::LeCarrier`] carves `A_φ(p⃗) = {q ∈ Idx(p⃗) : φ(q)}` for a
//! subsingleton family. At `ni = 0` — [`super::index`]'s header says why that
//! case exists at all — the index space is the one-point set, so `A_φ` is a
//! subset of `1`, which is to say it is a **proposition**. Its truth value is
//! φ with the index equation discharged, and that value is what a consumer
//! actually wants:
//!
//! ```text
//! ψ := ⋁ᵢ ∃y⃗ᵢ. ( ⋀ⱼ yⱼ ∈ βᵢⱼ(p⃗, y⃗<ⱼ)  ∧  • = • )
//! ```
//!
//! — "some constructor's fields can all be inhabited". For `And a b` that is
//! `∃y₀ ∃y₁. (y₀ ∈ a ∧ (y₁ ∈ b ∧ • = •))`, for `PUnit` it is `• = •`, and for
//! a declaration with no constructors it is `⊥`. Read as truth values in `U₀`
//! those are conjunction, truth and falsity — which is exactly what the three
//! direct clauses a checker would otherwise hand-write say, and this file says
//! it once for every class-(S) declaration instead of three times for three.
//!
//! # Why `• = •` is a conjunct and not an oversight
//!
//! ψ is φ's matrix with the subject variable substituted by `•`, **not** φ's
//! matrix with the index equation deleted. Deleting it would be the more
//! obvious reading and it does not typecheck: at a nullary constructor
//! (`PUnit.unit`) the remaining conjunction is *empty*, and this kernel has no
//! `⊤` to spell an empty conjunction with. Substituting instead leaves
//! `• = •` standing in that slot, which is a formula, is provable by
//! reflexivity, and costs one `Thm::eq_refl`. The two readings are equivalent;
//! only one of them exists.
//!
//! The substitution is also the *whole* derivation of the bridge, because
//! `q ∈ 1 → q = •` ([`crate::sums::unit_eta`]) makes `q` and `•`
//! interchangeable inside the Separation, in both directions.
//!
//! # Interface
//!
//! With `p⃗` the declaration's own parameter variables:
//!
//! ```text
//! ψ                                                        [LeProp::psi]
//! A_φ(p⃗)                                                   [LeProp::set]
//! ⊢ ∀p⃗ ∀z. (z ∈ A_φ(p⃗) ↔ (z ∈ 1 ∧ ψ))                      [LeProp::chi]
//! ⊢ ∀z. (z ∈ A_φ(p⃗) ↔ (z ∈ 1 ∧ ψ))                         [LeProp::chi_at_params]
//! ⊢ ψ → • ∈ A_φ(p⃗)                                         [LeProp::intro]
//! ⊢ • ∈ A_φ(p⃗) → ψ                                         [LeProp::elim]
//! ⊢ ∀x ∀y. ((x ∈ A_φ(p⃗) ∧ y ∈ A_φ(p⃗)) → x = y)             [LeProp::subsingleton]
//! ⊢ ψ → A_φ(p⃗) = 1                                         [LeProp::true_]
//! ⊢ ¬ψ → A_φ(p⃗) = 0                                        [LeProp::false_]
//! ```
//!
//! [`LeProp::chi_at_params`] is precisely the characteristic theorem
//! [`crate::prop::conditional_singleton`] hands back, at `c := A_φ(p⃗)` and
//! `φ := ψ`, so **every** lemma in [`crate::prop`] applies to it unchanged —
//! the five below are the ones this file bothers to pre-compose, and a caller
//! wanting `⊢ A_φ(p⃗) ∈ U₀` passes the same three arguments to
//! [`crate::tower::Tower::cond_in_u0`]. The symbol `A_φ` is **not**
//! re-introduced: this is the same set [`super::le::LeCarrier`] built, described
//! a second way, not a second Separation over `1`.
//!
//! # Where the `acc` goes
//!
//! For a **non-recursive** declaration — which, as [`super::le`]'s census
//! records, is every class-(S) declaration in this repository that is
//! representable as an [`IndexedDeclSpec`] at all — the relation is empty, so
//! [`super::le::LeCarrier::degenerate`] is `⊢ ∀p⃗. acc(A_φ(p⃗), R(p⃗)) = A_φ(p⃗)`
//! and the carrier *is* `A_φ`. Composed with this file, a non-recursive
//! non-indexed subsingleton's whole interpretation is one conditional
//! singleton and the `acc` never has to be unfolded. [`LeProp::build`]
//! therefore does not require `degenerate` and does not consult it: the bridge
//! is about `A_φ`, and whether the carrier equals `A_φ` is a separate
//! question with a separate theorem.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced and no Separation is performed. One instance of
//! [`super::index::IndexSpace::point`], two [`Thm::eq_leibniz`]s, one
//! [`crate::sums::unit_eta`], and the [`crate::prop`] lemmas — which are
//! themselves one Separation's worth, already spent. Every theorem read out of
//! `lc` is pinned against one rebuilt here, so a [`LeCarrier`] from a different
//! [`Machine`] is refused rather than silently described.

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::machine::Machine;
use crate::prop::{cond_elim, cond_false, cond_intro, cond_subsingleton, cond_true};
use crate::{
    and_intro, and_left, and_right, disj_of, eq_symm, eq_symm_imp, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, inst_all, syl,
};

use super::index::IndexSpace;
use super::le::{LeCarrier, LeSpec};

/// A non-indexed class-(S) carrier, read as a conditional singleton.
pub struct LeProp {
    /// ψ — the class-(S) truth value, free of the subject variable.
    pub psi: Formula,
    /// `A_φ(p⃗)`, at the declaration's own parameters. Repeated from
    /// [`LeCarrier::a_phi`] so a caller compares the term the theorems below
    /// are about rather than assuming it.
    pub set: Term,
    /// `⊢ ∀p⃗ ∀z. (z ∈ A_φ(p⃗) ↔ (z ∈ 1 ∧ ψ))` — the same shape
    /// [`LeCarrier::phi_ax`] has, with `Idx(p⃗)` collapsed to `1` and the index
    /// equation discharged.
    pub chi: Thm,
    /// [`LeProp::chi`] with the parameters instantiated at the declaration's
    /// own variables — the form [`crate::prop`]'s lemmas take.
    pub chi_at_params: Thm,
    /// `⊢ ψ → • ∈ A_φ(p⃗)`.
    pub intro: Thm,
    /// `⊢ • ∈ A_φ(p⃗) → ψ`.
    pub elim: Thm,
    /// `⊢ ∀x ∀y. ((x ∈ A_φ(p⃗) ∧ y ∈ A_φ(p⃗)) → x = y)` — proof irrelevance,
    /// and it holds whatever ψ is.
    pub subsingleton: Thm,
    /// `⊢ ψ → A_φ(p⃗) = 1`.
    pub true_: Thm,
    /// `⊢ ¬ψ → A_φ(p⃗) = 0`.
    pub false_: Thm,
}

impl LeProp {
    /// Read a non-indexed class-(S) carrier as a conditional singleton.
    ///
    /// `ix` and `lc` must be the index space and carrier of `spec` at
    /// `params`, and `spec` must have **no indices** — with an index there is
    /// no collapse to make, `A_φ` is a subset of a genuine `Σ` nest rather than
    /// of `1`, and every lemma below would be false.
    ///
    /// `None` when `spec` has indices, when `ix` is not `spec`'s index space
    /// (its [`IndexSpace::point`] must be present and must be about `lc`'s own
    /// `Idx(p⃗)`), or when `lc`'s recorded φ-disjuncts do not reproduce the
    /// matrix its own [`LeCarrier::phi_ax`] states — which is the check that a
    /// carrier from another `Machine` fails.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        spec: &LeSpec,
        ix: &IndexSpace,
        lc: &LeCarrier,
        params: &[kernel::FreeVar],
    ) -> Option<LeProp> {
        if !spec.well_formed()
            || spec.num_indices() != 0
            || ix.num_indices() != 0
            || params.len() != spec.params()
            || lc.phi_disjuncts.len() != spec.len()
        {
            return None
        }
        let s = &mach.wt.sums;
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let one = s.unit();
        let pt = s.point();

        let qv = lc.phi_subject;
        let tq = Term::var(qv);
        let phi = disj_of(&lc.phi_disjuncts).unwrap_or_else(Formula::false_);
        // ψ is φ at the one point the index space has. `subst` is capture-free,
        // and `•` is closed, so nothing under the `∃y⃗ᵢ` binders moves.
        let psi = phi.subst(qv, &pt);

        // ── `A_φ(p⃗)`'s own characteristic theorem, at the subject variable ──
        //
        // Instantiating at `q` itself is what makes the conclusion compare
        // *equal* to the matrix `lc` recorded: `phi_ax`'s binder is de Bruijn,
        // so any other variable would give an alpha-variant that no `==` below
        // would accept.
        let mut aq = ps.clone();
        aq.push(tq.clone());
        let at = inst_all(&lc.phi_ax, &aq)?;
        let mem_idx = Formula::mem(tq.clone(), ix.idx.clone());
        let mem_one = Formula::mem(tq.clone(), one.clone());
        let mem_a = Formula::mem(tq.clone(), lc.a_phi.clone());
        if *at.concl() != Formula::iff(mem_a.clone(), Formula::and(mem_idx.clone(), phi.clone())) {
            return None
        }

        // ── `Idx(p⃗) = 1`, the collapse the whole file rests on ──────────────
        let idx_is_one = inst_all(ix.point()?, &ps)?;
        if !crate::establishes(&idx_is_one, &Formula::eq(ix.idx.clone(), one.clone())) {
            return None
        }
        let hole = env.fresh_var();
        let idx_to_one = Thm::mp(
            &Thm::eq_leibniz(
                ix.idx.clone(),
                one.clone(),
                hole,
                Formula::mem(tq.clone(), Term::var(hole)),
            ),
            &idx_is_one,
        )?;
        let one_to_idx = Thm::mp(
            &Thm::eq_leibniz(
                one.clone(),
                ix.idx.clone(),
                hole,
                Formula::mem(tq.clone(), Term::var(hole)),
            ),
            &eq_symm(env, &idx_is_one)?,
        )?;

        // `q ∈ 1 → q = •`, and the two Leibniz steps that trade φ for ψ.
        let one_to_pt = inst_all(&s.unit_eta, std::slice::from_ref(&tq))?;
        let phi_to_psi = Thm::eq_leibniz(tq.clone(), pt.clone(), qv, phi.clone());
        let psi_to_phi = Thm::eq_leibniz(pt.clone(), tq.clone(), qv, phi.clone());
        if *phi_to_psi.concl()
            != Formula::imp(
                Formula::eq(tq.clone(), pt.clone()),
                Formula::imp(phi.clone(), psi.clone()),
            )
            || *psi_to_phi.concl()
                != Formula::imp(
                    Formula::eq(pt.clone(), tq.clone()),
                    Formula::imp(psi.clone(), phi.clone()),
                )
        {
            return None
        }

        // ── forward: `q ∈ A_φ → (q ∈ 1 ∧ ψ)` ────────────────────────────────
        // Under `H := q ∈ Idx ∧ φ`.
        let h_one = syl(&and_left(mem_idx.clone(), phi.clone()), &idx_to_one)?;
        let h_pt = syl(&h_one, &one_to_pt)?;
        let h_psi = hyp_mp(
            &syl(&h_pt, &phi_to_psi)?,
            &and_right(mem_idx.clone(), phi.clone()),
        )?;
        let fwd = syl(&iff_mp(&at)?, &hyp_and(&h_one, &h_psi)?)?;

        // ── backward: `(q ∈ 1 ∧ ψ) → q ∈ A_φ` ───────────────────────────────
        // Under `K := q ∈ 1 ∧ ψ`.
        let k_one = and_left(mem_one.clone(), psi.clone());
        let k_pt = syl(&k_one, &one_to_pt)?;
        let k_sym = syl(&k_pt, &eq_symm_imp(env, tq.clone(), pt.clone()))?;
        let k_phi = hyp_mp(&syl(&k_sym, &psi_to_phi)?, &and_right(mem_one.clone(), psi.clone()))?;
        let k_idx = syl(&k_one, &one_to_idx)?;
        let bwd = syl(&hyp_and(&k_idx, &k_phi)?, &iff_mpr(&at)?)?;

        let body = and_intro(&fwd, &bwd);
        let want = Formula::iff(mem_a, Formula::and(mem_one, psi.clone()));
        if !crate::establishes(&body, &want) {
            return None
        }
        let chi_at_params = Thm::gen(qv, &body);
        let chi = gen_all(params, &chi_at_params);

        // ── and the `prop` lemmas, at this set and this truth value ─────────
        let set = lc.a_phi.clone();
        let intro = cond_intro(s, &psi, &set, &chi_at_params)?;
        let elim = cond_elim(s, &psi, &set, &chi_at_params)?;
        let subsingleton = cond_subsingleton(env, s, &psi, &set, &chi_at_params)?;
        let true_ = cond_true(env, s, &psi, &set, &chi_at_params)?;
        let false_ = cond_false(env, s, &psi, &set, &chi_at_params)?;

        let out = LeProp {
            psi,
            set,
            chi,
            chi_at_params,
            intro,
            elim,
            subsingleton,
            true_,
            false_,
        };
        out.all_unconditional().then_some(out)
    }

    /// Whether every theorem here rests on nothing.
    ///
    /// A `Γ ⊢` has the conclusion the real theorem has and rides through `mp`
    /// with `Γ` intact, so it would arrive at statements this module advertises
    /// without one. Checked on the way out, once, over all seven.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(&[
            &self.chi,
            &self.chi_at_params,
            &self.intro,
            &self.elim,
            &self.subsingleton,
            &self.true_,
            &self.false_,
        ])
    }
}
