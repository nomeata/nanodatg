//! **The class-(P) recursor, non-indexed** — `‖ind(p⃗)‖`'s elimination rule,
//! one theorem per declaration.
//!
//! # Interface
//!
//! Writing `‖ind(p⃗)‖` for [`TruncCarrier::carrier`], `m` for a fresh motive
//! variable and `•` for the point:
//!
//! ```text
//! MINORᵢ(m) := ∀y⃗. ( ( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)      the kᵢ plain field typings
//!                     ∧ (• ∈ ‖ind(p⃗)‖) × mᵢ     the recursive arguments
//!                     ∧ (• ∈ app(m, •)) × mᵢ )  the induction hypotheses
//!                   → • ∈ app(m, •) )                    [TruncRecursor::minors]
//!
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀t. (t ∈ ‖ind(p⃗)‖ → • ∈ app(m, t)) )
//!                                                        [TruncRecursor::rec]
//! ```
//!
//! [`TruncRecursor::minor_atoms`] is `MINORᵢ`'s antecedent atom by atom, and
//! [`TruncRecursor::minors`] the `n` quantified formulas, so a consumer
//! discharging the antecedent rebuilds exactly what the theorem carries rather
//! than guessing its association or its order.
//!
//! # Why it is a composition and not a new primitive
//!
//! The motive of a class-(P) recursor is `Sort 0`, so its value is `•`
//! (`thesis.txt:2114`) and `⟦motive t⟧` is a *truth value* — a subset of `{•}`.
//! Every inhabitant of `‖ind(p⃗)‖` is `•` ([`TruncCarrier::only_point`]), so the
//! motive is only ever asked about one element, and the whole induction is
//! [`decl_rect`] run at the **constant** formula
//!
//! ```text
//! φ(z) := • ∈ app(m, •)
//! ```
//!
//! [`decl_rect`]'s `φ` may mention a motive — every free variable of `φ` is
//! carried into the Separation `w_rect` mints — and `φ` here mentions `m` and
//! nothing else, so generalising over `m` at the end yields **one theorem per
//! declaration, not one per use site**. That is the standing rule about
//! declaration-level facts, and it is why the motive is minted here rather than
//! taken as an argument.
//!
//! # `φ` constant makes the recursive minors trivial — on both sides
//!
//! This is not obvious and it is why the two shapes agree. With `φ` constant in
//! `z`, [`rect_step`]'s antecedent for a constructor with `mᵢ ≥ 1` contains
//! `φ(tⱼ)`, i.e. `φ` itself, and its conclusion is `φ(ctorᵢ(y⃗,t⃗))`, i.e. again
//! `φ`. So `rect_stepᵢ` is `A ∧ … ∧ φ ∧ … → φ`: **provable by one projection**,
//! with no minor needed. `MINORᵢ` for such a constructor is likewise its own
//! consequent, so it is stated but never used.
//!
//! That is exactly why Lean's `step` minor for `Nat.le` carries no content
//! either, and both bottom out at a non-recursive constructor: they agree
//! because they are the same induction. A declaration all of whose constructors
//! are recursive has an empty carrier and the conclusion is vacuous — the
//! statement stays true, and says nothing, which is correct.
//!
//! At `mᵢ = 0`, by contrast, `MINORᵢ` **is** `rect_stepᵢ` on the nose: no
//! recursive atom to truncate and no induction hypothesis to add. Those are the
//! minors that carry the whole content, and the build checks the identity
//! rather than assuming it.
//!
//! # The two ends: `only_point` and `elim`
//!
//! [`decl_rect`] concludes `∀z. (z ∈ W → φ)`, over the *raw* carrier `W` and at
//! the constant `φ`. Turning that into the interface above is two steps, and
//! both are [`TruncCarrier`]'s:
//!
//! * `t ∈ ‖ind(p⃗)‖ ⟹ t = •` ([`TruncCarrier::only_point`]) — which both
//!   supplies `• ∈ ‖ind(p⃗)‖` and, read backwards through Leibniz, moves `φ`'s
//!   `app(m,•)` onto the `app(m,t)` the conclusion wants;
//! * `• ∈ ‖ind(p⃗)‖ ⟹ ∃w. w ∈ ind(p⃗)` ([`TruncCarrier::elim`]) — the induction
//!   speaks about a *member* of the carrier and the truncation has thrown the
//!   member away, so it has to be recovered. [`Inductive::ty_ax`] moves the
//!   existential from `ind(p⃗)` to `W`, and [`crate::conjoin`] plus
//!   `hyp_ex_branch` discharge the witness, which is free in neither the
//!   antecedent nor the conclusion.
//!
//! Without `elim` the theorem would be unprovable, and that is the honest
//! reading of what a small eliminator costs: the truncation is a *conservative*
//! quotient, so eliminating out of it has to go back to the thing truncated.
//!
//! # Scope: non-indexed only
//!
//! The indexed class-(P) recursor is a different construction, not a relaxed
//! guard on this one. Its `φ` is
//! `φ(z) := ∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗), z) → • ∈ app(m, x⃗, •))`, which is
//! **not constant in `z`**, so none of the simplifications above apply:
//! `rect_stepᵢ` then has to force `x⃗ = e⃗ᵢ` through
//! [`IndexedCtor::inv`](super::IndexedCtor::inv) and the recursive minors stop
//! being trivial. There is no tutorial witness for it, so it is not built and
//! not designed for.
//!
//! `n = 0` is **declined**. [`decl_rect`] returns `None` there, and the true
//! statement at zero constructors is a different one: `‖ind(p⃗)‖ = 0`, the
//! conclusion vacuous and there are no minors to state. `False` is class (S),
//! so there is no corpus witness either.
//!
//! # Nothing here is an axiom
//!
//! One Separation per call, inside [`decl_rect`]'s [`crate::wtype::w_rect`].
//! Everything else is an instance of a theorem [`TruncCarrier`] or
//! [`super::super::rect`] already proved.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{
    carry_under, gen_under, hyp_conj, hyp_ex_branch, hyp_inst, rewrite_under,
};
use crate::inductive::rect::{decl_rect, rect_parts};
use crate::inductive::Slot;
use crate::wrec::hyp_eq_symm;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conjoin, establishes, gen_all, hyp_mp,
    inst_all, syl, uncurry,
};

use super::trunc::TruncCarrier;

/// A non-indexed class-(P) declaration's elimination rule.
pub struct TruncRecursor {
    /// The motive variable `m`, minted here. Free in
    /// [`TruncRecursor::minor_atoms`] and [`TruncRecursor::minors`], and bound
    /// by the outermost `∀` but one of [`TruncRecursor::rec`].
    pub motive: FreeVar,
    /// `MINORᵢ`'s antecedent, atom by atom, **positional against the
    /// constructor's Lean field spine**: the `kᵢ + mᵢ` field atoms in *declared*
    /// order — `yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)` for a plain field, `• ∈ ‖ind(p⃗)‖` for a
    /// recursive one — followed by the `mᵢ` induction hypotheses, which is
    /// where Lean's minor premise puts them.
    ///
    /// Empty for a constructor with no fields, in which case `MINORᵢ` has no
    /// antecedent at all.
    pub minor_atoms: Vec<Vec<Formula>>,
    /// `MINORᵢ` itself, `∀y⃗`-quantified — and with **no `∀r⃗`**, exactly as in
    /// [`TruncCtor::trunc_mem`](super::trunc::TruncCtor::trunc_mem): a
    /// recursive argument of a `Prop` is a proof, so it contributes an atom and
    /// not a variable, and the two theorems can be read side by side.
    pub minors: Vec<Formula>,
    /// `⋀ᵢ MINORᵢ(m)`, the antecedent of [`TruncRecursor::rec`].
    pub hyp: Formula,
    /// **`⊢ ∀p⃗ ∀m. (⋀ᵢ MINORᵢ(m) → ∀t. (t ∈ ‖ind(p⃗)‖ → • ∈ app(m, t)))`**.
    pub rec: Thm,
}

impl TruncRecursor {
    /// The elimination rule for a **non-indexed** class-(P) declaration.
    ///
    /// `tc` must be [`TruncCarrier::over_declaration`] at this `ind` — checked
    /// on its `base` and, more tellingly, on the *statements* of the two
    /// theorems this spends, each of which is rebuilt here and compared.
    ///
    /// `None` for a declaration with no constructors (see the header), for an
    /// indexed `tc`, for a foreign apparatus, and on any internal shape check.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, so build this
    /// once per declaration and cache it with the result.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        tc: &TruncCarrier,
    ) -> Option<TruncRecursor> {
        let n = ind.spec.ctors.len();
        if n == 0
            || !ind.is_over(mach)
            || !tc.xvs.is_empty()
            || tc.base != ind.carrier
            || tc.ctors.len() != n
        {
            return None
        }
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let pt = s.point();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        // `φ(z) := • ∈ app(m, •)` — constant in `z`, and mentioning no free
        // variable but the motive.
        let mv = env.fresh_var();
        let zv = env.fresh_var();
        let phi = Formula::mem(pt.clone(), ap.apply(Term::var(mv), pt.clone()));

        // ── the minors, in Lean field order ─────────────────────────────────
        let mut minor_atoms: Vec<Vec<Formula>> = Vec::with_capacity(n);
        let mut minors: Vec<Formula> = Vec::with_capacity(n);
        for i in 0..n {
            let c = &tc.ctors[i];
            let (k, m) = (c.yvs.len(), c.tvs.len());
            if c.trunc_atoms.len() != k + m || ind.spec.ctors[i].order.len() != k + m {
                return None
            }
            // The mask, read as a permutation of the carrier's atom order:
            // plains occupy `0..k` of `trunc_atoms` and recursives `k..k+m`.
            let mut atoms: Vec<Formula> = Vec::with_capacity(k + 2 * m);
            let (mut plains, mut recs) = (0usize, 0usize);
            for slot in &ind.spec.ctors[i].order {
                match slot {
                    Slot::Plain => {
                        atoms.push(c.trunc_atoms[plains].clone());
                        plains += 1;
                    }
                    Slot::Rec => {
                        atoms.push(c.trunc_atoms[k + recs].clone());
                        recs += 1;
                    }
                }
            }
            if plains != k || recs != m {
                return None
            }
            atoms.extend(std::iter::repeat_n(phi.clone(), m));
            let body = match conj_of(&atoms) {
                Some(h) => Formula::imp(h, phi.clone()),
                None => phi.clone(),
            };
            minors.push(quantify(&c.yvs, body));
            minor_atoms.push(atoms);
        }
        let hyp = conj_of(&minors)?;

        // ── `⊢ HYP → RECT(φ)` ───────────────────────────────────────────────
        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != n {
            return None
        }
        let mut steps: Vec<Thm> = Vec::with_capacity(n);
        for i in 0..n {
            let c = &tc.ctors[i];
            let (k, m) = (c.yvs.len(), c.tvs.len());
            if m == 0 {
                // The minor *is* the induction step. Checked, not assumed.
                if minors[i] != parts[i] {
                    return None
                }
                steps.push(conj_proj(&minors, i)?);
            } else {
                // `φ` is its own induction hypothesis: one projection, and the
                // minor is not consulted.
                let mut atoms: Vec<Formula> = c.trunc_atoms[..k].to_vec();
                atoms.extend(
                    c.tvs.iter().map(|v| Formula::mem(Term::var(*v), ind.wty.clone())),
                );
                atoms.extend(std::iter::repeat_n(phi.clone(), m));
                let mut q = c.yvs.clone();
                q.extend(c.tvs.iter().copied());
                let step = gen_all(&q, &conj_proj(&atoms, k + m)?);
                if !establishes(&step, &parts[i]) {
                    return None
                }
                steps.push(a1i(&step, hyp.clone()));
            }
        }
        // `⊢ HYP → ∀z. (z ∈ W → φ)`.
        let h_all = syl(&hyp_conj(&steps)?, &decl_rect(env, mach, ind, zv, &phi)?)?;

        // ── the conclusion, at `‖ind(p⃗)‖` and at the motive's own argument ──
        let tv = env.fresh_var();
        let tt = Term::var(tv);
        let mem_t = Formula::mem(tt.clone(), tc.carrier.clone());
        let kf = Formula::and(hyp.clone(), mem_t.clone());
        let k_h = and_left(hyp.clone(), mem_t.clone());
        let k_m = and_right(hyp.clone(), mem_t.clone());

        // `t = •`, hence `• ∈ ‖ind(p⃗)‖`.
        let mut op_args = ps.clone();
        op_args.push(tt.clone());
        let op = inst_all(&tc.only_point, &op_args)?;
        if *op.concl() != Formula::imp(mem_t.clone(), Formula::eq(tt.clone(), pt.clone())) {
            return None
        }
        let k_pt = syl(&k_m, &op)?;
        let carrier = tc.carrier.clone();
        let k_ptmem = rewrite_under(env, &k_pt, move |q| Formula::mem(q, carrier.clone()), &k_m)?;

        // `∃w. w ∈ ind(p⃗)`, then the same existential at `W`.
        let wv = env.fresh_var();
        let ex_of = |a: Term| Formula::exists(wv, Formula::mem(Term::var(wv), a));
        let elim = inst_all(&tc.elim, &ps)?;
        if *elim.concl()
            != Formula::imp(
                Formula::mem(pt.clone(), tc.carrier.clone()),
                ex_of(ind.carrier.clone()),
            )
        {
            return None
        }
        let to_w = inst_all(&ind.ty_ax, &ps)?;
        let k_ex = carry_under(env, &to_w, ex_of, &syl(&k_ptmem, &elim)?)?;

        // Discharge the witness against the induction's conclusion.
        let k_at_w = hyp_inst(&syl(&k_h, &h_all)?, std::slice::from_ref(&Term::var(wv)))?;
        let branch = hyp_ex_branch(wv, &conjoin(&k_at_w)?, &kf, &phi)?;
        let k_phi = hyp_mp(&branch, &k_ex)?;

        // `t = •` back onto the motive's argument.
        let back = hyp_eq_symm(env, &k_pt)?;
        let (mt, ptc) = (Term::var(mv), pt.clone());
        let k_goal = rewrite_under(
            env,
            &back,
            move |q| Formula::mem(ptc.clone(), ap.apply(mt.clone(), q)),
            &k_phi,
        )?;

        let want_body = Formula::mem(pt.clone(), ap.apply(Term::var(mv), tt.clone()));
        if *k_goal.concl() != Formula::imp(kf, want_body.clone()) {
            return None
        }
        let closed = gen_under(tv, &hyp, &uncurry(&k_goal)?)?;

        let mut quant = ind.params.clone();
        quant.push(mv);
        let rec = gen_all(&quant, &closed);
        let want = quantify(
            &quant,
            Formula::imp(
                hyp.clone(),
                Formula::forall(tv, Formula::imp(mem_t, want_body)),
            ),
        );
        if !establishes(&rec, &want) {
            return None
        }
        Some(TruncRecursor { motive: mv, minor_atoms, minors, hyp, rec })
    }
}

/// `∀x₀ … ∀x_{n-1}. φ`, as a formula — outermost first, matching
/// [`gen_all`].
fn quantify(xs: &[FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}
