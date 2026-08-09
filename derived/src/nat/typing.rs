//! **The recursor's typing rule** — `natrec(c,g,n)` lands in the motive's fibre
//! at `n`, given that the two minor premises land in theirs.
//!
//! # Interface
//!
//! ```text
//! natrec_mem(env, nat, C, c, g) ->
//!   ⊢ ( c ∈ app(C, 0)
//!     ∧ ∀x ∀v. ((x ∈ ω ∧ v ∈ app(C,x)) → app(app(g,x), v) ∈ app(C, succ x)) )
//!     → ∀n. (n ∈ ω → natrec(c,g,n) ∈ app(C,n))
//! ```
//!
//! `C`, `c` and `g` are **terms the caller supplies** and nothing is assumed
//! about any of them: `app(C,·)` is a term whatever `C` is, exactly as
//! [`crate::nat::uniqueness`] reads `f` only through `app`. In particular there
//! is no `C ∈ fs(ω, U)` antecedent — it would be an antecedent nothing below
//! reads and a caller would have to discharge before this could fire.
//!
//! # Why it is here and not in [`crate::nat::apparatus`]
//!
//! [`Nat`] states what `natrec` *computes* — the two ι rules — and says nothing
//! about where its value lives, because where it lives depends on the motive
//! and the motive is not part of the recursor's construction. The two are
//! independent: a caller that only reduces needs the ι rules and not this, and
//! this file's proof uses the ι rules as its only facts about `natrec`.
//!
//! # The whole proof is one induction
//!
//! At `φ(n) := natrec(c,g,n) ∈ app(C,n)`:
//!
//! * `φ(0)` is the base premise moved along
//!   [`Nat::iota_zero`](crate::nat::Nat::iota_zero) — `natrec(c,g,0) = c`;
//! * `φ(succ x)` is the step premise at `v := natrec(c,g,x)`, moved along
//!   [`Nat::iota_succ`](crate::nat::Nat::iota_succ).
//!
//! So the ι rules are not an aside here, they are the two rewrites that turn a
//! statement about the *minors* into a statement about the recursor, and
//! [`crate::recursion::induction_scheme`] does the rest. Nothing new is minted
//! and no symbol is defined: the theorem is about the `natrec` the apparatus
//! already built.
//!
//! # A dependent motive, not a constant one
//!
//! The fibre moves with `n` on both sides — the step's hypothesis is at
//! `app(C,x)` and its conclusion at `app(C, succ x)`. A version stated at a
//! fixed set `A` would be strictly weaker and would not carry a checker's
//! `Nat.rec`, whose codomain is `C t` at the major premise's own value.
//! `tests/nat_typing.rs` pins this by instantiating at a motive that is
//! **different at every point**, so a proof that had silently collapsed the
//! fibre could not satisfy it.

use kernel::{Env, Formula, Term, Thm};

use crate::and_intro;
use crate::discharge::{assuming, discharge};
use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{and_elim_left, and_elim_right, inst_all};

use super::apparatus::Nat;
use super::glue::{induct, induct_step};

/// `⊢ b ∈ S` from `⊢ a = b` and `⊢ a ∈ S`.
///
/// One Leibniz instance at the hole `y ∈ S`. Kept local because the two
/// existing spellings do not fit: [`super::glue::congr_tmpl`] rewrites a
/// *term* and [`crate::rules::eq_trans`] composes two equations, and what is
/// wanted here is a membership carried along one.
fn mem_along(env: &mut Env, eq: &Thm, mem: &Thm) -> DResult<Thm> {
    let (a, b) = eq.concl().eq_parts()?;
    let (_, s) = mem.concl().mem_parts()?;
    let y = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, y, Formula::mem(Term::var(y), s));
    prim::mp(&prim::mp(&leib, eq)?, mem)
}

/// The recursor's typing rule at a motive `C`, a base `c` and a step `g`.
///
/// See the module header for the statement. Every hypothesis is discharged
/// before the result is returned, so the theorem is unconditional.
pub fn natrec_mem(env: &mut Env, nat: &Nat, cfam: &Term, c: &Term, g: &Term) -> DResult<Thm> {
    let zero = nat.zero();
    let x = env.fresh_var();
    let v = env.fresh_var();
    let (tx, tv) = (Term::var(x), Term::var(v));
    let fibre = |t: Term| nat.apply(cfam.clone(), t);

    // `φ(x) := natrec(c,g,x) ∈ app(C,x)`.
    let phi = Formula::mem(
        nat.natrec_of(c.clone(), g.clone(), tx.clone()),
        fibre(tx.clone()),
    );

    // The two premises, as formulas, and the conjunction they are assumed under.
    let base_f = Formula::mem(c.clone(), fibre(zero.clone()));
    let step_f = Formula::forall(
        x,
        Formula::forall(
            v,
            Formula::imp(
                Formula::and(nat.in_omega(tx.clone()), Formula::mem(tv.clone(), fibre(tx.clone()))),
                Formula::mem(
                    nat.apply(nat.apply(g.clone(), tx.clone()), tv.clone()),
                    fibre(nat.succ_of(tx.clone())),
                ),
            ),
        ),
    );
    let h = Formula::and(base_f, step_f);
    let assumed = assuming(h.clone());
    let base_h = and_elim_left(&assumed)?;
    let step_h = and_elim_right(&assumed)?;

    // ── `φ(0)` ───────────────────────────────────────────────────────────────
    // `natrec(c,g,0) = c` read backwards: the premise is about `c` and the
    // goal about the recursor.
    let iota0 = inst_all(&nat.iota_zero, &[c.clone(), g.clone()])?;
    let c_eq_rec = crate::rules::eq_symm(env, &iota0)?;
    let base = mem_along(env, &c_eq_rec, &base_h)?;

    // ── `∀x. ((x ∈ ω ∧ φ(x)) → φ(succ x))` ───────────────────────────────────
    let step = induct_step(nat.core(), x, &phi, |x_om, phi_x| {
        let rec_x = nat.natrec_of(c.clone(), g.clone(), tx.clone());
        // The step premise at `v := natrec(c,g,x)`, discharged with the two
        // facts the induction hands in.
        let at = inst_all(&step_h, &[tx.clone(), rec_x])?;
        let applied = prim::mp(&at, &and_intro(x_om, phi_x))?;
        // …and moved onto the recursor by the ι rule at a successor, whose own
        // side condition is the `x ∈ ω` in hand.
        let rule = inst_all(&nat.iota_succ, &[c.clone(), g.clone(), tx.clone()])?;
        let iota = prim::mp(&rule, x_om)?;
        let back = crate::rules::eq_symm(env, &iota)?;
        mem_along(env, &back, &applied)
    })?;

    let all = induct(env, nat.core(), x, &phi, &base, &step)?;
    Ok(discharge(&h, &all))
}
