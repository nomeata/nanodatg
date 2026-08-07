//! Tarski's Axiom A, unpacked, and the two closure facts it yields.
//!
//! # Interface
//!
//! [`Universe`] is the axiom's body decomposed: the universe variable, the
//! membership clause and the four closure clauses, each *read off* the axiom
//! rather than rebuilt. [`tarski_at`] and [`tarski_at_term`] produce it together
//! with `⊢ ∃u. Body(x, u)`. The theorems are
//!
//! ```text
//! ⊢ Body(x, u) → ∀y. (y ∈ u → 𝒫y ∈ u)                [universe_power_closed]
//! ⊢ Body(x, u) → ∀y. (y ∈ u → ∃p. (p ∈ u ∧ y ∈ p))   [universe_no_maximal]
//! ```
//!
//! Callers need neither derivation.
//!
//! # Every client must go through [`tarski_at_term`]
//!
//! The clause decomposition lives here and nowhere else, so that changing the
//! axiom breaks one call site rather than several. That is not hypothetical:
//! adding the transitivity clause `C₁` on 2026-07-31 broke two, because
//! `recursion.rs` had hand-rolled its own copy of this destructuring, and a
//! silently-shifted clause index is precisely the kind of error this development
//! cannot afford to make quietly. Because `C₁` sits second in the conjunction,
//! every projection here is one `split_and` deeper than it used to be.
//!
//! The clauses are *read* rather than rebuilt because the last of them mentions
//! equinumerosity, a formula several hundred nodes deep that no client should
//! have to reconstruct in order to project the others out of the conjunction.
//!
//! # What the two theorems are for
//!
//! [`universe_power_closed`] needs both closure clauses and neither alone; it is
//! what makes [`crate::empty::inductive_set_exists`] go through, i.e. it is
//! where Infinity comes from.
//!
//! [`universe_no_maximal`] is one line of Tarski's third clause — the `p ∈ u` it
//! provides holds every subset of `y`, and `y ⊆ y`, so `y ∈ p` — and it is what
//! rules out the counter-model [`crate::separation`] uses to show the empty set
//! independent of the other axioms. That model is generated from the `ℤ`-chain
//! by pairing, union, relative power set and replacement — all of which send
//! finite sets to finite sets, so every set in it is finite, and a finite
//! non-empty set does have an `∈`-maximal element. Tarski therefore fails there,
//! and the independence argument does not transfer.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{
    com12, exists_elim_imp, exists_intro_imp, hyp_and, hyp_mp, hyp_syl, iff_mp, imp_mono_r,
    inst_all, syl, uncurry,
};
use crate::{a1i, and_left, and_right, imp_refl};
use super::readers::{hyp_contract, open_exists, split_and};

/// Tarski's universe around `x`, with its five clauses read off the axiom.
///
/// The clauses are *read* rather than rebuilt — the last mentions
/// equinumerosity, a formula several hundred nodes deep that no client should
/// have to reconstruct in order to project the others out of the conjunction.
///
/// The transitivity clause `C₁` was added to `ax_tarski` on 2026-07-31; see the
/// note there. Because it sits second in the conjunction, every projection below
/// is one `split_and` deeper than it used to be.
pub struct Universe {
    /// The universe variable the clauses speak about.
    pub u: FreeVar,
    /// The whole body: `x ∈ u ∧ (C₁ ∧ (C₂ ∧ (C₃ ∧ C₄)))`.
    pub body: Formula,
    /// `x ∈ u`.
    pub mem: Formula,
    /// `∀y ∈ u. ∀z ∈ y. z ∈ u` — transitivity. Note `z ∈ y`, not `z ⊆ y`.
    pub transitive: Formula,
    /// `∀y ∈ u. ∀z ⊆ y. z ∈ u` — closure under subsets of members.
    pub closed_sub: Formula,
    /// `∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p` — power sets stay inside.
    pub closed_pow: Formula,
    /// `∀y ⊆ u. (y ≈ u ∨ y ∈ u)` — inaccessibility.
    pub inaccessible: Formula,
}

/// Tarski's Axiom A at a free variable `x`: `⊢ ∃u. Body(x, u)`, together with
/// the decomposition of `Body`.
pub fn tarski_at(env: &mut Env, x: FreeVar) -> DResult<(Universe, Thm)> {
    tarski_at_term(env, &Term::var(x))
}

/// As [`tarski_at`], but at an arbitrary term.
///
/// **Every client must go through this.** The clause decomposition lives here
/// and nowhere else, so that changing the axiom breaks one call site rather than
/// several. That is not hypothetical: adding the transitivity clause on
/// 2026-07-31 broke two, because `recursion.rs` had hand-rolled its own copy of
/// this destructuring, and a silently-shifted clause index is precisely the kind
/// of error this development cannot afford to make quietly.
pub fn tarski_at_term(env: &mut Env, x: &Term) -> DResult<(Universe, Thm)> {
    let ax = Thm::ax_tarski(env);
    let ex = inst_all(&ax, std::slice::from_ref(x))?;

    let u = env.fresh_var();
    let body = open_exists(ex.concl(), &Term::var(u))?;
    debug_assert_eq!(*ex.concl(), Formula::exists(u, body.clone()), "the ∃u did not reopen");

    let (mem, rest) = split_and(&body)?;
    let (transitive, rest2) = split_and(&rest)?;
    let (closed_sub, rest3) = split_and(&rest2)?;
    let (closed_pow, inaccessible) = split_and(&rest3)?;
    debug_assert_eq!(mem, Formula::mem(x.clone(), Term::var(u)));

    Ok((Universe { u, body, mem, transitive, closed_sub, closed_pow, inaccessible }, ex))
}

impl Universe {
    /// The three suffixes of the body, as the projections need them:
    /// `rest = C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`, `rest2 = C₂ ∧ (C₃ ∧ C₄)`, `rest3 = C₃ ∧ C₄`.
    fn suffixes(&self) -> (Formula, Formula, Formula) {
        let (_, rest) = split_and(&self.body).expect("Universe body is a conjunction");
        let (_, rest2) = split_and(&rest).expect("Universe body is a conjunction");
        let (_, rest3) = split_and(&rest2).expect("Universe body is a conjunction");
        (rest, rest2, rest3)
    }

    /// `⊢ Body → Cₙ₊₁ ∧ …`, i.e. peel `n` conjuncts off the front of the body.
    fn drop_front(&self, n: usize) -> Thm {
        let (rest, rest2, rest3) = self.suffixes();
        let steps = [
            and_right(self.mem.clone(), rest),
            and_right(self.transitive.clone(), rest2),
            and_right(self.closed_sub.clone(), rest3),
        ];
        let mut acc = steps[0].clone();
        for step in &steps[1..n] {
            acc = syl(&acc, step).expect("projection composes");
        }
        acc
    }

    /// `⊢ Body → x ∈ u`.
    pub fn body_mem(&self) -> Thm {
        let (rest, _, _) = self.suffixes();
        and_left(self.mem.clone(), rest)
    }

    /// `⊢ Body → C₁` — transitivity.
    pub fn body_transitive(&self) -> Thm {
        let (_, rest2, _) = self.suffixes();
        syl(&self.drop_front(1), &and_left(self.transitive.clone(), rest2)).expect("projection composes")
    }

    /// `⊢ Body → C₂`.
    pub fn body_closed_sub(&self) -> Thm {
        let (_, _, rest3) = self.suffixes();
        syl(&self.drop_front(2), &and_left(self.closed_sub.clone(), rest3)).expect("projection composes")
    }

    /// `⊢ Body → C₃`.
    pub fn body_closed_pow(&self) -> Thm {
        syl(&self.drop_front(3), &and_left(self.closed_pow.clone(), self.inaccessible.clone()))
            .expect("projection composes")
    }

    /// `⊢ Body → C₄` — inaccessibility.
    pub fn body_inaccessible(&self) -> Thm {
        syl(&self.drop_front(3), &and_right(self.closed_pow.clone(), self.inaccessible.clone()))
            .expect("projection composes")
    }
}

/// `⊢ Body(x, u) → ∀y. (y ∈ u → 𝒫y ∈ u)` — Tarski's universe is closed under
/// power sets.
///
/// The two closure clauses do this between them, and neither does it alone.
/// Clause C₃ puts *some* `p ∈ u` above every subset of `y`, so `𝒫y ⊆ p`; clause
/// C₂ then pulls `𝒫y`, being a subset of the member `p`, back into `u`. Note
/// what is *not* needed: no appeal to inaccessibility, and so no unpacking of
/// the equinumerosity formula.
pub fn universe_power_closed(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    univ: &Universe,
) -> DResult<Thm> {
    let tu = Term::var(univ.u);
    let y = env.fresh_var();
    let ty = Term::var(y);
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let goal = Formula::mem(pow_y.clone(), tu.clone());

    // C₃ at `y`, with the witness `p` and the clause it satisfies read off.
    let c3_y = prim::ax_inst(univ.closed_pow.clone(), ty.clone())?;
    let (_, c3_y_body) = c3_y.concl().imp_parts()?;
    let (_, ex_p) = c3_y_body.imp_parts()?;
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    debug_assert_eq!(ex_p, Formula::exists(p, bp.clone()), "C₃'s ∃p did not reopen");
    let (p_in_u, all_sub_p) = split_and(&bp)?;
    debug_assert_eq!(p_in_u, Formula::mem(tp.clone(), tu.clone()));

    // Under `K := Body ∧ y ∈ u`, C₃ supplies the witness.
    let k = Formula::and(univ.body.clone(), y_in_u.clone());
    let k_body = and_left(univ.body.clone(), y_in_u.clone());
    let k_y_in_u = and_right(univ.body.clone(), y_in_u.clone());
    let k_ex_p = hyp_mp(&syl(&k_body, &syl(&univ.body_closed_pow(), &c3_y)?)?, &k_y_in_u)?;

    // Under `L := K ∧ (p ∈ u ∧ ∀z ⊆ y. z ∈ p)`.
    let l = Formula::and(k.clone(), bp.clone());
    let l_k = and_left(k.clone(), bp.clone());
    let l_bp = and_right(k.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all_sub_p = syl(&l_bp, &and_right(p_in_u.clone(), all_sub_p.clone()))?;

    // `L → 𝒫y ⊆ p`: a member of `𝒫y` is a subset of `y`, and those are in `p`.
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l_v_sub_p = syl(&l_all_sub_p, &prim::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_v_pow = a1i(&iff_mp(&pw_at_v)?, l.clone());
    let l_step = hyp_syl(&l_v_pow, &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = prim::mp(&prim::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l.clone(), kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // C₂ at `p` and then at `𝒫y`: a subset of the member `p` is a member.
    let c2_p = prim::ax_inst(univ.closed_sub.clone(), tp)?;
    let (_, c2_p_body) = c2_p.concl().imp_parts()?;
    let (_, all_sub_u) = c2_p_body.imp_parts()?;
    let c2_pw = syl(&c2_p, &imp_mono_r(&prim::ax_inst(all_sub_u, pow_y)?, p_in_u)?)?;

    let l_c2 = syl(&l_k, &syl(&k_body, &univ.body_closed_sub())?)?;
    let l_goal = hyp_mp(&hyp_mp(&syl(&l_c2, &c2_pw)?, &l_p_in_u)?, &l_sub)?;

    // Discharge the witness `p`, then contract the duplicated `K`.
    let k_goal_f = Formula::imp(k.clone(), goal.clone());
    let bp_kg = com12(&uncurry(&l_goal)?)?;
    let ex_kg = exists_elim_imp(p, &Thm::gen(p, &bp_kg), &k_goal_f)?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;

    let body_y = uncurry(&k_goal)?;
    let out = prim::mp(
        &prim::ax_dist(y, univ.body.clone(), Formula::imp(y_in_u.clone(), goal.clone()))?,
        &Thm::gen(y, &body_y),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(univ.body.clone(), Formula::forall(y, Formula::imp(y_in_u, goal))),
        "universe_power_closed produced an unexpected shape"
    );
    Ok(out)
}

/// `⊢ Body(x, u) → ∀y. (y ∈ u → ∃p. (p ∈ u ∧ y ∈ p))` — Tarski's universe has
/// no `∈`-maximal element.
///
/// One line of Tarski's third clause: the `p ∈ u` it provides holds every
/// subset of `y`, and `y ⊆ y`, so `y ∈ p`.
///
/// This is what rules out the counter-model `separation.rs` uses to show the
/// empty set independent of the other axioms. That model is generated from the
/// `ℤ`-chain by pairing, union, relative power set and replacement — all of
/// which send finite sets to finite sets, so every set in it is finite, and a
/// finite non-empty set does have an `∈`-maximal element. Tarski therefore
/// fails there, and the independence argument does not transfer.
pub fn universe_no_maximal(env: &mut Env, univ: &Universe) -> DResult<Thm> {
    let tu = Term::var(univ.u);
    let y = env.fresh_var();
    let ty = Term::var(y);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());

    let c3_y = prim::ax_inst(univ.closed_pow.clone(), ty.clone())?;
    let (_, c3_y_body) = c3_y.concl().imp_parts()?;
    let (_, ex_p) = c3_y_body.imp_parts()?;
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    let (p_in_u, all_sub_p) = split_and(&bp)?;

    // The goal, with its own witness variable.
    let p2 = env.fresh_var();
    let tp2 = Term::var(p2);
    let goal_body =
        Formula::and(Formula::mem(tp2.clone(), tu.clone()), Formula::mem(ty.clone(), tp2));
    let goal = Formula::exists(p2, goal_body.clone());

    let k = Formula::and(univ.body.clone(), y_in_u.clone());
    let k_body = and_left(univ.body.clone(), y_in_u.clone());
    let k_y_in_u = and_right(univ.body.clone(), y_in_u.clone());
    let k_ex_p = hyp_mp(&syl(&k_body, &syl(&univ.body_closed_pow(), &c3_y)?)?, &k_y_in_u)?;

    // `⊢ y ⊆ y`, which is what puts `y` itself into `p`.
    let v = env.fresh_var();
    let sub_refl = Thm::gen(v, &imp_refl(Formula::mem(Term::var(v), ty.clone())));
    debug_assert_eq!(*sub_refl.concl(), kernel::thm::subset(env, ty.clone(), ty.clone()));

    let l = Formula::and(k.clone(), bp.clone());
    let l_bp = and_right(k.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all = syl(&l_bp, &and_right(p_in_u, all_sub_p.clone()))?;
    let l_y_in_p = hyp_mp(
        &syl(&l_all, &prim::ax_inst(all_sub_p, ty.clone())?)?,
        &a1i(&sub_refl, l.clone()),
    )?;
    let l_goal = syl(&hyp_and(&l_p_in_u, &l_y_in_p)?, &exists_intro_imp(p2, goal_body, tp)?)?;

    let ex_kg = exists_elim_imp(
        p,
        &Thm::gen(p, &com12(&uncurry(&l_goal)?)?),
        &Formula::imp(k.clone(), goal.clone()),
    )?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;
    let out = prim::mp(
        &prim::ax_dist(y, univ.body.clone(), Formula::imp(y_in_u.clone(), goal.clone()))?,
        &Thm::gen(y, &uncurry(&k_goal)?),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(univ.body.clone(), Formula::forall(y, Formula::imp(y_in_u, goal))),
        "universe_no_maximal produced an unexpected shape"
    );
    Ok(out)
}
