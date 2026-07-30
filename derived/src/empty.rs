//! Towards the empty set, using Tarski's Axiom A.
//!
//! `separation.rs` records why an empty set is not derivable from
//! Extensionality, Pairing, Union, Power, Replacement and Regularity: those
//! axioms are all modelled by the sets generated from a `ℤ`-indexed membership
//! chain, in which nothing bottoms out. This module is the attempt to close
//! that gap with [`Thm::ax_tarski`], and it records exactly how far the
//! attempt gets.
//!
//! # Where the derivation stands
//!
//! Two ends of a bridge are built here, and the middle is identified.
//!
//! * **The far end.** [`empty_from_transitive`] proves
//!   `⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)`: Regularity turns *any*
//!   non-empty transitive set into an empty one, because an `∈`-minimal element
//!   of a transitive set is a subset of it and so has no members at all. Every
//!   ingredient downstream of an empty set — [`empty_of_exists`], and hence
//!   `crate::separation::separation` — is built and ready.
//! * **The near end.** Tarski's universe `u` around a given `x` is closed under
//!   power sets: [`universe_power_closed`] derives `∀y ∈ u. 𝒫y ∈ u` by taking
//!   the `p ⊇ 𝒫y` that Tarski's third clause supplies inside `u` and pushing
//!   `𝒫y ⊆ p` back into `u` with the second clause. Hence
//!   [`inductive_set_exists`]: `⊢ ∀x ∃u. (x ∈ u ∧ ∀y ∈ u. 𝒫y ∈ u)` — an
//!   **inductive set**, which is to say Tarski gives Infinity — and then
//!   [`least_inductive_set_exists`]: `⊢ ∀x ∃n. Least(x, n)`, an `ω` that is
//!   contained in every inductive set, **so induction is available**. That is
//!   new, and it is what makes the remaining gap a matter of length rather than
//!   of independence: the `ℤ`-chain counter-model of `separation.rs` does *not*
//!   satisfy Tarski (see [`universe_no_maximal`]), so the independence argument
//!   there no longer applies once `ax_tarski` is in play.
//! * **The middle, not built.** Induction gives the recursion theorem, which
//!   gives the iterates `⋃ⁿx`; their union is the transitive closure of `x`,
//!   which is the transitive set the far end wants (its members' members are
//!   one iterate further down, hence still in the union). The recursion theorem
//!   needs only Separation *at a satisfied condition* —
//!   [`crate::separation::separation_nonvacuous`], which is already available
//!   and needs no empty set, because every induction here carries its base case
//!   as the required witness. So the derivation is not circular, merely long:
//!   it wants finite approximating functions and induction over `ω` on top of
//!   the function-graph apparatus in `crate::funcs`, and that is where the work
//!   remaining sits.
//!
//! Nothing here adds an axiom, and no `Thm` is produced other than through the
//! kernel's rules.
//!
//! # Why the obvious shortcuts do not work
//!
//! Tarski's `u` is **not** stated to be transitive, and it need not be: the
//! second clause closes it under *subsets* of members, not under members of
//! members. From `w ∈ y ∈ u` one gets `{w} ⊆ y`, hence `{w} ∈ u` — the
//! singleton, never `w` itself. So Regularity applied to `u`, to `⋃u`, to
//! `𝒫m`, or to `u ∪ ⋃u` yields a minimal element that is not known to be a
//! subset of the set it is minimal in, and the argument stalls in exactly the
//! same place each time. Everything Tarski *adds* points upwards (`u` is closed
//! under `𝒫`, under singletons, and has no `∈`-maximal element); reaching the
//! bottom is what needs the downward iteration of `⋃`, and that needs
//! recursion.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, com12_imp, define_by_membership, eq_symm_imp, ex_falso, exists_elim,
    exists_elim_imp, exists_intro, exists_intro_imp, exists_mono, gen_all, hyp_and, hyp_mp, iff_mp,
    iff_mpr, imp_mono_r, imp_refl, inst_all, singleton, syl, uncurry,
};
use crate::separation::hyp_syl;

// ─────────────────────────────────────────────────────────────────────────────
// Reading formulas back apart.
//
// The axioms are built by the kernel with the kernel's own fresh variables. A
// derivation outside it either rebuilds each subformula (and hopes the shapes
// agree) or *reads* them off, which is what these do. Reading is untrusted and
// safe: no `Thm` is produced.
// ─────────────────────────────────────────────────────────────────────────────

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
pub fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
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
///
/// `Thm::ax_inst` is a theorem whatever `φ` is, so its conclusion can be mined
/// for the instance without `φ` being proved.
pub fn open_forall(phi: &Formula, t: &Term) -> Option<Formula> {
    let inst = Thm::ax_inst(phi.clone(), t.clone())?;
    let (_, body) = inst.concl().as_imp()?;
    Some(body)
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`, so this unwraps two
/// negations around [`open_forall`].
pub fn open_exists(phi: &Formula, t: &Term) -> Option<Formula> {
    let (all_not, fls) = phi.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let not_body = open_forall(&all_not, t)?;
    let (body, fls2) = not_body.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some(body)
}

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
pub fn hyp_contract(t: &Thm) -> Option<Thm> {
    let (h, rest) = t.concl().as_imp()?;
    let (h2, phi) = rest.as_imp()?;
    if h != h2 {
        return None
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    let step = Thm::mp(&s, t)?;
    Thm::mp(&step, &imp_refl(h))
}

/// From `⊢ A → (B → χ)` infer `⊢ (A ∧ B) → χ` — the converse of
/// [`crate::uncurry`].
pub fn curry(t: &Thm) -> Option<Thm> {
    let (a, rest) = t.concl().as_imp()?;
    let (b, _) = rest.as_imp()?;
    // Under `A ∧ B`: apply the theorem to the left conjunct, then to the right.
    let via_a = syl(&and_left(a.clone(), b.clone()), t)?;
    hyp_mp(&via_a, &and_right(a, b))
}

// ─────────────────────────────────────────────────────────────────────────────
// Regularity, applied.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀x. ¬(x ∈ x)` — no set is a member of itself.
///
/// Regularity at the singleton `{x}`: its only member is `x`, so `x` is the
/// `∈`-minimal one, and `x ∈ x` would put `x` in `x ∩ {x}`.
pub fn no_self_mem(env: &mut Env, up: FnSym, mem_sing: &Thm) -> Option<Thm> {
    let reg = Thm::ax_regularity(env);

    let x = env.fresh_var();
    let tx = Term::var(x);
    let sx = singleton(up, tx.clone());

    // Regularity at `{x}`, with the two bound variables rebuilt as our own —
    // alpha-equivalent formulas are syntactically equal, so this is the very
    // formula the kernel produced.
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let inst = inst_all(&reg, std::slice::from_ref(&sx))?;
    let y_in_sx = Formula::mem(ty.clone(), sx.clone());
    let clash = Formula::exists(
        z,
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), sx.clone())),
    );
    let body = Formula::and(y_in_sx.clone(), Formula::not(clash.clone()));
    debug_assert_eq!(
        *inst.concl(),
        Formula::imp(Formula::exists(y, Formula::mem(ty.clone(), sx.clone())), Formula::exists(y, body.clone())),
        "Regularity did not instantiate to the expected shape"
    );

    // `⊢ x ∈ {x}`, so `{x}` is non-empty and Regularity applies.
    let ms_x = inst_all(mem_sing, &[tx.clone(), tx.clone()])?;
    let x_in_sx = Thm::mp(&iff_mpr(&ms_x)?, &Thm::eq_refl(tx.clone()))?;
    let nonempty = exists_intro(y, Formula::mem(ty.clone(), sx.clone()), tx.clone(), &x_in_sx)?;
    let ex_min = Thm::mp(&inst, &nonempty)?;

    // Under `W := body(y) ∧ x ∈ x`, derive `⊥`.
    let xx = Formula::mem(tx.clone(), tx.clone());
    let w = Formula::and(body.clone(), xx.clone());
    let w_body = and_left(body.clone(), xx.clone());
    let w_y_in_sx = syl(&w_body, &and_left(y_in_sx.clone(), Formula::not(clash.clone())))?;
    let w_y_eq_x = syl(&w_y_in_sx, &iff_mp(&inst_all(mem_sing, &[tx.clone(), ty.clone()])?)?)?;
    let w_x_eq_y = syl(&w_y_eq_x, &eq_symm_imp(env, ty.clone(), tx.clone()))?;
    let w_xx = and_right(body.clone(), xx.clone());

    // Leibniz carries `x ∈ x` along `x = y` to `x ∈ y`.
    let v = env.fresh_var();
    let leib = Thm::eq_leibniz(tx.clone(), ty.clone(), v, Formula::mem(tx.clone(), Term::var(v)));
    let w_x_in_y = hyp_mp(&hyp_mp(&a1i(&leib, w.clone()), &w_x_eq_y)?, &w_xx)?;
    let w_x_in_sx = a1i(&x_in_sx, w.clone());
    let w_pair = hyp_and(&w_x_in_y, &w_x_in_sx)?;
    let clash_body =
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), sx.clone()));
    let w_clash = syl(&w_pair, &exists_intro_imp(z, clash_body, tx.clone())?)?;
    let w_not_clash = syl(&w_body, &and_right(y_in_sx, Formula::not(clash)))?;
    let w_false = hyp_mp(&w_not_clash, &w_clash)?;

    let not_xx = Formula::not(xx);
    let body_to_goal = uncurry(&w_false)?;
    debug_assert_eq!(*body_to_goal.concl(), Formula::imp(body, not_xx.clone()));

    let out = exists_elim(y, &ex_min, &Thm::gen(y, &body_to_goal), &not_xx)?;
    debug_assert_eq!(*out.concl(), not_xx);
    Some(Thm::gen(x, &out))
}

/// The transitivity of `t`, spelled out: `∀a ∀b. ((b ∈ a ∧ a ∈ t) → b ∈ t)`.
pub fn transitive(env: &mut Env, t: &Term) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::imp(
                Formula::and(Formula::mem(tb.clone(), ta.clone()), Formula::mem(ta, t.clone())),
                Formula::mem(tb, t.clone()),
            ),
        ),
    )
}

/// `⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)`.
///
/// **The far end of the bridge.** Regularity hands back an `∈`-minimal `y ∈ t`,
/// meaning nothing is in both `y` and `t`. Transitivity says everything in `y`
/// *is* in `t`. So nothing is in `y`.
///
/// This is exactly the step `separation.rs` names as unreachable — "a minimal
/// element of `t` is empty only when `t` is transitive" — turned into a
/// theorem, so that producing any non-empty transitive set now suffices.
pub fn empty_from_transitive(env: &mut Env) -> Option<Thm> {
    let reg = Thm::ax_regularity(env);

    let t = env.fresh_var();
    let tt = Term::var(t);
    let trans = transitive(env, &tt);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let inst = inst_all(&reg, std::slice::from_ref(&tt))?;
    let y_in_t = Formula::mem(ty.clone(), tt.clone());
    let clash_body =
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), tt.clone()));
    let clash = Formula::exists(z, clash_body.clone());
    let body = Formula::and(y_in_t.clone(), Formula::not(clash.clone()));
    let nonempty = Formula::exists(y, y_in_t.clone());
    debug_assert_eq!(
        *inst.concl(),
        Formula::imp(nonempty.clone(), Formula::exists(y, body.clone())),
        "Regularity did not instantiate to the expected shape"
    );

    // `⊢ Trans(t) → ((z ∈ y ∧ y ∈ t) → z ∈ t)`, by instantiating twice.
    let trans_y = Thm::ax_inst(trans.clone(), ty.clone())?;
    let (_, trans_y_body) = trans_y.concl().as_imp()?;
    let trans_yz = syl(&trans_y, &Thm::ax_inst(trans_y_body, tz.clone())?)?;

    // Under `W := Trans(t) ∧ body(y)`, then `V := W ∧ z ∈ y`, derive `⊥`.
    let w = Formula::and(trans.clone(), body.clone());
    let w_trans = and_left(trans.clone(), body.clone());
    let w_body = and_right(trans.clone(), body.clone());
    let w_y_in_t = syl(&w_body, &and_left(y_in_t.clone(), Formula::not(clash.clone())))?;
    let w_not_clash = syl(&w_body, &and_right(y_in_t, Formula::not(clash)))?;
    let w_trans_yz = syl(&w_trans, &trans_yz)?;

    let zy = Formula::mem(tz.clone(), ty.clone());
    let v = Formula::and(w.clone(), zy.clone());
    let v_zy = and_right(w.clone(), zy.clone());
    let v_w = and_left(w.clone(), zy.clone());
    let v_pair = hyp_and(&v_zy, &syl(&v_w, &w_y_in_t)?)?;
    let v_zt = hyp_mp(&syl(&v_w, &w_trans_yz)?, &v_pair)?;
    let v_clash = hyp_mp(
        &a1i(&exists_intro_imp(z, clash_body, tz.clone())?, v.clone()),
        &hyp_and(&v_zy, &v_zt)?,
    )?;
    let v_false = hyp_mp(&syl(&v_w, &w_not_clash)?, &v_clash)?;

    // `⊢ W → ∀z. ¬(z ∈ y)`, then `y` witnesses the goal.
    let not_zy = Formula::not(zy);
    let w_not_zy = uncurry(&v_false)?;
    let w_all = Thm::mp(&Thm::ax_dist(z, w.clone(), not_zy.clone())?, &Thm::gen(z, &w_not_zy))?;

    let e = env.fresh_var();
    let empty_of = |s: &Term| Formula::forall(z, Formula::not(Formula::mem(tz.clone(), s.clone())));
    let goal = Formula::exists(e, empty_of(&Term::var(e)));
    let w_goal = syl(&w_all, &exists_intro_imp(e, empty_of(&Term::var(e)), ty.clone())?)?;
    debug_assert_eq!(*w_goal.concl(), Formula::imp(w, goal.clone()));

    // Discharge the witness `y`, then Regularity's premise.
    let trans_goal = Formula::imp(trans.clone(), goal.clone());
    let body_tg = com12(&uncurry(&w_goal)?)?;
    let ex_tg = exists_elim_imp(y, &Thm::gen(y, &body_tg), &trans_goal)?;
    let ne_tg = syl(&inst, &ex_tg)?;

    let out = curry(&ne_tg)?;
    debug_assert_eq!(*out.concl(), Formula::imp(Formula::and(nonempty, trans), goal));
    Some(Thm::gen(t, &out))
}

/// Introduce the symbol `∅` with `⊢ ∀z. ¬(z ∈ ∅)`, given `⊢ ∃e ∀z. ¬(z ∈ e)`.
///
/// The `∃!` that `kernel::thm::define` demands is existence plus
/// Extensionality — two sets with no members have the same members — which is
/// exactly what [`crate::define_by_membership`] packages, at the membership
/// condition `⊥`.
///
/// An unconditional `empty(env) -> (FnSym, Thm)` is deliberately **not**
/// provided. The premise is precisely the part that is not yet derivable, and a
/// version of this function without it would be an axiom in disguise. Supply
/// the premise — [`empty_from_transitive`] discharges it as soon as a non-empty
/// transitive set is in hand — and this produces the symbol, after which
/// [`crate::separation::separation`] becomes callable.
pub fn empty_of_exists(env: &mut Env, existence: &Thm) -> Option<(FnSym, Thm)> {
    let (e, z) = (env.fresh_var(), env.fresh_var());
    let (te, tz) = (Term::var(e), Term::var(z));
    let mem = Formula::mem(tz.clone(), te.clone());
    let emp = Formula::forall(z, Formula::not(mem.clone()));
    if *existence.concl() != Formula::exists(e, emp.clone()) {
        return None
    }

    // `¬(z ∈ e)` is the forward half of `z ∈ e ↔ ⊥`; the backward half is ex
    // falso. So `⊢ ∃e ∀z. ¬(z ∈ e)` is `⊢ ∃e ∀z. (z ∈ e ↔ ⊥)` in the shape
    // `define_by_membership` wants.
    let fwd = Thm::ax_inst(emp.clone(), tz.clone())?;
    let bwd = a1i(&ex_falso(mem.clone()), emp.clone());
    let iff_body = Formula::iff(mem, Formula::false_());
    let all = Thm::mp(&Thm::ax_dist(z, emp.clone(), iff_body)?, &Thm::gen(z, &hyp_and(&fwd, &bwd)?))?;
    let ex_iff = Thm::mp(&exists_mono(e, &Thm::gen(e, &all))?, existence)?;

    let (sym, ax) = define_by_membership(env, &[], &ex_iff, z, &Formula::false_())?;
    let at_z = Thm::mp(&Thm::ax_inst(ax.concl().clone(), tz.clone())?, &ax)?;
    let out = Thm::gen(z, &iff_mp(&at_z)?);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(z, Formula::not(Formula::mem(tz, Term::apply(sym, vec![])))),
        "empty_of_exists produced an unexpected shape"
    );
    Some((sym, out))
}

/// `⊢ ∀t ∀a. ((∃w. w ∈ t) ∧ Trans(t)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`.
///
/// The full Separation scheme, for a caller-supplied `φ`, resting on nothing
/// but a non-empty transitive set. This is
/// [`crate::separation::separation_existence`] — which carries emptiness as an
/// antecedent — with that antecedent traded for the transitivity hypothesis via
/// [`empty_from_transitive`].
///
/// It is the sharpest honest statement of where the development stands:
/// Separation is one non-empty transitive set away, and nothing else is
/// missing.
pub fn separation_from_transitive(env: &mut Env, x: FreeVar, phi: &Formula) -> Option<Thm> {
    let sep = crate::separation::separation_existence(env, x, phi)?;

    let a = env.fresh_var();
    let all_e = inst_all(&sep, &[Term::var(a)])?;
    let e = env.fresh_var();
    let opened = open_forall(all_e.concl(), &Term::var(e))?;
    let (emp, goal) = opened.as_imp()?;
    debug_assert_eq!(*all_e.concl(), Formula::forall(e, Formula::imp(emp, goal.clone())));

    let ex_goal = exists_elim_imp(e, &all_e, &goal)?;
    let t = env.fresh_var();
    let at_t = inst_all(&empty_from_transitive(env)?, &[Term::var(t)])?;
    let out = syl(&at_t, &ex_goal)?;
    Some(gen_all(&[t, a], &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Tarski's Axiom A, unpacked.
// ─────────────────────────────────────────────────────────────────────────────

/// Tarski's universe around `x`, with its four clauses read off the axiom.
///
/// The clauses are *read* rather than rebuilt — the fourth mentions
/// equinumerosity, a formula several hundred nodes deep that no client should
/// have to reconstruct in order to project the other three out of the
/// conjunction.
pub struct Universe {
    /// The universe variable the clauses speak about.
    pub u: FreeVar,
    /// The whole body: `x ∈ u ∧ (C₂ ∧ (C₃ ∧ C₄))`.
    pub body: Formula,
    /// `x ∈ u`.
    pub mem: Formula,
    /// `∀y ∈ u. ∀z ⊆ y. z ∈ u` — closure under subsets of members.
    pub closed_sub: Formula,
    /// `∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p` — power sets stay inside.
    pub closed_pow: Formula,
    /// `∀y ⊆ u. (y ≈ u ∨ y ∈ u)` — inaccessibility.
    pub inaccessible: Formula,
}

/// Tarski's Axiom A at a free variable `x`: `⊢ ∃u. Body(x, u)`, together with
/// the decomposition of `Body`.
pub fn tarski_at(env: &mut Env, x: FreeVar) -> Option<(Universe, Thm)> {
    let ax = Thm::ax_tarski(env);
    let ex = inst_all(&ax, &[Term::var(x)])?;

    let u = env.fresh_var();
    let body = open_exists(ex.concl(), &Term::var(u))?;
    debug_assert_eq!(*ex.concl(), Formula::exists(u, body.clone()), "the ∃u did not reopen");

    let (mem, rest) = split_and(&body)?;
    let (closed_sub, rest2) = split_and(&rest)?;
    let (closed_pow, inaccessible) = split_and(&rest2)?;
    debug_assert_eq!(mem, Formula::mem(Term::var(x), Term::var(u)));

    Some((Universe { u, body, mem, closed_sub, closed_pow, inaccessible }, ex))
}

impl Universe {
    /// `⊢ Body → x ∈ u`.
    pub fn body_mem(&self) -> Thm {
        let (_, rest) = split_and(&self.body).expect("Universe body is a conjunction");
        and_left(self.mem.clone(), rest)
    }

    /// `⊢ Body → C₂`.
    pub fn body_closed_sub(&self) -> Thm {
        let (_, rest) = split_and(&self.body).expect("Universe body is a conjunction");
        let (_, rest2) = split_and(&rest).expect("Universe body is a conjunction");
        syl(&and_right(self.mem.clone(), rest), &and_left(self.closed_sub.clone(), rest2))
            .expect("projection composes")
    }

    /// `⊢ Body → C₃`.
    pub fn body_closed_pow(&self) -> Thm {
        let (_, rest) = split_and(&self.body).expect("Universe body is a conjunction");
        let (_, rest2) = split_and(&rest).expect("Universe body is a conjunction");
        let to_rest2 = syl(&and_right(self.mem.clone(), rest), &and_right(self.closed_sub.clone(), rest2.clone()))
            .expect("projection composes");
        syl(&to_rest2, &and_left(self.closed_pow.clone(), self.inaccessible.clone()))
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
) -> Option<Thm> {
    let tu = Term::var(univ.u);
    let y = env.fresh_var();
    let ty = Term::var(y);
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let goal = Formula::mem(pow_y.clone(), tu.clone());

    // C₃ at `y`, with the witness `p` and the clause it satisfies read off.
    let c3_y = Thm::ax_inst(univ.closed_pow.clone(), ty.clone())?;
    let (_, c3_y_body) = c3_y.concl().as_imp()?;
    let (_, ex_p) = c3_y_body.as_imp()?;
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
    let l_v_sub_p = syl(&l_all_sub_p, &Thm::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_v_pow = a1i(&iff_mp(&pw_at_v)?, l.clone());
    let l_step = hyp_syl(&l_v_pow, &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = Thm::mp(&Thm::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l.clone(), kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // C₂ at `p` and then at `𝒫y`: a subset of the member `p` is a member.
    let c2_p = Thm::ax_inst(univ.closed_sub.clone(), tp)?;
    let (_, c2_p_body) = c2_p.concl().as_imp()?;
    let (_, all_sub_u) = c2_p_body.as_imp()?;
    let c2_pw = syl(&c2_p, &imp_mono_r(&Thm::ax_inst(all_sub_u, pow_y)?, p_in_u)?)?;

    let l_c2 = syl(&l_k, &syl(&k_body, &univ.body_closed_sub())?)?;
    let l_goal = hyp_mp(&hyp_mp(&syl(&l_c2, &c2_pw)?, &l_p_in_u)?, &l_sub)?;

    // Discharge the witness `p`, then contract the duplicated `K`.
    let k_goal_f = Formula::imp(k.clone(), goal.clone());
    let bp_kg = com12(&uncurry(&l_goal)?)?;
    let ex_kg = exists_elim_imp(p, &Thm::gen(p, &bp_kg), &k_goal_f)?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;

    let body_y = uncurry(&k_goal)?;
    let out = Thm::mp(
        &Thm::ax_dist(y, univ.body.clone(), Formula::imp(y_in_u.clone(), goal.clone()))?,
        &Thm::gen(y, &body_y),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(univ.body.clone(), Formula::forall(y, Formula::imp(y_in_u, goal))),
        "universe_power_closed produced an unexpected shape"
    );
    Some(out)
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
pub fn universe_no_maximal(env: &mut Env, univ: &Universe) -> Option<Thm> {
    let tu = Term::var(univ.u);
    let y = env.fresh_var();
    let ty = Term::var(y);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());

    let c3_y = Thm::ax_inst(univ.closed_pow.clone(), ty.clone())?;
    let (_, c3_y_body) = c3_y.concl().as_imp()?;
    let (_, ex_p) = c3_y_body.as_imp()?;
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
        &syl(&l_all, &Thm::ax_inst(all_sub_p, ty.clone())?)?,
        &a1i(&sub_refl, l.clone()),
    )?;
    let l_goal = syl(&hyp_and(&l_p_in_u, &l_y_in_p)?, &exists_intro_imp(p2, goal_body, tp)?)?;

    let ex_kg = exists_elim_imp(
        p,
        &Thm::gen(p, &com12(&uncurry(&l_goal)?)?),
        &Formula::imp(k.clone(), goal.clone()),
    )?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(y, univ.body.clone(), Formula::imp(y_in_u.clone(), goal.clone()))?,
        &Thm::gen(y, &uncurry(&k_goal)?),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(univ.body.clone(), Formula::forall(y, Formula::imp(y_in_u, goal))),
        "universe_no_maximal produced an unexpected shape"
    );
    Some(out)
}

/// `Ind(x, u) := x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u)` — `u` is *inductive over* `x`,
/// with the power set as successor.
pub fn inductive(env: &mut Env, pow: FnSym, x: &Term, u: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    Formula::and(
        Formula::mem(x.clone(), u.clone()),
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(ty.clone(), u.clone()),
                Formula::mem(Term::apply(pow, vec![ty]), u.clone()),
            ),
        ),
    )
}

/// `Least(x, n) := Ind(x, n) ∧ ∀w. (Ind(x, w) → ∀q. (q ∈ n → q ∈ w))` — `n` is
/// inductive over `x` and contained in every set that is.
pub fn least_inductive(env: &mut Env, pow: FnSym, x: &Term, n: &Term) -> Formula {
    let (w, q) = (env.fresh_var(), env.fresh_var());
    let (tw, tq) = (Term::var(w), Term::var(q));
    let contained = Formula::forall(
        q,
        Formula::imp(Formula::mem(tq.clone(), n.clone()), Formula::mem(tq, tw.clone())),
    );
    Formula::and(
        inductive(env, pow, x, n),
        Formula::forall(w, Formula::imp(inductive(env, pow, x, &tw), contained)),
    )
}

/// `⊢ ∀x ∃n. Least(x, n)` — **the least inductive set over `x` exists**, and so
/// induction is available.
///
/// This is `ω` (with `𝒫` as successor, and `x` in place of `∅` at the bottom).
/// Tarski's universe `u` around `x` is inductive by [`inductive_set_exists`];
/// the least inductive set is carved out of it as
/// `{q ∈ u : ∀w. (Ind(x, w) → q ∈ w)}`, which is a legitimate use of
/// [`crate::separation::separation_nonvacuous`] because `x` itself satisfies
/// the condition — so the Separation used here is the *non-vacuous* one, needs
/// no empty set, and the argument is not circular.
///
/// Its point is the third conjunct: any inductive `w` contains `n`, which is
/// induction. That is the hypothesis the recursion theorem runs on, and the
/// recursion theorem is what the remaining gap needs.
pub fn least_inductive_set_exists(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let (univ, ex_u) = tarski_at(env, x)?;
    let tu = Term::var(univ.u);
    let body = univ.body.clone();
    let closed = universe_power_closed(env, pow, pow_ax, &univ)?;

    // The condition to separate by: `hered(q) := ∀w. (Ind(x, w) → q ∈ w)`.
    let (q, w) = (env.fresh_var(), env.fresh_var());
    let (tq, tw) = (Term::var(q), Term::var(w));
    let ind_w = inductive(env, pow, &tx, &tw);
    let (ind_mem_w, ind_step_w) = split_and(&ind_w)?;
    let hered = Formula::forall(w, Formula::imp(ind_w.clone(), Formula::mem(tq.clone(), tw.clone())));

    // `⊢ hered(x)`: every inductive set contains `x` outright.
    let hered_x = Thm::gen(w, &and_left(ind_mem_w.clone(), ind_step_w.clone()));
    debug_assert_eq!(*hered_x.concl(), hered.subst(q, &tx), "hered(x) is not the right instance");

    // Separation at `u`, non-vacuously: `x ∈ u` and `hered(x)` supply the witness.
    let sep = crate::separation::separation_nonvacuous(env, q, &hered)?;
    let at_u = inst_all(&sep, std::slice::from_ref(&tu))?;
    let (ante, ex_s) = at_u.concl().as_imp()?;
    let v = env.fresh_var();
    let ante_body = open_exists(&ante, &Term::var(v))?;
    debug_assert_eq!(
        ante_body,
        Formula::and(Formula::mem(Term::var(v), tu.clone()), hered.subst(q, &Term::var(v))),
        "the non-vacuity premise is not the expected one"
    );
    let body_witness = hyp_and(&univ.body_mem(), &a1i(&hered_x, body.clone()))?;
    let body_ex_s = syl(&syl(&body_witness, &exists_intro_imp(v, ante_body, tx.clone())?)?, &at_u)?;

    // The separated set `s`, with its membership condition.
    let (s, y) = (env.fresh_var(), env.fresh_var());
    let (ts, ty) = (Term::var(s), Term::var(y));
    let sep_at = |r: &Term| Formula::and(Formula::mem(r.clone(), tu.clone()), hered.subst(q, r));
    let p_s = Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), ts.clone()), sep_at(&ty)));
    debug_assert_eq!(ex_s, Formula::exists(s, p_s.clone()), "the separated set is not as expected");

    // Work under `M := Body ∧ P(s)`.
    let m = Formula::and(body.clone(), p_s.clone());
    let m_body = and_left(body.clone(), p_s.clone());
    let m_ps = and_right(body.clone(), p_s.clone());
    let m_at = |r: &Term| -> Option<Thm> {
        syl(&m_ps, &Thm::ax_inst(p_s.clone(), r.clone())?)
    };

    // ── (i) `x ∈ s` ──────────────────────────────────────────────────────────
    let m_x_cond = hyp_and(&syl(&m_body, &univ.body_mem())?, &a1i(&hered_x, m.clone()))?;
    let m_x_in_s = hyp_mp(&crate::hyp_iff_mpr(&m_at(&tx)?)?, &m_x_cond)?;

    // ── (ii) `∀y. (y ∈ s → 𝒫y ∈ s)` ──────────────────────────────────────────
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let y_in_s = Formula::mem(ty.clone(), ts.clone());
    let n = Formula::and(m.clone(), y_in_s.clone());
    let n_m = and_left(m.clone(), y_in_s.clone());
    let n_cond = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mp(&m_at(&ty)?)?)?,
        &and_right(m.clone(), y_in_s.clone()),
    )?;
    let n_y_in_u = syl(&n_cond, &and_left(y_in_u.clone(), hered.subst(q, &ty)))?;
    let n_hered_y = syl(&n_cond, &and_right(y_in_u.clone(), hered.subst(q, &ty)))?;

    // `𝒫y ∈ u`, from the universe's power closure.
    let (_, closed_all) = closed.concl().as_imp()?;
    let body_pow_y = syl(&closed, &Thm::ax_inst(closed_all, ty.clone())?)?;
    let n_pow_in_u = hyp_mp(&syl(&n_m, &syl(&m_body, &body_pow_y)?)?, &n_y_in_u)?;

    // `hered(𝒫y)`: under `O := N ∧ Ind(x, w)`, the successor step of `Ind(x, w)`
    // carries `y ∈ w` — which `hered(y)` gives — up to `𝒫y ∈ w`.
    let o = Formula::and(n.clone(), ind_w.clone());
    let o_n = and_left(n.clone(), ind_w.clone());
    let o_ind = and_right(n.clone(), ind_w.clone());
    let o_hered_y = syl(&o_n, &n_hered_y)?;
    let o_y_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &ty), tw.clone())?, o.clone()), &o_hered_y)?,
        &o_ind,
    )?;
    let o_ind_step = syl(&o_ind, &and_right(ind_mem_w.clone(), ind_step_w.clone()))?;
    let o_pow_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(ind_step_w.clone(), ty.clone())?, o.clone()), &o_ind_step)?,
        &o_y_in_w,
    )?;
    let pow_y_in_w = Formula::mem(pow_y.clone(), tw.clone());
    let n_hered_pow = Thm::mp(
        &Thm::ax_dist(w, n.clone(), Formula::imp(ind_w.clone(), pow_y_in_w))?,
        &Thm::gen(w, &uncurry(&o_pow_in_w)?),
    )?;
    debug_assert_eq!(
        *n_hered_pow.concl(),
        Formula::imp(n.clone(), hered.subst(q, &pow_y)),
        "hered(𝒫y) was not assembled in the shape the separation condition uses"
    );

    let pow_y_in_s = Formula::mem(pow_y.clone(), ts.clone());
    let n_pow_in_s = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mpr(&m_at(&pow_y)?)?)?,
        &hyp_and(&n_pow_in_u, &n_hered_pow)?,
    )?;
    let m_all_step = Thm::mp(
        &Thm::ax_dist(y, m.clone(), Formula::imp(y_in_s, pow_y_in_s))?,
        &Thm::gen(y, &uncurry(&n_pow_in_s)?),
    )?;
    let m_ind_s = hyp_and(&m_x_in_s, &m_all_step)?;
    debug_assert_eq!(
        *m_ind_s.concl(),
        Formula::imp(m.clone(), inductive(env, pow, &tx, &ts)),
        "Ind(x, s) was not assembled in the expected shape"
    );

    // ── (iii) `∀w. (Ind(x, w) → ∀q. (q ∈ s → q ∈ w))` ────────────────────────
    let q2 = env.fresh_var();
    let tq2 = Term::var(q2);
    let q2_in_s = Formula::mem(tq2.clone(), ts.clone());
    let q2_in_w = Formula::mem(tq2.clone(), tw.clone());
    let n2 = Formula::and(m.clone(), q2_in_s.clone());
    let n2_m = and_left(m.clone(), q2_in_s.clone());
    let n2_cond = hyp_mp(
        &syl(&n2_m, &crate::hyp_iff_mp(&m_at(&tq2)?)?)?,
        &and_right(m.clone(), q2_in_s.clone()),
    )?;
    let n2_hered = syl(
        &n2_cond,
        &and_right(Formula::mem(tq2.clone(), tu.clone()), hered.subst(q, &tq2)),
    )?;
    let n2_imp =
        hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &tq2), tw.clone())?, n2.clone()), &n2_hered)?;
    // `⊢ M → (q ∈ s → (Ind(x,w) → q ∈ w))`, swapped to `M → (Ind(x,w) → …)`.
    let m_swapped = hyp_mp(
        &a1i(&com12_imp(q2_in_s.clone(), ind_w.clone(), q2_in_w.clone()), m.clone()),
        &uncurry(&n2_imp)?,
    )?;
    let mi = Formula::and(m.clone(), ind_w.clone());
    let mi_all = Thm::mp(
        &Thm::ax_dist(q2, mi, Formula::imp(q2_in_s.clone(), q2_in_w.clone()))?,
        &Thm::gen(q2, &curry(&m_swapped)?),
    )?;
    let contained = Formula::forall(q2, Formula::imp(q2_in_s, q2_in_w));
    let m_min = Thm::mp(
        &Thm::ax_dist(w, m.clone(), Formula::imp(ind_w, contained))?,
        &Thm::gen(w, &uncurry(&mi_all)?),
    )?;

    // ── Assemble, then discharge `s` and `u` ─────────────────────────────────
    let m_least = hyp_and(&m_ind_s, &m_min)?;
    debug_assert_eq!(
        *m_least.concl(),
        Formula::imp(m, least_inductive(env, pow, &tx, &ts)),
        "Least(x, s) was not assembled in the expected shape"
    );

    let nvar = env.fresh_var();
    let goal_body = least_inductive(env, pow, &tx, &Term::var(nvar));
    let goal = Formula::exists(nvar, goal_body.clone());
    let m_goal = syl(&m_least, &exists_intro_imp(nvar, goal_body, ts)?)?;

    let body_goal_f = Formula::imp(body.clone(), goal.clone());
    let ex_bg = exists_elim_imp(s, &Thm::gen(s, &com12(&uncurry(&m_goal)?)?), &body_goal_f)?;
    let body_goal = hyp_contract(&syl(&body_ex_s, &ex_bg)?)?;

    let out = exists_elim(univ.u, &ex_u, &Thm::gen(univ.u, &body_goal), &goal)?;
    debug_assert_eq!(*out.concl(), goal, "least_inductive_set_exists produced an unexpected shape");
    Some(Thm::gen(x, &out))
}

/// `⊢ ∀x ∃u. (x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u))` — **an inductive set exists**.
///
/// This is the near end of the bridge, and the point of bringing Tarski in:
/// `separation.rs` observes that closing its gap "needs a new axiom (Infinity
/// is the usual source)", and this is Infinity, derived. `x`, `𝒫x`, `𝒫𝒫x`, …
/// all lie in Tarski's universe around `x`, so the universe is inductive; see
/// [`least_inductive_set_exists`] for the `ω` inside it.
///
/// It does *not* yet give an empty set: every iterate points upwards, and
/// reaching the bottom means iterating `⋃` downwards, which needs the recursion
/// theorem. See the module documentation.
pub fn inductive_set_exists(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let (univ, ex) = tarski_at(env, x)?;
    let closed = universe_power_closed(env, pow, pow_ax, &univ)?;
    let ind = hyp_and(&univ.body_mem(), &closed)?;
    let out = Thm::mp(&exists_mono(univ.u, &Thm::gen(univ.u, &ind))?, &ex)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::exists(univ.u, inductive(env, pow, &Term::var(x), &Term::var(univ.u))),
        "inductive_set_exists produced an unexpected shape"
    );
    Some(Thm::gen(x, &out))
}
