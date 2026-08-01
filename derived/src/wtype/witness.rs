//! Non-vacuity: a W-type with something in it, and a bound that is closed.
//!
//! # Interface
//!
//! ```text
//! ⊢ ⟨•,∅⟩ ∈ W(1, ∅, {⟨•,∅⟩})                            [unit_wtype_inhabited]
//! ⊢ closed(1, ∅, {⟨•,∅⟩})                                  [unit_bound_closed]
//! ```
//!
//! Both are closed theorems at a fixed instance — no free variables, no
//! antecedents. Callers need none of the derivations below.
//!
//! # Why both, and why either is needed
//!
//! Every lemma in [`crate::wtype`] is trivially true when `W(A,B,u)` is empty,
//! so without a witness the module proves nothing at all.
//! [`unit_wtype_inhabited`] is that witness: the unit type as a W-type, a
//! one-element W-type needing no recursion. `∅` serves as the constant-empty
//! family and as the empty function at once, via [`super::app_of_empty`] and
//! [`super::empty_is_a_function`].
//!
//! There is a **second** way the development could have said nothing: W1, W3
//! and [`super::w_rect`] all carry `closed(A,B,u)` as an antecedent, and an
//! antecedent no set ever satisfies makes a theorem vacuous just as surely as an
//! empty `W`. [`unit_bound_closed`] discharges that too, at the same instance,
//! so W1 there becomes an unconditional typing rule for `sup`.
//!
//! It has a second use now that [`crate::bound`] proves the general statement:
//! `tests/bound.rs` checks that
//! [`crate::bound::universe_closed`]'s conclusion, instantiated at `A := 1`,
//! `B := ∅`, `u := {⟨•,∅⟩}`, is **literally** the formula this hand-built
//! instance proves — so the general theorem and the worked instance cannot have
//! drifted apart, and neither is a look-alike of the other.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::sums::Sums;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, hyp_mp, iff_mpr, inst_all, opair, syl,
    uncurry,
};

use super::shared::apply_closed;
use super::condition::{closed, w_cond};

/// `⊢ ⟨•,∅⟩ ∈ W(1, ∅, {⟨•,∅⟩})` — **the unit type as a W-type**, and the only
/// thing in this module that rules out the whole development being vacuous.
///
/// Every other theorem here is trivially true when `W(A,B,u)` is empty, so
/// without this one the module proves nothing. The instance is the smallest
/// possible: one constructor, no recursive arguments, no recursion needed to
/// bound it.
///
/// * `A := 1 = {∅}`, so there is exactly one constructor, `•`;
/// * `B := ∅`, the constant-empty family — [`crate::wtype::app_of_empty`] gives
///   `app(∅,a) = ∅` for every `a`, and `closed` only ever mentions `B` through
///   `app(B,a)`, so `∅` *is* `λ_. 0` as far as anything here can tell;
/// * `u := {⟨•,∅⟩}`, the bound, supplied outright rather than constructed.
///
/// The witness is `⟨•,∅⟩`: it is in `u` by definition of the singleton, and it
/// is in every closed `S ⊆ u` because `∅ ∈ fs(0,S)` ([`crate::wtype::empty_is_a_function`])
/// so `closed(1,∅,S)` applies at `a := •`, `f := ∅`.
pub fn unit_wtype_inhabited(
    env: &mut Env,
    s: &Sums,
    w: FnSym,
    w_ax: &Thm,
    empty_fun: &Thm,
    app_empty: &Thm,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let e = Term::apply(s.ap.empty, vec![]);
    let one = s.unit();
    let sup0 = opair(up, e.clone(), e.clone());
    let u = crate::singleton(up, sup0.clone());

    // ── ⟨•,∅⟩ ∈ u, membership in its own singleton ──────────────────────────
    let ms = inst_all(&s.ap.mem_sing, &[sup0.clone(), sup0.clone()])?;
    let in_u = Thm::mp(&iff_mpr(&ms)?, &Thm::eq_refl(sup0.clone()))?;

    // ── ∅ ∈ fs(B(•), S), i.e. the empty function into an arbitrary `S` ──────
    let sv = env.fresh_var();
    let ts = Term::var(sv);
    let fibre = s.ap.apply(e.clone(), e.clone());
    let ef = inst_all(empty_fun, std::slice::from_ref(&ts))?;
    let ae = inst_all(app_empty, std::slice::from_ref(&e))?;
    let ae_symm = crate::eq_symm(env, &ae)?;
    let x = env.fresh_var();
    let leib = Thm::eq_leibniz(
        e.clone(),
        fibre,
        x,
        Formula::mem(e.clone(), s.fs.of(Term::var(x), ts.clone())),
    );
    let in_fs = Thm::mp(&Thm::mp(&leib, &ae_symm)?, &ef)?;

    // ── Every closed `S ⊆ u` contains it ────────────────────────────────────
    let sub_s_u = kernel::thm::subset(env, ts.clone(), u.clone());
    let cl_s = closed(env, s, &one, &e, &ts);
    let g = Formula::and(sub_s_u.clone(), cl_s.clone());
    let g_sup = apply_closed(
        &and_right(sub_s_u, cl_s.clone()),
        &a1i(&s.unit_mem, g.clone()),
        &a1i(&in_fs, g),
        &cl_s,
        &e,
        &e,
    )?;
    let all = Thm::gen(sv, &g_sup);

    let cond = w_cond(env, s, &one, &e, &u, &sup0);
    if *all.concl() != cond {
        return None
    }

    let at = inst_all(w_ax, &[one.clone(), e.clone(), u.clone(), sup0.clone()])?;
    let goal = Formula::mem(sup0.clone(), Term::apply(w, vec![one, e, u.clone()]));
    if *at.concl()
        != Formula::iff(goal.clone(), Formula::and(Formula::mem(sup0, u), cond))
    {
        return None
    }
    let out = Thm::mp(&iff_mpr(&at)?, &and_intro(&in_u, &all))?;
    debug_assert_eq!(*out.concl(), goal, "unit_wtype_inhabited: unexpected shape");
    Some(out)
}

/// `⊢ closed(1, ∅, {⟨•,∅⟩})` — **the bound hypothesis is satisfiable**.
///
/// W1, W3 and [`crate::wtype::w_rect`] all carry `closed(A,B,u)` as an antecedent, so they
/// would be vacuous if no `u` were ever closed. This exhibits one, at the same
/// instance [`unit_wtype_inhabited`] uses — by hand, from the axioms, with no
/// universe anywhere. [`crate::bound::universe_closed`] proves the general
/// statement, and `tests/bound.rs` checks that its conclusion at these three
/// terms is precisely the formula proved here: the general theorem and the
/// worked instance are about the same predicate.
///
/// The argument is that the instance is completely rigid: `a ∈ 1` forces
/// `a = •` ([`crate::sums::unit_eta`]), `app(∅,a) = ∅` ([`crate::wtype::app_of_empty`]) so
/// `f ∈ fs(∅, u)` forces `f = ∅` ([`crate::wtype::empty_funspace`]), and `⟨•,∅⟩` is the sole
/// member of `u`.
pub fn unit_bound_closed(
    env: &mut Env,
    s: &Sums,
    empty_fs: &Thm,
    app_empty: &Thm,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let e = Term::apply(s.ap.empty, vec![]);
    let one = s.unit();
    let sup0 = opair(up, e.clone(), e.clone());
    let u = crate::singleton(up, sup0.clone());

    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));
    let fibre = s.ap.apply(e.clone(), tpa.clone());
    let mem_a1 = Formula::mem(tpa.clone(), one.clone());
    let mem_f = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), u.clone()));
    let h = Formula::and(mem_a1.clone(), mem_f.clone());
    let h_a1 = and_left(mem_a1.clone(), mem_f.clone());
    let h_f = and_right(mem_a1.clone(), mem_f.clone());

    // ── a = •, and f = ∅ once the domain has been rewritten to `∅` ──────────
    let h_a_pt = syl(&h_a1, &inst_all(&s.unit_eta, std::slice::from_ref(&tpa))?)?;
    let ae = inst_all(app_empty, std::slice::from_ref(&tpa))?;
    let w1 = env.fresh_var();
    let carry = Thm::eq_leibniz(
        fibre,
        e.clone(),
        w1,
        Formula::mem(tpf.clone(), s.fs.of(Term::var(w1), u.clone())),
    );
    let h_f0 = hyp_mp(&a1i(&Thm::mp(&carry, &ae)?, h.clone()), &h_f)?;
    let h_f_e = syl(&h_f0, &inst_all(empty_fs, &[u.clone(), tpf.clone()])?)?;

    // ── ⟨•,∅⟩ ∈ u, rewritten along `• = a` and then `∅ = f` ─────────────────
    let ms = inst_all(&s.ap.mem_sing, &[sup0.clone(), sup0.clone()])?;
    let in_u = Thm::mp(&iff_mpr(&ms)?, &Thm::eq_refl(sup0))?;

    let h_pt_a = syl(&h_a_pt, &eq_symm_imp(env, tpa.clone(), e.clone()))?;
    let w2 = env.fresh_var();
    let l1 = Thm::eq_leibniz(
        e.clone(),
        tpa.clone(),
        w2,
        Formula::mem(opair(up, Term::var(w2), e.clone()), u.clone()),
    );
    let h_ae_u = hyp_mp(&hyp_mp(&a1i(&l1, h.clone()), &h_pt_a)?, &a1i(&in_u, h.clone()))?;

    let h_e_f = syl(&h_f_e, &eq_symm_imp(env, tpf.clone(), e.clone()))?;
    let w3 = env.fresh_var();
    let l2 = Thm::eq_leibniz(
        e.clone(),
        tpf.clone(),
        w3,
        Formula::mem(opair(up, tpa.clone(), Term::var(w3)), u.clone()),
    );
    let h_goal = hyp_mp(&hyp_mp(&a1i(&l2, h.clone()), &h_e_f)?, &h_ae_u)?;

    // ── Reassemble into `closed`'s own shape ────────────────────────────────
    let x_f = Formula::imp(mem_f, Formula::mem(opair(up, tpa, tpf), u.clone()));
    let out = Thm::gen(
        pa,
        &Thm::mp(
            &Thm::ax_dist(pf, mem_a1, x_f)?,
            &Thm::gen(pf, &uncurry(&h_goal)?),
        )?,
    );
    if *out.concl() != closed(env, s, &one, &e, &u) {
        return None
    }
    Some(out)
}
