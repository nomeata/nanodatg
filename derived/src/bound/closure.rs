//! **Step 4** — `closed(A,B,u)` for an arbitrary universe.
//!
//! # Interface
//!
//! ```text
//! fibres_in(A,B,u) := ∀a. (a ∈ A → app(B,a) ∈ u)                    [fibres_in]
//!
//! ⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ fibres_in(A,B,u)))
//!                 → closed(A,B,u))                            [universe_closed]
//! ```
//!
//! where `closed` is [`crate::wtype::closed`], the W-type's bound hypothesis.
//! Callers need none of the derivation below.
//!
//! # What is left to do at this point
//!
//! Everything hard is already proved. `closed(A,B,u)` asks that `⟨a,f⟩ ∈ u`
//! whenever `a ∈ A` and `f ∈ fs(app(B,a), u)`, so: `app(B,a) ∈ u` is the
//! hypothesis [`fibres_in`], [`super::funspace_mem_universe`] puts `f` into `u`,
//! `a ∈ u` follows from `a ∈ A ∈ u` by `C₁`, and
//! [`super::universe_opair`] pairs them. The file is long only because each of
//! those four facts has to be threaded under the ambient conjunction.
//!
//! # Non-vacuity
//!
//! `tests/bound.rs` checks the conclusion of [`universe_closed`], instantiated
//! at `1`, `∅` and `{⟨•,∅⟩}`, against the formula
//! [`crate::wtype::unit_bound_closed`] proves **by hand** from the axioms with
//! no universe anywhere — so the general theorem and the worked instance are
//! about the same predicate, and neither is a look-alike of the other.

use kernel::{Env, Formula, Term, Thm};
use crate::sums::Sums;
use crate::universe::is_universe;
use crate::wtype::closed;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, inst_all, opair, syl, uncurry};

use super::shared::hyp_inst_mp;

/// `∀a. (a ∈ A → app(B,a) ∈ u)` — "every fibre of the family `B` is a member
/// of `u`", as a formula.
///
/// The typing side condition on the family. Together with `A ∈ u` it is what
/// replaces `closed(A,B,u)` everywhere downstream, and it is a condition on
/// `A` and `B` alone — no quantification over function spaces, and nothing a
/// caller does not already have when it writes down a W-type.
pub fn fibres_in(env: &mut Env, s: &Sums, a: &Term, b: &Term, u: &Term) -> Formula {
    let av = env.fresh_var();
    let ta = Term::var(av);
    Formula::forall(
        av,
        Formula::imp(
            Formula::mem(ta.clone(), a.clone()),
            Formula::mem(s.ap.apply(b.clone(), ta), u.clone()),
        ),
    )
}

/// `⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a. (a ∈ A → app(B,a) ∈ u))) → closed(A,B,u))`
/// — **a universe is closed under `sup`**, which is the W-type's bound
/// hypothesis discharged.
///
/// Given `a ∈ A` and `f ∈ fs(B(a), u)`: `B(a) ∈ u` by the family condition, so
/// `f ∈ u` by [`crate::bound::funspace_mem_universe`]; `a ∈ u` because `A ∈ u` and `u` is
/// transitive; so `⟨a,f⟩ ∈ u` by [`crate::bound::universe_opair`]. That is the whole
/// argument — the three steps of the module documentation, in order.
///
/// This is *not* directly applicable to `U(c)`, whose `is_universe` is not
/// available; see [`crate::bound::least_universe_closed`] for the transfer.
pub fn universe_closed(
    env: &mut Env,
    s: &Sums,
    mem_mem: &Thm,
    pair: &Thm,
    fs_mem: &Thm,
) -> Option<Thm> {
    let up = s.ap.sets.up;
    let (uv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(uv), Term::var(av), Term::var(bv));
    let (pav, pfv) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pav), Term::var(pfv));

    let univ_u = is_universe(env, &tu);
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let fam = Formula::forall(
        pav,
        Formula::imp(
            Formula::mem(tpa.clone(), ta.clone()),
            Formula::mem(s.ap.apply(tb.clone(), tpa.clone()), tu.clone()),
        ),
    );
    if fam != fibres_in(env, s, &ta, &tb, &tu) {
        return None
    }
    let rest = Formula::and(a_in_u.clone(), fam.clone());
    let h = Formula::and(univ_u.clone(), rest.clone());
    let h_univ = and_left(univ_u.clone(), rest.clone());
    let h_rest = and_right(univ_u, rest);
    let h_a = syl(&h_rest, &and_left(a_in_u.clone(), fam.clone()))?;
    let h_fam = syl(&h_rest, &and_right(a_in_u, fam))?;

    // ── `K := (H ∧ a ∈ A) ∧ f ∈ fs(B(a), u)` ────────────────────────────────
    let fibre = s.ap.apply(tb.clone(), tpa.clone());
    let mem_aa = Formula::mem(tpa.clone(), ta.clone());
    let mem_f = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), tu.clone()));
    let pair_t = opair(up, tpa.clone(), tpf.clone());
    let front = Formula::and(h.clone(), mem_aa.clone());
    let k = Formula::and(front.clone(), mem_f.clone());

    let k_front = and_left(front.clone(), mem_f.clone());
    let k_h = syl(&k_front, &and_left(h.clone(), mem_aa.clone()))?;
    let k_aa = syl(&k_front, &and_right(h.clone(), mem_aa.clone()))?;
    let k_f = and_right(front.clone(), mem_f.clone());
    let k_univ = syl(&k_h, &h_univ)?;

    // `B(a) ∈ u`, then `f ∈ u`.
    let k_fibre = hyp_inst_mp(&syl(&k_h, &h_fam)?, &tpa, &k_aa)?;
    let fs_at = inst_all(fs_mem, &[tu.clone(), fibre.clone(), tpf.clone()])?;
    if *fs_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(Formula::mem(fibre.clone(), tu.clone()), mem_f.clone()),
            ),
            Formula::mem(tpf.clone(), tu.clone()),
        )
    {
        return None
    }
    let k_f_u = hyp_mp(&a1i(&fs_at, k.clone()), &hyp_and(&k_univ, &hyp_and(&k_fibre, &k_f)?)?)?;

    // `a ∈ u` by transitivity, then the pair.
    let mm_at = inst_all(mem_mem, &[tu.clone(), ta.clone(), tpa.clone()])?;
    if *mm_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(Formula::mem(ta.clone(), tu.clone()), mem_aa.clone()),
            ),
            Formula::mem(tpa.clone(), tu.clone()),
        )
    {
        return None
    }
    let k_a_u = hyp_mp(
        &a1i(&mm_at, k.clone()),
        &hyp_and(&k_univ, &hyp_and(&syl(&k_h, &h_a)?, &k_aa)?)?,
    )?;

    let op_at = inst_all(pair, &[tu.clone(), tpa.clone(), tpf.clone()])?;
    if *op_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(tpa.clone(), tu.clone()),
                    Formula::mem(tpf.clone(), tu.clone()),
                ),
            ),
            Formula::mem(pair_t.clone(), tu.clone()),
        )
    {
        return None
    }
    let k_goal =
        hyp_mp(&a1i(&op_at, k.clone()), &hyp_and(&k_univ, &hyp_and(&k_a_u, &k_f_u)?)?)?;

    // ── Reassemble into `closed`'s own shape ────────────────────────────────
    let x_f = Formula::imp(mem_f.clone(), Formula::mem(pair_t, tu.clone()));
    let front_all = Thm::mp(
        &Thm::ax_dist(pfv, front.clone(), x_f.clone())?,
        &Thm::gen(pfv, &uncurry(&k_goal)?),
    )?;
    let inner = Formula::imp(mem_aa, Formula::forall(pfv, x_f));
    let out = Thm::mp(
        &Thm::ax_dist(pav, h.clone(), inner)?,
        &Thm::gen(pav, &uncurry(&front_all)?),
    )?;

    if *out.concl() != Formula::imp(h, closed(env, s, &ta, &tb, &tu)) {
        return None
    }
    Some(gen_all(&[uv, av, bv], &out))
}
