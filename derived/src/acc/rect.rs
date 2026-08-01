//! **A3** — well-founded induction over a formula.
//!
//! # Interface
//!
//! ```text
//! ind_step(φ) := ∀x. (x ∈ A → ((∀y. (y ∈ A → (⟨y,x⟩ ∈ R →
//!                       (y ∈ acc(A,R) ∧ φ(y))))) → φ(x)))          [ind_step]
//!
//! ⊢ ind_step(φ) → ∀z. (z ∈ acc(A,R) → φ(z))                        [acc_rect]
//! ```
//!
//! [`Params`] carries the free variables the caller has chosen for `A` and `R`,
//! so that the formula `φ` the caller supplies and the one this file builds are
//! literally the same. Callers need none of the derivation below.
//!
//! **Unconditional.** [`crate::wtype::w_rect`] carries `closed(A,B,u)` as an
//! extra antecedent, discharged only at a universe. There is no analogue here:
//! see [`crate::acc::acc_intro`].
//!
//! # It is a scheme, and it is [`crate::acc::acc_induction`] in disguise
//!
//! `φ` is an arbitrary formula of the ambient language, not a set, so this is a
//! **scheme**: one theorem per `φ`, built on demand. The argument is to apply
//! A2 to the set
//!
//! ```text
//! C := { z ∈ acc(A,R) : φ(z) }
//! ```
//!
//! carved out of `acc(A,R)` by one Separation. `C ⊆ A` holds because
//! `acc(A,R) ⊆ A`, and `step_closed(A,R,C)` is precisely [`ind_step`]. A2 then
//! gives `acc ⊆ C`, i.e. `φ` on all of `acc`.
//!
//! **`C` is carved out of `acc`, not out of `A`, and that ordering is the one
//! real trap** — the same trap as in [`crate::wtype::w_rect`]. Proving
//! `step_closed(A,R,C)` needs `x ∈ acc` for the point being added, and the only
//! route to it is [`crate::acc::acc_intro`] from `preds_in(A,R,acc,x)`, which is
//! available only because `C`'s defining condition has `z ∈ acc` as a conjunct.
//! That same conjunct is what puts `y ∈ acc(A,R)` into the induction
//! hypothesis, which is exactly the extra argument Lean's `Acc.rec` gives its
//! minor premise.
//!
//! # Why the induction hypothesis has that shape
//!
//! Lean's eliminator is
//!
//! ```text
//! Acc.rec : (∀ x (h : ∀ y, r y x → Acc r y),
//!              (∀ y (hy : r y x), C y (h y hy)) → C x (Acc.intro x h))
//!           → ∀ a (h : Acc r a), C a h
//! ```
//!
//! — the minor premise receives both `h`, the accessibility of every
//! predecessor, and the recursive results. Under the thesis's interpretation
//! (`⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r⟧)]`, thesis.txt:2126) a proof term is `•`
//! and the two collapse into the single conjunction `y ∈ acc(A,R) ∧ φ(y)`. A
//! scheme that offered only `φ(y)` would be strictly weaker and would not
//! interpret `Acc.rec`.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::funcs::separation_full;
use crate::{
    a1i, and_left, and_right, forall_mono, hyp_and, hyp_mp, iff_mp, iff_mpr,
    imp_mono_r, inst_all, opair, syl, uncurry,
};

use super::apparatus::Acc;
use super::condition::{preds_in, step_closed};
use super::shared::hyp_inst_mp;

/// The minor premise of well-founded induction, as a formula:
///
/// ```text
/// ∀x. (x ∈ A → ((∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ φ(y))))) → φ(x)))
/// ```
///
/// `zv` is the variable `phi` speaks about; `φ(t)` is `phi[t/zv]`.
pub fn ind_step(
    env: &mut Env,
    ac: &Acc,
    acc_t: &Term,
    a: &Term,
    r: &Term,
    zv: FreeVar,
    phi: &Formula,
) -> Formula {
    let up = ac.sets.up;
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let hyp = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), a.clone()),
            Formula::imp(
                Formula::mem(opair(up, ty.clone(), tx.clone()), r.clone()),
                Formula::and(Formula::mem(ty.clone(), acc_t.clone()), phi.subst(zv, &ty)),
            ),
        ),
    );
    Formula::forall(
        xv,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::imp(hyp, phi.subst(zv, &tx)),
        ),
    )
}

/// The two parameter variables an accessibility instance is taken over: the
/// carrier `A` and the relation `R`.
///
/// Bundled because they always travel together — `acc(A,R)`,
/// `step_closed(A,R,C)` and the subset `{z ∈ acc(A,R) : φ(z)}` all mention
/// both — and because passing them separately is exactly how a derivation ends
/// up quantifying over the wrong variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// The carrier.
    pub a: FreeVar,
    /// The relation.
    pub r: FreeVar,
}

/// **The capstone: well-founded induction over a formula.**
///
/// ```text
/// ⊢ (∀x. (x ∈ A → ((∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ φ(y))))) → φ(x))))
///     → ∀z. (z ∈ acc(A,R) → φ(z))
/// ```
///
/// `φ` is an arbitrary formula, so this cannot be a theorem of the first-order
/// signature: like [`crate::wtype::w_rect`] it is a *construction taking a
/// formula*, and it mints one fresh symbol (for `C`) per call. `zv` is the
/// variable `φ` speaks about; `params` must cover every free variable of `φ`
/// and must include `ar.a` and `ar.r`, since `C` mentions `acc(A,R)`.
pub fn acc_rect(
    env: &mut Env,
    ac: &Acc,
    params: &[FreeVar],
    ar: Params,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Thm> {
    let (av, rv) = (ar.a, ar.r);
    if !params.contains(&av) || !params.contains(&rv) || params.contains(&zv) {
        return None
    }
    let up = ac.sets.up;
    let (ta, tr, tz) = (Term::var(av), Term::var(rv), Term::var(zv));
    let acc_t = ac.of(ta.clone(), tr.clone());
    let args: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();

    // ── C := { z ∈ acc(A,R) : φ(z) } ────────────────────────────────────────
    let existence = separation_full(env, zv, phi, &acc_t, &ac.empty_ax)?;
    let mem_zacc = Formula::mem(tz.clone(), acc_t.clone());
    let guard = Formula::and(mem_zacc.clone(), phi.clone());
    let (c_sym, c_ax) = crate::define_by_membership(env, params, &existence, zv, &guard)?;
    let c_t = Term::apply(c_sym, args.clone());
    let c_at = inst_all(&c_ax, &args)?;

    // `t ∈ C ↔ (t ∈ acc(A,R) ∧ φ(t))`, insisted on rather than assumed.
    let c_iff = |t: &Term| -> Option<Thm> {
        let x = inst_all(&c_at, std::slice::from_ref(t))?;
        let want = Formula::iff(
            Formula::mem(t.clone(), c_t.clone()),
            Formula::and(Formula::mem(t.clone(), acc_t.clone()), phi.subst(zv, t)),
        );
        if *x.concl() != want {
            return None
        }
        Some(x)
    };

    let c_z = c_iff(&tz)?;
    let z_in_acc = syl(&iff_mp(&c_z)?, &and_left(mem_zacc.clone(), phi.clone()))?;
    let sub_at = inst_all(&ac.acc_subset, &[ta.clone(), tr.clone(), tz.clone()])?;
    let c_sub_a = Thm::gen(zv, &syl(&z_in_acc, &sub_at)?);
    if *c_sub_a.concl() != kernel::thm::subset(env, c_t.clone(), ta.clone()) {
        return None
    }

    // ── H := the minor premise, and the point `x` being added to `C` ────────
    let ih = ind_step(env, ac, &acc_t, &ta, &tr, zv, phi);
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let preds_c = preds_in(env, up, &ta, &tr, &c_t, &tx);

    let front = Formula::and(ih.clone(), mem_xa.clone());
    let k = Formula::and(front.clone(), preds_c.clone());
    let k_front = and_left(front.clone(), preds_c.clone());
    let k_ih = syl(&k_front, &and_left(ih.clone(), mem_xa.clone()))?;
    let k_xa = syl(&k_front, &and_right(ih.clone(), mem_xa.clone()))?;
    let k_pc = and_right(front, preds_c.clone());

    // ── Every `R`-predecessor of `x` in `A` is accessible and satisfies `φ` ──
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let mem_pair = Formula::mem(opair(up, ty.clone(), tx.clone()), tr.clone());
    // `M := (K ∧ y ∈ A) ∧ ⟨y,x⟩ ∈ R`.
    let m1 = Formula::and(k.clone(), mem_ya.clone());
    let m_m1 = and_left(m1.clone(), mem_pair.clone());
    let m_k = syl(&m_m1, &and_left(k.clone(), mem_ya.clone()))?;
    let m_ya = syl(&m_m1, &and_right(k.clone(), mem_ya.clone()))?;
    let m_r = and_right(m1, mem_pair.clone());

    let pc_at_y = Thm::ax_inst(preds_c.clone(), ty.clone())?;
    let m_yc = hyp_mp(&hyp_mp(&syl(&m_k, &syl(&k_pc, &pc_at_y)?)?, &m_ya)?, &m_r)?;

    let phi_y = phi.subst(zv, &ty);
    let mem_yacc = Formula::mem(ty.clone(), acc_t.clone());
    let m_both = syl(&m_yc, &iff_mp(&c_iff(&ty)?)?)?;
    let m_yacc_thm = syl(&m_both, &and_left(mem_yacc.clone(), phi_y.clone()))?;

    let dist = |inner: Formula, body: &Thm| -> Option<Thm> {
        Thm::mp(
            &Thm::ax_dist(yv, k.clone(), inner)?,
            &Thm::gen(yv, &uncurry(&uncurry(body)?)?),
        )
    };
    let k_pacc = dist(
        Formula::imp(
            mem_ya.clone(),
            Formula::imp(mem_pair.clone(), mem_yacc.clone()),
        ),
        &m_yacc_thm,
    )?;
    let k_ihyp = dist(
        Formula::imp(
            mem_ya,
            Formula::imp(mem_pair, Formula::and(mem_yacc, phi_y)),
        ),
        &m_both,
    )?;
    if *k_pacc.concl() != Formula::imp(k.clone(), preds_in(env, up, &ta, &tr, &acc_t, &tx)) {
        return None
    }

    // ── so `x ∈ acc` by A1, and `φ(x)` by the minor premise ─────────────────
    let intro_at = inst_all(&ac.acc_intro, &[ta.clone(), tr.clone(), tx.clone()])?;
    let k_xacc = syl(&hyp_and(&k_xa, &k_pacc)?, &intro_at)?;
    if *k_xacc.concl() != Formula::imp(k.clone(), Formula::mem(tx.clone(), acc_t.clone())) {
        return None
    }

    let k_ih_x = hyp_inst_mp(&k_ih, &tx, &k_xa)?;
    let k_phix = hyp_mp(&k_ih_x, &k_ihyp)?;
    let k_xc = syl(&hyp_and(&k_xacc, &k_phix)?, &iff_mpr(&c_iff(&tx)?)?)?;

    // ── which is `step_closed(A,R,C)` ───────────────────────────────────────
    let inner = Formula::imp(
        mem_xa,
        Formula::imp(preds_c, Formula::mem(tx.clone(), c_t.clone())),
    );
    let ih_closed = Thm::mp(
        &Thm::ax_dist(xv, ih.clone(), inner)?,
        &Thm::gen(xv, &uncurry(&uncurry(&k_xc)?)?),
    )?;
    let cl_c = step_closed(env, up, &ta, &tr, &c_t);
    if *ih_closed.concl() != Formula::imp(ih.clone(), cl_c) {
        return None
    }

    // ── A2 at `C`, then read `φ` off the membership ─────────────────────────
    let ind_at = inst_all(&ac.acc_induction, &[ta.clone(), tr.clone(), c_t.clone()])?;
    let ih_acc_c = syl(&hyp_and(&a1i(&c_sub_a, ih.clone()), &ih_closed)?, &ind_at)?;

    let c_phi = syl(&iff_mp(&c_z)?, &and_right(mem_zacc.clone(), phi.clone()))?;
    let fm = forall_mono(zv, &Thm::gen(zv, &imp_mono_r(&c_phi, mem_zacc.clone())?))?;
    let out = syl(&ih_acc_c, &fm)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(ih, Formula::forall(zv, Formula::imp(mem_zacc, phi.clone()))),
        "acc_rect: unexpected shape"
    );
    Some(out)
}
