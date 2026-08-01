//! **A1** — the introduction rule for accessibility, **unconditionally**.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc(A,R))))
//!                  → x ∈ acc(A,R))                              [acc_intro]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # This is the theorem that makes `acc` cheaper than `W`
//!
//! The corresponding W-type rule, [`crate::wtype::sup_mem`], carries
//! `closed(A,B,u)` as an antecedent and cannot drop it: `⟨a,f⟩ ∈ W` unfolds to
//! `⟨a,f⟩ ∈ u` *and* `⟨a,f⟩ ∈ S` for every closed `S ⊆ u`, and the first
//! conjunct — membership in the bound — has no other source. Discharging it is
//! what [`crate::bound`], the universe-closure chain and the `ω`-tower exist
//! for.
//!
//! Here the first conjunct is `x ∈ A`, which is *given* as a hypothesis of the
//! rule. So there is no bound hypothesis, no universe, and no
//! `crate::bound`-style companion module: this rule is unconditional as stated.
//!
//! The second conjunct is the same argument as W1's: fix a step-closed `C ⊆ A`;
//! [`crate::acc::acc_induction`] gives `acc ⊆ C`, which moves the induction
//! hypothesis `preds_in(A,R,acc,x)` to `preds_in(A,R,C,x)`, and then `C`'s own
//! closure applies at `x`.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::{
    and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, opair, syl, uncurry,
};

use super::condition::{acc_cond, preds_in, step_closed};
use super::shared::hyp_inst_mp;

/// **A1, the introduction rule.**
/// `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc(A,R)))) → x ∈ acc(A,R))`
///
/// Both halves of membership in `acc` have to be established:
///
/// * `x ∈ A` — the left conjunct of the hypothesis, verbatim;
/// * `x ∈ C` for every step-closed `C ⊆ A` — [`crate::acc::acc_induction`]
///   gives `acc ⊆ C`, so every `R`-predecessor of `x` in `A` lands in `C`, and
///   `step_closed(A,R,C)` applies at `x`.
///
/// Both `acc_ax` and `acc_ind` must **establish** what their names say: the
/// conclusions are both pinned below, and both must be
/// unconditional. The header advertises an *unconditional* introduction rule —
/// that unconditionality is the whole reason this module is cheaper than
/// [`crate::wtype`] — and a `Γ` on either premise would ride through the
/// [`crate::syl`] chain into a theorem still labelled `⊢`.
pub fn acc_intro(
    env: &mut Env,
    up: FnSym,
    acc: FnSym,
    acc_ax: &Thm,
    acc_ind: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[acc_ax, acc_ind]) {
        return None
    }
    let (av, rv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx) = (Term::var(av), Term::var(rv), Term::var(xv));
    let acc_t = Term::apply(acc, vec![ta.clone(), tr.clone()]);

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let preds_acc = preds_in(env, up, &ta, &tr, &acc_t, &tx);
    let h = Formula::and(mem_xa.clone(), preds_acc.clone());
    let h_xa = and_left(mem_xa.clone(), preds_acc.clone());
    let h_pa = and_right(mem_xa.clone(), preds_acc.clone());

    // ── Under `K := H ∧ (C ⊆ A ∧ step_closed(A,R,C))` ────────────────────────
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let sub_c_a = kernel::thm::subset(env, tc.clone(), ta.clone());
    let sc_c = step_closed(env, up, &ta, &tr, &tc);
    let g = Formula::and(sub_c_a.clone(), sc_c.clone());
    let k = Formula::and(h.clone(), g.clone());
    let k_h = and_left(h.clone(), g.clone());
    let k_g = and_right(h.clone(), g.clone());
    let k_xa = syl(&k_h, &h_xa)?;
    let k_pa = syl(&k_h, &h_pa)?;
    let k_sc = syl(&k_g, &and_right(sub_c_a, sc_c.clone()))?;

    // A2 at this `C`: `acc(A,R) ⊆ C`.
    let ind_at = inst_all(acc_ind, &[ta.clone(), tr.clone(), tc.clone()])?;
    if *ind_at.concl()
        != Formula::imp(g.clone(), kernel::thm::subset(env, acc_t.clone(), tc.clone()))
    {
        return None
    }
    let k_sub = syl(&k_g, &ind_at)?;

    // ── The induction hypothesis, moved from `acc` into `C` ──────────────────
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let mem_pair = Formula::mem(opair(up, ty.clone(), tx.clone()), tr.clone());
    // `M := (K ∧ y ∈ A) ∧ ⟨y,x⟩ ∈ R`.
    let m1 = Formula::and(k.clone(), mem_ya.clone());
    let m_m1 = and_left(m1.clone(), mem_pair.clone());
    let m_k = syl(&m_m1, &and_left(k.clone(), mem_ya.clone()))?;
    let m_ya = syl(&m_m1, &and_right(k.clone(), mem_ya.clone()))?;
    let m_r = and_right(m1, mem_pair.clone());

    let pa_at_y = Thm::ax_inst(preds_acc.clone(), ty.clone())?;
    let m_yacc = hyp_mp(&hyp_mp(&syl(&m_k, &syl(&k_pa, &pa_at_y)?)?, &m_ya)?, &m_r)?;
    let m_yc = hyp_inst_mp(&syl(&m_k, &k_sub)?, &ty, &m_yacc)?;

    let inner = Formula::imp(
        mem_ya,
        Formula::imp(mem_pair, Formula::mem(ty.clone(), tc.clone())),
    );
    let k_pc = Thm::mp(
        &Thm::ax_dist(yv, k.clone(), inner)?,
        &Thm::gen(yv, &uncurry(&uncurry(&m_yc)?)?),
    )?;
    let preds_c = preds_in(env, up, &ta, &tr, &tc, &tx);
    if *k_pc.concl() != Formula::imp(k.clone(), preds_c) {
        return None
    }

    // ── `C`'s own closure, at `x` ────────────────────────────────────────────
    let sc_at_x = Thm::ax_inst(sc_c, tx.clone())?;
    let k_xc = hyp_mp(&hyp_mp(&syl(&k_sc, &sc_at_x)?, &k_xa)?, &k_pc)?;
    let mem_xc = Formula::mem(tx.clone(), tc.clone());
    if *k_xc.concl() != Formula::imp(k, mem_xc.clone()) {
        return None
    }

    // ── Quantify over `C`, then cash the defining biconditional ──────────────
    let h_all = Thm::mp(
        &Thm::ax_dist(cv, h.clone(), Formula::imp(g, mem_xc))?,
        &Thm::gen(cv, &uncurry(&k_xc)?),
    )?;
    let cond_x = acc_cond(env, up, &ta, &tr, &tx);
    if *h_all.concl() != Formula::imp(h.clone(), cond_x.clone()) {
        return None
    }

    let at_x = inst_all(acc_ax, &[ta.clone(), tr.clone(), tx.clone()])?;
    let mem_x_acc = Formula::mem(tx, acc_t);
    if *at_x.concl() != Formula::iff(mem_x_acc.clone(), Formula::and(mem_xa, cond_x)) {
        return None
    }
    let out = syl(&hyp_and(&h_xa, &h_all)?, &iff_mpr(&at_x)?)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, mem_x_acc), "acc_intro: unexpected shape");
    Some(gen_all(&[av, rv, xv], &out))
}
