//! **Step 4 — W1**: `sup`'s typing rule.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u. (closed(A,B,u) →
//!       ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W(A,B,u)) → ⟨a,f⟩ ∈ W(A,B,u))))    [sup_mem]
//! ```
//!
//! Callers need none of the derivation below; at `u := U(c)` the antecedent is
//! discharged and the rule is unconditional, as [`crate::bound::sup_mem_at`].
//!
//! # Why this is the hard half of the intersection
//!
//! `⟨a,f⟩ ∈ W` unfolds to `⟨a,f⟩ ∈ u` **and** `⟨a,f⟩ ∈ S` for *every* closed
//! `S ⊆ u`, so the goal is universally quantified over `S` and the hypothesis
//! `f ∈ fs(B(a), W)` is about `W`, not about `S`. The bridge is
//! [`super::fs_mono`] over `W ⊆ S` — which is exactly
//! [`super::w_induction`] — moving `f` into `fs(B(a), S)` so that `S`'s own
//! closure hypothesis applies. The first conjunct, `⟨a,f⟩ ∈ u`, is the
//! antecedent `closed(A,B,u)` used at `S := u`, which is the only thing it is
//! ever used for and the reason it cannot be dropped.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, iff_mpr, imp_mono_r, inst_all, opair, syl,
    uncurry,
};

use super::shared::apply_closed;
use super::condition::{closed, w_cond};

/// **W1, the typing rule for `sup`.**
/// `⊢ ∀A ∀B ∀u. (closed(A,B,u) → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W(A,B,u)) → ⟨a,f⟩ ∈ W(A,B,u))))`
///
/// The antecedent `closed(A,B,u)` is where the bound hypothesis does its work:
/// `W(A,B,u)` is a subset of `u`, and if `u` itself were not closed there would
/// be nothing to put `⟨a,f⟩` into. For an arbitrary parameter `u` it is not
/// removable; **at a universe it is discharged** —
/// [`crate::bound::sup_mem_at`] is this rule at `u := U(c)` with the antecedent
/// gone, and [`crate::bound::least_universe_closed`] is what removes it.
///
/// Both halves of membership in `W` have to be established:
///
/// * `⟨a,f⟩ ∈ u` — `W ⊆ u`, so [`crate::wtype::fs_mono`] lifts `f ∈ fs(B(a), W)` to
///   `f ∈ fs(B(a), u)`, and `closed(A,B,u)` applies;
/// * `⟨a,f⟩ ∈ S` for every closed `S ⊆ u` — [`crate::wtype::w_induction`] gives `W ⊆ S`, so
///   [`crate::wtype::fs_mono`] lifts the same `f` to `fs(B(a), S)` and `closed(A,B,S)`
///   applies.
pub fn sup_mem(
    env: &mut Env,
    s: &Sums,
    w: FnSym,
    w_ax: &Thm,
    w_sub: &Thm,
    w_ind: &Thm,
    fs_mono_thm: &Thm,
) -> Option<Thm> {
    let (av, bv, uv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (ta, tb, tu) = (Term::var(av), Term::var(bv), Term::var(uv));
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));

    let w_t = Term::apply(w, vec![ta.clone(), tb.clone(), tu.clone()]);
    let fibre = s.ap.apply(tb.clone(), tpa.clone());
    let cl_u = closed(env, s, &ta, &tb, &tu);
    let mem_aa = Formula::mem(tpa.clone(), ta.clone());
    let mem_f = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), w_t.clone()));
    let pair = opair(s.ap.sets.up, tpa.clone(), tpf.clone());

    let front = Formula::and(cl_u.clone(), mem_aa.clone());
    let h = Formula::and(front.clone(), mem_f.clone());
    let h_front = and_left(front.clone(), mem_f.clone());
    let h_cl = syl(&h_front, &and_left(cl_u.clone(), mem_aa.clone()))?;
    let h_aa = syl(&h_front, &and_right(cl_u.clone(), mem_aa.clone()))?;
    let h_f = and_right(front, mem_f.clone());

    // ── (i) ⟨a,f⟩ ∈ u, via `W ⊆ u` and `closed(A,B,u)` ───────────────────────
    let wsub_at = inst_all(w_sub, &[ta.clone(), tb.clone(), tu.clone()])?;
    if *wsub_at.concl() != kernel::thm::subset(env, w_t.clone(), tu.clone()) {
        return None
    }
    let mono_u =
        inst_all(fs_mono_thm, &[fibre.clone(), w_t.clone(), tu.clone(), tpf.clone()])?;
    let h_f_u = syl(&hyp_and(&h_f, &a1i(&wsub_at, h.clone()))?, &mono_u)?;

    let h_pair_u = apply_closed(&h_cl, &h_aa, &h_f_u, &cl_u, &tpa, &tpf)?;
    if *h_pair_u.concl() != Formula::imp(h.clone(), Formula::mem(pair.clone(), tu.clone())) {
        return None
    }

    // ── (ii) ⟨a,f⟩ ∈ S for every closed S ⊆ u, via W2 ────────────────────────
    let sv = env.fresh_var();
    let ts = Term::var(sv);
    let sub_s_u = kernel::thm::subset(env, ts.clone(), tu.clone());
    let cl_s = closed(env, s, &ta, &tb, &ts);
    let g = Formula::and(sub_s_u.clone(), cl_s.clone());

    let k_h = and_left(h.clone(), g.clone());
    let k_g = and_right(h.clone(), g.clone());

    let ind_at = inst_all(w_ind, &[ta.clone(), tb.clone(), tu.clone(), ts.clone()])?;
    if *ind_at.concl()
        != Formula::imp(g.clone(), kernel::thm::subset(env, w_t.clone(), ts.clone()))
    {
        return None
    }
    let k_sub = syl(&k_g, &ind_at)?;
    let mono_s =
        inst_all(fs_mono_thm, &[fibre.clone(), w_t.clone(), ts.clone(), tpf.clone()])?;
    let k_f_s = syl(&hyp_and(&syl(&k_h, &h_f)?, &k_sub)?, &mono_s)?;

    let k_cls = syl(&k_g, &and_right(sub_s_u, cl_s.clone()))?;
    let k_aa = syl(&k_h, &h_aa)?;
    let k_pair_s = apply_closed(&k_cls, &k_aa, &k_f_s, &cl_s, &tpa, &tpf)?;

    let h_all = Thm::mp(
        &Thm::ax_dist(
            sv,
            h.clone(),
            Formula::imp(g, Formula::mem(pair.clone(), ts.clone())),
        )?,
        &Thm::gen(sv, &uncurry(&k_pair_s)?),
    )?;
    let cond_pair = w_cond(env, s, &ta, &tb, &tu, &pair);
    if *h_all.concl() != Formula::imp(h.clone(), cond_pair.clone()) {
        return None
    }

    // ── Both halves, cashed through the defining biconditional ───────────────
    let at_pair = inst_all(w_ax, &[ta.clone(), tb.clone(), tu.clone(), pair.clone()])?;
    let mem_pair_w = Formula::mem(pair.clone(), w_t);
    if *at_pair.concl()
        != Formula::iff(
            mem_pair_w.clone(),
            Formula::and(Formula::mem(pair, tu), cond_pair),
        )
    {
        return None
    }
    let out = syl(&hyp_and(&h_pair_u, &h_all)?, &iff_mpr(&at_pair)?)?;

    // ── Uncurry into the nested shape and quantify ───────────────────────────
    let nested = uncurry(&uncurry(&out)?)?;
    let x_f = Formula::imp(mem_f, mem_pair_w);
    let g1 = Thm::mp(
        &Thm::ax_dist(pf, cl_u.clone(), Formula::imp(mem_aa.clone(), x_f.clone()))?,
        &Thm::gen(pf, &nested),
    )?;
    let g2 = Thm::mp(
        &imp_mono_r(&Thm::ax_dist(pf, mem_aa.clone(), x_f.clone())?, cl_u.clone())?,
        &g1,
    )?;
    let inner = Formula::imp(mem_aa, Formula::forall(pf, x_f));
    let g3 = Thm::mp(
        &Thm::ax_dist(pa, cl_u.clone(), inner.clone())?,
        &Thm::gen(pa, &g2),
    )?;
    debug_assert_eq!(
        *g3.concl(),
        Formula::imp(cl_u, Formula::forall(pa, inner)),
        "sup_mem: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv], &g3))
}
