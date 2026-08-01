//! **Step 5 — W3**: inversion, i.e. **no junk**.
//!
//! # Interface
//!
//! ```text
//! is_sup(W,A,B,z) := ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a), W) ∧ z = ⟨a,f⟩))     [is_sup]
//!
//! ⊢ ∀A ∀B ∀u. (closed(A,B,u) →
//!       ∀w. (w ∈ W(A,B,u) → is_sup(W(A,B,u),A,B,w)))                  [w_inversion]
//! ```
//!
//! Callers need none of the derivation below; at `u := U(c)` the antecedent is
//! discharged and the rule is unconditional, as [`crate::bound::w_inversion_at`].
//!
//! # Why this needs an induction at all
//!
//! Nothing in the definition of `W` says its members are pairs — it is an
//! intersection, and an intersection of sets of pairs is a set of pairs only
//! because each of them is. So "every member of `W` is a `sup`" is not a
//! projection; it is [`super::w_rect`] at `φ(z) := is_sup(W,A,B,z)`, whose
//! induction step is discharged by [`super::sup_mem`] and by choosing the
//! obvious witnesses. The induction hypothesis is not used, which is the sign
//! that this is a *case analysis* dressed as an induction — but there is no
//! case-analysis principle for `W` other than the induction.

use kernel::{Env, Formula, Term, Thm};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, imp_mono_r, mpd_const, opair,
    syl, uncurry,
};

use super::condition::closed;
use super::rect::{Params, ind_step, w_rect};
use super::apparatus::Wtype;

/// `∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a), W(A,B,u)) ∧ z = ⟨a,f⟩))` — "`z` is a `sup`",
/// as a formula.
pub fn is_sup(env: &mut Env, s: &Sums, w_t: &Term, a: &Term, b: &Term, z: &Term) -> Formula {
    let (qa, qf) = (env.fresh_var(), env.fresh_var());
    let (tqa, tqf) = (Term::var(qa), Term::var(qf));
    let fibre = s.ap.apply(b.clone(), tqa.clone());
    let inner = Formula::exists(
        qf,
        Formula::and(
            Formula::mem(tqf.clone(), s.fs.of(fibre, w_t.clone())),
            Formula::eq(z.clone(), opair(s.ap.sets.up, tqa.clone(), tqf)),
        ),
    );
    Formula::exists(qa, Formula::and(Formula::mem(tqa, a.clone()), inner))
}

/// **W3, inversion — "no junk".**
/// `⊢ ∀A ∀B ∀u. (closed(A,B,u) → ∀w. (w ∈ W(A,B,u) → ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a), W(A,B,u)) ∧ w = ⟨a,f⟩))))`
///
/// The `closed(A,B,u)` antecedent is inherited from [`crate::wtype::sup_mem`]: without it
/// `W(A,B,u)` need not be closed, and the subset of `sup`s need not be either.
/// At `u := U(c)` it is discharged — see [`crate::bound::w_inversion_at`].
///
/// This is [`crate::wtype::w_rect`] at `φ(z) := "z is a sup"`. The minor premise is
/// discharged **without using the induction hypothesis at all** — `⟨a,f⟩` is a
/// `sup` by taking `a` and `f` as the witnesses — which is why the ordering
/// matters and nothing else does: the work is entirely in `w_rect`'s `C ⊆ W`.
pub fn w_inversion(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let s = &wt.sums;
    let (av, bv, uv, zv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(av), Term::var(bv), Term::var(uv), Term::var(zv));
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let psi = is_sup(env, s, &w_t, &ta, &tb, &tz);

    let rect = w_rect(env, wt, &[av, bv, uv], Params { a: av, b: bv, u: uv }, zv, &psi)?;

    // ── The minor premise: `⟨a,f⟩` is a `sup`, witnessed by `a` and `f` ─────
    let (pa, pf, pb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tpb) = (Term::var(pa), Term::var(pf), Term::var(pb));
    let fibre = s.ap.apply(tb.clone(), tpa.clone());
    let pair = opair(s.ap.sets.up, tpa.clone(), tpf.clone());
    let mem_aa = Formula::mem(tpa.clone(), ta.clone());
    let mem_fw = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), w_t.clone()));
    let h2 = Formula::and(mem_aa.clone(), mem_fw.clone());

    // The two existential bodies, rebuilt exactly as `is_sup` builds them.
    let (qa, qf) = (env.fresh_var(), env.fresh_var());
    let (tqa, tqf) = (Term::var(qa), Term::var(qf));
    let inner_body = |outer: &Term| {
        Formula::and(
            Formula::mem(tqf.clone(), s.fs.of(s.ap.apply(tb.clone(), outer.clone()), w_t.clone())),
            Formula::eq(pair.clone(), opair(s.ap.sets.up, outer.clone(), tqf.clone())),
        )
    };
    let inner_at_pa = inner_body(&tpa);
    let outer_body = Formula::and(
        Formula::mem(tqa.clone(), ta.clone()),
        Formula::exists(qf, inner_body(&tqa)),
    );

    let h2_fw = and_right(mem_aa.clone(), mem_fw.clone());
    let h2_eq = a1i(&Thm::eq_refl(pair.clone()), h2.clone());
    let h2_inner = syl(
        &hyp_and(&h2_fw, &h2_eq)?,
        &exists_intro_imp(qf, inner_at_pa, tpf.clone())?,
    )?;
    let h2_aa = and_left(mem_aa.clone(), mem_fw.clone());
    let h2_psi = syl(
        &hyp_and(&h2_aa, &h2_inner)?,
        &exists_intro_imp(qa, outer_body, tpa.clone())?,
    )?;
    let psi_pair = psi.subst(zv, &pair);
    if *h2_psi.concl() != Formula::imp(h2, psi_pair.clone()) {
        return None
    }

    // Weaken in the (unused) induction hypothesis, then quantify.
    let hyp_b = Formula::forall(
        pb,
        Formula::imp(
            Formula::mem(tpb.clone(), fibre.clone()),
            psi.subst(zv, &s.ap.apply(tpf.clone(), tpb)),
        ),
    );
    let weakened = syl(
        &uncurry(&h2_psi)?,
        &imp_mono_r(&Thm::ax_k(psi_pair.clone(), hyp_b.clone()), mem_fw.clone())?,
    )?;
    let x_f = Formula::imp(mem_fw, Formula::imp(hyp_b, psi_pair));
    let step = Thm::gen(
        pa,
        &Thm::mp(&Thm::ax_dist(pf, mem_aa.clone(), x_f.clone())?, &Thm::gen(pf, &weakened))?,
    );
    let expected = ind_step(env, s, &w_t, &ta, &tb, zv, &psi);
    if *step.concl() != expected {
        return None
    }

    let out = mpd_const(&rect, &step)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            closed(env, s, &ta, &tb, &tu),
            Formula::forall(zv, Formula::imp(Formula::mem(tz, w_t), psi))
        ),
        "w_inversion: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv], &out))
}
