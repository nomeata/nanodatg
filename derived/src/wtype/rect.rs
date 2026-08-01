//! **Step 7** — structural induction over a formula.
//!
//! # Interface
//!
//! ```text
//! ind_step(φ) := ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) →
//!                    ((∀b. (b ∈ B(a) → φ(app(f,b)))) → φ(⟨a,f⟩))))       [ind_step]
//!
//! ⊢ closed(A,B,u) → (ind_step(φ) → ∀z. (z ∈ W(A,B,u) → φ(z)))             [w_rect]
//! ```
//!
//! [`Params`] carries the free variables the caller has chosen for `A`, `B`, `u`
//! and the induction variable, so that the formula `φ` the caller supplies and
//! the one this file builds are literally the same. Callers need none of the
//! derivation below; at `u := U(c)` the antecedent is discharged and the rule is
//! unconditional, as [`crate::bound::w_rect_at`].
//!
//! # It is a scheme, and it is [`super::w_induction`] in disguise
//!
//! `φ` is an arbitrary formula of the ambient language, not a set, so this is a
//! **scheme**: one theorem per `φ`, built on demand. The argument is to apply
//! W2 to the set
//!
//! ```text
//! C := { z ∈ u : φ(z) }
//! ```
//!
//! carved out of `u` by one Separation. `C ⊆ u` holds by construction, and
//! `closed(A,B,C)` is precisely [`ind_step`] — modulo moving `f` between
//! `fs(B(a), W)` and `fs(B(a), C)`, which is [`super::fs_mono`] again in both
//! directions. W2 then gives `W ⊆ C`, i.e. `φ` on all of `W`.
//!
//! This is the single most-used export of [`crate::wtype`]: the recursor's
//! agreement lemma, every typing theorem about a W-type, and the inversion rule
//! below are all instances of it.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, forall_mono, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_mono_r,
    inst_all, opair, syl, uncurry,
};

use super::shared::hyp_inst_mp;
use super::condition::closed;
use super::apparatus::Wtype;

/// The minor premise of structural induction, as a formula:
///
/// ```text
/// ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) →
///        ((∀b. (b ∈ B(a) → φ(app(f,b)))) → φ(⟨a,f⟩))))
/// ```
///
/// `zv` is the variable `phi` speaks about; `φ(t)` is `phi[t/zv]`. The
/// induction hypothesis `∀b ∈ B(a). φ(f b)` is available because `f` lands in
/// the subset `{z ∈ W : φ(z)}` that [`w_rect`] runs W2 at — see the note there.
pub fn ind_step(
    env: &mut Env,
    s: &Sums,
    w_t: &Term,
    a: &Term,
    b: &Term,
    zv: FreeVar,
    phi: &Formula,
) -> Formula {
    let (pa, pf, pb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tpb) = (Term::var(pa), Term::var(pf), Term::var(pb));
    let fibre = s.ap.apply(b.clone(), tpa.clone());
    let hyp = Formula::forall(
        pb,
        Formula::imp(
            Formula::mem(tpb.clone(), fibre.clone()),
            phi.subst(zv, &s.ap.apply(tpf.clone(), tpb)),
        ),
    );
    Formula::forall(
        pa,
        Formula::imp(
            Formula::mem(tpa.clone(), a.clone()),
            Formula::forall(
                pf,
                Formula::imp(
                    Formula::mem(tpf.clone(), s.fs.of(fibre, w_t.clone())),
                    Formula::imp(hyp, phi.subst(zv, &opair(s.ap.sets.up, tpa, tpf))),
                ),
            ),
        ),
    )
}

/// The three parameter variables a W-type instance is taken over: the
/// constructor set `A`, the family `B`, and the bound `u`.
///
/// Bundled because they always travel together — `W(A,B,u)`, `closed(A,B,S)`
/// and the subset `{z ∈ W(A,B,u) : φ(z)}` all mention all three — and because
/// passing them separately is exactly how a derivation ends up quantifying over
/// the wrong variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// The set of constructors.
    pub a: FreeVar,
    /// The arity family.
    pub b: FreeVar,
    /// The bound.
    pub u: FreeVar,
}

/// **The capstone: structural induction over a formula.**
///
/// ```text
/// ⊢ closed(A,B,u) →
///     ((∀a. (a ∈ A → ∀f. (f ∈ fs(B(a),W) →
///        ((∀b. (b ∈ B(a) → φ(f b))) → φ(⟨a,f⟩)))))
///      → ∀z. (z ∈ W(A,B,u) → φ(z)))
/// ```
///
/// This is the form everything downstream actually uses — the recursor is built
/// on it — and it is [`crate::wtype::w_induction`] instantiated at
///
/// ```text
/// C := { z ∈ W(A,B,u) : φ(z) }
/// ```
///
/// **`C` is carved out of `W`, not out of `u`, and that ordering is the one
/// real trap.** `closed(A,B,C)` is not provable for a subset of `u`: proving it
/// needs `f ∈ fs(B(a), C)` to be lifted to `f ∈ fs(B(a), W)` before
/// [`crate::wtype::sup_mem`] applies, and that lift is [`crate::wtype::fs_mono`] along `C ⊆ W` — which is
/// available only because `C`'s defining condition has `z ∈ W` as a conjunct.
/// The same conjunct is what makes the induction hypothesis appear: a member of
/// `fs(B(a), C)` sends every `b ∈ B(a)` into `C`, i.e. to something satisfying
/// `φ`, which is exactly `∀b ∈ B(a). φ(f b)`.
///
/// `φ` is an arbitrary formula, so this cannot be a theorem of the first-order
/// signature: like [`crate::prop::conditional_singleton`] it is a *construction
/// taking a formula*, and it mints one fresh symbol (for `C`) per call. `zv` is
/// the variable `φ` speaks about; `params` must cover every free variable of
/// `φ` and must include `av`, `bv` and `uv`, since `C` mentions `W(A,B,u)`.
pub fn w_rect(
    env: &mut Env,
    wt: &Wtype,
    params: &[FreeVar],
    abu: Params,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Thm> {
    let (av, bv, uv) = (abu.a, abu.b, abu.u);
    if !params.contains(&av)
        || !params.contains(&bv)
        || !params.contains(&uv)
        || params.contains(&zv)
    {
        return None
    }
    let s = &wt.sums;
    let (ta, tb, tu, tz) = (Term::var(av), Term::var(bv), Term::var(uv), Term::var(zv));
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let args: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();

    // ── C := { z ∈ W : φ(z) } ───────────────────────────────────────────────
    let existence = separation_full(env, zv, phi, &w_t, &s.ap.empty_ax)?;
    let mem_zw = Formula::mem(tz.clone(), w_t.clone());
    let guard = Formula::and(mem_zw.clone(), phi.clone());
    let (c_sym, c_ax) = crate::define_by_membership(env, params, &existence, zv, &guard)?;
    let c_t = Term::apply(c_sym, args.clone());
    let c_at = inst_all(&c_ax, &args)?;

    // `t ∈ C ↔ (t ∈ W ∧ φ(t))`, insisted on rather than assumed.
    let c_iff = |t: &Term| -> Option<Thm> {
        let x = inst_all(&c_at, std::slice::from_ref(t))?;
        let want = Formula::iff(
            Formula::mem(t.clone(), c_t.clone()),
            Formula::and(Formula::mem(t.clone(), w_t.clone()), phi.subst(zv, t)),
        );
        if *x.concl() != want {
            return None
        }
        Some(x)
    };

    let c_z = c_iff(&tz)?;
    let z_in_w = syl(&iff_mp(&c_z)?, &and_left(mem_zw.clone(), phi.clone()))?;
    let c_sub_w = Thm::gen(zv, &z_in_w);
    if *c_sub_w.concl() != kernel::thm::subset(env, c_t.clone(), w_t.clone()) {
        return None
    }
    let ws_at = inst_all(&wt.w_subset, &[ta.clone(), tb.clone(), tu.clone(), tz.clone()])?;
    let c_sub_u = Thm::gen(zv, &syl(&z_in_w, &ws_at)?);
    if *c_sub_u.concl() != kernel::thm::subset(env, c_t.clone(), tu.clone()) {
        return None
    }

    // ── H := closed(A,B,u) ∧ (the minor premise) ────────────────────────────
    let cl_u = closed(env, s, &ta, &tb, &tu);
    let ih = ind_step(env, s, &w_t, &ta, &tb, zv, phi);
    let h = Formula::and(cl_u.clone(), ih.clone());

    let (pa, pf, pb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tpb) = (Term::var(pa), Term::var(pf), Term::var(pb));
    let fibre = s.ap.apply(tb.clone(), tpa.clone());
    let pair = opair(s.ap.sets.up, tpa.clone(), tpf.clone());
    let mem_aa = Formula::mem(tpa.clone(), ta.clone());
    let mem_f_c = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), c_t.clone()));

    let front = Formula::and(h.clone(), mem_aa.clone());
    let k = Formula::and(front.clone(), mem_f_c.clone());
    let k_front = and_left(front.clone(), mem_f_c.clone());
    let k_h = syl(&k_front, &and_left(h.clone(), mem_aa.clone()))?;
    let k_aa = syl(&k_front, &and_right(h.clone(), mem_aa.clone()))?;
    let k_fc = and_right(front, mem_f_c.clone());
    let k_clu = syl(&k_h, &and_left(cl_u.clone(), ih.clone()))?;
    let k_ih = syl(&k_h, &and_right(cl_u.clone(), ih.clone()))?;

    // ── `f` lands in `W`, so `sup_mem` puts `⟨a,f⟩` there ───────────────────
    let mono = inst_all(&wt.fs_mono, &[fibre.clone(), c_t.clone(), w_t.clone(), tpf.clone()])?;
    let k_fw = syl(&hyp_and(&k_fc, &a1i(&c_sub_w, k.clone()))?, &mono)?;

    let sm = inst_all(&wt.sup_mem, &[ta.clone(), tb.clone(), tu.clone()])?;
    let k_sup_all = syl(&k_clu, &sm)?;
    let k_sup_inner = hyp_inst_mp(&k_sup_all, &tpa, &k_aa)?;
    let k_pair_w = hyp_inst_mp(&k_sup_inner, &tpf, &k_fw)?;
    if *k_pair_w.concl() != Formula::imp(k.clone(), Formula::mem(pair.clone(), w_t.clone())) {
        return None
    }

    // ── The induction hypothesis, from `f`'s values lying in `C` ────────────
    let mem_b = Formula::mem(tpb.clone(), fibre.clone());
    let m = Formula::and(k.clone(), mem_b.clone());
    let m_k = and_left(k.clone(), mem_b.clone());
    let m_b = and_right(k.clone(), mem_b.clone());
    let app_fb = s.ap.apply(tpf.clone(), tpb.clone());
    let am = inst_all(&wt.app_mem, &[fibre.clone(), c_t.clone(), tpf.clone(), tpb.clone()])?;
    let m_app_c = syl(&hyp_and(&syl(&m_k, &k_fc)?, &m_b)?, &am)?;
    if *m_app_c.concl() != Formula::imp(m, Formula::mem(app_fb.clone(), c_t.clone())) {
        return None
    }
    let c_app = c_iff(&app_fb)?;
    let phi_app = phi.subst(zv, &app_fb);
    let m_phi = syl(
        &m_app_c,
        &syl(
            &iff_mp(&c_app)?,
            &and_right(Formula::mem(app_fb, w_t.clone()), phi_app.clone()),
        )?,
    )?;
    let k_all_b = Thm::mp(
        &Thm::ax_dist(pb, k.clone(), Formula::imp(mem_b.clone(), phi_app.clone()))?,
        &Thm::gen(pb, &uncurry(&m_phi)?),
    )?;

    // ── The minor premise, at this `a` and this `f` ─────────────────────────
    let k_ih_a = hyp_inst_mp(&k_ih, &tpa, &k_aa)?;
    let k_ih_f = hyp_inst_mp(&k_ih_a, &tpf, &k_fw)?;
    let k_phi_pair = hyp_mp(&k_ih_f, &k_all_b)?;
    let phi_pair = phi.subst(zv, &pair);
    if *k_phi_pair.concl() != Formula::imp(k.clone(), phi_pair.clone()) {
        return None
    }

    // ── so `⟨a,f⟩ ∈ C`, i.e. `closed(A,B,C)` ────────────────────────────────
    let c_pair = c_iff(&pair)?;
    let k_pair_c = syl(&hyp_and(&k_pair_w, &k_phi_pair)?, &iff_mpr(&c_pair)?)?;

    let x_f = Formula::imp(mem_f_c, Formula::mem(pair, c_t.clone()));
    let g1 = Thm::mp(
        &Thm::ax_dist(pf, h.clone(), Formula::imp(mem_aa.clone(), x_f.clone()))?,
        &Thm::gen(pf, &uncurry(&uncurry(&k_pair_c)?)?),
    )?;
    let g2 = Thm::mp(
        &imp_mono_r(&Thm::ax_dist(pf, mem_aa.clone(), x_f.clone())?, h.clone())?,
        &g1,
    )?;
    let inner = Formula::imp(mem_aa, Formula::forall(pf, x_f));
    let h_closed_c =
        Thm::mp(&Thm::ax_dist(pa, h.clone(), inner.clone())?, &Thm::gen(pa, &g2))?;
    let cl_c = closed(env, s, &ta, &tb, &c_t);
    if *h_closed_c.concl() != Formula::imp(h.clone(), cl_c) {
        return None
    }

    // ── W2 at `C`, then read `φ` off the membership ─────────────────────────
    let ind_at =
        inst_all(&wt.w_induction, &[ta.clone(), tb.clone(), tu.clone(), c_t.clone()])?;
    let h_wc = syl(&hyp_and(&a1i(&c_sub_u, h.clone()), &h_closed_c)?, &ind_at)?;

    let c_phi = syl(&iff_mp(&c_z)?, &and_right(mem_zw.clone(), phi.clone()))?;
    let fm = forall_mono(zv, &Thm::gen(zv, &imp_mono_r(&c_phi, mem_zw.clone())?))?;
    let out = uncurry(&syl(&h_wc, &fm)?)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            cl_u,
            Formula::imp(ih, Formula::forall(zv, Formula::imp(mem_zw, phi.clone())))
        ),
        "w_rect: unexpected shape"
    );
    Some(out)
}
