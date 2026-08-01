//! The **induction-hypothesis function** `ih(g,A,R,x)`, and the edge
//! proposition `ep(R,y,x) = [⟨y,x⟩ ∈ R]` it is built from.
//!
//! # Interface
//!
//! ```text
//! ep(R,y,x)   := { z ∈ 1 : ⟨y,x⟩ ∈ R }                         [edge_prop]
//! row(g,R,x,y):= ⟨y, cval(ep(R,y,x), app(g,y))⟩
//! ih(g,A,R,x) := { row(g,R,x,y) : y ∈ A }                     [ih_symbol]
//!
//! preds_agree(g,h,A,R,x) := ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → app(g,y) = app(h,y)))
//! preds_typed(g,A,R,T,x) := ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → app(g,y) ∈ T))
//! ih_bound(A,T)          := 𝒫(prod(A, 𝒫(prod(1,T))))
//!
//! ⊢ ∀R ∀y ∀x ∀z. (z ∈ ep(R,y,x) ↔ (z ∈ 1 ∧ ⟨y,x⟩ ∈ R))         [edge_prop]
//! ⊢ ∀g ∀A ∀R ∀x ∀p. (p ∈ ih(g,A,R,x) ↔
//!       ∃y. (y ∈ A ∧ p = row(g,R,x,y)))                       [ih_symbol]
//! ⊢ ∀g ∀h ∀A ∀R ∀x. (preds_agree(g,h,A,R,x) →
//!       ih(g,A,R,x) = ih(h,A,R,x))                            [ih_ext]
//! ⊢ ∀g ∀A ∀R ∀T ∀x. (preds_typed(g,A,R,T,x) →
//!       ih(g,A,R,x) ∈ ih_bound(A,T))                          [ih_typed]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What this is
//!
//! Carneiro's *The Type Theory of Lean* §6.2.2 writes the recursion equation as
//!
//! ```text
//! F(x) = e(x)(•)(y ∈ A ↦ (h ∈ [⟨y,x⟩ ∈ R] ↦ F(y)))
//! ```
//!
//! The third argument is the induction hypothesis: a function on **all** of `A`
//! — not on the predecessors of `x` — whose value at `y` is a function out of
//! the *proof* that `y` is an `R`-predecessor of `x`. `ih(g,A,R,x)` is that
//! function, with `g` standing in for the partially-built `F`. One Replacement
//! along `y ↦ row(g,R,x,y)`, in exactly the shape of
//! [`crate::wrec::compose`] — and, like it, the recursion never *applies* an
//! `ih`, it only compares two of them, so no beta rule for `ih` itself is
//! needed. (The beta rule for the *inner* function is
//! [`super::cval::cval_app`], and that one is needed, because Lean's minor
//! premise does apply it.)
//!
//! # Why the domain is `A` and not the predecessors of `x`
//!
//! Because the thesis says so, and because it costs less. Restricting to
//! `{y ∈ A : ⟨y,x⟩ ∈ R}` would need a Separation *per `x`*, i.e. a second
//! symbol and a membership condition to unfold at every use; taking the whole of
//! `A` and letting the empty proposition `[⟨y,x⟩ ∈ R]` erase the non-predecessors
//! costs nothing — [`super::cval::cval_ext`] and [`super::cval::cval_bound`] are
//! both guarded by inhabitation of that proposition, so a `y` off the relation
//! contributes no obligation to either lemma. That is the whole reason those two
//! lemmas are stated with a guarded premise; see [`super::cval`].
//!
//! # The two lemmas, and what they are for
//!
//! [`ih_ext`] is spent in the agreement argument: two attempts that agree on the
//! predecessors of `x` produce *the same* induction hypothesis at `x`, hence the
//! same value. [`ih_typed`] is spent in the totality argument: it is what lets
//! `step_typed` be stated over a plain power set rather than over a function
//! space, so no attempt ever has to be proved total on `A` to be usable —
//! `𝒫(prod(A,·))` contains both the function space and `∅`, the `pow_prod`
//! superset trick `RECURSOR-DESIGN.md` §3.2 records for the general W-recursor.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::prop::conditional_singleton;
use crate::sums::Sums;
use crate::wrec::{hyp_congr, hyp_eq_trans};
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp,
    exists_unique_eq, forall_mono, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_mono_r, inst_all,
    syl, uncurry,
};

use super::cval::{agree_on_cond, bound_cond, cval_of};

/// Introduce `ep(R,y,x) = [⟨y,x⟩ ∈ R] = { z ∈ 1 : ⟨y,x⟩ ∈ R }`, with
/// `⊢ ∀R ∀y ∀x ∀z. (z ∈ ep(R,y,x) ↔ (z ∈ 1 ∧ ⟨y,x⟩ ∈ R))`.
///
/// A [`crate::prop::conditional_singleton`] at the formula `⟨y,x⟩ ∈ R`, whose
/// free variables are all set variables — so this is a genuine ternary function
/// symbol, not a scheme, and the recursor's theorems quantify over `R` like
/// everything else.
pub fn edge_prop(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    let (rv, yv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(
        s.ap.sets.pair(Term::var(yv), Term::var(xv)),
        Term::var(rv),
    );
    conditional_singleton(env, s, &[rv, yv, xv], &phi)
}

/// The term `ep(R,y,x)` — the proposition "`y` is an `R`-predecessor of `x`".
pub fn ep_of(ep: FnSym, r: Term, y: Term, x: Term) -> Term {
    Term::apply(ep, vec![r, y, x])
}

/// The term `⟨y, cval(ep(R,y,x), app(g,y))⟩` — one row of the induction
/// hypothesis.
pub fn row_of(s: &Sums, ep: FnSym, g: &Term, r: &Term, x: &Term, y: &Term) -> Term {
    let value = cval_of(
        s,
        ep_of(ep, r.clone(), y.clone(), x.clone()),
        s.ap.apply(g.clone(), y.clone()),
    );
    s.ap.sets.pair(y.clone(), value)
}

/// Introduce `ih(g,A,R,x) = { ⟨y, cval(ep(R,y,x), app(g,y))⟩ : y ∈ A }`, with
///
/// ```text
/// ⊢ ∀g ∀A ∀R ∀x ∀p. (p ∈ ih(g,A,R,x) ↔ ∃y. (y ∈ A ∧ p = row(g,R,x,y)))
/// ```
///
/// One Replacement along `y ↦ row(g,R,x,y)`; the `∃!` premise is `∃!v. v = t`,
/// which [`crate::exists_unique_eq`] supplies for nothing.
pub fn ih_symbol(env: &mut Env, s: &Sums, ep: FnSym) -> Option<(FnSym, Thm)> {
    let (gv, av, rv, xv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tx, ty) = (
        Term::var(gv),
        Term::var(av),
        Term::var(rv),
        Term::var(xv),
        Term::var(yv),
    );

    let pair = row_of(s, ep, &tg, &tr, &tx, &ty);
    let (pv, phi, exu) = exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, yv, pv, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(yv, &a1i(&exu, Formula::mem(ty.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(yv, Formula::and(Formula::mem(ty, ta), phi));
    crate::define_by_membership(env, &[gv, av, rv, xv], &img, pv, &cond)
}

/// The term `ih(g,A,R,x)`.
pub fn ih_of(ih: FnSym, g: Term, a: Term, r: Term, x: Term) -> Term {
    Term::apply(ih, vec![g, a, r, x])
}

/// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → app(g,y) = app(h,y)))` — "`g` and `h` agree on
/// the `R`-predecessors of `x` inside `A`", as a formula.
pub fn preds_agree(env: &mut Env, s: &Sums, g: &Term, h: &Term, a: &Term, r: &Term, x: &Term) -> Formula {
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), a.clone()),
            Formula::imp(
                Formula::mem(s.ap.sets.pair(ty.clone(), x.clone()), r.clone()),
                Formula::eq(
                    s.ap.apply(g.clone(), ty.clone()),
                    s.ap.apply(h.clone(), ty),
                ),
            ),
        ),
    )
}

/// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → app(g,y) ∈ T))` — "`g`'s values on the
/// `R`-predecessors of `x` land in `T`", as a formula.
pub fn preds_typed(env: &mut Env, s: &Sums, g: &Term, a: &Term, r: &Term, t: &Term, x: &Term) -> Formula {
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), a.clone()),
            Formula::imp(
                Formula::mem(s.ap.sets.pair(ty.clone(), x.clone()), r.clone()),
                Formula::mem(s.ap.apply(g.clone(), ty), t.clone()),
            ),
        ),
    )
}

/// The term `𝒫(prod(A, 𝒫(prod(1,T))))` — the set every induction hypothesis
/// with values in `T` belongs to.
///
/// A power set, not a function space: an attempt need not be total on `A`, and
/// `𝒫(prod(A,·))` holds `∅` as happily as it holds a total function. Making
/// `step_typed` quantify over this is what keeps the recursion's typing side
/// condition free of any well-definedness obligation on `g`.
pub fn ih_bound(s: &Sums, a: &Term, t: &Term) -> Term {
    let inner = Term::apply(s.pow, vec![s.prod.of(s.unit(), t.clone())]);
    Term::apply(s.pow, vec![s.prod.of(a.clone(), inner)])
}

/// One inclusion of [`ih_ext`], as `⊢ H → (p ∈ ih(g,…) → p ∈ ih(h,…))`.
#[allow(clippy::too_many_arguments)]
fn ih_incl(
    env: &mut Env,
    s: &Sums,
    ep: FnSym,
    ep_ax: &Thm,
    ih: FnSym,
    ih_ax: &Thm,
    cval_ext: &Thm,
    g: &Term,
    h: &Term,
    a: &Term,
    r: &Term,
    x: &Term,
    p: &Term,
) -> Option<Thm> {
    let hyp = preds_agree(env, s, g, h, a, r, x);
    let yv = env.fresh_var();
    let ty = Term::var(yv);

    let row_g = row_of(s, ep, g, r, x, &ty);
    let row_h = row_of(s, ep, h, r, x, &ty);
    let mem_ya = Formula::mem(ty.clone(), a.clone());
    let body_g = Formula::and(mem_ya.clone(), Formula::eq(p.clone(), row_g.clone()));
    let body_h = Formula::and(mem_ya.clone(), Formula::eq(p.clone(), row_h.clone()));

    // ── Work under `K := H ∧ body_g` ────────────────────────────────────────
    let k = Formula::and(hyp.clone(), body_g.clone());
    let k_h = and_left(hyp.clone(), body_g.clone());
    let k_body = and_right(hyp.clone(), body_g.clone());
    let k_ya = syl(
        &k_body,
        &and_left(mem_ya.clone(), Formula::eq(p.clone(), row_g.clone())),
    )?;
    let k_peq = syl(
        &k_body,
        &and_right(mem_ya.clone(), Formula::eq(p.clone(), row_g.clone())),
    )?;

    // `K → (⟨y,x⟩ ∈ R → app(g,y) = app(h,y))`.
    let k_at_y = hyp_mp(&syl(&k_h, &Thm::ax_inst(hyp.clone(), ty.clone())?)?, &k_ya)?;

    // `K → ∀h′. (h′ ∈ ep(R,y,x) → app(g,y) = app(h,y))` — the guarded premise
    // of `cval_ext`. The edge proposition is inhabited only when the edge is
    // present, which is exactly the guard.
    let hv = env.fresh_var();
    let th = Term::var(hv);
    let ep_t = ep_of(ep, r.clone(), ty.clone(), x.clone());
    let ep_at = inst_all(ep_ax, &[r.clone(), ty.clone(), x.clone(), th.clone()])?;
    let mem_h1 = Formula::mem(th.clone(), s.unit());
    let edge = Formula::mem(s.ap.sets.pair(ty.clone(), x.clone()), r.clone());
    if *ep_at.concl()
        != Formula::iff(
            Formula::mem(th.clone(), ep_t.clone()),
            Formula::and(mem_h1.clone(), edge.clone()),
        )
    {
        return None
    }
    let h_edge = syl(&iff_mp(&ep_at)?, &and_right(mem_h1, edge))?;
    let inner = syl(&h_edge, &{
        // `K → (edge → eq)` commuted to `edge → (K → eq)`, then composed.
        com12(&k_at_y)?
    })?; // h′ ∈ ep → (K → eq)
    let k_guarded = Thm::mp(
        &Thm::ax_dist(
            hv,
            k.clone(),
            Formula::imp(
                Formula::mem(th.clone(), ep_t.clone()),
                Formula::eq(
                    s.ap.apply(g.clone(), ty.clone()),
                    s.ap.apply(h.clone(), ty.clone()),
                ),
            ),
        )?,
        &Thm::gen(hv, &com12(&inner)?),
    )?;
    let want = agree_on_cond(
        env,
        &ep_t,
        &s.ap.apply(g.clone(), ty.clone()),
        &s.ap.apply(h.clone(), ty.clone()),
    );
    if *k_guarded.concl() != Formula::imp(k.clone(), want) {
        return None
    }

    // `K → cval(ep, app(g,y)) = cval(ep, app(h,y))`, then one pairing
    // congruence, then transitivity onto `p`.
    let ce = inst_all(
        cval_ext,
        &[
            ep_t,
            s.ap.apply(g.clone(), ty.clone()),
            s.ap.apply(h.clone(), ty.clone()),
        ],
    )?;
    let k_val = syl(&k_guarded, &ce)?;
    let ty2 = ty.clone();
    let up = s.ap.sets.up;
    let k_row = hyp_congr(env, &k_val, move |t| crate::opair(up, ty2.clone(), t))?;
    if *k_row.concl() != Formula::imp(k.clone(), Formula::eq(row_g.clone(), row_h.clone())) {
        return None
    }
    let k_ph = hyp_eq_trans(env, &k_peq, &k_row)?;
    let k_body_h = hyp_and(&k_ya, &k_ph)?;
    if *k_body_h.concl() != Formula::imp(k, body_h.clone()) {
        return None
    }

    // ── Discharge the witness, then cross the two membership conditions ─────
    let ex_h = Formula::exists(yv, body_h.clone());
    let k_ex = syl(&k_body_h, &exists_intro_imp(yv, body_h, ty)?)?;
    let per_y = com12(&uncurry(&k_ex)?)?;
    let h_ex = com12(&exists_elim_imp(
        yv,
        &Thm::gen(yv, &per_y),
        &Formula::imp(hyp.clone(), ex_h.clone()),
    )?)?;

    let ig = ih_of(ih, g.clone(), a.clone(), r.clone(), x.clone());
    let ihh = ih_of(ih, h.clone(), a.clone(), r.clone(), x.clone());
    let ax_g = inst_all(
        ih_ax,
        &[g.clone(), a.clone(), r.clone(), x.clone(), p.clone()],
    )?;
    let ax_h = inst_all(
        ih_ax,
        &[h.clone(), a.clone(), r.clone(), x.clone(), p.clone()],
    )?;
    if *ax_g.concl() != Formula::iff(Formula::mem(p.clone(), ig), Formula::exists(yv, body_g))
        || *ax_h.concl() != Formula::iff(Formula::mem(p.clone(), ihh), ex_h)
    {
        return None
    }
    let step1 = crate::funcs::hyp_syl(&a1i(&iff_mp(&ax_g)?, hyp.clone()), &h_ex)?;
    crate::funcs::hyp_syl(&step1, &a1i(&iff_mpr(&ax_h)?, hyp))
}

/// `⊢ ∀g ∀h ∀A ∀R ∀x. (preds_agree(g,h,A,R,x) → ih(g,A,R,x) = ih(h,A,R,x))` —
/// **the induction hypothesis is determined by the values on the predecessors**.
///
/// The analogue of [`crate::wrec::compose_ext`], and the fact the agreement
/// argument of [`super::agreement`] is made of. Nothing is assumed about `g` and
/// `h` off the predecessors of `x`, and nothing needs to be: there the edge
/// proposition is empty, so [`super::cval::cval_ext`]'s guarded premise is
/// vacuous.
///
/// All three theorem arguments must be **unconditional**. `ep_ax` and `ih_ax`
/// have their conclusions pinned inside `ih_incl`, and
/// `cval_ext`'s is forced by the [`syl`] it is joined with, but nothing anywhere
/// read a `Γ`, and this header promises `⊢ …`. The final `debug_assert` stays a
/// `debug_assert`: the last join is against [`Thm::ax_extensionality`] at `ig`
/// and `ihh`, so the equation is kernel-forced and the assertion re-checks only
/// that the derivation has not drifted.
#[allow(clippy::too_many_arguments)]
pub fn ih_ext(
    env: &mut Env,
    s: &Sums,
    ep: FnSym,
    ep_ax: &Thm,
    ih: FnSym,
    ih_ax: &Thm,
    cval_ext: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[ep_ax, ih_ax, cval_ext]) {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let (gv, hv, av, rv, xv, pv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, th, ta, tr, tx, tp) = (
        Term::var(gv),
        Term::var(hv),
        Term::var(av),
        Term::var(rv),
        Term::var(xv),
        Term::var(pv),
    );

    let hyp = preds_agree(env, s, &tg, &th, &ta, &tr, &tx);
    let hyp_rev = preds_agree(env, s, &th, &tg, &ta, &tr, &tx);
    let ig = ih_of(ih, tg.clone(), ta.clone(), tr.clone(), tx.clone());
    let ihh = ih_of(ih, th.clone(), ta.clone(), tr.clone(), tx.clone());

    // `H → H⁻¹`: symmetry of the equation, under two implications and a binder.
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let sym_eq = eq_symm_imp(
        env,
        s.ap.apply(tg.clone(), ty.clone()),
        s.ap.apply(th.clone(), ty.clone()),
    );
    let sym_body = imp_mono_r(
        &imp_mono_r(
            &sym_eq,
            Formula::mem(s.ap.sets.pair(ty.clone(), tx.clone()), tr.clone()),
        )?,
        Formula::mem(ty, ta.clone()),
    )?;
    let h_sym = forall_mono(yv, &Thm::gen(yv, &sym_body))?;
    if *h_sym.concl() != Formula::imp(hyp.clone(), hyp_rev) {
        return None
    }

    let fwd = ih_incl(env, s, ep, ep_ax, ih, ih_ax, cval_ext, &tg, &th, &ta, &tr, &tx, &tp)?;
    let bwd_raw = ih_incl(env, s, ep, ep_ax, ih, ih_ax, cval_ext, &th, &tg, &ta, &tr, &tx, &tp)?;
    let bwd = syl(&h_sym, &bwd_raw)?;

    let both = hyp_and(&fwd, &bwd)?;
    let iff = Formula::iff(
        Formula::mem(tp.clone(), ig.clone()),
        Formula::mem(tp, ihh.clone()),
    );
    if *both.concl() != Formula::imp(hyp.clone(), iff.clone()) {
        return None
    }
    let h_all = Thm::mp(&Thm::ax_dist(pv, hyp.clone(), iff)?, &Thm::gen(pv, &both))?;
    let out = syl(&h_all, &inst_all(&ext, &[ig.clone(), ihh.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::eq(ig, ihh)),
        "ih_ext: unexpected shape"
    );
    Some(gen_all(&[gv, hv, av, rv, xv], &out))
}

/// `⊢ ∀g ∀A ∀R ∀T ∀x. (preds_typed(g,A,R,T,x) → ih(g,A,R,x) ∈ ih_bound(A,T))` —
/// **the induction hypothesis is a set of the expected shape**.
///
/// What `step_typed` is stated against. Note it asks nothing of `g` off the
/// predecessors of `x`: there the row is `⟨y, ∅⟩`, and `∅ ⊆ prod(1,T)` whatever
/// `app(g,y)` happens to be.
///
/// All three theorem arguments must be **unconditional**; `ep_ax`, `ih_ax` and
/// the power-set axiom instance all have their conclusions pinned in release
/// below, but no `hyps()` was read anywhere and the header says `⊢ …`. The final
/// `debug_assert` stays a `debug_assert`: the last join is a [`syl`] against
/// `iff_mpr(pow_ig)`, and `pow_ig` is release-pinned just above it, so the
/// membership is already forced.
#[allow(clippy::too_many_arguments)]
pub fn ih_typed(
    env: &mut Env,
    s: &Sums,
    ep: FnSym,
    ep_ax: &Thm,
    ih: FnSym,
    ih_ax: &Thm,
    cval_bound: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[ep_ax, ih_ax, cval_bound]) {
        return None
    }
    let (gv, av, rv, tv, xv, pv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tt, tx, tp, ty) = (
        Term::var(gv),
        Term::var(av),
        Term::var(rv),
        Term::var(tv),
        Term::var(xv),
        Term::var(pv),
        Term::var(yv),
    );

    let hyp = preds_typed(env, s, &tg, &ta, &tr, &tt, &tx);
    let ig = ih_of(ih, tg.clone(), ta.clone(), tr.clone(), tx.clone());
    let inner_pow = Term::apply(s.pow, vec![s.prod.of(s.unit(), tt.clone())]);
    let target = s.prod.of(ta.clone(), inner_pow.clone());

    let row = row_of(s, ep, &tg, &tr, &tx, &ty);
    let cval = cval_of(
        s,
        ep_of(ep, tr.clone(), ty.clone(), tx.clone()),
        s.ap.apply(tg.clone(), ty.clone()),
    );
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let body = Formula::and(mem_ya.clone(), Formula::eq(tp.clone(), row.clone()));
    let goal = Formula::mem(tp.clone(), target.clone());

    // ── Under `K := H ∧ body` ───────────────────────────────────────────────
    let k = Formula::and(hyp.clone(), body.clone());
    let k_h = and_left(hyp.clone(), body.clone());
    let k_body = and_right(hyp.clone(), body.clone());
    let k_ya = syl(
        &k_body,
        &and_left(mem_ya.clone(), Formula::eq(tp.clone(), row.clone())),
    )?;
    let k_peq = syl(
        &k_body,
        &and_right(mem_ya.clone(), Formula::eq(tp.clone(), row.clone())),
    )?;
    let k_at_y = hyp_mp(&syl(&k_h, &Thm::ax_inst(hyp.clone(), ty.clone())?)?, &k_ya)?;

    // `K → ∀h′. (h′ ∈ ep(R,y,x) → (h′ ∈ 1 ∧ app(g,y) ∈ T))`.
    let hv = env.fresh_var();
    let th = Term::var(hv);
    let ep_t = ep_of(ep, tr.clone(), ty.clone(), tx.clone());
    let ep_at = inst_all(ep_ax, &[tr.clone(), ty.clone(), tx.clone(), th.clone()])?;
    let mem_h1 = Formula::mem(th.clone(), s.unit());
    let edge = Formula::mem(s.ap.sets.pair(ty.clone(), tx.clone()), tr.clone());
    if *ep_at.concl()
        != Formula::iff(
            Formula::mem(th.clone(), ep_t.clone()),
            Formula::and(mem_h1.clone(), edge.clone()),
        )
    {
        return None
    }
    let mem_ep = Formula::mem(th.clone(), ep_t.clone());
    let l = Formula::and(k.clone(), mem_ep.clone());
    let l_k = and_left(k.clone(), mem_ep.clone());
    let l_ep = and_right(k.clone(), mem_ep.clone());
    let l_unfold = syl(&l_ep, &iff_mp(&ep_at)?)?;
    let l_h1 = syl(&l_unfold, &and_left(mem_h1.clone(), edge.clone()))?;
    let l_edge = syl(&l_unfold, &and_right(mem_h1, edge))?;
    let l_typed = hyp_mp(&syl(&l_k, &k_at_y)?, &l_edge)?;
    let l_both = hyp_and(&l_h1, &l_typed)?;
    let k_guarded = Thm::mp(
        &Thm::ax_dist(
            hv,
            k.clone(),
            Formula::imp(
                mem_ep,
                Formula::and(
                    Formula::mem(th.clone(), s.unit()),
                    Formula::mem(s.ap.apply(tg.clone(), ty.clone()), tt.clone()),
                ),
            ),
        )?,
        &Thm::gen(hv, &uncurry(&l_both)?),
    )?;
    let _ = l;
    let want = bound_cond(
        env,
        &ep_t,
        &s.ap.apply(tg.clone(), ty.clone()),
        &s.unit(),
        &tt,
    );
    if *k_guarded.concl() != Formula::imp(k.clone(), want) {
        return None
    }

    // `cval ⊆ prod(1,T)`, hence `cval ∈ 𝒫(prod(1,T))`, hence the row is in the
    // product, hence — carried back along `p = row` — so is `p`.
    let cb = inst_all(
        cval_bound,
        &[
            ep_t,
            s.ap.apply(tg.clone(), ty.clone()),
            s.unit(),
            tt.clone(),
        ],
    )?;
    let k_sub = syl(&k_guarded, &cb)?;
    let pow_at = inst_all(
        &s.pow_ax,
        &[s.prod.of(s.unit(), tt.clone()), cval.clone()],
    )?;
    if *pow_at.concl()
        != Formula::iff(
            Formula::mem(cval.clone(), inner_pow.clone()),
            kernel::thm::subset(env, cval.clone(), s.prod.of(s.unit(), tt.clone())),
        )
    {
        return None
    }
    let k_pow = syl(&k_sub, &iff_mpr(&pow_at)?)?;
    let pip = inst_all(
        &s.pair_in_prod,
        &[ta.clone(), inner_pow.clone(), ty.clone(), cval],
    )?;
    let k_row = syl(&hyp_and(&k_ya, &k_pow)?, &iff_mpr(&pip)?)?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        row.clone(),
        tp.clone(),
        hole,
        Formula::mem(Term::var(hole), target.clone()),
    );
    let k_pr = syl(&k_peq, &eq_symm_imp(env, tp.clone(), row))?;
    let k_goal = hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &k_pr)?, &k_row)?;
    if *k_goal.concl() != Formula::imp(k, goal.clone()) {
        return None
    }

    // ── Discharge the witness, then the subset, then the power set ──────────
    let per_y = com12(&uncurry(&k_goal)?)?;
    let h_ex = com12(&exists_elim_imp(
        yv,
        &Thm::gen(yv, &per_y),
        &Formula::imp(hyp.clone(), goal.clone()),
    )?)?;
    let ax = inst_all(
        ih_ax,
        &[tg.clone(), ta.clone(), tr.clone(), tx.clone(), tp.clone()],
    )?;
    if *ax.concl() != Formula::iff(Formula::mem(tp.clone(), ig.clone()), Formula::exists(yv, body))
    {
        return None
    }
    let per_p = crate::funcs::hyp_syl(&a1i(&iff_mp(&ax)?, hyp.clone()), &h_ex)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(
            pv,
            hyp.clone(),
            Formula::imp(Formula::mem(tp.clone(), ig.clone()), goal),
        )?,
        &Thm::gen(pv, &per_p),
    )?;
    let pow_ig = inst_all(&s.pow_ax, &[target.clone(), ig.clone()])?;
    if *pow_ig.concl()
        != Formula::iff(
            Formula::mem(ig.clone(), ih_bound(s, &ta, &tt)),
            kernel::thm::subset(env, ig.clone(), target),
        )
    {
        return None
    }
    let out = syl(&h_sub, &iff_mpr(&pow_ig)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::mem(ig, ih_bound(s, &ta, &tt))),
        "ih_typed: unexpected shape"
    );
    Some(gen_all(&[gv, av, rv, tv, xv], &out))
}

/// The free variables an `ih` instance is taken over, in argument order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IhVars {
    /// The partial recursor.
    pub g: FreeVar,
    /// The carrier.
    pub a: FreeVar,
    /// The relation.
    pub r: FreeVar,
    /// The point.
    pub x: FreeVar,
}

/// `⊢ ∀g ∀A ∀R ∀x ∀p ∀u. (⟨p,u⟩ ∈ ih(g,A,R,x) → u = cval(ep(R,p,x), app(g,p)))`
/// — every value of the induction hypothesis is *the* row at its key.
///
/// `ih_ax` must be **unconditional**; its conclusion is pinned in release just
/// before the last join. The closing `debug_assert` stays a `debug_assert`: it is a
/// [`syl`] of `iff_mp(at)` — with `at` that same release-pinned instance —
/// against an `exists_elim_imp` whose consequent is `goal`, so both ends are
/// already forced.
pub fn ih_value(env: &mut Env, s: &Sums, ep: FnSym, ih: FnSym, ih_ax: &Thm) -> Option<Thm> {
    if !ih_ax.hyps().is_empty() {
        return None
    }
    let (gv, av, rv, xv, pv, uv, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tx, tp, tu, ty) = (
        Term::var(gv),
        Term::var(av),
        Term::var(rv),
        Term::var(xv),
        Term::var(pv),
        Term::var(uv),
        Term::var(yv),
    );
    let pair = s.ap.sets.pair(tp.clone(), tu.clone());
    let ig = ih_of(ih, tg.clone(), ta.clone(), tr.clone(), tx.clone());
    let at = inst_all(
        ih_ax,
        &[tg.clone(), ta.clone(), tr.clone(), tx.clone(), pair.clone()],
    )?;

    let row_y = row_of(s, ep, &tg, &tr, &tx, &ty);
    let val_p = cval_of(
        s,
        ep_of(ep, tr.clone(), tp.clone(), tx.clone()),
        s.ap.apply(tg.clone(), tp.clone()),
    );
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let eq_row = Formula::eq(pair.clone(), row_y.clone());
    let body = Formula::and(mem_ya.clone(), eq_row.clone());
    let goal = Formula::eq(tu.clone(), val_p.clone());

    // From `⟨p,u⟩ = ⟨y, row(y)⟩`: `p = y` and `u = row-value(y)`.
    let (fy, sy) = {
        let value_y = cval_of(
            s,
            ep_of(ep, tr.clone(), ty.clone(), tx.clone()),
            s.ap.apply(tg.clone(), ty.clone()),
        );
        let pi = inst_all(
            &s.ap.pair_inj,
            &[tp.clone(), tu.clone(), ty.clone(), value_y.clone()],
        )?;
        let l = Formula::eq(tp.clone(), ty.clone());
        let r = Formula::eq(tu.clone(), value_y);
        (
            syl(&and_right(mem_ya.clone(), eq_row.clone()), &syl(&pi, &and_left(l.clone(), r.clone()))?)?,
            syl(&and_right(mem_ya, eq_row), &syl(&pi, &and_right(l, r))?)?,
        )
    };
    // `p = y` carries the row back.
    let (tr2, tx2, tg2) = (tr.clone(), tx.clone(), tg.clone());
    let s2 = s.clone();
    let cong = hyp_congr(env, &fy, move |t| {
        cval_of(
            &s2,
            ep_of(ep, tr2.clone(), t.clone(), tx2.clone()),
            Term::apply(s2.ap.app, vec![tg2.clone(), t]),
        )
    })?;
    let cong_rev = syl(&cong, &eq_symm_imp(env, {
        cval_of(
            s,
            ep_of(ep, tr.clone(), tp.clone(), tx.clone()),
            s.ap.apply(tg.clone(), tp.clone()),
        )
    }, {
        cval_of(
            s,
            ep_of(ep, tr.clone(), ty.clone(), tx.clone()),
            s.ap.apply(tg.clone(), ty.clone()),
        )
    }))?;
    let out_body = hyp_eq_trans(env, &sy, &cong_rev)?;
    if *out_body.concl() != Formula::imp(body.clone(), goal.clone()) {
        return None
    }
    let elim = exists_elim_imp(yv, &Thm::gen(yv, &out_body), &goal)?;
    if *at.concl() != Formula::iff(Formula::mem(pair.clone(), ig.clone()), Formula::exists(yv, body))
    {
        return None
    }
    let out = syl(&iff_mp(&at)?, &elim)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(pair, ig), goal),
        "ih_value: unexpected shape"
    );
    Some(gen_all(&[gv, av, rv, xv, pv, uv], &out))
}

/// `⊢ ∀g ∀A ∀R ∀x. sv(ih(g,A,R,x))` — the induction hypothesis is a function.
///
/// `value` must be [`ih_value`] and must be **unconditional**; its conclusion is
/// pinned by the two release checks below, which rebuild the implication and
/// `is_single_valued(ih(g,A,R,x))` and compare.
pub fn ih_single_valued(env: &mut Env, s: &Sums, ih: FnSym, value: &Thm) -> Option<Thm> {
    if !value.hyps().is_empty() {
        return None
    }
    let (gv, av, rv, xv, pv, uv, u2v) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tx, tp, tu, tu2) = (
        Term::var(gv),
        Term::var(av),
        Term::var(rv),
        Term::var(xv),
        Term::var(pv),
        Term::var(uv),
        Term::var(u2v),
    );
    let ig = ih_of(ih, tg.clone(), ta.clone(), tr.clone(), tx.clone());
    let m1 = Formula::mem(s.ap.sets.pair(tp.clone(), tu.clone()), ig.clone());
    let m2 = Formula::mem(s.ap.sets.pair(tp.clone(), tu2.clone()), ig.clone());
    let h = Formula::and(m1.clone(), m2.clone());

    let inst = |u: &Term| -> Option<Thm> {
        inst_all(
            value,
            &[
                tg.clone(),
                ta.clone(),
                tr.clone(),
                tx.clone(),
                tp.clone(),
                u.clone(),
            ],
        )
    };
    let h1 = syl(&and_left(m1.clone(), m2.clone()), &inst(&tu)?)?;
    let h2 = syl(&and_right(m1, m2), &inst(&tu2)?)?;
    let (_, e1) = h1.concl().as_imp()?;
    let (_, rhs) = e1.as_eq()?;
    let h2r = syl(&h2, &eq_symm_imp(env, tu2.clone(), rhs))?;
    let out = hyp_eq_trans(env, &h1, &h2r)?;
    if *out.concl() != Formula::imp(h, Formula::eq(tu.clone(), tu2.clone())) {
        return None
    }
    let body = gen_all(&[pv, uv, u2v], &out);
    if *body.concl() != crate::funspace::is_single_valued(env, &s.ap.sets, &ig) {
        return None
    }
    Some(gen_all(&[gv, av, rv, xv], &body))
}

/// `⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) →
///       app(app(ih(g,A,R,x), y), •) = app(g,y))` — **the beta rule of the
/// induction hypothesis**.
///
/// Applied at a predecessor `y` and at the proof `•` that `y` really is one, the
/// induction hypothesis gives back the recursive value. This is the statement
/// that makes the ι rule of [`crate::rec_acc`] say something: without it the
/// third argument of the step is an opaque set, and ι could be true of a
/// recursor that never recurses. With it, `app(g,y)` — for `g := accrec`, the
/// recursive call — is visibly inside the equation.
///
/// It is also exactly what a checker backend needs, since Lean's minor premise
/// for `Acc.rec` applies its induction hypothesis to `y` and to a proof of
/// `r y x`.
///
/// All four theorem arguments must be **unconditional**. This is the theorem
/// [`crate::rec_acc`]'s header lists among the closed non-vacuity facts — "the
/// recursive value is visibly inside the ι equation" — so a `Γ` on any premise
/// would falsify the module's own claim. The conclusion is pinned in release at
/// the end of `finish_ih_app`, which is also where a wrong `cval_app` is caught:
/// [`super::cval::cval_app`]'s output is the only source of the final `= app(g,y)`.
#[allow(clippy::too_many_arguments)]
pub fn ih_app(
    env: &mut Env,
    s: &Sums,
    ep: FnSym,
    ep_ax: &Thm,
    ih: FnSym,
    ih_ax: &Thm,
    sv: &Thm,
    cval_app: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[ep_ax, ih_ax, sv, cval_app]) {
        return None
    }
    let (gv, av, rv, xv, yv, y2v) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tx, ty, ty2) = (
        Term::var(gv),
        Term::var(av),
        Term::var(rv),
        Term::var(xv),
        Term::var(yv),
        Term::var(y2v),
    );
    let pt = s.point();
    let ig = ih_of(ih, tg.clone(), ta.clone(), tr.clone(), tx.clone());
    let ep_t = ep_of(ep, tr.clone(), ty.clone(), tx.clone());
    let gy = s.ap.apply(tg.clone(), ty.clone());
    let cval = cval_of(s, ep_t.clone(), gy.clone());
    let row = row_of(s, ep, &tg, &tr, &tx, &ty);

    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(s.ap.sets.pair(ty.clone(), tx.clone()), tr.clone());
    let h = Formula::and(mem_ya.clone(), edge.clone());
    let h_ya = and_left(mem_ya.clone(), edge.clone());
    let h_edge = and_right(mem_ya.clone(), edge.clone());

    // `y ∈ A → row(g,R,x,y) ∈ ih(g,A,R,x)`.
    let body = Formula::and(
        Formula::mem(ty2.clone(), ta.clone()),
        Formula::eq(row.clone(), row_of(s, ep, &tg, &tr, &tx, &ty2)),
    );
    let witness = hyp_and(
        &crate::imp_refl(mem_ya.clone()),
        &a1i(&Thm::eq_refl(row.clone()), mem_ya.clone()),
    )?;
    if *witness.concl() != Formula::imp(mem_ya.clone(), body.subst(y2v, &ty)) {
        return None
    }
    let ex = syl(&witness, &exists_intro_imp(y2v, body.clone(), ty.clone())?)?;
    let ih_at = inst_all(
        ih_ax,
        &[tg.clone(), ta.clone(), tr.clone(), tx.clone(), row.clone()],
    )?;
    if *ih_at.concl()
        != Formula::iff(Formula::mem(row.clone(), ig.clone()), Formula::exists(y2v, body))
    {
        return None
    }
    let mem_row = syl(&ex, &iff_mpr(&ih_at)?)?;

    // `app(ih,y) = cval(ep(R,y,x), app(g,y))`.
    let sv_at = inst_all(sv, &[tg.clone(), ta.clone(), tr.clone(), tx.clone()])?;
    finish_ih_app(
        env, s, ep_ax, cval_app, &h, &h_ya, &h_edge, &sv_at, &mem_row, &ig, &ep_t, &gy, &cval,
        &ty, &tx, &tr, &pt, &[gv, av, rv, xv, yv],
    )
}

/// The tail of [`ih_app`]: read the value off the graph, then apply the
/// conditional value at the proof.
#[allow(clippy::too_many_arguments)]
fn finish_ih_app(
    env: &mut Env,
    s: &Sums,
    ep_ax: &Thm,
    cval_app: &Thm,
    h: &Formula,
    h_ya: &Thm,
    h_edge: &Thm,
    sv_at: &Thm,
    mem_row: &Thm,
    ig: &Term,
    ep_t: &Term,
    gy: &Term,
    cval: &Term,
    ty: &Term,
    tx: &Term,
    tr: &Term,
    pt: &Term,
    vars: &[FreeVar],
) -> Option<Thm> {
    let app_of_graph = crate::recursion::app_of_graph(env, &s.ap)?;
    let aog = inst_all(&app_of_graph, &[ig.clone(), ty.clone(), cval.clone()])?;
    let h_mem = syl(h_ya, mem_row)?;
    let h_val = hyp_mp(
        &a1i(&aog, h.clone()),
        &hyp_and(&a1i(sv_at, h.clone()), &h_mem)?,
    )?;

    // `• ∈ ep(R,y,x)`, from the edge.
    let ep_at = inst_all(
        ep_ax,
        &[tr.clone(), ty.clone(), tx.clone(), pt.clone()],
    )?;
    let h_pt = syl(
        &hyp_and(&a1i(&s.unit_mem, h.clone()), h_edge)?,
        &iff_mpr(&ep_at)?,
    )?;
    let ca = inst_all(cval_app, &[ep_t.clone(), gy.clone()])?;
    let h_beta = hyp_mp(&a1i(&ca, h.clone()), &h_pt)?;

    // Carry `app(ih,y) = cval` through the outer application.
    let ap = s.ap.app;
    let pt2 = pt.clone();
    let h_outer = hyp_congr(env, &h_val, move |t| Term::apply(ap, vec![t, pt2.clone()]))?;
    let out = hyp_eq_trans(env, &h_outer, &h_beta)?;
    if *out.concl()
        != Formula::imp(
            h.clone(),
            Formula::eq(
                s.ap.apply(s.ap.apply(ig.clone(), ty.clone()), pt.clone()),
                gy.clone(),
            ),
        )
    {
        return None
    }
    Some(gen_all(vars, &out))
}
