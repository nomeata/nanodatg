//! **Step 1** — composition along a function, restricted to a domain.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀f ∀d ∀p. (p ∈ comp(g,f,d) ↔ ∃b. (b ∈ d ∧ p = ⟨b, app(g,app(f,b))⟩))   [compose]
//! ⊢ ∀g ∀h ∀f ∀d. (agree_on(g,h,f,d) → comp(g,f,d) = comp(h,f,d))             [compose_ext]
//! ```
//!
//! with [`comp_of`] building the term `comp(g,f,d)` and [`agree_on`] the
//! formula `∀b. (b ∈ d → app(g,app(f,b)) = app(h,app(f,b)))`. Callers need
//! none of the derivation below.
//!
//! # Why `comp` is shaped this way
//!
//! `comp(g,f,d)` is `g ∘ f` restricted to `d`, i.e. `{ ⟨b, g(f b)⟩ : b ∈ d }`,
//! introduced by Replacement along `b ↦ ⟨b, app(g,app(f,b))⟩` — the same shape
//! as [`crate::funcs::lambda`], which cannot be reused because it takes a
//! *unary function symbol* and the body here mentions the two parameters `g`
//! and `f`. The `∃!` premise is `∃!v. v = t`, which
//! [`crate::exists_unique_eq`] supplies for nothing.
//!
//! **The domain is a parameter, not read off `f`.** There is no domain operator
//! in this crate, and the recursion equation always has `B(a)` to hand, so
//! `comp` takes it. That also keeps `comp` free of any well-definedness side
//! condition: it is a total operation on three arbitrary sets.
//!
//! **[`compose_ext`] is the only fact the recursor needs about it** — no beta
//! rule, because the recursion equation never *applies* a composite, it only
//! compares two of them. It is proved by mutual inclusion, so
//! `compose_incl` is run twice with `g` and `h` swapped; the second run needs
//! the agreement hypothesis reversed, which is why it is a private helper
//! rather than the theorem itself.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_intro_imp, exists_unique_eq, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

/// Introduce `comp(g,f,d) = { ⟨b, app(g,app(f,b))⟩ : b ∈ d }`, with
///
/// ```text
/// ⊢ ∀g ∀f ∀d ∀p. (p ∈ comp(g,f,d) ↔ ∃b. (b ∈ d ∧ p = ⟨b, app(g,app(f,b))⟩))
/// ```
///
/// Replacement along `b ↦ ⟨b, app(g,app(f,b))⟩`. The `∃!` premise is
/// `∃!v. v = t`, which [`crate::exists_unique_eq`] supplies for nothing, so
/// this costs one Replacement instance and one [`crate::define_by_membership`].
pub fn compose(env: &mut Env, ap: &Apply) -> Option<(FnSym, Thm)> {
    let (gv, fv, dv, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tf, td, tb) = (Term::var(gv), Term::var(fv), Term::var(dv), Term::var(bv));

    let value = ap.apply(tg.clone(), ap.apply(tf.clone(), tb.clone()));
    let pair = ap.sets.pair(tb.clone(), value);

    let (pv, phi, exu) = exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, bv, pv, phi.clone())?;
    let repl_d = inst_all(&repl, std::slice::from_ref(&td))?;
    let premise = Thm::gen(bv, &a1i(&exu, Formula::mem(tb.clone(), td.clone())));
    let img = Thm::mp(&repl_d, &premise)?;

    let cond = Formula::exists(bv, Formula::and(Formula::mem(tb, td), phi));
    crate::define_by_membership(env, &[gv, fv, dv], &img, pv, &cond)
}

/// The term `comp(g,f,d)`.
pub fn comp_of(comp: FnSym, g: Term, f: Term, d: Term) -> Term {
    Term::apply(comp, vec![g, f, d])
}

/// `∀b. (b ∈ d → app(g,app(f,b)) = app(h,app(f,b)))` — "`g` and `h` agree
/// everywhere `f` lands on `d`", as a formula.
pub fn agree_on(env: &mut Env, ap: &Apply, g: &Term, h: &Term, f: &Term, d: &Term) -> Formula {
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let fb = ap.apply(f.clone(), tb.clone());
    Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tb, d.clone()),
            Formula::eq(ap.apply(g.clone(), fb.clone()), ap.apply(h.clone(), fb)),
        ),
    )
}

/// One inclusion of [`compose_ext`]: `⊢ agree_on(g,h,f,d) → comp(g,f,d) ⊆ … `,
/// as `⊢ H → (p ∈ comp(g,f,d) → p ∈ comp(h,f,d))` at the caller's `p`.
///
/// Split out because the other inclusion is this one with `g` and `h` swapped,
/// under the symmetric agreement.
#[allow(clippy::too_many_arguments)]
fn compose_incl(
    env: &mut Env,
    ap: &Apply,
    comp: FnSym,
    comp_ax: &Thm,
    g: &Term,
    h: &Term,
    f: &Term,
    d: &Term,
    p: &Term,
) -> Option<Thm> {
    let hyp = agree_on(env, ap, g, h, f, d);
    let bv = env.fresh_var();
    let tb = Term::var(bv);

    let fb = ap.apply(f.clone(), tb.clone());
    let val_g = ap.apply(g.clone(), fb.clone());
    let val_h = ap.apply(h.clone(), fb);
    let pair_g = ap.sets.pair(tb.clone(), val_g.clone());
    let pair_h = ap.sets.pair(tb.clone(), val_h.clone());

    let mem_bd = Formula::mem(tb.clone(), d.clone());
    let body_g = Formula::and(mem_bd.clone(), Formula::eq(p.clone(), pair_g.clone()));
    let body_h = Formula::and(mem_bd.clone(), Formula::eq(p.clone(), pair_h.clone()));

    // ── Work under `K := H ∧ body_g` ─────────────────────────────────────────
    let k = Formula::and(hyp.clone(), body_g.clone());
    let k_h = and_left(hyp.clone(), body_g.clone());
    let k_body = and_right(hyp.clone(), body_g.clone());
    let k_bd = syl(&k_body, &and_left(mem_bd.clone(), Formula::eq(p.clone(), pair_g.clone())))?;
    let k_peq = syl(&k_body, &and_right(mem_bd.clone(), Formula::eq(p.clone(), pair_g.clone())))?;

    // `K → g(f b) = h(f b)`.
    let k_agree = syl(&k_h, &Thm::ax_inst(hyp.clone(), tb.clone())?)?;
    let k_val = hyp_mp(&k_agree, &k_bd)?;

    // `K → ⟨b, g(f b)⟩ = ⟨b, h(f b)⟩`, two `upair` congruences deep.
    let hole = env.fresh_var();
    let up = ap.sets.up;
    let inner_hole = Term::apply(up, vec![tb.clone(), Term::var(hole)]);
    let outer = Term::apply(
        up,
        vec![Term::apply(up, vec![tb.clone(), tb.clone()]), inner_hole],
    );
    let k_pair = hyp_mp(
        &hyp_mp(
            &a1i(
                &Thm::eq_leibniz(val_g, val_h, hole, Formula::eq(pair_g.clone(), outer)),
                k.clone(),
            ),
            &k_val,
        )?,
        &a1i(&Thm::eq_refl(pair_g.clone()), k.clone()),
    )?;
    if *k_pair.concl() != Formula::imp(k.clone(), Formula::eq(pair_g.clone(), pair_h.clone())) {
        return None
    }

    // `K → p = ⟨b, h(f b)⟩`, by transitivity carried under the hypothesis.
    let hole2 = env.fresh_var();
    let trans = Thm::eq_leibniz(
        pair_g.clone(),
        pair_h.clone(),
        hole2,
        Formula::eq(p.clone(), Term::var(hole2)),
    );
    let k_ph = hyp_mp(&hyp_mp(&a1i(&trans, k.clone()), &k_pair)?, &k_peq)?;
    let k_body_h = hyp_and(&k_bd, &k_ph)?;
    if *k_body_h.concl() != Formula::imp(k.clone(), body_h.clone()) {
        return None
    }

    // ── Discharge the witness ────────────────────────────────────────────────
    let ex_h = Formula::exists(bv, body_h.clone());
    let k_ex = syl(&k_body_h, &exists_intro_imp(bv, body_h.clone(), tb.clone())?)?;
    let psi = Formula::imp(hyp.clone(), ex_h.clone());
    let per_b = crate::com12(&uncurry(&k_ex)?)?; // body_g → (H → ∃b. body_h)
    let discharged = crate::exists_elim_imp(bv, &Thm::gen(bv, &per_b), &psi)?;
    let h_ex = crate::com12(&discharged)?; // H → (∃b. body_g → ∃b. body_h)

    // ── Across the two membership conditions ─────────────────────────────────
    let cg = comp_of(comp, g.clone(), f.clone(), d.clone());
    let ch = comp_of(comp, h.clone(), f.clone(), d.clone());
    let ax_g = inst_all(comp_ax, &[g.clone(), f.clone(), d.clone(), p.clone()])?;
    let ax_h = inst_all(comp_ax, &[h.clone(), f.clone(), d.clone(), p.clone()])?;
    if *ax_g.concl() != Formula::iff(Formula::mem(p.clone(), cg.clone()), Formula::exists(bv, body_g))
        || *ax_h.concl() != Formula::iff(Formula::mem(p.clone(), ch.clone()), ex_h)
    {
        return None
    }
    let step1 = crate::funcs::hyp_syl(&a1i(&iff_mp(&ax_g)?, hyp.clone()), &h_ex)?;
    crate::funcs::hyp_syl(&step1, &a1i(&iff_mpr(&ax_h)?, hyp))
}

/// `⊢ ∀g ∀h ∀f ∀d. (agree_on(g,h,f,d) → comp(g,f,d) = comp(h,f,d))` —
/// **composites are determined by the values, not by the function**.
///
/// This is the only fact about `comp` the recursor needs. It replaces the beta
/// rule a `λ`-style composite would have to carry: the recursion equation never
/// applies `comp(g,f,d)` to anything, it only compares two of them.
pub fn compose_ext(env: &mut Env, ap: &Apply, comp: FnSym, comp_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (gv, hv, fv, dv, pv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, th, tf, td, tp) =
        (Term::var(gv), Term::var(hv), Term::var(fv), Term::var(dv), Term::var(pv));

    let hyp = agree_on(env, ap, &tg, &th, &tf, &td);
    let cg = comp_of(comp, tg.clone(), tf.clone(), td.clone());
    let ch = comp_of(comp, th.clone(), tf.clone(), td.clone());

    // `H → H⁻¹`: the agreement is symmetric, one `eq_symm` under the binder.
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let fb = ap.apply(tf.clone(), tb.clone());
    let sym_body = crate::imp_mono_r(
        &eq_symm_imp(env, ap.apply(tg.clone(), fb.clone()), ap.apply(th.clone(), fb)),
        Formula::mem(tb.clone(), td.clone()),
    )?;
    let h_sym = crate::forall_mono(bv, &Thm::gen(bv, &sym_body))?;
    let hyp_rev = agree_on(env, ap, &th, &tg, &tf, &td);
    if *h_sym.concl() != Formula::imp(hyp.clone(), hyp_rev.clone()) {
        return None
    }

    let fwd = compose_incl(env, ap, comp, comp_ax, &tg, &th, &tf, &td, &tp)?;
    let bwd_raw = compose_incl(env, ap, comp, comp_ax, &th, &tg, &tf, &td, &tp)?;
    let bwd = syl(&h_sym, &bwd_raw)?;

    let both = hyp_and(&fwd, &bwd)?;
    let iff = Formula::iff(Formula::mem(tp.clone(), cg.clone()), Formula::mem(tp, ch.clone()));
    if *both.concl() != Formula::imp(hyp.clone(), iff.clone()) {
        return None
    }

    let h_all = Thm::mp(&Thm::ax_dist(pv, hyp.clone(), iff)?, &Thm::gen(pv, &both))?;
    let out = syl(&h_all, &inst_all(&ext, &[cg.clone(), ch.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::eq(cg, ch)),
        "compose_ext: unexpected shape"
    );
    Some(gen_all(&[gv, hv, fv, dv], &out))
}
