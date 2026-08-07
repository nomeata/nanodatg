//! **The range of a set relation** — `ran(g) = { y : ∃a. ⟨a,y⟩ ∈ g }`, with the
//! two facts that make it usable as a *codomain*.
//!
//! # Why it is wanted
//!
//! A [`crate::isum::Dispatch`] over branch **variables** cannot take its
//! codomain as a parameter: the dispatcher's *term* mentions its codomain, so a
//! constructor built over one would mention a set that is not part of the
//! constructor's data. The codomain has to be **built from the branches**. At
//! `γ = ∅` the branches are one-point graphs and
//! [`crate::finset::FinSet::of`] is that set; at a general `γ` the branches are
//! functions `gⱼ` and the codomain is `⋃ⱼ ran(gⱼ)`.
//!
//! [`snd_in_union2`](crate::funcs::snd_in_union2) — `⟨a,y⟩ ∈ f → y ∈ ⋃⋃f` —
//! looks like it would serve and **does not**. `⟨a,y⟩` is `{{a},{a,y}}`, so
//! `⋃⋃f` holds the *domain* elements as well as the values, and `⋃⋃gⱼ ⊆ W` is
//! therefore false exactly when the fibre is not itself inside the carrier —
//! which is the case a general fibre exists for. So a genuine range is forced.
//! `⋃⋃g` survives as the **superset Separation is taken over**, which is all it
//! was ever good for here.
//!
//! # Interface
//!
//! [`Ran::new`] introduces the symbol and derives
//!
//! ```text
//! ⊢ ∀g ∀y. (y ∈ ran(g) ↔ ∃a. ⟨a,y⟩ ∈ g)                            [Ran::mem]
//! ⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → ran(g) ⊆ S)                        [Ran::subset]
//! ⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → g ∈ fs(A, ran(g)))               [Ran::retarget]
//! ```
//!
//! [`Ran::mem`] is **unconditional** — one
//! [`separation_full`](crate::funcs::separation_full) over `⋃⋃g`, with the
//! `y ∈ ⋃⋃g` conjunct Separation leaves behind erased by the very inclusion
//! that justified the superset. The term is [`Ran::of`].
//!
//! The two typed rules are the pair a codomain-builder needs and they pull in
//! opposite directions: [`Ran::retarget`] says `ran(g)` is **big enough** to
//! serve as a codomain for `g`, and [`Ran::subset`] says it is **small enough**
//! to be widened back to any real codomain `g` already had — which is the same
//! division of labour [`crate::finset`] has, and the same place the caller's
//! hypothesis is paid: once, in an inclusion, rather than once per branch.
//!
//! # Non-vacuity
//!
//! [`Ran::subset`] alone would hold of `ran(g) := ∅` and [`Ran::retarget`]
//! would not; [`Ran::retarget`] alone would hold of `ran(g) := V` and
//! [`Ran::subset`] would not. `tests/ran.rs` pins both against a concrete
//! one-point graph, where `ran({⟨•,r⟩})` is inhabited by `r` and included in
//! every set holding `r`.
//!
//! # Nothing here is an axiom
//!
//! One [`separation_full`](crate::funcs::separation_full), the Union axiom
//! through [`snd_in_union2`](crate::funcs::snd_in_union2), and the function
//! space's own characterisation
//! ([`funspace_members`](crate::funspace::funspace_members)). One new symbol,
//! `ran`, defined by its membership condition.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{hyp_syl, separation_full, snd_in_union2, Sets};
use crate::funspace::{is_function, is_single_valued, is_total};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, com12, com12_imp, curry, eq_symm_imp, exists_elim_imp,
    exists_intro_imp, exists_mono, gen_all, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp,
    iff_mpr, imp_mono_r, imp_refl, inst_all, syl, uncurry,
};

/// The range symbol with its three theorems.
pub struct Ran {
    /// The symbol `ran`, of arity 1.
    pub ran: FnSym,
    /// `⊢ ∀g ∀y. (y ∈ ran(g) ↔ ∃a. ⟨a,y⟩ ∈ g)` — **unconditional**.
    pub mem: Thm,
    /// `⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → ran(g) ⊆ S)`.
    pub subset: Thm,
    /// `⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → g ∈ fs(A, ran(g)))`.
    pub retarget: Thm,
}

impl Ran {
    /// The term `ran(g)`.
    pub fn of(&self, g: Term) -> Term { Term::apply(self.ran, vec![g]) }

    /// Introduce `ran` and derive all three theorems over the caller's
    /// [`Sums`] — so the pairing, the product and the function space are the
    /// ones every other construction in the same development uses.
    pub fn new(env: &mut Env, s: &Sums) -> Option<Ran> {
        let snd = snd_in_union2(env, &s.ap.sets).ok()?;
        let (ran, mem) = range_symbol(env, s, &snd)?;
        let subset = range_subset(env, s, ran, &mem)?;
        let retarget = range_retarget(env, s, ran, &mem)?;
        Some(Ran { ran, mem, subset, retarget })
    }
}

/// `⟨a,y⟩ ∈ g → y ∈ ran(g)`, at caller-supplied terms.
///
/// The one step both typed rules spend, and the only place `mem`'s backward
/// half is used: one existential introduction at the given first component.
fn pair_in_range(
    env: &mut Env,
    sets: &Sets,
    mem_ax: &Thm,
    g: &Term,
    a: &Term,
    y: &Term,
) -> Option<Thm> {
    let bv = env.fresh_var();
    let body = Formula::mem(sets.pair(Term::var(bv), y.clone()), g.clone());
    let intro = exists_intro_imp(bv, body, a.clone())?;
    syl(&intro, &iff_mpr(&inst_all(mem_ax, &[g.clone(), y.clone()])?)?)
}

/// The symbol, with `⊢ ∀g ∀y. (y ∈ ran(g) ↔ ∃a. ⟨a,y⟩ ∈ g)`.
///
/// Separation over `⋃⋃g`, then the same swap
/// [`value_collection`](crate::funcs::separation_full)'s neighbour performs:
/// the inclusion that made `⋃⋃g` a legitimate superset also erases the
/// `y ∈ ⋃⋃g` conjunct, so the condition defined is the intended one and carries
/// no antecedent.
fn range_symbol(env: &mut Env, s: &Sums, snd: &Thm) -> Option<(FnSym, Thm)> {
    let sets = &s.ap.sets;
    let (g, y, a) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, ty, ta) = (Term::var(g), Term::var(y), Term::var(a));
    let uug = sets.union_of(sets.union_of(tg.clone()));

    let l = Formula::exists(a, Formula::mem(sets.pair(ta.clone(), ty.clone()), tg.clone()));
    let mem_uu = Formula::mem(ty.clone(), uug.clone());
    let sep_cond = Formula::and(mem_uu.clone(), l.clone());

    let sep = separation_full(env, y, &l, &uug, &s.ap.empty_ax).ok()?;

    // ⊢ (∃a. ⟨a,y⟩ ∈ g) → y ∈ ⋃⋃g, and hence `L ↔ (y ∈ ⋃⋃g ∧ L)`.
    let l_to_uu = {
        let at = inst_all(snd, &[tg.clone(), ta.clone(), ty.clone()])?;
        exists_elim_imp(a, &Thm::gen(a, &at), &mem_uu)?
    };
    let l_to_both = hyp_and(&l_to_uu, &imp_refl(l.clone()))?;
    let both_to_l = and_right(mem_uu, l.clone());

    let sv = env.fresh_var();
    let mem_ys = Formula::mem(ty.clone(), Term::var(sv));
    let p_s = Formula::forall(y, Formula::iff(mem_ys.clone(), sep_cond));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(sv, p_s.clone()),
        "ran: Separation has an unexpected shape"
    );

    let p_inst = Thm::ax_inst(p_s.clone(), ty.clone())?;
    let p_fwd = hyp_syl(&hyp_iff_mp(&p_inst)?, &a1i(&both_to_l, p_s.clone()))?;
    let p_bwd = hyp_syl(&a1i(&l_to_both, p_s.clone()), &hyp_iff_mpr(&p_inst)?)?;
    let p_q = Thm::mp(
        &Thm::ax_dist(y, p_s.clone(), Formula::iff(mem_ys.clone(), l.clone()))?,
        &Thm::gen(y, &hyp_and(&p_fwd, &p_bwd)?),
    )?;
    let existence = Thm::mp(&exists_mono(sv, &Thm::gen(sv, &p_q))?, &sep)?;

    crate::define_by_membership(env, &[g], &existence, y, &l)
}

/// The three formulas `f ∈ fs(a,b)` unfolds to, rebuilt so that the derivations
/// below can take them apart — and checked against
/// [`is_function`](crate::funspace::is_function), which is what `fs`'s own axiom
/// is stated over.
fn isfun_parts(env: &mut Env, s: &Sums, a: &Term, b: &Term, f: &Term) -> (Formula, Formula, Formula) {
    let sets = &s.ap.sets;
    let sub = kernel::thm::subset(env, f.clone(), s.prod.of(a.clone(), b.clone()));
    let total = is_total(env, sets, a, b, f);
    let single = is_single_valued(env, sets, f);
    debug_assert_eq!(
        Formula::and(sub.clone(), Formula::and(total.clone(), single.clone())),
        is_function(env, sets, &s.prod, a, b, f),
        "ran: isfun's shape has drifted"
    );
    (sub, total, single)
}

/// `⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → ran(g) ⊆ S)`.
///
/// A member of `ran(g)` is the second component of some pair in `g`; `g` is a
/// subset of `A × S`, and [`Sums::pair_in_prod`](crate::sums::Sums) reads the
/// second component's membership straight off. The existential is discharged by
/// [`exists_elim_imp`], which is legal because the goal `y ∈ S` does not mention
/// the first component.
fn range_subset(env: &mut Env, s: &Sums, ran: FnSym, mem_ax: &Thm) -> Option<Thm> {
    let sets = s.ap.sets.clone();
    let (av, tv, gv, yv, bv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, ts, tg, ty, tb) =
        (Term::var(av), Term::var(tv), Term::var(gv), Term::var(yv), Term::var(bv));
    let rg = Term::apply(ran, vec![tg.clone()]);

    let h = Formula::mem(tg.clone(), s.fs.of(ta.clone(), ts.clone()));
    let (sub, total, single) = isfun_parts(env, s, &ta, &ts, &tg);

    // ⊢ H → g ⊆ A × S
    let h_sub = syl(
        &iff_mp(&inst_all(&s.fs.fs_ax, &[ta.clone(), ts.clone(), tg.clone()])?)?,
        &and_left(sub.clone(), Formula::and(total, single)),
    )?;

    // ⊢ H → (⟨b,y⟩ ∈ g → y ∈ S)
    let pair = sets.pair(tb.clone(), ty.clone());
    let in_g = Formula::mem(pair.clone(), tg.clone());
    let y_in_s = Formula::mem(ty.clone(), ts.clone());
    let to_s = syl(
        &iff_mp(&inst_all(
            &s.pair_in_prod,
            &[ta.clone(), ts.clone(), tb.clone(), ty.clone()],
        )?)?,
        &and_right(Formula::mem(tb.clone(), ta.clone()), y_in_s.clone()),
    )?;
    let h_step = syl(
        &syl(&h_sub, &Thm::ax_inst(sub.clone(), pair)?)?,
        &imp_mono_r(&to_s, in_g)?,
    )?;

    // Discharge the existential, then read `y ∈ ran(g)` through `mem`.
    let psi = Formula::imp(h.clone(), y_in_s.clone());
    let ex_step = exists_elim_imp(bv, &Thm::gen(bv, &com12(&h_step)?), &psi)?;
    let body = com12(&syl(
        &iff_mp(&inst_all(mem_ax, &[tg.clone(), ty.clone()])?)?,
        &ex_step,
    )?)?;

    let (_, inner) = body.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(yv, h.clone(), inner)?, &Thm::gen(yv, &body))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, rg, ts)),
        "ran: subset has the wrong shape"
    );
    Some(gen_all(&[av, tv, gv], &out))
}

/// `⊢ ∀A ∀S ∀g. (g ∈ fs(A,S) → g ∈ fs(A, ran(g)))`.
///
/// Three clauses, and only two of them move. Single-valuedness does not mention
/// the codomain at all. Totality weakens `y ∈ S` to `y ∈ ran(g)` **without any
/// hypothesis**, because the same existential quantifier already supplies
/// `⟨x,y⟩ ∈ g`. The inclusion `g ⊆ A × ran(g)` is the one that costs something:
/// an arbitrary member `z` of `g` has to be decomposed through
/// [`Product::prod_ax`](crate::funspace::Product) before its second component
/// can be named, and `z ∈ g` has to be carried across `z = ⟨x,y⟩` to reach
/// `⟨x,y⟩ ∈ g`.
fn range_retarget(env: &mut Env, s: &Sums, ran: FnSym, mem_ax: &Thm) -> Option<Thm> {
    let sets = s.ap.sets.clone();
    let (av, tv, gv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ts, tg) = (Term::var(av), Term::var(tv), Term::var(gv));
    let rg = Term::apply(ran, vec![tg.clone()]);

    let h = Formula::mem(tg.clone(), s.fs.of(ta.clone(), ts.clone()));
    let (sub, total, single) = isfun_parts(env, s, &ta, &ts, &tg);
    let (sub_r, total_r, single_r) = isfun_parts(env, s, &ta, &rg, &tg);
    debug_assert_eq!(single, single_r, "ran: single-valuedness mentions the codomain");

    let unfolded = iff_mp(&inst_all(&s.fs.fs_ax, &[ta.clone(), ts.clone(), tg.clone()])?)?;
    let tail = Formula::and(total.clone(), single.clone());
    let h_sub = syl(&unfolded, &and_left(sub.clone(), tail.clone()))?;
    let h_tail = syl(&unfolded, &and_right(sub.clone(), tail))?;
    let h_total = syl(&h_tail, &and_left(total.clone(), single.clone()))?;
    let h_single = syl(&h_tail, &and_right(total.clone(), single.clone()))?;

    let h_total_r =
        retarget_total(env, &sets, mem_ax, &h, &h_total, &total, &total_r, &ta, &ts, &tg, &rg)?;
    let h_sub_r = retarget_sub(env, s, &sets, mem_ax, &h, &h_sub, &sub, &sub_r, &ta, &ts, &tg, &rg)?;

    let isfun = hyp_and(&h_sub_r, &hyp_and(&h_total_r, &h_single)?)?;
    let out = syl(
        &isfun,
        &iff_mpr(&inst_all(&s.fs.fs_ax, &[ta.clone(), rg.clone(), tg.clone()])?)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tg, s.fs.of(ta, rg))),
        "ran: retarget has the wrong shape"
    );
    Some(gen_all(&[av, tv, gv], &out))
}

/// `⊢ H → is_total(A, ran(g), g)` from `⊢ H → is_total(A, S, g)`.
///
/// The body map is **unconditional**: the witness `y` of `∃y. (y ∈ S ∧ ⟨x,y⟩ ∈ g)`
/// carries its own membership in `ran(g)` in the second conjunct, so nothing
/// about `S` is needed to move it.
#[allow(clippy::too_many_arguments)]
fn retarget_total(
    env: &mut Env,
    sets: &Sets,
    mem_ax: &Thm,
    h: &Formula,
    h_total: &Thm,
    total: &Formula,
    total_r: &Formula,
    ta: &Term,
    ts: &Term,
    tg: &Term,
    rg: &Term,
) -> Option<Thm> {
    let (xv, wv) = (env.fresh_var(), env.fresh_var());
    let (tx, tw) = (Term::var(xv), Term::var(wv));

    let w_in_s = Formula::mem(tw.clone(), ts.clone());
    let w_in_r = Formula::mem(tw.clone(), rg.clone());
    let pxw = Formula::mem(sets.pair(tx.clone(), tw.clone()), tg.clone());

    let to_ran = pair_in_range(env, sets, mem_ax, tg, &tx, &tw)?;
    let body = hyp_and(
        &syl(&and_right(w_in_s.clone(), pxw.clone()), &to_ran)?,
        &and_right(w_in_s.clone(), pxw.clone()),
    )?;
    debug_assert_eq!(
        *body.concl(),
        Formula::imp(
            Formula::and(w_in_s.clone(), pxw.clone()),
            Formula::and(w_in_r.clone(), pxw.clone())
        ),
        "ran: the totality body map has the wrong shape"
    );
    let mono = exists_mono(wv, &Thm::gen(wv, &body))?;

    let x_in_a = Formula::mem(tx.clone(), ta.clone());
    let at_x = syl(h_total, &Thm::ax_inst(total.clone(), tx.clone())?)?;
    let widened = syl(&at_x, &imp_mono_r(&mono, x_in_a.clone())?)?;
    let (_, inner) = widened.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(xv, h.clone(), inner)?, &Thm::gen(xv, &widened))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h.clone(), total_r.clone()),
        "ran: retargeted totality has the wrong shape"
    );
    Some(out)
}

/// `⊢ H → g ⊆ A × ran(g)` from `⊢ H → g ⊆ A × S`.
///
/// The one clause that needs the product's characterisation. Under
/// `K := (y ∈ S ∧ z = ⟨x,y⟩) ∧ (x ∈ A ∧ z ∈ g)` the equation carries `z ∈ g` to
/// `⟨x,y⟩ ∈ g`, which puts `y` in `ran(g)`, and
/// [`Sums::pair_in_prod`](crate::sums::Sums) rebuilds the pair in
/// `A × ran(g)`; the equation then carries that back to `z`. Both existentials
/// are discharged with [`exists_elim_imp`], whose side condition holds because
/// neither `z ∈ g` nor `z ∈ A × ran(g)` mentions a witness.
#[allow(clippy::too_many_arguments)]
fn retarget_sub(
    env: &mut Env,
    s: &Sums,
    sets: &Sets,
    mem_ax: &Thm,
    h: &Formula,
    h_sub: &Thm,
    sub: &Formula,
    sub_r: &Formula,
    ta: &Term,
    ts: &Term,
    tg: &Term,
    rg: &Term,
) -> Option<Thm> {
    let (zv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tz, tx, ty) = (Term::var(zv), Term::var(xv), Term::var(yv));

    let pair = sets.pair(tx.clone(), ty.clone());
    let prod_r = s.prod.of(ta.clone(), rg.clone());
    let z_in_g = Formula::mem(tz.clone(), tg.clone());
    let z_in_r = Formula::mem(tz.clone(), prod_r.clone());
    let x_in_a = Formula::mem(tx.clone(), ta.clone());
    let y_in_s = Formula::mem(ty.clone(), ts.clone());
    let z_eq = Formula::eq(tz.clone(), pair.clone());

    // ── under `K`, rebuild the pair in `A × ran(g)` ─────────────────────────
    let e = Formula::and(y_in_s.clone(), z_eq.clone());
    let c = Formula::and(x_in_a.clone(), z_in_g.clone());
    let k = Formula::and(e.clone(), c.clone());
    let k_e = and_left(e.clone(), c.clone());
    let k_c = and_right(e.clone(), c.clone());
    let k_eq = syl(&k_e, &and_right(y_in_s.clone(), z_eq.clone()))?;
    let k_zg = syl(&k_c, &and_right(x_in_a.clone(), z_in_g.clone()))?;
    let k_xa = syl(&k_c, &and_left(x_in_a.clone(), z_in_g.clone()))?;

    let hole = env.fresh_var();
    let fwd = Thm::eq_leibniz(
        tz.clone(),
        pair.clone(),
        hole,
        Formula::mem(Term::var(hole), tg.clone()),
    );
    let k_pair_g = hyp_mp(&hyp_mp(&a1i(&fwd, k.clone()), &k_eq)?, &k_zg)?;
    let k_y_ran = syl(&k_pair_g, &pair_in_range(env, sets, mem_ax, tg, &tx, &ty)?)?;
    let k_in_prod = syl(
        &hyp_and(&k_xa, &k_y_ran)?,
        &iff_mpr(&inst_all(
            &s.pair_in_prod,
            &[ta.clone(), rg.clone(), tx.clone(), ty.clone()],
        )?)?,
    )?;
    let hole2 = env.fresh_var();
    let back = Thm::eq_leibniz(
        pair.clone(),
        tz.clone(),
        hole2,
        Formula::mem(Term::var(hole2), prod_r.clone()),
    );
    let k_eq_sym = syl(&k_eq, &eq_symm_imp(env, tz.clone(), pair.clone()))?;
    let k_goal = hyp_mp(&hyp_mp(&a1i(&back, k.clone()), &k_eq_sym)?, &k_in_prod)?;

    // ── discharge `∃y`, then `∃x` ───────────────────────────────────────────
    let inner_psi = Formula::imp(c.clone(), z_in_r.clone());
    let at_y = exists_elim_imp(yv, &Thm::gen(yv, &uncurry(&k_goal)?), &inner_psi)?;
    let ex_y = Formula::exists(yv, e.clone());

    // `EX → ((x ∈ A ∧ z ∈ g) → G)` becomes `(x ∈ A ∧ EX) → (z ∈ g → G)`.
    let swapped = uncurry(&com12(&at_y)?)?;
    let regrouped = curry(&Thm::mp(
        &imp_mono_r(
            &com12_imp(z_in_g.clone(), ex_y.clone(), z_in_r.clone()),
            x_in_a.clone(),
        )?,
        &swapped,
    )?)?;
    let outer_psi = Formula::imp(z_in_g.clone(), z_in_r.clone());
    let at_x = exists_elim_imp(xv, &Thm::gen(xv, &regrouped), &outer_psi)?;

    // ── feed it the product's characterisation, under `H` ───────────────────
    let p_to_g = syl(
        &iff_mp(&inst_all(&s.prod.prod_ax, &[ta.clone(), ts.clone(), tz.clone()])?)?,
        &at_x,
    )?;
    let h_z = syl(h_sub, &Thm::ax_inst(sub.clone(), tz.clone())?)?;
    let u1 = curry(&h_z)?;
    let u2 = syl(&and_right(h.clone(), z_in_g.clone()), &com12(&p_to_g)?)?;
    let body = uncurry(&hyp_mp(&u2, &u1)?)?;

    let (_, inner) = body.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(zv, h.clone(), inner)?, &Thm::gen(zv, &body))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h.clone(), sub_r.clone()),
        "ran: the retargeted inclusion has the wrong shape"
    );
    Some(out)
}
