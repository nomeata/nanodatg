//! **`⊢ bnd(finord(m))`** — the bridge that lets the general inductive
//! translation's fibres bound the tower.
//!
//! # Interface
//!
//! Writing `Σ` for `finord(m) = Sum_m(1,…,1)`, `Iᵢ` for `Inj_i(•)`, `bnd` for
//! [`super::bounded::bnd`] and
//!
//! ```text
//! E(m) := {I₀} ∪ ({I₁} ∪ (… ∪ ({I_{m-1}} ∪ ∅)))
//! ```
//!
//! for the same set written out of its points, the exports are
//!
//! ```text
//! ⊢ finord(m) = E(m)                                       [finord_is_explicit]
//! ⊢ bnd(finord(m))                                         [bnd_finord]
//! ```
//!
//! both at **closed terms** and with no hypothesis, for each concrete `m`. The
//! second is the one two consumers want; the first is public because it is what
//! makes it true and is worth having on its own. [`bnd_finords`] is the second
//! at a whole declaration's recursive-argument counts, deriving
//! [`mod@super::finite`]'s three closure lemmas once rather than per
//! constructor.
//!
//! # Why this is needed, and why `finord(m) ∈ ω` is not an option
//!
//! [`super::tower_closed_bnd`] asks `bnd(B(a))` of every fibre, and
//! [`mod@super::bounded`] discharges that for `B(a) ∈ ω`. `crate::wnat` and
//! `crate::enums` have von Neumann naturals as fibres and are done there.
//!
//! The general translation does not. `crate::fibre` sends a constructor with
//! `m` recursive arguments to `finord(m)`, which is `1 + (1 + (… + 0))` — a set
//! with exactly `m` elements, but **not** the numeral `m`: `finord(1)` is
//! `1 + 0`, a set of ordered pairs, and `1` is `{∅}`. `finord(m) ∈ ω` is
//! therefore false and no amount of work would prove it. That is the blocker
//! this file removes, and with it the reason the checker could not replace its
//! three hand-written recognisers with the general path.
//!
//! # The route
//!
//! `finord(m)` has `m` named elements and [`crate::isum::ISumSyms::no_junk`]
//! says it has no others, so it *is* the union of `m` singletons — and
//! [`mod@super::finite`] proves `bnd` of exactly such a set. So:
//!
//! ```text
//! bnd(∅), bnd({Iᵢ}), bnd closed under ∪   ⇒   bnd(E(m))     super::finite
//! Σ = E(m)                                                  finord_is_explicit
//! bnd(Σ)                                                    Leibniz
//! ```
//!
//! Everything indexed by `m` happens in Rust, because `m` is a `usize`: the
//! translation knows a constructor's arity at translation time, so no induction
//! in the object language is needed and none is done. `finord_is_explicit` is
//! one Extensionality whose two halves are each an `m`-fold case analysis —
//! `no_junk` plus [`crate::sums::Sums::unit_eta`] forwards, the binary union's
//! elimination rule backwards.
//!
//! # What is *not* claimed
//!
//! Nothing here says `finord(m)` has `m` elements rather than fewer. It does —
//! [`crate::isum::ISumSyms::inj_distinct`] is exactly that, and `tests/isum.rs`
//! cashes it at `finord(3)` — but `bnd` does not need it and this file does not
//! use it. The statement proved would be just as true of a fibre with one
//! element, which is why the non-vacuity belongs in `isum` and stays there.

use kernel::{Env, Formula, Term, Thm};

use crate::isum::ISumSyms;
use crate::recursion::Rec;
use crate::sums::Sums;
use crate::{
    a1i, and_intro, ex_falso, eq_symm, eq_symm_imp, exists_elim_imp, hyp_or_elim, iff_mp, iff_mpr,
    imp_refl, inst_all, singleton, syl,
};

use super::stages::Stages;

/// `E(m) = {I₀} ∪ ({I₁} ∪ (… ∪ ({I_{m-1}} ∪ ∅)))`, and the tails `E(m)ᵢ`.
///
/// Index `i` is the tail starting at `Iᵢ`; `tails[m]` is `∅` and `tails[0]` is
/// the whole thing.
fn tails(r: &Rec, s: &Sums, syms: &ISumSyms, m: usize) -> Option<Vec<Term>> {
    let up = r.ap.sets.up;
    let mut out = vec![s.zero(); m + 1];
    for i in (0..m).rev() {
        let point = singleton(up, syms.inj(i, s.point())?);
        out[i] = crate::funspace::bin_union(&r.ap.sets, point, out[i + 1].clone());
    }
    Some(out)
}

/// `⊢ finord(m) = {I₀} ∪ ({I₁} ∪ (… ∪ ({I_{m-1}} ∪ ∅)))` — **the fibre written
/// out of its points**.
///
/// One Extensionality. Forwards is [`crate::isum::ISumSyms::no_junk`] followed
/// by `x ∈ 1 → x = •`, so each disjunct names one `Iᵢ`; backwards is the binary
/// union's elimination rule peeled `m` times, bottoming out on `z ∈ ∅`.
///
/// `syms` must have been [`crate::isum::ISumSyms::ensure`]d to arity `m` over
/// `s`, and `r` must share its `Apply` with `s` — the guard is that `r.zero()`
/// and `s.zero()` are the same term, since every set former below is taken from
/// one of the two.
pub fn finord_is_explicit(
    env: &mut Env,
    r: &Rec,
    s: &Sums,
    syms: &ISumSyms,
    m: usize,
) -> Option<Thm> {
    if r.zero() != s.zero() || !syms.is_over(s) {
        return None
    }
    let sets = r.ap.sets.clone();
    let sigma = syms.finord(s, m)?;
    let e = tails(r, s, syms, m)?;
    let summands = vec![s.unit(); m];

    let (zv, av, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tz, ta) = (Term::var(zv), Term::var(av));
    let in_e = Formula::mem(tz.clone(), e[0].clone());
    let in_sigma = Formula::mem(tz.clone(), sigma.clone());

    let mem_sing = r.core().mem_sing.clone();
    let (bu_left, bu_right) = crate::funspace::pow_pow::mem_bin_union(env, &sets)?;
    let bu_elim = super::step::mem_bin_union_elim(env, &sets)?;

    // ── Forwards: `z ∈ Σ → z ∈ E` ───────────────────────────────────────────
    //
    // `no_junk` reduces membership to the `m`-ary disjunction whose `i`-th
    // disjunct names `Iᵢ`; each is walked into `E` through one singleton and
    // `i` right-introductions of the union.
    let mut args = summands.clone();
    args.push(tz.clone());
    let junk = inst_all(&syms.no_junk(env, s, m)?, &args)?;
    let (junk_hyp, disj) = junk.concl().as_imp()?;
    if junk_hyp != in_sigma {
        return None
    }

    // `z ∈ {Iᵢ} → z ∈ E`: one left introduction, then `i` right ones.
    let into_e = |i: usize| -> Option<Thm> {
        let point = singleton(sets.up, syms.inj(i, s.point())?);
        let mut th = inst_all(&bu_left, &[point, e[i + 1].clone(), tz.clone()])?;
        for j in (0..i).rev() {
            let head = singleton(sets.up, syms.inj(j, s.point())?);
            th = syl(&th, &inst_all(&bu_right, &[head, e[j + 1].clone(), tz.clone()])?)?;
        }
        Some(th)
    };

    // The `i`-th disjunct, `∃a. (a ∈ 1 ∧ z = Inj_i(a))`, sent into `E`.
    let disjunct_case = |i: usize| -> Option<Thm> {
        let inj_a = syms.inj(i, ta.clone())?;
        let inj_pt = syms.inj(i, s.point())?;
        let atom = Formula::and(
            Formula::mem(ta.clone(), s.unit()),
            Formula::eq(tz.clone(), inj_a.clone()),
        );
        // `a ∈ 1 → a = •`, carried along `z = Inj_i(·)`.
        let to_point = syl(
            &inst_all(&s.unit_eta, std::slice::from_ref(&ta))?,
            &Thm::eq_leibniz(
                ta.clone(),
                s.point(),
                wv,
                Formula::eq(tz.clone(), syms.inj(i, Term::var(wv)).expect("depth is in range")),
            ),
        )?;
        let body = crate::hyp_mp(
            &crate::hyp_mp(
                &a1i(&to_point, atom.clone()),
                &crate::and_left(
                    Formula::mem(ta.clone(), s.unit()),
                    Formula::eq(tz.clone(), inj_a.clone()),
                ),
            )?,
            &crate::and_right(Formula::mem(ta.clone(), s.unit()), Formula::eq(tz.clone(), inj_a)),
        )?;
        // `z = Iᵢ → z ∈ {Iᵢ} → z ∈ E`.
        let land = syl(
            &iff_mpr(&inst_all(&mem_sing, &[inj_pt, tz.clone()])?)?,
            &into_e(i)?,
        )?;
        exists_elim_imp(av, &Thm::gen(av, &syl(&body, &land)?), &in_e)
    };

    // Fold the disjunction from its tail. `crate::disj_of` nests to the right
    // and puts **no** trailing `⊥` after the last atom, so the fold starts at
    // the last disjunct rather than at `⊥`; the empty case is `⊥` itself, which
    // is where `m = 0` lands.
    let atom = |i: usize| -> Option<Formula> {
        Some(Formula::exists(
            av,
            Formula::and(
                Formula::mem(ta.clone(), s.unit()),
                Formula::eq(tz.clone(), syms.inj(i, ta.clone())?),
            ),
        ))
    };
    let (mut fwd_tail, mut tail_form) = match m.checked_sub(1) {
        None => (ex_falso(in_e.clone()), Formula::false_()),
        Some(last) => (disjunct_case(last)?, atom(last)?),
    };
    for i in (0..m.saturating_sub(1)).rev() {
        let d_i = Formula::or(atom(i)?, tail_form.clone());
        fwd_tail = hyp_or_elim(
            &imp_refl(d_i.clone()),
            &a1i(&disjunct_case(i)?, d_i.clone()),
            &a1i(&fwd_tail, d_i.clone()),
        )?;
        tail_form = d_i;
    }
    if tail_form != disj {
        return None
    }
    let fwd = syl(&junk, &fwd_tail)?;

    // ── Backwards: `z ∈ E → z ∈ Σ` ──────────────────────────────────────────
    //
    // Peel one union at a time. `z ∈ {Iᵢ}` gives `z = Iᵢ`, and `Iᵢ ∈ Σ` is the
    // injection's membership rule at `• ∈ 1`.
    let mut bwd = syl(
        &inst_all(&r.ap.empty_ax, std::slice::from_ref(&tz))?,
        &ex_falso(in_sigma.clone()),
    )?;
    for i in (0..m).rev() {
        let inj_pt = syms.inj(i, s.point())?;
        let point = singleton(sets.up, inj_pt.clone());
        let hyp = Formula::mem(tz.clone(), e[i].clone());

        let mem_i = Thm::mp(
            &inst_all(syms.inj_mem(m, i)?, &{
                let mut a = summands.clone();
                a.push(s.point());
                a
            })?,
            &s.unit_mem,
        )?;
        if *mem_i.concl() != Formula::mem(inj_pt.clone(), sigma.clone()) {
            return None
        }
        // `z ∈ {Iᵢ} → z = Iᵢ → Iᵢ = z`, then Leibniz on `Iᵢ ∈ Σ`.
        let head = syl(
            &syl(
                &iff_mp(&inst_all(&mem_sing, &[inj_pt.clone(), tz.clone()])?)?,
                &eq_symm_imp(env, tz.clone(), inj_pt.clone()),
            )?,
            &Thm::eq_leibniz(
                inj_pt,
                tz.clone(),
                wv,
                Formula::mem(Term::var(wv), sigma.clone()),
            ),
        )?;
        let head = crate::mpd_const(&head, &mem_i)?;

        // `split`'s antecedent already *is* `z ∈ Eᵢ`, so it serves as the
        // disjunction premise unchanged; the two cases are weakened onto it.
        let split = inst_all(&bu_elim, &[point, e[i + 1].clone(), tz.clone()])?;
        if split.concl().as_imp()?.0 != hyp {
            return None
        }
        bwd = hyp_or_elim(&split, &a1i(&head, hyp.clone()), &a1i(&bwd, hyp))?;
    }

    // ── One Extensionality ──────────────────────────────────────────────────
    let same = Thm::gen(zv, &and_intro(&fwd, &bwd));
    let out = Thm::mp(
        &inst_all(&Thm::ax_extensionality(env), &[sigma.clone(), e[0].clone()])?,
        &same,
    )?;
    (out.hyps().is_empty() && *out.concl() == Formula::eq(sigma, e[0].clone())).then_some(out)
}

/// **`⊢ bnd(finord(m))`** — the fibre a constructor with `m` recursive
/// arguments gets bounds the tower.
///
/// [`super::finite`]'s three lemmas build `bnd` up the explicit union, and
/// [`finord_is_explicit`] moves it onto `finord(m)`. Unconditional, at closed
/// terms, for each concrete `m` — including `m = 0`, where `finord(0)` is the
/// *symbol* `Sum_0()` and not the term `∅`, so the equation is doing work even
/// there.
pub fn bnd_finord(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    m: usize,
) -> Option<Thm> {
    Some(bnd_finords(env, r, st, s, syms, std::slice::from_ref(&m))?.remove(0))
}

/// [`bnd_finord`] at every arity a declaration uses, deriving
/// [`mod@super::finite`]'s three lemmas **once**.
///
/// A declaration with `n` constructors needs `n` of these, and the three
/// closure lemmas do not depend on `m`; re-deriving them per constructor is the
/// only thing that would make this quadratic in the declaration. `counts[i]` is
/// the `i`-th constructor's recursive-argument count, exactly as
/// [`crate::fibre::Fibre::new`] takes it.
pub fn bnd_finords(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    counts: &[usize],
) -> Option<Vec<Thm>> {
    let empty = super::finite::bnd_empty(env, r, st)?;
    let sing = super::finite::bnd_singleton(env, r, st)?;
    let union = super::finite::bnd_bin_union(env, r, st)?;
    counts
        .iter()
        .map(|&m| one(env, r, st, s, syms, m, &empty, &sing, &union))
        .collect()
}

/// One arity, over closure lemmas the caller already has.
#[allow(clippy::too_many_arguments)]
fn one(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    m: usize,
    empty: &Thm,
    sing: &Thm,
    union: &Thm,
) -> Option<Thm> {
    let eq = finord_is_explicit(env, r, s, syms, m)?;
    let e = tails(r, s, syms, m)?;
    let sigma = syms.finord(s, m)?;

    let mut acc = empty.clone();
    for i in (0..m).rev() {
        let inj_pt = syms.inj(i, s.point())?;
        let point = singleton(r.ap.sets.up, inj_pt.clone());
        let at = inst_all(union, &[point, e[i + 1].clone()])?;
        acc = Thm::mp(
            &at,
            &and_intro(&inst_all(sing, std::slice::from_ref(&inj_pt))?, &acc),
        )?;
    }
    if *acc.concl() != super::bounded::bnd(env, r, st, &e[0]) {
        return None
    }

    // `E = Σ` carries `bnd(E)` to `bnd(Σ)`.
    let wv = env.fresh_var();
    let hole = super::bounded::bnd(env, r, st, &Term::var(wv));
    let out = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(e[0].clone(), sigma.clone(), wv, hole),
            &eq_symm(env, &eq)?,
        )?,
        &acc,
    )?;
    let expected = super::bounded::bnd(env, r, st, &sigma);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
