//! The general recursor's hypothesis bundle `HYP` — **pointwise, not
//! curried**.
//!
//! # Why pointwise
//!
//! `wnat_rec`/`wlist_rec` state their hypothesis as a curried function-space
//! membership (`s ∈ fs(α, fs(lt(α), fs(T,T)))`). That does not generalise,
//! for a reason that has nothing to do with arity: a *dependent* telescope
//! (`β₁` mentioning `y₀`) has no iterated-`fs` type at all — the inner space
//! varies with the outer argument. So the general bundle is the pointwise
//! form, per constructor `i` with `k` non-recursive and `m` recursive fields:
//!
//! ```text
//! minor_typedᵢ(p⃗, sᵢ, T) :=
//!   ∀y₀ … y_{k−1} ∀t₀ … t_{m−1} ∀v₀ … v_{m−1}.
//!     (( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y₀…y_{j−1}) ∧ ⋀ⱼ tⱼ ∈ W ∧ ⋀ⱼ vⱼ ∈ T ))
//!       → sᵢ ⟪order mask over y⃗, t⃗⟫ v₀ … v_{m−1} ∈ T
//!
//! HYP := minor_typed₀ ∧ ( … ∧ minor_typed_{n−1})
//! ```
//!
//! This is strictly weaker than the curried form (which implies it by `k+2m`
//! applications of the function-space application rule), and weaker
//! hypotheses make the derived theorems stronger. The backend bridges from
//! whatever typing it can produce; for the corpus's non-dependent shapes that
//! is the `fs`-membership asked at the beta-reduced kernel term.
//!
//! Two deliberate choices, both load-bearing:
//!
//! * The recursive-argument slots `tⱼ` quantify over the **whole raw carrier
//!   `W`**, not over anything a constructor produces — because
//!   `step_typed`'s own quantification `∀f ∈ fs(B(a), W)` ranges over all
//!   functions, including ones no constructor produces, and the two must
//!   match for [`super::typed`]'s case analysis to close. (`W` here is the
//!   raw `W(A,B,U({A,T}))`; the abbreviation `ind(p⃗)` is one Leibniz away
//!   along `ty_ax` for any caller that has the Lean-shaped membership.)
//! * The application `sᵢ ⟪…⟫` is [`super::step::applied_minor`] — the same
//!   spelling the step value and the ι rules use, so the three cannot drift.
//!
//! For a nullary constructor the antecedent is empty and `minor_typedᵢ` is
//! the bare `sᵢ ∈ T`, mirroring how the carrier's constructor rule loses its
//! antecedent.
//!
//! # Interface
//!
//! [`minor_typed_at`] builds one conjunct; [`hyp_of`] the bundle; and
//! [`typed_atoms_at`] the antecedent alone, for the callers that project out of
//! it. All are formula builders (fresh bound variables each call — the
//! kernel's de-Bruijn closure makes the results α-invariantly equal), exported
//! so a caller discharging `HYP` can rebuild exactly what the theorems carry.
//!
//! **There is no plain-spelled entry point.** `minor_typedᵢ` at a declaration
//! whose `γⱼ` are all empty is [`minor_typed_at`] at `&[]`, and writing that
//! argument is the whole of the difference; a wrapper that hid it is what let
//! the indexed recursor layer state this conjunction plainly for five rounds
//! while the constructors it was about had function-typed fields.

use kernel::{Env, Formula, Term};

use crate::conj_of;
use crate::sums::Sums;

use super::spec::CtorSpec;
use super::step::applied_minor;

/// **`minor_typedᵢ`'s antecedent, atom by atom, at caller-chosen terms** — the
/// `k` argument typings, the `m` recursive slots at the carrier, the `m` values
/// at the target, each recursive one stated through `doms` exactly as
/// [`minor_typed_at`] states it.
///
/// `minor_typed_at` *is* this list quantified and implied, so a caller that has
/// to project out of that antecedent — [`super::guard::guarded_core`] and every
/// `lands` closure it calls — reads the atoms from here rather than respelling
/// them. **There is one spelling of this conjunction in the tree.** It had two
/// until an indexed family with a function-typed recursive argument made them
/// different formulas: the second was plain, and the projections out of a
/// general `k_h` stopped composing.
///
/// A short or absent `doms` means `None` at the missing slots, so the plain
/// spelling is this function at `&[]`.
#[allow(clippy::too_many_arguments)]
pub fn typed_atoms_at(
    s: &Sums,
    ctor: &CtorSpec,
    ps: &[Term],
    w: &Term,
    t: &Term,
    ys: &[Term],
    ts: &[Term],
    vs: &[Term],
    doms: &[Option<Term>],
) -> Vec<Formula> {
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    // The stated set of the `j`-th recursive slot: the carrier (or the target)
    // itself at a plain argument, and the function space out of `Aⱼ` at a
    // function-typed one.
    let stated = |j: usize, set: &Term| match doms.get(j).and_then(|d| d.as_ref()) {
        None => set.clone(),
        Some(a) => s.fs.of(a.clone(), set.clone()),
    };
    atoms.extend(ts.iter().enumerate().map(|(j, tj)| Formula::mem(tj.clone(), stated(j, w))));
    atoms.extend(vs.iter().enumerate().map(|(j, vj)| Formula::mem(vj.clone(), stated(j, t))));
    atoms
}

/// `minor_typedᵢ` with the recursive-argument slots **stated per slot**.
///
/// `doms[j]` is `None` for a plain recursive argument — `tⱼ ∈ W` and `vⱼ ∈ T`
/// — and `Some(Aⱼ)` for a function-typed one, where Lean's minor premise takes
/// the field's own **function** on `Aⱼ` and one induction hypothesis, also on
/// `Aⱼ`:
///
/// ```text
/// tⱼ ∈ fs(Aⱼ, W)        vⱼ ∈ fs(Aⱼ, T)
/// ```
///
/// A short or absent `doms` means `None` at the missing slots, which is
/// [`CtorSpec::rec_dom`]'s own convention for an absent `rec_doms`, and is how a
/// caller with no function-typed field anywhere spells the plain form.
///
/// **The choice is per recursive argument and not per constructor.** A
/// constructor with `γ₀ = ∅` and `γ₁ = [Bool]` takes
/// [`RecArg::general`](crate::recarg::RecArg::general) as a whole — that choice
/// *is* per constructor — while its first minor slot is still the plain
/// `t₀ ∈ W`, because Lean's first field is still a plain recursive occurrence.
/// [`Inductive::rec_slot_domains`](super::Inductive::rec_slot_domains) is the
/// single place that decides, so the four files on the recursor path cannot
/// disagree about which slot is which.
///
/// # One door, and why
///
/// A caller discharging `HYP` has to rebuild *exactly* what the theorems carry,
/// so this was landed as a *second* door beside a plain-spelled `minor_typed`
/// that `checker/src/tg.rs` was already calling. That wrapper is gone: it was
/// the second spelling of a conjunction whose two spellings agree on every
/// declaration with no function-typed recursive field, which is every
/// declaration in the corpus and none of the ones this generality exists for.
/// The plain form is this function at `doms = &[]`, written out at each site.
#[allow(clippy::too_many_arguments)]
pub fn minor_typed_at(
    env: &mut Env,
    s: &Sums,
    ctor: &CtorSpec,
    ps: &[Term],
    w: &Term,
    su: &Term,
    t: &Term,
    doms: &[Option<Term>],
) -> Formula {
    let (k, m) = (ctor.args.len(), ctor.recs);
    let yvs: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    let atoms = typed_atoms_at(s, ctor, ps, w, t, &ys, &ts, &vs, doms);

    let applied = applied_minor(&s.ap, &ctor.order, su, &ys, &ts, &vs);
    let concl = Formula::mem(applied, t.clone());
    let body = match conj_of(&atoms) {
        Some(h) => Formula::imp(h, concl),
        None => concl,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    quant.extend(vvs);
    quant.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc))
}

/// `HYP = minor_typed₀ ∧ ( … ∧ minor_typed_{n−1})`, right-nested. `None` for
/// a declaration with no constructors, which needs no recursor hypotheses and
/// no ι rule.
#[allow(clippy::too_many_arguments)]
pub fn hyp_of(
    env: &mut Env,
    s: &Sums,
    ctors: &[CtorSpec],
    ps: &[Term],
    w: &Term,
    minors: &[Term],
    t: &Term,
) -> Option<Formula> {
    let parts: Vec<Formula> = ctors
        .iter()
        .zip(minors)
        .map(|(c, su)| minor_typed_at(env, s, c, ps, w, su, t, &[]))
        .collect();
    conj_of(&parts)
}

/// The individual conjuncts of [`hyp_of`], for a caller that needs them as a
/// list — [`super::typed`] projects the `i`-th out of the bundle, and the
/// projection must be built over exactly these formulas.
pub fn minors_of(
    env: &mut Env,
    s: &Sums,
    ctors: &[CtorSpec],
    ps: &[Term],
    w: &Term,
    minors: &[Term],
    t: &Term,
) -> Vec<Formula> {
    minors_of_at(env, s, ctors, ps, w, minors, t, &[])
}

/// [`minors_of`] with each constructor's recursive slots stated per slot.
///
/// `doms[i]` is constructor `i`'s slice, in the shape [`minor_typed_at`] takes;
/// a short or absent `doms` means the plain spelling for the constructors it
/// does not reach, so this is [`minors_of`] at the empty slice.
#[allow(clippy::too_many_arguments)]
pub fn minors_of_at(
    env: &mut Env,
    s: &Sums,
    ctors: &[CtorSpec],
    ps: &[Term],
    w: &Term,
    minors: &[Term],
    t: &Term,
    doms: &[Vec<Option<Term>>],
) -> Vec<Formula> {
    ctors
        .iter()
        .zip(minors)
        .enumerate()
        .map(|(i, (c, su))| {
            let d = doms.get(i).map(|v| v.as_slice()).unwrap_or(&[]);
            minor_typed_at(env, s, c, ps, w, su, t, d)
        })
        .collect()
}
