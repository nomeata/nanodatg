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
//! [`minor_typed`] builds one conjunct; [`hyp_of`] the bundle. Both are
//! formula builders (fresh bound variables each call — the kernel's
//! de-Bruijn closure makes the results α-invariantly equal), exported so a
//! caller discharging `HYP` can rebuild exactly what the theorems carry.

use kernel::{Env, Formula, Term};

use crate::conj_of;
use crate::sums::Sums;

use super::spec::CtorSpec;
use super::step::applied_minor;

/// `minor_typedᵢ` for a constructor with argument types `ctor.args`, mask
/// `ctor.order`, at parameters `ps`, raw carrier `w`, minor `su` and target
/// `t`.
pub fn minor_typed(
    env: &mut Env,
    s: &Sums,
    ctor: &CtorSpec,
    ps: &[Term],
    w: &Term,
    su: &Term,
    t: &Term,
) -> Formula {
    let (k, m) = (ctor.args.len(), ctor.recs);
    let yvs: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|tj| Formula::mem(tj.clone(), w.clone())));
    atoms.extend(vs.iter().map(|vj| Formula::mem(vj.clone(), t.clone())));

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
        .map(|(c, su)| minor_typed(env, s, c, ps, w, su, t))
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
    ctors
        .iter()
        .zip(minors)
        .map(|(c, su)| minor_typed(env, s, c, ps, w, su, t))
        .collect()
}
