//! **`∀`-extensionality**: two conditional singletons over pointwise-equal
//! bounded families are the same set.
//!
//! # Interface
//!
//! For two fibre symbols `b` of arity `k+1` and `b'` of arity `k'+1`, and two
//! symbols `chi`/`chi'` introduced by [`super::conditional_singleton`] on the
//! formulas
//!
//! ```text
//! φ (p⃗,A)  :=  ∀x. (x ∈ A  → • ∈ b(p⃗,x))
//! φ'(q⃗,A') :=  ∀x. (x ∈ A' → • ∈ b'(q⃗,x))
//! ```
//!
//! — that is, carrying `⊢ ∀z. (z ∈ chi(p⃗,A) ↔ (z ∈ 1 ∧ φ(p⃗,A)))` and likewise
//! for `chi'` — the single export is
//!
//! ```text
//! ⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(p⃗,x) = b'(q⃗,x)))
//!                              → chi(p⃗,A) = chi'(q⃗,A')))          [cond_ext_n]
//! ```
//!
//! The two prefixes are independent and need not have the same length. The two
//! characteristic theorems are instantiated and *compared against the shape
//! claimed* before anything rests on them, so a mismatched conditional
//! singleton is refused with `None` rather than silently described, and each is
//! additionally required to be **unconditional** — see "The `Hyp` layer does
//! not carry kernel hypotheses" below for why that check is not optional here.
//!
//! # Why this is needed
//!
//! It is the [`crate::ext::dprod_ext_n`] of the *other* clause of Carneiro
//! §6.2: a `Prop`-valued `∀x : α. β` interprets to `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`, a
//! conditional singleton, rather than to a dependent product. Two such `∀`s
//! whose bodies have different shapes are built over different, unrelated
//! symbols, and congruence over sub-terms relates nothing.
//!
//! What relates them is that the two singletons are conditional on *equivalent*
//! formulas: `[φ] = {x ∈ 1 : φ}` and `[φ'] = {x ∈ 1 : φ'}` have the same
//! members as soon as `φ ↔ φ'`, and `φ ↔ φ'` is exactly what the domain
//! equation and the pointwise premise give. Extensionality then finishes it.
//!
//! # Written against [`crate::hyp::Hyp`]
//!
//! That layer is documented as superseded and is not to be *built on* — nothing
//! else depends on this construction, and the alternative here was a hundred
//! lines of `hyp_syl`/`a1i` plumbing whose only reader would be its author. The
//! theorem it produces is an ordinary [`Thm`] like any other, and a caller
//! derives it once per pair of skeletons and memoises it.
//!
//! # The [`Hyp`] layer does not carry kernel hypotheses
//!
//! [`Hyp`] tracks the antecedents *this derivation* introduces with
//! [`Hyp::assume`], and every one of them is discharged before the end. It says
//! nothing about the `Γ` of a theorem that arrives already carrying one:
//! [`Hyp::lift`] sets `hyps: []` and wraps the theorem as `⊢ ⊤ → φ`, so a
//! kernel hypothesis on `chi_ax` is invisible to the whole layer and rides
//! straight out through [`Hyp::into_thm`] — which checks only that the *`Hyp`'s*
//! own list is empty. A `concl()` comparison cannot see it either. Hence the
//! guard below pins the conclusion **and** demands `hyps().is_empty()`, via
//! [`crate::establishes`]: without the second half, a `Thm::assume` of exactly
//! the closed formula [`super::conditional_singleton`] produces would satisfy
//! the shape check and its own antecedent would end up in the `Γ` of the
//! theorem the statement above calls `⊢`.
//!
//! Nothing here is trusted. A mistake yields `None` — hence a reported gap —
//! rather than a false theorem, and the final conclusion is checked against the
//! statement above in release as well as debug.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::hyp::Hyp;
use crate::sums::Sums;
use crate::{gen_all, inst_all};

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(p⃗,x) = b'(q⃗,x))) → chi(p⃗,A) = chi'(q⃗,A')))`
/// — **`∀`-extensionality**: the [`crate::ext::dprod_ext_n`] of §6.2's other
/// clause.
///
/// `a` is `(b, chi, chi_ax)` for the left-hand `∀` and `b` the same for the
/// right, with `chi_ax` the characteristic theorem
/// [`super::conditional_singleton`] returns. Each `chi_ax` must **establish**
/// that theorem — right conclusion *and* empty hypothesis set. The hypothesis
/// half is checked here rather than left to [`Hyp`]: that layer's `hyps` list
/// records only what this derivation itself assumed, so a caller's `Γ` passes
/// through [`Hyp::lift`] and [`Hyp::into_thm`] unremarked. See the module
/// header.
pub fn cond_ext_n(
    env: &mut Env,
    sums: &Sums,
    a: (FnSym, FnSym, &Thm),
    b: (FnSym, FnSym, &Thm),
) -> Option<Thm> {
    let (bs, chi, chi_ax) = a;
    let (bs2, chi2, chi2_ax) = b;
    let np = (bs.arity() as usize).checked_sub(1)?;
    let nq = (bs2.arity() as usize).checked_sub(1)?;
    if chi.arity() as usize != np + 1 || chi2.arity() as usize != nq + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..nq).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();

    let at = |f: FnSym, prefix: &[Term], arg: &Term| {
        let mut v = prefix.to_vec();
        v.push(arg.clone());
        Term::apply(f, v)
    };

    let (x, av, av2, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ta, ta2, tz) = (Term::var(x), Term::var(av), Term::var(av2), Term::var(z));
    let (bx, b2x) = (at(bs, &pts, &tx), at(bs2, &qts, &tx));
    let (c, c2) = (at(chi, &pts, &ta), at(chi2, &qts, &ta2));
    let (point, one) = (sums.point(), sums.unit());

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), b2x.clone())));
    let phi = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::mem(point.clone(), bx.clone())));
    let phi2 =
        Formula::forall(x, Formula::imp(mem_xa2.clone(), Formula::mem(point.clone(), b2x.clone())));

    // The two characteristic theorems at these parameters, checked to *establish*
    // what this derivation is about to assume they say — conclusion pinned and
    // hypothesis set required empty. The second half is not redundant: `Hyp`
    // tracks only the assumptions made below with `Hyp::assume`, and `Hyp::lift`
    // records `hyps: []` for whatever theorem it is handed, so a kernel `Γ` on
    // `chi_ax` would be invisible all the way through `into_thm`.
    let guard = |t: &Thm, c: &Term, p: &Formula| -> Option<Thm> {
        let want = Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), c.clone()),
                Formula::and(Formula::mem(tz.clone(), one.clone()), p.clone()),
            ),
        );
        crate::establishes(t, &want).then(|| t.clone())
    };
    let xa = {
        let mut args = pts.clone();
        args.push(ta.clone());
        guard(&inst_all(chi_ax, &args)?, &c, &phi)?
    };
    let xb = {
        let mut args = qts.clone();
        args.push(ta2.clone());
        guard(&inst_all(chi2_ax, &args)?, &c2, &phi2)?
    };

    let g_dom = Hyp::assume(eq_dom.clone());
    let g_pw = Hyp::assume(pointwise.clone());
    let (w1, w2) = (env.fresh_var(), env.fresh_var());
    let mem_x_w = |w: FreeVar| Formula::mem(tx.clone(), Term::var(w));
    let point_in_w = |w: FreeVar| Formula::mem(point.clone(), Term::var(w));

    // ── φ → φ' ───────────────────────────────────────────────────────────────
    // Under `x ∈ A'`: the domain equation carries `x` back to `A`, where both
    // the assumed `φ` and the pointwise premise apply.
    let fwd = {
        let g_phi = Hyp::assume(phi.clone());
        let g_xa2 = Hyp::assume(mem_xa2.clone());
        let g_xa = g_dom.symm(env)?.subst(w1, &mem_x_w(w1), &g_xa2)?;
        let g_in_b = g_phi.inst(tx.clone())?.mp(&g_xa)?;
        let g_eq_b = g_pw.inst(tx.clone())?.mp(&g_xa)?;
        let g_in_b2 = g_eq_b.subst(w2, &point_in_w(w2), &g_in_b)?;
        g_in_b2.discharge(&mem_xa2)?.gen(x)?.discharge(&phi)?
    };
    // ── φ' → φ ───────────────────────────────────────────────────────────────
    let bwd = {
        let g_phi2 = Hyp::assume(phi2.clone());
        let g_xa = Hyp::assume(mem_xa.clone());
        let g_xa2 = g_dom.subst(w1, &mem_x_w(w1), &g_xa)?;
        let g_in_b2 = g_phi2.inst(tx.clone())?.mp(&g_xa2)?;
        let g_eq_b = g_pw.inst(tx.clone())?.mp(&g_xa)?;
        let g_in_b = g_eq_b.symm(env)?.subst(w2, &point_in_w(w2), &g_in_b2)?;
        g_in_b.discharge(&mem_xa)?.gen(x)?.discharge(&phi2)?
    };
    let g_iff = fwd.iff_intro(&bwd)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let (za, zb) = (Hyp::lift(&xa).inst(tz.clone())?, Hyp::lift(&xb).inst(tz.clone())?);
    let (mem_zc, mem_zc2) = (Formula::mem(tz.clone(), c.clone()), Formula::mem(tz.clone(), c2.clone()));
    let step = |from: &Hyp, to: &Hyp, assumed: &Formula, iff: &Hyp| -> Option<Hyp> {
        let g = Hyp::assume(assumed.clone());
        let both = from.iff_mp()?.mp(&g)?;
        let carried = iff.mp(&both.and_right()?)?;
        to.iff_mpr()?.mp(&both.and_left()?.and_intro(&carried)?)?.discharge(assumed)
    };
    let z_fwd = step(&za, &zb, &mem_zc, &g_iff.iff_mp()?)?;
    let z_bwd = step(&zb, &za, &mem_zc2, &g_iff.iff_mpr()?)?;
    let g_eq = z_fwd
        .iff_intro(&z_bwd)?
        .gen(z)?
        .rule(&inst_all(&ext, &[c.clone(), c2.clone()])?)?;

    let out = g_eq.discharge(&pointwise)?.discharge(&eq_dom)?.into_thm()?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(c, c2))) {
        return None
    }
    let mut binders = ps;
    binders.extend(qs);
    binders.push(av);
    binders.push(av2);
    Some(gen_all(&binders, &out))
}
