//! The terms, and the step function as one Replacement over the packed argument.
//!
//! # Interface
//!
//! [`StepSyms::new`] introduces the step symbol; [`payload`], [`domain`] and
//! [`value_packed`] are the builders a caller needs to state anything about it.
//! The rest are the term constructors the sibling files share, so that every
//! file spells the same key the same way.
//!
//! # Why one Replacement over a *packed* argument
//!
//! `List`'s `cons` branch carries three things — the head, the function into the
//! W-type, and the function into the motive — and Replacement needs a single
//! **set** to range over. They are packed into one, and the set ranged over is
//! [`pow_prod`]: `𝒫(prod(1,x))` is a superset of `fs(1,x)`
//! ([`crate::funspace::space::funspace_subset_pow_prod`]) which also contains
//! `∅`, and — the point — it is built from `1` and `x` alone, so no
//! function-space membership has to be discharged before the step even exists.
//!
//! `unpack` and `unpack_row` are the inverses: they recover the head and the
//! two functions from a packed row, which is what lets [`super::computes`] state
//! the step's value in the terms the caller supplied.
//!
//! `List α`'s index set is `1 + α`, so unlike [`crate::wnat_rec`] the `cons`
//! branch is indexed by an arbitrary `α` rather than by a point, and every key
//! carries that head along. `row_at` is what keeps the two spellings — the one
//! inside the Replacement and the one a caller writes — literally equal.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::proj::Proj;
use crate::sums::Sums;
use crate::wlist::WList;
use crate::wtype::Wtype;
use crate::{a1i, inst_all, singleton};

use super::shared::congr_ctx;

/// `𝒫(prod(1, x))` — a superset of `fs(1,x)` which also contains `∅`.
///
/// The step's Replacement has to range over a **set**, and the two candidates
/// are `fs(1,lt(α))` and `fs(1,T)`. Taking the power set of the product instead
/// costs nothing ([`crate::funspace::funspace_subset_pow_prod`] puts every
/// function space inside it) and buys one thing that matters: it is a set built
/// from `1` and `x` alone, so no function-space membership has to be discharged
/// before the step even exists.
pub fn pow_prod(s: &Sums, x: &Term) -> Term {
    Term::apply(s.pow, vec![s.prod.of(s.unit(), x.clone())])
}

/// `⟨inl •, ⟨∅,∅⟩⟩` — the whole argument the step gets at `List.nil`.
///
/// Both `f` and `r` are forced to `∅` there, the fibre `fam(α)(inl •)` being `0`.
pub fn key_nil(wt: &Wtype) -> Term {
    let s = &wt.sums;
    let z = wt.empty();
    s.ap.sets.pair(s.inl(s.point()), s.ap.sets.pair(z.clone(), z))
}

/// `⟨inr h, ⟨f,r⟩⟩` — the step's argument at `List.cons`.
pub fn key_cons(wt: &Wtype, h: &Term, f: &Term, r: &Term) -> Term {
    let s = &wt.sums;
    s.ap.sets.pair(s.inr(h.clone()), s.ap.sets.pair(f.clone(), r.clone()))
}

/// `app(app(app(s,h), app(f,•)), app(r,•))` — the value the step takes at
/// `List.cons`.
///
/// Curried, because Lean's minor premise is
/// `s : ∀ h, ∀ t, motive t → motive (cons h t)` and the checker reads `s h t ih`
/// as `app(app(app(⟦s⟧,⟦h⟧),⟦t⟧),⟦ih⟧)`, one application per argument.
pub fn value_cons(ap: &Apply, su: &Term, h: &Term, f: &Term, r: &Term) -> Term {
    let point = Term::apply(ap.empty, vec![]);
    ap.apply(
        ap.apply(
            ap.apply(su.clone(), h.clone()),
            ap.apply(f.clone(), point.clone()),
        ),
        ap.apply(r.clone(), point),
    )
}

/// `prod(FW(α), FT(T))` — the cons branch's fibre payload: a subterm family and
/// a family of recursive values, packed as one Kuratowski pair.
pub fn payload(s: &Sums, wl: &WList, alpha: &Term, t: &Term) -> Term {
    s.prod.of(pow_prod(s, &wl.ty_of(alpha.clone())), pow_prod(s, t))
}

/// `prod(α, P(α,T))` — the payload together with the head the tag carries.
pub fn domain(s: &Sums, wl: &WList, alpha: &Term, t: &Term) -> Term {
    s.prod.of(alpha.clone(), payload(s, wl, alpha, t))
}

/// `app(app(app(s,h), app(π₁ p,•)), app(π₂ p,•))` — the cons branch's value, **as
/// a function of the head and the packed payload**.
///
/// Against [`crate::wnat_rec::value_packed`] this is one more application and
/// nothing else. That is the whole of what a constructor's extra field costs in
/// this encoding, and it is the claim [`crate::proj`] exists to make good.
pub fn value_packed(ap: &Apply, pj: &Proj, su: &Term, h: &Term, p: &Term) -> Term {
    let point = Term::apply(ap.empty, vec![]);
    ap.apply(
        ap.apply(
            ap.apply(su.clone(), h.clone()),
            ap.apply(pj.fst_of(ap, p.clone()), point.clone()),
        ),
        ap.apply(pj.snd_of(ap, p.clone()), point),
    )
}

/// `⟨inr h, p⟩` — the step's argument at a cons, with the payload packed.
pub(super) fn key_packed(wt: &Wtype, h: &Term, p: &Term) -> Term {
    let s = &wt.sums;
    s.ap.sets.pair(s.inr(h.clone()), p.clone())
}

/// `⟨⟨inr h, p⟩, val(s,h,p)⟩` — one point of the step's graph.
fn row_packed(wt: &Wtype, pj: &Proj, su: &Term, h: &Term, p: &Term) -> Term {
    let s = &wt.sums;
    s.ap.sets.pair(key_packed(wt, h, p), value_packed(&s.ap, pj, su, h, p))
}

/// The same row, as a function of the **single** Replacement variable
/// `q ∈ prod(α, P(α,T))`: `row(s, π₁ q, π₂ q)`.
///
/// This is the one place `List` needs a projection that `N` did not, and it is
/// deliberately confined here: nothing below reads `q` again, so no lemma has to
/// know that `q` is a pair.
pub(super) fn row_at(wt: &Wtype, pj: &Proj, su: &Term, q: &Term) -> Term {
    let ap = &wt.sums.ap;
    row_packed(wt, pj, su, &pj.fst_of(ap, q.clone()), &pj.snd_of(ap, q.clone()))
}

/// `⊢ val(s, h, ⟨f,r⟩) = app(app(app(s,h), app(f,•)), app(r,•))` — **the
/// projections compute**, so the packed value is the unpacked one.
///
/// Unconditional. Everything above this line is stated at a packed payload and
/// so does not mention the constructor's fibre arity; everything below it is
/// stated at the components Lean's minor premise actually takes.
pub(super) fn unpack(
    env: &mut Env,
    ap: &Apply,
    pj: &Proj,
    su: &Term,
    h: &Term,
    f: &Term,
    r: &Term,
) -> Option<Thm> {
    let point = Term::apply(ap.empty, vec![]);
    let p = ap.sets.pair(f.clone(), r.clone());
    let f_eq = inst_all(&pj.fst, &[f.clone(), r.clone()])?;
    let s_eq = inst_all(&pj.snd, &[f.clone(), r.clone()])?;
    let e1 = congr_ctx(env, &f_eq, |q| {
        ap.apply(
            ap.apply(
                ap.apply(su.clone(), h.clone()),
                ap.apply(q, point.clone()),
            ),
            ap.apply(pj.snd_of(ap, p.clone()), point.clone()),
        )
    })?;
    let e2 = congr_ctx(env, &s_eq, |q| {
        ap.apply(
            ap.apply(
                ap.apply(su.clone(), h.clone()),
                ap.apply(f.clone(), point.clone()),
            ),
            ap.apply(q, point.clone()),
        )
    })?;
    let out = crate::eq_trans(env, &e1, &e2)?;
    if *out.concl() != Formula::eq(value_packed(ap, pj, su, h, &p), value_cons(ap, su, h, f, r)) {
        return None
    }
    Some(out)
}

/// `⊢ row_at(s, ⟨h,p⟩) = row(s,h,p)` — the Replacement's own projection
/// computes, so a row at an explicit pair is the row at its components.
pub(super) fn unpack_row(
    env: &mut Env,
    wt: &Wtype,
    pj: &Proj,
    su: &Term,
    h: &Term,
    p: &Term,
) -> Option<Thm> {
    let ap = &wt.sums.ap;
    let q = ap.sets.pair(h.clone(), p.clone());
    let h_eq = inst_all(&pj.fst, &[h.clone(), p.clone()])?;
    let p_eq = inst_all(&pj.snd, &[h.clone(), p.clone()])?;
    let snd_q = pj.snd_of(ap, q.clone());
    let e1 = congr_ctx(env, &h_eq, |w| row_packed(wt, pj, su, &w, &snd_q))?;
    let e2 = congr_ctx(env, &p_eq, |w| row_packed(wt, pj, su, h, &w))?;
    let out = crate::eq_trans(env, &e1, &e2)?;
    if *out.concl() != Formula::eq(row_at(wt, pj, su, &q), row_packed(wt, pj, su, h, p)) {
        return None
    }
    Some(out)
}

/// The Replacement symbol the `cons` half of the step is, with its membership
/// condition.
///
/// Built once and shared: it is a `define_by_membership`, so a second copy would
/// be a different step.
pub struct StepSyms {
    /// `E(α,s,T) = { row(s, π₁ q, π₂ q) : q ∈ prod(α, P(α,T)) }`.
    pub e: FnSym,
    /// `⊢ ∀α ∀s ∀T ∀x. (x ∈ E(α,s,T) ↔ ∃q. (q ∈ Q(α,T) ∧ x = row_at(s,q)))`.
    pub e_ax: Thm,
}

impl StepSyms {
    /// Introduce the symbol. `wl` fixes `FW(α) = 𝒫(prod(1,lt(α)))`.
    pub fn new(env: &mut Env, wt: &Wtype, wl: &WList, pj: &Proj) -> Option<StepSyms> {
        let s = &wt.sums;
        let (av, suv, tv, qv) =
            (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (ta, tsu, tt, tq) = (Term::var(av), Term::var(suv), Term::var(tv), Term::var(qv));
        let body = row_at(wt, pj, &tsu, &tq);
        let (xv, phi, exu) = crate::exists_unique_eq(env, &[], &body);
        let repl = Thm::ax_replacement(env, qv, xv, phi.clone())?;
        let dom = domain(s, wl, &ta, &tt);
        let repl_d = inst_all(&repl, std::slice::from_ref(&dom))?;
        let premise = Thm::gen(qv, &a1i(&exu, Formula::mem(tq.clone(), dom.clone())));
        let img = Thm::mp(&repl_d, &premise)?;
        let cond = Formula::exists(qv, Formula::and(Formula::mem(tq, dom), phi));
        let (e, e_ax) = crate::define_by_membership(env, &[av, suv, tv], &img, xv, &cond)?;
        Some(StepSyms { e, e_ax })
    }

    /// The term `E(α,s,T)`.
    pub(super) fn e_of(&self, alpha: &Term, su: &Term, t: &Term) -> Term {
        Term::apply(self.e, vec![alpha.clone(), su.clone(), t.clone()])
    }

    /// The packed step `e(α,z,s,T) = E(α,s,T) ∪ {⟨k₀,z⟩}`.
    pub fn step_of(&self, wt: &Wtype, alpha: &Term, z: &Term, su: &Term, t: &Term) -> Term {
        let s = &wt.sums;
        let pt = s.ap.sets.pair(key_nil(wt), z.clone());
        crate::funspace::bin_union(
            &s.ap.sets,
            self.e_of(alpha, su, t),
            singleton(s.ap.sets.up, pt),
        )
    }
}
