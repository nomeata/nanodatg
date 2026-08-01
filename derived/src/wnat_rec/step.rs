//! The terms, and the step function as one Replacement over the packed payload.
//!
//! # Interface
//!
//! [`StepSyms::new`] introduces the step symbol `e(z,s,T)`;
//! [`payload`] and [`value_packed`] are the two formula/term builders a caller
//! needs to state anything about it. The rest are the term constructors the
//! sibling files share, so that every file spells the same key the same way.
//!
//! # Why one Replacement over a *packed* payload
//!
//! The recursor's step takes `⟨a,⟨f,r⟩⟩` — a tag, a function into the W-type,
//! and a function into the motive. Replacement needs a **set** to range over, so
//! the two arguments are packed into one, and the set ranged over is
//! [`pow_prod`]: `𝒫(prod(1,x))` is a superset of `fs(1,x)`
//! ([`crate::funspace::space::funspace_subset_pow_prod`]) which also contains
//! `∅`, and — the point — it is built from `1` and `x` alone, so no
//! function-space membership has to be discharged before the step even exists.
//!
//! `unpack` is the inverse: it recovers `f` and `r` from a packed pair, and is
//! what lets [`super::computes`] state the step's value in terms the caller
//! supplied.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::sums::Sums;
use crate::wnat::Nat;
use crate::proj::Proj;
use crate::wtype::Wtype;
use crate::{a1i, inst_all, singleton};

use super::shared::congr_ctx;

/// `𝒫(prod(1, x))` — a superset of `fs(1,x)` which also contains `∅`.
///
/// The step's Replacement has to range over a **set**, and the two candidates
/// for the `succ` branch are `fs(1,N)` and `fs(1,T)`. Taking the power set of
/// the product instead costs nothing ([`crate::funspace::space::funspace_subset_pow_prod`]
/// puts every function space inside it) and buys one thing that matters: it is
/// a set built from `1` and `x` alone, so no function-space membership has to be
/// discharged before the step even exists.
pub fn pow_prod(s: &Sums, x: &Term) -> Term {
    Term::apply(s.pow, vec![s.prod.of(s.unit(), x.clone())])
}

/// `⟨inl •, ⟨∅,∅⟩⟩` — the whole argument the step gets at `N.zero`.
///
/// Both `f` and `r` are forced to `∅` there, the fibre `B(inl •)` being `0`.
pub fn key_zero(wt: &Wtype) -> Term {
    let s = &wt.sums;
    let z = wt.empty();
    s.ap.sets.pair(s.inl(s.point()), s.ap.sets.pair(z.clone(), z))
}

/// `⟨inr •, ⟨f,r⟩⟩` — the step's argument at `N.succ`.
pub fn key_succ(wt: &Wtype, f: &Term, r: &Term) -> Term {
    let s = &wt.sums;
    s.ap.sets.pair(s.inr(s.point()), s.ap.sets.pair(f.clone(), r.clone()))
}

/// `app(app(s, app(f,•)), app(r,•))` — the value the step takes at `N.succ`.
///
/// Curried, because Lean's minor premise is `s : ∀ n, C n → C (succ n)` and the
/// checker reads `s n ih` as `app(app(⟦s⟧,⟦n⟧),⟦ih⟧)`, one application per
/// argument.
pub fn value_succ(ap: &Apply, su: &Term, f: &Term, r: &Term) -> Term {
    let point = Term::apply(ap.empty, vec![]);
    ap.apply(
        ap.apply(su.clone(), ap.apply(f.clone(), point.clone())),
        ap.apply(r.clone(), point),
    )
}

/// `prod(FW, FT(T))` — the `succ` branch's payload: a subterm family and a
/// family of recursive values, packed as one Kuratowski pair.
pub fn payload(s: &Sums, nat: &Nat, t: &Term) -> Term {
    s.prod.of(pow_prod(s, &nat.ty), pow_prod(s, t))
}

/// `app(app(s, app(π₁ p, •)), app(π₂ p, •))` — the `succ` branch's value, **as a
/// function of the packed payload**.
///
/// This term is what the projections exist for, and it is the whole difference
/// between this construction and the one the brief proposed. See the header.
pub fn value_packed(ap: &Apply, pj: &Proj, su: &Term, p: &Term) -> Term {
    let point = Term::apply(ap.empty, vec![]);
    ap.apply(
        ap.apply(su.clone(), ap.apply(pj.fst_of(ap, p.clone()), point.clone())),
        ap.apply(pj.snd_of(ap, p.clone()), point),
    )
}

/// `⟨⟨inr •, p⟩, val(s,p)⟩` — one point of the step's graph.
pub(super) fn row_packed(wt: &Wtype, pj: &Proj, su: &Term, p: &Term) -> Term {
    let s = &wt.sums;
    s.ap.sets.pair(
        s.ap.sets.pair(s.inr(s.point()), p.clone()),
        value_packed(&s.ap, pj, su, p),
    )
}

/// `⊢ val(s, ⟨f,r⟩) = app(app(s, app(f,•)), app(r,•))` — **the projections
/// compute**, so the packed value is the unpacked one.
///
/// Unconditional, and the only place [`Proj::fst`] and [`Proj::snd`] are used.
/// Everything above this line is stated at a packed payload and so does not
/// mention the constructor's arity; everything below it is stated at the
/// components Lean's minor premise actually takes.
pub(super) fn unpack(env: &mut Env, ap: &Apply, pj: &Proj, su: &Term, f: &Term, r: &Term) -> Option<Thm> {
    let point = Term::apply(ap.empty, vec![]);
    let p = ap.sets.pair(f.clone(), r.clone());
    let f_eq = inst_all(&pj.fst, &[f.clone(), r.clone()])?;
    let s_eq = inst_all(&pj.snd, &[f.clone(), r.clone()])?;
    let e1 = congr_ctx(env, &f_eq, |q| {
        ap.apply(
            ap.apply(su.clone(), ap.apply(q, point.clone())),
            ap.apply(pj.snd_of(ap, p.clone()), point.clone()),
        )
    })?;
    let e2 = congr_ctx(env, &s_eq, |q| {
        ap.apply(
            ap.apply(su.clone(), ap.apply(f.clone(), point.clone())),
            ap.apply(q, point.clone()),
        )
    })?;
    let out = crate::eq_trans(env, &e1, &e2)?;
    if *out.concl() != Formula::eq(value_packed(ap, pj, su, &p), value_succ(ap, su, f, r)) {
        return None
    }
    Some(out)
}

/// The Replacement symbol the `succ` half of the step is, with its membership
/// condition.
///
/// Built once and shared: it is a `define_by_membership`, so a second copy
/// would be a different step.
pub struct StepSyms {
    /// `E(s,T) = { ⟨⟨inr •,p⟩, val(s,p)⟩ : p ∈ prod(FW, FT(T)) }`.
    pub e: FnSym,
    /// `⊢ ∀s ∀T ∀x. (x ∈ E(s,T) ↔ ∃p. (p ∈ prod(FW,FT(T)) ∧ x = ⟨⟨inr •,p⟩, val(s,p)⟩))`.
    pub e_ax: Thm,
}

impl StepSyms {
    /// Introduce the symbol. `nat` fixes `FW = 𝒫(prod(1,N))`.
    pub fn new(env: &mut Env, wt: &Wtype, nat: &Nat, pj: &Proj) -> Option<StepSyms> {
        let s = &wt.sums;
        let (suv, tv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tsu, tt, tp) = (Term::var(suv), Term::var(tv), Term::var(pv));
        let body = row_packed(wt, pj, &tsu, &tp);
        let (xv, phi, exu) = crate::exists_unique_eq(env, &[], &body);
        let repl = Thm::ax_replacement(env, pv, xv, phi.clone())?;
        let dom = payload(s, nat, &tt);
        let repl_d = inst_all(&repl, std::slice::from_ref(&dom))?;
        let premise = Thm::gen(pv, &a1i(&exu, Formula::mem(tp.clone(), dom.clone())));
        let img = Thm::mp(&repl_d, &premise)?;
        let cond = Formula::exists(pv, Formula::and(Formula::mem(tp, dom), phi));
        let (e, e_ax) = crate::define_by_membership(env, &[suv, tv], &img, xv, &cond)?;
        Some(StepSyms { e, e_ax })
    }

    /// The term `E(s,T)`.
    pub(super) fn e_of(&self, su: &Term, t: &Term) -> Term {
        Term::apply(self.e, vec![su.clone(), t.clone()])
    }

    /// The packed step `e(z,s,T) = E(s,T) ∪ {⟨k₀,z⟩}`.
    pub fn step_of(&self, wt: &Wtype, z: &Term, su: &Term, t: &Term) -> Term {
        let s = &wt.sums;
        let pt = s.ap.sets.pair(key_zero(wt), z.clone());
        crate::funspace::bin_union(
            &s.ap.sets,
            self.e_of(su, t),
            singleton(s.ap.sets.up, pt),
        )
    }
}
