//! **The packed step of the general recursor** — the terms, and one
//! Replacement per constructor, unioned.
//!
//! # What the step is
//!
//! [`crate::wrec_total`] runs on a single set `e` that packs every minor
//! premise: at a key `⟨a, ⟨f, r⟩⟩` — a tag, the family of recursive subterms
//! and the family of recursive *values* — it must return what Lean's matching
//! minor premise returns. For the `i`-th constructor of a declaration, with
//! `k` non-recursive and `m` recursive fields and the declared order `order`:
//!
//! ```text
//! FWᵢ := 𝒫(prod(finord(mᵢ), W))       FTᵢ := 𝒫(prod(finord(mᵢ), T))
//! Pᵢ  := prod(FWᵢ, FTᵢ)               Qᵢ  := prod(Aᵢ, Pᵢ)
//!
//! valᵢ(σ, f, r) := sᵢ applied, left to right,
//!                    per Slot::Plain j:  compⱼ(σ)
//!                    per Slot::Rec j:    app(f, Injⱼ(•))
//!                  and then, for j = 0 … mᵢ−1:  app(r, Injⱼ(•))
//!
//! rowᵢ(σ, p) := ⟨⟨Injᵢ(σ), p⟩, valᵢ(σ, π₁p, π₂p)⟩
//! Eᵢ         := { rowᵢ(π₁q, π₂q) : q ∈ Qᵢ }          one Replacement
//! e(p⃗,s⃗,T)   := E₀ ∪ (E₁ ∪ (… ∪ ∅))                  right-nested, n branches
//! ```
//!
//! Three design decisions, each with its reason, all from `RECURSOR-DESIGN.md`
//! §3.2:
//!
//! * **No nullary special case.** The hand-written steps union a Replacement
//!   with a hand-made one-point graph for the nullary constructor; here a
//!   nullary constructor is just a branch whose `Qᵢ` degenerates, and the
//!   construction never asks.
//! * **`pow_prod` supersets**, as in [`crate::wlist_rec`]: `Qᵢ` must be a set
//!   before anything is proved, and `𝒫(prod(finord(mᵢ), X))` contains both
//!   `fs(finord(mᵢ), X)` and `∅` with no typing side condition.
//! * **Projections, not existentials** — `rowᵢ` is `wlist_rec::row_at` with
//!   the bare head replaced by the telescope element `σ`: one projection at
//!   the Replacement, values stated at `(σ, p)` so the η rule is never needed.
//!   Everything from the case analysis to [`unpack`] stays payload-opaque;
//!   the `k`-fold component reads happen only in `valᵢ` and in
//!   [`super::computes`].
//!
//! Note the fibre is `finord(mᵢ)` and the applications are at `Injⱼ(•)`,
//! **never** at `•` — `finord(1) ≠ 1` is the recorded trap, and
//! [`crate::recarg`] already routes around it; the step must match.
//!
//! # Interface
//!
//! [`Rx`] is the term-forming context every sibling file works in;
//! [`StepSym::new`] mints the `i`-th Replacement symbol; [`applied_minor`] is
//! the one spelling of "the minor premise applied to its arguments", shared by
//! the step value, the hypothesis bundle ([`super::premise`]) and the ι rules
//! so the three cannot drift apart. [`unpack`] and [`unpack_row`] compute the
//! projections at literal pairs, unconditionally.

use std::rc::Rc;

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::bin_union;
use crate::proj::Proj;
use crate::sigma::Telescope;
use crate::sums::Sums;
use crate::{a1i, eq_trans, inst_all};

use super::machine::Machine;
use super::carrier::Inductive;
use super::rec_shared::congr_ctx;
use super::spec::Slot;

/// `𝒫(prod(d, x))` — a superset of `fs(d, x)` that also holds `∅`, built from
/// `d` and `x` alone so no function-space membership has to be discharged
/// before the step even exists.
pub fn pow_prod(s: &Sums, d: &Term, x: &Term) -> Term {
    Term::apply(s.pow, vec![s.prod.of(d.clone(), x.clone())])
}

/// The minor premise applied to its arguments, **in declared order**: per
/// [`Slot::Plain`] the next of `fields`, per [`Slot::Rec`] the next of `subs`,
/// and then every element of `ihs`.
///
/// This is the single spelling of the minor-premise application convention
/// (fields in declared order, then one ih per recursive field in field
/// order). The step value, [`super::premise`]'s hypothesis bundle and the ι
/// rules all call it, which is what pins them to *one* convention — §7.2's
/// order-mask failure mode is a drift between two spellings, and there is
/// only one.
pub fn applied_minor(
    ap: &Apply,
    order: &[Slot],
    su: &Term,
    fields: &[Term],
    subs: &[Term],
    ihs: &[Term],
) -> Term {
    let (mut pi, mut ri) = (0, 0);
    let mut acc = su.clone();
    for sl in order {
        match sl {
            Slot::Plain => {
                acc = ap.apply(acc, fields[pi].clone());
                pi += 1;
            }
            Slot::Rec => {
                acc = ap.apply(acc, subs[ri].clone());
                ri += 1;
            }
        }
    }
    for v in ihs {
        acc = ap.apply(acc, v.clone());
    }
    acc
}

/// **Which value the step's rows carry** — the one thing two recursions over
/// the same skeleton differ in.
///
/// The value recursor's rows carry the minor premise applied to the
/// constructor's fields ([`Vals::Minor`]); the `good` recursion of
/// [`super::family`] runs the *same* Replacement/union/single-valuedness
/// apparatus over the same tag sum with a Separation subset of the index space
/// in the value slot ([`Vals::Good`]). Everything between the two — the
/// Replacement symbols ([`StepSym`]), what is in the step and what is not
/// ([`super::members`]), single-valuedness ([`super::values`]), the
/// per-constructor computation rules ([`super::computes`]) and the whole prefix
/// of the ι argument ([`super::iota::iota_core`]) — is *value-agnostic* and is
/// shared verbatim. Only [`super::typed`] and the tail of [`super::iota`] look
/// inside the value, and each recursion writes its own.
///
/// Adding a third recursion means adding a variant here and writing its
/// `step_typed`; it does not mean a second copy of the step.
pub(crate) enum Vals {
    /// `valᵢ(σ,f,r) = sᵢ ⟪fields in declared order⟫ ihs` — the value recursor
    /// ([`super::recursor::GenRecursor`]).
    Minor,
    /// `valᵢ(σ,f,r) = Gᵢ(p⃗, σ, r)` — the `good` recursion. `f`, the row of
    /// recursive *subterms*, is dead in the value: `good` reads only the row of
    /// recursive *good-sets*. The vector is one symbol per constructor, each of
    /// arity `np + 2`.
    Good(Vec<FnSym>),
}

/// The term-forming context of the general recursor: the machine, the
/// translated declaration, and the working variables — the declaration's own
/// parameters, one minor-premise variable per constructor, and one target.
///
/// Every sibling file builds its terms through this struct, so every file
/// spells the same key the same way.
pub(crate) struct Rx<'a> {
    pub(crate) mach: &'a Machine,
    pub(crate) ind: &'a Inductive,
    /// The parameter terms — [`Inductive::params`] as variables.
    pub(crate) ps: Vec<Term>,
    /// The minor-premise terms `s₀ … s_{n-1}`. **Empty** under
    /// [`Vals::Good`], which has no minor premises.
    pub(crate) minors: Vec<Term>,
    /// The target term `T`. A variable for the value recursor, which is
    /// generic in it; the concrete `𝒫(Idx(p⃗))` for the `good` recursion,
    /// which is not.
    pub(crate) t: Term,
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))` — the union chain's walk.
    pub(crate) bin: Thm,
    /// Which value the rows carry.
    pub(crate) vals: Vals,
}

impl<'a> Rx<'a> {
    pub(crate) fn s(&self) -> &Sums { &self.mach.wt.sums }
    pub(crate) fn ap(&self) -> &Apply { &self.mach.wt.sums.ap }
    pub(crate) fn pj(&self) -> &Proj { &self.mach.proj }

    /// The number of constructors.
    pub(crate) fn n(&self) -> usize { self.ind.spec.ctors.len() }
    /// The `i`-th constructor's recursive-argument count.
    pub(crate) fn m(&self, i: usize) -> usize { self.ind.spec.ctors[i].recs }
    /// The `i`-th constructor's non-recursive-argument count.
    pub(crate) fn k(&self, i: usize) -> usize { self.ind.spec.ctors[i].args.len() }
    /// The `i`-th constructor's declared field order.
    pub(crate) fn order(&self, i: usize) -> &[Slot] { &self.ind.spec.ctors[i].order }
    /// The `i`-th constructor's telescope.
    pub(crate) fn tel(&self, i: usize) -> &Rc<Telescope> { &self.ind.telescopes[i] }
    /// The `i`-th tag summand `Aᵢ` at the working parameters.
    pub(crate) fn summand(&self, i: usize) -> Term { self.ind.summands[i].clone() }
    /// The raw carrier `W(A, B, U({A,T}))`.
    pub(crate) fn w(&self) -> Term { self.ind.wty.clone() }

    /// The `i`-th constructor's recursive-argument **fibre**, `Sum_{mᵢ}(A⃗)`.
    ///
    /// Read off [`RecArg::domain`](crate::recarg::RecArg::domain) rather than
    /// recomputed, and that is what makes it general: the same field is
    /// `finord(mᵢ)` **literally** when every `γⱼ` of the constructor is empty,
    /// because `finord` is `Sum_m` at `m` copies of `1` and
    /// [`RecArg::new`](crate::recarg::RecArg::new) builds its domain with that
    /// same symbol. So a plain declaration's fibre term does not move, and the
    /// 56 places pinned on term identity at `γ = ∅` are pinned on one
    /// construction rather than on two spellings agreeing.
    ///
    /// It also cannot drift from the constructor's own dispatcher, which is
    /// what a second call to `ISumSyms::finord` here could: the fibre a step's
    /// payload is stated over and the domain the recursive-argument function
    /// lands in are now the *same term by construction*.
    pub(crate) fn fibre(&self, i: usize) -> Option<Term> {
        Some(self.ind.recargs.get(i)?.domain.clone())
    }
    /// `Injⱼ(•)`, the `j`-th element of a fibre.
    pub(crate) fn inj_pt(&self, j: usize) -> Option<Term> {
        self.mach.syms.inj(j, self.s().point())
    }
    /// `⊢ Injⱼ(•) ∈ finord(m)` — unconditional.
    pub(crate) fn inj_pt_mem(&self, m: usize, j: usize) -> Option<Thm> {
        let s = self.s();
        let mut args = vec![s.unit(); m];
        args.push(s.point());
        Thm::mp(
            &inst_all(self.mach.syms.inj_mem(m, j)?, &args)?,
            &s.unit_mem,
        )
    }

    /// `FWᵢ = 𝒫(prod(Sum_{mᵢ}(A⃗), W))`.
    pub(crate) fn fw(&self, i: usize) -> Option<Term> {
        Some(pow_prod(self.s(), &self.fibre(i)?, &self.w()))
    }
    /// `FTᵢ = 𝒫(prod(Sum_{mᵢ}(A⃗), T))`.
    pub(crate) fn ft(&self, i: usize) -> Option<Term> {
        Some(pow_prod(self.s(), &self.fibre(i)?, &self.t))
    }
    /// `Pᵢ = prod(FWᵢ, FTᵢ)`.
    pub(crate) fn payload(&self, i: usize) -> Option<Term> {
        Some(self.s().prod.of(self.fw(i)?, self.ft(i)?))
    }
    /// `Qᵢ = prod(Aᵢ, Pᵢ)` — the `i`-th Replacement's domain.
    pub(crate) fn domain(&self, i: usize) -> Option<Term> {
        Some(self.s().prod.of(self.summand(i), self.payload(i)?))
    }

    /// The telescope components `comp₀(σ) … comp_{k-1}(σ)`.
    pub(crate) fn comps(&self, i: usize, sigma: &Term) -> Vec<Term> {
        (0..self.k(i))
            .map(|j| Telescope::comp_of(self.ap(), self.pj(), j, sigma.clone()))
            .collect()
    }
    /// `app(f, Inj₀(•)) … app(f, Inj_{m-1}(•))`.
    pub(crate) fn fibre_apps(&self, i: usize, f: &Term) -> Option<Vec<Term>> {
        (0..self.m(i))
            .map(|j| Some(self.ap().apply(f.clone(), self.inj_pt(j)?)))
            .collect()
    }

    /// `valᵢ(σ, f, r)`, per [`Vals`].
    pub(crate) fn val(&self, i: usize, sigma: &Term, f: &Term, r: &Term) -> Option<Term> {
        match &self.vals {
            Vals::Minor => Some(applied_minor(
                self.ap(),
                self.order(i),
                self.minors.get(i)?,
                &self.comps(i, sigma),
                &self.fibre_apps(i, f)?,
                &self.fibre_apps(i, r)?,
            )),
            Vals::Good(g) => {
                let mut args = self.ps.clone();
                args.push(sigma.clone());
                args.push(r.clone());
                Some(Term::apply(*g.get(i)?, args))
            }
        }
    }
    /// `valᵢ(σ, π₁p, π₂p)` — the value at a packed payload.
    pub(crate) fn val_packed(&self, i: usize, sigma: &Term, p: &Term) -> Option<Term> {
        let ap = self.ap();
        self.val(i, sigma, &self.pj().fst_of(ap, p.clone()), &self.pj().snd_of(ap, p.clone()))
    }
    /// `⟨Injᵢ(σ), p⟩` — the step's key at the `i`-th constructor.
    pub(crate) fn key(&self, i: usize, sigma: &Term, p: &Term) -> Option<Term> {
        Some(self.ap().sets.pair(self.mach.syms.inj(i, sigma.clone())?, p.clone()))
    }
    /// `⟨⟨Injᵢ(σ), p⟩, valᵢ(σ, π₁p, π₂p)⟩` — one point of the step's graph.
    pub(crate) fn row(&self, i: usize, sigma: &Term, p: &Term) -> Option<Term> {
        Some(self.ap().sets.pair(self.key(i, sigma, p)?, self.val_packed(i, sigma, p)?))
    }
    /// The same row as a function of the single Replacement variable:
    /// `rowᵢ(π₁q, π₂q)`.
    pub(crate) fn row_at(&self, i: usize, q: &Term) -> Option<Term> {
        let ap = self.ap();
        self.row(i, &self.pj().fst_of(ap, q.clone()), &self.pj().snd_of(ap, q.clone()))
    }

    /// The arguments the `i`-th Replacement symbol is applied to: the
    /// declaration's parameters, then whatever the value slot's own variables
    /// are — `(sᵢ, T)` for the value recursor, nothing for `good`, whose
    /// target is the fixed `𝒫(Idx(p⃗))` and which has no minors.
    ///
    /// One method rather than three inline spellings, because the abbreviation
    /// [`StepSym::new`] introduces is generalised over exactly this list and a
    /// mismatch would show up as a `None` several files away.
    pub(crate) fn e_args(&self, i: usize) -> Vec<Term> {
        let mut args = self.ps.clone();
        if let Vals::Minor = self.vals {
            args.push(self.minors[i].clone());
            args.push(self.t.clone());
        }
        args
    }
    /// `Eᵢ(p⃗, sᵢ, T)` at the working variables.
    pub(crate) fn e_of(&self, syms: &[StepSym], i: usize) -> Term {
        Term::apply(syms[i].e, self.e_args(i))
    }
    /// The union tail `Eⱼ ∪ (… ∪ ∅)` from branch `j` on; `j = 0` is the whole
    /// step, `j = n` is `∅`.
    pub(crate) fn chain(&self, syms: &[StepSym], j: usize) -> Term {
        (j..self.n()).rev().fold(self.s().zero(), |acc, i| {
            bin_union(&self.ap().sets, self.e_of(syms, i), acc)
        })
    }
    /// The packed step `e(p⃗, s⃗, T) = E₀ ∪ (E₁ ∪ (… ∪ ∅))`.
    pub(crate) fn step(&self, syms: &[StepSym]) -> Term { self.chain(syms, 0) }
}

/// `⊢ valᵢ(σ, π₁⟨f,r⟩, π₂⟨f,r⟩) = valᵢ(σ, f, r)` — **the projections
/// compute**, so the packed value is the unpacked one. Unconditional.
pub(crate) fn unpack(
    env: &mut Env,
    cx: &Rx<'_>,
    i: usize,
    sigma: &Term,
    f: &Term,
    r: &Term,
) -> Option<Thm> {
    let ap = cx.ap();
    let p = ap.sets.pair(f.clone(), r.clone());
    let f_eq = inst_all(&cx.pj().fst, &[f.clone(), r.clone()])?;
    let r_eq = inst_all(&cx.pj().snd, &[f.clone(), r.clone()])?;
    let snd_p = cx.pj().snd_of(ap, p.clone());
    let e1 = congr_ctx(env, &f_eq, |q| {
        cx.val(i, sigma, &q, &snd_p).expect("arity ensured")
    })?;
    let e2 = congr_ctx(env, &r_eq, |q| cx.val(i, sigma, f, &q).expect("arity ensured"))?;
    let out = eq_trans(env, &e1, &e2)?;
    if *out.concl() != Formula::eq(cx.val_packed(i, sigma, &p)?, cx.val(i, sigma, f, r)?) {
        return None
    }
    Some(out)
}

/// `⊢ rowᵢ(π₁⟨σ,p⟩, π₂⟨σ,p⟩) = rowᵢ(σ, p)` — the Replacement's own projection
/// computes, so a row at an explicit pair is the row at its components.
/// Unconditional.
pub(crate) fn unpack_row(
    env: &mut Env,
    cx: &Rx<'_>,
    i: usize,
    sigma: &Term,
    p: &Term,
) -> Option<Thm> {
    let ap = cx.ap();
    let q = ap.sets.pair(sigma.clone(), p.clone());
    let s_eq = inst_all(&cx.pj().fst, &[sigma.clone(), p.clone()])?;
    let p_eq = inst_all(&cx.pj().snd, &[sigma.clone(), p.clone()])?;
    let snd_q = cx.pj().snd_of(ap, q.clone());
    let e1 = congr_ctx(env, &s_eq, |w| cx.row(i, &w, &snd_q).expect("arity ensured"))?;
    let e2 = congr_ctx(env, &p_eq, |w| cx.row(i, sigma, &w).expect("arity ensured"))?;
    let out = eq_trans(env, &e1, &e2)?;
    if *out.concl() != Formula::eq(cx.row_at(i, &q)?, cx.row(i, sigma, p)?) {
        return None
    }
    Some(out)
}

/// One constructor's Replacement symbol, with its membership condition.
///
/// Built once per constructor per declaration and cached on the
/// [`super::recursor::GenRecursor`]: it is a [`crate::define_by_membership`],
/// so a second copy would be a different step and nothing would compose.
pub struct StepSym {
    /// `Eᵢ(p⃗, s, T) = { rowᵢ(π₁q, π₂q) : q ∈ Qᵢ(p⃗, T) }`, arity `np + 2`.
    pub e: FnSym,
    /// `⊢ ∀p⃗ ∀s ∀T ∀x. (x ∈ Eᵢ(p⃗,s,T) ↔ ∃q. (q ∈ Qᵢ ∧ x = rowᵢ(π₁q, π₂q)))`.
    pub e_ax: Thm,
}

impl StepSym {
    /// Introduce the `i`-th constructor's Replacement symbol. `extra` is the
    /// value slot's own variables — `[sᵢ, T]` for the value recursor, empty
    /// for `good` — appended to the declaration's parameters; it must match
    /// [`Rx::e_args`], and the shape check in [`super::members`] catches it if
    /// it does not.
    pub(crate) fn new(
        env: &mut Env,
        cx: &Rx<'_>,
        i: usize,
        extra: &[kernel::FreeVar],
    ) -> Option<StepSym> {
        let qv = env.fresh_var();
        let tq = Term::var(qv);
        let body = cx.row_at(i, &tq)?;
        let (xv, phi, exu) = crate::exists_unique_eq(env, &[], &body);
        let repl = Thm::ax_replacement(env, qv, xv, phi.clone())?;
        let dom = cx.domain(i)?;
        let repl_d = inst_all(&repl, std::slice::from_ref(&dom))?;
        let premise = Thm::gen(qv, &a1i(&exu, Formula::mem(tq.clone(), dom.clone())));
        let img = Thm::mp(&repl_d, &premise)?;
        let cond = Formula::exists(qv, Formula::and(Formula::mem(tq, dom), phi));
        let mut params = cx.ind.params.clone();
        params.extend(extra.iter().copied());
        let (e, e_ax) = crate::define_by_membership(env, &params, &img, xv, &cond)?;
        Some(StepSym { e, e_ax })
    }
}
