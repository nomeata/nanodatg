//! **The indexed class-(T) eliminator at a `Prop` motive** — one theorem per
//! declaration, generated at declaration time. `INDEXED-DESIGN.md` §5.3 and §8's
//! D7.
//!
//! # What this is for, and what it is not
//!
//! Two different things live at motive level `u₁ = 0`, and only this one blocks.
//! Prop-motive ι *at a use site* is unchanged — the certifier's `proof_eq`
//! short-circuit takes it. Prop-motive **typing of the recursor constant** is
//! not covered by §5.1 at all: at `RBTree.rec.{0,0}` the motive is `Sort 0`, the
//! whole recursor type is a `Prop`, and `⟦RBTree.rec.{0,0}⟧ = •`. There is no
//! `grec`, no target set and no `T`-policy — §5.1's `app(grec(p⃗,s⃗),t)` is the
//! *value* recursor. What is owed is that the motive holds at every inhabitant
//! of the carrier, which is structural induction with the index carried.
//!
//! # Interface
//!
//! Writing `ind(p⃗,x⃗)` for [`IndexedCarrier`]'s carrier, `m` for a fresh motive
//! variable, `•` for the point, and `app(m, x⃗, t)` for the **curried**
//! application [`motive_app`] — the motive takes its `ni` indices and then the
//! major premise, which is the spine Lean's `motive c n t` produces:
//!
//! ```text
//! MINORᵢ(m) := ∀f⃗. ( Aᵢ → • ∈ app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗)) )   [minors]
//!
//! Aᵢ  :=  the kᵢ + mᵢ FIELD atoms, in DECLARED order:            [minor_atoms]
//!             yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)              at a Slot::Plain
//!             rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))       at a Slot::Rec
//!         then the mᵢ induction hypotheses
//!             • ∈ app(m, d⃗ᵢⱼ(p⃗,y⃗), rⱼ)
//!
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) →
//!       ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → • ∈ app(m, x⃗, t) ) )                   [rec]
//! ```
//!
//! [`IndexedPropRecursor::minor_atoms`] is `Aᵢ` atom by atom and
//! [`IndexedPropRecursor::minor_vars`] the binders it is stated at, position for
//! position with the constructor's declared fields, so a consumer discharging
//! the antecedent rebuilds exactly what the theorem carries rather than guessing
//! its association or its order.
//!
//! # The binder order is Lean's, not the carrier's — a deliberate departure
//!
//! `INDEXED-DESIGN.md` §8's D7 states the quantifier prefix as `∀y⃗∀r⃗`,
//! plains-then-recs "matching `rect_step`", with the consumer permuting by the
//! `Slot` mask. **This module quantifies in the constructor's declared field
//! order instead**, and states `Aᵢ`'s field atoms in that same order. The
//! permutation has not gone away; it has moved inside, where
//! [`IndexedPropRecursor::over_family`] does it once against the mask and no
//! consumer can get it wrong.
//!
//! Three reasons, in the order they mattered:
//!
//! 1. **It is the shape the consumer already holds.** A class-(T) declaration's
//!    minor premise is a `Prop`, so `• ∈ ⟦minorᵢ⟧` unfolds binder by binder into
//!    exactly `∀ (declared field). (its typing → …)` with the induction
//!    hypotheses innermost — Lean's own telescope, decoded at `RBTree.red` as
//!    `n, l, x, r, ih_l, ih_r`. Prenexing and flattening that is arithmetic on a
//!    list; re-sorting it by a mask is not, and a mis-sort is silent.
//! 2. **The declared order is dependency-correct.** `d⃗ᵢⱼ` may mention only the
//!    plain fields *preceding* the `j`-th `Slot::Rec`
//!    ([`IndexedDeclSpec::plains_before`]), so a recursive field's atom is
//!    well-formed exactly where the mask puts it. Plains-then-recs is also
//!    well-formed, but it is not the *only* well-formed order, so it buys
//!    nothing here.
//! 3. **It is what the sibling already does.**
//!    [`TruncRecursor::minor_atoms`](super::trunc_rec::TruncRecursor::minor_atoms)
//!    is Lean-positional, and so is
//!    [`IndexedCtor::mem_atoms_lean`](super::IndexedCtor::mem_atoms_lean). One
//!    order across the interface was the lesson of `mem_lean`; a second order
//!    exposed here would be the third spelling of one list.
//!
//! `rect_step`'s own prefix is untouched — it is `crate::inductive::rect`'s
//! statement, not this module's — and the derivation instantiates `MINORᵢ` at
//! the mask-permuted term list to meet it.
//!
//! # The derivation — composition, no new primitive
//!
//! ```text
//! φ(z) := ∀x⃗. ( tup(x⃗) ∈ app(goodrec(p⃗), z) → • ∈ app(m, x⃗, z) )
//! ```
//!
//! [`decl_rect`] at that `φ`, and each `rect_stepᵢ` discharged from `MINORᵢ`:
//!
//! * the skeleton hypotheses come from `rect_step`'s own `tⱼ ∈ W`, one Leibniz
//!   along [`Inductive::ty_ax`] each;
//! * `ctorᵢ(y⃗,t⃗) ∈ ind(p⃗,x⃗)` from [`Inductive::ctor_term`]'s typing plus
//!   [`IndexedCarrier::intro`] against `φ`'s own antecedent;
//! * [`IndexedCtor::inv`](super::IndexedCtor::inv) then yields
//!   `tup(x⃗) = tup(e⃗ᵢ)` and `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)`;
//! * Kuratowski injectivity ([`crate::funcs::Apply::pair_inj`]) reads
//!   `xₖ = eᵢₖ` off componentwise;
//! * [`IndexedCarrier::good_of`] turns `tⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` into the antecedent
//!   `φ(tⱼ)` wants, firing the induction hypothesis at the child's **own**
//!   indices;
//! * one [`kernel::Thm::eq_leibniz`] per index moves the conclusion from `e⃗ᵢ`
//!   to `x⃗`.
//!
//! The major premise is [`IndexedCarrier::subset_w`] and
//! [`IndexedCarrier::good_of`] again: `t ∈ ind(p⃗,x⃗)` feeds the induction's
//! `t ∈ W` and `φ(t)`'s antecedent at that very `x⃗`.
//!
//! # `φ` is not constant in `z`, so nothing collapses
//!
//! [`super::trunc_rec`]'s class-(P) `φ` is constant, which makes its recursive
//! minors provable by one projection. Here `φ` mentions `z` in
//! `app(goodrec(p⃗), z)` **and** in `app(m, x⃗, z)`, so every minor carries
//! content and the induction hypotheses are consumed rather than stated. That is
//! the whole difference between the two files, and it is why this one needs
//! inversion at all.
//!
//! # Symbols versus interpretations — the consumer's move, and why
//!
//! Everything above is stated at the index **symbols** `e⃗ᵢ`, `d⃗ᵢⱼ` and `ιₖ`,
//! per the convention `crate::inductive::spec` explains: the kernel has
//! `Formula::subst` and no `Term::subst`, so an index expression reaches
//! `derived/` as a `FnSym` and dependence is application. A checker's `x⃗` are
//! *interpretations* of Lean index expressions, and the two are related only by
//! those symbols' own defining axioms.
//!
//! **That move belongs to the consumer, and the consumer has already built
//! it.** It is the same gap [`IndexedCtor::mem_lean`](super::IndexedCtor::mem_lean)
//! met: inference hands back a fact at the interpretations, and a congruence
//! along the abbreviations' defining equations moves it to the symbols —
//! `mini`'s `ctor_ix::index_congr`, which produces
//! `⊢ ind(p⃗, x⃗_syms) = ind(p⃗, ⟦x⃗⟧)` in one step and degenerates to reflexivity
//! at a closed index, so `RBTree` pays nothing. It cannot be done here, because
//! the defining equations are minted at the boundary and this module never sees
//! them; a second congruence built out of caution would be a second spelling of
//! a solved problem. What this module owes instead is that the terms needing the
//! move are *enumerable* rather than buried: the index expressions are the
//! `e⃗ᵢ` in [`IndexedPropRecursor::minors`]' conclusions and the `d⃗ᵢⱼ` in the
//! recursive and induction-hypothesis atoms of
//! [`IndexedPropRecursor::minor_atoms`], and both are exported term by term.
//! (The `βⱼ` in the plain-field atoms are symbols by the same convention, but
//! they are not new here: every constructor rule in `derived/` states them that
//! way and the consumer already folds them.) The conclusion's `x⃗` need no move at all:
//! they are `∀`-bound, so the consumer instantiates them at its own
//! interpretations directly.
//!
//! # Scope
//!
//! Class (T), indexed, `ni ≥ 1`, non-mutual, no function-typed recursive
//! arguments — [`super::IndexedInductive`]'s scope exactly, since that is what
//! `good` and the carrier were built for. `n = 0` is declined: [`decl_rect`]
//! returns `None` there and the true statement at zero constructors is the
//! different one that the carrier is empty. The **value** recursor at a
//! `Sort u+1` motive is `INDEXED-DESIGN.md` §5.1/§5.2 and is not here.
//!
//! # Nothing here is an axiom
//!
//! One Separation per call, inside [`decl_rect`]'s [`crate::wtype::w_rect`].
//! Everything else is an instance of a theorem [`IndexedCarrier`],
//! [`super::good`] or [`crate::inductive::rect`] already proved.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::{ctor_atoms, Inductive};
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{
    carry_under, gen_under, hyp_conj, hyp_inst, rewrite_under, under,
};
use crate::inductive::rect::{decl_rect, rect_parts};
use crate::inductive::Slot;
use crate::recursion::hyp::hyp_eq_symm;
use crate::sums::Sums;
use crate::{
    a1i, all_unconditional, and_left, and_right, conj_of, conj_proj, eq_symm, establishes,
    gen_all, hyp_and, hyp_mp, imp_refl, inst_all, syl, uncurry,
};

use super::carrier::IndexedCarrier;
use super::spec::IndexedDeclSpec;
use super::IndexedInductive;

/// `app(m, x⃗, t)` — the motive applied **curried**, to its `ni` indices in
/// order and then to the major premise.
///
/// This is the spine Lean's `motive c n t` produces and the only spelling this
/// module uses; a consumer building the motive term builds it against this.
pub fn motive_app(s: &Sums, m: &Term, xs: &[Term], t: &Term) -> Term {
    let mut cur = m.clone();
    for x in xs {
        cur = s.ap.apply(cur, x.clone());
    }
    s.ap.apply(cur, t.clone())
}

/// **The congruence along [`motive_app`]'s spine**, at `ni` indices:
///
/// ```text
/// ⊢ ∀m ∀a⃗ ∀t ∀b⃗ ∀u. ( (a₀ = b₀ ∧ (… ∧ (a_{ni−1} = b_{ni−1} ∧ t = u))) →
///       app(m, a⃗, t) = app(m, b⃗, u) )
/// ```
///
/// `ni + 1` equations — **the subject is one of them**, and last. The quantifier
/// prefix is the motive, then the whole *left* spine (indices, then subject),
/// then the whole *right* spine, matching
/// [`pair_inj`](crate::funcs::Apply::pair_inj)'s left-then-right convention.
///
/// # Why this lives here rather than in the consumer
///
/// A checker's `x⃗` are interpretations of Lean index expressions and this
/// module's are `FnSym`s (see the header), so every use of
/// [`IndexedPropRecursor`] has to move between the two. At a `mem`-shaped
/// position that is one congruence over a **single symbol applied to
/// `p⃗ ++ x⃗`**, which `mini`'s `ctor_ix::index_congr` already does. Inside
/// `motive_app` it is not: the spine is a nest of *binary* `app` nodes, so the
/// move has to be folded down it one node at a time. That fold is a property of
/// the spine, and the spine is defined here — so a consumer writing its own
/// would be the second definition of one convention, which is how the
/// `mem_atoms` order, the `LePropFields` ladder and the `motive_app` argument
/// order each went wrong once already.
///
/// It covers the **subject** position too, and that is not decoration: a
/// minor's conclusion is `• ∈ app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))`, where the constructor
/// term is at this crate's spelling and the consumer holds its own. A subject
/// *retarget* cannot reach it, because here the constructor sits inside an
/// argument of the membership, not at its subject. Pass
/// [`kernel::Thm::eq_refl`] where a position does not move.
///
/// One theorem per arity, minted fresh; cache it per `ni`. `None` only if an
/// internal shape check fails.
pub fn motive_congr(env: &mut Env, s: &Sums, ni: usize) -> Option<Thm> {
    let mv = env.fresh_var();
    let avs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let tv = env.fresh_var();
    let bvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let uv = env.fresh_var();

    let tm = Term::var(mv);
    let a: Vec<Term> = avs.iter().map(|v| Term::var(*v)).collect();
    let b: Vec<Term> = bvs.iter().map(|v| Term::var(*v)).collect();
    let (tt, tu) = (Term::var(tv), Term::var(uv));

    let mut atoms: Vec<Formula> =
        (0..ni).map(|k| Formula::eq(a[k].clone(), b[k].clone())).collect();
    atoms.push(Formula::eq(tt.clone(), tu.clone()));
    let h = conj_of(&atoms)?; // `ni + 1 ≥ 1`, so never empty

    let lhs = motive_app(s, &tm, &a, &tt);
    let mut cur = under(&Thm::eq_refl(lhs.clone()), &h);

    // The `ni` index nodes, outermost first, then the subject.
    let mut spine = a.clone();
    for k in 0..ni {
        let eq = conj_proj(&atoms, k)?;
        let (pre, post) = (b[..k].to_vec(), spine[k + 1..].to_vec());
        let (sc, mc, lc, tc) = (s.clone(), tm.clone(), lhs.clone(), tt.clone());
        cur = rewrite_under(
            env,
            &eq,
            move |hole| {
                let mut v = pre.clone();
                v.push(hole);
                v.extend(post.iter().cloned());
                Formula::eq(lc.clone(), motive_app(&sc, &mc, &v, &tc))
            },
            &cur,
        )?;
        spine[k] = b[k].clone();
    }
    {
        let eq = conj_proj(&atoms, ni)?;
        let (sc, mc, lc, bc) = (s.clone(), tm.clone(), lhs.clone(), b.clone());
        cur = rewrite_under(
            env,
            &eq,
            move |hole| Formula::eq(lc.clone(), motive_app(&sc, &mc, &bc, &hole)),
            &cur,
        )?;
    }

    let want = Formula::imp(h, Formula::eq(lhs, motive_app(s, &tm, &b, &tu)));
    if !establishes(&cur, &want) {
        return None
    }
    let mut quant = vec![mv];
    quant.extend(avs);
    quant.push(tv);
    quant.extend(bvs);
    quant.push(uv);
    Some(gen_all(&quant, &cur))
}

/// [`motive_congr`] applied: `⊢ app(m, a⃗, t) = app(m, b⃗, u)` from the `ni + 1`
/// equations `⊢ aₖ = bₖ` and `⊢ t = u`, **subject last**.
///
/// The spine terms are read off the equations rather than taken as arguments,
/// so a caller cannot instantiate the scheme in the wrong order — which is the
/// only way to use [`motive_congr`] wrongly, and exactly the drift this
/// function exists to remove. Use [`kernel::Thm::eq_refl`] for a position that
/// does not move; a wholly reflexive call is a legitimate no-op.
///
/// Every equation must be **unconditional**. Under an ambient hypothesis, take
/// [`motive_congr`] itself, [`crate::a1i`] it under the hypothesis and feed the
/// conjunction with [`crate::hyp_and`]; that path is deliberately not wrapped,
/// because the terms would then have to be passed in and the ordering hazard
/// would come straight back.
///
/// `None` on an empty list, on a hypothesis-carrying or non-equational input,
/// and on any internal shape check.
pub fn motive_congr_of(env: &mut Env, s: &Sums, m: &Term, eqs: &[Thm]) -> Option<Thm> {
    if eqs.is_empty() || !all_unconditional(&eqs.iter().collect::<Vec<_>>()) {
        return None
    }
    let mut lefts = Vec::with_capacity(eqs.len());
    let mut rights = Vec::with_capacity(eqs.len());
    for e in eqs {
        let (x, y) = e.concl().as_eq()?;
        lefts.push(x);
        rights.push(y);
    }
    let rule = motive_congr(env, s, eqs.len() - 1)?;
    let mut args = vec![m.clone()];
    args.extend(lefts.iter().cloned());
    args.extend(rights.iter().cloned());
    let at = inst_all(&rule, &args)?;

    let mut acc = eqs.last()?.clone();
    for e in eqs[..eqs.len() - 1].iter().rev() {
        acc = crate::and_intro(e, &acc);
    }
    let out = Thm::mp(&at, &acc)?;
    let (ni, sub) = (eqs.len() - 1, eqs.len() - 1);
    if !establishes(
        &out,
        &Formula::eq(
            motive_app(s, m, &lefts[..ni], &lefts[sub]),
            motive_app(s, m, &rights[..ni], &rights[sub]),
        ),
    ) {
        return None
    }
    Some(out)
}

/// `∀x₀ … ∀x_{n-1}. φ`, outermost first — [`gen_all`] at the formula level.
fn quantify(xs: &[FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}

/// `⊢ tup(u⃗) = tup(v⃗) → uₖ = vₖ` — walk `k` steps down the tuple spine with
/// Kuratowski injectivity, then take the head.
fn tup_proj(s: &Sums, us: &[Term], vs: &[Term], k: usize) -> Option<Thm> {
    if us.len() != vs.len() || k >= us.len() {
        return None
    }
    let ap = &s.ap;
    let mut cur = imp_refl(Formula::eq(
        IndexedDeclSpec::tup(s, us),
        IndexedDeclSpec::tup(s, vs),
    ));
    for lvl in 0..=k {
        let (tu, tv) = (
            IndexedDeclSpec::tup(s, &us[lvl + 1..]),
            IndexedDeclSpec::tup(s, &vs[lvl + 1..]),
        );
        let inj = inst_all(
            &ap.pair_inj,
            &[us[lvl].clone(), tu.clone(), vs[lvl].clone(), tv.clone()],
        )?;
        let both = syl(&cur, &inj)?;
        let (l, r) = (Formula::eq(us[lvl].clone(), vs[lvl].clone()), Formula::eq(tu, tv));
        cur = if lvl == k {
            syl(&both, &and_left(l, r))?
        } else {
            syl(&both, &and_right(l, r))?
        };
    }
    Some(cur)
}

/// An indexed class-(T) declaration's `Prop`-motive elimination rule.
pub struct IndexedPropRecursor {
    /// The motive variable `m`, minted here. Free in
    /// [`IndexedPropRecursor::minor_atoms`] and
    /// [`IndexedPropRecursor::minors`], and bound by the outermost `∀` but one
    /// of [`IndexedPropRecursor::rec`].
    pub motive: FreeVar,
    /// Per constructor, the `kᵢ + mᵢ` field variables **in declared order** —
    /// the binders [`IndexedPropRecursor::minors`] quantifies over and the
    /// variables [`IndexedPropRecursor::minor_atoms`] is stated at. Entry `q` is
    /// the constructor's `q`-th Lean field.
    pub minor_vars: Vec<Vec<FreeVar>>,
    /// Per constructor, `Aᵢ` atom by atom: the `kᵢ + mᵢ` field typings in
    /// declared order, then the `mᵢ` induction hypotheses. See the header for
    /// why the order is Lean's.
    ///
    /// Empty for a constructor with no fields, in which case `MINORᵢ` has no
    /// antecedent at all.
    pub minor_atoms: Vec<Vec<Formula>>,
    /// `MINORᵢ` itself, closed over [`IndexedPropRecursor::minor_vars`].
    pub minors: Vec<Formula>,
    /// `⋀ᵢ MINORᵢ(m)`, the antecedent of [`IndexedPropRecursor::rec`].
    pub hyp: Formula,
    /// The `ni` index variables the conclusion quantifies over, outermost
    /// first — exported, with [`IndexedPropRecursor::major`], so a consumer can
    /// rebuild the statement it is instantiating.
    pub xvs: Vec<FreeVar>,
    /// The major-premise variable `t`, bound **inside** all of
    /// [`IndexedPropRecursor::xvs`].
    pub major: FreeVar,
    /// **`⊢ ∀p⃗ ∀m. (⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. (t ∈ ind(p⃗,x⃗) → • ∈ app(m,x⃗,t)))`**
    /// — unconditional, checked on the way out.
    pub rec: Thm,
}

/// The context one induction step is built in. Private; every field is either
/// the family's or minted by [`IndexedPropRecursor::over_family`].
struct Step<'a> {
    mach: &'a Machine,
    ind: &'a Inductive,
    spec: &'a IndexedDeclSpec,
    ixc: &'a IndexedCarrier,
    /// `goodrec(p⃗)`.
    grec: &'a Term,
    ps: &'a [Term],
    /// The motive term.
    tm: &'a Term,
    zv: FreeVar,
    phi: &'a Formula,
    hyp: &'a Formula,
    minors: &'a [Formula],
}

impl IndexedPropRecursor {
    /// The `Prop`-motive elimination rule for an indexed class-(T) family.
    ///
    /// `fam` must be [`IndexedInductive::build`] over `ind` and `mach`; the
    /// pieces are taken from one struct rather than four arguments precisely so
    /// that a carrier and a `good` from two different builds cannot be mixed.
    /// Every theorem spent is additionally required to be **unconditional** at
    /// the door — a hypothesis riding in on `inv` or `intro` would otherwise
    /// ride into a conclusion documented `⊢`, and neither
    /// [`IndexedInductive::rests_on_nothing`] nor this build's own `establishes`
    /// on the way out would catch it, since a sequent hypothesis is invisible to
    /// a conclusion comparison. On top of that, `inv`, `subset_w` and `good_of`
    /// are compared *after instantiation* against the statement rebuilt here;
    /// `intro` and the skeleton's constructor rule are checked by use, since
    /// [`hyp_mp`] refuses a premise whose shape is not the one the rule asks
    /// for.
    ///
    /// `None` for a declaration with no constructors, for a family whose spec
    /// and skeleton disagree, for a foreign apparatus, and on any internal shape
    /// check.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, so build this
    /// once per declaration and cache it with the result.
    pub fn over_family(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        fam: &IndexedInductive,
    ) -> Option<IndexedPropRecursor> {
        let spec = &fam.spec;
        let ixc = &fam.carrier;
        let (n, ni) = (spec.len(), spec.num_indices());
        if n == 0 || ni == 0 || !ind.is_over(mach) {
            return None
        }
        if ind.spec.ctors.len() != n
            || ind.spec.params != spec.base.params
            || ind.params.len() != spec.base.params
            || ixc.ctors.len() != n
            || ixc.xvs.len() != ni
            || ixc.ty.arity() as usize != spec.base.params + ni
        {
            return None
        }
        if !all_unconditional(&[&ixc.subset_w, &ixc.good_of, &ixc.intro, &ind.ty_ax])
            || !all_unconditional(&ixc.ctors.iter().map(|c| &c.inv).collect::<Vec<_>>())
            || !all_unconditional(&ind.ctors.iter().map(|c| &c.mem).collect::<Vec<_>>())
        {
            return None
        }

        let s = &mach.wt.sums;
        let ap = &s.ap;
        let pt = s.point();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let grec = fam.good.rec.clone();

        // ── `φ(z) := ∀x⃗. (tup(x⃗) ∈ app(goodrec,z) → • ∈ app(m,x⃗,z))` ────────
        let mv = env.fresh_var();
        let tm = Term::var(mv);
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let pxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let pxs: Vec<Term> = pxvs.iter().map(|v| Term::var(*v)).collect();
        let phi = quantify(
            &pxvs,
            Formula::imp(
                Formula::mem(IndexedDeclSpec::tup(s, &pxs), ap.apply(grec.clone(), tz.clone())),
                Formula::mem(pt.clone(), motive_app(s, &tm, &pxs, &tz)),
            ),
        );

        // ── the minors, in Lean field order ─────────────────────────────────
        let mut minor_vars: Vec<Vec<FreeVar>> = Vec::with_capacity(n);
        let mut minor_atoms: Vec<Vec<Formula>> = Vec::with_capacity(n);
        let mut minors: Vec<Formula> = Vec::with_capacity(n);
        let mut fields: Vec<(Vec<FreeVar>, Vec<FreeVar>)> = Vec::with_capacity(n);
        for i in 0..n {
            let c = &spec.base.ctors[i];
            let (k, m) = (c.args.len(), c.recs);
            let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
            let tvs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
            let childs: Vec<Vec<Term>> = (0..m)
                .map(|j| spec.rec_index_vec(i, j, &ps, &ys))
                .collect::<Option<_>>()?;

            let mut vars: Vec<FreeVar> = Vec::with_capacity(k + m);
            let mut atoms: Vec<Formula> = Vec::with_capacity(k + 2 * m);
            let (mut plains, mut recs) = (0usize, 0usize);
            for slot in &c.order {
                match slot {
                    Slot::Plain => {
                        let mut a = ps.clone();
                        a.extend(ys[..plains].iter().cloned());
                        atoms.push(Formula::mem(
                            ys[plains].clone(),
                            Term::apply(*c.args.get(plains)?, a),
                        ));
                        vars.push(yvs[plains]);
                        plains += 1;
                    }
                    Slot::Rec => {
                        atoms.push(Formula::mem(
                            ts.get(recs)?.clone(),
                            ixc.ty_of(&ps, childs.get(recs)?)?,
                        ));
                        vars.push(tvs[recs]);
                        recs += 1;
                    }
                }
            }
            if plains != k || recs != m {
                return None
            }
            for j in 0..m {
                atoms.push(Formula::mem(
                    pt.clone(),
                    motive_app(s, &tm, &childs[j], &ts[j]),
                ));
            }
            let concl = Formula::mem(
                pt.clone(),
                motive_app(
                    s,
                    &tm,
                    &spec.result_vec(i, &ps, &ys)?,
                    &ind.ctor_term(mach, i, &ys, &ts)?,
                ),
            );
            let body = match conj_of(&atoms) {
                Some(h) => Formula::imp(h, concl),
                None => concl,
            };
            minors.push(quantify(&vars, body));
            minor_vars.push(vars);
            minor_atoms.push(atoms);
            fields.push((yvs, tvs));
        }
        let hyp = conj_of(&minors)?;

        // ── `⊢ HYP → RECT(φ)` ───────────────────────────────────────────────
        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != n {
            return None
        }
        let mut steps: Vec<Thm> = Vec::with_capacity(n);
        for i in 0..n {
            let cx = Step {
                mach,
                ind,
                spec,
                ixc,
                grec: &grec,
                ps: &ps,
                tm: &tm,
                zv,
                phi: &phi,
                hyp: &hyp,
                minors: &minors,
            };
            let st = induction_step(env, &cx, i, &fields[i].0, &fields[i].1, &minor_atoms[i])?;
            if *st.concl() != Formula::imp(hyp.clone(), parts[i].clone()) {
                return None
            }
            steps.push(st);
        }
        // `⊢ HYP → ∀z. (z ∈ W → φ(z))`.
        let h_all = syl(&hyp_conj(&steps)?, &decl_rect(env, mach, ind, zv, &phi)?)?;

        // ── the conclusion, at the carrier and at the motive's own indices ──
        let fxvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let fxs: Vec<Term> = fxvs.iter().map(|v| Term::var(*v)).collect();
        let tv = env.fresh_var();
        let tt = Term::var(tv);
        let mem_t = Formula::mem(tt.clone(), ixc.ty_of(&ps, &fxs)?);
        let kf = Formula::and(hyp.clone(), mem_t.clone());
        let k_h = and_left(hyp.clone(), mem_t.clone());
        let k_m = and_right(hyp.clone(), mem_t.clone());

        let mut ca = ps.clone();
        ca.extend(fxs.iter().cloned());
        ca.push(tt.clone());
        let sub = inst_all(&ixc.subset_w, &ca)?;
        if *sub.concl() != Formula::imp(mem_t.clone(), Formula::mem(tt.clone(), ind.wty.clone())) {
            return None
        }
        let gof = inst_all(&ixc.good_of, &ca)?;
        if *gof.concl()
            != Formula::imp(
                mem_t.clone(),
                Formula::mem(
                    IndexedDeclSpec::tup(s, &fxs),
                    ap.apply(grec.clone(), tt.clone()),
                ),
            )
        {
            return None
        }

        let k_phi = hyp_mp(
            &hyp_inst(&syl(&k_h, &h_all)?, std::slice::from_ref(&tt))?,
            &syl(&k_m, &sub)?,
        )?;
        let k_goal = hyp_mp(&hyp_inst(&k_phi, &fxs)?, &syl(&k_m, &gof)?)?;

        let want_body = Formula::mem(pt.clone(), motive_app(s, &tm, &fxs, &tt));
        if *k_goal.concl() != Formula::imp(kf, want_body.clone()) {
            return None
        }
        let mut closed = gen_under(tv, &hyp, &uncurry(&k_goal)?)?;
        for v in fxvs.iter().rev() {
            closed = gen_under(*v, &hyp, &closed)?;
        }

        let mut quant = ind.params.clone();
        quant.push(mv);
        let rec = gen_all(&quant, &closed);
        let want = quantify(
            &quant,
            Formula::imp(
                hyp.clone(),
                quantify(&fxvs, Formula::forall(tv, Formula::imp(mem_t, want_body))),
            ),
        );
        if !establishes(&rec, &want) {
            return None
        }

        Some(IndexedPropRecursor {
            motive: mv,
            minor_vars,
            minor_atoms,
            minors,
            hyp,
            xvs: fxvs,
            major: tv,
            rec,
        })
    }
}

/// `⊢ HYP → rect_stepᵢ(φ)` — one constructor's induction step, discharged from
/// `MINORᵢ`.
fn induction_step(
    env: &mut Env,
    cx: &Step<'_>,
    i: usize,
    yvs: &[FreeVar],
    tvs: &[FreeVar],
    atoms: &[Formula],
) -> Option<Thm> {
    let (mach, ind, spec, ixc) = (cx.mach, cx.ind, cx.spec, cx.ixc);
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let pt = s.point();
    let ps = cx.ps;
    let ni = spec.num_indices();
    let c = &spec.base.ctors[i];
    let (k, m) = (c.args.len(), c.recs);
    if yvs.len() != k || tvs.len() != m || atoms.len() != k + 2 * m {
        return None
    }
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let ctor = ind.ctor_term(mach, i, &ys, &ts)?;
    let res = spec.result_vec(i, ps, &ys)?;
    let childs: Vec<Vec<Term>> =
        (0..m).map(|j| spec.rec_index_vec(i, j, ps, &ys)).collect::<Option<_>>()?;

    // ── `rect_stepᵢ`'s own antecedent, in its own order ─────────────────────
    let mut ratoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(c.args[j], a))
        })
        .collect();
    ratoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), ind.wty.clone())));
    ratoms.extend(ts.iter().map(|t| cx.phi.subst(cx.zv, t)));
    let hr = conj_of(&ratoms);
    let kf = match &hr {
        Some(h) => Formula::and(cx.hyp.clone(), h.clone()),
        None => cx.hyp.clone(),
    };
    let (k_hyp, k_rect) = match &hr {
        Some(h) => (
            and_left(cx.hyp.clone(), h.clone()),
            Some(and_right(cx.hyp.clone(), h.clone())),
        ),
        None => (imp_refl(cx.hyp.clone()), None),
    };
    let rect_at = |j: usize| -> Option<Thm> {
        syl(k_rect.as_ref()?, &conj_proj(&ratoms, j)?)
    };

    // ── under `K2 = kf ∧ (tup(x⃗) ∈ app(goodrec, ctorᵢ))` ────────────────────
    let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
    let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
    let tup_x = IndexedDeclSpec::tup(s, &xs);
    let mem_g = Formula::mem(tup_x.clone(), ap.apply(cx.grec.clone(), ctor.clone()));
    let k2 = Formula::and(kf.clone(), mem_g.clone());
    let k2_kf = and_left(kf.clone(), mem_g.clone());
    let k2_g = and_right(kf.clone(), mem_g.clone());
    let lift = |t: &Thm| syl(&k2_kf, t);

    // The skeleton hypotheses: `rect_step`'s `tⱼ ∈ W`, one Leibniz each.
    let skel_atoms = ctor_atoms(&ind.telescopes[i], ps, &ys, &ts, &ind.carrier);
    let to_skel = eq_symm(env, &inst_all(&ind.ty_ax, ps)?)?; // `W = skel(p⃗)`
    let mut skel: Vec<Thm> = Vec::with_capacity(k + m);
    for j in 0..k {
        skel.push(lift(&rect_at(j)?)?);
    }
    for (j, tj) in ts.iter().enumerate() {
        let base = lift(&rect_at(k + j)?)?;
        let tj = tj.clone();
        skel.push(carry_under(env, &to_skel, move |t| Formula::mem(tj.clone(), t), &base)?);
    }

    // `ctorᵢ(y⃗,t⃗) ∈ W`, then in the carrier at `x⃗`.
    let ctor_w = {
        let mut a = ps.to_vec();
        a.extend(ys.iter().cloned());
        a.extend(ts.iter().cloned());
        let rule = inst_all(&ind.ctors[i].mem, &a)?;
        let base = match hyp_conj(&skel) {
            Some(h) => syl(&h, &rule)?,
            None => under(&rule, &k2),
        };
        let cc = ctor.clone();
        rewrite_under(
            env,
            &under(&inst_all(&ind.ty_ax, ps)?, &k2),
            move |t| Formula::mem(cc.clone(), t),
            &base,
        )?
    };
    let mem_ind = {
        let mut a = ps.to_vec();
        a.extend(xs.iter().cloned());
        a.push(ctor.clone());
        hyp_mp(
            &a1i(&inst_all(&ixc.intro, &a)?, k2.clone()),
            &hyp_and(&ctor_w, &k2_g)?,
        )?
    };

    // ── inversion: the index equality and the children at their own indices ─
    let mut inv_args = ps.to_vec();
    inv_args.extend(ys.iter().cloned());
    inv_args.extend(ts.iter().cloned());
    inv_args.extend(xs.iter().cloned());
    let inv_at = inst_all(&ixc.ctors[i].inv, &inv_args)?;
    let mut want_ante = skel_atoms.clone();
    want_ante.push(Formula::mem(ctor.clone(), ixc.ty_of(ps, &xs)?));
    let mut want_out = vec![Formula::eq(tup_x.clone(), IndexedDeclSpec::tup(s, &res))];
    for j in 0..m {
        want_out.push(Formula::mem(ts[j].clone(), ixc.ty_of(ps, &childs[j])?));
    }
    if *inv_at.concl() != Formula::imp(conj_of(&want_ante)?, conj_of(&want_out)?) {
        return None
    }
    let mut prem = skel.clone();
    prem.push(mem_ind);
    let inv_out = syl(&hyp_conj(&prem)?, &inv_at)?;

    let eq_tup = syl(&inv_out, &conj_proj(&want_out, 0)?)?;
    let mut idx_eqs: Vec<Thm> = Vec::with_capacity(ni);
    for q in 0..ni {
        idx_eqs.push(syl(&eq_tup, &tup_proj(s, &xs, &res, q)?)?);
    }
    let mut child_mem: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        child_mem.push(syl(&inv_out, &conj_proj(&want_out, 1 + j)?)?);
    }

    // The induction hypotheses, fired at the child's **own** indices.
    let mut ihs: Vec<Thm> = Vec::with_capacity(m);
    for j in 0..m {
        let at_child = hyp_inst(&lift(&rect_at(k + m + j)?)?, &childs[j])?;
        let mut ga = ps.to_vec();
        ga.extend(childs[j].iter().cloned());
        ga.push(ts[j].clone());
        ihs.push(hyp_mp(&at_child, &syl(&child_mem[j], &inst_all(&ixc.good_of, &ga)?)?)?);
    }

    // ── `MINORᵢ`, instantiated at the fields in **declared** order ──────────
    let mut lean_terms: Vec<Term> = Vec::with_capacity(k + m);
    let mut lean_thms: Vec<Thm> = Vec::with_capacity(k + 2 * m);
    let (mut plains, mut recs) = (0usize, 0usize);
    for slot in &c.order {
        match slot {
            Slot::Plain => {
                lean_terms.push(ys[plains].clone());
                lean_thms.push(lift(&rect_at(plains)?)?);
                plains += 1;
            }
            Slot::Rec => {
                lean_terms.push(ts[recs].clone());
                lean_thms.push(child_mem[recs].clone());
                recs += 1;
            }
        }
    }
    if plains != k || recs != m {
        return None
    }
    lean_thms.extend(ihs.iter().cloned());
    for (q, th) in lean_thms.iter().enumerate() {
        if *th.concl() != Formula::imp(k2.clone(), atoms[q].clone()) {
            return None
        }
    }

    let minor = hyp_inst(
        &syl(&lift(&k_hyp)?, &conj_proj(cx.minors, i)?)?,
        &lean_terms,
    )?;
    let mut cur = match hyp_conj(&lean_thms) {
        Some(p) => hyp_mp(&minor, &p)?,
        None => minor,
    };

    // ── move the conclusion from `e⃗ᵢ` to `x⃗`, one index at a time ──────────
    let mut spine = res.clone();
    for q in 0..ni {
        let back = hyp_eq_symm(env, &idx_eqs[q])?;
        let (pre, post) = (xs[..q].to_vec(), spine[q + 1..].to_vec());
        let (sc, tmc, cc, ptc) = (s.clone(), cx.tm.clone(), ctor.clone(), pt.clone());
        cur = rewrite_under(
            env,
            &back,
            move |hole| {
                let mut v = pre.clone();
                v.push(hole);
                v.extend(post.iter().cloned());
                Formula::mem(ptc.clone(), motive_app(&sc, &tmc, &v, &cc))
            },
            &cur,
        )?;
        spine[q] = xs[q].clone();
    }
    if *cur.concl()
        != Formula::imp(
            k2,
            Formula::mem(pt.clone(), motive_app(s, cx.tm, &xs, &ctor)),
        )
    {
        return None
    }

    // ── close `∀x⃗`, then the constructor's own fields ───────────────────────
    let mut acc = uncurry(&cur)?;
    for v in xvs.iter().rev() {
        acc = gen_under(*v, &kf, &acc)?;
    }
    if *acc.concl() != Formula::imp(kf, cx.phi.subst(cx.zv, &ctor)) {
        return None
    }
    match &hr {
        None => Some(acc),
        Some(_) => {
            let mut out = uncurry(&acc)?;
            for v in tvs.iter().rev() {
                out = gen_under(*v, cx.hyp, &out)?;
            }
            for v in yvs.iter().rev() {
                out = gen_under(*v, cx.hyp, &out)?;
            }
            Some(out)
        }
    }
}
