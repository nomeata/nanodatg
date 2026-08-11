//! **The degenerate recursor** — the eliminator of a one-constructor,
//! non-recursive declaration, which is the inverse of its constructor.
//!
//! # The whole idea, in one line
//!
//! ```text
//! S.rec C f (S.mk a⃗)  ≡  f a⃗
//! ```
//!
//! A one-constructor inductive **has no case analysis**. Every apparatus in
//! [`super::recursor`] — the packed step, one Replacement per constructor,
//! single-valuedness across `n²` branch comparisons, `HYP`, `step_typed`, and
//! above all a *target set* `T` for the W-recursor to land in — exists because
//! the general construction has to branch over constructors and the branching
//! needs somewhere to go. At one constructor there is nothing to branch over
//! and no target to decide: the eliminator's value at `x` is the minor premise
//! applied to `x`'s fields, and `ctor₀` is what puts them there.
//!
//! So this file is **beside** [`super::recursor::GenRecursor`] and not inside
//! it. Threading a special case through the general construction would keep
//! every part the diagnosis says is unnecessary; the point is that none of them
//! is reached.
//!
//! # Interface
//!
//! With `k` the constructor's field count, `s` the minor premise and `z` the
//! major premise:
//!
//! ```text
//! drec(s, z) := app(…app(s, π₀ z)…, π_{k-1} z)              [DegenRec::value_of]
//! ⊢ ∀y⃗. πⱼ(ctor₀(y⃗)) = yⱼ                                   [DegenRec::proj_computes]
//! ⊢ ∀s ∀y⃗. drec(s, ctor₀(y⃗)) = app(…app(s,y₀)…,y_{k-1})     [DegenRec::iota]
//! ```
//!
//! Both theorems are **unconditional and free of `p⃗`**, and both facts are
//! load-bearing rather than incidental.
//!
//! *Unconditional*: the general (S4) carries `HYP ∧ Hᵢ^ctor`, because the
//! W-recursor's ι needs the step to be typed into `T` and the recursive
//! children to be in the carrier. Here there is no `T` and no child. Nothing
//! about `z ∈ ind(p⃗)` is needed either — every layer of a class-(T) carrier
//! element is a literal Kuratowski pair, so the projections compute on the term
//! (see [`super::decl_proj::computes`]).
//!
//! *Parameter-free*: `ctor₀(y⃗)` is `⟨Inj₀(tuple y⃗), f()⟩`, and at `m = 0` none
//! of those layers takes `p⃗`. The parameters live in the field *types* `βⱼ`,
//! which this rule never mentions because it assumes nothing about the fields.
//! A consumer therefore instantiates `∀s ∀y⃗` and is done: no parameter spine,
//! no [`Inductive::ty_ax`] bridge, no type-former nest.
//!
//! # Two consumers, one theorem
//!
//! [`DegenRec::proj_computes`] is not a private step of the ι derivation that
//! happens to be exported. It is **the projection reduction rule** —
//! `(mk a⃗).j ⟶ aⱼ` — at the same declaration, and the two Lean rules are the
//! same eliminator asked by different syntax: `S.rec C f (S.mk a⃗)` at the
//! projection motive *is* `(S.mk a⃗).j`. A checker that wires only one of them
//! from this bundle is leaving the other on the table for no derivation it does
//! not already have.
//!
//! The bundle is therefore built **once per declaration and cached**, and both
//! rules come out of it — the standing memo rule, and here it is also what keeps
//! the two consumers on one spelling of `πⱼ` ([`super::decl_proj::proj_of`]).
//!
//! # The sibling this does **not** cover, and how they sit together
//!
//! A consumer's gate on the general recursor is the *target policy*: it needs a
//! nullary constructor to site the motive's canonical point at, and declines
//! when there is none. That gate catches two populations, and they are two
//! constructions rather than one:
//!
//! * **one constructor, fields** — this file. There is nothing to branch over,
//!   so there is no target to pick.
//! * **several constructors, none nullary** — *not* this file, and not a
//!   widening of it. Several constructors do have a case analysis; what they
//!   want is a target that is not a constructor's value (an image-union over the
//!   motive is the standing proposal), which is a question inside
//!   [`super::recursor`] and its `carrier_at`, not out here.
//!
//! The two therefore compose by a **shape test on the declaration** —
//! `ctors.len() == 1 && recs == 0` — and nothing else, with this path taken
//! first because it is strictly cheaper. Two properties make trying it first
//! free, and both are worth relying on:
//!
//! * [`DegenRec::build`] **mints no symbol into `env`** — no `define_abbrev`, no
//!   Replacement, no Separation, only fresh variables. Contrast
//!   [`super::recursor::GenRecursor::build`], whose own header records that a
//!   late refusal used to leave the environment permanently larger because
//!   `StepSym::new` had already minted one Replacement per constructor. A
//!   decline here costs nothing and leaves nothing behind.
//! * Nothing here reads or constrains the carrier's universe bound, so a
//!   sibling that changes how the target is chosen cannot collide with it: this
//!   construction has no target.
//!
//! # Why there is no eliminator *set*
//!
//! `drec` is a term in `s` and `z`, not a function whose graph is a set. That is
//! deliberate, and it is not a weaker deliverable:
//!
//! * A consumer's currying nest bottoms out in **a term in the major premise**
//!   (`checker`'s `RecNest`), so a set would be built only to be applied.
//! * Building one means a Replacement over `ind(p⃗)` and `app(R, z) = drec(s,z)`
//!   for `z ∈ ind(p⃗)` — so every ι firing would acquire a membership premise
//!   `ctor₀(y⃗) ∈ ind(p⃗)` that the equation above does not have. That is a cost
//!   paid for nothing: the set's only content is the term.
//! * The W-recursor is a set because it is defined by *recursion*, and there is
//!   no recursion here — which is the same observation as "no target", one level
//!   down.
//!
//! # Scope, and where each refusal happens
//!
//! One constructor, **no recursive field**, over the apparatus the declaration
//! was translated against. The recursive case is not a near miss: at `m > 0` the
//! `j`-th induction hypothesis is `drec(s, ρⱼ(z))` with `ρⱼ` reading a child out
//! of `sup`'s second component, and defining a term by an equation that mentions
//! itself is exactly the W-recursor. That case belongs to
//! [`super::recursor::GenRecursor`] and is declined here by name rather than
//! left to fail somewhere inside.
//!
//! | input | refuser |
//! |---|---|
//! | two or more constructors | [`DegenRec::build`]'s own guard |
//! | a recursive field | [`DegenRec::build`]'s own guard (and `ctor_term` behind it) |
//! | a foreign apparatus | [`Inductive::is_over`], at the door and at every term-former |
//! | a field mask that is not all-plain | [`DegenRec::build`]'s own guard |
//!
//! `k = 0` is **allowed**, and its ι rule is `⊢ ∀s. s = s`. That is true, and it
//! is the right degenerate value rather than a bug: a fieldless one-constructor
//! declaration's eliminator *is* its minor premise. It is also the one case a
//! consumer should not route here — the general recursor's target policy 1
//! already serves an all-nullary declaration, and does so with a real W-recursor
//! — so the field count is exported ([`DegenRec::arity`]) for a caller that
//! wants to choose.
//!
//! # Nothing here is an axiom
//!
//! No Separation, no Replacement, no new symbol at all. `k` chains of `j + 3`
//! projection instantiations ([`super::decl_proj::computes`]) and `k` Leibniz
//! steps to walk them into the minor premise's argument positions.
//!
//! [`Inductive::ty_ax`]: super::carrier::Inductive

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::err::{DResult, Operand};
use crate::{assembly, decline, establishes, gen_all};

use super::carrier::Inductive;
use super::decl_proj::{computes, proj_of};
use super::machine::{Machine, MachineId};
use super::spec::Slot;
use super::step::applied_minor;

/// The degenerate recursor of one declaration: the projection rules it is built
/// from, and the ι rule it is.
pub struct DegenRec {
    /// The minor-premise variable `s`, bound by the first `∀` of
    /// [`DegenRec::iota`].
    pub minor: FreeVar,
    /// The field variables `y₀ … y_{k-1}`, bound after it — and by the `∀` of
    /// each [`DegenRec::proj_computes`]. Exported so a consumer can rebuild
    /// what it instantiates.
    pub fields: Vec<FreeVar>,
    /// **`⊢ ∀y⃗. πⱼ(ctor₀(y⃗)) = yⱼ`**, one per field in declared order — the
    /// projection reduction rule, and the ι rule's own ingredient. Empty at
    /// `k = 0`.
    pub proj_computes: Vec<Thm>,
    /// **`⊢ ∀s ∀y⃗. drec(s, ctor₀(y⃗)) = app(…app(s,y₀)…,y_{k-1})`.**
    pub iota: Thm,
    /// The number of fields, `k`.
    pub arity: usize,
    /// The declaration this eliminates — [`Inductive::ty`], the carrier's own
    /// defined symbol.
    pub decl: FnSym,
    /// The apparatus it was built over.
    pub machine: MachineId,
}

impl DegenRec {
    /// Derive the ι rule and the `k` projection rules of a one-constructor,
    /// non-recursive declaration.
    ///
    /// Declines — see the module header's table — for a declaration that is not
    /// of that shape, and for an `ind` that is not the declaration translated
    /// over `mach` ([`Inductive::is_over`]): every term below resolves `Inj₀`,
    /// the pairing and the projections against `mach`'s symbols, and a second
    /// apparatus with warm caches answers all of them, with theorems about
    /// somebody else's sets.
    ///
    /// Build this **once per declaration and cache it**, with its theorems: the
    /// field variables are drawn from `env` and two builds hand back two rules
    /// about two sets of variables, which a consumer holding one and
    /// instantiating the other cannot chain.
    pub fn build(env: &mut Env, mach: &Machine, ind: &Inductive) -> DResult<DegenRec> {
        if !ind.is_over(mach) {
            return Err(decline!("DegenRec: the declaration is not translated over this apparatus"))
        }
        if ind.spec.ctors.len() != 1 {
            return Err(decline!(
                "DegenRec: not a one-constructor declaration — the general recursor's case"
            ))
        }
        let c = &ind.spec.ctors[0];
        if c.recs != 0 {
            return Err(decline!(
                "DegenRec: the constructor takes a recursive field — the induction hypothesis \
                 needs the W-recursor, which is GenRecursor"
            ))
        }
        if c.order.iter().any(|sl| *sl != Slot::Plain) {
            return Err(decline!("DegenRec: the field mask is not all-plain at m = 0"))
        }
        let k = c.args.len();
        let ap = mach.wt.sums.ap.clone();

        let sv = env.fresh_var();
        let s = Term::var(sv);
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();

        // ── the `k` projection rules, at those very variables ───────────────
        let rules: Vec<Thm> =
            (0..k).map(|j| computes(env, mach, ind, j, &ys)).collect::<DResult<_>>()?;

        // `ctor₀(y⃗)`, and the projections *out of it* — the terms the rules are
        // about, and the arguments `drec` puts in the minor premise's slots
        // before any of them is rewritten.
        let Some(ctor) = ind.ctor_term(mach, 0, &ys, &[]) else {
            return Err(decline!("DegenRec: this declaration has no fieldwise constructor term"))
        };
        let pc: Vec<Term> = (0..k).map(|j| proj_of(&ap, &mach.proj, j, ctor.clone())).collect();

        // The minor premise applied to a caller-supplied argument list, in the
        // declaration's own field order. `super::step::applied_minor` and not a
        // local fold: the general ι rules, `HYP` and the step value all spell
        // the convention with it, and a consumer that fires both recursors must
        // see one convention.
        let order = c.order.clone();
        let mk = |v: &[Term]| applied_minor(&ap, &order, &s, v, &[], &[]);

        // ── walk `πⱼ(ctor₀(y⃗))` to `yⱼ`, one argument position at a time ────
        //
        // `spine` is the right-hand side as it stands; the left stays
        // `drec(s, ctor₀(y⃗))` throughout. The hole goes only in position `i` of
        // the right, so the `pc[i]` occurrences on the *left* are untouched —
        // which is the whole reason this is a Leibniz over a hole and not a
        // rewrite of a term.
        let mut spine = pc.clone();
        let mut cur = Thm::eq_refl(mk(&pc));
        for i in 0..k {
            let hole = env.fresh_var();
            let mut with_hole = spine.clone();
            with_hole[i] = Term::var(hole);
            let leib = Thm::eq_leibniz(
                pc[i].clone(),
                ys[i].clone(),
                hole,
                Formula::eq(mk(&pc), mk(&with_hole)),
            );
            cur = crate::prim::mp(&crate::prim::mp(&leib, &rules[i])?, &cur)?;
            spine[i] = ys[i].clone();
        }

        let want = Formula::eq(mk(&pc), mk(&ys));
        if !establishes(&cur, &want) {
            return Err(assembly!(
                "DegenRec: the ι chain did not land on drec(s, ctor₀(y⃗)) = s y⃗",
                Operand::thm("cur", &cur),
                Operand::formula("want", &want),
            ))
        }

        // ── generalise: the minor premise, then the fields ──────────────────
        let mut outer = vec![sv];
        outer.extend(yvs.iter().copied());
        let iota = gen_all(&outer, &cur);
        let proj_computes: Vec<Thm> = rules.iter().map(|r| gen_all(&yvs, r)).collect();

        // The way out. Both exports are stated `⊢ …` in the header, and
        // `Thm::gen` cannot discharge a sequent hypothesis, so anything that
        // arrived with one is still carrying it. Nothing above can produce one
        // — which is the point: this is what says so.
        let fields: Vec<&Thm> = std::iter::once(&iota).chain(proj_computes.iter()).collect();
        if !crate::all_unconditional(&fields) {
            return Err(assembly!(
                "DegenRec: an export carries a sequent hypothesis",
                Operand::thm("iota", &iota),
            ))
        }

        Ok(DegenRec {
            minor: sv,
            fields: yvs,
            proj_computes,
            iota,
            arity: k,
            decl: ind.ty,
            machine: mach.ident(),
        })
    }

    /// Whether `mach` and `ind` are the apparatus and the declaration this
    /// recursor was built over.
    ///
    /// [`Inductive::is_over`] ties a declaration to a machine; this ties *the
    /// eliminator* to both. Two of the three agreeing is not enough: a second
    /// declaration over the same machine has its own `Inj₀` and its own carrier,
    /// so this bundle's rules at that declaration's terms would be theorems
    /// about the wrong sets, and — since [`DegenRec::value_of`] hands back a
    /// *term* — nothing downstream could notice.
    pub fn is_over(&self, mach: &Machine, ind: &Inductive) -> bool {
        self.machine == mach.ident() && self.decl == ind.ty && ind.is_over(mach)
    }

    /// **`drec(s, z) = app(…app(s, π₀ z)…, π_{k-1} z)`** — the eliminator's
    /// value at a caller-supplied minor premise and major premise.
    ///
    /// This is what a consumer puts at the bottom of its currying nest, and it
    /// is the left-hand side [`DegenRec::iota`] is stated at: at
    /// `z := ctor₀(y⃗)` the two are the same term by construction, not by check.
    ///
    /// Declines unless `mach`/`ind` are this bundle's own
    /// ([`DegenRec::is_over`]).
    pub fn value_of(&self, mach: &Machine, ind: &Inductive, s: &Term, z: &Term) -> DResult<Term> {
        if !self.is_over(mach, ind) {
            return Err(decline!("DegenRec::value_of: not this bundle's apparatus or declaration"))
        }
        let ap = &mach.wt.sums.ap;
        let projs: Vec<Term> =
            (0..self.arity).map(|j| proj_of(ap, &mach.proj, j, z.clone())).collect();
        Ok(applied_minor(ap, &ind.spec.ctors[0].order, s, &projs, &[], &[]))
    }

    /// **`πⱼ(z)`** at a caller-supplied subject — [`proj_of`], with the field
    /// index range-checked against this declaration.
    ///
    /// The projection consumer's term-former: it holds `⟦s⟧`, builds `⟦projⱼ s⟧`
    /// with this, and instantiates [`DegenRec::proj_computes`]`[j]` at its own
    /// fields. One spelling, so the checker's subject and the theorems' subject
    /// are the same function.
    pub fn proj_at(&self, mach: &Machine, ind: &Inductive, j: usize, z: Term) -> DResult<Term> {
        if !self.is_over(mach, ind) {
            return Err(decline!("DegenRec::proj_at: not this bundle's apparatus or declaration"))
        }
        if j >= self.arity {
            return Err(decline!("DegenRec::proj_at: the field index is out of range"))
        }
        Ok(proj_of(&mach.wt.sums.ap, &mach.proj, j, z))
    }
}
