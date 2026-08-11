//! **An axiom's inhabitation** — the interpretation's *third* insertion point
//! (`MINI-HANDOFF.md` §14).
//!
//! # Interface
//!
//! ```text
//! axiom::clause_for(name)                  -> Option<Clause>
//! axiom::inhabit(checker, cl, name, σ, ty) -> Result<Thm, Gap>
//! ```
//!
//! Called from [`crate::mini::ledger::Ledger::run`], on a `Declaration::Axiom` whose
//! **type has already interpreted**, immediately before the fallback that files
//! the pair as `Gap::Axiom(name)`.
//!
//! # Why it cannot live where the other two clauses live
//!
//! There are three places an interpretation clause can be reached from, and
//! which one a clause belongs to is decided by *what asks for it*:
//!
//! | # | point | what triggers it |
//! |---|---|---|
//! | 1 | [`crate::mini::zoneb::ensure`] | an **inductive or `Quot` declaration** being reached, at each scheduled σ |
//! | 2 | [`crate::mini::direct::build`] | point 1, on a declaration `direct::clause_for` names |
//! | 3 | **here** | a declaration reaching its own typing obligation |
//!
//! *(Point 1's trigger used to read "a **constant occurrence** that misses the
//! store", and it was rewritten when `crate::mini::ledger::fill_declaration` started
//! driving `ensure` from the schedule. The rest of this section is unchanged
//! and was never about the trigger: it is about which obligation each point can
//! **see**, and an axiom's is invisible to points 1 and 2 either way.)*
//!
//! Points 1 and 2 structurally cannot see this obligation, and the reason is
//! not about quotients:
//!
//! > **An axiom's inhabitation is the one obligation with no constant
//! > occurrence to hang off**, and it will be true of every axiom this project
//! > ever certifies.
//!
//! `ensure` runs on an inductive declaration and its constants. An axiom's own
//! pair is reached by the declaration walk, which mints `⟦c.{σ}⟧` for it before
//! anything mentions it — and for an axiom that mint is an **opaque symbol**, a
//! pure signature extension about which nothing whatever is derivable, so the
//! typing is `Err(Gap::Axiom)` by construction. Hooking `ensure` instead is not
//! merely late, it is **silently wrong**: `Ledger::run`'s store-hit branch `continue`s
//! without counting the pair's constant typing at all, so an axiom pre-filled
//! from `ensure` would leave a pair that emits no `waiting:` row and no
//! `constEv` — an absence with no reason, which is the one thing this project's
//! ledger exists to prevent.
//!
//! # What a clause here must produce, and what it may not
//!
//! `⊢ • ∈ ⟦ty[σ]⟧`, together with the interpretation `•`. **Only a
//! proof-valued axiom can be certified this way** and that is not a
//! restriction this module imposes: §6.2 gives every proof the denotation `•`,
//! so an axiom whose type is not a `Prop` would have to inhabit a genuine set,
//! and no clause below produces one. The `Prop`-ness is not tested here either
//! — it is *derived*: the nest's own bottom membership is checked against the
//! declared codomain's interpretation, and a codomain that is not a
//! proposition does not yield one.
//!
//! **This is where a false axiom would become unsoundness, and the discipline
//! is the one every other clause here uses.** The name selects, the derivation
//! verifies: the nest is built from the constant's *own declared type*, its
//! depth is checked against that type, and the bottom's membership is checked
//! against the declared codomain's interpretation. An axiom that is called
//! `Quot.sound` and states something else produces a membership in the wrong
//! set and is declined with a reason.
//!
//! # `Quot.sound`
//!
//! ```text
//! Quot.sound.{u} : ∀ (α : Sort u) (r : α → α → Prop) (a b : α),
//!                    r a b → Eq (Quot α r) (Quot.mk α r a) (Quot.mk α r b)
//! ```
//!
//! At `u = 0` the whole codomain is `Eq` at two *proofs*, so both sides are `•`
//! and the set is `eq_set(•,•)`: the obligation is reflexivity, and `r a b` is
//! never consulted — `sound` is **free** at `Sort 0` because `⟦α⟧` is a
//! subsingleton (`QUOT-MODEL.md` §2.3's T8, §1.4). `derived/` owes nothing.
//!
//! At `u ≥ 1` this module is not reached at all, and not because it declines:
//! the *type* does not interpret, because `⟦Quot.{1}⟧` is the equivalence-class
//! clause and is not built. The pair keeps `quot-classes(u:1)` as its reason,
//! which is the axis it belongs on.
//!
//! # `propext`
//!
//! ```text
//! propext : ∀ {a b : Prop}, (a ↔ b) → a = b
//! ```
//!
//! `⟦Prop⟧` is `U₀ = {∅, {•}}`, so `⟦a⟧` and `⟦b⟧` are subsets of `1` and a
//! subset of `1` is determined by whether `•` is in it. The biconditional gives
//! both implications between `• ∈ ⟦a⟧` and `• ∈ ⟦b⟧`, and Extensionality
//! closes it: [`derived::prop::prop_ext`]. Carneiro §6.3 is the same argument,
//! and it needs no set-theoretic axiom — which is the contrast
//! `derived/src/choice.rs`'s header draws.
//!
//! The codomain is an equation at **`Eq.{1}`**, not `Eq.{0}`: the two sides are
//! `Prop`s and `Prop : Sort 1`. So this clause takes `Quot.sound`'s `u ≥ 1`
//! path through [`crate::mini::direct::eq_bottom`] — an equation between two terms
//! that are not syntactically the same — and the only new thing is the equation
//! itself, [`propext_eq`].
//!
//! # `Classical.choice` — one clause, and it covers half the levels
//!
//! ```text
//! Classical.choice.{u} : ∀ {α : Sort u}, Nonempty α → α
//! ```
//!
//! **This is the one axiom whose clause is not the same derivation at every
//! `σ`**, and the reason is the sentence the "what a clause here must produce"
//! section used to open with: *only a proof-valued axiom can be inhabited this
//! way*. At `u = 0` the codomain `α` *is* a `Prop`, so `Classical.choice.{0}` is
//! proof-valued and this module's frame fitted it with nothing moved. At
//! `u ≥ 1` it is not: `⟦Classical.choice α h⟧` is `ε(⟦α⟧)` (§6.2), not `•`.
//!
//! **That restriction is now lifted, and it was never a soundness property.**
//! [`inhabit`] returns `(Term, Thm)` and checks that the membership is about the
//! term the nest interpreted to; [`crate::mini::ledger`] stores that term. The old
//! pair of checks — "`tm` is `•`", "the conclusion is `• ∈ ⟦ty[σ]⟧`" — got the
//! same guarantee by pinning both sides to one constant, which worked only while
//! there was one constant to pin them to. The header's rule is therefore now:
//!
//! > A clause must produce a **term and its membership in `⟦ty[σ]⟧`**. For a
//! > proof-valued axiom that term is `•` and nothing changed; for
//! > `Classical.choice` at `u ≥ 1` it is `ε(⟦α⟧)`.
//!
//! **That was described here as the smaller half of the problem, with the
//! larger being that "`ε` is not a term of the kernel's language and cannot be
//! made one here". The larger half is gone, and it is now the only half.** The
//! paragraph is rewritten rather than annotated, because it told the next reader
//! that the blocker was in `kernel/` and `derived/`, and it is in this file and
//! `crate::mini::ledger`.
//!
//! `ε` **is** a term of the kernel's language. `kernel::thm::henkin` mints a
//! 0-ary constant from `⊢ ∃y. φ` with `FV(φ) ⊆ {y}` — a Henkin constant, not
//! Skolemisation, which at arity ≥ 1 would be unsound here — and
//! [`derived::choice::Epsilon`] is its one caller and the seam a replacement
//! would cut at. `Epsilon::on(env, u)` requires a **closed** `u`, which every
//! rung of `derived::tower` is, and yields two hypothesis-free sentences:
//! `⊢ IsChoiceFn(ε, Uₙ)` and
//! `⊢ ∀x. ((x ∈ Uₙ ∧ ∃w. w ∈ x) → app(ε,x) ∈ x)`. Both reach a
//! [`crate::mini::ev::Sealed`] — the funnel checks `hyps().is_empty()` and there is
//! nothing in either to check against.
//!
//! **The nonemptiness half is already there**, which is worth saying so that
//! nobody spends an agent on it: `Nonempty` is class (P), its carrier is
//! `‖·‖`, and
//! [`TruncFields::elim_psi`](derived::inductive::family::TruncFields::elim_psi)
//! at one field is `⊢ ∀α. (• ∈ ‖Nonempty α‖ → ∃y. y ∈ β₀(α))` — which is
//! `derived::choice::choice_app`'s `∃w. w ∈ x` antecedent, modulo the
//! abbreviation `β₀(α) = ⟦α⟧` every class-(P) consumer already carries. (The
//! *ladder* beneath `elim_psi` is not usable here and does not need to be: its
//! `Pⱼ : βⱼ ⊆ 1` is false for a data field.)
//!
//! So the missing thing is still not a lemma, and it is no longer a decision
//! either — the kernel rule was taken, on 2026-08-10, and the alternative
//! (mini's evidence carrying one distinguished whole-run hypothesis
//! `IsChoiceFn(f, U_ω)`, which would have changed what a `Sealed` means for
//! `checker/` too) was **not**. What is left is plumbing in this file and in
//! `crate::mini::ledger`, and it splits by level in a way worth writing down, because
//! the two halves are unequal and only one of them needs `ε` at all.
//!
//! ### `σ = [0]` — **done**, and it needed no `ε`
//!
//! At `u = 0` the type is `∀ {α : Prop}, Nonempty α → α`. The nest bottom's
//! `ty` is `α : Sort 0`, so [`crate::mini::kernel::Checker::lam_nest`] takes
//! `lam_evidence`'s **`Prop` branch at both binders and `tm` is `•`** — the
//! existing `t.tm == Some(point)` check passes unchanged and the ledger's
//! `term: ip.point()` is already right. The obligation is `⊢ • ∈ ⟦α⟧`, and that
//! is not `elim_psi` but the class-(P) ladder: `TruncFields::steps[0]` needs
//! `P₀ : β₀(α) ⊆ 1`, which at `u = 0` is [`crate::mini::rec_prop::subset_of_unit`] at
//! the `α` binder's `⟦α⟧ ∈ U₀`. `crate::mini::proj_prop::trunc_typing`'s
//! major-premise block is the template and [`choice_point`] follows it step for
//! step. **Nothing in `crate::mini::ledger` changed.**
//!
//! The measurement, `mini/tests/fixtures/standard_axioms.lean`:
//!
//! ```text
//! before  constEv=3  library-gap=4  waiting:axiom(Classical.choice)=4
//! after   constEv=5  library-gap=2  waiting:axiom(Classical.choice)=2
//! ```
//!
//! Two, not one, because the four pairs were never four σ of one declaration:
//! they are `Classical.choice` and its use site `choiceUse`, at `u := 0` and
//! `u := 1` each. Half the pairs of the standard axiom that this project's goal
//! statement cannot excuse are closed by a derivation with no choice in it —
//! which is the right answer and not a shortcut. At `u = 0`, `Nonempty α`
//! *already is* the statement that `⟦α⟧` is the inhabited one of `U₀`'s two
//! elements; there is nothing left to choose.
//!
//! ### `σ = [1]` and above — **done**, and this is where `ε` is
//!
//! `P₀` is false for a data field above `Prop`, so the ladder is unusable and
//! the fact needed is the rung above it,
//! [`TruncFields::elim_psi`](derived::inductive::family::TruncFields::elim_psi),
//! `⊢ ∀α. (• ∈ ‖Nonempty α‖ → ∃y. y ∈ β₀(α))` — *some* element exists, with
//! nothing said about which, which is exactly the shape a choice function is
//! for and exactly the `∃w. w ∈ x` antecedent of
//! [`derived::choice::Epsilon::chooses`]. The other antecedent, `⟦α⟧ ∈ Uᵤ`, *is*
//! the `α` binder's own membership, because [`Interp::sort`] is
//! `prelude.tower.u(u)` and nothing has to be moved onto it. See
//! [`choice_epsilon`], and [`crate::mini::choice_clause`] for the per-rung `ε`.
//!
//! Three things moved, none of them in `kernel/` or `derived/`: [`inhabit`]
//! hands back a `Term` beside the `Thm`; `crate::mini::ledger` stores it; and
//! `lam_evidence`'s **non-`Prop`** branch fires from an axiom nest for the first
//! time. That last had no precedent to copy and turned out to need nothing new —
//! it is the branch every `def` already goes through, and an axiom nest is a
//! `lam_nest` like any other once its bottom denotes a value.
//!
//! What did bite, and is worth the line because it will bite the next clause
//! too: a nest binder's typing **carries hypotheses**. `crate::mini::scope` is mini's
//! one `Thm::assume` module and `⟦α⟧ ∈ Uᵤ` arrives as an assumption discharged
//! by `lam_evidence` as the nest closes. A `hyps().is_empty()` guard on those
//! premises — which reads like prudence — declined every call.
//!
//! ```text
//! before Clause::Choice   constEv=3  library-gap=4  waiting:axiom(Classical.choice)=4
//! after u = 0             constEv=5  library-gap=2  waiting:axiom(Classical.choice)=2
//! after u ≥ 1             constEv=7  no library-gap, no waiting rows
//! ```
//!
//! `constEv == pairs` on that fixture: every pair is certified, so there is no
//! reason row left for a later change to hide behind.
//!
//! `mini/tests/fixtures/standard_axioms.lean` keeps all four pairs measurable
//! meanwhile, and it is still measuring 4: **the kernel rule and its
//! encapsulation closed no pair on their own, and nothing here changed.**
//!
//! # What `propext` alone buys on the generated models — counted
//!
//! It is not zero and it is not the W route. `#print axioms` over
//! `scripts/inductive-basis/`, 2026-08-10:
//!
//! | generator | bill | covered now |
//! |---|---|---|
//! | `WFromPaths` 7 + `WIndexedCarve` 24 | `propext, Classical.choice, Quot.sound` — all 31 | no |
//! | `AccArmShapes` — arm G, 6 | `Classical.choice`, and `Quot.sound` at the two `iota`s | no |
//! | `AccPhi::literal_has_no_rec` | `propext, Quot.sound` | **yes** |
//!
//! So **`propext` closes no W model and no arm-G model on its own**: every
//! declaration that spends it on the W route spends `Classical.choice` too, and
//! from the *same* source — `WFromPaths.lean`'s header says the label test goes
//! through `Classical.propDecidable`, "hence choice, hence (via
//! `Classical.em`) propext. Nothing else in the construction is classical."
//! Arm G spends choice and never propext at all.
//!
//! Two consequences worth having in one place. First, a bill of
//! `[propext, Quot.sound]` or any subset is now **fully covered**, which is the
//! shape `AccPhi` already produces. Second, the lever on the W route is not
//! this module: `WFromPaths.lean`'s item E records that the classical dispatch
//! is avoidable whenever `B` factors through the constructor tag — "almost all
//! of them" — and that removes *both* axioms at the generator instead of
//! certifying either here.

use kernel::{Formula, Term, Thm};

use crate::mini::env::ConstantInfo;
use crate::mini::ev::{Ev, Gap};
use crate::mini::expr::{Expr, Name, NameView, E};
use crate::mini::ground;
use crate::mini::interp::{Interp, PiShape};
use crate::mini::kernel::{Checker, Typing, R};

/// Which axiom this module can inhabit, if any.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// `Quot.sound.{u}` — reflexivity at `u = 0`.
    QuotSound,
    /// `propext` — Extensionality inside `U₀`.
    PropExt,
    /// `Classical.choice.{u}` — the class-(P) ladder at `u = 0`.
    Choice,
}

impl Clause {
    /// How many `Π` binders the axiom's declared type has — the depth of the
    /// nest. Checked against the type by [`crate::mini::zoneb::peel`], never assumed.
    fn depth(self) -> usize {
        match self {
            // `α r a b h`. The codomain is the equation.
            Clause::QuotSound => 5,
            // `a b h`. The codomain is the equation.
            Clause::PropExt => 3,
            // `α h`. The codomain is `α` itself — the implicit binder, which is
            // why this is the one clause whose codomain is a bare `bvar`.
            Clause::Choice => 2,
        }
    }
}

/// The table. One comparison on the name the declaration walk already holds.
pub fn clause_for(n: &Name) -> Option<Clause> {
    let NameView::Str(pre, s) = n.view() else { return None };
    match pre.view() {
        NameView::Anon if &*s == "propext" => Some(Clause::PropExt),
        NameView::Str(root, q) if root.is_anon() && &*q == "Quot" && &*s == "sound" => {
            Some(Clause::QuotSound)
        }
        NameView::Str(root, q) if root.is_anon() && &*q == "Classical" && &*s == "choice" => {
            Some(Clause::Choice)
        }
        _ => None,
    }
}

const SHAPE: &str = "axiom: the declared type is not this clause's";

/// `(⟦c.{σ}⟧, ⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧)` for one axiom at one `σ`, or the reason it
/// could not be derived.
///
/// `ty_tm` is the type's interpretation the ledger already has in hand; the
/// conclusion is checked against it, so a nest that closed over some *other*
/// reading of the declared type cannot be handed back.
///
/// # It used to return the theorem alone, and require the term to be `•`
///
/// **The invariant did not weaken when the term came back; it moved and got
/// stronger.** The old pair of checks was "`t.tm` is `•`" and "the conclusion is
/// `• ∈ ⟦ty[σ]⟧`", and the ledger then stored `ip.point()` from its own side —
/// so the term in the store and the term the theorem was about agreed because
/// *both* were separately pinned to the same constant. The new single check is
/// "the conclusion is `tm ∈ ⟦ty[σ]⟧`" for the nest's own `tm`, **and the ledger
/// stores that same `tm`**. That implies the old conjunction whenever `tm` is
/// `•`, and it is the property the store actually needs: a membership and a
/// denotation that are about the same thing.
///
/// The point requirement had to go because it was never about soundness — it
/// was the "only a proof-valued axiom can be inhabited here" restriction wearing
/// a check. [`Clause::Choice`] at `u ≥ 1` is the first axiom whose codomain is
/// not a `Prop`: `⟦Classical.choice α h⟧` is `ε(⟦α⟧)` (§6.2), and there is
/// nothing wrong with that except that this function used to forbid it.
pub fn inhabit(
    c: &mut Checker<'_, '_>,
    cl: Clause,
    name: &Name,
    inst: &[u32],
    ty_tm: &kernel::Term,
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(*name, w);
    let miss = || Gap::NoInterpretation(*name, inst.to_vec());
    // The declared type, from the environment rather than from the ledger's
    // substituted copy: this module states its depth against what the *export*
    // says, which is the half of "the name is not the evidence" that is cheap.
    let ci = c.environment().get(name).ok_or_else(miss)?;
    if !matches!(ci, ConstantInfo::Opaque { .. }) {
        return Err(miss())
    }
    let (lparams, ty) = (ci.lparams().to_vec(), *ci.ty());
    if lparams.len() != inst.len() {
        return Err(miss())
    }
    let lean_ty = ground::subst_ground(&ty, &lparams, inst);
    let depth = cl.depth();
    let cod = crate::mini::zoneb::peel(&lean_ty, depth).ok_or_else(|| bad(SHAPE))?;
    let sigma = inst.to_vec();
    let nm = *name;
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        Ok(nest_bottom(c, cl, &nm, &sigma, &lean_ty, &cod))
    };
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    // **The bottom's own reason comes first.** This read used to sit *after* the
    // `tm == point` test, and that was only harmless while every clause here
    // produced a term on both paths. It does not survive a clause that declines
    // at some `σ` and not others: [`Clause::Choice`] at `u ≥ 1` hands back a
    // `Gap` and no term, `lam_evidence`'s value branch propagates the `None`
    // upward, and the point test then fired first and relabelled a perfectly
    // well-understood decline as "the nest does not interpret to the point" —
    // turning a counted axis into a shape complaint about the clause's own
    // deliberate refusal.
    //
    // Reordering weakens nothing. A `Gap` was going to be an `Err` either way;
    // what changes is only *which* reason is reported, and the sub-result's own
    // is the right one (`crate::mini::ledger` §0.4). Both checks below still run in
    // full on every path that produces a theorem.
    let thm = match t.ev {
        Ev::Proved(th) => th,
        Ev::Gap(g) => return Err(g),
    };
    // **The nest must interpret, and its membership must be about the term it
    // interpreted to, in `⟦ty[σ]⟧`.** One check where there were two, and it is
    // the conjunction of them plus the thing they were standing in for: the
    // ledger stores `tm` and the theorem beside it, so a membership about some
    // *other* term is a store entry whose denotation and whose typing are about
    // different objects — which is the failure the old point check bought by
    // accident, by pinning both sides to one constant.
    let tm = t.tm.ok_or_else(|| bad("axiom: the nest does not interpret"))?;
    if *thm.concl() != Formula::mem(tm.clone(), ty_tm.clone()) {
        return Err(bad("axiom: the nest is not about its own declared type"))
    }
    Ok((tm, thm))
}

/// The bottom of one axiom's nest — the denoting term and its membership in the
/// declared codomain's interpretation.
///
/// `lean_ty` is the whole declared type at σ, not only the codomain: a clause
/// whose *premise* carries the information — [`Clause::PropExt`]'s does — reads
/// it off the binder the export declared and not off a name this module chose.
fn nest_bottom(
    c: &mut Checker<'_, '_>,
    cl: Clause,
    name: &Name,
    inst: &[u32],
    lean_ty: &E,
    cod: &E,
) -> Typing {
    match cl {
        // `Eq Prop a b` from `a ↔ b`. The equation between the two `Prop`s is
        // [`propext_eq`]; everything after it is `Quot.sound`'s `u ≥ 1` path,
        // at `Eq.{1}` because the equation is between two *propositions* and
        // `Prop : Sort 1`. The level is not read off the axiom — `propext` has
        // no level parameter — but it is *checked*, because `eq_bottom`
        // decomposes the codomain and compares against the stored `⟦Eq.{1}⟧`.
        Clause::PropExt => match propext_eq(c, lean_ty) {
            Some(t) => crate::mini::direct::eq_bottom(c, cod, vec![1], Some(t)),
            None => Typing {
                ty: *cod,
                tm: None,
                ev: Ev::missing(Gap::IndSpec(Name::simple("propext"), PROPEXT)),
            },
        },
        // `Eq (Quot α r) (Quot.mk α r a) (Quot.mk α r b)` at `u = 0`. Both
        // sides are proofs, so both interpret to `•` by §6.2's application
        // clause, and the obligation is one instance of `Direct::eq_refl`
        // composed with a `beta_spine` down `⟦Eq.{0}⟧`'s own stored nest.
        //
        // That is exactly [`crate::mini::direct::ctor_bottom`]'s derivation at a
        // codomain that is not a constructor's, and it is reused rather than
        // rewritten — see [`crate::mini::direct::eq_refl_bottom`]. In particular the
        // check that the equation's two sides are the *same* term is that
        // function's, not a weaker one written here.
        Clause::QuotSound => {
            let u = inst.first().copied().unwrap_or(0);
            let eq = if u == 0 { None } else { Some(sound_eq(c, u)) };
            match eq {
                // `u = 0`: reflexivity, and `⟦Eq.{0}⟧` is the nest to β down.
                None => crate::mini::direct::eq_bottom(c, cod, vec![0], None),
                Some(Some(t)) => crate::mini::direct::eq_bottom(c, cod, vec![u], Some(t)),
                Some(None) => Typing {
                    ty: *cod,
                    tm: None,
                    ev: Ev::missing(Gap::Quotient(u, crate::mini::quot::Prim::Mk)),
                },
            }
        }
        // `α` itself, from `Nonempty α`. **Only `u = 0` is here**; see the
        // module header for why the two levels are different derivations and
        // not one with a parameter.
        //
        // At `u = 0` the codomain is a `Prop`, so §6.2 gives it the denotation
        // `•` like every other proof and the obligation is `⊢ • ∈ ⟦α⟧`. The
        // bottom is therefore built directly rather than through
        // [`crate::mini::direct::eq_bottom`]: there is no application to decompose,
        // the codomain being a bare `bvar`.
        //
        // At `u ≥ 1` the reason handed back is `Gap::Axiom` **and not a shape
        // complaint**, deliberately: the row this leaves in the ledger is the
        // one that was there before this clause existed, so a partial clause
        // moves the *count* and never the axis. `inhabit` reads this before it
        // tests `tm`, which is what makes that true.
        Clause::Choice => {
            let u = inst.first().copied().unwrap_or(0);
            let built = if u == 0 {
                choice_point(c, lean_ty, cod).map(|t| (c.interp().map(|ip| ip.point()), t))
            } else {
                choice_epsilon(c, u, lean_ty, cod).map(|(tm, t)| (Some(tm), t))
            };
            match built {
                Some((tm, t)) => Typing { ty: *cod, tm, ev: Ev::Proved(t) },
                None => Typing {
                    ty: *cod,
                    tm: None,
                    ev: Ev::missing(Gap::IndSpec(*name, CHOICE)),
                },
            }
        }
    }
}

const CHOICE: &str =
    "axiom: the premise is not a one-field class-(P) truncation of the codomain binder";

/// `⊢ • ∈ ⟦α⟧` for `Classical.choice.{0}` — the nest bottom at `u = 0`.
///
/// # Why `u = 0` needs no `ε` at all
///
/// `Nonempty α` is a **class-(P)** declaration with one field, of type `α`. Its
/// ladder ([`derived::inductive::family::TruncFields`]) states, at field 0,
///
/// ```text
/// ⊢ ∀α. ( • ∈ ‖Nonempty α‖ → (β₀(α) ⊆ 1 → • ∈ β₀(α)) )        [steps[0]]
/// ```
///
/// and `β₀(α)` is `⟦α⟧`. At `u = 0` the side condition `β₀(α) ⊆ 1` is
/// discharged from the `α` binder's own `⟦α⟧ ∈ U₀` by
/// [`crate::mini::rec_prop::subset_of_unit`] — so the whole obligation is the ladder
/// plus one subset fact, and Carneiro's `ε` never appears. It cannot: at
/// `u = 0` the choice being made is between the two elements of `U₀`, and
/// `Nonempty α` at a `Prop` already *is* the statement that `⟦α⟧` is the
/// non-empty one.
///
/// That is not an optimisation, it is why this half landed first: it exercises
/// no new machinery and closes half the pairs.
///
/// # Nothing here is keyed on the name `Nonempty`
///
/// The premise's head constant is read off the **declared type** and its
/// apparatus looked up at that key, exactly as [`propext_eq`] does. What makes
/// this derivation `Classical.choice`'s rather than some other declaration's is
/// checked at four places, none of them a name:
///
/// * the codomain must be `bvar 1` — **the axiom must return its own first
///   binder**. An axiom called `Classical.choice` that returns something else
///   gets no theorem, which is the analogue of
///   `an_axiom_named_quot_sound_that_is_not_reflexivity_is_declined`;
/// * the premise must have exactly one argument and it must be the outer
///   binder, `bvar 0`, so a premise about some other type is refused;
/// * the head constant must be in the **class-(P)** table — a truncation — with
///   one parameter and exactly one constructor field. `Iff` (class (S), two
///   fields) reaches this test and stops;
/// * the ladder's `P₀` is compared against `TruncFields::subsets[0]` and the
///   final membership against `⟦α⟧`, both rebuilt, so a ladder belonging to
///   another declaration cannot be applied here.
///
/// # Why the major premise needs three moves and not one
///
/// The `h` binder's typing is stated at the **stored** type former applied to
/// `⟦α⟧`; `TruncFields` states everything at `derived`'s own `‖·‖`. Getting
/// between them is [`Interp::beta_spine`] down the stored nest, then
/// `TruncTranslation::abbrev`, then — because `⟦h⟧` is a scope variable and not
/// the point — `TruncCarrier::only_point`. That is
/// [`crate::mini::proj_prop`]'s `trunc_typing` sequence, and it is followed here
/// step for step rather than re-derived, because the two are the same statement
/// reached from a nest binder instead of from a projection's subject.
fn choice_point(c: &mut Checker<'_, '_>, lean_ty: &E, cod: &E) -> Option<Thm> {
    let p = ChoiceParts::read(c, lean_ty, cod)?;
    let ip = c.interp()?;
    let point = ip.point();
    // `u = 0` is read off the *evidence* and not only off `σ`: the binder's own
    // membership must land in `U₀`, or `subset_of_unit` below is about a set
    // this derivation has no fact for.
    if *p.a_mem.concl() != Formula::mem(p.a.clone(), ip.sort(0)) {
        return None
    }

    // ── `P₀ : β₀ ⊆ 1`, off the α binder's `∈ U₀` ────────────────────────────
    let sym_in_u0 = ip.retarget_subject(&p.a_mem, &p.unfold)?;
    let sym = sym_in_u0.concl().as_mem()?.0.clone();
    let p0 = crate::mini::rec_prop::subset_of_unit(ip, &sym, &sym_in_u0)?;
    if *p0.concl() != crate::mini::rec_dep::subst_f(&p.fields.subsets[0], &p.psub) {
        return None
    }

    // ── the ladder, and back onto `⟦α⟧` ─────────────────────────────────────
    let hs = derived::inst_all(&p.fields.steps[0], std::slice::from_ref(&p.a))
        .and_then(|t| Thm::mp(&t, &p.major))
        .and_then(|t| Thm::mp(&t, &p0))?;
    let hyps: Vec<Formula> =
        p.fields.memberships.iter().map(|f| crate::mini::rec_dep::subst_f(f, &p.psub)).collect();
    let h_sym = derived::conj_proj(&hyps, 0).and_then(|pr| Thm::mp(&pr, &hs))?;
    let out = ip.retarget_set(&h_sym, &p.unfold)?;
    (*out.concl() == Formula::mem(point, p.a)).then_some(out)
}

/// `(app(εᵤ, ⟦α⟧), ⊢ app(εᵤ, ⟦α⟧) ∈ ⟦α⟧)` — the nest bottom at `u ≥ 1`.
///
/// # This is the only place in the system that spends choice
///
/// Everything up to the last two lines is [`choice_point`]'s reading of the
/// declared type and its class-(P) major premise, shared verbatim through
/// [`ChoiceParts`]. What differs is one step, and it is the step §6.2 is about.
///
/// At `u ≥ 1` the ladder is unusable: `P₀` is `β₀(α) ⊆ 1`, which for a **data**
/// field is simply false, so `TruncFields::steps[0]` has an antecedent nothing
/// can discharge. What survives the loss of `P₀` is the rung above it,
/// [`derived::inductive::family::TruncFields::elim_psi`]:
///
/// ```text
/// ⊢ ∀α. ( • ∈ ‖Nonempty α‖ → ∃y. y ∈ β₀(α) )
/// ```
///
/// *Some* element exists, with nothing said about which — which is exactly the
/// shape a choice function is for, and exactly the antecedent
/// [`derived::choice::Epsilon::chooses`] wants. The other antecedent, `⟦α⟧ ∈ Uᵤ`,
/// is the `α` binder's own typing, because [`Interp::sort`] is
/// `prelude.tower.u(u)` and nothing has to be moved onto it.
///
/// # Why the term comes back and `•` does not
///
/// `Classical.choice.{u}` at `u ≥ 1` is **not proof-valued**: its codomain is
/// `α : Sort u`. §6.2 gives it `⟦choice α h⟧ = ε(⟦α⟧)`, so the nest bottom
/// denotes a genuine set element and `crate::mini::kernel`'s `lam_evidence` takes its
/// *value* branch at both binders — the first time an axiom nest has done so.
/// [`inhabit`] hands the term back and `crate::mini::ledger` stores it; the invariant
/// that replaced "the term is `•`" is that the membership is about the term the
/// nest actually interpreted to.
fn choice_epsilon(
    c: &mut Checker<'_, '_>,
    u: u32,
    lean_ty: &E,
    cod: &E,
) -> Option<(Term, Thm)> {
    let p = ChoiceParts::read(c, lean_ty, cod)?;
    let ip = c.interp()?;

    // ── `⊢ ∃w. w ∈ ⟦α⟧`, from the carrier's inversion ───────────────────────
    //
    // `elim_psi` states it at the field *symbol* `β₀(⟦α⟧)`; `chooses_at` wants
    // it at `⟦α⟧`. `unfold` is the equation between them, and the move under
    // the existential is one Leibniz generalised and lifted by `exists_mono`
    // rather than a second `retarget_set`, because the membership is bound.
    let psi = derived::inst_all(p.fields.elim_psi.as_ref()?, std::slice::from_ref(&p.a))
        .and_then(|t| Thm::mp(&t, &p.major))?;
    let (b0, alpha) = p.unfold.concl().as_eq()?;
    if alpha != p.a {
        return None
    }
    let (w, s) = {
        let mut e = ip.env_mut();
        (e.fresh_var(), e.fresh_var())
    };
    let step = Thm::mp(
        &Thm::eq_leibniz(b0, alpha, s, Formula::mem(Term::var(w), Term::var(s))),
        &p.unfold,
    )?;
    // `gen_checked`, not `gen`: R6′ forbids the panicking wrapper in `mini/`,
    // and the side condition is real here rather than nominal — `step` is built
    // from `unfold`, and a `Γ` on it mentioning `w` would be a decline rather
    // than an abort. (It has none today; `field_abbrev` is a closed equation.)
    let ne = Thm::mp(&derived::exists_mono(w, &Thm::gen_checked(w, &step)?)?, &psi)?;

    // ── and `ε` picks one ───────────────────────────────────────────────────
    let (a, a_mem) = (p.a.clone(), p.a_mem.clone());
    c.interp()?.chooses_at(u, &a, &a_mem, &ne)
}

/// The half of the `Classical.choice` bottom that does not depend on `u`: the
/// declared type read and checked, the class-(P) apparatus, and
/// `⊢ • ∈ ‖ind(⟦α⟧)‖`.
///
/// Shared by [`choice_point`] and [`choice_epsilon`] rather than written twice.
/// That is not only economy: **every one of the four "the name is not the
/// evidence" checks lives here**, so the `u ≥ 1` arm cannot come to rest on a
/// weaker reading of the declared type than the `u = 0` arm does, and a test of
/// one arm's refusal is a test of both.
struct ChoiceParts {
    /// `⟦α⟧`, the outer binder.
    a: Term,
    /// `⊢ ⟦α⟧ ∈ ⟦Sort u⟧`.
    a_mem: Thm,
    /// `⊢ • ∈ ‖ind(⟦α⟧)‖`, the ladder's and `elim_psi`'s major premise.
    major: Thm,
    /// `⊢ β₀(⟦α⟧) = ⟦α⟧`.
    unfold: Thm,
    fields: std::rc::Rc<derived::inductive::family::TruncFields>,
    psub: Vec<(kernel::FreeVar, Term)>,
}

impl ChoiceParts {
    /// # Why the major premise needs three moves and not one
    ///
    /// The `h` binder's typing is stated at the **stored** type former applied
    /// to `⟦α⟧`; `TruncFields` states everything at `derived`'s own `‖·‖`.
    /// Getting between them is [`Interp::beta_spine`] down the stored nest, then
    /// `TruncTranslation::abbrev`, then — because `⟦h⟧` is a scope variable and
    /// not the point — `TruncCarrier::only_point`. That is
    /// [`crate::mini::proj_prop`]'s `trunc_typing` sequence, and it is followed here
    /// step for step rather than re-derived, because the two are the same
    /// statement reached from a nest binder instead of from a projection's
    /// subject.
    fn read(c: &mut Checker<'_, '_>, lean_ty: &E, cod: &E) -> Option<ChoiceParts> {
        // ── the codomain is the first binder, and the premise is about it ───
        if !matches!(cod.view(), Expr::BVar(1)) {
            return None
        }
        let mut cur = *lean_ty;
        let mut prem = None;
        for i in 0..Clause::Choice.depth() {
            let Expr::Forall { ty, body } = cur.view() else { return None };
            if i == 1 {
                prem = Some(ty);
            }
            cur = body;
        }
        let (head, args) = crate::mini::expr::get_app(&prem?);
        let Expr::Const(ind, us) = head.view() else { return None };
        if args.len() != 1 || !matches!(args[0].view(), Expr::BVar(0)) {
            return None
        }
        let empty = std::collections::HashMap::new();
        let inst: Vec<u32> =
            us.iter().map(|l| crate::mini::ground::eval(l, &empty)).collect::<Option<_>>()?;
        let ConstantInfo::Inductive { num_params, .. } = c.environment().get(&ind)? else {
            return None
        };
        if *num_params != 1 {
            return None
        }

        // ── the class-(P) apparatus for it ──────────────────────────────────
        let key = (ind, inst.clone());
        let tt = c.interp()?.ind_apparatus()?.truncs.get(&key).cloned()?;
        let spec = tt.ind.spec.ctors.first()?;
        if spec.args.len() != 1 || tt.ind.params.len() != 1 {
            return None
        }
        let former = c.stored_term(&ind, &inst)?;
        let fields = {
            let (mut kenv, app, _) = c.interp()?.ind_parts()?;
            app.trunc_fields(&mut kenv, &key, &tt)?
        };
        if fields.subsets.len() != 1 || fields.steps.len() != 1 {
            return None
        }

        // ── the nest's two binders ──────────────────────────────────────────
        let (xs, mems) = c.binders(Clause::Choice.depth())?;
        let (a, h) = (xs[0].clone(), xs[1].clone());
        let ip = c.interp()?;
        let point = ip.point();

        // ── `⊢ • ∈ ‖ind(⟦α⟧)‖` ──────────────────────────────────────────────
        let (carrier, spine_eq) = ip.beta_spine(&former, &xs[..1], &mems[..1])?;
        let ab = derived::inst_all(&tt.abbrev, &xs[..1])?;
        let (ab_l, ab_r) = ab.concl().as_eq()?;
        if ab_l != carrier {
            return None
        }
        let norm = crate::mini::rec_dep::eq_trans_pub(ip, &spine_eq, &ab)?;
        let in_t = ip.retarget_set(&mems[1], &norm)?;
        let major = if h == point {
            in_t
        } else {
            let only = derived::inst_all(&tt.tc.only_point, &xs[..1])
                .and_then(|t| derived::inst_all(&t, std::slice::from_ref(&h)))
                .and_then(|t| Thm::mp(&t, &in_t))?;
            let back = derived::eq_symm(&mut ip.env_mut(), &only)?;
            ip.retarget_subject(&in_t, &back)?
        };
        if *major.concl() != Formula::mem(point, ab_r) {
            return None
        }

        let unfold = derived::inst_all(tt.field_abbrev.first()?.first()?, &xs[..1])?;
        let psub: Vec<(kernel::FreeVar, Term)> =
            tt.ind.params.iter().copied().zip(xs[..1].iter().cloned()).collect();
        Some(ChoiceParts { a, a_mem: mems[0].clone(), major, unfold, fields, psub })
    }
}

const PROPEXT: &str = "axiom: the premise is not a two-field class-(S) biconditional over the two propositions";

/// `⊢ ⟦a⟧ = ⟦b⟧` for `propext` — the equation [`crate::mini::direct::eq_bottom`] then
/// puts `•` into.
///
/// # The obligation, and where each half comes from
///
/// The nest holds three binders and their scope typings:
///
/// ```text
/// ⊢ ⟦a⟧ ∈ U₀      ⊢ ⟦b⟧ ∈ U₀      ⊢ ⟦h⟧ ∈ ⟦a ↔ b⟧
/// ```
///
/// and [`derived::prop::prop_ext`] wants four facts about the two *sets*:
/// `⟦a⟧ ⊆ 1`, `⟦b⟧ ⊆ 1`, and the two implications between `• ∈ ⟦a⟧` and
/// `• ∈ ⟦b⟧`. The subset halves are [`crate::mini::rec_prop::subset_of_unit`] at the
/// two parameter typings. The implications are the biconditional, taken apart:
///
/// | step | what it is |
/// |---|---|
/// | `⟦h⟧ = •` | proof irrelevance, [`Interp::point_of_proof`] at the carrier's `∈ U₀` |
/// | `• ∈ ⟦a → b⟧`, `• ∈ ⟦b → a⟧` | [`crate::mini::rec_prop::inhabit`]'s ladder — `LePropFields` |
/// | `• ∈ ⟦a⟧ → • ∈ ⟦b⟧` | [`Interp::cond_app`] under an assumption, discharged |
///
/// # Nothing here is keyed on the name `Iff`
///
/// The premise's head constant and its levels are read off the **declared
/// type**, and the class-(S) apparatus is looked up at that key. What makes the
/// derivation `propext`'s rather than some other declaration's is checked and
/// not assumed, at three places:
///
/// * the premise must have exactly two arguments and they must be the nest's
///   own first two binders — so a premise over something else is refused;
/// * the class-(S) declaration must have exactly two fields, and each field's
///   interpretation must be a **`Prop`-valued `Π`** whose domain is one binder
///   and whose codomain is the other, in opposite orders;
/// * the two implications are compared against
///   [`derived::prop::prop_ext`]'s own antecedent before it is applied.
///
/// A structure with two fields that are *not* the two implications — `And`, for
/// instance, whose fields are the propositions themselves and not arrows — gets
/// as far as the second check and stops there.
///
/// **Two of those checks are measured redundant and are kept for the reason,
/// not for the rejection.** Mutating away the `bvar 1`/`bvar 0` comparison on
/// the premise's arguments, and mutating away [`arrow`]'s domain comparison,
/// each leave `mini/tests/designed.rs` and `derived/tests/prop.rs` **green**:
/// a premise `b ↔ a` is caught one step later by [`Interp::retarget_set`],
/// whose spine is built from the nest's binders and not from the premise's
/// arguments, and a field whose domain is the wrong binder is caught by
/// [`arrow`]'s own final comparison. Five other mutations — the two
/// implications swapped, the two subset facts swapped, `Eq.{1}` moved to
/// `Eq.{0}`, and two inside [`derived::prop::prop_ext`] — are red. The two
/// green ones stay because they name *which* premise was wrong at the place it
/// is read; nothing rests on them.
///
/// # Why the lemma is derived here and not cached
///
/// `propext` has no level parameters, so a file schedules **one** pair for it
/// and this runs at most once per export. [`derived::prop::prop_ext`] is a
/// dozen primitive steps over two fresh variables; a cache slot on `Interp` for
/// a once-per-file derivation would be a contended field for no measurable
/// gain.
fn propext_eq(c: &mut Checker<'_, '_>, lean_ty: &E) -> Option<Thm> {
    // ── the premise, off the declared type ──────────────────────────────────
    //
    // Three binders: `a`, `b`, and the biconditional. Only the third's domain
    // is read; the first two are reached through the nest's scope stack, where
    // their *interpretations* are.
    let mut cur = *lean_ty;
    let mut prem = None;
    for i in 0..Clause::PropExt.depth() {
        let Expr::Forall { ty, body } = cur.view() else { return None };
        if i == 2 {
            prem = Some(ty);
        }
        cur = body;
    }
    let (head, args) = crate::mini::expr::get_app(&prem?);
    let Expr::Const(ind, us) = head.view() else { return None };
    if args.len() != 2 {
        return None
    }
    // The two arguments must be the two binders, in order: `a ↔ b` and not
    // `b ↔ a`, and not some third proposition. `bvar 1` is `a` and `bvar 0` is
    // `b` under the two binders the premise sits inside.
    if !matches!(args[0].view(), Expr::BVar(1)) || !matches!(args[1].view(), Expr::BVar(0)) {
        return None
    }
    let empty = std::collections::HashMap::new();
    let inst: Vec<u32> = us.iter().map(|l| crate::mini::ground::eval(l, &empty)).collect::<Option<_>>()?;

    // ── the nest's own three binders ────────────────────────────────────────
    let (xs, mems) = c.binders(Clause::PropExt.depth())?;
    let (ps, param_mems) = (xs[..2].to_vec(), mems[..2].to_vec());
    let cs = crate::mini::class_s::of(c, &ind, &inst)?;
    if cs.np() != 2 || cs.spec.base.ctors.len() != 1 {
        return None
    }
    let former = c.stored_term(&ind, &inst)?;
    let fields = {
        let (mut kenv, app, _) = c.interp()?.ind_parts()?;
        app.prop_fields(&mut kenv, &(ind, inst.clone()), &cs)?
    };

    // ── `• ∈ A_φ(⟦a⟧,⟦b⟧)`, and the two field inhabitations off it ──────────
    let ip = c.interp()?;
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems)?;
    if carrier != ip.mk(cs.lc.phi, ps.clone()) {
        return None
    }
    let h_in_a = ip.retarget_set(&mems[2], &spine_eq)?;
    let a_in_u0 = derived::inst_all(&cs.in_u0, &ps)?;
    let h_pt = ip.point_of_proof(&a_in_u0, &h_in_a)?;
    let pt_eq_h = derived::eq_symm(&mut ip.env_mut(), &h_pt)?;
    let major = ip.retarget_subject(&h_in_a, &pt_eq_h)?;
    let hs = crate::mini::rec_prop::inhabit(ip, &cs, &fields, &ps, &param_mems, &major).ok()?;
    if hs.len() != 2 {
        return None
    }

    // ── the two implications, and the two subset facts ──────────────────────
    let fwd = arrow(ip, &hs[0], &ps[0], &ps[1])?;
    let bwd = arrow(ip, &hs[1], &ps[1], &ps[0])?;
    let u0 = ip.sort(0);
    let sub = |ip: &mut Interp, x: &Term, m: &Thm| -> Option<Thm> {
        (*m.concl() == Formula::mem(x.clone(), u0.clone()))
            .then(|| crate::mini::rec_prop::subset_of_unit(ip, x, m))
            .flatten()
    };
    let pa = sub(ip, &ps[0], &param_mems[0])?;
    let pb = sub(ip, &ps[1], &param_mems[1])?;

    // ── Extensionality inside `U₀` ──────────────────────────────────────────
    let sums = ip.prelude.tower.sums.clone();
    let lemma = derived::prop::prop_ext(&mut ip.env_mut(), &sums)?;
    let at = derived::inst_all(&lemma, &ps)?;
    // The right-nested conjunction `conj_of` built, folded in the same order.
    let hyp = [pa, pb, fwd, bwd]
        .into_iter()
        .rev()
        .reduce(|acc, t| derived::and_intro(&t, &acc))?;
    let out = Thm::mp(&at, &hyp)?;
    (*out.concl() == Formula::eq(ps[0].clone(), ps[1].clone())).then_some(out)
}

/// `⊢ • ∈ dom → • ∈ cod` from `⊢ • ∈ ⟦dom → cod⟧`.
///
/// The field's interpretation must be the **`Prop`** clause of §6.2's `Π` —
/// `chi(h⃗,⟦dom⟧)` — because that is the only clause whose inhabitation *is* an
/// implication; a field that came out a dependent product is a field of some
/// other declaration and is declined here.
///
/// The implication is obtained by assuming its antecedent and discharging it,
/// rather than by unfolding the conditional singleton a second time:
/// [`Interp::cond_app`] already carries the membership from `chi` through
/// `cond_elim` **and off the fibre symbol onto `⟦cod⟧`**, and reproducing that
/// second half here would be a second, unverified copy of it. `crate::mini::scope` is
/// the only module that names `Thm::assume`, which is why the assumption goes
/// through [`Scopes::assume`] and not through the kernel directly.
fn arrow(ip: &mut Interp, field: &Thm, dom: &Term, cod: &Term) -> Option<Thm> {
    let point = ip.point();
    let set = field.concl().as_mem()?.1.clone();
    let PiShape::Prop { site, dom: d } = ip.as_pi(&set)? else { return None };
    if d != *dom {
        return None
    }
    let mut scopes = crate::mini::scope::Scopes::new();
    let want = Formula::mem(point.clone(), dom.clone());
    let (tok, assumed) = scopes.assume(want.clone());
    // Discharged on **both** exits: `Scopes` enforces LIFO order, and leaving
    // an assumption open on the failing path would make the next `assume` in
    // this run assert.
    let applied = ip.cond_app(&site, &d, field, &point, &assumed);
    let out = scopes.discharge_assumption(tok, applied.as_ref().unwrap_or(&assumed));
    applied?;
    (*out.concl() == Formula::imp(want, Formula::mem(point, cod.clone()))).then_some(out)
}

/// `⊢ ⟦Quot.mk α r a⟧ = ⟦Quot.mk α r b⟧` at `u ≥ 1` — the equation
/// [`crate::mini::direct::eq_bottom`] then puts `•` into.
///
/// Everything it needs is the nest's own five binders and their scope typings,
/// read off at one vector index each; the rule is
/// [`crate::mini::quot_classes::sound_eq`].
fn sound_eq(c: &mut Checker<'_, '_>, u: u32) -> Option<Thm> {
    let (xs, mems) = c.binders(Clause::QuotSound.depth())?;
    let mk_former = c.stored_term(&Name::str(&Name::simple("Quot"), "mk"), &[u])?;
    let ip = c.interp()?;
    let q = ip.quotient()?;
    crate::mini::quot_classes::sound_eq(
        &q, ip, &mk_former, &xs[0], &mems[0], &xs[1], &mems[1], &xs[2], &mems[2], &xs[3],
        &mems[3], &mems[4],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mini::env::{Declaration, Environment};
    use crate::mini::expr::{app, bvar, forall, konst, sort, Level};
    use crate::mini::interp::Interp;

    fn nm(s: &str) -> Name { Name::simple(s) }

    /// The table is a table: one name, whole, and not a component of it.
    #[test]
    fn the_clause_table_is_keyed_on_the_whole_name() {
        assert_eq!(clause_for(&Name::str(&nm("Quot"), "sound")), Some(Clause::QuotSound));
        assert_eq!(clause_for(&nm("Quot")), None, "the type former is not the axiom");
        assert_eq!(clause_for(&Name::str(&nm("Quot"), "mk")), None);
        assert_eq!(
            clause_for(&Name::str(&Name::str(&nm("Foo"), "Quot"), "sound")),
            None,
            "Foo.Quot.sound is not Quot.sound"
        );
        assert_eq!(clause_for(&nm("sound")), None);

        // `propext` is a **root** name, so the anonymous prefix is the whole of
        // what distinguishes it — the shape `crate::mini::convert::is_standard_axiom`
        // matches on, and the one a `to_string()` comparison would wave a
        // dotted component through.
        assert_eq!(clause_for(&nm("propext")), Some(Clause::PropExt));
        assert_eq!(clause_for(&Name::str(&nm("My"), "propext")), None, "My.propext is not propext");
        assert_eq!(clause_for(&Name::num(&nm("propext"), 0)), None, "propext.0 is not propext");
        assert_eq!(clause_for(&Name::str(&nm("propext"), "aux")), None);

        // `Classical.choice` is two components and the *root* must be anonymous,
        // exactly as `Quot.sound`'s is — a `Foo.Classical.choice` is somebody
        // else's declaration and gets no clause.
        assert_eq!(clause_for(&Name::str(&nm("Classical"), "choice")), Some(Clause::Choice));
        assert_eq!(clause_for(&nm("Classical")), None, "the namespace is not the axiom");
        assert_eq!(clause_for(&nm("choice")), None);
        assert_eq!(
            clause_for(&Name::str(&Name::str(&nm("Foo"), "Classical"), "choice")),
            None,
            "Foo.Classical.choice is not Classical.choice"
        );
        assert_eq!(clause_for(&Name::str(&nm("Classical"), "choice_spec")), None);
    }

    /// The two clauses do not share a depth, and each one's is the binder count
    /// of the axiom it names. `crate::mini::zoneb::peel` checks it against the
    /// declared type, so a wrong number here is a decline and not a wrong
    /// theorem — but it is still the number that decides which binders
    /// `Checker::binders` hands back, and `propext`'s clause indexes into them.
    #[test]
    fn each_clauses_depth_is_its_axioms_binder_count() {
        assert_eq!(Clause::QuotSound.depth(), 5, "α r a b h");
        assert_eq!(Clause::PropExt.depth(), 3, "a b h");
        assert_eq!(Clause::Choice.depth(), 2, "α h");
    }

    /// An environment with `Eq` and one axiom called `Quot.sound` whose
    /// codomain is the caller's — so that the same clause can be run at the law
    /// it is about and at a law it is not.
    fn env_with_sound(cod: E) -> (Environment, Name) {
        let (e, refl) = (nm("Eq"), Name::str(&nm("Eq"), "refl"));
        let u = Level::param(nm("u"));
        let us: std::rc::Rc<[Level]> = vec![u].into();
        // `Eq : ∀ (α : Sort u) (a : α), α → Prop`
        let eq_ty =
            forall(sort(u), forall(bvar(0), forall(bvar(1), sort(Level::zero()))));
        // `Eq.refl : ∀ (α : Sort u) (a : α), Eq α a a`
        let refl_ty = forall(
            sort(u),
            forall(bvar(0), app(app(app(konst(e, us), bvar(1)), bvar(0)), bvar(0))),
        );
        let mut env = Environment::empty();
        crate::mini::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e,
                lparams: vec![nm("u")],
                num_params: 2,
                ty: eq_ty,
                ctors: vec![(refl, refl_ty)],
            },
        )
        .expect("Eq is accepted");
        // `Quot.sound : ∀ (α : Sort u) (r : α → α → Prop) (a b : α), r a b → cod`
        let name = Name::str(&nm("Quot"), "sound");
        let ty = forall(
            sort(u),
            forall(
                forall(bvar(0), forall(bvar(1), sort(Level::zero()))),
                forall(
                    bvar(1),
                    forall(bvar(2), forall(app(app(bvar(2), bvar(1)), bvar(0)), cod)),
                ),
            ),
        );
        crate::mini::kernel::add(
            &mut env,
            &Declaration::Axiom { name, lparams: vec![nm("u")], ty },
        )
        .expect("the axiom is accepted");
        (env, name)
    }

    /// `⟦ty[0]⟧`, and the clause's verdict about it.
    fn verdict(cod: E) -> Result<(), Gap> {
        let (env, name) = env_with_sound(cod);
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let ci = c.environment().get(&name).expect("declared").clone();
        let lean_ty = ground::subst_ground(ci.ty(), ci.lparams(), &[0]);
        let want = c
            .infer_type(&lean_ty)
            .expect("the type infers")
            .tm
            .expect("the type interprets");
        inhabit(&mut c, Clause::QuotSound, &name, &[0], &want).map(|_| ())
    }

    /// **The law it is about.** At `u = 0` both sides of the equation are
    /// proofs, so both denote `•` and the obligation is reflexivity — with no
    /// `Quot` in sight, which is the point: this clause reads the *codomain*,
    /// and `Quot α r` at `u = 0` is `⟦α⟧`, so an equation between two proofs of
    /// `α` is the same obligation.
    #[test]
    fn the_law_it_is_about_is_certified() {
        // `Eq α a a` — the two sides are one term.
        let cod = app(app(app(konst(nm("Eq"), vec![Level::param(nm("u"))].into()), bvar(4)), bvar(2)), bvar(2));
        assert!(verdict(cod).is_ok(), "reflexivity at a proof-valued equation must derive");
    }

    /// **The name is not the evidence.** An axiom called `Quot.sound` whose
    /// codomain is an equation between two *different* binders is declined,
    /// because the membership this clause derives is about `eq_set(a,a)` and
    /// the codomain interprets to `eq_set(a,b)`.
    ///
    /// This is the test the module header's soundness claim rests on: an axiom
    /// is the one declaration whose typing cannot be checked against a value,
    /// so a clause that believed its own table would certify a false axiom.
    #[test]
    fn an_axiom_named_quot_sound_that_is_not_reflexivity_is_declined() {
        // `Eq α a b` — the sides are the two distinct element binders.
        let cod = app(app(app(konst(nm("Eq"), vec![Level::param(nm("u"))].into()), bvar(4)), bvar(2)), bvar(1));
        assert_eq!(
            verdict(cod),
            Err(Gap::IndSpec(nm("Eq"), "ctor is not about its own codomain")),
            "a false axiom must be declined with a reason, never given a typing"
        );
    }

    // ── Clause::Choice ──────────────────────────────────────────────────────

    /// An environment with a class-(P) `Nonempty` and an axiom called
    /// `Classical.choice` whose **codomain is the caller's** — so that the same
    /// clause can be run at the law it is about and at a law it is not.
    ///
    /// This mirrors [`env_with_sound`] and exists for the same reason: the
    /// negative direction cannot be reached through `mini/tests/designed.rs`,
    /// because a fixture declaring a second, wrong `Classical.choice` is
    /// declined by `crate::mini::convert::is_standard_axiom` at the frontend and
    /// would measure that decline instead of this one.
    fn env_with_choice(cod: E) -> (Environment, Name) {
        let u = Level::param(nm("u"));
        let us: std::rc::Rc<[Level]> = vec![u].into();
        let ne = nm("Nonempty");
        let mut env = Environment::empty();
        // `inductive Nonempty (α : Sort u) : Prop where | intro (val : α)`
        crate::mini::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: ne,
                lparams: vec![nm("u")],
                num_params: 1,
                ty: forall(sort(u), sort(Level::zero())),
                ctors: vec![(
                    Name::str(&ne, "intro"),
                    forall(sort(u), forall(bvar(0), app(konst(ne, us.clone()), bvar(1)))),
                )],
            },
        )
        .expect("Nonempty is accepted");
        // `axiom Classical.choice {α : Sort u} : Nonempty α → cod`
        let name = Name::str(&nm("Classical"), "choice");
        let ty = forall(sort(u), forall(app(konst(ne, us), bvar(0)), cod));
        crate::mini::kernel::add(&mut env, &Declaration::Axiom { name, lparams: vec![nm("u")], ty })
            .expect("the axiom is accepted");
        (env, name)
    }

    /// `⟦ty[0]⟧`, and the clause's verdict about it.
    fn choice_verdict(cod: E) -> Result<(), Gap> {
        let (env, name) = env_with_choice(cod);
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let ci = c.environment().get(&name).expect("declared").clone();
        let lean_ty = ground::subst_ground(ci.ty(), ci.lparams(), &[0]);
        let want = c
            .infer_type(&lean_ty)
            .expect("the type infers")
            .tm
            .expect("the type interprets");
        inhabit(&mut c, Clause::Choice, &name, &[0], &want).map(|_| ())
    }

    /// **The law it is about.** At `u = 0` the codomain is the binder `α`, a
    /// `Prop`, so the obligation is `⊢ • ∈ ⟦α⟧` and the class-(P) ladder
    /// discharges it. This is the positive control: without it the negative
    /// test below could pass because the clause never works at all.
    #[test]
    fn the_choice_law_at_sort_zero_is_certified() {
        // The codomain is `α` — `bvar 1` under the two binders.
        assert!(choice_verdict(bvar(1)).is_ok(), "Classical.choice at u = 0 must derive");
    }

    /// **The name is not the evidence.** An axiom called `Classical.choice`
    /// with the right premise, the right depth and the right level, whose
    /// codomain is `Nonempty α` rather than `α`, is declined — the clause
    /// derives a membership in `⟦α⟧` and the declared type asks for one in
    /// `⟦Nonempty α⟧`.
    ///
    /// The difference from the positive case above is **one `Expr`**, which is
    /// what makes this a test of the codomain check rather than of the clause.
    #[test]
    fn an_axiom_named_classical_choice_that_does_not_return_its_binder_is_declined() {
        let us: std::rc::Rc<[Level]> = vec![Level::param(nm("u"))].into();
        let cod = app(konst(nm("Nonempty"), us), bvar(1));
        assert_eq!(
            choice_verdict(cod),
            Err(Gap::IndSpec(Name::str(&nm("Classical"), "choice"), CHOICE)),
            "a false axiom must be declined with a reason, never given a typing"
        );
    }

    /// **The premise is read too.** An axiom of the right shape whose premise
    /// is not about the codomain binder — `Nonempty` at a *second*, unrelated
    /// binder — has no ladder that says anything about `⟦α⟧`, and is declined
    /// at the `args[0] == bvar 0` test rather than producing a theorem about
    /// the wrong parameter.
    #[test]
    fn a_premise_about_another_binder_is_declined() {
        // Three binders is a different depth, so instead keep depth 2 and make
        // the premise `Nonempty.{0} (Nonempty.{u} α)` — still one argument, and
        // still a class-(P) truncation, but of the wrong thing. The outer copy
        // is at level 0 because `Nonempty.{u} α : Prop`, and Lean's own kernel
        // rejects the declaration otherwise — which is worth saying, because a
        // fixture that does not typecheck tests nothing.
        let u = Level::param(nm("u"));
        let us: std::rc::Rc<[Level]> = vec![u].into();
        let ne = nm("Nonempty");
        let mut env = Environment::empty();
        crate::mini::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: ne,
                lparams: vec![nm("u")],
                num_params: 1,
                ty: forall(sort(u), sort(Level::zero())),
                ctors: vec![(
                    Name::str(&ne, "intro"),
                    forall(sort(u), forall(bvar(0), app(konst(ne, us.clone()), bvar(1)))),
                )],
            },
        )
        .expect("Nonempty is accepted");
        let name = Name::str(&nm("Classical"), "choice");
        let inner = app(konst(ne, us), bvar(0));
        let zero: std::rc::Rc<[Level]> = vec![Level::zero()].into();
        let ty = forall(sort(u), forall(app(konst(ne, zero), inner), bvar(1)));
        crate::mini::kernel::add(&mut env, &Declaration::Axiom { name, lparams: vec![nm("u")], ty })
            .expect("the axiom is accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let ci = c.environment().get(&name).expect("declared").clone();
        let lean_ty = ground::subst_ground(ci.ty(), ci.lparams(), &[0]);
        let want =
            c.infer_type(&lean_ty).expect("the type infers").tm.expect("the type interprets");
        assert_eq!(
            inhabit(&mut c, Clause::Choice, &name, &[0], &want).map(|_| ()),
            Err(Gap::IndSpec(name, CHOICE)),
            "the premise must be the truncation of the codomain binder itself"
        );
    }
}
