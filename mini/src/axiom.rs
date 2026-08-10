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
//! Called from [`crate::ledger::Ledger::run`], on a `Declaration::Axiom` whose
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
//! | 1 | [`crate::zoneb::ensure`] | an **inductive or `Quot` declaration** being reached, at each scheduled σ |
//! | 2 | [`crate::direct::build`] | point 1, on a declaration `direct::clause_for` names |
//! | 3 | **here** | a declaration reaching its own typing obligation |
//!
//! *(Point 1's trigger used to read "a **constant occurrence** that misses the
//! store", and it was rewritten when `crate::ledger::fill_declaration` started
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
//! path through [`crate::direct::eq_bottom`] — an equation between two terms
//! that are not syntactically the same — and the only new thing is the equation
//! itself, [`propext_eq`].
//!
//! # `Classical.choice` — why there is no clause, and what would be needed
//!
//! ```text
//! Classical.choice.{u} : ∀ {α : Sort u}, Nonempty α → α
//! ```
//!
//! **Its codomain is not a `Prop`**, and the "what a clause here must produce"
//! section above is not a stylistic preference: `inhabit` requires the nest to
//! interpret to `•`, and [`crate::ledger`] stores `ip.point()` as the term of
//! every axiom this module inhabits. `⟦Classical.choice α h⟧` is `ε(⟦α⟧)`
//! (§6.2), so both would have to change — `inhabit` to hand back a term, and
//! the ledger to store it.
//!
//! That is the smaller half. The larger one is that **`ε` is not a term of the
//! kernel's language and cannot be made one here.** [`kernel::Thm::ax_choice`]
//! is `∀X ∃f. IsChoiceFn(f,X)`, an existential; `kernel::thm::define` requires
//! `∃!` and a choice function is never unique, so no symbol can be introduced
//! for it. `derived/src/choice.rs` says exactly this and carries `f` as a **free
//! variable under the antecedent `IsChoiceFn(f,u)`** instead — which makes
//! every theorem about it hypothetical, and [`crate::ev::Sealed`] (the
//! checker's, shared) refuses a theorem with hypotheses.
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
//! So the missing thing is not a lemma. It is a decision about whether mini's
//! evidence may carry one distinguished, whole-run hypothesis
//! `IsChoiceFn(f, U_ω)` — discharged once at the top against
//! `derived::choice::choice_fn_existence`, which is Carneiro's "fix a choice
//! function `ε` on `U_ω`" verbatim — and that decision changes what a `Sealed`
//! means for `checker/` too. The alternative, a kernel rule turning `⊢ ∃x. φ`
//! into a fresh symbol with `⊢ φ(c)`, is conservative and small and was
//! **already declined**: `derived/src/choice.rs` records that "no
//! `define_choice` primitive was added to let it".
//! `mini/tests/fixtures/standard_axioms.lean` is the witness that keeps the
//! four pairs measurable until one of the two is taken.
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

use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap};
use crate::expr::{Expr, Name, NameView, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};

/// Which axiom this module can inhabit, if any.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// `Quot.sound.{u}` — reflexivity at `u = 0`.
    QuotSound,
    /// `propext` — Extensionality inside `U₀`.
    PropExt,
}

impl Clause {
    /// How many `Π` binders the axiom's declared type has — the depth of the
    /// nest. Checked against the type by [`crate::zoneb::peel`], never assumed.
    fn depth(self) -> usize {
        match self {
            // `α r a b h`. The codomain is the equation.
            Clause::QuotSound => 5,
            // `a b h`. The codomain is the equation.
            Clause::PropExt => 3,
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
        _ => None,
    }
}

const SHAPE: &str = "axiom: the declared type is not this clause's";

/// `⊢ • ∈ ⟦ty[σ]⟧` for one axiom at one `σ`, or the reason it could not be
/// derived.
///
/// `ty_tm` is the type's interpretation the ledger already has in hand; the
/// conclusion is checked against it, so a nest that closed over some *other*
/// reading of the declared type cannot be handed back.
pub fn inhabit(
    c: &mut Checker<'_, '_>,
    cl: Clause,
    name: &Name,
    inst: &[u32],
    ty_tm: &kernel::Term,
) -> Result<Thm, Gap> {
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
    let cod = crate::zoneb::peel(&lean_ty, depth).ok_or_else(|| bad(SHAPE))?;
    let sigma = inst.to_vec();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        Ok(nest_bottom(c, cl, &sigma, &lean_ty, &cod))
    };
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    let point = c.interp().ok_or(Gap::SymbolicLevel)?.point();
    // **The nest's `tm` must be `•` and its membership must be about `⟦ty[σ]⟧`.**
    // Both halves matter: a nest that interpreted to something other than the
    // point is not a proof, and a membership in some other set is a theorem
    // about a term the ledger is not going to store.
    if t.tm.as_ref() != Some(&point) {
        return Err(bad("axiom: the nest does not interpret to the point"))
    }
    let thm = match t.ev {
        Ev::Proved(th) => th,
        Ev::Gap(g) => return Err(g),
    };
    if *thm.concl() != Formula::mem(point, ty_tm.clone()) {
        return Err(bad("axiom: the nest is not about its own declared type"))
    }
    Ok(thm)
}

/// The bottom of one axiom's nest — the denoting term and its membership in the
/// declared codomain's interpretation.
///
/// `lean_ty` is the whole declared type at σ, not only the codomain: a clause
/// whose *premise* carries the information — [`Clause::PropExt`]'s does — reads
/// it off the binder the export declared and not off a name this module chose.
fn nest_bottom(c: &mut Checker<'_, '_>, cl: Clause, inst: &[u32], lean_ty: &E, cod: &E) -> Typing {
    match cl {
        // `Eq Prop a b` from `a ↔ b`. The equation between the two `Prop`s is
        // [`propext_eq`]; everything after it is `Quot.sound`'s `u ≥ 1` path,
        // at `Eq.{1}` because the equation is between two *propositions* and
        // `Prop : Sort 1`. The level is not read off the axiom — `propext` has
        // no level parameter — but it is *checked*, because `eq_bottom`
        // decomposes the codomain and compares against the stored `⟦Eq.{1}⟧`.
        Clause::PropExt => match propext_eq(c, lean_ty) {
            Some(t) => crate::direct::eq_bottom(c, cod, vec![1], Some(t)),
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
        // That is exactly [`crate::direct::ctor_bottom`]'s derivation at a
        // codomain that is not a constructor's, and it is reused rather than
        // rewritten — see [`crate::direct::eq_refl_bottom`]. In particular the
        // check that the equation's two sides are the *same* term is that
        // function's, not a weaker one written here.
        Clause::QuotSound => {
            let u = inst.first().copied().unwrap_or(0);
            let eq = if u == 0 { None } else { Some(sound_eq(c, u)) };
            match eq {
                // `u = 0`: reflexivity, and `⟦Eq.{0}⟧` is the nest to β down.
                None => crate::direct::eq_bottom(c, cod, vec![0], None),
                Some(Some(t)) => crate::direct::eq_bottom(c, cod, vec![u], Some(t)),
                Some(None) => Typing {
                    ty: *cod,
                    tm: None,
                    ev: Ev::missing(Gap::Quotient(u, crate::quot::Prim::Mk)),
                },
            }
        }
    }
}

const PROPEXT: &str = "axiom: the premise is not a two-field class-(S) biconditional over the two propositions";

/// `⊢ ⟦a⟧ = ⟦b⟧` for `propext` — the equation [`crate::direct::eq_bottom`] then
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
/// `• ∈ ⟦b⟧`. The subset halves are [`crate::rec_prop::subset_of_unit`] at the
/// two parameter typings. The implications are the biconditional, taken apart:
///
/// | step | what it is |
/// |---|---|
/// | `⟦h⟧ = •` | proof irrelevance, [`Interp::point_of_proof`] at the carrier's `∈ U₀` |
/// | `• ∈ ⟦a → b⟧`, `• ∈ ⟦b → a⟧` | [`crate::rec_prop::inhabit`]'s ladder — `LePropFields` |
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
    let (head, args) = crate::expr::get_app(&prem?);
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
    let inst: Vec<u32> = us.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<_>>()?;

    // ── the nest's own three binders ────────────────────────────────────────
    let (xs, mems) = c.binders(Clause::PropExt.depth())?;
    let (ps, param_mems) = (xs[..2].to_vec(), mems[..2].to_vec());
    let cs = crate::class_s::of(c, &ind, &inst)?;
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
    let hs = crate::rec_prop::inhabit(ip, &cs, &fields, &ps, &param_mems, &major).ok()?;
    if hs.len() != 2 {
        return None
    }

    // ── the two implications, and the two subset facts ──────────────────────
    let fwd = arrow(ip, &hs[0], &ps[0], &ps[1])?;
    let bwd = arrow(ip, &hs[1], &ps[1], &ps[0])?;
    let u0 = ip.sort(0);
    let sub = |ip: &mut Interp, x: &Term, m: &Thm| -> Option<Thm> {
        (*m.concl() == Formula::mem(x.clone(), u0.clone()))
            .then(|| crate::rec_prop::subset_of_unit(ip, x, m))
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
/// second half here would be a second, unverified copy of it. `crate::scope` is
/// the only module that names `Thm::assume`, which is why the assumption goes
/// through [`Scopes::assume`] and not through the kernel directly.
fn arrow(ip: &mut Interp, field: &Thm, dom: &Term, cod: &Term) -> Option<Thm> {
    let point = ip.point();
    let set = field.concl().as_mem()?.1.clone();
    let PiShape::Prop { site, dom: d } = ip.as_pi(&set)? else { return None };
    if d != *dom {
        return None
    }
    let mut scopes = crate::scope::Scopes::new();
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
/// [`crate::direct::eq_bottom`] then puts `•` into.
///
/// Everything it needs is the nest's own five binders and their scope typings,
/// read off at one vector index each; the rule is
/// [`crate::quot_classes::sound_eq`].
fn sound_eq(c: &mut Checker<'_, '_>, u: u32) -> Option<Thm> {
    let (xs, mems) = c.binders(Clause::QuotSound.depth())?;
    let mk_former = c.stored_term(&Name::str(&Name::simple("Quot"), "mk"), &[u])?;
    let ip = c.interp()?;
    let q = ip.quotient()?;
    crate::quot_classes::sound_eq(
        &q, ip, &mk_former, &xs[0], &mems[0], &xs[1], &mems[1], &xs[2], &mems[2], &xs[3],
        &mems[3], &mems[4],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;

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
        // what distinguishes it — the shape `crate::convert::is_standard_axiom`
        // matches on, and the one a `to_string()` comparison would wave a
        // dotted component through.
        assert_eq!(clause_for(&nm("propext")), Some(Clause::PropExt));
        assert_eq!(clause_for(&Name::str(&nm("My"), "propext")), None, "My.propext is not propext");
        assert_eq!(clause_for(&Name::num(&nm("propext"), 0)), None, "propext.0 is not propext");
        assert_eq!(clause_for(&Name::str(&nm("propext"), "aux")), None);
    }

    /// The two clauses do not share a depth, and each one's is the binder count
    /// of the axiom it names. `crate::zoneb::peel` checks it against the
    /// declared type, so a wrong number here is a decline and not a wrong
    /// theorem — but it is still the number that decides which binders
    /// `Checker::binders` hands back, and `propext`'s clause indexes into them.
    #[test]
    fn each_clauses_depth_is_its_axioms_binder_count() {
        assert_eq!(Clause::QuotSound.depth(), 5, "α r a b h");
        assert_eq!(Clause::PropExt.depth(), 3, "a b h");
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
        crate::kernel::add(
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
        crate::kernel::add(
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
}
