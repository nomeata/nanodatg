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
//! # The one clause
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

use kernel::{Formula, Thm};

use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap};
use crate::expr::{Name, E, NameView};
use crate::ground;
use crate::kernel::{Checker, Typing, R};

/// Which axiom this module can inhabit, if any.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// `Quot.sound.{u}` — reflexivity at `u = 0`.
    QuotSound,
}

impl Clause {
    /// How many `Π` binders the axiom's declared type has — the depth of the
    /// nest. Checked against the type by [`crate::zoneb::peel`], never assumed.
    fn depth(self) -> usize {
        match self {
            // `α r a b h`. The codomain is the equation.
            Clause::QuotSound => 5,
        }
    }
}

/// The table. One comparison on the name the declaration walk already holds.
pub fn clause_for(n: &Name) -> Option<Clause> {
    let NameView::Str(pre, s) = n.view() else { return None };
    match pre.view() {
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
    let mut bottom =
        move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(nest_bottom(c, cl, &sigma, &cod)) };
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
fn nest_bottom(c: &mut Checker<'_, '_>, cl: Clause, inst: &[u32], cod: &E) -> Typing {
    match cl {
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
