//! **`Quot`'s interpretation clause at `Sort 0`** — the identity reading
//! (`QUOT-MODEL.md` §2).
//!
//! # Interface
//!
//! ```text
//! quot::prim_for(name)          -> Option<Prim>
//! quot::build(checker, name, σ) -> Result<(), Gap>
//! ```
//!
//! [`build`] is called from [`crate::zoneb::ensure`] **first**, before anything
//! else in it, because none of the four primitives is a
//! `ConstantInfo::Inductive` and none has an `owner`: they are `add_quot`'s
//! opaque constants, so every other branch of `ensure` answers `no-interp` on
//! the name before reaching them. They are §6.2 *clauses* rather than
//! translations — [`crate::direct`]'s `Eq` is the shape, and the store, the
//! `lam_nest` and the `Gap` vocabulary are the same.
//!
//! # The clause, and why it is forced rather than chosen
//!
//! At ground `u = 0`:
//!
//! ```text
//! ⟦Quot α r⟧        := ⟦α⟧            (r is not consulted)
//! ⟦Quot.mk r a⟧     := •
//! ⟦Quot.ind β h⟧    := •
//! ⟦Quot.lift β f h⟧ := ⟦f⟧ at lvl(β) ≥ 1,  • at lvl(β) = 0
//! ```
//!
//! `⟦Quot α r⟧` and `⟦α⟧` are the **same term**, not merely provably equal
//! sets. The equivalence-class construction cannot be the clause here and its
//! failure is *refutable* rather than merely unproved: `⟦Sort 0⟧ = U₀ = {∅,{•}}`,
//! so a member of it is a subset of `1`, while at any inhabited proposition
//! `quot(1,R) = {1} ⊄ 1`. `QUOT-MODEL.md` §1.2 has the countermodel in the
//! code's own terms and §2.2 the three soundness invariants — formation, `mk`
//! and `Quot.ind` — that pin the value pointwise with no level restriction.
//!
//! # Only the formation clause is here, and that is most of the row
//!
//! `⟦Quot.{0}⟧` alone moves `typeEv` on **five of the six** `Quot` exports,
//! because at `u = 0` the *types* need nothing else. `Quot.mk α r a` has type
//! `Quot α r`, which is a `Prop`, so §6.2's **application** clause gives it `•`
//! and the constant `⟦Quot.mk.{0}⟧` is never consulted — `⟦Quot.sound⟧`'s type
//! comes out as `f60(⟦Eq.{0}⟧, ⟦Quot.{0}⟧, •, •, …)` with `mk` already
//! collapsed. So the `mk`, `ind` and `lift` clauses are needed **only** where
//! the bare constant is a declaration's *value*, which is one export each.
//!
//! That is worth stating because it is the opposite of how the row reads from
//! `QUOT-MODEL.md`'s obligation table, which lists T1–T8 as a set: T1 is not
//! the first of eight, it is the one that carries the types and the other seven
//! are one export apiece.
//!
//! # `u ≥ 1` is a different clause and a different ledger row
//!
//! It declines as [`Gap::Quotient`], which carries the level. Every
//! `Quot`-bearing declaration is scheduled at *both* `u = 0` and `u = 1`, so
//! the row is roughly seven pairs and seven and neither clause alone closes an
//! export; a reason without the level would report a half-closed row as
//! untouched.
//!
//! # Keyed by name, verified against the declared type
//!
//! [`prim_for`] is a table on the name `ensure` was asked about. A name is not
//! evidence and this module never treats it as one: the nest is built from the
//! constant's **own declared type**, its depth is checked against that type,
//! and its bottom's membership is checked against the declared codomain's
//! interpretation. A constant called `Quot` whose type is not `add_quot`'s
//! produces a bottom about the wrong set and is refused.

use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::kernel::{Checker, Typing, R};

/// Which of the four primitives a name is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    /// `Quot : ∀ (α : Sort u), (α → α → Prop) → Sort u`.
    Quot,
    /// `Quot.mk : ∀ α r (a : α), Quot α r`.
    Mk,
    /// `Quot.lift : ∀ α r (β : Sort v) (f : α → β) (h : …), Quot α r → β`.
    Lift,
    /// `Quot.ind : ∀ α r (β : Quot α r → Prop) (h : …), ∀ q, β q`.
    Ind,
}

impl Prim {
    /// How many `Π` binders the primitive's declared type has — the depth of
    /// the λ-nest its interpretation is. Checked against the type by
    /// [`crate::zoneb::peel`], not assumed from this table.
    fn depth(self) -> usize {
        match self {
            Prim::Quot => 2,
            Prim::Mk => 3,
            Prim::Ind => 5,
            Prim::Lift => 6,
        }
    }
}

/// The table. One comparison on the name, never a scan and never a shape match.
pub fn prim_for(n: &Name) -> Option<Prim> {
    let Name::Str(pre, s) = n else { return None };
    match &**pre {
        Name::Anon if &**s == "Quot" => Some(Prim::Quot),
        Name::Str(root, q) if **root == Name::Anon && &**q == "Quot" => match &**s {
            "mk" => Some(Prim::Mk),
            "lift" => Some(Prim::Lift),
            "ind" => Some(Prim::Ind),
            _ => None,
        },
        _ => None,
    }
}

const SHAPE: &str = "quotient: the primitive's declared type is not add_quot's";

/// Build and store one primitive at one `σ`.
///
/// **One primitive per call, not the family.** The other three clauses obtain
/// `⟦Quot α r⟧` by *inferring* their declared codomain, so `zoneb::ensure`
/// re-enters this module for `Quot` while one of them is being built — one
/// level deep and terminating. Building the family eagerly would replace that
/// dependency with an ordering, and the ordering would be the thing that had to
/// be right.
///
/// `inst` is the constant's **own** instantiation: `Quot`, `Quot.mk` and
/// `Quot.ind` take `[u]`, `Quot.lift` takes `[u, v]`. `u` is first in every
/// case — `add_quot`'s order — and the length is checked against the constant's
/// declared parameter list rather than against the table.
pub fn build(c: &mut Checker<'_, '_>, name: &Name, inst: &[u32]) -> Result<(), Gap> {
    let miss = || Gap::NoInterpretation(name.clone(), inst.to_vec());
    let bad = |w: &'static str| Gap::IndSpec(Name::simple("Quot"), w);
    let prim = prim_for(name).ok_or_else(miss)?;

    let (lparams, ty) = match c.environment().get(name) {
        Some(ConstantInfo::Opaque { lparams, ty }) => (lparams.clone(), ty.clone()),
        _ => return Err(miss()),
    };
    if lparams.len() != inst.len() {
        return Err(miss())
    }
    let u = *inst.first().ok_or_else(|| bad(SHAPE))?;
    if u != 0 {
        return Err(Gap::Quotient(u))
    }
    // **The other three decline by their own name**, not by a shared reason:
    // the row reports which of the four is owed rather than "quotients", and
    // each is one export.
    if prim != Prim::Quot {
        return Err(miss())
    }

    let lean_ty = ground::subst_ground(&ty, &lparams, inst);
    let depth = prim.depth();
    let cod = crate::zoneb::peel(&lean_ty, depth).ok_or_else(|| bad(SHAPE))?;
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(nest_bottom(c, prim, &cod)) };
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, name, inst, t)
}

/// The bottom of one primitive's nest — the denoting term and its membership in
/// the declared codomain's interpretation.
fn nest_bottom(c: &mut Checker<'_, '_>, prim: Prim, cod: &E) -> Typing {
    let ty = cod.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let Some((xs, mems)) = c.binders(prim.depth()) else { return gap(Gap::NoEndpoint) };

    match prim {
        // **`⟦Quot α r⟧ = ⟦α⟧`, and the bottom is the binder's own scope typing
        // returned unaltered.** No theorem is derived and no symbol is minted:
        // `lam_nest` put `⟦α⟧` and `⊢ ⟦α⟧ ∈ ⟦Sort 0⟧` in scope two levels up,
        // and `⟦Sort 0⟧` is exactly what the declared codomain `Sort u` denotes
        // at `u = 0`. `r` is never consulted — that *is* the clause, and
        // `QUOT-MODEL.md` §2.3's T1 is this line.
        //
        // The membership is nevertheless **checked** against the codomain's own
        // interpretation rather than taken on trust, which is what keeps the
        // name a key and not evidence.
        Prim::Quot => {
            let Ok(ct) = c.infer_type(cod) else { return gap(Gap::Classifier) };
            let Some(cod_tm) = ct.tm.clone() else { return gap(ct.ev.reason(Gap::NoEndpoint)) };
            if *mems[0].concl() != kernel::Formula::mem(xs[0].clone(), cod_tm) {
                return gap(Gap::IndSpec(Name::simple("Quot"), SHAPE))
            }
            Typing { ty, tm: Some(xs[0].clone()), ev: Ev::Proved(mems[0].clone()) }
        }
        _ => gap(Gap::NoInterpretation(Name::simple("Quot"), vec![])),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The name table is a table, and it is exact.**
    ///
    /// Four accepted and four refused. The failure mode a prefix test has is
    /// accepting `Quot.foo` — routing a declaration this clause knows nothing
    /// about into `build` — and `Foo.Quot.mk`, doing it for a namespaced
    /// look-alike. `Name::Anon` at the root is what rules both out, and it is
    /// asserted rather than assumed.
    #[test]
    fn the_primitive_table_is_exact() {
        let q = Name::simple("Quot");
        assert_eq!(prim_for(&q), Some(Prim::Quot));
        assert_eq!(prim_for(&Name::str(&q, "mk")), Some(Prim::Mk));
        assert_eq!(prim_for(&Name::str(&q, "lift")), Some(Prim::Lift));
        assert_eq!(prim_for(&Name::str(&q, "ind")), Some(Prim::Ind));
        assert_eq!(prim_for(&Name::str(&q, "sound")), None, "sound is an axiom, not a primitive");
        assert_eq!(prim_for(&Name::str(&q, "foo")), None);
        assert_eq!(prim_for(&Name::simple("Quotient")), None);
        let nested = Name::str(&Name::str(&Name::simple("Foo"), "Quot"), "mk");
        assert_eq!(prim_for(&nested), None, "a namespaced look-alike is not Lean's Quot.mk");
    }
}
