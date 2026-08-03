//! **A projection out of a class-(S) structure** — `⊢ ⟦proj[T,j] x⟧ ∈ ⟦βⱼ⟧`
//! (`SCOPING.md` §9, construction 1).
//!
//! # Interface
//!
//! ```text
//! proj_prop::typing(checker, T, j, x, βⱼ) -> Result<Thm, Gap>
//! ```
//!
//! Called from [`Checker::infer_type`](crate::kernel::Checker::infer_type)'s
//! `Expr::Proj` arm and nowhere else, after
//! [`Checker::infer_proj`](crate::kernel::Checker) has established that the
//! projection is legal and produced `βⱼ`, the projection's Lean type.
//!
//! # The obligation is inhabitation, and it is the same fact twice
//!
//! `T` is a proposition, so `proj[T,j] x` is a **proof**: §6.2's left column
//! gives it `•` without looking at the structure at all. What is owed is not a
//! term but a certificate — `⊢ • ∈ ⟦βⱼ⟧`, i.e. that the field type is
//! *inhabited* — and at a class-(S) declaration that is
//! [`derived::inductive::family::LePropFields`]:
//!
//! ```text
//! ⊢ ∀p⃗. ( • ∈ A_φ(p⃗) → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)) )
//!         Pⱼ := βⱼ(p⃗,•⃗<ⱼ) ⊆ 1        Hⱼ := • ∈ βⱼ(p⃗,•⃗<ⱼ)
//! ```
//!
//! built, tested and **already consumed**: [`crate::rec_prop::inhabit`] climbs
//! exactly this ladder for the class-(S) eliminator's minor premise, and each
//! rung it produces is `Γ ⊢ • ∈ ⟦βⱼ⟧` at the *interpretation's* own set. That
//! is this clause's conclusion on the nose. So construction 1 is **a second
//! call site**: no theorem, no store, and nothing new in `derived/`.
//!
//! The one thing this module does that the eliminator does not is acquire the
//! ladder's major premise `• ∈ A_φ(⟦p⃗⟧)` from a *term* rather than from a nest
//! binder — `infer_type` on the projected expression, then the carrier
//! equation, then proof irrelevance if the subject is not already `•`.
//!
//! # Where the `•` comes from, and where it does not
//!
//! Not from here, and not from the `Expr::Proj` arm, which returns `tm: None`
//! unconditionally with no `is_prop` test. `⟦proj[T,j] x⟧ = •` arrives from the
//! **λ clause's proof branch** one level up, whose left column needs neither
//! the domain nor the body. This module supplies the typing that the pairs were
//! actually waiting on, which is why `084`/`086`'s interpretation finding was
//! right and their pairs still waited: at a `proj` row the "type or value?"
//! question answers *differently for the two halves of one family*
//! (`SCOPING.md` §9).
//!
//! # What routes elsewhere, and it routes by the store
//!
//! The class is decided by whether `IndApparatus::props` holds the declaration,
//! not by a second classification here:
//!
//! * **class (P)** (`PropStructure`) has no `A_φ` and no `LeProp::elim`, so the
//!   premise would have to be `TruncCarrier::elim` and `derived/` owes the
//!   analogue — `SCOPING.md` §9's construction 2. It keeps `Gap::StructProj`.
//! * **class (T)** (`Prod`) projects a **value**, so `⟦proj x⟧` is absent and
//!   what is owed is a term-former — construction 3, half the row. It keeps
//!   `Gap::StructProj` too.
//!
//! Reading the class off the store rather than re-deriving it is the same
//! discipline `crate::rec_dep`'s two clauses follow, and it means a declaration
//! whose class-(S) translation declined cannot be silently spoken for here.
//!
//! # Nothing here searches
//!
//! Every input is read: the parameters off the structure's own type, the
//! carrier equation off `beta_spine` down the stored type former's nest, and
//! the conclusion compared against `⟦βⱼ⟧` **inferred** — a rung that landed in
//! some other set is a decline and never a typing about the wrong field.

use kernel::{Formula, Term, Thm};

use crate::env::ConstantInfo;
use crate::ev::Gap;
use crate::expr::{Expr, Name, E};
use crate::ground;
use crate::kernel::Checker;

/// `Γ ⊢ • ∈ ⟦βⱼ⟧` for `proj[ind, idx] s`, or the reason it does not route here.
///
/// `field_ty` is the projection's own Lean type as `infer_proj` computed it —
/// `βⱼ` with each earlier projection substituted, which interprets to `•` in
/// every position the rung's `•⃗<ⱼ` occupies, and that is why the two sets meet.
pub(crate) fn typing(
    c: &mut Checker<'_, '_>,
    ind: &Name,
    idx: u32,
    s: &E,
    field_ty: &E,
) -> Result<Thm, Gap> {
    let miss = || Gap::StructProj(ind.clone());

    // ── the structure's own type: which declaration, at which levels ────────
    let te = c.infer_type(s).map_err(|_| Gap::Classifier)?;
    let sty = c.whnf(&te.ty).map_err(|_| Gap::Classifier)?;
    let (head, args) = crate::expr::get_app(&sty);
    let Expr::Const(name, us) = &*head else { return Err(miss()) };
    if name != ind {
        return Err(miss())
    }
    let empty = std::collections::HashMap::new();
    let inst: Vec<u32> =
        us.iter().map(|l| ground::eval(l, &empty)).collect::<Option<_>>().ok_or(Gap::SymbolicLevel)?;
    let Some(ConstantInfo::Inductive { num_params, .. }) = c.environment().get(ind) else {
        return Err(miss())
    };
    let np = *num_params as usize;
    if args.len() < np {
        return Err(miss())
    }

    // ── the class, read off the store ───────────────────────────────────────
    let key = (ind.clone(), inst.clone());
    let cs = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.props.get(&key).cloned().ok_or_else(miss)?
    };
    let spec = cs.spec.base.ctors.first().ok_or_else(miss)?;
    let j = idx as usize;
    if j >= spec.args.len() || cs.params.len() != np {
        return Err(miss())
    }

    // ── the parameters, and the type former's spine ─────────────────────────
    let mut ps = Vec::with_capacity(np);
    let mut param_mems = Vec::with_capacity(np);
    for a in &args[..np] {
        let t = c.infer_type(a).map_err(|_| Gap::Classifier)?;
        ps.push(t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
        param_mems.push(t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
    }
    let former = c.stored_term(ind, &inst).ok_or_else(miss)?;
    let subject = te.tm.clone().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let s_mem = te.ev.thm().cloned().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;

    // ── `⊢ • ∈ A_φ(⟦p⃗⟧)`, the ladder's major premise ────────────────────────
    //
    // The eliminator gets this from a nest binder; here it comes from a term,
    // and the two steps between are the carrier equation and — when the
    // projected expression does not already denote `•` — proof irrelevance,
    // which is sound because `A_φ ⊆ 1` whatever ψ is.
    let fields = {
        let (kenv, app, _) = c.interp().and_then(|ip| ip.ind_parts()).ok_or(Gap::IndApparatus)?;
        app.prop_fields(kenv, &key, &cs).ok_or_else(miss)?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let point = ip.point();
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(miss)?;
    if carrier != ip.mk(cs.lc.phi, ps.clone()) {
        return Err(miss())
    }
    let in_a = ip.retarget_set(&s_mem, &spine_eq).ok_or_else(miss)?;
    let major = if subject == point {
        in_a
    } else {
        let a_in_u0 = derived::inst_all(&cs.in_u0, &ps).ok_or_else(miss)?;
        let pt = ip.point_of_proof(&a_in_u0, &in_a).ok_or_else(miss)?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(miss)?;
        ip.retarget_subject(&in_a, &back).ok_or_else(miss)?
    };

    // ── the ladder, and the rung this projection is ─────────────────────────
    let hs = crate::rec_prop::inhabit(ip, &cs, &fields, &ps, &param_mems, &major)
        .map_err(|_| miss())?;
    let h = hs.get(j).cloned().ok_or_else(miss)?;

    // **The conclusion is checked against `⟦βⱼ⟧` inferred**, for the reason
    // `Checker::nest_iota` checks its endpoint: a rung that landed in some
    // other set would be a true theorem filed as this projection's typing. The
    // two meet because every earlier projection in `field_ty` interprets to `•`
    // — this clause, one index down — which is the rung's own `•⃗<ⱼ`.
    let want = c.infer_type(field_ty).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    if *h.concl() != Formula::mem(ip.point(), want) {
        return Err(miss())
    }
    Ok(h)
}

/// `⟦proj[T,j] x⟧` when the projection is a proof — `•`, and nothing else is
/// looked at.
pub(crate) fn point_of(c: &mut Checker<'_, '_>) -> Option<Term> {
    c.interp().map(|ip| ip.point())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, lam, sort, Level};
    use crate::interp::Interp;
    use crate::kernel::add;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no() -> Rc<[Level]> { Vec::<Level>::new().into() }
    fn prop() -> E { sort(Level::Zero) }

    /// ```text
    /// inductive P2 (a : Prop) (b : Prop) : Prop | mk : a → b → P2 a b
    /// ```
    ///
    /// Class (S) — the resultant sort is `Prop` and the eliminator is large —
    /// with **two** fields, which is what makes the ladder a ladder: `H₁` needs
    /// `P₀` and `H₀` before it, and a clause that answered every index with
    /// rung zero would pass at one field and fail here.
    fn env() -> Environment {
        let p2 = nm("P2");
        let spine = |x: u32, y: u32| app(app(konst(p2.clone(), no()), bvar(x)), bvar(y));
        let mut env = Environment::empty();
        add(
            &mut env,
            &Declaration::Inductive {
                name: p2.clone(),
                lparams: vec![],
                num_params: 2,
                ty: forall(prop(), forall(prop(), prop())),
                ctors: vec![(
                    Name::str(&p2, "mk"),
                    forall(
                        prop(),
                        forall(prop(), forall(bvar(1), forall(bvar(1), spine(3, 2)))),
                    ),
                )],
            },
        )
        .expect("P2 is accepted");
        env
    }

    /// `fun (a b : Prop) (h : P2 a b) => h.idx`, and its declared type.
    fn projector(idx: u32) -> (E, E) {
        let p2 = nm("P2");
        let structure = app(app(konst(p2.clone(), no()), bvar(1)), bvar(0));
        // The codomain is `a` at index 0 and `b` at index 1 — three binders in,
        // so `#2` and `#1`.
        let cod = bvar(2 - idx);
        let ty = forall(prop(), forall(prop(), forall(structure.clone(), cod)));
        let body = Rc::new(crate::expr::Expr::Proj { ind: p2, idx, s: bvar(0) });
        (ty, lam(prop(), lam(prop(), lam(structure, body))))
    }

    /// **A projection out of a class-(S) structure carries a typing, at each
    /// field.**
    ///
    /// The λ is a *proof* — its codomain is a `Prop`, so `imax` makes the whole
    /// `Π` one — and §6.2's left column gives it `•` without looking at the
    /// body at all. That is why this is the right assertion and why the pairs
    /// waited: the **term** was never missing, and `⊢ • ∈ ⟦Π…⟧` at a
    /// `Prop`-valued `Π` needs the codomain inhabited pointwise, which is the
    /// projection's own typing and nothing else.
    ///
    /// Both indices, because they are two different rungs of one ladder: `H₁`
    /// is derived *through* `P₀` and `H₀`, so a clause that stopped at the
    /// first field would pass at `idx = 0` and fail here. And the two land in
    /// **different** sets (`⟦a⟧` and `⟦b⟧`), so returning the wrong rung is a
    /// decline rather than a silent pass — the internal check against `⟦βⱼ⟧`
    /// inferred is what turns it into one.
    #[test]
    fn a_class_s_projection_is_typed_at_every_field() {
        let env = env();
        for idx in [0u32, 1] {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let (ty, val) = projector(idx);
            let t = c.infer_type(&val).unwrap_or_else(|e| panic!("idx {idx}: infer: {e}"));
            let thm = t
                .ev
                .thm()
                .unwrap_or_else(|| panic!("idx {idx}: the projection has no typing: {:?}", t.ev))
                .clone();
            assert_eq!(*t.ty, *ty, "idx {idx}: infer_proj chose the wrong field type");
            let point = c.interp().expect("threaded").point();
            assert_eq!(t.tm, Some(point.clone()), "idx {idx}: a proof denotes •");
            let want = c
                .infer_type(&ty)
                .unwrap_or_else(|e| panic!("idx {idx}: infer ⟦ty⟧: {e}"))
                .tm
                .unwrap_or_else(|| panic!("idx {idx}: ⟦ty⟧ is absent"));
            assert_eq!(
                *thm.concl(),
                Formula::mem(point, want),
                "idx {idx}: the typing is about the wrong set"
            );
            assert!(thm.hyps().is_empty(), "idx {idx}: no binder is open, so Γ must be empty");
        }
    }

    /// **A structure that is not class (S) is declined, by name, and not
    /// spoken for.**
    ///
    /// The same declaration one level up — resultant `Type 0` rather than
    /// `Prop` — is a class-(T) carrier with `Prop` fields, so `⟦h.0⟧` is still
    /// `•` and the obligation is still inhabitation, but `A_φ` does not exist
    /// and `LePropFields` is not about it. That is `SCOPING.md` §9's row
    /// re-split (see `MINI-HANDOFF.md` §11), and `PProd`/`PSigma` are its
    /// corpus witnesses. Pinned so that a later route which *does* cover it
    /// flips this test rather than quietly widening the class-(S) one.
    #[test]
    fn a_class_t_structure_with_prop_fields_is_declined_not_spoken_for() {
        let p2 = nm("P2");
        let ty0 = sort(Level::Zero.succ());
        let spine = |x: u32, y: u32| app(app(konst(p2.clone(), no()), bvar(x)), bvar(y));
        let mut env = Environment::empty();
        add(
            &mut env,
            &Declaration::Inductive {
                name: p2.clone(),
                lparams: vec![],
                num_params: 2,
                // `Prop → Prop → Type 0`: the fields are propositions and the
                // structure is not.
                ty: forall(prop(), forall(prop(), ty0)),
                ctors: vec![(
                    Name::str(&p2, "mk"),
                    forall(
                        prop(),
                        forall(prop(), forall(bvar(1), forall(bvar(1), spine(3, 2)))),
                    ),
                )],
            },
        )
        .expect("the declaration is accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let (_, val) = projector(0);
        let t = c.infer_type(&val).expect("infer");
        assert_eq!(
            t.ev.gap(),
            Some(&Gap::StructProj(p2)),
            "a class-(T) structure must keep the projection row's own name"
        );
    }
}
