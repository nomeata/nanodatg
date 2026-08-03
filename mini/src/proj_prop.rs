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
    //
    // Two tables, mutually exclusive by `zoneb::ensure`'s own branch, and a
    // declaration in neither is class (T) and owes a *term* rather than a
    // certificate — `SCOPING.md` §9's rows 2 and 4.
    let key = (ind.clone(), inst.clone());
    let (cs, tt) = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        (app.props.get(&key).cloned(), app.truncs.get(&key).cloned())
    };
    if let Some(tt) = tt {
        return trunc_typing(c, ind, idx, s, field_ty, &key, np, &args[..np], &tt)
    }
    let cs = cs.ok_or_else(miss)?;
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

/// `Γ ⊢ • ∈ ⟦βⱼ⟧` at a **class-(P)** structure — `SCOPING.md` §9's construction
/// 2, over [`derived::inductive::family::TruncFields`].
///
/// The same statement as [`typing`]'s class-(S) half with the major premise
/// swapped: `• ∈ ‖ind(p⃗)‖` instead of `• ∈ A_φ(p⃗)`, because a truncated
/// carrier has no `A_φ` and the witness is recovered through the carrier's own
/// inversion rather than through ψ. Everything after the premise is the same
/// ladder.
///
/// # The `Pⱼ` come from `infer_proj`, not from a store, and that is deliberate
///
/// [`crate::rec_prop::inhabit`] reads `⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧` off
/// [`ClassS::field_sort`](crate::class_s::ClassS), which the boundary walk
/// retained for the class-(S) *eliminator*.
/// [`TruncTranslation`](crate::interp::TruncTranslation) has no such field —
/// the class-(P) walk kept `field_abbrev` and dropped the sorts, which is
/// §2's pattern at a sixth position and would be worth closing if a second
/// consumer wanted it.
///
/// This route does not need it closed, and the reason generalises: a **use
/// site** can ask [`Checker::infer_proj`](crate::kernel::Checker) for each
/// earlier field's Lean type and infer its sort directly, because those types
/// are expressions in scope here — where at a nest bottom they are not. So the
/// missing store costs this consumer nothing, and re-deriving is not re-minting:
/// `infer_type` introduces no symbol.
///
/// # `Pⱼ` is `βⱼ ⊆ 1` and that is **weaker** than "βⱼ is a `Prop`"
///
/// `086` projects index 2 and so needs `P₀ ∧ P₁ ∧ P₂`, and `PropStructure`'s
/// field 1 is `PUnit.{1}` — *data*. There is deliberately no
/// field-is-a-proposition guard here: it would refuse a projection the checker
/// accepts, and `infer_proj` already owns that boundary (`085`, `087`–`089` are
/// in `bad/tutorial/` for exactly it). What this route can discharge is
/// `⟦βⱼ⟧ ∈ ⟦Sort 0⟧ ⟹ βⱼ ⊆ 1`; a field at a higher sort declines **by name**
/// rather than being assumed away.
#[allow(clippy::too_many_arguments)]
fn trunc_typing(
    c: &mut Checker<'_, '_>,
    ind: &Name,
    idx: u32,
    s: &E,
    field_ty: &E,
    key: &(Name, Vec<u32>),
    np: usize,
    param_args: &[E],
    tt: &crate::interp::TruncTranslation,
) -> Result<Thm, Gap> {
    let miss = || Gap::StructProj(ind.clone());
    let j = idx as usize;
    let spec = tt.ind.spec.ctors.first().ok_or_else(miss)?;
    if j >= spec.args.len() || tt.ind.params.len() != np {
        return Err(miss())
    }

    // ── the parameters, and every field type up to and including this one ───
    let mut ps = Vec::with_capacity(np);
    let mut param_mems = Vec::with_capacity(np);
    for a in param_args {
        let t = c.infer_type(a).map_err(|_| Gap::Classifier)?;
        ps.push(t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
        param_mems.push(t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
    }
    let mut betas = Vec::with_capacity(j + 1);
    for q in 0..=idx {
        let e = if q == idx {
            field_ty.clone()
        } else {
            c.infer_proj_ty(ind, q, s).map_err(|_| Gap::Classifier)?
        };
        let t = c.infer_type(&e).map_err(|_| Gap::Classifier)?;
        let set = t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?;
        betas.push((set, field_in_u0(c, &e).ok_or_else(miss)?));
    }

    let te = c.infer_type(s).map_err(|_| Gap::Classifier)?;
    let subject = te.tm.clone().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let s_mem = te.ev.thm().cloned().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let former = c.stored_term(ind, &key.1).ok_or_else(miss)?;
    let fields = {
        let (kenv, app, _) = c.interp().and_then(|ip| ip.ind_parts()).ok_or(Gap::IndApparatus)?;
        app.trunc_fields(kenv, key, tt).ok_or_else(miss)?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let point = ip.point();
    if fields.subsets.len() != spec.args.len() || fields.steps.len() != spec.args.len() {
        return Err(miss())
    }

    // ── `⊢ • ∈ ‖ind(⟦p⃗⟧)‖`, the ladder's major premise ──────────────────────
    //
    // Two moves from what the checker holds: β down the stored type former's
    // nest onto mini's own name for the truncation, then that name's defining
    // axiom. Proof irrelevance is not needed and not used — `TruncCarrier`'s
    // `only_point` is what makes the subject `•`, and it is the *carrier's*
    // theorem rather than a fact about `U₀`.
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(miss)?;
    let ab = derived::inst_all(&tt.abbrev, &ps).ok_or_else(miss)?;
    let (ab_l, ab_r) = ab.concl().as_eq().ok_or_else(miss)?;
    if ab_l != carrier {
        return Err(miss())
    }
    let norm = crate::rec_dep::eq_trans_pub(ip, &spine_eq, &ab).ok_or_else(miss)?;
    let in_t = ip.retarget_set(&s_mem, &norm).ok_or_else(miss)?;
    let major = if subject == point {
        in_t
    } else {
        let only = derived::inst_all(&tt.tc.only_point, &ps)
            .and_then(|t| derived::inst_all(&t, std::slice::from_ref(&subject)))
            .and_then(|t| Thm::mp(&t, &in_t))
            .ok_or_else(miss)?;
        let back = derived::eq_symm(&mut ip.env, &only).ok_or_else(miss)?;
        ip.retarget_subject(&in_t, &back).ok_or_else(miss)?
    };
    if *major.concl() != Formula::mem(point.clone(), ab_r) {
        return Err(miss())
    }

    // ── the ladder, `P₀ … Pⱼ` then `steps[j]` ───────────────────────────────
    let psub: Vec<(kernel::FreeVar, Term)> =
        tt.ind.params.iter().copied().zip(ps.iter().cloned()).collect();
    let mut subs = Vec::with_capacity(j + 1);
    for (q, (_, mem)) in betas.iter().enumerate() {
        let unfold = tt
            .field_abbrev
            .first()
            .and_then(|r| r.get(q))
            .and_then(|t| {
                let mut a = ps.clone();
                a.extend(std::iter::repeat_n(point.clone(), q));
                derived::inst_all(t, &a)
            })
            .ok_or_else(miss)?;
        let sym_in_u0 = ip.retarget_subject(mem, &unfold).ok_or_else(miss)?;
        let sym = sym_in_u0.concl().as_mem().ok_or_else(miss)?.0.clone();
        let p_q = crate::rec_prop::subset_of_unit(ip, &sym, &sym_in_u0).ok_or_else(miss)?;
        if *p_q.concl() != crate::rec_dep::subst_f(&fields.subsets[q], &psub) {
            return Err(miss())
        }
        subs.push(p_q);
    }
    let all = derived::inst_all(&fields.steps[j], &ps)
        .and_then(|t| Thm::mp(&t, &major))
        .ok_or_else(miss)?;
    let conj = subs
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(miss)?;
    let hs_all = Thm::mp(&all, &conj).ok_or_else(miss)?;
    let hyps: Vec<Formula> = fields.memberships[..=j]
        .iter()
        .map(|f| crate::rec_dep::subst_f(f, &psub))
        .collect();
    let h_sym = derived::conj_proj(&hyps, j)
        .and_then(|pr| Thm::mp(&pr, &hs_all))
        .ok_or_else(miss)?;

    // …and back onto `⟦βⱼ⟧`, where the projection's own type is.
    let unfold = tt
        .field_abbrev
        .first()
        .and_then(|r| r.get(j))
        .and_then(|t| {
            let mut a = ps.clone();
            a.extend(std::iter::repeat_n(point.clone(), j));
            derived::inst_all(t, &a)
        })
        .ok_or_else(miss)?;
    let h = ip.retarget_set(&h_sym, &unfold).ok_or_else(miss)?;
    if *h.concl() != Formula::mem(point, betas[j].0.clone()) {
        return Err(miss())
    }
    Ok(h)
}

/// `⟦proj[T,j] x⟧` when the projection is a proof — `•`, and nothing else is
/// looked at.
pub(crate) fn point_of(c: &mut Checker<'_, '_>) -> Option<Term> {
    c.interp().map(|ip| ip.point())
}

/// `Γ ⊢ ⟦β⟧ ∈ ⟦Prop⟧` — what `Pⱼ = βⱼ ⊆ 1` is derived from, by **two** routes.
///
/// # The Lean sort is one route and it is not the only one
///
/// `⊆ 1` says every member of `βⱼ` is `•`. That is implied by `βⱼ ∈ ⟦Prop⟧`
/// and is **strictly weaker** than the *Lean* type `βⱼ` being a `Prop`, and
/// `PropStructure`'s field 1 is exactly the gap between them: it is
/// `PUnit.{1}`, whose Lean sort is `Type 0`, and whose **carrier** mini
/// translates as a conditional singleton that is in `U₀` outright
/// (`ClassS::in_u0`, `TruncCarrier::in_u0`).
///
/// *(This function exists because the first revision of this route checked only
/// the Lean sort and declined `086` by name, and the decline was recorded as a
/// finding — that `⟦PUnit.{1}⟧ ⊆ 1` "looks false because `1` is `{•}` and a
/// W-encoded unit's inhabitant is a pair". Wrong: a unit-like declaration never
/// reaches the W-carrier, it reaches `class_s`. One `--dump-only=PUnit` showed
/// `⊢ ⟦PUnit.{1}⟧ ∈ ⟦Sort 0⟧` sitting in the store. The reasoning was about the
/// wrong translation and the instrument settled it in one command.)*
///
/// So: the inferred sort when it is `⟦Prop⟧`, and otherwise the field type's
/// **own declaration's** carrier membership, moved back along `beta_spine` onto
/// the interpretation the field binder was opened at. A field type that is
/// neither is a decline, which is where a genuine data field lands.
fn field_in_u0(c: &mut Checker<'_, '_>, e: &E) -> Option<Thm> {
    let t = c.infer_type(e).ok()?;
    let mem = t.ev.thm()?.clone();
    let u0 = c.interp()?.sort(0);
    if mem.concl().as_mem()?.1 == u0 {
        return Some(mem)
    }
    let ty = c.whnf(e).ok()?;
    let (head, args) = crate::expr::get_app(&ty);
    let Expr::Const(name, us) = &*head else { return None };
    let empty = std::collections::HashMap::new();
    let inst: Vec<u32> = us.iter().map(|l| ground::eval(l, &empty)).collect::<Option<_>>()?;
    let ConstantInfo::Inductive { num_params, .. } = c.environment().get(name)? else {
        return None
    };
    let np = *num_params as usize;
    if args.len() < np {
        return None
    }
    let (mut ps, mut pm) = (Vec::with_capacity(np), Vec::with_capacity(np));
    for a in &args[..np] {
        let t = c.infer_type(a).ok()?;
        ps.push(t.tm.clone()?);
        pm.push(t.ev.thm()?.clone());
    }
    let former = c.stored_term(name, &inst)?;
    let key = (name.clone(), inst);
    let (cs, tt) = {
        let app = c.interp()?.ind_apparatus()?;
        (app.props.get(&key).cloned(), app.truncs.get(&key).cloned())
    };
    let ip = c.interp()?;
    let (_, spine_eq) = ip.beta_spine(&former, &ps, &pm)?;
    let carrier = match (cs, tt) {
        (Some(cs), _) => derived::inst_all(&cs.in_u0, &ps)?,
        (None, Some(tt)) => {
            let at = derived::inst_all(&tt.tc.in_u0, &ps)?;
            let ab = derived::inst_all(&tt.abbrev, &ps)?;
            ip.retarget_subject(&at, &ab)?
        }
        (None, None) => return None,
    };
    ip.retarget_subject(&carrier, &spine_eq)
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

    /// **A structure that is neither class (S) nor class (P) is declined, by
    /// name, and not spoken for.**
    ///
    /// The same declaration one level up — resultant `Type 0` rather than
    /// `Prop` — is a class-(T) carrier with `Prop` fields, so `⟦h.0⟧` is still
    /// `•` and the obligation is still inhabitation, but neither `A_φ` nor a
    /// truncation exists and neither ladder is about it. That is `SCOPING.md`
    /// §9's row re-split (see `MINI-HANDOFF.md` §11), and `PProd`/`PSigma` are
    /// its corpus witnesses. Pinned so that a later route which *does* cover it
    /// flips this test rather than quietly widening either existing one.
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
