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
//! From [`point_of`], which the `Expr::Proj` arm calls **exactly when this
//! module's `typing` succeeds** — so the `•` is licensed by
//! [`field_in_u0`]'s `⊢ ⟦βⱼ⟧ ∈ U₀` and not by an `is_prop` test on the Lean
//! sort, and those two are not the same condition: see `field_in_u0`'s own
//! header for the case that separates them, and `INTERP-AUDIT.md` L4 for what
//! the divergence can and cannot cost. This module supplies the typing that the
//! pairs were actually waiting on, which is why `084`/`086`'s finding was
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
    // The `?`-census: every decline below names its own line, not the
    // caller that turned it into an `Ev`. See [`crate::gap!`].
    macro_rules! miss {
        () => { crate::gap!(Gap::StructProj(ind.clone())) };
    }

    // ── the structure's own type: which declaration, at which levels ────────
    let te = c.infer_type(s).map_err(|_| Gap::Classifier)?;
    let sty = c.whnf(&te.ty).map_err(|_| Gap::Classifier)?;
    let (head, args) = crate::expr::get_app(&sty);
    let Expr::Const(name, us) = &*head else { return Err(miss!()) };
    if name != ind {
        return Err(miss!())
    }
    let empty = std::collections::HashMap::new();
    let inst: Vec<u32> =
        us.iter().map(|l| ground::eval(l, &empty)).collect::<Option<_>>().ok_or(Gap::SymbolicLevel)?;
    let Some(ConstantInfo::Inductive { num_params, .. }) = c.environment().get(ind) else {
        return Err(miss!())
    };
    let np = *num_params as usize;
    if args.len() < np {
        return Err(miss!())
    }

    // ── the class, read off the store ───────────────────────────────────────
    //
    // Two tables, mutually exclusive by `zoneb::ensure`'s own branch, and a
    // declaration in neither is class (T) and owes a *term* rather than a
    // certificate — `SCOPING.md` §9's rows 2 and 4.
    let key = (*ind, inst.clone());
    let (cs, tt, dt) = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        (
            app.props.get(&key).cloned(),
            app.truncs.get(&key).cloned(),
            app.decls.get(&key).cloned(),
        )
    };
    if let Some(tt) = tt {
        return trunc_typing(c, ind, idx, s, field_ty, &key, np, &args[..np], &tt)
    }
    let Some(cs) = cs else {
        let dt = dt.ok_or_else(|| miss!())?;
        return decl_typing(c, ind, idx, s, field_ty, &key, np, &args[..np], &dt)
    };
    let spec = cs.spec.base.ctors.first().ok_or_else(|| miss!())?;
    let j = idx as usize;
    if j >= spec.args.len() || cs.params.len() != np {
        return Err(miss!())
    }

    // ── the parameters, and the type former's spine ─────────────────────────
    let mut ps = Vec::with_capacity(np);
    let mut param_mems = Vec::with_capacity(np);
    for a in &args[..np] {
        let t = c.infer_type(a).map_err(|_| Gap::Classifier)?;
        ps.push(t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
        param_mems.push(t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
    }
    let former = c.stored_term(ind, &inst).ok_or_else(|| miss!())?;
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
        app.prop_fields(kenv, &key, &cs).ok_or_else(|| miss!())?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let point = ip.point();
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(|| miss!())?;
    if carrier != ip.mk(cs.lc.phi, ps.clone()) {
        return Err(miss!())
    }
    let in_a = ip.retarget_set(&s_mem, &spine_eq).ok_or_else(|| miss!())?;
    let major = if subject == point {
        in_a
    } else {
        let a_in_u0 = derived::inst_all(&cs.in_u0, &ps).ok_or_else(|| miss!())?;
        let pt = ip.point_of_proof(&a_in_u0, &in_a).ok_or_else(|| miss!())?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(|| miss!())?;
        ip.retarget_subject(&in_a, &back).ok_or_else(|| miss!())?
    };

    // ── the ladder, and the rung this projection is ─────────────────────────
    let hs = crate::rec_prop::inhabit(ip, &cs, &fields, &ps, &param_mems, &major)
        .map_err(|_| miss!())?;
    let h = hs.get(j).cloned().ok_or_else(|| miss!())?;

    // **The conclusion is checked against `⟦βⱼ⟧` inferred**, for the reason
    // `Checker::nest_iota` checks its endpoint: a rung that landed in some
    // other set would be a true theorem filed as this projection's typing. The
    // two meet because every earlier projection in `field_ty` interprets to `•`
    // — this clause, one index down — which is the rung's own `•⃗<ⱼ`.
    let want = c.infer_type(field_ty).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    if *h.concl() != Formula::mem(ip.point(), want) {
        return Err(miss!())
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
    // The `?`-census: every decline below names its own line, not the
    // caller that turned it into an `Ev`. See [`crate::gap!`].
    macro_rules! miss {
        () => { crate::gap!(Gap::StructProj(ind.clone())) };
    }
    let j = idx as usize;
    let spec = tt.ind.spec.ctors.first().ok_or_else(|| miss!())?;
    if j >= spec.args.len() || tt.ind.params.len() != np {
        return Err(miss!())
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
        betas.push((set, field_in_u0(c, &e).ok_or_else(|| miss!())?));
    }

    let te = c.infer_type(s).map_err(|_| Gap::Classifier)?;
    let subject = te.tm.clone().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let s_mem = te.ev.thm().cloned().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let former = c.stored_term(ind, &key.1).ok_or_else(|| miss!())?;
    let fields = {
        let (kenv, app, _) = c.interp().and_then(|ip| ip.ind_parts()).ok_or(Gap::IndApparatus)?;
        app.trunc_fields(kenv, key, tt).ok_or_else(|| miss!())?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let point = ip.point();
    if fields.subsets.len() != spec.args.len() || fields.steps.len() != spec.args.len() {
        return Err(miss!())
    }

    // ── `⊢ • ∈ ‖ind(⟦p⃗⟧)‖`, the ladder's major premise ──────────────────────
    //
    // Two moves from what the checker holds: β down the stored type former's
    // nest onto mini's own name for the truncation, then that name's defining
    // axiom. Proof irrelevance is not needed and not used — `TruncCarrier`'s
    // `only_point` is what makes the subject `•`, and it is the *carrier's*
    // theorem rather than a fact about `U₀`.
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(|| miss!())?;
    let ab = derived::inst_all(&tt.abbrev, &ps).ok_or_else(|| miss!())?;
    let (ab_l, ab_r) = ab.concl().as_eq().ok_or_else(|| miss!())?;
    if ab_l != carrier {
        return Err(miss!())
    }
    let norm = crate::rec_dep::eq_trans_pub(ip, &spine_eq, &ab).ok_or_else(|| miss!())?;
    let in_t = ip.retarget_set(&s_mem, &norm).ok_or_else(|| miss!())?;
    let major = if subject == point {
        in_t
    } else {
        let only = derived::inst_all(&tt.tc.only_point, &ps)
            .and_then(|t| derived::inst_all(&t, std::slice::from_ref(&subject)))
            .and_then(|t| Thm::mp(&t, &in_t))
            .ok_or_else(|| miss!())?;
        let back = derived::eq_symm(&mut ip.env, &only).ok_or_else(|| miss!())?;
        ip.retarget_subject(&in_t, &back).ok_or_else(|| miss!())?
    };
    if *major.concl() != Formula::mem(point.clone(), ab_r) {
        return Err(miss!())
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
            .ok_or_else(|| miss!())?;
        let sym_in_u0 = ip.retarget_subject(mem, &unfold).ok_or_else(|| miss!())?;
        let sym = sym_in_u0.concl().as_mem().ok_or_else(|| miss!())?.0.clone();
        let p_q = crate::rec_prop::subset_of_unit(ip, &sym, &sym_in_u0).ok_or_else(|| miss!())?;
        if *p_q.concl() != crate::rec_dep::subst_f(&fields.subsets[q], &psub) {
            return Err(miss!())
        }
        subs.push(p_q);
    }
    let all = derived::inst_all(&fields.steps[j], &ps)
        .and_then(|t| Thm::mp(&t, &major))
        .ok_or_else(|| miss!())?;
    let conj = subs
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| miss!())?;
    let hs_all = Thm::mp(&all, &conj).ok_or_else(|| miss!())?;
    let hyps: Vec<Formula> = fields.memberships[..=j]
        .iter()
        .map(|f| crate::rec_dep::subst_f(f, &psub))
        .collect();
    let h_sym = derived::conj_proj(&hyps, j)
        .and_then(|pr| Thm::mp(&pr, &hs_all))
        .ok_or_else(|| miss!())?;

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
        .ok_or_else(|| miss!())?;
    let h = ip.retarget_set(&h_sym, &unfold).ok_or_else(|| miss!())?;
    if *h.concl() != Formula::mem(point, betas[j].0.clone()) {
        return Err(miss!())
    }
    Ok(h)
}

/// `Γ ⊢ • ∈ ⟦βⱼ⟧` at a **class-(T)** structure whose field `j` is a `Prop` —
/// `MINI-HANDOFF.md` §11's row 2, over [`derived::inductive::DeclFields`].
///
/// The third and last spelling of one statement, and the shortest, because the
/// major premise is the weakest of the three:
///
/// ```text
/// (S)  • ∈ A_φ(p⃗)      (P)  • ∈ ‖ind(p⃗)‖      (T)  z ∈ ind(p⃗)
/// ```
///
/// # `z` is quantified, and that is what removes two steps
///
/// Both siblings state their premise **at the point**, because for them the
/// carrier's only possible inhabitant is the point — so both need a move onto
/// `•` first ([`Interp::point_of_proof`](crate::interp::Interp), or
/// `TruncCarrier::only_point`) before the ladder applies. Here the carrier
/// holds W-elements and the projected term is whatever the checker has, so
/// `DeclFields` quantifies `z` and the membership goes in as it comes out of
/// `beta_spine`. Nothing in the conclusion mentions `z`.
///
/// There is also no carrier abbreviation to compose: the class-(T) type
/// former's nest bottom **is** `ind(p⃗)` (`zoneb::former_at` builds it with
/// `Interp::mk` at [`Inductive::ty`](derived::inductive::Inductive)), where the
/// class-(P) one is mini's own name for the truncation and needs `tt.abbrev`.
///
/// # Everything after the premise is [`trunc_typing`]'s ladder verbatim
///
/// `Pⱼ = βⱼ ⊆ 1` from the field's `U₀` membership by [`field_in_u0`], one
/// `field_abbrev` unfold per rung to move between mini's `βⱼ` symbol and the
/// interpretation's `⟦βⱼ⟧`, `steps[j]` rather than `inhabited` — a projection at
/// index `j` is owed `P₀ … Pⱼ` and holds no reason for the rest — and the
/// conclusion checked against `⟦βⱼ⟧` **inferred**.
///
/// # What this declines, and it is where the σ split lives
///
/// `PProd.{1,1}` and `PSigma.{1,1}` reach here and decline, at
/// [`field_in_u0`]: at `u = v = 1` the field is *data*, `⟦α⟧ ∈ U₁` gives no
/// `⟦α⟧ ⊆ 1`, and the projection is not a proof at all — `⟦projⱼ x⟧` is absent
/// rather than `•`, so those four pairs owe a **term** and belong with `Prod`
/// on §11's row 4. The theorem above is σ-generic; what is σ-specific is
/// whether `Pⱼ` can be discharged, which is exactly why `DeclFields`
/// *quantifies* `Pⱼ` instead of deciding it.
#[allow(clippy::too_many_arguments)]
fn decl_typing(
    c: &mut Checker<'_, '_>,
    ind: &Name,
    idx: u32,
    s: &E,
    field_ty: &E,
    key: &(Name, Vec<u32>),
    np: usize,
    param_args: &[E],
    dt: &crate::interp::Translated,
) -> Result<Thm, Gap> {
    // The `?`-census: every decline below names its own line, not the
    // caller that turned it into an `Ev`. See [`crate::gap!`].
    macro_rules! miss {
        () => { crate::gap!(Gap::StructProj(ind.clone())) };
    }
    let j = idx as usize;
    let spec = dt.ind.spec.ctors.first().ok_or_else(|| miss!())?;
    if j >= spec.args.len() || dt.ind.params.len() != np {
        return Err(miss!())
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
        betas.push((set, field_in_u0(c, &e).ok_or_else(|| miss!())?));
    }

    let te = c.infer_type(s).map_err(|_| Gap::Classifier)?;
    let subject = te.tm.clone().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let s_mem = te.ev.thm().cloned().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let former = c.stored_term(ind, &key.1).ok_or_else(|| miss!())?;
    let fields = {
        let (kenv, app, _) = c.interp().and_then(|ip| ip.ind_parts()).ok_or(Gap::IndApparatus)?;
        app.decl_fields(kenv, key, dt).ok_or_else(|| miss!())?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let point = ip.point();
    if fields.subsets.len() != spec.args.len() || fields.steps.len() != spec.args.len() {
        return Err(miss!())
    }

    // ── `⊢ ⟦s⟧ ∈ ind(⟦p⃗⟧)`, the ladder's major premise ──────────────────────
    //
    // One move from what the checker holds: β down the stored type former's
    // nest. The equality against `Interp::mk` is the drift check — a `beta_spine`
    // that landed anywhere else is not this declaration's carrier.
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(|| miss!())?;
    if carrier != ip.mk(dt.ind.ty, ps.clone()) {
        return Err(miss!())
    }
    let major = ip.retarget_set(&s_mem, &spine_eq).ok_or_else(|| miss!())?;

    // ── the ladder, `P₀ … Pⱼ` then `steps[j]` ───────────────────────────────
    let psub: Vec<(kernel::FreeVar, Term)> =
        dt.ind.params.iter().copied().zip(ps.iter().cloned()).collect();
    let mut subs = Vec::with_capacity(j + 1);
    for (q, (_, mem)) in betas.iter().enumerate() {
        let unfold = dt
            .field_abbrev
            .first()
            .and_then(|r| r.get(q))
            .and_then(|t| {
                let mut a = ps.clone();
                a.extend(std::iter::repeat_n(point.clone(), q));
                derived::inst_all(t, &a)
            })
            .ok_or_else(|| miss!())?;
        let sym_in_u0 = ip.retarget_subject(mem, &unfold).ok_or_else(|| miss!())?;
        let sym = sym_in_u0.concl().as_mem().ok_or_else(|| miss!())?.0.clone();
        let p_q = crate::rec_prop::subset_of_unit(ip, &sym, &sym_in_u0).ok_or_else(|| miss!())?;
        if *p_q.concl() != crate::rec_dep::subst_f(&fields.subsets[q], &psub) {
            return Err(miss!())
        }
        subs.push(p_q);
    }
    // `∀p⃗ ∀z`, in that order — `z` is the last binder and `major` its premise.
    let mut inst = ps.clone();
    inst.push(subject);
    let all = derived::inst_all(&fields.steps[j], &inst)
        .and_then(|t| Thm::mp(&t, &major))
        .ok_or_else(|| miss!())?;
    let conj = subs
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| miss!())?;
    let hs_all = Thm::mp(&all, &conj).ok_or_else(|| miss!())?;
    let hyps: Vec<Formula> = fields.memberships[..=j]
        .iter()
        .map(|f| crate::rec_dep::subst_f(f, &psub))
        .collect();
    let h_sym = derived::conj_proj(&hyps, j)
        .and_then(|pr| Thm::mp(&pr, &hs_all))
        .ok_or_else(|| miss!())?;

    // …and back onto `⟦βⱼ⟧`, where the projection's own type is.
    let unfold = dt
        .field_abbrev
        .first()
        .and_then(|r| r.get(j))
        .and_then(|t| {
            let mut a = ps.clone();
            a.extend(std::iter::repeat_n(point.clone(), j));
            derived::inst_all(t, &a)
        })
        .ok_or_else(|| miss!())?;
    let h = ip.retarget_set(&h_sym, &unfold).ok_or_else(|| miss!())?;
    if *h.concl() != Formula::mem(point, betas[j].0.clone()) {
        return Err(miss!())
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
///
/// The second route is a *fixture* and no longer only an argument, at both
/// levels. `structure W : Type where u : PUnit.{1}` reaches it and gating on
/// `is_prop_ev` would fail it; no corpus member is in that cell.
///
/// * [`tests::a_unit_like_data_field_denotes_the_point_by_its_carrier`] asserts
///   the **divergence** — `is_prop_ev` on the field says `false` and the
///   projection is typed at `• ∈ ⟦PU⟧` all the same. That statement is not
///   available end to end, because `is_prop_ev` is not in any report.
/// * `mini/tests/fixtures/field_in_u0_by_carrier.lean` and
///   `designed.rs::a_data_field_whose_carrier_is_in_u0_denotes_the_point` run
///   the same shape through the frontend and read the **term**. Both routes are
///   pinned there, and both are load-bearing: the fixture's `Mixed.u` needs
///   route 1 for its parameter rung and route 2 for its `PU.{1}` rung, and the
///   mutation that removes either one fires only that test.
///
/// **A count cannot adjudicate this**, which is why the e2e assertions read
/// dumped conclusions: under option B every pair in that fixture still derives,
/// because [`crate::proj_data`] answers `πⱼ(z)` where this route answers `•`.
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
    let key = (*name, inst);
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
    fn prop() -> E { sort(Level::zero()) }

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
        let spine = |x: u32, y: u32| app(app(konst(p2, no()), bvar(x)), bvar(y));
        let mut env = Environment::empty();
        add(
            &mut env,
            &Declaration::Inductive {
                name: p2,
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
    fn projector(idx: u32) -> (E, E) { projector_at(idx, prop()) }

    /// The same at an arbitrary parameter sort — `Prop` makes the projection a
    /// proof and `Type 0` makes it data, and nothing else about the term moves.
    fn projector_at(idx: u32, field_sort: E) -> (E, E) {
        let p2 = nm("P2");
        let structure = app(app(konst(p2, no()), bvar(1)), bvar(0));
        // The codomain is `a` at index 0 and `b` at index 1 — three binders in,
        // so `#2` and `#1`.
        let cod = bvar(2 - idx);
        let ty = forall(
            field_sort.clone(),
            forall(field_sort.clone(), forall(structure.clone(), cod)),
        );
        let body = Rc::new(crate::expr::Expr::Proj { ind: p2, idx, s: bvar(0) });
        (ty, lam(field_sort.clone(), lam(field_sort, lam(structure, body))))
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

    /// `P2 (a b : σ) : Type 0 | mk : a → b → P2 a b` — the same shape as
    /// [`env`] one level up, so the **carrier** is class (T) whatever the
    /// fields are, and `σ` is the only thing that moves.
    ///
    /// At `σ = Prop` the fields are propositions and the projections are
    /// proofs; at `σ = Type 0` they are data. `PProd.{0,0}` and `PProd.{1,1}`
    /// are exactly these two, which is why one declaration with one parameter
    /// sort is the whole corner walk.
    fn class_t_env(field_sort: E) -> Environment {
        let p2 = nm("P2");
        let ty0 = sort(Level::zero().succ());
        let spine = |x: u32, y: u32| app(app(konst(p2, no()), bvar(x)), bvar(y));
        let mut env = Environment::empty();
        add(
            &mut env,
            &Declaration::Inductive {
                name: p2,
                lparams: vec![],
                num_params: 2,
                ty: forall(field_sort.clone(), forall(field_sort.clone(), ty0)),
                ctors: vec![(
                    Name::str(&p2, "mk"),
                    forall(
                        field_sort.clone(),
                        forall(field_sort, forall(bvar(1), forall(bvar(1), spine(3, 2)))),
                    ),
                )],
            },
        )
        .expect("the declaration is accepted");
        env
    }

    /// **A `Prop` field of a class-(T) structure is typed, at every field** —
    /// over [`derived::inductive::DeclFields`].
    ///
    /// *(Flipped in place, `MINI-HANDOFF.md` §9's convention; the prior
    /// revision is at `fd6b16b`, where this asserted
    /// `Gap::StructProj` under the name
    /// `a_class_t_structure_with_prop_fields_is_declined_not_spoken_for`. The
    /// decline was pinned deliberately so that a route covering the row would
    /// flip this rather than quietly widen one of the other two, and that is
    /// what happened: `DeclFields` landed and the third branch spends it. The
    /// **rationale** the old header gave — neither `A_φ` nor a truncation
    /// exists, so neither existing ladder is about this carrier — was right and
    /// is why the third ladder exists rather than a widening.)*
    ///
    /// Both indices, for [`a_class_s_projection_is_typed_at_every_field`]'s
    /// reason: `H₁` is derived *through* `P₀` and `H₀`, so a clause that
    /// stopped at the first field would pass at `idx = 0`.
    #[test]
    fn a_class_t_structures_prop_fields_are_typed_at_every_field() {
        let env = class_t_env(prop());
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

    /// **A *data* field of the same carrier is typed too, and its
    /// interpretation is a term** — `MINI-HANDOFF.md` §11's row 4, over
    /// [`crate::proj_data`].
    ///
    /// *(Flipped in place, §9's convention; the prior revision is at `8bb3915`,
    /// where this asserted `Gap::StructProj` and `tm == None` under the name
    /// `a_data_field_of_a_class_t_structure_is_declined_not_spoken_for`. It was
    /// written as the frontier the previous flip vacated and it flipped in the
    /// next commit but one. Its rationale was that the σ split on a `proj` row
    /// is about **whether a hypothesis is available** and not about the
    /// theorem — that held: what closed the row was a *different* theorem
    /// (`DeclProj`) at a `φ` mentioning `z`, not `DeclFields` becoming
    /// dischargeable at `Type 0`.)*
    ///
    /// The two cells are one corner walk over one declaration: at `Prop`
    /// parameters the fields are proofs and `⟦projⱼ x⟧` is `•`
    /// ([`a_class_t_structures_prop_fields_are_typed_at_every_field`]); at
    /// `Type 0` they are data and it is `πⱼ(⟦x⟧)`. **Both cells are now
    /// positive, and the assertion that keeps them apart is the term**, which
    /// is the sharp statement of the row and the thing the previous two
    /// revisions could only pin negatively.
    #[test]
    fn a_data_field_of_a_class_t_structure_is_typed_at_a_real_term() {
        let ty0 = sort(Level::zero().succ());
        let env = class_t_env(ty0.clone());
        for idx in [0u32, 1] {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let (_, val) = projector_at(idx, ty0.clone());
            let t = c.infer_type(&val).expect("infer");
            assert!(
                t.ev.thm().is_some(),
                "idx {idx}: the data projection has no typing: {:?}",
                t.ev
            );
            let point = c.interp().expect("threaded").point();
            let tm = t.tm.clone().unwrap_or_else(|| panic!("idx {idx}: no interpretation"));
            // The λ is *not* a proof — its codomain is `Type 0` — so this is a
            // function-space element and not `•`. Asserting the inequality is
            // what separates row 4 from its three siblings: they all return the
            // point, and a route that quietly widened one of them would pass
            // every other assertion here.
            assert_ne!(tm, point, "idx {idx}: a data projection must not denote •");
        }
    }

    /// ```text
    /// inductive PU.{u} : Sort u | unit : PU.{u}   -- `PUnit.{u}`
    /// inductive W : Type 0 | mk : PU.{1} → W      -- `structure W : Type where u : PUnit.{1}`
    /// ```
    ///
    /// The **second route** of [`field_in_u0`]: a field whose Lean sort is
    /// `Type 0` — so `is_prop` is false — and whose *carrier* is a conditional
    /// singleton in `U₀` all the same.
    ///
    /// **`PU` must be level-*polymorphic*, and that is the whole of what makes
    /// the second route reachable.** [`crate::zoneb::provably_nonzero`] reads
    /// the declaration's own level *expression*, so `Sort u` at a bare `Param`
    /// is class (S) at every σ, `PU.{1}` included, and the carrier lands in
    /// `IndApparatus::props` with `ClassS::in_u0` beside it. Written
    /// monomorphically as `inductive PU : Type 0`, the level is `Succ Zero`,
    /// the declaration is class (T), its carrier is in `decls` — which the
    /// second route does not consult — and the projection routes to
    /// [`crate::proj_data`] at `π₀(⟦x⟧)` instead. That was measured, not
    /// reasoned: the monomorphic version of this fixture was written first and
    /// failed, with `field_in_u0` declining and `props` empty.
    fn unit_field_env() -> Environment {
        let (pu, w) = (nm("PU"), nm("W"));
        let u = nm("u");
        let at1: Rc<[Level]> = vec![Level::zero().succ()].into();
        let ty0 = sort(Level::zero().succ());
        let mut env = Environment::empty();
        add(
            &mut env,
            &Declaration::Inductive {
                name: pu,
                lparams: vec![u],
                num_params: 0,
                ty: sort(Level::param(u)),
                ctors: vec![(
                    Name::str(&pu, "unit"),
                    konst(pu, vec![Level::param(u)].into()),
                )],
            },
        )
        .expect("PU is accepted");
        add(
            &mut env,
            &Declaration::Inductive {
                name: w,
                lparams: vec![],
                num_params: 0,
                ty: ty0,
                ctors: vec![(
                    Name::str(&w, "mk"),
                    forall(konst(pu, at1), konst(w, no())),
                )],
            },
        )
        .expect("W is accepted");
        env
    }

    /// **A field whose Lean sort is not `Prop` still denotes `•` when its
    /// carrier is in `U₀`** — [`field_in_u0`]'s second route, which is
    /// `INTERP-AUDIT.md` L4's divergence made into a fixture.
    ///
    /// The two assertions are the divergence itself. `is_prop_ev` on the
    /// field's type says **false** — `PU : Type 0`, exactly `PUnit.{1}` — and
    /// the projection is nonetheless typed at `• ∈ ⟦PU⟧`, so the route is
    /// licensed by the *carrier* membership and not by the Lean sort. Gating
    /// the route on `is_prop_ev` (`INTERP-AUDIT.md` L4, option B) fails the
    /// second assertion: `proj_prop` would decline and `proj_data` would answer
    /// `π₀(⟦W.mk PU.unit⟧)`, which is a **different term** for the same
    /// expression. The two are provably equal — `⟦PU.{1}⟧ ⊆ 1` — but nothing
    /// here derives the equation, so the cost of choosing wrongly is drift and
    /// gaps rather than a false certificate.
    ///
    /// It is the third cell of the class-(T) walk beside
    /// [`a_class_t_structures_prop_fields_are_typed_at_every_field`] (a `Prop`
    /// field: `•`, route one) and
    /// [`a_data_field_of_a_class_t_structure_is_typed_at_a_real_term`] (a field
    /// at a *variable* of sort `Type 0`, where neither route applies and the
    /// term is `πⱼ`). No corpus member is in this cell.
    ///
    /// **Kept beside the end-to-end fixture, and this is what it adds.**
    /// `mini/tests/fixtures/field_in_u0_by_carrier.lean` runs the same shape
    /// through the frontend and pins the *term*; what it cannot state is the
    /// first assertion below. `is_prop_ev` appears in no report, so "the Lean
    /// sort says `false` **and** the projection is `•`" — the divergence L4 is
    /// about — is only sayable here.
    #[test]
    fn a_unit_like_data_field_denotes_the_point_by_its_carrier() {
        let env = unit_field_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let mk = Name::str(&nm("W"), "mk");
        let unit = Name::str(&nm("PU"), "unit");
        let at1u: Rc<[Level]> = vec![Level::zero().succ()].into();
        let subject = app(konst(mk, no()), konst(unit, at1u));
        let e = Rc::new(Expr::Proj { ind: nm("W"), idx: 0, s: subject });

        let at1: Rc<[Level]> = vec![Level::zero().succ()].into();
        let field_ty = konst(nm("PU"), at1);
        let (is_prop, _) = c.is_prop_ev(&field_ty).expect("PU has a sort");
        assert!(!is_prop, "the witness is only a witness while `PU`'s Lean sort is not `Prop`");

        let t = c.infer_type(&e).expect("infer W.mk PU.unit |>.0");
        let thm = t.ev.thm().unwrap_or_else(|| panic!("no typing: {:?}", t.ev)).clone();
        let point = c.interp().expect("threaded").point();
        assert_eq!(t.tm, Some(point.clone()), "the proof route ran, so the projection is •");
        let want = c.infer_type(&field_ty).expect("infer ⟦PU⟧").tm.expect("⟦PU⟧ is absent");
        assert_eq!(*thm.concl(), Formula::mem(point, want), "the typing is about ⟦PU⟧");
        assert!(thm.hyps().is_empty(), "no binder is open, so Γ must be empty");
    }
}
