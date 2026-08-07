//! **The class-(S) eliminator at an index** — `⟦T.rec.{σ}⟧` for a declaration
//! [`crate::class_s_ix`] built a carrier for (Carneiro §5.3–§5.4).
//!
//! # Interface
//!
//! ```text
//! rec_s_ix::ensure(checker, T, σ_T, T.rec, σ_rec, ClassSIx) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] and nowhere else, on a declaration
//! whose class-(S) *indexed* carrier is in the store.
//!
//! # §5.3's delayed elimination, and why it cancels
//!
//! `thesis.txt:1856–1858`: every non-propositional non-recursive argument of a
//! class-(S) constructor **must appear in the result index**, which yields a
//! variable–variable equality, "and this variable can be eliminated — however,
//! due to potential dependencies on earlier arguments, we will delay this
//! elimination to the recursor". This module is where it is delayed *to*.
//!
//! The nest binds `p⃗`, the motive `C`, the minor `m`, the indices `x⃗` and the
//! major premise `t`, and owes `⟦T.rec …⟧ ∈ app(C, x⃗, ⟦t⟧)`. The minor is
//! addressed by the constructor's **fields**; the goal is addressed by its
//! **index slots**; and the delayed elimination is the map between them. At
//! `SortElimProp`:
//!
//! ```text
//! mk    : ∀ (b b1 b2 : Bool). SortElimProp b b2 b1      slot 0 ← field 1
//!                                                        slot 1 ← field 0
//! minor : ∀ (y0 y1 : Bool). C y1 y0 (mk b y0 y1)
//! goal  :                   C x0 x1 t
//! ```
//!
//! Applying the minor at `y0 := x1, y1 := x0` — the map read **backwards** —
//! makes the minor's own motive arguments `(y1, y0)` come out as `(x0, x1)`,
//! which is the goal's. **The permutation cancels against itself**, and that
//! cancellation *is* the elimination: nothing is proved about `y⃗ = e⃗⁻¹(x⃗)`,
//! the terms are simply built at the arguments the map names and the result is
//! compared against the goal. A map read the wrong way round produces
//! `C x1 x0 t` and the comparison fails.
//!
//! The major premise is where the other half goes. `⟦T p⃗ x⃗⟧` is the
//! conditional singleton `χ(p⃗,x⃗)`, `χ ⊆ 1` unconditionally, so `⟦t⟧ = •` by
//! proof irrelevance; and `⟦mk p⃗ y⃗⟧` is `•` too, because a class-(S)
//! declaration's constructor is proof-valued. One Leibniz closes the gap
//! between them. **`LeIndexCarrier::elim` and `A_φ` are not consulted at all**
//! — the nest opened the major premise, so its inhabitation is a hypothesis
//! rather than something to establish, exactly as at `ni = 0`
//! ([`crate::rec_prop`]'s header makes the same observation about ψ).
//!
//! # Two σ, one problem
//!
//! `sortElimPropRec.{u}` at `u := 0` and `u := 1` is **one** derivation, and
//! this module does not branch on `u₁` except where `crate::rec_prop` does: the
//! *stored term* is `•` at a `Prop`-valued motive and the minor's own value
//! otherwise. The reason is structural — every argument the minor is applied to
//! comes from a binder the nest already opened, and `Sort u₁` is never itself
//! `Prop`, so the motive's `Π` clause is the function space at every `u₁`. That
//! had been read off `rec_prop` and asserted three times without being
//! measured; `two_sigma_is_one_problem` below is the measurement.
//!
//! # What this declines, and why each is a shape rather than a defence
//!
//! * **a field that is not a bare result index** — `eᵢₖ` may be any term, and
//!   then the field is not recoverable from `x⃗` at all. §5.3's side condition
//!   guarantees each non-propositional field *appears* in the result index, not
//!   that it appears bare. [`NOT_BARE`].
//! * **a propositional field** — recoverable, but not from the index: it needs
//!   the `Hⱼ` ladder `crate::rec_prop` climbs, and `LePropFields` is stated at
//!   `ni = 0`. [`PROP_FIELD`]. No witness in the corpus, which is why it is a
//!   name and not a derivation.
//! * **a recursive constructor** — [`crate::class_s_ix`] never built a carrier
//!   for one, so this is unreachable and says so.
//!
//! # Nothing here searches
//!
//! The field↔slot map is read **syntactically**, off the constructor's own
//! declared codomain, in the same way a `Slot` mask is; the derivation then
//! verifies, because the finished membership is compared against `⟦C x⃗ t⟧`
//! inferred from the recursor's declared codomain. A map read wrongly cannot
//! make that comparison succeed.

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use crate::class_s_ix::ClassSIx;
use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Expr, Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};

const ARITY: &str = "class (S) indexed eliminator: arity";
const MOTIVE: &str = "class (S) indexed eliminator: the motive's binder is not a Lean motive";
const DISAGREE: &str = "class (S) indexed eliminator: the recursor and the carrier disagree";
const CARRIER: &str = "class (S) indexed eliminator: the carrier at the major premise";
const MINOR: &str = "class (S) indexed eliminator: the minor does not apply at the indices";

/// A field whose result-index expression is not the field itself. See the
/// header: §5.3 promises the field *appears* in the index, not that it appears
/// bare, and a compound `eᵢₖ` is not invertible.
pub const NOT_BARE: &str =
    "class (S) indexed eliminator: a result index is not a bare field";
/// A **propositional** field, which is legitimate and is not recoverable from
/// the index — it wants `crate::rec_prop`'s `Hⱼ` ladder, and `LePropFields` is
/// stated at `ni = 0`.
pub const PROP_FIELD: &str =
    "class (S) indexed eliminator: a field is not in the result index";

/// Make `⟦T.rec.{σ_rec}⟧` available for a class-(S) declaration with indices.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    cs: Rc<ClassSIx>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    };
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    }
    let (np, n, ni) = (*num_params as usize, *num_minors as usize, *num_indices as usize);
    if n != 1 || cs.walk.spec.len() != 1 || cs.np() != np || cs.ni() != ni || ni == 0 {
        return Err(bad(DISAGREE))
    }
    let ctor = match env.get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) if ctors.len() == 1 => ctors[0].clone(),
        _ => return Err(Gap::NoInterpretation(ind_name.clone(), ind_inst.to_vec())),
    };
    let Some(ctor_info) = env.get(&ctor) else {
        return Err(Gap::NoInterpretation(ctor.clone(), ind_inst.to_vec()))
    };
    let cty = ground::subst_ground(ctor_info.ty(), lparams, rec_inst);
    let nf = cs.walk.spec.base.ctors[0].order.len();
    if cs.walk.spec.base.ctors[0].recs != 0 {
        return Err(bad(crate::class_s_ix::RECURSIVE))
    }

    // ── §5.3's map, read off the constructor's declared codomain ────────────
    let ccod = crate::zoneb::peel(&cty, np + nf).ok_or_else(|| bad(ARITY))?;
    let slots = crate::zoneb::ind_spine(ind_name, &ccod, np, ni, nf)
        .ok_or_else(|| bad("class (S) indexed eliminator: the constructor's codomain"))?;
    // `slot k = field j`, then inverted to `field j ↦ slot k`. Both directions
    // are checked total: a field missing from the index is `PROP_FIELD` and a
    // slot that is not a bare field is `NOT_BARE`.
    let mut field_of_slot = Vec::with_capacity(ni);
    for e in &slots {
        let Expr::BVar(d) = &**e else { return Err(bad(NOT_BARE)) };
        let d = *d as usize;
        if d >= nf {
            // A *parameter*, not a field — legitimate in Lean, and it means the
            // slot carries no field, so some field must be missing below.
            return Err(bad(NOT_BARE))
        }
        field_of_slot.push(nf - 1 - d);
    }
    let mut slot_of_field = vec![usize::MAX; nf];
    for (k, j) in field_of_slot.iter().enumerate() {
        if slot_of_field[*j] != usize::MAX {
            return Err(bad(NOT_BARE))
        }
        slot_of_field[*j] = k;
    }
    if slot_of_field.contains(&usize::MAX) {
        return Err(bad(PROP_FIELD))
    }

    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 1 + n + ni + 1;
    let codomain = crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad(ARITY))?;
    let u1 = crate::rec_dep::motive_level(&rec_ty, np, ni).ok_or_else(|| bad(MOTIVE))?;

    let site = Site {
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        np,
        ni,
        depth,
        codomain,
        u1,
        slot_of_field,
        cs,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

struct Site {
    ind: Name,
    inst: Vec<u32>,
    np: usize,
    ni: usize,
    /// `np + 1 + 1 + ni + 1` — parameters, motive, the minor, indices, major.
    depth: usize,
    codomain: E,
    /// The motive's resultant sort; `0` makes the eliminator a proof.
    u1: u32,
    /// **§5.3's delayed elimination**: which index slot field `j` sits in, so
    /// the minor can be applied at the index binder that determines it.
    slot_of_field: Vec<usize>,
    cs: Rc<ClassSIx>,
}

/// The bottom of `⟦T.rec⟧`'s nest.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);

    // §6.2's split, taken twice and required to agree.
    let prop = match c.is_prop(&site.codomain) {
        Ok(b) => b,
        Err(_) => return gap(Gap::Classifier),
    };
    if prop != (site.u1 == 0) {
        return gap(bad("class (S) indexed eliminator: the motive's sort and its codomain disagree"))
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match build(ip, site, &xs, &mems, &former, &goal, prop) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

#[allow(clippy::too_many_arguments)]
fn build(
    ip: &mut Interp,
    site: &Site,
    xs: &[Term],
    mems: &[Thm],
    former: &Term,
    goal: &Term,
    prop: bool,
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let (np, ni, depth) = (site.np, site.ni, site.depth);
    let point = ip.point();

    let ps = xs[..np].to_vec();
    let param_mems = mems[..np].to_vec();
    let c_tm = xs[np].clone();
    let c_mem = mems[np].clone();
    let m_tm = xs[np + 1].clone();
    let m_mem = mems[np + 1].clone();
    let ix_tms = xs[np + 2..np + 2 + ni].to_vec();
    let ix_mems = mems[np + 2..np + 2 + ni].to_vec();
    let t_tm = xs[depth - 1].clone();
    let t_mem = mems[depth - 1].clone();

    // ── the major premise: `⟦t⟧ ∈ χ(p⃗,x⃗)`, hence `⟦t⟧ = •` ─────────────────
    let mut sp_args = ps.clone();
    sp_args.extend(ix_tms.iter().cloned());
    let mut sp_mems = param_mems.clone();
    sp_mems.extend(ix_mems.iter().cloned());
    let (carrier, spine_eq) =
        ip.beta_spine(former, &sp_args, &sp_mems).ok_or_else(|| bad(CARRIER))?;
    let want = site.cs.lic.at(&ps, &ix_tms).ok_or_else(|| bad(CARRIER))?;
    if carrier != want {
        return Err(bad(CARRIER))
    }
    let t_in_chi = ip.retarget_set(&t_mem, &spine_eq).ok_or_else(|| bad(CARRIER))?;
    // `χ ⊆ 1` unconditionally, so this needs nothing about the declaration.
    let chi_in_u0 = derived::inst_all(&site.cs.lic.in_u0, &sp_args).ok_or_else(|| bad(CARRIER))?;
    let t_pt = ip.point_of_proof(&chi_in_u0, &t_in_chi).ok_or_else(|| bad(CARRIER))?;
    let pt_eq_t = derived::eq_symm(&mut ip.env, &t_pt).ok_or_else(|| bad(CARRIER))?;

    // ── the minor, applied at the indices the map names ─────────────────────
    //
    // Field `j` is determined by index slot `slot_of_field[j]`, so its argument
    // is that binder's own term and its membership that binder's own scope
    // assumption — nothing is derived, and the domain is compared against the
    // one the interpretation recorded, which is where a field whose type is not
    // its slot's index type is refused.
    let mut f_tm = m_tm;
    let mut f_mem = m_mem;
    for j in 0..site.slot_of_field.len() {
        let k = site.slot_of_field[j];
        let (a, a_mem) = (
            ix_tms.get(k).cloned().ok_or_else(|| bad(MINOR))?,
            ix_mems.get(k).cloned().ok_or_else(|| bad(MINOR))?,
        );
        let set = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?.1;
        let shape = ip.as_pi(&set).ok_or_else(|| bad(MINOR))?;
        if *a_mem.concl() != Formula::mem(a.clone(), shape.dom()) {
            return Err(bad(MINOR))
        }
        let out = match &shape {
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &a, &f_mem, &a_mem),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &a, &a_mem),
        }
        .ok_or_else(|| bad(MINOR))?;
        f_tm = out.concl().as_mem().ok_or_else(|| bad(MINOR))?.0;
        f_mem = out;
    }
    let (subject, landed) = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?;
    let (subject, landed) = (subject.clone(), landed.clone());

    // ── `⟦mk p⃗ y⃗⟧ = •`, then `• = ⟦t⟧` ─────────────────────────────────────
    //
    // The constructor's codomain is the declaration, which is a `Prop`, so the
    // whole applied spine is a proof and its interpretation is `•` outright —
    // there is no nest to β-reduce and no equation to compose, which is the one
    // place this is *simpler* than `crate::rec_prop` rather than harder.
    // Everything the permutation did is checked by the comparison below.
    let hole = ip.env.fresh_var();
    let goal_at = |ip: &mut Interp, z: &Term| {
        let mut t = c_tm.clone();
        for x in &ix_tms {
            t = ip.app(t, x.clone());
        }
        ip.app(t, z.clone())
    };
    let at_pt = goal_at(ip, &point);
    if landed != at_pt {
        return Err(bad(
            "class (S) indexed eliminator: the minor does not land at the goal's own indices",
        ))
    }
    let at_hole = goal_at(ip, &Term::var(hole));
    let leib = Thm::eq_leibniz(
        point.clone(),
        t_tm.clone(),
        hole,
        Formula::mem(subject.clone(), at_hole),
    );
    let mut out = Thm::mp(&Thm::mp(&leib, &pt_eq_t).ok_or_else(|| bad(CARRIER))?, &f_mem)
        .ok_or_else(|| bad(CARRIER))?;

    // A field-free minor is a proof *variable*, not `•` — the same step
    // `crate::rec_prop` takes, and at a value motive there is nothing to take.
    let mut term = subject.clone();
    if prop && subject != point {
        // `⊢ app(C,x⃗,t) ∈ ⟦Prop⟧`, by walking the motive's own
        // `Π`-interpretation at the binders the nest already opened — the same
        // dispatch the minor walk uses, so the two cannot disagree about what
        // the motive is.
        let mut args: Vec<(Term, Thm)> =
            ix_tms.iter().cloned().zip(ix_mems.iter().cloned()).collect();
        args.push((t_tm.clone(), t_mem.clone()));
        let goal_in_u0 = apply_all(ip, &c_tm, &c_mem, &args).ok_or_else(|| bad(MINOR))?;
        let pt = ip.point_of_proof(&goal_in_u0, &out).ok_or_else(|| bad(MINOR))?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(|| bad(MINOR))?;
        out = ip.retarget_subject(&out, &back).ok_or_else(|| bad(MINOR))?;
        term = point;
    }
    if *out.concl() != Formula::mem(term.clone(), goal.clone()) {
        return Err(bad("class (S) indexed eliminator: the result is not about the codomain"))
    }
    Ok((term, out))
}

/// `Γ ⊢ app(f, a⃗) ∈ …`, one application rule per level, read off the
/// interpretation's own `Π` clause. The minor walk above is this with the
/// arguments chosen by §5.3's map instead of taken in order.
fn apply_all(ip: &mut Interp, f: &Term, f_mem: &Thm, args: &[(Term, Thm)]) -> Option<Thm> {
    let mut f_tm = f.clone();
    let mut cur = f_mem.clone();
    for (a, a_mem) in args {
        let set = cur.concl().as_mem()?.1;
        let shape = ip.as_pi(&set)?;
        if *a_mem.concl() != Formula::mem(a.clone(), shape.dom()) {
            return None
        }
        let out = match &shape {
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, a, &cur, a_mem),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &cur, a, a_mem),
        }?;
        f_tm = out.concl().as_mem()?.0;
        cur = out;
    }
    Some(cur)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;

    /// **Two σ, one problem — measured.**
    ///
    /// The claim, made from reading `crate::rec_prop` and repeated through
    /// three scoping rounds without a measurement, was that a class-(S)
    /// eliminator at `u := 0` and at `u := 1` is *one* derivation: every
    /// class-(S) field is a proposition or an index, the major premise is a
    /// proof, and `Sort u₁` is never itself `Prop`, so nothing in the argument
    /// can depend on `u₁`.
    ///
    /// It holds, and the measurement is sharper than the claim. **This module
    /// contains no `u₁` branch that fires.** The one guard that mentions the
    /// motive's sort — the field-free minor's proof-irrelevance step — does not
    /// run at either σ here; the split between "the eliminator is `•`" and "the
    /// eliminator is the minor's own value" is made *inside the walk*, by §6.2's
    /// own clause dispatch on the minor's `Π`, because at `u₁ = 0` the minor's
    /// body is a `Prop` and `cond_app` delivers `•` while at `u₁ ≥ 1` it is a
    /// value and `fs_app` delivers an application. The two σ do not take two
    /// paths through this file; they take one path through a term-former that
    /// answers differently.
    ///
    /// So the assertion is exactly that: both σ derive, and their **stored terms
    /// differ**, with `u := 0`'s being the point. A build that had special-cased
    /// `u₁` would satisfy the first half and this test would not notice; a build
    /// that had *failed* to distinguish them would satisfy neither.
    ///
    /// ```text
    /// inductive Sw (α : Type) : α → α → α → Prop | mk : ∀ (a b c : α), Sw α b c a
    /// ```
    ///
    /// A 3-cycle, for the reason `zoneb`'s correspondence test uses one: a swap
    /// is its own inverse, so a delayed elimination applied in the wrong
    /// direction would pass on two slots and fails on three.
    #[test]
    fn two_sigma_is_one_problem() {
        let sw = Name::simple("Sw");
        let mk = Name::str(&sw, "mk");
        let rec = Name::str(&sw, "rec");
        let ty0 = || sort(Level::Zero.succ());
        let k = || konst(sw.clone(), Vec::<Level>::new().into());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: sw.clone(),
                lparams: vec![],
                num_params: 1,
                ty: forall(
                    ty0(),
                    forall(bvar(0), forall(bvar(1), forall(bvar(2), sort(Level::Zero)))),
                ),
                ctors: vec![(
                    mk,
                    forall(
                        ty0(),
                        forall(
                            bvar(0),
                            forall(
                                bvar(1),
                                forall(
                                    bvar(2),
                                    // `Sw α b c a` — the 3-cycle.
                                    app(app(app(app(k(), bvar(3)), bvar(1)), bvar(0)), bvar(2)),
                                ),
                            ),
                        ),
                    ),
                )],
            },
        )
        .expect("Sw is accepted");
        // A class-(S) declaration's recursor carries the motive's level and
        // nothing else, which is what put it on this route in the first place.
        let lparams = match env.get(&rec) {
            Some(ConstantInfo::Recursor { lparams, .. }) => lparams.len(),
            other => panic!("Sw.rec is not a recursor: {other:?}"),
        };
        assert_eq!(lparams, 1, "large-eliminating, so the motive has its own level");

        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        let at = |c: &mut Checker<'_, '_>, l: Level| {
            let t = c
                .infer_type(&konst(rec.clone(), vec![l].into()))
                .expect("infer the eliminator");
            (t.tm.clone(), t.ev.gap().cloned())
        };
        let (t0, g0) = at(&mut c, Level::Zero);
        let (t1, g1) = at(&mut c, Level::Zero.succ());
        let t0 = t0.unwrap_or_else(|| panic!("u := 0 derives: {g0:?}"));
        let t1 = t1.unwrap_or_else(|| panic!("u := 1 derives: {g1:?}"));
        let point = c.interp().expect("threaded").point();
        assert_eq!(t0, point, "at a Prop-valued motive the eliminator is a proof");
        assert_ne!(t1, point, "…and at a value-valued one it is the minor's own value");
    }
}
