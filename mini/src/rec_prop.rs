//! **The class-(S) eliminator at `ni = 0`** — `⟦T.rec.{σ}⟧` for a declaration
//! whose carrier [`crate::class_s`] built (Carneiro §5.3, MINI-DESIGN.md §9).
//!
//! # Interface
//!
//! ```text
//! rec_prop::ensure(checker, T, σ_T, T.rec, σ_rec, ClassS) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] and nowhere else, on a declaration
//! [`crate::class_s::of`] returned a carrier for and with **exactly one**
//! constructor. On success `⟦T.rec.{σ_rec}⟧` and its typing are in the store
//! under the recursor's own instantiation.
//!
//! # The obligation, and why there is no function to build
//!
//! The pair asks for
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : T p⃗ → Sort u₁) (m : minor) (t : T p⃗). C t⟧
//! ```
//!
//! and the nest is `np + 1 + 1 + 1` deep — parameters, motive, the one minor,
//! **and `t`**. [`Checker::lam_nest`](crate::kernel::Checker::lam_nest) builds
//! the graph; what is left is a *value* in `app(C,t)` with `t ∈ A_φ(p⃗)` in the
//! innermost scope.
//!
//! **That scope atom is the whole of it.** This row was priced for a long time
//! through [`LePropRecursor::rec_typed`](derived::inductive::family::LePropRecursor),
//! `⊢ ∀m ∀T. (minor(m,•⃗) ∈ T → rec(m) ∈ fs(1,T))`, and worried that `fs(1,T)`
//! is not `fs(A_φ,T)` — a function *space* membership needing ψ to retarget,
//! where at the constant's typing the parameters are universally quantified and
//! `A_φ` may be `0`. The worry dissolves because the nest opens the major
//! premise: ψ is not needed, the retarget never arises, and `rec_term` /
//! `rec_typed` are not on the path at all. The interpretation of the
//! eliminator is the minor at the point, and the *reason* that is sound is
//! §5.3's own delayed elimination
//! ([`LePropRecursor::erase`](derived::inductive::family::LePropRecursor)):
//! every field of a `ni = 0` class-(S) constructor is a proposition, so
//! `minor(m,y⃗)` cannot tell `y⃗` from `•⃗`.
//!
//! ```text
//! t ∈ A_φ(p⃗)                          the innermost scope atom
//! t = •                                proof irrelevance at ⊢ A_φ(p⃗) ∈ U₀
//! • ∈ A_φ(p⃗)                          one Leibniz
//! Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1                 the field type's own typing — see below
//! Hⱼ : • ∈ βⱼ(p⃗,•⃗<ⱼ)                 LePropFields::steps[j]
//! minor(m,•⃗) ∈ app(C, ⟦T.ctor p⃗ •⃗⟧)  Interp::{fs_app, dprod_app, cond_app}
//! ⟦T.ctor p⃗ •⃗⟧ = •,  • = t            two Leibniz
//!   ⟹ minor(m,•⃗) ∈ app(C,t)          ∎
//! ```
//!
//! `carrier_point` is not read, though it states the second line: it lives on
//! [`LePropRecursor`](derived::inductive::family::LePropRecursor), whose build
//! costs a [`PointFun`](derived::point_fun::PointFun) and every ι rule this
//! route does not use, and the same fact is one
//! [`Interp::point_of_proof`](crate::interp::Interp::point_of_proof) off
//! [`ClassS::in_u0`](crate::class_s::ClassS::in_u0) — the theorem the carrier
//! was *stored* with. Proof irrelevance at a proposition is not a shortcut
//! here; it is the step `cond_app` already takes at every proof-valued
//! application in the program.
//!
//! # `k = 0` is the same code with one discharge fewer
//!
//! At `PUnit.unit` / `True.intro` the field loop does not run,
//! `LePropFields::steps` is empty, `minor(m,•⃗)` *is* `m`, and the bottom is the
//! minor binder's own scope typing plus the `• = t` Leibniz. Nothing is
//! special-cased: the two coincide because
//! [`LePropFields`](derived::inductive::family::LePropFields) is `Some` with an
//! empty ladder at `k = 0` rather than `None`, which its header states as the
//! contract this consumer relies on.
//!
//! # Where `Pⱼ` comes from, and the trap it walks around
//!
//! `LePropFields` will not produce `Hⱼ` without `P₀ … Pⱼ`, and `Pⱼ` is
//! `βⱼ(p⃗,•⃗<ⱼ) ⊆ 1` — the field type is a **proposition**, which at `ni = 0` is
//! forced by §5.3's side condition (`thesis.txt:1856–1858`) but is recorded
//! nowhere in [`IndexedDeclSpec`](derived::inductive::family::IndexedDeclSpec)
//! and so is a hypothesis the consumer owes.
//!
//! It is discharged from [`crate::zoneb::CtorEvidence::field_sort`], the field
//! type's own sort typing kept by the boundary walk — the only place `⟦βⱼ⟧`,
//! its typing and the scopes the earlier fields opened are ever in hand at
//! once.
//!
//! **On the corpus that certifies nothing, and the code must not be written as
//! though it did.** All three class-(S) declarations have field types that are
//! *parameters* or *closed* — `And a b`'s fields are `a` and `b`,
//! `ProjDataIndex p`'s is the closed `True`, `PUnit` has none — so `⊢ ⟦βⱼ⟧ ∈ U₀`
//! is available at this nest from the parameter binder's own scope assumption,
//! and a build that took it from there would pass every corpus test while
//! being wrong for a field type that is neither. That is the same trap as the
//! closed-index-types case that hid a `scope_vars` off-by-one for the life of
//! the project. So:
//!
//! * `field_sort` is retained **discharged** — `zoneb` states it as
//!   `⊢ ∀p⃗.(p⃗ ∈ ⟦σ⃗⟧ → ∀y⃗<ⱼ.(y⃗<ⱼ ∈ ⟦β⃗<ⱼ⟧ → ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧))`, because a
//!   hypothesis-carrying theorem cannot be `inst_all`'d and every consumer of
//!   it is at some other nest;
//! * this module instantiates it at `(p⃗, •⃗<ⱼ)` and discharges its guards from
//!   the nest's own parameter typings and from `H₀ … H_{j-1}`, which is
//!   **`LePropFields::steps`' ladder** and not the bundle: `steps[j]` needs
//!   `P₀ … Pⱼ` and no others, and that is exactly the order the climb produces
//!   them in;
//! * two tests pin it, at two levels.
//!   `dependent_field_type_is_not_a_parameter` below is the unit one: two
//!   fields where the second's type is `g y₀` at a parameter `g : a → Prop`, so
//!   `P₁` is underivable without `H₀`. `mini/tests/designed.rs`'s
//!   `a_class_s_declaration_whose_field_type_depends_on_an_earlier_field` is
//!   the end-to-end one and the sharper: `Dep3`'s three fields make `β₂`
//!   mention *both* earlier ones while `β₀` is the bare parameter `α`, so a
//!   build reading `Pⱼ` off the parameter scope gets field 0 right and fields
//!   1 and 2 wrong inside a single declaration. Two fields cannot separate
//!   "fold the whole prefix" from "take the first of it"; three can.
//!
//! `ℓⱼ = 0` is **checked**, not assumed: the retained typing is at whatever
//! sort inference gave the field type, and a class-(S) declaration with a
//! `Type`-resident field is declined by name rather than mis-derived.
//!
//! # Nothing here searches
//!
//! The route is [`crate::class_s::of`], a store read on the key
//! [`crate::zoneb::ensure`] was already handed. Inside, every theorem is
//! composed forward from the nest's own binders, from what the boundary walk
//! retained and from what `derived` handed back — and each is compared against
//! the statement it is supposed to be before it is used: `Pⱼ` against
//! `LePropFields::subsets[j]`, the walk's landing set against the motive at the
//! constructor's own interpretation, and the finished membership against
//! `⟦C t⟧` inferred from the recursor's declared codomain. A recursor of some
//! other shape cannot make those agree.

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use crate::class_s::ClassS;
use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};
use crate::scope::Scopes;

/// Make `⟦T.rec.{σ_rec}⟧` available for a class-(S) declaration with one
/// constructor, or say what the wiring could not compose.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    cs: Rc<ClassS>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    };
    // An indexed family never reaches the class-(S) carrier — `LeProp` is
    // stated at `ni = 0` — so this is the statement that the *recursor* agrees.
    if *num_indices != 0 {
        return Err(Gap::IndexedFamily(*ind_name, "an indexed recursor at the class-(S) route"))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    }
    let np = *num_params as usize;
    if *num_minors != 1 || cs.spec.len() != 1 || cs.np() != np {
        return Err(bad("class (S) eliminator: the recursor and the carrier disagree"))
    }
    let ctor = match env.get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) if ctors.len() == 1 => ctors[0],
        _ => return Err(Gap::NoInterpretation(*ind_name, ind_inst.to_vec())),
    };

    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 3;
    let codomain =
        crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad("class (S) eliminator: arity"))?;
    let u1 = crate::rec_dep::motive_level(&rec_ty, np, 0)
        .ok_or_else(|| bad("class (S) eliminator: the motive's binder is not a Lean motive"))?;

    let site = Site {
        ind: *ind_name,
        inst: ind_inst.to_vec(),
        ctor,
        np,
        depth,
        codomain,
        u1,
        cs,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// Which eliminator is being built, and everything read off the declaration
/// before a binder is opened.
struct Site {
    ind: Name,
    inst: Vec<u32>,
    /// The one constructor's name.
    ctor: Name,
    np: usize,
    /// `np + 1 + 1 + 1` — parameters, motive, the minor, the major premise.
    depth: usize,
    codomain: E,
    /// The motive's resultant sort; `0` makes the eliminator a proof.
    u1: u32,
    cs: Rc<ClassS>,
}

/// What the nest's own scopes hold at the bottom, plus the store reads.
struct At {
    /// `⟦p⃗⟧, ⟦C⟧, ⟦m⟧, ⟦t⟧`, outermost first.
    xs: Vec<Term>,
    /// Their scope typings, in the same order.
    mems: Vec<Thm>,
    /// `⟦T⟧` and `⟦T.ctor⟧`, as the store holds them.
    former: Term,
    ctor_former: Term,
    /// `⟦C t⟧`, the set the bottom's membership must be about.
    goal: Term,
    /// `u₁ = 0`: the eliminator is a proof and its interpretation is `•`.
    prop: bool,
}

const SPINE: &str = "class (S) eliminator: the type former's spine";
const CARRIER: &str = "class (S) eliminator: the carrier at the major premise";
const MOTIVE_TY: &str = "class (S) eliminator: the motive's type is not T p⃗ → Sort u₁";
const NOT_PROP: &str = "class (S) eliminator: a field type is not a proposition";
const FIELDS: &str = "class (S) eliminator: the field inhabitations";
const MINOR: &str = "class (S) eliminator: the minor does not apply at the point";
const CTOR: &str = "class (S) eliminator: the constructor's own interpretation";

/// The bottom of `⟦T.rec⟧`'s nest.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort, once from the codomain the nest actually reached.
    let prop = match c.is_prop(&site.codomain) {
        Ok(b) => b,
        Err(_) => return gap(Gap::Classifier),
    };
    if prop != (site.u1 == 0) {
        return gap(bad("class (S) eliminator: the motive's sort and its codomain disagree"))
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ctor_former) = c.stored_term(&site.ctor, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };
    let at = At { xs, mems, former, ctor_former, goal, prop };
    let key = (site.ind, site.inst.clone());
    let fields = {
        let Some((mut kenv, app, _)) = c.interp().and_then(|ip| ip.ind_parts()) else {
            return gap(Gap::IndApparatus)
        };
        let kenv = &mut *kenv;
        match app.prop_fields(kenv, &key, &site.cs) {
            Some(f) => f,
            None => return gap(bad(FIELDS)),
        }
    };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match build(ip, site, &at, &fields) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// The bottom's term and typing, or the step that did not compose.
fn build(
    ip: &mut Interp,
    site: &Site,
    at: &At,
    fields: &derived::inductive::family::LePropFields,
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let (np, depth) = (site.np, site.depth);
    let cs = &site.cs;
    let point = ip.point();

    let ps = at.xs[..np].to_vec();
    let param_mems = at.mems[..np].to_vec();
    let c_tm = at.xs[np].clone();
    let c_mem = at.mems[np].clone();
    let m_tm = at.xs[np + 1].clone();
    let m_mem = at.mems[np + 1].clone();
    let t_tm = at.xs[depth - 1].clone();
    let t_mem = at.mems[depth - 1].clone();

    // ── the carrier, and the major premise moved onto it ────────────────────
    let (carrier, spine_eq) =
        ip.beta_spine(&at.former, &ps, &param_mems).ok_or_else(|| bad(SPINE))?;
    if carrier != ip.mk(cs.lc.phi, ps.clone()) {
        return Err(bad(SPINE))
    }
    let (spine, _) = spine_eq.concl().as_eq().ok_or_else(|| bad(SPINE))?;
    let spine = spine.clone();
    let t_in_a = ip.retarget_set(&t_mem, &spine_eq).ok_or_else(|| bad(CARRIER))?;

    // `⊢ A_φ(p⃗) ∈ U₀` is the theorem the carrier is *stored* with, and one
    // proof irrelevance turns the major premise into `t = •`. `A_φ ⊆ 1`
    // whatever ψ is, so this is unconditional and needs nothing about the
    // declaration.
    let a_in_u0 = derived::inst_all(&cs.in_u0, &ps).ok_or_else(|| bad(CARRIER))?;
    let t_pt = ip.point_of_proof(&a_in_u0, &t_in_a).ok_or_else(|| bad(CARRIER))?;
    let pt_eq_t = derived::eq_symm(&mut ip.env_mut(), &t_pt).ok_or_else(|| bad(CARRIER))?;
    // `• ∈ A_φ(p⃗)` — `LePropFields`' own major premise.
    let major = ip.retarget_subject(&t_in_a, &pt_eq_t).ok_or_else(|| bad(CARRIER))?;

    // ── the motive's type, read off rather than assumed ─────────────────────
    //
    // `C : T p⃗ → Sort u₁` is binder-free in its codomain and `Sort u₁` lives in
    // `Sort (u₁+1)`, never in `Prop`, so §6.2's `Π` clause for it is the
    // **dependent product at the constant fibre** at every `u₁` — there is no
    // binder-free clause (`SCOPING.md` §10).
    let v_set = ip.sort(site.u1);
    let motive_set = c_mem.concl().as_mem().ok_or_else(|| bad(MOTIVE_TY))?.1;
    let c_fibre = ip.const_fibre_site(&v_set).ok_or_else(|| bad(MOTIVE_TY))?;
    if motive_set != ip.dprod_term(&c_fibre, spine.clone()) {
        return Err(bad(MOTIVE_TY))
    }
    if at.goal != ip.app(c_tm.clone(), t_tm.clone()) {
        return Err(bad("class (S) eliminator: the codomain is not the motive at the major premise"))
    }

    // ── the ladder: P₀ ⟹ H₀ ⟹ P₁ ⟹ … ──────────────────────────────────────
    let hs = inhabit(ip, cs, fields, &ps, &param_mems, &major).map_err(bad)?;

    // ── the minor, applied at `•⃗` ───────────────────────────────────────────
    let k = hs.len();
    let mut f_tm = m_tm;
    let mut f_mem = m_mem;
    for h in hs.iter() {
        let set = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?.1;
        let shape = ip.as_pi(&set).ok_or_else(|| bad(MINOR))?;
        // The membership the level's rule consumes is `Hⱼ` and is compared
        // against the domain the interpretation itself recorded — this is where
        // a minor whose binders are not the constructor's fields is refused.
        if *h.concl() != Formula::mem(point.clone(), shape.dom()) {
            return Err(bad(MINOR))
        }
        let out = match &shape {
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &point, &f_mem, h),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &point, h),
        }
        .ok_or_else(|| bad(MINOR))?;
        f_tm = out.concl().as_mem().ok_or_else(|| bad(MINOR))?.0;
        f_mem = out;
    }
    let (subject, landed) = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?;
    let (subject, landed) = (subject.clone(), landed.clone());

    // ── `⟦T.ctor p⃗ •⃗⟧ = •`, and the two Leibniz steps ──────────────────────
    //
    // **§6.2's proof clause decides whether there is a spine at all**, and this
    // is the one place the two class-(S) resident levels part company. When the
    // declaration's resultant sort is `Prop` the constructor *is* a proof — and
    // so is every partial application of it, because a `Prop`-valued `Π` stays
    // `Prop` under `imax` — so the interpretation short-circuits to `•` at each
    // application node and `⟦T.ctor⟧` itself is the point. When it is not
    // (`PUnit.{u}` at `u ≥ 1`, and any class-(S) declaration the trichotomy
    // sends here at a nonzero level) the store holds an `np + k`-deep λ-nest
    // with `•` at the bottom, and the equation is that nest β-reduced at these
    // very arguments.
    //
    // The split is read off the **stored term** rather than recomputed: the
    // interpretation already took it, and taking it a second time is a second
    // chance to disagree. The premise each level of the reduction consumes is
    // the parameter's own typing or `Hⱼ` — the same theorems the walk above
    // used, so the two cannot be about different points.
    let ctor_eq = if at.ctor_former == point {
        Thm::eq_refl(point.clone())
    } else {
        let mut sp_args = ps.clone();
        sp_args.extend(std::iter::repeat_n(point.clone(), k));
        let mut sp_mems = param_mems.clone();
        sp_mems.extend(hs.iter().cloned());
        let (ctor_val, eq) =
            ip.beta_spine(&at.ctor_former, &sp_args, &sp_mems).ok_or_else(|| bad(CTOR))?;
        if ctor_val != point {
            return Err(bad(CTOR))
        }
        eq
    };
    let (ctor_spine, _) = ctor_eq.concl().as_eq().ok_or_else(|| bad(CTOR))?;
    let ctor_spine = ctor_spine.clone();
    if landed != ip.app(c_tm.clone(), ctor_spine.clone()) {
        return Err(bad("class (S) eliminator: the minor does not land at the motive's constructor"))
    }
    let at_point =
        leibniz_in_motive(ip, &subject, &c_tm, &ctor_eq, &f_mem).ok_or_else(|| bad(CTOR))?;
    let mut out = leibniz_in_motive(ip, &subject, &c_tm, &pt_eq_t, &at_point)
        .ok_or_else(|| bad(CARRIER))?;

    // **A field-free constructor's minor is a proof *variable*, not `•`.**
    // At `k = 0` no application rule fires and the subject is still the minor
    // binder's own scope variable; §6.2 gives a proof `•` by irrelevance, which
    // is the same step `lam_evidence` takes one level up. With fields the last
    // `cond_app` has already delivered `•` and this costs nothing.
    let mut term = subject.clone();
    if at.prop && subject != point {
        let goal_in_u0 = ip
            .dprod_app(&c_fibre, &spine, &c_tm, &t_tm, &c_mem, &t_mem)
            .ok_or_else(|| bad(MOTIVE_TY))?;
        let pt = ip.point_of_proof(&goal_in_u0, &out).ok_or_else(|| bad(MOTIVE_TY))?;
        let back = derived::eq_symm(&mut ip.env_mut(), &pt).ok_or_else(|| bad(MOTIVE_TY))?;
        out = ip.retarget_subject(&out, &back).ok_or_else(|| bad(MOTIVE_TY))?;
        term = point;
    }
    if *out.concl() != Formula::mem(term.clone(), at.goal.clone()) {
        return Err(bad("class (S) eliminator: the minor is not about the codomain"))
    }
    Ok((term, out))
}

/// `Γ ⊢ subject ∈ app(C, b)` from `Γ ⊢ subject ∈ app(C, a)` and `⊢ a = b`.
fn leibniz_in_motive(
    ip: &mut Interp,
    subject: &Term,
    motive: &Term,
    eq: &Thm,
    mem: &Thm,
) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (a, b) = (a.clone(), b.clone());
    let hole = ip.fresh_var();
    let at_hole = ip.app(motive.clone(), Term::var(hole));
    let leib = Thm::eq_leibniz(a, b, hole, Formula::mem(subject.clone(), at_hole));
    Thm::mp(&Thm::mp(&leib, eq)?, mem)
}

/// **The ladder.** `Hⱼ : Γ ⊢ • ∈ ⟦βⱼ⟧` at `y⃗<ⱼ := •⃗`, one per plain field, at
/// the *interpretation's* own sets so that the application rules can consume
/// them directly.
///
/// **Shared with [`crate::proj_prop`], and `Hⱼ` is that clause's whole
/// obligation.** A projection out of a class-(S) structure is a proof, so
/// `⟦projⱼ x⟧` is `•` and what is owed is that `⟦βⱼ⟧` has a member — which is
/// this, unchanged. That is why the reason type is `&'static str` rather than a
/// `Gap`: the two consumers are two rows of the ledger (`recursor(T: …)` and
/// `proj(T)`) and the shared code must not mint either one's label.
///
/// Each turn of the climb is
///
/// ```text
/// field_sort[j] at (p⃗, •⃗<ⱼ), guards discharged from p⃗'s typings and H₀…H_{j-1}
///   ⟹  ⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧,  and ℓⱼ = 0 is checked here
///   ⟹  ⊢ βⱼ(p⃗,•⃗<ⱼ) ∈ U₀        along the abbreviation's own axiom
///   ⟹  Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1      one scope, prop_subsingleton, • ∈ 1
///   ⟹  H₀ … Hⱼ                  LePropFields::steps[j] at P₀ … Pⱼ
/// ```
///
/// and `Pⱼ` is compared against `LePropFields::subsets[j]` before it is used,
/// which pins the field symbol, its argument list and the binder the subset was
/// spelled with all at once.
pub(crate) fn inhabit(
    ip: &mut Interp,
    cs: &ClassS,
    fields: &derived::inductive::family::LePropFields,
    ps: &[Term],
    param_mems: &[Thm],
    major: &Thm,
) -> Result<Vec<Thm>, &'static str> {
    let bad = |w: &'static str| w;
    let point = ip.point();
    let u0 = ip.sort(0);
    let spec = cs.spec.base.ctors.first().ok_or_else(|| bad(FIELDS))?;
    let k = spec.args.len();
    if fields.subsets.len() != k || fields.memberships.len() != k || fields.steps.len() != k {
        return Err(bad(FIELDS))
    }
    let abbrev = cs.abbrev.first().ok_or_else(|| bad(FIELDS))?;
    let sorts = cs.field_sort.first().ok_or_else(|| bad(FIELDS))?;
    if abbrev.len() != k || sorts.len() != k || cs.params.len() != ps.len() {
        return Err(bad(FIELDS))
    }
    // `LePropFields`' *theorems* are prenex over the declaration's parameters
    // and instantiate; its `subsets` and `memberships` are bare **formulas**
    // and do not, so they are moved onto this nest's binders here. Everything
    // compared below is compared at mini's own terms.
    let psub: Vec<kernel::FreeVar> = cs.params.clone();
    let psub: Vec<(kernel::FreeVar, Term)> =
        psub.into_iter().zip(ps.iter().cloned()).collect();
    let hyps: Vec<Formula> =
        fields.memberships.iter().map(|f| crate::rec_dep::subst_f(f, &psub)).collect();

    // `Hⱼ` twice over: at the abbreviation symbol, which is what `steps`
    // produces, and at `⟦βⱼ⟧`, which is what the field typings' guards and the
    // application rules consume.
    let mut hs: Vec<Thm> = Vec::with_capacity(k);
    let mut subs: Vec<Thm> = Vec::with_capacity(k);
    for j in 0..k {
        let mut args: Vec<Term> = ps.to_vec();
        args.extend(std::iter::repeat_n(point.clone(), j));

        // `⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧` at `(p⃗, •⃗<ⱼ)`. The guards come off in binder
        // order: the parameters' own scope typings, then `H₀ … H_{j-1}`, which
        // is why this is a ladder and not `k` independent lemmas.
        let mut cur = sorts[j].clone();
        for (a, m) in ps.iter().zip(param_mems.iter()) {
            cur = derived::inst_all(&cur, std::slice::from_ref(a))
                .and_then(|t| Thm::mp(&t, m))
                .ok_or_else(|| bad(NOT_PROP))?;
        }
        for h in hs.iter().take(j) {
            cur = derived::inst_all(&cur, std::slice::from_ref(&point))
                .and_then(|t| Thm::mp(&t, h))
                .ok_or_else(|| bad(NOT_PROP))?;
        }
        // §5.3's side condition, as a check: at `ni = 0` every field type must
        // be a proposition, and a declaration whose field lands anywhere else
        // is declined by name rather than silently mis-derived.
        let (beta_j, sort) = cur.concl().as_mem().ok_or_else(|| bad(NOT_PROP))?;
        let (beta_j, sort) = (beta_j.clone(), sort.clone());
        if sort != u0 {
            return Err(bad(NOT_PROP))
        }

        // …carried onto the `define_abbrev` symbol `derived` states `Pⱼ` at.
        let unfold = derived::inst_all(&abbrev[j], &args).ok_or_else(|| bad(FIELDS))?;
        let sym_in_u0 = ip.retarget_subject(&cur, &unfold).ok_or_else(|| bad(FIELDS))?;
        let sym = sym_in_u0.concl().as_mem().ok_or_else(|| bad(FIELDS))?.0.clone();
        let p_j = subset_of_unit(ip, &sym, &sym_in_u0).ok_or_else(|| bad(FIELDS))?;
        if *p_j.concl() != crate::rec_dep::subst_f(&fields.subsets[j], &psub) {
            return Err(bad(FIELDS))
        }
        subs.push(p_j);

        // `H₀ … Hⱼ`, and `Hⱼ` projected out of it.
        let all = derived::inst_all(&fields.steps[j], ps)
            .and_then(|t| Thm::mp(&t, major))
            .ok_or_else(|| bad(FIELDS))?;
        let conj = subs
            .iter()
            .rev()
            .cloned()
            .reduce(|acc, t| derived::and_intro(&t, &acc))
            .ok_or_else(|| bad(FIELDS))?;
        let hs_all = Thm::mp(&all, &conj).ok_or_else(|| bad(FIELDS))?;
        let proj = derived::conj_proj(&hyps[..=j], j).ok_or_else(|| bad(FIELDS))?;
        let h_sym = Thm::mp(&proj, &hs_all).ok_or_else(|| bad(FIELDS))?;
        if *h_sym.concl() != Formula::mem(point.clone(), sym) {
            return Err(bad(FIELDS))
        }
        // …and back onto `⟦βⱼ⟧`, where the next field's typing and the minor's
        // application rule both want it.
        let h = ip.retarget_set(&h_sym, &unfold).ok_or_else(|| bad(FIELDS))?;
        if *h.concl() != Formula::mem(point.clone(), beta_j) {
            return Err(bad(FIELDS))
        }
        hs.push(h);
    }
    Ok(hs)
}

/// `Γ ⊢ B ⊆ 1` from `Γ ⊢ B ∈ U₀` — the `Pⱼ` shape, at
/// [`kernel::thm::subset`]'s own binder.
///
/// A member of `⟦Prop⟧` is `∅` or `{•}`, so each of its elements is `•` and `•`
/// is in `1`. Both halves are the anchor's:
/// [`derived::anchor::falsity::prop_subsingleton`] through
/// [`Interp::point_of_proof`], and [`derived::sums::Sums::unit_mem`]. The
/// formula comes out equal to `kernel::thm::subset(env, B, 1)` because
/// `Formula::forall` closes its binder, so the scope's own fresh variable and
/// `subset`'s are the same de Bruijn index.
pub(crate) fn subset_of_unit(ip: &mut Interp, b: &Term, in_u0: &Thm) -> Option<Thm> {
    let unit_mem = ip.prelude.tower.sums.unit_mem.clone();
    let mut scopes = Scopes::new();
    let tok = scopes.open(&mut ip.env_mut(), b.clone());
    let z_mem = scopes.get(0)?.assumption().clone();
    let z_pt = ip.point_of_proof(in_u0, &z_mem)?;
    let z_in_1 = ip.retarget_subject(&unit_mem, &z_pt)?;
    scopes.close(tok).discharge(&z_in_1).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }

    fn level(n: u32) -> Level {
        let mut l = Level::zero();
        for _ in 0..n {
            l = l.succ();
        }
        l
    }

    fn no_levels() -> Rc<[Level]> { Vec::new().into() }

    /// The eliminator's interpretation and its typing, or a panic naming the
    /// gap. Every caller then asserts the same three invariants, so they are
    /// checked here once: the typing is unconditional, it is about the term the
    /// store holds, and that term is in `⟦T.rec⟧`'s own Lean type.
    fn elim(env: &Environment, rec: &Name, sigma: &[u32]) -> (Term, Thm) {
        let mut ip = crate::interp::Interp::new();
        let mut c = Checker::threaded(env, &mut ip);
        let at: Rc<[Level]> = sigma.iter().map(|n| level(*n)).collect::<Vec<_>>().into();
        let t = c.infer_type(&konst(*rec, at)).expect("infer the eliminator");
        let tm = t
            .tm
            .clone()
            .unwrap_or_else(|| panic!("⟦{rec}.{sigma:?}⟧ has no interpretation: {:?}", t.ev));
        let m = t
            .ev
            .thm()
            .unwrap_or_else(|| panic!("⟦{rec}.{sigma:?}⟧ has no typing: {:?}", t.ev))
            .clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about the eliminator's own interpretation");
        let want = c.infer_type(&t.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…and about its own Lean type");
        (tm, m)
    }

    /// `And (a b : Prop) : Prop`, with `And.intro : ∀ a b, a → b → And a b`.
    /// `And.rec` is **generated** by [`crate::kernel::add`], exactly as it is on
    /// the corpus.
    fn and_env() -> (Environment, Name) {
        let (a, i) = (nm("And"), Name::str(&nm("And"), "intro"));
        let p = sort(Level::zero());
        let ty = forall(p, forall(p, sort(Level::zero())));
        let at = |f: E, x: E, y: E| app(app(f, x), y);
        let cty = forall(
            p,
            forall(
                p,
                forall(bvar(1), forall(bvar(1), at(konst(a, no_levels()), bvar(3), bvar(2)))),
            ),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: a,
                lparams: vec![],
                num_params: 2,
                ty,
                ctors: vec![(i, cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, Name::str(&a, "rec"))
    }

    /// **`And.rec` is interpreted with its typing, at both σ.**
    ///
    /// The two branches are §6.2's own split and not a case analysis of mini's:
    /// at `w = 0` the eliminator is a *proof* and denotes `•`; at `w ≥ 1` it is
    /// a value and its bottom is the minor applied to the two points, so the
    /// interpretation is a four-deep λ-graph that has to come apart again.
    /// Asserting the first shape at both σ would pin the wrong clause.
    #[test]
    fn and_rec_is_interpreted_at_both_sigma() {
        let (env, rec) = and_env();
        for w in [0u32, 1] {
            let (tm, _) = elim(&env, &rec, &[w]);
            let point = crate::interp::Interp::new().point();
            if w == 0 {
                assert_eq!(tm, point, "a Prop-valued motive makes And.rec a proof");
            } else {
                assert_ne!(tm, point, "a value-valued motive does not");
            }
        }
    }

    /// **The value branch's interpretation is a nest, and its bottom is the
    /// minor at the points** — non-vacuity for `w ≥ 1`, where a decline would
    /// leave the opaque constant symbol and every membership above would still
    /// hold.
    #[test]
    fn the_value_branch_is_the_minor_applied_twice() {
        let (env, rec) = and_env();
        let mut ip = crate::interp::Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer ⟦And.rec.{1}⟧");
        let mut cur = t.tm.clone().expect("interpreted");
        let ip = c.interp().expect("threaded");
        // `λ a b C m t. app(app(m,•),•)` — five binders, then two applications
        // whose arguments are both the point.
        let mut binders = Vec::new();
        for lv in 0..5 {
            let (site, _) =
                ip.as_lam(&cur).unwrap_or_else(|| panic!("⟦And.rec⟧ is not a λ at level {lv}"));
            let (skel, holes) = (site.skel.clone(), site.holes.clone());
            let x = Term::var(ip.fresh_var());
            binders.push(x.clone());
            cur = ip.rebuild(&skel, &holes, &x);
        }
        let point = ip.point();
        let ap = ip.prelude.ap.app;
        let (f, args) = ip.parts_of(&cur).expect("the bottom is an application");
        assert_eq!(f, ap, "the bottom applies the minor");
        assert_eq!(args[1], point, "…to the point");
        let (g, inner) = ip.parts_of(&args[0]).expect("…twice");
        assert_eq!(g, ap);
        assert_eq!(inner[0], binders[3], "…and the function is the minor binder");
        assert_eq!(inner[1], point);
    }

    /// **`PUnit.{u}` — `k = 0`, `np = 0`.** No field, so `LePropFields`' ladder
    /// is empty, `minor(m,•⃗)` *is* `m`, and at a `Prop`-valued motive the
    /// bottom is the minor binder's own scope variable rather than `•`. That
    /// last is the branch `rec_dep` needed too and is the one a corpus with only
    /// field-bearing constructors cannot exercise.
    #[test]
    fn punit_rec_at_no_fields() {
        let u = nm("u");
        let (p, unit) = (nm("PUnit"), Name::str(&nm("PUnit"), "unit"));
        let us: Rc<[Level]> = vec![Level::param(u)].into();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: p,
                lparams: vec![u],
                num_params: 0,
                ty: sort(Level::param(u)),
                ctors: vec![(unit, konst(p, us))],
            },
        )
        .expect("accepted");
        let rec = Name::str(&p, "rec");
        // `PUnit.rec.{u₁, u}`: the motive's level first.
        for sigma in [[0u32, 0], [1, 0], [0, 1]] {
            let (tm, _) = elim(&env, &rec, &sigma);
            if sigma[0] == 0 {
                let ip = crate::interp::Interp::new();
                assert_eq!(tm, ip.point(), "a Prop-valued motive makes PUnit.rec a proof");
            }
        }
    }

    /// **A field type that is neither a parameter nor closed.**
    ///
    /// ```text
    /// inductive D (a : Prop) (g : a → Prop) : Prop where
    ///   | mk : ∀ (y : a) (z : g y), D a g
    /// ```
    ///
    /// `β₁ = g y₀` mentions the *first field*, so `P₁ : β₁(a,g,•) ⊆ 1` cannot be
    /// read off any parameter binder: getting `app(g,•) ∈ U₀` needs `• ∈ ⟦a⟧`,
    /// which is `H₀`. This is the declaration the corpus does not have and the
    /// reason `CtorEvidence::field_sort` is retained *discharged* — with the
    /// raw, hypothesis-carrying form it kept before, this build is impossible
    /// and `And`/`PUnit`/`ProjDataIndex` cannot tell.
    ///
    /// Two fields, not one: with one field the ladder has no step to climb and
    /// the bundle would do.
    #[test]
    fn dependent_field_type_is_not_a_parameter() {
        let d = nm("D");
        let mk = Name::str(&d, "mk");
        let prop = sort(Level::zero());
        // `D : ∀ (a : Prop) (g : a → Prop), Prop`
        let ty = forall(prop, forall(forall(bvar(0), prop), prop));
        // `D.mk : ∀ (a : Prop) (g : a → Prop) (y : a) (z : g y), D a g`
        let cty = forall(
            prop,
            forall(
                forall(bvar(0), prop),
                forall(
                    bvar(1),
                    forall(
                        app(bvar(1), bvar(0)),
                        app(app(konst(d, no_levels()), bvar(3)), bvar(2)),
                    ),
                ),
            ),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: d,
                lparams: vec![],
                num_params: 2,
                ty,
                ctors: vec![(mk, cty)],
            },
        )
        .expect("accepted");
        {
            let mut ip = crate::interp::Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            assert!(
                crate::zoneb::large_eliminating(&mut c, &d),
                "one constructor with propositional fields eliminates largely"
            );
            assert!(
                crate::class_s::of(&mut c, &d, &[]).is_none(),
                "the carrier is built on demand, not before the first use"
            );
            let _ = c.infer_type(&konst(d, no_levels())).expect("infer ⟦D⟧");
            assert!(
                crate::class_s::of(&mut c, &d, &[]).is_some(),
                "D must take the class-(S) route, or this test pins nothing"
            );
        }
        let rec = Name::str(&d, "rec");
        for w in [0u32, 1] {
            elim(&env, &rec, &[w]);
        }
    }

    /// **A field that is not a proposition is declined, not mis-derived.**
    /// **A `Type`-resident field cannot reach this route, and the guard against
    /// it is a guard against the *trichotomy*, not against the corpus.**
    ///
    /// §5.3's side condition — at `ni = 0` every field is a proposition — is
    /// what makes the delayed elimination sound, and nothing in
    /// `IndexedDeclSpec` records it, so [`inhabit`] checks `ℓⱼ = 0` before it
    /// asks for `Pⱼ`. This test says why that check has no reachable witness:
    /// `E (α : Type) : Prop` with `mk : α → E α` is exactly the declaration the
    /// check is about, and the eliminator test sends it to class (P) instead —
    /// Lean's own condition and Carneiro §2.6.2 agree that a `Type`-resident
    /// field that is not a result index makes the declaration
    /// small-eliminating.
    ///
    /// So the guard is a *decline* if the two ever disagree, rather than a
    /// derivation over a false premise. Asserting only "E gets no eliminator"
    /// would pass for the wrong reason — it gets none because it has no
    /// class-(S) carrier — which is what this spells out instead.
    #[test]
    fn a_type_resident_field_cannot_reach_this_route() {
        let e = nm("E");
        let mk = Name::str(&e, "mk");
        let ty = forall(sort(level(1)), sort(Level::zero()));
        let cty = forall(
            sort(level(1)),
            forall(bvar(0), app(konst(e, no_levels()), bvar(1))),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e,
                lparams: vec![],
                num_params: 1,
                ty,
                ctors: vec![(mk, cty)],
            },
        )
        .expect("accepted");
        let mut ip = crate::interp::Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        assert!(
            !crate::zoneb::large_eliminating(&mut c, &e),
            "a Type-resident field that is not a result index is small-eliminating"
        );
        c.infer_type(&konst(e, no_levels())).expect("infer ⟦E⟧");
        assert!(
            crate::class_s::of(&mut c, &e, &[]).is_none(),
            "E must not have a class-(S) carrier — the ℓⱼ = 0 guard is what would \
             catch it if the trichotomy ever let it through"
        );
    }
}
