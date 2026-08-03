//! **The class-(P) clause at an index** — Carneiro §5.2's truncation clause
//! when the declaration has indices.
//!
//! # Interface
//!
//! ```text
//! class_p_ix::build(checker, T, σ, np, ni, ctor tys, level, walk) -> Result<(), Gap>
//! class_p_ix::of(checker, T, σ)                                   -> Option<Rc<ClassPIx>>
//! ```
//!
//! [`build`] is called from [`crate::zoneb::ensure`] on the branch that used to
//! decline with `CLASS_P_INDEXED`, and stores `⟦T.{σ}⟧` and every
//! `⟦T.ctor.{σ}⟧` exactly as [`crate::zoneb::build_trunc`] does at `ni = 0`.
//!
//! # What is different from `ni = 0`, and it is two things, not one
//!
//! `thesis.txt:1811–1819` states the class-(P) clause **for the indexed case
//! directly** — `⟦µt : ∀x::α. U_ℓ. K⟧ = λx::α. ulift_ℓ ‖⟦µt : ∀x::α. U_{ℓ'}. K⟧ x‖`
//! — so the `λx::α` prefix and the `x` applied to the underlying carrier are
//! the rule's own, not a non-indexed clause being stretched.
//!
//! * **The carrier.** [`TruncCarrier::over_family`] truncates an
//!   [`IndexedCarrier`], which is what [`IndexedInductive::build`] produces and
//!   nothing else does. So this route runs the §5.2 *indexed* chain
//!   (`Inductive::build` → `IndexedInductive::build`) at a `Prop`-resultant
//!   declaration, which no route did before: `zoneb::build_indexed` is reached
//!   only when the resultant sort is provably nonzero.
//!
//!   **What it does not run is the universe chain.** `decl_universe`,
//!   `IndexedUniverse::over_at` and `cumul::Chain` are all absent, because
//!   [`TruncCarrier::in_u0`] is unconditional and needs no size argument —
//!   `‖a‖ ⊆ 1` whatever `a` is. That is the whole of "class (P) is cheaper
//!   rather than more expensive", and it is why the `Legs::Skip` walk the
//!   decline already performed is enough input: the summand legs exist only to
//!   feed `DeclUniverse`, and there is no `DeclUniverse` here.
//!
//! * **The constructor.** [`crate::zoneb::trunc_ctor_bottom`] splits the nest's
//!   binders at `np` and applies the type former to the parameters *alone*. At
//!   `ni ≥ 1` the codomain is `T p⃗ e⃗ᵢ`, the spine is `np + ni` deep, and the
//!   index arguments are **expressions in the fields** rather than binders of
//!   the nest — so the result-index transport of [`crate::ctor_ix`] is needed
//!   and the non-indexed path does not extend. `TruncCtor::mem_atoms` is
//!   [`IndexedCtor::mem_atoms`] verbatim (`over_family` copies it), so the
//!   antecedent is the same three families of atom `ctor_ix` bridges, in the
//!   same order: `k` plain typings, `m` recursive ones, then the `ni` result
//!   indices `Eᵢ`.
//!
//! # `ulift_ℓ` is nothing, and the level is a refusal rather than a raise
//!
//! `thesis.txt:2106` gives `⟦ulift_n^n α⟧ = ⟦α⟧`, so the lift to `ℓ'` and the
//! drop back to `ℓ` are both no-ops on the sets and there is no second W-type.
//! Unlike [`crate::class_s_ix`], which raises `Prop` to the declaration's own
//! resultant sort with one `raise_in_gamma`, this route has nothing to raise
//! onto: `TruncCarrier::in_u0` is the only universe theorem class (P) has, and
//! `TruncCarrier::in_un` does not exist. A σ at which the resultant sort is a
//! nonzero numeral is therefore declined by name — [`ABOVE_PROP`], the same
//! refusal `build_trunc` makes at `ni = 0` and for the same reason, with the
//! same replacement scheduled.
//!
//! # What this route declines
//!
//! * **`ni = 0`** — [`crate::zoneb::build_trunc`]'s, and
//!   `TruncCarrier::over_family` refuses it too (`ixc.xvs.is_empty()`), so the
//!   two cannot both claim a declaration.
//! * **a resultant sort above `Prop`** — [`ABOVE_PROP`], above.
//!
//! It does **not** decline a recursive constructor. `TruncCtor::trunc_mem` is
//! the Lean-shaped rule whose recursive hypotheses are `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖`
//! rather than `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)`, which is what a `Prop`-valued recursive
//! declaration actually needs, and it is built for every constructor. `072` has
//! `recs = 0` and does not witness it; `Nat.le`, `Nat.le.below` and `List.Mem`
//! are the declarations that would, and they are in the prelude rather than in
//! the tutorial corpus — so the shape is covered by a synthetic witness in this
//! module's own tests, which is the only place it can be covered.
//!
//! # Nothing here searches
//!
//! Every theorem is composed forward from the nest's binders, the axioms
//! [`crate::zoneb::IndexAx`] kept, and what `derived` handed back, and the
//! finished membership is compared against `⟦codomain⟧` before it is accepted.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::{IndexedInductive, TruncCarrier};
use derived::inductive::{Inductive, Slot};
use derived::inst_all;

use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::kernel::{Checker, Typing, R};
use crate::zoneb::IndexedWalk;

/// A class-(P) declaration whose resultant sort at this σ is a nonzero numeral.
///
/// The same refusal [`crate::zoneb::build_trunc`] makes at `ni = 0`: the only
/// universe theorem class (P) has is `TruncCarrier::in_u0`, and there is no
/// `in_un` to raise onto. See that function's own comment for why the case is
/// real (`MyBool.{u} : Sort u` at `u := 1`), why the typing would be sound
/// anyway, and why it is nonetheless untestable from `good/`.
pub const ABOVE_PROP: &str = "class (P) at an index: a resultant sort above Prop";

/// **The eliminator `derived/` owes**, reported by [`crate::recursor::ensure`]
/// once the carrier is in the store.
///
/// `SCOPING.md` §7 states the theorem and places it: it sits strictly between
/// the two files that exist and takes one half from each — `prop_rec`'s
/// inversion machinery (`IndexedCtor::inv`, `Apply::pair_inj`,
/// `IndexedCarrier::good_of`, one `eq_leibniz` per index), because the
/// `goodrec` antecedent is there; and `trunc_rec`'s truncated minors and its
/// two ends (`TruncCarrier::only_point`, `TruncCarrier::elim`), because the
/// motive never sees `z`.
pub const ELIMINATOR: &str =
    "class (P) eliminator at an index: derived/ owes the indexed TruncRecursor";

/// One translated class-(P) **indexed** declaration, at one instantiation.
///
/// Kept whole for the reason [`crate::interp::TruncTranslation`] is: the
/// eliminator is a second build over the *same* `IndexedCarrier` and the same
/// truncation, and rebuilding either there would mint a second Separation that
/// no equation relates to the one the type former was stored at.
pub struct ClassPIx {
    /// The boundary walk, retained across what used to be this route's decline
    /// — the spec, the index abbreviations' defining axioms, and the field
    /// families. See [`crate::zoneb::IndexedWalk`].
    pub walk: Rc<IndexedWalk>,
    /// The erased §5.2 skeleton the indexed carrier is carved out of.
    pub base: Rc<Inductive>,
    /// The §5.2 indexed translation — `goodrec`, the `good` ι rules and
    /// `IndexedCtor::inv`, which the owed indexed class-(P) eliminator needs
    /// (`SCOPING.md` §7: it takes `prop_rec`'s inversion machinery and
    /// `trunc_rec`'s two ends).
    pub ii: Rc<IndexedInductive>,
    /// `‖ind(p⃗,x⃗)‖`, its `only_point`/`elim`/`in_u0` and the per-constructor
    /// rules.
    pub tc: Rc<TruncCarrier>,
    /// Mini's own name for `‖ind(p⃗,x⃗)‖`, of arity `np + ni` — the term the
    /// type former was stored at.
    pub sym: kernel::FnSym,
    /// `⊢ ∀p⃗∀x⃗. (sym(p⃗,x⃗) = ‖ind(p⃗,x⃗)‖)`. Without it nothing can get from
    /// `⟦T p⃗ x⃗⟧` to anything `derived` states.
    pub abbrev: Thm,
    /// The kernel variables `p⃗` every theorem above is stated at.
    pub params: Vec<FreeVar>,
}

impl ClassPIx {
    pub fn np(&self) -> usize { self.walk.spec.params() }
    pub fn ni(&self) -> usize { self.walk.spec.num_indices() }
}

/// The built objects for `(T, σ)`, if this route built them.
///
/// The consumer is the owed indexed class-(P) eliminator, which needs the
/// *same* `IndexedCarrier` and the *same* truncation this carrier was stored
/// at. Stored ahead of that consumer, as [`crate::class_s_ix::of`] was for one
/// commit and [`crate::zoneb::IndexAx`] before it.
#[allow(dead_code)]
pub(crate) fn of(c: &mut Checker<'_, '_>, ind_name: &Name, inst: &[u32]) -> Option<Rc<ClassPIx>> {
    let ip = c.interp()?;
    let app = ip.ind_apparatus()?;
    app.truncs_ix.get(&(ind_name.clone(), inst.to_vec())).cloned()
}

/// `⟦T.{σ}⟧` and `⟦T.ctor.{σ}⟧` for one class-(P) declaration with indices.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    ctor_tys: &[(Name, E)],
    level: u32,
    walk: Rc<IndexedWalk>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndexedFamily(ind_name.clone(), w);
    if walk.spec.params() != np || walk.spec.num_indices() != ni {
        return Err(bad("class (P) at an index: the walk and the declaration disagree"))
    }
    if level != 0 {
        return Err(bad(ABOVE_PROP))
    }

    let built = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let tower = ip.prelude.tower.clone();
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let wrec = app.wrec(kenv).ok_or(Gap::IndApparatus)?;
        let tr = app.trunc(kenv).ok_or(Gap::IndApparatus)?;
        // The erased skeleton, exactly as `build_indexed` builds it: the indexed
        // carrier is carved *out of* it, so it must be the same object.
        let base = Rc::new(
            Inductive::build(kenv, &mut app.mach, &walk.spec.base)
                .ok_or_else(|| bad("class (P) at an index: the skeleton"))?,
        );
        // **The §5.2 chain, with no universe chain beside it.** This is the
        // first caller to run it at a declaration whose resultant sort is not
        // provably nonzero; nothing in it reads a level, which is why it can be.
        let ii = Rc::new(
            IndexedInductive::build(
                kenv,
                &mut app.mach,
                &base,
                &walk.spec,
                &wrec.rc,
                &wrec.iota,
                &wrec.funspace,
            )
            .ok_or_else(|| bad("class (P) at an index: the indexed carrier"))?,
        );
        let tc = Rc::new(
            TruncCarrier::over_family(kenv, &app.mach, &tower, &tr, &base, &ii.carrier)
                .ok_or_else(|| bad("class (P) at an index: the truncation carrier"))?,
        );

        // **A name of mini's own for `‖ind(p⃗,x⃗)‖`**, of arity `np + ni`.
        // `trunc(ind(p⃗,x⃗))` is a term `derived` assembled, so it was never
        // recorded through `Interp::mk` and its head is `trunc` at arity 1
        // rather than the declaration at arity `np + ni`. One `define_abbrev`
        // over the parameters *and the index variables* fixes both — the same
        // move `build_trunc` makes at `ni = 0`, one binder family wider.
        let mut vars: Vec<FreeVar> = base.params.clone();
        vars.extend(tc.xvs.iter().copied());
        let (sym, ax) = derived::define_abbrev(kenv, &vars, &tc.carrier)
            .ok_or_else(|| bad("class (P) at an index: the truncation abbreviation"))?;
        let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
        let at = inst_all(&tc.in_u0, &args).ok_or(Gap::ConvCompose("trunc-ix-in-u0"))?;
        let ax_at = inst_all(&ax, &args).ok_or(Gap::ConvCompose("trunc-ix-abbrev"))?;
        let onto = ip.retarget_subject(&at, &ax_at).ok_or(Gap::ConvCompose("trunc-ix-subject"))?;
        let univ = derived::gen_all(&vars, &onto);
        let params = base.params.clone();
        (Rc::new(ClassPIx { walk: walk.clone(), base, ii, tc, sym, abbrev: ax, params }), univ)
    };
    let (built, univ) = built;

    crate::zoneb::former_at(c, ind_name, inst, np, ni, built.sym, &univ, false, 0)?;
    // **Stored before the constructors, not after them.** `base`, `ii`, `tc`
    // and the abbreviation are minted here and nowhere else — a second
    // `IndexedInductive::build` is a second family of symbols and a second
    // `TruncCarrier` a second Separation — so a consumer that cannot read them
    // back cannot re-derive them either. `MINI-HANDOFF.md` §2: the class-(P)
    // eliminator read as a `derived/` gap for a month because `build_trunc`
    // ended at `former_at` and dropped exactly this.
    if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
        app.truncs_ix.insert((ind_name.clone(), inst.to_vec()), built.clone());
    }
    // **After the former, and unable to unseat it** — `crate::ctor_ix`'s rule:
    // the type former is a complete obligation on its own, so a constructor
    // that does not build is recorded against its own name.
    for (i, (cname, cty)) in ctor_tys.iter().enumerate() {
        if let Err(g) = constructor(c, ind_name, inst, cname, cty, i, &built) {
            if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
                app.ctor_declined.insert((cname.clone(), inst.to_vec()), g);
            }
        }
    }
    Ok(())
}

/// One class-(P) indexed constructor: which declaration, which constructor, and
/// everything read before a binder opens.
struct CtorSite {
    ind: Name,
    ctor: Name,
    inst: Vec<u32>,
    i: usize,
    np: usize,
    ni: usize,
    /// `k + m`, the Lean field count.
    nf: usize,
    /// The declared field mask — the binders are in Lean order and
    /// `TruncCtor`'s atoms are plains-then-recs-then-indices.
    order: Vec<Slot>,
    codomain: E,
    cp: Rc<ClassPIx>,
}

fn constructor(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    cname: &Name,
    cty: &E,
    i: usize,
    cp: &Rc<ClassPIx>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(cname.clone(), w, Cause::Threading);
    let order = cp
        .walk
        .spec
        .base
        .ctors
        .get(i)
        .ok_or_else(|| bad(SHAPE))?
        .order
        .clone();
    let tcc = cp.tc.ctors.get(i).ok_or_else(|| bad(SHAPE))?;
    if tcc.yvs.len() + tcc.tvs.len() != order.len() {
        return Err(bad(SHAPE))
    }
    let (np, ni, nf) = (cp.np(), cp.ni(), order.len());
    let depth = np + nf;
    let codomain = crate::zoneb::peel(cty, depth).ok_or_else(|| bad("constructor arity"))?;
    let site = CtorSite {
        ind: ind_name.clone(),
        ctor: cname.clone(),
        inst: inst.to_vec(),
        i,
        np,
        ni,
        nf,
        order,
        codomain,
        cp: cp.clone(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, cname, inst, t)
}

const SHAPE: &str = "the constructor and the truncation disagree";
const FIELD: &str = "a plain field's typing";
const REC_ARG: &str = "a recursive argument's typing";
const RESULT: &str = "the result indices";
const SPINE: &str = "the family's spine at the constructor's own indices";
const RULE: &str = "TruncCtor's rule does not discharge here";

/// The bottom of `⟦T.ctorᵢ⟧`'s nest: `•`, with `TruncCtor::mem` (or, when the
/// constructor is recursive, `TruncCtor::trunc_mem`) at this nest's binders.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, nf) = (site.np, site.ni, site.nf);

    // ── the index expressions, off the checker's own telescope ──────────────
    //
    // The result indices come from the codomain; each recursive argument's from
    // that binder's Lean type, which `local_type` hands back already shifted
    // into the bottom's context. Both are then *inferred* here, which is the
    // only place the certificate `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧` exists. Read before
    // `c.binders`, exactly as `ctor_ix::ctor_bottom` does, because inference
    // needs the checker and the borrow of `interp` below is exclusive.
    let Some(result_e) = crate::zoneb::ind_spine(&site.ind, &site.codomain, np, ni, nf) else {
        return gap(bad("the codomain is not the family at its own indices"))
    };
    let mut rec_e: Vec<Vec<E>> = Vec::new();
    let mut rec_ty: Vec<Thm> = Vec::new();
    for (q, slot) in site.order.iter().enumerate() {
        if *slot != Slot::Rec {
            continue
        }
        // **The `bvar` index of the `q`-th field at the bottom** — `nf - 1 - q`,
        // the parameters cancel. `ctor_ix` records why writing it the other way
        // picks a parameter's type at every declaration with more than one
        // field.
        let idx = match u32::try_from(nf - 1 - q) {
            Ok(v) => v,
            Err(_) => return gap(bad(REC_ARG)),
        };
        let Ok(dty) = c.local_type(idx) else { return gap(bad(REC_ARG)) };
        let Some(ds) = crate::zoneb::ind_spine(&site.ind, &dty, np, ni, nf) else {
            return gap(bad(REC_ARG))
        };
        // **A recursive argument of a `Prop` family is a proof**, so its own
        // typing `⊢ ⟦T p⃗ d⃗⟧ ∈ U₀` is what moves the binder's inhabitant onto
        // the point. Inferred here, at the binder's type, and not reused from
        // the codomain: the two are the family at *different* indices.
        let Ok(dt) = c.infer_type(&dty) else { return gap(Gap::Classifier) };
        let Some(dmem) = dt.ev.thm().cloned() else {
            return gap(dt.ev.reason(Gap::NoEndpoint))
        };
        rec_e.push(ds);
        rec_ty.push(dmem);
    }
    let result = match crate::ctor_ix::infer_indices(c, &result_e) {
        Some(v) => v,
        None => return gap(bad(RESULT)),
    };
    let mut rec_tm: Vec<Vec<(Term, Thm)>> = Vec::with_capacity(rec_e.len());
    for ds in &rec_e {
        match crate::ctor_ix::infer_indices(c, ds) {
            Some(v) => rec_tm.push(v),
            None => return gap(bad(REC_ARG)),
        }
    }

    let Some((all, mems)) = c.binders(np + nf) else { return gap(Gap::NoEndpoint) };
    let Some(store_ty) = c.stored_term(&site.ind, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let at = At { all, mems, store_ty, result, recs: rec_tm, rec_ty };
    match build_ctor(ip, site, &at) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// What the nest holds at the bottom, plus the store read and the inferred
/// index expressions.
struct At {
    all: Vec<Term>,
    mems: Vec<Thm>,
    store_ty: Term,
    /// `⟦e⃗ᵢ⟧` with their typings.
    result: Vec<(Term, Thm)>,
    /// The same per recursive argument, in recursive-slot order.
    recs: Vec<Vec<(Term, Thm)>>,
    /// `⊢ ⟦T p⃗ d⃗ᵢⱼ⟧ ∈ U₀`, per recursive argument — the proof irrelevance a
    /// truncated recursive hypothesis needs.
    rec_ty: Vec<Thm>,
}

fn build_ctor(
    ip: &mut crate::interp::Interp,
    site: &CtorSite,
    at: &At,
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, nf) = (site.np, site.ni, site.nf);
    let cp = site.cp.clone();
    let tcc = cp.tc.ctors.get(site.i).ok_or_else(|| bad(SHAPE))?;
    let point = ip.point();

    let (ps, fields) = at.all.split_at(np);
    let (param_mems, field_mems) = at.mems.split_at(np);
    let (ps, fields) = (ps.to_vec(), fields.to_vec());

    // The Lean fields, split by the mask into the plains-then-recs order the
    // carrier states everything in.
    let (mut ys, mut rs) = (Vec::new(), Vec::new());
    let (mut y_mems, mut r_mems) = (Vec::new(), Vec::new());
    for (j, slot) in site.order.iter().enumerate() {
        match slot {
            Slot::Plain => {
                ys.push(fields[j].clone());
                y_mems.push(field_mems[j].clone());
            }
            Slot::Rec => {
                rs.push(fields[j].clone());
                r_mems.push(field_mems[j].clone());
            }
        }
    }
    if ys.len() != tcc.yvs.len() || rs.len() != tcc.tvs.len() || at.result.len() != ni {
        return Err(bad(SHAPE))
    }
    let k = ys.len();

    // The substitution that brings `mem_atoms` — which `derived` states at its
    // own working variables — onto this nest's terms, so every atom built below
    // can be *compared* against the one the rule carries rather than assumed.
    let mut args: Vec<Term> = ps.clone();
    args.extend(ys.iter().cloned());
    args.extend(rs.iter().cloned());
    let vars: Vec<FreeVar> = cp
        .params
        .iter()
        .chain(tcc.yvs.iter())
        .chain(tcc.tvs.iter())
        .copied()
        .collect();
    if vars.len() != args.len() {
        return Err(bad(SHAPE))
    }
    let sub: Vec<(FreeVar, Term)> = vars.iter().copied().zip(args.iter().cloned()).collect();
    // `mem`'s antecedent at the nest's terms; `trunc_mem`'s differs only at the
    // recursive atoms, and each is compared against its own rule's.
    let atoms_of = |src: &[Formula], q: usize| crate::rec_dep::subst_f(&src[q], &sub);

    let mut atoms: Vec<Thm> = Vec::with_capacity(nf + ni);

    // ── the plain fields ────────────────────────────────────────────────────
    //
    // The scope holds `yⱼ ∈ ⟦βⱼ⟧`; `Hᵢ` wants it at the `define_abbrev` symbol.
    let abbrev = cp.walk.field_abbrev.get(site.i).ok_or_else(|| bad(FIELD))?;
    for (j, mem) in y_mems.iter().enumerate() {
        let mut a: Vec<Term> = ps.clone();
        a.extend(ys[..j].iter().cloned());
        let ax = abbrev.get(j).ok_or_else(|| bad(FIELD))?;
        let unfold = inst_all(ax, &a).ok_or_else(|| bad(FIELD))?;
        let back = derived::eq_symm(&mut ip.env, &unfold).ok_or_else(|| bad(FIELD))?;
        let out = ip.retarget_set(mem, &back).ok_or_else(|| bad(FIELD))?;
        if *out.concl() != atoms_of(&tcc.trunc_atoms, j) {
            return Err(bad(FIELD))
        }
        atoms.push(out);
    }

    // ── the recursive arguments, truncated ──────────────────────────────────
    //
    // `TruncCtor::mem`'s recursive atom is `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` — an *element* of
    // the underlying §5.2 carrier, which a checker never has: the scope holds
    // `rⱼ ∈ ⟦T p⃗ d⃗⟧`, and `⟦T p⃗ d⃗⟧` is the **truncation**. `trunc_mem` is the
    // rule stated at what is actually in hand, `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖`, and the two
    // moves that get there are proof irrelevance on the subject (the field is a
    // proof, so it *is* the point) and the same spine/congruence/abbreviation
    // composite the conclusion travels on, at `d⃗ᵢⱼ` instead of `e⃗ᵢ`.
    for (j, (r_mem, ds)) in r_mems.iter().zip(at.recs.iter()).enumerate() {
        let d_axs = cp
            .walk
            .ax
            .ctors
            .get(site.i)
            .and_then(|cx| cx.rec_args.get(j))
            .ok_or_else(|| bad(REC_ARG))?;
        let before = cp.walk.spec.plains_before(site.i, j).ok_or_else(|| bad(REC_ARG))?;
        let mut d_args: Vec<Term> = ps.clone();
        d_args.extend(ys.get(..before).ok_or_else(|| bad(REC_ARG))?.iter().cloned());
        let to_trunc = carrier_eq(ip, site, &cp, &at.store_ty, &ps, param_mems, ds, d_axs, &d_args)?;
        let d_mem = at.rec_ty.get(j).ok_or_else(|| bad(REC_ARG))?;
        let pt = ip.point_of_proof(d_mem, r_mem).ok_or_else(|| bad(REC_ARG))?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(|| bad(REC_ARG))?;
        let at_pt = ip.retarget_subject(r_mem, &back).ok_or_else(|| bad(REC_ARG))?;
        let out = ip.retarget_set(&at_pt, &to_trunc).ok_or_else(|| bad(REC_ARG))?;
        if *out.concl() != atoms_of(&tcc.trunc_atoms, k + j) {
            return Err(bad(REC_ARG))
        }
        atoms.push(out);
    }

    // ── the result indices `Eᵢ` ─────────────────────────────────────────────
    //
    // No binder to read them off, so they are the inferred typings of the
    // codomain's own index expressions, moved onto `eᵢₖ` and `ιₖ`. `ιₖ` has
    // arity `np + k` and is instantiated at the earlier *interpretations*, then
    // carried to the symbols by one congruence — `ctor_ix`'s step, whose header
    // is where the argument for that order is.
    let e_axs = cp
        .walk
        .ax
        .ctors
        .get(site.i)
        .map(|cx| &cx.result)
        .ok_or_else(|| bad(RESULT))?;
    let mut e_args: Vec<Term> = ps.clone();
    e_args.extend(ys.iter().cloned());
    let mut interps: Vec<(Term, Thm)> = Vec::with_capacity(ni);
    for (q, (e_tm, mem)) in at.result.iter().enumerate() {
        let e_ax = e_axs.get(q).ok_or_else(|| bad(RESULT))?;
        let e_at = inst_all(e_ax, &e_args).ok_or_else(|| bad(RESULT))?;
        let subj = ip.retarget_subject(mem, &e_at).ok_or_else(|| bad(RESULT))?;
        let i_ax = cp.walk.ax.indices.get(q).ok_or_else(|| bad(RESULT))?;
        let mut i_args: Vec<Term> = ps.clone();
        i_args.extend(interps.iter().map(|(t, _)| t.clone()));
        let i_at = inst_all(i_ax, &i_args).ok_or_else(|| bad(RESULT))?;
        let back = derived::eq_symm(&mut ip.env, &i_at).ok_or_else(|| bad(RESULT))?;
        let onto = ip.retarget_set(&subj, &back).ok_or_else(|| bad(crate::ctor_ix::INDEX_TYPE))?;
        let i_sym = cp.walk.spec.indices.get(q).copied().ok_or_else(|| bad(RESULT))?;
        let cong = crate::ctor_ix::index_congr(ip, i_sym, &ps, &at.result[..q], &e_axs[..q], &e_args)
            .ok_or_else(|| bad(crate::ctor_ix::INDEX_TYPE))?;
        let to_syms = derived::eq_symm(&mut ip.env, &cong).ok_or_else(|| bad(RESULT))?;
        let out = ip.retarget_set(&onto, &to_syms).ok_or_else(|| bad(crate::ctor_ix::INDEX_TYPE))?;
        if *out.concl() != atoms_of(&tcc.trunc_atoms, nf + q) {
            return Err(bad(RESULT))
        }
        atoms.push(out);
        interps.push((e_tm.clone(), mem.clone()));
    }

    // ── the rule, instantiated and discharged ───────────────────────────────
    //
    // **`trunc_mem` at every `m`, including `m = 0`.** `mem` quantifies
    // `∀p⃗∀y⃗∀r⃗` and states its recursive atoms at the `r⃗`; `trunc_mem`
    // quantifies `∀p⃗∀y⃗` only and states them at `•`, which is what a checker
    // holds. At `m = 0` the two are the same theorem — `trunc_atoms` is
    // `mem_atoms` and `tvs` is empty — so there is no second shape to carry and
    // the atoms above were all compared against `trunc_atoms`.
    let mut rule_args: Vec<Term> = ps.clone();
    rule_args.extend(ys.iter().cloned());
    let rule_at = inst_all(&tcc.trunc_mem, &rule_args).ok_or_else(|| bad(RULE))?;
    let mem = match atoms.iter().rev().cloned().reduce(|acc, t| derived::and_intro(&t, &acc)) {
        None => rule_at,
        Some(h) => Thm::mp(&rule_at, &h).ok_or_else(|| bad(RULE))?,
    };

    // ── `‖ind(p⃗, e⃗ᵢ)‖` back onto `⟦T p⃗ e⃗⟧` ──────────────────────────────────
    let to_trunc =
        carrier_eq(ip, site, &cp, &at.store_ty, &ps, param_mems, &at.result, e_axs, &e_args)?;
    let back = derived::eq_symm(&mut ip.env, &to_trunc).ok_or_else(|| bad(SPINE))?;
    let out = ip.retarget_set(&mem, &back).ok_or_else(|| bad(SPINE))?;
    let goal_set = {
        let mut a: Vec<Term> = ps.clone();
        a.extend(at.result.iter().map(|(t, _)| t.clone()));
        crate::zoneb::store_spine(ip, &at.store_ty, &a)
    };
    if *out.concl() != Formula::mem(point.clone(), goal_set) {
        return Err(bad("the constructor did not land in its own codomain"))
    }
    Ok((point, out))
}

/// `⊢ ⟦T p⃗ x⃗⟧ = ‖ind(p⃗, x⃗_syms)‖` — the three-step composite this module
/// travels on twice: at a recursive argument's `d⃗ᵢⱼ` and at the codomain's
/// `e⃗ᵢ`.
///
/// ```text
/// ⟦T p⃗ x⃗⟧      = sym(p⃗, ⟦x⃗⟧)        the type former's own nest, β-reduced
/// sym(p⃗, ⟦x⃗⟧)  = sym(p⃗, x⃗_syms)     one congruence along the index axioms
/// sym(p⃗, x⃗ˢ)   = ‖ind(p⃗, x⃗ˢ)‖       mini's abbreviation for the carrier
/// ```
///
/// The middle step is where the index abbreviations the boundary walk retained
/// are load-bearing, and the last is the one the non-indexed path makes at
/// arity `np` — `build_trunc`'s `to_trunc`, one binder family wider.
#[allow(clippy::too_many_arguments)]
fn carrier_eq(
    ip: &mut crate::interp::Interp,
    site: &CtorSite,
    cp: &Rc<ClassPIx>,
    store_ty: &Term,
    ps: &[Term],
    param_mems: &[Thm],
    xs: &[(Term, Thm)],
    axs: &[Thm],
    iargs: &[Term],
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    // **Scope, not threading**, for the reason `ctor_ix::spine_eq` gives: an
    // index expression at a type the declaration's own binder was not opened at
    // is `ιₖ` mentioning `x⃗<ₖ`, which is a missing design decision rather than
    // a missing wire.
    let scope = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Scope);
    let mut a: Vec<Term> = ps.to_vec();
    let mut m: Vec<Thm> = param_mems.to_vec();
    for (t, mem) in xs {
        a.push(t.clone());
        m.push(mem.clone());
    }
    let (_, beta) = ip
        .beta_spine(store_ty, &a, &m)
        .ok_or_else(|| scope(crate::ctor_ix::INDEX_TYPE))?;
    let cong = crate::ctor_ix::index_congr(ip, cp.sym, ps, xs, axs, iargs)
        .ok_or_else(|| bad(crate::ctor_ix::INDEX_TYPE))?;
    let to_syms = derived::eq_symm(&mut ip.env, &cong).ok_or_else(|| bad(SPINE))?;
    let onto = derived::eq_trans(&mut ip.env, &beta, &to_syms).ok_or_else(|| bad(SPINE))?;
    let mut sym_args: Vec<Term> = ps.to_vec();
    for (k, _) in xs.iter().enumerate() {
        let at = inst_all(&axs[k], iargs).ok_or_else(|| bad(SPINE))?;
        sym_args.push(at.concl().as_eq().ok_or_else(|| bad(SPINE))?.0);
    }
    let ax_at = inst_all(&cp.abbrev, &sym_args).ok_or_else(|| bad(SPINE))?;
    derived::eq_trans(&mut ip.env, &onto, &ax_at).ok_or_else(|| bad(SPINE))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;

    /// Build one synthetic indexed class-(P) declaration and report what came
    /// out: whether `⟦T⟧` built, the gap if not, and whether **every**
    /// constructor built too.
    fn route(name: &str, np: u32, ty: E, ctors: &[(&str, E)]) -> (bool, Option<Gap>, bool) {
        let n = Name::simple(name);
        let no: std::rc::Rc<[Level]> = Vec::new().into();
        let names: Vec<Name> = ctors.iter().map(|(c, _)| Name::str(&n, c)).collect();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: n.clone(),
                lparams: vec![],
                num_params: np,
                ty,
                ctors: names.iter().cloned().zip(ctors.iter().map(|(_, t)| t.clone())).collect(),
            },
        )
        .unwrap_or_else(|e| panic!("{name} is accepted: {e}"));
        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        // The trichotomy must have routed it here at all: a declaration that
        // came out large-eliminating would be `class_s_ix`'s and the cell would
        // be testing the wrong route.
        assert!(
            !crate::zoneb::large_eliminating(&mut c, &n),
            "{name} is class (P) — two constructors, resultant sort not provably nonzero"
        );
        let t = c.infer_type(&konst(n, no.clone())).expect("infer the former");
        let ctor_ok = t.tm.is_some()
            && names
                .iter()
                .all(|m| c.infer_type(&konst(m.clone(), no.clone())).map(|x| x.tm.is_some()).unwrap_or(false));
        (t.tm.is_some(), t.ev.gap().cloned(), ctor_ok)
    }

    /// **The four corners of `(kᵢ, mᵢ)` at `np = 0, ni = 1`** — the class-(P)
    /// indexed seam, all four of which build.
    ///
    /// # Why these two variables and why `np = 0`
    ///
    /// `072_sortElimProp2Rec` is the corpus's only class-(P) indexed export and
    /// it is `np = 1, kᵢ = 2, mᵢ = 0, ni = 2`. So the corpus pins one cell, and
    /// what it cannot see is a **recursive** constructor and a **parameterless**
    /// declaration. `mᵢ` is the interesting variable of the two:
    ///
    /// * `mᵢ = 0` uses `TruncCtor::trunc_mem` where it coincides with
    ///   `TruncCtor::mem`, so the cell says nothing about the truncation of a
    ///   recursive hypothesis.
    /// * `mᵢ ≥ 1` is the half of `trunc_rec.rs`'s "Scope: non-indexed only"
    ///   flag that `072` does **not** witness (`SCOPING.md` §7(b): size the
    ///   guard as half-covered). It needs three things `mᵢ = 0` does not: the
    ///   recursive binder's own typing `⊢ ⟦T p⃗ d⃗⟧ ∈ U₀` for proof irrelevance,
    ///   the `d⃗ᵢⱼ` index axioms, and `plains_before` — which only bites when
    ///   `kᵢ ≥ 1` as well, and that interaction is the reason this is a walk
    ///   rather than two tests.
    ///
    /// The declarations that would witness `mᵢ ≥ 1` from a real file are
    /// `Nat.le`, `Nat.le.below` and `List.Mem`, all in the prelude and
    /// `grind-ring-5` rather than in the tutorials — so a synthetic witness is
    /// the only witness available, exactly as `zoneb`'s
    /// `a_class_p_constructor_with_a_parameter_and_a_field` is at `ni = 0`.
    ///
    /// Two constructors in every cell, and that is load-bearing rather than
    /// decorative: one constructor whose every field is a `Prop`, is recursive,
    /// or is a result index passes Carneiro's subsingleton test and the
    /// declaration comes out class **(S)**, on `class_s_ix`'s route. The
    /// `large_eliminating` assertion in `route` is what stops a cell from
    /// silently testing the wrong module.
    #[test]
    fn the_class_p_index_route_builds_at_every_field_shape() {
        let ty0 = || sort(Level::Zero.succ());
        let prop = || sort(Level::Zero);
        let k = |n: &str| konst(Name::simple(n), Vec::new().into());
        let fam = || forall(ty0(), prop());

        // `Pa : Type → Prop | a0 : Pa Prop | a1 : Pa Prop` — kᵢ = 0, mᵢ = 0.
        let (ok, gap, ctor) = route(
            "Pa",
            0,
            fam(),
            &[("a0", app(k("Pa"), prop())), ("a1", app(k("Pa"), prop()))],
        );
        assert!(ok && ctor, "kᵢ = 0, mᵢ = 0: carrier and constructors build ({gap:?})");

        // `Pb : Type → Prop | b0 : ∀ (x : Type), Pb x | b1 : Pb Prop` — a
        // **plain field**, which is also the result index.
        let (ok, gap, ctor) = route(
            "Pb",
            0,
            fam(),
            &[
                ("b0", forall(ty0(), app(k("Pb"), bvar(0)))),
                ("b1", app(k("Pb"), prop())),
            ],
        );
        assert!(ok && ctor, "kᵢ = 1, mᵢ = 0: a plain field builds ({gap:?})");

        // `Pc : Type → Prop | c0 : Pc Prop | c1 : Pc Prop → Pc Prop` — a
        // **recursive argument** at a closed index.
        let (ok, gap, ctor) = route(
            "Pc",
            0,
            fam(),
            &[
                ("c0", app(k("Pc"), prop())),
                ("c1", forall(app(k("Pc"), prop()), app(k("Pc"), prop()))),
            ],
        );
        assert!(ok && ctor, "kᵢ = 0, mᵢ = 1: a recursive argument builds ({gap:?})");

        // `Pd : Type → Prop | d0 : ∀ (x : Type), Pd x
        //                   | d1 : ∀ (x : Type), Pd x → Pd x` — both, with the
        // recursive argument's index **being the plain field**, which is what
        // makes `plains_before` load-bearing.
        let (ok, gap, ctor) = route(
            "Pd",
            0,
            fam(),
            &[
                ("d0", forall(ty0(), app(k("Pd"), bvar(0)))),
                (
                    "d1",
                    forall(ty0(), forall(app(k("Pd"), bvar(0)), app(k("Pd"), bvar(1)))),
                ),
            ],
        );
        assert!(ok && ctor, "kᵢ = 1, mᵢ = 1: a field and a recursive argument together ({gap:?})");
    }
}
