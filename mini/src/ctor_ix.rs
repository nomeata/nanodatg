//! **An indexed family's constructors** — `⟦T.ctorᵢ.{ℓ⃗}⟧` for a class-(T)
//! declaration with `ni > 0` (`INDEXED-DESIGN.md` §4, MINI-DESIGN.md §9).
//!
//! # Interface
//!
//! ```text
//! ctor_ix::ctor_abbrevs(interp, Inductive, DeclSpec)  -> the ctorᵢ names
//! ctor_ix::constructors(checker, T, σ, np, ni, ctor tys, IndexedTranslation)
//! ```
//!
//! Both are called from [`crate::zoneb::build_indexed`] and from nowhere else:
//! the first *before* the translation is assembled, because the translation
//! carries what it mints (see [`ctor_abbrevs`]); the second once the type
//! former is in the store. It returns `()` **always**: a constructor that
//! does not build is recorded under its own key in
//! [`IndApparatus::ctor_untranslated`](crate::interp::IndApparatus), and the type
//! former — a complete obligation on its own, which `042_rbTreeDef` asks for
//! and nothing else — stays where it is. A single constructor's decline must
//! not take the declaration's carrier down with it.
//!
//! # The obligation
//!
//! `⟦T.ctorᵢ⟧` is the `np + k + m`-deep λ-nest whose bottom is `ctorᵢ(y⃗,r⃗)` and
//! whose membership is [`IndexedCtor::mem`],
//!
//! ```text
//! ⊢ ∀p⃗∀y⃗∀r⃗. ((Hᵢ^ind ∧ Eᵢ) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)))
//! ```
//!
//! discharged at the nest's own binders. Three families of atom, and each is a
//! different bridge between what the *interpretation* names and what `derived`
//! names:
//!
//! | atom | the scope holds | `mem_atoms` wants | the bridge |
//! |---|---|---|---|
//! | plain `yⱼ` | `yⱼ ∈ ⟦βⱼ⟧` | `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` | `CtorEvidence::abbrev` |
//! | recursive `rⱼ` | `rⱼ ∈ ⟦T p⃗ d⃗⟧`, the **applied spine** | `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))` | `beta_spine`, then the `d` axioms under one congruence |
//! | index `Eₖ` | nothing — there is no binder | `eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ)` | inference on the index *expression*, then the `e` and `ι` axioms |
//!
//! and the conclusion travels the other way: `ind(p⃗, e⃗ᵢ(p⃗,y⃗))` back onto the
//! applied spine `⟦T p⃗ e⃗⟧`, which is what the Lean codomain interprets to.
//!
//! # Why [`IndexedCtor::mem`] and not [`IndexedCtor::mem_lean`]
//!
//! `mem_lean` is the same theorem with `Eᵢ` pre-discharged and its antecedent
//! permuted into Lean field order, and it is the obvious thing to call. It
//! cannot be called from here. Its witness protocol demands each `wₖ` be
//! **closed, prenex, and at `derived`'s own working variables** `pvs`/`yvs`/
//! `tvs` — and this consumer sits at the bottom of a λ-nest holding
//! *open-scope, already-instantiated* theorems about the nest's own kernel
//! variables. Generalising them back is not available: the parameters' scope
//! assumptions are live hypotheses at that point, and a hypothesis-carrying
//! theorem cannot be generalised or instantiated.
//!
//! That mismatch is real and general — it is the same shape as the one
//! `CtorEvidence::field_sort` had — and the bridge for it is filed as task #38.
//! Until it exists, `mem` + [`IndexedCtor::mem_atoms`] +
//! [`IndexedCtor::lean_order`] is the interface a nest can use: `mem`
//! instantiates at the nest's terms like any other `∀`, `mem_atoms` says
//! exactly which formulas the antecedent is made of so they can be rebuilt at
//! those terms, and `lean_order` is the only place the declared field order
//! enters a carrier that otherwise erases it.
//!
//! `mem_lean`'s single existing consumer — `zoneb`'s
//! `mem_lean_composes_with_the_constructor_typings_mini_already_has` — is a
//! *field-less* constructor, where the protocol is met vacuously because there
//! are no `y⃗` and the witness really is closed. That is exactly the shape that
//! cannot tell the two interfaces apart, and it is why the test says so.
//!
//! # The index expressions come from the checker's own telescope
//!
//! `e⃗ᵢ` is read off the constructor's codomain by
//! [`crate::zoneb::ind_spine`], and `d⃗ᵢⱼ` off the recursive argument's binder
//! type — obtained from [`Checker::local_type`](crate::kernel::Checker::local_type),
//! which is the checker's own `getLocalType` and does the de Bruijn shift
//! itself. Both are then *inferred* at the bottom, which is what produces the
//! certificate `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧` that nothing else has.
//!
//! **Nothing is carried shifted by hand, and nothing is re-derived.** The
//! design note proposed recovering `⟦dₖ⟧` by decomposing the scope's own set
//! through `Interp::parts_of`, on the reasoning that reading the term the
//! traversal already built cannot drift from what the scope holds. That
//! reasoning is right and this is the same guarantee obtained for free:
//! [`Interp::beta_spine`](crate::interp::Interp::beta_spine) rebuilds the spine
//! from the arguments it is handed and states its equation *at that rebuilt
//! term*, so requiring the equation's left-hand side to be the set the scope
//! holds is the drift check, exactly. A decomposition would have given the
//! terms and not the memberships, and the memberships are the part with no
//! other source.
//!
//! # The sub-case that is a named decline
//!
//! `ιₖ` has arity `np + k`, so an index **type** may mention the earlier index
//! **expressions**, and `mem_atoms` states `Eₖ` at `ιₖ(p⃗, e⃗<ₖ)` accordingly.
//! `mem_lean` passes that through and is general in it. *Nothing exercises it
//! at either end*: `RBTree`'s index types are `Color` and `N`, `Acc`'s is a
//! parameter, every fixture's is closed, and `derived`'s own tests do not build
//! one either. Fiona's caution in `mem_lean`'s header is that a consumer
//! meeting one owes a **named decline** rather than code that looks general.
//!
//! It is [`INDEX_TYPE`], and it is not a special case bolted on: the check is
//! that the type inference gave the index expression interprets to the very set
//! the type former's own λ-nest opened that binder at. When `ιₖ` is closed the
//! two are the same term and the check costs nothing; when it is not they
//! differ by a conversion this module has no certificate for, and it says so by
//! name instead of guessing. The same check is what refuses a constructor whose
//! result index is at the wrong type, so it is load-bearing at the exercised
//! shape too.
//!
//! # Nothing here searches
//!
//! Every theorem is composed forward from the nest's binders, the axioms
//! [`crate::zoneb::IndexAx`] kept, and what `derived` handed back — and the
//! finished membership is compared against `⟦codomain⟧` before it is accepted.
//! A constructor whose codomain is not the family at its own result indices
//! cannot make that comparison succeed.

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use derived::inductive::Slot;

use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::interp::Interp;
use crate::kernel::{Checker, Typing, R};
use crate::zoneb::IndexedTranslation;

/// The index type the declaration opened its `k`-th binder at is not the one
/// the constructor's index expression was inferred to live in.
///
/// See the module header: the general case is `ιₖ` depending on `x⃗<ₖ`, which
/// nothing in the repository builds at either end.
pub const INDEX_TYPE: &str = "an index type that mentions an earlier index";

const SPINE: &str = "the family's spine at the constructor's own indices";
const REC_ARG: &str = "a recursive argument's indices";
const RESULT: &str = "the result indices";
const FIELD: &str = "a plain field's typing";
const MEM: &str = "IndexedCtor::mem does not discharge here";
const TERM: &str = "naming the constructor's term";
const SHAPE: &str = "the constructor and the carrier disagree";

/// `⊢ ∀f⃗. (cᵢ(f⃗) = ctorᵢ(y⃗,r⃗))` — one abbreviation per constructor, over the
/// constructor's Lean fields in **declared** order, minted once per
/// declaration.
///
/// # Why this is a declaration-time mint and a retained axiom
///
/// The bottom of `⟦T.ctorᵢ⟧`'s nest needs a name of mini's own: `⟨Injᵢ⟨y⃗⟩,
/// f(r⃗)⟩` is a term `derived` assembled, and no `λ` above it can skeletonise a
/// body that mentions a field. That much [`one`] used to do for itself, at
/// variables of its own, and it *worked* — for the constructor.
///
/// It does not work for anybody else. `crate::rec_ix_prop`'s minor premise has
/// to move the interpretation of `T.ctorᵢ p⃗ y⃗ r⃗` — which β-reduces to
/// `cᵢ(y⃗,r⃗)`, the symbol — onto `ctorᵢ(y⃗,r⃗)`, which is the term
/// `IndexedPropRecursor::minors` states its conclusion at, and the two are
/// related by this axiom and by nothing else. A symbol whose defining equation
/// was dropped at the end of the call that minted it is a term no later
/// consumer can get inside, and re-minting it would give a *second* symbol
/// equal to the same set with no equation between the two.
///
/// So it is minted here, before the translation is built, and stored on
/// [`IndexedTranslation::ctor_abbrev`](crate::zoneb::IndexedTranslation) beside
/// `field_abbrev` and the index axioms, which are kept for exactly this reason
/// — and it is the non-indexed path's
/// [`Translated::ctor_abbrev`](crate::interp::Translated::ctor_abbrev) at the
/// indexed shape, so this is the second occupant of a slot the design already
/// has rather than a new kind of thing.
///
/// **`p⃗ ++ f⃗`, and the two agree again.** This was over the *fields alone* for
/// as long as nothing indexed reached the general dispatcher: at `np = 0` the
/// prefix is empty and the two spellings are the same term, so the narrower
/// list cost nothing and there was no witness to widen against. The header used
/// to say "the day there is a witness, this takes `p⃗`" — the witness is
/// `mini/tests/fixtures/indexed_infinitary_ctor.lean`, which arrived once
/// `zoneb::ctor_spec` stopped refusing an indexed function-typed recursive
/// argument, and the prediction held: it took `p⃗` and nothing else about the
/// mint changed.
///
/// The reason it must is the non-indexed one's: a constructor taking
/// `RecArg::of_general` has a term mentioning the parameters through its fibre
/// summands `Σ(z::γⱼ(p⃗))`, so `define_abbrev`'s free-variable guard refuses the
/// fields alone at every `np ≥ 1`. That guard is what reported the gap —
/// `ind-spec(IxT: naming a constructor's term)` — rather than a wrong term
/// being built, which is what the previous header predicted and is what
/// happened.
///
/// **The consumer instantiates at `p⃗ ++ f⃗` too**, at the *nest's* parameters
/// ([`build`]), which is the half no arity assertion catches: the term the
/// abbreviation names has to be the term `IndexedCtor::mem` is stated at, and
/// `mem` is instantiated at this nest's `ps` through `args`. `retarget_subject`
/// is what compares them, and a mint at the declaration's parameters against a
/// `mem` at the nest's would fail there rather than silently.
pub(crate) fn ctor_abbrevs(
    ip: &mut Interp,
    base: &derived::inductive::Inductive,
    spec: &derived::inductive::DeclSpec,
) -> Option<Vec<(kernel::FnSym, Thm)>> {
    let mut out = Vec::with_capacity(spec.ctors.len());
    for (i, cs) in spec.ctors.iter().enumerate() {
        let fvs: Vec<kernel::FreeVar> = {
            let (kenv, _, _) = ip.ind_parts()?;
            (0..cs.order.len()).map(|_| kenv.fresh_var()).collect()
        };
        let (mut ys, mut rs) = (Vec::new(), Vec::new());
        for (j, slot) in cs.order.iter().enumerate() {
            match slot {
                Slot::Plain => ys.push(Term::var(fvs[j])),
                Slot::Rec => rs.push(Term::var(fvs[j])),
            }
        }
        // **The recursive slots, transported to the fibre the dispatcher is
        // over.** A constructor taking `RecArg::general` dispatches over
        // `Σ(z::γⱼ(p⃗))`, and Lean's field is a function on `⟦γⱼ⟧` — a
        // *different set*. Handing the raw field to `ctor_term` builds a
        // perfectly well-formed dispatcher over a branch that is not a
        // function on the summand: a wrong term, minted in silence, with the
        // symbol then stored on the translation for every later consumer.
        //
        // [`crate::zoneb::rec_slot_terms`] is the one place that transport is
        // written — `{⟨•,rⱼ⟩}` at a degenerate slot and `pull(gⱼ, β₀ⱼ(p⃗))` at
        // a function-typed one — and it is the identity at a plain
        // constructor, so nothing indexed-and-plain moves.
        let ps = base.param_terms();
        let rs_c = crate::zoneb::rec_slot_terms(ip, cs, spec.params, &ps, &rs)?;
        let (kenv, app, _) = ip.ind_parts()?;
        // `ctor_term_at` at `base.param_terms()` is `ctor_term`, and it is
        // those variables and not fresh ones because they are what the
        // abstraction list below holds.
        let raw = base.ctor_term_at(&app.mach, i, &ys, &rs_c, &ps)?;
        let abstraction: Vec<kernel::FreeVar> =
            base.params.iter().copied().chain(fvs.iter().copied()).collect();
        out.push(derived::define_abbrev(kenv, &abstraction, &raw)?);
    }
    Some(out)
}

/// Build every constructor of an indexed family, recording per-constructor
/// declines rather than propagating them.
pub(crate) fn constructors(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    ctor_tys: &[(Name, E)],
    tr: &Rc<IndexedTranslation>,
) {
    for (i, (cname, cty)) in ctor_tys.iter().enumerate() {
        if let Err(g) = one(c, ind_name, inst, np, ni, i, cname, cty, tr) {
            if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
                app.ctor_untranslated.insert((cname.clone(), inst.to_vec()), g);
            }
        }
    }
}

/// One constructor's λ-nest.
#[allow(clippy::too_many_arguments)]
fn one(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    i: usize,
    cname: &Name,
    cty: &E,
    tr: &Rc<IndexedTranslation>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(cname.clone(), w, Cause::Threading);
    let spec = tr
        .ii
        .spec
        .base
        .ctors
        .get(i)
        .cloned()
        .ok_or_else(|| bad(SHAPE))?;
    let nf = spec.order.len();
    let depth = np + nf;
    let codomain = crate::zoneb::peel(cty, depth).ok_or_else(|| bad("constructor arity"))?;

    // **The carrier term's name is minted at declaration time and kept on the
    // translation** — see [`ctor_abbrevs`], which explains why it cannot be
    // minted here any more.
    let (ctor_sym, ctor_ax) = tr.ctor_abbrev.get(i).cloned().ok_or_else(|| bad(TERM))?;

    let site = Site {
        ind: ind_name.clone(),
        ctor: cname.clone(),
        inst: inst.to_vec(),
        i,
        np,
        ni,
        nf,
        codomain,
        tr: tr.clone(),
        ctor_sym,
        ctor_ax,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, cname, inst, t)
}

/// Which constructor is being built, and everything read before a binder opens.
struct Site {
    ind: Name,
    ctor: Name,
    inst: Vec<u32>,
    i: usize,
    np: usize,
    ni: usize,
    /// `k + m`, the Lean field count.
    nf: usize,
    codomain: E,
    tr: Rc<IndexedTranslation>,
    ctor_sym: kernel::FnSym,
    ctor_ax: Thm,
}

/// The bottom of `⟦T.ctorᵢ⟧`'s nest.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, nf) = (site.np, site.ni, site.nf);

    let Some((all, mems)) = c.binders(np + nf) else { return gap(Gap::NoEndpoint) };
    let Some(store_ty) = c.stored_term(&site.ind, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };

    // ── the index expressions, off the checker's own telescope ──────────────
    //
    // The result indices come from the codomain; each recursive argument's from
    // that binder's Lean type, which `local_type` hands back already shifted
    // into the bottom's context. Both are then *inferred* here, which is the
    // only place the certificate `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧` exists.
    let Some(result_e) = crate::zoneb::ind_spine(&site.ind, &site.codomain, np, ni, nf) else {
        return gap(bad("the codomain is not the family at its own indices"))
    };
    let spec = &site.tr.ii.spec.base.ctors[site.i];
    let mut rec_e: Vec<Vec<E>> = Vec::new();
    for (q, slot) in spec.order.iter().enumerate() {
        if *slot != Slot::Rec {
            continue
        }
        // **The `bvar` index of the `q`-th *field* at the bottom.** `q` counts
        // fields, so the binder is at position `np + q` of an `np + nf` nest
        // and its index is `(np + nf) - 1 - (np + q)` — the parameters cancel.
        // Writing `nf + np - 1 - q` reads plausibly and picks a *parameter*'s
        // type at every declaration with more than one field; `RBTree.red` is
        // where that showed, and `local_type` is asked rather than indexed for
        // the same reason.
        let idx = match u32::try_from(nf - 1 - q) {
            Ok(v) => v,
            Err(_) => return gap(bad(REC_ARG)),
        };
        let Ok(dty) = c.local_type(idx) else { return gap(bad(REC_ARG)) };
        let Some(ds) = crate::zoneb::ind_spine(&site.ind, &dty, np, ni, nf) else {
            return gap(bad(REC_ARG))
        };
        rec_e.push(ds);
    }
    let result_tm = match infer_indices(c, &result_e) {
        Some(v) => v,
        None => return gap(bad(RESULT)),
    };
    let mut rec_tm: Vec<Vec<(Term, Thm)>> = Vec::with_capacity(rec_e.len());
    for ds in &rec_e {
        match infer_indices(c, ds) {
            Some(v) => rec_tm.push(v),
            None => return gap(bad(REC_ARG)),
        }
    }

    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let at = At { all, mems, store_ty, result: result_tm, recs: rec_tm };
    match build(ip, site, &at) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// `⟦eₖ⟧` and `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧`, one per index expression, by inference.
///
/// Shared with [`crate::rec_ix_prop`], which asks the same question of a
/// recursive argument's binder type inside a *minor premise*: the certificate
/// exists nowhere else, and a second inference would be a second chance to
/// disagree about what an index expression denotes.
pub(crate) fn infer_indices(c: &mut Checker<'_, '_>, es: &[E]) -> Option<Vec<(Term, Thm)>> {
    let mut out = Vec::with_capacity(es.len());
    for e in es {
        let t = c.infer_type(e).ok()?;
        out.push((t.tm.clone()?, t.ev.thm()?.clone()));
    }
    Some(out)
}

/// What the nest holds at the bottom, plus the store reads and the inferred
/// index expressions.
struct At {
    all: Vec<Term>,
    mems: Vec<Thm>,
    store_ty: Term,
    /// `⟦e⃗ᵢ⟧` with their typings.
    result: Vec<(Term, Thm)>,
    /// The same per recursive argument, in recursive-slot order.
    recs: Vec<Vec<(Term, Thm)>>,
}

/// The bottom's term and typing, or the bridge that did not fit.
fn build(ip: &mut Interp, site: &Site, at: &At) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, nf) = (site.np, site.ni, site.nf);
    let carrier = &site.tr.ii.carrier;
    let ctor = carrier.ctors.get(site.i).ok_or_else(|| bad(SHAPE))?;
    let spec = &site.tr.ii.spec.base.ctors[site.i];

    let (ps, fields) = at.all.split_at(np);
    let (param_mems, field_mems) = at.mems.split_at(np);
    let (ps, fields) = (ps.to_vec(), fields.to_vec());

    // The Lean fields, split by the mask into the plains-then-recs order the
    // carrier states everything in.
    let (mut ys, mut rs) = (Vec::new(), Vec::new());
    let (mut y_mems, mut r_mems) = (Vec::new(), Vec::new());
    for (j, slot) in spec.order.iter().enumerate() {
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
    if ys.len() + rs.len() != nf || at.recs.len() != rs.len() || at.result.len() != ni {
        return Err(bad(SHAPE))
    }

    // The variable list `mem` and every atom is stated at, and the substitution
    // that brings `mem_atoms` — which `derived` states at its own working
    // variables — onto this nest's terms.
    let mut args: Vec<Term> = ps.clone();
    args.extend(ys.iter().cloned());
    args.extend(rs.iter().cloned());
    let vars: Vec<kernel::FreeVar> = ctor
        .pvs
        .iter()
        .chain(ctor.yvs.iter())
        .chain(ctor.tvs.iter())
        .copied()
        .collect();
    if vars.len() != args.len() {
        return Err(bad(SHAPE))
    }
    let sub: Vec<(kernel::FreeVar, Term)> = vars.iter().copied().zip(args.iter().cloned()).collect();
    let want = |k: usize| crate::rec_dep::subst_f(&ctor.mem_atoms[k], &sub);

    // ── the plain fields ────────────────────────────────────────────────────
    let abbrev = site.tr.field_abbrev.get(site.i).ok_or_else(|| bad(FIELD))?;
    let mut atoms: Vec<Thm> = Vec::with_capacity(nf + ni);
    for (j, m) in y_mems.iter().enumerate() {
        let mut a: Vec<Term> = ps.clone();
        a.extend(ys[..j].iter().cloned());
        let ax = abbrev.get(j).ok_or_else(|| bad(FIELD))?;
        let unfold = derived::inst_all(ax, &a).ok_or_else(|| bad(FIELD))?;
        let back = derived::eq_symm(&mut ip.env, &unfold).ok_or_else(|| bad(FIELD))?;
        let out = ip.retarget_set(m, &back).ok_or_else(|| bad(FIELD))?;
        if *out.concl() != want(j) {
            return Err(bad(FIELD))
        }
        atoms.push(out);
    }

    // ── the recursive arguments ─────────────────────────────────────────────
    //
    // The scope holds `rⱼ ∈ ⟦T p⃗ d⃗⟧`, the applied spine; the atom is about
    // `ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))`. Two moves: β down the type former's own nest, and
    // one congruence carrying each `⟦dₖ⟧` onto its abbreviation symbol.
    let k_plain = ys.len();
    for (j, (r_mem, ds)) in r_mems.iter().zip(at.recs.iter()).enumerate() {
        let held = r_mem.concl().as_mem().map(|(_, set)| set);
        let eq = spine_eq(ip, site, &at.store_ty, &ps, param_mems, ds, held.as_ref())?;
        let onto = ip.retarget_set(r_mem, &eq).ok_or_else(|| bad(REC_ARG))?;
        let before = site
            .tr
            .ii
            .spec
            .plains_before(site.i, j)
            .ok_or_else(|| bad(REC_ARG))?;
        let mut a: Vec<Term> = ps.clone();
        a.extend(ys.get(..before).ok_or_else(|| bad(REC_ARG))?.iter().cloned());
        let axs = site
            .tr
            .ax
            .ctors
            .get(site.i)
            .and_then(|cx| cx.rec_args.get(j))
            .ok_or_else(|| bad(REC_ARG))?;
        let cong = index_congr(ip, carrier.ty, &ps, ds, axs, &a).ok_or_else(|| bad(REC_ARG))?;
        // `cong` is `ind(p⃗, d⃗ᵢⱼ) = ind(p⃗, ⟦d⃗⟧)` — the symbols on the left,
        // because that is the direction the abbreviation axioms are stated in.
        // The atom travels the other way.
        let back = derived::eq_symm(&mut ip.env, &cong).ok_or_else(|| bad(REC_ARG))?;
        let out = ip.retarget_set(&onto, &back).ok_or_else(|| bad(REC_ARG))?;
        if *out.concl() != want(k_plain + j) {
            return Err(bad(REC_ARG))
        }
        atoms.push(out);
    }

    // ── the result indices `Eₖ` ─────────────────────────────────────────────
    //
    // No binder to read them off, so they are the inferred typings of the
    // codomain's own index expressions, moved onto `eᵢₖ` and `ιₖ`. The `ι`
    // axiom is instantiated at the **earlier result symbols**, which is the
    // arity `ιₖ` was abstracted at.
    let e_axs = site
        .tr
        .ax
        .ctors
        .get(site.i)
        .map(|cx| &cx.result)
        .ok_or_else(|| bad(RESULT))?;
    let mut e_args: Vec<Term> = ps.clone();
    e_args.extend(ys.iter().cloned());
    let mut interps: Vec<(Term, Thm)> = Vec::with_capacity(ni);
    for (k, (e_tm, mem)) in at.result.iter().enumerate() {
        let e_ax = e_axs.get(k).ok_or_else(|| bad(RESULT))?;
        // `eᵢₖ(p⃗,y⃗) = ⟦eₖ⟧`, so the subject moves onto the symbol.
        let e_at = derived::inst_all(e_ax, &e_args).ok_or_else(|| bad(RESULT))?;
        let subj = ip.retarget_subject(mem, &e_at).ok_or_else(|| bad(RESULT))?;

        // **`ιₖ` is instantiated at the earlier *interpretations*, not at the
        // earlier *symbols*, and then carried across by one congruence.**
        //
        // This is the sub-case `mem_lean`'s header calls untested at both ends:
        // `ιₖ` has arity `np + k`, so an index *type* may mention the earlier
        // index *expressions*. When it does — `Depth`'s `j : β w` and
        // `k : γ w j` — inference hands back `⟦j⟧ ∈ app(⟦β⟧, ⟦Wrap.wrap a⟧)`,
        // at the interpretation, while `mem_atoms` states `Eₖ` at
        // `ιₖ(p⃗, e⃗<ₖ)`, at the symbols. Instantiating the `ι` axiom at the
        // symbols produces a third term equal to neither, and the move fails.
        //
        // Instantiating it at the interpretations makes the first step exact,
        // and the difference between the two spellings is then a congruence
        // over `ιₖ` along the very `e` axioms already in hand — the same shape
        // as the one carrying a recursive argument's indices. **Nothing is
        // declined here**: the general case costs one congruence, and at a
        // closed `ιₖ` (`RBTree`'s `Color` and `N`) that congruence is
        // reflexivity and costs nothing.
        let i_ax = site.tr.ax.indices.get(k).ok_or_else(|| bad(RESULT))?;
        let mut i_args: Vec<Term> = ps.clone();
        i_args.extend(interps.iter().map(|(t, _)| t.clone()));
        let i_at = derived::inst_all(i_ax, &i_args).ok_or_else(|| bad(RESULT))?;
        let back = derived::eq_symm(&mut ip.env, &i_at).ok_or_else(|| bad(RESULT))?;
        let onto = ip.retarget_set(&subj, &back).ok_or_else(|| bad(INDEX_TYPE))?;

        let i_sym = site.tr.ii.spec.indices.get(k).copied().ok_or_else(|| bad(RESULT))?;
        let cong = index_congr(ip, i_sym, &ps, &at.result[..k], &e_axs[..k], &e_args)
            .ok_or_else(|| bad(INDEX_TYPE))?;
        let to_syms = derived::eq_symm(&mut ip.env, &cong).ok_or_else(|| bad(RESULT))?;
        let out = ip.retarget_set(&onto, &to_syms).ok_or_else(|| bad(INDEX_TYPE))?;
        if *out.concl() != want(nf + k) {
            return Err(bad(RESULT))
        }
        atoms.push(out);
        interps.push((e_tm.clone(), mem.clone()));
    }

    // ── `IndexedCtor::mem`, discharged ──────────────────────────────────────
    let mem_at = derived::inst_all(&ctor.mem, &args).ok_or_else(|| bad(MEM))?;
    let mem = match conj(&atoms) {
        None => mem_at,
        Some(h) => Thm::mp(&mem_at, &h).ok_or_else(|| bad(MEM))?,
    };

    // ── the term, under a name of mini's own ────────────────────────────────
    //
    // **At `p⃗ ++ f⃗`**, the list [`ctor_abbrevs`] abstracted over, and `p⃗` is
    // the *nest's* parameters rather than the declaration's — so the term this
    // names is the one `IndexedCtor::mem` was instantiated at through `args`
    // just above. `retarget_subject` is the check that they are one term.
    let mut fargs: Vec<Term> = ps.clone();
    fargs.extend(fields.iter().cloned());
    let unfold = derived::inst_all(&site.ctor_ax, &fargs).ok_or_else(|| bad(TERM))?;
    let term = ip.mk(site.ctor_sym, fargs.clone());
    let mem = ip.retarget_subject(&mem, &unfold).ok_or_else(|| bad(TERM))?;

    // ── the codomain: `ind(p⃗, e⃗ᵢ)` back onto `⟦T p⃗ e⃗⟧` ─────────────────────
    let goal_set = {
        let mut a: Vec<Term> = ps.clone();
        a.extend(at.result.iter().map(|(t, _)| t.clone()));
        crate::zoneb::store_spine(ip, &at.store_ty, &a)
    };
    let beta = spine_eq(ip, site, &at.store_ty, &ps, param_mems, &at.result, None)?;
    let cong = index_congr(ip, carrier.ty, &ps, &at.result, e_axs, &e_args)
        .ok_or_else(|| bad(RESULT))?;
    let onto = ip.retarget_set(&mem, &cong).ok_or_else(|| bad(SPINE))?;
    let to_spine = derived::eq_symm(&mut ip.env, &beta).ok_or_else(|| bad(SPINE))?;
    let out = ip.retarget_set(&onto, &to_spine).ok_or_else(|| bad(SPINE))?;
    if *out.concl() != Formula::mem(term.clone(), goal_set) {
        return Err(bad("the constructor did not land in its own codomain"))
    }
    Ok((term, out))
}

/// `Γ ⊢ ⟦T p⃗ x⃗⟧ = ind(p⃗, ⟦x⃗⟧)` — the type former's nest β-reduced at these
/// parameters and these index terms.
///
/// **This is where [`INDEX_TYPE`] is decided.** `beta_spine` consumes one
/// membership per level, checked against the domain that level's binder was
/// opened at, so an index expression whose inferred type is not the declared
/// index type at these arguments is refused *here* rather than producing an
/// equation about the wrong sets. When `ιₖ` is closed the two are the same term
/// and this costs nothing; when `ιₖ` mentions `x⃗<ₖ` — a shape nothing in the
/// repository builds at either end — it is a named decline.
///
/// `held` is the set the scope actually holds, when there is one: requiring the
/// equation's left-hand side to be it is the drift check the design note wanted
/// `parts_of` for, obtained from the theorem rather than from a second read.
fn spine_eq(
    ip: &mut Interp,
    site: &Site,
    former: &Term,
    ps: &[Term],
    param_mems: &[Thm],
    xs: &[(Term, Thm)],
    held: Option<&Term>,
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    // **Scope, not threading.** An index expression at a type the declaration's
    // own binder was not opened at is `ιₖ` mentioning `x⃗<ₖ` — a shape nothing
    // in the repository builds at either end, so what is missing is a witness
    // and a design decision, not a wire.
    let scope = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Scope);
    let mut a: Vec<Term> = ps.to_vec();
    let mut m: Vec<Thm> = param_mems.to_vec();
    for (t, mem) in xs {
        a.push(t.clone());
        m.push(mem.clone());
    }
    let (_, eq) = ip.beta_spine(former, &a, &m).ok_or_else(|| scope(INDEX_TYPE))?;
    if let Some(set) = held {
        let lhs = eq.concl().as_eq().map(|(l, _)| l.clone()).ok_or_else(|| bad(SPINE))?;
        if lhs != *set {
            return Err(bad(SPINE))
        }
    }
    Ok(eq)
}

/// `⊢ ind(p⃗, x⃗_syms) = ind(p⃗, ⟦x⃗⟧)` — one congruence over the carrier symbol,
/// with the parameters at reflexivity and each index at its abbreviation's own
/// defining axiom instantiated at `iargs`.
pub(crate) fn index_congr(
    ip: &mut Interp,
    ty: kernel::FnSym,
    ps: &[Term],
    xs: &[(Term, Thm)],
    axs: &[Thm],
    iargs: &[Term],
) -> Option<Thm> {
    if axs.len() != xs.len() {
        return None
    }
    let mut eqs: Vec<Thm> = ps.iter().map(|p| Thm::eq_refl(p.clone())).collect();
    for (k, (t, _)) in xs.iter().enumerate() {
        let at = derived::inst_all(&axs[k], iargs)?;
        // The axiom is `symₖ(…) = ⟦xₖ⟧`; the right-hand side must be the term
        // inference produced, or the congruence is about someone else's index.
        if at.concl().as_eq()?.1 != *t {
            return None
        }
        eqs.push(at);
    }
    derived::congr(&mut ip.env, ty, &eqs)
}

/// The right-nested conjunction of the atoms, or `None` when there are none.
fn conj(atoms: &[Thm]) -> Option<Thm> {
    atoms.iter().rev().cloned().reduce(|acc, t| derived::and_intro(&t, &acc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no_levels() -> Rc<[Level]> { Vec::new().into() }
    fn ty1() -> E { sort(Level::Zero.succ()) }

    /// The same family `zoneb`'s `indexed_env` walks — three constructors with
    /// three distinct plain/rec counts:
    ///
    /// ```text
    /// inductive B : Type    | b0 | b1
    /// inductive T (α : Type) : B → B → Type
    ///   | c0 : T α b0 b0                                    0 plain, 0 rec
    ///   | c1 : ∀ (x : B), T α x b0 → T α b1 x                1 plain, 1 rec
    ///   | c2 : ∀ (x y : B), T α x y → T α y x → T α b0 b1    2 plain, 2 rec
    /// ```
    ///
    /// `c2` is the one that matters here and its two recursive arguments have
    /// their indices **swapped** between them, so a build that reads the wrong
    /// `rec_args` row, or the wrong binder for `d⃗`, lands in a carrier at the
    /// other index and is refused rather than believed.
    fn indexed_env() -> (Environment, Name, Vec<Name>) {
        let b = nm("B");
        let bt = konst(b.clone(), no_levels());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: b.clone(),
                lparams: vec![],
                num_params: 0,
                ty: ty1(),
                ctors: vec![
                    (Name::str(&b, "b0"), bt.clone()),
                    (Name::str(&b, "b1"), bt.clone()),
                ],
            },
        )
        .expect("B is accepted");
        let b0 = konst(Name::str(&b, "b0"), no_levels());
        let b1 = konst(Name::str(&b, "b1"), no_levels());
        let t = nm("T");
        let tap = |a: E, i: E, j: E| app(app(app(konst(t.clone(), no_levels()), a), i), j);
        let ty = forall(ty1(), forall(bt.clone(), forall(bt.clone(), ty1())));
        let ctors = vec![
            (Name::str(&t, "c0"), forall(ty1(), tap(bvar(0), b0.clone(), b0.clone()))),
            (
                Name::str(&t, "c1"),
                forall(
                    ty1(),
                    forall(
                        bt.clone(),
                        forall(tap(bvar(1), bvar(0), b0.clone()), tap(bvar(2), b1.clone(), bvar(1))),
                    ),
                ),
            ),
            (
                Name::str(&t, "c2"),
                forall(
                    ty1(),
                    forall(
                        bt.clone(),
                        forall(
                            bt,
                            forall(
                                tap(bvar(2), bvar(1), bvar(0)),
                                forall(tap(bvar(3), bvar(1), bvar(2)), tap(bvar(4), b0, b1)),
                            ),
                        ),
                    ),
                ),
            ),
        ];
        let names: Vec<Name> = ctors.iter().map(|(n, _)| n.clone()).collect();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 1,
                ty,
                ctors,
            },
        )
        .expect("T is accepted");
        (env, t, names)
    }

    /// **Every constructor of an indexed family is interpreted with its
    /// typing**, and the typing is about the applied spine at that
    /// constructor's own result indices.
    ///
    /// The three assertions are the same three every zone-B build owes: the
    /// typing is unconditional, it is about the term the store holds, and the
    /// set it is about is `⟦the constructor's declared codomain⟧` — inferred,
    /// not synthesised, so a build landing in the family at *some* index would
    /// fail the third.
    ///
    /// `c2` is the one this test exists for. Its recursive arguments are
    /// `T α x y` and `T α y x`: the same two index variables in both orders, so
    /// the `d⃗ᵢⱼ` rows are positional rather than incidental, and a nest that
    /// read the wrong binder for `d⃗` — the arithmetic that reads plausibly and
    /// picks a *parameter*'s type — cannot make the membership come out.
    #[test]
    fn an_indexed_family_gets_its_constructors() {
        let (env, t, ctors) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        // The former first; the constructors are built with it, not on demand.
        c.infer_type(&konst(t.clone(), no_levels())).expect("infer ⟦T⟧");
        for n in &ctors {
            let got = c.infer_type(&konst(n.clone(), no_levels())).expect("infer");
            let tm = got
                .tm
                .clone()
                .unwrap_or_else(|| panic!("⟦{n}⟧ has no interpretation: {:?}", got.ev));
            let m = got
                .ev
                .thm()
                .unwrap_or_else(|| panic!("⟦{n}⟧ has no typing: {:?}", got.ev))
                .clone();
            assert!(m.hyps().is_empty(), "{n}: a stored typing is unconditional");
            let (subj, set) = m.concl().as_mem().expect("a membership");
            assert_eq!(subj, tm, "{n}: the typing must be about its own interpretation");
            let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
            assert_eq!(set, want, "{n}: …and about its own Lean type");
        }
    }

    /// **Non-vacuity: the three constructors are provably distinct.**
    ///
    /// Memberships alone are satisfied by a one-element carrier, so the
    /// assertion that says the nest built something is the negative one.
    /// `Inductive::distinct` is about `ctorᵢ(y⃗,r⃗)`, and mini's own
    /// abbreviations are equal to those terms by the defining equations this
    /// module mints — comparing the two `Term`s would prove nothing, since two
    /// symbols can denote one set.
    #[test]
    fn the_constructors_are_provably_distinct() {
        let (env, t, ctors) = indexed_env();
        let mut ip = Interp::new();
        {
            let mut c = Checker::threaded(&env, &mut ip);
            c.infer_type(&konst(t.clone(), no_levels())).expect("infer ⟦T⟧");
            for n in &ctors {
                c.infer_type(&konst(n.clone(), no_levels())).expect("infer");
            }
        }
        let key = (t.clone(), Vec::new());
        let base = ip
            .ind_apparatus()
            .expect("apparatus")
            .indexed
            .get(&key)
            .expect("translated")
            .base
            .clone();
        let (kenv, app, _) = ip.ind_parts().expect("apparatus");
        for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
            let d = base
                .distinct(kenv, &app.mach, i, j)
                .unwrap_or_else(|| panic!("no distinctness for ({i},{j})"));
            assert!(d.hyps().is_empty(), "distinctness must be unconditional");
        }
    }

    /// **A constructor that declines reports its reason, not its absence** —
    /// and one that nothing tried still reports absence.
    ///
    /// This is the whole of the label split. `no-interp(RBTree.leaf)` was
    /// `zoneb::stored_or_reason_after`'s **fallback**: "the constant is not in
    /// the store", which cannot be told apart from a constant no code path ever
    /// attempted, so nobody could size the work from it. C2 is what makes these
    /// constructors exist, so it is the moment to make the label distinguish
    /// the two — and both halves have to be asserted, because a change that
    /// reported the recorded reason for *everything* would look equally green.
    ///
    /// The two calls differ only in whether a reason was recorded, at one key
    /// the store misses. Planted rather than provoked: no declaration in the
    /// repository declines here today (that is what the test above says), and a
    /// decline manufactured by breaking one would be testing the break.
    ///
    /// It also pins that a constructor's decline does **not** take the type
    /// former with it — `042_rbTreeDef` is `def rbTreeDef := RBTree` and asks
    /// for the former and nothing else, so a path that returned the error
    /// upwards would have regressed a file green since the indexed carrier
    /// landed.
    #[test]
    fn a_declining_constructor_reports_its_reason_not_its_absence() {
        let (env, t, ctors) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(t.clone(), no_levels())).expect("infer ⟦T⟧");
        // The former is in the store and stays there, whatever a constructor
        // does — and every constructor is there beside it.
        assert!(c.stored_term(&t, &[]).is_some(), "the type former must survive");
        for n in &ctors {
            assert!(c.stored_term(n, &[]).is_some(), "{n} builds today");
        }

        // A key the store misses. `T` has no level parameters, so nothing is
        // ever built at `[9]` and both calls below take the miss branch.
        let miss: &[u32] = &[9];
        let c2 = ctors[2].clone();
        assert_eq!(
            crate::zoneb::stored_or_reason_after(&mut c, &c2, &t, miss, miss).unwrap_err(),
            Gap::NoInterpretation(c2.clone(), miss.to_vec()),
            "with nothing recorded, a store miss is an absence and says so"
        );
        let want = Gap::IndexedCtor(c2.clone(), INDEX_TYPE, Cause::Scope);
        {
            let app = c.interp().expect("threaded").ind_apparatus().expect("apparatus");
            app.ctor_untranslated.insert((c2.clone(), miss.to_vec()), want.clone());
        }
        assert_eq!(
            crate::zoneb::stored_or_reason_after(&mut c, &c2, &t, miss, miss).unwrap_err(),
            want,
            "with a reason recorded, the same miss must report the reason"
        );
    }
}
