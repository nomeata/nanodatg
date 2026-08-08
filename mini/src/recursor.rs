//! **The eliminator** — `⟦T.rec.{ℓ⃗}⟧` (MINI-DESIGN.md §9, zone B's last step).
//!
//! # Interface
//!
//! ```text
//! recursor::ensure(checker, T, σ_T, T.rec, σ_rec) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::zoneb::ensure`] once the declaration's carrier and
//! constructors are in the store, and from nowhere else. On success
//! `⟦T.rec.{σ_rec}⟧` and its typing are in the store under the **recursor's
//! own** instantiation, which is one level longer than the declaration's: the
//! motive's `u₁` is prepended to `T`'s parameters, so the two keys differ and
//! must not be confused.
//!
//! # The obligation, and why it is not the ι rule
//!
//! What a `(declaration, σ)` pair asks for is `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, so for a
//! recursor it is
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : T p⃗ → Sort u₁) (s⃗ : minors) (t : T p⃗). C t⟧
//! ```
//!
//! and the innermost factor of that is a **dependent** product: the motive `C`
//! is a bound variable, and the eliminator has to land in `app(C,t)` at every
//! `t` of the carrier. That is a different obligation from the one
//! `checker/src/tg.rs` discharges, which is the ι *equation* at a use site
//! where `C` has already been instantiated — and it is why
//! `RECURSOR-DESIGN.md` §11.1's dependent-motive census could close at zero on
//! `init-prelude` while the census *here* was the opposite. See §5.1 of that
//! note: the corpus's recursor files η-expand the eliminator itself
//! (`def boolRec := fun motive f t b => Bool.rec motive f t b`), so the motive
//! is never a constant. Every one of those 18 pairs is now derived or one row
//! along; [`crate::rec_dep`] is where.
//!
//! # What each declaration's eliminator waits on
//!
//! This is the register the [`Gap::Recursor`] detail strings index. Every route
//! with an occupant in the corpus is now wired; what is left is one row with
//! one occupant, and it is threading.
//!
//! | route | detail | what is missing |
//! |---|---|---|
//! | `Eq` — the thesis's own clause | — | nothing; [`eq_rec`] is it |
//! | class (T), `n ≥ 1` | — | nothing; [`crate::rec_dep`] is it |
//! | class (T), `n = 0` | — | nothing; [`empty_rec`] is it (`⟦T⟧ = 0` and `ex_falso`) |
//! | class (S), `ni = 0`, one constructor | — | nothing; [`crate::rec_prop`] is it |
//! | class (S), no constructors | [`CLASS_S_EMPTY`] | the wiring; `LeProp::false_` and ex falso |
//! | class (P), `ni = 0` | — | nothing; [`crate::rec_trunc`] is it |
//!
//! ```text
//! And.rec.{w} : ∀ (a b : Prop) (C : And a b → Sort w)
//!                 (m : ∀ (l : a) (r : b), C (And.intro l r)) (t : And a b), C t
//! ```
//!
//! ## The class-(S) row split, and why it had to
//!
//! It used to be one row holding two problems: the eliminator of a
//! subsingleton with a constructor, and the eliminator of one with none. The
//! first is [`crate::rec_prop`] and is done; the second is `¬ψ`,
//! [`LeProp::false_`](derived::inductive::family::LeProp) and ex falso, and
//! shares no step with it — no guard, no minor, no carrier point. Leaving one
//! label over both would have left `VoidProp` filed under a detail string that
//! describes a derivation it does not need, which is how `Acc` sat misfiled as
//! `indexed-family` for the life of the project and cost a planning round. A
//! label is split the moment it is known to cover two things.
//!
//! **Not [`empty_rec`]'s route, and the ordering here is what says so.**
//! `EmptyDecl::over_declaration` takes the erased W-type skeleton and requires
//! `ind.is_over(mach)`; a class-(S) declaration never builds one, because its
//! carrier is `A_φ(p⃗) ⊆ 1` held by `LeCarrier`/`LeProp`. So the class-(S) test
//! comes *before* the zero-constructor test: the carrier route decides, and the
//! eliminator must be about the carrier actually built.
//!
//! ## The dependent-motive row is closed
//!
//! It was the largest row here, and what it waited on was two `derived/`
//! constructions rather than a target policy. [`derived::inductive::guard`]
//! makes `HYP` dischargeable at a *variable* motive — the minor `HYP` quantifies
//! need not be Lean's `Sᵢ`, so it may test its own induction hypotheses —
//! and [`derived::inductive::rect`] carries the conclusion from the
//! constructors to the whole carrier. With both,
//! [`derived::inductive::DepRecursor`] *is* `GenRecursor`'s term at a particular
//! `s⃗` and `T`, and `RECURSOR-DESIGN.md` §5.3's Σ-target variant is retired.
//!
//! The wiring is [`crate::rec_dep`], and its header is where the two clauses —
//! a `Prop`-valued motive and a value-valued one — and the transport of Lean's
//! minor premises into `DEPᵢ` are described. Two things it found that the
//! design note did not have:
//!
//! * `motive::cod_at_funspace`, documented as *the* way to discharge `COD`, is
//!   not the way this wiring discharges it. It used to return `None` at every
//!   input and that is what this line used to say; it was repaired at `derived`
//!   `c2bd75f` (in **two** places, not the one every record here named) and the
//!   wiring did not change, because the reason is its statement: its hypothesis
//!   is `C ∈ fs(W,V)` and the motive is a `dprod` at a constant fibre, and its
//!   target is `⋃V ∪ {∅}`. The target premise is discharged instead at
//!   `⟦Sort u₁⟧` itself, which satisfies it because a rung of the cumulative
//!   hierarchy is transitive and holds `∅` — so the target policy is not a
//!   policy at all. [`crate::rec_dep`]'s header has both halves.
//! * The `u₁ = 0` half of the row needs no `DepRecursor`: the eliminator is a
//!   *proof*, `⟦T.rec⟧` is `•`, and the obligation is `decl_rect` at
//!   `φ(z) := • ∈ app(C,z)`.
//!
//! # Nothing here searches
//!
//! The route is chosen by [`crate::direct::clause_for`] on the declaration's
//! name — one hash comparison on the name [`crate::zoneb::ensure`] was already
//! keyed on — or, for the other three, by a **store read** on the key this
//! module was handed: `crate::class_s::of` and `IndApparatus::decls` are the
//! carrier route's own answers, not a second classification, so the eliminator
//! and the carrier cannot disagree about which clause the declaration took. As
//! in [`crate::direct`], **the name selects and the
//! derivation verifies**. [`eq_rec`] rebuilds the two sets it reasons about
//! from the nest's own binders and refuses unless the scope's minor typing and
//! the declared codomain are literally those terms, so a declaration called
//! `Eq` whose recursor is some other rule is declined with a reason rather than
//! given a typing.

use kernel::{Formula, Term, Thm};

use crate::direct::Clause;
use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::kernel::{Checker, Typing, R};

/// **A class-(S) declaration with no constructors.** ψ is the empty
/// disjunction, so `¬ψ` is immediate and
/// [`LeProp::false_`](derived::inductive::family::LeProp) gives
/// `⊢ A_φ(p⃗) = 0`; the innermost scope's `t ∈ A_φ(p⃗)` is then `t ∈ 0` and ex
/// falso types anything at all against the motive. No `guard`, no `minor`, no
/// carrier point — simpler than either the class-(T) empty route or
/// [`crate::rec_prop`], and **threading**, because `LeProp::false_` exists.
///
/// A label of its own from the moment there was a second occupant of the row:
/// while `And`, `PUnit` and `ProjDataIndex` sat here too, "class (S)
/// eliminator" named one problem; with them derived it would name a different
/// one, and a label covering two problems is how `Acc` sat misfiled as
/// `indexed-family` for the life of the project.
pub const CLASS_S_EMPTY: &str = "class (S) eliminator: no constructors";

/// Make `⟦T.rec.{σ_rec}⟧` available, or say which construction it waits on.
///
/// The declaration is already translated when this runs — `zoneb::ensure`
/// builds it first and returns before reaching here if it could not — so the
/// route below is a statement about `T`, never a retry of the carrier.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    match crate::direct::clause_for(ind_name) {
        Some(Clause::Eq) => return eq_rec(c, ind_name, ind_inst, rec_name, rec_inst),
        // **`Acc.rec` is [`crate::rec_acc`], and it is two rules.** The route
        // is named here rather than left to fall through, because every test
        // below is a *store read* on a table `Acc` is in none of — the
        // declaration takes [`crate::direct`]'s clause, so it has no `ClassS`,
        // no `TruncTranslation` and no erased W-skeleton — and the fall-through
        // is `crate::rec_dep`, which would report that a family it never
        // translated has no carrier. A label that names the wrong construction
        // is how `Acc` sat misfiled as `indexed-family` for the life of the
        // project.
        Some(Clause::Acc) => {
            return crate::rec_acc::ensure(c, ind_name, ind_inst, rec_name, rec_inst)
        }
        None => {}
    }
    // A class-(S) declaration is the one the *carrier* route already
    // identified: `crate::class_s::of` is a store read on the key this call
    // was handed, not a second classification, so the two cannot disagree.
    //
    // **The zero-constructor occupant takes its own label.** It is not
    // `empty_rec`'s: `EmptyDecl::over_declaration` wants the erased W-type
    // skeleton and `ind.is_over(mach)`, which a class-(S) declaration never
    // builds — its carrier is `A_φ(p⃗) ⊆ 1`, held by `LeCarrier`/`LeProp`. So
    // the carrier route decides, the class-(S) test comes first, and what is
    // owed here is [`CLASS_S_EMPTY`] rather than the eliminator this module
    // now wires.
    if let Some(cs) = crate::class_s::of(c, ind_name, ind_inst) {
        if cs.spec.len() != 1 {
            return Err(Gap::Recursor(*ind_name, CLASS_S_EMPTY, Cause::Threading))
        }
        return crate::rec_prop::ensure(c, ind_name, ind_inst, rec_name, rec_inst, cs)
    }
    // Class (S) **at an index** — the same store read one table along, and
    // before class (P) because `zoneb::ensure` decides the two on the
    // eliminator trichotomy and a declaration is in exactly one table.
    if let Some(cs) = crate::class_s_ix::of(c, ind_name, ind_inst) {
        return crate::rec_s_ix::ensure(c, ind_name, ind_inst, rec_name, rec_inst, cs)
    }
    // **Class (P), and before the zero-constructor test for the reason class
    // (S) is: the carrier route decides.** A `Prop` that failed Lean's
    // subsingleton test has no class-(T) carrier and never builds an erased
    // W-type skeleton, so neither `empty_rec` nor `crate::rec_dep` is about the
    // sets it was translated into. The store read is
    // `crate::zoneb::build_trunc`'s own answer, not a second classification.
    let tt = {
        let key = (*ind_name, ind_inst.to_vec());
        c.interp().and_then(|ip| ip.ind_apparatus()).and_then(|a| a.truncs.get(&key).cloned())
    };
    if let Some(tt) = tt {
        return crate::rec_trunc::ensure(c, ind_name, ind_inst, rec_name, rec_inst, tt)
    }
    // Class (P) **at an index** — the same store read one table along, and it
    // has to be *before* the fall-through rather than merely somewhere: without
    // it the route reaches `crate::rec_ix_prop`, which reads
    // `IndApparatus::indexed` and reports *the family is not translated* — a
    // class-(T) route's answer about a family that **is** translated, as class
    // (P), by [`crate::class_p_ix`].
    if let Some(cp) = crate::class_p_ix::of(c, ind_name, ind_inst) {
        return crate::rec_trunc_ix::ensure(c, ind_name, ind_inst, rec_name, rec_inst, cp)
    }
    let empty = matches!(
        c.environment().get(ind_name),
        Some(ConstantInfo::Inductive { ctors, .. }) if ctors.is_empty()
    );
    if empty {
        return empty_rec(c, ind_name, ind_inst, rec_name, rec_inst)
    }
    crate::rec_dep::ensure(c, ind_name, ind_inst, rec_name, rec_inst)
}

/// **The eliminator of a declaration with no constructors** —
/// `derived::inductive::EmptyDecl`.
///
/// `Empty.rec.{u} : ∀ (C : Empty → Sort u) (t : Empty), C t`. There are no
/// minors, so the nest is `np + 1 + 0 + 1` deep and its bottom has nothing to
/// return *from*: the obligation `⟦Empty.rec C t⟧ ∈ ⟦C t⟧` is discharged from
/// the major premise alone, because `⊢ ∀p⃗∀z. ¬(z ∈ ind(p⃗))` makes the
/// hypothesis false and `ex_falso` does the rest.
///
/// # The bottom term is `•`, and that is a choice with no content
///
/// [`EmptyDecl::anything`] proves `∀p⃗∀z. (z ∈ ind(p⃗) → φ(z))` for **the
/// caller's own `φ`**, so the interpretation of `Empty.rec C t` may be any term
/// at all; `•` is chosen because it needs nothing to build. Nothing observes
/// the choice: there are no ι rules to satisfy — a declaration with no
/// constructors has no reduction equations, which `EmptyDecl`'s header states
/// and a test there pins by asserting `GenRecursor::build` still declines — and
/// no closed term of `⟦Empty⟧` exists for a use site to reduce against.
///
/// **This is why `anything` taking the caller's `φ` matters here.** The
/// obligation is `app(f, t) ∈ app(⟦C⟧, t)` at a *dependent* motive, which is
/// `rec_typed`'s shape; but stating it as `• ∈ app(⟦C⟧, t)` avoids inventing an
/// `f` and a funspace membership to carry it, and `anything` accepts that
/// directly rather than making this site contort into the general form.
///
/// # What is read off rather than assumed
///
/// The recursor's own counts, the motive binder, and `⟦C t⟧` by inference on
/// the declared codomain — then the derived membership is compared against
/// `• ∈ ⟦C t⟧` before it is accepted. A recursor that is not of this shape
/// cannot make that comparison succeed.
fn empty_rec(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    };
    if *num_minors != 0 {
        return Err(bad("no constructors: the recursor has minors"))
    }
    if *num_indices != 0 {
        return Err(Gap::IndexedFamily(*ind_name, "an indexed recursor at a non-indexed route"))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    }
    let np = *num_params as usize;
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 2;
    let codomain =
        crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad("no constructors: arity"))?;

    let key = (*ind_name, ind_inst.to_vec());
    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.decls
            .get(&key)
            .cloned()
            .ok_or_else(|| bad("no constructors: the declaration has no carrier"))?
    };
    if !tr.ind.spec.ctors.is_empty() || tr.ind.params.len() != np {
        return Err(bad("no constructors: the recursor and the carrier disagree"))
    }
    let site = EmptySite {
        ind: *ind_name,
        inst: ind_inst.to_vec(),
        np,
        codomain,
        ind_obj: tr.ind.clone(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(empty_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// What [`empty_bottom`] needs: the declaration, its erased carrier, and the
/// codomain read off the recursor's own type.
struct EmptySite {
    ind: Name,
    inst: Vec<u32>,
    np: usize,
    codomain: E,
    ind_obj: std::rc::Rc<derived::inductive::Inductive>,
}

/// `⊢ • ∈ ⟦C t⟧`, from `t ∈ ⟦T p⃗⟧` and nothing else.
fn empty_bottom(c: &mut Checker<'_, '_>, site: &EmptySite) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let depth = site.np + 2;

    // `⟦C t⟧`, by inference on the declared codomain — the term the membership
    // has to be *about*, not one this clause synthesises.
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let (ps, param_mems) = (&xs[..site.np], &mems[..site.np]);
    let major_mem = mems[depth - 1].clone();
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let point = ip.point();

    // The scope holds `t ∈ ⟦T p⃗⟧`, the applied spine; `EmptyDecl` speaks of
    // `ind(p⃗)`. `beta_spine` is the equation between them, and it is
    // reflexivity at `np = 0` rather than absent.
    let Some((_, eq)) = ip.beta_spine(&former, ps, param_mems) else {
        return gap(bad("no constructors: the carrier spine"))
    };
    let Some(major_mem) = ip.retarget_set(&major_mem, &eq) else {
        return gap(Gap::ConvCompose("empty-rec-major"))
    };

    // `φ(z) := • ∈ app(⟦C⟧, z)` — the caller's own formula, which is the
    // whole reason `anything` takes one.
    let zv = ip.env.fresh_var();
    let motive = xs[site.np].clone();
    let at_z = ip.app(motive.clone(), Term::var(zv));
    let phi = Formula::mem(point.clone(), at_z);
    let Some((kenv, app, _)) = ip.ind_parts() else { return gap(Gap::IndApparatus) };
    let Some(ed) = derived::inductive::EmptyDecl::over_declaration(kenv, &app.mach, &site.ind_obj)
    else {
        return gap(bad("no constructors: EmptyDecl"))
    };
    let Some(any) = ed.anything(&site.ind_obj, zv, &phi) else {
        return gap(bad("no constructors: anything"))
    };

    let mut args: Vec<Term> = ps.to_vec();
    args.push(xs[depth - 1].clone());
    let ev = match derived::inst_all(&any, &args).and_then(|t| Thm::mp(&t, &major_mem)) {
        // The statement is compared against `• ∈ ⟦C t⟧`, so a rule of some
        // other shape cannot slip a true theorem about other terms through.
        Some(t) if *t.concl() == Formula::mem(point.clone(), goal.clone()) => Ev::Proved(t),
        _ => return gap(bad("no constructors: the eliminator's typing")),
    };
    Typing { ty, tm: Some(point), ev }
}

/// **`Eq`'s eliminator**, the thesis's own clause `⟦rec₌ e b h⟧ = ⟦e⟧`
/// (`INDEXED-DESIGN.md` §2.2, Carneiro §6.2).
///
/// `Eq.rec.{u₁,u} : Π (α : Sort u) (a : α) (C : Π b, Eq α a b → Sort u₁)
/// (r : C a (Eq.refl α a)) (b : α) (t : Eq α a b). C b t`, so the nest is
/// `2 + 1 + 1 + 1 + 1 = 6` deep and its bottom is the minor `r` itself. The
/// derivation is two Leibniz steps on the *one* thing `t ∈ eq_set(a,b)` says:
/// `a = b`, and `t = •` because the conditional singleton is a subset of `1`.
///
/// The nest's depth is read off the export's own
/// [`ConstantInfo::Recursor`] counts rather than hardcoded, and the two are
/// compared: a `Eq.rec` with a different number of minors or indices is a
/// different rule, and the closed form below is not about it.
fn eq_rec(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    };
    if (*num_params, *num_minors, *num_indices) != (2, 1, 1) {
        return Err(bad("Eq.rec: recursor shape"))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    }
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let codomain =
        crate::zoneb::peel(&rec_ty, EQ_DEPTH).ok_or_else(|| bad("Eq.rec: recursor arity"))?;
    let site = EqSite { ind: *ind_name, inst: ind_inst.to_vec(), codomain };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(eq_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, EQ_DEPTH, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// `α, a, C, r, b, t` — `num_params + 1 + num_minors + num_indices + 1` at
/// `Eq`'s `(2, 1, 1)`.
const EQ_DEPTH: usize = 6;

/// Which declaration `Eq.rec`'s nest is being built for, and the codomain read
/// off its type.
struct EqSite {
    ind: Name,
    inst: Vec<u32>,
    codomain: E,
}

/// The bottom of `Eq.rec`'s nest: the minor `r`, and its membership in
/// `⟦C b t⟧`.
///
/// Everything the derivation needs is already in the scope stack or in
/// [`crate::direct::Direct`]; the three things read off rather than assumed are
///
/// * `⟦C a (Eq.refl α a)⟧`, which is the *minor binder's own* scope typing;
/// * `⟦C b t⟧`, which is [`Checker::infer_type`] on the declared codomain;
/// * `⟦Eq α a b⟧`, which is `⟦Eq⟧`'s nest β-reduced at the major premise's own
///   three arguments by [`crate::interp::Interp::beta_spine`].
///
/// Each is then compared against the term this clause expects, and a mismatch
/// is a decline. That is the whole shape check: there is no separate syntactic
/// audit of `Eq.rec`, because a rule that is not `Eq.rec` cannot make these
/// three agree.
fn eq_bottom(c: &mut Checker<'_, '_>, site: &EqSite) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    // `⟦C b t⟧`, by inference on the declared codomain.
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(EQ_DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let sums = ip.prelude.tower.sums.clone();
    let point = sums.point();
    let (alpha, a, motive) = (xs[0].clone(), xs[1].clone(), xs[2].clone());
    let (refl, b, t) = (xs[3].clone(), xs[4].clone(), xs[5].clone());

    // The two motive instances, rebuilt from the binders. `⟦Eq.refl α a⟧` is
    // `•` by §6.2's proof clause, which is what puts `point` in the first.
    let at_refl = {
        let m = ip.app(motive.clone(), a.clone());
        ip.app(m, point.clone())
    };
    let at_t = {
        let m = ip.app(motive.clone(), b.clone());
        ip.app(m, t.clone())
    };
    if mems[3].concl().as_mem().map(|(_, s)| s) != Some(at_refl.clone()) {
        return gap(bad("Eq.rec: minor is not the motive at reflexivity"))
    }
    if goal != at_t {
        return gap(bad("Eq.rec: codomain is not the motive at the major premise"))
    }

    // `⟦Eq α a b⟧`, β-reduced to `eq_set(⟦a⟧,⟦b⟧)`, and the major premise's own
    // typing carried onto it. The premises `beta_spine` consumes are the three
    // arguments' scope typings, which is where a recursor whose major premise
    // is at other arguments is refused.
    let Some((carrier, spine_eq)) = ip.beta_spine(
        &former,
        &[alpha, a.clone(), b.clone()],
        &[mems[0].clone(), mems[1].clone(), mems[4].clone()],
    ) else {
        return gap(bad("Eq.rec: type former spine"))
    };
    if carrier != ip.mk(d.eq, vec![a.clone(), b.clone()]) {
        return gap(bad("Eq.rec: spine bottom"))
    }
    let Some(t_mem) = ip.retarget_set(&mems[5], &spine_eq) else {
        return gap(Gap::ConvCompose("eq-rec-major"))
    };

    // `t ∈ eq_set(a,b) → (t ∈ 1 ∧ a = b)` — the conditional singleton's own
    // defining axiom, at these very terms.
    let both = derived::inst_all(&d.eq_ax, &[a.clone(), b.clone(), t.clone()])
        .and_then(|chi| derived::iff_mp(&chi))
        .and_then(|fwd| Thm::mp(&fwd, &t_mem));
    let Some(both) = both else { return gap(Gap::ConvCompose("eq-rec-elim")) };
    let (Some(t_in_1), Some(a_eq_b)) =
        (derived::and_elim_left(&both), derived::and_elim_right(&both))
    else {
        return gap(Gap::ConvCompose("eq-rec-conjuncts"))
    };
    // `• = t`: the subset of `1` has `•` for its only element.
    let pt_eq_t = derived::inst_all(&sums.unit_eta, std::slice::from_ref(&t))
        .and_then(|r| Thm::mp(&r, &t_in_1))
        .and_then(|t_pt| derived::eq_symm(&mut ip.env, &t_pt));
    let Some(pt_eq_t) = pt_eq_t else { return gap(Gap::ConvCompose("eq-rec-unit-eta")) };

    // Two Leibniz steps, in the order the two facts arrive: `a ↦ b` in the
    // motive's first argument, then `• ↦ t` in its second.
    let x = ip.env.fresh_var();
    let phi_a = Formula::mem(refl.clone(), {
        let m = ip.app(motive.clone(), Term::var(x));
        ip.app(m, point.clone())
    });
    let at_b = Thm::mp(&Thm::eq_leibniz(a, b.clone(), x, phi_a), &a_eq_b)
        .and_then(|i| Thm::mp(&i, &mems[3]));
    let Some(at_b) = at_b else { return gap(Gap::ConvCompose("eq-rec-motive-index")) };

    let y = ip.env.fresh_var();
    let phi_pt = Formula::mem(refl.clone(), {
        let m = ip.app(motive, b);
        ip.app(m, Term::var(y))
    });
    let out = Thm::mp(&Thm::eq_leibniz(point, t, y, phi_pt), &pt_eq_t)
        .and_then(|i| Thm::mp(&i, &at_b));
    let Some(out) = out else { return gap(Gap::ConvCompose("eq-rec-proof-index")) };

    if *out.concl() != Formula::mem(refl.clone(), goal) {
        return gap(bad("Eq.rec: the minor is not about the codomain"))
    }
    Typing { ty, tm: Some(refl), ev: Ev::Proved(out) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Expr, Level};
    use crate::interp::Interp;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }

    fn level(n: u32) -> Level {
        let mut l = Level::zero();
        for _ in 0..n {
            l = l.succ();
        }
        l
    }

    /// `Eq`, as the exports declare it. `Eq.rec` is **generated** by
    /// [`crate::kernel::add`], exactly as it is on the corpus, so this test
    /// reads the same recursor type the tutorial files do rather than a
    /// hand-written imitation of it.
    fn eq_env() -> (Environment, Name, Name) {
        let (e, refl) = (nm("Eq"), Name::str(&nm("Eq"), "refl"));
        let u: Level = Level::param(nm("u"));
        let us: Rc<[Level]> = vec![u].into();
        let ty = forall(sort(u), forall(bvar(0), forall(bvar(1), sort(Level::zero()))));
        let at = |f: E, x: E, y: E, z: E| app(app(app(f, x), y), z);
        let cty =
            forall(sort(u), forall(bvar(0), at(konst(e, us), bvar(1), bvar(0), bvar(0))));
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e,
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(refl, cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, e, Name::str(&e, "rec"))
    }

    /// Replace the body under `depth` `Π` binders.
    fn with_codomain(ty: &E, depth: usize, cod: E) -> E {
        if depth == 0 {
            return cod
        }
        let Expr::Forall { ty: d, body } = &ty.view() else { panic!("fewer than {depth} binders") };
        forall(*d, with_codomain(body, depth - 1, cod))
    }

    /// **`⟦Eq.rec⟧` is interpreted with its typing**, at a `Type`-valued motive
    /// and at a `Prop`-valued one — the two branches the `λ` clause takes, the
    /// second of which is what `094_ruleK` exercises.
    ///
    /// Non-vacuity: the typing has to be about `⟦Eq.rec⟧` *itself* and to have
    /// no hypotheses, and the interpretation has to be a six-deep nest rather
    /// than the opaque symbol a decline would leave.
    #[test]
    fn eq_rec_is_interpreted_with_its_typing() {
        let (env, _, rec) = eq_env();
        for sigma in [[1u32, 1], [0, 0]] {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let at: Rc<[Level]> = sigma.iter().map(|n| level(*n)).collect::<Vec<_>>().into();
            let t = c.infer_type(&konst(rec, at)).expect("infer ⟦Eq.rec⟧");
            let m = t
                .ev
                .thm()
                .unwrap_or_else(|| panic!("⟦Eq.rec.{sigma:?}⟧ has no typing: {:?}", t.ev))
                .clone();
            assert!(m.hyps().is_empty(), "a stored typing is unconditional");
            let (subj, _) = m.concl().as_mem().expect("a membership");
            assert_eq!(
                Some(subj),
                t.tm,
                "the typing must be about ⟦Eq.rec⟧ itself, not some other term"
            );
            // Non-vacuity, and it differs by branch because the *clause*
            // differs. A `Type`-valued motive makes `⟦Eq.rec⟧` a six-deep
            // λ-graph, and every level of it has to come apart again; a
            // `Prop`-valued one makes the whole eliminator a **proof**, so
            // §6.2 gives it `•` and its type is a conditional singleton. That
            // second branch is the one `094_ruleK` takes, and asserting the
            // first there would have pinned the wrong clause.
            if sigma[0] == 0 {
                assert_eq!(
                    t.tm,
                    Some(c.interp().expect("threaded").point()),
                    "a Prop-valued motive makes Eq.rec a proof, which denotes •"
                );
            } else {
                let mut cur = t.tm.clone().expect("interpreted");
                let ip = c.interp().expect("threaded");
                for lv in 0..EQ_DEPTH {
                    let (site, _) = ip
                        .as_lam(&cur)
                        .unwrap_or_else(|| panic!("⟦Eq.rec⟧ is not a λ at level {lv}"));
                    let (skel, holes) = (site.skel.clone(), site.holes.clone());
                    let x = Term::var(ip.env.fresh_var());
                    cur = ip.rebuild(&skel, &holes, &x);
                }
            }
        }
    }

    /// **The name is not the evidence.** A declaration called `Eq` whose
    /// recursor concludes at the *reflexivity* index rather than at the major
    /// premise's — `C a (Eq.refl α a)` where Lean writes `C b t` — is a
    /// well-typed six-binder `Π` and is still declined, because the set the
    /// minor's scope typing is about and the set the codomain interprets to no
    /// longer agree.
    ///
    /// The codomain is *inferred*, so nothing about the name is trusted; this
    /// is [`crate::direct`]'s discipline at the eliminator.
    #[test]
    fn a_recursor_at_the_wrong_index_is_declined_not_believed() {
        let (mut env, e, rec) = eq_env();
        let us: Rc<[Level]> = vec![Level::param(nm("u"))].into();
        // `C a (Eq.refl α a)`, at binders `α a C r b t` = `#5 … #0`.
        let cod = app(
            app(bvar(3), bvar(4)),
            app(app(konst(Name::str(&e, "refl"), us), bvar(5)), bvar(4)),
        );
        let Some(ConstantInfo::Recursor { ty, .. }) = env.consts.get_mut(&rec) else {
            panic!("the recursor was generated")
        };
        *ty = with_codomain(&ty.clone(), EQ_DEPTH, cod);

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1), level(1)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer");
        assert_eq!(
            t.ev.gap(),
            Some(&Gap::Recursor(
                e,
                "Eq.rec: codomain is not the motive at the major premise",
                Cause::Threading
            )),
            "a recursor named Eq.rec that is not Eq's rule must be declined, with a reason \
             naming what was refused"
        );
    }

    /// **A declaration with no constructors gets its eliminator**, and its
    /// typing is about its own interpretation.
    ///
    /// This row used to be the register's last class-(T) entry, asserting the
    /// decline. `derived::inductive::EmptyDecl` closed it: the carrier is `0`,
    /// so the major premise's membership is false and `ex_falso` types any
    /// term at all against the motive. There are **no ι rules** to check
    /// alongside — a declaration with no constructors has no reduction
    /// equations — so the typing is the whole obligation.
    #[test]
    fn a_declaration_with_no_constructors_gets_its_eliminator() {
        let mut env = Environment::empty();
        let empty = nm("E");
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: empty,
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::zero().succ()),
                ctors: vec![],
            },
        )
        .expect("accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let rec = Name::str(&empty, "rec");
        let at: Rc<[Level]> = vec![Level::zero()].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer ⟦E.rec⟧");
        let tm = t.tm.clone().unwrap_or_else(|| panic!("no interpretation: {:?}", t.ev));
        let m = t.ev.thm().unwrap_or_else(|| panic!("no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "the eliminator's typing must be unconditional");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about the eliminator's own interpretation");
        // And about its own Lean type, not merely about something.
        let want = c.infer_type(&t.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…in ⟦∀ C t. C t⟧");
    }
}
