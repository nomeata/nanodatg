//! **The class-(T) eliminator at a dependent motive** — `⟦T.rec.{σ}⟧` for a
//! declaration with constructors (MINI-DESIGN.md §9, `RECURSOR-DESIGN.md` §5.3).
//!
//! # Interface
//!
//! ```text
//! rec_dep::ensure(checker, T, σ_T, T.rec, σ_rec) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] and nowhere else, on a class-(T)
//! declaration whose carrier and constructors are already in the store. On
//! success `⟦T.rec.{σ_rec}⟧` and its typing are stored under the **recursor's
//! own** instantiation.
//!
//! # The obligation, and the two clauses it comes in
//!
//! What the pair asks for is
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : T p⃗ → Sort u₁) (S⃗ : minors) (t : T p⃗). C t⟧
//! ```
//!
//! and the innermost factor is a *dependent* product: `C` is a bound variable
//! and the eliminator has to land in `app(C,t)` at every `t` of the carrier.
//! [`Checker::lam_nest`](crate::kernel::Checker::lam_nest) walks the `Π`
//! binders with the same clause dispatch `infer_type`'s `λ` arm uses, so the
//! only thing this module supplies is the **bottom**: a term and a proof of
//! `⊢ • ∈ ⟦C t⟧` or `⊢ ⟦rec⟧(t) ∈ ⟦C t⟧`.
//!
//! Which of the two is Carneiro §6.2's own split, not a case analysis of
//! mini's: `C t : Sort u₁`, so at `u₁ = 0` the eliminator is a **proof**, its
//! interpretation is `•` by the left-hand column, and the obligation is that
//! `app(C,t)` is *inhabited*. At `u₁ ≥ 1` it is a value and the obligation is
//! that a particular set-theoretic function lands in the right fibre. The same
//! split decides `lam_evidence`'s branch one level up, and `u₁` is read off the
//! recursor's own motive binder rather than off the σ list's first entry.
//!
//! | `u₁` | interpretation | what carries the bottom |
//! |---|---|---|
//! | `0` | `•` | [`derived::inductive::rect::decl_rect`] at `φ(z) := • ∈ app(C,z)` |
//! | `≥ 1` | `app(drec, ⟦t⟧)` | [`derived::inductive::DepRecursor`] |
//!
//! Neither branch is a bespoke clause for a declaration: both are stated for
//! every class-(T) declaration at once, and the *whole* of what either one
//! needs from this module is Lean's minor premises, transported from the shape
//! the interpretation gives them into the shape `derived` states them in.
//!
//! # `DEPᵢ` and `rect_stepᵢ` are the same transport, and it is not a search
//!
//! `derived`'s two premises differ in one place — the induction hypotheses and
//! the conclusion sit at `app(C,tⱼ)` and `app(C,ctorᵢ)` in `DEPᵢ`, and at the
//! caller's `φ` in `rect_stepᵢ` — and agree everywhere else: the same argument
//! order, the same `k + 2m` right-nested antecedent, and the same vanishing of
//! that antecedent at a field-free constructor. So [`minor_at`] produces both,
//! by walking the minor binder's own **interpretation**:
//!
//! * [`Interp::as_pi`](crate::interp::Interp::as_pi) says which of §6.2's three
//!   `Π` clauses built each level, and the matching application rule consumes
//!   the scope assumption the level's binder opened. Nothing is looked for: the
//!   clause is read off the term the interpretation itself recorded, and the
//!   membership is the assumption, not a lookup.
//! * The scopes are then discharged and re-instantiated at the statement's own
//!   arguments, which turns the interleaved `∀w. (w ∈ D → …)` family a binder
//!   walk produces into the flat prenex conjunction `derived` states.
//! * Three atoms have to move between a set the *interpretation* names and a
//!   set `derived` names, and each moves along an equation that was **kept**
//!   rather than re-derived: a plain field's `⟦βⱼ⟧` along
//!   [`Translated::field_abbrev`](crate::interp::Translated::field_abbrev), a
//!   recursive field's `⟦T p⃗⟧` along `Inductive::ty_ax`, and the conclusion's
//!   `⟦T.ctorᵢ p⃗ y⃗ t⃗⟧` along
//!   [`Translated::ctor_abbrev`](crate::interp::Translated::ctor_abbrev)
//!   composed with `beta_spine`. Dropping any of the three would leave a fact
//!   that can only be recovered by re-minting the symbol it is about, which is
//!   why they are memoised with the declaration.
//!
//! What comes out is then **compared against the statement `derived` rebuilds**
//! — `motive::dep_minor`'s conjunct and `rect::rect_step` — at mini's own
//! terms. A transport that produced something else is declined with a reason,
//! never handed on.
//!
//! # A **function-typed** recursive slot: the binder crosses, not the atom
//!
//! Lean's minor premise binds a field `γ → T p⃗` at `dprod(b, ⟦γ⟧)`, §12's
//! one-clause `Π` at a constant fibre. `rect_step` and `dep_minor` bind the
//! same slot at `fs(Aⱼ, W)` over the **fibre summand** `Aⱼ = Σ(z::γ)` — a set
//! of *tuples*, because that is what the carrier's own `W`-encoding sums. The
//! two are functions on different domains and no equation relates them; what
//! relates them is `derived::sigma`'s pair of operators, `pull` one way and
//! `push` the other.
//!
//! The **constructor** crossed this seam with `pull` (`zoneb::rec_slot_terms`),
//! so `⟦T.ctorᵢ f⟧` is `ctorᵢ(pull(⟦f⟧, T(p⃗)))`. A minor premise is the mirror:
//! it *quantifies* the `fs(Aⱼ,W)` side, so [`minor_at`] opens that slot's scope
//! at `derived`'s set and hands the interpretation `push(t, β₀(p⃗))`. Three
//! things follow, and each is one function:
//!
//! * [`push_into_pi`] — `t ∈ fs(Aⱼ,W)` to `push(t,β₀(p⃗)) ∈ ⟦γ → T p⃗⟧`, which
//!   is §33's four rewrites run backwards over `sigma::push_in_funspace`;
//! * [`ctor_at_binders`] — the walk lands at `ctorᵢ(pull(push(t,β₀),T(p⃗)))` and
//!   the obligation names `ctorᵢ(t)`, which is `sigma::push_pull_roundtrip`;
//! * [`ih_transport`] — `derived` states the induction hypothesis as a
//!   *pointwise family* over `Aⱼ` and the minor binds one element of a `Π` over
//!   `⟦γ⟧`. That is a λ-introduction, not a rewrite, which is why [`at_atom`]
//!   has a third mode and not a third equation.
//!
//! **The `u₁ ≥ 1` clause does not cross**, and the reason is a statement rather
//! than a wiring: `dep_minor` *applies* the minor premise to the constructor
//! term's own argument. See [`MINOR_GRAIN`].
//!
//! # `COD` is discharged at the sort the motive lands in, and costs two rung
//! facts
//!
//! `DepRecursor`'s premise is `COD ∧ DEP`, and `COD(C,T)` says only that `T`
//! holds every *element of* every value of the motive, and holds `∅`. Nothing
//! about closure, so the target is free — and `⟦Sort u₁⟧` already satisfies it,
//! because a rung of the cumulative hierarchy is **transitive** and contains
//! `∅` ([`derived::tower::Rung::transitive`], [`derived::tower::Rung::empty_mem`]).
//! `app(C,x) ∈ ⟦Sort u₁⟧` is one `fs_app` off the motive binder's own scope
//! typing, and transitivity turns that into `y ∈ app(C,x) → y ∈ ⟦Sort u₁⟧`. Two
//! [`Scopes`] discharge it into `COD`'s own `∀`/`→` shape, which is the shape
//! `crate::scope` produces and the reason it produces that shape.
//!
//! So there is no `⋃V ∪ {∅}` here and no target *policy* left to state: the
//! target is the sort the motive was declared into. `RECURSOR-DESIGN.md` §5.2's
//! three-way choice existed because the target had to make `minor_typedᵢ` true;
//! [`derived::inductive::guard`] removed that, and what is left is satisfied by
//! the one set the declaration already names.
//!
//! **[`derived::inductive::motive::cod_at_funspace`] is *not* used, and the
//! reason is its statement rather than its health.** It works — it returned
//! `None` at every input until `derived` `c2bd75f`, and this paragraph used to
//! say so and stop there, which left "not used" and "dead" as one sentence that
//! could only come apart the day it was repaired. They are two facts:
//!
//! * **Repaired, in two places and not one.** The recorded cause — `k` is
//!   `h ∧ (mx ∧ my)` while the two `gen_under`s want `(h ∧ mx) ∧ my`, so
//!   `Thm::ax_dist` never matches `Thm::gen`'s output — was real and not
//!   sufficient: the union injection was also lifted under `k` with `a1i`
//!   before `syl`, which wants it bare. **Either alone fires the `?`**, so
//!   applying the fix as recorded would have measured it still dead with
//!   nothing pointing further.
//! * **Still not this route's discharge**, for two reasons visible in the
//!   statement `⊢ ∀C ∀V. (C ∈ fs(W,V) → COD(C, ⋃V ∪ {∅}))`. Its hypothesis is
//!   a *function-space* membership, and what this module holds is [`Cx`]'s
//!   `⟦C⟧ ∈ dprod(⟦Sort u₁⟧, W)` at a constant fibre — `SCOPING.md` §10 took
//!   the `fs` clause out of `⟦Π⟧`, so reaching it costs
//!   `derived::ext::dprod_const_fibre_n`. *(That theorem was called "stored
//!   and unread" here and in three other places, and it was neither by the
//!   time the sentence was written: `crate::quot_classes::lift_at` has read it
//!   since `9edf304`. It is now [`crate::interp::Interp::dprod_is_fs`], one
//!   call, and the constructor's nest bottom is its third consumer. **This
//!   bullet's force is unchanged and its cost estimate is wrong in the cheap
//!   direction**: the bridge is a method call now, so what still keeps this
//!   route off `cod_at_funspace` is the second bullet alone.)* And it discharges
//!   at `⋃V ∪ {∅}`, not at the sort the motive was declared into, which is
//!   what this route instantiates `DepRecursor::target` at.
//!
//! [`cod_at_rung`] needs neither: two rung facts and the motive's own
//! application rule. `cod_at_funspace_is_stated_at_a_function_space_and_at_
//! another_target` pins both halves — that it is `Some`, and that its
//! hypothesis and its target are not the ones in hand — where the old test
//! pinned only `is_none()`.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::rect::{decl_rect, rect_parts};
use derived::inductive::{Inductive, Slot};

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Expr, Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape, Translated};
use crate::kernel::{Checker, Typing, R};
use crate::scope::Scopes;

/// Make `⟦T.rec.{σ_rec}⟧` available for a class-(T) declaration with
/// constructors, or say what the wiring could not transport.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
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
    let (np, n) = (*num_params as usize, *num_minors as usize);
    // **The indexed eliminator, and it is two constructions, not one.**
    //
    // This used to be `Gap::IndexedFamily`, the same label the *carrier*
    // decline carries — so `042`'s "the family is not translated" and `068`'s
    // "the family is translated and its eliminator is not" read identically,
    // and after `crate::ctor_ix` the first of those is no longer true of
    // `RBTree` at all. Worse, the two halves of what is left are different
    // constructions, and §6.2's own split decides which: `C x⃗ t : Sort u₁`, so
    // at `u₁ = 0` the eliminator is a **proof**, `⟦T.rec⟧` is `•`, and what
    // carries it is `IndexedPropRecursor` over `IndexedCtor::inv`
    // (`INDEXED-DESIGN.md` §5.3) — that is `crate::rec_ix_prop`. At `u₁ ≥ 1` it
    // is a value at a possibly family-valued motive, which is §5.2's `T`-policy
    // branch: a mini-side recogniser, so **threading**, and still owed.
    //
    // **Splitting the label was worth a row on its own, before either half was
    // built.** The `Prop` row read 2 and only 1 of it was the `Prop` clause:
    // `077` uses `RBTree.rec` at both motive sorts and reported whichever it
    // met first, so closing this half moved that pair *across* the axis rather
    // than off the ledger. A rolled-up `indexed eliminator` row would have
    // shown 4 → 3 and said nothing about which construction was owed.
    //
    // The level is read off the recursor's own motive binder, exactly as the
    // non-indexed clause below reads it, and a recursor whose motive is not a
    // family of sorts is not either rule and says so.
    if *num_indices != 0 {
        let ni = *num_indices as usize;
        let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
        return match motive_level(&rec_ty, np, ni) {
            Some(0) => crate::rec_ix_prop::ensure(
                c, ind_name, ind_inst, rec_name, rec_inst, np, n, ni, &rec_ty,
            ),
            Some(_) => crate::rec_ix_dep::ensure(
                c, ind_name, ind_inst, rec_name, rec_inst, np, n, ni, &rec_ty,
            ),
            None => Err(bad("indexed eliminator: the motive's binder is not a Lean motive")),
        }
    }
    let ctors = match env.get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) => ctors.clone(),
        _ => return Err(Gap::NoInterpretation(ind_name.clone(), ind_inst.to_vec())),
    };
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 1 + n + 1;
    let codomain =
        crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad("dependent recursor: arity"))?;
    let u1 = motive_level(&rec_ty, np, 0)
        .ok_or_else(|| bad("dependent recursor: the motive's binder is not a Lean motive"))?;

    let key = (ind_name.clone(), ind_inst.to_vec());
    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.decls
            .get(&key)
            .cloned()
            .ok_or_else(|| bad("dependent recursor: the declaration has no class-(T) carrier"))?
    };
    if tr.ind.spec.ctors.len() != n || tr.ind.params.len() != np || ctors.len() != n {
        return Err(bad("dependent recursor: the recursor and the carrier disagree"))
    }

    let site = Site {
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        rec: rec_name.clone(),
        rec_inst: rec_inst.to_vec(),
        ctors,
        np,
        n,
        depth,
        codomain,
        u1,
        tr,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

// **The value-motive row's history is `INDEXED-DESIGN.md` §5.1 and
// `crate::rec_ix_dep`'s header, not a constant here.** There used to be an
// `INDEXED_VALUE` reason string carrying the argument that the row was a
// library gap rather than the threading one it had been filed as; the row
// closed and the string stopped being emitted, and a reason nothing produces is
// a trap for the next reader who greps for it. The argument is kept where it is
// still true.
/// `u₁`, read off the recursor's **own** type: the motive binder is
/// `C : Π (_ : T p⃗). Sort u₁`, and this is that `Sort`'s ground numeral.
///
/// Not `rec_inst[0]`. The motive's level is prepended to the declaration's by
/// Lean's own generator, but a recursor whose motive is not a `T p⃗`-indexed
/// family of sorts is not this rule, and reading the type is what says so.
///
/// Shared with [`crate::rec_prop`], which asks the same question of a class-(S)
/// recursor, and with the indexed decline above: the motive binder is the same
/// binder and §6.2's split on `u₁` is the same split, so a second reader would
/// be a second chance to disagree.
pub(crate) fn motive_level(rec_ty: &E, np: usize, ni: usize) -> Option<u32> {
    let after = crate::zoneb::peel(rec_ty, np)?;
    let Expr::Forall { ty: motive, .. } = &*after else { return None };
    // **`ni + 1`, not one.** An indexed family's motive is
    // `C : ∀ x⃗ (t : T p⃗ x⃗). Sort u₁`, so the `Sort` sits under the index
    // binders as well as the major premise's. Reading only one binder deep
    // returns `None` at every indexed recursor — which is not "this is not a
    // Lean motive", it is this function not knowing about indices, and it
    // reported the first as the second until `RBTree` was asked.
    let inner = crate::zoneb::peel(motive, ni + 1)?;
    let Expr::Sort(l) = &*inner else { return None };
    ground::eval(l, &Default::default())
}

/// Which eliminator is being built, and everything read off the declaration
/// before a binder is opened.
///
/// **Shared with the use site.** [`crate::iota_dep`] fills the same struct from
/// the arguments `whnf` holds on its stack, because [`minor_at`] and
/// [`cod_at_rung`] are parameterised over *terms and memberships*, not over
/// nest positions — see this module's header and `MINI-HANDOFF.md` §8. The one
/// field neither of them reads is [`Site::codomain`], which is the nest's own.
pub(crate) struct Site {
    pub(crate) ind: Name,
    pub(crate) inst: Vec<u32>,
    /// The eliminator's own name and instantiation — the key
    /// [`crate::interp::IndApparatus::dep_elims`] stores the nest bottom's
    /// abbreviation under, because `drec`'s target is `⟦Sort u₁⟧` and `u₁` is
    /// the recursor's, not the declaration's.
    pub(crate) rec: Name,
    pub(crate) rec_inst: Vec<u32>,
    /// The constructors' names, in declaration order.
    pub(crate) ctors: Vec<Name>,
    pub(crate) np: usize,
    pub(crate) n: usize,
    /// `np + 1 + n + 1` — parameters, motive, minors, major premise.
    pub(crate) depth: usize,
    /// `C t`, the recursor type's codomain under all `depth` binders. Read only
    /// by [`rec_bottom`]; a use site fills it from the same
    /// [`crate::zoneb::peel`] and nothing it calls looks at it.
    pub(crate) codomain: E,
    /// The motive's resultant sort; `0` is the proof clause.
    pub(crate) u1: u32,
    pub(crate) tr: Rc<Translated>,
}

/// The bottom of `⟦T.rec⟧`'s nest.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort, once from the codomain the nest actually reached.
    let prop = match c.is_prop(&site.codomain) {
        Ok(b) => b,
        Err(_) => return gap(Gap::Classifier),
    };
    if prop != (site.u1 == 0) {
        return gap(bad("dependent recursor: the motive's sort and its codomain disagree"))
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(vars) = c.scope_vars(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let mut ctor_formers = Vec::with_capacity(site.n);
    for name in &site.ctors {
        match c.stored_term(name, &site.inst) {
            Some(t) => ctor_formers.push(t),
            None => return gap(Gap::NoEndpoint),
        }
    }
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let at = At { xs, mems, vars, former, ctor_formers, goal, prop };
    match build(ip, site, &at) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// What the nest's own scopes hold at the bottom, plus the store reads.
///
/// **Nothing here is a nest position.** `xs` are terms and `mems` are
/// memberships *at the domains the interpretation names*, which is what a λ
/// binder's scope assumption is and equally what
/// [`Checker::nest_arg_mems`](crate::kernel::Checker::nest_arg_mems) produces
/// for an arbitrary argument. That is the whole reason [`crate::iota_dep`] can
/// reuse [`cx_of`], [`minor_at`] and [`cod_at_rung`] verbatim.
pub(crate) struct At {
    /// `⟦p⃗⟧, ⟦C⟧, ⟦S⃗⟧, ⟦t⟧`, outermost first.
    pub(crate) xs: Vec<Term>,
    /// Their scope typings, in the same order.
    pub(crate) mems: Vec<Thm>,
    /// Their kernel variables, in the same order. **Empty at a use site**: the
    /// arguments are terms, not variables, and the only reader is
    /// [`dep_bottom`]'s `define_abbrev`.
    pub(crate) vars: Vec<FreeVar>,
    pub(crate) former: Term,
    pub(crate) ctor_formers: Vec<Term>,
    /// `⟦C t⟧`, the set the bottom's membership must be about.
    pub(crate) goal: Term,
    pub(crate) prop: bool,
}

/// The bottom's term and typing, or the transport that did not fit.
fn build(ip: &mut Interp, site: &Site, at: &At) -> Result<(Term, Thm), Gap> {
    let cx = cx_of(ip, site, at)?;
    if at.prop {
        prop_bottom(ip, site, at, &cx)
    } else {
        dep_bottom(ip, site, at, &cx)
    }
}

/// The carrier equations and the binders split by role — everything both
/// clauses need before either one starts.
///
/// Split out of [`build`] so that a **use site** can have it: every input is a
/// term or a membership, so `whnf` can supply them from its own stack and this
/// function does not know the difference.
pub(crate) fn cx_of(ip: &mut Interp, site: &Site, at: &At) -> Result<Cx, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let (np, n, depth) = (site.np, site.n, site.depth);
    let ind = site.tr.ind.clone();
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();

    let ps = at.xs[..np].to_vec();
    let param_mems = at.mems[..np].to_vec();
    let c_tm = at.xs[np].clone();
    let c_mem = at.mems[np].clone();
    let s_tms = at.xs[np + 1..np + 1 + n].to_vec();
    let s_mems = at.mems[np + 1..np + 1 + n].to_vec();
    let t_tm = at.xs[depth - 1].clone();
    let t_mem = at.mems[depth - 1].clone();

    // ── the carrier, and the one equation everything downstream travels on ──
    let (carrier, spine_eq) =
        ip.beta_spine(&at.former, &ps, &param_mems).ok_or_else(|| bad(SPINE))?;
    if carrier != ip.mk(ind.ty, ps.clone()) {
        return Err(bad(SPINE))
    }
    let ty_at = derived::inst_all(&ind.ty_ax, &ps).ok_or_else(|| bad(CARRIER))?;
    let w_eq = eq_trans(ip, &spine_eq, &ty_at).ok_or_else(|| bad(CARRIER))?;
    let (spine, w_term) = w_eq.concl().as_eq().ok_or_else(|| bad(CARRIER))?;
    let t_in_w = ip.retarget_set(&t_mem, &w_eq).ok_or_else(|| bad(CARRIER))?;
    if at.goal != ap.apply(c_tm.clone(), t_tm.clone()) {
        return Err(bad("dependent recursor: the codomain is not the motive at the major premise"))
    }
    let psub: Vec<(FreeVar, Term)> =
        ind.params.iter().copied().zip(ps.iter().cloned()).collect();

    // **The motive is a function into `⟦Sort u₁⟧`, and this is where that is
    // read off rather than assumed.** `C : T p⃗ → Sort u₁` is binder-free in its
    // codomain and `Sort u₁` lives in `Sort (u₁+1)`, never in `Prop`, so §6.2's
    // `Π` clause for it is the **dependent product at the constant fibre** at
    // every `u₁`, including `0`. One Leibniz moves the domain from the applied
    // spine to the raw carrier — and the domain is still an *argument slot* of
    // a shared symbol, which is the property that makes that one step.
    //
    // *(Rewritten at the `fs`-clause removal. This read `s.fs.of(spine, v_set)`
    // and `fs` was right for as long as `⟦Π⟧` had a binder-free clause. The
    // sentence is the same sentence, one symbol along; `SCOPING.md` §10
    // predicted it in all four routes and this is the first.)*
    let v_set = ip.sort(site.u1);
    let set = c_mem.concl().as_mem().ok_or_else(|| bad(MOTIVE_TY))?.1;
    let c_fibre = ip.const_fibre_site(&v_set).ok_or_else(|| bad(MOTIVE_TY))?;
    if set != ip.dprod_term(&c_fibre, spine.clone()) {
        return Err(bad(MOTIVE_TY))
    }
    let hole = ip.env.fresh_var();
    let at_hole = ip.dprod_term(&c_fibre, Term::var(hole));
    let leib = Thm::eq_leibniz(
        spine.clone(),
        w_term.clone(),
        hole,
        Formula::mem(c_tm.clone(), at_hole),
    );
    let c_in_fs = Thm::mp(&leib, &w_eq)
        .and_then(|t| Thm::mp(&t, &c_mem))
        .ok_or_else(|| bad(MOTIVE_TY))?;

    Ok(Cx {
        ind,
        ps,
        param_mems,
        c_tm,
        s_tms,
        s_mems,
        t_tm,
        t_in_w,
        w_term,
        w_eq,
        psub,
        v_set,
        c_in_fs,
        c_fibre,
    })
}

/// The bottom's working context: the binders split by role, and the carrier
/// equations, all at mini's own terms.
pub(crate) struct Cx {
    pub(crate) ind: Rc<Inductive>,
    pub(crate) ps: Vec<Term>,
    pub(crate) param_mems: Vec<Thm>,
    pub(crate) c_tm: Term,
    pub(crate) s_tms: Vec<Term>,
    pub(crate) s_mems: Vec<Thm>,
    pub(crate) t_tm: Term,
    /// `Γ ⊢ ⟦t⟧ ∈ W`.
    pub(crate) t_in_w: Thm,
    /// `W`, the raw carrier at `⟦p⃗⟧`.
    pub(crate) w_term: Term,
    /// `Γ ⊢ ⟦T p⃗⟧ = W`.
    pub(crate) w_eq: Thm,
    /// The declaration's parameter variables at `⟦p⃗⟧`.
    pub(crate) psub: Vec<(FreeVar, Term)>,
    /// `⟦Sort u₁⟧`, the set the motive is a function into.
    pub(crate) v_set: Term,
    /// `Γ ⊢ ⟦C⟧ ∈ dprod(⟦Sort u₁⟧, W)` — the motive as a dependent product at
    /// the **constant** fibre, which is what `⟦T p⃗ → Sort u₁⟧` is now that
    /// §6.2's `Π` has one value clause (`SCOPING.md` §10). The name is kept:
    /// it is still "the motive is a function into `⟦Sort u₁⟧`", and renaming a
    /// field in four routes would obscure that the *sentence* did not change.
    pub(crate) c_in_fs: Thm,
    /// The constant fibre's site, so a consumer can *apply* the motive as well
    /// as name its type — `dprod_app` where this used to call `fs_app`.
    pub(crate) c_fibre: crate::interp::FibreSite,
}

const SPINE: &str = "dependent recursor: the type former's spine";
const CARRIER: &str = "dependent recursor: the carrier equation";
const MINOR: &str = "dependent recursor: a minor premise does not transport";
/// **The dependent clause's own crossing, and it is not a threading gap.**
///
/// `derived`'s `DEPᵢ` applies the minor premise to the *constructor term's*
/// argument — `app(app(Sᵢ, t), v)` with `t ∈ fs(Aⱼ, W)` — while `⟦Sᵢ⟧` is a
/// function on `⟦γ → T p⃗⟧ = dprod(b,⟦γ⟧)`. The two are functions on **disjoint
/// domains** (`Aⱼ = Σ(z::γ)` is a set of pairs, `⟦γ⟧` is not), so `DEPᵢ` at
/// `su := ⟦Sᵢ⟧` is not merely unproved here; it is false at a general motive.
///
/// `push` closes the slot's *typing* seam and [`prop_bottom`] is through on it.
/// What the `u₁ ≥ 1` clause needs in addition is that `derived` state the
/// applied minor at `push(tⱼ, β₀(p⃗))` and `push(vⱼ, β₀(p⃗))` — its own
/// vocabulary, and exactly what `sigma::push` was built for. **No term mini
/// can pass as `su` fixes it**: the ih binder `vⱼ` carries no set typing in
/// `dep_minor`, only the pointwise family, and the `vⱼ` satisfying it are not
/// contained in any set, so no graph is defined at all of them.
const MINOR_GRAIN: &str =
    "dependent recursor: derived's DEP applies the minor at the constructor's grain";
/// A **mixed** constructor's plain recursive slot: `derived::point_fun` at
/// `a := •`, and no corpus witness. See [`general_slot_declines`].
const MIXED: &str = "dependent recursor: a mixed constructor's plain recursive slot";

/// **What constructor `i`'s minor premise needs at each recursive slot beyond
/// what the plain walk does** — `None` when nothing, `Some(reason)` when the
/// crossing is one this file has not built.
///
/// Lean's minor premise binds a function-typed recursive field at
/// `⟦γ → T p⃗⟧`, which §12's one-clause `Π` makes `dprod(b, ⟦γ⟧)` at a constant
/// fibre. [`rect_step`](derived::inductive::rect::rect_step) and
/// [`dep_minor`](derived::inductive::motive::dep_minor) bind it at
/// `fs(Aⱼ, W)` over the **fibre summand** `Aⱼ = Σ(z::γⱼ)`, a set of tuples —
/// `Inductive::ctor_slot_domains` is the grain, and it is `Some` at *every*
/// slot of a constructor that takes `RecArg::general`, including a mixed one's
/// plain slot, because that choice is made per constructor.
///
/// The **binder** is what crosses, not the atom: [`minor_at`] opens the slot's
/// scope at `derived`'s `fs(Aⱼ,W)` and hands the interpretation the *pushed*
/// function `push(t, β₀(p⃗))`, over `derived::sigma::push_in_funspace` and
/// `derived::sigma::push_pull_roundtrip`. What still declines here is a shape
/// no cell of the corpus contains and one whose obligation `derived` states at
/// a grain no interpreted minor premise can meet:
///
/// * a **mixed** constructor's plain slot ([`MIXED`]) — `ctor_slot_domains` is
///   `Some(1)` there while `rec_slot_domains` is `None`, so the field the minor
///   premise binds is a carrier element and the constructor's own argument is a
///   function out of `1`. `derived::point_fun` is the step and nothing on the
///   corpus reaches it.
///
/// **`γ` at depth `≥ 2` is not one of them**, and the reason is measured rather
/// than argued: a currying is refused two constructions earlier, at
/// `Gap::IndSpec(T, "recursive argument telescope depth")`, so a guard for it
/// here would be a branch nothing can take. `derived::sigma`'s own depth-one
/// guard on both operators is the second line of defence and is never reached.
/// The frontier test's `T.e` row asserts the *earlier* refusal by name, so a
/// successor lifting it sees this cell go red rather than silently pass.
fn general_slot_declines(ind: &Inductive, i: usize) -> Option<&'static str> {
    let (cd, rd) = (ind.ctor_slot_domains(i), ind.rec_slot_domains(i));
    if cd.len() != rd.len() {
        return Some(MIXED)
    }
    for j in 0..cd.len() {
        if cd[j].is_none() {
            continue
        }
        if rd[j].is_none() {
            return Some(MIXED)
        }
    }
    None
}

/// **The crossing at one function-typed recursive slot** — every term and
/// theorem the walk, the constructor spine and the induction hypothesis share,
/// minted once so that the `push` the scope opens with is the `push` the round
/// trip closes over.
struct Crossing {
    /// `Aⱼ = T(p⃗)`, the fibre summand — the set `rect_step` binds the slot at.
    a: Term,
    /// `β₀(p⃗)`, the telescope's argument type.
    beta0: Term,
    /// `⟦γ⟧`, the interpretation of the same type.
    gamma: Term,
    /// `⊢ β₀(p⃗) = ⟦γ⟧` — `crate::zoneb::CtorEvidence::rec_dom_abbrev` at `p⃗`.
    gamma_ax: Thm,
    /// `⊢ ∀S ∀t. (t ∈ fs(T(p⃗),S) → push(t,β₀(p⃗)) ∈ fs(β₀(p⃗),S))`, at `p⃗`.
    in_funspace: Thm,
    /// `⊢ ∀S ∀t. (t ∈ fs(T(p⃗),S) → pull(push(t,β₀(p⃗)),T(p⃗)) = t)`, at `p⃗`.
    roundtrip: Thm,
    px: Rc<derived::sigma::Push>,
    rx: Rc<derived::sigma::Reindex>,
    tel: Rc<derived::sigma::Telescope>,
}

impl Crossing {
    /// `push(t, β₀(p⃗))` — the interpretation's own function, from the minor
    /// premise's binder.
    fn pushed(&self, t: &Term) -> Term { self.px.of(t.clone(), self.beta0.clone()) }

    /// `pull(push(t, β₀(p⃗)), T(p⃗))` — what `crate::zoneb::rec_slot_terms` put
    /// in the constructor term, at the pushed function.
    fn pulled(&self, t: &Term, ps: &[Term]) -> Term {
        self.rx.of(self.pushed(t), self.tel.ty_of(ps.to_vec()))
    }
}

/// The crossing at every recursive slot of constructor `i`, `None` at a plain
/// one.
///
/// Both keyed theorems are built here rather than per level, because both are
/// keyed by the [`Telescope`](derived::sigma::Telescope) and a second build
/// would be a second one.
fn crossings(ip: &mut Interp, site: &Site, cx: &Cx, i: usize) -> Option<Vec<Option<Crossing>>> {
    let cd = cx.ind.ctor_slot_domains(i);
    let ctor = cx.ind.spec.ctors.get(i)?.clone();
    let mut out = Vec::with_capacity(cd.len());
    for (j, dom) in cd.iter().enumerate() {
        let Some(a) = dom.clone() else {
            out.push(None);
            continue
        };
        // `⊢ ∀p⃗. (γ(p⃗) = ⟦γ⟧)`, kept by the boundary walk and nowhere else.
        let gamma_ax = derived::inst_all(
            site.tr.rec_dom_abbrev.get(i)?.get(j)?.first()?,
            &cx.ps,
        )?;
        let gamma = gamma_ax.concl().as_eq()?.1.clone();
        let g: Vec<kernel::FnSym> = ctor.rec_dom(j).to_vec();
        let s = ip.prelude.tower.sums.clone();
        let fs_app_mem = ip.prelude.fs_app_mem.clone();
        let fun_ext = crate::conv::funspace_ext(ip)?;
        let ps = cx.ps.clone();
        let (tel, px, rx, in_funspace, roundtrip) = {
            let (kenv, app, _) = ip.ind_parts()?;
            let tel = app.mach.telescope(kenv, ps.len(), &g)?;
            let px = app.push(kenv)?;
            let rx = app.reindex(kenv)?;
            // The slot's stated set really is *this* telescope's — the one
            // whose `push` the walk is about to open a scope with, not a
            // second one of the same shape.
            if a != tel.ty_of(ps.clone()) {
                return None
            }
            let inf = derived::sigma::push_in_funspace(kenv, &s, &tel, &px, &fs_app_mem)?;
            let rt = derived::sigma::push_pull_roundtrip(
                kenv,
                &s,
                &app.mach.proj,
                &tel,
                &rx,
                &px,
                &fs_app_mem,
                &fun_ext,
            )?;
            (tel, px, rx, inf, rt)
        };
        let in_funspace = derived::inst_all(&in_funspace, &cx.ps)?;
        let roundtrip = derived::inst_all(&roundtrip, &cx.ps)?;
        let beta0 = Term::apply(*tel.betas.first()?, cx.ps.clone());
        if gamma_ax.concl().as_eq()?.0 != beta0 {
            return None
        }
        out.push(Some(Crossing {
            a,
            beta0,
            gamma,
            gamma_ax,
            in_funspace,
            roundtrip,
            px,
            rx,
            tel,
        }));
    }
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// `u₁ = 0` — the eliminator is a proof, and the obligation is inhabitation
// ─────────────────────────────────────────────────────────────────────────────

/// `⟦T.rec.{0,σ}⟧ = •`, with `• ∈ ⟦C t⟧` by structural induction.
///
/// No recursor term and no target: at a `Prop`-valued motive `app(C,z)` is a
/// truth value, every element of it is `•`, and what has to be shown is that it
/// has one. That is [`decl_rect`] at `φ(z) := • ∈ app(C,z)` — and each
/// induction step *is* Lean's minor premise applied to its own arguments, with
/// the induction hypotheses supplying the `•`s the conditional-singleton
/// application rule consumes.
fn prop_bottom(ip: &mut Interp, site: &Site, at: &At, cx: &Cx) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let s = ip.prelude.tower.sums.clone();
    let point = ip.point();

    let zv = ip.env.fresh_var();
    let phi = Formula::mem(point.clone(), s.ap.apply(cx.c_tm.clone(), Term::var(zv)));
    let (rule, parts) = {
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let rule = decl_rect(kenv, &app.mach, &cx.ind, zv, &phi)
            .ok_or_else(|| bad("dependent recursor: structural induction"))?;
        let parts = rect_parts(kenv, &app.mach, &cx.ind, zv, &phi)
            .ok_or_else(|| bad("dependent recursor: structural induction"))?;
        (rule, parts)
    };
    // `decl_rect` is stated at the declaration's own parameter variables; the
    // whole bottom lives at `⟦p⃗⟧`.
    let rule = gen_all_checked(&cx.ind.params, &rule).ok_or_else(|| bad(CARRIER))?;
    let rule = derived::inst_all(&rule, &cx.ps).ok_or_else(|| bad(CARRIER))?;

    let mut steps = Vec::with_capacity(site.n);
    for (i, part) in parts.iter().enumerate().take(site.n) {
        if let Some(why) = general_slot_declines(&cx.ind, i) {
            return Err(Gap::Recursor(site.ind.clone(), why, Cause::Library))
        }
        let got = minor_at(ip, site, cx, at, i, true).ok_or_else(|| bad(MINOR))?;
        let want = subst_f(part, &cx.psub);
        if *got.concl() != want {
            return Err(bad(MINOR))
        }
        steps.push(got);
    }
    let all = steps
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("dependent recursor: a declaration with no constructors"))?;
    let over = Thm::mp(&rule, &all).ok_or_else(|| bad(MINOR))?;
    let at_t = derived::inst_all(&over, std::slice::from_ref(&cx.t_tm))
        .ok_or_else(|| bad(CARRIER))?;
    let mem = Thm::mp(&at_t, &cx.t_in_w).ok_or_else(|| bad(CARRIER))?;
    if *mem.concl() != Formula::mem(point.clone(), at.goal.clone()) {
        return Err(bad("dependent recursor: the proof clause did not land in the codomain"))
    }
    Ok((point, mem))
}

// ─────────────────────────────────────────────────────────────────────────────
// `u₁ ≥ 1` — the eliminator is a value
// ─────────────────────────────────────────────────────────────────────────────

/// **`PRE = COD(⟦C⟧,⟦Sort u₁⟧) ∧ DEP(⟦C⟧,⟦S⃗⟧)`**, at whatever motive and
/// minors the caller has — together with the eliminator it belongs to and the
/// substitution that carries `derived`'s variables onto the caller's terms.
///
/// # Why this is a function and not four lines inside [`dep_bottom`]
///
/// `PRE` is a fact about the *minors*, which at a use site are arbitrary terms
/// rather than the eliminator nest's binders. `dep_bottom` derived it, spent it
/// on the typing and dropped it — `MINI-HANDOFF.md` §2's sixth instance, and
/// the reason a reduction reads as blocked on an ι theorem that has been in the
/// store the whole time. It is **not** kept as a stored theorem, because its
/// `Γ` is the caller's: what is shared is the *derivation*, and every input it
/// takes ([`Cx`]) is a term or a membership.
pub(crate) fn pre_at(ip: &mut Interp, site: &Site, at: &At, cx: &Cx) -> Result<Pre, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let key = (site.ind.clone(), site.inst.clone());
    let dep = {
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        app.dep_recursor(kenv, &key, &cx.ind).ok_or_else(|| {
            Gap::Recursor(
                site.ind.clone(),
                "dependent recursor: DepRecursor::build declined",
                Cause::Library,
            )
        })?
    };
    let dr = &dep.dr;

    // ── `DEP`, one conjunct per constructor ─────────────────────────────────
    //
    // The target is `⟦Sort u₁⟧` itself; see [`cod_at_rung`].
    let target = cx.v_set.clone();
    let mut sub = cx.psub.clone();
    sub.push((dr.motive, cx.c_tm.clone()));
    for (v, t) in dr.minors.iter().zip(cx.s_tms.iter()) {
        sub.push((*v, t.clone()));
    }
    sub.push((dr.target, target));

    let mut deps = Vec::with_capacity(site.n);
    for i in 0..site.n {
        if let Some(why) = general_slot_declines(&cx.ind, i) {
            return Err(Gap::Recursor(site.ind.clone(), why, Cause::Library))
        }
        // **The dependent clause's own crossing** — see [`MINOR_GRAIN`]. The
        // check is here and not in `general_slot_declines` because it is a
        // property of *this* clause's obligation and not of the declaration:
        // `rect_step` states no applied minor at all, so `prop_bottom` is
        // through on the same constructor.
        if cx.ind.ctor_slot_domains(i).iter().any(Option::is_some) {
            return Err(Gap::Recursor(site.ind.clone(), MINOR_GRAIN, Cause::Library))
        }
        let got = minor_at(ip, site, cx, at, i, false).ok_or_else(|| bad(MINOR))?;
        let want = subst_f(&dr.guards.dep_parts[i], &sub);
        if *got.concl() != want {
            return Err(bad(MINOR))
        }
        deps.push(got);
    }
    let dep_all = deps
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("dependent recursor: a declaration with no constructors"))?;
    let cod = cod_at_rung(ip, site, cx).ok_or_else(|| bad(COD))?;
    if *cod.concl() != subst_f(&dr.guards.cod, &sub) {
        return Err(bad(COD))
    }
    let pre = derived::and_intro(&cod, &dep_all);
    if *pre.concl() != subst_f(&dr.premise, &sub) {
        return Err(bad("dependent recursor: the premise is not DepRecursor's"))
    }
    Ok(Pre { dep: dep.clone(), pre, sub })
}

/// [`pre_at`]'s three outputs: the eliminator, `PRE` at the caller's terms, and
/// the substitution that carries `derived`'s statement variables onto them.
pub(crate) struct Pre {
    pub(crate) dep: Rc<crate::interp::DepRec>,
    pub(crate) pre: Thm,
    pub(crate) sub: Vec<(FreeVar, Term)>,
}

/// The variables `DepRecursor` states `typing` and `iota` at, and the terms a
/// caller instantiates them to — the two halves of one `gen_all`/`inst_all`,
/// kept together so the orders cannot drift apart.
pub(crate) fn quant_at(cx: &Cx, dr: &derived::inductive::DepRecursor) -> (Vec<FreeVar>, Vec<Term>) {
    let quant: Vec<FreeVar> = cx
        .ind
        .params
        .iter()
        .copied()
        .chain(std::iter::once(dr.motive))
        .chain(dr.minors.iter().copied())
        .chain(std::iter::once(dr.target))
        .collect();
    let args: Vec<Term> = cx
        .ps
        .iter()
        .cloned()
        .chain(std::iter::once(cx.c_tm.clone()))
        .chain(cx.s_tms.iter().cloned())
        .chain(std::iter::once(cx.v_set.clone()))
        .collect();
    (quant, args)
}

/// `⟦T.rec.{u₁,σ}⟧ = λp⃗ C S⃗ t. app(drec, t)`, with `DepRecursor::typing`.
fn dep_bottom(ip: &mut Interp, site: &Site, at: &At, cx: &Cx) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();

    let Pre { dep, pre, sub } = pre_at(ip, site, at, cx)?;
    let dr = &dep.dr;

    // ── the typing obligation, instantiated and discharged ──────────────────
    let (quant, args) = quant_at(cx, dr);
    let typing = gen_all_checked(&quant, &dr.typing).ok_or_else(|| bad(TYPING))?;
    let typing = derived::inst_all(&typing, &args).ok_or_else(|| bad(TYPING))?;
    let over = Thm::mp(&typing, &pre).ok_or_else(|| bad(TYPING))?;
    let at_t = derived::inst_all(&over, std::slice::from_ref(&cx.t_tm))
        .ok_or_else(|| bad(CARRIER))?;
    let mem = Thm::mp(&at_t, &cx.t_in_w).ok_or_else(|| bad(CARRIER))?;

    // ── the term, under a name of mini's own ────────────────────────────────
    //
    // `drec` is assembled inside `derived`, so its applicative structure was
    // never recorded through `Interp::mk` and the λ above it could not
    // skeletonise its body. One abbreviation over the nest's own binders fixes
    // it, exactly as `zoneb`'s constructor bottom does.
    let raw = ap.apply(subst_term(&dr.rec, &sub), cx.t_tm.clone());
    let (sym, ax) = {
        let (kenv, _, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        derived::define_abbrev(kenv, &at.vars, &raw).ok_or_else(|| bad(TERM))?
    };
    let unfold = derived::inst_all(&ax, &at.xs).ok_or_else(|| bad(TERM))?;
    let term = ip.mk(sym, at.xs.clone());
    let out = ip.retarget_subject(&mem, &unfold).ok_or_else(|| bad(TERM))?;
    if *out.concl() != Formula::mem(term.clone(), at.goal.clone()) {
        return Err(bad("dependent recursor: the eliminator did not land in the codomain"))
    }
    // **Kept, not spent.** `ax` is `∀p⃗ C S⃗ t. sym(p⃗,C,S⃗,t) = app(drec, t)` over
    // the nest's *own* binders, so it instantiates at any arguments at all —
    // and a use site that has β'd down this nest has `sym(⟦p⃗⟧,…,⟦major⟧)` in
    // hand and no other way back to `drec`, because re-minting the abbreviation
    // gives a second symbol no equation relates to this one. Dropping it was
    // `MINI-HANDOFF.md` §2's sixth instance; [`crate::iota_dep`] is the
    // consumer.
    if let Some(app) = ip.ind_apparatus() {
        let key = (site.rec.clone(), site.rec_inst.clone());
        let target = cx.v_set.clone();
        app.dep_elims.insert(key, Rc::new(crate::interp::DepElim { sym, ax, target }));
    }
    Ok((term, out))
}

/// `Γ ⊢ COD(⟦C⟧, ⟦Sort u₁⟧)` — the target premise, at the sort the motive was
/// declared into.
///
/// Two rung facts and one application rule; see the module header for why no
/// other target and no other theorem is needed. The `∀`/`→` shape is
/// [`Closed::discharge`](crate::scope::Closed::discharge)'s, which is `COD`'s
/// on the nose.
pub(crate) fn cod_at_rung(ip: &mut Interp, site: &Site, cx: &Cx) -> Option<Thm> {
    let rung = ip.prelude.tower.at(site.u1 as usize)?;
    if rung.set != cx.v_set {
        return None
    }
    let mut scopes = Scopes::new();
    let tok_x = scopes.open(&mut ip.env, cx.w_term.clone());
    let (xt, xm) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let cx_at = ip.app(cx.c_tm.clone(), xt.clone());
    let cx_mem = ip.dprod_app(&cx.c_fibre, &cx.w_term, &cx.c_tm, &xt, &cx.c_in_fs, &xm)?;

    let tok_y = scopes.open(&mut ip.env, cx_at.clone());
    let (yt, ym) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    // `app(C,x) ∈ Uₙ → ∀z. (z ∈ app(C,x) → z ∈ Uₙ)`.
    let trans = derived::inst_all(&rung.transitive, std::slice::from_ref(&cx_at))?;
    let over = Thm::mp(&trans, &cx_mem)?;
    let at_y = derived::inst_all(&over, std::slice::from_ref(&yt))?;
    let inner = Thm::mp(&at_y, &ym)?;

    let fam = scopes.close(tok_y).discharge(&inner).ok()?;
    let covers = scopes.close(tok_x).discharge(&fam).ok()?;
    Some(derived::and_intro(&covers, &rung.empty_mem))
}

const COD: &str = "dependent recursor: COD at the motive's own sort";
const MOTIVE_TY: &str = "dependent recursor: the motive's type is not T p⃗ → Sort u₁";
const TYPING: &str = "dependent recursor: DepRecursor::typing does not instantiate here";
const TERM: &str = "dependent recursor: naming the eliminator's term";

// ─────────────────────────────────────────────────────────────────────────────
// One minor premise, transported
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ DEPᵢ(C,Sᵢ)` — or `⊢ rect_stepᵢ(φ)` when `prop` — from the minor binder's
/// own scope typing.
///
/// The two differ only in what the induction-hypothesis arguments are: the
/// variables `DEPᵢ` quantifies, or `•` at a `Prop`-valued motive, where the
/// hypothesis *is* `φ(tⱼ)`. Everything else is one walk.
pub(crate) fn minor_at(
    ip: &mut Interp,
    site: &Site,
    cx: &Cx,
    at: &At,
    i: usize,
    prop: bool,
) -> Option<Thm> {
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();
    let point = ip.point();
    let ctor = cx.ind.spec.ctors.get(i)?.clone();
    let (k, m) = (ctor.args.len(), ctor.recs);
    let nlev = k + 2 * m;

    // ── the crossing at each recursive slot, or `None` at a plain one ───────
    //
    // **The binder is what moves, not the atom.** At a function-typed slot the
    // scope opens at `derived`'s `fs(Aⱼ,W)` — the set `rect_step` and
    // `dep_minor` both bind it at — and what the interpretation is handed is
    // the *pushed* function `push(t, β₀(p⃗))`, which is the element of
    // `⟦γ → T p⃗⟧` the minor premise's own Π clause wants.
    let cross = crossings(ip, site, cx, i)?;
    // Which recursive slot each level binds, `None` at a plain field and at
    // every induction-hypothesis level.
    let lvl_rec: Vec<Option<usize>> = {
        let mut ri = 0usize;
        let mut v: Vec<Option<usize>> = ctor
            .order
            .iter()
            .map(|sl| match sl {
                Slot::Plain => None,
                Slot::Rec => {
                    let j = ri;
                    ri += 1;
                    Some(j)
                }
            })
            .collect();
        v.extend(std::iter::repeat_n(None, m));
        v
    };

    // ── one scope per binder of the minor's Π-interpretation ────────────────
    let mut scopes = Scopes::new();
    let mut toks = Vec::new();
    let (mut ws, mut wvs, mut wmems) = (Vec::new(), Vec::new(), Vec::new());
    // The interpretation's own term at each level — the same as `ws[l]` except
    // at a function-typed slot, where it is the pushed function.
    let mut ifields: Vec<Term> = Vec::new();
    // The slot's own scope assumption, `tⱼ ∈ fs(Aⱼ,W)`, kept per recursive
    // slot: the round trip and the constructor congruence both spend it.
    let mut rec_mems: Vec<Option<Thm>> = vec![None; m];
    let mut rec_ws: Vec<Term> = vec![point.clone(); m];
    // The **plain** fields in plain order. `ws[..k]` is not that: the two agree
    // only when every field precedes every recursive slot, and a
    // `Rec, Plain, …` mask is what says so.
    let mut plain_ws: Vec<Term> = Vec::with_capacity(k);
    // `⊢ atomᵢ → ante` at an induction-hypothesis level whose slot is
    // function-typed, indexed by *atom* position. See [`at_atom`].
    let mut ih_imp: Vec<Option<Thm>> = vec![None; k + 2 * m];
    let mut f_tm = cx.s_tms[i].clone();
    let mut f_mem = cx.s_mems[i].clone();
    for (l, at_slot) in lvl_rec.iter().enumerate().take(nlev) {
        let set = f_mem.concl().as_mem()?.1;
        let shape = ip.as_pi(&set)?;
        let gen = at_slot.and_then(|j| cross[j].as_ref());
        let dom = match gen {
            None => shape.dom(),
            Some(cr) => s.fs.of(cr.a.clone(), cx.w_term.clone()),
        };
        let tok = scopes.open(&mut ip.env, dom);
        let (wv, wt, wm) = {
            let sc = scopes.get(0)?;
            (sc.var(), sc.term(), sc.assumption().clone())
        };
        toks.push(tok);
        // What the interpretation's application rule is fed, and its typing.
        let (arg, arg_mem) = match gen {
            None => (wt.clone(), wm.clone()),
            Some(cr) => {
                let g = cr.pushed(&wt);
                let gm = push_into_pi(ip, cx, cr, &wt, &wm, &shape.dom())?;
                (g, gm)
            }
        };
        match at_slot {
            Some(j) => {
                rec_ws[*j] = wt.clone();
                rec_mems[*j] = Some(wm.clone());
            }
            None if l < k + m => plain_ws.push(wt.clone()),
            None => {}
        }
        // The induction hypothesis of a function-typed slot: `derived` states
        // it pointwise over `Aⱼ` and the minor's binder is a whole `Π` over
        // `⟦γ⟧`, so the two are a transport apart rather than a rewrite.
        if l >= k + m {
            let j = l - (k + m);
            if let Some(cr) = cross[j].as_ref() {
                ih_imp[k + m + j] =
                    Some(ih_transport(ip, cx, cr, &rec_ws[j], &shape.dom(), prop)?);
            }
        }
        let out = match &shape {
            PiShape::Dep { site, dom } => {
                ip.dprod_app(site, dom, &f_tm, &arg, &f_mem, &arg_mem)
            }
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &arg, &arg_mem),
        }?;
        f_tm = out.concl().as_mem()?.0;
        f_mem = out;
        ws.push(wt);
        wvs.push(wv);
        wmems.push(arg_mem);
        ifields.push(arg);
    }

    // ── the conclusion, off the interpretation's constructor spine ──────────
    let (subject, set) = f_mem.concl().as_mem()?;
    let fields: Vec<Term> = ifields[..k + m].to_vec();
    let mut sp_args = cx.ps.clone();
    sp_args.extend(fields.iter().cloned());
    let mut sp_mems = cx.param_mems.clone();
    sp_mems.extend(wmems[..k + m].iter().cloned());
    let (_, ceq) = ip.beta_spine(&at.ctor_formers[i], &sp_args, &sp_mems)?;
    let cax = derived::inst_all(&site.tr.ctor_abbrev[i], &fields)?;
    let ceq = eq_trans(ip, &ceq, &cax)?;
    // **`⟦T.ctorᵢ f⟧` is `ctorᵢ(pull(f, T(p⃗)))`**, and the obligation names
    // `ctorᵢ(t)` at the minor premise's own binder. The round trip is what
    // closes that, one slot at a time.
    let ceq = ctor_at_binders(ip, cx, i, &plain_ws, &cross, &rec_ws, &rec_mems, &ceq)?;
    let (lhs, rhs) = ceq.concl().as_eq()?;
    if set != ap.apply(cx.c_tm.clone(), lhs.clone()) {
        return None
    }
    let hole = ip.env.fresh_var();
    let leib = Thm::eq_leibniz(
        lhs,
        rhs.clone(),
        hole,
        Formula::mem(subject.clone(), ap.apply(cx.c_tm.clone(), Term::var(hole))),
    );
    let mut chain = Thm::mp(&leib, &ceq).and_then(|t| Thm::mp(&t, &f_mem))?;

    // **A field-free constructor's minor is a proof *variable*, not `•`.**
    // Every application rule the walk above fires at a `Prop`-valued motive is
    // `cond_app`, whose subject is `•` already; at `k + 2m = 0` no rule fires at
    // all and the subject is still the minor binder's own scope variable. §6.2
    // gives it `•` by proof irrelevance — the same step `lam_evidence` takes one
    // level up — and `app(C, ctorᵢ) ∈ ⟦Prop⟧` is one `fs_app` away.
    if prop && subject != point {
        let ctor_in_w = ctor_in_carrier(ip, cx, i, &rhs)?;
        let ty_mem =
            ip.dprod_app(&cx.c_fibre, &cx.w_term, &cx.c_tm, &rhs, &cx.c_in_fs, &ctor_in_w)?;
        let pt = ip.point_of_proof(&ty_mem, &chain)?;
        let back = derived::eq_symm(&mut ip.env, &pt)?;
        chain = ip.retarget_subject(&chain, &back)?;
    }

    // ── discharge, innermost first ──────────────────────────────────────────
    for _ in 0..nlev {
        let closed = scopes.close(toks.pop()?);
        chain = closed.discharge(&chain).ok()?;
    }

    // ── the statement's own arguments and atoms ─────────────────────────────
    let args: Vec<Term> = (0..nlev)
        .map(|l| if prop && l >= k + m { point.clone() } else { ws[l].clone() })
        .collect();
    let (mut ys, mut ts, mut yvs, mut tvs) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for (j, sl) in ctor.order.iter().enumerate() {
        match sl {
            Slot::Plain => {
                ys.push(ws[j].clone());
                yvs.push(wvs[j]);
            }
            Slot::Rec => {
                ts.push(ws[j].clone());
                tvs.push(wvs[j]);
            }
        }
    }
    let vs: Vec<Term> = args[k + m..].to_vec();
    let vvs: Vec<FreeVar> = wvs[k + m..].to_vec();

    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = cx.ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    // **`rect_step` reads `Inductive::ctor_slot_domains`**: a plain slot's atom
    // is `tⱼ ∈ W`, and a function-typed one's is `tⱼ ∈ fs(Aⱼ, W)` — the set
    // this walk opened the slot's scope at, so the two are the *same formula*
    // and no equation moves between them.
    atoms.extend((0..m).map(|j| {
        let set = match cross[j].as_ref() {
            None => cx.w_term.clone(),
            Some(cr) => s.fs.of(cr.a.clone(), cx.w_term.clone()),
        };
        Formula::mem(ts[j].clone(), set)
    }));
    // The induction hypotheses. A plain slot's is `vⱼ ∈ app(C, tⱼ)`; a
    // function-typed one's is `ih_at_motive`'s pointwise family
    // `∀z. (z ∈ Aⱼ → app(vⱼ,z) ∈ app(C, app(tⱼ,z)))`, which at `prop` is
    // `φ`'s own substitution instance with `vⱼ` gone and `•` in its place.
    // [`ih_transport`] is what carries it onto the minor's own `Π` binder.
    atoms.extend((0..m).map(|j| match cross[j].as_ref() {
        None => Formula::mem(vs[j].clone(), ap.apply(cx.c_tm.clone(), ts[j].clone())),
        Some(cr) => {
            let zv = ip.env.fresh_var();
            let tz = Term::var(zv);
            let val = if prop {
                point.clone()
            } else {
                ap.apply(vs[j].clone(), tz.clone())
            };
            Formula::forall(
                zv,
                Formula::imp(
                    Formula::mem(tz.clone(), cr.a.clone()),
                    Formula::mem(
                        val,
                        ap.apply(cx.c_tm.clone(), ap.apply(ts[j].clone(), tz)),
                    ),
                ),
            )
        }
    }));

    // The equation that moves atom `a`'s set onto the one the interpretation
    // named, where the two are different sets with the same members.
    let back = derived::eq_symm(&mut ip.env, &cx.w_eq)?;
    let mut set_eq: Vec<Option<Thm>> = Vec::with_capacity(atoms.len());
    for j in 0..k {
        let mut a = cx.ps.clone();
        a.extend(ys[..j].iter().cloned());
        set_eq.push(derived::inst_all(site.tr.field_abbrev.get(i)?.get(j)?, &a));
    }
    for c in cross.iter().take(m) {
        // A function-typed slot's scope *is* `derived`'s set; the plain one's
        // is the applied spine and needs the carrier equation.
        set_eq.push(c.is_none().then(|| back.clone()));
    }
    for _ in 0..m {
        set_eq.push(None);
    }

    // Level `l` of the walk answers atom `order_index[l]`.
    let mut order_index = Vec::with_capacity(nlev);
    let (mut pi, mut ri) = (0usize, 0usize);
    for sl in &ctor.order {
        match sl {
            Slot::Plain => {
                order_index.push(pi);
                pi += 1
            }
            Slot::Rec => {
                order_index.push(k + ri);
                ri += 1
            }
        }
    }
    for j in 0..m {
        order_index.push(k + m + j);
    }

    // ── re-instantiate, discharging each antecedent from the conjunction ────
    let hyp = derived::conj_of(&atoms);
    let mut cur = match &hyp {
        None => chain,
        Some(h) => derived::a1i(&chain, h.clone()),
    };
    for (l, arg) in args.iter().enumerate() {
        cur = hyp_inst(&cur, arg)?;
        let ante = cur.concl().as_imp()?.1.as_imp()?.0;
        let ai = order_index[l];
        let step =
            at_atom(ip, &atoms, ai, &ante, set_eq[ai].as_ref(), ih_imp[ai].as_ref())?;
        cur = derived::hyp_mp(&cur, &step)?;
    }

    let vars: Vec<FreeVar> = if prop {
        yvs.iter().chain(tvs.iter()).copied().collect()
    } else {
        yvs.iter().chain(tvs.iter()).chain(vvs.iter()).copied().collect()
    };
    // The caller compares what comes out against `motive::dep_minor` /
    // `rect::rect_step` rebuilt at these very terms, which is what pins the
    // `applied_minor` spelling, the atom order and the quantifier prefix — so
    // nothing is asserted here that is not then checked there.
    gen_all_checked(&vars, &cur)
}

/// `Γ ⊢ push(t, β₀(p⃗)) ∈ ⟦γ → T p⃗⟧` from `Γ ⊢ t ∈ fs(Aⱼ, W)` — §33's four
/// rewrites, **reversed**.
///
/// The constructor's nest bottom runs them the other way: it holds
/// `g ∈ dprod(b,⟦γ⟧)` and carries it to `fs(T(p⃗), ind(p⃗))` so that
/// `sigma::reindex_in_funspace` applies. A minor premise *quantifies* that
/// side, so it starts where the constructor arrives and has to get back:
///
/// ```text
/// 1.  t ∈ fs(T(p⃗), W)                          the slot's own scope
/// 2.  push(t,β₀(p⃗)) ∈ fs(β₀(p⃗), W)             sigma::push_in_funspace
/// 3.  fs(β₀(p⃗),·) ↦ fs(⟦γ⟧,·)                  congr_arg at argument 0
/// 4.  fs(·,W) ↦ fs(·,⟦T p⃗⟧)                    congr_arg at argument 1
/// 5.  fs(⟦γ⟧,⟦T p⃗⟧) = dprod(b,⟦γ⟧)             Interp::dprod_is_fs, symm
/// ```
///
/// `dom` is the minor's own binder domain, read off its `Π` interpretation, and
/// the result is checked against it: the crossing is only sound if the set the
/// walk is about to apply into is the set this arrives at.
fn push_into_pi(
    ip: &mut Interp,
    cx: &Cx,
    cr: &Crossing,
    t: &Term,
    t_mem: &Thm,
    dom: &Term,
) -> Option<Thm> {
    let s = ip.prelude.tower.sums.clone();
    let PiShape::Dep { site: fsite, dom: gamma } = ip.as_pi(dom)? else { return None };
    if gamma != cr.gamma {
        return None
    }
    let spine = cx.w_eq.concl().as_eq()?.0.clone();

    let rule = derived::inst_all(&cr.in_funspace, &[cx.w_term.clone(), t.clone()])?;
    let mem = Thm::mp(&rule, t_mem)?;

    let fs_sym = ip.prelude.fs_sym();
    let onto_gamma = derived::congr_arg(
        &mut ip.env,
        fs_sym,
        &[cr.beta0.clone(), cx.w_term.clone()],
        0,
        &cr.gamma_ax,
    )?;
    let mem = ip.retarget_set(&mem, &onto_gamma)?;

    let back = derived::eq_symm(&mut ip.env, &cx.w_eq)?;
    let onto_spine = derived::congr_arg(
        &mut ip.env,
        fs_sym,
        &[gamma.clone(), cx.w_term.clone()],
        1,
        &back,
    )?;
    let mem = ip.retarget_set(&mem, &onto_spine)?;

    let (cod, bridge) = ip.dprod_is_fs(&fsite, &gamma)?;
    if cod != spine {
        return None
    }
    let unbridge = derived::eq_symm(&mut ip.env, &bridge)?;
    let out = ip.retarget_set(&mem, &unbridge)?;
    let _ = s;
    (*out.concl() == Formula::mem(cr.pushed(t), dom.clone())).then_some(out)
}

/// `⊢ (∀z. (z ∈ Aⱼ → • ∈ app(C, app(t,z)))) → • ∈ ⟦∀z:γ, C (f z)⟧` — the
/// induction hypothesis, from `derived`'s grain onto the minor premise's own
/// binder.
///
/// **This is a λ-introduction and not a rewrite**, which is why [`at_atom`]
/// needed a third mode rather than another equation: `derived`'s hypothesis is
/// a *pointwise family* over the fibre summand and what the minor premise binds
/// is one element of a `Π`. `Push::app` is what lines the two fibres up —
/// `app(t, ⟨z,•⟩) = app(push(t,β₀), z)`, so the family instantiated at the
/// telescope's own tuple is the family the minor's fibre symbol is stated at.
///
/// At `prop` the `Π` is `Prop`-valued, so the introduction is
/// [`Interp::cond_lam_typing`] and the element is `•`. The dependent clause
/// wants `crate::interp::Interp`'s `dprod` and `derived::ext::lam_in_dprod_n`
/// there, and it does not reach here: see [`MINOR_GRAIN`].
fn ih_transport(
    ip: &mut Interp,
    cx: &Cx,
    cr: &Crossing,
    t: &Term,
    dom: &Term,
    prop: bool,
) -> Option<Thm> {
    if !prop {
        return None
    }
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();
    let point = ip.point();
    let PiShape::Prop { site: inner, dom: gamma } = ip.as_pi(dom)? else { return None };
    if gamma != cr.gamma {
        return None
    }

    // `derived`'s atom, built here so that the caller's copy and this
    // derivation's cannot drift: [`minor_at`] rebuilds the same formula and
    // `at_atom` compares them.
    let zv = ip.env.fresh_var();
    let tz = Term::var(zv);
    let atom = Formula::forall(
        zv,
        Formula::imp(
            Formula::mem(tz.clone(), cr.a.clone()),
            Formula::mem(
                point.clone(),
                ap.apply(cx.c_tm.clone(), ap.apply(t.clone(), tz)),
            ),
        ),
    );

    let mut sc = Scopes::new();
    let (tok_a, h) = sc.assume(atom.clone());
    let tok_b = sc.open(&mut ip.env, cr.gamma.clone());
    let (bv, bt, bm) = {
        let scope = sc.get(0)?;
        (scope.var(), scope.term(), scope.assumption().clone())
    };

    // `b ∈ ⟦γ⟧` is `b ∈ β₀(p⃗)`, which is what both the telescope's own
    // introduction rule and `Push::app`'s side condition are stated at.
    let back = derived::eq_symm(&mut ip.env, &cr.gamma_ax)?;
    let b_in_beta = ip.retarget_set(&bm, &back)?;

    let mut ia = cx.ps.clone();
    ia.push(bt.clone());
    let tup_mem = Thm::mp(&derived::inst_all(&cr.tel.intro, &ia)?, &b_in_beta)?;
    let tup = derived::sigma::Telescope::tuple_of(&s, std::slice::from_ref(&bt));
    if *tup_mem.concl() != Formula::mem(tup.clone(), cr.a.clone()) {
        return None
    }

    let val = Thm::mp(&derived::inst_all(&h, std::slice::from_ref(&tup))?, &tup_mem)?;
    let beta = Thm::mp(
        &derived::inst_all(&cr.px.app, &[t.clone(), cr.beta0.clone(), bt.clone()])?,
        &b_in_beta,
    )?;
    // `app(push(t,β₀), b) = app(t,⟨b,•⟩)`, wanted the other way round.
    let beta = derived::eq_symm(&mut ip.env, &beta)?;
    let (lhs, rhs) = beta.concl().as_eq()?;
    let hole = ip.env.fresh_var();
    let leib = Thm::eq_leibniz(
        lhs.clone(),
        rhs.clone(),
        hole,
        Formula::mem(point.clone(), ap.apply(cx.c_tm.clone(), Term::var(hole))),
    );
    let moved = Thm::mp(&Thm::mp(&leib, &beta)?, &val)?;

    // …which is the minor's own fibre at `b`, and then the `Π` it belongs to.
    let onto = ip.to_cond_fibre(&inner, bv, &moved)?;
    let family = sc.close(tok_b).discharge(&onto).ok()?;
    let out = ip.cond_lam_typing(&inner, cr.gamma.clone(), &family)?;
    if *out.concl() != Formula::mem(point, dom.clone()) {
        return None
    }
    Some(sc.discharge_assumption(tok_a, &out))
}

/// The constructor equation with every function-typed slot's argument moved
/// from `pull(push(tⱼ,β₀(p⃗)), T(p⃗))` — which is what
/// `crate::zoneb::rec_slot_terms` put in the constructor's term — back onto the
/// minor premise's own binder `tⱼ`, which is what the obligation names.
///
/// `derived::sigma::push_pull_roundtrip` is the equation and the slot's own
/// scope assumption is its premise; the rest is one Leibniz per slot, at the
/// hole `Inductive::ctor_term` leaves when that argument is a variable. Slots
/// are moved left to right and the term is rebuilt each time, so a declaration
/// with two of them cannot rewrite one into the other's position.
#[allow(clippy::too_many_arguments)]
fn ctor_at_binders(
    ip: &mut Interp,
    cx: &Cx,
    i: usize,
    ys: &[Term],
    cross: &[Option<Crossing>],
    rec_ws: &[Term],
    rec_mems: &[Option<Thm>],
    ceq: &Thm,
) -> Option<Thm> {
    if cross.iter().all(Option::is_none) {
        return Some(ceq.clone())
    }
    let mut ts: Vec<Term> = (0..cross.len())
        .map(|j| match cross[j].as_ref() {
            None => rec_ws[j].clone(),
            Some(cr) => cr.pulled(&rec_ws[j], &cx.ps),
        })
        .collect();
    let mut out = ceq.clone();
    for j in 0..cross.len() {
        let Some(cr) = cross[j].as_ref() else { continue };
        let rt = Thm::mp(
            &derived::inst_all(&cr.roundtrip, &[cx.w_term.clone(), rec_ws[j].clone()])?,
            rec_mems[j].as_ref()?,
        )?;
        if *rt.concl() != Formula::eq(ts[j].clone(), rec_ws[j].clone()) {
            return None
        }
        let hole = ip.env.fresh_var();
        let mut ts_hole = ts.clone();
        ts_hole[j] = Term::var(hole);
        let (got, at_hole) = {
            let (_, app, _) = ip.ind_parts()?;
            (
                cx.ind.ctor_term(&app.mach, i, ys, &ts)?,
                cx.ind.ctor_term(&app.mach, i, ys, &ts_hole)?,
            )
        };
        if out.concl().as_eq()?.1 != got {
            return None
        }
        let leib =
            Thm::eq_leibniz(ts[j].clone(), rec_ws[j].clone(), hole, Formula::eq(got.clone(), at_hole));
        let step = Thm::mp(&leib, &rt)?;
        let eq = Thm::mp(&step, &Thm::eq_refl(got))?;
        out = eq_trans(ip, &out, &eq)?;
        ts[j] = rec_ws[j].clone();
    }
    Some(out)
}

/// `Γ ⊢ ctorᵢ ∈ W` for a constructor with **no fields**, whose own membership
/// rule carries no antecedent.
///
/// Not a special case of anything: this is the one place the proof clause needs
/// a constructor's carrier membership, and it needs it exactly where
/// `Ctor::mem`'s antecedent has vanished. A constructor with fields never
/// reaches here — the walk's last `cond_app` has already delivered `•`.
fn ctor_in_carrier(ip: &mut Interp, cx: &Cx, i: usize, ctor: &Term) -> Option<Thm> {
    let at = derived::inst_all(&cx.ind.ctors.get(i)?.mem, &cx.ps)?;
    let ty_at = derived::inst_all(&cx.ind.ty_ax, &cx.ps)?;
    let out = ip.retarget_set(&at, &ty_at)?;
    (*out.concl() == Formula::mem(ctor.clone(), cx.w_term.clone())).then_some(out)
}

/// `⊢ H → ante`, where `ante` is `atoms[i]` under one of **three** modes.
///
/// 1. the two formulas are the same — a plain field's atom stated at the set
///    the interpretation's own binder opened at, and every function-typed
///    slot's, because [`minor_at`] opens that scope at `derived`'s set;
/// 2. same subject, set differs by one equation — a plain field at `βⱼ`
///    against `⟦βⱼ⟧`, and a plain recursive slot at `W` against the applied
///    spine. This is the mode this function was written for;
/// 3. neither subject nor shape survives: `imp` is a derivation of
///    `atoms[i] → ante` supplied by the caller. It is what a function-typed
///    slot's **induction hypothesis** needs — `derived` states a pointwise
///    family over `Aⱼ` and the minor premise binds a whole `Π` over `⟦γ⟧` — and
///    it is a *transport*, not a rewrite, so it cannot be an equation.
///
/// Mode 3 is tried last and only when the first two do not apply, so a caller
/// that supplies a transport where a rewrite would have done cannot change what
/// comes out.
fn at_atom(
    ip: &mut Interp,
    atoms: &[Formula],
    i: usize,
    ante: &Formula,
    eq: Option<&Thm>,
    imp: Option<&Thm>,
) -> Option<Thm> {
    let base = derived::conj_proj(atoms, i)?;
    if atoms[i] == *ante {
        return Some(base)
    }
    if let (Some((subj, s1)), Some((subj2, s2))) = (atoms[i].as_mem(), ante.as_mem()) {
        if subj == subj2 {
            let eq = eq?;
            if eq.concl().as_eq()? != (s1.clone(), s2.clone()) {
                return None
            }
            let hole = ip.env.fresh_var();
            let leib = Thm::eq_leibniz(s1, s2, hole, Formula::mem(subj, Term::var(hole)));
            return derived::syl(&base, &Thm::mp(&leib, eq)?)
        }
    }
    let imp = imp?;
    if *imp.concl() != Formula::imp(atoms[i].clone(), ante.clone()) {
        return None
    }
    derived::syl(&base, imp)
}

// ─────────────────────────────────────────────────────────────────────────────
// Small kernel helpers
// ─────────────────────────────────────────────────────────────────────────────

/// `Γ ⊢ x = z` from `Γ ⊢ x = y` and `Γ ⊢ y = z`.
pub(crate) fn eq_trans_pub(ip: &mut Interp, xy: &Thm, yz: &Thm) -> Option<Thm> {
    eq_trans(ip, xy, yz)
}

/// `Γ ⊢ x = z` from `Γ ⊢ x = y` and `Γ ⊢ y = z`.
fn eq_trans(ip: &mut Interp, xy: &Thm, yz: &Thm) -> Option<Thm> {
    let (x, y1) = xy.concl().as_eq()?;
    let (y2, z) = yz.concl().as_eq()?;
    if y1 != y2 {
        return None
    }
    let hole = ip.env.fresh_var();
    let leib = Thm::eq_leibniz(y2, z, hole, Formula::eq(x, Term::var(hole)));
    Thm::mp(&leib, yz).and_then(|t| Thm::mp(&t, xy))
}

/// `⊢ H → φ[t]` from `⊢ H → ∀v. φ`. Shared with [`crate::rec_ix_prop`], whose
/// prenexing loop is this one at an indexed family.
pub(crate) fn hyp_inst(thm: &Thm, t: &Term) -> Option<Thm> {
    let (_, all) = thm.concl().as_imp()?;
    derived::syl(thm, &Thm::ax_inst(all, t.clone())?)
}

/// [`derived::gen_all`] with the side condition reported — R6′ I3: mini never
/// calls the panicking wrapper, even where the theorem is known unconditional.
pub(crate) fn gen_all_checked(vs: &[FreeVar], thm: &Thm) -> Option<Thm> {
    vs.iter().rev().try_fold(thm.clone(), |acc, v| Thm::gen_checked(*v, &acc))
}

/// A formula at the caller's terms. Shared with [`crate::rec_prop`], which
/// has the same job: `derived` states its formulas at the declaration's own
/// parameter variables and every consumer is at a nest's binders.
pub(crate) fn subst_f(f: &Formula, subs: &[(FreeVar, Term)]) -> Formula {
    subs.iter().fold(f.clone(), |acc, (v, t)| acc.subst(*v, t))
}

/// A term at the caller's terms — `Formula::subst` is the kernel's only
/// substitution, so the term rides inside a reflexivity.
pub(crate) fn subst_term(t: &Term, subs: &[(FreeVar, Term)]) -> Term {
    let f = subst_f(&Formula::eq(t.clone(), t.clone()), subs);
    f.as_eq().expect("a reflexivity stays a reflexivity").0
}

/// The ground numeral of a `Sort`, or `None` at anything else — used to read
/// the rung a motive's own *type* inhabits.
///
/// Shared with [`crate::rec_ix_dep`], which needs the sort `infer_type` gave
/// the motive binder's type rather than the one the motive lands in; see that
/// module's header for why the two rungs differ and why it is the outer one.
pub(crate) fn sort_of(ty: &E) -> Option<u32> {
    let Expr::Sort(l) = &**ty else { return None };
    ground::eval(l, &Default::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }

    fn level(n: u32) -> Level {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = l.succ();
        }
        l
    }

    /// ```text
    /// inductive L (α : Type 0) : Type 0
    /// | nil  : L α
    /// | cons : α → L α → L α
    /// ```
    ///
    /// One parameter, two constructors of **different** arities, one plain
    /// field, one recursive field, and a mask that is not all-`Plain` or
    /// all-`Rec` — so the argument permutation, the vanishing antecedent at
    /// `nil` and the induction hypothesis at `cons` are all exercised. `L.rec`
    /// is **generated** by [`crate::kernel::add`], exactly as it is on the
    /// corpus.
    fn list_env() -> (Environment, Name, Name) {
        let l = nm("L");
        let (nil, cons) = (Name::str(&l, "nil"), Name::str(&l, "cons"));
        let ty0 = sort(Level::Zero.succ());
        let no: Rc<[Level]> = Vec::new().into();
        let spine = |d: u32| app(konst(l.clone(), no.clone()), bvar(d));
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: l.clone(),
                lparams: vec![],
                num_params: 1,
                ty: forall(ty0.clone(), ty0),
                ctors: vec![
                    (nil, forall(sort(Level::Zero.succ()), spine(0))),
                    (
                        cons,
                        forall(
                            sort(Level::Zero.succ()),
                            forall(bvar(0), forall(spine(1), spine(2))),
                        ),
                    ),
                ],
            },
        )
        .expect("the declaration is accepted");
        let rec = Name::str(&l, "rec");
        (env, l, rec)
    }

    /// `α, C, nil-minor, cons-minor, t`.
    const L_DEPTH: usize = 5;

    /// **`⟦L.rec⟧` is interpreted with its typing**, at a `Type`-valued motive
    /// and at a `Prop`-valued one — the two clauses of §6.2, and the two the
    /// corpus actually asks for at every class-(T) recursor it mentions.
    ///
    /// Non-vacuity, three ways. The typing must be about `⟦L.rec⟧` *itself* and
    /// carry no hypotheses; the interpretation must be a five-deep λ-nest that
    /// comes apart again at the value clause and `•` at the proof clause — a
    /// decline would leave the opaque symbol and pass a weaker assertion; and
    /// the set the bottom lands in must be the motive **at the major premise**,
    /// which [`a_recursor_that_concludes_at_a_fixed_constructor_is_declined`]
    /// pins from the other side.
    #[test]
    fn the_dependent_eliminator_is_interpreted_with_its_typing() {
        let (env, _, rec) = list_env();
        for u1 in [1u32, 0] {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let at: Rc<[Level]> = vec![level(u1)].into();
            let t = c.infer_type(&konst(rec.clone(), at)).expect("infer ⟦L.rec⟧");
            let m = t
                .ev
                .thm()
                .unwrap_or_else(|| panic!("⟦L.rec.{{{u1}}}⟧ has no typing: {:?}", t.ev))
                .clone();
            assert!(m.hyps().is_empty(), "a stored typing is unconditional");
            let (subj, _) = m.concl().as_mem().expect("a membership");
            assert_eq!(
                Some(subj),
                t.tm,
                "the typing must be about ⟦L.rec⟧ itself, not some other term"
            );
            if u1 == 0 {
                assert_eq!(
                    t.tm,
                    Some(c.interp().expect("threaded").point()),
                    "a Prop-valued motive makes the eliminator a proof, which denotes •"
                );
                continue
            }
            let mut cur = t.tm.clone().expect("interpreted");
            let ip = c.interp().expect("threaded");
            for lv in 0..L_DEPTH {
                let (site, _) = ip
                    .as_lam(&cur)
                    .unwrap_or_else(|| panic!("⟦L.rec⟧ is not a λ at level {lv}"));
                let (skel, holes) = (site.skel.clone(), site.holes.clone());
                let x = Term::var(ip.env.fresh_var());
                cur = ip.rebuild(&skel, &holes, &x);
            }
        }
    }

    /// **The declaration's name is not the evidence.** A rule called `L.rec`
    /// whose codomain is the motive at a *fixed* constructor — `C (L.nil α)`
    /// where Lean writes `C t` — is a well-typed five-binder `Π`, and is
    /// exactly what a wiring that ignored the major premise would satisfy. It
    /// is declined, and the reason names what was refused.
    ///
    /// This is the assertion that makes the motive's *dependence* load-bearing:
    /// at a constant motive the two codomains coincide, so a derivation that
    /// only ever proved membership in one fixed fibre would pass every other
    /// test in this file.
    #[test]
    fn a_recursor_that_concludes_at_a_fixed_constructor_is_declined() {
        let (mut env, l, rec) = list_env();
        let no: Rc<[Level]> = Vec::new().into();
        // Binders `α C n c t` = `#4 … #0`; `C (L.nil α)`.
        let cod = app(bvar(3), app(konst(Name::str(&l, "nil"), no), bvar(4)));
        let Some(ConstantInfo::Recursor { ty, .. }) = env.consts.get_mut(&rec) else {
            panic!("the recursor was generated")
        };
        *ty = with_codomain(&ty.clone(), L_DEPTH, cod);

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer");
        assert_eq!(
            t.ev.gap(),
            Some(&Gap::Recursor(
                l,
                "dependent recursor: the codomain is not the motive at the major premise",
                Cause::Threading
            )),
            "a recursor that concludes at a fixed constructor must be declined"
        );
    }

    /// Replace the body under `depth` `Π` binders.
    fn with_codomain(ty: &E, depth: usize, cod: E) -> E {
        if depth == 0 {
            return cod
        }
        let Expr::Forall { ty: d, body } = &**ty else { panic!("fewer than {depth} binders") };
        forall(d.clone(), with_codomain(body, depth - 1, cod))
    }

    /// **`derived::inductive::motive::cod_at_funspace` works, and it is still
    /// not this wiring's discharge** — which are two facts, and this file
    /// recorded them as one.
    ///
    /// Until `derived` `c2bd75f` it returned `None` at every input, and every
    /// record of that (this test, this file's header, `recursor.rs`'s header,
    /// `SCOPING.md` §4) gave *one* cause: `k` is `h ∧ (mx ∧ my)` where the two
    /// `gen_under`s want `(h ∧ mx) ∧ my`. True, and **not sufficient** — the
    /// union injection was also lifted under `k` with `a1i` before `syl`,
    /// which wants it bare, and either defect alone makes the `?` fire. A
    /// reader who applied the recorded fix would have measured it still dead
    /// with nothing pointing further. That is why the assertions below are
    /// about *statements* and not about `is_none()`: a tombstone goes stale
    /// silently in one direction and loudly in the other, and neither told
    /// anybody why [`cod_at_rung`] would still exist the day it was repaired.
    ///
    /// It exists for two reasons that have nothing to do with the repair, both
    /// asserted here:
    ///
    /// * **its hypothesis is `C ∈ fs(W,V)`, a function-space membership**, and
    ///   what this wiring holds is [`Cx::c_in_fs`]'s
    ///   `⟦C⟧ ∈ dprod(⟦Sort u₁⟧, W)` at a *constant* fibre — `SCOPING.md` §10
    ///   removed the `fs` clause from `⟦Π⟧`, so the two are one
    ///   `derived::ext::dprod_const_fibre_n` apart. *(That bridge is
    ///   [`crate::interp::Interp::dprod_is_fs`] and has three consumers; the
    ///   "stored and unread" this bullet used to say was already false when it
    ///   was written. The distance is one method call, so this bullet is a
    ///   *statement* mismatch and not a cost — corrected in place, because a
    ///   successor reading "unread" would size the crossing wrongly.)*
    /// * **it discharges `COD` at `⋃V ∪ {∅}` and not at `V`**, so it does not
    ///   speak about the sort the motive was declared into — which is the set
    ///   this route instantiates `DepRecursor::target` at and stores in
    ///   [`crate::interp::DepElim::target`], asserted below from the wiring's
    ///   own run rather than from this module's source.
    ///
    /// [`cod_at_rung`] needs neither bridge: two rung facts and the motive's
    /// own application rule, at the target the declaration already names.
    #[test]
    fn cod_at_funspace_is_stated_at_a_function_space_and_at_another_target() {
        use derived::inductive::motive::{cod_at_funspace, cod_parts, cod_target};

        let (env, l, rec) = list_env();
        let mut ip = Interp::new();
        {
            let mut c = Checker::threaded(&env, &mut ip);
            c.infer_type(&konst(l.clone(), Vec::new().into())).expect("carrier");
        }
        let s = ip.prelude.tower.sums.clone();
        let key = (l, Vec::new());
        let (kenv, app, _) = ip.ind_parts().expect("apparatus");
        let ind = app.decls.get(&key).expect("translated").ind.clone();
        let w = ind.wty.clone();
        let th = cod_at_funspace(kenv, &app.mach, &ind)
            .expect("cod_at_funspace was repaired in derived at c2bd75f");
        let (cv, vv) = (kenv.fresh_var(), kenv.fresh_var());
        let (tc, tv) = (Term::var(cv), Term::var(vv));

        let inst = derived::inst_all(&th, &[tc.clone(), tv.clone()]).expect("∀C ∀V");
        let (ante, cons) = inst.concl().as_imp().expect("an implication");
        assert_eq!(
            ante,
            Formula::mem(tc.clone(), s.fs.of(w.clone(), tv.clone())),
            "cod_at_funspace's hypothesis is a function-space membership, and \
             ⟦T p⃗ → Sort u₁⟧ is a dprod at a constant fibre"
        );
        let (_, holds_empty) = cod_parts(&cons).expect("COD's two conjuncts");
        let (_, target) = holds_empty.as_mem().expect("`∅ ∈ T`");
        assert_eq!(target, cod_target(&s, &tv), "the target is ⋃V ∪ {{∅}}");
        assert_ne!(target, tv, "…and in particular it is not V itself");

        // The wiring's own choice, read off a real run rather than off this
        // module: `⟦Sort 1⟧`, which is neither of the two above.
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1)].into();
        c.infer_type(&konst(rec.clone(), at)).expect("infer ⟦L.rec.{1}⟧");
        let u1 = ip.prelude.tower.at(1).expect("the first rung").set.clone();
        let stored = ip
            .ind_apparatus()
            .expect("apparatus")
            .dep_elims
            .get(&(rec, vec![1]))
            .expect("the eliminator nest was built")
            .target
            .clone();
        assert_eq!(stored, u1, "the target this route discharges COD at is ⟦Sort u₁⟧");
        assert_ne!(stored, cod_target(&s, &u1), "…and not cod_at_funspace's own");
    }

    /// **The frontier: what a function-typed recursive slot still stops, and
    /// which clause stops it** — eight cells, one build.
    ///
    /// Four declarations against two motive levels, because the two σ are two
    /// *routes* — [`dep_bottom`] through [`pre_at`] and [`prop_bottom`] through
    /// [`decl_rect`] — and the widening closes **one of them**:
    ///
    /// | declaration | `u₁ = 1` | `u₁ = 0` |
    /// | --- | --- | --- |
    /// | `L.cons : α → L α → L α` | interpreted | interpreted |
    /// | `T.c : (A → T) → T` | [`MINOR_GRAIN`] | **interpreted** |
    /// | `T.d : T → (A → T) → (B → T) → T` | [`MIXED`] | [`MIXED`] |
    /// | `T.f : (A → T) → A → (B → T) → (C → T) → T` | [`MINOR_GRAIN`] | **interpreted** |
    /// | `T.e : (A → B → T) → T` | `IndSpec` | `IndSpec` |
    ///
    /// **`T.f` is where the widening is actually pinned.** `T.c` has one slot,
    /// and every index map in [`crossings`], [`ctor_at_binders`] and the walk's
    /// `lvl_rec` is the identity on one element; `T.f` has **three**, at three
    /// distinct domains, because two would catch a permutation and not a clamp
    /// — `j ↦ min(j,1)` is the identity on `{0,1}`, which is how eight index
    /// maps survived an 868-test suite one crate over, and six more were found
    /// live in `derived/` the same way. Its mask is `Rec, Plain, Rec, Rec`, so
    /// the declared-order split (`lvl_rec`, `order_index`, `ys`/`ts`) is
    /// exercised as well as the slot-to-position one; a mask with every `Rec`
    /// before every `Plain` cannot separate the two.
    ///
    /// **It caught one before it landed**, which is why it is stated at this
    /// mask rather than at three bare `Rec`s: [`ctor_at_binders`] was handed
    /// `ws[..k]` as the constructor's plain fields, and `ws[..k]` is the first
    /// `k` *levels*, not the `k` plain ones. The two agree at every mask in
    /// which no field follows a recursive slot — which is `RTree`, every cell
    /// this test had, and the whole tutorial corpus. Three mutations were run
    /// against the fixture and all three fail: `min(j,1)` on `crossings`'
    /// `rec_dom_abbrev` index and on [`ctor_at_binders`]' slot index fail at
    /// `T.f` **and not at `T.c`**, which is the clamp rule measured rather than
    /// quoted; dropping the `eq_symm` that orients [`ih_transport`]'s Leibniz
    /// step fails at both.
    ///
    /// **The `T.c` row at `u₁ = 0` is the increment**, and it is the cell that
    /// says the seam was the *binder* and not the atom: the same declaration,
    /// the same constructor, the same `push`, and the clause that still
    /// declines is the one whose obligation mentions the minor premise at all.
    /// `rect_step` states no applied minor, so the proof clause never meets
    /// [`MINOR_GRAIN`]'s crossing; `dep_minor` applies `⟦Sᵢ⟧` to the
    /// constructor term's own argument and no interpreted minor premise is a
    /// function on that set.
    ///
    /// The mixed row is unchanged and its reason is now its own — a mixed
    /// constructor's plain slot needs `derived::point_fun` at `a := •` and
    /// nothing on the corpus reaches it — so the two declines are told apart by
    /// name rather than sharing one literal, which is what let the previous
    /// version of this test pass while covering two different facts.
    ///
    /// `T.e` is the **depth-`≥ 2`** column and it is a *measurement*, not a
    /// prediction: a currying never reaches this module at all — it is refused
    /// two constructions earlier, at
    /// `Gap::IndSpec(T, "recursive argument telescope depth")`, which is what
    /// the cell asserts by name. That is why [`general_slot_declines`] carries
    /// no depth guard: it would be a branch nothing can take, and this row is
    /// the frontier test that goes red the day the earlier refusal lifts. The
    /// scoping note that said the guard belonged here was written from
    /// `derived::sigma`'s depth-one guard, which is real and is second in line.
    #[test]
    fn a_function_typed_recursive_slot_stops_the_dependent_eliminator_at_both_sigma() {
        let ty0 = sort(Level::Zero.succ());
        let no: Rc<[Level]> = Vec::new().into();
        let (t, a, b, cc) = (nm("T"), nm("A"), nm("B"), nm("C"));
        let spine = konst(t.clone(), no.clone());
        let enum_of = |n: &Name| konst(n.clone(), no.clone());

        // `T.c : (A → T) → T` and `T.d : T → (A → T) → (B → T) → T`, the second
        // **mixed**, and with **three** recursive slots at two distinct
        // domains rather than two. Two is enough to catch a permutation and not
        // enough to catch a **clamp** — `j ↦ min(j,1)` is the identity on
        // `{0,1}` — which is the measurement `derived`'s seat took over eight
        // index maps, all eight of which survived the whole suite for exactly
        // that reason. Nothing in *this* test pins a slot-to-position
        // correspondence, so the third slot buys nothing today and is stated
        // anyway: the widening behind this frontier is per slot, at
        // `ctor_slot_domains`, `rec_slot_domains` and `minor_subs` at once, and
        // it is the fixture it will need. `A` and `B` are two declarations of
        // the same shape rather than one used twice, so their `β₀`s are
        // separated by their defining axioms and not by an arity.
        let only = forall(forall(enum_of(&a), spine.clone()), spine.clone());
        let mixed = forall(
            spine.clone(),
            forall(
                forall(enum_of(&a), spine.clone()),
                forall(forall(enum_of(&b), spine.clone()), spine.clone()),
            ),
        );

        let general = |ctor_ty: E| {
            let mut env = Environment::empty();
            for e in [&a, &b, &cc] {
                crate::kernel::add(
                    &mut env,
                    &Declaration::Inductive {
                        name: e.clone(),
                        lparams: vec![],
                        num_params: 0,
                        ty: ty0.clone(),
                        ctors: vec![
                            (Name::str(e, "t"), enum_of(e)),
                            (Name::str(e, "f"), enum_of(e)),
                        ],
                    },
                )
                .unwrap_or_else(|err| panic!("{e:?} is accepted: {err:?}"));
            }
            crate::kernel::add(
                &mut env,
                &Declaration::Inductive {
                    name: t.clone(),
                    lparams: vec![],
                    num_params: 0,
                    ty: ty0.clone(),
                    ctors: vec![(Name::str(&t, "c"), ctor_ty)],
                },
            )
            .expect("the checker accepts a function-typed recursive argument");
            (env, t.clone(), Name::str(&t, "rec"))
        };

        // `T.f : (A → T) → A → (B → T) → (C → T) → T` — the **`Rec, Plain, Rec,
        // Rec`** mask: three function-typed slots at three distinct domains,
        // with a data field *between* the first two, and no plain recursive
        // slot, so it is not mixed and the widening runs on all three.
        //
        // Three recursive slots and not two: a permutation of two moves both,
        // but `j ↦ min(j,1)` is the identity on `{0,1}`, and every index map
        // inside [`crossings`], [`ctor_at_binders`] and the walk's `lvl_rec` is
        // a slot-to-position correspondence a clamp would survive. The
        // interleaved field is the second axis — `lvl_rec`, `order_index` and
        // `minor_at`'s `ys`/`ts` split all read the declared order, and a mask
        // with every `Rec` before every `Plain` cannot tell them apart. `A`,
        // `B` and `C` are three declarations of the same shape rather than one
        // used three times, so their `β₀`s are separated by their defining
        // axioms and not by an arity.
        let three = forall(
            forall(enum_of(&a), spine.clone()),
            forall(
                enum_of(&a),
                forall(
                    forall(enum_of(&b), spine.clone()),
                    forall(forall(enum_of(&cc), spine.clone()), spine.clone()),
                ),
            ),
        );

        // `T.e : (A → B → T) → T` — the slot's `γ` is **two** binders deep, a
        // currying rather than a reindexing, which `derived::sigma` refuses on
        // both operators for a stated reason.
        let deep = forall(forall(enum_of(&a), forall(enum_of(&b), spine.clone())), spine.clone());

        /// What a cell expects: an interpretation, a decline this module owns
        /// and names, or a refusal from an earlier construction.
        enum Want {
            Interp,
            Named(&'static str),
            /// Refused before this module: `Gap::IndSpec`, by its own literal.
            Spec,
        }

        type Cell = (&'static str, (Environment, Name, Name), [Want; 2]);
        let cells: Vec<Cell> = vec![
            ("L: a plain recursive field", list_env(), [Want::Interp, Want::Interp]),
            ("T.c: one function-typed slot", general(only), [
                Want::Named(MINOR_GRAIN),
                Want::Interp,
            ]),
            ("T.d: a mixed constructor", general(mixed), [
                Want::Named(MIXED),
                Want::Named(MIXED),
            ]),
            ("T.f: Rec, Plain, Rec, Rec", general(three), [
                Want::Named(MINOR_GRAIN),
                Want::Interp,
            ]),
            ("T.e: γ at depth 2", general(deep), [Want::Spec, Want::Spec]),
        ];

        for (label, (env, ind, rec), wants) in cells {
            for (u1, want) in [1u32, 0].into_iter().zip(wants) {
                let mut ip = Interp::new();
                let mut c = Checker::threaded(&env, &mut ip);
                let at: Rc<[Level]> = vec![level(u1)].into();
                let got = c
                    .infer_type(&konst(rec.clone(), at))
                    .unwrap_or_else(|e| panic!("{label} u₁={u1}: infer_type: {e:?}"));
                match want {
                    Want::Interp => assert!(
                        got.ev.thm().is_some(),
                        "{label} u₁={u1}: this eliminator interprets — the check fires \
                         where it must not: {:?}",
                        got.ev
                    ),
                    Want::Named(why) => assert_eq!(
                        got.ev.gap(),
                        Some(&Gap::Recursor(ind.clone(), why, Cause::Library)),
                        "{label} u₁={u1}: the crossing must decline by *this* name, on \
                         the library axis"
                    ),
                    Want::Spec => assert_eq!(
                        got.ev.gap(),
                        Some(&Gap::IndSpec(
                            ind.clone(),
                            "recursive argument telescope depth"
                        )),
                        "{label} u₁={u1}: a currying is refused at the spec, two \
                         constructions before this module — which is why \
                         `general_slot_declines` carries no depth guard"
                    ),
                }
            }
        }
    }
}
