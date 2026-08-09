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
//!   clause is read off the term itself, and the membership is the
//!   assumption, not a lookup.
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
//! **Both clauses cross**, and the `u₁ ≥ 1` one needed a change on the other
//! side of the boundary to be able to. `dep_minor` *applies* the minor premise,
//! and it used to apply it to the constructor term's own argument — a member of
//! `fs(Aⱼ,W)`, while `⟦Sᵢ⟧` is a function on `dprod(b,⟦γ⟧)`, so the premise was
//! **false** at a general motive rather than unproved. It is now stated through
//! `derived::inductive::Inductive::minor_args`, at `push(·, β₀ⱼ(p⃗))`, and the
//! two columns differ only in [`ih_transport`]'s table: `cond_lam_typing` and
//! `•` at `u₁ = 0`, `derived::ext::lam_in_dprod_n` at `Push`'s own quadruple and
//! `push(vⱼ, β₀ⱼ(p⃗))` at `u₁ ≥ 1`. The statement's ih binder is a variable of
//! [`minor_at`]'s own, because `derived` quantifies `vⱼ` with **no** set typing
//! while the walk's binder is typed at `⟦∀z:γ, C (f z)⟧`.
//!
//! The mirror of all of this at a **use site** — where `whnf` holds `⟦f⟧` and
//! the ι rule wants the pulled function — is [`pull_from_pi`] here and
//! `crate::iota_dep` there.
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
use crate::expr::{Expr, Level, Name, E};
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
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    };
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
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
        _ => return Err(Gap::NoInterpretation(*ind_name, ind_inst.to_vec())),
    };
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 1 + n + 1;
    let codomain =
        crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad("dependent recursor: arity"))?;
    let u1 = motive_level(&rec_ty, np, 0)
        .ok_or_else(|| bad("dependent recursor: the motive's binder is not a Lean motive"))?;

    let key = (*ind_name, ind_inst.to_vec());
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
        ind: *ind_name,
        inst: ind_inst.to_vec(),
        rec: *rec_name,
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
    let Expr::Forall { ty: motive, .. } = &after.view() else { return None };
    // **`ni + 1`, not one.** An indexed family's motive is
    // `C : ∀ x⃗ (t : T p⃗ x⃗). Sort u₁`, so the `Sort` sits under the index
    // binders as well as the major premise's. Reading only one binder deep
    // returns `None` at every indexed recursor — which is not "this is not a
    // Lean motive", it is this function not knowing about indices, and it
    // reported the first as the second until `RBTree` was asked.
    let inner = crate::zoneb::peel(motive, ni + 1)?;
    let Expr::Sort(l) = &inner.view() else { return None };
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
    // **Before the `Interp` is borrowed, because both of these are `whnf`.**
    // The nest's parameters as expressions are its own innermost-counted
    // locals: binder `j` of `depth` is `bvar (depth-1-j)`, which is the index
    // [`Checker::local_type`] answers at and the one `infer_type` reads the
    // scope term off. See [`CtorBridge`].
    let param_es: Vec<E> = (0..site.np)
        .map(|j| crate::expr::bvar(u32::try_from(site.depth - 1 - j).unwrap_or(u32::MAX)))
        .collect();
    let bridges = match ctor_bridges(c, site, &param_es, &xs[..site.np]) {
        Ok(b) => b,
        Err(g) => return gap(g),
    };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let at = At { xs, mems, vars, former, ctor_formers, goal, prop, bridges };
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
    /// Per constructor, the conversions [`minor_at`] cannot mint — see
    /// [`CtorBridge`] and [`ctor_bridges`]. Filled by whoever holds the
    /// `Checker`, which is this nest's bottom and the use site, and by nobody
    /// else: the walk below it has an `Interp` and `whnf` is not one.
    pub(crate) bridges: Vec<CtorBridge>,
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
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
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
// **The dependent clause's own crossing is closed, and the reason string is
// gone rather than kept.** `MINOR_GRAIN` said that `derived`'s `DEPᵢ` applies
// the minor premise to the *constructor term's* argument — `app(app(Sᵢ,t),v)`
// with `t ∈ fs(Aⱼ,W)` — while `⟦Sᵢ⟧` is a function on `dprod(b,⟦γ⟧)`: disjoint
// domains, so the premise was false at a general motive rather than unproved,
// and no term mini could pass as `su` would have repaired it. That was right,
// and the fix was on the other side of the boundary:
// `derived::inductive::Inductive::minor_args` now states both argument families
// at `push(·, β₀ⱼ(p⃗))`, `motive::dep_minor` and `DepRecursor::iota` are stated
// through it, and `guard`'s `minor_lands` proves it there. A reason nothing
// produces is a trap for the next reader who greps for it, so the constant is
// deleted and the argument is kept where it is still true — in
// [`ih_transport`]'s table and in `minor_args`' own header.
/// A **mixed** constructor's plain recursive slot: `derived::point_fun` at
/// `a := •`, and no corpus witness. See [`general_slot_declines`].
const MIXED: &str = "dependent recursor: a mixed constructor's plain recursive slot";
/// The constructor's own declaration and the recursor's disagree about how many
/// parameters there are, or the store has no term for one of them.
const BRIDGE: &str = "dependent recursor: the constructor's declared binders";

// ─────────────────────────────────────────────────────────────────────────────
// The two conversions the walk cannot mint
// ─────────────────────────────────────────────────────────────────────────────

/// **What constructor `i`'s own declaration says, converted once, in the
/// caller's frame** — the two facts [`minor_at`] needs and structurally cannot
/// derive.
///
/// # Why this struct exists at all
///
/// [`minor_at`], [`cx_of`] and [`crossings`] take a `&mut Interp` and not a
/// [`Checker`], deliberately: [`crate::iota_dep`]'s use site reuses them from
/// inside `whnf`, where the checker is already borrowed. An `Interp` holds the
/// interpretation store and can β-reduce a stored λ; what it cannot do is
/// **convert** — δ-unfold a Lean constant and certify the equation — because
/// that is `whnf`, and `whnf` is the checker's.
///
/// Both facts below are conversions and both are facts about the
/// *declaration*, not about the eliminator, so both are minted at the two
/// places that do hold a `Checker` — [`rec_bottom`] and the use site — and
/// carried in [`At`]. That is `zoneb`'s `ctor_bottom` one construction later
/// and it is the same conversion: `67f34e0` gave the *constructor* its
/// reducible-alias bridge and left the *eliminator* without one.
///
/// Nothing here is trusted. Each field is an ordinary kernel theorem and every
/// consumer checks both of its endpoints before spending it, so a bridge built
/// at the wrong frame costs a decline and not a false equation.
pub(crate) struct CtorBridge {
    /// `Γ ⊢ ⟦pⱼ⟧ ∈ ⟦this constructor's own j-th parameter domain⟧`, for the
    /// `np` parameters, outermost first.
    ///
    /// **Not the recursor's, and the two are not the same set.** Lean writes a
    /// constructor's parameter binders from the `inductive` command's own
    /// syntax, so `mk : ∀ α : id (Type 1) Type, …` while the recursor and the
    /// type former both say `Sort 1` — definitionally equal and syntactically
    /// two terms, which is `good/tutorial/052`, `113` and `114`. [`minor_at`]
    /// walks `⟦T.ctorᵢ⟧`'s stored nest with [`Interp::beta_spine`], whose
    /// per-level premise is `⟦a⟧ ∈ dom` at the **λ's own** domain, and the
    /// recursor nest's `⟦pⱼ⟧ ∈ ⟦Sort 1⟧` is not that premise.
    ///
    /// [`Checker::nest_arg_mems`] is exactly this walk on the checker's side
    /// and it already spends the conversion, in `beta_premise_of`, at the one
    /// declaration that needs it and nowhere else — a domain that matches is
    /// returned untouched.
    pub(crate) param_mems: Vec<Thm>,
    /// `Γ ⊢ ⟦B⟧ = ⟦T p⃗⟧` per **recursive** slot, in recursive-slot order;
    /// `None` where `⟦B⟧` already *is* the spine, which is every declaration in
    /// the corpus but these three.
    ///
    /// `B` is the slot's Lean type at a plain recursive argument and its
    /// **codomain** at a function-typed one — the same two readings
    /// `zoneb::ctor_bottom`'s two bridges take, because they are consumed at
    /// the same two places: a plain slot's atom is stated at the carrier and
    /// its binder at `⟦B⟧` ([`at_atom`]'s mode 2), and a function-typed slot's
    /// membership is at `⟦∀z:γ. B⟧`, which no `whnf` moves — a `Π` is already
    /// in weak head normal form and the redex is under its binder
    /// ([`push_into_pi`], [`pull_from_pi`]).
    pub(crate) rec_eq: Vec<Option<Thm>>,
}

/// [`CtorBridge`] at every constructor, from the frame the caller's parameters
/// are spelled in.
///
/// `param_es` are the parameter *expressions* — the nest's own locals at
/// [`rec_bottom`], the reduction's own arguments at a use site — and
/// `param_tms` their interpretations. The two lists are what puts every
/// expression this reads into the caller's frame, and they are the only frame
/// input: nothing below does de Bruijn arithmetic against a telescope it does
/// not own.
///
/// **Fail-open here, fail-closed at the consumer.** A slot whose bridge cannot
/// be built gets `None` rather than an error, so that a declaration which
/// certified without one still does and a declaration that needs one declines
/// under the consumer's own name. The two `Err`s are the shapes at which
/// nothing downstream could be stated at all.
pub(crate) fn ctor_bridges(
    c: &mut Checker<'_, '_>,
    site: &Site,
    param_es: &[E],
    param_tms: &[Term],
) -> Result<Vec<CtorBridge>, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    if param_es.len() != site.np || param_tms.len() != site.np {
        return Err(bad(BRIDGE))
    }
    // `⟦T p⃗⟧`, built the way [`cx_of`] builds it — the applied spine
    // `Interp::beta_spine` walks, which is the left-hand side of `Cx::w_eq` and
    // therefore the `spine` every consumer below compares against.
    let spine = {
        let former = c.stored_term(&site.ind, &site.inst).ok_or_else(|| bad(CARRIER))?;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        param_tms.iter().fold(former, |f, p| ip.app(f, p.clone()))
    };
    let mut out = Vec::with_capacity(site.n);
    for (i, name) in site.ctors.iter().enumerate() {
        let spec = site.tr.ind.spec.ctors.get(i).ok_or_else(|| bad(BRIDGE))?.clone();
        let cinfo = c.environment().get(name).ok_or_else(|| bad(BRIDGE))?;
        let ctor_ty = ground::subst_ground(cinfo.ty(), cinfo.lparams(), &site.inst);
        let former = c.stored_term(name, &site.inst).ok_or_else(|| bad(BRIDGE))?;
        let param_mems = c.nest_arg_mems(&former, &ctor_ty, param_es, param_tms)?;
        let fields = field_types(&ctor_ty, param_es, spec.order.len());
        let mut rec_eq = Vec::with_capacity(spec.recs);
        for (j, ty) in fields.iter().enumerate() {
            if !matches!(spec.order.get(j), Some(Slot::Rec)) {
                continue
            }
            let ng = spec.rec_dom(rec_eq.len()).len();
            rec_eq.push(rec_slot_eq(c, &spine, ty.as_ref(), ng));
        }
        out.push(CtorBridge { param_mems, rec_eq });
    }
    Ok(out)
}

/// Constructor field `j`'s Lean type, **lifted into the caller's frame**, or
/// `None` from the first field whose binder a later type mentions.
///
/// The parameters are substituted by the caller's own expressions, which is
/// [`Checker::nest_arg_mems`]' own `ty = subst(body, a)` and puts the result in
/// the frame `param_es` are spelled in. The **fields** have no expression at
/// all — [`minor_at`] binds them with kernel scope variables — so each one is
/// instantiated at two distinct closed dummies and the remaining type compared,
/// exactly as `zoneb::rec_field_codomain` treats the binder it peels. A type
/// that does not mention the field comes back as one and the same expression
/// under both, and *that* expression is the caller's own spelling with no depth
/// left to get wrong; a type that does mention it is `None` and its slot gets
/// no bridge.
///
/// The `None` tail is not a loss of generality that matters here: a slot whose
/// `⟦B⟧` mentions an earlier field is not `⟦T p⃗⟧` and its bridge would fail its
/// endpoint check anyway.
fn field_types(ctor_ty: &E, param_es: &[E], nf: usize) -> Vec<Option<E>> {
    let mut out: Vec<Option<E>> = Vec::with_capacity(nf);
    let mut ty = *ctor_ty;
    for p in param_es {
        let Expr::Forall { body, .. } = &ty.clone().view() else {
            out.resize(nf, None);
            return out
        };
        ty = crate::expr::subst(body, p);
    }
    for _ in 0..nf {
        let Expr::Forall { ty: dom, body } = &ty.clone().view() else { break };
        out.push(Some(*dom));
        let at = |l: Level| crate::expr::subst(body, &crate::expr::sort(l));
        let (a, b) = (at(Level::zero()), at(Level::zero().succ()));
        if a != b {
            break
        }
        ty = a;
    }
    out.resize(nf, None);
    out
}

/// `⊢ ⟦B⟧ = ⟦T p⃗⟧` for one recursive slot, or `None` when nothing is owed and
/// when the reduction is not this one.
///
/// `ng` is `|γ⃗|`, the slot's own telescope depth, and the peel is
/// `zoneb::rec_field_codomain` iterated that many times — syntactic, one binder
/// at a time, each body checked at two dummies. At `ng = 0` the slot's type
/// *is* `B`.
///
/// **Asked only when something is owed.** A codomain whose interpretation
/// already is the spine returns before `whnf_conv` is entered, so no
/// declaration that certified before this existed spends a conversion now —
/// the guard `zoneb::ctor_bottom` keeps at its own two bridges, for the same
/// reason: a `whnf_conv` at a term already in weak head normal form is a census
/// entry for a conversion nobody needed.
fn rec_slot_eq(
    c: &mut Checker<'_, '_>,
    spine: &Term,
    ty: Option<&E>,
    ng: usize,
) -> Option<Thm> {
    let mut b = *ty?;
    for _ in 0..ng {
        b = crate::zoneb::rec_field_codomain(&b)?;
    }
    let tm = c.infer_type(&b).ok()?.tm?;
    if tm == *spine {
        return None
    }
    // **`why` is inert at this call and there is no reason of ours to mint.**
    // [`Checker::whnf_conv`] spends it in one place — as the accumulator when
    // `tm` is *absent* — and this call always supplies `⟦B⟧`. Nothing here
    // reports a gap either: a bridge that cannot be built is `None` and the
    // consumer declines under its own name, so a constant named for this site
    // would be a reason nothing produces and a trap for the next reader who
    // greps for it. `Checker::whnf`'s own call passes the same placeholder for
    // the same reason.
    let (_, conv) = c.whnf_conv(&b, Some(tm.clone()), &Gap::NoEndpoint).ok()?;
    let eq = conv.ev.thm()?.clone();
    // Both endpoints, on the way in. The left is what makes the theorem *this*
    // slot's — `whnf_conv` starts from the `Term` it is handed and composes
    // kernel legs onto it, so a mis-read expression yields a true equation
    // about the wrong set — and the right is what makes it usable at all.
    (eq.concl().as_eq() == Some((tm, spine.clone()))).then_some(eq)
}

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
pub(crate) struct Crossing {
    /// `Aⱼ = T(p⃗)`, the fibre summand — the set `rect_step` binds the slot at.
    pub(crate) a: Term,
    /// `β₀(p⃗)`, the telescope's argument type.
    pub(crate) beta0: Term,
    /// `⟦γ⟧`, the interpretation of the same type.
    pub(crate) gamma: Term,
    /// `⊢ β₀(p⃗) = ⟦γ⟧` — `crate::zoneb::CtorEvidence::rec_dom_abbrev` at `p⃗`.
    pub(crate) gamma_ax: Thm,
    /// `⊢ ∀S ∀t. (t ∈ fs(T(p⃗),S) → push(t,β₀(p⃗)) ∈ fs(β₀(p⃗),S))`, at `p⃗`.
    pub(crate) in_funspace: Thm,
    /// `⊢ ∀S ∀t. (t ∈ fs(T(p⃗),S) → pull(push(t,β₀(p⃗)),T(p⃗)) = t)`, at `p⃗`.
    pub(crate) roundtrip: Thm,
    /// `⊢ ∀S ∀g. (g ∈ fs(β₀(p⃗),S) → pull(g,T(p⃗)) ∈ fs(T(p⃗),S))`, at `p⃗` — the
    /// **other** direction's typing, which a *use site* needs where the minor
    /// premise's binder needed [`Crossing::in_funspace`].
    pub(crate) pull_in_funspace: Thm,
    /// `⊢ ∀S ∀g. (g ∈ fs(β₀(p⃗),S) → push(pull(g,T(p⃗)),β₀(p⃗)) = g)`, at `p⃗`.
    pub(crate) pull_roundtrip: Thm,
    /// `⊢ ∀g ∀b. (b ∈ β₀(p⃗) → app(pull(g,T(p⃗)),⟨b,•⟩) = app(g,b))`, at `p⃗`.
    pub(crate) at_tuple: Thm,
    pub(crate) px: Rc<derived::sigma::Push>,
    pub(crate) rx: Rc<derived::sigma::Reindex>,
    pub(crate) tel: Rc<derived::sigma::Telescope>,
}

impl Crossing {
    /// `push(t, β₀(p⃗))` — the interpretation's own function, from the minor
    /// premise's binder.
    pub(crate) fn pushed(&self, t: &Term) -> Term { self.px.of(t.clone(), self.beta0.clone()) }

    /// `pull(g, T(p⃗))` — what `crate::zoneb::rec_slot_terms` put in the
    /// constructor term, at Lean's own function.
    pub(crate) fn pull_of(&self, g: &Term, ps: &[Term]) -> Term {
        self.rx.of(g.clone(), self.tel.ty_of(ps.to_vec()))
    }

    /// `pull(push(t, β₀(p⃗)), T(p⃗))` — the same, at the pushed function.
    fn pulled(&self, t: &Term, ps: &[Term]) -> Term { self.pull_of(&self.pushed(t), ps) }
}

/// The crossing at every recursive slot of constructor `i`, `None` at a plain
/// one.
///
/// Both keyed theorems are built here rather than per level, because both are
/// keyed by the [`Telescope`](derived::sigma::Telescope) and a second build
/// would be a second one.
pub(crate) fn crossings(
    ip: &mut Interp,
    site: &Site,
    cx: &Cx,
    i: usize,
) -> Option<Vec<Option<Crossing>>> {
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
        let (tel, px, rx, in_funspace, roundtrip, pull_in_funspace, pull_roundtrip, at_tuple) = {
            let (kenv, app, _) = ip.ind_parts()?;
            let tel = app.mach.telescope(kenv, ps.len(), &g)?;
            let px = app.push(kenv)?;
            let rx = app.reindex(kenv)?;
            // The slot's stated set really is *this* telescope's — the one
            // whose `push` the walk is about to open a scope with, not a
            // second one of the same shape.
            //
            // **The two are compared at the declaration's own parameters, not
            // at `⟦p⃗⟧`.** `Inductive::ctor_slot_domains` reads `RecArg::summands`,
            // which `Inductive::build` minted as `tel.ty_of(self.params)` — free
            // variables — while everything this walk does is at mini's `⟦p⃗⟧`. At a
            // fibre domain that does not mention a parameter the two spellings
            // are the same term and the distinction is invisible; at
            // `γⱼ(p⃗) = p₀` — a recursive field whose domain **is** the
            // declaration's own parameter — they are different terms and this
            // guard fired on a declaration it was built to admit
            // (`good/tutorial/113`, `114`). `a` is then re-stated at `⟦p⃗⟧`,
            // which is the frame `Crossing::a` is consumed in: `minor_at` opens
            // the slot's scope at `fs(a, W)` and `derived`'s own statement
            // arrives there through `Cx::psub`.
            let own: Vec<Term> = cx.ind.params.iter().map(|v| Term::var(*v)).collect();
            if a != tel.ty_of(own) {
                return None
            }
            let proj = &app.mach.proj;
            let inf = derived::sigma::push_in_funspace(kenv, &s, &tel, &px, &fs_app_mem)?;
            let rt = derived::sigma::push_pull_roundtrip(
                kenv, &s, proj, &tel, &rx, &px, &fs_app_mem, &fun_ext,
            )?;
            let pinf =
                derived::sigma::reindex_in_funspace(kenv, &s, proj, &tel, &rx, &fs_app_mem)?;
            let prt = derived::sigma::pull_push_roundtrip(
                kenv, &s, proj, &tel, &rx, &px, &fs_app_mem, &fun_ext,
            )?;
            let att = derived::sigma::reindex_at_tuple(kenv, &s, proj, &tel, &rx)?;
            (tel, px, rx, inf, rt, pinf, prt, att)
        };
        let in_funspace = derived::inst_all(&in_funspace, &cx.ps)?;
        let roundtrip = derived::inst_all(&roundtrip, &cx.ps)?;
        let pull_in_funspace = derived::inst_all(&pull_in_funspace, &cx.ps)?;
        let pull_roundtrip = derived::inst_all(&pull_roundtrip, &cx.ps)?;
        let at_tuple = derived::inst_all(&at_tuple, &cx.ps)?;
        // …and re-stated at `⟦p⃗⟧`, which is the frame `Crossing::a` is consumed
        // in — see the guard above.
        let a = tel.ty_of(cx.ps.clone());
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
            pull_in_funspace,
            pull_roundtrip,
            at_tuple,
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
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
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
            return Err(Gap::Recursor(site.ind, why, Cause::Library))
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
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let key = (site.ind, site.inst.clone());
    let dep = {
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        app.dep_recursor(kenv, &key, &cx.ind).ok_or({
            Gap::Recursor(
                site.ind,
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
            return Err(Gap::Recursor(site.ind, why, Cause::Library))
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
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
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
    // `drec` is assembled inside `derived`, which while decomposability was a
    // property of who built a term left the λ above it unable to skeletonise
    // its body. One abbreviation over the nest's own binders fixes it, exactly
    // as `zoneb`'s constructor bottom does.
    let raw = ap.apply(derived::subst_term(&dr.rec, &sub), cx.t_tm.clone());
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
        let key = (site.rec, site.rec_inst.clone());
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
    // The two conversions this walk cannot mint, minted by whoever held the
    // `Checker` — see [`CtorBridge`]. The arity is checked here rather than at
    // each read, so a bridge list built for another declaration cannot supply
    // one slot's equation at another slot's index.
    let bridge = at.bridges.get(i)?;
    if bridge.param_mems.len() != cx.ps.len() || bridge.rec_eq.len() != m {
        return None
    }

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
    // **The statement's own induction-hypothesis binder at a function-typed
    // slot, which is not the walk's.** `derived` quantifies `vⱼ` with *no* set
    // typing — only the pointwise family — and applies the minor at
    // `push(vⱼ, β₀(p⃗))`. The walk's binder is the interpretation's, typed at
    // `⟦∀z:γ, C (f z)⟧`, and the two are related by [`ih_transport`] and not by
    // an instantiation, so the statement gets a variable of its own.
    let mut ih_vs: Vec<Option<FreeVar>> = vec![None; m];
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
                let cod_eq = bridge.rec_eq.get((*at_slot)?)?.as_ref();
                let gm = push_into_pi(ip, cx, cr, &wt, &wm, &shape.dom(), cod_eq)?;
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
                let vj = (!prop).then(|| ip.env.fresh_var());
                let vt = vj.map(Term::var);
                ih_vs[j] = vj;
                ih_imp[k + m + j] =
                    Some(ih_transport(ip, cx, cr, &rec_ws[j], vt.as_ref(), &shape.dom())?);
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
    // **The constructor's own parameter domains, not the recursor's.** See
    // [`CtorBridge::param_mems`]: `beta_spine`'s premise is at the λ's own
    // domain and `⟦T.ctorᵢ⟧`'s outermost λ was built over the *constructor's*
    // declared binder, which Lean need not spell the way the type former does.
    let mut sp_mems = bridge.param_mems.clone();
    sp_mems.extend(wmems[..k + m].iter().cloned());
    let (_, ceq) = ip.beta_spine(&at.ctor_formers[i], &sp_args, &sp_mems)?;
    // `Translated::ctor_abbrev` is stated over `p⃗ ++ f⃗`, which is `sp_args`.
    let cax = derived::inst_all(&site.tr.ctor_abbrev[i], &sp_args)?;
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
    // What the *statement* instantiates each level at. At an
    // induction-hypothesis level of a function-typed slot that is not the walk's
    // own binder but `push(vⱼ, β₀(p⃗))`, which is what `dep_minor` applies the
    // minor to — see [`ih_transport`].
    let args: Vec<Term> = (0..nlev)
        .map(|l| {
            if l < k + m {
                return ws[l].clone()
            }
            let j = l - (k + m);
            match (prop, ih_vs[j], cross[j].as_ref()) {
                (true, _, _) => point.clone(),
                (false, Some(v), Some(cr)) => cr.pushed(&Term::var(v)),
                _ => ws[l].clone(),
            }
        })
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
    // The induction hypotheses the **atoms** are stated about, which is
    // `args[k+m..]` at every slot but a function-typed one, where the atom is
    // about `vⱼ` and the instantiation is about `push(vⱼ, β₀(p⃗))`.
    let vs: Vec<Term> = (0..m)
        .map(|j| match (prop, ih_vs[j]) {
            (true, _) => point.clone(),
            (false, Some(v)) => Term::var(v),
            (false, None) => ws[k + m + j].clone(),
        })
        .collect();
    let vvs: Vec<FreeVar> = (0..m).map(|j| ih_vs[j].unwrap_or(wvs[k + m + j])).collect();

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
    for (j, c) in cross.iter().take(m).enumerate() {
        // A function-typed slot's scope *is* `derived`'s set; the plain one's
        // is the applied spine and needs the carrier equation — and, where the
        // slot's Lean type only *reduces* to the spine, that equation composed
        // with the reduction. `052_reduceCtorParam`'s field is
        // `constType (T α) (T α)`: the walk opened its scope at `⟦that⟧` and
        // `rect_step`'s atom is at `W`, two rewrites apart rather than one.
        if c.is_some() {
            set_eq.push(None);
            continue
        }
        set_eq.push(match bridge.rec_eq.get(j).and_then(|o| o.as_ref()) {
            None => Some(back.clone()),
            Some(eq) => derived::eq_symm(&mut ip.env, eq)
                .and_then(|to_cod| eq_trans(ip, &back, &to_cod)),
        });
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
///
/// `cod_eq` is [`CtorBridge::rec_eq`] at this slot — `⊢ ⟦B⟧ = ⟦T p⃗⟧` where the
/// field's Lean codomain only *reduces* to the spine, and `None` where it
/// spells it, which is every declaration in the corpus but two. Step 5 composes
/// it in; nothing else about the chain changes.
#[allow(clippy::too_many_arguments)]
fn push_into_pi(
    ip: &mut Interp,
    cx: &Cx,
    cr: &Crossing,
    t: &Term,
    t_mem: &Thm,
    dom: &Term,
    cod_eq: Option<&Thm>,
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
    let unbridge = derived::eq_symm(&mut ip.env, &bridge)?;
    // **The codomain has to reach the spine, and it need not *spell* it.** A
    // field written `∀z:α. constType (T α) (T α)` is a recursive argument —
    // `zoneb::rec_field` classifies it by its reduct and the constructor's own
    // nest bottom already bridges the same step — and its `⟦B⟧` is an
    // application term while `mem` has arrived at `fs(⟦γ⟧, ⟦T p⃗⟧)`. One
    // congruence at the funspace's **second** argument closes the gap, and it
    // is composed onto `dprod_is_fs`'s own equation rather than spent
    // separately. A codomain that is the spine composes nothing.
    let to_dom = if cod == spine {
        unbridge
    } else {
        let eq = cod_eq?;
        // Both endpoints. This equation is spent at a *set* argument, where a
        // theorem about some other set rewrites a well-formed `fs` into a
        // well-formed `fs` about the wrong carrier and nothing downstream looks
        // at the codomain again — the final `Formula::mem` check below compares
        // the `dprod`, not what it was reached through.
        if eq.concl().as_eq() != Some((cod.clone(), spine.clone())) {
            return None
        }
        let to_cod = derived::eq_symm(&mut ip.env, eq)?;
        let onto_cod = derived::congr_arg(
            &mut ip.env,
            fs_sym,
            &[gamma.clone(), spine.clone()],
            1,
            &to_cod,
        )?;
        derived::eq_trans(&mut ip.env, &onto_cod, &unbridge)?
    };
    let out = ip.retarget_set(&mem, &to_dom)?;
    let _ = s;
    (*out.concl() == Formula::mem(cr.pushed(t), dom.clone())).then_some(out)
}

/// `Γ ⊢ pull(g, T(p⃗)) ∈ fs(Aⱼ, W)` from `Γ ⊢ g ∈ ⟦γ → T p⃗⟧` — [`push_into_pi`]
/// **run the other way**, for a *use site*.
///
/// The minor premise's own binder crosses with `push`, because the walk opens
/// the slot's scope at `derived`'s set and has to hand the interpretation an
/// element of `⟦γ → T p⃗⟧`. A **use site** starts on the other side: `whnf`
/// holds Lean's own `⟦f⟧` and the ι rule quantifies its recursive slot at
/// `fs(Aⱼ,W)`, so what has to be produced is the *pulled* function — the very
/// term `crate::zoneb::rec_slot_terms` put inside `⟦T.ctorᵢ f⟧`, which is why
/// the ι rule's own left-hand side already mentions it.
///
/// ```text
/// 1.  g ∈ ⟦γ → T p⃗⟧ = dprod(b,⟦γ⟧)            the use site's own typing
/// 2.  fs(⟦γ⟧,⟦T p⃗⟧) = dprod(b,⟦γ⟧)            Interp::dprod_is_fs, reversed
/// 3.  fs(⟦γ⟧,·) ↦ fs(β₀(p⃗),·)                 congr_arg at argument 0
/// 4.  fs(·,⟦T p⃗⟧) ↦ fs(·,W)                   congr_arg at argument 1
/// 5.  pull(g,T(p⃗)) ∈ fs(T(p⃗),W)               sigma::reindex_in_funspace
/// ```
///
/// Steps 2–4 are `crate::zoneb`'s constructor bottom, at a use site rather than
/// inside a λ-nest; the difference is only where the two equations come from —
/// `Crossing::gamma_ax` and `Cx::w_eq` rather than the walk's own frame.
pub(crate) fn pull_from_pi(
    ip: &mut Interp,
    cx: &Cx,
    cr: &Crossing,
    g: &Term,
    g_mem: &Thm,
    cod_eq: Option<&Thm>,
) -> Option<(Thm, Thm)> {
    let s = ip.prelude.tower.sums.clone();
    let dom = g_mem.concl().as_mem()?.1;
    let PiShape::Dep { site: fsite, dom: gamma } = ip.as_pi(&dom)? else { return None };
    if gamma != cr.gamma {
        return None
    }
    let spine = cx.w_eq.concl().as_eq()?.0.clone();
    let (cod, bridge) = ip.dprod_is_fs(&fsite, &gamma)?;
    let mem = ip.retarget_set(g_mem, &bridge)?;

    let fs_sym = ip.prelude.fs_sym();
    // [`push_into_pi`]'s composition, in the direction a use site travels: the
    // reduction lands on `fs(⟦γ⟧, ⟦B⟧)` and the three rewrites below are stated
    // at `fs(⟦γ⟧, ⟦T p⃗⟧)`, so the codomain moves first and once.
    let mem = if cod == spine {
        mem
    } else {
        let eq = cod_eq?;
        if eq.concl().as_eq() != Some((cod.clone(), spine.clone())) {
            return None
        }
        let onto_spine =
            derived::congr_arg(&mut ip.env, fs_sym, &[gamma.clone(), cod], 1, eq)?;
        ip.retarget_set(&mem, &onto_spine)?
    };
    let back = derived::eq_symm(&mut ip.env, &cr.gamma_ax)?;
    let onto_beta =
        derived::congr_arg(&mut ip.env, fs_sym, &[gamma, spine.clone()], 0, &back)?;
    let mem = ip.retarget_set(&mem, &onto_beta)?;
    let onto_w = derived::congr_arg(
        &mut ip.env,
        fs_sym,
        &[cr.beta0.clone(), spine],
        1,
        &cx.w_eq,
    )?;
    let mem = ip.retarget_set(&mem, &onto_w)?;

    let rule = derived::inst_all(&cr.pull_in_funspace, &[cx.w_term.clone(), g.clone()])?;
    let out = Thm::mp(&rule, &mem)?;
    let want =
        Formula::mem(cr.pull_of(g, &cx.ps), s.fs.of(cr.a.clone(), cx.w_term.clone()));
    // The `fs(β₀(p⃗), W)` typing is returned as well as consumed: it is the
    // hypothesis of `sigma::pull_push_roundtrip`, which the same caller spends
    // to recognise the pushed pull in the ι rule's right-hand side as the
    // `⟦f⟧` Lean's own right-hand side names. Deriving it twice would be two
    // derivations of one fact, which is `MINI-HANDOFF.md` §2's pattern.
    (*out.concl() == want).then_some((out, mem))
}

/// `⊢ (∀z. (z ∈ Aⱼ → ν(z) ∈ app(C, app(t,z)))) → ν̂ ∈ ⟦∀z:γ, C (f z)⟧` — the
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
/// `v` says which of §6.2's two columns is being crossed, and everything that
/// differs between them follows from it:
///
/// | | `v = None` (`u₁ = 0`) | `v = Some(vⱼ)` (`u₁ ≥ 1`) |
/// |---|---|---|
/// | `ν(z)` | `•`, by proof irrelevance | `app(vⱼ, z)` |
/// | the `Π` | a conditional singleton | `dprod(q⃗, ⟦γ⟧)` |
/// | the introduction | [`Interp::cond_lam_typing`] | [`Interp::push_lam_typing`] |
/// | `ν̂` | `•` | `push(vⱼ, β₀(p⃗))` |
/// | the binder's own scope | `⟦γ⟧` | `β₀(p⃗)` |
///
/// The last row is not a taste: `cond_lam_typing` states its family at the
/// domain the conditional singleton was built at, which is the
/// interpretation's `⟦γ⟧`, while `lam_in_dprod_n` states `push(v,A)` at the `A`
/// the family ranges over — and the term `derived`'s `DEPᵢ` names is
/// `push(vⱼ, β₀(p⃗))`, so the family has to range over `β₀(p⃗)` and the
/// resulting `dprod(q⃗, β₀(p⃗))` is moved onto the minor's own
/// `dprod(q⃗, ⟦γ⟧)` by one `congr_arg`. That is the mirror of what
/// [`push_into_pi`] does at the *field*, and for the same reason.
fn ih_transport(
    ip: &mut Interp,
    cx: &Cx,
    cr: &Crossing,
    t: &Term,
    v: Option<&Term>,
    dom: &Term,
) -> Option<Thm> {
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();
    let point = ip.point();
    let shape = ip.as_pi(dom)?;
    if shape.dom() != cr.gamma {
        return None
    }
    // What the induction hypothesis's value at a point is, in each column.
    let value = |x: &Term| match v {
        None => point.clone(),
        Some(vt) => ap.apply(vt.clone(), x.clone()),
    };

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
                value(&tz),
                ap.apply(cx.c_tm.clone(), ap.apply(t.clone(), tz)),
            ),
        ),
    );

    let mut sc = Scopes::new();
    let (tok_a, h) = sc.assume(atom.clone());
    let bdom = match v {
        None => cr.gamma.clone(),
        Some(_) => cr.beta0.clone(),
    };
    let tok_b = sc.open(&mut ip.env, bdom);
    let (bv, bt, bm) = {
        let scope = sc.get(0)?;
        (scope.var(), scope.term(), scope.assumption().clone())
    };

    // `b ∈ ⟦γ⟧` is `b ∈ β₀(p⃗)`, which is what both the telescope's own
    // introduction rule and `Push::app`'s side condition are stated at.
    let b_in_beta = match v {
        None => {
            let back = derived::eq_symm(&mut ip.env, &cr.gamma_ax)?;
            ip.retarget_set(&bm, &back)?
        }
        Some(_) => bm.clone(),
    };

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
    let subject = value(&tup);
    let leib = Thm::eq_leibniz(
        lhs.clone(),
        rhs.clone(),
        hole,
        Formula::mem(subject.clone(), ap.apply(cx.c_tm.clone(), Term::var(hole))),
    );
    let moved = Thm::mp(&Thm::mp(&leib, &beta)?, &val)?;

    // …which is the minor's own fibre at `b`, and then the `Π` it belongs to.
    let out = match (&shape, v) {
        (PiShape::Prop { site: inner, .. }, None) => {
            let onto = ip.to_cond_fibre(inner, bv, &moved)?;
            let family = sc.close(tok_b).discharge(&onto).ok()?;
            ip.cond_lam_typing(inner, cr.gamma.clone(), &family)?
        }
        (PiShape::Dep { site: inner, .. }, Some(vt)) => {
            let onto = ip.to_fibre_set(inner, bv, &moved)?;
            // `app(v, ⟨b,•⟩)` is `Q(v,b)`, which is the form
            // `lam_in_dprod_n` pins its body condition at.
            let bx = derived::inst_all(&cr.px.body_ax, &[vt.clone(), bt.clone()])?;
            let onto = ip.retarget_subject(&onto, &bx)?;
            let family = sc.close(tok_b).discharge(&onto).ok()?;
            let raw = ip.push_lam_typing(&cr.px, inner, vt, cr.beta0.clone(), &family)?;
            // `dprod(q⃗, β₀(p⃗))` is the minor's own `dprod(q⃗, ⟦γ⟧)`.
            let mut args = inner.holes.clone();
            args.push(cr.beta0.clone());
            let idx = args.len() - 1;
            let onto_gamma =
                derived::congr_arg(&mut ip.env, inner.dp.dprod, &args, idx, &cr.gamma_ax)?;
            ip.retarget_set(&raw, &onto_gamma)?
        }
        _ => return None,
    };
    let landed = match v {
        None => point,
        Some(vt) => cr.pushed(vt),
    };
    if *out.concl() != Formula::mem(landed, dom.clone()) {
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
        // **At `⟦p⃗⟧`, not at the declaration's own parameter variables.** A
        // general constructor's term dispatches over its fibre summands
        // `Σ(z::γⱼ(p⃗))`, so it *mentions* the parameters — and
        // `Inductive::ctor_term` states them at `Inductive::params`, free
        // variables of `derived`'s own, while everything in this walk is at
        // mini's `⟦p⃗⟧`. The mixture is what `ctor_term_at`'s own header calls
        // "half at its own variables and half at the declaration's, which is not
        // a constructor application of anything", and the comparison below
        // rejected it — so this was fail-closed and not wrong, but it declined
        // every parameterised declaration with a function-typed slot. Invisible
        // at `γ` closed, where the summands mention no parameter: that is the
        // same axis [`crossings`]' guard was wrong on, one construction later,
        // and `P.c` in `a_function_typed_recursive_slot_stops_…` is the cell
        // for both.
        let (got, at_hole) = {
            let (_, app, _) = ip.ind_parts()?;
            (
                cx.ind.ctor_term_at(&app.mach, i, ys, &ts, &cx.ps)?,
                cx.ind.ctor_term_at(&app.mach, i, ys, &ts_hole, &cx.ps)?,
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
///
/// # Sequential, where [`derived::subst_term`] is simultaneous — and why the
/// # two never diverge here
///
/// This folds `Formula::subst`, so a later pair substitutes into an earlier
/// pair's *result*; the theorem this formula is compared against was produced
/// by [`derived::inst_all`], which closes every variable before opening any
/// argument and is therefore simultaneous. The two agree because the two sides
/// of `subs` are **disjoint by construction**: the domain is `derived`'s own
/// declaration variables and the range is built from mini's nest binders, so no
/// argument mentions a later variable and there is nothing for a second pass to
/// reach.
///
/// If that ever stopped holding the consequence is a **decline**, not a wrong
/// theorem: every consumer of `subst_f` uses it as an oracle — `if *thm.concl()
/// != subst_f(…) { return Err(…) }` — so a divergence fails the comparison.
/// The term half is not folded at all; it is [`derived::subst_term`], which is
/// simultaneous outright and which this module used to spell for itself.
pub(crate) fn subst_f(f: &Formula, subs: &[(FreeVar, Term)]) -> Formula {
    subs.iter().fold(f.clone(), |acc, (v, t)| acc.subst(*v, t))
}

/// The ground numeral of a `Sort`, or `None` at anything else — used to read
/// the rung a motive's own *type* inhabits.
///
/// Shared with [`crate::rec_ix_dep`], which needs the sort `infer_type` gave
/// the motive binder's type rather than the one the motive lands in; see that
/// module's header for why the two rungs differ and why it is the outer one.
pub(crate) fn sort_of(ty: &E) -> Option<u32> {
    let Expr::Sort(l) = &ty.view() else { return None };
    ground::eval(l, &Default::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, lam, sort, Level};
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
        let ty0 = sort(Level::zero().succ());
        let no: Rc<[Level]> = Vec::new().into();
        let spine = |d: u32| app(konst(l, no.clone()), bvar(d));
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: l,
                lparams: vec![],
                num_params: 1,
                ty: forall(ty0, ty0),
                ctors: vec![
                    (nil, forall(sort(Level::zero().succ()), spine(0))),
                    (
                        cons,
                        forall(
                            sort(Level::zero().succ()),
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
            let t = c.infer_type(&konst(rec, at)).expect("infer ⟦L.rec⟧");
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
        let Expr::Forall { ty: d, body } = &ty.view() else { panic!("fewer than {depth} binders") };
        forall(*d, with_codomain(body, depth - 1, cod))
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
            c.infer_type(&konst(l, Vec::new().into())).expect("carrier");
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
        c.infer_type(&konst(rec, at)).expect("infer ⟦L.rec.{1}⟧");
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
    /// | `P.c : (α → P α) → P α`, `np = 1` | interpreted | interpreted |
    ///
    /// **`P` is the `np ≥ 1` row and it was added after the fact.** Every other
    /// cell here is `np = 0`, so every `γ` is a *closed* set and a term stated
    /// at `Inductive::params` is the same term as one stated at `⟦p⃗⟧`. Two
    /// separate frame bugs in this module lived behind that degeneracy —
    /// [`crossings`]' guard and [`ctor_at_binders`]' constructor term — and both
    /// go red on this one row. See its own comment below.
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
        let ty0 = sort(Level::zero().succ());
        let no: Rc<[Level]> = Vec::new().into();
        let (t, a, b, cc, p) = (nm("T"), nm("A"), nm("B"), nm("C"), nm("P"));
        let (q, r) = (nm("Q"), nm("R"));
        let spine = konst(t, no.clone());
        let pspine = konst(p, no.clone());
        let qspine = konst(q, no.clone());
        let rspine = konst(r, no.clone());
        let enum_of = |n: &Name| konst(*n, no.clone());

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
        let only = forall(forall(enum_of(&a), spine), spine);
        let mixed = forall(
            spine,
            forall(
                forall(enum_of(&a), spine),
                forall(forall(enum_of(&b), spine), spine),
            ),
        );

        let general = |ctor_ty: E| {
            let mut env = Environment::empty();
            for e in [&a, &b, &cc] {
                crate::kernel::add(
                    &mut env,
                    &Declaration::Inductive {
                        name: *e,
                        lparams: vec![],
                        num_params: 0,
                        ty: ty0,
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
                    name: t,
                    lparams: vec![],
                    num_params: 0,
                    ty: ty0,
                    ctors: vec![(Name::str(&t, "c"), ctor_ty)],
                },
            )
            .expect("the checker accepts a function-typed recursive argument");
            (env, t, Name::str(&t, "rec"))
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
            forall(enum_of(&a), spine),
            forall(
                enum_of(&a),
                forall(
                    forall(enum_of(&b), spine),
                    forall(forall(enum_of(&cc), spine), spine),
                ),
            ),
        );

        // **`P (α : Type) : Type | c : (α → P α) → P α` — the slot's fibre is the
        // declaration's own parameter**, which is the axis every other cell in
        // this test leaves at zero: `T`, `A`, `B` and `C` are all `np = 0`, so
        // `γ` is a *closed* set in every one of them.
        //
        // It is the axis [`crossings`] was wrong on. `Inductive::ctor_slot_domains`
        // hands back `RecArg::summands`, stated at the declaration's own
        // parameter **variables**, and the guard compared it against
        // `tel.ty_of(⟦p⃗⟧)` — mini's interpreted parameters. A `γ` that mentions
        // no parameter makes `ty_of` constant, so the two spellings coincide and
        // nothing in the tree could see the difference; `γ(p⃗) = p₀` is the
        // shortest declaration at which they are different terms, and there the
        // guard refused a declaration it exists to admit.
        //
        // **It covers two bugs on that one axis, not one.** Behind `crossings`
        // was [`ctor_at_binders`], which built the constructor term with
        // `Inductive::ctor_term` — `ctor_term_at` at `Inductive::params` — while
        // the walk is at `⟦p⃗⟧`; a general constructor's term mentions the
        // parameters through its fibre summands, so that mixture is the same
        // frame error one construction later, and it is the same closed-`γ`
        // degeneracy that hid it. Both were seen red here, at both `u₁`.
        //
        // `good/tutorial/113_reduceCtorParamRefl` and `114` are the corpus's
        // witnesses and they stop one construction further on, at a *codomain*
        // spelled through a reducible definition; this cell is that shape with
        // the alias taken out, so it isolates the frame.
        let param_slot = forall(
            ty0,
            forall(forall(bvar(0), app(pspine, bvar(1))), app(pspine, bvar(1))),
        );
        let parameterised = || {
            let mut env = Environment::empty();
            crate::kernel::add(
                &mut env,
                &Declaration::Inductive {
                    name: p,
                    lparams: vec![],
                    num_params: 1,
                    ty: forall(ty0, ty0),
                    ctors: vec![(Name::str(&p, "c"), param_slot)],
                },
            )
            .expect("a function-typed slot at the parameter is accepted");
            (env, p, Name::str(&p, "rec"))
        };

        // `T.e : (A → B → T) → T` — the slot's `γ` is **two** binders deep, a
        // currying rather than a reindexing, which `derived::sigma` refuses on
        // both operators for a stated reason.
        let deep = forall(forall(enum_of(&a), forall(enum_of(&b), spine)), spine);

        // ── the two reducible aliases, which surface Lean cannot write ──────
        //
        // **`052_reduceCtorParam`, `113` and `114` are hand-built kernel
        // tests, and the reason they have to be is measurable.** Writing
        // `inductive T (α : id Type) : Type` puts the alias on the type
        // former, on every constructor *and* on the generated recursor at
        // once — one uniform frame, which exercises nothing and declines
        // earlier under `ind-spec(T: type former spine)` because the former's
        // own binder is then not a `Sort`. That was tried;
        // `mini/tests/fixtures/reducible_ctor_binders.lean` records it, and
        // carries the half surface syntax *can* express.
        //
        // The alias here is a **β-redex**, `(λx:Sort 2. x) (Sort 1)`, and not
        // a `Definition`: it reduces by β alone, so these two cells depend on
        // no other declaration and cannot be weakened by one becoming
        // reducible or not. `alias(e, s)` is `e` behind one such redex whose
        // binder is at `Sort s` — the sort of `e`'s own **type**, which is one
        // rung apart in the two uses below and is the whole reason it is a
        // parameter rather than a constant.
        let alias = |e: E, s: Level| app(lam(sort(s), bvar(0)), e);
        let ty0_alias = alias(ty0, Level::zero().succ().succ());

        // **`Q (α : Type 0) : Type 0 | c : Q α → Q α`, with the constructor's
        // *parameter binder* written as the alias.** The type former's is
        // `Sort 1` and `crate::kernel::add` generates the recursor from the
        // former, so the recursor's is `Sort 1` too — which is exactly the
        // corpus shape: `⟦Q.c⟧`'s outermost λ is at `⟦(λx.x) (Sort 1)⟧` and
        // the walk arrives holding `⟦p⟧ ∈ ⟦Sort 1⟧`.
        //
        // `Interp::beta_spine` checks its per-level premise against the λ's
        // *own* domain, so this was a bare `return None` inside `minor_at` and
        // the whole eliminator declined as `MINOR`. The recursive slot is
        // spelled as the spine, so nothing else is owed and this cell isolates
        // the parameter frame.
        let q_ctor = forall(ty0_alias, forall(app(qspine, bvar(0)),
            app(qspine, bvar(1))));
        let param_binder = || {
            let mut env = Environment::empty();
            crate::kernel::add(
                &mut env,
                &Declaration::Inductive {
                    name: q,
                    lparams: vec![],
                    num_params: 1,
                    ty: forall(ty0, ty0),
                    ctors: vec![(Name::str(&q, "c"), q_ctor)],
                },
            )
            .expect("a constructor's parameter binder may reduce to the type former's");
            (env, q, Name::str(&q, "rec"))
        };

        // **`R (α : Type 0) : Type 0 | c : ((λX.X) (R α)) → R α`** — the
        // *plain* recursive slot's type only reduces to the spine.
        // `zoneb::rec_field` classifies the field by its reduct, so the slot is
        // recursive and `rect_step`'s atom is at the carrier; the walk's own
        // binder is at `⟦(λX.X) (R α)⟧`, two rewrites from it rather than one.
        // `052`'s field is `constType (T α) (T α)`, the same shape behind a
        // `def` — and `mini/tests/fixtures/reducible_ctor_binders.lean`'s `Cod`
        // is that spelling end to end.
        let r_ctor = forall(
            ty0,
            forall(
                alias(app(rspine, bvar(0)), Level::zero().succ()),
                app(rspine, bvar(1)),
            ),
        );
        let plain_cod = || {
            let mut env = Environment::empty();
            crate::kernel::add(
                &mut env,
                &Declaration::Inductive {
                    name: r,
                    lparams: vec![],
                    num_params: 1,
                    ty: forall(ty0, ty0),
                    ctors: vec![(Name::str(&r, "c"), r_ctor)],
                },
            )
            .expect("a plain recursive field may only reduce to the spine");
            (env, r, Name::str(&r, "rec"))
        };

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
            ("T.c: one function-typed slot", general(only), [Want::Interp, Want::Interp]),
            ("T.d: a mixed constructor", general(mixed), [
                Want::Named(MIXED),
                Want::Named(MIXED),
            ]),
            ("T.f: Rec, Plain, Rec, Rec", general(three), [Want::Interp, Want::Interp]),
            ("T.e: γ at depth 2", general(deep), [Want::Spec, Want::Spec]),
            ("P.c: the slot's fibre is the parameter", parameterised(), [
                Want::Interp,
                Want::Interp,
            ]),
            ("Q.c: the ctor's parameter binder is an alias", param_binder(), [
                Want::Interp,
                Want::Interp,
            ]),
            ("R.c: a plain recursive field is an alias", plain_cod(), [
                Want::Interp,
                Want::Interp,
            ]),
        ];

        for (label, (env, ind, rec), wants) in cells {
            for (u1, want) in [1u32, 0].into_iter().zip(wants) {
                let mut ip = Interp::new();
                let mut c = Checker::threaded(&env, &mut ip);
                let at: Rc<[Level]> = vec![level(u1)].into();
                let got = c
                    .infer_type(&konst(rec, at))
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
                        Some(&Gap::Recursor(ind, why, Cause::Library)),
                        "{label} u₁={u1}: the crossing must decline by *this* name, on \
                         the library axis"
                    ),
                    Want::Spec => assert_eq!(
                        got.ev.gap(),
                        Some(&Gap::IndSpec(
                            ind,
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
