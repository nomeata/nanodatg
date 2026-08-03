//! **A projection out of a class-(T) structure at a *data* field** — the term
//! (`MINI-HANDOFF.md` §11's row 4, `SCOPING.md` §9's construction 3).
//!
//! # Interface
//!
//! ```text
//! proj_data::term(mach, j, z)                  -> Term        ⟦proj[T,j] s⟧
//! proj_data::computes(env, mach, ind, j, y⃗)    -> Option<Thm> ⊢ πⱼ(ctor₀(y⃗)) = yⱼ
//! ```
//!
//! Nothing consumes either yet, and that is deliberate — see *What is missing*
//! below, and `MINI-HANDOFF.md` §2's two counter-examples for why a value with
//! a named future consumer is kept rather than re-derived.
//!
//! # Route (b), and the term it produces
//!
//! `Prod.fst := fun α β self => proj[Prod,0] self` projects at a **variable**,
//! so `whnf`'s proj-of-ctor step never fires and `⟦projⱼ x⟧` has to be a real
//! term. Two routes were scoped and route (b) — the carrier's own structure —
//! was chosen on an invariant: route (a), via the eliminator, would make
//! `whnf`'s `Expr::Proj` arm rewrite a `Proj` node into a `rec` application,
//! changing `cur` into an expression that is **not a subterm of its input**,
//! which every other arm preserves.
//!
//! Route (b) is a pure composite of term-formers `derived` already has, and it
//! is shorter than the scope suggests because *every layer of a class-(T)
//! carrier element is a Kuratowski pair*:
//!
//! ```text
//! ctor₀(y⃗)  =  sup( Inj₀(tuple(y⃗)), f(∅) )       Inductive::ctor_term
//!           =  ⟨ ⟨∅, ⟨y₀, ⟨y₁, … ⟨y_{k-1}, •⟩…⟩⟩⟩ , f(∅) ⟩
//! ```
//!
//! — `sup(a,f)` is `⟨a,f⟩`, `Inj₀(x)` unfolds to `inl(x) = ⟨∅,x⟩`, and
//! `Telescope::tuple_of` is the right-nested pair chain. So
//!
//! ```text
//! πⱼ(z)  :=  compⱼ( π₂( π₁ z ) )  =  π₁(π₂ʲ(π₂(π₁ z)))
//! ```
//!
//! reaches field `j` in `j + 3` projections, and its computation rule is `j + 3`
//! instantiations of [`Proj::fst`](derived::proj::Proj) /
//! [`Proj::snd`](derived::proj::Proj) plus the injection's defining equation —
//! **all unconditional**, no Separation, no induction, and no hypothesis about
//! `z` at all. [`computes`] is that chain and `tests` cashes it.
//!
//! # What is missing, and it is **not** a term — the scope said it was
//!
//! *(`SCOPING.md` §9's construction 3 and `MINI-HANDOFF.md` §11's row 4 both
//! record this row as owing "a **term** — the only one that does", against
//! three sibling rows owing only a certificate. The term is above and it is
//! the small half. What the row also owes, and neither note says, is a
//! **theorem**, and it is `derived/`'s by every criterion the other three rows
//! were split on.)*
//!
//! The constant's obligation is `⊢ ⟦Prod.fst.{σ}⟧ ∈ ⟦ty[σ]⟧`, and mini's λ
//! clause reduces it to the nest bottom's
//!
//! ```text
//! Γ, self ∈ ind(⟦α⟧,⟦β⟧)  ⊢  πⱼ(self) ∈ βⱼ(⟦α⟧,⟦β⟧, π₀(self), …, π_{j-1}(self))
//! ```
//!
//! and **nothing in `derived/` states that.** [`computes`] is about a
//! constructor term; this is about an arbitrary carrier element, and getting
//! from one to the other is exactly the inversion the non-indexed carrier does
//! not have ([`Ctor`](derived::inductive::Ctor) has `mem` and `inj` only).
//! Composing `Telescope::proj_mem[j]` with `ISumSyms::no_junk` and
//! `bound::w_inversion_at` would do it and costs two existential eliminations;
//! the cheaper route is the one its three siblings already take:
//!
//! ```text
//! decl_rect at   φ(z) := πⱼ(z) ∈ βⱼ(p⃗, π₀(z), …, π_{j-1}(z))
//!
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π₀ z, …, π_{j-1} z) )
//! ```
//!
//! whose single induction step is `∀y⃗. (⋀ yq ∈ βq(p⃗,y⃗<q) → φ(ctor₀(y⃗)))`, and
//! `φ(ctor₀(y⃗))` is `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` — conjunct `j` of its own antecedent —
//! after `j + 1` rewrites by [`computes`]. So it is `decl_rect` at a φ that is
//! *not* constant in `z`, which is the only structural difference from
//! [`DeclFields`](derived::inductive::DeclFields), and it is the **fourth
//! member of the same family**:
//!
//! | class | major premise | φ | where |
//! |---|---|---|---|
//! | (S) | `• ∈ A_φ(p⃗)` | constant | `family::le_prop_fields` |
//! | (P) | `• ∈ ‖ind(p⃗)‖` | constant | `family::trunc_fields` |
//! | (T), `Prop` fields | `z ∈ ind(p⃗)` | constant | `decl_fields` |
//! | **(T), data fields** | `z ∈ ind(p⃗)` | **`πⱼ(z) ∈ βⱼ(…)`** | **unbuilt** |
//!
//! **Why `derived/` and not here**, on the same three grounds row 2 was split
//! on: it mentions no Lean syntax and no `Expr` at all; it is the fourth member
//! of a family whose other three live in `derived/src/inductive/`; and its
//! step wants `inductive::rec_shared`'s `rewrite_under`, which is private to
//! that module. Mini's side is then a fourth branch in [`crate::proj_prop`]
//! plus [`term`] above, and the routing already keys on which store holds the
//! declaration.
//!
//! **The σ question answers "the same" here**, unlike on row 2: `Prod.fst`'s
//! field sort is `Sort (u+1)`, a successor, so it is data at *every* σ. What
//! this route would close is `Prod` at both σ **and** the `{1,1}` halves of
//! `PProd`/`PSigma` that row 2 declines — one theorem, 16 pairs.
//!
//! # Nothing here searches
//!
//! [`computes`] rebuilds the constructor term from
//! [`Inductive::ctor_term`](derived::inductive::Inductive) and checks its own
//! conclusion against `yⱼ` on the nose, so a chain that walked into the wrong
//! component is a `None` and never an equation about the wrong field.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use derived::inductive::decl_proj::{proj_of, DeclProj};
use derived::inductive::{Inductive, Machine};
use derived::sigma::Telescope;

use crate::env::ConstantInfo;
use crate::ev::Gap;
use crate::expr::{Expr, Name, E};
use crate::ground;
use crate::kernel::Checker;

/// `⊢ g(a) = g(b)` from `⊢ a = b`, for a term-former `g` given as a closure.
///
/// [`derived::congr_arg`] does this for one argument of one `FnSym`; `π₁` and
/// `π₂` are *composites* (`π₁ p = ⋃⋂p`, `π₂ p = app({p}, π₁ p)`, and the second
/// mentions `p` twice), so a per-symbol congruence would need three steps and
/// the two occurrences would have to move together. One Leibniz over the hole
/// does both.
fn congr_of(env: &mut Env, g: &dyn Fn(Term) -> Term, ab: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    let x = env.fresh_var();
    let phi = Formula::eq(g(a.clone()), g(Term::var(x)));
    let leib = Thm::eq_leibniz(a.clone(), b, x, phi);
    Thm::mp(&Thm::mp(&leib, ab)?, &Thm::eq_refl(g(a)))
}

/// The tag component's payload, `π₂(π₁ z)` — the constructor's packed
/// telescope element, for a **one-constructor** declaration.
///
/// `π₂` and not an injection inverse: `Inj₀(x)` is `inl(x) = ⟨∅,x⟩`, so the
/// payload is literally the pair's second component and no inverse symbol is
/// needed. At a declaration with more than one constructor the *same* term
/// would still be the payload of whichever `Injᵢ` the element carries, which is
/// precisely why the tag has to be identified before this is meaningful — and
/// why every consumer of this file must be single-constructor.
pub(crate) fn payload(mach: &Machine, z: Term) -> Term {
    let ap = &mach.wt.sums.ap;
    mach.proj.snd_of(ap, mach.proj.fst_of(ap, z))
}

/// `⟦proj[T,j] s⟧ = πⱼ(⟦s⟧) = compⱼ(π₂(π₁ ⟦s⟧))`.
///
/// **[`derived::inductive::decl_proj::proj_of`] and not a second spelling.**
/// This module used to build the spine itself; `DeclProj::over_declaration`
/// compares every computation rule it is handed against `proj_of`, so a local
/// copy would be a term that agrees today and is checked against nothing. The
/// checker's subject and the theorems' subject are now one function.
pub(crate) fn term(mach: &Machine, j: usize, z: Term) -> Term {
    proj_of(&mach.wt.sums.ap, &mach.proj, j, z)
}

/// The same term, built through [`Interp::mk`] so that its applicative
/// structure is in the `Parts` hint table.
///
/// **This is the one thing route (b) needs that no theorem supplies, and
/// nothing about it was visible until the wiring ran.** `⟦projⱼ x⟧` is the
/// interpretation of a λ *body*, and `Interp::lam_site` has to split that body
/// around the binder — every subterm on the path from the root down to the
/// bound variable must have been recorded on the way in, because the kernel
/// does not expose `Term`'s constructors for reading. `proj_of` builds with
/// `Term::apply`, as every term-former in `derived` does; here every layer
/// mentions the binder, so **every** layer needs an entry, and without them the
/// λ clause reports `Gap::Skeleton` — "the interpretation leaked a variable" —
/// which is exactly what it should say and is what it did say.
///
/// The layers are `proj_of`'s, in its order: `π₁ p = ⋃(⋂p)` is two, and
/// `π₂ p = app({p}, π₁ p)` is two more over it. The result is compared against
/// [`term`] before it is returned, so this cannot record the structure of a
/// term that is not the one the theorems are about.
///
/// [`Interp::mk`]: crate::interp::Interp::mk
fn term_recorded(ip: &mut crate::interp::Interp, j: usize, z: Term) -> Option<Term> {
    let (inter, un, up, app) = {
        let mach = &ip.ind_apparatus()?.mach;
        (mach.proj.inter, mach.wt.sums.ap.sets.un, mach.wt.sums.ap.sets.up, mach.wt.sums.ap.app)
    };
    let fst = |ip: &mut crate::interp::Interp, p: Term| {
        let i = ip.mk(inter, vec![p]);
        ip.mk(un, vec![i])
    };
    let snd = |ip: &mut crate::interp::Interp, p: Term| {
        let first = fst(ip, p.clone());
        let sing = ip.mk(up, vec![p.clone(), p]);
        ip.mk(app, vec![sing, first])
    };
    // `compⱼ(π₂(π₁ z))`: the tag-and-payload pair, its payload, `j` tails, one
    // head — `proj_of`'s composition read left to right.
    let tagpair = fst(ip, z.clone());
    let mut cur = snd(ip, tagpair);
    for _ in 0..j {
        cur = snd(ip, cur);
    }
    let out = fst(ip, cur);
    let mach = &ip.ind_apparatus()?.mach;
    (out == term(mach, j, z)).then_some(out)
}

/// `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` — **unconditional**, and the whole computation rule
/// route (b) needs.
///
/// `ind` must have exactly one constructor with no recursive field; `ys` are
/// its `k` fields. The chain, in the order it is built:
///
/// ```text
/// π₁ ⟨Inj₀(tuple), f(∅)⟩  = Inj₀(tuple)        Proj::fst
/// Inj₀(tuple)             = ⟨∅, tuple⟩         ISumSyms::inj_ax at depth 0
/// π₂ ⟨∅, tuple⟩           = tuple              Proj::snd
/// π₂ ⟨y_q, rest⟩          = rest               Proj::snd, q < j
/// π₁ ⟨y_j, rest⟩          = y_j                Proj::fst
/// ```
///
/// with one [`congr_of`] between consecutive steps, because each rewrites a
/// *subterm* of the next one's subject.
pub(crate) fn computes(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    j: usize,
    ys: &[Term],
) -> Option<Thm> {
    if ind.spec.ctors.len() != 1 || j >= ys.len() {
        return None
    }
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ctor = ind.ctor_term(mach, 0, ys, &[])?;
    let tuple = Telescope::tuple_of(s, ys);
    let tag = mach.syms.inj(0, tuple.clone())?;
    let recf = derived::recarg::RecArg::of(s, &mach.cases, &[]);

    // ── the tag, out of the outer pair ──────────────────────────────────────
    let e_tag = derived::inst_all(&mach.proj.fst, &[tag.clone(), recf])?;
    if e_tag.concl().as_eq()? != (mach.proj.fst_of(ap, ctor.clone()), tag.clone()) {
        return None
    }

    // ── the payload, out of the tag: unfold `Inj₀`, then `π₂` ──────────────
    let unfold = derived::inst_all(mach.syms.inj_ax(0)?, std::slice::from_ref(&tuple))?;
    let (_, inl) = unfold.concl().as_eq()?;
    if inl != s.inl(tuple.clone()) {
        return None
    }
    let snd = |t: Term| mach.proj.snd_of(ap, t);
    let e_pay = {
        let a = congr_of(env, &snd, &e_tag)?;
        let b = congr_of(env, &snd, &unfold)?;
        let via = derived::eq_trans(env, &a, &b)?;
        let step = derived::inst_all(&mach.proj.snd, &[s.zero(), tuple.clone()])?;
        derived::eq_trans(env, &via, &step)?
    };
    if e_pay.concl().as_eq()? != (payload(mach, ctor.clone()), tuple.clone()) {
        return None
    }

    // ── down the telescope: `j` tails, then one head ────────────────────────
    let mut cur = e_pay;
    for q in 0..j {
        let rest = Telescope::tuple_of(s, &ys[q + 1..]);
        let step = derived::inst_all(&mach.proj.snd, &[ys[q].clone(), rest])?;
        let lift = congr_of(env, &snd, &cur)?;
        cur = derived::eq_trans(env, &lift, &step)?;
    }
    let fst = |t: Term| mach.proj.fst_of(ap, t);
    let head = derived::inst_all(
        &mach.proj.fst,
        &[ys[j].clone(), Telescope::tuple_of(s, &ys[j + 1..])],
    )?;
    let lift = congr_of(env, &fst, &cur)?;
    let out = derived::eq_trans(env, &lift, &head)?;

    // The conclusion is checked against `yⱼ` and against the term-former this
    // module hands out, so a chain that walked into the wrong component — or a
    // `term` that stopped counting somewhere else — is a `None`.
    if out.concl().as_eq()? != (term(mach, j, ctor), ys[j].clone()) {
        return None
    }
    Some(out)
}

/// Every computation rule of one declaration, at fresh field variables, and
/// the theorems [`DeclProj`] derives from them.
///
/// The `k` rules are what `over_declaration` compares against
/// [`proj_of`] before deriving anything, so this function's whole
/// responsibility is to produce them **at the variables it is about to hand
/// over** — `yvs` and `computes[j]`'s `yⱼ` are the same variable by
/// construction, not by check.
///
/// One `w_rect` Separation is minted per call, for all `k + 1` theorems, so a
/// caller memoises this per declaration ([`IndApparatus::decl_proj`]).
///
/// [`IndApparatus::decl_proj`]: crate::interp::IndApparatus::decl_proj
pub(crate) fn build(env: &mut Env, mach: &Machine, ind: &Inductive) -> Option<DeclProj> {
    let c = ind.spec.ctors.first()?;
    if ind.spec.ctors.len() != 1 {
        return None
    }
    let k = c.args.len();
    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let rules: Vec<Thm> =
        (0..k).map(|j| computes(env, mach, ind, j, &ys)).collect::<Option<_>>()?;
    DeclProj::over_declaration(env, mach, ind, &yvs, &rules)
}

/// `⟦proj[T,j] s⟧` **and** `Γ ⊢ ⟦proj[T,j] s⟧ ∈ ⟦βⱼ⟧`, at a class-(T) structure
/// whose field `j` is **data** — `MINI-HANDOFF.md` §11's row 4.
///
/// The fourth and last branch of the projection row, and the only one that
/// returns a term. Its three siblings live in [`crate::proj_prop`] and all
/// return `•`; this one is reached from
/// [`Checker::infer_type`](crate::kernel::Checker::infer_type)'s `Expr::Proj`
/// arm **after** they have declined, which is the order §6.2 fixes: a
/// projection whose *type* is a `Prop` is a proof and denotes `•` whatever its
/// carrier is, so the proof routes must answer first or a proof would acquire a
/// second interpretation.
///
/// # What it needs beyond the theorem, and it is one membership
///
/// `DeclProj::typed[j]` is `∀p⃗ ∀z. (z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π⃗<ⱼ z))`, so
/// the whole use-site cost is `⊢ ⟦s⟧ ∈ ind(⟦p⃗⟧)` — β down the stored type
/// former's nest, exactly as [`crate::proj_prop`]'s class-(T) branch does for
/// its own major premise, and with no move onto `•` because `z` is quantified.
///
/// # `⟦βⱼ⟧` is *inferred*, and here that check is load-bearing twice
///
/// `βⱼ(p⃗, π₀ z, …)` is `derived`'s spelling and `⟦βⱼ⟧` the interpretation's;
/// the two meet because `field_ty` is the Lean field type with each **earlier
/// projection substituted**, and each of those interprets — by this very clause
/// one index down — to `π_q(⟦s⟧)`, which is the rung's own argument. So the
/// comparison at the end is not a formality: it is what pins that the
/// substitution the checker performed and the arguments the theorem carries are
/// the same terms. `PSigma.snd`, whose field type is `β fst`, is the corpus
/// member that can tell them apart.
///
/// # Scope
///
/// One constructor, and the refusal is by name: at two constructors the theorem
/// does not exist, because `π₂(π₁ z)` is the packed tuple only under `Inj₀` and
/// an element built by the second constructor carries `Inj₁`. The statement is
/// **false** there, not merely unproved, so this declines rather than reaching
/// for another route.
pub(crate) fn typing(
    c: &mut Checker<'_, '_>,
    ind: &Name,
    idx: u32,
    s: &E,
    field_ty: &E,
) -> Result<(Term, Thm), Gap> {
    let miss = || Gap::StructProj(ind.clone());
    let j = idx as usize;

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

    // ── the class, read off the store — `decls`, like row 2's branch ────────
    let key = (ind.clone(), inst.clone());
    let dt = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.decls.get(&key).cloned().ok_or_else(miss)?
    };
    let spec = dt.ind.spec.ctors.first().ok_or_else(miss)?;
    if dt.ind.spec.ctors.len() != 1 || j >= spec.args.len() || dt.ind.params.len() != np {
        return Err(miss())
    }

    // ── the parameters, the subject, and the type former's spine ────────────
    let mut ps = Vec::with_capacity(np);
    let mut param_mems = Vec::with_capacity(np);
    for a in &args[..np] {
        let t = c.infer_type(a).map_err(|_| Gap::Classifier)?;
        ps.push(t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
        param_mems.push(t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?);
    }
    let subject = te.tm.clone().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let s_mem = te.ev.thm().cloned().ok_or_else(|| te.ev.reason(Gap::NoEndpoint))?;
    let former = c.stored_term(ind, &inst).ok_or_else(miss)?;
    let dp = {
        let (kenv, app, _) = c.interp().and_then(|ip| ip.ind_parts()).ok_or(Gap::IndApparatus)?;
        app.decl_proj(kenv, &key, &dt).ok_or_else(miss)?
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    // `π₀ ⟦s⟧ … π_{j-1} ⟦s⟧`, the rung's own arguments, and `πⱼ ⟦s⟧`, the
    // projection's interpretation — all through `term_recorded`, so the λ
    // clause above this one can split them around its binder.
    let pis: Vec<Term> = (0..j)
        .map(|q| term_recorded(ip, q, subject.clone()))
        .collect::<Option<_>>()
        .ok_or_else(miss)?;
    let tm = term_recorded(ip, j, subject.clone()).ok_or_else(miss)?;

    // ── `⊢ ⟦s⟧ ∈ ind(⟦p⃗⟧)`, the theorem's own premise ───────────────────────
    let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(miss)?;
    if carrier != ip.mk(dt.ind.ty, ps.clone()) {
        return Err(miss())
    }
    let major = ip.retarget_set(&s_mem, &spine_eq).ok_or_else(miss)?;

    let mut inst_at = ps.clone();
    inst_at.push(subject.clone());
    let h_sym = derived::inst_all(dp.typed.get(j).ok_or_else(miss)?, &inst_at)
        .and_then(|t| Thm::mp(&t, &major))
        .ok_or_else(miss)?;

    // ── `βⱼ(p⃗, π⃗<ⱼ z)` onto `⟦βⱼ⟧`, the interpretation's own set ────────────
    //
    // The same unfold both sibling branches make, at **this** rung's arguments
    // rather than at `•⃗<ⱼ`: the theorem's set is `derived`'s field symbol
    // applied to the earlier *projections*, and the abbreviation instantiated
    // at the same list is what carries it to the interpretation the checker
    // inferred. `PSigma.snd`, whose field type is `β fst`, is where the two
    // argument lists have to agree for a non-trivial reason.
    let unfold = dt
        .field_abbrev
        .first()
        .and_then(|r| r.get(j))
        .and_then(|t| {
            let mut a = ps.clone();
            a.extend(pis.iter().cloned());
            derived::inst_all(t, &a)
        })
        .ok_or_else(miss)?;
    let h = ip.retarget_set(&h_sym, &unfold).ok_or_else(miss)?;

    // …and the conclusion against `⟦βⱼ⟧` inferred, which is where the
    // substitution and the theorem's arguments are pinned to be the same terms.
    let want = c.infer_type(field_ty).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;
    if *h.concl() != Formula::mem(tm.clone(), want) {
        return Err(miss())
    }
    Ok((tm, h))
}

#[cfg(test)]
mod tests {
    use super::*;
    use derived::inductive::{CtorSpec, DeclSpec};
    use kernel::FreeVar;

    /// An opaque field type of arity `np + j` whose body is its `which`-th
    /// argument — `derived/tests/decl_fields.rs`'s fixture, and opaque for the
    /// same reason: the *symbol application* is what appears in every term
    /// below and nothing here unfolds it.
    fn field(env: &mut Env, np: usize, j: usize, which: usize) -> kernel::FnSym {
        let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
        let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
        let t = args[which].clone();
        derived::define_abbrev(env, &vars, &t).expect("an abbreviation").0
    }

    /// **Route (b)'s computation rule, at three fields.**
    ///
    /// Three and not two, because the claim under test is that
    /// `πⱼ = π₁ ∘ π₂ʲ ∘ π₂ ∘ π₁` counts the *right* number of tails: at two
    /// fields an off-by-one in either the `π₂(π₁ ·)` prefix or the `π₂ʲ` walk
    /// still lands on a component of the tuple and the equation still has two
    /// visibly different sides, so a wrong index passes. At three, `j = 1`'s
    /// answer is distinct from both neighbours. (`MEMORY`: two atoms cannot
    /// distinguish.)
    ///
    /// The declaration is `T (a b c : Type 0) : Type 0 | mk : a → b → c → T`
    /// with **no recursive field**, which is the shape route (b) is about, and
    /// the three field types are three *different* parameters so a chain that
    /// returned the wrong one is caught by the statement rather than by luck.
    #[test]
    fn the_projection_chain_reaches_the_field_it_names() {
        let mut env = Env::new();
        let mut mach = Machine::new(&mut env).expect("the apparatus");
        // Three parameters, three plain fields, `βq(p⃗,y⃗<q) = pq`.
        let betas: Vec<kernel::FnSym> = (0..3).map(|q| field(&mut env, 3, q, q)).collect();
        let spec = DeclSpec::new(3, vec![CtorSpec::new(betas.clone(), 0)]);
        let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the carrier");
        let ys: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();

        for j in 0..3 {
            let thm = computes(&mut env, &mach, &ind, j, &ys)
                .unwrap_or_else(|| panic!("j = {j}: the chain did not compute"));
            let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
            assert_eq!(rhs, ys[j], "j = {j}: the chain reached the wrong field");
            assert_eq!(
                lhs,
                term(&mach, j, ind.ctor_term(&mach, 0, &ys, &[]).expect("the ctor term")),
                "j = {j}: the equation is not about this module's own term"
            );
            assert!(thm.hyps().is_empty(), "j = {j}: the computation rule is unconditional");
            // …and it is not the *same* equation at two indices, which a chain
            // that ignored `j` would make it.
            assert_ne!(rhs, ys[(j + 1) % 3], "j = {j}: the fields are not distinguished");
        }
    }
}
