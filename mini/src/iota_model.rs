//! **The ι rule of a *nested* recursor, at a use site** — the certificate
//! `whnf`'s recursor arm needs when the eliminator is `T.rec_k` of a nested
//! declaration and the rule it fires is a theorem of that declaration's model.
//!
//! # Interface
//!
//! ```text
//! iota_model::selects(checker, T.rec_k)         -> bool
//! iota_model::fire(checker, T.rec_k, σ, …)      -> Result<(Thm, Term), Gap>
//! ```
//!
//! One **composed** equation
//!
//! ```text
//! Γ ⊢ app(…app(⟦T.rec_k⟧, ⟦p⃗⟧)…, ⟦major⟧) = ⟦rhs⟧
//! ```
//!
//! together with `⟦rhs⟧`, or a named absence — the same contract
//! [`crate::iota_dep::fire`] has, at the same call site in
//! [`crate::kernel::Checker::whnf_conv`], and it is a **sibling** of that
//! module rather than a widening of it.
//!
//! # Why a sibling and not a repair
//!
//! `iota_dep::fire`'s first check is `args.len() != np + 1 + n + 1`: one
//! motive, one minor per constructor of the recursor's own type. A nested
//! recursor does not have that arity and cannot be given it — `Tree.rec` binds
//! **two** motives and **four** minors, because Lean's nested compiler makes
//! every member of the specialised block a motive of every recursor, so a redex
//! has seven arguments where that arity expects four. Relaxing the check would
//! make one arm answer for two shapes, and the shapes disagree in more than a
//! count: `iota_dep` builds its equation out of
//! [`derived::inductive::DepRecursor::iota`] over a class-(T) carrier, and a
//! nested declaration **has no class-(T) carrier at all**. Its interpretation
//! is its model's, by [`crate::interp::IndApparatus::model_of`], and its rules
//! are the model's theorems.
//!
//! So the split is made off that very table — see [`selects`] — and the two
//! arms' domains are disjoint by construction rather than by a count.
//!
//! # What the equation is made of
//!
//! Almost nothing, and that is the point of having built the model. The rule is
//! already a proved Lean theorem inside the run:
//!
//! ```text
//! T._model.iota_k_j : ∀ p⃗ M⃗ S⃗ f⃗, Eq.{v} (T._model.rec_k p⃗ M⃗ S⃗ (c p⃗ f⃗)) (Sⱼ f⃗ ih⃗)
//! ```
//!
//! `modelgen` wrote it, mini's own kernel checked it as an ordinary declaration
//! of the file and [`crate::nested_splice::recognise`] checked its statement
//! against the export's before keying it, so the
//! interpretation pass has already opened its pair. There is no derivation here
//! and `derived/` owes this row nothing.
//!
//! # The one thing that does *not* work, and it was the plan
//!
//! **The rule cannot be applied to the redex's arguments in Lean world.** The
//! obvious arm — build `T._model.iota_k_j M⃗ S⃗ f⃗` and hand it to
//! [`crate::eq_cash::cash`] — was written first and measured: fourteen
//! `waiting:classifier`, every one of them `eq_cash.rs`'s step 1, because
//! `infer_type` on that application is a **type error**. The theorem's motive
//! binder is `M₀ : T._model.self → Sort v` and the redex's motive is
//! `m1 : T → Sort v`, and Lean has no conversion between the two: `T` is a
//! primitive `ConstantInfo::Inductive` and `T._model.self` a `def` over the
//! specialised block, which is precisely the separation
//! `mini/src/nested_splice.rs`'s header keeps on purpose. "The model's `rec_k`
//! and the export's are the same statement about different constants" is true
//! of the *statement* and false of the *type*.
//!
//! In set world there is nothing to convert. `model_alias` stores one term
//! under both keys, so `⟦T⟧` **is** `⟦T._model.self⟧`, `⟦∀ _:T, Sort v⟧` is
//! `⟦∀ _:T._model.self, Sort v⟧`, and the redex's motive is already a member of
//! the domain the theorem's nest asks for. So the arm walks the nest at the
//! *interpretation*: [`crate::interp::Interp::cond_app`] once per argument,
//! which is [`crate::kernel::Checker`]'s own `App` clause with its Lean
//! `assert_def_eq_as` replaced by the **stronger** demand that the two
//! interpretations be equal on the nose. That demand is the keying, stated as a
//! check, and a declaration where it fails declines at `DOMAIN` rather than
//! reaching for a conversion.
//!
//! What comes out is `Γ ⊢ • ∈ ⟦Eq.{v} α L R⟧` at the model's names. The
//! equation is then read off it by [`crate::eq_cash::cash_stmt`] — `cash`
//! without its step 1 — handed the **export-side** spelling of the same
//! statement: the redex itself on the left, `whnf`'s own right-hand side on the
//! right. Every subterm of that is well-typed, because every one of them is
//! part of what the checker is already reducing. Nothing is assumed by the
//! substitution: `cash_stmt`'s step 4 retargets the membership onto the `Eq`
//! nest those three build and `Interp::retarget_set` refuses unless that nest
//! **is** the membership's own set, so a keying that did not hold stops with a
//! reason instead of asserting the model's theorem about the export's terms.
//!
//! One further comparison is made rather than assumed: the left endpoint
//! against `app(…app(head_tm, arg_tms)…)`, `whnf`'s own accumulator. `whnf`'s
//! contract is that `cur_tm` interprets `cur`, and this is the only statement
//! in the arm relating `cash_stmt`'s world to the reduction's. The *right*
//! endpoint is not compared, because it is not derived here: `cash_stmt` was
//! handed `rhs` and gives its interpretation back. See the site.
//!
//! # What declines
//!
//! * **a rule with no `model_iota` entry.** The table is filled only from a
//!   theorem [`crate::nested_splice::recognise`] found and checked, and
//!   the seeding is now **total** over the rules of every recursor the file
//!   applies — it used to leave out the ones whose model proof transports,
//!   because their own constant typings had no endpoint and there was nothing
//!   for [`crate::eq_cash`] to read. What is left in this case is a rule at a σ
//!   the recursor has no interpretation at.
//!   **This is a decline and never a fall-back** — not to `iota_dep`, whose
//!   tables are empty for a nested declaration, and not to a name rule. A
//!   dispatch arm whose missing case answers from somewhere else reports a
//!   working model when there is none, which is the error
//!   `mini/src/nested_splice.rs`'s header is about, one table along;
//! * **a major whose constructor arity disagrees with the theorem's**, which is
//!   the same statement as "this is not the rule for this constructor";
//! * **an argument whose interpretation is not the nest's own domain** — the
//!   keying not holding at this σ, and the one place this arm would otherwise
//!   have to reach for a conversion;
//! * **anything `cash_stmt` refuses**, with its own reason and not one invented
//!   here — §0.4.
//!
//! # The boundary
//!
//! This module derives nothing. It reads two tables, walks a nest with
//! [`crate::interp::Interp::cond_app`], builds one Lean expression out of terms
//! the checker is already holding, calls [`crate::eq_cash::cash_stmt`] and
//! compares two terms.

use kernel::{Term, Thm};

use crate::env::ConstantInfo;
use crate::ev::{Cause, Gap};
use crate::expr::{app_n, konst, subst, Expr, Level, Name, E};
use crate::interp::{Interp, PiShape};
use crate::kernel::Checker;

const NORULE: &str = "iota: the model has no rule for this constructor at this level";
const SHAPE: &str = "iota: the model rule's telescope and the redex disagree";
const OWNER: &str = "iota: the major's constructor has no inductive owner";
const NOTPROP: &str = "iota: the model rule's statement is not a Prop-valued nest";
const DOMAIN: &str = "iota: an argument is not in the domain the model rule binds";
const WALK: &str = "iota: the model rule does not instantiate at these arguments";
const LHS: &str = "iota: the model rule is not about the redex this run is reducing";

/// **Is this recursor a nested declaration's?**
///
/// The discriminator [`crate::kernel::Checker::whnf_conv`] chooses this arm on,
/// and it is [`crate::interp::IndApparatus::nested`] — the very membership
/// [`crate::zoneb::ensure`] routes the declaration's *interpretation* on, so
/// the two axes cannot disagree about which declarations are modelled.
///
/// Three things it is deliberately **not**:
///
/// * **not a name** and not the recursor's arity. `mini/src/nested_splice.rs`'s
///   header is about the first; the second would be a count that two shapes can
///   share, which is what put this arm's fourteen redexes into `iota_dep`;
/// * **not [`crate::interp::IndApparatus::model_iota`]**. Selecting on the
///   *rule* table would mean an unseeded rule silently took `iota_dep`'s route
///   — a fall-back, and the one this arrangement exists to refuse. A nested
///   recursor selects here and then declines here;
/// * **not [`crate::interp::IndApparatus::model_of`]** either, which is the σ-keyed
///   table. A nested recursor at a σ nothing keyed still belongs to this arm and
///   still has to decline by name rather than borrow another module's reason.
///
/// [`Interp::ind_built`] and not `ind_apparatus`: this is asked at every
/// recursor redex in every file, and the apparatus is built on first use.
pub(crate) fn selects(c: &mut Checker<'_, '_>, rec: &Name) -> bool {
    let Some(owner) = c.environment().owner(rec).cloned() else { return false };
    let Some(ip) = c.interp() else { return false };
    ip.ind_built().is_some_and(|app| app.nested.contains_key(&owner))
}

/// The ι certificate at one use site of a nested recursor.
///
/// `args`/`arg_tms` are the arguments up to and including the major premise —
/// `np + nmotives + nminors + 1` of them for a nested recursor — with their
/// interpretations; `ctor_args` is the major's own spine (the constructor's
/// parameters then its fields) and `rhs` the Lean right-hand side `whnf` is
/// about to move to. `ls` is the redex's own level list, which the rule is
/// instantiated at: the model's theorem carries the recursor's universe
/// parameters, because `modelgen` states it over the recursor's own
/// (`MODELGEN.md` §1.1, property 3).
#[allow(clippy::too_many_arguments)]
pub(crate) fn fire(
    c: &mut Checker<'_, '_>,
    rec: &Name,
    rec_inst: &[u32],
    ls: &[Level],
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor: &Name,
    ctor_args: &[E],
    rhs: &E,
) -> Result<(Thm, Term), Gap> {
    let bad = |w: &'static str| Gap::Recursor(rec.clone(), w, Cause::Threading);
    if args.is_empty() || args.len() != arg_tms.len() {
        return Err(bad(SHAPE))
    }

    // ── which rule ──────────────────────────────────────────────────────────
    //
    // The key is everything this site holds: the recursor, the σ it is being
    // reduced at, and the major's head constructor. A miss is the decline the
    // module note is about.
    let thm = {
        let app =
            c.interp().ok_or(Gap::SymbolicLevel)?.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.model_iota.get(&((rec.clone(), rec_inst.to_vec()), ctor.clone())).cloned()
    };
    let Some(thm) = thm else { return Err(bad(NORULE)) };

    // ── the rule at the redex's own arguments ───────────────────────────────
    //
    // **The constructor's own parameter count, not the recursor's** —
    // `Checker::whnf_conv`'s reason at the same spot: a nested recursor's rules
    // are another type's constructors, and `Tree.rec_1` (`numParams = 0`)
    // reduces on `List.cons` (`numParams = 1`). The model's theorem binds the
    // *fields* after the shared telescope, so the parameters come off the front
    // of the major's spine here exactly as they do there.
    let cnp = match c.environment().owner(ctor).and_then(|o| c.environment().get(o)) {
        Some(ConstantInfo::Inductive { num_params, .. }) => *num_params as usize,
        _ => return Err(bad(OWNER)),
    };
    let fields = ctor_args.get(cnp..).ok_or_else(|| bad(OWNER))?;
    let mut applied: Vec<E> = args[..args.len() - 1].to_vec();
    applied.extend_from_slice(fields);
    // **The arity is checked against the theorem, not assumed from the two
    // counts.** They agree for every rule this module's own table admits; one
    // that did not would run the walk below off the end of the ∀-nest and come
    // back as `WALK`, which says nothing about *which* shape disagreed.
    let thm_ty = c.environment().get(&thm).ok_or_else(|| bad(NORULE))?.ty();
    if crate::zoneb::peel(thm_ty, applied.len()).is_none() {
        return Err(bad(SHAPE))
    }
    // ── the rule, instantiated **at the interpretation** ────────────────────
    //
    // **This is the one thing the arm cannot do in Lean world, and it is why
    // `eq_cash::cash` is not called directly.** The theorem's binders are typed
    // at the *model's* carrier — `∀ (M₀ : T._model.self → Sort v) …` — and the
    // redex's own motives and minors are typed at the **export's** `T`. Lean
    // has no conversion between those two: `T` is a primitive inductive and
    // `T._model.self` a `def` over the specialised block, and making them
    // δ-related is exactly what `crate::nested_splice`'s header refuses. So
    // `infer_type` on `T._model.iota_k_j M₀ …` is an ill-typed application and
    // fails, which is what this route was measured doing before this loop
    // existed: fourteen `waiting:classifier` at `eq_cash.rs`'s step 1.
    //
    // In *set* world there is nothing to convert. `⟦T⟧` and `⟦T._model.self⟧`
    // are the same term because [`crate::zoneb::ensure`]'s `model_alias` stores
    // one under both keys, so `⟦∀ _:T, Sort v⟧` and `⟦∀ _:T._model.self,
    // Sort v⟧` are the same set and the redex's motive is already a member of
    // the domain the theorem's nest asks for. The walk below is therefore
    // `Checker::infer_type`'s own `App` arm with its Lean `assert_def_eq_as`
    // replaced by the **stronger** demand that the two interpretations be equal
    // on the nose — which is the keying, stated as a check. A σ or a
    // declaration where it does not hold declines at `DOMAIN`.
    let head = konst(thm.clone(), ls.to_vec().into());
    let t = c.infer_type(&head).map_err(|_| bad(NORULE))?;
    let mut mem = t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?;
    let mut ty = t.ty.clone();
    for a in &applied {
        let Expr::Forall { body, .. } = &*ty.clone() else { return Err(bad(SHAPE)) };
        let set = mem.concl().as_mem().map(|(_, s)| s).ok_or_else(|| bad(WALK))?;
        // **Every level of the nest is `Prop`-valued**, because the statement
        // is an `Eq` and `∀x, Prop` is `Prop`. Reading the clause off the
        // interpretation rather than assuming it is `app_evidence`'s own rule;
        // a `Dep` shape here would mean the theorem is not the proposition this
        // module thinks it is, and it declines rather than guessing.
        let shape = c.interp().ok_or(Gap::SymbolicLevel)?.as_pi(&set);
        let Some(PiShape::Prop { site, dom }) = shape else { return Err(bad(NOTPROP)) };
        let ta = c.infer_type(a).map_err(|_| Gap::Classifier)?;
        let a_tm = ta.tm.clone().ok_or_else(|| ta.ev.reason(Gap::NoEndpoint))?;
        let a_mem = ta.ev.thm().cloned().ok_or_else(|| ta.ev.reason(Gap::NoEndpoint))?;
        if ta.ev.mem_set() != Some(dom.clone()) {
            return Err(bad(DOMAIN))
        }
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        mem = ip.cond_app(&site, &dom, &mem, &a_tm, &a_mem).ok_or_else(|| bad(WALK))?;
        ty = subst(body, a);
    }

    // ── the statement, spelled in the *export's* constants ──────────────────
    //
    // `ty` is now the rule at the redex's arguments and in the model's names,
    // and it is the ill-typed expression this whole detour exists to avoid
    // handing to `infer_type`. What goes to [`crate::eq_cash::cash_stmt`] is
    // the **same equation written on the export side**: the redex itself on the
    // left, `whnf`'s own right-hand side on the right, and the motive at the
    // major for the type. Every one of those is well-typed, because every one
    // of them is a subterm of what the checker is already reducing.
    //
    // Nothing is assumed by the substitution. `cash_stmt`'s step 4 retargets
    // `mem` onto the `Eq` nest these three build, and `Interp::retarget_set`
    // refuses unless that nest **is** `mem`'s own set — so if the keying did
    // not make the two statements one set, this stops at `eq-cash-retarget`
    // rather than claiming the model's theorem about the export's terms.
    let (ty_head, ty_args) = crate::expr::get_app(&ty);
    let Expr::Const(ty_nm, ty_ls) = &*ty_head else { return Err(bad(SHAPE)) };
    if *ty_nm != eq_name() || ty_args.len() != 3 {
        return Err(bad(SHAPE))
    }
    let lhs_e = app_n(konst(rec.clone(), ls.to_vec().into()), args);
    let alpha = c.infer_type(&lhs_e).map_err(|_| Gap::Classifier)?.ty;
    let stmt = app_n(konst(eq_name(), ty_ls.clone()), &[alpha, lhs_e, rhs.clone()]);
    let cashed = crate::eq_cash::cash_stmt(c, &stmt, mem)?;

    // ── and it is about *this* redex ────────────────────────────────────────
    //
    // **`⟦rhs⟧` is `cashed.rhs` and is not inferred a second time.** `iota_dep`
    // compares its composite's endpoint against a separately inferred `⟦rhs⟧`,
    // because there the endpoint is *derived* and could land elsewhere; here
    // the statement handed to `cash_stmt` was built with `rhs` as its third
    // argument, so `cashed.rhs` **is** that inference. Two mutations measured
    // it: re-inferring and comparing survives, and so does re-checking
    // `cashed.eq`'s conclusion against `Formula::eq(lhs, rhs)`, which is
    // `cash_stmt`'s own last line one call up. Both are deleted rather than
    // excused — `eq_cash`'s header makes the same argument about the three
    // guards it removed — and deleting the first saves an `infer_type` of the
    // whole right-hand side at every firing.
    //
    // **The left endpoint is kept and it survives too, for a different
    // reason.** `cashed.lhs` is `infer_type`'s interpretation of the redex and
    // `spine(head_tm, arg_tms)` is `whnf`'s accumulator: the same term by two
    // code paths, and this is the only statement in the arm that relates them.
    // `iota_dep` keeps the identical comparison at the identical place (its
    // step 1's `spine(&ap, head_tm, arg_tms)`), and a certificate about a term
    // `whnf` is not tracking is the failure it exists for.
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    if cashed.lhs != spine(ip, head_tm, arg_tms) {
        return Err(bad(LHS))
    }
    Ok((cashed.eq, cashed.rhs))
}

/// `Eq`, as [`crate::eq_cash`] knows it — the statement handed to
/// [`crate::eq_cash::cash_stmt`] has to be headed by the same constant that
/// module decomposes on.
fn eq_name() -> Name { Name::simple("Eq") }

/// `app(…app(f, a₀)…, a_{n-1})` — the applicative spine an interpretation gives
/// a Lean application, which is what `whnf`'s accumulator is about.
fn spine(ip: &Interp, f: &Term, args: &[Term]) -> Term {
    let ap = ip.prelude.tower.sums.ap.clone();
    args.iter().fold(f.clone(), |acc, a| ap.apply(acc, a.clone()))
}
