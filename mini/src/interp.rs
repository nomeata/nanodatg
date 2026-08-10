//! `⟦·⟧` — the interpretation of mini's `Expr` as a kernel `Term`
//! (MINI-DESIGN.md §7), and the per-`(name, σ)` constant store (§8).
//!
//! # Interface
//!
//! ```text
//! Interp::new()                                  -> Interp
//! ip.sort(n)                                     -> Term          ⟦Sort n⟧
//! ip.sort_typing(n)                              -> Thm           ⊢ ⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧
//! ip.app(f, a)                                   -> Term          ⟦f a⟧
//! ip.abbrev(&body)                               -> Option<(Term, Thm)>
//! ip.opaque()                                    -> Term
//! ip.get_const(&key) / ip.put_const(key, interp)
//! ip.skeleton(&t, v, &mut holes)                 -> Term
//! ```
//!
//! **What is reimplemented and what is reused.** `kernel` and `derived` are
//! reused wholesale: everything mini composes with is `Term`/`Thm`-level and
//! knows nothing about Lean syntax. What is written here is only the §6.2
//! *clause dispatch* against mini's own `Expr` — a few hundred lines against a
//! stable original, rather than adopting `ExprPtr`/`TcCtx` and re-importing
//! the arena and the per-declaration re-interning that mini exists to escape.
//! Independent reimplementation also has diagnostic value: where mini and
//! nanoda disagree about a certificate, one of the two dispatches is wrong, and
//! they fail independently.
//!
//! # What state this keeps, and why none of it is a cache
//!
//! The per-skeleton symbol tables and the per-`(name, ground levels)` constant
//! interpretations are **identity**, not memoised recomputation: two
//! occurrences of one lambda body shape must be the *same* symbol, or their
//! definitional equality needs a theorem where reflexivity should do. Mini has
//! no `whnf`/`infer`/`defeq` result memos at all — nanoda's caches, with their
//! hypothesis-import guards, are engineering for a later stage, and mini's role
//! is to show the design correct without them. Everything stored keeps the
//! certificate that produced it beside the result.
//!
//! # Ground levels only
//!
//! Every level reaching this module is a numeral, because the checker runs once
//! per ground instantiation σ (§3). `⟦Sort u⟧` is therefore always exactly one
//! clause, and `PiUndet` — nanoda's "this `Π` is a proposition at `v := 0` and
//! a function space otherwise" — cannot arise. The declaration-shape zone (§9
//! zone A) runs at symbolic levels and simply has no `Interp` at all.

use std::collections::HashMap;
use std::rc::Rc;

use derived::cumul::apparatus::IndChain;
use derived::inductive::Machine;
use derived::prelude::{prelude, Prelude};
use nanoda_lib::tg::EnvCore;
use derived::skeleton;
use derived::tower::Cumul;
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ev::{Gap, Sealed};
use crate::expr::{Level, Name};

/// A constant at one instantiation, keyed by the **level expressions** its
/// universe parameters stand for.
///
/// `LEVELPOLY.md` §5.3 step 2. This used to be `(Name, Vec<u32>)` — one entry
/// per *ground* σ, a numeral per parameter — which made the store unable to
/// even *name* a declaration at its own parameters, and so made the schedule a
/// precondition of the interpretation rather than a choice. A [`Level`] is
/// hash-consed, `Copy` and `Hash`, so the key is no more expensive; what it
/// buys is that `⟦c.{u}⟧` has a key at all.
///
/// **The levels are canonicalised** ([`crate::expr::Level::simplify`], via
/// [`crate::ground::key_levels`]) so that two spellings of one instantiation
/// are one entry, exactly as the checker's `canon_level` discipline requires.
/// At a ground σ that is the identity on numerals, so every key this store held
/// before it widened it still holds, at the same identity.
pub type ConstKey = (Name, Vec<Level>);

/// What the store holds for `⟦c.{σ}⟧`.
#[derive(Debug, Clone)]
pub struct ConstInterp {
    /// `⟦c.{σ}⟧`.
    pub term: Term,
    /// `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, or why it is missing.
    pub typing: Result<Sealed, Gap>,
    /// For a transparent definition, `⊢ ⟦c.{σ}⟧ = ⟦val[σ]⟧` — the defining
    /// axiom, which is also delta reduction's certificate.
    pub defeq: Option<Sealed>,
}

/// The interpretation's state: one kernel `Env`, the ambient signature, the
/// term registry the skeleton decomposition needs, and the stores.
pub struct Interp {
    /// The kernel `Env`, the canonical skeleton variables and the W-type
    /// machine, behind the same-thread handle both engines can hold at once.
    /// [`Interp::new`] mints a private one — the historical behaviour — and
    /// [`Interp::over`] takes the caller's, which is what makes this engine's
    /// symbols and the checker's one signature (ENV-UNIFY.md §3.3).
    core: EnvCore,
    pub prelude: Rc<Prelude>,
    /// The canonical binder slot every skeleton abstracts over — a copy of
    /// the core's, kept because the common read-only use needs no borrow.
    x_canon: FreeVar,
    /// `⊢ Uₘ ⊆ Uₙ` for every `m ≤ n ≤ height`, and the lifting rules over it.
    ///
    /// Built eagerly to [`CUMUL_HEIGHT`]: it is `O(h²)` theorems, `h` is a
    /// small numeral because a closed Lean level evaluates to one before the
    /// interpretation runs, and every `Π` rule needs the two premises raised to
    /// `max(l1, l2)` before it applies.
    cumul: Cumul,
    consts: HashMap<ConstKey, ConstInterp>,
    /// The graph machinery per lambda body **shape**. Identity, not a cache:
    /// see [`Interp::lam_site`].
    lams: HashMap<Term, LamSite>,
    /// The dependent-product machinery per fibre **shape**.
    fibres: HashMap<Term, FibreSite>,
    /// The conditional-singleton machinery per `Prop`-valued `∀` shape.
    conds: HashMap<Term, CondSite>,
    /// The same three tables keyed the other way, by the symbol each site
    /// *builds* — so that an interpretation handed back can be taken apart
    /// again ([`Interp::as_lam`], [`Interp::as_pi`]).
    ///
    /// This is what lets `whnf` and `assert_def_eq` recover `⟦A⟧` and `⟦B⟧`
    /// from `⟦Π x:A. B⟧` instead of re-interpreting the subterms. Every
    /// interpretation comes from a `Typing` already in hand; taking one apart
    /// is not a second traversal, it is reading the term the traversal built.
    lam_by_sym: HashMap<FnSym, LamSite>,
    fibre_by_sym: HashMap<FnSym, FibreSite>,
    cond_by_sym: HashMap<FnSym, CondSite>,
    /// `⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)`, built on first use.
    prop_sub: Option<Thm>,
    /// [`derived::ext::dprod_const_fibre_n`] per **fibre symbol** — the
    /// `dprod`↔`fs` bridge rule, before its hypothesis is discharged.
    ///
    /// A memo and not an identity: the theorem is a closed statement about the
    /// site's own symbols, so two builds would be the same formula. What a
    /// second build costs is one **Extensionality instance** — the callee opens
    /// with `Thm::ax_contains`/`ax_extensionality` — and
    /// [`Interp::dprod_is_fs`] is called once per function-typed field
    /// *occurrence*, twice per `Quot.lift`. The key is the fibre symbol because
    /// every other argument the callee takes is read off the same
    /// [`FibreSite`], so `b` determines all of them.
    dprod_fs: HashMap<FnSym, Thm>,
    /// The direct clauses' two conditional singletons, built on first use.
    /// Shared rather than rebuilt: see [`Interp::direct`].
    pub(crate) direct: Option<Rc<crate::direct::Direct>>,
    /// Why they could not be built, if they could not.
    pub(crate) direct_failed: bool,
    /// [`derived::ext::Eta`], built on **its own** first use — the η graph and
    /// its four theorems. An export with no function η must not pay for a
    /// `lambda_n` carving. See [`crate::fun_eta`].
    pub(crate) eta: Option<Rc<derived::ext::Eta>>,
    /// Why it could not be built, if it could not.
    pub(crate) eta_failed: bool,
    /// The `Quot` clause's apparatus at `u ≥ 1`, built on **its own** first
    /// use — the equivalence closure, the classes, `lift`'s graph and the
    /// formation theorem. An export that mentions no quotient must not pay for
    /// any of it. See [`crate::quot_classes`].
    pub(crate) quotient: Option<Rc<crate::quot_classes::QuotClause>>,
    /// Why it could not be built, if it could not.
    pub(crate) quotient_failed: bool,
    /// The `Nat` clause's apparatus — `ω`, its recursor and its arithmetic —
    /// built on **its own** first use. Two of the ninety-one tutorial exports
    /// mention `Nat`; the other eighty-nine must not pay for the whole of
    /// `derived/src/nat/`. See [`crate::nat_clause`].
    pub(crate) nat: Option<Rc<crate::nat_clause::NatClause>>,
    /// Why it could not be built, if it could not.
    pub(crate) nat_failed: bool,
    /// The `Acc` clause's apparatus, built on **its own** first use.
    ///
    /// Separate from [`Interp::direct`] rather than a field of it: `Eq` occurs
    /// in most exports and this one carves a Separation and derives A0–A2, none
    /// of which an export that mentions only `Eq` should pay for. See
    /// [`crate::acc`].
    pub(crate) acc: Option<Rc<crate::acc::AccClause>>,
    /// Why it could not be built, if it could not.
    pub(crate) acc_failed: bool,
    /// [`derived::rec_acc`], over the `Acc` clause's own carrier — built on
    /// **its** own first use, since only `Acc.rec` at a *value* motive wants it
    /// and the whole of the attempts/union/totality development is behind it.
    /// See [`crate::rec_acc_ap`], whose header names the trap this field's
    /// builder exists to avoid.
    pub(crate) rec_acc: Option<Rc<crate::rec_acc_ap::RecAccApparatus>>,
    /// Why it could not be built, if it could not.
    pub(crate) rec_acc_failed: bool,
    /// **What `⟦Acc.rec.{u₁,u}⟧`'s nest bottom is called**, at `u₁ ≥ 1` — see
    /// [`RecAccElim`]. Keyed by the *recursor*'s constant, like
    /// [`IndApparatus::dep_elims`], and on `Interp` rather than on the inductive
    /// apparatus because `Acc` takes [`crate::direct::clause_for`] and must not
    /// build a `Wtype` for one abbreviation.
    pub(crate) rec_acc_elims: HashMap<ConstKey, Rc<RecAccElim>>,
    /// The inductive-translation apparatus (§9 zone B), built on first use.
    ///
    /// Lazily, and that is not an optimisation detail: it is a `Tower`'s worth
    /// of derivations, and the 27 inductive-free exports must not pay for it.
    ind: Option<Box<IndApparatus>>,
    /// Why the apparatus could not be built, if it could not. Recorded so the
    /// failure is reported once with its own name rather than retried per
    /// constant.
    ind_failed: bool,
    /// The conversion census (MINI-DESIGN.md §0.3).
    pub convs: ConvStats,
    /// **How many times a constant occurrence had to build its own
    /// interpretation** — the residue of the store-miss path, and a number that
    /// is zero on every export mini checks.
    ///
    /// `⟦c.{σ}⟧` is put here at `c`'s declaration, from the schedule
    /// ([`crate::ledger::fill_declaration`]), so an occurrence should only ever
    /// *read*. This counts the occurrences that did not: a miss whose key no
    /// decline table explains, which `Checker::miss_reason`
    /// then falls back to constructing. `mini/tests/tutorial.rs` pins it at
    /// **0** over all 91 exports; with the eager fill removed it is nonzero on
    /// 61 of them.
    pub lazy_fills: usize,
    /// **Human-readable names for the terms mini itself minted**, and nothing
    /// else. `Term` has no public destructor, so a blocker report would
    /// otherwise print `⟨·⟩` where `⟦Nat.succ.{}⟧` belongs; this is the small
    /// registry that lets [`crate::blocker::show_term`] name what it can.
    ///
    /// Diagnostics only, filled only when [`crate::blocker::is_armed`] — no
    /// derivation reads it, and an entry that is wrong or missing costs a
    /// legible report, never a theorem.
    labels: HashMap<Term, String>,
    /// Fill [`Interp::labels`] even when the blocker is not armed — what
    /// [`Interp::set_labels_on`] switches, and the reason a dump can have names
    /// without also inheriting the stop-at-first-blocker behaviour.
    labels_on: bool,
    /// The same for the two ambient symbols every interpretation is built
    /// out of, so a report reads `fs(⟦Sort 1⟧, ⟦Sort 0⟧)` and not `f10(…)`.
    /// Seeded once; the per-site symbols stay numbered, because a lambda body
    /// shape has no better name than its number.
    sym_labels: HashMap<FnSym, &'static str>,
}

/// **How many conversions are hypothesis-free** — the measurement §0.3 asked
/// for, taken with [`crate::ev::Sealed::new`] on each `Conv`'s evidence.
///
/// The census named "kernel-hypothesis evidence versus `ExprPtr`-keyed caches"
/// as the one genuine unsettled design decision, and §0.3 reduced it to: *a
/// conversion cache must either key on `Γ` as well as the endpoints, or store
/// `Sealed` entries only.* Which of the two is cheaper is an empirical
/// question about the ratio below, and this is the counter that answers it.
#[derive(Debug, Default, Clone)]
pub struct ConvStats {
    /// Conversions produced with a certificate.
    pub proved: usize,
    /// …of which `Sealed::new` accepted — no hypotheses, shareable across
    /// declarations.
    pub sealed: usize,
    /// Conversions that reached their reduct with no certificate.
    pub gapped: usize,
    /// …**by reason**, keyed exactly as the evidence ledger's `waiting:` rows
    /// are ([`crate::ledger::Ledger::key`]).
    ///
    /// # Why the bare count was not enough
    ///
    /// [`ConvStats::gapped`] alone says a conversion could not be certified and
    /// not *what* was missing, and the two indexed eliminators landing moved it
    /// 216 → 988 with no recoverable cause at all. That is worse than the
    /// declaration-level version of the same defect, where an unattributed row
    /// at least names *a* gap: here a 772-row movement had nothing to attribute
    /// it to, and the reason table in `tutorial_conversion_split`'s header had
    /// to be marked not-re-measured rather than updated.
    ///
    /// The keys being `Ledger::key`'s is the point rather than a convenience.
    /// A conversion-level reason and a declaration-level one that name the same
    /// missing theorem must compare equal, or the two censuses cannot be read
    /// against each other — which is the whole claim the header makes when it
    /// says the conversion rows are "the conversion-level view of debt the
    /// evidence ledger was already counting at declaration level".
    pub gapped_by: std::collections::BTreeMap<String, usize>,
    /// Of the proved ones, those whose **endpoints differ** — the ones a cache
    /// would exist for. A reflexivity is free to re-derive, so counting it
    /// would let trivia dominate the ratio.
    pub moved: usize,
    /// …of which hypothesis-free.
    pub moved_sealed: usize,
}

/// The conditional-singleton machinery for one `Prop`-valued `∀` shape.
#[derive(Clone)]
pub struct CondSite {
    /// The fibre symbol, of arity `k+1`: `b(h⃗, x)`.
    pub b: FnSym,
    /// The body shape `b` abbreviates, at the canonical hole and binder
    /// variables. Kept so an instance can be *rebuilt* through
    /// [`Interp::mk`] — see [`Interp::rebuild`].
    pub skel: Term,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    pub b_ax: Thm,
    /// The conditional singleton `chi(h⃗, A) = [∀x ∈ A. • ∈ b(h⃗,x)]`.
    pub chi: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀z. (z ∈ chi(h⃗,A) ↔ (z ∈ 1 ∧ φ))`.
    pub chi_ax: Thm,
    /// `φ(h⃗, A) := ∀x. (x ∈ A → • ∈ b(h⃗,x))`, open in `params`.
    pub phi: Formula,
    /// `φ`'s free variables, in `chi`'s argument order: holes, then domain.
    pub params: Vec<FreeVar>,
    /// This *occurrence*'s abstracted binder-free subterms.
    pub holes: Vec<Term>,
    pub k: usize,
}

/// The dependent-product machinery for one fibre shape.
#[derive(Clone)]
pub struct FibreSite {
    /// The fibre symbol, of arity `k+1`: `b(h⃗, x)`.
    pub b: FnSym,
    /// The fibre shape, at the canonical variables. See [`Interp::rebuild`].
    pub skel: Term,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    pub b_ax: Thm,
    /// `img` and `dprod` and everything proved about them.
    pub dp: Rc<derived::ext::DProdN>,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → img(h⃗,A) ∈ U(c))`.
    pub replacement: Thm,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → dprod(h⃗,A) ∈ U(c))` — Lean's `Π` rule.
    pub rule: Thm,
    /// This *occurrence*'s abstracted binder-free subterms.
    pub holes: Vec<Term>,
    pub k: usize,
}

/// The graph machinery for one lambda body shape.
#[derive(Debug, Clone)]
pub struct LamSite {
    /// The body symbol, of arity `k+1`: `t(h⃗, x)`.
    pub t: FnSym,
    /// The body shape, at the canonical variables. See [`Interp::rebuild`].
    pub skel: Term,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    pub t_ax: Thm,
    /// The graph symbol, of arity `k+1`: `lam(h⃗, A) = { ⟨x, t(h⃗,x)⟩ : x ∈ A }`.
    pub lam: FnSym,
    /// `derived::funcs::lambda_n`'s characteristic theorem.
    pub lam_ax: Thm,
    /// This *occurrence*'s abstracted binder-free subterms, in traversal
    /// order. Not part of the key: the shape is shared, the holes are not.
    pub holes: Vec<Term>,
    /// `holes.len()` for the occurrence that first built the symbols.
    pub k: usize,
}

/// Which of §6.2's three `Π` clauses an interpretation came from, recovered
/// from the term itself by [`Interp::as_pi`].
///
/// The application rule differs per clause and the three are *different sets*,
/// so this is a decision that has to be read off rather than guessed — which is
/// exactly why the interpretation records its applicative structure.
#[derive(Clone)]
/// *(The `Fs` variant is gone, deliberately, at the `fs`-clause removal.
/// `SCOPING.md` §10 left the choice open — the arm becomes unreachable either
/// way, because `as_pi` keyed on **head symbol** and `derived::fs` stays in the
/// library. It is removed rather than left unreachable for the reason
/// `QUOT-MODEL.md` §2.1 gives about keying decomposition on a head symbol: a
/// stray `fs` term is not an interpreted `Π` and must not decompose as one.
/// With the variant gone it yields `None` and the caller's own gap; with the
/// variant kept it would have decomposed, silently and wrongly, the first time
/// a library `fs(W,T)` obligation met a conversion. This repository had one
/// precedent of each — `Clause::Undet` made unrepresentable,
/// `stuck-major-moved` left unreachable — and the discriminator is whether a
/// wrong input can reach it. Here one can.)*
pub enum PiShape {
    /// `dprod(q⃗, ⟦A⟧)` — a dependent product, at a constant fibre when the
    /// codomain does not mention the binder.
    Dep { site: FibreSite, dom: Term },
    /// `chi(h⃗, ⟦A⟧)` — a `Prop`-valued `∀`, a conditional singleton.
    Prop { site: CondSite, dom: Term },
}

impl PiShape {
    /// The domain, whichever clause built it.
    pub fn dom(&self) -> Term {
        match self {
            PiShape::Dep { dom, .. } | PiShape::Prop { dom, .. } => dom.clone(),
        }
    }

    /// `⟦B⟧` at a point — the codomain's interpretation, rebuilt at `x`.
    /// Constant in the binder-free clause, the fibre's skeleton otherwise.
    pub fn body_at(&self, ip: &mut Interp, x: &Term) -> Term {
        match self {
            PiShape::Dep { site, .. } => {
                let s = site.skel.clone();
                ip.rebuild(&s, &site.holes, x)
            }
            PiShape::Prop { site, .. } => {
                let s = site.skel.clone();
                ip.rebuild(&s, &site.holes, x)
            }
        }
    }

    /// `⊢ b(q⃗,x) = ⟦B⟧`, or reflexivity where there is no fibre symbol.
    pub fn sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm> {
        match self {
            PiShape::Dep { site, .. } => {
                let (b, ax, holes) = (site.b, site.b_ax.clone(), site.holes.clone());
                ip.symbol_at(b, &ax, &holes, x)
            }
            PiShape::Prop { site, .. } => {
                let (b, ax, holes) = (site.b, site.b_ax.clone(), site.holes.clone());
                ip.symbol_at(b, &ax, &holes, x)
            }
        }
    }
}

/// How far the cumulativity table reaches. A Lean sort above this yields a gap
/// rather than a wrong universe; the tutorial corpus's highest is far below it.
pub const CUMUL_HEIGHT: usize = 8;

/// The §9 zone-B apparatus: the translation machine, the cumulative chain over
/// the **same** signature, and the per-`(name, σ)` stores that go with them.
pub struct IndApparatus {
    /// The apparatus every declaration is translated over — one, so that the
    /// `MachineId` guards on `Inductive::is_over` all pass. Held through the
    /// [`EnvCore`]'s cell: the machine is the core's, so an `Interp` and a
    /// checker backend over one core translate onto **one** machine, and
    /// each other's carriers compose. `RefCell` because `Inductive::build`
    /// needs `&mut Machine` at the same time as `&mut Env`, and the two live
    /// behind different cells.
    pub mach: Rc<std::cell::RefCell<Machine>>,
    /// The cumulative hierarchy over that same `Wtype` and `Bound`.
    pub chain: IndChain,
    /// The translated declarations, by `(name, ground levels)`.
    ///
    /// Identity, not memoisation, for the same reason [`Interp::lam_site`]'s
    /// table is: two uses of `List.{0}` must name **one** carrier, or their
    /// definitional equality needs a theorem where reflexivity should do.
    pub decls: HashMap<ConstKey, Rc<Translated>>,
    /// The dependent eliminator of each translated declaration, by the
    /// **declaration's** key — one per declaration, never per recursor σ.
    ///
    /// [`derived::inductive::GenRecursor`]'s header is explicit that a second
    /// build mints a second family of Replacement symbols whose theorems cannot
    /// be chained with the first's, so this is identity for the same reason
    /// [`IndApparatus::decls`] is, not a speed cache.
    pub deprecs: HashMap<ConstKey, Rc<DepRec>>,
    /// Declarations whose dependent eliminator was attempted and not built, so
    /// the (expensive) attempt is made once. The *reason* lives in
    /// [`IndApparatus::rec_untranslated`]; this is only the "already tried" bit.
    pub deprec_failed: std::collections::HashSet<ConstKey>,
    /// The **name `⟦T.rec.{σ}⟧`'s λ-nest bottom is bound to**, by the
    /// *recursor's* key — see [`DepElim`].
    ///
    /// Keyed by the recursor and not by the declaration, unlike
    /// [`IndApparatus::deprecs`]: `drec`'s target is instantiated to
    /// `⟦Sort u₁⟧`, and `u₁` is read off the recursor's own motive binder, so
    /// two σ of one declaration are two abbreviations of two different terms.
    pub dep_elims: HashMap<ConstKey, Rc<DepElim>>,
    /// The same, for the **class-(S)** route: `A_φ`, its truth value and the
    /// introduction rules, by `(name, ground levels)`.
    ///
    /// Identity for the same reason [`IndApparatus::decls`] is, and one reason
    /// more: `crate::recursor`'s class-(S) rule is a second build over *this*
    /// `A_φ`, and rebuilding the carrier there would mint a second Separation
    /// that no equation relates to the one in the store.
    pub props: HashMap<ConstKey, Rc<crate::class_s::ClassS>>,
    /// The same, for the **class-(P)** route: the underlying carrier, its
    /// truncation, and the two abbreviation families a later build over them
    /// needs. See [`TruncTranslation`].
    ///
    /// Identity, not memoisation, and for the sharpest version of the reason
    /// [`IndApparatus::decls`] gives: `TruncCarrier::over_declaration` carves a
    /// Separation and `Inductive::build` mints a family of symbols, so a second
    /// build is a second carrier that no equation relates to the one the type
    /// former was stored at.
    pub truncs: HashMap<ConstKey, Rc<TruncTranslation>>,
    /// The class-(P) **elimination rule** of each such declaration, by the
    /// *declaration's* key — one per declaration, never per recursor σ.
    ///
    /// [`derived::inductive::family::TruncRecursor::over_declaration`]'s header
    /// says one `w_rect` Separation is minted per call, so this is identity for
    /// the reason [`IndApparatus::prop_recs`] is, not speed.
    trunc_recs: HashMap<ConstKey, Rc<derived::inductive::family::TruncRecursor>>,
    trunc_recs_failed: std::collections::HashSet<ConstKey>,
    /// The field inhabitations of each class-(S) declaration, by the
    /// **declaration's** key — one per declaration, never per recursor σ.
    ///
    /// `And.rec.{0}` and `And.rec.{1}` are two pairs over one declaration, so
    /// without this the ladder is climbed twice; and while
    /// [`derived::inductive::family::LePropFields`] introduces no symbol and a
    /// second build would be harmless, the standing rule is that a certificate
    /// is stored beside the result it belongs to rather than re-derived.
    prop_fields: HashMap<ConstKey, Rc<derived::inductive::family::LePropFields>>,
    prop_fields_failed: std::collections::HashSet<ConstKey>,
    /// The same at a **class-(P)** declaration — `TruncFields`, whose major
    /// premise is `• ∈ ‖ind(p⃗)‖` where `LePropFields`' is `• ∈ A_φ(p⃗)`.
    ///
    /// One Separation per build (`TruncFields::elim_psi`), so this is identity
    /// and not speed, like every other table here.
    trunc_fields: HashMap<ConstKey, Rc<derived::inductive::family::TruncFields>>,
    trunc_fields_failed: std::collections::HashSet<ConstKey>,
    /// The same at a **class-(T)** declaration — `DeclFields`, whose major
    /// premise is plain carrier membership `z ∈ ind(p⃗)` where its two siblings
    /// need `• ∈ A_φ(p⃗)` and `• ∈ ‖ind(p⃗)‖`. This is the third and smallest of
    /// the three, and the one a `Type`-resultant structure with `Prop` fields
    /// (`PProd.{0,0}`, `PSigma.{0,0}`) needs.
    ///
    /// One Separation per build, so identity and not speed, like every other
    /// table here.
    decl_fields: HashMap<ConstKey, Rc<derived::inductive::DeclFields>>,
    decl_fields_failed: std::collections::HashSet<ConstKey>,
    /// The **typed projections and the η rule** of each class-(T) declaration,
    /// by the declaration's key — `MINI-HANDOFF.md` §11's row 4.
    ///
    /// The fourth and last member of the field family, and the only one whose
    /// conclusion is about a *term* rather than about `•`. One `w_rect`
    /// Separation per build covers all `k + 1` theorems, so this is identity
    /// and not speed, like every other table here — and here the identity
    /// matters twice over: `⟦projⱼ x⟧` is the **interpretation of Lean syntax**,
    /// so two occurrences of `proj 0 s` must denote one term, and a second
    /// build would relate them by nothing.
    decl_projs: HashMap<ConstKey, Rc<derived::inductive::decl_proj::DeclProj>>,
    decl_projs_failed: std::collections::HashSet<ConstKey>,
    /// **`pull(g,D) = { ⟨q, app(g, π₁ q)⟩ : q ∈ D }`** and its three theorems —
    /// `derived::sigma::Reindex`, derived once.
    ///
    /// Identity and not speed, and the reason is in the callee's own header:
    /// `Reindex::new` mints **two** definitional extensions (the body
    /// abbreviation and the lambda graph), so a second build is a second `pull`
    /// operator, and `reindex_at_tuple` about one of them says nothing about a
    /// constructor built with the other. The struct is deliberately independent
    /// of the telescope — `π₁ q` mentions neither the argument types nor `k` —
    /// so one serves every declaration in a run, which is what makes a single
    /// slot right rather than a map.
    ///
    /// Built on **its own** first use: a corpus with no function-typed
    /// recursive field pays nothing for it.
    reindex: Option<Rc<derived::sigma::Reindex>>,
    reindex_failed: bool,
    /// The same, for an **indexed family**: the index space, the `good`
    /// recursion and the indexed carrier, by `(name, ground levels)`.
    ///
    /// Identity for the reason [`IndApparatus::decls`] is, and one more:
    /// `IndexedCtor::mem_lean` is stated at *this* build's working variables
    /// and about *this* build's `ind(p⃗,x⃗)`, so a constructor derived over a
    /// second `IndexedInductive` would be a true theorem about a carrier no
    /// equation relates to the one in the store.
    pub indexed: HashMap<ConstKey, Rc<crate::zoneb::IndexedTranslation>>,
    /// What the boundary walk found about an indexed declaration whose carrier
    /// is **not** wired — kept across the decline. See
    /// [`crate::zoneb::IndexedWalk`], which is where the argument is.
    ///
    /// Disjoint from [`IndApparatus::indexed`] by construction: `zoneb::ensure`
    /// fills that one on the class-(T) branch and this one on the branch that
    /// declines, and the two are decided by the same `provably_nonzero` test.
    /// When a carrier lands for either of the declining classes, its build
    /// **reads this** rather than walking again — a second walk would mint a
    /// second family of index symbols related to the stored ones by nothing.
    pub indexed_walks: HashMap<ConstKey, Rc<crate::zoneb::IndexedWalk>>,
    /// The same as [`IndApparatus::props`], for a class-(S) declaration **with
    /// indices** — `A_φ`, the `Σ` nest, and the conditional singleton `χ` of
    /// arity `np + ni` that `derived::…::LeIndexCarrier` mints.
    ///
    /// A separate table rather than a variant of `props` because the two
    /// carriers are different objects: at `ni = 0` there is nothing to mint and
    /// `A_φ` *is* the truth value, and a consumer that could not tell them
    /// apart would hand `prop`'s lemmas the wrong `φ`.
    pub props_ix: HashMap<ConstKey, Rc<crate::class_s_ix::ClassSIx>>,
    /// The same as [`IndApparatus::truncs`], for a class-(P) declaration **with
    /// indices** — the erased skeleton, the §5.2 `IndexedCarrier` it is carved
    /// into, the truncation of that, and mini's own name for `‖ind(p⃗,x⃗)‖` at
    /// arity `np + ni`. See [`crate::class_p_ix::ClassPIx`].
    ///
    /// A separate table rather than a variant of `truncs` because the two
    /// carriers are different objects — `over_declaration` truncates an
    /// [`Inductive`](derived::inductive::Inductive) and `over_family` an
    /// `IndexedCarrier` — and because [`crate::rec_trunc_ix`]'s rule needs the
    /// `IndexedInductive` that only this one carries.
    pub truncs_ix: HashMap<ConstKey, Rc<crate::class_p_ix::ClassPIx>>,
    /// The class-(P) **indexed** elimination rule of each such declaration, by
    /// the *declaration's* key — one per declaration, never per recursor σ.
    /// See [`IndApparatus::indexed_trunc_recursor`].
    trunc_recs_ix: HashMap<ConstKey, Rc<derived::inductive::family::IndexedTruncRecursor>>,
    trunc_recs_ix_failed: std::collections::HashSet<ConstKey>,
    /// The **`Prop`-motive elimination rule** of each indexed class-(T)
    /// declaration, by the *declaration's* key — one per declaration, never per
    /// recursor σ.
    ///
    /// [`derived::inductive::family::IndexedPropRecursor::over_family`]'s
    /// header states that one `w_rect` Separation is minted per call, so a
    /// second build would be a second carving no equation relates to the first
    /// — identity, not speed, exactly as [`IndApparatus::deprecs`] is.
    prop_recs: HashMap<ConstKey, Rc<derived::inductive::family::IndexedPropRecursor>>,
    prop_recs_failed: std::collections::HashSet<ConstKey>,
    /// The same at a **value** motive — `INDEXED-DESIGN.md` §5.1's D8.
    ///
    /// A `w_rect` Separation *and* the guarded minors' own are minted per
    /// build, and the `GenRecursor` underneath it splices its Replacement
    /// symbols into this declaration's carrier, so a second build would be a
    /// second family of symbols no theorem relates to the first. Identity, like
    /// every other entry here. It cannot collide with
    /// [`IndApparatus::deprecs`]: that table is fed from
    /// [`IndApparatus::decls`] and this one from
    /// [`IndApparatus::indexed`], which `zoneb::ensure` populates on mutually
    /// exclusive branches (`ni == 0` against `ni > 0`), so a declaration is in
    /// exactly one of them.
    dep_recs_ix: HashMap<ConstKey, Rc<derived::inductive::family::IndexedDepRecursor>>,
    dep_recs_ix_failed: std::collections::HashSet<ConstKey>,
    /// **One indexed family's constructors that have no translation**, by the
    /// *constructor's* own key, with the reason.
    ///
    /// Separate from [`IndApparatus::untranslated`], which is about a whole
    /// declaration and is consulted before the carrier is built. A constructor
    /// giving up must not take the type former down with it — `042_rbTreeDef`
    /// asks for the former and nothing else — so `crate::ctor_ix` records here
    /// and returns, and `zoneb::stored_or_reason_after` reads it in place of
    /// the bare `no-interp(·)` fallback.
    ///
    /// Counted by [`crate::ledger::Untranslated`], which is the reason it must
    /// stay a record and not become a bare early return.
    pub ctor_untranslated: HashMap<ConstKey, Gap>,
    /// Declarations the boundary produced **no translation** for, with the
    /// reason. Kept so the absence is reported once, by its own name, rather
    /// than retried at every use and reported as a bare store miss.
    ///
    /// **Not an arena decline.** [`crate::run::Verdict::Declined`] is a verdict
    /// about the *file* and exits 2; an entry here is an internal record about
    /// one declaration in a file mini **accepted**, and it lands on the
    /// certification axis — see [`crate::ledger::Untranslated`] and
    /// `zoneb`'s header, which distinguishes the three senses of the word.
    pub untranslated: HashMap<ConstKey, Gap>,
    /// **Eliminators that were attempted and could not be built**, by the
    /// *recursor's* own key, with the reason.
    ///
    /// A third table and not a case of [`IndApparatus::untranslated`], because
    /// the two are different judgements about different things: `untranslated`
    /// says the *declaration* has no translation, and the dump prints it under
    /// that heading; this says the declaration translated and its eliminator is
    /// waiting on a `derived/` construction, which is also a per-pair
    /// `waiting:` row (`recursor(X: …)`) at every use site there is.
    ///
    /// It exists because [`crate::ledger::fill_declaration`] attempts the
    /// eliminator **once**, at the declaration, and the constant occurrences
    /// that report the reason come later. `IndApparatus::deprec_failed` already
    /// records that an attempt was made and is a `HashSet`; the reason was
    /// recomputed by re-entering `recursor::ensure` from the store miss, which
    /// is the path that no longer exists.
    pub rec_untranslated: HashMap<ConstKey, Gap>,
    /// **A nested declaration's interpretation is its model's** — the export
    /// constant's own key ↦ the model constant that carries `⟦·⟧`.
    ///
    /// Filled by [`crate::nested_splice::recognise`], from a model the export
    /// carries,
    /// checked and put into the declaration list, and by nothing else. A
    /// constant with no entry **declines** in [`crate::zoneb::ensure`]; there
    /// is no name rule and no fall-through, and
    /// `mini/src/nested_splice.rs`'s header says why that is the whole point of
    /// the table rather than a strictness about it.
    ///
    /// Keyed on the [`ConstKey`] and not on the [`Name`]: a recursor's motive
    /// level is part of what is keyed, and the σ a model was built for is the
    /// σ it answers at.
    pub model_of: HashMap<ConstKey, Name>,
    /// **A nested recursor's ι rule is its model's theorem** — `((T.rec_k, σ),
    /// the major's head constructor) ↦ the model theorem that states the rule`.
    ///
    /// Filled by [`crate::nested_splice::recognise`] beside
    /// [`IndApparatus::model_of`] and from the same source, and read by
    /// [`crate::iota_model::fire`] and by nothing else. The key is what a
    /// dispatch site holds and all it holds.
    ///
    /// A rule with no entry **declines** there. It does not fall back to
    /// [`crate::iota_dep::fire`] and it does not fall back to a name: the
    /// entries exist only for rules whose theorem this pass seeded, and a rule
    /// answered from anywhere else would be a computation rule for a model
    /// nothing checked.
    pub model_iota: HashMap<(ConstKey, Name), Name>,
    /// Every nested declaration the splice saw, by its own name — see
    /// [`crate::nested_splice::NestedRecord`].
    ///
    /// The membership test, not the table above, is what says a declaration
    /// takes the model route: a nested declaration whose model *failed* is in
    /// here with a reason and in [`IndApparatus::model_of`] not at all, and it
    /// must decline by that reason rather than fall through to the class-(T)
    /// walk.
    pub nested: HashMap<Name, crate::nested_splice::NestedRecord>,
    /// The accessibility apparatus, over **this** machine's own pairing.
    ///
    /// Built on first use, because only the class-(S) route needs it and most
    /// corpus files have no class-(S) declaration at all; shared thereafter,
    /// because `LeCarrier::build` refuses an `Acc` whose `up` is not the
    /// machine's, and two carriers built over two `Acc`s would speak of two
    /// different `acc`.
    acc: Option<Rc<derived::acc::Acc>>,
    acc_failed: bool,
    /// The W-recursor over **this** machine's `Wtype`, and the two theorems
    /// `GenRecursor::build` pins its inputs against. Built on first use, like
    /// [`IndApparatus::acc`] and for the same reason: only the class-(T)
    /// eliminator needs it, and it costs an `extension`, a `totality`, an `ι`
    /// and a `funspace` — the expensive half of `wnat_rec`'s bill.
    wrec: Option<Rc<WRec>>,
    wrec_failed: bool,
    /// The truncation `‖·‖`, built on first use — the class-(P) carrier's
    /// whole apparatus. See [`IndApparatus::trunc`].
    trunc: Option<Rc<derived::prop::trunc::Trunc>>,
    trunc_failed: bool,
}

/// One translated class-(T) declaration, with the certificates the *later*
/// builds over it need.
///
/// The two abbreviation families are the reason this is a struct rather than
/// the bare [`derived::inductive::Inductive`]. `define_abbrev` mints a fresh
/// symbol per call, so a defining axiom that is dropped cannot be recovered —
/// and `crate::rec_dep` needs both of them to relate what the *interpretation*
/// says (`⟦βⱼ⟧`, `⟦T.ctorᵢ p⃗ y⃗ t⃗⟧`) to what `derived::inductive` says
/// (`βⱼ(p⃗,y⃗<ⱼ)`, `Inductive::ctor_term`). Storing the certificate beside the
/// result is the standing memo rule.
pub struct Translated {
    /// The carrier and everything `derived::inductive` derived about it.
    pub ind: Rc<derived::inductive::Inductive>,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per constructor, per **plain** field
    /// in declared plain order — `crate::zoneb::CtorEvidence::abbrev`.
    pub field_abbrev: Vec<Vec<Thm>>,
    /// `⊢ ∀p⃗ ∀f⃗. (ctor_symᵢ(p⃗,f⃗) = ctorᵢ(y⃗,t⃗))`, per constructor, at the
    /// parameters and then the fields in **declared** order — the symbol
    /// `crate::zoneb`'s constructor nest binds its bottom to, so that a use
    /// site's applied spine reaches `Inductive::ctor_term` in one Leibniz step.
    ///
    /// **The parameters are part of the abstraction list**, because under
    /// `RecArg::general` the constructor term mentions them: its
    /// recursive-argument function dispatches over `Sum_m(Σ(z::γⱼ(p⃗)))`. A
    /// consumer therefore instantiates at `np` parameters *and* the fields, in
    /// that order, and the arity is `Term::apply`'s assertion rather than a
    /// check of ours.
    pub ctor_abbrev: Vec<Thm>,
    /// `⊢ ∀p⃗. (γⱼᵢ(p⃗) = ⟦γⱼᵢ⟧)`, per constructor, per **recursive** field, per
    /// binder of that field's `γⱼ` — `crate::zoneb::CtorEvidence::rec_dom_abbrev`,
    /// and empty at a plain recursive argument.
    ///
    /// Kept for [`Self::field_abbrev`]'s reason at the other kind of slot. A
    /// **minor premise** at a function-typed recursive slot has to move between
    /// the telescope's own `β₀(p⃗)`, where `derived::sigma::push_in_funspace`
    /// states the pushed function's typing, and the interpretation's `⟦γ⟧`,
    /// where the minor's own binder is. `crate::zoneb`'s constructor bottom
    /// needed the same equation and had the walk's frame to get it from;
    /// `crate::rec_dep` is one construction later and does not.
    pub rec_dom_abbrev: Vec<Vec<Vec<Thm>>>,
}

/// One translated **class-(P)** declaration — the truncated carrier and the
/// certificates a later build over it needs.
///
/// # Why this struct exists at all
///
/// `crate::zoneb::build_trunc` had all four of these in hand and returned
/// none of them: it ended at the type former, and `ind`, `tc`, the carrier
/// abbreviation and the plain fields' abbreviations died with the call. That
/// is the fourth instance of this project's recurring defect — *a value
/// computed at the bottom of a call whose site outlives nothing* — and the
/// most expensive of the four, because it is not one fact but the whole
/// translation. Re-deriving is not an option and never was: `Inductive::build`
/// mints a family of symbols and `TruncCarrier::over_declaration` carves a
/// Separation, so a second build is a second carrier, true of itself and
/// related to the stored type former by nothing.
///
/// It read, from outside, as `derived/` owing a class-(P) eliminator.
/// `TruncRecursor` had been built and tested for a month
/// (`derived/tests/family_trunc_rec.rs`) and could not be *called*, because its
/// `tc` argument no longer existed anywhere by the time the recursor was asked
/// for.
pub struct TruncTranslation {
    /// The **underlying** §5.2 carrier — the thing `‖·‖` truncates.
    pub ind: Rc<derived::inductive::Inductive>,
    /// The truncation, its `only_point`/`elim`/`in_u0` and the per-constructor
    /// rules.
    pub tc: Rc<derived::inductive::family::TruncCarrier>,
    /// `⊢ ∀p⃗. (sym(p⃗) = ‖ind(p⃗)‖)` — mini's own name for the carrier, which is
    /// the term the type former was stored at. Without it nothing can get from
    /// `⟦T p⃗⟧` to anything `derived` states.
    pub abbrev: Thm,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per constructor, per **plain** field
    /// in declared plain order — `crate::zoneb::CtorEvidence::abbrev`, the same
    /// family [`Translated::field_abbrev`] carries and for the same consumer:
    /// a minor premise's field atom is stated at `βⱼ` and the interpretation's
    /// binder at `⟦βⱼ⟧`.
    pub field_abbrev: Vec<Vec<Thm>>,
}

/// The W-recursor and the two inputs [`derived::inductive::GenRecursor::build`]
/// checks its callers on.
pub struct WRec {
    pub rc: derived::wrec_total::Recursor,
    /// `⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (…)` — `derived::wrec_total::iota`.
    pub iota: Thm,
    /// `⊢ ∀A ∀B ∀u ∀T ∀e. (H → wrec ∈ fs(W, T))`.
    pub funspace: Thm,
}

/// The general and dependent eliminators of one declaration, over one machine.
pub struct DepRec {
    pub gr: derived::inductive::GenRecursor,
    pub dr: derived::inductive::DepRecursor,
}

/// **What `⟦T.rec.{σ}⟧`'s nest bottom is called**, and the equation that takes
/// the name off again.
///
/// `derived` assembles `drec` outside [`Interp::mk`], which while
/// decomposability was a property of *who built a term* left the λ above unable
/// to skeletonise a body containing it; `crate::rec_dep`'s `dep_bottom`
/// therefore binds `app(drec, t)` to a symbol of mini's own. That symbol is what a β
/// chain down the stored nest lands on, and this axiom is the **only** way back
/// — `define_abbrev` mints a fresh symbol per call, so re-minting produces a
/// second name related to this one by nothing.
///
/// It used to die with the call that made it, which is `MINI-HANDOFF.md` §2's
/// sixth instance and the whole reason an ι reduction read as blocked on a
/// theorem the store already held.
/// **What `⟦Acc.rec.{u₁,u}⟧`'s nest bottom is called at `u₁ ≥ 1`**, and the
/// equation that takes the name off again.
///
/// The same problem [`DepElim`] solves, at the one eliminator that is not built
/// out of [`IndApparatus`]: `derived::rec_acc`'s `pack` is assembled inside
/// `derived`, which on the same argument left the λ above the bottom unable to
/// skeletonise a body containing it, and [`crate::rec_acc_value`] binds
/// `app(app(pack,⟦a⟧),⟦t⟧)` to a symbol of mini's own. A β chain down the stored nest lands on that symbol and this
/// axiom is the **only** way back — `define_abbrev` mints a fresh symbol per
/// call, so re-minting produces a second name related to this one by nothing.
///
/// Stored the moment it has a reader, and not before: `MINI-HANDOFF.md` §27's
/// sizing of piece 4 names the store as part of the ι rule rather than as a
/// prerequisite of it, because a store with no reader is §26 item 1's failure
/// from the other side.
pub struct RecAccElim {
    /// `sym`, of arity 6 — `α, r, C, m, a, t`, the eliminator's whole nest.
    pub sym: FnSym,
    /// `⊢ ∀α r C m a t. (sym(α,r,C,m,a,t) = app(app(pack(A,R̄,T,ē),a),t))`.
    pub ax: Thm,
}

pub struct DepElim {
    /// `sym`, of arity `np + 1 + n + 1`.
    pub sym: FnSym,
    /// `⊢ ∀p⃗ C S⃗ [x⃗] t. (sym(…) = app(drec(p⃗,C,S⃗,T), t))`, over the nest's own
    /// binders — the index binders are present at an indexed family and absent
    /// otherwise, so a consumer instantiates it at the same list the nest was.
    pub ax: Thm,
    /// **The set `T` was instantiated at**, kept rather than the level it came
    /// from, because the two routes choose it differently and a consumer that
    /// re-derived the choice could pick the other one.
    /// [`crate::rec_dep`]'s value clause takes `⟦Sort u₁⟧`, the sort the motive
    /// lands in; [`crate::rec_ix_dep`] takes the rung the motive's own *type*
    /// inhabits, because `Rung::app` is unconditional in the argument and
    /// `ICOV`'s index binders are unbounded (that module's header). Nothing
    /// downstream should have to know which.
    pub target: Term,
}

impl IndApparatus {
    fn build(core: &EnvCore, p: &Prelude) -> Option<IndApparatus> {
        // The `Wtype`, `Bound` and `Machine` are the **core's** — built once,
        // over the prelude tower's own `Sums`, and shared with any other
        // engine holding the same core. A second `Machine` would mint a
        // second `rec₊` and a second `MachineId`, and nothing translated
        // over it would compose with the first's carriers.
        let mach = core.machine(p)?;
        let chain = {
            let m = mach.borrow();
            let mut env = core.env_mut();
            IndChain::over(&mut env, &p.tower, &m.wt, &m.bnd)
        }?;
        // Necessary *and* checked: the chain's `U₁` must be the tower level
        // `⟦Type 0⟧` names, or `⊢ ind(p⃗) ∈ U₁` would be a membership in a
        // universe no Lean sort denotes.
        if chain.chain.u1.set != p.tower.u(1) || !chain.is_over(&mach.borrow()) {
            return None
        }
        Some(IndApparatus {
            mach,
            chain,
            decls: HashMap::new(),
            deprecs: HashMap::new(),
            deprec_failed: std::collections::HashSet::new(),
            dep_elims: HashMap::new(),
            props: HashMap::new(),
            truncs: HashMap::new(),
            trunc_recs: HashMap::new(),
            trunc_recs_failed: std::collections::HashSet::new(),
            prop_fields: HashMap::new(),
            prop_fields_failed: std::collections::HashSet::new(),
            trunc_fields: HashMap::new(),
            trunc_fields_failed: std::collections::HashSet::new(),
            decl_fields: HashMap::new(),
            decl_fields_failed: std::collections::HashSet::new(),
            decl_projs: HashMap::new(),
            decl_projs_failed: std::collections::HashSet::new(),
            reindex: None,
            reindex_failed: false,
            indexed: HashMap::new(),
            indexed_walks: HashMap::new(),
            props_ix: HashMap::new(),
            truncs_ix: HashMap::new(),
            trunc_recs_ix: HashMap::new(),
            trunc_recs_ix_failed: Default::default(),
            prop_recs: HashMap::new(),
            prop_recs_failed: std::collections::HashSet::new(),
            dep_recs_ix: HashMap::new(),
            dep_recs_ix_failed: std::collections::HashSet::new(),
            ctor_untranslated: HashMap::new(),
            untranslated: HashMap::new(),
            rec_untranslated: HashMap::new(),
            model_of: HashMap::new(),
            model_iota: HashMap::new(),
            nested: HashMap::new(),
            acc: None,
            acc_failed: false,
            wrec: None,
            wrec_failed: false,
            trunc: None,
            trunc_failed: false,
        })
    }

    // ───────────────────────────────────────────── read-only, for the dump ──
    //
    // Every accessor below is `&self` and **builds nothing**. The `*_attempted`
    // pairs exist because MINI-DESIGN.md §0.5's lesson applies to these tables
    // exactly as it does to a ledger row: absent-and-never-asked-for and
    // absent-because-the-build-failed are different facts, and a dump that
    // could not tell them apart would reproduce the defect §0.5 is about.

    pub fn stored_wrec(&self) -> Option<&Rc<WRec>> { self.wrec.as_ref() }

    pub fn wrec_attempted(&self) -> bool { self.wrec_failed }

    pub fn stored_acc(&self) -> Option<&Rc<derived::acc::Acc>> { self.acc.as_ref() }

    pub fn acc_attempted(&self) -> bool { self.acc_failed }

    pub fn stored_trunc(&self) -> Option<&Rc<derived::prop::trunc::Trunc>> { self.trunc.as_ref() }

    pub fn trunc_attempted(&self) -> bool { self.trunc_failed }

    pub fn stored_prop_rec(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::IndexedPropRecursor>> {
        self.prop_recs.get(k)
    }

    pub fn prop_rec_attempted(&self, k: &ConstKey) -> bool { self.prop_recs_failed.contains(k) }

    pub fn stored_dep_rec_ix(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::IndexedDepRecursor>> {
        self.dep_recs_ix.get(k)
    }

    pub fn dep_rec_ix_attempted(&self, k: &ConstKey) -> bool {
        self.dep_recs_ix_failed.contains(k)
    }

    pub fn stored_prop_fields(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::LePropFields>> {
        self.prop_fields.get(k)
    }

    pub fn prop_fields_attempted(&self, k: &ConstKey) -> bool {
        self.prop_fields_failed.contains(k)
    }

    pub fn stored_trunc_rec(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::TruncRecursor>> {
        self.trunc_recs.get(k)
    }

    pub fn trunc_rec_attempted(&self, k: &ConstKey) -> bool { self.trunc_recs_failed.contains(k) }

    /// The same for the **indexed** class-(P) rule, so `--dump-theorems` can
    /// see the store rather than printing a fixed absence beside it. The rule
    /// this pair of accessors exists for is `MINI-HANDOFF.md` §8's: a new store
    /// gets a dump section in the same commit, and the instrument built to find
    /// storeless evidence must be able to see the stores.
    pub fn stored_trunc_rec_ix(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::IndexedTruncRecursor>> {
        self.trunc_recs_ix.get(k)
    }

    pub fn trunc_rec_ix_attempted(&self, k: &ConstKey) -> bool {
        self.trunc_recs_ix_failed.contains(k)
    }

    /// The class-(P) elimination rule of one translated declaration, built
    /// once.
    ///
    /// `tt` must be [`IndApparatus::truncs`]' entry for `key`;
    /// `TruncRecursor::over_declaration` rebuilds and compares the statements
    /// of the two `TruncCarrier` theorems it spends, so a `tc` from a different
    /// build is a `None` rather than a theorem about somebody else's carrier.
    pub fn trunc_recursor(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        tt: &TruncTranslation,
    ) -> Option<Rc<derived::inductive::family::TruncRecursor>> {
        if let Some(t) = self.trunc_recs.get(key) {
            return Some(t.clone())
        }
        if self.trunc_recs_failed.contains(key) {
            return None
        }
        let built = derived::inductive::family::TruncRecursor::over_declaration(
            env, &self.mach.borrow(), &tt.ind, &tt.tc,
        )
        .map(Rc::new);
        match built {
            Some(t) => {
                self.trunc_recs.insert(key.clone(), t.clone());
                Some(t)
            }
            None => {
                self.trunc_recs_failed.insert(key.clone());
                None
            }
        }
    }

    /// `‖·‖`, over this machine's own `Sums` — the class-(P) truncation.
    /// Lazily, like the rest: the thirteen class-(P) declarations are a small
    /// minority and the other seventy-six must not pay for it.
    pub fn trunc(&mut self, env: &mut Env) -> Option<Rc<derived::prop::trunc::Trunc>> {
        if self.trunc.is_none() && !self.trunc_failed {
            self.trunc =
                derived::prop::trunc::Trunc::new(env, &self.mach.borrow().wt.sums).map(Rc::new);
            self.trunc_failed = self.trunc.is_none();
        }
        self.trunc.clone()
    }

    /// `acc`, over this machine's own `Apply`. See [`IndApparatus::acc`].
    pub fn acc(&mut self, env: &mut Env) -> Option<Rc<derived::acc::Acc>> {
        if self.acc.is_none() && !self.acc_failed {
            self.acc = derived::acc::Acc::with_apply(env, &self.mach.borrow().wt.sums.ap).map(Rc::new);
            self.acc_failed = self.acc.is_none();
        }
        self.acc.clone()
    }

    /// The W-recursor over this machine's `Wtype`. See [`IndApparatus::wrec`].
    pub fn wrec(&mut self, env: &mut Env) -> Option<Rc<WRec>> {
        if self.wrec.is_none() && !self.wrec_failed {
            let built = Self::build_wrec(env, &self.mach.borrow());
            self.wrec_failed = built.is_none();
            self.wrec = built;
        }
        self.wrec.clone()
    }

    fn build_wrec(env: &mut Env, mach: &Machine) -> Option<Rc<WRec>> {
        let wt = &mach.wt;
        let rc = derived::wrec_total::Recursor::new(env, wt)?;
        let ext = derived::wrec_extend::extension(env, wt, &rc)?;
        let total = derived::wrec_total::totality(env, wt, &rc, &ext)?;
        let iota = derived::wrec_total::iota(env, wt, &rc, &total)?;
        let funspace = derived::wrec_total::wrec_funspace(env, wt, &rc, &total)?;
        Some(Rc::new(WRec { rc, iota, funspace }))
    }

    /// The dependent eliminator of one translated declaration, built once.
    ///
    /// `ind` must be [`IndApparatus::decls`]' entry for `key`; the guards
    /// inside `GenRecursor::build` and `DepRecursor::build` refuse a carrier
    /// built over a different machine, so a mismatch is a `None` and never a
    /// theorem about somebody else's sets.
    pub fn dep_recursor(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        ind: &derived::inductive::Inductive,
    ) -> Option<Rc<DepRec>> {
        if let Some(d) = self.deprecs.get(key) {
            return Some(d.clone())
        }
        if self.deprec_failed.contains(key) {
            return None
        }
        let w = self.wrec(env);
        let built = w.and_then(|w| {
            let gr = derived::inductive::GenRecursor::build(
                env, &self.mach.borrow(), ind, &w.rc, &w.iota, &w.funspace,
            )?;
            let dr = derived::inductive::DepRecursor::build(env, &self.mach.borrow(), ind, &gr, &w.rc)?;
            Some(Rc::new(DepRec { gr, dr }))
        });
        match built {
            Some(d) => {
                self.deprecs.insert(key.clone(), d.clone());
                Some(d)
            }
            None => {
                self.deprec_failed.insert(key.clone());
                None
            }
        }
    }

    /// The field inhabitations of one class-(S) declaration, built once.
    ///
    /// `cs` must be [`IndApparatus::props`]' entry for `key`;
    /// `LePropFields::build` rebuilds ψ from the spec and compares it against
    /// `LeProp::psi`, so a `ClassS` describing another declaration is a `None`
    /// and never a theorem about somebody else's fields.
    ///
    /// At `k = 0` this is a `Some` whose `steps` are empty — "nothing to
    /// inhabit", not "input not recognised" — which is why the consumer needs
    /// no `match` on the field count.
    pub fn prop_fields(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        cs: &crate::class_s::ClassS,
    ) -> Option<Rc<derived::inductive::family::LePropFields>> {
        if let Some(f) = self.prop_fields.get(key) {
            return Some(f.clone())
        }
        if self.prop_fields_failed.contains(key) {
            return None
        }
        let built = derived::inductive::family::LePropFields::build(
            env, &self.mach.borrow(), &cs.spec, &cs.lp, &cs.params,
        )
        .map(Rc::new);
        match built {
            Some(f) => {
                self.prop_fields.insert(key.clone(), f.clone());
                Some(f)
            }
            None => {
                self.prop_fields_failed.insert(key.clone());
                None
            }
        }
    }

    /// The field inhabitations of one **class-(P)** declaration, built once.
    ///
    /// `tt` must be [`IndApparatus::truncs`]' entry for `key`:
    /// `TruncFields::over_declaration` compares `tc.elim`'s conclusion against
    /// `∃w. w ∈ ind(p⃗)` rebuilt from `ind`, so a truncation of some other
    /// declaration is a `None` and never a theorem about somebody else's
    /// fields.
    pub fn trunc_fields(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        tt: &TruncTranslation,
    ) -> Option<Rc<derived::inductive::family::TruncFields>> {
        if let Some(f) = self.trunc_fields.get(key) {
            return Some(f.clone())
        }
        if self.trunc_fields_failed.contains(key) {
            return None
        }
        let built = derived::inductive::family::TruncFields::over_declaration(
            env, &self.mach.borrow(), &tt.ind, &tt.tc,
        )
        .map(Rc::new);
        match built {
            Some(f) => {
                self.trunc_fields.insert(key.clone(), f.clone());
                Some(f)
            }
            None => {
                self.trunc_fields_failed.insert(key.clone());
                None
            }
        }
    }

    /// [`IndApparatus::trunc_fields`]' store, for `--dump-theorems`.
    pub fn stored_trunc_fields(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::family::TruncFields>> {
        self.trunc_fields.get(k)
    }

    pub fn trunc_fields_attempted(&self, k: &ConstKey) -> bool {
        self.trunc_fields_failed.contains(k)
    }

    /// The reindexing operator, built once. See [`IndApparatus::reindex`].
    pub fn reindex(&mut self, env: &mut Env) -> Option<Rc<derived::sigma::Reindex>> {
        if let Some(r) = &self.reindex {
            return Some(r.clone())
        }
        if self.reindex_failed {
            return None
        }
        let built = derived::sigma::Reindex::new(env, &self.mach.borrow().wt.sums, &self.mach.borrow().proj)
            .map(Rc::new);
        match built {
            Some(r) => {
                self.reindex = Some(r.clone());
                Some(r)
            }
            None => {
                self.reindex_failed = true;
                None
            }
        }
    }

    /// The push operator, built once — **the machine's own**.
    ///
    /// This used to be a memo of mini's, beside [`IndApparatus::reindex`], and
    /// that was right for exactly as long as `push` was only a step in a mini
    /// derivation. It is not any more: `derived::inductive::motive::dep_minor`
    /// *states* the applied minor at `push(tⱼ, β₀ⱼ(p⃗))`, so the operator is
    /// part of the premises a declaration carries, and a second one here would
    /// make every one of those statements about a term this crate's `push`
    /// theorems say nothing about. Delegating rather than mirroring is what
    /// makes the two the same by construction.
    pub fn push(&mut self, env: &mut Env) -> Option<Rc<derived::sigma::Push>> {
        self.mach.borrow().push(env)
    }

    /// The field inhabitations of one **class-(T)** declaration, built once.
    ///
    /// `t` must be [`IndApparatus::decls`]' entry for `key`.
    /// `DeclFields::over_declaration` refuses an `Inductive` that is not over
    /// this machine, and every one of its other refusals is a statement
    /// comparison against the spec it was handed, so a carrier belonging to
    /// another declaration is a `None` and never a theorem about somebody
    /// else's fields.
    ///
    /// One `w_rect` Separation per call — for the whole ladder, not per rung —
    /// so this is identity and not speed, exactly as its two siblings are.
    pub fn decl_fields(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        t: &Translated,
    ) -> Option<Rc<derived::inductive::DeclFields>> {
        if let Some(f) = self.decl_fields.get(key) {
            return Some(f.clone())
        }
        if self.decl_fields_failed.contains(key) {
            return None
        }
        let built =
            derived::inductive::DeclFields::over_declaration(env, &self.mach.borrow(), &t.ind).map(Rc::new);
        match built {
            Some(f) => {
                self.decl_fields.insert(key.clone(), f.clone());
                Some(f)
            }
            None => {
                self.decl_fields_failed.insert(key.clone());
                None
            }
        }
    }

    /// [`IndApparatus::decl_fields`]' store, for `--dump-theorems`.
    pub fn stored_decl_fields(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::DeclFields>> {
        self.decl_fields.get(k)
    }

    pub fn decl_fields_attempted(&self, k: &ConstKey) -> bool {
        self.decl_fields_failed.contains(k)
    }

    /// The typed projections and η rule of one **class-(T)** declaration, built
    /// once.
    ///
    /// `t` must be [`IndApparatus::decls`]' entry for `key`.
    /// `crate::proj_data::build` mints the field variables and the `k`
    /// computation rules at them, and `DeclProj::over_declaration` **compares
    /// every one against its own `proj_of`** before deriving anything — so the
    /// term a checker projects with and the term these theorems are about
    /// cannot be two different terms, and a carrier belonging to another
    /// declaration is a `None`.
    pub fn decl_proj(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        t: &Translated,
    ) -> Option<Rc<derived::inductive::decl_proj::DeclProj>> {
        if let Some(p) = self.decl_projs.get(key) {
            return Some(p.clone())
        }
        if self.decl_projs_failed.contains(key) {
            return None
        }
        let built = crate::proj_data::build(env, &self.mach.borrow(), &t.ind).map(Rc::new);
        match built {
            Some(p) => {
                self.decl_projs.insert(key.clone(), p.clone());
                Some(p)
            }
            None => {
                self.decl_projs_failed.insert(key.clone());
                None
            }
        }
    }

    /// [`IndApparatus::decl_proj`]' store, for `--dump-theorems`.
    pub fn stored_decl_proj(
        &self,
        k: &ConstKey,
    ) -> Option<&Rc<derived::inductive::decl_proj::DeclProj>> {
        self.decl_projs.get(k)
    }

    pub fn decl_proj_attempted(&self, k: &ConstKey) -> bool {
        self.decl_projs_failed.contains(k)
    }

    /// The `Prop`-motive elimination rule of one indexed class-(T)
    /// declaration, built once.
    ///
    /// `ind` and `fam` must be [`IndApparatus::indexed`]' entry for `key` —
    /// `over_family` takes the family as **one** struct precisely so a carrier
    /// and a `good` from two different builds cannot be mixed, and it refuses
    /// an `Inductive` that is not over this machine.
    pub fn indexed_prop_recursor(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        ind: &derived::inductive::Inductive,
        fam: &derived::inductive::family::IndexedInductive,
    ) -> Option<Rc<derived::inductive::family::IndexedPropRecursor>> {
        if let Some(r) = self.prop_recs.get(key) {
            return Some(r.clone())
        }
        if self.prop_recs_failed.contains(key) {
            return None
        }
        let built = derived::inductive::family::IndexedPropRecursor::over_family(
            env, &self.mach.borrow(), ind, fam,
        )
        .map(Rc::new);
        match built {
            Some(r) => {
                self.prop_recs.insert(key.clone(), r.clone());
                Some(r)
            }
            None => {
                self.prop_recs_failed.insert(key.clone());
                None
            }
        }
    }

    /// The elimination rule of one indexed **class-(P)** declaration, built
    /// once.
    ///
    /// `ind`, `fam` and `tc` must be [`IndApparatus::truncs_ix`]' entry for
    /// `key`: `over_family` pins `tc` against the family it is handed, so a
    /// truncation of one declaration cannot be eliminated into another's
    /// induction, and one `w_rect` Separation is minted per call — identity,
    /// not speed, exactly as [`IndApparatus::prop_recs`] is.
    pub fn indexed_trunc_recursor(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        tr: &derived::prop::trunc::Trunc,
        ind: &derived::inductive::Inductive,
        fam: &derived::inductive::family::IndexedInductive,
        tc: &derived::inductive::family::TruncCarrier,
    ) -> Option<Rc<derived::inductive::family::IndexedTruncRecursor>> {
        if let Some(r) = self.trunc_recs_ix.get(key) {
            return Some(r.clone())
        }
        if self.trunc_recs_ix_failed.contains(key) {
            return None
        }
        let built = derived::inductive::family::IndexedTruncRecursor::over_family(
            env, &self.mach.borrow(), tr, ind, fam, tc,
        )
        .map(Rc::new);
        match built {
            Some(r) => {
                self.trunc_recs_ix.insert(key.clone(), r.clone());
                Some(r)
            }
            None => {
                self.trunc_recs_ix_failed.insert(key.clone());
                None
            }
        }
    }

    /// The **value**-motive elimination rule of one indexed class-(T)
    /// declaration, built once, with the `GenRecursor` it stands on.
    ///
    /// `ind` and `fam` must be [`IndApparatus::indexed`]' entry for `key`.
    pub fn indexed_dep_recursor(
        &mut self,
        env: &mut Env,
        key: &ConstKey,
        ind: &derived::inductive::Inductive,
        fam: &derived::inductive::family::IndexedInductive,
    ) -> Option<Rc<derived::inductive::family::IndexedDepRecursor>> {
        if let Some(r) = self.dep_recs_ix.get(key) {
            return Some(r.clone())
        }
        if self.dep_recs_ix_failed.contains(key) {
            return None
        }
        let built = self.wrec(env).and_then(|w| {
            let gr = derived::inductive::GenRecursor::build(
                env, &self.mach.borrow(), ind, &w.rc, &w.iota, &w.funspace,
            )?;
            derived::inductive::family::IndexedDepRecursor::over_family(
                env, &self.mach.borrow(), ind, fam, &gr, &w.rc,
            )
            .map(Rc::new)
        });
        match built {
            Some(r) => {
                self.dep_recs_ix.insert(key.clone(), r.clone());
                Some(r)
            }
            None => {
                self.dep_recs_ix_failed.insert(key.clone());
                None
            }
        }
    }
}

impl Default for Interp {
    fn default() -> Self { Interp::new() }
}

impl Interp {
    pub fn new() -> Interp {
        // A private core: one `Env::new()` fast-forwarded past the prelude —
        // exactly the preamble this constructor used to run inline. The
        // prelude was proved against a different `Env`; an `Env` is only a
        // pair of counters, so replaying its theorems is sound whichever
        // `Env` the core minted.
        Interp::over(EnvCore::fresh())
    }

    /// An `Interp` over a **caller-supplied** [`EnvCore`] — the `Nat::over`
    /// pattern at the engine root. Handing the same core to this and to the
    /// checker's `tg::install_shared_core` is what makes the two engines'
    /// skeleton keys equal terms, their hole series one series, and their
    /// W-type machines one machine; `Interp::new` hands each `Interp` a
    /// private core, which is the historical two-signature behaviour.
    pub fn over(core: EnvCore) -> Interp {
        let prelude = prelude();
        let x_canon = core.x_canon;
        let cumul = Cumul::new(&mut core.env_mut(), &prelude.tower, CUMUL_HEIGHT)
            .expect("the cumulativity table is a closed derivation over the prelude's own tower");
        let mut ip = Interp {
            core,
            prelude,
            x_canon,
            cumul,
            consts: HashMap::new(),
            lams: HashMap::new(),
            fibres: HashMap::new(),
            conds: HashMap::new(),
            lam_by_sym: HashMap::new(),
            fibre_by_sym: HashMap::new(),
            cond_by_sym: HashMap::new(),
            prop_sub: None,
            dprod_fs: HashMap::new(),
            direct: None,
            nat: None,
            nat_failed: false,
            direct_failed: false,
            acc: None,
            acc_failed: false,
            rec_acc: None,
            rec_acc_failed: false,
            rec_acc_elims: HashMap::new(),
            quotient: None,
            quotient_failed: false,
            eta: None,
            eta_failed: false,
            ind: None,
            ind_failed: false,
            convs: ConvStats::default(),
            lazy_fills: 0,
            labels: HashMap::new(),
            labels_on: false,
            sym_labels: HashMap::new(),
        };
        ip.sym_labels.insert(ip.prelude.ap.app, "app");
        ip.sym_labels.insert(ip.prelude.fs_sym(), "fs");
        ip
    }

    /// The shared kernel `Env`, for the duration of one statement. Every use
    /// is deliberately short-lived: holding this across a call that itself
    /// reaches the core would panic on the re-entrant borrow.
    pub fn env_mut(&self) -> std::cell::RefMut<'_, Env> { self.core.env_mut() }

    /// Mint a fresh variable. One internal borrow, so two of these may sit in
    /// one expression — which `env_mut().fresh_var()` twice may not.
    pub fn fresh_var(&self) -> FreeVar { self.core.fresh_var() }

    /// The shared-signature handle, for handing this `Interp`'s `Env`,
    /// canonical variables and machine to the other engine — or to a second
    /// `Interp`, whose keys then compare term-for-term with this one's.
    pub fn core(&self) -> &EnvCore { &self.core }

    /// The name of an ambient symbol, for a blocker report.
    pub fn sym_label(&self, f: FnSym) -> Option<&'static str> { self.sym_labels.get(&f).copied() }

    /// Name a term for the blocker report. Diagnostics only.
    pub fn set_label(&mut self, t: &Term, s: impl Into<String>) {
        self.labels.entry(t.clone()).or_insert_with(|| s.into());
    }

    /// The name, if this term has one.
    pub fn label_of(&self, t: &Term) -> Option<&str> { self.labels.get(t).map(String::as_str) }

    /// The inductive-translation apparatus, over **this** `Interp`'s own tower.
    ///
    /// The signature identity is the whole point and it is checked, not
    /// assumed: [`derived::inductive::Machine::new`] and
    /// [`IndChain::new`] each mint a fresh `Wtype`, `Bound` and `Tower`, and a
    /// second `W` or a second `U(·)` is a *different symbol* — every theorem
    /// about it would be true of a set that is not this carrier and would fail
    /// to compose with `⟦Sort n⟧`. So both are built with the `over`
    /// constructors on the prelude's own tower, and the resulting `U₁` is
    /// compared against [`Interp::sort`]`(1)` before anything is derived over
    /// it.
    /// The apparatus **if one has already been built**, and never a reason to
    /// build one.
    ///
    /// [`Interp::ind_apparatus`] constructs on first use, which is right for a
    /// route that is about to derive something and wrong for a *routing*
    /// question. [`crate::iota_model::selects`] is asked at every recursor
    /// redex in every file, and `crate::run::check_file` is explicit that a
    /// file with no nested declaration must not acquire an apparatus it would
    /// otherwise never have had — a `Quot.lift` reduction in a file with no
    /// inductive translation would otherwise mint a whole [`Machine`].
    pub fn ind_built(&self) -> Option<&IndApparatus> { self.ind.as_deref() }

    pub fn ind_apparatus(&mut self) -> Option<&mut IndApparatus> {
        if self.ind.is_none() && !self.ind_failed {
            self.ind = IndApparatus::build(&self.core, &self.prelude).map(Box::new);
            self.ind_failed = self.ind.is_none();
        }
        self.ind.as_deref_mut()
    }

    /// The three things a zone-B construction needs at once: the kernel `Env`,
    /// the apparatus, and the ambient signature. Handed out together because
    /// every builder needs all three. The `Env` arrives as a `RefMut` guard on
    /// the shared core — callers rebind it with `let env = &mut *env;` and
    /// proceed exactly as before; the guard lives to the end of the caller's
    /// borrow, during which only `derived/` code (which never reaches back
    /// into the core) runs.
    pub fn ind_parts(
        &mut self,
    ) -> Option<(std::cell::RefMut<'_, Env>, &mut IndApparatus, Rc<Prelude>)> {
        self.ind_apparatus()?;
        let p = self.prelude.clone();
        let Interp { core, ind, .. } = self;
        Some((core.env_mut(), ind.as_deref_mut()?, p))
    }

    /// **Proof irrelevance**: `Γ ⊢ ⟦e⟧ = •` from `Γ ⊢ ⟦T⟧ ∈ U₀` and
    /// `Γ ⊢ ⟦e⟧ ∈ ⟦T⟧`.
    ///
    /// [`derived::anchor::falsity::prop_subsingleton`] states it for every
    /// proposition at once — a member of `{0,1}` is empty or is `1`, and `1`'s
    /// only element is `•` — so nothing about how `T` was built is needed and
    /// there is nothing to look up.
    ///
    /// **This is where §6.5's "addition over mini-lean's control flow" turns
    /// out to be unnecessary**, and the design said it was. §6.5 asked for
    /// `⟦e₂⟧` to be *retargeted into `⟦T₁⟧`* along a conversion of the two
    /// types, which is a strictness delta (§13 risk 2) and an extra recursive
    /// `assert_def_eq` at every proof comparison. It is not needed: each side
    /// reaches `•` from *its own* type independently, and the equation is then
    /// `trans` of one with `symm` of the other. The two types are never
    /// compared.
    pub fn point_of_proof(&mut self, ty_mem: &Thm, e_mem: &Thm) -> Option<Thm> {
        if self.prop_sub.is_none() {
            let p = self.prelude.clone();
            let t = derived::anchor::falsity::prop_subsingleton(&mut self.env_mut(), &p.tower.sums)?;
            self.prop_sub = Some(t);
        }
        let rule = self.prop_sub.clone()?;
        let (subj, set) = e_mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        // The two premises must speak of the same `T`, and `T` must be in the
        // tower's own `U₀` — checked, not assumed.
        if *ty_mem.concl() != Formula::mem(set.clone(), self.sort(0)) {
            return None
        }
        let inst = derived::inst_all(&rule, &[set, subj.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(ty_mem, e_mem))?;
        (*out.concl() == Formula::eq(subj, self.point())).then_some(out)
    }

    /// Record one conversion in the §0.3 census.
    pub fn note_conv(&mut self, ev: &crate::ev::Ev) {
        match ev {
            crate::ev::Ev::Proved(t) => {
                let free = t.hyps().is_empty();
                let moved = t.concl().as_eq().is_some_and(|(a, b)| a != b);
                self.convs.proved += 1;
                self.convs.sealed += usize::from(free);
                self.convs.moved += usize::from(moved);
                self.convs.moved_sealed += usize::from(moved && free);
            }
            crate::ev::Ev::Gap(g) => {
                self.convs.gapped += 1;
                let k = crate::ledger::Ledger::key(Some(g));
                *self.convs.gapped_by.entry(k).or_default() += 1;
            }
        }
    }

    /// A term's applicative structure: the head symbol and its arguments, or
    /// `None` if the term is a variable.
    ///
    /// Read off the term by [`kernel::Term::as_app`]. **It cannot miss**, and
    /// that is the whole of the difference from what it replaced: this used to
    /// be a lookup in a `parts: HashMap<Term, (FnSym, Vec<Term>)>` that every
    /// builder had to write to, so a term the *kernel* built — a substitution
    /// instance, or an endpoint of `derived::congr` — read back as structureless
    /// and gapped the next decomposition. See [`derived::skeleton`] for the
    /// table's cost and `PRELUDE-COST.md` §3.2 for the measurement.
    pub fn parts_of(&self, t: &Term) -> Option<(FnSym, Vec<Term>)> {
        t.as_app().map(|(f, args)| (f, args.to_vec()))
    }

    /// `Term::apply`.
    ///
    /// Kept as a method because the call sites read as "the interpretation
    /// builds this", and because it was for years the *only* sanctioned way to
    /// build an applicative term — one that failed to go through it produced a
    /// term nothing could take apart again. [`Interp::parts_of`] no longer
    /// distinguishes them, so this is now plain construction.
    pub fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term { Term::apply(f, args) }

    /// The canonical binder slot.
    pub fn x_canon(&self) -> FreeVar { self.x_canon }

    /// The `i`-th canonical hole variable, allocated on demand — from the
    /// [`EnvCore`], so the series is one series across every client of the
    /// core, the checker included.
    pub fn hole_var(&mut self, i: usize) -> FreeVar { self.core.hole_var(i) }

    /// Split `t` into the part mentioning `v` and its maximal `v`-free
    /// subterms, which are pushed onto `holes` and replaced by canonical hole
    /// variables; `v` itself becomes [`Interp::x_canon`].
    ///
    /// **Total** — see [`derived::skeleton::skeleton`]. It used to answer
    /// `None` for a subterm mentioning `v` that had not been built through
    /// [`Interp::mk`], which was read as "the interpretation leaked a
    /// variable"; the structure is now read off the term, so there is no such
    /// term and nothing to leak.
    pub fn skeleton(&mut self, t: &Term, v: FreeVar, holes: &mut Vec<Term>) -> Term {
        let core = self.core.clone();
        let mut hv = |i: usize| -> FreeVar { core.hole_var(i) };
        skeleton::skeleton(self.x_canon, &mut hv, t, v, holes)
    }

    // ─────────────────────────────────────────────────── the sort tower ──

    /// `⟦Sort n⟧`. `⟦Sort 0⟧ = U₀ = {0,1}` is `Prop`; `⟦Sort 1⟧ = U(ω)` is
    /// `Type 0`; above that `⟦Sort (n+1)⟧ = U(⟦Sort n⟧)`.
    ///
    /// **The `n` is a Lean universe level and the answer is a rung of the
    /// cumulative hierarchy, and this line is where the two senses meet.** They
    /// are different things — `crate::expr::Level` is a level *expression*,
    /// `derived::tower::Rung` is a bundle of closed theorems about a concrete
    /// `Uₙ` — and everywhere else in the workspace confusing them is an error.
    /// Here it is the interpretation itself: `⟦Sort ℓ⟧ = U_ℓ`, at a numeral,
    /// because `n` is what the ground-σ pre-pass already evaluated the level
    /// to. `crate::zoneb::decl_universe` is the consumer that most depends on
    /// it and says so.
    pub fn sort(&self, n: u32) -> Term { self.prelude.tower.u(n as usize) }

    /// `⊢ ⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧`, the typing of a sort.
    ///
    /// Two cases, and the split is the tower's, not a special case of mini's:
    /// the tower is seeded at `ω` rather than at `U₀`, so `⟦Sort 1⟧` is *not*
    /// `U(⟦Sort 0⟧)` and the generic `⊢ ∀x. x ∈ U(x)` does not carry `n = 0`.
    /// [`Prelude::u0_in_u1`] is the theorem that does.
    pub fn sort_typing(&self, n: u32) -> Option<Thm> {
        if n == 0 {
            return Some(self.prelude.u0_in_u1.clone())
        }
        // `⟦Sort (n+1)⟧ = U(⟦Sort n⟧)` for `n ≥ 1`, so `mem_u` at `⟦Sort n⟧` is
        // exactly the statement wanted.
        let t = self.sort(n);
        let out = derived::inst_all(&self.prelude.mem_u, std::slice::from_ref(&t))?;
        (*out.concl() == Formula::mem(t.clone(), self.sort(n + 1))).then_some(out)
    }

    // ────────────────────────────────────────────────────── application ──

    /// `⟦f a⟧ = app(⟦f⟧, ⟦a⟧)` on the non-proof branch of §6.2.
    pub fn app(&mut self, f: Term, a: Term) -> Term {
        let ap = self.prelude.ap.app;
        self.mk(ap, vec![f, a])
    }

    /// `•`, Carneiro §6.2's interpretation of every *proof*.
    pub fn point(&self) -> Term { self.prelude.point() }

    // ──────────────────────────────────── the non-dependent Π clause ──
    /// The term `fs(A, B)`, the library's function space.
    ///
    /// **Not an interpretation clause.** `⟦Π x:A. B⟧` is `dprod` at every
    /// binder-free codomain too (`SCOPING.md` §10), so nothing that names an
    /// *interpreted* arrow calls this — [`Interp::const_dprod`] is what those
    /// call. What is left for it is the library's own function spaces, which
    /// are real sets this checker still has to name: the recursor's
    /// `wrec ∈ fs(W,T)` obligation is the standing example, and the two `Π`
    /// bridges in `derived::ext` are stated over `fs` whatever mini emits.
    ///
    /// Kept with [`Interp::fs_typing`] and [`Interp::fs_app`], which have no
    /// caller today either and are tested. They are three wrappers over
    /// `derived::fs`, which the decision keeps *exactly as it is*; deleting a
    /// tested wrapper over a library the project has committed to is not a
    /// safety improvement, and their tests are that library's non-vacuity.
    ///
    /// *(The paragraph that stood here argued that `dep = has_bvar(body, 0)` is
    /// β-unstable — `(fun _ => T) x` mentions the binder and `T` does not — so
    /// one side of a conversion could take this clause and the other
    /// [`Interp::dprod_term`]'s, both correctly, with the two spellings bridged
    /// by `dprod_fs_bridge`. Every word of that was true and it is why the
    /// clause is gone: an instability that needs a bridge at 937 conversions is
    /// a clause that should not exist.)*
    pub fn fs(&mut self, dom: Term, cod: Term) -> Term {
        let fs = self.prelude.fs_sym();
        self.mk(fs, vec![dom, cod])
    }

    /// **`⟦A → B⟧` at a binder-free `B`** — `dprod` at the constant fibre, and
    /// the replacement for every `Interp::fs` that was naming an *interpreted*
    /// arrow.
    ///
    /// `⟦Π x:A. B⟧` is `dprod` whether or not `B` mentions `x` (`SCOPING.md`
    /// §10), so a consumer that knows a Lean arrow is non-dependent — a
    /// motive's `T p⃗ → Sort u₁`, say — still has to name a `dprod`. It does not
    /// have to name a *new* one: [`skeleton`](Interp::skeleton) makes a
    /// binder-free term **hole 0 entire**, so the key in
    /// [`Interp::fibres`] is the bare `Term::var(h₀)` for every non-dependent
    /// arrow in the corpus — one table entry, one `b(h₀,x) = h₀` projection,
    /// minted once. The arguments are `fs`'s swapped.
    ///
    /// `derived::fs` is untouched and stays in the library; what is gone is the
    /// *clause* that emitted it. Anything naming a function space that is not
    /// an interpreted `Π` — the recursor's own `fs(W,T)` obligations, say —
    /// still calls [`Interp::fs`], and that is the distinction to keep.
    pub fn const_dprod(&mut self, dom: Term, cod: Term) -> Option<Term> {
        let site = self.const_fibre_site(&cod)?;
        Some(self.dprod_term(&site, dom))
    }

    /// The constant fibre's own site, for a caller that needs the application
    /// rule as well as the term — `dprod_app` where it used to call `fs_app`.
    ///
    /// The binder variable is fresh and does not occur in `cod`, which is what
    /// makes the skeleton hole 0 entire.
    pub fn const_fibre_site(&mut self, cod: &Term) -> Option<FibreSite> {
        let w = self.fresh_var();
        self.fibre_site(cod, w)
    }

    /// From `Γ ⊢ t ∈ Uₘ` infer `Γ ⊢ t ∈ Uₙ`, **keeping `Γ`**.
    ///
    /// [`Cumul::raise`] is the same rule for `Γ = ∅`, and refuses a
    /// hypothesis-carrying premise on purpose: it would otherwise union the
    /// caller's `Γ` into a result its own signature calls `⊢ t ∈ Uₙ`. That
    /// guard is right, and it names this module as the reason it exists —
    /// `mini` is exempt from boundary rule 6 and legitimately holds
    /// `Γ`-carrying theorems, so it is the one caller that can trip it.
    ///
    /// The fix belongs here rather than in `derived`, and it is not a
    /// weakening: the inclusion `⊢ Uₘ ⊆ Uₙ` is itself unconditional, and
    /// [`Thm::mp`] merges hypothesis sets correctly, so `Γ ⊢ t ∈ Uₘ` really
    /// does give `Γ ⊢ t ∈ Uₙ`. What mini must not do — and does not — is
    /// *label* the result unconditional; that is [`crate::ev::Sealed`]'s job at
    /// the store, and `Γ` is carried honestly until a scope discharges it.
    ///
    /// Every `Π` under a binder reaches this with a non-empty `Γ`: the domain's
    /// typing is derived under the enclosing scopes' hypotheses. So the empty
    /// case is the *rare* one here, which is exactly the inversion that makes
    /// mini's context constant-cost.
    pub fn raise_in_gamma(&self, m: usize, n: usize, mem: &Thm) -> Option<Thm> {
        let (x, _) = mem.concl().as_mem()?;
        let x = x.clone();
        // Same shape check `Cumul::raise` makes: a membership in some *other*
        // set must be refused rather than instantiated into nonsense.
        if *mem.concl() != Formula::mem(x.clone(), self.cumul.u(m)?) {
            return None
        }
        let step = derived::inst_all(self.cumul.lift(m, n)?, std::slice::from_ref(&x))?;
        Thm::mp(&step, mem)
    }

    /// `⊢ Uₘ ⊆ Uₙ`, for `m ≤ n ≤ height` — the inclusion itself, for the one
    /// caller that cannot use [`Interp::raise_in_gamma`].
    ///
    /// A membership whose antecedent lives in its *conclusion* — `⊢ H → A ∈ Uₘ`
    /// — is not of the shape `raise` accepts, and composing the inclusion with
    /// a syllogism is the whole of the fix. Handing back the inclusion rather
    /// than growing a second `raise` variant is deliberate: the variant would
    /// have to guess which subterm of the conclusion is the subject.
    pub fn cumul_lift(&self, m: usize, n: usize) -> Option<&Thm> { self.cumul.lift(m, n) }

    /// `⊢ fs(⟦A⟧,⟦B⟧) ∈ ⟦Sort (imax l1 l2)⟧`, from `⊢ ⟦A⟧ ∈ ⟦Sort l1⟧` and
    /// `⊢ ⟦B⟧ ∈ ⟦Sort l2⟧`. Lean's non-dependent `Π` typing rule.
    ///
    /// `imax l1 l2` with `l2 > 0` is `max l1 l2`, so both premises must first
    /// be **raised** to that level — which is what the cumulativity table is
    /// for, and is the step that makes this rule need more than
    /// `Tower::funspace` alone. `l2 = 0` is the `Prop` clause and does not come
    /// here.
    ///
    /// Every intermediate is checked against the statement claimed, so a
    /// mismatched tower or an out-of-range level yields `None` — a gap — and
    /// never a theorem about the wrong universe.
    ///
    /// **`Γ` is carried, not required to be empty.** Under a binder the
    /// domain's typing is derived from the enclosing scopes' hypotheses, so the
    /// premises normally have a non-empty `Γ` and the conclusion inherits it.
    /// See [`Interp::raise_in_gamma`].
    pub fn fs_typing(&mut self, dom_mem: &Thm, cod_mem: &Thm, l1: u32, l2: u32) -> Option<Thm> {
        if l2 == 0 {
            return None // the `Prop` clause; a different derivation entirely
        }
        let n = l1.max(l2) as usize;
        if n > self.cumul.height {
            return None
        }
        let a = dom_mem.concl().as_mem()?.0.clone();
        let b = cod_mem.concl().as_mem()?.0.clone();
        // Both premises to `U_n`, keeping whatever `Γ` they carry.
        let a_mem = self.raise_in_gamma(l1 as usize, n, dom_mem)?;
        let b_mem = self.raise_in_gamma(l2 as usize, n, cod_mem)?;
        // `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` at the seed
        // of `U_n`, which for `n ≥ 1` is what `Tower::level(n)` is `U(·)` of.
        let seed = self.prelude.tower.seed(n);
        let inst = derived::inst_all(&self.prelude.tower.funspace, &[seed, a.clone(), b.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(&a_mem, &b_mem))?;
        let want = Formula::mem(self.fs(a, b), self.sort(n as u32));
        (*out.concl() == want).then_some(out)
    }

    // ──────────────────────────────────────────────────── the λ clause ──

    /// The graph machinery for one lambda **body shape**, keyed on its
    /// skeleton.
    ///
    /// Keyed, not memoised: two occurrences of one body shape must be the
    /// *same* graph symbol, or their definitional equality needs a theorem
    /// where reflexivity should do. The `holes` differ per occurrence and are
    /// therefore returned rather than stored.
    pub fn lam_site(&mut self, body_tm: &Term, w: FreeVar) -> Option<LamSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_tm, w, &mut holes);
        let k = holes.len();
        if let Some(c) = self.lams.get(&skel) {
            return Some(LamSite { holes, ..c.clone() })
        }
        // `t(h⃗, x) = skeleton`, with the holes **first** and the binder
        // **last** — the argument order every `_n` construction assumes.
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (t, t_ax) = derived::define_abbrev(&mut self.env_mut(), &xs, &skel)?;
        let p = self.prelude.clone();
        let (lam, lam_ax) = derived::funcs::lambda_n(&mut self.env_mut(), &p.ap, t)?;
        let site = LamSite { t, skel: skel.clone(), t_ax, lam, lam_ax, holes: Vec::new(), k };
        self.lams.insert(skel, site.clone());
        self.lam_by_sym.insert(lam, site.clone());
        Some(LamSite { holes, ..site })
    }

    /// `⟦λ x:A. b⟧ = lam(h⃗,⟦A⟧)`, taken apart again: the site at *this*
    /// occurrence's holes, and the domain.
    ///
    /// The inverse of [`Interp::lam_term`], and the reason `whnf`'s beta step
    /// needs no second traversal: the redex's own interpretation names the
    /// graph symbol, and the symbol names the site.
    pub fn as_lam(&self, t: &Term) -> Option<(LamSite, Term)> {
        let (f, mut args) = self.parts_of(t)?;
        let site = self.lam_by_sym.get(&f)?;
        if args.len() != site.k + 1 {
            return None
        }
        let dom = args.pop()?;
        Some((LamSite { holes: args, ..site.clone() }, dom))
    }

    /// `⟦Π x:A. B⟧`, taken apart: which of §6.2's **two** clauses built it, its
    /// domain, and the site that carries the fibre.
    ///
    /// **A constant-fibre `dprod` and a genuine dependent one both land in
    /// `Dep`, told apart by which fibre symbol** — which is what
    /// [`Interp::fibre_by_sym`] is for, and is `QUOT-MODEL.md` §2.1's own
    /// invariant. An `fs` term is not an interpreted `Π` and answers `None`.
    pub fn as_pi(&self, t: &Term) -> Option<PiShape> {
        let (f, mut args) = self.parts_of(t)?;
        if let Some(site) = self.fibre_by_sym.get(&f) {
            if args.len() != site.k + 1 {
                return None
            }
            let dom = args.pop()?;
            return Some(PiShape::Dep { site: FibreSite { holes: args, ..site.clone() }, dom })
        }
        if let Some(site) = self.cond_by_sym.get(&f) {
            if args.len() != site.k + 1 {
                return None
            }
            let dom = args.pop()?;
            return Some(PiShape::Prop { site: CondSite { holes: args, ..site.clone() }, dom })
        }
        None
    }

    /// `⟦λ x:A. b⟧ = lam(h⃗, ⟦A⟧)` — the graph of the body symbol over the
    /// domain, §6.2's right column.
    pub fn lam_term(&mut self, site: &LamSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.lam, args)
    }

    /// **The conditional beta chain down a λ-nest**:
    /// `Γ ⊢ app(…app(f, a₀)…, a_{n-1}) = bottom`, together with `bottom`.
    ///
    /// This is the one thing the Lean-facing layer of §9 zone B needs that
    /// nothing else does. `⟦T⟧` is a nest of graphs whose bottom is the
    /// carrier `ind(p⃗)`; `Ctor::mem` speaks of `ind(p⃗)`; a use site speaks of
    /// the applied spine. The two are related by beta, once per level, and the
    /// premise each level consumes is the parameter's own typing — which the
    /// caller holds, because it is the scope assumption the binder opened.
    ///
    /// **Nothing is searched.** The nest is taken apart with [`Interp::as_lam`],
    /// which reads the graph symbol off the term itself; the equation at each
    /// level is that symbol's own
    /// `beta_conditional_n` and its own defining axiom. A term that is not a
    /// graph — a nest shallower than the spine — is `None`, never a guess.
    pub fn beta_spine(
        &mut self,
        f: &Term,
        args: &[Term],
        mems: &[Thm],
    ) -> Option<(Term, Thm)> {
        if args.len() != mems.len() {
            return None
        }
        // A parameterless declaration: `⟦T⟧` *is* the carrier and the spine is
        // the empty one, so the equation is reflexivity rather than absent.
        if args.is_empty() {
            return Some((f.clone(), Thm::eq_refl(f.clone())))
        }
        let mut cur = f.clone();
        let mut spine = f.clone();
        let mut acc: Option<Thm> = None;
        for (a, mem) in args.iter().zip(mems.iter()) {
            let (site, dom) = self.as_lam(&cur)?;
            // The premise this level consumes, checked rather than assumed.
            if *mem.concl() != Formula::mem(a.clone(), dom.clone()) {
                return None
            }
            let p = self.prelude.clone();
            let beta = derived::funcs::beta_conditional_n(
                &mut self.env_mut(),
                &p.ap,
                site.t,
                site.lam,
                &site.lam_ax,
            )?;
            let mut inst_args = site.holes.clone();
            inst_args.push(dom);
            inst_args.push(a.clone());
            let step = Thm::mp(&derived::inst_all(&beta, &inst_args)?, mem)?;
            // …and off the body symbol onto the next level's own term.
            let unfold = self.body_unfold(&site, a.clone())?;
            let level = derived::eq_trans(&mut self.env_mut(), &step, &unfold)?;
            let next = level.concl().as_eq()?.1.clone();
            let applied = self.app(spine.clone(), a.clone());
            acc = Some(match acc {
                None => level,
                Some(prev) => {
                    let ap = p.ap.app;
                    let cong = derived::congr(
                        &mut self.env_mut(),
                        ap,
                        &[prev, Thm::eq_refl(a.clone())],
                    )?;
                    derived::eq_trans(&mut self.env_mut(), &cong, &level)?
                }
            });
            spine = applied;
            cur = next;
        }
        let out = acc?;
        (*out.concl() == Formula::eq(spine, cur.clone())).then_some((cur, out))
    }

    /// Instantiate a skeleton: the holes at `holes`, the canonical binder slot
    /// at `x`.
    ///
    /// A walk, not a search — the skeleton's own structure is read back with
    /// [`Interp::parts_of`] and its leaves are the canonical variables, so
    /// every node is either a hole, the slot, or an application to descend
    /// into.
    ///
    /// `inst_all` produces the same `Term`, instantiation happening inside the
    /// kernel, and this function exists because it once did not deliver the
    /// same thing: a term's applicative structure lived in a side table that
    /// only `Interp::mk` wrote to, so the kernel's own result arrived as an
    /// opaque blob and the next decomposition of it failed. That was not a
    /// hypothetical — it is how a whole class of curried applications was
    /// silently gapping.
    pub fn rebuild(&mut self, skel: &Term, holes: &[Term], x: &Term) -> Term {
        if *skel == Term::var(self.x_canon) {
            return x.clone()
        }
        for (i, h) in holes.iter().enumerate() {
            if self.core.hole(i).is_some_and(|v| *skel == Term::var(v)) {
                return h.clone()
            }
        }
        let Some((f, args)) = self.parts_of(skel) else { return skel.clone() };
        let mut out = Vec::with_capacity(args.len());
        for a in &args {
            out.push(self.rebuild(a, holes, x));
        }
        self.mk(f, out)
    }

    /// `⊢ t(h⃗, a) = ⟦b[a]⟧` — the body symbol unfolded at an argument.
    ///
    /// **Beta's second leg, and it is not optional.**
    /// [`crate::conv::beta_leg`] lands on `t(h⃗,⟦a⟧)`, a *defined symbol*; the
    /// contractum the caller is about to hand back is `⟦b[a]⟧`. The two are
    /// equal by `t`'s own defining equation, and — this is the skeleton's
    /// substitution-stability property doing its job — instantiating the
    /// skeleton at `(h⃗, ⟦a⟧)` gives `⟦b[a]⟧` **on the nose**, so the leg is
    /// one instantiation and no search.
    ///
    /// Without it every beta step ends at a symbol nothing else mentions, and
    /// the conversion that consumes it fails a shape check one composition
    /// later — which is how this was found.
    ///
    /// It used to open with a [`Interp::rebuild`] whose result was *discarded*:
    /// `derived::inst_all` produces `⟦b[a]⟧` inside the kernel, so while
    /// applicative structure lived in a side table the contractum arrived
    /// unrecorded, and the rebuild was there to walk the same nodes through
    /// `Interp::mk` and file them. `Interp::parts_of` reads structure off the
    /// term, so the walk computed a term nobody read and it is gone.
    pub fn body_unfold(&mut self, site: &LamSite, a: Term) -> Option<Thm> {
        let mut args = site.holes.clone();
        args.push(a);
        derived::inst_all(&site.t_ax, &args)
    }

    /// `⊢ b(q⃗, a) = ⟦B[a]⟧` — a fibre unfolded at a point, for either the
    /// dependent or the `Prop` clause. Same argument as [`Interp::body_unfold`]:
    /// the application rules land on the symbol, and the caller's `⟦B[a]⟧` is
    /// the skeleton instance — and the same discarded rebuild, gone for the
    /// same reason.
    fn fibre_unfold(&mut self, b_ax: &Thm, holes: &[Term], a: &Term) -> Option<Thm> {
        let mut args = holes.to_vec();
        args.push(a.clone());
        derived::inst_all(b_ax, &args)
    }

    /// Rewrite `Γ ⊢ ⟦b⟧ ∈ C` into `Γ ⊢ t(h⃗, w) ∈ C`, which is the shape the
    /// lambda typing rules state their premise in.
    ///
    /// One Leibniz step along the body symbol's own defining equation. The
    /// reassembly property is what makes it possible: instantiating the
    /// skeleton back at `(h⃗, w)` gives `⟦b⟧` on the nose, so the two sides of
    /// the equation are the two terms wanted and nothing has to be searched
    /// for.
    pub fn to_body_symbol(&mut self, site: &LamSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let mut args = site.holes.clone();
        args.push(Term::var(w));
        let tw = self.mk(site.t, args.clone());
        let inst = derived::inst_all(&site.t_ax, &args)?;
        // `⊢ t(h⃗,w) = ⟦b⟧`; Leibniz wants it the other way round.
        if *inst.concl() != Formula::eq(tw.clone(), subj.clone()) {
            return None
        }
        let back = derived::eq_symm(&mut self.env_mut(), &inst)?;
        let x = self.fresh_var();
        let leib =
            Thm::eq_leibniz(subj, tw.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(tw, set)).then_some(out)
    }

    /// `⊢ lam(h⃗,⟦A⟧) ∈ fs(⟦A⟧, C)` from `⊢ ∀x. (x ∈ ⟦A⟧ → t(h⃗,x) ∈ C)`.
    ///
    /// Lean's λ typing rule at a **constant** codomain. `family` is exactly
    /// what [`crate::scope::Closed::discharge`] produces, which is not a
    /// coincidence: the discharge shape and the lemma shape were chosen to be
    /// the same one, so nothing is re-proved against a merged hypothesis set.
    pub fn lam_typing_fs(
        &mut self,
        site: &LamSite,
        dom: Term,
        cod: Term,
        family: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let rule = derived::ext::lam_in_funspace_n(
            &mut self.env_mut(),
            &p.ap,
            &p.prod,
            &p.fs,
            site.t,
            site.lam,
            &site.lam_ax,
        )?;
        let mut args = site.holes.clone();
        args.push(dom.clone());
        args.push(cod.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let out = Thm::mp(&inst, family)?;
        let want = Formula::mem(self.lam_term(site, dom.clone()), self.fs(dom, cod));
        (*out.concl() == want).then_some(out)
    }

    // ──────────────────────────────────────── the dependent Π clause ──

    /// The dependent-product machinery for one **fibre shape** — the skeleton
    /// of `⟦B⟧` under the binder — keyed on that skeleton for the same reason
    /// [`Interp::lam_site`] is.
    ///
    /// This is the whole of `pi-dep`'s assembly, and it is assembly rather than
    /// derivation: every piece already exists in `derived`, and what mini
    /// supplies is the fibre symbol and the wiring. `Tower::family` packages
    /// exactly this for a *unary* fibre; a Lean `Π` body is an open expression,
    /// so mini's fibre has arity `k+1` and needs the `_n` route.
    pub fn fibre_site(&mut self, body_ty_tm: &Term, w: FreeVar) -> Option<FibreSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_ty_tm, w, &mut holes);
        let k = holes.len();
        if let Some(c) = self.fibres.get(&skel) {
            return Some(FibreSite { holes, ..c.clone() })
        }
        // `b(h⃗, x) = ⟦B⟧`'s skeleton — holes first, binder last.
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (b, b_ax) = derived::define_abbrev(&mut self.env_mut(), &xs, &skel)?;

        let p = self.prelude.clone();
        let dp = derived::ext::DProdN::new(&mut self.env_mut(), &p.ap, &p.fs, b)?;
        // The one ingredient that mentions `b`, and hence the only one that
        // has to be re-run per fibre rather than taken from the tower.
        let ur = derived::universe::universe_replacement_n(
            &mut self.env_mut(),
            &p.tower.space.empty_ax,
            dp.img,
            &dp.img_ax,
            b,
        )?;
        let replacement = derived::universe::least_universe_replacement_n(
            &mut self.env_mut(),
            p.tower.space.lu,
            &p.tower.space.lu_ax,
            dp.img,
            b,
            &ur,
        )?;
        let fibre = dp.fibre(&replacement);
        let u = derived::ext::UniverseParts {
            lu: p.tower.space.lu,
            c2: &p.tower.space.c2,
            fs_in_u: &p.tower.funspace_of,
            union: &p.tower.union,
            bin_union: &p.tower.bin_union,
        };
        let general =
            derived::ext::dprod_in_universe_of_n(&mut self.env_mut(), &p.ap, &p.fs, &fibre, &u)?;
        let rule =
            derived::ext::dprod_in_universe_pair_n(&mut self.env_mut(), &p.ap, &fibre, &u, &general)?;
        // `fibre` borrows `replacement`; the borrow ends here.

        let site =
            FibreSite { b, skel: skel.clone(), b_ax, dp: Rc::new(dp), replacement, rule, holes: Vec::new(), k };
        // **The constant fibre gets a label, because it is one symbol
        // corpus-wide and it is the commonest thing in a dump.** Its skeleton
        // is the bare hole-0 variable — `skeleton` makes a binder-free term
        // hole 0 entire — so every non-dependent arrow in the corpus shares it.
        // Every *other* `dprod` symbol is one fibre shape among ~1300, so
        // labelling those all `dprod` would print two different symbols the
        // same way; this one is the degenerate shape and is unique, so naming
        // it costs no ambiguity. `dprod₀(B, A)` is `A → B` — the arguments are
        // `fs`'s swapped, which the label deliberately does not hide, because
        // that order is exactly what a reader comparing a dump against the old
        // spelling has to see.
        if k == 1 && skel == Term::var(self.hole_var(0)) {
            self.sym_labels.insert(site.dp.dprod, "dprod₀");
        }
        self.fibres.insert(skel, site.clone());
        self.fibre_by_sym.insert(site.dp.dprod, site.clone());
        Some(FibreSite { holes, ..site })
    }

    /// `b(q⃗, x)` — the fibre at a point.
    pub fn fibre_at(&mut self, site: &FibreSite, x: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(x);
        self.mk(site.b, args)
    }

    /// `⟦Π x:A. B⟧ = dprod(h⃗, ⟦A⟧)` — §6.2's right column, dependent case.
    pub fn dprod_term(&mut self, site: &FibreSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.dp.dprod, args)
    }

    /// Rewrite `Γ ⊢ ⟦B⟧ ∈ C` into `Γ ⊢ b(h⃗, w) ∈ C`, the shape the `Π` rule
    /// states its fibre premise in. [`Interp::to_body_symbol`] for the fibre.
    pub fn to_fibre_symbol(&mut self, site: &FibreSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        self.rewrite_subject_to_symbol(site.b, &site.b_ax, &site.holes, w, mem)
    }

    /// Rewrite `Γ ⊢ • ∈ ⟦β⟧` into `Γ ⊢ • ∈ b(h⃗,w)` — the `Prop` clause's
    /// fibre, on the **set** side.
    ///
    /// The side matters and getting it wrong is silent: the `Π` rule's premise
    /// is `b(h⃗,x) ∈ ⟦Sort n⟧`, where the fibre is the *subject*
    /// ([`Interp::to_fibre_symbol`]), while `cond_intro`'s is `• ∈ b(h⃗,x)`,
    /// where it is the *set*. Rewriting the subject there produces a theorem
    /// about `b(h⃗,w) ∈ ⟦β⟧`, which is true of nothing in particular and fails
    /// the shape check one step later.
    pub fn to_cond_fibre(&mut self, site: &CondSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        self.rewrite_set_to_symbol(site.b, &site.b_ax, &site.holes, w, mem)
    }

    /// Rewrite `Γ ⊢ s ∈ C` into `Γ ⊢ sym(h⃗,w) ∈ C` along the symbol's own
    /// defining equation.
    fn rewrite_subject_to_symbol(
        &mut self,
        sym: FnSym,
        ax: &Thm,
        holes: &[Term],
        w: FreeVar,
        mem: &Thm,
    ) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let mut args = holes.to_vec();
        args.push(Term::var(w));
        let bw = self.mk(sym, args.clone());
        let inst = derived::inst_all(ax, &args)?;
        if *inst.concl() != Formula::eq(bw.clone(), subj.clone()) {
            return None
        }
        let back = derived::eq_symm(&mut self.env_mut(), &inst)?;
        let x = self.fresh_var();
        let leib = Thm::eq_leibniz(subj, bw.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(bw, set)).then_some(out)
    }

    /// Rewrite `Γ ⊢ s ∈ ⟦B⟧` into `Γ ⊢ s ∈ b(q⃗,w)` — the *set* side, along the
    /// fibre symbol's defining equation, which is what the dependent `λ` rule
    /// wants its premise stated in.
    pub fn to_fibre_set(&mut self, site: &FibreSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        self.rewrite_set_to_symbol(site.b, &site.b_ax, &site.holes, w, mem)
    }

    /// Rewrite `Γ ⊢ s ∈ ⟦B⟧` into `Γ ⊢ s ∈ sym(h⃗,w)`.
    fn rewrite_set_to_symbol(
        &mut self,
        sym: FnSym,
        ax: &Thm,
        holes: &[Term],
        w: FreeVar,
        mem: &Thm,
    ) -> Option<Thm> {
        let mut args = holes.to_vec();
        args.push(Term::var(w));
        // Record the instance, so a later decomposition can walk into it.
        let _ = self.mk(sym, args.clone());
        let at = derived::inst_all(ax, &args)?;
        let back = derived::eq_symm(&mut self.env_mut(), &at)?;
        self.retarget_set(mem, &back)
    }

    /// From `Γ ⊢ x ∈ A` and `⊢ A = B` infer `Γ ⊢ x ∈ B` — MINI-DESIGN.md
    /// §6.2's `retarget`, one Leibniz step on the membership's **right** side.
    ///
    /// This is what a conversion is *for*: every `assert_def_eq` in the
    /// application and `let` clauses ends by moving a typing along the
    /// equation it just proved. `Γ` is carried.
    pub fn retarget_set(&mut self, mem: &Thm, eq: &Thm) -> Option<Thm> {
        let (subj, a) = mem.concl().as_mem()?;
        let (subj, a) = (subj.clone(), a.clone());
        let (lhs, rhs) = eq.concl().as_eq()?;
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        if lhs != a {
            return None
        }
        let x = self.fresh_var();
        let leib =
            Thm::eq_leibniz(lhs, rhs.clone(), x, Formula::mem(subj.clone(), Term::var(x)));
        let out = Thm::mp(&Thm::mp(&leib, eq)?, mem)?;
        (*out.concl() == Formula::mem(subj, rhs)).then_some(out)
    }

    /// `⊢ dprod(h⃗,⟦A⟧) ∈ ⟦Sort n⟧` from `⊢ ⟦A⟧ ∈ ⟦Sort n⟧` and
    /// `⊢ ∀x. (x ∈ ⟦A⟧ → b(h⃗,x) ∈ ⟦Sort n⟧)` — **Lean's dependent `Π` rule**.
    ///
    /// `n` must be `max(l1, l2)`; both premises are the caller's to raise
    /// there, because the fibre premise sits *under* a binder and needs
    /// `Cumul::raise_fibres` rather than `raise`. `Γ` is carried.
    pub fn dprod_typing(
        &mut self,
        site: &FibreSite,
        dom: Term,
        dom_mem: &Thm,
        fibres: &Thm,
        n: u32,
    ) -> Option<Thm> {
        if n == 0 || n as usize > self.cumul.height {
            return None
        }
        let seed = self.prelude.tower.seed(n as usize);
        let mut args = site.holes.clone();
        args.push(seed);
        args.push(dom.clone());
        let inst = derived::inst_all(&site.rule, &args)?;
        let out = Thm::mp(&inst, &derived::and_intro(dom_mem, fibres))?;
        let want = Formula::mem(self.dprod_term(site, dom), self.sort(n));
        (*out.concl() == want).then_some(out)
    }

    /// `⊢ lam(h⃗,⟦A⟧) ∈ dprod(q⃗,⟦A⟧)` from
    /// `⊢ ∀x. (x ∈ ⟦A⟧ → t(h⃗,x) ∈ b(q⃗,x))` — Lean's λ rule at a **dependent**
    /// codomain, and the half of `lam` that `pi-dep` unblocks.
    pub fn lam_typing_dprod(
        &mut self,
        lam: &LamSite,
        fibre: &FibreSite,
        dom: Term,
        family: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let beta =
            derived::funcs::beta_conditional_n(&mut self.env_mut(), &p.ap, lam.t, lam.lam, &lam.lam_ax)?;
        let lam_fs = derived::ext::lam_in_funspace_n(
            &mut self.env_mut(),
            &p.ap,
            &p.prod,
            &p.fs,
            lam.t,
            lam.lam,
            &lam.lam_ax,
        )?;
        let rule = derived::ext::lam_in_dprod_n(
            &mut self.env_mut(),
            &p.ap,
            &p.fs,
            (lam.t, lam.lam, &beta, &lam_fs),
            (fibre.b, fibre.dp.img, &fibre.dp.img_ax, fibre.dp.dprod, &fibre.dp.dprod_def),
        )?;
        let mut args = lam.holes.clone();
        args.extend(fibre.holes.clone());
        args.push(dom.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let out = Thm::mp(&inst, family)?;
        let want =
            Formula::mem(self.lam_term(lam, dom.clone()), self.dprod_term(fibre, dom));
        (*out.concl() == want).then_some(out)
    }

    /// `⊢ push(v, A) ∈ dprod(q⃗, A)` from `⊢ ∀z. (z ∈ A → Q(v,z) ∈ b(q⃗,z))` —
    /// **`push` is the λ-introduction a dependent fibre needs**, and the one a
    /// minor premise's induction hypothesis crosses on.
    ///
    /// [`Interp::lam_typing_dprod`] is the same rule at a [`LamSite`]: a λ mini
    /// built out of Lean syntax, whose body symbol is a skeleton of the
    /// interpretation. Here the graph is `derived::sigma::Push`, whose body is
    /// `Q(v,b) = app(v, ⟨b,•⟩)`, and the quadruple it needs
    /// (`body`, `graph`, `beta`, `lam_in_funspace`) is what that struct already
    /// stores — which is why [`derived::sigma::Push::beta`] is a public field
    /// and this is a rule instance rather than a construction. The
    /// `derived`-side measurement of that claim is
    /// `the_push_is_the_lambda_introduction_a_dependent_fibre_needs`.
    pub fn push_lam_typing(
        &mut self,
        px: &derived::sigma::Push,
        fibre: &FibreSite,
        v: &Term,
        dom: Term,
        family: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let rule = derived::ext::lam_in_dprod_n(
            &mut self.env_mut(),
            &p.ap,
            &p.fs,
            (px.body, px.graph, &px.beta, &px.lam_in_funspace),
            (fibre.b, fibre.dp.img, &fibre.dp.img_ax, fibre.dp.dprod, &fibre.dp.dprod_def),
        )?;
        let mut args = vec![v.clone()];
        args.extend(fibre.holes.clone());
        args.push(dom.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let out = Thm::mp(&inst, family)?;
        let want =
            Formula::mem(px.of(v.clone(), dom.clone()), self.dprod_term(fibre, dom));
        (*out.concl() == want).then_some(out)
    }

    // ───────────────────────────────────────────── the Prop Π clause ──

    /// The conditional-singleton machinery for one **`Prop`-valued `∀`** shape.
    ///
    /// §6.2's *other* column for `Π`: a `Prop`-valued `∀x : α. β` interprets to
    /// `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`, a conditional singleton, rather than to a
    /// dependent product. The two are different sets and nothing relates them,
    /// which is why the clause has to be decided and not guessed. The two
    /// deciders are [`Checker::pi_evidence`]'s `l2` numeral — which is
    /// **unwitnessed**, `INTERP-AUDIT.md` L1 — and [`Checker::lam_evidence`]'s
    /// `is_prop_ev`, which is not. `body_clause` does not reach this site.
    ///
    /// [`Checker::pi_evidence`]: crate::kernel::Checker
    /// [`Checker::lam_evidence`]: crate::kernel::Checker
    ///
    /// The fibre symbol is built exactly as [`Interp::fibre_site`] builds one —
    /// same skeleton, same holes-first order — but nothing else is: there is no
    /// image, no dependent product and no universe chain, because the whole
    /// thing lands in `U₀` by one lemma.
    pub fn cond_site(&mut self, body_ty_tm: &Term, w: FreeVar) -> Option<CondSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_ty_tm, w, &mut holes);
        let k = holes.len();
        if let Some(c) = self.conds.get(&skel) {
            return Some(CondSite { holes, ..c.clone() })
        }
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (b, b_ax) = derived::define_abbrev(&mut self.env_mut(), &xs, &skel)?;

        // `φ(h⃗, A) := ∀x. (x ∈ A → • ∈ b(h⃗, x))`, with the binder slot the
        // canonical one, so that one body shape gives one formula.
        let a_var = self.fresh_var();
        let mut bargs: Vec<Term> = xs[..k].iter().map(|v| Term::var(*v)).collect();
        bargs.push(Term::var(self.x_canon));
        let bx = self.mk(b, bargs);
        let point = self.prelude.point();
        let phi = Formula::forall(
            self.x_canon,
            Formula::imp(
                Formula::mem(Term::var(self.x_canon), Term::var(a_var)),
                Formula::mem(point, bx),
            ),
        );
        let mut params: Vec<FreeVar> = xs[..k].to_vec();
        params.push(a_var);

        let p = self.prelude.clone();
        let (chi, chi_ax) =
            derived::prop::conditional_singleton(&mut self.env_mut(), &p.tower.sums, &params, &phi)?;
        let site = CondSite { b, skel: skel.clone(), b_ax, chi, chi_ax, phi, params, holes: Vec::new(), k };
        self.conds.insert(skel, site.clone());
        self.cond_by_sym.insert(chi, site.clone());
        Some(CondSite { holes, ..site })
    }

    /// `b(q⃗, x)` for the `Prop` clause's fibre.
    pub fn cond_fibre_at(&mut self, site: &CondSite, x: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(x);
        self.mk(site.b, args)
    }

    /// This occurrence's `(⟦∀x:α.β⟧, φ, ⊢ ∀z. (z ∈ χ ↔ (z ∈ 1 ∧ φ)))`.
    ///
    /// The three things every `cond` lemma wants, computed once: the term, the
    /// formula at this occurrence's holes and domain, and the characteristic
    /// theorem instantiated there.
    pub fn cond_parts(&mut self, site: &CondSite, dom: Term) -> Option<(Term, Formula, Thm)> {
        let c = self.cond_term(site, dom.clone());
        let mut args = site.holes.clone();
        args.push(dom);
        let chi_at = derived::inst_all(&site.chi_ax, &args)?;
        let mut phi = site.phi.clone();
        for (v, t) in site.params.iter().zip(args.iter()) {
            phi = phi.subst(*v, t);
        }
        Some((c, phi, chi_at))
    }

    /// `⟦∀x:α. β⟧ = chi(h⃗, ⟦α⟧) = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`.
    pub fn cond_term(&mut self, site: &CondSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.chi, args)
    }

    // ────────────────────────────────────────── the application rules ──
    //
    // One per `Π` clause, because the three interpretations are three
    // different sets and nothing relates them. Each takes the two memberships
    // the checker already holds — `Γ ⊢ ⟦f⟧ ∈ ⟦Π x:A. B⟧` from `infer_type(f)`
    // transported along `whnf`, and `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧` from `infer_type(a)`
    // retargeted along the domain conversion — and composes. Nothing is looked
    // for: this is where nanoda's `ty_app`/`app_in_codomain`/`app_in_fibre`
    // reach for `has_type_a`, and mini has both premises in its hands.

    /// `Γ ⊢ app(f,a) ∈ ⟦B⟧` from `Γ ⊢ f ∈ fs(⟦A⟧,⟦B⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    pub fn fs_app(
        &mut self,
        dom: &Term,
        cod: &Term,
        f: &Term,
        a: &Term,
        f_mem: &Thm,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let rule = self.prelude.fs_app_mem.clone();
        let inst =
            derived::inst_all(&rule, &[dom.clone(), cod.clone(), f.clone(), a.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(f_mem, a_mem))?;
        let want = Formula::mem(self.app(f.clone(), a.clone()), cod.clone());
        (*out.concl() == want).then_some(out)
    }

    /// `Γ ⊢ app(f,a) ∈ b(q⃗,a)` from `Γ ⊢ f ∈ dprod(q⃗,⟦A⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    ///
    /// The dependent product's defining axiom says its members are exactly the
    /// sections, so the fibre membership is the right conjunct instantiated at
    /// `a`. No new derivation: `DProdN` proved it when the fibre symbol was
    /// introduced.
    pub fn dprod_app(
        &mut self,
        site: &FibreSite,
        dom: &Term,
        f: &Term,
        a: &Term,
        f_mem: &Thm,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let mut args = site.holes.clone();
        args.push(dom.clone());
        args.push(f.clone());
        let at = derived::inst_all(&site.dp.dprod_def, &args)?;
        let cond = Thm::mp(&derived::iff_mp(&at)?, f_mem)?;
        let section = derived::and_elim_right(&cond)?;
        let at_a = derived::inst_all(&section, std::slice::from_ref(a))?;
        let out = Thm::mp(&at_a, a_mem)?;
        let fibre = self.fibre_at(site, a.clone());
        let want = Formula::mem(self.app(f.clone(), a.clone()), fibre);
        if *out.concl() != want {
            return None
        }
        // …and off the fibre symbol onto `⟦B[a]⟧` itself, so the result type is
        // the term the caller's own interpretation would build.
        let (b_ax, holes) = (site.b_ax.clone(), site.holes.clone());
        let unfold = self.fibre_unfold(&b_ax, &holes, a)?;
        self.retarget_set(&out, &unfold)
    }

    /// `Γ ⊢ • ∈ b(h⃗,a)` from `Γ ⊢ • ∈ chi(h⃗,⟦A⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    ///
    /// The `Prop` clause's application rule. Both the function and the result
    /// are proofs, so both interpret to `•` and there is no graph to apply;
    /// what the certificate does is move from the conditional singleton's
    /// inhabitation to the fibre's, which is [`derived::prop::cond_elim`]
    /// followed by one instantiation.
    pub fn cond_app(
        &mut self,
        site: &CondSite,
        dom: &Term,
        f_mem: &Thm,
        a: &Term,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom.clone())?;
        // **`⟦f⟧` need not be `•` even though `f` is a proof.** §6.2 sends a
        // proof-valued *application* or *lambda* to `•`, but a proof that is a
        // `bvar` interprets to its scope variable — which is an element of the
        // conditional singleton and therefore *equal* to `•`, but not that
        // term. So the membership is first moved onto `•` by the same proof
        // irrelevance defeq uses; when it already is `•` the step is `• = •`
        // and costs nothing.
        let ty_mem = self.cond_typing(site, dom.clone())?;
        let f_pt = self.point_of_proof(&ty_mem, f_mem)?;
        let back = derived::eq_symm(&mut self.env_mut(), &f_pt)?;
        let f_mem = &self.retarget_subject(f_mem, &back)?;
        let p = self.prelude.clone();
        let elim = derived::prop::cond_elim(&p.tower.sums, &phi, &c, &chi_at)?;
        let all = Thm::mp(&elim, f_mem)?;
        let at_a = derived::inst_all(&all, std::slice::from_ref(a))?;
        let out = Thm::mp(&at_a, a_mem)?;
        let fibre = self.cond_fibre_at(site, a.clone());
        let want = Formula::mem(self.point(), fibre);
        if *out.concl() != want {
            return None
        }
        let (b_ax, holes) = (site.b_ax.clone(), site.holes.clone());
        let unfold = self.fibre_unfold(&b_ax, &holes, a)?;
        self.retarget_set(&out, &unfold)
    }

    /// `Γ ⊢ • ∈ chi(h⃗,⟦A⟧)` from `⊢ ∀x. (x ∈ ⟦A⟧ → • ∈ b(h⃗,x))` — the `λ`
    /// typing rule on the `Prop` branch.
    pub fn cond_lam_typing(&mut self, site: &CondSite, dom: Term, family: &Thm) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom)?;
        let p = self.prelude.clone();
        let intro = derived::prop::cond_intro(&p.tower.sums, &phi, &c, &chi_at)?;
        let out = Thm::mp(&intro, family)?;
        (*out.concl() == Formula::mem(self.point(), c)).then_some(out)
    }

    // ─────────────────────────────────────────── the binder congruences ──
    //
    // Two binders whose bodies have *different shapes* have different, unrelated
    // head symbols, so congruence over subterms relates nothing: the equation
    // has to come from Extensionality. That is what `lam_ext_n`, `dprod_ext_n`
    // and `cond_ext_n` are, and all three take the same two premises — the
    // domain equation, and a *pointwise* family over the left domain, which is
    // exactly what `Closed::discharge` produces.

    /// `⊢ b(h⃗,x) = ⟦B⟧` at a point — one site's defining equation, for moving
    /// a body conversion onto the symbols the congruence lemmas speak of.
    pub fn symbol_at(&mut self, sym: FnSym, ax: &Thm, holes: &[Term], x: &Term) -> Option<Thm> {
        let mut args = holes.to_vec();
        args.push(x.clone());
        let _ = self.mk(sym, args.clone());
        derived::inst_all(ax, &args)
    }

    /// The instantiation list every `_ext_n` wants: `p⃗, q⃗, A, A'`.
    fn ext_args(h1: &[Term], h2: &[Term], a: &Term, b: &Term) -> Vec<Term> {
        let mut v = h1.to_vec();
        v.extend_from_slice(h2);
        v.push(a.clone());
        v.push(b.clone());
        v
    }

    fn finish_cong(
        rule: &Thm,
        args: &[Term],
        dom_eq: &Thm,
        pointwise: &Thm,
        want: Formula,
    ) -> Option<Thm> {
        let inst = derived::inst_all(rule, args)?;
        let out = Thm::mp(&Thm::mp(&inst, dom_eq)?, pointwise)?;
        (*out.concl() == want).then_some(out)
    }

    /// `Γ ⊢ lam(p⃗,⟦A⟧) = lam'(q⃗,⟦A'⟧)` — `λ` congruence at two shapes.
    pub fn lam_cong(
        &mut self,
        s1: &LamSite,
        s2: &LamSite,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pointwise: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let rule = derived::ext::lam_ext_n(
            &mut self.env_mut(),
            &p.ap,
            s1.t,
            s1.lam,
            &s1.lam_ax,
            s2.t,
            s2.lam,
            &s2.lam_ax,
        )?;
        let args = Self::ext_args(&s1.holes, &s2.holes, d1, d2);
        let want =
            Formula::eq(self.lam_term(s1, d1.clone()), self.lam_term(s2, d2.clone()));
        Self::finish_cong(&rule, &args, dom_eq, pointwise, want)
    }

    /// `Γ ⊢ dprod(p⃗,⟦A⟧) = dprod'(q⃗,⟦A'⟧)` — dependent-`Π` congruence.
    pub fn dprod_cong(
        &mut self,
        s1: &FibreSite,
        s2: &FibreSite,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pointwise: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let (a, b) = (s1.dp.clone(), s2.dp.clone());
        let rule = derived::ext::dprod_ext_n(
            &mut self.env_mut(),
            &p.ap,
            &p.fs,
            (a.b, a.img, &a.img_ax, a.dprod, &a.dprod_def),
            (b.b, b.img, &b.img_ax, b.dprod, &b.dprod_def),
        )?;
        let args = Self::ext_args(&s1.holes, &s2.holes, d1, d2);
        let want =
            Formula::eq(self.dprod_term(s1, d1.clone()), self.dprod_term(s2, d2.clone()));
        Self::finish_cong(&rule, &args, dom_eq, pointwise, want)
    }

    /// `Γ ⊢ chi(p⃗,⟦A⟧) = chi'(q⃗,⟦A'⟧)` — `∀`-congruence, §6.2's other clause.
    pub fn cond_cong(
        &mut self,
        s1: &CondSite,
        s2: &CondSite,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pointwise: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let rule = derived::prop::cond_ext_n(
            &mut self.env_mut(),
            &p.tower.sums,
            (s1.b, s1.chi, &s1.chi_ax),
            (s2.b, s2.chi, &s2.chi_ax),
        )?;
        let args = Self::ext_args(&s1.holes, &s2.holes, d1, d2);
        let want =
            Formula::eq(self.cond_term(s1, d1.clone()), self.cond_term(s2, d2.clone()));
        Self::finish_cong(&rule, &args, dom_eq, pointwise, want)
    }
    // *(`dprod_fs_bridge` stood here until the `fs`-clause removal, and it was
    // `MINI-HANDOFF.md` §5's whole subject: 937 of 988 gapped conversions were
    // one type classified as a dependent product on one side and a function
    // space on the other, both correctly, because `dep = has_bvar(body, 0)` is
    // syntactic and β-unstable. The repair was a bridge over
    // `derived::ext::dprod_const_fibre_n` rather than a reclassification, and
    // that call was right for as long as there were two clauses. With one there
    // are no two *interpretation* spellings, so the **conversion** bridge has no
    // input and was deleted rather than left unreachable.
    //
    // The paragraph that stood here went on to say the theorem "is now unread".
    // That was true for one round. It is not a conversion that reads it but a
    // **library obligation stated over `fs`**: `derived` keeps `fs` deliberately
    // (`crate::quot_classes`'s header), so every theorem stated at a function
    // space meets an interpreted `Π` that is a `dprod`, and the bridge is what
    // stands between them. [`Interp::dprod_is_fs`] below is that move, made
    // once; `Quot.lift` reads it twice and a function-typed recursive field
    // once.)*

    /// **`Γ ⊢ dprod(q⃗, A) = fs(A, B)`** — the interpreted arrow spelled as the
    /// library's function space, at a *constant* fibre.
    ///
    /// `⟦Π x:A. B⟧` is a `dprod` at every codomain (`MINI-HANDOFF.md` §12), so
    /// nothing mini builds is ever an `fs`. `derived` nevertheless states real
    /// obligations over `fs` — `Ctor::mem`'s function-typed recursive atom,
    /// `lift_in_funspace`, `cod_at_funspace`'s hypothesis — and this is the one
    /// place the two vocabularies meet. Keeping it here rather than at the call
    /// sites is `MINI-HANDOFF.md` §29 item 3's instruction, written when there
    /// was one consumer and stated for when there were two.
    ///
    /// `B` is **read off the fibre**, not taken from the caller: the returned
    /// term is the right-hand side of `b(q⃗,x) = ⟦B⟧` at a fresh `x`, which is
    /// what makes the hypothesis `∀x. (x ∈ A → b(q⃗,x) = B)` free — it is the
    /// fibre symbol's own defining axiom weakened by `a1i` and generalised. A
    /// caller that wants the codomain spelled some other way moves it
    /// afterwards, along its own equation.
    ///
    /// **The fibre must really be constant, and that is measured rather than
    /// assumed.** A dependent fibre's `⟦B⟧` mentions `x`, and instantiating the
    /// rule's `∀B` at such a term would put a free occurrence under the `∀x`
    /// the hypothesis binds. So the skeleton is rebuilt at a *second* fresh
    /// variable and the two right-hand sides are compared: equal iff the body
    /// mentions no binder. `None` otherwise, and the caller reports its own gap.
    pub fn dprod_is_fs(&mut self, site: &FibreSite, dom: &Term) -> Option<(Term, Thm)> {
        let p = self.prelude.clone();
        let rule = match self.dprod_fs.get(&site.b) {
            Some(t) => t.clone(),
            None => {
                let t = derived::ext::dprod_const_fibre_n(
                    &mut self.env_mut(),
                    &p.ap,
                    &p.fs,
                    site.b,
                    site.dp.img,
                    &site.dp.img_ax,
                    site.dp.dprod,
                    &site.dp.dprod_def,
                    &p.fs_app_mem,
                    &p.fs_retarget,
                )?;
                self.dprod_fs.insert(site.b, t.clone());
                t
            }
        };
        // The fibre at a point, and the proof that the point does not matter.
        // Two statements, not a tuple: each `env_mut()` borrow must end
        // before the next begins.
        let xv = self.fresh_var();
        let yv = self.fresh_var();
        let at_x = self.symbol_at(site.b, &site.b_ax, &site.holes, &Term::var(xv))?;
        let at_y = self.symbol_at(site.b, &site.b_ax, &site.holes, &Term::var(yv))?;
        let cod = at_x.concl().as_eq()?.1.clone();
        if cod != at_y.concl().as_eq()?.1 || cod.occurs_free(xv) {
            return None
        }
        let mut args = site.holes.clone();
        args.push(dom.clone());
        args.push(cod.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let family = crate::rec_dep::gen_all_checked(
            &[xv],
            &derived::a1i(&at_x, Formula::mem(Term::var(xv), dom.clone())),
        )?;
        let out = Thm::mp(&inst, &family)?;
        let want =
            Formula::eq(self.dprod_term(site, dom.clone()), self.fs(dom.clone(), cod.clone()));
        (*out.concl() == want).then_some((cod, out))
    }

    /// From `Γ ⊢ x ∈ A` and `⊢ y = x` infer `Γ ⊢ y ∈ A` — [`Interp::retarget_set`]
    /// on the membership's **left** side.
    ///
    /// The declaration pipeline's last step: a definition's constant is an
    /// abbreviation for its value's interpretation, and its typing is the
    /// value's typing carried back along that defining equation.
    pub fn retarget_subject(&mut self, mem: &Thm, eq: &Thm) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let (lhs, rhs) = eq.concl().as_eq()?;
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        if rhs != subj {
            return None
        }
        let x = self.fresh_var();
        let leib =
            Thm::eq_leibniz(rhs, lhs.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let back = derived::eq_symm(&mut self.env_mut(), eq)?;
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(lhs, set)).then_some(out)
    }

    /// `⊢ ⟦∀x:α. β⟧ ∈ ⟦Prop⟧` — the whole typing obligation of the `Prop` `Π`
    /// clause, and it is *unconditional*: every conditional singleton is a
    /// subset of `1`, hence a truth value, hence in `U₀`, whatever the fibre
    /// does. Nothing about `⟦β⟧` is needed, so nothing is assumed about it.
    ///
    /// This is where the two `Π` clauses differ most sharply. The dependent
    /// product needs its domain *and* its fibres placed in a universe first
    /// ([`Interp::dprod_typing`]); this needs neither.
    pub fn cond_typing(&mut self, site: &CondSite, dom: Term) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom)?;
        let p = self.prelude.clone();
        let out = p.tower.cond_in_u0(&mut self.env_mut(), &phi, &c, &chi_at)?;
        (*out.concl() == Formula::mem(c, self.sort(0))).then_some(out)
    }

    // ───────────────────────────────────────────────────────── symbols ──

    /// A 0-ary abbreviation: a fresh symbol `c` with `⊢ c = body`.
    ///
    /// A conservative definitional extension. This is how a transparent Lean
    /// definition gets a name of its own, and the returned theorem *is* delta
    /// reduction's certificate for it.
    pub fn abbrev(&mut self, body: &Term) -> Option<(Term, Thm)> {
        let (sym, ax) = derived::define_abbrev(&mut self.env_mut(), &[], body)?;
        let t = self.mk(sym, vec![]);
        // The axiom is checked against the statement claimed rather than
        // trusted: a mismatch is a gap, never a described-but-false theorem.
        (*ax.concl() == Formula::eq(t.clone(), body.clone())).then_some((t, ax))
    }

    /// A fresh opaque constant — a pure *signature* extension, with no
    /// defining axiom.
    ///
    /// This is what an axiom, and any constant mini cannot yet interpret, gets.
    /// Extending the signature is conservative on its own; what is *not*
    /// derivable is that the new symbol denotes an inhabitant of anything,
    /// which is why the store's `typing` is a [`Gap`] on this path.
    pub fn opaque(&mut self) -> Term {
        let sym = self.env_mut().declare(0);
        self.mk(sym, vec![])
    }

    // ─────────────────────────────────────────────────── the const store ──

    pub fn get_const(&self, key: &ConstKey) -> Option<&ConstInterp> { self.consts.get(key) }

    pub fn put_const(&mut self, key: ConstKey, c: ConstInterp) {
        if crate::blocker::is_armed() || self.labels_on {
            let (name, sigma) = &key;
            let s: Vec<String> = sigma.iter().map(crate::ground::show_level).collect();
            let t = c.term.clone();
            self.set_label(&t, format!("⟦{name}.{{{}}}⟧", s.join(",")));
        }
        self.consts.insert(key, c);
    }

    pub fn const_count(&self) -> usize { self.consts.len() }

    /// Every key in the constant store, **unsorted**.
    ///
    /// The order is a `HashMap`'s and therefore differs between two runs of the
    /// same file; every caller must sort. `crate::dump` does, and its
    /// determinism test is what holds that.
    pub fn const_keys(&self) -> Vec<ConstKey> { self.consts.keys().cloned().collect() }

    // ───────────────────────────────────────────── read-only, for the dump ──

    /// **Fill the label registry even unarmed.** [`Interp::labels`] is written
    /// only under [`crate::blocker::is_armed`], and arming also stops the run
    /// at the first blocker — so a `--dump-theorems` pass that armed to get
    /// names would dump one pair. This is the same switch without the stop.
    pub fn set_labels_on(&mut self, on: bool) { self.labels_on = on; }

    /// The apparatus **if it was built**, without building it.
    ///
    /// [`Interp::ind_apparatus`] constructs on demand, so a dump that used it
    /// would report an apparatus that exists only because the dump asked —
    /// turning "nothing reached zone B" into a page of theorems. Observation
    /// must not create what it observes.
    pub fn ind_opt(&self) -> Option<&IndApparatus> { self.ind.as_deref() }

    /// How many per-shape binder symbols carry a defining axiom. Summarised in
    /// the dump rather than listed; see `crate::dump`'s header.
    pub fn site_count(&self) -> usize { self.lams.len() + self.fibres.len() + self.conds.len() }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tower's two typing cases, both pinned against the statement they
    /// are supposed to make. The `n = 0` case is the one a "just use `mem_u`"
    /// implementation gets wrong, because `⟦Sort 1⟧` is `U(ω)` and not
    /// `U(⟦Sort 0⟧)`.
    #[test]
    fn sort_typings_conclude_what_they_claim() {
        let ip = Interp::new();
        for n in 0..4u32 {
            let t = ip.sort_typing(n).unwrap_or_else(|| panic!("no typing for Sort {n}"));
            assert!(t.hyps().is_empty());
            assert_eq!(
                *t.concl(),
                Formula::mem(ip.sort(n), ip.sort(n + 1)),
                "Sort {n}'s typing does not conclude ⟦Sort {n}⟧ ∈ ⟦Sort {}⟧",
                n + 1
            );
        }
        // ⟦Prop⟧ and ⟦Type 0⟧ are distinct, or the tower has collapsed.
        assert_ne!(ip.sort(0), ip.sort(1));
    }

    /// An abbreviation is a definitional extension whose axiom is *the*
    /// equation delta reduction needs.
    #[test]
    fn abbrev_gives_back_its_defining_equation() {
        let mut ip = Interp::new();
        let body = ip.sort(0);
        let (c, ax) = ip.abbrev(&body).expect("abbrev");
        assert!(ax.hyps().is_empty());
        assert_eq!(*ax.concl(), Formula::eq(c.clone(), body.clone()));
        // Distinct calls mint distinct symbols: identity is the store's job,
        // not `abbrev`'s.
        let (c2, _) = ip.abbrev(&body).expect("abbrev");
        assert_ne!(c, c2);
    }

    /// The skeleton decomposition is what makes a lambda body abstractable.
    /// Both halves are pinned: an application decomposes, and the maximal
    /// binder-free subterm comes back as a hole.
    #[test]
    fn skeleton_abstracts_the_binder_and_holes_the_rest() {
        let mut ip = Interp::new();
        let v = ip.fresh_var();
        let closed = ip.sort(0);
        // `app(v, ⟦Prop⟧)` — mentions the binder, so it must be recorded.
        let t = ip.app(Term::var(v), closed.clone());
        let mut holes = Vec::new();
        let sk = ip.skeleton(&t, v, &mut holes);
        assert_eq!(holes, vec![closed], "the binder-free subterm is the one hole");
        let expect = {
            let x = ip.x_canon();
            let h = ip.hole_var(0);
            ip.app(Term::var(x), Term::var(h))
        };
        assert_eq!(sk, expect, "the skeleton is the term with the binder and hole canonicalised");

        // Two occurrences of one body shape must decompose to the *same*
        // skeleton, or their defeq needs a theorem where reflexivity should do.
        let v2 = ip.fresh_var();
        let other = ip.sort(3);
        let t2 = ip.app(Term::var(v2), other.clone());
        let mut holes2 = Vec::new();
        let sk2 = ip.skeleton(&t2, v2, &mut holes2);
        assert_eq!(sk, sk2, "one body shape, one skeleton");
        assert_eq!(holes2, vec![other]);
    }

    /// **A term the interpretation did not build decomposes exactly like one
    /// it did.** Seen red first: on the design this replaces, `skeleton`
    /// answered `None` here.
    ///
    /// This is the regression for the whole change, and it is the mutation
    /// that catches an unsound prune. The old `parts` table was written to by
    /// `Interp::mk` and read by the decomposition, and *recordedness* was
    /// therefore standing in for *decomposability* — a proxy that is wrong in
    /// one direction and expensive in the other. Wrong, because the kernel
    /// builds terms too: a substitution instance, or either endpoint of a
    /// `derived::congr`, never passed through `mk` and read back as an opaque
    /// atom. Expensive, because keeping the proxy true meant remembering every
    /// term ever built, forever — 54 % of an `init-prelude` run's live heap
    /// (`PRELUDE-COST.md` §3.2).
    ///
    /// Both halves are what this test pins. Restore the table and any prune of
    /// it — clearing it per declaration, bounding it, evicting from it — turns
    /// this term back into an atom and the assertion below goes red, which is
    /// precisely the 213 gaps `MINI_PARTS_RESET=1` measured. Reading the
    /// structure off the term is the version with nothing to prune.
    #[test]
    fn skeleton_decomposes_a_term_the_interpretation_did_not_build() {
        let mut ip = Interp::new();
        let v = ip.fresh_var();
        let closed = ip.sort(0);
        let f = ip.env_mut().declare(2);
        // Built with `Term::apply`, behind mini's back — as `derived::congr`
        // and every kernel-side instantiation build their terms.
        let unbuilt = Term::apply(f, vec![Term::var(v), closed.clone()]);
        let mut holes = Vec::new();
        let sk = ip.skeleton(&unbuilt, v, &mut holes);
        assert_eq!(holes, vec![closed], "the binder-free subterm is still the one hole");
        let expect = {
            let x = ip.x_canon();
            let h = ip.hole_var(0);
            Term::apply(f, vec![Term::var(x), Term::var(h)])
        };
        assert_eq!(sk, expect, "and the skeleton is the same one a recorded term would give");
    }

    /// **The library's function-space typing**, end to end and at every level
    /// pair the corpus can present, including the ones needing a cumulativity
    /// lift on one side, on the other, or on neither.
    ///
    /// *(Re-headed at the `fs`-clause removal; it read "Lean's non-dependent
    /// `Π` rule", which it was until `⟦Π⟧` stopped having one. The theorem is
    /// unchanged and still true — what moved is that nothing interprets a `Π`
    /// with it. See [`Interp::fs`] for why the three wrappers are kept.)*
    ///
    /// `⟦Sort l⟧ ∈ ⟦Sort (l+1)⟧` is the premise to hand, so this checks
    /// `fs(⟦Sort l1⟧, ⟦Sort l2⟧) ∈ ⟦Sort (max (l1+1) (l2+1))⟧` — that is, the
    /// function space of two sorts lands where `imax` says it does.
    #[test]
    fn the_function_space_lands_in_the_max_universe() {
        let mut ip = Interp::new();
        for l1 in 0..4u32 {
            for l2 in 0..4u32 {
                let (a, b) = (ip.sort(l1), ip.sort(l2));
                let (ma, mb) = (ip.sort_typing(l1).unwrap(), ip.sort_typing(l2).unwrap());
                // `⟦A⟧ ∈ ⟦Sort (l1+1)⟧` and `⟦B⟧ ∈ ⟦Sort (l2+1)⟧`; the `Π` sits
                // in `Sort (imax (l1+1) (l2+1))`, and `l2+1 > 0` always, so the
                // `imax` is a `max`.
                let n = (l1 + 1).max(l2 + 1);
                let out = ip
                    .fs_typing(&ma, &mb, l1 + 1, l2 + 1)
                    .unwrap_or_else(|| panic!("no Π typing at ({l1},{l2})"));
                assert!(out.hyps().is_empty(), "the Π rule must be unconditional");
                let want = Formula::mem(ip.fs(a, b), ip.sort(n));
                assert_eq!(*out.concl(), want, "wrong universe at ({l1},{l2})");
            }
        }
    }

    /// **The function-space rule under a binder**: the domain's typing comes
    /// from an enclosing scope and carries that scope's hypothesis. The result must carry it too — and must not be
    /// labelled unconditional, which is what `Cumul::raise`'s `hyps()` guard
    /// exists to prevent and what `Interp::raise_in_gamma` handles instead.
    ///
    /// `Π (_ : α). Prop` for a bound `α : Type 0`.
    #[test]
    fn the_function_space_rule_carries_gamma_from_an_enclosing_scope() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let u1 = ip.sort(1);
        let tok = sc.open(&mut ip.env_mut(), u1.clone());
        // `Γ ⊢ α ∈ ⟦Type 0⟧` — the scope's own assumption, at zero cost.
        let dom_mem = sc.get(0).unwrap().assumption().clone();
        let alpha = sc.get(0).unwrap().term();
        assert_eq!(dom_mem.hyps().len(), 1);
        // `⊢ ⟦Prop⟧ ∈ ⟦Type 0⟧`, hypothesis-free.
        let cod_mem = ip.sort_typing(0).unwrap();

        let out = ip.fs_typing(&dom_mem, &cod_mem, 1, 1).expect("Π typing under a binder");
        assert_eq!(out.hyps(), dom_mem.hyps(), "Γ must be carried, not dropped");
        let want = Formula::mem(ip.fs(alpha, ip.sort(0)), ip.sort(1));
        assert_eq!(*out.concl(), want);
        // And it is not silently unconditional: sealing it must fail.
        assert!(crate::ev::Sealed::new(out).is_err());
        let _ = sc.close(tok);
    }

    /// The `Prop` codomain is a different clause — a conditional singleton, not
    /// a function space — and this rule must refuse it rather than produce a
    /// theorem about the wrong set. Likewise a level past the table.
    #[test]
    fn the_pi_rule_refuses_what_is_not_its_clause() {
        let mut ip = Interp::new();
        let m = ip.sort_typing(1).unwrap();
        assert!(ip.fs_typing(&m, &m, 1, 0).is_none(), "l2 = 0 is the Prop clause");
        assert!(
            ip.fs_typing(&m, &m, 1, CUMUL_HEIGHT as u32 + 1).is_none(),
            "a level past the cumulativity table must gap, not guess"
        );
        // A membership in something that is not this tower's `U_m` is refused
        // by `Cumul::raise` rather than lifted into nonsense.
        let bogus = kernel::Thm::eq_refl(ip.sort(1));
        assert!(ip.fs_typing(&bogus, &m, 1, 2).is_none());
    }

    /// **`⟦λ (x : Prop). x⟧ ∈ ⟦Prop → Prop⟧`, end to end**, through exactly the
    /// pipeline the checker will use: interpret the domain, open a scope,
    /// interpret the body, decompose it into a skeleton, define the body
    /// symbol, build the graph, rewrite the body's membership along the body
    /// symbol's own defining equation, discharge the scope, and feed the
    /// resulting `∀`-`→` family to the typing rule.
    ///
    /// Nothing is searched for at any step, and the family `discharge`
    /// produces is fed to the lemma unchanged — the two shapes were chosen to
    /// be the same one.
    #[test]
    fn the_identity_lambda_lands_in_the_function_space() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);

        let tok = sc.open(&mut ip.env_mut(), dom.clone());
        let w = sc.get(0).unwrap().var();
        // The body is `bvar 0`, so ⟦b⟧ is the scope's own variable and its
        // typing is the scope's stored assumption — no derivation at all.
        let body_tm = Term::var(w);
        let body_mem = sc.get(0).unwrap().assumption().clone();

        let site = ip.lam_site(&body_tm, w).expect("lam site");
        assert_eq!(site.k, 0, "the identity body has no holes");
        let as_sym = ip.to_body_symbol(&site, w, &body_mem).expect("rewrite");
        assert_eq!(as_sym.hyps().len(), 1, "the rewrite must keep Γ, not drop it");

        let closed = crate::scope::test_support::close_single_stack(&mut sc, tok, &as_sym);
        let family = closed.discharge(&as_sym).expect("discharge");
        assert!(family.hyps().is_empty());

        let out = ip.lam_typing_fs(&site, dom.clone(), dom.clone(), &family).expect("λ typing");
        assert!(out.hyps().is_empty(), "the λ rule must be unconditional");
        let want = Formula::mem(ip.lam_term(&site, dom.clone()), ip.fs(dom.clone(), dom));
        assert_eq!(*out.concl(), want);
    }

    /// A body with a **hole**: `λ (x : Prop). app(c, x)` for a closed `c`. The
    /// prefix is what the whole `_n` lemma family exists for, and it must be
    /// threaded in the right order — holes first, domain last.
    #[test]
    fn a_lambda_with_a_prefix_threads_its_holes() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c, _) = ip.abbrev(&ip.sort(1)).expect("abbrev");

        let tok = sc.open(&mut ip.env_mut(), dom.clone());
        let w = sc.get(0).unwrap().var();
        let body_tm = ip.app(c.clone(), Term::var(w));
        let site = ip.lam_site(&body_tm, w).expect("lam site");
        assert_eq!(site.k, 1, "`c` is the one hole");
        assert_eq!(site.holes, vec![c], "and it is the abstracted subterm");
        // The graph term carries the prefix, then the domain.
        let lam = ip.lam_term(&site, dom.clone());
        assert_eq!(lam, {
            let mut a = site.holes.clone();
            a.push(dom);
            ip.mk(site.lam, a)
        });
        let _ = sc.close(tok);
    }

    /// **One body shape, one graph symbol.** Two lambdas whose bodies differ
    /// only in the binder-free parts must share the symbol, or their
    /// definitional equality would need a theorem where reflexivity does.
    #[test]
    fn two_occurrences_of_one_shape_share_the_graph() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c1, _) = ip.abbrev(&ip.sort(1)).unwrap();
        let (c2, _) = ip.abbrev(&ip.sort(2)).unwrap();

        let t1 = sc.open(&mut ip.env_mut(), dom.clone());
        let w1 = sc.get(0).unwrap().var();
        let b1 = ip.app(c1.clone(), Term::var(w1));
        let s1 = ip.lam_site(&b1, w1).unwrap();
        let _ = sc.close(t1);

        let t2 = sc.open(&mut ip.env_mut(), dom);
        let w2 = sc.get(0).unwrap().var();
        let b2 = ip.app(c2.clone(), Term::var(w2));
        let s2 = ip.lam_site(&b2, w2).unwrap();
        let _ = sc.close(t2);

        assert_eq!(s1.lam, s2.lam, "one shape must give one graph symbol");
        assert_eq!(s1.t, s2.t);
        assert_eq!(s1.holes, vec![c1]);
        assert_eq!(s2.holes, vec![c2], "the holes differ; the shape does not");
    }

    /// **`⟦Π (x : Type 0). x⟧ ∈ ⟦Type 1⟧`, end to end.** A genuinely dependent
    /// `Π`: the fibre is the binder itself, so the function space cannot say
    /// it and the dependent product must.
    ///
    /// Pipeline: interpret the domain, open a scope, interpret the body type,
    /// decompose it into a fibre skeleton, define `b(h⃗,x)`, build `DProdN` and
    /// the Π rule over it, rewrite the body type's membership along `b`'s
    /// defining equation, discharge, and apply.
    #[test]
    fn a_dependent_pi_lands_in_the_universe() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        // `Π (x : Type 0). x` — domain `⟦Type 0⟧ = U₁`, body `x : Type 0`.
        let dom = ip.sort(1);
        let dom_mem = ip.sort_typing(1).unwrap(); // ⊢ U₁ ∈ U₂

        let tok = sc.open(&mut ip.env_mut(), dom.clone());
        let w = sc.get(0).unwrap().var();
        let body_ty = Term::var(w);
        // `Γ ⊢ x ∈ U₁`, the scope's own assumption; raise it to `U₂`, which is
        // where the `Π` lives (`imax 2 2 = 2`).
        let body_mem = sc.get(0).unwrap().assumption().clone();
        let body_mem = ip.raise_in_gamma(1, 2, &body_mem).expect("lift the fibre");

        let site = ip.fibre_site(&body_ty, w).expect("fibre site");
        assert_eq!(site.k, 0, "the fibre is the binder itself — no holes");
        let as_sym = ip.to_fibre_symbol(&site, w, &body_mem).expect("rewrite");
        let closed = crate::scope::test_support::close_single_stack(&mut sc, tok, &as_sym);
        let fibres = closed.discharge(&as_sym).expect("discharge");
        assert!(fibres.hyps().is_empty());

        let out = ip.dprod_typing(&site, dom.clone(), &dom_mem, &fibres, 2).expect("Π typing");
        assert!(out.hyps().is_empty());
        let want = Formula::mem(ip.dprod_term(&site, dom), ip.sort(2));
        assert_eq!(*out.concl(), want);
    }

    /// **`⟦λ (x : Prop). x⟧ ∈ ⟦Π (x : Prop). Prop⟧`** — the λ rule at a
    /// *dependent* codomain, which is the half of `lam` that `pi-dep`
    /// unblocks. Both the graph and the dependent product are built here and
    /// the membership relates them.
    ///
    /// The fibre is constant in this example, but the code path is not: the
    /// fibre's skeleton has no occurrence of the binder, so `⟦Prop⟧` becomes a
    /// **hole** and `b` has arity 2, which is exactly the prefix threading the
    /// `_n` family exists for. The first attempt at this test used a fibre that
    /// *was* the binder — `Π (x : Type 0). x` — which is not inhabited by the
    /// identity: it would need `x : x`, which Regularity refutes. The rule
    /// refused it, correctly.
    #[test]
    fn the_identity_lambda_lands_in_the_dependent_product() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);

        let tok = sc.open(&mut ip.env_mut(), dom.clone());
        let w = sc.get(0).unwrap().var();
        let lam = ip.lam_site(&Term::var(w), w).expect("lam site");
        let fib = ip.fibre_site(&dom.clone(), w).expect("fibre site");
        assert_eq!(fib.k, 1, "the binder-free fibre becomes one hole");
        assert_eq!(fib.holes, vec![dom.clone()]);

        // `Γ ⊢ w ∈ ⟦Prop⟧`, the scope's own assumption, rewritten to
        // `Γ ⊢ t(w) ∈ b(⟦Prop⟧, w)` — subject side then set side.
        let mem = sc.get(0).unwrap().assumption().clone();
        let mem = ip.to_body_symbol(&lam, w, &mem).expect("to t");
        let b_at = derived::inst_all(&fib.b_ax, &[dom.clone(), Term::var(w)]).expect("b at w");
        let back = derived::eq_symm(&mut ip.env_mut(), &b_at).expect("symm");
        let mem = ip.retarget_set(&mem, &back).expect("retarget to the fibre");

        let closed = crate::scope::test_support::close_single_stack(&mut sc, tok, &mem);
        let family = closed.discharge(&mem).expect("discharge");
        let out = ip.lam_typing_dprod(&lam, &fib, dom.clone(), &family).expect("λ in dprod");
        assert!(out.hyps().is_empty());
        let want = Formula::mem(ip.lam_term(&lam, dom.clone()), ip.dprod_term(&fib, dom));
        assert_eq!(*out.concl(), want);
    }

    /// **§6.2 has one value clause, and these are the three things that says.**
    ///
    /// *(Replaces `the_two_pi_clauses_bridge_in_both_orientations`, at the
    /// `fs`-clause removal; the prior revision is at `d17adf8`. That test
    /// pinned both orientations of `Interp::dprod_fs_bridge` — the repair for
    /// `MINI-HANDOFF.md` §5's 937-conversion row — and its own header argued
    /// the mirror arm deserved a unit test because a corpus pin on a zero row
    /// would go on passing if it broke. **That argument held and the row it
    /// guarded is gone**: with one clause there are no two spellings of one
    /// type, so the bridge has no input. What replaces it is the invariant that
    /// makes it unnecessary.)*
    ///
    /// Each assertion owns one input:
    ///
    /// * a **binder-free** codomain still interprets to `dprod`, at a fibre
    ///   whose skeleton is hole 0 entire — so one `fibres` entry serves every
    ///   non-dependent arrow in the corpus and `const_dprod` mints nothing;
    /// * `fs(A,B)` is **not** an interpreted `Π`. `as_pi` answers `None`, which
    ///   is why `PiShape::Fs` was deleted rather than left unreachable: a stray
    ///   library function space must not decompose as a binder shape;
    /// * a constant fibre and a genuine dependent one are **different sites**,
    ///   which is what `fibre_by_sym` tells apart and the property
    ///   `QUOT-MODEL.md` §2.1 rests on.
    #[test]
    fn there_is_one_value_pi_clause_and_a_stray_fs_is_not_one() {
        let mut ip = Interp::new();
        let (a, b) = (ip.sort(0), ip.sort(1));

        // A binder-free codomain: hole 0 entire, and `const_dprod` is the term.
        let w = ip.fresh_var();
        let konst = ip.fibre_site(&b, w).expect("the constant fibre");
        assert_eq!(konst.holes, vec![b.clone()], "a binder-free codomain is hole 0 entire");
        let dp = ip.const_dprod(a.clone(), b.clone()).expect("dprod at the constant fibre");
        assert_eq!(dp, ip.dprod_term(&konst, a.clone()));
        // …and asking again mints nothing: the same site, at any binder.
        let w2 = ip.fresh_var();
        let again = ip.fibre_site(&b, w2).expect("the same constant fibre");
        assert_eq!(again.dp.dprod, konst.dp.dprod, "one table entry, corpus-wide");

        // It decomposes, and the domain is in an argument slot.
        match ip.as_pi(&dp) {
            Some(PiShape::Dep { dom, site }) => {
                assert_eq!(dom, a, "the domain is an argument slot of a shared symbol");
                assert_eq!(site.dp.dprod, konst.dp.dprod);
            }
            other => panic!("a constant-fibre Π must decompose as Dep, got {:?}", other.is_some()),
        }

        // A library function space is not a binder shape.
        let stray = ip.fs(a.clone(), b.clone());
        assert!(ip.as_pi(&stray).is_none(), "a stray fs must not decompose as an interpreted Π");

        // A genuinely dependent fibre is a different site.
        let w3 = ip.fresh_var();
        let dep_cod = ip.mk(ip.prelude.fs_sym(), vec![Term::var(w3), b.clone()]);
        let dep = ip.fibre_site(&dep_cod, w3).expect("a dependent fibre");
        assert_ne!(dep.dp.dprod, konst.dp.dprod, "fibre_by_sym must tell the two apart");
    }

    /// **`⟦∀ (x : Prop). x⟧ ∈ ⟦Prop⟧`** — the `Prop` `Π` clause, end to end.
    ///
    /// The fibre here genuinely *is* the binder, so this is the dependent
    /// shape that `a_dependent_pi_lands_in_the_universe` could not use on the
    /// `Type` side (there it would have needed `x : x`). On the `Prop` side it
    /// is fine and is the honest test: the conditional singleton lands in `U₀`
    /// **whatever the fibre does**, so nothing about `⟦β⟧` is assumed.
    #[test]
    fn a_prop_valued_forall_lands_in_prop() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let tok = sc.open(&mut ip.env_mut(), dom.clone());
        let w = sc.get(0).unwrap().var();

        let site = ip.cond_site(&Term::var(w), w).expect("cond site");
        assert_eq!(site.k, 0, "the fibre is the binder itself — no holes");
        let out = ip.cond_typing(&site, dom.clone()).expect("Prop Π typing");
        assert!(out.hyps().is_empty(), "the Prop Π rule is unconditional");
        assert_eq!(*out.concl(), Formula::mem(ip.cond_term(&site, dom.clone()), ip.sort(0)));

        // **The two Π clauses are different sets.** A conditional singleton is
        // not a dependent product, which is why the clause has to be decided
        // rather than guessed.
        let fib = ip.fibre_site(&Term::var(w), w).expect("fibre site");
        assert_ne!(ip.cond_term(&site, dom.clone()), ip.dprod_term(&fib, dom));
        let _ = sc.close(tok);
    }

    /// The `Prop` clause with a **prefix**: `∀ (x : Prop). c`, whose fibre is
    /// binder-free and so becomes a hole. Same shape-keying discipline as the
    /// other two sites.
    #[test]
    fn the_prop_clause_threads_a_prefix_and_shares_shapes() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c1, _) = ip.abbrev(&ip.sort(1)).unwrap();
        let (c2, _) = ip.abbrev(&ip.sort(2)).unwrap();

        let t1 = sc.open(&mut ip.env_mut(), dom.clone());
        let w1 = sc.get(0).unwrap().var();
        let s1 = ip.cond_site(&c1.clone(), w1).expect("site");
        let out = ip.cond_typing(&s1, dom.clone()).expect("typing");
        assert_eq!(*out.concl(), Formula::mem(ip.cond_term(&s1, dom.clone()), ip.sort(0)));
        let _ = sc.close(t1);

        let t2 = sc.open(&mut ip.env_mut(), dom);
        let w2 = sc.get(0).unwrap().var();
        let s2 = ip.cond_site(&c2.clone(), w2).expect("site");
        let _ = sc.close(t2);

        assert_eq!(s1.k, 1);
        assert_eq!(s1.chi, s2.chi, "one shape, one conditional singleton symbol");
        assert_eq!(s1.holes, vec![c1]);
        assert_eq!(s2.holes, vec![c2]);
    }

    /// The store is identity, not memoisation: what goes in comes back, with
    /// its certificate.
    #[test]
    fn const_store_round_trips_with_its_certificate() {
        let mut ip = Interp::new();
        let body = ip.sort(1);
        let (c, ax) = ip.abbrev(&body).unwrap();
        let key = (Name::simple("Foo"), crate::ground::ground_levels(&[0, 1]));
        ip.put_const(
            key.clone(),
            ConstInterp {
                term: c.clone(),
                typing: Err(Gap::Axiom(Name::simple("Foo"))),
                defeq: Some(Sealed::new(ax.clone()).unwrap()),
            },
        );
        let got = ip.get_const(&key).expect("stored");
        assert_eq!(got.term, c);
        assert_eq!(*got.defeq.as_ref().unwrap().thm().concl(), Formula::eq(c, body));
        // A different instantiation is a different key.
        assert!(ip
            .get_const(&(Name::simple("Foo"), crate::ground::ground_levels(&[0])))
            .is_none());
    }

    /// **The store can name a declaration at its own universe parameter, and
    /// that key is distinct from every ground one** — `LEVELPOLY.md` §5.3
    /// step 2, stated as the thing that was *impossible* before
    /// [`ConstKey`] widened.
    ///
    /// With a `Vec<u32>` key there was no term to write here at all: a
    /// parameter has no numeral, so `⟦c.{u}⟧` had no address in the store and
    /// the ground σ-schedule was a precondition of the interpretation rather
    /// than a choice. This does not make anything *mint* such a key — the σ
    /// threading is still `&[u32]` and step 1 is what changes that — it pins
    /// that the address exists.
    ///
    /// **Three instantiations, not two.** `u`, `0` and `1`: two would pass
    /// under a key that collapsed every ground level to one entry, or under
    /// one that hashed the parameter to the same slot as `0`. Each of the
    /// three is stored under its own name so a mixed-up read is visible in
    /// the assertion rather than in a count.
    #[test]
    fn the_store_addresses_a_declaration_at_its_own_parameter() {
        let mut ip = Interp::new();
        let foo = Name::simple("Foo");
        let at_u = vec![crate::expr::Level::param(Name::simple("u"))];
        let sigmas: [(&str, Vec<crate::expr::Level>); 3] = [
            ("u", at_u.clone()),
            ("0", crate::ground::ground_levels(&[0])),
            ("1", crate::ground::ground_levels(&[1])),
        ];
        for (tag, levels) in &sigmas {
            let body = ip.sort(0);
            let (c, ax) = ip.abbrev(&body).unwrap();
            ip.set_label(&c, format!("at-{tag}"));
            ip.put_const(
                (foo, crate::ground::key_levels(levels)),
                ConstInterp {
                    term: c,
                    typing: Err(Gap::Axiom(foo)),
                    defeq: Some(Sealed::new(ax).unwrap()),
                },
            );
        }
        assert_eq!(ip.const_count(), 3, "three instantiations are three entries");
        // Each address holds its own entry, and the parameter one is not a
        // ground one wearing a different spelling.
        let mut terms = Vec::new();
        for (tag, levels) in &sigmas {
            let got = ip
                .get_const(&(foo, crate::ground::key_levels(levels)))
                .unwrap_or_else(|| panic!("Foo at σ = [{tag}] is addressable"));
            terms.push(got.term.clone());
        }
        assert_ne!(terms[0], terms[1], "⟦Foo.{{u}}⟧ is not ⟦Foo.{{0}}⟧");
        assert_ne!(terms[0], terms[2], "⟦Foo.{{u}}⟧ is not ⟦Foo.{{1}}⟧");
        assert_ne!(terms[1], terms[2], "⟦Foo.{{0}}⟧ is not ⟦Foo.{{1}}⟧");
        // And a *ground* key is still spelled with its numeral, not with the
        // level ladder — the one thing the widening could have moved for free.
        assert_eq!(crate::ground::show_levels(&sigmas[2].1), "[1]");
        assert_eq!(crate::ground::show_levels(&sigmas[0].1), "[u]");
    }
}
