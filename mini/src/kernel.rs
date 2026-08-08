//! The port of `MiniKernel/Kernel.lean`.
//!
//! # Interface
//!
//! One file, like the original, and laid out in the original's order so the two
//! can be read side by side: context primitives, the `whnf`/`inferType`/
//! `isProp`/`inferProj`/telescope mutual block, the level order, definitional
//! equality, and `Environment.add`.
//!
//! **On the acceptance axis this reproduces mini-lean exactly**: every function
//! returns what mini-lean's returns, and `Result<_, String>` is its
//! `Except String`. Deviating from the original *here* would make the fidelity
//! gate (`mini/tests/tutorial.rs`) meaningless, so where the original is odd —
//! the `whnf` of a codomain sort performed outside the binder's scope in
//! `inferType`'s `.forall` clause, `natLit`'s dropped argument stack,
//! `Level.le`'s incompleteness — the oddity is reproduced and commented.
//!
//! **The evidence types of §5 are threaded through those same signatures**, and
//! live here: [`Typing`], `Ev`, and the `pi_evidence` / `lam_evidence` /
//! `app_evidence` / `is_prop_ev` / `def_eq_ev` family. The two axes stay
//! independent — acceptance is what mini-lean decides, certification is whether
//! a derivation was produced — and keeping them from collapsing into one is
//! what §0's arrangement exists for.
//!
//! Departures from mini-lean, all mechanical:
//!
//! * `ReaderT`'s implicit scoping becomes explicit push/pop on `Checker::lenv`,
//!   always through [`Checker::scoped`], which restores the telescope on the
//!   error path too. `openForall`/`openForallEager` become "push and return the
//!   body" rather than continuation-passing: a continuation-passing port
//!   recurses with a *new* closure type at each step, which does not
//!   monomorphise.
//! * The telescope is a `Vec` whose **last** element is `bvar 0`, where
//!   mini-lean's `List`'s **head** is.
//! * `appendError`'s message decoration is dropped except where it aids
//!   debugging; it cannot change a verdict.

use crate::env::{instantiate_lparams, ConstantInfo, DefKind, Declaration, Environment, IndType};
use crate::ev::{BinderClause, BinderRule, Ev, Gap};
use crate::conv::Conv;
use crate::interp::{Interp, LamSite, PiShape};
use crate::scope::{Closed, ScopeToken, Scopes};
use kernel::{FreeVar, Term, Thm};
use crate::expr::{
    app, app_n, arrow, bvar, bvars, forall, get_app, has_bvar, has_bvar_in_proj, has_const, konst,
    lam, shift, sort,
    subst, substs, Expr, Level, Name, E,
};
use std::collections::HashMap;
use std::rc::Rc;

pub type R<T> = Result<T, String>;

/// What [`Checker::binder_cong`] needs of a pair of binder interpretations,
/// abstracted over the `Π` and `λ` cases so the two share one derivation.
///
/// The three §6.2 `Π` clauses and the `λ` clause differ only in *which*
/// extensionality lemma applies and which symbol the body was abbreviated to;
/// the shape of the argument — domain conversion, pointwise family, discharge —
/// is identical, and duplicating it would be four chances to get the argument
/// order wrong instead of one.
pub trait BinderShapes {
    fn left_dom(&self) -> Term;
    fn right_dom(&self) -> Term;
    /// `⟦body⟧` on each side, rebuilt at this scope's variable.
    fn left_body(&self, ip: &mut Interp, x: &Term) -> Term;
    fn right_body(&self, ip: &mut Interp, x: &Term) -> Term;
    /// `⊢ S(p⃗,x) = ⟦body⟧`, the body symbol's defining equation at `x`.
    fn left_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm>;
    fn right_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm>;
    /// **Which rule this pair of clauses calls for** — reported when it does
    /// not fire, so the row can be scoped. See [`BinderRule`].
    fn rule(&self) -> BinderRule;
    /// The extensionality lemma, applied to the two premises.
    ///
    /// `pw` is the **discharged** family, and it is the only conversion an
    /// implementation gets. There used to be a `raw` beside it — the same
    /// conversion *before* the discharge, kept for a binder-free clause that
    /// was retired when the `Π` value clauses were unified. Both
    /// implementations took it as `_raw` and neither read it, so what it
    /// actually did was carry `{w ∈ ⟦A⟧} ⊢ …` past the close that owned that
    /// hypothesis, with the [`Closed`] already spent on `pw` and no second
    /// discharge available. See [`Checker::binder_cong`].
    fn apply(
        &self,
        ip: &mut Interp,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pw: &Thm,
    ) -> Option<Thm>;
}

impl BinderShapes for (PiShape, PiShape) {
    fn left_dom(&self) -> Term { self.0.dom() }
    fn right_dom(&self) -> Term { self.1.dom() }
    fn left_body(&self, ip: &mut Interp, x: &Term) -> Term { self.0.body_at(ip, x) }
    fn right_body(&self, ip: &mut Interp, x: &Term) -> Term { self.1.body_at(ip, x) }
    fn left_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm> { self.0.sym_at(ip, x) }
    fn right_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm> { self.1.sym_at(ip, x) }
    fn rule(&self) -> BinderRule {
        match (&self.0, &self.1) {
            (PiShape::Dep { .. }, PiShape::Dep { .. }) => BinderRule::DProd,
            (PiShape::Prop { .. }, PiShape::Prop { .. }) => BinderRule::Cond,
            (a, b) => BinderRule::Mismatch(clause_of(a), clause_of(b)),
        }
    }
    fn apply(
        &self,
        ip: &mut Interp,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pw: &Thm,
    ) -> Option<Thm> {
        match (&self.0, &self.1) {
            (PiShape::Dep { site: a, .. }, PiShape::Dep { site: b, .. }) => {
                ip.dprod_cong(a, b, d1, d2, dom_eq, pw)
            }
            (PiShape::Prop { site: a, .. }, PiShape::Prop { site: b, .. }) => {
                ip.cond_cong(a, b, d1, d2, dom_eq, pw)
            }
            // **The 937-conversion binder-congruence row is gone at its
            // source.** It was `dep = has_bvar(body, 0)` classifying two
            // spellings of one type onto two clauses with both sides right, and
            // it was repaired here by `Interp::dprod_fs_bridge` over
            // `derived::ext::dprod_const_fibre_n`. With one value clause there
            // are no two spellings, so the bridge has no input and is deleted
            // rather than left unreachable — `MINI-HANDOFF.md` §5's design call
            // stands and its subject is retired. *(This used to add that `raw`
            // survives "because the λ pair still needs the undischarged
            // conversion". It never did: the λ implementation below took it as
            // `_raw` too. `raw` is gone.)*
            //
            // A `Prop`-valued `∀` against a value one: §6.2's proof/value split
            // disagreeing across a conversion, which is a different question
            // and has never occurred in this corpus.
            _ => None,
        }
    }
}

/// Which §6.2 clause a `Π` interpretation took — for the mismatch report.
fn clause_of(s: &PiShape) -> BinderClause {
    match s {
        PiShape::Dep { .. } => BinderClause::Dep,
        PiShape::Prop { .. } => BinderClause::Cond,
    }
}

impl BinderShapes for ((LamSite, Term), (LamSite, Term)) {
    fn left_dom(&self) -> Term { self.0 .1.clone() }
    fn right_dom(&self) -> Term { self.1 .1.clone() }
    fn left_body(&self, ip: &mut Interp, x: &Term) -> Term {
        let s = self.0 .0.skel.clone();
        ip.rebuild(&s, &self.0 .0.holes, x)
    }
    fn right_body(&self, ip: &mut Interp, x: &Term) -> Term {
        let s = self.1 .0.skel.clone();
        ip.rebuild(&s, &self.1 .0.holes, x)
    }
    fn left_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm> {
        let (t, ax, holes) = (self.0 .0.t, self.0 .0.t_ax.clone(), self.0 .0.holes.clone());
        ip.symbol_at(t, &ax, &holes, x)
    }
    fn right_sym_at(&self, ip: &mut Interp, x: &Term) -> Option<Thm> {
        let (t, ax, holes) = (self.1 .0.t, self.1 .0.t_ax.clone(), self.1 .0.holes.clone());
        ip.symbol_at(t, &ax, &holes, x)
    }
    fn rule(&self) -> BinderRule { BinderRule::Lam }
    fn apply(
        &self,
        ip: &mut Interp,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pw: &Thm,
    ) -> Option<Thm> {
        ip.lam_cong(&self.0 .0, &self.1 .0, d1, d2, dom_eq, pw)
    }
}


/// **What `infer_type` returns**: the inferred type, the subject's
/// interpretation, and the evidence that the one inhabits the other.
///
/// One traversal produces all three. `⟦e⟧` *is* `infer_type(e).tm` — there is
/// no separate interpretation walk, which is what closes the two interleaved
/// cycles MINI-DESIGN.md §13 risk 3 records.
///
/// When `tm` is `None`, `ev` carries **why the interpretation stopped**, taken
/// from the sub-`Typing` that stopped it — not the clause's own label. A `Π`
/// whose domain mentions an uninterpreted inductive is blocked by that
/// inductive, and saying "the `Π` rule is unthreaded" would misfile it as
/// threading debt. Gaps propagate; the left one wins.
///
/// Invariant when `ev` is `Proved(t)`: `t.concl()` is `mem(tm.unwrap(), ⟦ty⟧)`
/// and `t.hyps()` is within the open scopes' hypotheses (I2).
///
/// # `tm` is **not** a projection of `ev`, and the attempt to make it one is
/// the measurement that says so
///
/// This struct's three fields look like one field and two derived from it, and
/// making `tm` a projection off the certificate — as [`Ev::mem_set`] already
/// reads the *set* side off it — would make "a term with no certificate"
/// inexpressible. It was tried, at the `infer_type` boundary, and the cost is
/// exact:
///
/// * the corpus is untouched — `constEv = typeEv = pairs = 218`, `gapped = 0`;
/// * `mini/tests/fixtures/beyond_the_tower.ndjson` loses a derivation.
///   `Type 30 → Type 30` interprets to a perfectly good `dprod`, and mini
///   proves `⊢ ⟦c⟧ ∈ ⟦Type 30 → Type 30⟧` about it; what it cannot prove is
///   that same term's own membership in `⟦Type 31⟧`, because
///   [`crate::interp::CUMUL_HEIGHT`] is 8. Projecting drops the term for want
///   of a *different* theorem about it, and `constEv` falls from 2 to 1.
///
/// So `⟦e⟧` is defined by §6.2 whether or not mini can certify it, and
/// `⊢ ⟦e⟧ ∈ ⟦ty⟧` is a second obligation and `⊢ ⟦ty⟧ ∈ ⟦Sort l⟧` a third.
/// That is MINI-DESIGN.md §0's two axes, and `beyond_the_tower` is the witness
/// that they are two. A `Gap` beside a term is not a lie; it is a resource
/// limit, or a declined declaration whose *proof* still denotes `•`.
///
/// What **is** enforced is narrower and is the part that was worth enforcing:
/// no clause mints a term out of a syntactic flag alone. `lam_evidence`'s
/// proof branch used to, on an uninterpretable domain, and no longer does.
#[derive(Debug, Clone)]
pub struct Typing {
    pub ty: E,
    /// `⟦subject⟧`, or `None` when the subject has no interpretation.
    pub tm: Option<Term>,
    pub ev: Ev,
}

/// **Which clause of Carneiro §6.2 an expression falls under.**
///
/// §6.2 splits three constructors two ways:
///
/// ```text
/// ⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]     ⟦Πx : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧
/// ⟦λx : α. e⟧ = •                        ⟦Λx : α. e⟧ = (x ∈ ⟦α⟧ ↦ ⟦e⟧)
/// ⟦e₁ e₂⟧     = •                        ⟦e₁ · e₂⟧   = ⟦e₁⟧(⟦e₂⟧)
/// ```
///
/// # Two variants, where nanoda has three
///
/// nanoda's `Clause` carries an `Undet` arm, for two different reasons that it
/// counts apart. Neither survives in mini:
///
/// * **`imax u v` at a universe parameter.** It is `0` when `v := 0` and
///   `max(u,v)` otherwise, so at a level-polymorphic declaration's own
///   parameters neither clause applies. Mini checks per *ground* instantiation
///   (MINI-DESIGN.md §3), so every level reaching a classifier is a numeral and
///   the case cannot arise. The declaration-shape zone, which does run at
///   symbolic levels, has no interpretation at all and so asks no classifier.
/// * **"this approximation could not follow the term."** This is the
///   interesting one, and it is structural rather than a matter of degree.
///
/// # Why mini's classifier is exact and nanoda's is an approximation
///
/// nanoda's `body_clause` is a 100-line syntactic walk over heads and arities
/// that never instantiates, with a redex case, a `let` case, a projection case
/// and a `syn_type` shadow walk beside it. Its own doc says why: *"the decision
/// needs the body's sort, `infer` lives on `TypeChecker`, which owns this
/// backend and is in the middle of a call into it, and the backend may not call
/// back."* The approximation exists to route around the backend/checker split.
///
/// **Mini has no backend/checker split to route around.** The decision needs
/// the body's sort; `infer_type` computes the body's sort; so the classifier
/// *is* `infer_type`, and the two functions below are three lines each. This is
/// not a shortcut — it is §0's rule applied: running the checker's own
/// inference forward on a subterm is inference, not search. It is deterministic,
/// total on well-typed input, and produces its evidence as it goes.
///
/// The consequences are worth stating, because they are the first place mini
/// pays off as a design experiment rather than as a port:
///
/// * Every `Undet::Unknown` row disappears — not reduced, *unrepresentable*.
///   nanoda's `PSigma.fst` disagreement (`081_PSigma.snd`, eight derivations
///   lost because a projection was `Prop` on one path and undetermined on
///   another) cannot be expressed here.
/// * The `syn_type`/`syn_type_proj` shadow walk, which exists only to feed this
///   classifier without re-entering the checker, has no counterpart.
/// * The redex and `let` cases vanish: `infer_type` already handles them, and
///   `is_prop` already whnfs.
///
/// # Why it is still a function, without a memo
///
/// `⟦·⟧` must be a function — if one expression were classified `Prop` on one
/// path and `Type` on another, two equal Lean terms would interpret to unequal
/// set terms and every congruence rule over them would fail. nanoda pins that
/// with a memo. Mini does not need one for *correctness*: the answer is
/// `is_prop` of the expression, `is_prop` is deterministic, and mini has no
/// state that could make it answer differently on a second call. A memo here
/// would be an optimisation, and would be sound for the same reason — it stores
/// a function of its key.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// The left column: a proposition, or a proof, interpreted into `{•}`.
    Prop,
    /// The right column: a genuine set, function graph, or dependent product.
    Type,
}

/// **What the caller already knows about `def_eq_ev`'s left endpoint** — the
/// one thing that decides whether the proof-irrelevance gate has to be asked.
///
/// # Why a parameter and not an inference
///
/// [`Checker::def_eq_ev`] opens with `infer_type(e1)`, and that inference has
/// **exactly one consumer**: the `is_prop_or_unit_ev` gate, and `proof_irrel_ev`
/// on the branch where the gate says yes. Nothing below the gate reads `t1`. So
/// at any caller that can rule the gate out, the whole inference — and every
/// reduction it performs, and every β premise those reductions re-infer — is
/// dead work.
///
/// **`Type` is a theorem, not a hint.** If `e1`'s own type is a `Sort`, then
/// `is_prop_or_unit_ev(t1.ty, _)` is `None` on both of its branches, by
/// inspection of that function: the sort test computes `type of Sort v`, which
/// is `Sort (v+1)` and never `Sort 0`; the unit-like test then asks `whnf(t1.ty)`
/// for a `Const` head and a `Sort` has none. A caller comparing two *types* —
/// a `Π`'s domain against an argument's inferred type, a binder domain against
/// a binder domain — is in that case by construction, and the four sites that
/// pass `Type` each say which construction.
///
/// # Measured
///
/// On `proj_reduced_carrier`, `def_eq_ev`'s entry inference dynamically
/// contains **53.0%** of all 4 369 270 conversions, while proof irrelevance
/// itself fires **25** times in the whole run. The gate is nearly always
/// asked and almost never answered yes; the four `Type` sites are where the
/// asking was provably pointless.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lhs {
    /// Nothing known — infer `e1` and ask the gate. Every decision-only
    /// caller, and every congruence over *terms*, is here.
    Unknown,
    /// `e1`'s own type is a `Sort`: `e1` is a type, not an element of one.
    /// The gate cannot fire, so it is not asked.
    Type,
}

fn no_levels() -> Rc<[Level]> { Vec::new().into() }

fn levels(ls: &[Level]) -> Rc<[Level]> { ls.to_vec().into() }

/// `Array.extract`'s clamping slice, which mini-lean relies on in several
/// places (`retType.getApp.2[numParams:numParams+numIndices]` on a spine that
/// may be shorter).
fn slice(v: &[E], a: usize, b: usize) -> Vec<E> {
    let a = a.min(v.len());
    let b = b.min(v.len()).max(a);
    v[a..b].to_vec()
}

/// **§0.4 across two alternative routes**: the reason to publish when both of
/// them declined, given the clause's *own* fallback label `own`.
///
/// [`Ev::zip`]'s "the left gap wins" rule, with one correction that the two-route
/// shape needs and `zip` does not: a route whose decline *is* the clause's own
/// label has not given a reason at all — `proj_prop`'s `Gap::StructProj` means
/// "this is not my row", and it is exactly then that the second route's answer
/// is the informative one. So the first route wins unless it said nothing, and
/// when neither said anything the caller gets `own` back, which is what it
/// would have minted anyway.
///
/// Free rather than a method on [`Ev`] because the inputs are `Gap`s that never
/// became evidence: both routes return `Result<_, Gap>`, and there is nothing
/// to compose.
fn first_reason(own: &Gap, g1: Gap, g2: Gap) -> Gap { if g1 == *own { g2 } else { g1 } }

/// `sort` — the shape check, not the interpretation.
pub fn as_sort(e: &E) -> R<Level> {
    match &e.view() {
        Expr::Sort(u) => Ok(*u),
        _ => Err(format!("Expected a sort, got {e}")),
    }
}

/// `assertLevelLe`.
pub fn assert_level_le(l1: &Level, l2: &Level) -> R<()> {
    if Level::le(&l1.simplify(), &l2.simplify(), 0) {
        Ok(())
    } else {
        Err(format!("Expected level inequality does not hold: {l1} ≤ {l2}"))
    }
}

/// `assertLevelEq`.
pub fn assert_level_eq(l1: &Level, l2: &Level) -> R<()> {
    let (a, b) = (l1.simplify(), l2.simplify());
    if Level::le(&a, &b, 0) && Level::le(&b, &a, 0) {
        Ok(())
    } else {
        Err(format!("Expected level equality does not hold: {l1} = {l2}"))
    }
}

/// `freshLevelName`.
fn fresh_level_name(used: &[Name]) -> Name {
    let mut n = 0u32;
    loop {
        let name = if n == 0 { Name::simple("v") } else { Name::simple(&format!("v{n}")) };
        if !used.contains(&name) {
            return name
        }
        n += 1;
    }
}

/// The data `checkCtorType`/`checkCtorParam`/`isValidIndApp` close over in the
/// original; a struct here because Rust has no local `let rec` with capture.
///
/// **Plural, because a `mutual … end` block is checked as one declaration.**
/// The original closes over one name and one index count; a block closes over
/// all of its members', because a constructor of any member may end at any
/// member and may hold a recursive field at any member. `names[i]` and
/// `num_indices[i]` are the same member; the parameter count and the resultant
/// level are shared by kernel rule and are scalars.
struct IndCtx<'a> {
    names: &'a [Name],
    num_indices: &'a [u32],
    lparams: &'a [Name],
    num_params: u32,
    ind_level: &'a Level,
}

impl IndCtx<'_> {
    /// Which member of the block `n` is, if any. One linear scan of a list
    /// whose length is the block size — two on every corpus file, and one.
    fn member(&self, n: &Name) -> Option<usize> { self.names.iter().position(|m| m == n) }

    /// Does **any** member of the block occur in `e`?
    ///
    /// The single-declaration original asks `has_const(ind_name, e)`, and the
    /// generalisation is not "ask about the member being checked": a
    /// constructor of `Exp` holding a `Stm` is a recursive argument, and a
    /// positivity check that only looked for `Exp` would accept `(Stm → Exp) →
    /// Exp` as strictly positive.
    fn occurs(&self, e: &E) -> bool { self.names.iter().any(|n| has_const(n, e)) }
}

/// `LEnv` and its monad, minus the unused `lparams` set (mini-lean never reads
/// it: `checkDeclarInfo`-style parameter validation does not exist there).
pub struct Checker<'e, 'i> {
    env: &'e Environment,
    /// The local typing environment, as a telescope. **`lenv.last()` is the
    /// type of `bvar 0`**; a `bvar j` inside `lenv[i]` refers to `lenv[i+j+1]`
    /// in mini-lean's indexing, i.e. one step further out.
    lenv: Vec<E>,
    /// The evidence side, or `None` in the declaration-shape zone
    /// (MINI-DESIGN.md §9 zone A), which runs at the declaration's own
    /// symbolic levels and therefore has no interpretation at all.
    th: Option<Th<'i>>,
    /// **The certificate for one type's reduction, kept rather than rebuilt** —
    /// [`Checker::whnf_typing`]'s memo. See that function for the key and why
    /// it is sound; the lifetime is this `Checker`, so it is one
    /// `(declaration, σ)` and never leaks across pairs.
    wt_memo: HashMap<Term, (E, E, Thm)>,
    /// **`infer_type`'s frame-local memo**, one frame per telescope slot.
    /// `frames.len() == lenv.len() + 1` at all times. See [`Frame`].
    frames: Vec<Frame>,
}

/// One telescope slot's worth of [`Checker::infer_type`] results.
///
/// # Why a *frame* and not a memo
///
/// The whole `Typing` is cached — `ty`, `⟦e⟧` and the **evidence** — with no
/// α-canonicalisation, no `Sealed` closing and no re-instantiation at a hit.
/// That is affordable for exactly one reason: *within one frame the telescope
/// is fixed, so the opening is fixed, so the kernel variables the evidence
/// mentions are the same ones that are still open.* A key that crossed
/// openings would need all of that machinery; this one never crosses.
///
/// `mini::Expr` has only `BVar(u32)` — there is no free-variable case — so the
/// key is the expression alone. Nothing needs canonicalising: at a fixed
/// telescope, `e` denotes one judgement.
///
/// # The three things that could make a frame lie, and what stops each
///
/// * **A `bvar` meaning something else.** Only a change to `lenv` can do that,
///   and `frames` is pushed and popped at every one of the five sites that
///   touch `lenv` ([`Checker::push`], `push_types`, `close_one`, `close_slot`,
///   `scoped`) — including `push_types`, which grows `lenv` without opening a
///   kernel scope and is the one place the two stacks are *not* in lockstep.
///   Entries never travel under a binder; an outer frame becomes reachable
///   again only when `lenv` is back to what it was.
/// * **The same depth, a different binder.** Popping discards the frame, so a
///   re-entered binder — which mints a fresh kernel variable — gets an empty
///   one. `Frame::default()` on push is what makes that automatic.
/// * **A kernel scope opened behind `lenv`'s back.** `scope_term` reads
///   `scopes.get(scopes.len() - 1 - depth)`, so an extra scope left open on
///   `th.scopes` by a derivation *renumbers* every variable this frame's
///   evidence mentions, with `lenv` standing still. Twelve modules call
///   `Scopes::open` directly. Rather than audit them, `scopes_len` records the
///   depth the frame was filled at and any disagreement empties it — O(1), and
///   it needs no argument about who may open what.
#[derive(Default)]
struct Frame {
    /// `th.scopes.len()` when this frame was last written to.
    scopes_len: usize,
    /// Structural hash of the key expression → the candidates under it. `Expr`
    /// has no `Hash`, and a hash is a hint: a hit is confirmed by `==` before
    /// the `Typing` is handed back, exactly as `wt_memo` confirms its own.
    map: HashMap<u64, Vec<(E, Typing)>>,
}

/// A structural hash of a Lean expression. Not a canonical form and not
/// required to be one — [`Frame::map`] confirms every hit by equality.
fn hash_expr(e: &E) -> u64 {
    use std::hash::{Hash, Hasher};
    fn go<H: Hasher>(e: &E, h: &mut H) {
        match &e.view() {
            Expr::BVar(i) => {
                0u8.hash(h);
                i.hash(h);
            }
            Expr::Sort(u) => {
                1u8.hash(h);
                format!("{u}").hash(h);
            }
            Expr::Const(n, ls) => {
                2u8.hash(h);
                n.hash(h);
                ls.len().hash(h);
                for l in ls.iter() {
                    format!("{l}").hash(h);
                }
            }
            Expr::App(f, a) => {
                3u8.hash(h);
                go(f, h);
                go(a, h);
            }
            Expr::Lam { ty, body } => {
                4u8.hash(h);
                go(ty, h);
                go(body, h);
            }
            Expr::Forall { ty, body } => {
                5u8.hash(h);
                go(ty, h);
                go(body, h);
            }
            Expr::Let { ty, val, body } => {
                6u8.hash(h);
                go(ty, h);
                go(val, h);
                go(body, h);
            }
            Expr::Proj { ind, idx, s } => {
                7u8.hash(h);
                ind.hash(h);
                idx.hash(h);
                go(s, h);
            }
            other => {
                8u8.hash(h);
                format!("{other}").hash(h);
            }
        }
    }
    let mut h = std::collections::hash_map::DefaultHasher::new();
    go(e, &mut h);
    h.finish()
}

/// The interpretation and the kernel scope stack, kept **inside** the
/// `Checker` so they cannot desynchronise from the telescope: every `push`
/// opens a scope and every `scoped` closes one, in the same call.
struct Th<'i> {
    ip: &'i mut Interp,
    scopes: Scopes,
    /// One entry per `lenv` slot, outermost first: the scope's depth, or
    /// `None` when the domain could not be interpreted and so no kernel
    /// variable stands for the binder. A `bvar` pointing at such a slot has no
    /// interpretation, which is a gap and not a lie.
    slots: Vec<Option<usize>>,
    tokens: Vec<ScopeToken>,
}

impl<'e, 'i> Checker<'e, 'i> {
    /// The shape zone: acceptance only, no evidence.
    pub fn new(env: &'e Environment) -> Self {
        Checker {
            env,
            lenv: Vec::new(),
            th: None,
            wt_memo: HashMap::new(),
            frames: vec![Frame::default()],
        }
    }

    /// The evidence-carrying pass, at one ground instantiation.
    pub fn threaded(env: &'e Environment, ip: &'i mut Interp) -> Self {
        Checker {
            env,
            lenv: Vec::new(),
            th: Some(Th {
                ip,
                scopes: Scopes::new(),
                slots: Vec::new(),
                tokens: Vec::new(),
            }),
            wt_memo: HashMap::new(),
            frames: vec![Frame::default()],
        }
    }

    /// `⟦bvar i⟧`, or `None` when the binder's domain had no interpretation.
    fn scope_term(&self, idx: u32) -> Option<Term> {
        let th = self.th.as_ref()?;
        let n = self.lenv.len();
        let depth = (*th.slots.get(n.checked_sub(1 + idx as usize)?)?)?;
        // `slots` counts from the outermost; `Scopes::get` from the innermost.
        th.scopes.get(u32::try_from(th.scopes.len() - 1 - depth).ok()?).map(|s| s.term())
    }

    /// The typing of `bvar i`: the scope's own assumption, at zero cost.
    ///
    /// The consumer is `infer_type`'s `.bvar` clause, which is threaded in the
    /// next step; kept here because it is the counterpart of `scope_term` and
    /// belongs beside it.
    #[allow(dead_code)]
    pub fn scope_typing(&self, idx: u32) -> Ev {
        let Some(th) = self.th.as_ref() else { return Ev::missing(Gap::SymbolicLevel) };
        let n = self.lenv.len();
        let Some(Some(depth)) = n.checked_sub(1 + idx as usize).and_then(|k| th.slots.get(k))
        else {
            return Ev::missing(Gap::SymbolicLevel)
        };
        match th.scopes.get((th.scopes.len() - 1 - depth) as u32) {
            Some(s) => Ev::Proved(s.assumption().clone()),
            None => Ev::missing(Gap::SymbolicLevel),
        }
    }

    /// Environment lookup at the environment's own lifetime, so results may be
    /// held across `&mut self` calls (the environment is fixed for a
    /// `Checker`'s whole life).
    fn lookup(&self, n: &Name) -> Option<&'e ConstantInfo> { self.env.consts.get(n) }

    // ────────────────────────────────────────── the §6.2 dispatch ──
    //
    // **There is no separate `interp` traversal.** `⟦e⟧` is `infer_type(e).tm`:
    // one walk produces the type, the interpretation and the evidence
    // together, and every interpretation a rule needs comes from a `Typing`
    // already in hand. An earlier revision had `interp` and `infer_type` call
    // each other — `interp` needed the proof/non-proof clause, which is
    // `infer_type`, and `infer_type` wanted `⟦e⟧`, which was `interp` — and
    // `push` interpreted the binder's domain on top of that. Two interleaved
    // cycles, branching exponentially in binder depth. See MINI-DESIGN.md §13,
    // risk 3.

    /// Open a binder of type `ty`; returns the depth to restore.
    fn open_slot(&mut self, ty: E, dom: Option<Term>) -> usize {
        let saved = self.lenv.len();
        self.push(ty, dom);
        saved
    }

    /// Close the innermost binder and hand back its [`Closed`], which owns the
    /// discharge.
    ///
    /// The `λ` and `Π` rules need it: their premise is a family
    /// `∀w. (w ∈ ⟦A⟧ → φ)`, and that shape is what `Closed::discharge`
    /// produces and what `lam_in_funspace_n` / `lam_in_dprod_n` /
    /// `dprod_in_universe_pair_n` / `cond_intro` all take. Not a coincidence:
    /// the two shapes were chosen to be the same one, so nothing is ever
    /// re-proved against a merged hypothesis set.
    pub(crate) fn close_one(&mut self) -> Option<Closed> {
        self.lenv.pop();
        self.frames.truncate(self.lenv.len() + 1);
        let th = self.th.as_mut()?;
        let slot = th.slots.pop()?;
        slot?;
        let tok = th.tokens.pop().expect("a scoped slot has a token");
        Some(th.scopes.close(tok))
    }

    /// Close every binder opened since `saved`, innermost first.
    ///
    /// **The `Closed`s are dropped, and that is what this function is for.**
    /// It is the *unwind*, and it reaches a live scope in only two states.
    /// On an `Err` — a rejection of the file, which carries no evidence at all
    /// (`Ev`'s header: `Err` is not `Gap`). Or after the clause has finished
    /// with the binder: either it spent its `Closed` through
    /// [`Self::close_one`], in which case `slots.len() == saved` already and
    /// this loop does nothing, or it gave up and returned a `Gap`, which is
    /// not a theorem either.
    ///
    /// So it never drops a discharge that anything was owed. What it does
    /// guarantee is that the *token* is consumed on every path, which is the
    /// half [`Scopes::close`]'s LIFO assertion needs: a scope left open here
    /// would abort the next close on the same stack rather than corrupt it.
    fn close_slot(&mut self, saved: usize) {
        self.lenv.truncate(saved);
        self.frames.truncate(self.lenv.len() + 1);
        if let Some(th) = self.th.as_mut() {
            while th.slots.len() > saved {
                if th.slots.pop().flatten().is_some() {
                    let tok = th.tokens.pop().expect("a scoped slot has a token");
                    let _ = th.scopes.close(tok);
                }
            }
        }
    }

    /// The kernel variable of the innermost open binder, if it has one.
    fn current_var(&self) -> Option<FreeVar> {
        let th = self.th.as_ref()?;
        let d = (*th.slots.last()?)?;
        th.scopes.get(u32::try_from(th.scopes.len() - 1 - d).ok()?).map(|s| s.var())
    }

    /// `getLocalType`.
    ///
    /// `pub(crate)` for [`crate::ctor_ix`], which reads a recursive argument's
    /// binder type at the bottom of the constructor's nest. The shift is this
    /// function's, deliberately: a consumer doing its own de Bruijn arithmetic
    /// against a telescope it does not own is how off-by-ones get in.
    pub(crate) fn local_type(&self, idx: u32) -> R<E> {
        let n = self.lenv.len();
        if (idx as usize) >= n {
            return Err(format!("deBruijn index #{idx} out of bounds"))
        }
        Ok(shift(&self.lenv[n - 1 - idx as usize], 0, idx + 1))
    }

    /// `openType`, push half. Always paired by [`Checker::scoped`].
    ///
    /// In the threaded pass this also opens a kernel scope over the domain —
    /// the two halves are one operation, so a binder cannot be opened on one
    /// side and not the other.
    ///
    /// **`dom` is a parameter, not something this recomputes.** It is
    /// `infer_type(ty).tm`, which the caller has just computed. Interpreting
    /// it here instead put `interp` inside `infer_type` inside `push`, giving
    /// branching exponential in binder depth (MINI-DESIGN.md §13, risk 3).
    fn push(&mut self, ty: E, dom: Option<Term>) {
        self.lenv.push(ty);
        self.frames.push(Frame::default());
        if let Some(th) = self.th.as_mut() {
            match dom {
                Some(d) => {
                    let depth = th.scopes.len();
                    let tok = th.scopes.open(&mut th.ip.env, d);
                    th.tokens.push(tok);
                    th.slots.push(Some(depth));
                }
                None => th.slots.push(None),
            }
        }
    }

    /// `openTypes` — a non-dependent telescope, each entry shifted past the
    /// ones pushed before it.
    fn push_types(&mut self, tys: &[E]) {
        for (i, t) in tys.iter().enumerate() {
            let d = u32::try_from(i).expect("telescope length");
            self.lenv.push(shift(t, 0, d));
            // **`push_types` too.** It grows `lenv` without opening a kernel
            // scope, so it is the one site where the telescope and the scope
            // stack are not in lockstep — and it is a `bvar` reindexing all
            // the same, which is what a frame is about.
            self.frames.push(Frame::default());
        }
    }

    /// `readLocalTypes`: the innermost `n` types, brought into the current
    /// context and ordered outermost-first.
    fn read_local_types(&self, n: u32) -> R<Vec<E>> {
        if self.lenv.len() < n as usize {
            return Err(format!("Expected at least {n} local variables, got {}", self.lenv.len()))
        }
        let mut out: Vec<E> = (0..n).map(|i| self.local_type(i)).collect::<R<Vec<E>>>()?;
        out.reverse();
        Ok(out)
    }

    /// Run `f` with the telescope restored afterwards, on the error path too.
    /// This is `withReader`'s scoping, made explicit.
    ///
    /// **Generic in `T`, and the `Closed`s are dropped — so `T` must not be
    /// able to carry a theorem out.** At all sixteen call sites (`grep -n
    /// '\.scoped(|' mini/src/kernel.rs`) it cannot: `T` is `bool` at
    /// [`Self::try_fun_eta`], `def_eq_params` and the inductive-shape
    /// predicates, `()` at the `check_ctor_type` walks, and an `E` — or an
    /// `(u32, Level)`, or an `Option<E>` — at the recursor-type builders.
    /// Never a `Thm`, never an `Ev`: the two rules that build a certificate
    /// under a binder, [`Self::pi_evidence`] and [`Self::lam_evidence`], take
    /// their own [`Self::close_one`] and do not come through here. Every one
    /// of the sixteen is zone A or an acceptance decision, which is why
    /// dropping the discharge costs nothing — and it is a property of the
    /// callers, not of this function, so a seventeenth returning evidence
    /// would need [`Self::close_one`] instead.
    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.lenv.len();
        let r = f(self);
        self.lenv.truncate(saved);
        self.frames.truncate(self.lenv.len() + 1);
        if let Some(th) = self.th.as_mut() {
            while th.slots.len() > saved {
                if th.slots.pop().flatten().is_some() {
                    let tok = th.tokens.pop().expect("a scoped slot has a token");
                    let _ = th.scopes.close(tok);
                }
            }
        }
        r
    }

    /// `mkForall`: wrap `body` in `n` `Π`s with types read off the telescope.
    fn mk_forall(&self, n: u32, body: E) -> R<E> {
        let len = self.lenv.len();
        let n = (n as usize).min(len);
        let mut out = body;
        for i in 0..n {
            out = forall(self.lenv[len - 1 - i], out);
        }
        Ok(out)
    }

    /// `mkLambda`.
    fn mk_lambda(&self, n: u32, body: E) -> R<E> {
        let len = self.lenv.len();
        let n = (n as usize).min(len);
        let mut out = body;
        for i in 0..n {
            out = lam(self.lenv[len - 1 - i], out);
        }
        Ok(out)
    }

    // ─────────────────────────────────────────────────────── whnf ──

    /// The interpreter, when there is one.
    fn ip(&mut self) -> Option<&mut Interp> { self.th.as_mut().map(|t| &mut *t.ip) }

    /// Lift a leg about the head over the argument stack: from
    /// `⊢ ⟦c⟧ = ⟦c'⟧` build `⊢ ⟦c s⃗⟧ = ⟦c' s⃗⟧`, one [`conv::app_cong`] per
    /// argument against `eq_refl` of that argument's own interpretation.
    ///
    /// **This is why `whnf` takes `⟦e⟧`.** MINI-DESIGN.md §6.4 argued that no
    /// `whnf` site consumes a typing *to decide the reduction*, and that is
    /// true; what the argument missed is that the certificate for a delta step
    /// needs `⟦sᵢ⟧` for every argument on the stack. Deriving them here would
    /// walk the term a second time — §13 risk 3 one level down. They come from
    /// the `Typing` the caller already held, taken apart again by
    /// [`Interp::parts_of`].
    fn lift_over_stack(&mut self, leg: Ev, stack_tms: &[Option<Term>]) -> Ev {
        let mut out = leg;
        for s in stack_tms {
            if out.gap().is_some() {
                return out
            }
            let Some(s) = s.clone() else { return Ev::missing(Gap::NoEndpoint) };
            let refl = Ev::Proved(kernel::Thm::eq_refl(s));
            let Some(ip) = self.ip() else { return Ev::missing(Gap::SymbolicLevel) };
            out = crate::conv::app_cong(ip, &out, &refl);
        }
        out
    }

    /// `Γ ⊢ ⟦f a⃗⟧ = ⟦f a⃗′⟧` where `a⃗` and `a⃗′` agree everywhere but position
    /// `pos`, whose conversion is `at`.
    ///
    /// [`Checker::lift_over_stack`] with one argument allowed to move — the
    /// same fold, the same `app_cong`, and the reason it exists separately is
    /// that ι needs a congruence *inside* the spine rather than over its tail.
    /// See the ι site: a major premise spelled through an abbreviation reduces
    /// to its constructor, and the rule is stated at the reduct while the
    /// caller's expression is stated at the abbreviation.
    fn spine_cong(&mut self, head: Term, arg_tms: &[Option<Term>], pos: usize, at: Ev) -> Ev {
        let mut out = Ev::Proved(kernel::Thm::eq_refl(head));
        for (i, s) in arg_tms.iter().enumerate() {
            if out.gap().is_some() {
                return out
            }
            let leg = if i == pos {
                at.clone()
            } else {
                let Some(s) = s.clone() else { return Ev::missing(Gap::NoEndpoint) };
                Ev::Proved(kernel::Thm::eq_refl(s))
            };
            let Some(ip) = self.ip() else { return Ev::missing(Gap::SymbolicLevel) };
            out = crate::conv::app_cong(ip, &out, &leg);
        }
        out
    }

    /// `whnf`, acceptance only. The reduct, with the certificate discarded *by
    /// type* — every caller of this one is a decision with no evidence
    /// consumer (the shape zone, the K-rule probe, `is_def_eq`).
    pub fn whnf(&mut self, e: &E) -> R<E> {
        Ok(self.whnf_conv(e, None, &Gap::NoEndpoint)?.0)
    }

    /// **`whnf`, threaded**: the reduct and `Γ ⊢ ⟦e⟧ = ⟦e'⟧`.
    ///
    /// `tm` is `⟦e⟧`, handed in rather than derived — the uniform principle,
    /// see [`Checker::lift_over_stack`]. `why` is the reason to report when it
    /// is absent, which is the caller's own gap and never this function's
    /// label (§0.4).
    ///
    /// Mini-lean's stack machine, with full eager delta and no lazy-delta
    /// heuristic; `go`'s recursion is a loop here, and the certificate is a
    /// `trans` chain composed along it.
    pub fn whnf_conv(&mut self, e: &E, tm: Option<Term>, why: &Gap) -> R<(E, Conv)> {
        let tm_asked = tm.is_some();
        // Handed no endpoint, this is the acceptance-only `whnf` and its legs
        // state nothing; `why` is the caller's own reason and was recorded
        // where it was chosen. See [`crate::blocker::Quiet`].
        let _quiet =
            (!tm_asked && crate::blocker::is_armed()).then(crate::blocker::Quiet::new);
        let mut cur = *e;
        // The endpoint the caller asked about, kept for `done!`'s proof clause
        // below: `cur_tm` is loop state and is gone by the time it is needed.
        let from_tm = tm.clone();
        let mut cur_tm = tm;
        // `stack[0]` is the *first* argument, matching mini-lean's `a :: stack`.
        let mut stack: Vec<E> = Vec::new();
        let mut stack_tms: Vec<Option<Term>> = Vec::new();
        let mut acc = match &cur_tm {
            Some(t) => Conv::refl(*e, t),
            // **Propagation, not minting.** `why` is the caller's own reason,
            // already chosen and — where it came from an `Ev` — already
            // recorded at the site that chose it. Routing it through
            // `Ev::missing` again would put this one line at the top of every
            // blocker trail (it was, ×20 on a single pair) and bury the step
            // that actually gave up. `blocker`'s "re-wrapping is not minting".
            None => Conv { to: *e, ev: Ev::Gap(why.clone()) },
        };
        // A closure would borrow `self`; this macro is the same thing without
        // the borrow. `$leg` is about the head, `$to` the whole reduct.
        // `to` is filled in once, at the return: the intermediate expressions
        // are never looked at, and building them would cost an `app_n` per
        // step.
        macro_rules! step {
            ($leg:expr) => {{
                let lifted = self.lift_over_stack($leg, &stack_tms);
                let next = Conv { to: e.clone(), ev: lifted };
                acc = match self.ip() {
                    Some(ip) => acc.then(ip, next),
                    None => Conv { to: next.to, ev: Ev::missing(Gap::SymbolicLevel) },
                };
            }};
        }
        macro_rules! done {
            ($to:expr) => {{
                let to = $to;
                acc.to = to.clone();
                // **Reducing a proof is reflexivity**, and the walk cannot say
                // so on its own. See [`Checker::proof_point_leg`]: this is the
                // one place that asks, and it asks only when the walk has
                // already given up, so a threaded reduction is never re-derived
                // and an acceptance-only one never pays for the question.
                if acc.ev.gap().is_some() {
                    if let Some(ev) = self.proof_point_leg(&from_tm, &to) {
                        acc.ev = ev;
                    }
                }
                // The §0.3 census, on the *other* population: `whnf`'s legs are
                // where a `Γ`-carrying conversion would come from, because beta
                // is the one step that consumes a membership.
                if tm_asked {
                    if let Some(ip) = self.ip() {
                        ip.note_conv(&acc.ev);
                    }
                }
                return Ok((to, acc))
            }};
        }
        loop {
            let node = cur;
            match &node.view() {
                Expr::Const(name, ls) => {
                    let cinfo =
                        self.lookup(name).ok_or_else(|| format!("Unknown constant {name}"))?;
                    if let Some(value) = cinfo.value() {
                        let next = instantiate_lparams(value, cinfo.lparams(), ls)?;
                        // **Delta**: the constant's own defining equation, from
                        // the store. Mini-lean's whnf is eagerly unfolding, so
                        // nanoda's `lazy_delta_step`/`recall_eq` machinery has
                        // no counterpart and this is the whole of the step.
                        let (leg, to_tm) = self.delta_evidence(name, ls, &cur_tm);
                        step!(leg);
                        cur_tm = to_tm;
                        cur = next;
                        continue
                    }
                    if let ConstantInfo::Recursor {
                        lparams,
                        num_params,
                        num_motives,
                        num_minors,
                        num_indices,
                        rules,
                        k_type,
                        ..
                    } = cinfo
                    {
                        let np = *num_params as usize;
                        // **The motive count, read rather than assumed.** It is
                        // `1` for every recursor outside a `mutual … end` block
                        // and was a literal `1` here; a block of `n` types binds
                        // `n` motives before the minors, so the major argument
                        // moves and every `np + 1 + nm` below moves with it.
                        let nmot = *num_motives as usize;
                        let nm = *num_minors as usize;
                        let major_pos = np + nmot + nm + *num_indices as usize;
                        let Some(major) = stack.get(major_pos).cloned() else {
                            done!(app_n(node, &stack))
                        };
                        // The K-rule: an inductive proposition's major premise
                        // needs only to *have* the right type.
                        if let Some(kt) = k_type {
                            let kt = instantiate_lparams(kt, lparams, ls)?;
                            let kt = substs(&kt, &stack[..np], 0);
                            let major_ty = self.infer_ty(&major)?;
                            if self.is_def_eq(&major_ty, &kt)? {
                                if rules.len() != 1 {
                                    return Err("Wrong number of rules for k-rule recursor".into())
                                }
                                let args = stack[..np + nmot + nm].to_vec();
                                let rhs = instantiate_lparams(&rules[0].1, lparams, ls)?;
                                let next = substs(&rhs, &args, 0);
                                // **Iota**, K-rule form. A declaration mini
                                // *interprets* — one with a
                                // [`crate::direct::Clause`] — has no ι theorem
                                // and needs none: its eliminator's stored nest
                                // has the ι right-hand side at its bottom, so
                                // the certificate is [`Self::nest_iota`]'s β
                                // chain and it has no premise. `Eq` is the only
                                // such declaration and it is the only one the
                                // K-rule fires at, which is not a coincidence:
                                // both are `thesis.txt:2124`'s clause.
                                let direct = self
                                    .environment()
                                    .owner(name)
                                    .and_then(crate::direct::clause_for)
                                    .is_some();
                                let (legs, to_tm) = if direct && stack_tms.len() > major_pos {
                                    let rty = instantiate_lparams(cinfo.ty(), lparams, ls)?;
                                    let all = stack[..major_pos + 1].to_vec();
                                    let all_tms = stack_tms[..major_pos + 1].to_vec();
                                    self.nest_iota(&cur_tm, &rty, &all, &all_tms, &next)
                                } else {
                                    (Vec::new(), None)
                                };
                                match to_tm {
                                    Some(t) => {
                                        for leg in legs {
                                            stack_tms.remove(0);
                                            step!(leg);
                                        }
                                        cur_tm = Some(t);
                                    }
                                    // **The derived route's absence stays
                                    // named.** What is missing there is
                                    // `DepRecursor::iota` at the use site's own
                                    // minors, and `PRE` with it — a different
                                    // thing from this clause, and it keeps the
                                    // ι label rather than borrowing this one's
                                    // failure mode.
                                    None => {
                                        // **No interpretation was being
                                        // tracked, so there is no ι question**
                                        // — `delta_evidence`'s own first line,
                                        // at this site. An acceptance-only
                                        // `whnf` reaches here and reporting a
                                        // computation rule for it inflates the
                                        // ι census with a pair that is not
                                        // asking for one: `094`'s second K-rule
                                        // mint was exactly this, and the file
                                        // derives.
                                        let g = if cur_tm.is_none() {
                                            Gap::NoEndpoint
                                        } else {
                                            Gap::Iota(*name)
                                        };
                                        step!(Ev::missing(g));
                                        cur_tm = None;
                                        stack_tms =
                                            stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                                    }
                                }
                                cur = next;
                                stack = stack[major_pos + 1..].to_vec();
                                continue
                            }
                        }
                        // **The major is reduced *with* its certificate.**
                        //
                        // A redex whose major premise is spelled through an
                        // abbreviation — `Arec … Amk0` where `Amk0 := Aux.a0` —
                        // reaches its constructor only by δ, and every ι route
                        // has to read the fields off a constructor
                        // *application*. This used to be an acceptance-only
                        // `whnf` and each arm below then carried a
                        // `major2 == major` guard, so a major that moved took
                        // the `Err(None)` arm and the whole redex was filed
                        // `iota(T.rec)` — the underlying constructor certifying
                        // and its abbreviation not. That is not a spelling the
                        // aux encoding can avoid: an installed `A.rec`'s minors
                        // *must* mention `A.aB`, or the constant is the wrong
                        // one.
                        //
                        // The conversion the guard was standing in for is
                        // `mconv`, and [`Checker::spine_cong`] is what puts it
                        // in front of the rule. `whnf_conv` with the major's
                        // own interpretation costs a certificate only where one
                        // was being tracked: handed `None` it is the same walk
                        // the acceptance-only `whnf` was.
                        let major_tm = stack_tms.get(major_pos).cloned().flatten();
                        let (major2, mconv) = self.whnf_conv(&major, major_tm, why)?;
                        let (head, con_args) = get_app(&major2);
                        let mut fired = None;
                        if let Expr::Const(f, _) = &head.view() {
                            if let Some((_, rhs)) = rules.iter().find(|(c, _)| c == f) {
                                // **The constructor's own parameter count, not
                                // the recursor's.** They agree for every
                                // recursor whose rules are its own type's
                                // constructors, which is every recursor mini
                                // had before nesting; a *nested* recursor's
                                // rules are another type's, and `Tree.rec_1`
                                // (`numParams = 0`) reduces on `List.cons`
                                // (`numParams = 1`). Lean's own kernel takes
                                // the rule's `nfields` from the *end* of the
                                // constructor's arguments for exactly this
                                // reason; the owner's parameter count is that
                                // number, read from the environment rather than
                                // carried on the rule.
                                let cnp = self
                                    .environment()
                                    .owner(f)
                                    .and_then(|o| self.environment().get(o))
                                    .and_then(|ci| match ci {
                                        ConstantInfo::Inductive { num_params, .. } => {
                                            Some(*num_params as usize)
                                        }
                                        _ => None,
                                    })
                                    .unwrap_or(np);
                                let fields = slice(&con_args, cnp, con_args.len());
                                let mut args = stack[..np + nmot + nm].to_vec();
                                args.extend(fields);
                                let rhs = instantiate_lparams(rhs, lparams, ls)?;
                                fired = Some((*f, substs(&rhs, &args, 0)));
                            }
                        }
                        if let Some((cname, rhs)) = fired {
                            // **Iota, the derived route.** The eliminator's own
                            // ι theorem is in the store; what a use site lacks
                            // is `PRE` at *its* minors and the name the nest
                            // bottom was bound to. [`crate::iota_dep`] is both,
                            // and it returns the whole spine's equation
                            // composed — so the consumed arguments come off
                            // `stack_tms` first and this is **one** `step!`,
                            // not one per level.
                            // The spine the *rule* is stated at: the major is
                            // its reduct, on both axes. `all_tms` is `None`
                            // unless the major's own reduction was certified,
                            // because an ι theorem about a term this run cannot
                            // name is a theorem about the wrong redex.
                            let mut all = stack[..major_pos + 1].to_vec();
                            all[major_pos] = major2;
                            let all_tms: Option<Vec<Term>> = stack_tms
                                .get(..major_pos + 1)
                                .and_then(|s| s.iter().cloned().collect::<Option<Vec<Term>>>())
                                .and_then(|mut ts| {
                                    ts[major_pos] = mconv.ev.eq_rhs()?;
                                    Some(ts)
                                });
                            let empty = std::collections::HashMap::new();
                            let inst: Option<Vec<u32>> =
                                ls.iter().map(|l| crate::ground::eval(l, &empty)).collect();
                            // **A nested declaration's rules are its model's
                            // theorems**, and the membership that says so is
                            // the same one `zoneb::ensure` routes its
                            // *interpretation* on. Read here rather than in a
                            // guard because it needs `&mut self` for the
                            // apparatus, which a pattern guard may not take.
                            // See [`crate::iota_model`] for why this is a
                            // sibling of `iota_dep` and not a widening of its
                            // arity check.
                            let modelled = crate::iota_model::selects(self, name);
                            let attempt = match (cur_tm.clone(), all_tms, inst) {
                                // **`Quot.lift` is a `Recursor` and its ι is
                                // not an inductive one.** `add_quot` classifies
                                // it here, so it arrives at this site with
                                // `iota_dep`'s route — which is about
                                // `DepRecursor::iota` — having nothing to say
                                // about it. [`crate::quot_iota`] is its own
                                // route, over `derived::quot::lift_beta`, and
                                // it returns the same one composed equation
                                // about the whole spine for the same reason.
                                (Some(h), Some(ts), Some(inst))
                                    if crate::quot::prim_for(name)
                                        == Some(crate::quot::Prim::Lift) =>
                                {
                                    crate::quot_iota::fire(self, &inst, &h, &all, &ts, &con_args)
                                        .map_err(Some)
                                }
                                // **`Acc.rec` is an indexed family that has no
                                // `IndexedDepRecursor`.** `Acc` takes
                                // [`crate::direct::clause_for`], so its
                                // eliminator is `derived::rec_acc`'s `pack` and
                                // its ι is `pack_iota` — a different theorem
                                // from `iota_ix_dep`'s, and the arm below would
                                // decline for it. The split is made here, off
                                // the clause, so that neither module has to
                                // decline for the other; `118`'s twelve gapped
                                // conversions were all this arm choosing the
                                // wrong table. See [`crate::rec_acc_iota`].
                                (Some(h), Some(ts), Some(inst))
                                    if self
                                        .environment()
                                        .owner(name)
                                        .and_then(crate::direct::clause_for)
                                        == Some(crate::direct::Clause::Acc) =>
                                {
                                    let rty = instantiate_lparams(cinfo.ty(), lparams, ls)?;
                                    crate::rec_acc_iota::fire(
                                        self, name, &inst, &rty, &h, &all, &ts, &con_args,
                                        &rhs,
                                    )
                                    .map_err(Some)
                                }
                                // **A nested declaration has no class-(T)
                                // carrier**, so neither `DepRecursor::iota` nor
                                // `IndexedDepRecursor::iota` exists for it and
                                // both arms below would decline. Its `⟦T.rec_k⟧`
                                // is a model's, keyed by
                                // `crate::nested_splice::recognise`, and its rules
                                // are that model's proved theorems — cashed by
                                // [`crate::iota_model`], whose header says why
                                // widening `iota_dep`'s arity check instead
                                // would make one arm answer for two shapes.
                                (Some(h), Some(ts), Some(inst)) if modelled => {
                                    crate::iota_model::fire(
                                        self, name, &inst, ls, &h, &all, &ts, &cname,
                                        &con_args, &rhs,
                                    )
                                    .map_err(Some)
                                }
                                // **An indexed family is a different table.**
                                // `IndexedDepRecursor::iota` is not
                                // `DepRecursor::iota` and the two rules differ
                                // in their antecedent's order, in what a
                                // recursive atom says and in what the Lean
                                // right-hand side spells — see
                                // [`crate::iota_ix_dep`]. The split is made
                                // here, off `num_indices`, so that neither
                                // module has to decline for the other.
                                (Some(h), Some(ts), Some(inst)) if *num_indices != 0 =>
                                {
                                    let rty = instantiate_lparams(cinfo.ty(), lparams, ls)?;
                                    crate::iota_ix_dep::fire(
                                        self,
                                        name,
                                        &inst,
                                        &rty,
                                        np,
                                        nm,
                                        *num_indices as usize,
                                        &h,
                                        &all,
                                        &ts,
                                        &cname,
                                        &con_args,
                                        &rhs,
                                    )
                                    .map_err(Some)
                                }
                                (Some(h), Some(ts), Some(inst)) => {
                                    let rty = instantiate_lparams(cinfo.ty(), lparams, ls)?;
                                    crate::iota_dep::fire(
                                        self, name, &inst, &rty, np, nm, &h, &all, &ts, &cname,
                                        &con_args, &rhs,
                                    )
                                    .map_err(Some)
                                }
                                // Nothing to state the rule *about*: the
                                // head's interpretation, one argument's, or a
                                // ground level was absent — including the case
                                // where the major reduced and its own
                                // conversion did not certify, which is what
                                // makes `all_tms` `None`. `Err(None)`: **no
                                // route ran**, so there is no sub-result whose
                                // reason to carry, and the clause's own label
                                // is the honest one.
                                _ => Err(None),
                            };
                            stack = stack[major_pos + 1..].to_vec();
                            match attempt {
                                Ok((leg, to_tm)) => {
                                    // The rule is stated at the reduct, so the
                                    // major's own conversion goes in front of
                                    // it — refl and free when the major was
                                    // already the constructor application.
                                    let leg = if major2 == major {
                                        Ev::Proved(leg)
                                    } else {
                                        let head_tm = cur_tm.clone();
                                        let pre_tms =
                                            stack_tms[..major_pos + 1].to_vec();
                                        let pre = match head_tm {
                                            Some(h) => self.spine_cong(
                                                h,
                                                &pre_tms,
                                                major_pos,
                                                mconv.ev.clone(),
                                            ),
                                            None => Ev::missing(Gap::NoEndpoint),
                                        };
                                        self.ev_trans(pre, Ev::Proved(leg), "iota-major")
                                    };
                                    stack_tms =
                                        stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                                    step!(leg);
                                    cur_tm = Some(to_tm);
                                }
                                Err(sub) => {
                                    // **No interpretation was being tracked,
                                    // so there is no ι question** — the K-rule
                                    // branch's own argument, made at its `None`
                                    // arm above, which this branch was not
                                    // making.
                                    // Instrumented over all 91 exports with
                                    // `iota_dep` wired: **72** mints, of which
                                    // **67** are this case and 5 are a real
                                    // demand (`RBTree.rec` in `077`, which is
                                    // construction 3). A census that counted
                                    // the 67 over-stated the ι population by a
                                    // factor of thirteen, and Vera's "2 at the
                                    // K-rule" was the same artefact caught
                                    // once already.
                                    //
                                    // **`sub` first, and that is §0.4.** The
                                    // four routes each decline with a reason of
                                    // their own — `iota_dep`'s and
                                    // `quot_iota`'s are `Gap::Recursor` with
                                    // the step that refused — and this arm used
                                    // to throw all four away and mint `Iota`
                                    // regardless, so the published ι census
                                    // measured *this label* rather than the
                                    // sub-results'. Measured on the arena
                                    // corpus: `alg-conv-trans-quot-right` read
                                    // `waiting:iota(Quot.lift)=1` and now reads
                                    // `waiting:recursor(Quot.lift: quotient
                                    // iota: the redex's arity or its levels
                                    // disagree)=1`. The **totals** do not move
                                    // — both are `Cause::Threading` — which is
                                    // the point: what was wrong was the
                                    // attribution.
                                    let g = if cur_tm.is_none() {
                                        Gap::NoEndpoint
                                    } else {
                                        sub.unwrap_or(Gap::Iota(*name))
                                    };
                                    step!(Ev::missing(g));
                                    cur_tm = None;
                                    stack_tms =
                                        stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                                }
                            }
                            cur = rhs;
                            continue
                        }
                        let mut stack2 = stack.clone();
                        stack2[major_pos] = major2;
                        // **Stuck, but the major reduced under it — and that
                        // reduction is certified.** The expression changed, so
                        // the certificate owes a congruence over the change,
                        // and `mconv` is exactly it.
                        //
                        // *(Rewritten. This read "the major's own reduction is
                        // not threaded (it is the acceptance-only `whnf`
                        // above), so this is a named absence", and minted
                        // [`Gap::StuckRecursor`]. It was true when it was
                        // written and stopped being true when the `whnf` above
                        // became `whnf_conv`: the ι arm forty lines up already
                        // composes `mconv` through [`Checker::spine_cong`], and
                        // this arm kept declining for a reason that had been
                        // repaired underneath it. The evidence it cited —
                        // "instrumented over all 91 exports this branch mints
                        // `0`" — is the reason nobody noticed: no corpus
                        // declaration reaches it. `nested_model.ndjson` reaches
                        // it 3 214 times.)*
                        //
                        // **One congruence at the major's position, not one per
                        // argument.** `spine_cong` moves the single argument
                        // that changed and holds the rest at `eq_refl`;
                        // composing per-argument down the whole spine is the
                        // `ConvCompose` trap `MINI-HANDOFF.md` §8 is about. The
                        // consumed prefix then comes off `stack_tms` so that
                        // `step!`'s own lift covers the tail and nothing is
                        // lifted twice — the ι arm's split, at the arm that
                        // does not fire.
                        if stack2[major_pos] != stack[major_pos] {
                            let head_tm = cur_tm.clone();
                            let pre_tms =
                                stack_tms.get(..major_pos + 1).map(<[_]>::to_vec);
                            let leg = match (head_tm, pre_tms) {
                                (Some(h), Some(ts)) => {
                                    self.spine_cong(h, &ts, major_pos, mconv.ev.clone())
                                }
                                // No interpretation for the head or a consumed
                                // argument: §0.4 says the reason is the missing
                                // sub-result's, not this clause's label.
                                _ => Ev::missing(Gap::NoEndpoint),
                            };
                            stack_tms =
                                stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                            step!(leg);
                            // **No `cur_tm` update, and it is a redundant store
                            // rather than a missing term.** The question is
                            // worth settling because on this arm a term that
                            // never reaches the caller is the shape of four
                            // defects already fixed here; the answer is in the
                            // types. `done!` takes an **`E`** — `app_n(node,
                            // &stack2)` is the reduct *expression* — and
                            // `whnf_conv` returns `(E, Conv)`, so the only
                            // term-valued thing that leaves this function is
                            // `acc.ev`'s right endpoint. `cur_tm` is loop-local
                            // state for the *next* iteration's `split_app` /
                            // `beta_evidence` / `subject_of`, and this arm falls
                            // straight into `done!` and returns.
                            //
                            // So `⟦app_n(node, stack2)⟧` travels in `leg`, which
                            // `step!` has just composed into `acc`. That it is
                            // the *right* term is not taken on trust: the two
                            // mutations `stuck-no-split` and `stuck-head-leg`
                            // both make it wrong and both are caught, loudly, as
                            // `mini-bug` with `conv-compose(trans)`.
                            //
                            // A draft assigned `leg.eq_rhs()` here under a
                            // comment claiming `cur_tm` named the applied
                            // prefix. Clippy called the store dead; it was, and
                            // the comment was the misleading half.
                        }
                        done!(app_n(node, &stack2))
                    }
                    done!(app_n(node, &stack))
                }
                Expr::App(f, a) => {
                    // Peeling an application is not a reduction: no leg. What
                    // it costs is taking `⟦f a⟧ = app(⟦f⟧,⟦a⟧)` apart, which is
                    // one lookup in the applicative structure the
                    // interpretation recorded on the way in.
                    let (f_tm, a_tm) = self.split_app(&cur_tm);
                    stack.insert(0, *a);
                    stack_tms.insert(0, a_tm);
                    cur_tm = f_tm;
                    cur = *f;
                }
                Expr::Lam { ty, body } if !stack.is_empty() => {
                    let (ty, body) = (*ty, *body);
                    let a = stack.remove(0);
                    let a_tm = stack_tms.remove(0);
                    // **Beta.** `beta_leg` takes the argument's membership as a
                    // parameter; acquiring it is the caller's job, and here the
                    // caller is `beta_premise`, which reads a `bvar`'s typing
                    // off the scope stack and infers anything else forward.
                    // nanoda's `local_premises` reconstructs this by scanning
                    // for `Local` nodes; mini has nothing to reconstruct.
                    let (leg, to_tm) = self.beta_evidence(&cur_tm, &ty, &a, &a_tm);
                    step!(leg);
                    cur_tm = to_tm;
                    cur = subst(&body, &a);
                }
                Expr::Let { val, body, .. } => {
                    // **Zeta is reflexivity.** `⟦let x := v in b⟧` is *defined*
                    // as `⟦b[v]⟧` (§7), so the two sides are the same `Term`
                    // and there is no leg to compose at all.
                    cur = subst(body, val);
                }
                Expr::Proj { ind, idx, s } => {
                    // `⟦s⟧` is **peeled off `cur_tm`**, not inferred:
                    // [`crate::proj_data::subject_of`] says why the obvious
                    // route does not terminate in practice. It is computed
                    // *before* the reduction below because it is what decides
                    // whether that reduction is the certified one or the
                    // acceptance-only one — they are the same call.
                    let s_tm = match (cur_tm.clone(), *idx) {
                        (Some(t), j) => self
                            .th
                            .as_mut()
                            .and_then(|th| crate::proj_data::subject_of(th.ip, j as usize, &t)),
                        _ => None,
                    };
                    // **The subject reduces *with* its certificate.**
                    //
                    // A projection whose subject is already a constructor
                    // application is the easy case, and it was the only one
                    // this arm certified. Lean's structural-recursion compiler
                    // never emits that case: `Nat.brecOn` is
                    // `(Nat.brecOn.go …).1` and `Nat.add`'s step case projects
                    // out of a `Nat.below`-typed variable, so the subject has
                    // to move before a constructor is in head position. The
                    // equation `⟦s⟧ = ⟦s₂⟧` is what
                    // [`crate::proj_data::iota`] now composes in front of its
                    // computation rule.
                    //
                    // **The subject is reduced once.**
                    //
                    // *(Rewritten, and the previous arrangement is the finding.
                    // This arm read the shape off an acceptance-only
                    // `self.whnf(s)` and then, on the firing path only, re-ran
                    // the **same reduction of the same subject** through
                    // `whnf_conv(s, s_tm, …)` to obtain its certificate —
                    // guarded by `s_tm.is_some() && s2 != *s`, so the doubling
                    // fired precisely when the reduction was non-trivial. A
                    // projection nest is `2^depth` in that guard, and Lean's
                    // structural-recursion output is nothing but projection
                    // nests: `Nat.brecOn` is `(Nat.brecOn.go …).1`, and a
                    // transport over a round trip is a recursor whose subject
                    // is a recursor. The two calls also needed an `s2b == s2`
                    // agreement check between them, which is a check that only
                    // existed because the work was done twice.)*
                    //
                    // **`whnf_conv` with `s_tm` `None` *is* the acceptance-only
                    // `whnf`** — the same loop with the certificate legs not
                    // built (see [`Checker::whnf`]) — so the acceptance walk
                    // pays exactly what it paid before, and only a walk that
                    // was already tracking `⟦s⟧` reaches the certified form.
                    //
                    // What that moves is the trade this arm's header used to
                    // record: paying for a certificate at every *stuck*
                    // projection took `077_RBTree.id_spec` from 0.6 s to over
                    // two minutes on the first draft, and one reduction means
                    // the stuck path is now on the certified side of the fork
                    // whenever `cur_tm` is `Some`. `077` is the guard for that
                    // and is measured on every change to this arm.
                    //
                    // **The three stuck exits below compose that reduction
                    // too**, and `stuck!` is where they do it.
                    //
                    // *(Rewritten, and the previous arrangement is the finding.
                    // They `done!`d a *changed* expression — `stuck` carries
                    // `s2`, not `s` — without composing any leg, so `acc.ev`'s
                    // right-hand side named the **unreduced** subject while
                    // `acc.to` named the reduced one: this function's contract,
                    // broken silently, where the recursor arm's version of the
                    // same defect at least minted `Gap::StuckRecursor` until
                    // `77f4d55` repaired it. The observed consequence was
                    // `proj_data::proj_congr`'s endpoint check — it built
                    // `⊢ πⱼ(⟦s₂⟧) = πⱼ(⟦s₂⟧)` **successfully**, matched neither
                    // of the caller's endpoints, both of them stated at folded
                    // spellings the walk had already reduced past, and threw
                    // the theorem away. Measured on `nat_char_equations`: six
                    // pairs, all six with `s1` and `s2` the identical
                    // expression and `a_tm ≠ b_tm`.)*
                    let (s2, s_conv) = self.whnf_conv(s, s_tm.clone(), &Gap::NoEndpoint)?;
                    let stuck =
                        crate::expr::proj(*ind, *idx, s2);
                    // A subject that did not move owes nothing: the two
                    // endpoints are the same term and the leg would be a `refl`
                    // this chain does not need. That is also the only case the
                    // old arrangement was right about.
                    macro_rules! stuck {
                        () => {{
                            if s2 != *s {
                                let leg = match self.ip() {
                                    Some(ip) => crate::proj_data::stuck_leg(
                                        ip,
                                        *idx as usize,
                                        &s_conv.ev,
                                    ),
                                    None => Ev::missing(Gap::SymbolicLevel),
                                };
                                step!(leg);
                            }
                            done!(app_n(stuck.clone(), &stack))
                        }};
                    }
                    let (head, args) = get_app(&s2);
                    let Expr::Const(f, cls) = &head.view() else { stuck!() };
                    let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind)
                    else {
                        stuck!()
                    };
                    if ctors.len() != 1 || &ctors[0] != f {
                        stuck!()
                    }
                    let pos = (*num_params + *idx) as usize;
                    if pos >= args.len() {
                        return Err(format!(
                            "Type error during reduction: projection index {} out of bounds for {s2}",
                            idx + 1
                        ))
                    }
                    // **Proj-of-ctor**, and `crate::proj_data::iota` is the
                    // computation fact: `πⱼ(ctor₀(y⃗)) = yⱼ`, unconditional,
                    // composed with `beta_spine` down `⟦T.mk⟧`'s own nest.
                    //
                    // `cur` stays a **subterm of the input** — `args[pos]` —
                    // which every other arm of this loop preserves and which is
                    // what decided the projection's route: reading `proj i s`
                    // as `T.rec (λ_. βᵢ) (λ y⃗. yᵢ) s` would put an expression
                    // here that this `Expr` never contained.
                    let (ind2, idx2) = (*ind, *idx);
                    let np2 = *num_params as usize;
                    let ctor_n = *f;
                    // The constructor's own ground levels: a structure's
                    // constructor has the declaration's level parameters, so
                    // this is the key `IndApparatus::decls` holds it under.
                    let empty = std::collections::HashMap::new();
                    let cinst: Option<Vec<u32>> =
                        cls.iter().map(|l| crate::ground::eval(l, &empty)).collect();
                    // The subject's reduction certificate, from the one
                    // reduction above. A subject that is already the
                    // constructor application needs no equation, which is the
                    // case the old `s2 == s` guard admitted and the only one it
                    // admitted; `None` there keeps `proj_data::iota`'s
                    // composition off a `refl` it does not need.
                    let s_red = if s2 != *s { s_conv.ev.thm().cloned() } else { None };
                    let ev = if cinst.is_some() {
                        match crate::proj_data::iota(
                            self,
                            &ind2,
                            &ctor_n,
                            &cinst.clone().expect("checked"),
                            idx2 as usize,
                            s_tm.clone(),
                            &args,
                            np2,
                            s_red.as_ref(),
                        ) {
                            Ok((thm, to)) => {
                                cur_tm = Some(to);
                                Ev::Proved(thm)
                            }
                            Err(g) => {
                                cur_tm = None;
                                Ev::missing(g)
                            }
                        }
                    } else {
                        // A symbolic level on the constructor: there is no
                        // ground key for `IndApparatus::decls` to be read at,
                        // which is `SymbolicLevel` and not this clause's label.
                        cur_tm = None;
                        Ev::missing(Gap::SymbolicLevel)
                    };
                    step!(ev);
                    cur = args[pos];
                }
                Expr::NatLit(n) => {
                    // Note the original drops `stack` on this branch — a nat
                    // literal is never in head position of an application.
                    //
                    // **The unfolding is reflexivity, and now it is reflexivity
                    // at the term level too.** §7's choice of `⟦natLit n⟧` is
                    // the interpretation of this very expansion
                    // ([`Checker::nat_unfold`]), so `⟦natLit n⟧` and
                    // `⟦Nat.succ (natLit (n-1))⟧` are the *same* term and this
                    // step owes no `step!` at all.
                    //
                    // *(This comment read "what is missing is `Nat`'s
                    // interpretation, which is what `cur_tm` being `None`
                    // already says." `Nat` is an ordinary inductive and has
                    // translated for some time; what was missing was the
                    // literal's own clause, and the label said `Nat` because
                    // the literal's declared type is `Nat`.)*
                    done!(Self::nat_unfold(*n)?)
                }
                _ => done!(app_n(node, &stack)),
            }
        }
    }

    /// `⟦f a⟧ = app(⟦f⟧,⟦a⟧)`, split back into its two halves.
    ///
    /// `None` on both when the application interprets to `•` — it is a *proof*,
    /// and §6.2's left column has no `app` to take apart. A reduction inside a
    /// proof is related to its reduct by proof irrelevance, not by congruence,
    /// so the honest answer here is an absence.
    fn split_app(&mut self, tm: &Option<Term>) -> (Option<Term>, Option<Term>) {
        let Some(t) = tm else { return (None, None) };
        let Some(ip) = self.th.as_ref().map(|th| &*th.ip) else { return (None, None) };
        let ap = ip.prelude.ap.app;
        match ip.parts_of(t) {
            Some((f, args)) if f == ap && args.len() == 2 => {
                (Some(args[0].clone()), Some(args[1].clone()))
            }
            _ => (None, None),
        }
    }

    /// **Reducing a proof is reflexivity** — `Γ ⊢ ⟦e⟧ = ⟦whnf e⟧` when both
    /// sides are `•`, which is the whole certificate a proof-valued reduction
    /// owes.
    ///
    /// # The residual this closes, and what it was mistaken for
    ///
    /// §6.2 sends a proof-valued application to `•`, so [`Checker::split_app`]
    /// — which peels `app(⟦f⟧,⟦a⟧)` — hands back `None`/`None` on it and every
    /// endpoint after the first `App` node of a proof-valued spine is gone.
    /// The walk then gives up at whichever step comes next: `delta_evidence`'s
    /// first line, `beta_evidence`'s, the stuck-recursor arm's `spine_cong`
    /// inputs. **None of those is the defect** — each is correctly reporting an
    /// absence decided upstream — and the absence itself is not one either:
    /// `⟦e⟧` and `⟦whnf e⟧` are the *same term*, so the walk never needed an
    /// endpoint to carry. It needed to notice that it was reducing a proof.
    ///
    /// This is `eq_cash`'s "the endpoint loss inside `whnf_conv` on a
    /// proof-valued spine", recorded there as open and unreachable. It is
    /// reachable: `nested_model`'s `iotaNode` is `transportNode` applied at
    /// `congrPack (unpack (pack l)) l (unpackPack l)`, whose `Eq.rec` reduces
    /// its **major** — a proof — through [`Checker::whnf_conv`], and the three
    /// spines that lose their endpoint there are `congrPack …`,
    /// `packUnpack (pack l)` and `unpackPack l`.
    ///
    /// # Why the reduct is interpreted rather than assumed
    ///
    /// A proof's whnf is a proof, but a proof's *interpretation* is `•` only
    /// when §6.2's proof clause fires — at an application or a λ. A proof that
    /// reduces to a **scope variable** interprets to that scope's term and one
    /// that reduces to a bare **constant** to the stored symbol; both are
    /// *equal* to `•` by proof irrelevance ([`Interp::point_of_proof`], which
    /// is what `crate::eq_cash` uses for exactly this) and neither is `•` on
    /// the nose. So the reduct's own term is read and compared, and a reduct
    /// that is not `•` keeps the walk's gap rather than acquiring a theorem
    /// about the wrong term.
    ///
    /// # Where it is asked, and what that costs
    ///
    /// At `done!`, and **only when the walk's conversion is already a gap**.
    /// A reduction that threaded has its certificate and this must not replace
    /// it; a reduction that never had an endpoint (`from_tm` is `None`) fails
    /// the first test in one comparison. What is left is the proof-valued walk
    /// that gave up, where the cost is one `infer_type` of a term the caller is
    /// about to infer anyway — [`Checker::infer_type`]'s frame cache is what
    /// makes that the second lookup rather than the second inference.
    ///
    /// `infer_type` returning `Err` is **not** propagated: this is a repair on
    /// a path that is already gapping, and turning a gap into a rejection would
    /// move acceptance. It answers `None` and the gap stands.
    ///
    /// # What the tests kill, measured
    ///
    /// Five mutations, against `whnf_of_a_proof`, `nested_model`'s ι table, the
    /// tutorial corpus's ledger and conversion split, and
    /// [`the_proof_point_leg_refuses_a_reduct_that_is_not_the_point`]:
    ///
    /// ```text
    /// KILLED   delete the leg
    /// KILLED   drop the `from_tm == •` guard
    /// KILLED   drop the `⟦to⟧ == •` check
    /// KILLED   state the reflexivity at some other term
    /// SURVIVED drop the `acc.ev.gap().is_some()` guard
    /// ```
    ///
    /// Two of them are worth their notes.
    ///
    /// **`drop the from_tm guard` needed the corpus.** Against the four fast
    /// tests it survived; it dies on `tutorial_evidence_ledger` and
    /// `tutorial_conversion_split`, which is the honest reading of a guard whose
    /// occupant is "a walk that was tracking *something else*". The `None` half
    /// of it is unobservable by construction — a walk handed no endpoint has no
    /// consumer for the `Ev` — and the unit test asserts it anyway, because a
    /// property with no observer is exactly what a unit test is for.
    ///
    /// **The survivor is an equivalent mutant and is reported rather than
    /// excused.** Removing the gap guard makes the leg run on walks that
    /// *already* produced a certificate — but only where `from_tm` and `⟦to⟧`
    /// are both `•`, and there the certificate it replaces proves the same
    /// formula `• = •`. Nothing downstream can tell them apart. What the guard
    /// buys is not correctness but cost: without it every threaded proof-valued
    /// reduction in the run pays an extra `infer_type` of its reduct, and the
    /// conversion counters do not see that.
    fn proof_point_leg(&mut self, from_tm: &Option<Term>, to: &E) -> Option<Ev> {
        let point = self.ip()?.point();
        if from_tm.as_ref() != Some(&point) {
            return None
        }
        let to_tm = self.infer_type(to).ok()?.tm?;
        (to_tm == point).then(|| Ev::Proved(kernel::Thm::eq_refl(point)))
    }

    /// **Delta**'s leg: `⊢ ⟦c.{σ}⟧ = ⟦val[σ]⟧`, and the reduct's own
    /// interpretation, both from the store.
    ///
    /// The equation is the defining axiom minted when the declaration was
    /// checked — already proved, `Sealed`, hypothesis-free, so weakening it
    /// into `Γ` is free. There is no delta-graph search: a store miss is a
    /// named absence.
    fn delta_evidence(
        &mut self,
        name: &Name,
        ls: &[Level],
        cur_tm: &Option<Term>,
    ) -> (Ev, Option<Term>) {
        if cur_tm.is_none() {
            return (Ev::missing(Gap::NoEndpoint), None)
        }
        let empty = std::collections::HashMap::new();
        let Some(inst) =
            ls.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<Vec<u32>>>()
        else {
            return (Ev::missing(Gap::SymbolicLevel), None)
        };
        // **The store's own reason, not a bare `no-interp` on the name.** This
        // is the same call `const_evidence` makes and it was missing here; see
        // [`Checker::miss_reason`] for what that cost.
        if let Some(g) = self.miss_reason(name, &inst) {
            return (Ev::missing(g), None)
        }
        let Some(th) = self.th.as_ref() else { return (Ev::missing(Gap::SymbolicLevel), None) };
        let Some(c) = th.ip.get_const(&(*name, inst.clone())) else {
            return (Ev::missing(Gap::NoInterpretation(*name, inst)), None)
        };
        match &c.defeq {
            Some(s) => {
                let thm = s.thm().clone();
                let rhs = thm.concl().as_eq().map(|(_, b)| b);
                (Ev::Proved(thm), rhs)
            }
            None => (Ev::missing(Gap::NoDefiningEquation(*name)), None),
        }
    }

    /// **Beta**'s leg: `Γ ⊢ ⟦(λ x:A. b) a⟧ = ⟦b[a]⟧`, and `⟦b[a]⟧`.
    ///
    /// `cur_tm` is `⟦λ x:A. b⟧ = lam(h⃗,⟦A⟧)`, which names the graph symbol,
    /// which names the site — so the skeleton is *recovered*, not recomputed.
    fn beta_evidence(
        &mut self,
        cur_tm: &Option<Term>,
        lam_ty: &E,
        arg: &E,
        arg_tm: &Option<Term>,
    ) -> (Ev, Option<Term>) {
        let (Some(lam_t), Some(a_tm)) = (cur_tm.clone(), arg_tm.clone()) else {
            return (Ev::missing(Gap::NoEndpoint), None)
        };
        let Some((site, dom)) = self.th.as_ref().and_then(|th| th.ip.as_lam(&lam_t)) else {
            return (Ev::missing(Gap::NotDecomposable), None)
        };
        let arg_mem = match self.beta_premise(lam_ty, &dom, arg, &a_tm) {
            Ok(m) => m,
            Err(e) => return (Ev::missing(e), None),
        };
        let Some(ip) = self.ip() else { return (Ev::missing(Gap::SymbolicLevel), None) };
        let ev = crate::conv::beta_leg(ip, &site, dom, a_tm.clone(), &arg_mem);
        // …and then off the body symbol onto `⟦b[a]⟧` itself.
        let unfold = match ip.body_unfold(&site, a_tm) {
            Some(t) => Ev::Proved(t),
            None => Ev::missing(Gap::Skeleton),
        };
        let ev = self.ev_trans(ev, unfold, "beta-unfold");
        let to = ev.eq_rhs();
        (ev, to)
    }

    /// **The ι certificate for a recursor mini *interprets* rather than
    /// derives** — `Γ ⊢ ⟦T.rec ā⟧ = ⟦rhs⟧`, by β down the stored eliminator's
    /// own λ-nest.
    ///
    /// # Why this is a whole clause and not a shortcut
    ///
    /// `thesis.txt:2124` gives the equality recursor an **interpretation**,
    /// `⟦rec=_a e b h⟧γ = ⟦e⟧γ`, with the reduction at `:796`. Under that clause
    /// there is no recursor set, no ι *theorem* and no premise: `⟦Eq.rec⟧`'s
    /// stored λ-nest has the minor itself at its bottom
    /// ([`crate::recursor`]'s `eq_bottom`), so applying it to the six arguments
    /// **is** the reduction, and the certificate is the β chain the
    /// interpretation already supports. That is why this route has no side
    /// condition and the derived one does: `DepRecursor::iota` is
    /// `PRE → …`, and `PRE` is a fact about the minors that has to be
    /// re-established at whatever terms a use site supplies.
    ///
    /// It also means **the K-rule is covered for free**. Lean's ι computes only
    /// on `Eq.refl`; this equation holds at *any* major premise, because β does
    /// not look at one. The two are consistent because the nest's bottom typing
    /// already carried `t` to `•` by `Props::eq_sound` — the soundness argument
    /// is spent once, where the eliminator is built, and not again per
    /// reduction.
    ///
    /// # What is checked
    ///
    /// The chain's endpoint is compared against `⟦rhs⟧` **inferred**, because
    /// `whnf`'s contract is that `cur_tm` is the interpretation of `cur`: a
    /// nest whose bottom is not the ι right-hand side would otherwise hand the
    /// next step a certificate about a different term. A declaration with no
    /// [`crate::direct::Clause`] never reaches here — the derived eliminators'
    /// bottoms are `app(drec, ⟦t⟧)`, which is not any Lean subterm.
    /// Returns **one leg per argument**, in order, and the endpoint — not a
    /// single composed equation. `whnf`'s `step!` lifts each leg over the
    /// arguments still on the stack, so a leg is about the head *applied to one
    /// more argument* and the composition is the caller's, exactly as it is for
    /// an ordinary β. `None` for the endpoint means the route does not apply
    /// and the caller must fall back to a named absence.
    fn nest_iota(
        &mut self,
        head_tm: &Option<Term>,
        rec_ty: &E,
        args: &[E],
        arg_tms: &[Option<Term>],
        rhs: &E,
    ) -> (Vec<Ev>, Option<Term>) {
        if head_tm.is_none() || args.len() != arg_tms.len() {
            return (Vec::new(), None)
        }
        let mut legs = Vec::with_capacity(args.len());
        let mut cur_tm = head_tm.clone();
        let mut ty = *rec_ty;
        for (a, a_tm) in args.iter().zip(arg_tms.iter()) {
            let Expr::Forall { ty: dom_e, body } = &ty.clone().view() else {
                return (legs, None)
            };
            let (leg, to) = self.beta_evidence(&cur_tm, dom_e, a, a_tm);
            let proved = matches!(leg, Ev::Proved(_));
            legs.push(leg);
            cur_tm = to;
            ty = subst(body, a);
            if !proved || cur_tm.is_none() {
                return (legs, None)
            }
        }
        // The endpoint is the ι right-hand side, or this is not that clause.
        let want = self.infer_type(rhs).ok().and_then(|t| t.tm);
        if want != cur_tm {
            return (legs, None)
        }
        (legs, cur_tm)
    }

    /// **The premises a β chain down a stored λ-nest consumes** — one
    /// `Γ ⊢ ⟦aᵢ⟧ ∈ domᵢ` per argument, at the domains the *interpretation*
    /// names.
    ///
    /// # Why this is separate from the chain itself
    ///
    /// [`Interp::beta_spine`](crate::interp::Interp::beta_spine) already walks
    /// a nest and returns the **composed, properly lifted** equation, which is
    /// the shape a single `step!` wants; what it does not do is *acquire* the
    /// memberships, because at its own callers those are scope assumptions
    /// already in hand. At a use site they are not: the arguments are arbitrary
    /// Lean terms and the premise is [`Checker::beta_premise`], per argument —
    /// inference, with a conversion when the inferred type is a different
    /// spelling of the declared domain.
    ///
    /// So this walks the nest once for the premises, and the caller walks it
    /// again for the equation. The alternative — one walk emitting both — would
    /// duplicate `beta_spine`'s `congr` lifting, which is exactly the step the
    /// `ConvCompose` trap in `MINI-HANDOFF.md` §8 is about getting wrong.
    ///
    /// The memberships are also **what `crate::rec_dep`'s `At` wants**: a nest
    /// binder's scope assumption and `⟦a⟧ ∈ ⟦declared domain⟧` are the same
    /// statement, which is why `cx_of`/`minor_at`/`cod_at_rung` need no variant
    /// for a use site.
    /// [`Checker::nest_arg_mems`], **inferring each argument once** and
    /// returning `⟦aᵢ⟧` alongside the membership.
    ///
    /// The `arg_tms` form is the older one and every caller of it built that
    /// vector with an `infer_type` loop of its own, so each argument was
    /// inferred twice: once for its term, once inside
    /// [`Checker::beta_premise`] for its typing. That is invisible on a corpus
    /// of small expressions and is a factor of two *per nest level* on
    /// arguments that are themselves nests — Lean's `brecOn` output, where a
    /// structure's parameters are `below` towers. Measured on
    /// `proj_reduced_carrier`.
    pub(crate) fn nest_arg_typings(
        &mut self,
        head_tm: &Term,
        nest_ty: &E,
        args: &[E],
    ) -> Result<(Vec<Term>, Vec<Thm>), Gap> {
        let mut cur = head_tm.clone();
        let mut ty = *nest_ty;
        let mut tms = Vec::with_capacity(args.len());
        let mut mems = Vec::with_capacity(args.len());
        for a in args {
            let Expr::Forall { ty: dom_e, body } = &ty.clone().view() else {
                return Err(Gap::NotDecomposable)
            };
            let Some((site, dom)) = self.th.as_ref().and_then(|th| th.ip.as_lam(&cur)) else {
                return Err(Gap::NotDecomposable)
            };
            let ta = self.infer_type(a).map_err(|_| Gap::Classifier)?;
            let a_tm = ta.tm.clone().ok_or_else(|| ta.ev.reason(Gap::NoEndpoint))?;
            let mem = self.beta_premise_of(ta, dom_e, &dom)?;
            let Some(thm) = mem.thm().cloned() else { return Err(mem.reason(Gap::NoEndpoint)) };
            mems.push(thm);
            let Some(ip) = self.ip() else { return Err(Gap::SymbolicLevel) };
            let Some(unfold) = ip.body_unfold(&site, a_tm.clone()) else {
                return Err(Gap::Skeleton)
            };
            let Some((_, next)) = unfold.concl().as_eq() else { return Err(Gap::NotDecomposable) };
            cur = next;
            ty = subst(body, a);
            tms.push(a_tm);
        }
        Ok((tms, mems))
    }

    pub(crate) fn nest_arg_mems(
        &mut self,
        head_tm: &Term,
        nest_ty: &E,
        args: &[E],
        arg_tms: &[Term],
    ) -> Result<Vec<Thm>, Gap> {
        if args.len() != arg_tms.len() {
            return Err(Gap::NotDecomposable)
        }
        let mut cur = head_tm.clone();
        let mut ty = *nest_ty;
        let mut out = Vec::with_capacity(args.len());
        for (a, a_tm) in args.iter().zip(arg_tms.iter()) {
            let Expr::Forall { ty: dom_e, body } = &ty.clone().view() else {
                return Err(Gap::NotDecomposable)
            };
            let Some((site, dom)) = self.th.as_ref().and_then(|th| th.ip.as_lam(&cur)) else {
                return Err(Gap::NotDecomposable)
            };
            let mem = self.beta_premise(dom_e, &dom, a, a_tm)?;
            let Some(thm) = mem.thm().cloned() else { return Err(mem.reason(Gap::NoEndpoint)) };
            out.push(thm);
            let Some(ip) = self.ip() else { return Err(Gap::SymbolicLevel) };
            let Some(unfold) = ip.body_unfold(&site, a_tm.clone()) else {
                return Err(Gap::Skeleton)
            };
            let Some((_, next)) = unfold.concl().as_eq() else { return Err(Gap::NotDecomposable) };
            cur = next;
            ty = subst(body, a);
        }
        Ok(out)
    }

    /// **`whnf`'s transport form**: reduce the *type* inside a typing and carry
    /// the subject's membership along it, in one Leibniz step.
    ///
    /// `(Γ ⊢ ⟦x⟧ ∈ ⟦T⟧)  ↦  (Γ ⊢ ⟦x⟧ ∈ ⟦T'⟧)`. This is the composition
    /// nanoda's `ensure_pi` drops and its silent `ty_bridge` leg compensates
    /// for; here it is one rule and it is not optional, because there is
    /// nothing else to fall back on.
    ///
    /// Note where `⟦T⟧` comes from: not a field of `Typing`, but the *set* side
    /// of the evidence's own conclusion. On a `Gap` it is unavailable, and that
    /// is right — a step whose endpoints have no interpretation has no
    /// certificate to build.
    pub fn whnf_typing(&mut self, t: Typing) -> R<(E, Conv, Typing)> {
        let ty_tm = t.ev.mem_set();
        // **The memo, and why it exists at all.** `proj_data::typing` reduces
        // the projection's carrier type here, and on Lean's `brecOn` output
        // that is a *certified ι through a recursor* — about 7 500 conversions.
        // Nothing caches `infer_type`, so one `addN` re-ran it 251 times:
        // 40 271 conversions became 1 936 075, and 4.5 s became 3 m 9 s.
        // Measured on `proj_reduced_carrier`, both ways.
        //
        // **The key is `⟦ty⟧`, and the Lean type is checked on the hit rather
        // than keyed on.** `Rc::as_ptr(&t.ty)` was the first key and it never
        // hit once: `subst` allocates, so the 251 calls carry 251 distinct
        // pointers for structurally identical types — measured, 1 932 801
        // conversions against 1 936 075, i.e. nothing. `Expr` has no `Hash`,
        // so the stored entry carries the `t.ty` it was derived from and a hit
        // is confirmed by structural equality. That check is what makes the
        // memo sound: `whnf` is deterministic in the expression and the
        // environment, and every leg the reduction builds bottoms out in
        // `beta_premise`, whose scope assumptions are read through terms
        // `⟦ty⟧` already fixes. A `Checker` is one `(declaration, σ)`, so
        // nothing here outlives a pair.
        //
        // Only *proved* conversions are kept. A gap is cheap by comparison and
        // caching one would keep it out of `blocker`'s trail on every call but
        // the first, which is the instrument this round already had to repair.
        let hit = ty_tm
            .as_ref()
            .and_then(|tm| self.wt_memo.get(tm))
            .filter(|(from, _, _)| *from == t.ty)
            .map(|(_, ty2, eq)| (*ty2, eq.clone()));
        if let Some((ty2, eq)) = hit {
            let conv = Conv { to: ty2, ev: Ev::Proved(eq.clone()) };
            let ev = t.ev.clone().zip(conv.ev.clone(), |mem, eq| {
                match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::ConvCompose("whnf-typing-retarget")),
                }
            });
            return Ok((ty2, conv, Typing { ty: ty2, tm: t.tm, ev }))
        }
        let why = t.ev.reason(Gap::NoEndpoint);
        let ty_tm2 = ty_tm.clone();
        let (ty2, conv) = self.whnf_conv(&t.ty, ty_tm, &why)?;
        if let (Some(k), Ev::Proved(eq)) = (ty_tm2, &conv.ev) {
            self.wt_memo.insert(k, (t.ty, ty2, eq.clone()));
        }
        let ev = t.ev.clone().zip(conv.ev.clone(), |mem, eq| {
            match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("whnf-typing-retarget")),
            }
        });
        Ok((ty2, conv, Typing { ty: ty2, tm: t.tm, ev }))
    }

    /// `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧` — beta's one premise, **taken** rather than looked for.
    ///
    /// The argument's typing comes from inference, which §0's rule permits:
    /// deterministic, total on well-typed input, producing its evidence as it
    /// goes. For a `bvar` it bottoms out in the scope's stored assumption at
    /// one vector index — the case that is 5 186 of nanoda's `has_type` misses.
    /// If the inferred type's interpretation is already `⟦A⟧` on the nose,
    /// which subject reduction makes the normal case, no conversion is needed
    /// at all.
    fn beta_premise(&mut self, lam_ty: &E, dom: &Term, arg: &E, a_tm: &Term) -> Result<Ev, Gap> {
        let ta = self.infer_type(arg).map_err(|_| Gap::Classifier)?;
        if ta.tm.as_ref() != Some(a_tm) {
            return Err(ta.ev.reason(Gap::NotDecomposable))
        }
        self.beta_premise_of(ta, lam_ty, dom)
    }

    /// [`Checker::beta_premise`] on a typing the caller **already inferred**.
    ///
    /// mini has no `infer_type` cache by design, so an argument inferred twice
    /// is an argument's whole subtree walked twice, and at a nest of arguments
    /// that are themselves nests the factor compounds. That is what this form
    /// exists to avoid at [`Checker::nest_arg_typings`], whose loop holds the
    /// `Typing` it just derived.
    ///
    /// # Holding `⟦a⟧` is *not* holding the inference — measured
    ///
    /// *(This read "Every caller here holds `⟦a⟧`, and holding `⟦a⟧` means it
    /// has already run the inference this used to run again", and
    /// `CERTIFYING-OVERHEAD.md` built fix 1 on that sentence: widen
    /// `whnf_conv`'s `stack_tms` to carry the `Typing` beside `⟦a⟧` and
    /// [`Checker::beta_premise`] collapses into this. It is false at the one
    /// caller that matters. `whnf_conv`'s `App` arm does not infer its
    /// argument: it **peels** `⟦a⟧ out of `⟦f a⟧` with
    /// [`Checker::split_app`], one lookup in the recorded applicative
    /// structure and no typing anywhere. A `Typing` on that stack would have
    /// to be minted at the push, and the pushes outnumber the β steps that
    /// consume them — on `proj_reduced_carrier`, **252 962 `App`-arm pushes
    /// against 119 216 `Lam`-arm β steps**, so paying inference at the push
    /// costs 2.1 arguments inferred for every one it saves. The widening is a
    /// measured regression, not a saving, and the compounding above is real
    /// but is **not** reachable from the reduction stack.
    ///
    /// Where it *is* reachable is across openings: the same 124 534
    /// `beta_premise` calls are only **1 983** distinct α-canonical judgements
    /// (1.6%) and **64 863** distinct ones at their own kernel scope variables
    /// (52%). Nothing a single `whnf_conv` invocation holds can see the first
    /// number; see `CERTIFYING-OVERHEAD.md` §4 for both counters and what does
    /// reach it.)*
    fn beta_premise_of(&mut self, ta: Typing, lam_ty: &E, dom: &Term) -> Result<Ev, Gap> {
        let Some(have) = ta.ev.mem_set() else { return Err(ta.ev.reason(Gap::NoEndpoint)) };
        if have == *dom {
            return Ok(ta.ev)
        }
        // The domains differ syntactically; the conversion is the price, and
        // it is the strictness delta MINI-DESIGN.md §13 risk 2 names.
        //
        // `Lhs::Type`: `ta.ty` is the type `infer_type` just assigned to the
        // argument, so its own type is a sort.
        let conv = self
            .assert_def_eq_as(&ta.ty, Some(have), lam_ty, Some(dom.clone()), Lhs::Type)
            .map_err(|_| Gap::Classifier)?;
        Ok(ta.ev.zip(conv.ev, |mem, eq| {
            match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("beta-arg-retarget")),
            }
        }))
    }

    // ────────────────────────────────────────────────── inferType ──

    pub fn infer_type(&mut self, e: &E) -> R<Typing> {
        let h = hash_expr(e);
        if let Some(t) = self.frame_get(h, e) {
            return Ok(t)
        }
        let t = self.infer_type_inner(e)?;
        self.frame_put(h, e, &t);
        Ok(t)
    }

    /// A hit in the innermost frame, or `None`. Empties the frame first if a
    /// kernel scope was opened behind `lenv`'s back — see [`Frame`].
    fn frame_get(&mut self, h: u64, e: &E) -> Option<Typing> {
        let n = self.th.as_ref().map_or(0, |th| th.scopes.len());
        // **Every path counts.** The first draft took the `map.get(&h)?` early
        // return, which is the *common* miss, so the census reported a hit rate
        // computed over hits plus almost nothing.
        let hit = (|| {
            let f = self.frames.last_mut()?;
            if f.scopes_len != n {
                f.map.clear();
                f.scopes_len = n;
                return None
            }
            f.map.get(&h)?.iter().find(|(k, _)| k == e).map(|(_, t)| t.clone())
        })();
        crate::census::note_frame_cache(hit.is_some());
        hit
    }

    fn frame_put(&mut self, h: u64, e: &E, t: &Typing) {
        // **Only a certificate is kept.** A `Gap` is cheap to re-reach and
        // caching one would keep it out of `blocker`'s trail on every call but
        // the first — `wt_memo`'s policy, and the instrument it had to repair.
        if t.ev.thm().is_none() {
            return
        }
        let n = self.th.as_ref().map_or(0, |th| th.scopes.len());
        let Some(f) = self.frames.last_mut() else { return };
        if f.scopes_len != n {
            f.map.clear();
            f.scopes_len = n;
        }
        let slot = f.map.entry(h).or_default();
        if !slot.iter().any(|(k, _)| k == e) {
            slot.push((*e, t.clone()));
        }
    }

    fn infer_type_inner(&mut self, e: &E) -> R<Typing> {
        match &e.view() {
            Expr::BVar(i) => {
                let ty = self.local_type(*i)?;
                // The typing of a `bvar` is the scope's stored assumption:
                // one vector index, no derivation, nothing acquired.
                Ok(Typing { ty, tm: self.scope_term(*i), ev: self.scope_typing(*i) })
            }
            Expr::Const(name, ls) => {
                let cinfo = self.lookup(name).ok_or_else(|| format!("Unknown constant {name}"))?;
                let ty = instantiate_lparams(cinfo.ty(), cinfo.lparams(), ls)?;
                let (tm, ev) = self.const_evidence(name, ls);
                Ok(Typing { ty, tm, ev })
            }
            Expr::Sort(u) => {
                let ty = sort((*u).succ());
                let n = crate::ground::eval(u, &std::collections::HashMap::new());
                let (tm, ev) = match (n, self.th.as_mut()) {
                    (Some(n), Some(th)) => {
                        let tm = th.ip.sort(n);
                        let ev = match th.ip.sort_typing(n) {
                            Some(t) => Ev::Proved(t),
                            None => Ev::missing(Gap::SortTowerHeight),
                        };
                        (Some(tm), ev)
                    }
                    _ => (None, Ev::missing(Gap::SymbolicLevel)),
                };
                Ok(Typing { ty, tm, ev })
            }
            Expr::App(f, arg) => {
                let tf = self.infer_type(f)?;
                // `whnf_typing`, not `whnf`: the function's membership has to
                // travel to the reduced type. **This is the composition
                // nanoda's `ensure_pi` drops** and its silent `ty_bridge` leg
                // compensates for; here it is one Leibniz step and it is not
                // optional, because there is nothing else to fall back on.
                let (f_ty, _, tf) = self.whnf_typing(tf)?;
                let Expr::Forall { ty, body } = &f_ty.view() else {
                    return Err(format!(
                        "Expected a function type in application of {f} to {arg}, got {f_ty}"
                    ))
                };
                let (ty, body) = (*ty, *body);
                // Which of §6.2's three `Π` clauses the function's type took,
                // read off the interpretation the call above already produced.
                let shape = tf
                    .ev
                    .mem_set()
                    .and_then(|t| self.th.as_ref().and_then(|th| th.ip.as_pi(&t)));
                let dom_tm = shape.as_ref().map(|s| s.dom());
                let ta = self.infer_type(arg)?;
                let arg_ty_tm = ta.ev.mem_set();
                // `Lhs::Type`: `ty` is the domain of `f`'s `Π`-type, so its own
                // type is the sort the `Π` rule read off it.
                let ceq = self.assert_def_eq_as(
                    &ty,
                    dom_tm.clone(),
                    &ta.ty,
                    arg_ty_tm.clone(),
                    Lhs::Type,
                )?;
                let out_ty = subst(&body, arg);
                // The **proof clause**: an application that is a proof
                // interprets to `•`. The classifier reads the type this call
                // has just derived — nothing is re-inferred at this node.
                let tm = if self.body_clause(&out_ty)? == Clause::Prop {
                    self.th.as_ref().map(|th| th.ip.point())
                } else {
                    match (tf.tm.clone(), ta.tm.clone()) {
                        // `⟦f a⟧ = app(⟦f⟧, ⟦a⟧)`, from the two sub-`Typing`s.
                        (Some(f), Some(a)) => self.th.as_mut().map(|th| th.ip.app(f, a)),
                        _ => None,
                    }
                };
                // `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`: the argument's own typing, moved onto the
                // domain the function actually wants. `ty_conv`, and the one
                // place a conversion is *consumed* rather than merely proved.
                let a_mem = if arg_ty_tm.is_some() && arg_ty_tm == dom_tm {
                    ta.ev.clone()
                } else {
                    let back = self.ev_symm(ceq.ev, "app-domain-symm");
                    ta.ev.clone().zip(back, |mem, eq| {
                        match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                            Some(t) => Ev::Proved(t),
                            None => Ev::missing(Gap::ConvCompose("app-arg-retarget")),
                        }
                    })
                };
                // **This node has two classifiers for one clause**, and they
                // are *not* made to agree by a runtime comparison. `tm` is
                // chosen by `body_clause(&out_ty)`; the certificate is chosen
                // by `shape`, read off `⟦type of f⟧` by `as_pi`. Both read
                // Lean's own sorts, so no declaration makes them disagree, and
                // a check for it was measured never to fire across 11 578 061
                // conversions. A guard that fails nothing is not a guard; the
                // obligation the node actually carries is that its certificate
                // composes, and `app_evidence`'s own rules are what carry it.
                let ev = self.app_evidence(shape, &tf, &ta, a_mem);
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Forall { ty, body } => {
                let t1 = self.infer_type(ty)?;
                // The domain's sort, with the membership carried to it. Its
                // witness has a consumer — the `Π` rule below — which is the
                // evidence nanoda drops 33 587 times as `Dropped::BinderSort`.
                let (s1, _, t1) = self.whnf_typing(t1)?;
                let l1 = as_sort(&s1)?;
                let saved = self.open_slot(*ty, t1.tm.clone());
                let w = self.current_var();
                // NB: mini-lean whnfs the codomain's sort *outside* the
                // binder's scope. Mini does it inside, because the certificate
                // for the transport belongs in the `Γ` the binder opened, and
                // the reduct is the same either way: `tb.ty` reduces to a
                // `Sort`, and a sort mentions no local. The fidelity gate
                // (`mini/tests/tutorial.rs`) is what watches that claim.
                let inner = (|c: &mut Self| -> R<(Typing, Level)> {
                    let tb = c.infer_type(body)?;
                    let (s2, _, tb) = c.whnf_typing(tb)?;
                    let l2 = as_sort(&s2)?;
                    Ok((tb, l2))
                })(self);
                let (tb, l2) = match inner {
                    Ok(v) => v,
                    Err(e) => {
                        self.close_slot(saved);
                        return Err(e)
                    }
                };
                let out_ty = sort(Level::imax(l1, l2));
                // **The clause is `l2 == 0`, already computed.** No classifier
                // call: §6.2's `∀` column is exactly a codomain in `Sort 0`.
                let dep = has_bvar_in_proj(body, 0);
                let (tm, ev) = self.pi_evidence(&t1, &tb, w, dep, &l1, &l2);
                self.close_slot(saved);
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Lam { ty, body } => {
                let t1 = self.infer_type(ty)?;
                let (s1, _, t1) = self.whnf_typing(t1)?;
                as_sort(&s1)?;
                let saved = self.open_slot(*ty, t1.tm.clone());
                let w = self.current_var();
                let inner = (|c: &mut Self| -> R<(Typing, bool, Ev)> {
                    let tb = c.infer_type(body)?;
                    // A `λ` is a proof exactly when its body is, decided from
                    // the body's own type under the binder. The witness on the
                    // licensing branch is what the `Prop` rule consumes.
                    let (prop, w_ev) = c.is_prop_ev(&tb.ty)?;
                    Ok((tb, prop, w_ev))
                })(self);
                let (tb, prop, body_ty_ev) = match inner {
                    Ok(v) => v,
                    Err(e) => {
                        self.close_slot(saved);
                        return Err(e)
                    }
                };
                let out_ty = forall(*ty, tb.ty);
                let dep = has_bvar_in_proj(&tb.ty, 0);
                let (tm, ev) = self.lam_evidence(&t1, &tb, w, prop, dep, body_ty_ev);
                self.close_slot(saved);
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Let { ty, val, body } => {
                let s1 = self.infer_type(ty)?.ty;
                let s1 = self.whnf(&s1)?;
                as_sort(&s1)?;
                let val_ty = self.infer_type(val)?.ty;
                self.assert_is_def_eq(ty, &val_ty)?;
                // **The substituted body's own inference *is* the evidence.**
                // §6.3: the gate above has no downstream consumer after
                // substitution, so nothing is dropped and this clause is fully
                // threaded without a `Conv`.
                let body2 = subst(body, val);
                self.infer_type(&body2)
            }
            Expr::Proj { ind, idx, s } => {
                let (ty, sub) = self.infer_proj(ind, *idx, s)?;
                // **A projection whose own *type* is a proposition is a
                // proof**, so §6.2's left column gives it `•` and the whole
                // obligation is that `⟦βⱼ⟧` is inhabited — `crate::proj_prop`,
                // which routes on the carrier's class and has one ladder per
                // class: `LePropFields` at (S), `TruncFields` at (P),
                // `DeclFields` at (T).
                //
                // *(Rewritten. Through `9e60a27` this said the clause "routes
                // by the class-(S) store, so a class-(P) or class-(T) structure
                // falls through" — true then, and it read as a statement about
                // the clause when it was a statement about how much of the row
                // had landed. The `•` is decided by the projection's type, not
                // by the structure's class; `MINI-HANDOFF.md` §11 is the split
                // and it is by carrier, into four.)*
                //
                // A projection that is **not** a proof — a data field of a
                // class-(T) structure, `Prod.fst` and `PProd.fst.{1,1}` — is
                // `crate::proj_data`, whose `⟦projⱼ x⟧` is a real term
                // `πⱼ(⟦x⟧)` read straight out of the carrier's own Kuratowski
                // nesting, over `derived::…::DeclProj`.
                //
                // **The proof routes answer first, and the order is §6.2's
                // rather than a preference.** A projection whose *type* is a
                // `Prop` denotes `•` whatever its carrier is; `proj_data` would
                // type it too, at `πⱼ(⟦x⟧)`, and a proof would then have two
                // interpretations with no equation between them.
                //
                // §0.4: a projection out of a structure mini cannot interpret
                // is blocked by *that*, not by "projections are unwired". The
                // two are different categories — interpretation scope versus a
                // library item — and stamping the clause's own label on the
                // first would report the project as further behind on the
                // library than it is.
                //
                // **And the two routes' own declines are reasons too.** Each
                // returns `Err(Gap)` — `Gap::Classifier` when inference failed
                // under it, `Gap::IndApparatus`, `Gap::SymbolicLevel`, or a
                // parameter's reason forwarded through `Ev::reason` — and this
                // clause dropped both with `if let Ok` and minted `StructProj`
                // regardless, ten lines under the paragraph above. The `sub`
                // half of this very expression already obeyed §0.4; the two
                // halves disagreed. [`first_reason`] is the rule.
                let mut sub = sub;
                if sub.is_none() {
                    let g1 = match crate::proj_prop::typing(self, ind, *idx, s, &ty) {
                        Ok(thm) => {
                            let tm = crate::proj_prop::point_of(self);
                            return Ok(Typing { ty, tm, ev: Ev::Proved(thm) })
                        }
                        Err(g) => g,
                    };
                    let g2 = match crate::proj_data::typing(self, ind, *idx, s, &ty) {
                        Ok((tm, thm)) => {
                            return Ok(Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) })
                        }
                        Err(g) => g,
                    };
                    sub = Some(first_reason(&Gap::StructProj(*ind), g1, g2));
                }
                Ok(Typing { ty, tm: None, ev: Ev::missing(sub.unwrap_or(Gap::StructProj(*ind))) })
            }
            // **`⟦natLit n⟧ = ⟦Nat.succ^n Nat.zero⟧`, and there is no clause
            // beyond that.** The literal is *expanded* and the expansion is
            // inferred, so the term and the certificate both come from the
            // ordinary inductive route — `Nat`'s carrier, `Nat.zero`'s and
            // `Nat.succ`'s constructor typings — and nothing here knows what a
            // numeral is. That is the point: an accelerated representation
            // would be a second arithmetic to keep in step with the first, and
            // this project does not want one yet.
            //
            // It also makes `whnf`'s unfolding **reflexivity at the term
            // level**, which is what lets that branch emit no `step!`: the two
            // sides are one term rather than two related ones.
            //
            // The recursion terminates because [`Checker::nat_unfold`] refuses
            // above 10 — mini-lean's own guard, which the parser applies first
            // — and each step drops one.
            Expr::NatLit(n) => {
                let ty = konst(Name::simple("Nat"), no_levels());
                let t = self.infer_type(&Self::nat_unfold(*n)?)?;
                Ok(Typing { ty, tm: t.tm, ev: t.ev })
            }
            Expr::StrLit(_) => Ok(Typing {
                ty: konst(Name::simple("String"), no_levels()),
                tm: None,
                ev: Ev::missing(Gap::StrLit),
            }),
        }
    }

    /// One level of `Nat.succ^n Nat.zero` — `whnf`'s step **and** the
    /// literal's own interpretation, from one place.
    ///
    /// Shared rather than written twice because the two must agree exactly: the
    /// reduction owes no conversion certificate precisely when `⟦natLit n⟧` is
    /// the interpretation of *this* expansion, and two spellings that could
    /// drift is the defect `MINI-HANDOFF.md` §12 records the project paying for
    /// elsewhere.
    ///
    /// Refuses above 10 — mini-lean's `parseExprNatLit` guard, which
    /// [`crate::convert`] applies first, so this is a second line of defence
    /// rather than the reachable one. It is an `Err` and not a `Gap` because
    /// `whnf` has always answered that way for the same input, and an
    /// interpretation that declined where the reduction rejects would put the
    /// two axes out of step.
    fn nat_unfold(n: u64) -> R<E> {
        if n > 10 {
            return Err("The mini kernel does not support nat literals larger than 10".into())
        }
        let nat = Name::simple("Nat");
        Ok(if n == 0 {
            konst(Name::str(&nat, "zero"), no_levels())
        } else {
            app(konst(Name::str(&nat, "succ"), no_levels()), crate::expr::nat_lit(n - 1))
        })
    }

    /// The first sub-`Typing` that failed to interpret, as a reason.
    fn sub_gap(parts: &[&Typing]) -> Option<Gap> {
        parts.iter().find(|t| t.tm.is_none()).and_then(|t| t.ev.gap().cloned())
    }

    /// **The application rule**, one per `Π` clause: `Γ ⊢ ⟦f a⟧ ∈ ⟦B[a]⟧`.
    ///
    /// Both premises are in hand — `Γ ⊢ ⟦f⟧ ∈ ⟦Π x:A. B⟧` from `infer_type(f)`
    /// carried along `whnf`, and `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧` from `infer_type(a)`
    /// retargeted along the domain conversion — so this composes and nothing
    /// is looked for. nanoda's `ty_app` / `app_in_codomain` / `app_in_fibre`
    /// reach for `has_type_a` at exactly this point.
    ///
    /// Note what `⟦B[a]⟧` *is* here: not something recomputed by interpreting
    /// the substituted body, but whatever the rule concludes — `⟦B⟧` at a
    /// constant fibre, `b(q⃗,⟦a⟧)` at a dependent one. That is the skeleton's
    /// substitution-stability property doing its job, and it is why a `Typing`
    /// carries `⟦ty⟧` inside its evidence rather than as a field.
    fn app_evidence(
        &mut self,
        shape: Option<PiShape>,
        tf: &Typing,
        ta: &Typing,
        a_mem: Ev,
    ) -> Ev {
        // §0.4: the reason comes from whichever premise was missing, and only
        // from this clause when both were present and the *shape* was the
        // problem. `NotDecomposable` here would otherwise absorb every
        // uninterpreted inductive in the corpus and file it as threading debt.
        let blocked = |fallback: Gap| {
            Ev::missing(
                tf.ev
                    .gap()
                    .or_else(|| a_mem.gap())
                    .cloned()
                    .or_else(|| Self::sub_gap(&[tf, ta]))
                    .unwrap_or(fallback),
            )
        };
        let Some(shape) = shape else { return blocked(Gap::NotDecomposable) };
        let (Some(f_tm), Some(a_tm)) = (tf.tm.clone(), ta.tm.clone()) else {
            return blocked(Gap::NoEndpoint)
        };
        tf.ev.clone().zip(a_mem, |fm, am| {
            let Some(ip) = self.ip() else { return Ev::missing(Gap::SymbolicLevel) };
            let out = match &shape {
                PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &a_tm, &fm, &am),
                PiShape::Prop { site, dom } => ip.cond_app(site, dom, &fm, &a_tm, &am),
            };
            match out {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("app-rule")),
            }
        })
    }

    /// **The `Π` typing rules**, one per §6.2 clause, with the binder closed
    /// and its family discharged in the same call.
    ///
    /// Returns `⟦Π x:A. B⟧` and `Γ ⊢ ⟦Π x:A. B⟧ ∈ ⟦Sort (imax l1 l2)⟧`. **Two**
    /// clauses, which is §6.2's own count:
    ///
    /// * `l2 = 0` — a conditional singleton, in `U₀` **unconditionally**;
    ///   nothing about the fibre is needed, so nothing about it is assumed.
    /// * otherwise — the dependent product, `dprod_in_universe_pair_n` at this
    ///   fibre's prefix, **whether or not the codomain mentions the binder**.
    ///
    /// The *typing* of the first clause is unconditional; **choosing** it is
    /// not, and the two are different obligations. `l2 = 0` is a numeral mini
    /// computed, and it decides what `⟦Π x:A. B⟧` *is* — so the branch reads
    /// the codomain's own membership and takes the clause **only** when that
    /// membership is `⟦B⟧ ∈ U₀`, rather than interpreting against its own
    /// evidence. An absent one is refused too, carrying the sub-result's own
    /// reason; see the branch.
    ///
    /// # The binder-free clause was mini's own, and it is retired
    ///
    /// *(`SCOPING.md` §10, prototyped before the change. A third clause emitted
    /// `fs(⟦A⟧,⟦B⟧)` when `dep = has_bvar(body, 0)` said the codomain was
    /// binder-free. `derived::fs` and everything on it stay in the library; what
    /// is gone is the clause, and with it `MINI-HANDOFF.md` §5's entire
    /// 937-conversion binder-congruence row — one type, two spellings, two
    /// clauses, both right. Carneiro gives the dependent product
    /// unconditionally (`thesis.txt:2077`) and has no function-space clause, so
    /// this is a removal rather than an addition.)*
    ///
    /// **The λ clause moves with it and they are one decision** — see
    /// `lam_evidence`. The fibre costs nothing new: a binder-free codomain is
    /// hole 0 entire, so [`Interp::const_dprod`] hits one `fibres` entry for
    /// every non-dependent arrow in the corpus.
    ///
    /// # The one detector this removes, and it is not the one that matters
    ///
    /// The `!dep` branch carried a guard turning *"the codomain's typing
    /// depends on the binder's hypothesis"* into `Gap::Skeleton`. Under `dprod`
    /// the fibre premise is discharged **under** the binder, so that input is
    /// now simply proved — strictly more permissive, and a real proof.
    ///
    /// **It was never a bug detector, and it never fired.** Measured at zero in
    /// every corpus run it existed for. It was detecting *an input its own rule
    /// could not state*, not a defect: there is nothing wrong with a codomain
    /// whose term is binder-free and whose typing is not. The detector credited
    /// with catching `proj_data`'s missing `Interp::mk` records is a different
    /// and stronger one — `Interp::skeleton` answering `None`, which is
    /// term-level, survives the change, and now runs on **every** `Π` instead
    /// of only the dependent ones. `interp::tests::skeleton_refuses_an_unrecorded_term`
    /// is its pin and says so.
    fn pi_evidence(
        &mut self,
        t1: &Typing,
        tb: &Typing,
        w: Option<FreeVar>,
        dep: bool,
        l1: &Level,
        l2: &Level,
    ) -> (Option<Term>, Ev) {
        let empty = std::collections::HashMap::new();
        let (Some(dom), Some(cod), Some(w)) = (t1.tm.clone(), tb.tm.clone(), w) else {
            return (None, Ev::missing(Self::sub_gap(&[t1, tb]).unwrap_or(Gap::NoEndpoint)))
        };
        let (Some(n1), Some(n2)) =
            (crate::ground::eval(l1, &empty), crate::ground::eval(l2, &empty))
        else {
            return (None, Ev::missing(Gap::SymbolicLevel))
        };
        if n2 == 0 {
            // **The clause is chosen from a numeral, and the witness for what
            // the numeral says is already an argument.** `l2 = 0` claims
            // `⟦B⟧ ∈ U₀`, and `tb.ev` — transported to the codomain's sort by
            // the `whnf_typing` above this call — *is* that membership. Nothing
            // downstream ever asks for it: [`Interp::cond_typing`] is
            // unconditional by design and says so, so a wrong `l2` here would
            // hand back a true theorem about the wrong interpretation —
            // `[∀x∈⟦A⟧. •∈⟦B⟧]`, a truth value, where the dependent product
            // belongs — and every certificate built on it would compose.
            // `interp::point_of_proof` makes exactly this test one level down,
            // at the λ clause; this is it at the `Π`.
            //
            // **The witness must be present and must agree.** An earlier round
            // weakened this to "refuse a witness that contradicts the numeral,
            // let an absent one through", for one reason that has since been
            // removed at its source: `axiom A : Prop`, `def id : A → A` was a
            // codomain whose membership mini did not have. Mini now **declines
            // any export that declares an axiom of its own**
            // (`crate::convert::is_standard_axiom`), so that codomain cannot
            // reach this clause from a file at all, and the strong form is
            // back. `⟦A⟧ ∈ U₀` for a *declared* `A` was briefly derived instead
            // (`Interp::opaque_in_sort`, `cc0f898`), which bought the same
            // absence at the price of narrowing the model; that construction
            // is gone and this guard did not follow it.
            //
            // The other objection to the strong form was §0.4: firing on an
            // absence files someone else's gap under this clause's label. That
            // is answered by *taking* the sub-result's reason rather than
            // minting one — `tb.ev.reason(…)` — so the `Acc` negative test
            // keeps naming the `Acc` defect rather than this clause.
            //
            // **It never fires on the corpus, and it does fire.** Replaced by a
            // `panic!` across both corpus targets — the positive tutorial and
            // the negative one — it is not reached once; re-measured after
            // `opaque_in_sort` was withdrawn, since that is exactly the change
            // that could have brought the absence back. The same `panic!` takes
            // two unit tests, `the_pi_prop_clause_refuses_a_codomain_that_is_
            // not_witnessed_in_u0` and the `Acc` negative, so it is a guard and
            // not decoration. Every conditional-singleton `Π` on the corpus has
            // its codomain's `⟦B⟧ ∈ U₀` in hand, so the strong form costs
            // nothing; what it buys is that a clause chosen from a numeral can
            // no longer be taken on an unwitnessed codomain.
            let u0 = self.ip().map(|ip| ip.sort(0));
            if tb.ev.mem_set().as_ref() != u0.as_ref() {
                let g = tb.ev.reason(Gap::ConvCompose("pi-cond-witness"));
                return (None, Ev::missing(g))
            }
            let Some(site) = self.ip().and_then(|ip| ip.cond_site(&cod, w)) else {
                return (None, Ev::missing(Gap::Skeleton))
            };
            let tm = self.ip().map(|ip| ip.cond_term(&site, dom.clone()));
            // **The [`Closed`] is abandoned here, and the argument is about
            // this site rather than about scopes in general.**
            //
            // Nothing derived under this binder crosses the close. `tb.ev` is
            // the one thing in scope that carries `{w ∈ ⟦A⟧}`, and the two
            // lines that touch it are *above* this one and read only its
            // shape: `mem_set()` compares a set, `reason()` takes a label.
            // Neither yields a theorem and neither is returned.
            //
            // What is returned is `cond_typing`, which is **unconditional by
            // construction** — `Interp::cond_typing` builds
            // `⊢ chi(h⃗,⟦B⟧) ∈ U₀` from `cond_in_u0` at terms, with no premise
            // under the binder — so the `Closed` has nothing to discharge.
            // That is exactly the difference from the value clause below,
            // which *does* have a fibre premise raised under the binder and
            // therefore spends its `Closed` on it. The two clauses are not the
            // same shape and only one of them owes a discharge.
            //
            // The `let _` is deliberate: an abandoned `Closed` at this site is
            // a decision, and a bare statement would read as an oversight.
            let _ = self.close_one();
            let ev = match self.ip().and_then(|ip| ip.cond_typing(&site, dom)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("pi-cond")),
            };
            return (tm, ev)
        }
        // **There is no binder-free clause.** `⟦Π x:A. B⟧` is `dprod` whether or
        // not `B` mentions `x`; see this function's own header for why the
        // clause that used to sit here was retired rather than repaired.
        let _ = dep;
        let Some(site) = self.ip().and_then(|ip| ip.fibre_site(&cod, w)) else {
            return (None, Ev::missing(Gap::Skeleton))
        };
        let tm = self.ip().map(|ip| ip.dprod_term(&site, dom.clone()));
        let n = n1.max(n2);
        // The fibre premise sits *under* the binder, so it is raised there and
        // discharged afterwards; the domain's is raised outside.
        let fibre = tb.ev.clone().and_then(|m| {
            match self
                .ip()
                .and_then(|ip| ip.raise_in_gamma(n2 as usize, n as usize, &m))
                .and_then(|m| self.ip().and_then(|ip| ip.to_fibre_symbol(&site, w, &m)))
            {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::SortTowerHeight),
            }
        });
        let closed = self.close_one();
        let family = match (&closed, fibre) {
            (Some(c), ev) => match c.discharge_ev(ev) {
                Ok(e) => e,
                Err(_) => Ev::missing(Gap::Skeleton),
            },
            (None, _) => Ev::missing(Gap::NoEndpoint),
        };
        let dom_mem = t1.ev.clone().and_then(|m| {
            match self.ip().and_then(|ip| ip.raise_in_gamma(n1 as usize, n as usize, &m)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::SortTowerHeight),
            }
        });
        let ev = dom_mem.zip(family, |d, f| {
            match self.ip().and_then(|ip| ip.dprod_typing(&site, dom, &d, &f, n)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("pi-dprod")),
            }
        });
        (tm, ev)
    }

    /// **The `λ` typing rules**, one per clause of the *codomain*, with the
    /// binder closed and its family discharged in the same call.
    ///
    /// Returns `⟦λ x:A. b⟧` and `Γ ⊢ ⟦λ x:A. b⟧ ∈ ⟦Π x:A. B⟧`. The premise
    /// every one of them takes is `∀w. (w ∈ ⟦A⟧ → …)`, which is exactly what
    /// [`Closed::discharge`] produces — the shape the library consumes is the
    /// shape the scope produces, by design and not by coincidence.
    fn lam_evidence(
        &mut self,
        t1: &Typing,
        tb: &Typing,
        w: Option<FreeVar>,
        prop: bool,
        dep: bool,
        body_ty_ev: Ev,
    ) -> (Option<Term>, Ev) {
        // **A proof-λ over an uninterpretable domain denotes nothing**, and
        // this is a decision rather than a fall-through — audit finding L5.
        //
        // §6.2's `⟦λ x:α. e⟧ = •` needs neither the domain nor the binder's
        // variable, so an earlier revision handed the point back here and let
        // only the *evidence* be a gap, on the grounds that guarding both
        // together confuses §0's two axes. That reading is wrong at this one
        // site, and the asymmetry is what shows it: on the **value** branch the
        // very same situation returns `None`, so the clause was already
        // treating an uninterpreted domain as fatal to the term — and the only
        // thing deciding which way it went was `prop`, a bool from
        // `is_prop_ev` whose own `Ev` this branch neither holds nor checks.
        //
        // A term minted from a syntactic flag, on the path that has already
        // given up, cannot be composed with by anything downstream: it is
        // handed back beside a `Gap`. All it can do is be counted as an
        // interpretation mini does not have.
        //
        // **Measured before it was changed.** The state is reachable exactly
        // once in the whole suite — `rec_acc`'s reversed-relation fixture, where
        // `⟦Acc α r x⟧` is declined — and never on the corpus; every other
        // occurrence is `Checker::new`'s shape zone, where `self.ip()` is `None`
        // and the point was never minted anyway. Returning `None` here costs
        // nothing on either corpus target.
        let (Some(dom), Some(w)) = (t1.tm.clone(), w) else {
            let _ = prop;
            return (None, Ev::missing(Self::sub_gap(&[t1, tb]).unwrap_or(Gap::NoEndpoint)))
        };
        if prop {
            // A proof interprets to `•`, and its type is a conditional
            // singleton. The body's own membership is about `⟦b⟧`, which for a
            // `bvar` body is a scope variable rather than `•` — so it is first
            // taken to `•` by proof irrelevance, which is the same rule defeq
            // uses and needs no new lemma.
            let tm = self.ip().map(|ip| ip.point());
            let Some(cod) = tb.ev.mem_set() else {
                self.close_one();
                return (tm, Ev::missing(tb.ev.reason(Gap::NoEndpoint)))
            };
            let Some(site) = self.ip().and_then(|ip| ip.cond_site(&cod, w)) else {
                self.close_one();
                return (tm, Ev::missing(Gap::Skeleton))
            };
            let pt = self.point_eq(&tb.ev, body_ty_ev);
            let back = self.ev_symm(pt, "lam-point-symm");
            let at_point = tb.ev.clone().zip(back, |m, eq| {
                match self.ip().and_then(|ip| ip.retarget_subject(&m, &eq)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::ConvCompose("lam-point")),
                }
            });
            let in_fibre = at_point.and_then(|m| {
                match self.ip().and_then(|ip| ip.to_cond_fibre(&site, w, &m)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::Skeleton),
                }
            });
            let closed = self.close_one();
            let family = match &closed {
                Some(c) => c.discharge_ev(in_fibre).unwrap_or_else(|_| Ev::missing(Gap::Skeleton)),
                None => Ev::missing(Gap::NoEndpoint),
            };
            let ev = family.and_then(|f| {
                match self.ip().and_then(|ip| ip.cond_lam_typing(&site, dom, &f)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::ConvCompose("lam-cond")),
                }
            });
            return (tm, ev)
        }
        let Some(body_tm) = tb.tm.clone() else {
            self.close_one();
            return (None, Ev::missing(tb.ev.reason(Gap::NoEndpoint)))
        };
        let Some(lam) = self.ip().and_then(|ip| ip.lam_site(&body_tm, w)) else {
            self.close_one();
            return (None, Ev::missing(Gap::Skeleton))
        };
        let tm = self.ip().map(|ip| ip.lam_term(&lam, dom.clone()));
        // `Γ,w ⊢ t(h⃗,w) ∈ C` — the body's membership stated at the body
        // symbol, one Leibniz along the symbol's own defining equation.
        let at_sym = tb.ev.clone().and_then(|m| {
            match self.ip().and_then(|ip| ip.to_body_symbol(&lam, w, &m)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::Skeleton),
            }
        });
        // **The λ clause moves with the `Π` clause, and they are one decision.**
        // `lam_typing_fs` asserts `⟦λ⟧ ∈ fs(dom,cod)`; leaving it here against a
        // codomain type that is now a `dprod` re-creates the two-spellings
        // mismatch one layer down, which is the thing the change exists to
        // remove. Measured by Vera at `e258538`: Π alone is `constEv` 96 with
        // **64** `Gap::EndpointDrift`; Π and λ together is 0 drift.
        let _ = dep;
        let Some(cod) = tb.ev.mem_set() else {
            self.close_one();
            return (tm, Ev::missing(tb.ev.reason(Gap::NoEndpoint)))
        };
        let Some(fib) = self.ip().and_then(|ip| ip.fibre_site(&cod, w)) else {
            self.close_one();
            return (tm, Ev::missing(Gap::Skeleton))
        };
        let in_fibre = at_sym.and_then(|m| {
            match self.ip().and_then(|ip| ip.to_fibre_set(&fib, w, &m)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::Skeleton),
            }
        });
        let closed = self.close_one();
        let family = match &closed {
            Some(c) => c.discharge_ev(in_fibre).unwrap_or_else(|_| Ev::missing(Gap::Skeleton)),
            None => Ev::missing(Gap::NoEndpoint),
        };
        let ev = family.and_then(|f| {
            match self.ip().and_then(|ip| ip.lam_typing_dprod(&lam, &fib, dom, &f)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("lam-dprod")),
            }
        });
        (tm, ev)
    }

    /// **A λ-nest over a kernel bottom**, at the binders of a Lean `Π` type.
    ///
    /// `⟦T⟧`, `⟦T.ctor⟧` and `⟦T.rec⟧` are not Lean lambda expressions — their
    /// bodies are carrier terms `derived::inductive` builds — but their *types*
    /// are ordinary Lean `Π`s, and their interpretations must be exactly what
    /// the `λ` clause of §6.2 would produce if they were. So this walks the
    /// type's binders with the same `open_slot`/`is_prop_ev`/`lam_evidence`
    /// sequence [`Checker::infer_type`]'s `Expr::Lam` arm uses, and differs from
    /// it in one place only: at the bottom, instead of recursing on a body
    /// expression, it calls `bottom`.
    ///
    /// Sharing the clause dispatch is the point. The three `Π` clauses are
    /// three different sets, the choice between them is decided by `is_prop` on
    /// the body's type, and a zone-B nest that decided it by its own rule would
    /// be a second, unverified copy of the decision — which is exactly the
    /// divergence MINI-DESIGN.md §0.1 says an architecture should not force.
    pub(crate) fn lam_nest(
        &mut self,
        ty: &E,
        depth: usize,
        bottom: &mut dyn FnMut(&mut Checker<'e, 'i>) -> R<Typing>,
    ) -> R<Typing> {
        if depth == 0 {
            return bottom(self)
        }
        let Expr::Forall { ty: dom_e, body } = &ty.view() else {
            return Err(format!("expected {depth} more binders, got {ty}"))
        };
        let (dom_e, body) = (*dom_e, *body);
        let t1 = self.infer_type(&dom_e)?;
        let (s1, _, t1) = self.whnf_typing(t1)?;
        as_sort(&s1)?;
        let saved = self.open_slot(dom_e, t1.tm.clone());
        let w = self.current_var();
        let inner = (|c: &mut Self| -> R<(Typing, bool, Ev)> {
            let tb = c.lam_nest(&body, depth - 1, bottom)?;
            let (prop, w_ev) = c.is_prop_ev(&tb.ty)?;
            Ok((tb, prop, w_ev))
        })(self);
        let (tb, prop, body_ty_ev) = match inner {
            Ok(v) => v,
            Err(e) => {
                self.close_slot(saved);
                return Err(e)
            }
        };
        let out_ty = forall(dom_e, tb.ty);
        let dep = has_bvar_in_proj(&tb.ty, 0);
        let (tm, ev) = self.lam_evidence(&t1, &tb, w, prop, dep, body_ty_ev);
        self.close_slot(saved);
        Ok(Typing { ty: out_ty, tm, ev })
    }

    /// The interpretation and typing of the `i`-th binder counted from the
    /// innermost — `⟦bvar i⟧` and `Γ ⊢ ⟦bvar i⟧ ∈ ⟦its type⟧`, both already
    /// held by the scope stack.
    ///
    /// What a zone-B bottom needs: the parameter and field variables the nest
    /// opened above it, and the memberships that discharge `Ctor::mem`'s
    /// antecedent and `DeclUniverse`'s `H`. Neither is derived here; both are
    /// read off, at one vector index each.
    pub(crate) fn binder(&self, idx: u32) -> Option<(Term, Thm)> {
        let tm = self.scope_term(idx)?;
        match self.scope_typing(idx) {
            Ev::Proved(t) => Some((tm, t)),
            Ev::Gap(_) => None,
        }
    }

    /// The `n` innermost binders, **outermost first** — the order every
    /// `∀p⃗ ∀y⃗` prefix in `derived` is stated in.
    pub(crate) fn binders(&self, n: usize) -> Option<(Vec<Term>, Vec<Thm>)> {
        let mut tms = Vec::with_capacity(n);
        let mut mems = Vec::with_capacity(n);
        for i in (0..n).rev() {
            let (t, m) = self.binder(u32::try_from(i).ok()?)?;
            tms.push(t);
            mems.push(m);
        }
        Some((tms, mems))
    }

    /// The interpretation store, for the zone-B builder.
    pub(crate) fn interp(&mut self) -> Option<&mut Interp> { self.ip() }

    /// The syntactic environment, at its own lifetime.
    pub(crate) fn environment(&self) -> &'e Environment { self.env }

    /// `⟦c.{σ}⟧` as already stored — the zone-B builder's own lookup, at the
    /// levels it is building for. Only the term: the typing is what it is in the
    /// middle of establishing.
    pub(crate) fn stored_term(&mut self, name: &Name, inst: &[u32]) -> Option<Term> {
        let ip = self.th.as_ref()?.ip.get_const(&(*name, inst.to_vec()))?;
        Some(ip.term.clone())
    }

    /// Run `f` with the telescope and every scope it opened restored.
    pub(crate) fn in_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, Gap>) -> Result<T, Gap> {
        let saved = self.lenv.len();
        let r = f(self);
        self.close_slot(saved);
        r
    }

    /// Interpret a binder's type and open it, in one step — the pairing
    /// [`Checker::push`]'s doc insists on, exposed for the zone-B walk.
    pub(crate) fn interpret_and_open(&mut self, ty: &E) -> R<Option<Term>> {
        let t1 = self.infer_type(ty)?;
        let (s1, _, t1) = self.whnf_typing(t1)?;
        as_sort(&s1)?;
        self.push(*ty, t1.tm.clone());
        Ok(t1.tm)
    }

    /// Open a binder at an interpretation the caller **already has**.
    ///
    /// [`Checker::interpret_and_open`] infers and pushes in one step and throws
    /// the typing away; zone B's summand legs need that typing, so they infer
    /// first and push with this. The pairing `push`'s doc insists on is
    /// preserved — the domain handed in is still `infer_type(ty).tm` and still
    /// computed exactly once.
    pub(crate) fn push_interpreted(&mut self, ty: E, dom: Term) { self.push(ty, Some(dom)) }

    /// Open a binder with **no** interpretation — a recursive constructor
    /// field, whose type is the declaration being translated and so has no
    /// carrier yet. The de Bruijn telescope keeps its shape; nothing may depend
    /// on the variable, and `define_abbrev` is what refuses anything that does.
    pub(crate) fn open_uninterpreted(&mut self, ty: E) { self.push(ty, None); }

    /// The kernel variables of the `n` innermost open binders, outermost first.
    pub(crate) fn scope_vars(&self, n: usize) -> Option<Vec<FreeVar>> {
        let th = self.th.as_ref()?;
        let mut out = Vec::with_capacity(n);
        for i in (0..n).rev() {
            let d = (*th.slots.get(th.slots.len().checked_sub(1 + i)?)?)?;
            out.push(th.scopes.get(u32::try_from(th.scopes.len() - 1 - d).ok()?)?.var());
        }
        Some(out)
    }

    /// **On a store miss, hand back the reason that was recorded when the
    /// constant was built.** `None` means the constant is in the store.
    ///
    /// `⟦c.{σ}⟧` is put in the store at *`c`'s own declaration*, from the
    /// schedule the pre-pass computed — a `def` by
    /// [`crate::ledger::Ledger::run`]'s walk, an inductive's constants and
    /// `Quot`'s by [`crate::ledger::fill_declaration`]. So by the time any
    /// occurrence of `c` is checked, the question "is it there" has already
    /// been settled, and a miss means only that the build was attempted and
    /// declined. [`crate::zoneb::recorded_reason`] reads which of the three
    /// decline tables says so, and builds nothing.
    ///
    /// # The construction on a miss is what is left, and it is measured at zero
    ///
    /// The `else` below still runs §9 zone B, and over every export and fixture
    /// mini has it never runs at all: with the miss path made to `panic!` and
    /// the corpus run, the only misses on all 91 tutorial exports and all nine
    /// designed fixtures are `Squash` (a declaration that declined) and
    /// `VoidProp.rec` (an eliminator waiting on `derived/`), both of which the
    /// line above answers from a table. [`crate::interp::Interp::lazy_fills`]
    /// counts what reaches the construction and `mini/tests/tutorial.rs` pins
    /// it at zero; removing the eager fill takes it nonzero on 61 of the 91.
    ///
    /// **The enumeration above is the whole population and it once was not.**
    /// The mutual fixtures are neither exports nor designed fixtures, and three
    /// of them reached this construction — `Eq`, at the σ its rule theorems are
    /// stated at. The same `panic!` settled that too, and the reason was not a
    /// missing schedule entry but a *declaration order*: `mutual_aux::expand`
    /// emitted the rule theorems at the block, ahead of the `Eq` declaration
    /// their statements name. They are emitted last now. `mini/tests/mutual.rs`
    /// pins the count at zero on all ten.
    ///
    /// It is kept because it has a caller that is not the checker: 52 of
    /// `mini/src`'s unit tests build a `Checker` over an ad-hoc `Environment`
    /// with no ledger, no schedule and therefore no fill, and infer a constant
    /// occurrence directly. Deleting the branch would not remove a production
    /// path — it would move the fill into 52 test bodies, each of which would
    /// have to name the `(declaration, σ)` its environment needs *and the order
    /// to build them in*, which is the schedule, restated by hand.
    ///
    /// # Why this is a function and not a block inside `const_evidence`
    ///
    /// It used to be one, and [`Checker::delta_evidence`] — `whnf`'s δ leg —
    /// had no equivalent: it looked the constant up and, on a miss, reported a
    /// bare `Gap::NoInterpretation` on the name. So a clause whose *store* had
    /// declined for a stated reason was reported as "not interpreted" whenever
    /// the constant was reached through δ rather than through a typing, and
    /// **the reason was discarded**. That is `MINI-HANDOFF.md` §2's pattern at
    /// a reporting position, and it is worse than the six before it in one
    /// way: those dropped a value a later consumer wanted, and this dropped the
    /// explanation of a failure, which is what a person wanted.
    ///
    /// It surfaced on `Quot.ind` — a declaration whose *value* is the bare
    /// constant, so the δ leg is the first thing that asks for it — and the
    /// blocker named `no-interp(Quot.ind)` with the store's own decline
    /// nowhere. Every clause with a bare-constant value has the same blind
    /// spot, which is why the fix is symmetry rather than a special case.
    fn miss_reason(&mut self, name: &Name, inst: &[u32]) -> Option<Gap> {
        let key = (*name, inst.to_vec());
        let missing = |c: &Self| c.th.as_ref().is_some_and(|t| t.ip.get_const(&key).is_none());
        if self.th.is_none() || !missing(self) {
            return None
        }
        match crate::zoneb::recorded_reason(self, name, inst) {
            Gap::NoInterpretation(..) => {
                if let Some(th) = self.th.as_mut() {
                    th.ip.lazy_fills += 1;
                }
                let declines_to = crate::zoneb::ensure(self, name, inst).err();
                // A decline that nevertheless filled the store is not a reason:
                // the constant is there and the caller should read it.
                declines_to.filter(|_| missing(self))
            }
            g => Some(g),
        }
    }

    /// `⟦c.{σ}⟧` and its stored typing, or a named absence.
    fn const_evidence(&mut self, name: &Name, ls: &[Level]) -> (Option<Term>, Ev) {
        let empty = std::collections::HashMap::new();
        let Some(inst) =
            ls.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<Vec<u32>>>()
        else {
            return (None, Ev::missing(Gap::SymbolicLevel))
        };
        let key = (*name, inst.clone());
        if let Some(g) = self.miss_reason(name, &inst) {
            return (None, Ev::missing(g))
        }
        let Some(th) = self.th.as_ref() else { return (None, Ev::missing(Gap::SymbolicLevel)) };
        match th.ip.get_const(&key) {
            Some(c) => {
                let ev = match &c.typing {
                    Ok(s) => Ev::Proved(s.thm().clone()),
                    Err(g) => Ev::missing(g.clone()),
                };
                (Some(c.term.clone()), ev)
            }
            None => (None, Ev::missing(Gap::NoInterpretation(*name, inst))),
        }
    }

    /// `Γ ⊢ ⟦e⟧ ∈ ⟦ty⟧` from `Γ ⊢ ⟦e⟧ ∈ ⟦tv.ty⟧` and the conversion between
    /// the two types — the declaration pipeline's step 3–4 (§8).
    ///
    /// The `Conv` `assert_def_eq` returns is *consumed* here rather than
    /// merely proved, which is why the acceptance gate is not a drop: nothing
    /// downstream would have to re-derive it, because this is the downstream.
    pub fn retarget_to(&mut self, tv: &Typing, ty: &E, ty_tm: Term) -> Ev {
        let have = tv.ev.mem_set();
        if have.as_ref() == Some(&ty_tm) {
            return tv.ev.clone()
        }
        // `Lhs::Type`: `tv.ty` is the type inference assigned to the value and
        // `ty` the declared one — both are types, so the gate cannot fire.
        let Ok(conv) = self.assert_def_eq_as(&tv.ty, have, ty, Some(ty_tm), Lhs::Type) else {
            return Ev::missing(Gap::Classifier)
        };
        tv.ev.clone().zip(conv.ev, |mem, eq| {
            match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("decl-retarget")),
            }
        })
    }

    /// `checkType`.
    pub fn check_type(&mut self, e: &E) -> R<()> { self.infer_ty(e).map(|_| ()) }

    /// The type alone, for the shape zone and every acceptance-only site.
    fn infer_ty(&mut self, e: &E) -> R<E> { Ok(self.infer_type(e)?.ty) }

    /// **Which §6.2 clause a `Π`/`∀` with body `b` takes** — the thesis's
    /// `lvl(Γ ⊢ b)`, and `Prop` exactly when that is `0`.
    ///
    /// This is [`Checker::is_prop`] under another name, and that is the whole
    /// point: see the module-level note on why mini's classifier is *exact*
    /// where nanoda's is a syntactic approximation.
    pub fn body_clause(&mut self, b: &E) -> R<Clause> {
        Ok(if self.is_prop(b)? { Clause::Prop } else { Clause::Type })
    }

    /// **Which §6.2 clause a `λ` or an application takes** — the thesis's
    /// `sort(Γ ⊢ e)`, i.e. whether `e` is a *proof*, i.e. whether the type of
    /// its type is `Sort 0`.
    ///
    /// Not a second classifier: `sort(e) = lvl(type of e)`, so this is
    /// [`Checker::body_clause`] one level up. Two classifiers that could
    /// disagree is exactly what would make `⟦·⟧` fail to be a function.
    pub fn term_clause(&mut self, e: &E) -> R<Clause> {
        let t = self.infer_ty(e)?;
        self.body_clause(&t)
    }

    /// `isProp`.
    pub fn is_prop(&mut self, ty: &E) -> R<bool> {
        let s = self.infer_ty(ty)?;
        let s = self.whnf(&s)?;
        Ok(as_sort(&s)?.is_zero())
    }

    /// `inferProj`. The second component is the *subject's* gap, when the
    /// subject is what could not be interpreted.
    /// The `j`-th field's Lean type alone, **without the legality guards** —
    /// for a consumer that needs the *earlier* fields' types in order to state
    /// their propositionality.
    ///
    /// Those earlier fields may be ones the checker refuses to *project*:
    /// `PropStructure`'s field 1 is data, `085_projProp2` is in `bad/` for it,
    /// and `086` still has to say something about it because `TruncFields`'
    /// ladder quantifies `P₀ … Pⱼ`. Asking `infer_proj` would fail on a
    /// declaration the checker accepts. **The guards stay where they are** —
    /// `Expr::Proj`'s own arm — and this reads the type and nothing else. See
    /// [`crate::proj_prop`].
    pub(crate) fn infer_proj_ty(&mut self, n: &Name, idx: u32, e: &E) -> R<E> {
        Ok(self.proj_ty(n, idx, e, false)?.0)
    }

    fn infer_proj(&mut self, n: &Name, idx: u32, e: &E) -> R<(E, Option<Gap>)> {
        self.proj_ty(n, idx, e, true)
    }

    /// `infer_proj`, with the two `Prop`-projection refusals under `strict`.
    fn proj_ty(&mut self, n: &Name, idx: u32, e: &E, strict: bool) -> R<(E, Option<Gap>)> {
        let te = self.infer_type(e)?;
        let sub = if te.tm.is_none() { te.ev.gap().cloned() } else { None };
        let t = te.ty;
        let ty = self.whnf(&t)?;
        let (head, args) = get_app(&ty);
        let Expr::Const(ind_name, us) = &head.view() else {
            return Err(format!("Type of projected expression is not an inductive: {ty}"))
        };
        let Some(ConstantInfo::Inductive { num_params, num_indices, ctors, .. }) =
            self.lookup(ind_name)
        else {
            return Err(format!("Type of projected expression is not an inductive: {ty}"))
        };
        if args.len() != (*num_params + *num_indices) as usize {
            return Err("Invalid projection, expression is not fully applied".to_string())
        }
        if ctors.len() != 1 {
            return Err(format!("Invalid projection, {ind_name} has not exactly one constructor"))
        }
        let ctor_name = &ctors[0];
        let Some(ConstantInfo::Opaque { lparams: clp, ty: cty }) = self.lookup(ctor_name) else {
            return Err(format!("Constructor {ctor_name} not found in environment"))
        };
        let ctor_ty = instantiate_lparams(cty, clp, us)?;
        let params = slice(&args, 0, *num_params as usize);
        let mut ctor_ty = self.instantiate_foralls(&ctor_ty, &params)?;
        let is_prop_type = self.is_prop(&ctor_ty)?;
        for i in 0..idx {
            let cur = ctor_ty;
            let Expr::Forall { ty: d, body: b } = &cur.view() else {
                return Err(format!(
                    "Projection index {} out of bounds for {ind_name}",
                    idx + 1
                ))
            };
            if strict && is_prop_type && has_bvar(b, 0) && !self.is_prop(d)? {
                return Err(format!(
                    "Invalid projection; projection {} is depended upon and not a proposition.",
                    i + 1
                ))
            }
            ctor_ty = subst(b, &crate::expr::proj(*n, i, *e));
        }
        let cur = ctor_ty;
        let Expr::Forall { ty: d, .. } = &cur.view() else {
            return Err(format!("Projection index {} out of bounds for {ind_name}", idx + 1))
        };
        if strict && is_prop_type && !self.is_prop(d)? {
            return Err(format!(
                "Invalid projection; projection {} would project data out of a proposition",
                idx + 1
            ))
        }
        Ok((*d, sub))
    }

    // ─────────────────────────────────────────── telescope helpers ──

    /// `openForall n type k`, push form: opens `n` binders and returns the body.
    /// The caller must be inside [`Checker::scoped`].
    fn open_forall_push(&mut self, n: u32, ty: &E) -> R<E> {
        let mut cur = *ty;
        for _ in 0..n {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &t.view() else {
                return Err(format!("Insufficient number of parameters: {t}"))
            };
            let (d, body) = (*d, *body);
            self.push(d, None);
            cur = body;
        }
        Ok(cur)
    }

    /// `openForallEager`, push form: returns `(binders opened, the whnf'd
    /// non-`Π` body)`. The caller must be inside [`Checker::scoped`].
    fn open_forall_eager_push(&mut self, ty: &E) -> R<(u32, E)> {
        let mut cur = *ty;
        let mut n = 0u32;
        loop {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &t.view() else { return Ok((n, t)) };
            let (d, body) = (*d, *body);
            self.push(d, None);
            cur = body;
            n += 1;
        }
    }

    /// `instantiateForalls`.
    fn instantiate_foralls(&mut self, ty: &E, xs: &[E]) -> R<E> {
        let mut result = *ty;
        for x in xs {
            let t = self.whnf(&result)?;
            let Expr::Forall { body, .. } = &t.view() else {
                return Err(format!("Expected a function type, got {t}"))
            };
            result = subst(body, x);
        }
        Ok(result)
    }

    // ──────────────────────────────────────── definitional equality ──

    /// `isPropOrUnit` — defeq's proof-irrelevance gate, with the witness.
    ///
    /// On the `Prop` branch the witness is `Γ ⊢ ⟦t⟧ ∈ U₀`, and it is **not a
    /// new derivation**: `infer_type(t)` produced `Γ ⊢ ⟦t⟧ ∈ ⟦s⟧`, the `whnf`
    /// leg transports it, and `⟦Sort 0⟧` *is* `U₀`. The census's "no new
    /// derivation needed, only non-discarding" (§1.6), made literal.
    ///
    /// `cert` says whether the caller wants the witness at all; when it does
    /// not, the inference still runs (the *decision* needs it) but the
    /// transport does not, which is what keeps the acceptance-only callers —
    /// `is_def_eq`, the shape zone — at their old cost.
    ///
    /// # `None` is the negative answer, and it carries no gap
    ///
    /// *(This returned `(bool, Ev)`, and every **negative** answer paired its
    /// `false` with an `Ev::missing` — `Gap::NoEndpoint` when the type's head
    /// was not a constant or not an inductive, and `Gap::UnitLike(name)` when
    /// the inductive simply was not unit-like. No caller ever reads the `Ev`
    /// beside a `false`: `def_eq_ev` destructures it and takes the other
    /// branch. So those were gaps minted for a **decision that succeeded** —
    /// "this is not a proof" is an answer, not a failure — and every one of
    /// them landed in the blocker trail. On `mutual_aux_encoding`'s first
    /// blocked pair they contributed the whole of `unit-like(Tag)`,
    /// `unit-like(Aux)` and a fifth of the `no-endpoint` mints, all of them
    /// about the ordinary business of deciding that `A`, `Tag` and `Aux` are
    /// data. §0.4 says a result carries the reason of the sub-result that
    /// stopped it; a sub-result that stopped nothing must not leave a reason
    /// lying around for a later one to be attributed to.)*
    ///
    /// `Some(ev)` therefore means *proof irrelevance applies*, with the
    /// witness or the named absence of it; `None` means it does not apply, and
    /// mints nothing.
    fn is_prop_or_unit_ev(&mut self, t: &E, cert: bool) -> R<Option<Ev>> {
        let tt = self.infer_type(t)?;
        let (s, ev) = if cert {
            let (s, _, tt) = self.whnf_typing(tt)?;
            (s, Some(tt.ev))
        } else {
            (self.whnf(&tt.ty)?, None)
        };
        let u = as_sort(&s)?;
        if u.is_zero() {
            // The witness is minted on this branch alone — the one whose
            // answer a caller consumes. Uncertified, the absence is the
            // caller's own and it is named here because this is where the
            // branch was taken.
            return Ok(Some(ev.unwrap_or_else(|| Ev::missing(Gap::NoEndpoint))))
        }
        let tw = self.whnf(t)?;
        let (head, _) = get_app(&tw);
        let Expr::Const(name, _) = &head.view() else { return Ok(None) };
        let Some(ConstantInfo::Inductive { is_unit, .. }) = self.lookup(name) else {
            return Ok(None)
        };
        if !*is_unit {
            return Ok(None)
        }
        // The unit-like branch's witness is the structure's subsingleton lemma
        // from the inductive interpretation, which §9 zone B has not reached.
        // Uncertified there is no witness to be missing: the caller handed in
        // no endpoints, and `no-endpoint` is the reason it gets back — the
        // same one it got before this branch had a name.
        let name = *name;
        Ok(Some(if cert { Ev::missing(Gap::UnitLike(name)) } else { Ev::missing(Gap::NoEndpoint) }))
    }

    /// `isProp`, with the witness. Same function as
    /// [`Checker::is_prop_or_unit_ev`] minus the unit probe.
    pub(crate) fn is_prop_ev(&mut self, ty: &E) -> R<(bool, Ev)> {
        let t = self.infer_type(ty)?;
        let (s, _, t) = self.whnf_typing(t)?;
        Ok((as_sort(&s)?.is_zero(), t.ev))
    }

    /// `Γ ⊢ ⟦a⟧ = ⟦c⟧` from `Γ ⊢ ⟦a⟧ = ⟦b⟧` and `Γ ⊢ ⟦b⟧ = ⟦c⟧`.
    fn ev_trans(&mut self, a: Ev, b: Ev, at: &'static str) -> Ev {
        a.zip(b, |x, y| match self.ip().and_then(|ip| derived::eq_trans(&mut ip.env, &x, &y)) {
            Some(t) => Ev::Proved(t),
            None => Ev::missing(Gap::ConvCompose(at)),
        })
    }

    /// `Γ ⊢ ⟦b⟧ = ⟦a⟧` from `Γ ⊢ ⟦a⟧ = ⟦b⟧`.
    fn ev_symm(&mut self, a: Ev, at: &'static str) -> Ev {
        a.and_then(|x| match self.ip().and_then(|ip| derived::eq_symm(&mut ip.env, &x)) {
            Some(t) => Ev::Proved(t),
            None => Ev::missing(Gap::ConvCompose(at)),
        })
    }

    /// `tryStructureEta`. Returns the **structure's name** when it fires, so
    /// that the gap it leaves names the inductive it is waiting on rather than
    /// a placeholder — §0.4 again, at the smallest scale.
    fn try_structure_eta(&mut self, e1: &E, e2: &E) -> R<Option<Name>> {
        let (head, args) = get_app(e1);
        let Expr::Const(con_name, _) = &head.view() else { return Ok(None) };
        let t = self.infer_ty(e1)?;
        let t = self.whnf(&t)?;
        let (ind_head, _) = get_app(&t);
        let Expr::Const(ind_name, _) = &ind_head.view() else { return Ok(None) };
        let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind_name) else {
            return Ok(None)
        };
        if ctors.len() != 1 || &ctors[0] != con_name {
            return Ok(None)
        }
        let ind_name = *ind_name;
        let np = *num_params as usize;
        for (i, arg) in args.iter().enumerate().skip(np) {
            let p = crate::expr::proj(ind_name, u32::try_from(i - np).expect("field index"), *e2);
            let arg = *arg;
            if !self.is_def_eq(&arg, &p)? {
                return Ok(None)
            }
        }
        Ok(Some(ind_name))
    }

    /// `tryFunEta`.
    fn try_fun_eta(&mut self, e1: &E, e2: &E) -> R<bool> {
        let Expr::Lam { ty: t1, body: b1 } = &e1.view() else { return Ok(false) };
        let (t1, b1) = (*t1, *b1);
        let rhs = app(shift(e2, 0, 1), bvar(0));
        self.scoped(|c| {
            c.push(t1, None);
            c.is_def_eq(&b1, &rhs)
        })
    }

    /// `isDefEq`: `assertIsDefEq` with the exception swallowed. The telescope is
    /// restored explicitly, which is what `ReaderT`'s backtracking does for the
    /// original.
    ///
    /// A **decision**, with no evidence consumer — `tryStructureEta`'s field
    /// comparison and the K-rule probe want a `bool` and nothing else — so it
    /// hands in no endpoints and no certificate is built. That is not a drop:
    /// there is no downstream step that would have to re-derive it.
    pub fn is_def_eq(&mut self, e1: &E, e2: &E) -> R<bool> {
        let saved = self.lenv.len();
        let r = self.assert_is_def_eq(e1, e2);
        self.close_slot(saved);
        Ok(r.is_ok())
    }

    /// `assertIsDefEq`, acceptance only.
    pub fn assert_is_def_eq(&mut self, e1: &E, e2: &E) -> R<()> {
        self.assert_def_eq(e1, None, e2, None).map(|_| ())
    }

    /// **`assertIsDefEq`, threaded**: `Γ ⊢ ⟦e1⟧ = ⟦e2⟧`.
    ///
    /// Clause order is `assertIsDefEqImpl`'s, which is what acceptance fidelity
    /// depends on. `tm1`/`tm2` are the endpoints' interpretations, from the
    /// `Typing`s the caller already holds; when either is absent no certificate
    /// is attempted at all, which is what keeps the decision-only callers at
    /// their old cost.
    ///
    /// # Nothing here searches
    ///
    /// Stated in those words, because this function is where the claim could
    /// still have broken. Every fact this needs is either handed in (the two
    /// endpoints), read from a store by an exact key (`(name, ground levels)`),
    /// read from the scope stack by index (a `bvar`'s typing), or computed
    /// *forward* by inference on a subterm. There is no fallback, no retry, and
    /// no goal-directed clause matching. In particular:
    ///
    /// * **`local_premises` has no counterpart.** nanoda guesses the ambient
    ///   context by scanning an argument for `Local` nodes, even under open
    ///   binders. Mini's scope stack *is* that information, so there is nothing
    ///   to reconstruct: see [`Checker::beta_premise`].
    /// * **`try_eta_expansion_aux`'s dropped half is unrepresentable.** The
    ///   only way to obtain evidence here is to compose it, so a congruence
    ///   cannot silently discard a side; it can only produce a named `Gap`.
    pub fn assert_def_eq(
        &mut self,
        e1: &E,
        tm1: Option<Term>,
        e2: &E,
        tm2: Option<Term>,
    ) -> R<Conv> {
        self.assert_def_eq_as(e1, tm1, e2, tm2, Lhs::Unknown)
    }

    /// [`Checker::assert_def_eq`], with what the caller already knows about
    /// `e1`'s own classifier. See [`Lhs`].
    pub fn assert_def_eq_as(
        &mut self,
        e1: &E,
        tm1: Option<Term>,
        e2: &E,
        tm2: Option<Term>,
        lhs: Lhs,
    ) -> R<Conv> {
        // The §0.3 census counts conversions that were *asked for*: a
        // decision-only call hands in no endpoints and states nothing, so
        // counting it would drown the measurement in its own scaffolding.
        let asked = tm1.is_some() && tm2.is_some();
        let ev = self.def_eq_ev(e1, tm1, e2, tm2, lhs)?;
        if asked {
            if let Some(ip) = self.ip() {
                ip.note_conv(&ev);
            }
        }
        Ok(Conv { to: *e2, ev })
    }

    fn def_eq_ev(
        &mut self,
        e1: &E,
        tm1: Option<Term>,
        e2: &E,
        tm2: Option<Term>,
        lhs: Lhs,
    ) -> R<Ev> {
        // A certificate needs *both* endpoints; one alone states nothing.
        let cert = tm1.is_some() && tm2.is_some();
        let (tm1, tm2) = if cert { (tm1, tm2) } else { (None, None) };
        // …and a conversion nobody asked for files nothing. Everything below
        // this line mints `no-endpoint` when `cert` is false — there is no
        // endpoint to state anything about — and every one of those mints is
        // the acceptance walk, not the pair's residual. See
        // [`crate::blocker::Quiet`], which carries what it was costing.
        let _quiet =
            (!cert && crate::blocker::is_armed()).then(crate::blocker::Quiet::new);

        // Proof irrelevance first.
        //
        // **No check that `t1.tm` and `tm1` agree.** `⟦·⟧` is a function, so
        // they do; a guard for it was measured never to fire across 11 578 061
        // conversions, and one that fails nothing is a finding rather than a
        // guard. What has to hold is that the certificate composes, and the
        // rules below are what make it: `whnf_conv`, `ev_trans` and `ev_symm`
        // each state their endpoints, and a wrong one stops there.
        //
        // **`infer_type(e1)` has exactly one consumer, and it is this gate.**
        // `t1` is read by `is_prop_or_unit_ev` and by `proof_irrel_ev` and by
        // nothing below, so at a caller that can rule the gate out the whole
        // inference is dead — see [`Lhs`] for which callers can and why the
        // ruling-out is a theorem rather than a guess.
        let irrel = match lhs {
            Lhs::Type => None,
            Lhs::Unknown => {
                let t1 = self.infer_type(e1)?;
                self.is_prop_or_unit_ev(&t1.ty, cert)?.map(|ev| (t1, ev))
            }
        };
        if let Some((t1, ty_ev)) = irrel {
            if !cert {
                return Ok(ty_ev)
            }
            return self.proof_irrel_ev(&t1, ty_ev, e2);
        }

        let (a, ca) = self.whnf_conv(e1, tm1, &Gap::NoEndpoint)?;
        let (b, cb) = self.whnf_conv(e2, tm2, &Gap::NoEndpoint)?;
        let (a_tm, b_tm) = (ca.ev.eq_rhs(), cb.ev.eq_rhs());
        let mid = self.def_eq_struct(&a, a_tm, &b, b_tm)?;
        // `⟦e1⟧ = ⟦a⟧`, then `⟦a⟧ = ⟦b⟧`, then `⟦b⟧ = ⟦e2⟧` — the composition
        // nanoda once skipped and now guards (the refl-for-a-reduction bug).
        let left = self.ev_trans(ca.ev, mid, "defeq-left");
        let back = self.ev_symm(cb.ev, "defeq-symm");
        Ok(self.ev_trans(left, back, "defeq-right"))
    }

    /// The certificate of proof irrelevance: both sides reach `•`, and the
    /// equation is `trans` of one with `symm` of the other.
    fn proof_irrel_ev(&mut self, t1: &Typing, ty_ev: Ev, e2: &E) -> R<Ev> {
        let why = ty_ev.gap().cloned();
        let left = self.point_eq(&t1.ev, ty_ev);
        let t2 = self.infer_type(e2)?;
        let (prop2, ty2_ev) = self.is_prop_ev(&t2.ty)?;
        if !prop2 {
            // **The unit-like branch, where `•` is not the inhabitant.** It
            // needs the structure's subsingleton lemma, and that is
            // `LeProp::subsingleton` — built, and already carried by every
            // class-(S) translation [`crate::class_s`] performs.
            //
            // *(This branch read "which §9 zone B has not reached". It had:
            // `MINI-HANDOFF.md` §21 records the search that was cut short and
            // the one that was not. The gate above still supplies the name, so
            // a decline keeps the row's own label.)*
            return Ok(match crate::unit_like::certify(self, t1, &t2) {
                Ok(t) => Ev::Proved(t),
                Err(g) => Ev::missing(why.unwrap_or(g)),
            })
        }
        let right = self.point_eq(&t2.ev, ty2_ev);
        let back = self.ev_symm(right, "irrel-symm");
        Ok(self.ev_trans(left, back, "irrel-trans"))
    }

    /// `Γ ⊢ ⟦e⟧ = •` from the term's membership and its type's `U₀` witness.
    fn point_eq(&mut self, e_mem: &Ev, ty_mem: Ev) -> Ev {
        ty_mem.zip(e_mem.clone(), |ty, e| {
            match self.ip().and_then(|ip| ip.point_of_proof(&ty, &e)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("proof-irrel")),
            }
        })
    }

    /// The two binders' interpretations, taken apart into their sites — the
    /// pair the congruence rule is chosen by.
    fn pi_shapes(&self, a: &Option<Term>, b: &Option<Term>) -> Option<(PiShape, PiShape)> {
        let ip = self.th.as_ref().map(|th| &*th.ip)?;
        Some((ip.as_pi(a.as_ref()?)?, ip.as_pi(b.as_ref()?)?))
    }

    fn lam_shapes(
        &self,
        a: &Option<Term>,
        b: &Option<Term>,
    ) -> Option<((LamSite, Term), (LamSite, Term))> {
        let ip = self.th.as_ref().map(|th| &*th.ip)?;
        Some((ip.as_lam(a.as_ref()?)?, ip.as_lam(b.as_ref()?)?))
    }

    /// **The binder congruence**, shared by `Π`/`∀` and `λ`.
    ///
    /// Two binders whose bodies have different shapes have different, unrelated
    /// head symbols, so congruence over subterms relates nothing and the
    /// equation has to come from Extensionality: `dprod_ext_n`, `cond_ext_n`,
    /// `lam_ext_n`. All three want the same two premises, and mini has both in
    /// the right shape already —
    ///
    /// * the domain conversion, recursively;
    /// * `∀x. (x ∈ ⟦A⟧ → S(p⃗,x) = S'(q⃗,x))`, which is the body conversion
    ///   under a scope opened on `⟦A⟧`, moved onto the two body symbols by
    ///   their own defining equations and discharged.
    ///
    /// The scope is opened on the **left** domain, which is what the lemma
    /// quantifies over; the recursion runs *inside* it, so a `bvar` in either
    /// body has a real typing at one vector index. Acceptance is the original's:
    /// domain first, then body under the pushed telescope, `Err` from either.
    #[allow(clippy::too_many_arguments)]
    fn binder_cong<S>(
        &mut self,
        t1: &E,
        t2: &E,
        b1: &E,
        b2: &E,
        same: bool,
        refl: Ev,
        shapes: Option<S>,
    ) -> R<Ev>
    where
        S: BinderShapes,
    {
        // Acceptance first, and unconditionally: the certificate must never be
        // able to change a verdict.
        let d1 = self.infer_type(t1)?;
        let (d1_tm, d2_tm) = match &shapes {
            Some(s) => (Some(s.left_dom()), Some(s.right_dom())),
            None => (None, None),
        };
        // `Lhs::Type`: `t1` is a binder's domain, and the `d1` above is exactly
        // the inference saying its type is a sort.
        let dom_conv =
            self.assert_def_eq_as(t1, d1_tm.clone(), t2, d2_tm.clone(), Lhs::Type)?;
        let saved = self.open_slot(*t1, d1.tm.clone());
        let w = self.current_var();
        let inner = (|c: &mut Self| -> R<Ev> {
            let (bt1, bt2) = match (&shapes, w) {
                (Some(s), Some(w)) => {
                    let x = Term::var(w);
                    match c.ip() {
                        Some(ip) => (Some(s.left_body(ip, &x)), Some(s.right_body(ip, &x))),
                        None => (None, None),
                    }
                }
                _ => (None, None),
            };
            let body = c.assert_def_eq(b1, bt1, b2, bt2)?;
            // Onto the two symbols: `S(p⃗,w) = ⟦b1⟧ = ⟦b2⟧ = S'(q⃗,w)`.
            let (Some(s), Some(w)) = (&shapes, w) else { return Ok(Ev::missing(Gap::NotDecomposable)) };
            let x = Term::var(w);
            let (l, r) = match c.ip() {
                Some(ip) => (s.left_sym_at(ip, &x), s.right_sym_at(ip, &x)),
                None => (None, None),
            };
            let (Some(l), Some(r)) = (l, r) else { return Ok(Ev::missing(Gap::Skeleton)) };
            let step = c.ev_trans(Ev::Proved(l), body.ev, "cong-left");
            let back = c.ev_symm(Ev::Proved(r), "cong-symm");
            Ok(c.ev_trans(step, back, "cong-right"))
        })(self);
        let pointwise = match inner {
            Ok(e) => e,
            Err(e) => {
                self.close_slot(saved);
                return Err(e)
            }
        };
        let closed = self.close_one();
        self.close_slot(saved);
        let (Some(closed), Some(s), Some(d1_tm), Some(d2_tm)) =
            (closed, shapes, d1_tm, d2_tm)
        else {
            return Ok(if same { refl } else { Ev::missing(Gap::NotDecomposable) })
        };
        // **Decided, not retried.** Two binders with the same interpretation
        // need no congruence at all, and asking for one first and falling back
        // on failure would be exactly the "try A, else try B" shape §0's rule
        // bans. The recursion above still ran — it is the acceptance check —
        // but its certificate has no consumer here, which is the `let` rule's
        // situation and not a drop.
        if same {
            return Ok(refl)
        }
        // **The `Closed` is spent, and nothing survives it.** `pointwise` was
        // derived under the binder and carries `{w ∈ ⟦A⟧}`; `discharge_ev` is
        // the one thing that can retire that hypothesis, and it takes the
        // evidence **by value**, so after this line there is no undischarged
        // copy left to hand anywhere.
        //
        // A `raw = pointwise.clone()` used to be taken one line above this and
        // handed to `apply` beside the discharged family — so a hypothetical
        // theorem outlived the close with the `Closed` already spent and no
        // second discharge in reach. Neither implementation of `apply` read
        // it (both spelled it `_raw`), and the `raw.and_then` around the
        // result was redundant with `zip`: `raw` is a gap exactly when
        // `pointwise` is, and whenever `pointwise` is a gap so is `family`,
        // which `zip` short-circuits before the closure runs. So it is
        // deleted rather than discharged twice.
        let family = closed.discharge_ev(pointwise).unwrap_or_else(|_| Ev::missing(Gap::Skeleton));
        Ok(dom_conv.ev.zip(family, |de, fam| {
            match self.ip().and_then(|ip| s.apply(ip, &d1_tm, &d2_tm, &de, &fam)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::BinderCongruence(s.rule())),
            }
        }))
    }

    /// The structural clauses, on two expressions already in weak head normal
    /// form. `Err` is rejection and needs no evidence on any branch — the
    /// licensing-branch principle, confirmed by the census for every negative
    /// branch of nanoda's defeq.
    fn def_eq_struct(
        &mut self,
        a: &E,
        a_tm: Option<Term>,
        b: &E,
        b_tm: Option<Term>,
    ) -> R<Ev> {
        // **Identical interpretations settle it by reflexivity**, whatever the
        // expressions look like. This is not an optimisation but the whole
        // point of `⟦·⟧` being a function: two Lean terms with one
        // interpretation need no theorem relating them, and the congruence
        // families below exist only for the case where they differ.
        let same = match (&a_tm, &b_tm) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        };
        let refl = || match &a_tm {
            Some(x) => Ev::Proved(kernel::Thm::eq_refl(x.clone())),
            None => Ev::missing(Gap::NoEndpoint),
        };
        let differ = || {
            Err(format!("Expected definitional equality between {a} and {b}, but they differ."))
        };
        match (&a.view(), &b.view()) {
            (Expr::Sort(l1), Expr::Sort(l2)) => {
                assert_level_eq(l1, l2)?;
                // Ground levels: equal levels give the *same* tower term, so
                // the certificate is reflexivity and nothing about level
                // algebra is needed. This is what retires nanoda's whole
                // "level algebra" admit family for mini.
                Ok(if same { refl() } else { Ev::missing(Gap::NoEndpoint) })
            }
            (Expr::Forall { ty: t1, body: b1 }, Expr::Forall { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (*t1, *b1, *b2);
                let shapes = self.pi_shapes(&a_tm, &b_tm);
                self.binder_cong(&t1, t2, &b1, &b2, same, refl(), shapes)
            }
            (Expr::Lam { ty: t1, body: b1 }, Expr::Lam { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (*t1, *b1, *b2);
                let shapes = self.lam_shapes(&a_tm, &b_tm);
                self.binder_cong(&t1, t2, &b1, &b2, same, refl(), shapes)
            }
            (Expr::BVar(n1), Expr::BVar(n2)) => {
                if n1 != n2 {
                    return differ()
                }
                // nanoda's `Admit::Local` becomes reflexivity, as the census
                // says it should: one index, one scope, one variable.
                Ok(refl())
            }
            (Expr::App(f1, a1), Expr::App(f2, a2)) => {
                let (f1, a1, f2, a2) = (*f1, *a1, *f2, *a2);
                // **Decided, not retried** — this clause's own opening
                // sentence, at the one arm that was not making the decision.
                //
                // Every other structural arm answers `same` with `refl()` and
                // only builds a congruence when the two interpretations differ;
                // this one descended unconditionally, so a pair whose equation
                // was *already* `⊢ ⟦e⟧ = ⟦e⟧` was re-derived as
                // `app_cong` of its two halves — and threw the reflexivity away
                // whenever a half could not state its own.
                //
                // That is `#90(b)`. `transport_through_eq_rec`'s residual is
                // `Eq.rec … (myCongr a b h)` compared with **itself**: the
                // major is a proof, so `⟦major⟧` is `•`,
                // [`Checker::split_app`] cannot peel it, and the recursive
                // `whnf_conv` on each side hands back a conversion with no
                // right endpoint. `def_eq_struct` then sees `None`/`None` at
                // the *reducts* and cannot say `same` — while the caller's own
                // `a_tm == b_tm` had said it one frame up and was discarded
                // here.
                //
                // The recursion below still runs, unthreaded: it is the
                // acceptance check and acceptance must not move. Running it
                // *with* endpoints and then dropping the result would be the
                // same certificate computed for nobody — `binder_cong`'s
                // `same` arm does exactly that and is the shape this avoids.
                //
                // **What it costs, measured in both directions**, with the arm
                // toggled by an environment variable in one binary so that both
                // columns come off the same build:
                //
                // ```text
                //                      conversions              time     constEv
                // tutorial corpus   1 102 350 →   829 661        —      218/218 → 218/218
                // nested_model      7 261 651 → 3 061 232   108s → 80s   37/41  →  39/41
                // nested_iota       8 133 944 → 3 878 982   171s → 147s 117/124 → 117/124
                // nested_iota_arm   1 011 975 →   469 765    23s → 20s   34/36  →  34/36
                // ```
                //
                // On the corpus `moved` goes 3896 → 3454 and `movedSealed`
                // 957 → 908, with `gapped` still 0 and the verdicts still
                // 89 accept / 2 decline / 0 reject. `nested_model` is where the
                // certificates move: two of its four `no-endpoint` constant
                // typings close, and they are `transportNode`/`transportCons`,
                // the pair `#90(b)` is about. The two nested fixtures gain no
                // typing here, because what they are still waiting on is the
                // ι dispatch arm's seeding decision and not this arm.
                //
                // `nested_model`'s **gapped conversions rise**, 30 → 41, and
                // that is the walk getting further: the two lemmas certify, so
                // the two ι rules built on them are now checked past the point
                // where they used to stop, and what they reach gaps. The two
                // constant typings are the number to read, not this one.
                //
                // Six mutations, against `eq_cash`'s five and `tutorial`'s
                // twelve:
                //
                // ```text
                // KILLED   delete the arm
                // KILLED   drop the `same` guard — always answer reflexivity
                // KILLED   drop both acceptance recursions
                // KILLED   drop the argument half of the acceptance recursion
                // KILLED   swap the halves the acceptance recursion compares
                // KILLED   answer `no-endpoint` instead of reflexivity
                // ```
                //
                // The third is killed **by the conversion count and not by an
                // acceptance change** — `tutorial_conversion_split` alone, with
                // the bad corpus still rejecting everything it rejected. So the
                // recursion's acceptance effect has no witness in the suite,
                // and the honest reading is that no input reaches it: for
                // `same` to hold at a pair that is *not* def-eq, two
                // applications would need one interpretation and different
                // meanings, and the only terms `⟦·⟧` collapses that way are
                // proofs, which never reach this arm because the proof-
                // irrelevance gate in `def_eq_ev` answers first.
                if same {
                    self.assert_is_def_eq(&f1, &f2)?;
                    self.assert_is_def_eq(&a1, &a2)?;
                    return Ok(refl())
                }
                let (ft1, at1) = self.split_app(&a_tm);
                let (ft2, at2) = self.split_app(&b_tm);
                let cf = self.assert_def_eq(&f1, ft1, &f2, ft2)?;
                let ca = self.assert_def_eq(&a1, at1, &a2, at2)?;
                // **Both halves are composed, never dropped.**
                Ok(match self.ip() {
                    Some(ip) => crate::conv::app_cong(ip, &cf.ev, &ca.ev),
                    None => Ev::missing(Gap::SymbolicLevel),
                })
            }
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) => {
                if n1 != n2 {
                    return differ()
                }
                if ls1.len() != ls2.len() {
                    return Err(format!("Mismatched level parameter list when checking {a} =?= {b}"))
                }
                for (l1, l2) in ls1.iter().zip(ls2.iter()) {
                    assert_level_eq(l1, l2)?;
                }
                // Both sides are post-eager-delta opaque and the ground levels
                // evaluate equal, so this is one store entry and reflexivity;
                // `lazy_delta` has no analogue here.
                Ok(if same { refl() } else { Ev::missing(Gap::NoEndpoint) })
            }
            (
                Expr::Proj { ind: n1, idx: i1, s: s1 },
                Expr::Proj { ind: n2, idx: i2, s: s2 },
            ) => {
                if n1 != n2 || i1 != i2 {
                    return Err(format!("Projections differ: {a} =?= {b}"))
                }
                let (s1, s2) = (*s1, *s2);
                self.assert_is_def_eq(&s1, &s2)?;
                // **The subjects' conversion was made and thrown away**, and
                // with route (b) it is the whole content of the congruence:
                // `⟦projⱼ x⟧` is a term in `⟦x⟧`, so one Leibniz over `πⱼ`
                // carries it. At a *proof* projection both sides are `•` and
                // `same` answered above, so this is only ever the data case.
                if same {
                    return Ok(refl())
                }
                let (Some(x), Some(y)) = (a_tm.clone(), b_tm.clone()) else {
                    return Ok(Ev::missing(Gap::NoEndpoint))
                };
                let (n, i) = (*n1, *i1);
                Ok(match crate::proj_data::proj_congr(self, &n, i, &s1, &s2, &x, &y) {
                    Ok(t) => Ev::Proved(t),
                    Err(g) => Ev::missing(g),
                })
            }
            _ => {
                // Short-circuiting, as the original's `||` is: the second
                // direction must not run — and must not be able to reject — when
                // the first already fired.
                let eta = match self.try_structure_eta(a, b)? {
                    Some(n) => Some((n, false)),
                    None => self.try_structure_eta(b, a)?.map(|n| (n, true)),
                };
                if let Some((n, flipped)) = eta {
                    if same {
                        return Ok(refl())
                    }
                    // **The probe decided; this only certifies.** `crate::proj_data`
                    // re-runs the field conversions the probe threw away — it
                    // used `is_def_eq`, which returns a `bool` — and composes
                    // them with `DeclProj::eta`. It runs *second* and its
                    // failure is a gap, never a rejection, because acceptance
                    // must not move when a certificate becomes available.
                    //
                    // `flipped` is which way round the rule fired, and the
                    // certificate is stated in the caller's own direction.
                    let (l, r) = if flipped { (b, a) } else { (a, b) };
                    let ev = match crate::proj_data::structure_eta(self, &n, l, r) {
                        Ok(t) => Ev::Proved(t),
                        Err(g) => return Ok(Ev::missing(g)),
                    };
                    return Ok(if flipped { self.ev_symm(ev, "struct-eta") } else { ev })
                }
                // Short-circuiting as above, and the direction is kept: the
                // certificate is stated in the caller's own order.
                let fe = if self.try_fun_eta(a, b)? {
                    Some(false)
                } else if self.try_fun_eta(b, a)? {
                    Some(true)
                } else {
                    None
                };
                if let Some(flipped) = fe {
                    if same {
                        return Ok(refl())
                    }
                    // **The probe decided; this only certifies** — the same
                    // split as `try_structure_eta` above, and its failure is a
                    // gap rather than a rejection for the same reason.
                    //
                    // *(This branch read "the pointwise family is discharged
                    // from a scope the recursion above opens with no endpoints;
                    // wiring `conv::fun_eta_leg` needs that recursion threaded
                    // first." The recursion is what a body merely **def-eq** to
                    // `f x` would need. η's own theorem needs none of it: the
                    // λ's interpretation is a `lambda_n` graph and so is
                    // `derived::ext::Eta`'s, and their body symbols agree by the
                    // site's own `t_ax`. See [`crate::fun_eta`].)*
                    let (l, r) = if flipped { (b, a) } else { (a, b) };
                    let (l_tm, r_tm) = if flipped {
                        (b_tm.clone(), a_tm.clone())
                    } else {
                        (a_tm.clone(), b_tm.clone())
                    };
                    let (Some(l_tm), Some(r_tm)) = (l_tm, r_tm) else {
                        return Ok(Ev::missing(Gap::NoEndpoint))
                    };
                    let _ = l;
                    let ev = match crate::fun_eta::certify(self, r, &l_tm, &r_tm) {
                        Ok(t) => Ev::Proved(t),
                        Err(g) => return Ok(Ev::missing(g)),
                    };
                    return Ok(if flipped { self.ev_symm(ev, "fun-eta") } else { ev })
                }
                differ()
            }
        }
    }

    /// `defEqParams`. Note the original does not whnf here, and neither does
    /// the official kernel.
    fn def_eq_params(&mut self, n: u32, type1: &E, type2: &E) -> R<()> {
        if n == 0 {
            return Ok(())
        }
        let Expr::Forall { ty: d1, body: b1 } = &type1.view() else {
            return Err(format!("Expected a function type, got {type1}"))
        };
        let Expr::Forall { ty: d2, body: b2 } = &type2.view() else {
            return Err(format!("Expected a function type, got {type2}"))
        };
        let (d1, b1, b2) = (*d1, *b1, *b2);
        self.assert_is_def_eq(&d1, d2)?;
        self.scoped(|c| {
            c.push(d1, None);
            c.def_eq_params(n - 1, &b1, &b2)
        })
    }

    // ──────────────────────────────── the inductive declaration zone ──

    /// `isValidIndApp`, generalised to a block: **which** member does `ty`
    /// end at?
    ///
    /// The original answers `Bool` because there is one candidate. A block's
    /// answer is an index, and every caller needs it: a constructor's result
    /// says which motive its minor is stated at, and a recursive field's type
    /// says which motive its induction hypothesis is stated at and which
    /// member's recursor computes it. `nanoda`'s port names the same function
    /// `which_valid_ind_app`.
    fn which_valid_ind_app(&self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<usize> {
        let (head, args) = get_app(ty);
        let Expr::Const(f, us) = &head.view() else {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        };
        let Some(k) = ic.member(f) else {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        };
        if us.len() != ic.lparams.len()
            || us.iter().zip(ic.lparams.iter()).any(|(l, p)| *l != Level::param(*p))
        {
            return Err(format!("Level parameters do not match those of {f} in {ty}"))
        }
        if args.len() != (ic.num_params + ic.num_indices[k]) as usize {
            return Err(format!(
                "Expected {} arguments, got {} in {ty}",
                ic.num_params + ic.num_indices[k],
                args.len()
            ))
        }
        for i in 0..ic.num_params {
            if args[i as usize].view() != Expr::BVar(sh + ic.num_params - (i + 1)) {
                return Err(format!("Unexpected parameter {} in {ty}", i + 1))
            }
        }
        for i in ic.num_params as usize..args.len() {
            // **Any** member, not just the one this application ends at: an
            // index of `T0` that mentions `T2` is as circular as one that
            // mentions `T0`.
            if let Some(n) = ic.names.iter().find(|n| has_const(n, &args[i])) {
                return Err(format!(
                    "Unexpected recursive occurrence of {} in index argument {} of {ty}",
                    n,
                    i + 1
                ))
            }
        }
        Ok(k)
    }

    /// `isValidIndApp`'s original signature, for the callers that only need the
    /// judgement.
    fn is_valid_ind_app(&self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        self.which_valid_ind_app(ic, sh, ty).map(|_| ())
    }

    /// `checkCtorParam`: universe bound, then strict positivity.
    fn check_ctor_param(&mut self, ic: &IndCtx<'_>, sh: u32, ctor_param: &E) -> R<()> {
        let s = self.infer_ty(ctor_param)?;
        let u = as_sort(&s)?;
        if !ic.ind_level.is_zero_syntactically() {
            assert_level_le(&u, ic.ind_level)?;
        }
        let cp = self.whnf(ctor_param)?;
        if ic.occurs(&cp) {
            self.scoped(|c| {
                let (m, ret) = c.open_forall_eager_push(&cp)?;
                for d in c.read_local_types(m)? {
                    if let Some(n) = ic.names.iter().find(|n| has_const(n, &d)) {
                        return Err(format!("Not strictly positive: {n} occurs in domain"))
                    }
                }
                c.is_valid_ind_app(ic, sh + m, &ret)
            })?;
        }
        Ok(())
    }

    /// `checkCtorType`. NB: no whnf, matching the official kernel.
    fn check_ctor_type(&mut self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        if let Expr::Forall { ty: domain, body } = &ty.view() {
            let (domain, body) = (*domain, *body);
            self.check_ctor_param(ic, sh, &domain)?;
            self.scoped(|c| {
                c.push(domain, None);
                c.check_ctor_type(ic, sh + 1, &body)
            })
        } else {
            self.is_valid_ind_app(ic, sh, ty)
        }
    }

    /// The `elimToSort` walk over a single constructor's telescope.
    fn elim_to_sort_go(&mut self, t: &E) -> R<bool> {
        let Expr::Forall { ty: domain, body } = &t.view() else { return Ok(true) };
        let (domain, body) = (*domain, *body);
        let s = self.infer_ty(&domain)?;
        let u = as_sort(&s)?;
        self.scoped(|c| {
            c.push(domain, None);
            let appears = c.scoped(|c2| {
                let (sh, res) = c2.open_forall_eager_push(&body)?;
                let (_, args) = get_app(&res);
                Ok(args.iter().any(|a| a.view() == Expr::BVar(sh)))
            })?;
            if !(u.is_zero() || appears) {
                return Ok(false)
            }
            c.elim_to_sort_go(&body)
        })
    }

    /// The recursor's type: steps 1–6 of mini-lean's `recType` builder,
    /// generalised to a `mutual … end` block.
    ///
    /// One recursor is built per member. Steps 1–3 — parameters, motives,
    /// minors — are the **same telescope for every member of the block**, and
    /// only steps 4–6 differ: member `k`'s recursor binds `k`'s indices, takes
    /// a major argument at `k`, and returns `k`'s motive. That sharing is not
    /// an optimisation, it is the definition: `A.rec` and `C.rec` of the same
    /// block must accept the same motive and minor arguments, and a builder
    /// that computed each member's prefix from that member's own constructors
    /// would produce constants Lean's export does not have.
    ///
    /// The single-declaration case is `n = 1`, and every position below reads
    /// `n - 1 - j` where the original read a literal `0`.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_type(
        &mut self,
        ic: &IndCtx<'_>,
        tys: &[E],
        ctors: &[Vec<(Name, E)>],
        k: usize,
        us: &Rc<[Level]>,
        motive_level: &Level,
    ) -> R<E> {
        let np = ic.num_params;
        let n = u32::try_from(ic.names.len()).expect("block size");
        let nc = u32::try_from(ctors.iter().map(Vec::len).sum::<usize>()).expect("minor count");
        let nik = ic.num_indices[k];
        self.scoped(|c| {
            // 1. Parameters. Every member of the block declares the same
            //    parameter telescope — `add_block` has checked it — so they are
            //    opened once, from the first member, and each member's *own*
            //    type is then instantiated at them.
            c.open_forall_push(np, &tys[0])?;
            let params0 = bvars(np, 0);
            let mut opened: Vec<E> = Vec::with_capacity(tys.len());
            for t in tys {
                opened.push(c.instantiate_foralls(t, &params0)?);
            }
            // 2. Motives, one per member, each over that member's own indices.
            //    Built with only the parameters in scope and pushed together, so
            //    that `push_types` does the shifting: a motive's type mentions
            //    the parameters and never an earlier motive.
            let mut motive_types: Vec<E> = Vec::new();
            for (j, ni) in ic.num_indices.iter().copied().enumerate() {
                let mt = c.scoped(|c| {
                    c.open_forall_push(ni, &opened[j])?;
                    let mut a = bvars(np, ni);
                    a.extend(bvars(ni, 0));
                    let major_type = app_n(konst(ic.names[j], us.clone()), &a);
                    c.push(major_type, None);
                    c.mk_forall(ni + 1, sort(*motive_level))
                })?;
                motive_types.push(mt);
            }
            c.push_types(&motive_types);
            // 3. Minors — every constructor of every member, in block order.
            let mut minor_types: Vec<E> = Vec::new();
            for (j, cs) in ctors.iter().enumerate() {
                let jm = u32::try_from(j).expect("block size");
                for (ctor_name, ctor_type) in cs {
                    let mt = c.scoped(|c| {
                        let params = bvars(np, n);
                        let ctor_type = c.instantiate_foralls(ctor_type, &params)?;
                        let (num_fields, ctor_res_type) = c.open_forall_eager_push(&ctor_type)?;
                        // Recursive fields get an induction hypothesis, stated
                        // at the motive of **the field's own member**, which is
                        // not in general the member this constructor builds.
                        let mut hyp_types: Vec<E> = Vec::new();
                        for field in bvars(num_fields, 0) {
                            let t = c.infer_ty(&field)?;
                            let t = c.whnf(&t)?;
                            if !ic.occurs(&t) {
                                continue
                            }
                            let hyp = c.scoped(|c| {
                                let (m, ret) = c.open_forall_eager_push(&t)?;
                                let l = head_member(ic, &ret)?;
                                let (_, rargs) = get_app(&ret);
                                let mut a = slice(
                                    &rargs,
                                    np as usize,
                                    (np + ic.num_indices[l]) as usize,
                                );
                                a.push(app_n(shift(&field, 0, m), &bvars(m, 0)));
                                let lm = u32::try_from(l).expect("block size");
                                let body = app_n(bvar(num_fields + m + (n - 1 - lm)), &a);
                                c.mk_forall(m, body)
                            })?;
                            hyp_types.push(hyp);
                        }
                        let nh = u32::try_from(hyp_types.len()).expect("hypothesis count");
                        c.push_types(&hyp_types);
                        let ctor_res_type = shift(&ctor_res_type, 0, nh);
                        let mut a: Vec<E> =
                            params.iter().map(|p| shift(p, 0, num_fields + nh)).collect();
                        a.extend(bvars(num_fields, nh));
                        let ctor_app = app_n(konst(*ctor_name, us.clone()), &a);
                        let (_, rargs) = get_app(&ctor_res_type);
                        let mut a2 =
                            slice(&rargs, np as usize, (np + ic.num_indices[j]) as usize);
                        a2.push(ctor_app);
                        let motive_app = app_n(bvar(num_fields + nh + (n - 1 - jm)), &a2);
                        c.mk_forall(num_fields + nh, motive_app)
                    })?;
                    minor_types.push(mt);
                }
            }
            c.push_types(&minor_types);
            // 4. Indices — member `k`'s own, and no other member's.
            c.open_forall_push(nik, &shift(&opened[k], 0, n + nc))?;
            // 5. Major argument, at member `k`.
            let mut a = bvars(np, n + nc + nik);
            a.extend(bvars(nik, 0));
            let major_type = app_n(konst(ic.names[k], us.clone()), &a);
            c.push(major_type, None);
            // 6. Result type: member `k`'s motive applied to indices and major.
            let mut a = bvars(nik, 1);
            a.push(bvar(0));
            let km = u32::try_from(k).expect("block size");
            let result_type = app_n(bvar(nc + nik + 1 + (n - 1 - km)), &a);
            c.mk_forall(np + n + nc + nik + 1, result_type)
        })
    }

    /// One iota rule's RHS: the body of
    /// `fun params motives minors fields => …`.
    ///
    /// `minor_pos` is the constructor's position in the **block-wide** minor
    /// list, not its position among its own member's constructors: the minors
    /// are one shared telescope and `Stms.cons`'s minor is the eighth of eight
    /// however few constructors `Stms` has.
    ///
    /// The induction hypothesis a recursive field contributes is an application
    /// of **that field's member's** recursor — `Stms.cons`'s two fields call
    /// `Stm.rec` and `Stms.rec` — to the very same parameters, motives and
    /// minors. That is the whole content of mutual recursion, and it is one
    /// line below.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_rule(
        &mut self,
        ic: &IndCtx<'_>,
        rec_type: &E,
        ctor_type: &E,
        minor_pos: u32,
        num_minors: u32,
        us2: &Rc<[Level]>,
    ) -> R<E> {
        let np = ic.num_params;
        let n = u32::try_from(ic.names.len()).expect("block size");
        self.scoped(|c| {
            c.open_forall_push(np + n + num_minors, rec_type)?;
            let ctor_type = c.instantiate_foralls(ctor_type, &bvars(np, n + num_minors))?;
            let (num_fields, _) = c.open_forall_eager_push(&ctor_type)?;
            let minor = bvar(num_minors - (minor_pos + 1) + num_fields);
            let fields = bvars(num_fields, 0);
            let mut ihs: Vec<E> = Vec::new();
            for field in &fields {
                let t = c.infer_ty(field)?;
                let t = c.whnf(&t)?;
                if !ic.occurs(&t) {
                    continue
                }
                let ih = c.scoped(|c| {
                    let (m, ret) = c.open_forall_eager_push(&t)?;
                    let l = head_member(ic, &ret)?;
                    let (_, rargs) = get_app(&ret);
                    let mut a = bvars(np + n + num_minors, num_fields + m);
                    a.extend(slice(&rargs, np as usize, (np + ic.num_indices[l]) as usize));
                    a.push(app_n(shift(field, 0, m), &bvars(m, 0)));
                    let rec_name = Name::str(&ic.names[l], "rec");
                    let body = app_n(konst(rec_name, us2.clone()), &a);
                    c.mk_lambda(m, body)
                })?;
                ihs.push(ih);
            }
            let mut a = fields;
            a.extend(ihs);
            Ok(app_n(minor, &a))
        })
    }
}

/// Which member of the block a recursive occurrence's type ends at.
///
/// Separate from [`Checker::which_valid_ind_app`], which also *validates*: that
/// one is the declaration-time positivity check and reads the parameter
/// arguments as de Bruijn indices at a known depth. By the time the recursor is
/// built the occurrence has already passed it, the depth is a different one,
/// and all that is wanted is the member — so this reads the head and nothing
/// else rather than re-running a check at coordinates that no longer hold.
fn head_member(ic: &IndCtx<'_>, ret: &E) -> R<usize> {
    let (head, _) = get_app(ret);
    let Expr::Const(f, _) = &head.view() else {
        return Err(format!("Expected a recursive argument headed by an inductive, got {ret}"))
    };
    ic.member(f).ok_or_else(|| format!("{f} is not a member of the block being declared"))
}

// ────────────────────────────────────────────────── Environment.add ──

fn nodup(lparams: &[Name], name: &Name) -> R<()> {
    for (i, p) in lparams.iter().enumerate() {
        if lparams[i + 1..].contains(p) {
            return Err(format!("Duplicate level parameters in declaration of {name}"))
        }
    }
    Ok(())
}

/// **The sort a type lives in, under a telescope.** Inference whose entire
/// output is a [`Level`].
///
/// `tys` is a telescope, outermost first, each entry scoped under the ones
/// before it; `e` is scoped under all of them. Returns `u` such that
/// `tys ⊢ e : Sort u`.
///
/// # Why this exists, and why the answer is a `Level` and not a `Typing`
///
/// `mini/src/mutual_aux.rs` encodes a `mutual … end` block whose members carry
/// indices, and the packed motive it builds — `fun t => ∀ix, Aux p⃗ t ix → Sort v`
/// — has to be handed to `Tag.rec` at *exactly* the level that expression
/// lives at, which is `max` over the index types' own sorts. Those sorts are
/// not readable off the declaration: an index of type `N` is `Sort 1` only
/// because `N`'s declaration says so.
///
/// So the encoder asks the checker. That is allowed and the boundary it must
/// not cross is a different one: `ci/check-mutual-blackbox.sh` requires that
/// the encoder never look *inside* a `Term` or a `Thm`, and this returns
/// neither. It is zone A — no interpretation, no evidence, `Checker::new`
/// rather than `Checker::threaded` — so there is no certificate here to look
/// inside of.
///
/// The allowlist in that script is `kernel::{add, sort_under}` and is checked
/// by name, so a third entry point cannot appear without someone editing the
/// rule.
pub fn sort_under(env: &Environment, tys: &[E], e: &E) -> R<Level> {
    let mut c = Checker::new(env);
    c.scoped(|c| {
        for t in tys {
            c.push(*t, None);
        }
        let s = c.infer_ty(e)?;
        let s = c.whnf(&s)?;
        as_sort(&s)
    })
}

/// `Environment.addQuot`, ported verbatim.
pub fn add_quot(env: &mut Environment) -> R<()> {
    let quot_name = Name::simple("Quot");
    let quot_mk_name = Name::str(&quot_name, "mk");
    let quot_lift_name = Name::str(&quot_name, "lift");
    let quot_ind_name = Name::str(&quot_name, "ind");
    let u = Name::simple("u");
    let v = Name::simple("v");
    let prop = sort(Level::zero());
    let sort_u = sort(Level::param(u));
    let sort_v = sort(Level::param(v));
    let eq_name = Name::simple("Eq");

    let aar_prop = |i: u32| arrow(bvar(i), arrow(bvar(i + 1), prop));
    let mk_quot = |a: u32, r: u32| {
        app(app(konst(quot_name, levels(&[Level::param(u)])), bvar(a)), bvar(r))
    };

    // Quot : ∀ (α : Sort u) (_ : α → α → Prop), Sort u
    let quot_type = arrow(sort_u, arrow(aar_prop(0), sort_u));
    // Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), @Quot α r
    let quot_mk_type =
        arrow(sort_u, arrow(aar_prop(0), arrow(bvar(1), mk_quot(2, 1))));
    // Quot.lift
    let f_type = arrow(bvar(2), bvar(1));
    let h_type = arrow(
        bvar(3),
        arrow(
            bvar(4),
            arrow(
                app(app(bvar(4), bvar(1)), bvar(0)),
                app(
                    app(
                        app(konst(eq_name, levels(&[Level::param(v)])), bvar(4)),
                        app(bvar(3), bvar(2)),
                    ),
                    app(bvar(3), bvar(1)),
                ),
            ),
        ),
    );
    let quot_lift_type = arrow(
        sort_u,
        arrow(
            aar_prop(0),
            arrow(sort_v, arrow(f_type, arrow(h_type, arrow(mk_quot(4, 3), bvar(3))))),
        ),
    );
    // Quot.ind
    let beta_ind_type = arrow(mk_quot(1, 0), prop);
    let h_ind_type = arrow(
        bvar(2),
        app(
            bvar(1),
            app(
                app(
                    app(konst(quot_mk_name, levels(&[Level::param(u)])), bvar(3)),
                    bvar(2),
                ),
                bvar(0),
            ),
        ),
    );
    let quot_ind_type = arrow(
        sort_u,
        arrow(
            aar_prop(0),
            arrow(beta_ind_type, arrow(h_ind_type, arrow(mk_quot(3, 2), app(bvar(2), bvar(0))))),
        ),
    );

    let lift_info = ConstantInfo::Recursor {
        lparams: vec![u, v],
        ty: quot_lift_type,
        num_params: 2,
        // `Quot` is not an inductive block; its two eliminators take one
        // "motive" apiece, at the position an inductive's single motive sits.
        num_motives: 1,
        num_minors: 2,
        num_indices: 0,
        rules: vec![(quot_mk_name, app(bvar(2), bvar(0)))],
        k_type: None,
    };
    let ind_info = ConstantInfo::Recursor {
        lparams: vec![u],
        ty: quot_ind_type,
        num_params: 2,
        num_motives: 1,
        num_minors: 1,
        num_indices: 0,
        rules: vec![(quot_mk_name, app(bvar(1), bvar(0)))],
        k_type: None,
    };
    env.insert_new(quot_name, ConstantInfo::Opaque { lparams: vec![u], ty: quot_type })?;
    env.insert_new(
        quot_mk_name,
        ConstantInfo::Opaque { lparams: vec![u], ty: quot_mk_type },
    )?;
    env.insert_new(quot_lift_name, lift_info)?;
    env.insert_new(quot_ind_name, ind_info)
}

/// `Environment.add`.
///
/// Mini-lean's version is functional (`Except String Environment`), so a
/// rejected declaration leaves the environment untouched. This one mutates,
/// which is observably the same because the only caller aborts the file on the
/// first rejection — mini-lean's `--liberal` mode is not ported.
pub fn add(env: &mut Environment, decl: &Declaration) -> R<()> {
    match decl {
        Declaration::Axiom { name, lparams, ty } => {
            nodup(lparams, name)?;
            {
                let mut c = Checker::new(env);
                c.infer_ty(ty)
                    .map_err(|e| format!("{e}\n… while checking declaration {name}"))?;
            }
            env.insert_new(
                *name,
                ConstantInfo::Opaque { lparams: lparams.clone(), ty: *ty },
            )
        }
        Declaration::Def { name, lparams, ty, value, kind } => {
            nodup(lparams, name)?;
            {
                let mut c = Checker::new(env);
                let go = |c: &mut Checker<'_, '_>| -> R<()> {
                    let s = c.infer_ty(ty)?;
                    let u = as_sort(&s)?;
                    if matches!(kind, DefKind::Theorem) && !u.is_zero() {
                        return Err(format!(
                            "The type of a theorem must be a proposition, but {ty} has universe {u}"
                        ))
                    }
                    let ty2 = c.infer_ty(value)?;
                    c.assert_is_def_eq(ty, &ty2)
                };
                go(&mut c).map_err(|e| format!("{e}\n… while checking declaration {name}"))?;
            }
            let cinfo = match kind {
                DefKind::Def | DefKind::Theorem => ConstantInfo::Def {
                    lparams: lparams.clone(),
                    ty: *ty,
                    value: *value,
                },
                DefKind::Opaque => {
                    ConstantInfo::Opaque { lparams: lparams.clone(), ty: *ty }
                }
            };
            env.insert_new(*name, cinfo)
        }
        Declaration::Quot => add_quot(env),
        // A single inductive is a block of one, and [`add_block`] is written so
        // that nothing inside it knows the difference.
        Declaration::Inductive { name, lparams, num_params, ty, ctors } => {
            let types =
                [IndType { name: *name, ty: *ty, ctors: ctors.clone() }];
            add_maybe_nested(env, lparams, *num_params, &types)
        }
        Declaration::Mutual { lparams, num_params, types } => {
            add_maybe_nested(env, lparams, *num_params, types)
        }
    }
}

/// **Nested or not**, which is a property of the constructor types and not of
/// anything the export flags for us.
///
/// A constructor argument typed at a *foreign* inductive applied to the type
/// being declared — `Tree.node : List Tree → Tree` — is a nested occurrence,
/// and `add_block` cannot check it: its positivity check is about the block's
/// own members and `List Tree` is not one. [`crate::nested`] specialises such
/// a declaration into a block that *is* checkable, hands it straight back to
/// [`add`], and restores what comes out. A declaration with no such occurrence
/// takes the same path it always did, with `plan` returning `None` before
/// anything is built.
///
/// # The nested path is only ever entered where mini used to reject
///
/// The detector's test for an occurrence is syntactic — a foreign inductive
/// applied to parameters that mention a member — and syntactic is *wider* than
/// Lean's `numNested`. `Eq T a b` mentions `T` in `Eq`'s parameter and is not a
/// nested occurrence; a declaration carrying one must go on getting the
/// recursor it always got, with one motive and not two.
///
/// So the ordinary path runs **first**, on a scratch environment, and nothing
/// about nesting is even asked unless it fails. That makes the invariant
/// mechanical rather than a claim about how good the detector is: a
/// declaration mini accepted before is checked by exactly the code that
/// accepted it and gets exactly the recursors it got, and the nested path can
/// only ever widen the set of *accepted* declarations. The export oracle
/// (`mini/tests/mutual.rs`) is what would catch a violation, at every recursor
/// in every fixture and in the tutorial corpus.
///
/// The scratch copy is also why a rejected declaration no longer leaves half a
/// block behind: `add_block` inserts every member before it checks any
/// constructor, and used to do that in the caller's environment.
///
/// **This guard has no measured occupant.** Removing it — specialising whenever
/// the detector fires — leaves every suite green, corpus and oracle included:
/// no declaration mini has ever been shown makes the detector fire spuriously.
/// It is kept for the argument and not for a fixture, and anyone tempted to
/// delete it should write the declaration that needs it first. MEASUREMENTS.md,
/// "Nested inductives: specialise, check, restore", is the mutation row.
fn add_maybe_nested(
    env: &mut Environment,
    lparams: &[Name],
    num_params: u32,
    types: &[IndType],
) -> R<()> {
    let mut scratch = env.clone();
    let plain = match add_block(&mut scratch, lparams, num_params, types) {
        Ok(()) => {
            *env = scratch;
            return Ok(())
        }
        Err(e) => e,
    };
    match crate::nested::plan(env, lparams, num_params, types) {
        Ok(Some(plan)) => crate::nested::add(env, lparams, num_params, types, &plan)
            .map_err(|e| format!("{e}\n… and as it stands the declaration is not checkable:\n{plain}")),
        // Not nested: the ordinary rejection is the answer, and it is the one
        // mini gave before this path existed.
        Ok(None) => Err(plain),
        // Nested in a way this module cannot express. Both halves are
        // reported: the rejection mini would have given, and why the
        // specialisation did not get off the ground.
        Err(why) => Err(format!("{plain}\n… the declaration looks nested, and {why}")),
    }
}

/// **One inductive declaration, of one type or of a `mutual … end` block.**
///
/// A block of one is exactly mini-lean's `Environment.add`'s `.inductive` arm;
/// nothing below special-cases it, and the corpus is the regression test for
/// that claim. The generalisations are named where they happen, and there are
/// five: every member's type is checked and their resultant universes must
/// agree; the constructor checks range over all members; large elimination is
/// refused for a block of more than one type; the K-rule needs a block of one;
/// and the recursor telescope binds one motive per member and one minor per
/// constructor **of the whole block**.
fn add_block(
    env: &mut Environment,
    lparams: &[Name],
    num_params: u32,
    types: &[IndType],
) -> R<()> {
    let Some(first) = types.first() else {
        return Err("Inductive declaration with no types".to_string())
    };
    nodup(lparams, &first.name)?;
    let names: Vec<Name> = types.iter().map(|t| t.name).collect();
    let tys: Vec<E> = types.iter().map(|t| t.ty).collect();
    let ctors: Vec<Vec<(Name, E)>> = types.iter().map(|t| t.ctors.clone()).collect();
    let n = u32::try_from(types.len()).expect("block size");
    let num_minors =
        u32::try_from(ctors.iter().map(Vec::len).sum::<usize>()).expect("minor count");

    // The type of each member: its indices and the block's universe.
    //
    // **The universe is the block's, not the member's.** The kernel requires
    // every type in a `mutual … end` block to have the same resultant sort —
    // `nanoda`'s `check_inductive_specs_mutual1` asserts it, and it is what
    // makes one shared motive level meaningful. The parameter telescopes must
    // agree too, which is `def_eq_params` against the first member.
    let mut num_indices: Vec<u32> = Vec::with_capacity(types.len());
    let mut ind_level: Option<Level> = None;
    for t in types {
        let mut c = Checker::new(env);
        let go = |c: &mut Checker<'_, '_>| -> R<(u32, Level)> {
            c.check_type(&t.ty)?;
            c.scoped(|c| {
                let b = c.open_forall_push(num_params, &t.ty)?;
                let (ni, b) = c.open_forall_eager_push(&b)?;
                Ok((ni, as_sort(&b)?))
            })
        };
        let (ni, lvl) = go(&mut c)
            .map_err(|e| format!("{e}\n… while checking type of inductive {}", t.name))?;
        match &ind_level {
            None => ind_level = Some(lvl),
            Some(l0) => {
                let mut c = Checker::new(env);
                c.def_eq_params(num_params, &first.ty, &t.ty).map_err(|e| {
                    format!(
                        "{e}\n… while checking that the parameters of {} match those of {}",
                        t.name, first.name
                    )
                })?;
                assert_level_eq(&lvl, l0).map_err(|e| {
                    format!(
                        "{e}\n… the types of a mutual block must live in one universe, \
                         but {} is at {lvl} and {} at {l0}",
                        t.name, first.name
                    )
                })?;
            }
        }
        num_indices.push(ni);
    }
    let ind_level = ind_level.expect("a non-empty block");

    // A "unit-like" type: one constructor, no fields. Computed per member,
    // with mini-lean's formula unchanged — a member of a block with a single
    // fieldless constructor really does have a single inhabitant, and being
    // inside a block does not change that.
    let mut is_unit: Vec<bool> = Vec::with_capacity(types.len());
    for t in types {
        let u = if t.ctors.len() == 1 {
            let mut c = Checker::new(env);
            c.scoped(|c| {
                let b = c.open_forall_push(num_params, &t.ctors[0].1)?;
                Ok(!matches!(&b.view(), Expr::Forall { .. }))
            })?
        } else {
            false
        };
        is_unit.push(u);
    }

    // Every member goes into the environment before any constructor is
    // checked: a constructor of one member mentions the others.
    for (j, t) in types.iter().enumerate() {
        env.insert_new(
            t.name,
            ConstantInfo::Inductive {
                lparams: lparams.to_vec(),
                ty: t.ty,
                num_params,
                num_indices: num_indices[j],
                ctors: t.ctors.iter().map(|(n, _)| *n).collect(),
                is_unit: is_unit[j],
            },
        )?;
    }

    // Constructor checks, with every member already in the environment.
    {
        let ic = IndCtx {
            names: &names,
            num_indices: &num_indices,
            lparams,
            num_params,
            ind_level: &ind_level,
        };
        let mut c = Checker::new(env);
        for t in types {
            for (ctor_name, ctor_type) in &t.ctors {
                c.check_type(ctor_type).map_err(|e| {
                    format!("{e}\n… while checking type of constructor {ctor_name}")
                })?;
                c.def_eq_params(num_params, &t.ty, ctor_type).map_err(|e| {
                    format!(
                        "{e}\n… while checking parameters of constructor {ctor_name} match those of {}",
                        t.name
                    )
                })?;
                c.scoped(|c| {
                    let b = c.open_forall_push(num_params, ctor_type)?;
                    c.check_ctor_type(&ic, 0, &b)
                })
                .map_err(|e| format!("{e}\n… while checking constructor {ctor_name}"))?;
            }
        }
    }

    for t in types {
        for (ctor_name, ctor_type) in &t.ctors {
            env.insert_new(
                *ctor_name,
                ConstantInfo::Opaque { lparams: lparams.to_vec(), ty: *ctor_type },
            )?;
            // The index §9 zone B reaches the declaration by. Built here, where
            // the relation is known, so that no later pass has to look for it.
            env.owners.insert(*ctor_name, t.name);
        }
    }

    // Large elimination?
    //
    // **A block of more than one type never eliminates large.** This used to be
    // a `TODO (mini-lean's own)` on the empty-constructor branch below, and the
    // branch order is why it was reachable at all: an empty `Prop` in a block
    // would have said `true`. The rule is Lean's own and `nanoda`'s
    // `large_elim_test` has it as the fall-through of a match on the block —
    // an eliminator that took a proof of one member to data would, through the
    // shared minors, take a proof of every member to data.
    let elim_to_sort = {
        if ind_level.is_not_zero() {
            true
        } else if n > 1 {
            false
        } else if first.ctors.is_empty() {
            true
        } else if first.ctors.len() > 1 {
            false
        } else {
            let mut c = Checker::new(env);
            c.elim_to_sort_go(&first.ctors[0].1)?
        }
    };

    // The K-rule applies to an inductive proposition with one fieldless ctor —
    // and to a block of one. `nanoda`'s `init_k_target` says the same with
    // `all_inductives.len() == 1` as its second conjunct.
    let k_type = {
        if ind_level.is_not_zero() || n > 1 || first.ctors.len() != 1 {
            None
        } else {
            let mut c = Checker::new(env);
            c.scoped(|c| {
                let b = c.open_forall_push(num_params, &first.ctors[0].1)?;
                Ok(if matches!(&b.view(), Expr::Forall { .. }) { None } else { Some(b) })
            })?
        }
    };

    let (motive_level, lparams2) = if elim_to_sort {
        let v = fresh_level_name(lparams);
        let mut l = vec![v];
        l.extend(lparams.iter().cloned());
        (Level::param(v), l)
    } else {
        (Level::zero(), lparams.to_vec())
    };
    let us: Rc<[Level]> =
        lparams.iter().map(|n| Level::param(*n)).collect::<Vec<_>>().into();
    let us2: Rc<[Level]> =
        lparams2.iter().map(|n| Level::param(*n)).collect::<Vec<_>>().into();

    let ic = IndCtx {
        names: &names,
        num_indices: &num_indices,
        lparams,
        num_params,
        ind_level: &ind_level,
    };

    // One recursor per member, and the minor positions are block-wide.
    let mut minor_base = 0u32;
    for (k, t) in types.iter().enumerate() {
        let rec_type = {
            let mut c = Checker::new(env);
            let rec_type = c.build_rec_type(&ic, &tys, &ctors, k, &us, &motive_level)?;
            // Sanity check, at the recursor's own (symbolic) level parameters.
            c.check_type(&rec_type).map_err(|e| {
                format!("{e}\n… while checking type of recursor for {}:\n{rec_type}", t.name)
            })?;
            rec_type
        };
        let mut rules: Vec<(Name, E)> = Vec::new();
        for (i, (ctor_name, ctor_type)) in t.ctors.iter().enumerate() {
            let mut c = Checker::new(env);
            let pos = minor_base + u32::try_from(i).expect("constructor index");
            let rhs =
                c.build_rec_rule(&ic, &rec_type, ctor_type, pos, num_minors, &us2)?;
            rules.push((*ctor_name, rhs));
        }
        minor_base += u32::try_from(t.ctors.len()).expect("constructor count");
        let rec_name = Name::str(&t.name, "rec");
        env.owners.insert(rec_name, t.name);
        env.insert_new(
            rec_name,
            ConstantInfo::Recursor {
                lparams: lparams2.clone(),
                ty: rec_type,
                num_params,
                num_motives: n,
                num_minors,
                num_indices: num_indices[k],
                rules,
                k_type,
            },
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::DefKind;

    /// `axiom P : Prop`, `axiom p : P`, `def Id : Prop → Prop := fun q => q`.
    fn env() -> Environment {
        let mut env = Environment::empty();
        let prop = sort(Level::zero());
        let p_ty = Name::simple("P");
        add(&mut env, &Declaration::Axiom { name: p_ty, lparams: vec![], ty: prop })
            .unwrap();
        let pk = konst(p_ty, no_levels());
        add(&mut env, &Declaration::Axiom { name: Name::simple("p"), lparams: vec![], ty: pk })
            .unwrap();
        add(
            &mut env,
            &Declaration::Def {
                name: Name::simple("Id"),
                lparams: vec![],
                ty: forall(prop, sort(Level::zero())),
                value: lam(prop, bvar(0)),
                kind: DefKind::Def,
            },
        )
        .unwrap();
        env
    }

    fn k(n: &str) -> E { konst(Name::simple(n), no_levels()) }

    /// **[`first_reason`]'s four cells**, which are the `Proj` clause's §0.4
    /// rule and are not symmetric in the two routes.
    ///
    /// The asymmetry is the whole content: `zip`'s plain "the left gap wins"
    /// gets three of the four cells right and the fourth — a first route that
    /// said only "not my row" over a second route that named a reason — wrong,
    /// which is the cell `proj_prop` occupies at every class-(T) carrier.
    #[test]
    fn a_route_that_only_said_not_my_row_does_not_own_the_reason() {
        let own = Gap::StructProj(Name::simple("PProd"));
        let a = Gap::Classifier;
        let b = Gap::SymbolicLevel;
        assert_eq!(first_reason(&own, a.clone(), b.clone()), a, "the first route's reason wins");
        assert_eq!(
            first_reason(&own, own.clone(), b.clone()),
            b,
            "…unless it is the clause's own fallback, which is not a reason"
        );
        assert_eq!(
            first_reason(&own, a.clone(), own.clone()),
            a,
            "and the second route's fallback must not displace a real reason"
        );
        assert_eq!(
            first_reason(&own, own.clone(), own.clone()),
            own,
            "neither route said anything, so the clause's own label is what is left"
        );
        // Not "the more specific of the two": the rule is positional, and a
        // second route that names a *different* structure's gap must not
        // outrank the first route's.
        let other = Gap::StructProj(Name::simple("PSigma"));
        assert_eq!(first_reason(&own, other.clone(), b), other);
    }

    /// `body_clause` decides `lvl(b) = 0`; `term_clause` decides
    /// `lvl(type of e) = 0`. The pairs below are the ones that separate the two.
    #[test]
    fn the_two_classifiers_answer_one_level_apart() {
        let env = env();
        let mut c = Checker::new(&env);
        // `P : Prop`, so `P` is a proposition and `p : P` is a proof.
        assert_eq!(c.body_clause(&k("P")).unwrap(), Clause::Prop);
        assert_eq!(c.term_clause(&k("p")).unwrap(), Clause::Prop, "`p : P : Prop`, so `p` is a proof");
        // …and `P` itself is not a *proof*: its type is `Prop`, whose type is
        // `Type 0`. This is the one level of separation between the two.
        assert_eq!(c.term_clause(&k("P")).unwrap(), Clause::Type);
        // `Prop : Type 0`, so `Prop` is *not* a proposition, and `Prop` is not
        // a proof either.
        assert_eq!(c.body_clause(&sort(Level::zero())).unwrap(), Clause::Type);
        assert_eq!(c.term_clause(&sort(Level::zero())).unwrap(), Clause::Type);
    }

    /// **The redex case, which nanoda's syntactic walk needs a special arm
    /// for.** `Id P` beta-reduces to `P`; both must classify the same, or the
    /// delta/beta step relating them has nothing to prove. Mini gets this from
    /// `is_prop` whnf-ing, with no redex arm anywhere.
    #[test]
    fn a_redex_and_its_contractum_classify_alike() {
        let env = env();
        let mut c = Checker::new(&env);
        let redex = app(k("Id"), k("P"));
        assert_eq!(c.body_clause(&redex).unwrap(), c.body_clause(&k("P")).unwrap());
        assert_eq!(c.body_clause(&redex).unwrap(), Clause::Prop);
        // And a literal `λ`-redex, not just a delta one.
        let lam_redex = app(lam(sort(Level::zero()), bvar(0)), k("P"));
        assert_eq!(c.body_clause(&lam_redex).unwrap(), Clause::Prop);
    }

    /// A `let` denotes its expansion and classifies with it — again with no
    /// `let` arm in the classifier, because `infer_type` substitutes.
    #[test]
    fn a_let_classifies_with_its_expansion() {
        let env = env();
        let mut c = Checker::new(&env);
        let e = crate::expr::let_(sort(Level::zero()), k("P"), bvar(0));
        assert_eq!(c.body_clause(&e).unwrap(), Clause::Prop);
    }

    // ───────────────────────────────────── the threaded operations ──

    /// An environment with a **three**-argument projection, `sel := λ a b c. b`,
    /// so that reducing `sel X Y Z` pins the *order* of the argument stack. Two
    /// arguments cannot tell a left fold from a right one, and picking the
    /// middle of three cannot be got right by accident.
    ///
    /// `X`/`Y`/`Z` are `opaque` rather than axioms, for a reason the first
    /// version of this test got wrong: beta's premise is `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`, and
    /// an *axiom's* inhabitation is a model assumption with no derivation, so
    /// the certificate would gap for a reason that has nothing to do with
    /// `whnf`. An `opaque` definition gets its typing from its value and keeps
    /// no defining equation, so it is inert under delta *and* inhabited.
    fn quantified(depth: u32) -> E {
        let prop = sort(Level::zero());
        let mut e = bvar(0);
        for _ in 0..depth {
            e = forall(prop, e);
        }
        e
    }

    fn decls3() -> Vec<Declaration> {
        let prop = sort(Level::zero());
        let mut v: Vec<Declaration> = ["X", "Y", "Z"]
            .iter()
            .enumerate()
            .map(|(i, n)| Declaration::Def {
                name: Name::simple(n),
                lparams: vec![],
                ty: prop,
                // Three distinct propositions, so the middle one is
                // recognisable: `∀p. p`, `∀p∀q. q`, `∀p∀q∀r. r`.
                value: quantified(u32::try_from(i).unwrap() + 1),
                kind: DefKind::Opaque,
            })
            .collect();
        let sel_ty = arrow(prop, arrow(prop, arrow(prop, prop)));
        v.push(Declaration::Def {
            name: Name::simple("sel"),
            lparams: vec![],
            ty: sel_ty,
            value: lam(prop, lam(prop, lam(prop, bvar(1)))),
            kind: DefKind::Def,
        });
        v
    }

    fn env3() -> (Environment, std::collections::HashMap<Name, Vec<Vec<u32>>>) {
        let mut env = Environment::empty();
        for d in decls3() {
            add(&mut env, &d).unwrap();
        }
        (env, Default::default())
    }

    /// **`whnf` returns a certificate, and it is about the right endpoints.**
    ///
    /// `sel X Y Z` is one delta unfold followed by three beta contractions, and
    /// the result is `Y` — the *middle* argument, which is what makes this test
    /// able to fail. The conversion's conclusion is checked to be exactly
    /// `⟦sel X Y Z⟧ = ⟦Y⟧`, so a certificate about the wrong redex, or one that
    /// stopped at the body symbol `t(h⃗,x)` instead of unfolding to `⟦Y⟧`, is a
    /// failure rather than a pass.
    #[test]
    fn whnf_certifies_a_delta_and_three_betas() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let e = app_n(k("sel"), &[k("X"), k("Y"), k("Z")]);

        let mut c = Checker::threaded(&env, &mut ip);
        let t = c.infer_type(&e).expect("infer");
        let tm = t.tm.clone().expect("⟦sel X Y Z⟧");
        let (reduct, conv) = c.whnf_conv(&e, Some(tm.clone()), &Gap::NoEndpoint).expect("whnf");
        assert_eq!(reduct, k("Y"), "the middle argument, not the first or the last");
        let thm = conv.ev.thm().expect("whnf certificate").clone();
        drop(c);

        let y = ip
            .get_const(&(Name::simple("Y"), vec![]))
            .expect("Y is in the store")
            .term
            .clone();
        assert_eq!(*thm.concl(), kernel::Formula::eq(tm, y), "wrong endpoints");
        assert!(thm.hyps().is_empty(), "no binder is open, so Γ must be empty");
    }

    /// **`assert_def_eq` returns a `Conv` about the endpoints it was handed.**
    ///
    /// `sel X Y Z` against `Y` — the two sides are syntactically unrelated and
    /// only the reduction relates them, so this cannot pass on reflexivity. The
    /// symmetric call is checked too, because the composition
    /// `⟦e1⟧ = ⟦a⟧ = ⟦b⟧ = ⟦e2⟧` is not symmetric in the code and a `symm` in
    /// the wrong place would show up on exactly one side.
    #[test]
    fn assert_def_eq_certifies_both_directions() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let e = app_n(k("sel"), &[k("X"), k("Y"), k("Z")]);

        let mut c = Checker::threaded(&env, &mut ip);
        let lhs = c.infer_type(&e).expect("infer").tm.expect("⟦sel X Y Z⟧");
        let rhs = c.infer_type(&k("Y")).expect("infer").tm.expect("⟦Y⟧");
        assert_ne!(lhs, rhs, "the two sides must not already be the same term");

        let fwd = c
            .assert_def_eq(&e, Some(lhs.clone()), &k("Y"), Some(rhs.clone()))
            .expect("defeq");
        assert_eq!(
            *fwd.ev.thm().expect("forward certificate").concl(),
            kernel::Formula::eq(lhs.clone(), rhs.clone())
        );
        let back = c
            .assert_def_eq(&k("Y"), Some(rhs.clone()), &e, Some(lhs.clone()))
            .expect("defeq");
        assert_eq!(
            *back.ev.thm().expect("backward certificate").concl(),
            kernel::Formula::eq(rhs, lhs)
        );
        // A rejection is still a rejection, and it needs no evidence.
        assert!(c.assert_def_eq(&e, None, &k("X"), None).is_err());
    }

    /// **A δ-redex inside an argument, under a binder, certified** — the
    /// obligation `072_sortElimProp2Rec` will present and the one nothing in
    /// `069`–`071` had.
    ///
    /// `SortElimProp2.mk`'s second result index is `id.{1} Bool b1`, which is
    /// what makes the index non-invertible and the eliminator small. It also
    /// means the *declared* minor is `motive b2 b1 (mk b b1 b2)` while the
    /// recursor's own is `motive b2 (id.{1} Bool b1) (mk b b1 b2)`: two `Π`
    /// types that are definitionally equal only through δ **and** β on `id`,
    /// inside an argument of a proof-valued application, under two binders.
    ///
    /// It was flagged as unmeasurable until `072`'s carrier lands. It is not:
    /// the question is a *conversion* between two Lean expressions and needs no
    /// carrier at all. Two cells, one build — the same corner walk that settled
    /// `(np, kᵢ)`:
    ///
    /// | shape | certified |
    /// | --- | --- |
    /// | `∀ (x : B). C x (Idf B x)` against `∀ (x : B). C x x` | yes |
    /// | `∀ (x y : B). C x (Idf B y)` against `∀ (x y : B). C x y` | yes |
    ///
    /// The redex is under a binder in both, so the certificate travels through
    /// the binder congruence rather than through `whnf` alone; the second puts
    /// it on an argument that is not the innermost binder, which is `072`'s
    /// depth. `B` and `C` are **opaque**, so nothing unfolds them and the
    /// conversion cannot go round the argument. Both directions are asked,
    /// because the composition is not symmetric in the code.
    ///
    /// **`⟦·⟧` does not see the redex at all**, which is why this works and is
    /// worth stating: `⟦Idf B x⟧` is `app(app(⟦Idf⟧,⟦B⟧),⟦x⟧)` and the defeq is
    /// carried by the stored defining axiom of `Idf` plus β, exactly as any
    /// other δ step is. Nothing about `id` is special; what is special is that
    /// `072` is the first declaration whose *recursor type* needs one.
    #[test]
    fn a_delta_redex_in_an_argument_converts_under_a_binder() {
        let ty0 = sort(Level::zero().succ());
        let prop = sort(Level::zero());
        // `B` and `C` are **opaque**, so nothing unfolds them and the
        // conversion has to go through the argument rather than round it.
        let decls = vec![
            Declaration::Def {
                name: Name::simple("B"),
                lparams: vec![],
                ty: ty0,
                value: prop,
                kind: DefKind::Opaque,
            },
            Declaration::Def {
                name: Name::simple("Idf"),
                lparams: vec![],
                ty: forall(ty0, arrow(bvar(0), bvar(1))),
                value: lam(ty0, lam(bvar(0), bvar(0))),
                kind: DefKind::Def,
            },
            Declaration::Def {
                name: Name::simple("C"),
                lparams: vec![],
                ty: arrow(k("B"), arrow(k("B"), prop)),
                value: lam(k("B"), lam(k("B"), forall(prop, bvar(0)))),
                kind: DefKind::Opaque,
            },
        ];
        let mut env = Environment::empty();
        for d in &decls {
            add(&mut env, d).unwrap();
        }
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls, &Default::default(), &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);
        let redex = |arg: E| app_n(k("Idf"), &[k("B"), arg]);

        // One binder, then two — `072`'s own depth, with the redex on the
        // argument that is *not* the innermost binder.
        let one = forall(k("B"), app_n(k("C"), &[bvar(0), bvar(0)]));
        let one_id = forall(k("B"), app_n(k("C"), &[bvar(0), redex(bvar(0))]));
        let two = forall(k("B"), forall(k("B"), app_n(k("C"), &[bvar(1), bvar(0)])));
        let two_id =
            forall(k("B"), forall(k("B"), app_n(k("C"), &[bvar(1), redex(bvar(0))])));

        for (tag, l, r) in [("one binder", one, one_id), ("two binders", two, two_id)] {
            let li = c.infer_type(&l).expect("infer lhs");
            let ri = c.infer_type(&r).expect("infer rhs");
            let lt = li.tm.clone().unwrap_or_else(|| panic!("{tag}: ⟦lhs⟧ {:?}", li.ev.gap()));
            let rt = ri.tm.clone().unwrap_or_else(|| panic!("{tag}: ⟦rhs⟧ {:?}", ri.ev.gap()));
            assert_ne!(lt, rt, "{tag}: the redex must not vanish in the interpretation");
            for (a, at, bb, bt) in [(&l, &lt, &r, &rt), (&r, &rt, &l, &lt)] {
                let conv = c
                    .assert_def_eq(a, Some(at.clone()), bb, Some(bt.clone()))
                    .unwrap_or_else(|e| panic!("{tag}: accepted, but {e}"));
                let thm = conv
                    .ev
                    .thm()
                    .unwrap_or_else(|| panic!("{tag}: uncertified — {:?}", conv.ev.gap()));
                assert_eq!(*thm.concl(), kernel::Formula::eq(at.clone(), bt.clone()));
                assert!(thm.hyps().is_empty(), "{tag}: and unconditional");
            }
        }
    }

    /// **A green path records nothing in the blocker's trail.**
    ///
    /// `Ev::missing` is `#[track_caller]` and, armed, files the site into
    /// [`crate::blocker`]'s trail — so it must be *evaluated* only where a
    /// derivation actually gave up. `unwrap_or(Ev::missing(..))` evaluates its
    /// argument whether or not the `Option`/`Result` needed it, which files a
    /// gap at a line that succeeded. Three λ/congruence clauses discharged a
    /// scope that way; measured on this fixture's three-binder λ alone it was
    /// three phantom `Gap::Skeleton` mints, and on `rec_prop`'s `And.rec` at
    /// both σ it was 22.
    ///
    /// The trail is what decides which blocker to work on next, so a mint at a
    /// line that did not give up is not cosmetic: with `TRAIL_CAP` mints kept
    /// per pair, a phantom *evicts* a real one.
    ///
    /// Each part is green — asserted, because a fixture that stopped
    /// interpreting would pass this vacuously.
    #[test]
    fn a_green_path_mints_no_gap() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);
        let prop = sort(Level::zero());

        // **The value-λ clause** — `λ p q r. q`, three binders, each closing a
        // scope that discharges. One binder would not separate "once" from
        // "per binder".
        let value_lam = lam(prop, lam(prop, lam(prop, bvar(1))));
        crate::blocker::arm(true);
        crate::blocker::enter_pair();
        let t = c.infer_type(&value_lam).expect("infer");
        let trail = crate::blocker::trail();
        assert!(t.ev.is_proved() && t.tm.is_some(), "the λ fixture is green: {:?}", t.ev.gap());
        assert!(trail.is_empty(), "a green value λ gave up nowhere, so nothing is filed: {trail:?}");

        // **The proof-λ clause** — `λ h:X. h`, which takes the conditional
        // route rather than the `dprod` one, and is the second of the three
        // sites.
        crate::blocker::enter_pair();
        let t = c.infer_type(&lam(k("X"), bvar(0))).expect("infer");
        let trail = crate::blocker::trail();
        assert!(t.ev.is_proved() && t.tm.is_some(), "the proof-λ fixture is green: {:?}", t.ev.gap());
        assert!(trail.is_empty(), "a green proof λ gave up nowhere either: {trail:?}");

        // **The binder-congruence clause** — `∀p. p` against `∀p. (λr. r) p`,
        // where the bodies differ by a β and the pointwise evidence is
        // discharged out of the binder's scope. Here the trail is *not* empty:
        // `assert_def_eq` legitimately mints `Gap::NoEndpoint` for the
        // sub-conversions it is not asked to certify. `Gap::Skeleton` is the
        // one this clause can file, and it must not.
        let l = forall(prop, bvar(0));
        let r = forall(prop, app(lam(prop, bvar(0)), bvar(0)));
        let lt = c.infer_type(&l).expect("infer lhs").tm.expect("⟦∀p. p⟧");
        let rt = c.infer_type(&r).expect("infer rhs").tm.expect("⟦∀p. (λr. r) p⟧");
        crate::blocker::enter_pair();
        let conv = c.assert_def_eq(&l, Some(lt), &r, Some(rt)).expect("defeq");
        let trail = crate::blocker::trail();
        crate::blocker::arm(false);
        assert!(conv.is_proved(), "the congruence fixture is green: {:?}", conv.ev.gap());
        assert!(
            !trail.iter().any(|m| m.gap == Gap::Skeleton),
            "a discharged congruence files no Gap::Skeleton: {trail:?}"
        );
    }

    /// **A conversion nobody asked for files nothing** — the *subtree* form of
    /// the rule the two tests either side of this one state per call, and the
    /// one the instrument was missing.
    ///
    /// `is_def_eq` and `whnf` hand in no endpoints: their callers want a `bool`
    /// and an expression, and the `Ev` the walk builds is dropped one frame up.
    /// Everything inside them therefore mints `no-endpoint` — `def_eq_struct`'s
    /// `Const` arm, `delta_evidence`'s first line, `beta_evidence`'s — and none
    /// of it is evidence about the pair being checked. The mint sites cannot
    /// tell: `def_eq_struct`'s `Const` arm is one line whether the conversion
    /// was asked for or not. [`crate::blocker::Quiet`] marks the entry instead.
    ///
    /// **What it was costing**, on `nested_model`'s `iotaNode`: 4 108 mints,
    /// 2 675 + 918 of them at those first two lines, against a `TRAIL_CAP` of
    /// 4 096 — so the pair overflowed and the trail evicted from the front,
    /// which is where the origin is. The same pair's trail is **17** mints now
    /// and names [`Checker::proof_point_leg`]'s three sites.
    ///
    /// The fixture below is `sel X Y Z` against `Y`, which is a delta and three
    /// betas: through `is_def_eq` it must file nothing at all, and through
    /// `assert_def_eq` with both endpoints it is green and also files nothing —
    /// the second half being what says the quieting is about the *asking* and
    /// not about the walk.
    #[test]
    fn a_conversion_nobody_asked_for_files_nothing() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);
        let e = app_n(k("sel"), &[k("X"), k("Y"), k("Z")]);

        // **The acceptance-only route.** It decides `true`, and a decision is
        // not giving up however many `no-endpoint`s the walk had to shrug at.
        crate::blocker::arm(true);
        crate::blocker::enter_pair();
        let yes = c.is_def_eq(&e, &k("Y")).expect("decide");
        let quiet_trail = crate::blocker::trail();
        assert!(yes, "`sel X Y Z` is `Y`; a fixture that stopped being def-eq measures nothing");
        assert!(
            quiet_trail.is_empty(),
            "an acceptance-only conversion filed {} mints: {quiet_trail:?}",
            quiet_trail.len()
        );

        // **…and the scope closed.** A `Quiet` that leaked would silence every
        // mint for the rest of the run, which would make this instrument worse
        // than the noise it replaces and would make every "the trail is empty"
        // assertion in this file pass vacuously. `is_quiet` is asserted rather
        // than inferred from a later emptiness, because an empty trail is
        // exactly what a leak looks like.
        assert!(
            !crate::blocker::is_quiet(),
            "a `Quiet` scope outlived the call that opened it"
        );

        // **The acceptance-only `whnf`, on its own.** `is_def_eq` above enters
        // through `def_eq_ev`, which quietens the whole subtree, so it cannot
        // distinguish the two sites — and `whnf` has callers of its own
        // (`is_prop`, the recursor arm's major, `proj_data`'s subject) that
        // never pass through `def_eq_ev` at all. `sel X Y Z` is a δ and three
        // βs, so this is four mints without the scope.
        crate::blocker::enter_pair();
        let reduct = c.whnf(&e).expect("whnf");
        let whnf_trail = crate::blocker::trail();
        assert_eq!(reduct, k("Y"), "the middle argument; the walk really ran");
        assert!(
            whnf_trail.is_empty(),
            "an acceptance-only `whnf` filed {} mints: {whnf_trail:?}",
            whnf_trail.len()
        );

        crate::blocker::enter_pair();
        let t = c.infer_type(&e).expect("infer");
        let tm = t.tm.clone().expect("⟦sel X Y Z⟧");
        let yt = c.infer_type(&k("Y")).expect("infer Y").tm.expect("⟦Y⟧");
        let conv = c.assert_def_eq(&e, Some(tm), &k("Y"), Some(yt)).expect("defeq");
        let asked_trail = crate::blocker::trail();
        crate::blocker::arm(false);
        assert!(conv.is_proved(), "the threaded conversion is green: {:?}", conv.ev.gap());
        assert!(
            asked_trail.is_empty(),
            "a green threaded conversion filed {} mints: {asked_trail:?}",
            asked_trail.len()
        );
    }

    /// **The proof-point leg reads the reduct, and refuses one that is not
    /// `•`** — [`Checker::proof_point_leg`]'s two answers, at the unit.
    ///
    /// The end-to-end witness is `mini/tests/fixtures/whnf_of_a_proof.lean` and
    /// it measures the *positive* answer only: everything in the fixture
    /// directory that reaches this leg reduces one proof-valued application to
    /// another, so `⟦to⟧` is `•` every time. **A mutation that deleted the
    /// `to_tm == point` comparison survived nine tests**, including the whole
    /// tutorial corpus and `nested_model`'s table, and this is what kills it.
    ///
    /// The refused input is a *proposition* rather than a proof — `X : Prop`,
    /// whose interpretation is the set `⟦X⟧` and emphatically not `•`. That is
    /// the same shape as the reachable one the leg's own note names, a proof
    /// that reduces to a bare constant or a scope variable: what those have in
    /// common is that `⟦·⟧` does not collapse them, and the leg has no theorem
    /// to offer unless it does. Under the mutant this pair comes back
    /// `⊢ • = •` *stated as* `⟦e⟧ = ⟦X⟧`, which is a true theorem about the
    /// wrong terms — it degrades to a `conv-compose` downstream rather than
    /// lying, but only where something downstream composes.
    #[test]
    fn the_proof_point_leg_refuses_a_reduct_that_is_not_the_point() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let point = ip.point();
        let mut c = Checker::threaded(&env, &mut ip);

        // **The positive.** `λ h:X. h` is a proof — its type `X → X` is a
        // `Prop` — so §6.2 sends it to `•` and the leg answers `⊢ • = •`.
        let proof = lam(k("X"), bvar(0));
        assert_eq!(
            c.infer_type(&proof).expect("infer").tm,
            Some(point.clone()),
            "the fixture is a proof; if `⟦λh:X. h⟧` stopped being `•` this test measures nothing"
        );
        let ev = c
            .proof_point_leg(&Some(point.clone()), &proof)
            .expect("a proof reduct is `•` and the leg says so");
        assert_eq!(
            ev.thm().map(|t| t.concl().clone()),
            Some(kernel::Formula::eq(point.clone(), point.clone())),
            "the leg's theorem is reflexivity at the point and nothing else"
        );

        // **The negative.** `X` is a proposition, not a proof: `⟦X⟧` is a set.
        assert_ne!(
            c.infer_type(&k("X")).expect("infer").tm,
            Some(point.clone()),
            "`⟦X⟧` is a set; a run in which it is `•` has no negative case left"
        );
        assert!(
            c.proof_point_leg(&Some(point.clone()), &k("X")).is_none(),
            "the leg offered a theorem about a reduct it never interpreted to `•`"
        );

        // …and the *caller's* half of the guard, which the corpus does exercise:
        // handed no endpoint there is nothing to be reflexive about.
        assert!(
            c.proof_point_leg(&None, &proof).is_none(),
            "the leg answered a walk that was never tracking an interpretation"
        );
    }

    /// **A decision that succeeded files nothing** — the other half of
    /// [`a_green_path_mints_no_gap`], and the half that was wrong.
    ///
    /// `is_prop_or_unit_ev` answers *is this a proof's type?*. **"No" is an
    /// answer**, and the three ways of reaching it — the type's head is not a
    /// constant, it is a constant that is not an inductive, it is an inductive
    /// that is not unit-like — used to pair their `false` with an `Ev::missing`
    /// nobody read. `def_eq_ev` destructures the pair and takes the other
    /// branch; the `Ev` existed only to fill the slot. But `Ev::missing` is
    /// `#[track_caller]`, so each filled slot put a `no-endpoint` or a
    /// `unit-like(T)` into the blocker's trail for the ordinary business of
    /// deciding that a set is a set. On `mutual_aux_encoding`'s first blocked
    /// pair that was `unit-like(Tag)`, `unit-like(Aux)` and a fifth of the
    /// `no-endpoint` mints — and with `TRAIL_CAP` mints kept per pair, a
    /// phantom evicts a real one.
    ///
    /// The function returns `Option<Ev>` now, so a negative answer has no slot
    /// to fill: for the first two branches the **type** is the guard, and what
    /// is asserted here is that the green path they sit on is silent. The
    /// third branch is asserted at the gap it used to mint, `Gap::UnitLike`,
    /// which no other site in the crate constructs.
    #[test]
    fn deciding_that_something_is_not_a_proof_mints_no_gap() {
        let (mut env, sched) = env3();
        // An **opaque** `D : Type 0`, so `whnf` leaves the head a constant and
        // the second negative branch is the one taken. Transparent, it would
        // δ-reduce to `Prop` and take the first. And a two-constructor
        // `E2 : Type`, which is an inductive and is emphatically not
        // unit-like — the third branch, the one that minted `Gap::UnitLike`.
        let e2 = Name::simple("E2");
        let more = vec![
            Declaration::Def {
                name: Name::simple("D"),
                lparams: vec![],
                ty: sort(Level::zero().succ()),
                value: sort(Level::zero()),
                kind: DefKind::Opaque,
            },
            Declaration::Inductive {
                name: e2,
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::zero().succ()),
                ctors: vec![
                    (Name::str(&e2, "a"), konst(e2, no_levels())),
                    (Name::str(&e2, "b"), konst(e2, no_levels())),
                ],
            },
        ];
        let mut decls = decls3();
        for d in &more {
            add(&mut env, d).unwrap();
            decls.push(d.clone());
        }
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls, &sched, &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);

        crate::blocker::arm(true);
        for (what, ty) in [
            ("a sort-headed type", sort(Level::zero().succ())),
            ("a constant that is not an inductive", k("D")),
        ] {
            crate::blocker::enter_pair();
            let ans = c.is_prop_or_unit_ev(&ty, true).expect("the classifier answers");
            let trail = crate::blocker::trail();
            assert!(ans.is_none(), "{what} is not a proof's type");
            assert!(
                trail.is_empty(),
                "{what}: answering *no* is not giving up, so nothing is filed: {trail:?}"
            );
        }

        // **The unit-like probe**, asserted at the gap only it can mint —
        // `Gap::UnitLike` has one construction site in the crate. This is the
        // branch the corpus reaches at every `Type`-valued inductive that is
        // not a one-field structure: `unit-like(Tag)` and `unit-like(Aux)` on
        // `mutual_aux_encoding` were exactly this, twice per pair.
        crate::blocker::enter_pair();
        let ans = c.is_prop_or_unit_ev(&k("E2"), true).expect("the classifier answers");
        let trail = crate::blocker::trail();
        assert!(ans.is_none(), "a two-constructor inductive is not unit-like");
        assert!(
            !trail.iter().any(|m| matches!(m.gap, Gap::UnitLike(_))),
            "a *negative* unit-like probe files no Gap::UnitLike: {trail:?}"
        );

        // **Non-vacuity.** `X : Prop`, so `X` is a proposition and the gate
        // must fire — uncertified, with the caller's own absence.
        crate::blocker::enter_pair();
        let ans = c.is_prop_or_unit_ev(&k("X"), false).expect("the classifier answers");
        crate::blocker::arm(false);
        assert_eq!(
            ans.as_ref().and_then(Ev::gap),
            Some(&Gap::NoEndpoint),
            "a proposition takes the irrelevance branch, and uncertified it has no witness"
        );
    }

    /// **`whnf` hands back no certificate when it was handed no endpoint**, and
    /// that is not a drop: `is_def_eq`'s callers want a `bool` and there is no
    /// downstream step that would have to re-derive the equation.
    ///
    /// **And it does not file the absence.** `why` is the *caller's* reason,
    /// already chosen and, where it came from an `Ev`, already recorded at the
    /// site that chose it; wrapping it in `Ev::missing` again would make this
    /// one line the top of every trail. It was: on a single `mutual_aux_encoding`
    /// pair, twenty of the thirty-odd mints. `blocker`'s own rule — re-wrapping
    /// is not minting — applied at the place that violated it hardest.
    #[test]
    fn an_uncertified_whnf_reports_a_named_absence() {
        let (env, _) = env3();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let e = app_n(k("sel"), &[k("X"), k("Y"), k("Z")]);
        let (reduct, conv) = c.whnf_conv(&e, None, &Gap::NoEndpoint).expect("whnf");
        assert_eq!(reduct, k("Y"), "the reduction is unaffected by the certificate");
        assert_eq!(conv.ev.gap(), Some(&Gap::NoEndpoint));

        // **A reduction with no steps**, so the `acc` arm is the only thing
        // that could file anything — and the reason that comes back is the
        // caller's own, not this function's label.
        crate::blocker::arm(true);
        crate::blocker::enter_pair();
        let (reduct, conv) = c.whnf_conv(&k("X"), None, &Gap::FunEta).expect("whnf");
        let trail = crate::blocker::trail();
        crate::blocker::arm(false);
        assert_eq!(reduct, k("X"), "an opaque constant is already in normal form");
        assert_eq!(conv.ev.gap(), Some(&Gap::FunEta), "§0.4: the caller's reason, unrelabelled");
        assert!(trail.is_empty(), "and propagating it is not minting it: {trail:?}");
    }

    /// **The `Π` `Prop` clause is refused when the codomain's own membership
    /// does not witness `⟦B⟧ ∈ U₀`** — `pi_evidence`'s `n2 == 0` branch.
    ///
    /// No Lean declaration can exhibit this and that is the point: `l2` is
    /// Lean's own sort, computed by mini's `infer`/`whnf`/`as_sort`, so the
    /// input under test is *a defect in mini's inference*, and the only way to
    /// present one is to hand the rule a level and a witness that disagree.
    /// Which is what this does: the codomain is `Prop`, whose membership is
    /// `⟦Sort 0⟧ ∈ ⟦Sort 1⟧`, offered with `l2 := 0`.
    ///
    /// Unguarded the call **succeeds** — `cond_typing` is unconditional, so it
    /// returns a real theorem, `⟦Π x:Prop. Prop⟧ ∈ ⟦Prop⟧`, about a
    /// conditional singleton that is not the interpretation of that `Π` at
    /// all. Nothing downstream can tell: every later step is a true statement
    /// about the term this one minted. That is the whole failure mode, and the
    /// non-vacuity half below is what stops the guard from being a rule that
    /// refuses everything.
    #[test]
    fn the_pi_prop_clause_refuses_a_codomain_that_is_not_witnessed_in_u0() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);
        let prop = sort(Level::zero());
        // `⟦Prop⟧ ∈ ⟦Sort 1⟧` — a perfectly good typing, of a codomain that is
        // *not* in `U₀`.
        let t1 = c.infer_type(&prop).expect("infer Prop");
        assert_eq!(t1.ev.mem_set(), Some(ip_sort(&c, 1)), "the domain's own witness");
        // `⟦X⟧ ∈ ⟦Sort 0⟧` — `X : Prop`, the codomain the clause is for.
        let tb = c.infer_type(&k("X")).expect("infer X");
        assert_eq!(tb.ev.mem_set(), Some(ip_sort(&c, 0)), "X : Prop, so ⟦X⟧ ∈ U₀");

        let pi = |c: &mut Checker<'_, '_>, tb: &Typing| {
            let saved = c.open_slot(prop, t1.tm.clone());
            let w = c.current_var();
            let out = c.pi_evidence(&t1, tb, w, false, &Level::zero(), &Level::zero());
            c.close_slot(saved);
            out
        };

        let (tm, ev) = pi(&mut c, &tb);
        assert!(tm.is_some() && ev.is_proved(), "the real clause still derives: {:?}", ev.gap());

        let (tm, ev) = pi(&mut c, &t1);
        assert_eq!(ev.gap(), Some(&Gap::ConvCompose("pi-cond-witness")));
        assert!(tm.is_none(), "and no interpretation is minted from the refused clause");
    }

    /// **The `Π`-`Prop` clause's evidence carries no hypothesis** — which is
    /// the whole licence for its abandoned [`Closed`].
    ///
    /// The clause closes its binder and drops the discharge. That is sound
    /// only if nothing derived under the binder crosses the close, and
    /// `cond_typing` being unconditional *by construction* is an argument
    /// about `Interp`, not about this clause. This is the same claim measured
    /// where it is spent: the binder is opened, the clause runs, and what
    /// comes back has an empty `Γ` — so the `Closed` had nothing to discharge
    /// and abandoning it strands nothing.
    ///
    /// Deliberately **not** an assertion inside `pi_evidence`: an unconditional
    /// theorem is what `cond_in_u0` states, and a runtime check on every `Π`
    /// would be a guard that fails on nothing. Here it is a fact pinned once.
    #[test]
    fn the_pi_prop_clauses_certificate_leaves_no_hypothesis_behind() {
        let (env, sched) = env3();
        let mut ip = Interp::new();
        crate::ledger::Ledger::run(&env, &decls3(), &sched, &mut ip);
        let mut c = Checker::threaded(&env, &mut ip);
        let prop = sort(Level::zero());
        let t1 = c.infer_type(&prop).expect("infer Prop");
        let tb = c.infer_type(&k("X")).expect("infer X");

        let saved = c.open_slot(prop, t1.tm.clone());
        let w = c.current_var();
        assert!(w.is_some(), "the binder must really be open, or the claim is vacuous");
        let (tm, ev) = c.pi_evidence(&t1, &tb, w, false, &Level::zero(), &Level::zero());
        c.close_slot(saved);

        assert!(tm.is_some(), "the clause must derive, or the assertion below is about nothing");
        let thm = ev.thm().unwrap_or_else(|| panic!("the cond clause gapped: {:?}", ev.gap()));
        assert!(
            thm.hyps().is_empty(),
            "the `Π`-`Prop` clause returned a theorem under `{:?}` — the `Closed` it drops \
             would have been owed that discharge",
            thm.hyps()
        );
    }

    /// `ip.sort(n)`, through the checker's own handle.
    fn ip_sort(c: &Checker<'_, '_>, n: u32) -> Term {
        c.th.as_ref().expect("threaded").ip.sort(n)
    }

    /// **A proof-λ over an uninterpretable domain denotes nothing** — audit
    /// finding L5, as a decision rather than as an unreachable state.
    ///
    /// §6.2's `⟦λ x:α. e⟧ = •` mentions neither `α` nor the binder, so this
    /// branch used to hand the point back beside a `Gap` on the strength of
    /// `prop` alone — a bool from `is_prop_ev` whose own `Ev` it does not hold.
    /// The value branch of the very same `let`-else already returned `None`, so
    /// a syntactic flag was deciding whether an interpretation existed.
    ///
    /// The state is reachable — `rec_acc`'s reversed-relation fixture reaches
    /// it once — but only there, so it is constructed directly here: a domain
    /// whose interpretation is absent, no binder variable, and `prop`. Nothing
    /// end-to-end distinguishes the two behaviours, which is exactly why this
    /// test exists.
    #[test]
    fn a_proof_lambda_over_an_uninterpretable_domain_denotes_nothing() {
        let env = env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let gap = || Typing { ty: sort(Level::zero()), tm: None, ev: Ev::missing(Gap::StrLit) };
        let (tm, ev) =
            c.lam_evidence(&gap(), &gap(), None, true, false, Ev::missing(Gap::StrLit));
        assert!(tm.is_none(), "the point may not be minted from `prop` alone");
        assert_eq!(ev.gap(), Some(&Gap::StrLit), "and the reason is the domain's own");
    }

    /// The classifier is a function: the same expression answers the same way
    /// however often it is asked, with no memo pinning it. That is what makes
    /// `⟦·⟧` a function.
    #[test]
    fn the_classifier_is_deterministic() {
        let env = env();
        let mut c = Checker::new(&env);
        let e = app(k("Id"), k("P"));
        let first = c.body_clause(&e).unwrap();
        for _ in 0..5 {
            assert_eq!(c.body_clause(&e).unwrap(), first);
        }
    }
}
