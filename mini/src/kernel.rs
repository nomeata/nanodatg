//! The port of `MiniKernel/Kernel.lean`.
//!
//! # Interface
//!
//! One file, like the original, and laid out in the original's order so the two
//! can be read side by side: context primitives, the `whnf`/`inferType`/
//! `isProp`/`inferProj`/telescope mutual block, the level order, definitional
//! equality, and `Environment.add`.
//!
//! **This is step (b) of MINI-DESIGN.md §12: acceptance only, no evidence.**
//! Every function returns exactly what mini-lean's returns, and `Result<_,
//! String>` is mini-lean's `Except String`. The evidence types of §5 (`Typing`,
//! `Conv`, `Ev`) do not appear yet; step (c) threads them through these same
//! signatures. Deviating from the original *here* would make the fidelity gate
//! (`mini/tests/tutorial.rs`) meaningless, so where the original is odd — the
//! `whnf` of a codomain sort performed outside the binder's scope in
//! `inferType`'s `.forall` clause, `natLit`'s dropped argument stack,
//! `Level.le`'s incompleteness — the oddity is reproduced and commented.
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

use crate::env::{instantiate_lparams, ConstantInfo, DefKind, Declaration, Environment};
use crate::ev::{BinderClause, BinderRule, Ev, Gap};
use crate::conv::Conv;
use crate::interp::{Interp, LamSite, PiShape};
use crate::scope::{Closed, ScopeToken, Scopes};
use kernel::{FreeVar, Term, Thm};
use crate::expr::{
    app, app_n, arrow, bvar, bvars, forall, get_app, has_bvar, has_const, konst, lam, shift, sort,
    subst, substs, Expr, Level, Name, E,
};
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
    /// `pw` is the discharged family; `raw` the same conversion before
    /// discharge, which the binder-free clause needs instead.
    fn apply(
        &self,
        ip: &mut Interp,
        d1: &Term,
        d2: &Term,
        dom_eq: &Thm,
        pw: &Thm,
        raw: &Thm,
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
            (PiShape::Fs { .. }, PiShape::Fs { .. }) => BinderRule::Fs,
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
        raw: &Thm,
    ) -> Option<Thm> {
        match (&self.0, &self.1) {
            (PiShape::Dep { site: a, .. }, PiShape::Dep { site: b, .. }) => {
                ip.dprod_cong(a, b, d1, d2, dom_eq, pw)
            }
            (PiShape::Prop { site: a, .. }, PiShape::Prop { site: b, .. }) => {
                ip.cond_cong(a, b, d1, d2, dom_eq, pw)
            }
            // The binder-free case needs no Extensionality: the codomain is
            // closed under the binder, so plain congruence over `fs` says it —
            // from the *undischarged* codomain conversion, since discharging
            // would put a vacuous `∀w. (w ∈ A → …)` in front of it and `A` may
            // be empty.
            (PiShape::Fs { .. }, PiShape::Fs { .. }) => ip.fs_cong(dom_eq, raw),
            // **The two `Π` clauses disagreeing is not a wrong classification.**
            // `dep = has_bvar(body, 0)` is syntactic and β-unstable, so two
            // spellings of one type reach here on different clauses with both
            // sides right. The constant-fibre bridge relates them; the family
            // is already exactly its hypothesis, because the `fs` side's
            // `sym_at` is reflexivity. See [`Interp::dprod_fs_bridge`].
            (PiShape::Dep { site, .. }, PiShape::Fs { cod, .. }) => {
                ip.dprod_fs_bridge(site, cod, d1, d2, dom_eq, pw, false)
            }
            (PiShape::Fs { cod, .. }, PiShape::Dep { site, .. }) => {
                ip.dprod_fs_bridge(site, cod, d1, d2, dom_eq, pw, true)
            }
            // A `Prop`-valued `∀` against either: §6.2's proof/value split
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
        PiShape::Fs { .. } => BinderClause::Fs,
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
        _raw: &Thm,
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
/// and `t.hyps()` is within the open scopes' hypotheses (I2). A `Gap` never
/// carries a term it cannot vouch for.
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

/// `sort` — the shape check, not the interpretation.
pub fn as_sort(e: &E) -> R<Level> {
    match &**e {
        Expr::Sort(u) => Ok(u.clone()),
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
struct IndCtx<'a> {
    ind_name: &'a Name,
    lparams: &'a [Name],
    num_params: u32,
    num_indices: u32,
    ind_level: &'a Level,
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
    pub fn new(env: &'e Environment) -> Self { Checker { env, lenv: Vec::new(), th: None } }

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
        let th = self.th.as_mut()?;
        let slot = th.slots.pop()?;
        slot?;
        let tok = th.tokens.pop().expect("a scoped slot has a token");
        Some(th.scopes.close(tok))
    }

    /// Close every binder opened since `saved`, innermost first.
    fn close_slot(&mut self, saved: usize) {
        self.lenv.truncate(saved);
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
    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.lenv.len();
        let r = f(self);
        self.lenv.truncate(saved);
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
            out = forall(self.lenv[len - 1 - i].clone(), out);
        }
        Ok(out)
    }

    /// `mkLambda`.
    fn mk_lambda(&self, n: u32, body: E) -> R<E> {
        let len = self.lenv.len();
        let n = (n as usize).min(len);
        let mut out = body;
        for i in 0..n {
            out = lam(self.lenv[len - 1 - i].clone(), out);
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
        let mut cur = e.clone();
        let mut cur_tm = tm;
        // `stack[0]` is the *first* argument, matching mini-lean's `a :: stack`.
        let mut stack: Vec<E> = Vec::new();
        let mut stack_tms: Vec<Option<Term>> = Vec::new();
        let mut acc = match &cur_tm {
            Some(t) => Conv::refl(e.clone(), t),
            None => Conv::gap(e.clone(), why.clone()),
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
            let node = cur.clone();
            match &*node {
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
                        lparams, num_params, num_minors, num_indices, rules, k_type, ..
                    } = cinfo
                    {
                        let np = *num_params as usize;
                        let nm = *num_minors as usize;
                        let major_pos = np + 1 + nm + *num_indices as usize;
                        let Some(major) = stack.get(major_pos).cloned() else {
                            done!(app_n(node.clone(), &stack))
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
                                let args = stack[..np + 1 + nm].to_vec();
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
                                            Gap::Iota(name.clone())
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
                        let major2 = self.whnf(&major)?;
                        let (head, con_args) = get_app(&major2);
                        let mut fired = None;
                        if let Expr::Const(f, _) = &*head {
                            if let Some((_, rhs)) = rules.iter().find(|(c, _)| c == f) {
                                let fields = slice(&con_args, np, con_args.len());
                                let mut args = stack[..np + 1 + nm].to_vec();
                                args.extend(fields);
                                let rhs = instantiate_lparams(rhs, lparams, ls)?;
                                fired = Some((f.clone(), substs(&rhs, &args, 0)));
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
                            let all = stack[..major_pos + 1].to_vec();
                            let all_tms: Option<Vec<Term>> =
                                stack_tms.get(..major_pos + 1).and_then(|s| s.iter().cloned().collect());
                            let empty = std::collections::HashMap::new();
                            let inst: Option<Vec<u32>> =
                                ls.iter().map(|l| crate::ground::eval(l, &empty)).collect();
                            let attempt = match (cur_tm.clone(), all_tms, inst) {
                                (Some(h), Some(ts), Some(inst)) if major2 == major => {
                                    let rty = instantiate_lparams(cinfo.ty(), lparams, ls)?;
                                    crate::iota_dep::fire(
                                        self, name, &inst, &rty, np, nm, &h, &all, &ts, &cname,
                                        &con_args, &rhs,
                                    )
                                    .ok()
                                }
                                // A major that had to *reduce* to reach its
                                // constructor owes a conversion this route
                                // does not hold, and an acceptance-only `whnf`
                                // is not asking for a certificate at all.
                                _ => None,
                            };
                            stack = stack[major_pos + 1..].to_vec();
                            match attempt {
                                Some((leg, to_tm)) => {
                                    stack_tms =
                                        stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                                    step!(Ev::Proved(leg));
                                    cur_tm = Some(to_tm);
                                }
                                None => {
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
                                    let g = if cur_tm.is_none() {
                                        Gap::NoEndpoint
                                    } else {
                                        Gap::Iota(name.clone())
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
                        // Stuck, but the major *may* have reduced under it. If
                        // it did, the expression changed and the certificate
                        // owes a congruence over that change; the major's own
                        // reduction is not threaded (it is the acceptance-only
                        // `whnf` above), so this is a named absence.
                        //
                        // **It is not an ι rule and no longer says it is.** The
                        // comment above has always said so and the label
                        // contradicted it; instrumented over all 91 exports
                        // this branch mints `0`, so the ι row's 58 conversions
                        // were never evidence about it either way. See
                        // [`Gap::StuckRecursor`].
                        if stack2[major_pos] != stack[major_pos] {
                            step!(Ev::missing(Gap::StuckRecursor(name.clone())));
                        }
                        done!(app_n(node.clone(), &stack2))
                    }
                    done!(app_n(node.clone(), &stack))
                }
                Expr::App(f, a) => {
                    // Peeling an application is not a reduction: no leg. What
                    // it costs is taking `⟦f a⟧ = app(⟦f⟧,⟦a⟧)` apart, which is
                    // one lookup in the applicative structure the
                    // interpretation recorded on the way in.
                    let (f_tm, a_tm) = self.split_app(&cur_tm);
                    stack.insert(0, a.clone());
                    stack_tms.insert(0, a_tm);
                    cur_tm = f_tm;
                    cur = f.clone();
                }
                Expr::Lam { ty, body } if !stack.is_empty() => {
                    let (ty, body) = (ty.clone(), body.clone());
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
                    let s2 = self.whnf(s)?;
                    let stuck =
                        Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: s2.clone() });
                    let (head, args) = get_app(&s2);
                    let Expr::Const(f, _) = &*head else { done!(app_n(stuck, &stack)) };
                    let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind)
                    else {
                        done!(app_n(stuck, &stack))
                    };
                    if ctors.len() != 1 || &ctors[0] != f {
                        done!(app_n(stuck, &stack))
                    }
                    let pos = (*num_params + *idx) as usize;
                    if pos >= args.len() {
                        return Err(format!(
                            "Type error during reduction: projection index {} out of bounds for {s2}",
                            idx + 1
                        ))
                    }
                    // Proj-of-ctor: the structure's projection computation fact,
                    // which needs the inductive interpretation (§9 zone B).
                    step!(Ev::missing(Gap::StructProj(ind.clone())));
                    cur = args[pos].clone();
                    cur_tm = None;
                }
                Expr::NatLit(n) => {
                    // The parser catches these; mini-lean is explicit here too.
                    // Note the original drops `stack` on this branch — a nat
                    // literal is never in head position of an application.
                    if *n > 10 {
                        return Err(
                            "The mini kernel does not support nat literals larger than 10".into()
                        )
                    }
                    let nat = Name::simple("Nat");
                    // The unfolding is reflexivity by §7's choice of
                    // `⟦natLit n⟧`; what is missing is `Nat`'s interpretation,
                    // which is what `cur_tm` being `None` already says.
                    done!(if *n == 0 {
                        konst(Name::str(&nat, "zero"), no_levels())
                    } else {
                        app(konst(Name::str(&nat, "succ"), no_levels()), Rc::new(Expr::NatLit(n - 1)))
                    })
                }
                _ => done!(app_n(node.clone(), &stack)),
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
        let Some(th) = self.th.as_ref() else { return (Ev::missing(Gap::SymbolicLevel), None) };
        let Some(c) = th.ip.get_const(&(name.clone(), inst.clone())) else {
            return (Ev::missing(Gap::NoInterpretation(name.clone(), inst)), None)
        };
        match &c.defeq {
            Some(s) => {
                let thm = s.thm().clone();
                let rhs = thm.concl().as_eq().map(|(_, b)| b);
                (Ev::Proved(thm), rhs)
            }
            None => (Ev::missing(Gap::NoDefiningEquation(name.clone())), None),
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
        let mut ty = rec_ty.clone();
        for (a, a_tm) in args.iter().zip(arg_tms.iter()) {
            let Expr::Forall { ty: dom_e, body } = &*ty.clone() else {
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
        let mut ty = nest_ty.clone();
        let mut out = Vec::with_capacity(args.len());
        for (a, a_tm) in args.iter().zip(arg_tms.iter()) {
            let Expr::Forall { ty: dom_e, body } = &*ty.clone() else {
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
        let why = t.ev.reason(Gap::NoEndpoint);
        let (ty2, conv) = self.whnf_conv(&t.ty, ty_tm, &why)?;
        let ev = t.ev.clone().zip(conv.ev.clone(), |mem, eq| {
            match self.th.as_mut().and_then(|th| th.ip.retarget_set(&mem, &eq)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("whnf-typing-retarget")),
            }
        });
        Ok((ty2.clone(), conv, Typing { ty: ty2, tm: t.tm, ev }))
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
        let Some(have) = ta.ev.mem_set() else { return Err(ta.ev.reason(Gap::NoEndpoint)) };
        if have == *dom {
            return Ok(ta.ev)
        }
        // The domains differ syntactically; the conversion is the price, and
        // it is the strictness delta MINI-DESIGN.md §13 risk 2 names.
        let conv = self
            .assert_def_eq(&ta.ty, Some(have), lam_ty, Some(dom.clone()))
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
        match &**e {
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
                let ty = sort(u.clone().succ());
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
                let Expr::Forall { ty, body } = &*f_ty else {
                    return Err(format!(
                        "Expected a function type in application of {f} to {arg}, got {f_ty}"
                    ))
                };
                let (ty, body) = (ty.clone(), body.clone());
                // Which of §6.2's three `Π` clauses the function's type took,
                // read off the interpretation the call above already produced.
                let shape = tf
                    .ev
                    .mem_set()
                    .and_then(|t| self.th.as_ref().and_then(|th| th.ip.as_pi(&t)));
                let dom_tm = shape.as_ref().map(|s| match s {
                    PiShape::Fs { dom, .. } => dom.clone(),
                    PiShape::Dep { dom, .. } => dom.clone(),
                    PiShape::Prop { dom, .. } => dom.clone(),
                });
                let ta = self.infer_type(arg)?;
                let arg_ty_tm = ta.ev.mem_set();
                let ceq = self.assert_def_eq(&ty, dom_tm.clone(), &ta.ty, arg_ty_tm.clone())?;
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
                let saved = self.open_slot(ty.clone(), t1.tm.clone());
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
                let out_ty = sort(Level::imax(l1.clone(), l2.clone()));
                // **The clause is `l2 == 0`, already computed.** No classifier
                // call: §6.2's `∀` column is exactly a codomain in `Sort 0`.
                let dep = has_bvar(body, 0);
                let (tm, ev) = self.pi_evidence(&t1, &tb, w, dep, &l1, &l2);
                self.close_slot(saved);
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Lam { ty, body } => {
                let t1 = self.infer_type(ty)?;
                let (s1, _, t1) = self.whnf_typing(t1)?;
                as_sort(&s1)?;
                let saved = self.open_slot(ty.clone(), t1.tm.clone());
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
                let out_ty = forall(ty.clone(), tb.ty.clone());
                let dep = has_bvar(&tb.ty, 0);
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
                // What still falls through is a projection that is **not** a
                // proof — a data field of a class-(T) structure, `Prod.fst` and
                // `PProd.fst.{1,1}` — where `⟦projⱼ x⟧` is absent rather than
                // `•` and what is owed is a term-former, not a certificate.
                //
                // §0.4: a projection out of a structure mini cannot interpret
                // is blocked by *that*, not by "projections are unwired". The
                // two are different categories — interpretation scope versus a
                // library item — and stamping the clause's own label on the
                // first would report the project as further behind on the
                // library than it is.
                if sub.is_none() {
                    if let Ok(thm) = crate::proj_prop::typing(self, ind, *idx, s, &ty) {
                        let tm = crate::proj_prop::point_of(self);
                        return Ok(Typing { ty, tm, ev: Ev::Proved(thm) })
                    }
                }
                Ok(Typing { ty, tm: None, ev: Ev::missing(sub.unwrap_or(Gap::StructProj(ind.clone()))) })
            }
            Expr::NatLit(_) => Ok(Typing {
                ty: konst(Name::simple("Nat"), no_levels()),
                tm: None,
                ev: Ev::missing(Gap::NoInterpretation(Name::simple("Nat"), vec![])),
            }),
            Expr::StrLit(_) => Ok(Typing {
                ty: konst(Name::simple("String"), no_levels()),
                tm: None,
                ev: Ev::missing(Gap::StrLit),
            }),
        }
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
                PiShape::Fs { dom, cod } => ip.fs_app(dom, cod, &f_tm, &a_tm, &fm, &am),
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
    /// Returns `⟦Π x:A. B⟧` and `Γ ⊢ ⟦Π x:A. B⟧ ∈ ⟦Sort (imax l1 l2)⟧`. The
    /// three clauses are three different sets and need three different rules:
    ///
    /// * `l2 = 0` — a conditional singleton, in `U₀` **unconditionally**;
    ///   nothing about the fibre is needed, so nothing about it is assumed.
    /// * `l2 > 0`, codomain binder-free — the function space, both premises
    ///   raised to `max(l1,l2)` by the cumulativity table.
    /// * otherwise — the dependent product, `dprod_in_universe_pair_n` at this
    ///   fibre's prefix (LIBRARY-BACKLOG entry 2, which was nanoda's largest
    ///   single `ty_pi` gap row).
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
            let Some(site) = self.ip().and_then(|ip| ip.cond_site(&cod, w)) else {
                return (None, Ev::missing(Gap::Skeleton))
            };
            let tm = self.ip().map(|ip| ip.cond_term(&site, dom.clone()));
            self.close_one();
            let ev = match self.ip().and_then(|ip| ip.cond_typing(&site, dom)) {
                Some(t) => Ev::Proved(t),
                None => Ev::missing(Gap::ConvCompose("pi-cond")),
            };
            return (tm, ev)
        }
        if !dep {
            let tm = self.ip().map(|ip| ip.fs(dom, cod));
            // The codomain does not mention the binder, so its typing must not
            // depend on the binder's hypothesis either. If it does, the
            // interpretation leaked a variable and saying so is the honest
            // answer.
            let closed = self.close_one();
            let cod_mem = match (&closed, &tb.ev) {
                (Some(c), Ev::Proved(t)) if t.hyps().contains(c.scope().hyp()) => {
                    Ev::missing(Gap::Skeleton)
                }
                _ => tb.ev.clone(),
            };
            let ev = t1.ev.clone().zip(cod_mem, |a, b| {
                match self.ip().and_then(|ip| ip.fs_typing(&a, &b, n1, n2)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::SortTowerHeight),
                }
            });
            return (tm, ev)
        }
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
        // **`⟦λ⟧ = •` on the proof branch needs neither the domain nor the
        // binder's variable**, so the interpretation survives a domain that
        // could not be interpreted even though the *evidence* cannot. Guarding
        // both together would have lost the term as well, which is the axis
        // confusion §0 exists to prevent.
        let (Some(dom), Some(w)) = (t1.tm.clone(), w) else {
            let tm = if prop { self.ip().map(|ip| ip.point()) } else { None };
            return (tm, Ev::missing(Self::sub_gap(&[t1, tb]).unwrap_or(Gap::NoEndpoint)))
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
                Some(c) => c.discharge_ev(in_fibre).unwrap_or(Ev::missing(Gap::Skeleton)),
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
        if !dep {
            let Some(cod) = tb.ev.mem_set() else {
                self.close_one();
                return (tm, Ev::missing(tb.ev.reason(Gap::NoEndpoint)))
            };
            let closed = self.close_one();
            let family = match &closed {
                Some(c) => c.discharge_ev(at_sym).unwrap_or(Ev::missing(Gap::Skeleton)),
                None => Ev::missing(Gap::NoEndpoint),
            };
            let ev = family.and_then(|f| {
                match self.ip().and_then(|ip| ip.lam_typing_fs(&lam, dom, cod, &f)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::ConvCompose("lam-fs")),
                }
            });
            return (tm, ev)
        }
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
            Some(c) => c.discharge_ev(in_fibre).unwrap_or(Ev::missing(Gap::Skeleton)),
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
        let Expr::Forall { ty: dom_e, body } = &**ty else {
            return Err(format!("expected {depth} more binders, got {ty}"))
        };
        let (dom_e, body) = (dom_e.clone(), body.clone());
        let t1 = self.infer_type(&dom_e)?;
        let (s1, _, t1) = self.whnf_typing(t1)?;
        as_sort(&s1)?;
        let saved = self.open_slot(dom_e.clone(), t1.tm.clone());
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
        let out_ty = forall(dom_e, tb.ty.clone());
        let dep = has_bvar(&tb.ty, 0);
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
        let ip = self.th.as_ref()?.ip.get_const(&(name.clone(), inst.to_vec()))?;
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
        self.push(ty.clone(), t1.tm.clone());
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

    /// `⟦c.{σ}⟧` and its stored typing, or a named absence.
    fn const_evidence(&mut self, name: &Name, ls: &[Level]) -> (Option<Term>, Ev) {
        let empty = std::collections::HashMap::new();
        let Some(inst) =
            ls.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<Vec<u32>>>()
        else {
            return (None, Ev::missing(Gap::SymbolicLevel))
        };
        let key = (name.clone(), inst.clone());
        if self.th.is_some() && self.th.as_ref().is_some_and(|t| t.ip.get_const(&key).is_none()) {
            // **A store miss on an inductive constant is where §9 zone B
            // runs.** Not a retry and not a search: the key is the same
            // `(name, ground levels)` the store is keyed on, the declaration is
            // fetched by that name, and a shape the translation cannot express
            // is declined with its own reason — which is then what this clause
            // reports, per §0.4.
            let declines_to = crate::zoneb::ensure(self, name, &inst).err();
            if let Some(g) = declines_to {
                if self.th.as_ref().is_some_and(|t| t.ip.get_const(&key).is_none()) {
                    return (None, Ev::missing(g))
                }
            }
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
            None => (None, Ev::missing(Gap::NoInterpretation(name.clone(), inst))),
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
        let Ok(conv) = self.assert_def_eq(&tv.ty, have, ty, Some(ty_tm)) else {
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
        let Expr::Const(ind_name, us) = &*head else {
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
            let cur = ctor_ty.clone();
            let Expr::Forall { ty: d, body: b } = &*cur else {
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
            ctor_ty = subst(b, &Rc::new(Expr::Proj { ind: n.clone(), idx: i, s: e.clone() }));
        }
        let cur = ctor_ty.clone();
        let Expr::Forall { ty: d, .. } = &*cur else {
            return Err(format!("Projection index {} out of bounds for {ind_name}", idx + 1))
        };
        if strict && is_prop_type && !self.is_prop(d)? {
            return Err(format!(
                "Invalid projection; projection {} would project data out of a proposition",
                idx + 1
            ))
        }
        Ok((d.clone(), sub))
    }

    // ─────────────────────────────────────────── telescope helpers ──

    /// `openForall n type k`, push form: opens `n` binders and returns the body.
    /// The caller must be inside [`Checker::scoped`].
    fn open_forall_push(&mut self, n: u32, ty: &E) -> R<E> {
        let mut cur = ty.clone();
        for _ in 0..n {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &*t else {
                return Err(format!("Insufficient number of parameters: {t}"))
            };
            let (d, body) = (d.clone(), body.clone());
            self.push(d, None);
            cur = body;
        }
        Ok(cur)
    }

    /// `openForallEager`, push form: returns `(binders opened, the whnf'd
    /// non-`Π` body)`. The caller must be inside [`Checker::scoped`].
    fn open_forall_eager_push(&mut self, ty: &E) -> R<(u32, E)> {
        let mut cur = ty.clone();
        let mut n = 0u32;
        loop {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &*t else { return Ok((n, t.clone())) };
            let (d, body) = (d.clone(), body.clone());
            self.push(d, None);
            cur = body;
            n += 1;
        }
    }

    /// `instantiateForalls`.
    fn instantiate_foralls(&mut self, ty: &E, xs: &[E]) -> R<E> {
        let mut result = ty.clone();
        for x in xs {
            let t = self.whnf(&result)?;
            let Expr::Forall { body, .. } = &*t else {
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
    fn is_prop_or_unit_ev(&mut self, t: &E, cert: bool) -> R<(bool, Ev)> {
        let tt = self.infer_type(t)?;
        let (s, ev) = if cert {
            let (s, _, tt) = self.whnf_typing(tt)?;
            (s, tt.ev)
        } else {
            (self.whnf(&tt.ty)?, Ev::missing(Gap::NoEndpoint))
        };
        let u = as_sort(&s)?;
        if u.is_zero() {
            return Ok((true, ev))
        }
        let tw = self.whnf(t)?;
        let (head, _) = get_app(&tw);
        let Expr::Const(name, _) = &*head else { return Ok((false, Ev::missing(Gap::NoEndpoint))) };
        let Some(ConstantInfo::Inductive { is_unit, .. }) = self.lookup(name) else {
            return Ok((false, Ev::missing(Gap::NoEndpoint)))
        };
        // The unit-like branch's witness is the structure's subsingleton lemma
        // from the inductive interpretation, which §9 zone B has not reached.
        Ok((*is_unit, Ev::missing(Gap::UnitLike(name.clone()))))
    }

    /// `isProp`, with the witness. Same function as
    /// [`Checker::is_prop_or_unit_ev`] minus the unit probe.
    fn is_prop_ev(&mut self, ty: &E) -> R<(bool, Ev)> {
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
        let Expr::Const(con_name, _) = &*head else { return Ok(None) };
        let t = self.infer_ty(e1)?;
        let t = self.whnf(&t)?;
        let (ind_head, _) = get_app(&t);
        let Expr::Const(ind_name, _) = &*ind_head else { return Ok(None) };
        let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind_name) else {
            return Ok(None)
        };
        if ctors.len() != 1 || &ctors[0] != con_name {
            return Ok(None)
        }
        let ind_name = ind_name.clone();
        let np = *num_params as usize;
        for (i, arg) in args.iter().enumerate().skip(np) {
            let p = Rc::new(Expr::Proj {
                ind: ind_name.clone(),
                idx: u32::try_from(i - np).expect("field index"),
                s: e2.clone(),
            });
            let arg = arg.clone();
            if !self.is_def_eq(&arg, &p)? {
                return Ok(None)
            }
        }
        Ok(Some(ind_name))
    }

    /// `tryFunEta`.
    fn try_fun_eta(&mut self, e1: &E, e2: &E) -> R<bool> {
        let Expr::Lam { ty: t1, body: b1 } = &**e1 else { return Ok(false) };
        let (t1, b1) = (t1.clone(), b1.clone());
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
        // The §0.3 census counts conversions that were *asked for*: a
        // decision-only call hands in no endpoints and states nothing, so
        // counting it would drown the measurement in its own scaffolding.
        let asked = tm1.is_some() && tm2.is_some();
        let ev = self.def_eq_ev(e1, tm1, e2, tm2)?;
        if asked {
            if let Some(ip) = self.ip() {
                ip.note_conv(&ev);
            }
        }
        Ok(Conv { to: e2.clone(), ev })
    }

    fn def_eq_ev(&mut self, e1: &E, tm1: Option<Term>, e2: &E, tm2: Option<Term>) -> R<Ev> {
        // A certificate needs *both* endpoints; one alone states nothing.
        let cert = tm1.is_some() && tm2.is_some();
        let (tm1, tm2) = if cert { (tm1, tm2) } else { (None, None) };

        // Proof irrelevance first.
        let t1 = self.infer_type(e1)?;
        // `⟦·⟧` must be a function: the endpoint handed in and the one this
        // inference just computed for the same expression have to be the same
        // term. If they are not, every certificate built from here would be a
        // true theorem about the wrong terms.
        if cert && t1.tm.is_some() && t1.tm != tm1 {
            return Ok(Ev::missing(Gap::EndpointDrift))
        }
        let (irrel, ty_ev) = self.is_prop_or_unit_ev(&t1.ty, cert)?;
        if irrel {
            if !cert {
                return Ok(Ev::missing(Gap::NoEndpoint))
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
            // The unit-like branch, where `•` is not the inhabitant. It needs
            // the structure's subsingleton lemma, which §9 zone B has not
            // reached — and the gate above already named the structure, so
            // that name is carried rather than a placeholder invented here.
            return Ok(Ev::missing(why.unwrap_or(Gap::NoEndpoint)))
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
        let dom_conv = self.assert_def_eq(t1, d1_tm.clone(), t2, d2_tm.clone())?;
        let saved = self.open_slot(t1.clone(), d1.tm.clone());
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
        let raw = pointwise.clone();
        let family = closed.discharge_ev(pointwise).unwrap_or(Ev::missing(Gap::Skeleton));
        Ok(dom_conv.ev.zip(family, |de, fam| {
            raw.and_then(|r| {
                match self.ip().and_then(|ip| s.apply(ip, &d1_tm, &d2_tm, &de, &fam, &r)) {
                    Some(t) => Ev::Proved(t),
                    None => Ev::missing(Gap::BinderCongruence(s.rule())),
                }
            })
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
        match (&**a, &**b) {
            (Expr::Sort(l1), Expr::Sort(l2)) => {
                assert_level_eq(l1, l2)?;
                // Ground levels: equal levels give the *same* tower term, so
                // the certificate is reflexivity and nothing about level
                // algebra is needed. This is what retires nanoda's whole
                // "level algebra" admit family for mini.
                Ok(if same { refl() } else { Ev::missing(Gap::NoEndpoint) })
            }
            (Expr::Forall { ty: t1, body: b1 }, Expr::Forall { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (t1.clone(), b1.clone(), b2.clone());
                let shapes = self.pi_shapes(&a_tm, &b_tm);
                self.binder_cong(&t1, t2, &b1, &b2, same, refl(), shapes)
            }
            (Expr::Lam { ty: t1, body: b1 }, Expr::Lam { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (t1.clone(), b1.clone(), b2.clone());
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
                let (f1, a1, f2, a2) = (f1.clone(), a1.clone(), f2.clone(), a2.clone());
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
                let (s1, s2) = (s1.clone(), s2.clone());
                self.assert_is_def_eq(&s1, &s2)?;
                Ok(Ev::missing(Gap::StructProj(n1.clone())))
            }
            _ => {
                // Short-circuiting, as the original's `||` is: the second
                // direction must not run — and must not be able to reject — when
                // the first already fired.
                let eta = match self.try_structure_eta(a, b)? {
                    Some(n) => Some(n),
                    None => self.try_structure_eta(b, a)?,
                };
                if let Some(n) = eta {
                    // Structure eta needs the structure's own eta lemma, which
                    // comes with the inductive interpretation (§9 zone B).
                    return Ok(if same { refl() } else { Ev::missing(Gap::StructEta(n)) })
                }
                if self.try_fun_eta(a, b)? || self.try_fun_eta(b, a)? {
                    // The pointwise family is discharged from a scope the
                    // recursion above opens with no endpoints; wiring
                    // `conv::fun_eta_leg` needs that recursion threaded first.
                    return Ok(if same { refl() } else { Ev::missing(Gap::FunEta) })
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
        let Expr::Forall { ty: d1, body: b1 } = &**type1 else {
            return Err(format!("Expected a function type, got {type1}"))
        };
        let Expr::Forall { ty: d2, body: b2 } = &**type2 else {
            return Err(format!("Expected a function type, got {type2}"))
        };
        let (d1, b1, b2) = (d1.clone(), b1.clone(), b2.clone());
        self.assert_is_def_eq(&d1, d2)?;
        self.scoped(|c| {
            c.push(d1.clone(), None);
            c.def_eq_params(n - 1, &b1, &b2)
        })
    }

    // ──────────────────────────────── the inductive declaration zone ──

    /// `isValidIndApp`.
    fn is_valid_ind_app(&self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        let (head, args) = get_app(ty);
        let Expr::Const(f, us) = &*head else {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        };
        if f != ic.ind_name {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        }
        if us.len() != ic.lparams.len()
            || us.iter().zip(ic.lparams.iter()).any(|(l, p)| *l != Level::Param(p.clone()))
        {
            return Err(format!("Level parameters do not match those of {} in {ty}", ic.ind_name))
        }
        if args.len() != (ic.num_params + ic.num_indices) as usize {
            return Err(format!(
                "Expected {} arguments, got {} in {ty}",
                ic.num_params + ic.num_indices,
                args.len()
            ))
        }
        for i in 0..ic.num_params {
            if *args[i as usize] != Expr::BVar(sh + ic.num_params - (i + 1)) {
                return Err(format!("Unexpected parameter {} in {ty}", i + 1))
            }
        }
        for i in ic.num_params as usize..args.len() {
            if has_const(ic.ind_name, &args[i]) {
                return Err(format!(
                    "Unexpected recursive occurrence of {} in index argument {} of {ty}",
                    ic.ind_name,
                    i + 1
                ))
            }
        }
        Ok(())
    }

    /// `checkCtorParam`: universe bound, then strict positivity.
    fn check_ctor_param(&mut self, ic: &IndCtx<'_>, sh: u32, ctor_param: &E) -> R<()> {
        let s = self.infer_ty(ctor_param)?;
        let u = as_sort(&s)?;
        if !matches!(ic.ind_level, Level::Zero) {
            assert_level_le(&u, ic.ind_level)?;
        }
        let cp = self.whnf(ctor_param)?;
        if has_const(ic.ind_name, &cp) {
            self.scoped(|c| {
                let (m, ret) = c.open_forall_eager_push(&cp)?;
                for d in c.read_local_types(m)? {
                    if has_const(ic.ind_name, &d) {
                        return Err(format!(
                            "Not strictly positive: {} occurs in domain",
                            ic.ind_name
                        ))
                    }
                }
                c.is_valid_ind_app(ic, sh + m, &ret)
            })?;
        }
        Ok(())
    }

    /// `checkCtorType`. NB: no whnf, matching the official kernel.
    fn check_ctor_type(&mut self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        if let Expr::Forall { ty: domain, body } = &**ty {
            let (domain, body) = (domain.clone(), body.clone());
            self.check_ctor_param(ic, sh, &domain)?;
            self.scoped(|c| {
                c.push(domain.clone(), None);
                c.check_ctor_type(ic, sh + 1, &body)
            })
        } else {
            self.is_valid_ind_app(ic, sh, ty)
        }
    }

    /// The `elimToSort` walk over a single constructor's telescope.
    fn elim_to_sort_go(&mut self, t: &E) -> R<bool> {
        let Expr::Forall { ty: domain, body } = &**t else { return Ok(true) };
        let (domain, body) = (domain.clone(), body.clone());
        let s = self.infer_ty(&domain)?;
        let u = as_sort(&s)?;
        self.scoped(|c| {
            c.push(domain.clone(), None);
            let appears = c.scoped(|c2| {
                let (sh, res) = c2.open_forall_eager_push(&body)?;
                let (_, args) = get_app(&res);
                Ok(args.iter().any(|a| **a == Expr::BVar(sh)))
            })?;
            if !(u.is_zero() || appears) {
                return Ok(false)
            }
            c.elim_to_sort_go(&body)
        })
    }

    /// The recursor's type: steps 1–6 of mini-lean's `recType` builder.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_type(
        &mut self,
        ind_name: &Name,
        ind_type: &E,
        ctors: &[(Name, E)],
        num_params: u32,
        num_indices: u32,
        us: &Rc<[Level]>,
        motive_level: &Level,
    ) -> R<E> {
        let num_ctors = u32::try_from(ctors.len()).expect("constructor count");
        self.scoped(|c| {
            // 1. Parameters
            let ind_type = c.open_forall_push(num_params, ind_type)?;
            // 2. Motive
            let motive_type = c.scoped(|c| {
                c.open_forall_push(num_indices, &ind_type)?;
                let mut a = bvars(num_params, num_indices);
                a.extend(bvars(num_indices, 0));
                let major_type = app_n(konst(ind_name.clone(), us.clone()), &a);
                c.push(major_type, None);
                c.mk_forall(num_indices + 1, sort(motive_level.clone()))
            })?;
            c.push(motive_type, None);
            // 3. Minors
            let mut minor_types: Vec<E> = Vec::new();
            for (ctor_name, ctor_type) in ctors {
                let mt = c.scoped(|c| {
                    let params = bvars(num_params, 1);
                    let ctor_type = c.instantiate_foralls(ctor_type, &params)?;
                    let (num_fields, ctor_res_type) = c.open_forall_eager_push(&ctor_type)?;
                    // Recursive fields get an induction hypothesis.
                    let mut hyp_types: Vec<E> = Vec::new();
                    for field in bvars(num_fields, 0) {
                        let t = c.infer_ty(&field)?;
                        let t = c.whnf(&t)?;
                        if !has_const(ind_name, &t) {
                            continue
                        }
                        let hyp = c.scoped(|c| {
                            let (m, ret) = c.open_forall_eager_push(&t)?;
                            let (_, rargs) = get_app(&ret);
                            let mut a = slice(
                                &rargs,
                                num_params as usize,
                                (num_params + num_indices) as usize,
                            );
                            a.push(app_n(shift(&field, 0, m), &bvars(m, 0)));
                            let body = app_n(bvar(num_fields + m), &a);
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
                    let ctor_app = app_n(konst(ctor_name.clone(), us.clone()), &a);
                    let (_, rargs) = get_app(&ctor_res_type);
                    let mut a2 =
                        slice(&rargs, num_params as usize, (num_params + num_indices) as usize);
                    a2.push(ctor_app);
                    let motive_app = app_n(bvar(num_fields + nh), &a2);
                    c.mk_forall(num_fields + nh, motive_app)
                })?;
                minor_types.push(mt);
            }
            c.push_types(&minor_types);
            // 4. Indices
            c.open_forall_push(num_indices, &shift(&ind_type, 0, 1 + num_ctors))?;
            // 5. Major argument
            let mut a = bvars(num_params, 1 + num_ctors + num_indices);
            a.extend(bvars(num_indices, 0));
            let major_type = app_n(konst(ind_name.clone(), us.clone()), &a);
            c.push(major_type, None);
            // 6. Result type: the motive applied to indices and major argument
            let mut a = bvars(num_indices, 1);
            a.push(bvar(0));
            let result_type = app_n(bvar(num_ctors + num_indices + 1), &a);
            c.mk_forall(num_params + 1 + num_ctors + num_indices + 1, result_type)
        })
    }

    /// One iota rule's RHS: the body of `fun params motive minors fields => …`.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_rule(
        &mut self,
        ind_name: &Name,
        rec_name: &Name,
        rec_type: &E,
        ctor_type: &E,
        i: u32,
        num_params: u32,
        num_indices: u32,
        num_ctors: u32,
        us2: &Rc<[Level]>,
    ) -> R<E> {
        self.scoped(|c| {
            c.open_forall_push(num_params + 1 + num_ctors, rec_type)?;
            let ctor_type =
                c.instantiate_foralls(ctor_type, &bvars(num_params, 1 + num_ctors))?;
            let (num_fields, _) = c.open_forall_eager_push(&ctor_type)?;
            let minor = bvar(num_ctors - (i + 1) + num_fields);
            let fields = bvars(num_fields, 0);
            let mut ihs: Vec<E> = Vec::new();
            for field in &fields {
                let t = c.infer_ty(field)?;
                let t = c.whnf(&t)?;
                if !has_const(ind_name, &t) {
                    continue
                }
                let ih = c.scoped(|c| {
                    let (m, ret) = c.open_forall_eager_push(&t)?;
                    let (_, rargs) = get_app(&ret);
                    let mut a = bvars(num_params + 1 + num_ctors, num_fields + m);
                    a.extend(slice(
                        &rargs,
                        num_params as usize,
                        (num_params + num_indices) as usize,
                    ));
                    a.push(app_n(shift(field, 0, m), &bvars(m, 0)));
                    let body = app_n(konst(rec_name.clone(), us2.clone()), &a);
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

// ────────────────────────────────────────────────── Environment.add ──

fn nodup(lparams: &[Name], name: &Name) -> R<()> {
    for (i, p) in lparams.iter().enumerate() {
        if lparams[i + 1..].contains(p) {
            return Err(format!("Duplicate level parameters in declaration of {name}"))
        }
    }
    Ok(())
}

/// `Environment.addQuot`, ported verbatim.
pub fn add_quot(env: &mut Environment) -> R<()> {
    let quot_name = Name::simple("Quot");
    let quot_mk_name = Name::str(&quot_name, "mk");
    let quot_lift_name = Name::str(&quot_name, "lift");
    let quot_ind_name = Name::str(&quot_name, "ind");
    let u = Name::simple("u");
    let v = Name::simple("v");
    let prop = sort(Level::Zero);
    let sort_u = sort(Level::Param(u.clone()));
    let sort_v = sort(Level::Param(v.clone()));
    let eq_name = Name::simple("Eq");

    let aar_prop = |i: u32| arrow(bvar(i), arrow(bvar(i + 1), prop.clone()));
    let mk_quot = |a: u32, r: u32| {
        app(app(konst(quot_name.clone(), levels(&[Level::Param(u.clone())])), bvar(a)), bvar(r))
    };

    // Quot : ∀ (α : Sort u) (_ : α → α → Prop), Sort u
    let quot_type = arrow(sort_u.clone(), arrow(aar_prop(0), sort_u.clone()));
    // Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), @Quot α r
    let quot_mk_type =
        arrow(sort_u.clone(), arrow(aar_prop(0), arrow(bvar(1), mk_quot(2, 1))));
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
                        app(konst(eq_name, levels(&[Level::Param(v.clone())])), bvar(4)),
                        app(bvar(3), bvar(2)),
                    ),
                    app(bvar(3), bvar(1)),
                ),
            ),
        ),
    );
    let quot_lift_type = arrow(
        sort_u.clone(),
        arrow(
            aar_prop(0),
            arrow(sort_v, arrow(f_type, arrow(h_type, arrow(mk_quot(4, 3), bvar(3))))),
        ),
    );
    // Quot.ind
    let beta_ind_type = arrow(mk_quot(1, 0), prop.clone());
    let h_ind_type = arrow(
        bvar(2),
        app(
            bvar(1),
            app(
                app(
                    app(konst(quot_mk_name.clone(), levels(&[Level::Param(u.clone())])), bvar(3)),
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
        lparams: vec![u.clone(), v],
        ty: quot_lift_type,
        num_params: 2,
        num_minors: 2,
        num_indices: 0,
        rules: vec![(quot_mk_name.clone(), app(bvar(2), bvar(0)))],
        k_type: None,
    };
    let ind_info = ConstantInfo::Recursor {
        lparams: vec![u.clone()],
        ty: quot_ind_type,
        num_params: 2,
        num_minors: 1,
        num_indices: 0,
        rules: vec![(quot_mk_name.clone(), app(bvar(1), bvar(0)))],
        k_type: None,
    };
    env.insert_new(quot_name, ConstantInfo::Opaque { lparams: vec![u.clone()], ty: quot_type })?;
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
                name.clone(),
                ConstantInfo::Opaque { lparams: lparams.clone(), ty: ty.clone() },
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
                    ty: ty.clone(),
                    value: value.clone(),
                },
                DefKind::Opaque => {
                    ConstantInfo::Opaque { lparams: lparams.clone(), ty: ty.clone() }
                }
            };
            env.insert_new(name.clone(), cinfo)
        }
        Declaration::Quot => add_quot(env),
        Declaration::Inductive { name: ind_name, lparams, num_params, ty: ind_type, ctors } => {
            add_inductive(env, ind_name, lparams, *num_params, ind_type, ctors)
        }
    }
}

fn add_inductive(
    env: &mut Environment,
    ind_name: &Name,
    lparams: &[Name],
    num_params: u32,
    ind_type: &E,
    ctors: &[(Name, E)],
) -> R<()> {
    nodup(lparams, ind_name)?;
    let num_ctors = u32::try_from(ctors.len()).expect("constructor count");

    // The type of the inductive: its indices and its universe.
    let (num_indices, ind_level) = {
        let mut c = Checker::new(env);
        let go = |c: &mut Checker<'_, '_>| -> R<(u32, Level)> {
            c.check_type(ind_type)?;
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, ind_type)?;
                let (ni, t) = c.open_forall_eager_push(&t)?;
                Ok((ni, as_sort(&t)?))
            })
        };
        go(&mut c)
            .map_err(|e| format!("{e}\n… while checking type of inductive {ind_name}"))?
    };

    // A "unit-like" type: one constructor, no fields.
    let is_unit = if ctors.len() == 1 {
        let mut c = Checker::new(env);
        c.scoped(|c| {
            let t = c.open_forall_push(num_params, &ctors[0].1)?;
            Ok(!matches!(&*t, Expr::Forall { .. }))
        })?
    } else {
        false
    };

    env.insert_new(
        ind_name.clone(),
        ConstantInfo::Inductive {
            lparams: lparams.to_vec(),
            ty: ind_type.clone(),
            num_params,
            num_indices,
            ctors: ctors.iter().map(|(n, _)| n.clone()).collect(),
            is_unit,
        },
    )?;

    // Constructor checks, with the inductive already in the environment.
    {
        let ic = IndCtx { ind_name, lparams, num_params, num_indices, ind_level: &ind_level };
        let mut c = Checker::new(env);
        for (ctor_name, ctor_type) in ctors {
            c.check_type(ctor_type)
                .map_err(|e| format!("{e}\n… while checking type of constructor {ctor_name}"))?;
            c.def_eq_params(num_params, ind_type, ctor_type).map_err(|e| {
                format!(
                    "{e}\n… while checking parameters of constructor {ctor_name} match those of {ind_name}"
                )
            })?;
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, ctor_type)?;
                c.check_ctor_type(&ic, 0, &t)
            })
            .map_err(|e| format!("{e}\n… while checking constructor {ctor_name}"))?;
        }
    }

    for (ctor_name, ctor_type) in ctors {
        env.insert_new(
            ctor_name.clone(),
            ConstantInfo::Opaque { lparams: lparams.to_vec(), ty: ctor_type.clone() },
        )?;
        // The index §9 zone B reaches the declaration by. Built here, where
        // the relation is known, so that no later pass has to look for it.
        env.owners.insert(ctor_name.clone(), ind_name.clone());
    }

    // Large elimination?
    let elim_to_sort = {
        if ind_level.is_not_zero() {
            true
        } else if num_ctors == 0 {
            // TODO (mini-lean's own): mutual inductives should return false.
            true
        } else if num_ctors > 1 {
            false
        } else {
            let mut c = Checker::new(env);
            c.elim_to_sort_go(&ctors[0].1)?
        }
    };

    // The K-rule applies to an inductive proposition with one fieldless ctor.
    let k_type = {
        if ind_level.is_not_zero() || ctors.len() != 1 {
            None
        } else {
            let mut c = Checker::new(env);
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, &ctors[0].1)?;
                Ok(if matches!(&*t, Expr::Forall { .. }) { None } else { Some(t) })
            })?
        }
    };

    let (motive_level, lparams2) = if elim_to_sort {
        let v = fresh_level_name(lparams);
        let mut l = vec![v.clone()];
        l.extend(lparams.iter().cloned());
        (Level::Param(v), l)
    } else {
        (Level::Zero, lparams.to_vec())
    };
    let us: Rc<[Level]> =
        lparams.iter().map(|n| Level::Param(n.clone())).collect::<Vec<_>>().into();
    let us2: Rc<[Level]> =
        lparams2.iter().map(|n| Level::Param(n.clone())).collect::<Vec<_>>().into();

    let rec_type = {
        let mut c = Checker::new(env);
        let rec_type = c.build_rec_type(
            ind_name,
            ind_type,
            ctors,
            num_params,
            num_indices,
            &us,
            &motive_level,
        )?;
        // Sanity check, at the recursor's own (symbolic) level parameters.
        c.check_type(&rec_type).map_err(|e| {
            format!("{e}\n… while checking type of recursor for {ind_name}:\n{rec_type}")
        })?;
        rec_type
    };

    let rec_name = Name::str(ind_name, "rec");
    let mut rules: Vec<(Name, E)> = Vec::new();
    for (i, (ctor_name, ctor_type)) in ctors.iter().enumerate() {
        let mut c = Checker::new(env);
        let rhs = c.build_rec_rule(
            ind_name,
            &rec_name,
            &rec_type,
            ctor_type,
            u32::try_from(i).expect("constructor index"),
            num_params,
            num_indices,
            num_ctors,
            &us2,
        )?;
        rules.push((ctor_name.clone(), rhs));
    }

    env.owners.insert(rec_name.clone(), ind_name.clone());
    env.insert_new(
        rec_name,
        ConstantInfo::Recursor {
            lparams: lparams2,
            ty: rec_type,
            num_params,
            num_minors: num_ctors,
            num_indices,
            rules,
            k_type,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::DefKind;

    /// `axiom P : Prop`, `axiom p : P`, `def Id : Prop → Prop := fun q => q`.
    fn env() -> Environment {
        let mut env = Environment::empty();
        let prop = sort(Level::Zero);
        let p_ty = Name::simple("P");
        add(&mut env, &Declaration::Axiom { name: p_ty.clone(), lparams: vec![], ty: prop.clone() })
            .unwrap();
        let pk = konst(p_ty.clone(), no_levels());
        add(&mut env, &Declaration::Axiom { name: Name::simple("p"), lparams: vec![], ty: pk })
            .unwrap();
        add(
            &mut env,
            &Declaration::Def {
                name: Name::simple("Id"),
                lparams: vec![],
                ty: forall(prop.clone(), sort(Level::Zero)),
                value: lam(prop, bvar(0)),
                kind: DefKind::Def,
            },
        )
        .unwrap();
        env
    }

    fn k(n: &str) -> E { konst(Name::simple(n), no_levels()) }

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
        assert_eq!(c.body_clause(&sort(Level::Zero)).unwrap(), Clause::Type);
        assert_eq!(c.term_clause(&sort(Level::Zero)).unwrap(), Clause::Type);
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
        let lam_redex = app(lam(sort(Level::Zero), bvar(0)), k("P"));
        assert_eq!(c.body_clause(&lam_redex).unwrap(), Clause::Prop);
    }

    /// A `let` denotes its expansion and classifies with it — again with no
    /// `let` arm in the classifier, because `infer_type` substitutes.
    #[test]
    fn a_let_classifies_with_its_expansion() {
        let env = env();
        let mut c = Checker::new(&env);
        let e = Rc::new(Expr::Let { ty: sort(Level::Zero), val: k("P"), body: bvar(0) });
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
        let prop = sort(Level::Zero);
        let mut e = bvar(0);
        for _ in 0..depth {
            e = forall(prop.clone(), e);
        }
        e
    }

    fn decls3() -> Vec<Declaration> {
        let prop = sort(Level::Zero);
        let mut v: Vec<Declaration> = ["X", "Y", "Z"]
            .iter()
            .enumerate()
            .map(|(i, n)| Declaration::Def {
                name: Name::simple(n),
                lparams: vec![],
                ty: prop.clone(),
                // Three distinct propositions, so the middle one is
                // recognisable: `∀p. p`, `∀p∀q. q`, `∀p∀q∀r. r`.
                value: quantified(u32::try_from(i).unwrap() + 1),
                kind: DefKind::Opaque,
            })
            .collect();
        let sel_ty = arrow(prop.clone(), arrow(prop.clone(), arrow(prop.clone(), prop.clone())));
        v.push(Declaration::Def {
            name: Name::simple("sel"),
            lparams: vec![],
            ty: sel_ty,
            value: lam(prop.clone(), lam(prop.clone(), lam(prop, bvar(1)))),
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
        assert_eq!(*reduct, *k("Y"), "the middle argument, not the first or the last");
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
        let ty0 = sort(Level::Zero.succ());
        let prop = sort(Level::Zero);
        // `B` and `C` are **opaque**, so nothing unfolds them and the
        // conversion has to go through the argument rather than round it.
        let decls = vec![
            Declaration::Def {
                name: Name::simple("B"),
                lparams: vec![],
                ty: ty0.clone(),
                value: prop.clone(),
                kind: DefKind::Opaque,
            },
            Declaration::Def {
                name: Name::simple("Idf"),
                lparams: vec![],
                ty: forall(ty0.clone(), arrow(bvar(0), bvar(1))),
                value: lam(ty0, lam(bvar(0), bvar(0))),
                kind: DefKind::Def,
            },
            Declaration::Def {
                name: Name::simple("C"),
                lparams: vec![],
                ty: arrow(k("B"), arrow(k("B"), prop.clone())),
                value: lam(k("B"), lam(k("B"), forall(prop.clone(), bvar(0)))),
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

    /// **`whnf` hands back no certificate when it was handed no endpoint**, and
    /// that is not a drop: `is_def_eq`'s callers want a `bool` and there is no
    /// downstream step that would have to re-derive the equation.
    #[test]
    fn an_uncertified_whnf_reports_a_named_absence() {
        let (env, _) = env3();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let e = app_n(k("sel"), &[k("X"), k("Y"), k("Z")]);
        let (reduct, conv) = c.whnf_conv(&e, None, &Gap::NoEndpoint).expect("whnf");
        assert_eq!(*reduct, *k("Y"), "the reduction is unaffected by the certificate");
        assert_eq!(conv.ev.gap(), Some(&Gap::NoEndpoint));
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
