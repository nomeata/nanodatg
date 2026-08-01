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
use crate::ev::{Ev, Gap};
use crate::conv::Conv;
use crate::interp::Interp;
use crate::scope::{ScopeToken, Scopes};
use kernel::{FreeVar, Term};
use crate::expr::{
    app, app_n, arrow, bvar, bvars, forall, get_app, has_bvar, has_const, konst, lam, shift, sort,
    subst, substs, Expr, Level, Name, E,
};
use std::rc::Rc;

pub type R<T> = Result<T, String>;

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
        let Some(th) = self.th.as_ref() else { return Ev::Gap(Gap::SymbolicLevel) };
        let n = self.lenv.len();
        let Some(Some(depth)) = n.checked_sub(1 + idx as usize).and_then(|k| th.slots.get(k))
        else {
            return Ev::Gap(Gap::SymbolicLevel)
        };
        match th.scopes.get((th.scopes.len() - 1 - depth) as u32) {
            Some(s) => Ev::Proved(s.assumption().clone()),
            None => Ev::Gap(Gap::SymbolicLevel),
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
    fn local_type(&self, idx: u32) -> R<E> {
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
            let Some(s) = s.clone() else { return Ev::Gap(Gap::NoEndpoint) };
            let refl = Ev::Proved(kernel::Thm::eq_refl(s));
            let Some(ip) = self.ip() else { return Ev::Gap(Gap::SymbolicLevel) };
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
                    None => Conv { to: next.to, ev: Ev::Gap(Gap::SymbolicLevel) },
                };
            }};
        }
        macro_rules! done {
            ($to:expr) => {{
                let to = $to;
                acc.to = to.clone();
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
                                // **Iota**, K-rule form. The stored per-`(rec,
                                // levels)` computation rule is §9 zone B's, and
                                // that wiring is not landed, so the step is a
                                // named absence rather than a silent one.
                                step!(Ev::Gap(Gap::Iota(name.clone())));
                                cur = substs(&rhs, &args, 0);
                                cur_tm = None;
                                stack = stack[major_pos + 1..].to_vec();
                                stack_tms = stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
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
                                fired = Some(substs(&rhs, &args, 0));
                            }
                        }
                        if let Some(rhs) = fired {
                            step!(Ev::Gap(Gap::Iota(name.clone())));
                            cur = rhs;
                            cur_tm = None;
                            stack = stack[major_pos + 1..].to_vec();
                            stack_tms = stack_tms.split_off((major_pos + 1).min(stack_tms.len()));
                            continue
                        }
                        let mut stack2 = stack.clone();
                        stack2[major_pos] = major2;
                        // Stuck, but the major *may* have reduced under it. If
                        // it did, the expression changed and the certificate
                        // owes a congruence over that change; the major's own
                        // reduction is not threaded (it is the acceptance-only
                        // `whnf` above), so this is a named absence.
                        if stack2[major_pos] != stack[major_pos] {
                            step!(Ev::Gap(Gap::Iota(name.clone())));
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
                    step!(Ev::Gap(Gap::StructProj(ind.clone())));
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
            return (Ev::Gap(Gap::NoEndpoint), None)
        }
        let empty = std::collections::HashMap::new();
        let Some(inst) =
            ls.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<Vec<u32>>>()
        else {
            return (Ev::Gap(Gap::SymbolicLevel), None)
        };
        let Some(th) = self.th.as_ref() else { return (Ev::Gap(Gap::SymbolicLevel), None) };
        let Some(c) = th.ip.get_const(&(name.clone(), inst.clone())) else {
            return (Ev::Gap(Gap::NoInterpretation(name.clone(), inst)), None)
        };
        match &c.defeq {
            Some(s) => {
                let thm = s.thm().clone();
                let rhs = thm.concl().as_eq().map(|(_, b)| b);
                (Ev::Proved(thm), rhs)
            }
            None => (Ev::Gap(Gap::NoDefiningEquation(name.clone())), None),
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
            return (Ev::Gap(Gap::NoEndpoint), None)
        };
        let Some((site, dom)) = self.th.as_ref().and_then(|th| th.ip.as_lam(&lam_t)) else {
            return (Ev::Gap(Gap::NotDecomposable), None)
        };
        let arg_mem = match self.beta_premise(lam_ty, &dom, arg, &a_tm) {
            Ok(m) => m,
            Err(e) => return (Ev::Gap(e), None),
        };
        let Some(ip) = self.ip() else { return (Ev::Gap(Gap::SymbolicLevel), None) };
        let ev = crate::conv::beta_leg(ip, &site, dom, a_tm.clone(), &arg_mem);
        let to = ev.eq_rhs();
        (ev, to)
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
                None => Ev::Gap(Gap::ConvCompose),
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
                None => Ev::Gap(Gap::ConvCompose),
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
                            None => Ev::Gap(Gap::SortTowerHeight),
                        };
                        (Some(tm), ev)
                    }
                    _ => (None, Ev::Gap(Gap::SymbolicLevel)),
                };
                Ok(Typing { ty, tm, ev })
            }
            Expr::App(f, arg) => {
                let tf = self.infer_type(f)?;
                let f_ty = self.whnf(&tf.ty)?;
                let Expr::Forall { ty, body } = &*f_ty else {
                    return Err(format!(
                        "Expected a function type in application of {f} to {arg}, got {f_ty}"
                    ))
                };
                let (ty, body) = (ty.clone(), body.clone());
                let ta = self.infer_type(arg)?;
                self.assert_is_def_eq(&ty, &ta.ty)?;
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
                let ev = Ev::Gap(match tm {
                    Some(_) => Gap::DefEqUnthreaded,
                    None => Self::sub_gap(&[&tf, &ta]).unwrap_or(Gap::DefEqUnthreaded),
                });
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Forall { ty, body } => {
                let t1 = self.infer_type(ty)?;
                let s1 = self.whnf(&t1.ty)?;
                let l1 = as_sort(&s1)?;
                let saved = self.open_slot(ty.clone(), t1.tm.clone());
                let w = self.current_var();
                let tb = self.infer_type(body);
                self.close_slot(saved);
                let tb = tb?;
                // NB: mini-lean whnfs the codomain's sort *outside* the
                // binder's scope. Reproduced deliberately.
                let s2 = self.whnf(&tb.ty)?;
                let l2 = as_sort(&s2)?;
                let out_ty = sort(Level::imax(l1.clone(), l2.clone()));
                // **The clause is `l2 == 0`, already computed.** No classifier
                // call: §6.2's `∀` column is exactly a codomain in `Sort 0`.
                let dep = has_bvar(body, 0);
                let t1x = t1.clone();
                let tm = match (t1.tm.clone(), tb.tm.clone(), w) {
                    (Some(dom), Some(cod), Some(w)) => self.th.as_mut().and_then(|th| {
                        if l2.is_zero() {
                            let site = th.ip.cond_site(&cod, w)?;
                            Some(th.ip.cond_term(&site, dom))
                        } else if !dep {
                            Some(th.ip.fs(dom, cod))
                        } else {
                            let site = th.ip.fibre_site(&cod, w)?;
                            Some(th.ip.dprod_term(&site, dom))
                        }
                    }),
                    _ => None,
                };
                let ev = Ev::Gap(match tm {
                    Some(_) => Gap::PiTypingUnthreaded,
                    None => Self::sub_gap(&[&t1x, &tb]).unwrap_or(Gap::PiTypingUnthreaded),
                });
                Ok(Typing { ty: out_ty, tm, ev })
            }
            Expr::Lam { ty, body } => {
                let t1 = self.infer_type(ty)?;
                let s1 = self.whnf(&t1.ty)?;
                as_sort(&s1)?;
                let saved = self.open_slot(ty.clone(), t1.tm.clone());
                let w = self.current_var();
                let t1x = t1.clone();
                let inner = (|c: &mut Self| -> R<(E, Option<Term>, bool, Option<Gap>)> {
                    let tb = c.infer_type(body)?;
                    let g = if tb.tm.is_none() { tb.ev.gap().cloned() } else { None };
                    // A `λ` is a proof exactly when its body is, decided from
                    // the body's own type under the binder.
                    let prop = c.body_clause(&tb.ty)? == Clause::Prop;
                    Ok((tb.ty, tb.tm, prop, g))
                })(self);
                self.close_slot(saved);
                let (body_ty, body_tm, prop, body_gap) = inner?;
                let out_ty = forall(ty.clone(), body_ty);
                let tm = if prop {
                    self.th.as_ref().map(|th| th.ip.point())
                } else {
                    match (t1.tm.clone(), body_tm, w) {
                        (Some(dom), Some(b), Some(w)) => self.th.as_mut().and_then(|th| {
                            let site = th.ip.lam_site(&b, w)?;
                            Some(th.ip.lam_term(&site, dom))
                        }),
                        _ => None,
                    }
                };
                let ev = Ev::Gap(match tm {
                    Some(_) => Gap::LamTypingUnthreaded,
                    None => body_gap.or_else(|| Self::sub_gap(&[&t1x]))
                        .unwrap_or(Gap::LamTypingUnthreaded),
                });
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
                let ty = self.infer_proj(ind, *idx, s)?;
                Ok(Typing { ty, tm: None, ev: Ev::Gap(Gap::StructProj(ind.clone())) })
            }
            Expr::NatLit(_) => Ok(Typing {
                ty: konst(Name::simple("Nat"), no_levels()),
                tm: None,
                ev: Ev::Gap(Gap::NoInterpretation(Name::simple("Nat"), vec![])),
            }),
            Expr::StrLit(_) => Ok(Typing {
                ty: konst(Name::simple("String"), no_levels()),
                tm: None,
                ev: Ev::Gap(Gap::StrLit),
            }),
        }
    }

    /// The first sub-`Typing` that failed to interpret, as a reason.
    fn sub_gap(parts: &[&Typing]) -> Option<Gap> {
        parts.iter().find(|t| t.tm.is_none()).and_then(|t| t.ev.gap().cloned())
    }

    /// `⟦c.{σ}⟧` and its stored typing, or a named absence.
    fn const_evidence(&mut self, name: &Name, ls: &[Level]) -> (Option<Term>, Ev) {
        let empty = std::collections::HashMap::new();
        let Some(inst) =
            ls.iter().map(|l| crate::ground::eval(l, &empty)).collect::<Option<Vec<u32>>>()
        else {
            return (None, Ev::Gap(Gap::SymbolicLevel))
        };
        let key = (name.clone(), inst.clone());
        let Some(th) = self.th.as_ref() else { return (None, Ev::Gap(Gap::SymbolicLevel)) };
        match th.ip.get_const(&key) {
            Some(c) => {
                let ev = match &c.typing {
                    Ok(s) => Ev::Proved(s.thm().clone()),
                    Err(g) => Ev::Gap(g.clone()),
                };
                (Some(c.term.clone()), ev)
            }
            None => (None, Ev::Gap(Gap::NoInterpretation(name.clone(), inst))),
        }
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

    /// `inferProj`.
    fn infer_proj(&mut self, n: &Name, idx: u32, e: &E) -> R<E> {
        let t = self.infer_ty(e)?;
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
            if is_prop_type && has_bvar(b, 0) && !self.is_prop(d)? {
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
        if is_prop_type && !self.is_prop(d)? {
            return Err(format!(
                "Invalid projection; projection {} would project data out of a proposition",
                idx + 1
            ))
        }
        Ok(d.clone())
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
            (self.whnf(&tt.ty)?, Ev::Gap(Gap::NoEndpoint))
        };
        let u = as_sort(&s)?;
        if u.is_zero() {
            return Ok((true, ev))
        }
        let tw = self.whnf(t)?;
        let (head, _) = get_app(&tw);
        let Expr::Const(name, _) = &*head else { return Ok((false, Ev::Gap(Gap::NoEndpoint))) };
        let Some(ConstantInfo::Inductive { is_unit, .. }) = self.lookup(name) else {
            return Ok((false, Ev::Gap(Gap::NoEndpoint)))
        };
        // The unit-like branch's witness is the structure's subsingleton lemma
        // from the inductive interpretation, which §9 zone B has not reached.
        Ok((*is_unit, Ev::Gap(Gap::UnitLike(name.clone()))))
    }

    /// `isProp`, with the witness. Same function as
    /// [`Checker::is_prop_or_unit_ev`] minus the unit probe.
    fn is_prop_ev(&mut self, ty: &E) -> R<(bool, Ev)> {
        let t = self.infer_type(ty)?;
        let (s, _, t) = self.whnf_typing(t)?;
        Ok((as_sort(&s)?.is_zero(), t.ev))
    }

    /// `Γ ⊢ ⟦a⟧ = ⟦c⟧` from `Γ ⊢ ⟦a⟧ = ⟦b⟧` and `Γ ⊢ ⟦b⟧ = ⟦c⟧`.
    fn ev_trans(&mut self, a: Ev, b: Ev) -> Ev {
        a.zip(b, |x, y| match self.ip().and_then(|ip| derived::eq_trans(&mut ip.env, &x, &y)) {
            Some(t) => Ev::Proved(t),
            None => Ev::Gap(Gap::ConvCompose),
        })
    }

    /// `Γ ⊢ ⟦b⟧ = ⟦a⟧` from `Γ ⊢ ⟦a⟧ = ⟦b⟧`.
    fn ev_symm(&mut self, a: Ev) -> Ev {
        a.and_then(|x| match self.ip().and_then(|ip| derived::eq_symm(&mut ip.env, &x)) {
            Some(t) => Ev::Proved(t),
            None => Ev::Gap(Gap::ConvCompose),
        })
    }

    /// `tryStructureEta`.
    fn try_structure_eta(&mut self, e1: &E, e2: &E) -> R<bool> {
        let (head, args) = get_app(e1);
        let Expr::Const(con_name, _) = &*head else { return Ok(false) };
        let t = self.infer_ty(e1)?;
        let t = self.whnf(&t)?;
        let (ind_head, _) = get_app(&t);
        let Expr::Const(ind_name, _) = &*ind_head else { return Ok(false) };
        let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind_name) else {
            return Ok(false)
        };
        if ctors.len() != 1 || &ctors[0] != con_name {
            return Ok(false)
        }
        let np = *num_params as usize;
        for (i, arg) in args.iter().enumerate().skip(np) {
            let p = Rc::new(Expr::Proj {
                ind: ind_name.clone(),
                idx: u32::try_from(i - np).expect("field index"),
                s: e2.clone(),
            });
            let arg = arg.clone();
            if !self.is_def_eq(&arg, &p)? {
                return Ok(false)
            }
        }
        Ok(true)
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
        let ev = self.def_eq_ev(e1, tm1, e2, tm2)?;
        if let Some(ip) = self.ip() {
            ip.note_conv(&ev);
        }
        Ok(Conv { to: e2.clone(), ev })
    }

    fn def_eq_ev(&mut self, e1: &E, tm1: Option<Term>, e2: &E, tm2: Option<Term>) -> R<Ev> {
        // A certificate needs *both* endpoints; one alone states nothing.
        let cert = tm1.is_some() && tm2.is_some();
        let (tm1, tm2) = if cert { (tm1, tm2) } else { (None, None) };

        // Proof irrelevance first.
        let t1 = self.infer_type(e1)?;
        let (irrel, ty_ev) = self.is_prop_or_unit_ev(&t1.ty, cert)?;
        if irrel {
            if !cert {
                return Ok(Ev::Gap(Gap::NoEndpoint))
            }
            return self.proof_irrel_ev(&t1, ty_ev, e2);
        }

        let (a, ca) = self.whnf_conv(e1, tm1, &Gap::NoEndpoint)?;
        let (b, cb) = self.whnf_conv(e2, tm2, &Gap::NoEndpoint)?;
        let (a_tm, b_tm) = (ca.ev.eq_rhs(), cb.ev.eq_rhs());
        let mid = self.def_eq_struct(&a, a_tm, &b, b_tm)?;
        // `⟦e1⟧ = ⟦a⟧`, then `⟦a⟧ = ⟦b⟧`, then `⟦b⟧ = ⟦e2⟧` — the composition
        // nanoda once skipped and now guards (the refl-for-a-reduction bug).
        let left = self.ev_trans(ca.ev, mid);
        let back = self.ev_symm(cb.ev);
        Ok(self.ev_trans(left, back))
    }

    /// The certificate of proof irrelevance: both sides reach `•`, and the
    /// equation is `trans` of one with `symm` of the other.
    fn proof_irrel_ev(&mut self, t1: &Typing, ty_ev: Ev, e2: &E) -> R<Ev> {
        let left = self.point_eq(&t1.ev, ty_ev);
        let t2 = self.infer_type(e2)?;
        let (prop2, ty2_ev) = self.is_prop_ev(&t2.ty)?;
        if !prop2 {
            // The unit-like branch, where `•` is not the inhabitant. It needs
            // the structure's subsingleton lemma, which §9 zone B has not
            // reached.
            return Ok(Ev::Gap(Gap::UnitLike(Name::simple("<unit-like>"))))
        }
        let right = self.point_eq(&t2.ev, ty2_ev);
        let back = self.ev_symm(right);
        Ok(self.ev_trans(left, back))
    }

    /// `Γ ⊢ ⟦e⟧ = •` from the term's membership and its type's `U₀` witness.
    fn point_eq(&mut self, e_mem: &Ev, ty_mem: Ev) -> Ev {
        ty_mem.zip(e_mem.clone(), |ty, e| {
            match self.ip().and_then(|ip| ip.point_of_proof(&ty, &e)) {
                Some(t) => Ev::Proved(t),
                None => Ev::Gap(Gap::ConvCompose),
            }
        })
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
            None => Ev::Gap(Gap::NoEndpoint),
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
                Ok(if same { refl() } else { Ev::Gap(Gap::NoEndpoint) })
            }
            (Expr::Forall { ty: t1, body: b1 }, Expr::Forall { ty: t2, body: b2 })
            | (Expr::Lam { ty: t1, body: b1 }, Expr::Lam { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (t1.clone(), b1.clone(), b2.clone());
                self.assert_is_def_eq(&t1, t2)?;
                self.scoped(|c| {
                    c.push(t1.clone(), None);
                    c.assert_is_def_eq(&b1, &b2)
                })?;
                // The binder congruences (`dprod_ext_n`, `cond_ext_n`,
                // `lam_ext_n`) take a *discharged* family over a scope opened
                // on `⟦A⟧`, and the recursion above runs with no endpoints. If
                // the two interpretations coincide the equation is
                // reflexivity; otherwise this is the one remaining wiring.
                Ok(if same { refl() } else { Ev::Gap(Gap::BinderCongruence) })
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
                    None => Ev::Gap(Gap::SymbolicLevel),
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
                Ok(if same { refl() } else { Ev::Gap(Gap::NoEndpoint) })
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
                Ok(Ev::Gap(Gap::StructProj(n1.clone())))
            }
            _ => {
                if self.try_structure_eta(a, b)? || self.try_structure_eta(b, a)? {
                    let (Expr::App(..) | Expr::Const(..), _) = (&**a, &**b) else {
                        return Ok(Ev::Gap(Gap::StructEta(Name::simple("<structure>"))))
                    };
                    return Ok(Ev::Gap(Gap::StructEta(Name::simple("<structure>"))))
                }
                if self.try_fun_eta(a, b)? || self.try_fun_eta(b, a)? {
                    // The pointwise family is discharged from a scope the
                    // recursion above opens with no endpoints; wiring
                    // `conv::fun_eta_leg` needs that recursion threaded first.
                    return Ok(if same { refl() } else { Ev::Gap(Gap::FunEta) })
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
