use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::level::Level;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor, 
    nat_xor, nat_shr, nat_shl, ExportFile, ExprPtr, LevelPtr, 
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr
};
use crate::certify::{
    typing_is_gap, Admit, Backend, Cert, Certifier, DefEq, Dropped, TyGap, Typing,
};
use crate::reduct::{self, Node, Reduct, Rule, Trace, TracePtr};
use std::rc::Rc;
use std::error::Error;
use num_traits::pow::Pow;

/// How a recursor's major premise reached constructor form during
/// [`TypeChecker::reduce_rec`] — the input to the congruence leg the caller
/// emits in front of the ι step. See that method.
struct MajorStep<'t, C> {
    /// Which argument of the recursor spine the major premise is.
    idx: usize,
    /// What it reduced to, or the original argument when nothing certifiable
    /// happened.
    to: ExprPtr<'t>,
    /// The reduction, or `None` when there is no certifiable one.
    trace: TracePtr<'t, C>,
}

/// The field selected by a projection reduction and, when the subject moved,
/// the exact whnf trace which exposed its constructor.
struct ProjectionStep<'t, C> {
    field: ExprPtr<'t>,
    subject: TracePtr<'t, C>,
}

impl<'t, C> MajorStep<'t, C> {
    /// The redex with the major premise replaced by what it reduced to.
    ///
    /// On a hash-consed representation this is `n` lookups and no allocation
    /// when nothing changed, so the common case — a major that was already a
    /// constructor — rebuilds the identical pointer and `reduct::cong` drops
    /// the empty leg.
    fn rebuild<'p: 't>(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        fun: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> ExprPtr<'t> {
        let mut out = fun;
        for (i, a) in args.iter().enumerate() {
            let a = if i == self.idx { self.to } else { *a };
            out = ctx.mk_app(out, a);
        }
        out
    }
}

use DeltaResult::*;
use Expr::*;
use InferFlag::*;

/// Communicates the result of lazy delta reduction during definitional equality
/// checking; if we can no longer unfold any definitions, and we weren't already
/// able to show that the expressions were equal using a cheap method, then we return
/// `Exhausted`, and continue with more expensive checks. If we were able to cheaply
/// determine that two expressions are or are not equal, we return `FoundEqResult`.
///
/// Both variants carry evidence. `FoundEqResult` used to be a bare `bool`,
/// which is why the whole loop had to be papered over with a single
/// `Admit::LazyDelta`; `Exhausted` used to hand back the *unfolded* pair with no
/// record of the unfolding, so the caller's certificate silently justified the
/// reduced pair rather than the one it was asked about. Carrying the two legs
/// closes that gap.
///
/// Generic over the certificate type `C` for the same reason `TcCache` is: the
/// `Cert<'t, 'p>` alias ignores both lifetimes, so naming it here would leave
/// `'p` unused.
pub(crate) enum DeltaResult<'t, C> {
    /// Equality settled during unfolding. The certificate justifies the pair
    /// `lazy_delta_step` was *called* with, not the unfolded one; `None` means
    /// the two were shown unequal.
    FoundEqResult(Option<C>),
    /// Nothing left to unfold. `x`/`y` are the unfolded pair, and `x_leg`/
    /// `y_leg` justify `x₀ ≡ x` and `y₀ ≡ y` for the original arguments.
    Exhausted { x: ExprPtr<'t>, y: ExprPtr<'t>, x_leg: Option<C>, y_leg: Option<C> },
}

/// What [`TypeChecker::infer`] returns: the inferred type **and** the evidence
/// that the term inhabits it.
///
/// Inference used to return the type alone. That is the same defect as a
/// `bool`-returning `def_eq`, one judgement up: the fact `⟦e⟧ ∈ ⟦T⟧` is
/// established by the very recursion that computes `T`, and returning only `T`
/// throws the reason away — after which the only way to get it back is to
/// search for it from scratch. On `init-prelude` that search was 36% of the
/// runtime and re-established, per declaration, exactly what inference had just
/// worked out.
///
/// `cert` is not an `Option`. "No evidence" is a *value* — [`Certifier::ty_gap`]
/// — so that a rule handed an unjustified premise still has something to
/// propagate, and so that the place the evidence ran out is named and counted
/// rather than silently absent.
///
/// Generic over the typing-certificate type `Y` for the same reason
/// [`DeltaResult`] is generic over `C`: the `Typing<'t, 'p>` alias ignores both
/// lifetimes, so naming it here would leave `'p` unused. [`Inferred`] is the
/// instance every caller means.
pub(crate) struct Typed<'t, Y> {
    /// The inferred type.
    pub(crate) ty: ExprPtr<'t>,
    /// Why the term inhabits it.
    pub(crate) cert: Y,
}

/// [`Typed`] at the active backend's typing-certificate type.
pub(crate) type Inferred<'t, 'p> = Typed<'t, Typing<'t, 'p>>;

impl<'t, Y: Clone> Clone for Typed<'t, Y> {
    fn clone(&self) -> Self { Typed { ty: self.ty, cert: self.cert.clone() } }
}

impl<'t, Y> Typed<'t, Y> {
    /// Take the type and **throw the evidence away**, naming the place that does
    /// it so the discard is counted (see [`crate::certify::Dropped`]).
    ///
    /// Every remaining use of this is a place where a typing derivation exists
    /// and nothing downstream can consume it. They are not silent.
    fn discard(self, site: Dropped) -> ExprPtr<'t> {
        crate::certify::bump_dropped(site);
        self.ty
    }
}

/// What [`TypeChecker::proof_witness`] returns: `e` is a proof, and **why**.
///
/// "`e` is a proof" is two judgements, not one — `e` inhabits `α` and `α` is a
/// proposition — and the two are needed separately: Carneiro's Theorem 6.7
/// takes `α ∈ U₀` and `⟦e⟧ ∈ ⟦α⟧` and concludes `⟦e⟧ = •`. Returning the pair
/// rather than a `bool` is what stops the backend having to find them again.
///
/// Generic over the typing-certificate type `Y` for the same reason [`Typed`]
/// is: the `Typing<'t, 'p>` alias ignores both lifetimes, so naming it here
/// would leave `'p` unused. [`ProofOf`] is the instance every caller means.
///
/// `pub` rather than `pub(crate)` only because it appears in the signature of
/// [`Certifier::proj_red`], which is a method of a public trait.
pub struct Proof<'t, Y> {
    /// The proposition `e` proves, as inference computed it.
    pub ty: ExprPtr<'t>,
    /// `⟦e⟧ ∈ ⟦ty⟧`.
    pub mem: Y,
    /// `⟦ty⟧ ∈ ⟦Sort 0⟧`, i.e. `⟦ty⟧ ∈ U₀`.
    pub prop: Y,
}

/// [`Proof`] at the active backend's typing-certificate type.
pub(crate) type ProofOf<'t, 'p> = Proof<'t, Typing<'t, 'p>>;

/// **Whose question "is this type a proposition?" is being asked** — and the two
/// are genuinely different questions in this checker, which is not obvious and
/// cost a stage to find out.
///
/// A declaration is checked **at its own universe parameters**, once, and then
/// *interpreted* once per scheduled ground instantiation σ
/// ([`crate::instantiations`]). σ is applied in exactly one place,
/// `TcCtx::under_sigma`, and everything the proof backend reads goes through it;
/// nothing the checker reads does. So for a type whose sort is `Sort u` at a
/// parameter `u` that σ sends to `0`:
///
/// * Lean's answer is **no**. The declaration is being checked for every
///   instantiation at once, and a step licensed only at `u := 0` would let the
///   checker accept a declaration that is ill-typed at `u := 1`. This is the
///   answer `is_proposition`, `is_proof` and upstream nanoda give, and changing
///   it would change what the checker *accepts*.
/// * The model's answer is **yes**. `⟦Sort u⟧` is built through
///   `TgBackend::interp_level`, which substitutes σ first, so at σ = `{u ↦ 0}`
///   the interpretation of that sort *is* `U₀` — and `⟦α⟧ ∈ U₀` is exactly the
///   premise Carneiro's Theorem 6.7 wants. This is the answer
///   `TgBackend::term_clause` gives, because it must: it is deciding which
///   §6.2 clause `⟦·⟧` took, and `⟦·⟧` is σ-instantiated.
///
/// The rule that follows is: **the question that gates a checker verdict is
/// asked at the parameters; the question that produces evidence for the backend
/// is asked under σ.** Nothing is weakened by that split — a witness built under
/// σ is a witness about the very terms the backend's claim is about, and the
/// backend's `u_mp` against `u0_subsingleton` fails closed if it is not.
///
/// This is one of the places nanoda's structure makes `mini`'s answer not
/// transfer. Mini has no σ layer: it checks one instantiation, its `is_prop` is
/// exact, and the two questions coincide — so `MINI-DESIGN.md` §0.1's "there is
/// only one classifier" is free there and is *not* free here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PropAt {
    /// Lean's question, at the declaration's own universe parameters. Use this
    /// wherever the answer decides what the checker accepts.
    Params,
    /// The model's question, under the ambient instantiation σ. Use this
    /// wherever the answer only decides what evidence is offered to the backend.
    Sigma,
}

impl PropAt {
    /// Is this universe level `0`, on this reading of it?
    fn is_zero<'t>(self, ctx: &mut TcCtx<'t, '_>, l: LevelPtr<'t>) -> bool {
        let l = match self {
            PropAt::Params => l,
            PropAt::Sigma => ctx.under_sigma(l),
        };
        ctx.read_level(l) == Level::Zero
    }
}

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: TcCache<'t, Cert<'t, 'p>, Typing<'t, 'p>>,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
    /// The proof backend. Every definitional-equality conclusion drawn by this
    /// type checker is obtained from this object, so that the conclusion comes
    /// with evidence rather than being a bare `bool`.
    ///
    /// It is a field rather than a generic parameter because exactly one backend
    /// is active per build (see `certify.rs`), and because keeping it beside
    /// `ctx` lets the borrow checker see that `self.certifier` and `self.ctx` are
    /// disjoint — which is what makes `self.certifier.beta(self.ctx, ..)`
    /// possible without fighting the borrow checker at every call.
    pub(crate) certifier: Backend<'x, 't, 'p>,
    /// **Re-entrancy guard for [`Self::beta_arg_typing`].**
    ///
    /// That method calls `infer` from inside `whnf`, and `infer` calls
    /// `ensure_pi` calls `whnf` — the hot path calling itself, on a step kind
    /// that is 81 % of all reduction steps. The guard makes the nesting depth
    /// exactly one: an inference started by the reduction does not itself get
    /// to start inferences from the reduction. Termination is then immediate
    /// rather than an argument about shrinking terms, which is the property
    /// worth having here, since the terms in question are ones the reduction
    /// just built and no measure orders them.
    pub(crate) whnf_typing_depth: u32,
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`, at its own universe
    /// parameters.
    ///
    /// Kept as the one-argument entry point because it is what a caller with no
    /// schedule in hand means. [`Self::check_all_declars`] uses
    /// [`Self::check_declar_at`] instead, once per instantiation the pre-pass
    /// found.
    pub fn check_declar(&self, d: &Declar<'p>) { self.check_declar_at(d, &[]) }

    /// Check `d` at one ground level instantiation.
    ///
    /// `sigma` is empty for a monomorphic declaration, and for `Inductive` and
    /// `Quot`, which do not take one — see [`Self::check_declar_all`].
    ///
    /// **The checking is identical at every σ.** `infer`, `whnf` and `def_eq`
    /// never read σ; only the interpretation does. So this either accepts at
    /// every instantiation or panics at every one, and running it more than
    /// once cannot change a verdict.
    pub fn check_declar_at(&self, d: &Declar<'p>, sigma: &[u32]) {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_tc_and_declar(*d.info(), sigma, |tc| tc.check_declar_info(d).unwrap()),
            Inductive(..) => self.check_inductive_declar(d),
            Quot { .. } => self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)),
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_tc_and_declar(*d.info(), sigma, |tc| {
                    tc.check_declar_info(d).unwrap();
                    // Inference establishes `⟦val⟧ ∈ ⟦T'⟧` and returns the
                    // derivation alongside `T'`; the conversion check returns
                    // `⟦T'⟧ = ⟦T⟧`. Composing the two *is* `⊢ ⟦val⟧ ∈ ⟦T⟧`.
                    // Both halves used to be discarded here — the second by
                    // `assert!(… .is_some())` — and the backend then searched
                    // for the result from scratch.
                    let info = *d.info();
                    let Typed { ty: inferred_type, cert } = tc.infer(*val, crate::tc::InferFlag::Check);
                    let eq = tc.assert_def_eq(inferred_type, info.ty);
                    let typing = tc.certifier.ty_conv(tc.ctx, *val, inferred_type, info.ty, cert, &eq);
                    // The declaration is checked: `val : ty`. Hand the backend
                    // the evidence, so that the constant's typing theorem is
                    // *composed* once here rather than re-derived at every use.
                    // See `Certifier::declar_checked`.
                    tc.certifier.declar_checked(tc.ctx, info.name, info.uparams, info.ty, *val, typing);
                }),
            Constructor(ctor_data) => {
                self.with_tc_and_declar(*d.info(), sigma, |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                self.with_tc_and_declar(*d.info(), sigma, |tc| tc.check_declar_info(d).unwrap());
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                }
            }
        }
    }

    /// Check `d` at **every** instantiation the schedule requires of it.
    ///
    /// `Inductive` and `Quot` are checked once, at their own parameters, and
    /// that is deliberate rather than an omission: neither goes through
    /// [`ExportFile::with_tc_and_declar`], so neither has anywhere to put a σ —
    /// an inductive's check runs over a whole mutual block, mints temporary
    /// declarations with universe parameters of their own for nested
    /// inductives, and introduces a fresh eliminator universe that is by
    /// construction *not* one of the declaration's. Running them per
    /// instantiation would repeat the work with the interpretation unchanged.
    /// Their *uses* are unaffected: a use of `Foo.{0}` is interpreted under the
    /// using declaration's σ, and that is where the levels matter.
    fn check_declar_all(&self, d: &Declar<'p>, schedule: &crate::instantiations::Instantiations) {
        use Declar::*;
        // The `translated` row's non-vacuity guard is the identity
        // `reached + collapsed == scheduled`, and this function is the only
        // place the two terms can be told apart: what the walk enters, and what
        // the schedule named but a once-per-declaration kind absorbs. Counting
        // the absorption here rather than inferring it later is what keeps the
        // identity able to fail — see [`crate::tg::Translated`].
        crate::tg::Translated::reached();
        if matches!(d, Inductive(..) | Quot { .. }) {
            let listed = schedule.for_name(d.info().name).map_or(1, |s| s.len().max(1));
            crate::tg::Translated::collapsed(listed as u64 - 1);
            return self.check_declar_at(d, &[])
        }
        match schedule.for_name(d.info().name) {
            // The schedule's default seeding gives every declaration at least
            // one instantiation, so this is the empty-schedule case only.
            None => self.check_declar_at(d, &[]),
            Some(insts) => {
                crate::tg::Translated::collapsed(0);
                for (i, sigma) in insts.iter().enumerate() {
                    // The first pair is the one already counted above; the rest
                    // are counted as they are entered.
                    if i > 0 {
                        crate::tg::Translated::reached();
                    }
                    self.check_declar_at(d, sigma)
                }
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self, schedule: &crate::instantiations::Instantiations) {
        for declar in self.declars.values() {
            self.check_declar_all(declar, schedule);
        }
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    /// checkers.
    fn check_all_declars_par(&self, num_threads: usize, schedule: &crate::instantiations::Instantiations) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        use std::thread;
        let task_num = AtomicUsize::new(0);
        thread::scope(|sco| {
            let mut handles = Vec::new();
            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || loop {
                            let idx = task_num.fetch_add(1, Relaxed);
                            if let Some((_, declar)) = self.declars.get_index(idx) {
                                self.check_declar_all(declar, schedule);
                            } else {
                                break
                            }
                        })
                        .unwrap(),
                )
            }
            for t in handles {
                t.join().expect("A thread in `check_all_declars` panicked while being joined");
            }
        });
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is num_threads <= 1).
    ///
    /// The **level-instantiation pre-pass** runs first and decides the
    /// schedule; see [`crate::instantiations`]. It is published before any
    /// checking starts so that the backend can report any instantiation it
    /// interprets that the pre-pass did not predict.
    pub fn check_all_declars(&self) {
        let schedule = crate::instantiations::publish(crate::instantiations::Instantiations::compute(self));
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads, &schedule)
        } else {
            self.check_all_declars_serial(&schedule)
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        assert_eq!(dag.dbj_level_counter, 0);
        Self {
            ctx: dag,
            env,
            tc_cache: TcCache::new(),
            declar_info,
            certifier: crate::certify::new_backend(env),
            whnf_typing_depth: 0,
        }
    }

    /// Conduct the preliminary checks done on all declarations; a declaration
    /// must not contain duplicate universe parameters, mut not have free variables,
    /// and must have an ascribed type that is actually a type (`infer declaration.type` must
    /// be a sort).
    pub(crate) fn check_declar_info(&mut self, d: &Declar<'t>) -> Result<(), Box<dyn Error>> {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams));
        assert!(!self.ctx.has_fvars(info.ty));
        let inferred_type = self.infer_ty(info.ty, Check, Dropped::BinderSort);
        let sort = self.ensure_sort(inferred_type);

        // This is sort of a "soft" check in terms of soundness, but for theorems, ensure 
        // that they're propositions.
        if let Declar::Theorem {..} = d {
            if !self.ctx.is_zero(sort) {
                return Err(Box::<dyn Error>::from(format!("Theorem type for {:?} must be `Prop` (sort 0); found type {:?}",
                    self.ctx.debug_print(info.name),
                    self.ctx.debug_print(sort)
                )))
            }
        } 
        Ok(())
    }

    /// Infer a `Const` by retrieving its type from the environment, then substituting
    /// the universe parameters for the ones in the declaration we're checking.
    fn infer_const(&mut self, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(declar_info) = self.env.get_declar(&c_name).map(|x| x.info()).cloned() {
            if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                for c_uparam in self.ctx.read_levels(c_uparams).iter().copied() {
                    assert!(self.ctx.all_uparams_defined(c_uparam, this_declar_info.uparams))
                }
            }
            self.ctx.subst_declar_info_levels(declar_info, c_uparams)
        } else {
            panic!("declaration not found in infer_const, {:?}", self.ctx.debug_print(c_name))
        }
    }

    /// Retrieve the recursor rule corresponding to the constructor used in the major premise.
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> Option<RecRule<'t>> {
        if let Const { name: major_ctor_name, .. } = self.ctx.read_expr(major_const) {
            for r @ RecRule { ctor_name, .. } in rec_rules.iter().copied() {
                if ctor_name == major_ctor_name {
                    return Some(r)
                }
            }
        }
        None
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = self.ctx.unfold_const_apps(e_type)?;
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&c_name, false)?;
        // Name = `Point.mk`
        let ctor_name0 = all_ctor_names.get(0).copied()?;
        // Ctor data for `Point.mk`
        let ConstructorData { num_params, num_fields, .. } = self.env.get_constructor(&ctor_name0).unwrap();
        // Const { name := Point.mk, levels := .. }
        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        for i in 0..((*num_params) as usize) {
            out = self.ctx.mk_app(out, args[i])
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        for i in 0..((*num_fields) as usize) {
            let proj = self.ctx.mk_proj(c_name, i, e);
            out = self.ctx.mk_app(out, proj);
        }
        Some(out)
    }

    pub(crate) fn ensure_infers_as_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        let infd = self.infer_ty(e, Check, Dropped::BinderSort);
        self.ensure_sort(infd)
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        if let Sort { level, .. } = self.ctx.read_expr(e) {
            return level
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("ensur_sort could not produce a sort"),
        }
    }

    fn ensure_pi(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return e
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Pi { .. } => whnfd,
            _ => panic!("ensure_pi could not produce a pi"),
        }
    }

    /// [`Self::ensure_pi`], returning the reduction leg `e ≡ Π…` as well.
    ///
    /// `None` means `e` was already a `Π` and reflexivity applies. The leg is
    /// what `infer_app` composes into the head's typing via `ty_conv` — the
    /// silently dropped `ensure_pi` leg of `THREADING-CENSUS.md` §1.2, which
    /// `TgBackend::ty_bridge` used to compensate for with a delta-only re-walk.
    fn ensure_pi_with_cert(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return (e, None)
        }
        let (whnfd, leg) = self.whnf_with_cert(e);
        match self.ctx.read_expr(whnfd) {
            Pi { .. } => (whnfd, leg),
            _ => panic!("ensure_pi could not produce a pi"),
        }
    }

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag, site: Dropped) -> LevelPtr<'t> {
        let whnfd = self.infer_then_whnf(e, flag, site);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("infer_sort_of could not infer a sort"),
        }
    }

    fn try_eta_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        self.try_eta_struct_aux(x, y).flatten().or_else(|| self.try_eta_struct_aux(y, x).flatten())
    }

    fn try_eta_struct_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        let (_, name, _, args) = self.ctx.unfold_const_apps(y)?;
        let ConstructorData { inductive_name, num_params, num_fields, .. } = self.env.get_constructor(&name)?;
        if args.len() == (*num_params + *num_fields) as usize && self.env.can_be_struct(inductive_name) {
            let (x_type, y_type) =
                (self.infer_ty(x, InferOnly, Dropped::DefEqSide), self.infer_ty(y, InferOnly, Dropped::DefEqSide));
            if self.def_eq(x_type, y_type).is_some() {
                for i in (*num_params as usize)..args.len() {
                    let proj = self.ctx.mk_proj(*inductive_name, i - *num_params as usize, x);
                    let rhs = args[i];
                    if self.def_eq(proj, rhs).is_none() {
                        return None
                    }
                }
                crate::stepcount::bump(crate::stepcount::Kind::EtaStruct);
                return Some(self.admit(x, y, Admit::EtaStruct))
            }
        }
        None
    }

    fn str_lit_to_ctor_reducing(&mut self, x: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        self.ctx.str_lit_to_constructor(x).map(|x| self.whnf(x))
    }

    fn try_string_lit_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        if let (StringLit { ptr, .. }, App { fun, .. }) = self.ctx.read_expr_pair(x, y) {
            if let Some((name, _levels)) = self.ctx.try_const_info(fun) {
                if name == self.ctx.export_file.name_cache.string_of_list? {
                    // levels should be empty
                    let lhs = self.str_lit_to_ctor_reducing(ptr)?;
                    crate::stepcount::bump(crate::stepcount::Kind::StringLit);
                    let r = self.def_eq(lhs, y);
                    return Some(r.and_then(|_| self.admit(x, y, Admit::StringLit)))
                }
            }
        }
        None
    }

    fn try_string_lit_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        if !self.ctx.export_file.config.string_extension {
            return None
        }
        self.try_string_lit_expansion_aux(x, y)
            .flatten()
            .or_else(|| self.try_string_lit_expansion_aux(y, x).flatten())
    }

    // For structures that carry no additional information, elements with the same type are def_eq.
    fn def_eq_unit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        let x_ty = self.infer_then_whnf(x, InferOnly, Dropped::DefEqSide);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&name, false)?;
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer_ty(y, InferOnly, Dropped::DefEqSide);
        let r = self.def_eq(x_ty, y_type);
        r.and_then(|_| self.admit(x, y, Admit::UnitLike))
    }

    fn do_nat_bin(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, op: NatBinOp) -> Option<ExprPtr<'t>> {
        use NatBinOp::*;
        let (x, y) = (self.whnf(x), self.whnf(y));
        let (arg1, arg2) = (self.ctx.get_bignum_from_expr(x)?, self.ctx.get_bignum_from_expr(y)?);
        match op {
            Add => self.ctx.mk_nat_lit_quick(arg1 + arg2),
            Sub => self.ctx.mk_nat_lit_quick(nat_sub(arg1, arg2)),
            Mul => self.ctx.mk_nat_lit_quick(arg1 * arg2),
            Pow => self.ctx.mk_nat_lit_quick(arg1.pow(arg2)),
            Div => self.ctx.mk_nat_lit_quick(nat_div(arg1, arg2)),
            Mod => self.ctx.mk_nat_lit_quick(nat_mod(arg1, arg2)),
            Gcd => self.ctx.mk_nat_lit_quick(nat_gcd(&arg1, &arg2)),
            LAnd => self.ctx.mk_nat_lit_quick(nat_land(arg1, arg2)),
            LOr => self.ctx.mk_nat_lit_quick(nat_lor(arg1, arg2)),
            XOr => self.ctx.mk_nat_lit_quick(nat_xor(&arg1, &arg2)),
            Shl => self.ctx.mk_nat_lit_quick(nat_shl(arg1, arg2)),
            Shr => self.ctx.mk_nat_lit_quick(nat_shr(arg1, arg2)),
            Beq => self.ctx.bool_to_expr(arg1 == arg2),
            Ble => self.ctx.bool_to_expr(arg1 <= arg2),
        }
    }
    
    /// Try to reduce an expression `e` which is an application of `Nat.succ`,
    /// or an application of a supported binary operation. `e` must have no free
    /// variables.
    pub(crate) fn try_reduce_nat(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.ctx.export_file.config.nat_extension {
            return None
        }
        if self.ctx.has_fvars(e) {
            return None
        }
        let (f, args) = self.ctx.unfold_apps(e);
        let out = match (self.ctx.read_expr(f), args.as_slice()) {
            (Const { name, .. }, [arg]) if Some(name) == self.ctx.export_file.name_cache.nat_succ => {
                let v_expr = self.whnf(*arg);
                self.ctx.get_bignum_succ_from_expr(v_expr)
            }
            (Const { name, .. }, [arg1, arg2]) => {
                let op = if Some(name) == self.ctx.export_file.name_cache.nat_add {
                    NatBinOp::Add
                } else if Some(name) == self.ctx.export_file.name_cache.nat_sub {
                    NatBinOp::Sub
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mul {
                    NatBinOp::Mul
                } else if Some(name) == self.ctx.export_file.name_cache.nat_pow {
                    NatBinOp::Pow
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mod {
                    NatBinOp::Mod
                } else if Some(name) == self.ctx.export_file.name_cache.nat_div {
                    NatBinOp::Div
                } else if Some(name) == self.ctx.export_file.name_cache.nat_beq {
                    NatBinOp::Beq
                } else if Some(name) == self.ctx.export_file.name_cache.nat_ble {
                    NatBinOp::Ble
                } else if Some(name) == self.ctx.export_file.name_cache.nat_land {
                    NatBinOp::LAnd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_lor {
                    NatBinOp::LOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_xor {
                    NatBinOp::XOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_gcd {
                    NatBinOp::Gcd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shl {
                    NatBinOp::Shl
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shr {
                    NatBinOp::Shr
                } else {
                    return None
                };
                self.do_nat_bin(*arg1, *arg2, op)
            }
            _ => None,
        };
        if out.is_some() {
            crate::stepcount::bump(crate::stepcount::Kind::NatLit);
        }
        out
    }

    fn reduce_proj(
        &mut self,
        ty_name: NamePtr<'t>,
        idx: usize,
        structure: ExprPtr<'t>,
        cheap: bool,
    ) -> Option<ProjectionStep<'t, Cert<'t, 'p>>> {
        let (mut reduced, trace) = if cheap {
            self.whnf_no_unfolding_reduce(structure, true)
        } else {
            self.whnf_reduce(structure)
        };
        let after_whnf = reduced;
        if let StringLit { ptr, .. } = self.ctx.read_expr(reduced) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                reduced = s;
            }
        }
        let (_, name, _, args) = self.ctx.unfold_const_apps(reduced)?;
        let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;
        let i = (*num_params as usize) + idx;
        let field = args.get(i).copied().unwrap();
        // The string-literal rescue is not traced, so it cannot license a
        // claim about the rescued constructor. Preserve the old projection
        // rule in that case. Ordinary subject reduction records its exact
        // trace; the readiness gate below decides whether exposing every rule
        // in it is non-increasing for the active backend.
        let subject = if reduced == after_whnf
            && self.certifier.wants_proj_red_subject(self.ctx, ty_name, reduced)
            && self.authoritative_reduction_ready(&trace)
        {
            trace
        } else {
            None
        };
        Some(ProjectionStep { field, subject })
    }

    /// Whether replaying this reduction trace can avoid asking an independently
    /// unsupported rule.
    ///
    /// Delta/beta/zeta/sort are the established reduction rules. A nested
    /// projection is admitted only when *its own* structure has authoritative
    /// Mini evidence, and the same is true of iota. This is shared by projection
    /// subjects and exact equality-cache trace recall so neither path can widen
    /// support independently of the other.
    fn authoritative_reduction_ready(&mut self, trace: &TracePtr<'t, Cert<'t, 'p>>) -> bool {
        let Some(trace) = trace else { return true };
        match &trace.node {
            Node::One(Rule::Beta | Rule::Zeta | Rule::Delta | Rule::Sort) => true,
            Node::One(Rule::ProjRed) => {
                let (head, _) = self.ctx.unfold_apps(trace.from);
                let Expr::Proj { ty_name, structure, .. } = self.ctx.read_expr(head) else {
                    return false
                };
                self.certifier.wants_proj_red_subject(self.ctx, ty_name, structure)
            }
            Node::One(Rule::Iota) => {
                self.certifier.wants_proj_red_iota(self.ctx, trace.from, trace.to)
            }
            Node::One(Rule::Admitted(_)) => false,
            Node::Seq(l, r) => {
                self.authoritative_reduction_ready(&Some(l.clone()))
                    && self.authoritative_reduction_ready(&Some(r.clone()))
            }
            Node::Cong(sub) => self.authoritative_reduction_ready(&Some(sub.clone())),
            Node::ProjRed(sub) => {
                let (head, _) = self.ctx.unfold_apps(trace.from);
                let Expr::Proj { ty_name, .. } = self.ctx.read_expr(head) else {
                    return false
                };
                self.certifier.wants_proj_red_subject(self.ctx, ty_name, sub.to)
                    && self.authoritative_reduction_ready(&Some(sub.clone()))
            }
        }
    }

    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag, site: Dropped) -> ExprPtr<'t> {
        let ty = self.infer_ty(e, flag, site);
        self.whnf(ty)
    }

    #[allow(non_snake_case)]
    fn infer_proj(&mut self, _ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let structure_ty = self.infer_ty(structure, flag, Dropped::Probe);
        let structure_ty = self.whnf(structure_ty);
        let structure_ty_is_prop = self.is_proposition(structure_ty).0;
        let (_, struct_ty_name, struct_ty_levels, struct_ty_args) = self.ctx.unfold_const_apps(structure_ty).unwrap();

        let InductiveData { info: inductive_info, all_ctor_names, num_params, .. } =
            self.env.get_structure(&struct_ty_name, true).unwrap();

        let ConstructorData { info: ctor_info, .. } = self.env.get_constructor(&all_ctor_names[0]).unwrap();
        let mut ctor_ty = self.ctx.subst_declar_info_levels(*ctor_info, struct_ty_levels);
        for i in 0..(*num_params) {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { body, .. } => {
                    ctor_ty = self.ctx.inst(body, &[struct_ty_args[i as usize]]);
                }
                _ => panic!("Ran out of param telescope"),
            }
        }
        for i in 0..idx {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                      if structure_ty_is_prop && !self.is_proposition(binder_type).0 {
                          panic!("infer_proj prop")
                      }
                      let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                      ctor_ty = self.ctx.inst(body, &[arg]);
                    } else {
                      ctor_ty = body;
                    }
                }
                _ => panic!("Ran out of constructor telescope"),
            }
        }
        let reduced = self.whnf(ctor_ty);
        match self.ctx.read_expr(reduced) {
            Pi { binder_type, .. } => {
                if structure_ty_is_prop && !self.is_proposition(binder_type).0 {
                    panic!("infer_proj prop")
                }
                binder_type
            }
            _ => panic!("Ran out of constructor telescope getting field"),
        }
    }

    /// Infer the type of `e`, **together with the derivation that `e` inhabits
    /// it**.
    ///
    /// The evidence is threaded through every rule below. Where a rule cannot
    /// justify its conclusion the result is a named, counted gap
    /// ([`Certifier::ty_gap`]) rather than silence — the same discipline
    /// `def_eq` follows, applied to the typing judgement.
    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> Inferred<'t, 'p> {
        if let Some((ty, cert)) = self.tc_cache.infer_cache_check.get(&e).cloned() {
            return Typed { ty, cert }
        }
        if flag == InferFlag::InferOnly {
            if let Some((ty, cert)) = self.tc_cache.infer_cache_no_check.get(&e).cloned() {
                return Typed { ty, cert }
            }
        }
        let r = match self.ctx.read_expr(e) {
            // A local's type is its binder's, and the evidence is the ambient
            // hypothesis about it — acquired as an antecedent, to be discharged
            // at the `λ` that introduced it.
            Local { binder_type, .. } => {
                let cert = self.certifier.ty_local(self.ctx, e, binder_type);
                Typed { ty: binder_type, cert }
            }
            Var { .. } => panic!("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(e, level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(e, binder_type, val, body, flag),
            Const { name, levels, .. } => {
                let ty = self.infer_const(name, levels, flag);
                let cert = self.certifier.ty_const(self.ctx, e, ty);
                Typed { ty, cert }
            }
            Proj { ty_name, idx, structure, .. } => {
                let ty = self.infer_proj(ty_name, idx, structure, flag);
                let cert = self.certifier.ty_proj(self.ctx, e, ty, structure);
                Typed { ty, cert }
            }
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                let ty = self.ctx.nat_type().unwrap();
                let cert = self.certifier.ty_gap(self.ctx, e, ty, TyGap::Lit.name());
                Typed { ty, cert }
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                let ty = self.ctx.string_type().unwrap();
                let cert = self.certifier.ty_gap(self.ctx, e, ty, TyGap::Lit.name());
                Typed { ty, cert }
            }
        };
        // The two memos below are keyed on `e` alone and store *conditional*
        // typings deliberately, on the premise that a typing's assumptions are
        // always about locals occurring in `e` itself — so a hit taken under a
        // different context asks about the same locals or mentions none. That
        // premise is what licenses omitting the context from the key, and it has
        // only ever been asserted. Now it is checked, in debug builds, at the one
        // place an entry is made.
        //
        // A failure here is not something to weaken: it would mean an entry can
        // be recalled under a context its assumptions do not describe, and the
        // fix would be to key on the context or to refuse the entry, exactly as
        // `certify::is_unconditional` refuses for the equality cache.
        debug_assert!(
            self.certifier.typing_is_confined(self.ctx, e, r.ty, &r.cert),
            "a memoised typing mentions a local that is not in the expression it is keyed on"
        );
        match flag {
            InferFlag::InferOnly => {
                self.tc_cache.infer_cache_no_check.insert(e, (r.ty, r.cert.clone()));
            }
            InferFlag::Check => {
                self.tc_cache.infer_cache_check.insert(e, (r.ty, r.cert.clone()));
            }
        }
        r
    }

    /// The type alone, for a caller with nothing to compose the evidence with.
    /// The discard is counted; see [`Typed::discard`].
    pub(crate) fn infer_ty(&mut self, e: ExprPtr<'t>, flag: InferFlag, site: Dropped) -> ExprPtr<'t> {
        self.infer(e, flag).discard(site)
    }

    fn infer_sort(&mut self, e: ExprPtr<'t>, l: LevelPtr<'t>, flag: InferFlag) -> Inferred<'t, 'p> {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))
        }
        let out = self.ctx.succ(l);
        let ty = self.ctx.mk_sort(out);
        let cert = self.certifier.ty_sort(self.ctx, e, ty);
        Typed { ty, cert }
    }

    /// Infer the type of an application spine `f a₁ … aₙ`, carrying the typing
    /// derivation along it.
    ///
    /// The spine is walked as a telescope rather than one application at a time
    /// — upstream's shape, kept — so the certificate has to be rebuilt one
    /// application at a time alongside it: the rule for `f a` needs the partial
    /// application `f a₁ … aᵢ`, its `Π` type and the argument's typing, and only
    /// the last of those is lying around. The extra work is two `inst`s and one
    /// `mk_app` per argument, and it is skipped entirely the moment the head's
    /// derivation is a hole, since a rule with a hole for a premise concludes
    /// nothing.
    ///
    /// The argument's own typing is stated at the type *inferred* for it, and
    /// the rule needs it at the binder's domain. Those two are definitionally
    /// equal, and `assert_def_eq` has just produced the certificate saying so —
    /// which is precisely the certificate that used to be thrown away here.
    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> Inferred<'t, 'p> {
        let (head, mut args) = self.ctx.unfold_apps_stack(e);
        let mut ctx = Vec::new();
        let Typed { ty: mut fun, cert: head_cert } = self.infer(head, flag);
        // The partial application built so far, and the evidence for it.
        // `applied` is `None` once the evidence has run out: from that point
        // nothing downstream can use it, so it is not built. Under a backend
        // whose typings carry no information that is *every* step, which is why
        // threading evidence costs the null build nothing.
        let mut cert = head_cert;
        let mut applied = (!typing_is_gap(&cert)).then_some(head);
        while !args.is_empty() {
            match self.ctx.read_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    // The `Π` this step eliminates, at the arguments already
                    // consumed. Needed only if there is a derivation to carry.
                    let live = applied.is_some();
                    let fun_pi = if live { self.ctx.inst(fun, ctx.as_slice()) } else { fun };
                    // `None` means "no premise to offer": either inference is
                    // not checking arguments at all, or the function's own
                    // derivation had already run out, in which case there is
                    // nothing to lose and nothing to report.
                    let arg_cert: Option<Typing<'t, 'p>> = if flag == Check {
                        let Typed { ty: arg_type, cert: at } = self.infer(arg, flag);
                        let binder_type = self.ctx.inst(binder_type, ctx.as_slice());
                        let outer_scope_eager_setting = self.ctx.eager_mode;
                        if self.ctx.is_eager_reduce_app(arg) {
                            self.ctx.eager_mode = true;
                        }
                        // `arg_type` and `binder_type` get swapped here to accommodate the
                        // eager reduction branch in `def_eq` being focused on reducing the lhs.
                        let eq = self.assert_def_eq(binder_type, arg_type);
                        // replace the outer scope's setting before next iteration
                        self.ctx.eager_mode = outer_scope_eager_setting;
                        // `⟦arg⟧ ∈ ⟦arg_type⟧` converted along `⟦binder_type⟧ = ⟦arg_type⟧`
                        // into the `⟦arg⟧ ∈ ⟦binder_type⟧` the application rule
                        // asks for. This is the discarded certificate, put to
                        // work — and composed whether or not the head's own
                        // derivation is still alive, because it now has a
                        // second consumer: a beta contraction of this argument
                        // at this domain owes exactly this membership, and
                        // `app_arg_checked` hands it to the backend's store so
                        // the beta rule reads it instead of searching
                        // (`THREADING-CENSUS.md` §1.3). When the head is dead
                        // *and* the argument's own typing is a hole there is
                        // nothing to convert and nothing to store, so the
                        // composition is skipped — but the hole is still
                        // handed over, so the store can say of a later miss
                        // "this argument was checked, and its typing was
                        // already a gap then" rather than leaving the miss
                        // unattributed. Under the null backend every call here
                        // is a no-op, so it still pays nothing.
                        if !live && typing_is_gap(&at) {
                            self.certifier.app_arg_checked(self.ctx, arg, binder_type, &at);
                            None
                        } else {
                            let composed =
                                self.certifier.ty_conv(self.ctx, arg, arg_type, binder_type, at, &eq);
                            self.certifier.app_arg_checked(self.ctx, arg, binder_type, &composed);
                            live.then_some(composed)
                        }
                    } else if live {
                        // `InferOnly` does not check the argument, so there is
                        // no premise to offer the application rule — and here
                        // that loses a derivation that was still going, so it is
                        // recorded.
                        Some(self.certifier.ty_gap(self.ctx, arg, binder_type, TyGap::InferOnly.name()))
                    } else {
                        None
                    };
                    ctx.push(arg);
                    fun = body;
                    if let (Some(so_far), Some(arg_cert)) = (applied, arg_cert) {
                        let next = self.ctx.mk_app(so_far, arg);
                        let next_ty = self.ctx.inst(fun, ctx.as_slice());
                        cert = self
                            .certifier
                            .ty_app(self.ctx, next, next_ty, so_far, fun_pi, arg, cert, arg_cert);
                        applied = (!typing_is_gap(&cert)).then_some(next);
                    } else {
                        applied = None;
                    }
                }
                _ => {
                    let as_pi0 = self.ctx.inst(fun, ctx.as_slice());
                    // The derivation in hand — when there is one — is stated at
                    // exactly `as_pi0`: each `ty_app` step claimed the type
                    // `inst(fun, ctx)`. Reducing to the `Π` therefore has a leg
                    // the typing must be converted along, or the certificate is
                    // left claiming membership in the unreduced type while the
                    // walk continues at the reduced one. That leg used to be
                    // silently dropped (no `Dropped` entry, no compose —
                    // `THREADING-CENSUS.md` §1.2), and `TgBackend::ty_bridge`
                    // compensated delta-only. The certificate is only built
                    // when a derivation is live to consume it, so the null
                    // backend — under which `applied` is always `None` — pays
                    // nothing.
                    let as_pi = if let Some(so_far) = applied {
                        let (as_pi, leg) = self.ensure_pi_with_cert(as_pi0);
                        if let Some(leg) = leg.as_ref() {
                            cert = self.certifier.ty_conv(self.ctx, so_far, as_pi0, as_pi, cert, leg);
                            applied = (!typing_is_gap(&cert)).then_some(so_far);
                        }
                        as_pi
                    } else {
                        self.ensure_pi(as_pi0)
                    };
                    match self.ctx.read_expr(as_pi) {
                        Pi { .. } => {
                            // Only clear what we just instantiated.
                            ctx.clear();
                            fun = as_pi;
                        }
                        _ => panic!(),
                    }
                }
            }
        }
        let ty = self.ctx.inst(fun, ctx.as_slice());
        // The spine was rebuilt application by application, and the derivation
        // in hand is about `applied`. If that is not the expression being
        // inferred — because a step ran out of premises and left the derivation
        // describing a *prefix* of the spine, or because the rebuild diverged —
        // it is not about this term and must not be handed on. This is the one
        // place the invariant "never hand back a theorem not matched against the
        // claim" could be violated by an early exit, so it is checked here
        // rather than at each exit.
        if applied != Some(e) && !typing_is_gap(&cert) {
            cert = self.certifier.ty_gap(self.ctx, e, ty, TyGap::Claim.name());
        }
        Typed { ty, cert }
    }

    //fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
    //    match self.ctx.read_expr(e) {
    //        App {fun, arg, ..} => {
    //            let fun_ty = self.infer_then_whnf(fun, flag);
    //            match self.ctx.read_expr(fun_ty) {
    //                Pi {binder_type, body, ..} => {
    //                    if flag == InferFlag::Check {
    //                        let arg_ty = self.infer(arg, flag);
    //                        let outer_scope_eager_setting = self.ctx.eager_mode;
    //                        if self.ctx.is_eager_reduce_app(arg) {
    //                            self.ctx.eager_mode = true;
    //                        }
    //                        self.assert_def_eq(binder_type, arg_ty);
    //                        self.ctx.eager_mode = outer_scope_eager_setting;
    //                    }
    //                    self.ctx.inst(body, &[arg])
    //                },
    //                _ => panic!()
    //            }
    //        },
    //        _ => panic!()
    //    }
    //}

    /// Infer the type of a `λ` chain, carrying the typing derivation out from
    /// under the binders.
    ///
    /// The type is computed exactly as upstream computes it — the body's type,
    /// abstracted once over all the locals, then wrapped in `Π`s. The
    /// certificate cannot be built that way: the lambda rule is one binder at a
    /// time, so the `λ` and the `Π` at each level are rebuilt as the locals are
    /// popped, each abstracting only its own local. Abstracting one local means
    /// abstracting at *its* level while it is still the innermost open one, so
    /// this has to happen before `replace_dbj_level` retires it.
    ///
    /// The two constructions are independent, and the outermost `Π` the second
    /// one builds is checked against the type the first one returns. If they
    /// disagree the derivation is not about the type being claimed and is
    /// dropped for a gap.
    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> Inferred<'t, 'p> {
        let mut locals = Vec::new();
        let start_pos = self.ctx.dbj_level_counter;
        let e0 = e;
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            if let Check = flag {
                self.infer_sort_of(binder_type, flag, Dropped::BinderSort);
            }

            let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
            locals.push(local);
            e = body;
        }

        let instd = self.ctx.inst(e, locals.as_slice());
        let Typed { ty: infd, cert: body_cert } = self.infer(instd, flag);
        let mut abstrd = self.ctx.abstr_levels(infd, start_pos);
        // The certificate's own view: `cur` is the λ built so far, `cur_ty` its
        // `Π`, both still open in the locals not yet popped.
        let (mut cur, mut cur_ty, mut cert) = (instd, infd, body_cert);
        let mut live = !typing_is_gap(&cert);
        while let Some(local) = locals.pop() {
            match self.ctx.read_expr(local) {
                Local { binder_name, binder_style, binder_type, id, .. } => {
                    if live {
                        let crate::expr::FVarId::DbjLevel(lv) = id else {
                            panic!("infer_lambda: binder local is not a de Bruijn level")
                        };
                        let lam_body = self.ctx.abstr_levels(cur, lv);
                        let pi_body = self.ctx.abstr_levels(cur_ty, lv);
                        let lam = self.ctx.mk_lambda(binder_name, binder_style, binder_type, lam_body);
                        let pi = self.ctx.mk_pi(binder_name, binder_style, binder_type, pi_body);
                        cert = self.certifier.ty_lam(self.ctx, lam, pi, local, cur, cert);
                        live = !typing_is_gap(&cert);
                        cur = lam;
                        cur_ty = pi;
                    }
                    self.ctx.replace_dbj_level(local);
                    let t = self.ctx.abstr_levels(binder_type, start_pos);
                    abstrd = self.ctx.mk_pi(binder_name, binder_style, t, abstrd);
                }
                _ => panic!(),
            }
        }
        if live && (cur != e0 || cur_ty != abstrd) {
            cert = self.certifier.ty_gap(self.ctx, e0, abstrd, TyGap::Claim.name());
        }
        Typed { ty: abstrd, cert }
    }

    /// A `Π`'s type is `Sort (imax u v)`. There is no rule here: what the
    /// interpretation lacks is a membership fact about the universe a `Π`
    /// lands in, and no premise inference could supply would give one. The gap
    /// is named [`TyGap::Pi`] so that it is not confused with a rule that
    /// exists and declined.
    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> Inferred<'t, 'p> {
        let e0 = e;
        let mut universes = Vec::new();
        let mut locals = Vec::new();
        let c0 = self.ctx.dbj_level_counter;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            let dom_univ = self.infer_sort_of(binder_type, flag, Dropped::BinderSort);
            universes.push(dom_univ);
            locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, binder_type));
            e = body;
        }
        let instd = self.ctx.inst(e, locals.as_slice());
        let mut infd = self.infer_sort_of(instd, flag, Dropped::BinderSort);
        while let (Some(universe), Some(local)) = (universes.pop(), locals.pop()) {
            infd = self.ctx.imax(universe, infd);
            self.ctx.replace_dbj_level(local);
        }
        assert_eq!(c0, self.ctx.dbj_level_counter);
        let ty = self.ctx.mk_sort(infd);
        // Three cases, not two. `imax u 0 = 0`: a `Π` into `Prop` is a
        // *proposition*, and the thesis interprets it by a different clause
        // entirely (see [`TyGap::PiProp`]). A `Succ` is definitely not `Prop`.
        // And `imax u v` with `v` a **level parameter** does not simplify at
        // all — it is `0` when the parameter is instantiated at `0` and
        // `max(u,v)` otherwise — so at the declaration's own parameters the `Π`
        // is *neither*, and neither clause may be applied (see
        // [`TyGap::PiUndet`]). Counted apart so that the size of each is
        // measured rather than guessed.
        // Under the ambient instantiation, which is what makes the third case
        // *rare* rather than structural: at a ground σ an `imax` at a parameter
        // simplifies to a numeral and one of the first two cases applies. The
        // label has to be computed the same way `TgBackend::clause_after` does,
        // or a `Π` would be interpreted by one clause and its typing obligation
        // stated for another.
        let simplified = self.ctx.under_sigma(infd);
        let which = match self.ctx.read_level(simplified) {
            Level::Zero => TyGap::PiProp,
            Level::Succ(..) => TyGap::Pi,
            _ => TyGap::PiUndet,
        };
        let cert = self.certifier.ty_pi(self.ctx, e0, ty, which);
        Typed { ty, cert }
    }

    /// A `let` denotes its expansion and is interpreted as an explicit
    /// definition of it, so the expansion's typing carries across the defining
    /// equation. The value's type annotation is checked as before; that check's
    /// certificate has nothing to compose with here — the expansion has already
    /// substituted the value — so it is dropped, and counted.
    fn infer_let(
        &mut self,
        e: ExprPtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> Inferred<'t, 'p> {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag, Dropped::BinderSort);
            let val_ty = self.infer_ty(val, flag, Dropped::Probe);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq_only(val_ty, binder_type, Dropped::DefEqSide);
        }
        let expansion = self.ctx.inst(body, &[val]);
        let Typed { ty, cert } = self.infer(expansion, flag);
        let cert = if typing_is_gap(&cert) {
            cert
        } else {
            self.certifier.ty_let(self.ctx, e, ty, expansion, cert)
        };
        Typed { ty, cert }
    }
    
    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer_ty(e, InferOnly, Dropped::Probe);
            if !reduce_types && matches!(self.ctx.read_expr(ty), Sort {..}) {
                return e
            }
            if !reduce_proofs && self.is_proposition(ty).0 {
                return e
            }
        }
        let e = self.whnf(e);
        if let Some(cached) = self.tc_cache.strong_cache.get(&(e, reduce_types, reduce_proofs)).copied() {
            return cached
        }

        let out = match self.ctx.read_expr(e) {
            Expr::App {fun, arg, ..} => {
                let f = self.strong_reduce(fun, reduce_types, reduce_proofs);
                let arg = self.strong_reduce(arg, reduce_types, reduce_proofs);
                self.ctx.mk_app(f, arg)
            }
            Expr::Lambda {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_lambda(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Pi {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_pi(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Proj {ty_name, idx, structure, ..} => {
                let structure = self.strong_reduce(structure, reduce_types, reduce_proofs);
                let x = self.ctx.mk_proj(ty_name, idx, structure);
                let y = self.whnf(x);
                if y != x {
                    self.strong_reduce(y, reduce_types, reduce_proofs)
                } else {
                    x
                }
                
            }
            _ => e
        };
        self.tc_cache.strong_cache.insert((e, reduce_types, reduce_proofs), out);
        out
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Weak-head normalisation, with evidence.
    //
    // The public entry points still return a bare `ExprPtr`, so none of their
    // 28 callers change. Underneath, the reduction is split in two:
    //
    //   * `whnf_reduce` / `whnf_no_unfolding_reduce` reduce and **record what
    //     they did**, as a [`crate::reduct::Trace`] — the rules applied and
    //     their endpoints, three words a step and no backend call. The trace is
    //     memoised in the same entry as the reduct.
    //   * `whnf_no_unfolding_aux_with_cert` turns that record into a
    //     certificate for `e ≡ whnf(e)` — `Certifier::beta` for a beta
    //     contraction, `zeta` for a let, `delta` for a definition unfolding,
    //     `iota` for a recursor, and an `Admit` for the rules the backend has no
    //     method for yet (quotient, projection, native arithmetic) — and stores
    //     it back into the entry, so the derivation is paid for once.
    //
    // Splitting them is what lets certificates be built **on demand** without
    // the memo ever holding a reduct it cannot justify. The majority of whnf
    // calls come from type inference, which needs the reduct and nothing else;
    // asking the backend there would tally gaps against steps that no
    // definitional-equality conclusion rests on, and the coverage report would
    // then measure something other than what it says it measures. Recording the
    // steps costs nothing on that path and leaves the evidence available to the
    // first `def_eq` that comes asking.
    //
    // Convention for the `DefEq` returned by these functions: `None` means *no
    // step was taken*, so the reduct is the input and reflexivity applies; no
    // certificate is built for that case. It never means "not equal" — a
    // reduction is always justified.
    // ─────────────────────────────────────────────────────────────────────────

    /// Chain two reduction certificates into one for `a ≡ b`. `None` is the
    /// identity (see above), so composing with it builds no `trans`.
    ///
    /// `a` and `b` are the endpoints of the *composite*, and every caller below
    /// names them explicitly: `trans` is one of the rules that concludes
    /// something about two specific terms, so it is handed those terms and
    /// checks its result against them rather than assuming its premises met in
    /// the middle. Passing an approximation here would be worse than passing
    /// nothing, so where a caller cannot name the endpoints it must not call
    /// this.
    fn seq(&mut self, a: ExprPtr<'t>, b: ExprPtr<'t>, acc: DefEq<'t, 'p>, next: DefEq<'t, 'p>) -> DefEq<'t, 'p> {
        match (acc, next) {
            (None, c) | (c, None) => c,
            (Some(x), Some(y)) => {
                crate::certify::bump_certified();
                Some(self.certifier.trans(self.ctx, a, b, x, y))
            }
        }
    }

    /// Reverse a reduction leg, concluding `a ≡ b` from a leg for `b ≡ a`.
    /// `None` (reflexivity) is its own inverse.
    fn symm_leg(&mut self, a: ExprPtr<'t>, b: ExprPtr<'t>, leg: DefEq<'t, 'p>) -> DefEq<'t, 'p> {
        leg.map(|c| {
            crate::certify::bump_certified();
            self.certifier.symm(self.ctx, a, b, c)
        })
    }

    /// Compose reduction legs onto a verdict about a *reduced* pair, so the
    /// certificate justifies the pair the caller actually asked about:
    /// `l ≡ l'` (`l_leg`), `l' ≡ mid_r` (`mid`), then `mid_r ≡ r` (`r_leg`
    /// reversed). The conclusion is `l ≡ r`.
    ///
    /// `l'` is not a parameter because no rule built here concludes about it:
    /// the first `trans` concludes `l ≡ mid_r` and the second `l ≡ r`, and those
    /// are the two claims that have to be named. `mid_r` is a parameter because
    /// the intermediate `trans` and the `symm` both do conclude about it.
    fn compose_legs(
        &mut self,
        l: ExprPtr<'t>,
        mid_r: ExprPtr<'t>,
        r: ExprPtr<'t>,
        mid: DefEq<'t, 'p>,
        l_leg: DefEq<'t, 'p>,
        r_leg: DefEq<'t, 'p>,
    ) -> DefEq<'t, 'p> {
        let mid = mid?;
        let c = self.seq(l, mid_r, l_leg, Some(mid));
        let back = self.symm_leg(mid_r, r, r_leg);
        self.seq(l, r, c, back)
    }

    /// Put the two weak-head-normalisation legs back on a certificate stated
    /// about the *reduced* pair, so that it justifies `x ≡ y`.
    ///
    /// ```text
    ///     x ≡ x_n   (x_leg)
    ///     x_n ≡ y_n (mid)
    ///     y_n ≡ y   (y_leg, reversed)
    /// ```
    ///
    /// A leg that is `None` means no step was taken, so the corresponding
    /// endpoint is already the one the next step names. Getting this wrong is a
    /// silent lie in the certificate chain — exactly the failure mode the whole
    /// design exists to prevent — so there is one function and every exit from
    /// `def_eq` goes through it.
    fn compose_whnf_legs(
        &mut self,
        x: ExprPtr<'t>,
        y: ExprPtr<'t>,
        y_n: ExprPtr<'t>,
        mid: DefEq<'t, 'p>,
        x_leg: DefEq<'t, 'p>,
        y_leg: DefEq<'t, 'p>,
    ) -> DefEq<'t, 'p> {
        let mut c = mid?;
        if let Some(leg) = x_leg {
            crate::certify::bump_certified();
            c = self.certifier.trans(self.ctx, x, y_n, leg, c);
        }
        if let Some(leg) = y_leg {
            crate::certify::bump_certified();
            let back = self.certifier.symm(self.ctx, y_n, y, leg);
            c = self.certifier.trans(self.ctx, x, y, c, back);
        }
        Some(c)
    }

    /// The certificate for a recorded reduction, built at most once.
    ///
    /// Nothing is reduced here: the trace is the chain of steps that produced
    /// the memoised reduct, so the derivation follows it. Nor is it flattened —
    /// a sub-reduction that already has a certificate contributes that
    /// certificate and one `trans`, rather than its steps and one `trans` each.
    /// That is the whole point of the trace being a shared tree; see
    /// [`crate::reduct`].
    fn trace_cert(&mut self, t: &Rc<Trace<'t, Cert<'t, 'p>>>) -> DefEq<'t, 'p> {
        let stored = t.cert.borrow().clone();
        if stored.is_some() {
            crate::certify::bump_trace_cert(crate::certify::TraceCert::Recalled);
            return stored
        }
        crate::certify::bump_trace_cert(crate::certify::TraceCert::Derived);
        // **Two refuted parkings, 2026-08-10, measured on `init-prelude`.** The
        // slot is filled by `certify_reduct` only for a memo entry's own root,
        // which leaves every interior node of every trace tree — and every
        // composite `whnf_reduce`'s delta loop builds — deriving again on each
        // ask (the ledger: 19 recalls against 21 392 derivations). Parking here,
        // in the node the certificate is about, is the obvious repair and it is
        // not worth doing:
        //
        // * under `hypothesis_free` — the guard `certify_reduct` uses, which
        //   admits *conditional* certificates — recalls went 19 → 36 and the
        //   ledger blew up: copies 184 → 15 618, escapes 2 247 → 17 670, gaps
        //   15 532 → 30 955. A parked conditional certificate is a copy the
        //   escape ledger charges for and no rule consumes, which is the
        //   843 → 5037 lesson recorded at `certify_reduct`, one order of
        //   magnitude larger.
        // * under `is_unconditional`, which costs no escape, the ledger was
        //   unchanged row for row and recalls went 19 → 27: **8 derivations
        //   saved** for +0.03 % instructions.
        //
        // So the reuse is not being lost, it is not there: a reduction is
        // certified once because `eq_cache` answers the repeat question before
        // `whnf` is re-entered. The slot earns its keep at the memo roots, where
        // `certify_reduct` already fills it, and nowhere else.
        match &t.node {
            Node::One(rule) => self.step_cert(*rule, t.from, t.to),
            Node::Seq(l, r) => {
                let (l, r) = (l.clone(), r.clone());
                // The two halves must meet, or the composite is not about the
                // pair this node claims. `seq` would catch it — `trans` checks
                // its conclusion — but catching it here names the reduction
                // rather than leaving a mismatch to surface several rules up.
                if l.to != r.from {
                    return self.admit(t.from, t.to, Admit::Whnf)
                }
                let lc = self.trace_cert(&l);
                let rc = self.trace_cert(&r);
                self.seq(t.from, t.to, lc, rc)
            }
            Node::Cong(sub) => {
                let sub = sub.clone();
                self.cong_cert(t.from, t.to, &sub)
            }
            Node::ProjRed(sub) => {
                let sub = sub.clone();
                self.proj_red_step(t.from, t.to, Some(&sub))
            }
        }
    }

    /// The certificate for a [`Node::Cong`]: `app_cong` folded over the spine,
    /// reflexivity at every argument the inner reduction did not touch.
    ///
    /// The endpoints are **checked** before anything is built: either the head
    /// is exactly the inner reduction and every argument is unchanged, or the
    /// head is unchanged and every differing argument is exactly the inner
    /// pair. A `Cong` of any other shape is a recording bug and is reported as
    /// `Admit::Whnf`, like a `Seq` whose halves do not meet.
    fn cong_cert(
        &mut self,
        from: ExprPtr<'t>,
        to: ExprPtr<'t>,
        sub: &Rc<Trace<'t, Cert<'t, 'p>>>,
    ) -> DefEq<'t, 'p> {
        // Head reduction under an unchanged suffix. Do not use
        // `unfold_apps`: `sub.to` may itself be an application (the projected
        // field in `proj_reduced_carrier` is a partially-applied lambda), and
        // flattening would absorb part of the inner endpoint into the suffix.
        let (mut hf, mut ht) = (from, to);
        let mut suffix = Vec::new();
        while (hf, ht) != (sub.from, sub.to) {
            let (
                Expr::App { fun: ff, arg: fa, .. },
                Expr::App { fun: tf, arg: ta, .. },
            ) = (self.ctx.read_expr(hf), self.ctx.read_expr(ht))
            else {
                break
            };
            if fa != ta {
                break
            }
            suffix.push(fa);
            hf = ff;
            ht = tf;
        }
        if (hf, ht) == (sub.from, sub.to) && !suffix.is_empty() {
            let Some(mut c) = self.trace_cert(sub) else {
                return if from == to { None } else { self.admit(from, to, Admit::Whnf) }
            };
            let (mut lhs, mut rhs) = (hf, ht);
            for a in suffix.into_iter().rev() {
                lhs = self.ctx.mk_app(lhs, a);
                rhs = self.ctx.mk_app(rhs, a);
                crate::certify::bump_certified();
                let ac = self.certifier.refl(self.ctx, a);
                c = self.certifier.app_cong(self.ctx, lhs, rhs, c, ac);
            }
            return Some(c)
        }

        let (f1, args1) = self.ctx.unfold_apps(from);
        let (f2, args2) = self.ctx.unfold_apps(to);
        if args1.len() != args2.len() || args1.is_empty() {
            return self.admit(from, to, Admit::Whnf)
        }
        if f1 != f2 {
            return self.admit(from, to, Admit::Whnf)
        }
        let mut touched = false;
        for (a, b) in args1.iter().zip(args2.iter()) {
            if a != b {
                if (*a, *b) != (sub.from, sub.to) {
                    return self.admit(from, to, Admit::Whnf)
                }
                touched = true;
            }
        }
        if !touched {
            // The spines are identical, so the inner reduction was not about an
            // argument of this one. Reflexivity is the whole certificate and
            // `None` is how this module spells it.
            return if from == to { None } else { self.admit(from, to, Admit::Whnf) }
        }
        // **Start at the first argument that moved, not at the head.** Every
        // `app_cong` over an admitted premise is itself a reported gap, so a
        // fold across the whole spine turns one gap into one per argument —
        // `reduct.rs`' own header records that lesson costing 971 extra gaps
        // when a reduction was flattened. The prefix the two spines share is
        // one term, so `refl` covers all of it in a single certificate and the
        // fold runs only over the suffix from the first change onward. For a
        // recursor applied to exactly its own arguments the major premise is
        // last and that is **one** congruence.
        let first = args1.iter().zip(args2.iter()).position(|(a, b)| a != b).unwrap_or(0);
        let prefix = self.ctx.foldl_apps(f1, args1[..first].iter().copied());
        let inner = self.trace_cert(sub);
        let mut c = self.certifier.refl(self.ctx, prefix);
        let (mut lhs, mut rhs) = (prefix, prefix);
        for (a, b) in args1[first..].iter().copied().zip(args2[first..].iter().copied()) {
            let ac = if a == b {
                self.certifier.refl(self.ctx, a)
            } else {
                match inner.clone() {
                    Some(x) => x,
                    // The inner reduction is reflexivity, so the two spines
                    // cannot differ. Recording says otherwise, which is a bug in
                    // the recording and is reported as one.
                    None => return self.admit(from, to, Admit::Whnf),
                }
            };
            lhs = self.ctx.mk_app(lhs, a);
            rhs = self.ctx.mk_app(rhs, b);
            crate::certify::bump_certified();
            c = self.certifier.app_cong(self.ctx, lhs, rhs, c, ac);
        }
        Some(c)
    }

    /// Ask the backend for one recorded step.
    fn step_cert(&mut self, rule: Rule, a: ExprPtr<'t>, b: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match rule {
            // `beta` is asked for the whole `n`-argument contraction at once,
            // `delta` for the whole application `c a₁ … aₙ ≡ value a₁ … aₙ`;
            // both are exactly the pair the reduction recorded.
            Rule::Beta => {
                crate::certify::bump_certified();
                Some(self.certifier.beta(self.ctx, a, b))
            }
            Rule::Zeta => {
                crate::certify::bump_certified();
                Some(self.certifier.zeta(self.ctx, a, b))
            }
            Rule::Delta => {
                crate::certify::bump_certified();
                Some(self.certifier.delta(self.ctx, a, b))
            }
            Rule::Sort => {
                crate::certify::bump_certified();
                Some(self.certifier.sort(self.ctx, a, b))
            }
            // Not an `admit`: `admit`'s contract is "I cannot justify this", and
            // a backend that answered it by recognising the reason string would
            // be reading a diagnostic as an instruction. Backends with nothing
            // to say about iota inherit `Certifier::iota`'s default, which
            // admits.
            Rule::Iota => self.iota_step(a, b),
            Rule::ProjRed => self.proj_red_step(a, b, None),
            Rule::Admitted(site) => self.admit(a, b, site),
        }
    }

    /// The certificate for `e ≡ r`, given the reduction that got there, stored
    /// back into that reduction so the next caller does not derive it again.
    ///
    /// The endpoints are checked against the trace before anything is built.
    /// This is the guard that makes a recalled certificate safe: it is checked
    /// against the equation the caller is actually asking about, not assumed to
    /// match because it came out of the entry the caller looked in. A mismatch
    /// is a bug in the recording, and it is reported as one `Admit::Whnf` about
    /// the claim rather than passed off — `Admit::Whnf` staying at zero is the
    /// evidence that traces and reducts have not drifted apart.
    fn certify_reduct(&mut self, e: ExprPtr<'t>, r: ExprPtr<'t>, trace: &TracePtr<'t, Cert<'t, 'p>>) -> DefEq<'t, 'p> {
        let Some(t) = trace else {
            // No step taken, so `r` is `e` and reflexivity applies.
            return if e == r { None } else { self.admit(e, r, Admit::Whnf) }
        };
        if t.from != e || t.to != r {
            return self.admit(e, r, Admit::Whnf)
        }
        let cert = self.trace_cert(t);
        // Store it back — but only into a trace the memo is actually holding.
        // `whnf`'s cheap-projection variant builds a trace per call and
        // memoises nothing, and parking a copy of a *conditional* certificate
        // in a node that is about to be dropped costs one escape apiece: 843
        // escapes became 5037 on `init-prelude` before this test was here.
        //
        // **And never a certificate that stands under kernel hypotheses.** This
        // is the third of the `Thm` stores `certify::is_unconditional` discusses,
        // and the one that had no guard at all: the reduct memos are keyed on the
        // input `ExprPtr` alone and live for a whole declaration, so a `Γ ⊢ a = b`
        // parked here would be handed to a later caller under a context that need
        // not satisfy `Γ`. A *conditional* certificate is still stored — its
        // assumptions are antecedents inside the formula, so it imports nothing
        // and the escape ledger already counts it — but a hypothetical one is
        // not. See `certify::hypothesis_free`.
        if let Some(c) = cert.as_ref() {
            if !crate::certify::hypothesis_free(c) {
                crate::certify::bump_trace_cert(crate::certify::TraceCert::Hypothetical);
            } else {
                let memoised = self
                    .tc_cache
                    .whnf_no_unfolding_cache
                    .get(&e)
                    .and_then(|m| m.trace.as_ref())
                    .is_some_and(|m| Rc::ptr_eq(m, t));
                if memoised {
                    crate::certify::bump_trace_cert(crate::certify::TraceCert::Parked);
                    let mut slot = t.cert.borrow_mut();
                    if slot.is_none() {
                        *slot = Some(c.clone());
                    }
                } else {
                    crate::certify::bump_trace_cert(crate::certify::TraceCert::NotAMemoRoot);
                    // How much of the refusal a store-back extended to the
                    // *full*-`whnf` memo would convert. Counted rather than
                    // assumed: the delta loop's composite is the obvious
                    // candidate, but `whnf_no_unfolding_cheap_proj`'s
                    // never-memoised trace is in the same bucket and must stay
                    // refused.
                    #[cfg(feature = "stepcount")]
                    if self
                        .tc_cache
                        .whnf_cache
                        .get(&e)
                        .and_then(|m| m.trace.as_ref())
                        .is_some_and(|m| Rc::ptr_eq(m, t))
                    {
                        crate::certify::bump_trace_cert(crate::certify::TraceCert::WhnfRoot);
                    }
                }
            }
        }
        cert
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_reduce(e).0 }

    /// [`Self::whnf`], with the certificate for `e ≡ whnf(e)`.
    ///
    /// The full-reduction counterpart of
    /// [`Self::whnf_no_unfolding_aux_with_cert`]: the trace was recorded either
    /// way (recording is unconditional and three words a step), so this is the
    /// same derive-on-demand, done over the memo entry that includes the delta
    /// steps. `certify_reduct`'s store-back guard only recognises the
    /// no-unfolding memo, so a certificate built here is rebuilt per call — its
    /// *sub*-reductions still hit their own stored certificates, which is where
    /// the sharing lives.
    fn whnf_with_cert(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        let (r, trace) = self.whnf_reduce(e);
        let cert = self.certify_reduct(e, r, &trace);
        (r, cert)
    }

    /// Weak-head normalisation, recording the steps it takes.
    ///
    /// Recording is unconditional and nearly free — three words per step, no
    /// backend call — and it is what makes the memo below able to answer with
    /// evidence however it was first populated. See [`crate::reduct`].
    fn whnf_reduce(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, TracePtr<'t, Cert<'t, 'p>>) {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return (e, None)
        }
        if let Some(hit) = self.tc_cache.whnf_cache.get(&e) {
            return (hit.reduct, hit.trace.clone())
        }
        let mut cursor = e;
        // `acc` records `e ⟶* cursor` throughout the loop.
        let mut acc: TracePtr<'t, Cert<'t, 'p>> = None;
        loop {
            let (whnfd, step) = self.whnf_no_unfolding_reduce(cursor, false);
            acc = reduct::then(acc, step);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                acc = reduct::then(acc, reduct::one(Rule::Admitted(Admit::NatRed), whnfd, reduce_nat_ok));
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                acc = reduct::then(acc, reduct::one(Rule::Delta, whnfd, next_term));
                cursor = next_term;
            } else {
                self.tc_cache.whnf_cache.insert(e, Reduct { reduct: whnfd, trace: acc.clone() });
                return (whnfd, acc)
            }
        }
    }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.whnf_no_unfolding_reduce(e, false).0
    }

    /// [`Self::whnf_no_unfolding_reduce`], with the certificate for
    /// `e ≡ whnf_no_unfolding(e)`.
    ///
    /// This is the only place the backend is asked about a weak-head reduction,
    /// and it is asked once per memo entry: the reduction is memoised, so is its
    /// trace, and so — after the first caller — is the certificate. There is no
    /// `Evidence` flag any more, because a call that does not want a certificate
    /// simply calls [`Self::whnf_no_unfolding_reduce`] and the entry it leaves
    /// behind is no poorer for it.
    ///
    /// The cheap-projection variant shares the memo but never writes to it, so
    /// its certificate is not stored and is rebuilt per call —
    /// [`Self::certify_reduct`]'s guard is what keeps it from being filed under
    /// a key whose memoised reduct is the *further*-reduced one.
    fn whnf_no_unfolding_aux_with_cert(
        &mut self,
        e: ExprPtr<'t>,
        cheap_proj: bool,
    ) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        let (r, trace) = self.whnf_no_unfolding_reduce(e, cheap_proj);
        let cert = self.certify_reduct(e, r, &trace);
        (r, cert)
    }

    /// **Derive the domain obligation of a beta contraction, at the one place
    /// the term and a `TypeChecker` are in the same hand.**
    ///
    /// `Certifier::app_arg_checked`'s store is filled by `infer_app`, which
    /// visits only the applications *written in the term*. A beta redex the
    /// reduction itself builds was never at an application check, so the store
    /// has nothing and the beta rule hoists `⟦a⟧ ∈ ⟦A⟧` raw — 18 656 of the
    /// 20 328 raw hoists on `init-prelude`.
    ///
    /// **Why deriving, rather than any of the four transports.** The fact is
    /// not somewhere else waiting to be carried. Asked at four keys
    /// (`THREADING-CENSUS.md` §2): the ground pair reaches 34, the subject at
    /// another target 460, the *generalised* membership with free variables
    /// abstracted away 134, and the target-side twin 145 closing nothing. It
    /// was never derived anywhere, at any generality, so the only thing that
    /// produces it is a typing rule firing. `TgBackend` cannot fire one — it is
    /// a *field* of this struct, so there is no path from
    /// `domain_obligation` back to `infer`. Here there is.
    ///
    /// **The outermost binder only, and that is a measured stopping point.**
    ///
    /// `derive_beta` peels the lambda nest one binder at a time, so the domain
    /// it keys `aₖ` at is the domain of the *k*-th lambda — which for `k > 0`
    /// is the **instantiated** one, reachable only by rebuilding the
    /// intermediate lambdas that the composite `inst` in the caller exists to
    /// avoid. The outermost argument is free: its domain is `lam`'s own.
    ///
    /// # The inner binders were built, measured, and removed
    ///
    /// Walking the nest — advancing `cur = inst(body, [aₖ])` exactly as
    /// `derive_beta` does, so the keys line up — works, and it reaches far
    /// more arguments: 3 313 typed becomes 8 281. **It also fails the escape
    /// ratchet by a factor of 2.6, and it does not even reduce its own target
    /// population.** Two restrictions were tried:
    ///
    /// | | typed | never-checked hoists | escapes | instr. |
    /// | --- | ---: | ---: | ---: | ---: |
    /// | outermost only (this code) | 3 313 | **16 502** | **2 247** | +0.47 % |
    /// | + inner binders | 8 281 | 12 347 | 5 909 | +5.7 % |
    /// | + inner binders, closed nests only | 6 442 | 16 688 | 5 661 | +4.6 % |
    ///
    /// The mechanism is the one that also killed the open arguments: the walk
    /// doubles the inference volume, inference *reduces*, reduction raises new
    /// obligations, and those escape. Restricting to nests that are closed
    /// throughout — so every intermediate lambda is closed and none mentions a
    /// local — does not save it, and leaves the never-checked row *worse* than
    /// doing nothing (16 688 against 16 502). The 12 347 in the middle row is
    /// not a win either: it comes with 22 139 more obligations asked, so the
    /// population shrank by being outrun, not by being answered.
    ///
    /// Do not re-derive this by retrying the walk. What it would take is a way
    /// to type an argument that does not go through `infer` — the same
    /// research question the open arguments raise.
    ///
    /// Three things keep what remains from being expensive or unsound:
    /// * the backend is **asked first** (`wants_arg_typing`), so nothing is
    ///   inferred for an argument a check already handed over;
    /// * `def_eq`, not `assert_def_eq`, because a redex the reduction built
    ///   need not be well-typed and a hard failure would cost acceptance;
    /// * [`Self::whnf_typing_depth`] bounds the re-entrancy at one.
    fn beta_arg_typing(&mut self, lam: ExprPtr<'t>, arg: ExprPtr<'t>) {
        if self.whnf_typing_depth > 0 {
            return
        }
        let Lambda { binder_type, .. } = self.ctx.read_expr(lam) else { return };
        // **Closed arguments only.** Measured: inferring every unstored
        // argument works — the handoff's outright answers go 102 → 2 334 — but
        // inference reduces, so it drives more `whnf`, which raises more
        // obligations, and the run inflates past what the answers buy
        // (+16.8 % instructions, escapes 2 247 → 3 033). A closed argument is
        // the case where that trade is best: its typing is context-free, so
        // the inference memo serves every later occurrence in the run, and it
        // is exactly the population nothing else can reach — 7 717 raw hoists
        // over 407 distinct terms, none of which any typing rule anywhere ever
        // spoke about.
        if self.ctx.has_fvars(arg) {
            return
        }
        // **Ask the backend before paying.** Inference is not free and beta is
        // 81 % of all reduction steps, so nothing is inferred for an argument
        // some application check already handed over. The default
        // implementation answers `false`, which is why a build with no proof
        // backend pays nothing at all for any of this — the question, not just
        // the answer, is the backend's.
        if !self.certifier.wants_arg_typing(self.ctx, arg) {
            return
        }
        crate::stepcount::bump(crate::stepcount::Kind::BetaArgAsked);
        self.whnf_typing_depth += 1;
        // `Check`, not `InferOnly`: measured, `InferOnly` on the same population
        // buys +32 discharged obligations where `Check` buys +977, at the same
        // gap cost — the argument's own sub-derivations are what make its
        // typing derivable, and `InferOnly` does not build them.
        let Typed { ty: arg_type, cert: at } = self.infer(arg, InferFlag::Check);
        // **`def_eq`, not `assert_def_eq`, and the difference is acceptance.**
        // `assert_def_eq` fails the check when the two types do not match, and
        // that is right at an application the user wrote — but a beta redex
        // the *reduction* built carries no such guarantee (`def_eq` compares
        // arbitrary pairs, `to_ctor_when_k` fabricates constructor
        // applications, and a term reached by delta is only as well-typed as
        // the path that reached it). Asserting here would turn a file the
        // checker accepts into one it rejects, for a certificate that is
        // optional by construction. A mismatch simply declines.
        if let Some(eq) = self.def_eq(arg_type, binder_type) {
            let composed = self.certifier.ty_conv(self.ctx, arg, arg_type, binder_type, at, &eq);
            self.certifier.app_arg_checked(self.ctx, arg, binder_type, &composed);
            crate::stepcount::bump(crate::stepcount::Kind::BetaArgTyped);
        }
        self.whnf_typing_depth -= 1;
    }

    fn whnf_no_unfolding_reduce(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> (ExprPtr<'t>, TracePtr<'t, Cert<'t, 'p>>) {
        if let Some(hit) = self.tc_cache.whnf_no_unfolding_cache.get(&e) {
            return (hit.reduct, hit.trace.clone())
        }
        let (e_fun, args) = self.ctx.unfold_apps(e);
        let (should_cache, eprime, trace) = match self.ctx.read_expr(e_fun) {
            Proj { ty_name, idx, structure, .. } =>
                if let Some(proj) = self.reduce_proj(ty_name, idx, structure, cheap_proj) {
                    crate::stepcount::bump(crate::stepcount::Kind::Proj);
                    let carry_subject = args.is_empty();
                    let e1 = self.ctx.foldl_apps(proj.field, args.into_iter());
                    // A backend rule, not an admission: `Certifier::proj_red` is
                    // asked, and reports its own gap when it cannot answer. The
                    // premises it may want are gathered in `proj_red_step`, at
                    // certification time — not here, where most callers want the
                    // reduct and nothing else and inferring both endpoints would
                    // be work no conclusion rests on.
                    // TG's computation package concludes the projection
                    // itself. When that projection is subsequently applied,
                    // record the projection at `e_fun`, then lift it through
                    // the unchanged application suffix. Flattening the pair
                    // into one `ProjRed(e,e1)` loses the rule's redex shape and
                    // was exactly the last three gaps in
                    // `proj_reduced_carrier`.
                    let step = match proj.subject {
                        Some(subject) => {
                            let direct = reduct::proj_red(e_fun, proj.field, Some(subject));
                            if carry_subject { direct } else { reduct::cong(e, e1, direct) }
                        }
                        None => reduct::one(Rule::ProjRed, e, e1),
                    };
                    let (r, rest) = self.whnf_no_unfolding_reduce(e1, cheap_proj);
                    (true, r, reduct::then(step, rest))
                } else {
                    (false, self.ctx.foldl_apps(e_fun, args.into_iter()), None)
                },
            Sort { level, .. } => {
                debug_assert!(args.is_empty());
                let level = self.ctx.simplify(level);
                let s = self.ctx.mk_sort(level);
                // Simplifying the level can change the term (`Sort (max 0 u)`
                // becomes `Sort u`); that is exactly what the backend's `sort`
                // rule is for. Stated against `e` rather than `e_fun` so the
                // certificate cannot outrun the reduct even if the
                // `debug_assert` above were violated in a release build.
                let trace = if s == e { None } else { reduct::one(Rule::Sort, e, s) };
                (false, s, trace)
            }
            Lambda { .. } if !args.is_empty() => {
                let (mut b, mut n_args) = (e_fun, 0usize);
                while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.read_expr(b), &args[n_args..]) {
                    n_args += 1;
                    b = body;
                    crate::stepcount::bump(crate::stepcount::Kind::Beta);
                }
                // **The domain obligation, derived where the term exists.**
                // The backend is about to owe `⟦a₁⟧ ∈ ⟦A₁⟧` for this
                // contraction, and for a redex the reduction itself built
                // nobody has ever derived it. Here — and only here — the term
                // and a `TypeChecker` are in the same hand.
                self.beta_arg_typing(e_fun, args[0]);
                let b = self.ctx.inst(b, &args[..n_args]);
                let e1 = self.ctx.foldl_apps(b, args.into_iter().skip(n_args));
                // `n_args` beta contractions happen at once, so the backend is
                // asked for the composite `(λ…λ. b) a₁ … aₙ ≡ b[a⃗]`.
                let step = reduct::one(Rule::Beta, e, e1);
                let (r, rest) = self.whnf_no_unfolding_reduce(e1, cheap_proj);
                (true, r, reduct::then(step, rest))
            }
            Lambda { .. } => {
                debug_assert!(args.is_empty());
                (false, self.ctx.foldl_apps(e_fun, args.into_iter()), None)
            }
            Let { val, body, .. } => {
                crate::stepcount::bump(crate::stepcount::Kind::Zeta);
                let b = self.ctx.inst(body, &[val]);
                let e1 = self.ctx.foldl_apps(b, args.into_iter());
                let step = reduct::one(Rule::Zeta, e, e1);
                let (r, rest) = self.whnf_no_unfolding_reduce(e1, cheap_proj);
                (true, r, reduct::then(step, rest))
            }
            Const { name, levels, .. } =>
                if let Some(reduced) = self.reduce_quot(name, &args) {
                    crate::stepcount::bump(crate::stepcount::Kind::Quot);
                    let step = reduct::one(Rule::Admitted(Admit::Quot), e, reduced);
                    let (r, rest) = self.whnf_no_unfolding_reduce(reduced, cheap_proj);
                    (true, r, reduct::then(step, rest))
                } else if let Some((reduced, major)) = self.reduce_rec(name, levels, &args) {
                    crate::stepcount::bump(crate::stepcount::Kind::Iota);
                    // **Two steps, not one.** The congruence leg carries the
                    // major premise to constructor form inside the spine; the ι
                    // leg is then a redex whose major *is* a constructor, which
                    // is the only shape the backend's rule can serve. When the
                    // major needed no reduction the first leg is empty and
                    // `then` drops it, so nothing changes for the majority that
                    // already arrived in constructor form.
                    let mid = major.rebuild(&mut self.ctx, e_fun, &args);
                    let leg1 = reduct::cong(e, mid, major.trace.clone());
                    let step = reduct::then(leg1, reduct::one(Rule::Iota, mid, reduced));
                    let (r, rest) = self.whnf_no_unfolding_reduce(reduced, cheap_proj);
                    (true, r, reduct::then(step, rest))
                } else {
                    (false, self.ctx.foldl_apps(e_fun, args.into_iter()), None)
                },
            Var { .. } => panic!("Loose bvars are not allowed"),
            Pi { .. } => {
                debug_assert!(args.is_empty());
                (false, e_fun, None)
            }
            App { .. } => panic!(),
            Local { .. } | NatLit { .. } | StringLit { .. } =>
                (false, self.ctx.foldl_apps(e_fun, args.into_iter()), None),
        };
        if should_cache && !cheap_proj {
            // The trace goes in beside the reduct, not into a table beside the
            // memo: an entry that records what it answered but not why is what
            // used to force a later certified call to admit or to redo the work.
            self.tc_cache
                .whnf_no_unfolding_cache
                .insert(e, Reduct { reduct: eprime, trace: trace.clone() });
        }
        (eprime, trace)
    }

    /// The outer `Option` is "did this settle the question"; the inner `DefEq`
    /// is the verdict with its evidence.
    fn def_eq_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        if self.ctx.is_nat_zero(x) && self.ctx.is_nat_zero(y) {
            // The two zeros need not be the same node: one may be `Nat.zero`
            // and the other the literal `0`.
            return Some(self.admit(x, y, Admit::NatEq))
        }
        if let (NatLit { .. }, NatLit { .. }) = (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
            assert!(self.ctx.export_file.config.nat_extension);
            return Some(if x == y {
                // Literals are hash-consed, so equal literals are one node.
                crate::certify::bump_certified();
                Some(self.certifier.refl(self.ctx, x))
            } else {
                None
            })
        }
        if let (Some(x_pred), Some(y_pred)) = (self.ctx.pred_of_nat_succ(x), self.ctx.pred_of_nat_succ(y)) {
            let r = self.def_eq(x_pred, y_pred);
            Some(r.and_then(|_| self.admit(x, y, Admit::NatEq)))
        } else {
            None
        }
    }

    fn def_eq_binder_multi(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        if matches!(self.ctx.read_expr_pair(x, y), (Pi { .. }, Pi { .. }) | (Lambda { .. }, Lambda { .. })) {
            self.def_eq_binder_aux(x, y)
        } else {
            None
        }
    }

    /// Compare two binder chains, descending under the binders.
    ///
    /// This is where the context-freeness discipline bites: descending under a
    /// binder introduces a local (`mk_dbj_level`), and the eventual certificate
    /// must be a *closed* statement universally quantified over that local's
    /// interpretation, not one relative to a local context. The `lam_cong` /
    /// `pi_cong` rules in the backend are the ones that discharge the
    /// generalisation, and they do: the fold at the end of this function calls
    /// them and `bump_certified()`, so the chain is certified rather than
    /// admitted. `Admit::Binder` is not raised anywhere in this crate.
    #[allow(unused_parens)]
    fn def_eq_binder_aux(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        let mut locals = Vec::new();
        // One entry per binder descended through: whether it was a `Pi` (as
        // opposed to a `Lambda`) and the certificate for its domain. These are
        // folded back up at the end, innermost binder first, so the resulting
        // certificate mirrors the term structure.
        // Each frame records the two binders being related as well as the
        // domain certificate, so that `lam_cong`/`pi_cong` can check their
        // result against the claim rather than take it on trust.
        //
        // The binders are recorded together with the number of locals that had
        // been introduced when they were met, because the *un-instantiated*
        // binder is not the term the frame's certificate is about. Descending
        // through `λ n. λ m. b` opens the body at real locals `lₙ`, `lₘ`, so
        // the certificate handed to the inner frame relates `b[lₙ,lₘ]` to its
        // counterpart — whereas the inner binder as encountered is `λ m. b`
        // with a *loose* de Bruijn index where `lₙ` belongs, which the backend
        // interprets as an opaque `bvar` symbol. A frame whose terms mention
        // `bvar` cannot be matched against a certificate that mentions `lₙ`, so
        // `lam_cong`'s extensionality derivation could never apply below the
        // outermost binder. Instantiating each frame's binders at the locals
        // introduced *above* it — `lₙ` for the `λ m` frame, nothing for the
        // outermost — makes the frame's terms the ones its premises talk about.
        //
        // The instantiation is deferred to the fold below rather than done
        // here: it is pure plumbing for the certifier, and the chain can still
        // fail (a domain mismatch, or bodies that are not equal) after any
        // number of binders, in which case no frame is ever used.
        let mut frames: Vec<(bool, ExprPtr<'t>, ExprPtr<'t>, usize, Cert<'t, 'p>)> = Vec::new();
        while let (
            Pi { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Pi { binder_type: t2, body: body2, .. },
        )
        | (
            Lambda { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Lambda { binder_type: t2, body: body2, .. },
        ) = self.ctx.read_expr_pair(x, y)
        {
            let is_pi = matches!(self.ctx.read_expr(x), Pi { .. });
            let t1 = self.ctx.inst(t1, locals.as_slice());
            let t2 = self.ctx.inst(t2, locals.as_slice());
            if let Some(dom_cert) = self.def_eq(t1, t2) {
                frames.push((is_pi, x, y, locals.len(), dom_cert));
                locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, t1));
                x = body1;
                y = body2;
            } else {
                self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();
                return Some(None)
            }
        }

        let x0 = self.ctx.inst(x, locals.as_slice());
        let y0 = self.ctx.inst(y, locals.as_slice());
        let body = self.def_eq(x0, y0);
        self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();

        // Fold the domain certificates back over the body certificate, from the
        // innermost binder outwards. Each step is a genuine congruence rule, so
        // this whole path is certified rather than admitted.
        //
        // This is where context-freeness is discharged: `lam_cong`/`pi_cong` are
        // responsible for generalising over the local introduced above, turning a
        // judgement made under a binder into a closed one. That is what keeps the
        // resulting certificate valid relative to nothing but its own
        // hypotheses.
        //
        // It is *not*, on its own, what keeps the equality cache sound — this
        // sentence used to claim that and it has not been true since `Thm`
        // became a sequent. A closed `Γ ⊢ a = b` with `Γ` non-empty is exactly
        // what must not be cached under an `Expr`-pair key, because the key does
        // not mention `Γ`. The cache write is gated separately, on
        // `certify::is_unconditional` (see the write site below), and that
        // predicate — not generalisation — is the soundness argument.
        Some(body.map(|mut c| {
            while let Some((is_pi, fx, fy, depth, dom)) = frames.pop() {
                crate::certify::bump_certified();
                // The binders as the frame's certificate sees them: opened at
                // the locals introduced above this binder. `inst` is a pure
                // operation on hash-consed terms and the outermost frame
                // (`depth == 0`) is a no-op, so this changes only which term
                // the certifier is shown, never what was compared.
                //
                // Both kinds of frame want this, and used not to. `⟦λ⟧` is a
                // function *graph*, built by opening the body at a local, so
                // what its rule can talk about is the opened form; `⟦Π⟧` used to
                // be a symbol applied to the interpretation of the *raw* de
                // Bruijn body, which is why the `Π` frames were left alone. It
                // is not any more — a dependent `Π` is a dependent *product*
                // over a fibre, which is also built by opening the body — so the
                // asymmetry has gone with the reason for it.
                //
                // `inst` is a pure operation on hash-consed terms and the
                // outermost frame (`depth == 0`) is a no-op, so this changes
                // only which term the certifier is shown, never what was
                // compared.
                let prefix = &locals[..depth];
                let (fx, fy) = (self.ctx.inst(fx, prefix), self.ctx.inst(fy, prefix));
                c = if is_pi {
                    self.certifier.pi_cong(self.ctx, fx, fy, dom, c)
                } else {
                    self.certifier.lam_cong(self.ctx, fx, fy, dom, c)
                };
            }
            c
        }))
    }

    /// Two projections at the same index out of definitionally equal
    /// structures.
    ///
    /// A **congruence**, and it always was: `⟦s.i⟧` is `proj(i, ⟦s⟧)` over a
    /// signature symbol, so the equation follows from the structures' by the
    /// same congruence rule every other former uses, with no axiom about `proj`
    /// needed at all. The structures' certificate is the premise; it used to be
    /// established and dropped, and the conclusion admitted.
    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.ctx.read_expr_pair(x, y) {
            (Proj { idx: idx_l, structure: structure_l, .. }, Proj { idx: idx_r, structure: structure_r, .. }) => {
                if idx_l != idx_r {
                    return None
                }
                let structures = self.def_eq(structure_l, structure_r)?;
                crate::certify::bump_certified();
                Some(self.certifier.proj_cong(self.ctx, x, y, structures))
            }
            _ => None,
        }
    }

    /// Two `Local`s carrying the same id, their binder types definitionally
    /// equal.
    ///
    /// The side condition's certificate used to be established and dropped and
    /// the conclusion admitted. It is now handed to [`Certifier::local_eq`],
    /// which can settle the common case with no axiom at all: the TG backend
    /// identifies a level-local's kernel variable by level **and** interpreted
    /// declared type (`LocalKey`), so when the two types interpret to the same
    /// term the two locals *are* one variable and reflexivity is the whole
    /// derivation. Same level at types merely definitionally equal is two
    /// variables, and stays a gap — reported by the rule, under the same
    /// `def_eq_local` label this arm used to admit under.
    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.ctx.read_expr_pair(x, y) {
            (Local { id: x_id, binder_type: tx, .. }, Local { id: y_id, binder_type: ty, .. }) => {
                if x_id != y_id {
                    return None
                }
                let ty_eq = self.def_eq(tx, ty)?;
                crate::certify::bump_certified();
                Some(self.certifier.local_eq(self.ctx, x, y, ty_eq))
            }
            _ => None,
        }
    }

    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.ctx.read_expr_pair(x, y) {
            (Const { name: x_name, levels: x_levels, .. }, Const { name: y_name, levels: y_levels, .. }) =>
                if x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels) {
                    // Same constant at pointwise-equal levels: this one is real,
                    // the backend's `const_eq` rule discharges it directly.
                    crate::certify::bump_certified();
                    let c = self.certifier.const_eq(self.ctx, x, y);
                    Some(c)
                } else {
                    None
                },
            _ => None,
        }
    }

    /// Congruence over an application spine.
    ///
    /// Note this compares the arguments *before* the heads, preserving upstream
    /// order: arguments are the cheaper discriminator in practice, so failing
    /// fast on them avoids recursing into the head. The eventual certificate is
    /// a fold of `app_cong` over the spine.
    fn def_eq_app(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        let (f1, args1) = self.ctx.unfold_apps(x);
        if args1.is_empty() {
            return None
        }

        let (f2, args2) = self.ctx.unfold_apps(y);
        if args2.is_empty() {
            return None
        }

        if args1.len() != args2.len() {
            return None
        }

        // Collect the per-argument certificates. Upstream compares arguments
        // before heads (arguments discriminate faster in practice), and that
        // order is preserved; only the evidence is new.
        let mut arg_certs = Vec::with_capacity(args1.len());
        for (xx, yy) in args1.iter().copied().zip(args2.iter().copied()) {
            match self.def_eq(xx, yy) {
                Some(c) => arg_certs.push(c),
                None => return None,
            }
        }

        let Some(head) = self.def_eq(f1, f2) else { return None };

        // Fold `app_cong` left-to-right over the spine, mirroring how the
        // application was built: `f a b` is `((f a) b)`.
        //
        // Each step is handed the two partial applications it concludes about,
        // rebuilt one argument at a time. On a hash-consed representation
        // `mk_app` is a lookup, so this costs one interning step per argument
        // and the last pair it produces is `(x, y)` itself — the rule can check
        // its result against the claim at every position, which is the whole
        // point of giving it the terms.
        let (mut lhs, mut rhs) = (f1, f2);
        let mut c = head;
        for ((a, xx), yy) in arg_certs.into_iter().zip(args1).zip(args2) {
            lhs = self.ctx.mk_app(lhs, xx);
            rhs = self.ctx.mk_app(rhs, yy);
            crate::certify::bump_certified();
            c = self.certifier.app_cong(self.ctx, lhs, rhs, c, a);
        }
        Some(c)
    }

    /// Confirm `u ≡ v` — and **hand back the certificate**.
    ///
    /// This used to be `assert!(self.def_eq(u, v).is_some())`: it established
    /// the equality, checked that a reason existed, and dropped the reason. Two
    /// of its callers had something to do with it — the application rule's
    /// domain check and the top of `check_declar` — and both now convert a
    /// typing along it instead.
    ///
    /// A `None` is still a panic, because a checker that cannot show the
    /// equality must reject, and rejection here is upstream nanoda's behaviour.
    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) -> Cert<'t, 'p> {
        match self.def_eq(u, v) {
            Some(c) => c,
            None => panic!("assert_def_eq: not definitionally equal"),
        }
    }

    /// Confirm `u ≡ v` where nothing downstream can use the certificate, naming
    /// the place that drops it so the discard is counted rather than invisible.
    pub fn assert_def_eq_only(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>, site: Dropped) {
        let _cert = self.assert_def_eq(u, v);
        crate::certify::bump_dropped(site);
    }

    /// Convenience: admit an equality the checker believes but cannot yet
    /// justify. Each call site names itself via one of `certify::admits`, so
    /// the remaining holes are enumerable. See `certify.rs`.
    pub(crate) fn admit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, site: Admit) -> DefEq<'t, 'p> {
        crate::certify::bump_admit(site);
        Some(self.certifier.admit(self.ctx, x, y, site.name()))
    }

    /// One iota contraction, handed to the backend's own rule.
    ///
    /// Counted as a real rule for the same reason `beta`, `zeta` and `delta`
    /// are: the *checker* is no longer taking the step on trust, it is asking a
    /// rule. Whether the backend can answer is the backend's ledger to keep —
    /// [`Certifier::iota`]'s default implementation admits, so a backend that
    /// has nothing to say still reports a gap under the reason `iota`.
    fn iota_step(&mut self, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> DefEq<'t, 'p> {
        crate::certify::bump_certified();
        Some(self.certifier.iota(self.ctx, redex, reduct))
    }

    /// One recorded **projection reduction**, asked of the backend with the
    /// premises the backend cannot get for itself.
    ///
    /// [`Certifier::proj_red`] says what those premises are: the already-recorded
    /// subject trace when one is ready, plus the independent per-side proof
    /// witnesses. What belongs here is why they are gathered *now* rather than
    /// when the step was recorded: certifying the trace and
    /// [`Self::proof_witness`] both ask the backend for real derivations, and
    /// most weak-head reductions are performed for a caller that wants the
    /// reduct and no certificate at all. Recording the step costs a few words;
    /// this costs two inferences, and it is paid only when a
    /// definitional-equality conclusion actually rests on the step. That is the
    /// same split [`crate::reduct`]'s module doc draws between reducing and
    /// deriving, applied to the premises as well as to the derivation.
    ///
    /// Running inference here is *forward* computation on subterms the checker
    /// is already handling, which is the permitted way to obtain a fact
    /// (`MINI-DESIGN.md` §0) — as opposed to the backend's `syn_type` +
    /// `has_type_a` route, which is the banned one. It is also strictly more
    /// informative: `syn_type` is a delta-only transcription of inference, so
    /// where it gives up inference does not.
    fn proj_red_step(
        &mut self,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        subject: Option<&Rc<Trace<'t, Cert<'t, 'p>>>>,
    ) -> DefEq<'t, 'p> {
        let reduced_subject = if let Some(subject) = subject {
            let (head, _) = self.ctx.unfold_apps(redex);
            let Expr::Proj { structure, .. } = self.ctx.read_expr(head) else {
                return self.admit(redex, reduct, Admit::Whnf)
            };
            if structure != subject.from || structure == subject.to {
                return self.admit(redex, reduct, Admit::Whnf)
            }
            let Some(cert) = self.trace_cert(subject) else {
                return self.admit(redex, reduct, Admit::Whnf)
            };
            Some((subject.to, cert))
        } else {
            None
        };
        let l = self.proof_witness(redex, PropAt::Sigma);
        let r = self.proof_witness(reduct, PropAt::Sigma);
        crate::certify::bump_certified();
        Some(self.certifier.proj_red(self.ctx, redex, reduct, reduced_subject, l, r))
    }

    /// Decide whether `x` and `y` are definitionally equal, returning a
    /// certificate for *why* when they are.
    ///
    /// The `Option` is the whole point: upstream nanoda returns `bool` here, and
    /// a `bool` cannot say why. Every `Some` below is accompanied by evidence,
    /// even if — for now — much of that evidence is an `admit` naming a hole
    /// still to be closed.
    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        crate::stepcount::bump(crate::stepcount::Kind::DefEqCall);
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            return easy
        }

        // `def_eq` compares the *reduced* terms, so the certificate for
        // `x_n ≡ y_n` does not on its own justify `x ≡ y`. The two reduction
        // legs have to be composed back on at the end:
        //
        //     x ≡ x_n   (reduction)
        //     x_n ≡ y_n (the work below)
        //     y_n ≡ y   (reduction, reversed)
        //
        // Getting this wrong would be a silent lie in the certificate chain —
        // exactly the failure mode the whole design exists to prevent.
        //
        // The legs are now the certificates the reduction itself emitted: a
        // composition of the actual beta/zeta/iota/projection steps taken,
        // rather than an opaque `Admit::Whnf`.
        let (x_n, x_leg) = self.whnf_no_unfolding_aux_with_cert(x, true);
        let (y_n, y_leg) = self.whnf_no_unfolding_aux_with_cert(y, true);

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            // Reduce first, certify only on the licensing branch: when `x_nn`
            // is not `Bool.true` this whole probe concluded nothing, and
            // deriving a certificate for it would be work no conclusion rests
            // on (the trace is recorded either way, so the first path that
            // does conclude something pays instead).
            let (x_nn, x_nn_trace) = self.whnf_reduce(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                // Every leg of this shortcut is in hand: `x ≡ x_n` (`x_leg`),
                // `x_n ≡ x_nn` from the trace just recorded, and `x_nn` *is*
                // `y_n` — both are the hash-consed `Bool.true` constant — so
                // the middle leg is already stated about `x_n ≡ y_n`. A `None`
                // leg means no step was taken, i.e. `x_n` was `Bool.true`
                // itself, and the middle is reflexivity. This used to be
                // `Admit::BoolTrue` with all three legs discarded.
                let x_nn_leg = self.certify_reduct(x_n, x_nn, &x_nn_trace);
                let mid = match x_nn_leg {
                    Some(c) => Some(c),
                    None => {
                        crate::certify::bump_certified();
                        Some(self.certifier.refl(self.ctx, x_n))
                    }
                };
                // Early return, deliberately: like the quick-check early return
                // below, this path has never reached the `eq_cache.union` at
                // the bottom, and which pairs get cached is nanoda's behaviour,
                // not this change's to alter.
                return self.compose_whnf_legs(x, y, y_n, mid, x_leg, y_leg)
            }
        }

        // The quick check on the *reduced* pair may not return its certificate
        // as it stands: that certificate is about `x_n ≡ y_n`, and the claim is
        // `x ≡ y`. Handing it back unchanged gives the caller a proof of the
        // wrong equation — reflexivity, when one side reduces to the other —
        // which the backend's congruence guard then rejects several levels up,
        // where the reason is no longer visible, and which nothing rejects at
        // all when the caller is the top-level judgement. So the reduction legs
        // go on here too, exactly as they do for every other branch below.
        //
        // It still returns *early*, and that is deliberate: falling through
        // would also reach the `eq_cache.union` at the bottom, which this path
        // has never done, and the checker's caches are not this change's to
        // repopulate. The reason it used to be given — that a union-find hit is
        // an `Admit::Cache` rather than a proof, so filling the cache more
        // eagerly traded derivations for gaps (measured: 50 `eq_cache` gaps over
        // the tutorials rather than 6) — no longer holds: a hit now composes the
        // certificates along the explain path (see [`Self::recall_eq`]). What
        // remains is simply that changing which pairs get cached would change
        // nanoda's behaviour, which is out of scope.
        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            return self.compose_whnf_legs(x, y, y_n, easy, x_leg, y_leg)
        }

        let result = if let Some(c) = self.proof_irrel_eq(x_n, y_n) {
            Some(c)
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                // Already stated about `x_n ≡ y_n`: `lazy_delta_step` composed
                // its own unfolding legs back on.
                FoundEqResult(c) => c,
                Exhausted { x: xd, y: yd, x_leg: dx_leg, y_leg: dy_leg } => {
                    let mid = self
                        .def_eq_const(xd, yd)
                        .or_else(|| self.def_eq_local(xd, yd))
                        .or_else(|| self.def_eq_proj(xd, yd))
                        .or_else(|| {
                            let (xn0, yn0) = (xd, yd);
                            // Reducing further here changes what is being
                            // compared, so these two legs have to be carried
                            // onto the recursive result as well.
                            let (x_n, x_step) = self.whnf_no_unfolding_aux_with_cert(xn0, false);
                            let (y_n, y_step) = self.whnf_no_unfolding_aux_with_cert(yn0, false);
                            if x_n != xn0 || y_n != yn0 {
                                let inner = self.def_eq(x_n, y_n);
                                // `x_step : xn0 ≡ x_n`, `inner : x_n ≡ y_n`,
                                // `y_step : yn0 ≡ y_n`; the claim is about the
                                // pair this branch was entered with.
                                self.compose_legs(xn0, y_n, yn0, inner, x_step, y_step)
                            } else {
                                self.def_eq_app(x_n, y_n)
                                    .or_else(|| self.try_eta_expansion(x_n, y_n))
                                    .or_else(|| self.try_eta_struct(x_n, y_n))
                                    .or_else(|| self.try_string_lit_expansion(x_n, y_n))
                                    .or_else(|| self.def_eq_unit(x_n, y_n))
                            }
                        });
                    // `dx_leg : x_n ≡ xd`, `mid : xd ≡ yd`, `dy_leg : y_n ≡ yd`;
                    // the whole thing is about the weak-head-normalised pair,
                    // which the block below then lifts to `x ≡ y`.
                    self.compose_legs(x_n, yd, y_n, mid, dx_leg, dy_leg)
                }
            }
        };
        // Compose the reduction legs back on, so the returned certificate
        // justifies `x ≡ y` rather than merely `x_n ≡ y_n`.
        //
        // Both compositions are named against the pair they conclude about:
        // `x ≡ y_n` first, then `x ≡ y`. A leg that is `None` means no step was
        // taken (see the convention above), so the corresponding endpoint is
        // already the one the next step names.
        let result = self.compose_whnf_legs(x, y, y_n, result, x_leg, y_leg);

        if let Some(c) = &result {
            // The certificate goes onto the union edge, so that a later hit is
            // answered by composing along the explain path rather than by
            // admitting `Admit::Cache` — see [`Self::recall_eq`].
            //
            // Only a certificate that rests on nothing is kept: see
            // `certify::is_unconditional` for what a cached conditional one
            // costs and why it is not worth it. The union itself happens either
            // way — what the checker decides must not come to depend on what the
            // backend could prove.
            let keep = crate::certify::is_unconditional(c).then(|| c.clone());
            self.tc_cache.eq_cache.union(x, y, keep);
        }
        result
    }

    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> Option<ExprPtr<'t>> {
        let (_fun, name, levels, args) = self.ctx.unfold_const_apps(e)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&name)?;
        let ctor_name = all_ctor_names[0];
        let new_const = self.ctx.mk_const(ctor_name, levels);
        let args = args.into_iter().take(num_params);
        Some(self.ctx.foldl_apps(new_const, args))
    }

    fn to_ctor_when_k(
        &mut self,
        major: ExprPtr<'t>,
        rec: &RecursorData<'t>,
    ) -> Option<ExprPtr<'t>> {
        if !rec.is_k {
            return None
        }
        let major_ty = self.infer_then_whnf(major, InferOnly, Dropped::DefEqSide);
        let f = self.ctx.unfold_apps_fun(major_ty);
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) if name == n => {
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                // This sometimes has free variables.
                let new_type = self.infer_ty(new_ctor_app, InferOnly, Dropped::DefEqSide);
                if self.def_eq(major_ty, new_type).is_some() {
                    Some(new_ctor_app)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn is_ctor_app(&self, e: ExprPtr<'t>) -> Option<NamePtr<'t>> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Constructor { .. }) = self.env.get_declar(&name) {
                return Some(name)
            }
        }
        None
    }

    fn iota_try_eta_struct(&mut self, ind_name: NamePtr<'t>, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if (!self.env.can_be_struct(&ind_name)) || self.is_ctor_app(e).is_some() {
            e
        } else {
            let e_type = self.infer_then_whnf(e, InferOnly, Dropped::DefEqSide);
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } if name == ind_name => {
                    let e_sort = self.infer_then_whnf(e_type, InferOnly, Dropped::DefEqSide);
                    // If it's a prop, return the original `e`
                    if e_sort == self.ctx.prop() {
                        e
                    } else {
                        // if it's not a prop, try to eta expand
                        self.expand_eta_struct_aux(e_type, e).unwrap_or(e)
                    }
                }
                _ => e,
            }
        }
    }
    
    /// One ι reduction, **and how the major premise got to be a constructor**.
    ///
    /// The second half is the whole of task link 3. This used to return the
    /// reduct alone, having weak-head-normalised the major premise internally
    /// and thrown that reduction away, so the caller reported a single `Iota`
    /// step from the *unreduced* redex — and the backend's ι rule, which reads
    /// the major off `args[major_idx]`, was handed something that is not a
    /// constructor and could only decline. That is 486 originated gaps on
    /// `init-prelude` and **3 066** with the sub-tree they feed, the second
    /// largest origin in the ledger, and it is not a missing derivation: the
    /// checker knows the reduction, it just did not say so.
    ///
    /// So the major's own trace comes back with the reduct, and the caller
    /// emits **two** steps where it emitted one. `None` for the trace means the
    /// major was already in constructor form, in which case the old single step
    /// is still exactly right.
    ///
    /// # Only the part that has a trace
    ///
    /// `whnf` is traced; the four shape-level rescues around it —
    /// [`Self::to_ctor_when_k`], literal-to-constructor for `Nat` and `String`,
    /// and [`Self::iota_try_eta_struct`] — are not. So what comes back is the
    /// major *as `whnf` left it*, together with the trace for exactly that, and
    /// the caller only splits the step when the rescues changed nothing after
    /// it. Where one of them fired the behaviour is unchanged, which is the
    /// point: this widens what can be certified and moves nothing else.
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<(ExprPtr<'t>, MajorStep<'t, Cert<'t, 'p>>)> {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major0 = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major0, rec).unwrap_or(major0);
        // The one reduction of the major premise that carries evidence. Kept
        // only if it starts where the redex's own argument does — a `K` rescue
        // in front of it has no certificate and would make the leg a claim
        // about a different term.
        let (major, whnf_trace) = {
            let (r, tr) = self.whnf_reduce(major);
            (r, if major == major0 { tr } else { None })
        };
        let after_whnf = major;
        let major = match self.ctx.read_expr(major) {
            NatLit { ptr, .. } => self.ctx.nat_lit_to_constructor(ptr).unwrap_or(major),
            StringLit { ptr, .. } => self.str_lit_to_ctor_reducing(ptr).unwrap_or(major),
            _ => {
                let ind_rec_name_prefix = self.ctx.get_major_induct(rec).unwrap();
                self.iota_try_eta_struct(ind_rec_name_prefix, major)
            }
        };
        let (major_ctor, major_ctor_args) = self.ctx.unfold_apps(major);
        let rec_rule = self.get_rec_rule(rec_rules, major_ctor)?;

        // The number of parameters in the constructor is not necessarily
        // equal to the number of parameters in the recursor when we have
        // nested inductive types.
        let num_extra_params_to_major =
            major_ctor_args.len().checked_sub(rec_rule.ctor_telescope_size_wo_params as usize).unwrap();
        let major_ctor_args_wo_params = major_ctor_args.into_iter().skip(num_extra_params_to_major).collect::<Vec<_>>();
        let r = self.ctx.subst_expr_levels(rec_rule.val, info.uparams, const_levels);
        let r = self.ctx.foldl_apps(r, args.iter().copied().take((num_params + num_motives + num_minors) as usize));
        let r = self.ctx.foldl_apps(r, major_ctor_args_wo_params.into_iter());
        let reduct = self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx() + 1).copied());
        // **The leg is offered only when saying more cannot cost more.**
        //
        // Three conditions, and the third is the one that matters. `whnf` alone
        // has to have got the major to the form the rule fired on; it has to
        // have moved at all; and its reduction has to be **fully ruled** — no
        // `Rule::Admitted` anywhere in the recorded tree.
        //
        // Without the third, splitting is a large loosening measured rather
        // than argued: it makes the checker ask for certificates it never asked
        // for, and on `init-prelude` that surfaces reductions whose own steps
        // are admissions — gaps 15 734 → **20 707**, and still 17 008 with the
        // numeral rule simulated. The ι origin does collapse (486 own → 228,
        // sub-tree 3 286 → 353) but it collapses *into* `nat_reduce`, whose
        // sub-tree goes 111 → 4 452, and the ledger is worse for it. A ratchet
        // that loosens needs a written trade and this one has nothing to trade.
        //
        // With it, the split fires only where every step of the major's
        // reduction is a rule some backend method is asked about, so the
        // congruence leg costs no admission the old single step was not already
        // paying for — **strictly non-increasing**. Today that is a small
        // population and the ledger does not move. It is not dead code waiting
        // for a caller: `Nat.ble` on literals is `Rule::Admitted(Admit::NatRed)`
        // *today*, and the moment the numeral rule makes it a real rule those
        // traces become fully ruled and this fires on 466 of the 486 by itself.
        //
        // `whnf_trace.is_some()` is not redundant with `major != major0`, and
        // leaving it out was a real defect: a reduction can move a term and
        // record nothing (an empty trace is the *identity*, so `then` drops the
        // congruence leg), and the composite would then claim to start at the
        // redex while actually starting at the rebuilt one. `certify_reduct`
        // catches that as `Admit::Whnf` — 8 of them on `init-prelude`, which is
        // exactly what that counter is for and why it is required to be zero.
        let step = if major == after_whnf
            && major != major0
            && whnf_trace.is_some()
            && reduct::fully_ruled(&whnf_trace)
        {
            MajorStep { idx: rec.major_idx(), to: major, trace: whnf_trace }
        } else {
            MajorStep { idx: rec.major_idx(), to: major0, trace: None }
        };
        Some((reduct, step))
    }

    pub fn reduce_quot(&mut self, c_name: NamePtr<'t>, args: &[ExprPtr<'t>]) -> Option<ExprPtr<'t>> {
        if !matches!(self.env.get_declar(&c_name), Some(Declar::Quot {..})) {
            return None
        }
        let (qmk, rest_idx) = if c_name == self.ctx.export_file.name_cache.quot_lift? {
            let qmk = args.get(5).copied()?;
            (self.whnf(qmk), 6)
        } else if c_name == self.ctx.export_file.name_cache.quot_ind? {
            let qmk = args.get(4).copied()?;
            (self.whnf(qmk), 5)
        } else {
            return None
        };
        {
            let (qmk_const, qmk_args) = self.ctx.unfold_apps(qmk);
            match self.ctx.read_expr(qmk_const) {
                Const { name, .. } if name == self.ctx.export_file.name_cache.quot_mk? && qmk_args.len() == 3 => (),
                _ => return None,
            };
        }
        let f = args.get(3).copied()?;
        let appd = match self.ctx.read_expr(qmk) {
            App { arg, .. } => self.ctx.mk_app(f, arg),
            _ => panic!("Quot iota"),
        };
        Some(self.ctx.foldl_apps(appd, args.iter().copied().skip(rest_idx)))
    }

    // We only need the name and reducibility from this.
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, ReducibilityHint)> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Definition { info, hint, .. }) = self.env.get_declar(&name) {
                return Some((info.name, *hint))
            } else if let Some(Declar::Theorem { info, .. }) = self.env.get_declar(&name) {
                return Some((info.name, ReducibilityHint::Opaque))
            }
        }
        None
    }

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    ///
    /// Returns the certificate too: the unfolding itself is `Certifier::delta`
    /// (the backend has a defining equation for the head constant and folds
    /// congruence over the argument spine), composed with whatever the cheap
    /// reduction of the result needed.
    fn delta(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, DefEq<'t, 'p>, TracePtr<'t, Cert<'t, 'p>>) {
        let unfolded = self.unfold_def(e).unwrap();
        crate::certify::bump_certified();
        let step = Some(self.certifier.delta(self.ctx, e, unfolded));
        let (r, rest_trace) = self.whnf_no_unfolding_reduce(unfolded, true);
        let rest = self.certify_reduct(unfolded, r, &rest_trace);
        let cert = self.seq(e, r, step, rest);
        let trace = reduct::then(reduct::one(Rule::Delta, e, unfolded), rest_trace);
        (r, cert, trace)
    }

    /// Try to unfold the base `Const` and re-fold applications, but don't
    /// do any further reduction.
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let (fun, args) = self.ctx.unfold_apps(e);
        let (name, levels) = self.ctx.try_const_info(fun)?;
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            crate::stepcount::bump(crate::stepcount::Kind::Delta);
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            Some(self.ctx.foldl_apps(def_val, args.into_iter()))
        } else {
            None
        }
    }

    fn def_eq_sort(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) =>
                if self.ctx.eq_antisymm(l, r) {
                    // Universe-level equality is discharged by the backend's
                    // `sort` rule; the level algebra itself stays out of the
                    // kernel (levels are monomorphised by the translator).
                    crate::certify::bump_certified();
                    let c = self.certifier.sort(self.ctx, x, y);
                    Some(Some(c))
                } else {
                    Some(None)
                },
            _ => None,
        }
    }

    /// The outer `Option` is "did the quick check settle it at all"; the inner
    /// `DefEq` is the verdict-with-evidence. Collapsing the two would lose the
    /// distinction between "cheaply shown unequal" and "no cheap answer".
    fn def_eq_quick_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        if x == y {
            crate::stepcount::bump(crate::stepcount::Kind::DefEqCacheHit);
            // Pointer equality on a hash-consed representation *is* alpha
            // equality, so this one needs no admit: reflexivity justifies it.
            crate::certify::bump_certified();
            let c = self.certifier.refl(self.ctx, x);
            return Some(Some(c))
        }
        if self.tc_cache.eq_cache.check_uf_eq(x, y) {
            crate::stepcount::bump(crate::stepcount::Kind::DefEqCacheHit);
            return Some(self.recall_eq(x, y))
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
    }

    /// The certificate for a definitional-equality *cache hit*.
    ///
    /// `x` and `y` are in one union-find class, which means a chain of earlier
    /// `def_eq` verdicts connects them. Each of those verdicts left its
    /// certificate on the edge it created, so the chain composes with `trans`
    /// and `symm` into a derivation of `x ≡ y` — the thing the caller is asking
    /// about, and nothing weaker.
    ///
    /// It is composed against `x` and `y` explicitly. A cached certificate is
    /// exactly the situation the cardinal rule is about: the temptation is to
    /// hand back what the cache holds because the *terms* matched, when what the
    /// cache holds is a proof of some other equation on the path. Every `trans`
    /// and `symm` below is told which pair it is concluding about and checks its
    /// own result, and a path that does not join up yields `Admit::Cache` — the
    /// answer this whole method exists to stop giving — rather than a claim.
    fn recall_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        let Some(hops) = self.tc_cache.eq_cache.explain(x, y) else {
            if let Some(cert) = self.recall_reduction_eq(x, y) {
                return cert
            }
            return self.admit(x, y, Admit::Cache)
        };
        let mut acc: DefEq<'t, 'p> = None;
        let mut cursor = x;
        for hop in hops {
            if hop.from != cursor {
                return self.admit(x, y, Admit::Cache)
            }
            // `Hop::reversed` says the edge's certificate reads the other way
            // round from the direction the path walks it.
            let leg = if hop.reversed {
                self.symm_leg(hop.from, hop.to, Some(hop.cert))
            } else {
                Some(hop.cert)
            };
            acc = self.seq(x, hop.to, acc, leg);
            cursor = hop.to;
        }
        if cursor != y || acc.is_none() {
            return self.admit(x, y, Admit::Cache)
        }
        acc
    }

    /// Recover an equality-cache decision from the exact reduction evidence
    /// that established it, when the union edge itself could not retain that
    /// evidence.
    ///
    /// Conditional certificates are deliberately not copied into the global
    /// proof forest: its key is only an expression pair and cannot account for
    /// their local premises. The lazy-delta recipe table is different. It
    /// retains the reduction trace, not a theorem, and that trace names both
    /// endpoints. Replaying it here is therefore licensed only when its key is
    /// the requested pair, the trace names exactly those endpoints, and
    /// every non-structural step is behind the backend's authoritative Mini
    /// readiness gate. No reduction or equality check is repeated, and an
    /// unexplained union path still fails closed as `eq_cache`.
    fn recall_reduction_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        let trace = self.tc_cache.eq_reduct_cache.get(&(x, y))?.clone();
        if !trace.as_ref().is_some_and(|t| t.from == x && t.to == y) {
            return None
        }
        if !self.authoritative_reduction_ready(&trace) {
            return None
        }
        Some(self.certify_reduct(x, y, &trace))
    }

    fn failure_cache_contains(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let pr = if x.get_hash() <= y.get_hash() { (x, y) } else { (y, x) };
        self.tc_cache.failure_cache.contains(&pr)
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        let pr = if x.get_hash() <= y.get_hash() { (x, y) } else { (y, x) };
        self.tc_cache.failure_cache.insert(pr);
    }

    fn try_eq_const_app(
        &mut self,
        x: ExprPtr<'t>,
        x_defname: NamePtr<'t>,
        x_hint: ReducibilityHint,
        y: ExprPtr<'t>,
        y_defname: NamePtr<'t>,
        y_hint: ReducibilityHint,
    ) -> Option<DefEq<'t, 'p>> {
        if x_defname != y_defname {
            return None
        }
        if !matches!((x_hint, y_hint), (ReducibilityHint::Regular(..), ReducibilityHint::Regular(..))) {
            return None
        }
        if x_hint != y_hint {
            return None
        }
        if self.failure_cache_contains(x, y) {
            return None
        }

        match self.ctx.read_expr_pair(x, y) {
            (App { .. }, App { .. }) if (x_defname == y_defname) => {
                let (l_fun, l_args) = self.ctx.unfold_apps(x);
                let (r_fun, r_args) = self.ctx.unfold_apps(y);
                match self.ctx.read_expr_pair(l_fun, r_fun) {
                    (Const { levels: l_levels, .. }, Const { levels: r_levels, .. }) => {
                        // Same conditions, same short-circuit order as upstream;
                        // the only difference is that the per-argument
                        // certificates are kept so the conclusion can be a real
                        // congruence instead of an admit.
                        let mut arg_certs = Vec::with_capacity(l_args.len());
                        let congruent = l_args.len() == r_args.len()
                            && !self.failure_cache_contains(x, y)
                            && l_args.iter().copied().zip(r_args.iter().copied()).all(|(x, y)| {
                                match self.def_eq(x, y) {
                                    Some(c) => {
                                        arg_certs.push(c);
                                        true
                                    }
                                    None => false,
                                }
                            })
                            && self.ctx.eq_antisymm_many(l_levels, r_levels);
                        if congruent {
                            // The heads are the same constant at pointwise-equal
                            // levels, which is exactly `const_eq`; fold
                            // `app_cong` over the spine as `def_eq_app` does.
                            crate::certify::bump_certified();
                            let mut c = self.certifier.const_eq(self.ctx, l_fun, r_fun);
                            // As in `def_eq_app`: each `app_cong` is handed the
                            // two partial applications it concludes about, built
                            // up one argument at a time, so the last pair is
                            // `(x, y)` and every step can check itself.
                            let (mut lhs, mut rhs) = (l_fun, r_fun);
                            for ((a, xx), yy) in arg_certs.into_iter().zip(l_args).zip(r_args) {
                                lhs = self.ctx.mk_app(lhs, xx);
                                rhs = self.ctx.mk_app(rhs, yy);
                                crate::certify::bump_certified();
                                c = self.certifier.app_cong(self.ctx, lhs, rhs, c, a);
                            }
                            Some(Some(c))
                        } else {
                            self.failure_cache_insert(x, y);
                            None
                        }
                    }
                    _ => panic!(),
                }
            }
            _ => None,
        }
    }

    fn try_unfold_proj_app(
        &mut self,
        e: ExprPtr<'t>,
    ) -> Option<(ExprPtr<'t>, DefEq<'t, 'p>, TracePtr<'t, Cert<'t, 'p>>)> {
        if let Proj { .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            let (eprime, trace) = self.whnf_no_unfolding_reduce(e, false);
            if eprime != e {
                let cert = self.certify_reduct(e, eprime, &trace);
                return Some((eprime, cert, trace))
            }
        }
        None
    }

    /// The outer `Option` is "did this settle the question"; the inner `DefEq`
    /// is the verdict with its evidence, about `x` and `y` as given.
    fn delta_try_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DefEq<'t, 'p>> {
        if let Some(short) = self.def_eq_nat(x, y) {
            return Some(short)
        }
        if (!self.ctx.has_fvars(x) && !self.ctx.has_fvars(y)) || self.ctx.eager_mode {
            if let Some(xprime) = self.try_reduce_nat(x) {
                // `x ≡ x'` by native arithmetic, then `x' ≡ y` by recursion.
                let step = self.admit(x, xprime, Admit::NatRed);
                let rest = self.def_eq(xprime, y);
                return Some(match rest {
                    None => None,
                    // `step : x ≡ x'`, `c : x' ≡ y`.
                    Some(c) => self.seq(x, y, step, Some(c)),
                })
            } else if let Some(yprime) = self.try_reduce_nat(y) {
                let step = self.admit(y, yprime, Admit::NatRed);
                let rest = self.def_eq(x, yprime);
                return Some(match rest {
                    None => None,
                    // `x ≡ y'` composed with `y' ≡ y`, the reduction reversed.
                    Some(c) => {
                        let back = self.symm_leg(yprime, y, step);
                        self.seq(x, y, Some(c), back)
                    }
                })
            }
        }
        None
    }

    /// If `x` and/or `y` are definitions that need to be unfolded, try to lazily unfold
    /// the "higher" definition to bring it closer to the lower one. Also try to efficiently
    /// check for congruence if `x` and `y` apply the same definitions.
    ///
    /// After each reduction, check whether we can show definitional equality without having
    /// to continue unfolding.
    fn lazy_delta_step(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> DeltaResult<'t, Cert<'t, 'p>> {
        // `x_leg` justifies `x₀ ≡ x` and `y_leg` justifies `y₀ ≡ y` for the
        // arguments this was called with, so that whatever is concluded about
        // the unfolded pair can be lifted back to the original one.
        //
        // `x₀`/`y₀` are held onto for that reason: every `trans` built below
        // concludes about the *original* left endpoint and the newly reached
        // one, and the rule is handed exactly that pair. `x`/`y` move as the
        // unfolding proceeds, so they cannot stand in for it.
        let (x0, y0) = (x, y);
        let (mut x_leg, mut y_leg): (DefEq<'t, 'p>, DefEq<'t, 'p>) = (None, None);
        let (mut x_trace, mut y_trace): (TracePtr<'t, Cert<'t, 'p>>, TracePtr<'t, Cert<'t, 'p>>) =
            (None, None);
        loop {
            if let Some(mid) = self.delta_try_nat(x, y) {
                return FoundEqResult(self.compose_legs(x0, y, y0, mid, x_leg, y_leg))
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted { x, y, x_leg, y_leg },
                (Some(..), None) =>
                    if let Some((yprime, step, trace)) = self.try_unfold_proj_app(y) {
                        y_leg = self.seq(y0, yprime, y_leg, step);
                        y_trace = reduct::then(y_trace, trace);
                        y = yprime;
                    } else {
                        let (xprime, step, trace) = self.delta(x);
                        x_leg = self.seq(x0, xprime, x_leg, step);
                        x_trace = reduct::then(x_trace, trace);
                        x = xprime;
                    },
                (None, Some(..)) =>
                    if let Some((xprime, step, trace)) = self.try_unfold_proj_app(x) {
                        x_leg = self.seq(x0, xprime, x_leg, step);
                        x_trace = reduct::then(x_trace, trace);
                        x = xprime;
                    } else {
                        let (yprime, step, trace) = self.delta(y);
                        y_leg = self.seq(y0, yprime, y_leg, step);
                        y_trace = reduct::then(y_trace, trace);
                        y = yprime;
                    },
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(&r_hint) => {
                    let (yprime, step, trace) = self.delta(y);
                    y_leg = self.seq(y0, yprime, y_leg, step);
                    y_trace = reduct::then(y_trace, trace);
                    y = yprime;
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(&l_hint) => {
                    let (xprime, step, trace) = self.delta(x);
                    x_leg = self.seq(x0, xprime, x_leg, step);
                    x_trace = reduct::then(x_trace, trace);
                    x = xprime;
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(mid) = self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint) {
                        return FoundEqResult(self.compose_legs(x0, y, y0, mid, x_leg, y_leg))
                    } else {
                        let (xprime, x_step, x_step_trace) = self.delta(x);
                        let (yprime, y_step, y_step_trace) = self.delta(y);
                        x_leg = self.seq(x0, xprime, x_leg, x_step);
                        y_leg = self.seq(y0, yprime, y_leg, y_step);
                        x_trace = reduct::then(x_trace, x_step_trace);
                        y_trace = reduct::then(y_trace, y_step_trace);
                        x = xprime;
                        y = yprime;
                    }
                }
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                // Pointer equality after reducing only one side is an exact
                // reduction explanation for the original pair. Retain the
                // trace recipe, not the conditional certificate produced from
                // it, so a later union-find hit can ask the authoritative rules
                // again without importing or parking local assumptions.
                if x == y && y == y0 && y_trace.is_none() && x_trace.is_some() {
                    self.tc_cache.eq_reduct_cache.insert((x0, y0), x_trace.clone());
                } else if x == y && x == x0 && x_trace.is_none() && y_trace.is_some() {
                    self.tc_cache.eq_reduct_cache.insert((y0, x0), y_trace.clone());
                }
                return FoundEqResult(self.compose_legs(x0, y, y0, quick_result, x_leg, y_leg))
            }
        }
    }

    pub fn is_sort_zero(&mut self, e: ExprPtr<'t>) -> bool {
        let e = self.whnf(e);
        match self.ctx.read_expr(e) {
            Sort { level, .. } => self.ctx.read_level(level) == Level::Zero,
            _ => false,
        }
    }

    /// [`Self::is_sort_zero`], **with the reduction leg**, on the branch that
    /// says yes.
    ///
    /// The `Sort 0` the answer is about is generally not the expression handed
    /// in — it is what that expression weak-head reduces to — so a witness
    /// stated at `⟦Sort 0⟧` needs `⟦e⟧ = ⟦Sort 0⟧` to get there. That equality
    /// is what `is_sort_zero` computes and throws away. `None` in the leg means
    /// no step was taken (`e` already *is* `Sort 0`), the same convention the
    /// rest of the reduction plumbing uses; `None` for the whole result means
    /// the answer was no, which licenses nothing and so needs nothing.
    fn sort_zero_leg(&mut self, e: ExprPtr<'t>, at: PropAt) -> Option<(ExprPtr<'t>, DefEq<'t, 'p>)> {
        let (r, trace) = self.whnf_reduce(e);
        match self.ctx.read_expr(r) {
            Sort { level, .. } if at.is_zero(self.ctx, level) => {
                let leg = self.certify_reduct(e, r, &trace);
                Some((r, leg))
            }
            _ => None,
        }
    }

    /// `e : Sort 0`, and the inferred type. The evidence is discarded; see
    /// [`Self::proposition_witness`] for the caller that keeps it.
    pub fn is_proposition(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer_ty(e, InferOnly, Dropped::Predicate);
        (self.is_sort_zero(infd), infd)
    }

    /// `e : Sort 0`, **with the witness** `⟦e⟧ ∈ ⟦Sort 0⟧` — which is
    /// `⟦e⟧ ∈ U₀`, because that is what the interpretation makes of `Sort 0`.
    ///
    /// Nothing new is derived here. `infer` established `⟦e⟧ ∈ ⟦T⟧` on its way
    /// to `T`, and `Sort 0` is where `T` weak-head reduces to, so the witness is
    /// that certificate carried across one conversion. It used to be thrown
    /// away and then searched for again from scratch, two rules further on, by
    /// `TgBackend::derive_point_of_proof`.
    fn proposition_witness(&mut self, e: ExprPtr<'t>, at: PropAt) -> Option<Typing<'t, 'p>> {
        let Typed { ty: infd, cert } = self.infer(e, InferOnly);
        let (sort0, leg) = self.sort_zero_leg(infd, at)?;
        Some(match leg {
            // `infd` *is* the sort already: the certificate states the witness.
            None => cert,
            Some(eq) => self.certifier.ty_conv(self.ctx, e, infd, sort0, cert, &eq),
        })
    }

    /// `e` is a proof, and the type it proves. The evidence is discarded; see
    /// [`Self::proof_witness`].
    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer_ty(e, InferOnly, Dropped::Predicate);
        (self.is_proposition(infd).0, infd)
    }

    /// `e` is a **proof**, with both halves of what that means.
    ///
    /// The two are exactly the premises of Carneiro's Theorem 6.7 — the
    /// proposition is a truth value, and `e` is in it — and therefore exactly
    /// the two facts a proof-irrelevance derivation needs. Both come out of
    /// inference; neither is looked for.
    fn proof_witness(&mut self, e: ExprPtr<'t>, at: PropAt) -> Option<ProofOf<'t, 'p>> {
        let Typed { ty, cert: mem } = self.infer(e, InferOnly);
        let prop = self.proposition_witness(ty, at)?;
        Some(Proof { ty, mem, prop })
    }

    /// **Proof irrelevance**, with its premises threaded rather than rebuilt.
    ///
    /// The rule needs three things and the checker has all three in hand: the
    /// two propositions are definitionally equal (`def_eq`'s certificate), and
    /// each side is a proof of its own ([`Self::proof_witness`]). Handing them
    /// over is the whole of the change: the backend used to be told only
    /// "somehow, these are equal", and its rescue path then went looking for
    /// the two memberships that had just been established and dropped.
    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        let l = self.proof_witness(x, PropAt::Params)?;
        let r = self.proof_witness(y, PropAt::Params)?;
        let ty_eq = self.def_eq(l.ty, r.ty)?;
        crate::stepcount::bump(crate::stepcount::Kind::ProofIrrel);
        crate::certify::bump_certified();
        let c = self.certifier.proof_irrel(self.ctx, x, y, l.ty, r.ty, l.mem, l.prop, r.mem, r.prop, &ty_eq);
        Some(c)
    }

    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        self.try_eta_expansion_aux(x, y).or_else(|| self.try_eta_expansion_aux(y, x))
    }

    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        if let Lambda { .. } = self.ctx.read_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly, Dropped::DefEqSide);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.read_expr(y_ty) {
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y, v0);
                let new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
                // The recursive comparison is *half the conclusion*: it settles
                // `x ≡ λz. y z`, and what is left is the genuine eta step
                // `λz. y z ≡ y`. It used to be established and dropped, so the
                // rule below was asked for the whole of `x ≡ y` with nothing to
                // build it from. It is handed over instead — and composed
                // inside the rule rather than by a `trans` out here, so that a
                // backend which cannot yet do eta reports one gap rather than
                // one gap and a transitivity over it.
                let expanded = self.def_eq(x, new_lambda)?;
                crate::stepcount::bump(crate::stepcount::Kind::Eta);
                // Eta is a real backend rule, not an admit: `λz. y z ≡ y`.
                crate::certify::bump_certified();
                let c = self.certifier.eta(self.ctx, x, y, new_lambda, expanded);
                return Some(c)
            }
        }
        None
    }
}
