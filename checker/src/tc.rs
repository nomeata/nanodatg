use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::level::Level;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor, 
    nat_xor, nat_shr, nat_shl, ExportFile, ExprPtr, LevelPtr, 
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr
};
use crate::certify::{Admit, Backend, Cert, DefEq};
use kernel::Certifier;
use std::error::Error;
use num_traits::pow::Pow;

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

/// Whether a weak-head reduction should build a certificate as it goes.
///
/// Most `whnf` calls come from type inference, which wants the reduct and
/// nothing else. Building evidence there would be wasted work, and — worse —
/// would tally gaps in the coverage report against reduction steps that no
/// definitional-equality conclusion depends on, so the report would stop
/// measuring what it claims to. Only the definitional-equality machinery asks
/// for [`Evidence::Wanted`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Evidence {
    /// Ask the backend at every reduction step and return the composed result.
    Wanted,
    /// Reduce only; the certificate comes back as `None`.
    Skip,
}

impl Evidence {
    fn wanted(self) -> bool { matches!(self, Evidence::Wanted) }
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
    pub(crate) tc_cache: TcCache<'t, Cert<'t, 'p>>,
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
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()),
            Inductive(..) => self.check_inductive_declar(d),
            Quot { .. } => self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)),
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                }),
            Constructor(ctor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                }
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self) {
        for declar in self.declars.values() {
            self.check_declar(declar);
        }
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    /// checkers.
    fn check_all_declars_par(&self, num_threads: usize) {
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
                                self.check_declar(declar);
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
    pub fn check_all_declars(&self) {
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads)
        } else {
            self.check_all_declars_serial()
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        assert_eq!(dag.dbj_level_counter, 0);
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info, certifier: crate::certify::new_backend(env) }
    }

    /// Conduct the preliminary checks done on all declarations; a declaration
    /// must not contain duplicate universe parameters, mut not have free variables,
    /// and must have an ascribed type that is actually a type (`infer declaration.type` must
    /// be a sort).
    pub(crate) fn check_declar_info(&mut self, d: &Declar<'t>) -> Result<(), Box<dyn Error>> {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams));
        assert!(!self.ctx.has_fvars(info.ty));
        let inferred_type = self.infer(info.ty, Check);
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
        let infd = self.infer(e, Check);
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

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t> {
        let whnfd = self.infer_then_whnf(e, flag);
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
            let (x_type, y_type) = (self.infer(x, InferOnly), self.infer(y, InferOnly));
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
        let x_ty = self.infer_then_whnf(x, InferOnly);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&name, false)?;
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer(y, InferOnly);
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

    fn reduce_proj(&mut self, idx: usize, structure: ExprPtr<'t>, cheap: bool) -> Option<ExprPtr<'t>> {
        let mut structure = if cheap { self.whnf_no_unfolding_cheap_proj(structure) } else { self.whnf(structure) };
        if let StringLit { ptr, .. } = self.ctx.read_expr(structure) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                structure = s;
            }
        }
        let (_, name, _, args) = self.ctx.unfold_const_apps(structure)?;
        let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;
        let i = (*num_params as usize) + idx;
        Some(args.get(i).copied().unwrap())
    }

    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let ty = self.infer(e, flag);
        self.whnf(ty)
    }

    #[allow(non_snake_case)]
    fn infer_proj(&mut self, _ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let structure_ty = self.infer(structure, flag);
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

    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(cached) = self.tc_cache.infer_cache_check.get(&e).copied() {
            return cached
        }
        if flag == InferFlag::InferOnly {
            if let Some(cached) = self.tc_cache.infer_cache_no_check.get(&e).copied() {
                return cached
            }
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => binder_type,
            Var { .. } => panic!("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(binder_type, val, body, flag),
            Const { name, levels, .. } => self.infer_const(name, levels, flag),
            Proj { ty_name, idx, structure, .. } => self.infer_proj(ty_name, idx, structure, flag),
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                self.ctx.nat_type().unwrap()
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                self.ctx.string_type().unwrap()
            }
        };
        match flag {
            InferFlag::InferOnly => {
                self.tc_cache.infer_cache_no_check.insert(e, r);
            }
            InferFlag::Check => {
                self.tc_cache.infer_cache_check.insert(e, r);
            }
        }
        r
    }

    fn infer_sort(&mut self, l: LevelPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))
        }
        let out = self.ctx.succ(l);
        self.ctx.mk_sort(out)
    }

    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let (mut fun, mut args) = self.ctx.unfold_apps_stack(e);
        let mut ctx = Vec::new();
        fun = self.infer(fun, flag);
        while !args.is_empty() {
            match self.ctx.read_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    if flag == Check {
                        let arg_type = self.infer(arg, flag);
                        let binder_type = self.ctx.inst(binder_type, ctx.as_slice());
                        let outer_scope_eager_setting = self.ctx.eager_mode;
                        if self.ctx.is_eager_reduce_app(arg) {
                            self.ctx.eager_mode = true;
                        }
                        // `arg_type` and `binder_type` get swapped here to accommodate the 
                        // eager reduction branch in `def_eq` being focused on reducing the lhs.
                        self.assert_def_eq(binder_type, arg_type);
                        // replace the outer scope's setting before next iteration
                        self.ctx.eager_mode = outer_scope_eager_setting;
                    }
                    ctx.push(arg);
                    fun = body;
                }
                _ => {
                    let as_pi = self.ctx.inst(fun, ctx.as_slice());
                    let as_pi = self.ensure_pi(as_pi);
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
        self.ctx.inst(fun, ctx.as_slice())
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

    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut locals = Vec::new();
        let start_pos = self.ctx.dbj_level_counter;
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            if let Check = flag {
                self.infer_sort_of(binder_type, flag);
            }

            let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
            locals.push(local);
            e = body;
        }

        let instd = self.ctx.inst(e, locals.as_slice());
        let infd = self.infer(instd, flag);
        let mut abstrd = self.ctx.abstr_levels(infd, start_pos);
        while let Some(local) = locals.pop() {
            match self.ctx.read_expr(local) {
                Local { binder_name, binder_style, binder_type, .. } => {
                    self.ctx.replace_dbj_level(local);
                    let t = self.ctx.abstr_levels(binder_type, start_pos);
                    abstrd = self.ctx.mk_pi(binder_name, binder_style, t, abstrd);
                }
                _ => panic!(),
            }
        }
        abstrd
    }

    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut universes = Vec::new();
        let mut locals = Vec::new();
        let c0 = self.ctx.dbj_level_counter;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            let dom_univ = self.infer_sort_of(binder_type, flag);
            universes.push(dom_univ);
            locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, binder_type));
            e = body;
        }
        let instd = self.ctx.inst(e, locals.as_slice());
        let mut infd = self.infer_sort_of(instd, flag);
        while let (Some(universe), Some(local)) = (universes.pop(), locals.pop()) {
            infd = self.ctx.imax(universe, infd);
            self.ctx.replace_dbj_level(local);
        }
        assert_eq!(c0, self.ctx.dbj_level_counter);
        self.ctx.mk_sort(infd)
    }

    fn infer_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> ExprPtr<'t> {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag);
            let val_ty = self.infer(val, flag);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq(val_ty, binder_type);
        }
        let body = self.ctx.inst(body, &[val]);
        self.infer(body, flag)
    }
    
    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer(e, InferOnly);
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
    // 28 callers change. Internally each is a thin wrapper over a `*_with_cert`
    // variant which additionally produces a certificate for `e ≡ whnf(e)`,
    // built out of the actual rules applied: `Certifier::beta` for a beta
    // contraction, `zeta` for a let, `delta` for a definition unfolding, and an
    // `Admit` for the rules the backend has no method for yet (iota, quotient,
    // projection, native arithmetic). `def_eq` composes those certificates onto
    // its result instead of admitting an opaque `Admit::Whnf`.
    //
    // Certificates are built **on demand** ([`Evidence`]): the majority of whnf
    // calls come from type inference, which needs the reduct and nothing else.
    // Asking the backend there would tally gaps against steps that no
    // definitional-equality conclusion rests on, and the coverage report would
    // then measure something other than what it says it measures.
    //
    // Convention for the `DefEq` returned by these functions: `None` means *no
    // step was taken*, so the reduct is the input and reflexivity applies; no
    // certificate is built for that case. It never means "not equal" — a
    // reduction is always justified.
    // ─────────────────────────────────────────────────────────────────────────

    /// Chain two reduction certificates. `None` is the identity (see above), so
    /// composing with it builds no `trans`.
    fn seq(&mut self, acc: DefEq<'t, 'p>, next: DefEq<'t, 'p>) -> DefEq<'t, 'p> {
        match (acc, next) {
            (None, c) | (c, None) => c,
            (Some(a), Some(b)) => {
                crate::certify::bump_certified();
                Some(self.certifier.trans(self.ctx, a, b))
            }
        }
    }

    /// Reverse a reduction leg. `None` (reflexivity) is its own inverse.
    fn symm_leg(&mut self, leg: DefEq<'t, 'p>) -> DefEq<'t, 'p> {
        leg.map(|c| {
            crate::certify::bump_certified();
            self.certifier.symm(self.ctx, c)
        })
    }

    /// Compose reduction legs onto a verdict about a *reduced* pair, so the
    /// certificate justifies the pair the caller actually asked about:
    /// `x ≡ x'`, `x' ≡ y'`, then `y' ≡ y`.
    fn compose_legs(&mut self, mid: DefEq<'t, 'p>, x_leg: DefEq<'t, 'p>, y_leg: DefEq<'t, 'p>) -> DefEq<'t, 'p> {
        let mid = mid?;
        let c = self.seq(x_leg, Some(mid));
        let back = self.symm_leg(y_leg);
        self.seq(c, back)
    }

    /// Remember why `e` reduces to `r`, so that a later reduct-cache hit can
    /// still recover the evidence.
    fn record_reduction(&mut self, e: ExprPtr<'t>, r: ExprPtr<'t>, cert: DefEq<'t, 'p>) {
        if e != r {
            if let Some(c) = cert {
                self.tc_cache.reduction_certs.insert((e, r), c);
            }
        }
    }

    /// The recorded justification for `e ⟶* r`.
    ///
    /// `None` when there is nothing to justify (`e == r`). The `Admit::Whnf`
    /// fallback covers the one remaining case: the reduct was memoised by an
    /// earlier call that did not want evidence, so no certificate was built and
    /// re-deriving one is not possible without redoing the reduction — which
    /// could return a *different* reduct (the cheap-projection variant does not
    /// reduce as far), and so would change what the checker does.
    fn recall_reduction(&mut self, e: ExprPtr<'t>, r: ExprPtr<'t>) -> DefEq<'t, 'p> {
        if e == r {
            return None
        }
        if let Some(c) = self.tc_cache.reduction_certs.get(&(e, r)).cloned() {
            return Some(c)
        }
        self.admit(e, r, Admit::Whnf)
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_with_cert(e, Evidence::Skip).0 }

    fn whnf_with_cert(&mut self, e: ExprPtr<'t>, ev: Evidence) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return (e, None)
        }
        if let Some(cached) = self.tc_cache.whnf_cache.get(&e).copied() {
            let cert = if ev.wanted() { self.recall_reduction(e, cached) } else { None };
            return (cached, cert)
        }
        let mut cursor = e;
        // `acc` justifies `e ≡ cursor` throughout the loop.
        let mut acc: DefEq<'t, 'p> = None;
        loop {
            let (whnfd, step) = self.whnf_no_unfolding_aux_with_cert(cursor, false, ev);
            acc = self.seq(acc, step);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                if ev.wanted() {
                    let step = self.admit(whnfd, reduce_nat_ok, Admit::NatRed);
                    acc = self.seq(acc, step);
                }
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                if ev.wanted() {
                    // `delta` wants the whole application `c a₁ … aₙ` together
                    // with `value a₁ … aₙ`; that is exactly the pair
                    // `unfold_def` relates, and the backend folds congruence
                    // over the spine itself.
                    crate::certify::bump_certified();
                    let step = Some(self.certifier.delta(self.ctx, whnfd, next_term));
                    acc = self.seq(acc, step);
                }
                cursor = next_term;
            } else {
                self.tc_cache.whnf_cache.insert(e, whnfd);
                self.record_reduction(e, whnfd, acc.clone());
                return (whnfd, acc)
            }
        }
    }

    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.whnf_no_unfolding_aux_with_cert(e, true, Evidence::Skip).0
    }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.whnf_no_unfolding_aux_with_cert(e, false, Evidence::Skip).0
    }

    fn whnf_no_unfolding_aux_with_cert(
        &mut self,
        e: ExprPtr<'t>,
        cheap_proj: bool,
        ev: Evidence,
    ) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        if let Some(cached) = self.tc_cache.whnf_no_unfolding_cache.get(&e).copied() {
            let cert = if ev.wanted() { self.recall_reduction(e, cached) } else { None };
            return (cached, cert)
        }
        let (e_fun, args) = self.ctx.unfold_apps(e);
        let (should_cache, eprime, cert) = match self.ctx.read_expr(e_fun) {
            Proj { idx, structure, .. } =>
                if let Some(field) = self.reduce_proj(idx, structure, cheap_proj) {
                    crate::stepcount::bump(crate::stepcount::Kind::Proj);
                    let e1 = self.ctx.foldl_apps(field, args.into_iter());
                    // No dedicated backend rule for projection reduction yet.
                    let step = if ev.wanted() { self.admit(e, e1, Admit::ProjRed) } else { None };
                    let (r, rest) = self.whnf_no_unfolding_aux_with_cert(e1, cheap_proj, ev);
                    let c = self.seq(step, rest);
                    (true, r, c)
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
                let cert = if s == e || !ev.wanted() {
                    None
                } else {
                    crate::certify::bump_certified();
                    Some(self.certifier.sort(self.ctx, e, s))
                };
                (false, s, cert)
            }
            Lambda { .. } if !args.is_empty() => {
                let (mut b, mut n_args) = (e_fun, 0usize);
                while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.read_expr(b), &args[n_args..]) {
                    n_args += 1;
                    b = body;
                    crate::stepcount::bump(crate::stepcount::Kind::Beta);
                }
                let b = self.ctx.inst(b, &args[..n_args]);
                let e1 = self.ctx.foldl_apps(b, args.into_iter().skip(n_args));
                // `n_args` beta contractions happen at once, so the backend is
                // asked for the composite `(λ…λ. b) a₁ … aₙ ≡ b[a⃗]`.
                let step = if ev.wanted() {
                    crate::certify::bump_certified();
                    Some(self.certifier.beta(self.ctx, e, e1))
                } else {
                    None
                };
                let (r, rest) = self.whnf_no_unfolding_aux_with_cert(e1, cheap_proj, ev);
                let c = self.seq(step, rest);
                (true, r, c)
            }
            Lambda { .. } => {
                debug_assert!(args.is_empty());
                (false, self.ctx.foldl_apps(e_fun, args.into_iter()), None)
            }
            Let { val, body, .. } => {
                crate::stepcount::bump(crate::stepcount::Kind::Zeta);
                let b = self.ctx.inst(body, &[val]);
                let e1 = self.ctx.foldl_apps(b, args.into_iter());
                let step = if ev.wanted() {
                    crate::certify::bump_certified();
                    Some(self.certifier.zeta(self.ctx, e, e1))
                } else {
                    None
                };
                let (r, rest) = self.whnf_no_unfolding_aux_with_cert(e1, cheap_proj, ev);
                let c = self.seq(step, rest);
                (true, r, c)
            }
            Const { name, levels, .. } =>
                if let Some(reduced) = self.reduce_quot(name, &args) {
                    crate::stepcount::bump(crate::stepcount::Kind::Quot);
                    let step = if ev.wanted() { self.admit(e, reduced, Admit::Quot) } else { None };
                    let (r, rest) = self.whnf_no_unfolding_aux_with_cert(reduced, cheap_proj, ev);
                    let c = self.seq(step, rest);
                    (true, r, c)
                } else if let Some(reduced) = self.reduce_rec(name, levels, &args) {
                    crate::stepcount::bump(crate::stepcount::Kind::Iota);
                    let step = if ev.wanted() { self.admit(e, reduced, Admit::Iota) } else { None };
                    let (r, rest) = self.whnf_no_unfolding_aux_with_cert(reduced, cheap_proj, ev);
                    let c = self.seq(step, rest);
                    (true, r, c)
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
            self.tc_cache.whnf_no_unfolding_cache.insert(e, eprime);
            // Recorded alongside the reduct, so that the cache-hit path above
            // can find the matching evidence on a later certified call.
            self.record_reduction(e, eprime, cert.clone());
        }
        (eprime, cert)
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
    /// `pi_cong` rules in the backend are the ones that will discharge the
    /// generalisation; today the whole chain is admitted as `BINDER`.
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
        let mut frames: Vec<(bool, ExprPtr<'t>, ExprPtr<'t>, Cert<'t, 'p>)> = Vec::new();
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
                frames.push((is_pi, x, y, dom_cert));
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
        // resulting certificate valid absolutely rather than relative to a local
        // context — and hence what keeps the equality cache globally sound.
        Some(body.map(|mut c| {
            while let Some((is_pi, fx, fy, dom)) = frames.pop() {
                crate::certify::bump_certified();
                c = if is_pi {
                    self.certifier.pi_cong(self.ctx, fx, fy, dom, c)
                } else {
                    self.certifier.lam_cong(self.ctx, fx, fy, dom, c)
                };
            }
            c
        }))
    }

    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.ctx.read_expr_pair(x, y) {
            (Proj { idx: idx_l, structure: structure_l, .. }, Proj { idx: idx_r, structure: structure_r, .. }) =>
                if idx_l == idx_r && self.def_eq(structure_l, structure_r).is_some() {
                    self.admit(x, y, Admit::Proj)
                } else {
                    None
                },
            _ => None,
        }
    }

    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.ctx.read_expr_pair(x, y) {
            (Local { id: x_id, binder_type: tx, .. }, Local { id: y_id, binder_type: ty, .. }) =>
                if x_id == y_id && self.def_eq(tx, ty).is_some() {
                    self.admit(x, y, Admit::Local)
                } else {
                    None
                },
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
        for (xx, yy) in args1.into_iter().zip(args2) {
            match self.def_eq(xx, yy) {
                Some(c) => arg_certs.push(c),
                None => return None,
            }
        }

        let Some(head) = self.def_eq(f1, f2) else { return None };

        // Fold `app_cong` left-to-right over the spine, mirroring how the
        // application was built: `f a b` is `((f a) b)`.
        let mut c = head;
        for a in arg_certs {
            crate::certify::bump_certified();
            c = self.certifier.app_cong(self.ctx, c, a);
        }
        Some(c)
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) { assert!(self.def_eq(u, v).is_some()) }

    /// Convenience: admit an equality the checker believes but cannot yet
    /// justify. Each call site names itself via one of `certify::admits`, so
    /// the remaining holes are enumerable. See `certify.rs`.
    pub(crate) fn admit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, site: Admit) -> DefEq<'t, 'p> {
        crate::certify::bump_admit(site);
        Some(self.certifier.admit(self.ctx, x, y, site.name()))
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
        let (x_n, x_leg) = self.whnf_no_unfolding_aux_with_cert(x, true, Evidence::Wanted);
        let (y_n, y_leg) = self.whnf_no_unfolding_aux_with_cert(y, true, Evidence::Wanted);

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                return self.admit(x, y, Admit::BoolTrue)
            }
        }

        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            return easy
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
                            let (x_n, x_step) = self.whnf_no_unfolding_aux_with_cert(xn0, false, Evidence::Wanted);
                            let (y_n, y_step) = self.whnf_no_unfolding_aux_with_cert(yn0, false, Evidence::Wanted);
                            if x_n != xn0 || y_n != yn0 {
                                let inner = self.def_eq(x_n, y_n);
                                self.compose_legs(inner, x_step, y_step)
                            } else {
                                self.def_eq_app(x_n, y_n)
                                    .or_else(|| self.try_eta_expansion(x_n, y_n))
                                    .or_else(|| self.try_eta_struct(x_n, y_n))
                                    .or_else(|| self.try_string_lit_expansion(x_n, y_n))
                                    .or_else(|| self.def_eq_unit(x_n, y_n))
                            }
                        });
                    self.compose_legs(mid, dx_leg, dy_leg)
                }
            }
        };
        // Compose the reduction legs back on, so the returned certificate
        // justifies `x ≡ y` rather than merely `x_n ≡ y_n`.
        let result = result.map(|mid| {
            let mut c = mid;
            if let Some(leg) = x_leg {
                crate::certify::bump_certified();
                c = self.certifier.trans(self.ctx, leg, c);
            }
            if let Some(leg) = y_leg {
                crate::certify::bump_certified();
                let back = self.certifier.symm(self.ctx, leg);
                c = self.certifier.trans(self.ctx, c, back);
            }
            c
        });

        if result.is_some() {
            // NOTE (milestone 3): this discards the certificate. A
            // proof-producing union-find — recording the justifying cert on each
            // union edge and reconstructing along the explain path — is what lets
            // the cache answer with evidence instead of `Admit::Cache`.
            self.tc_cache.eq_cache.union(x, y);
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
        let major_ty = self.infer_then_whnf(major, InferOnly);
        let f = self.ctx.unfold_apps_fun(major_ty);
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) if name == n => {
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                // This sometimes has free variables.
                let new_type = self.infer(new_ctor_app, InferOnly);
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
            let e_type = self.infer_then_whnf(e, InferOnly);
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } if name == ind_name => {
                    let e_sort = self.infer_then_whnf(e_type, InferOnly);
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
    
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major, rec).unwrap_or(major);
        let major = self.whnf(major);
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
        Some(self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx() + 1).copied()))
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
    fn delta(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, DefEq<'t, 'p>) {
        let unfolded = self.unfold_def(e).unwrap();
        crate::certify::bump_certified();
        let step = Some(self.certifier.delta(self.ctx, e, unfolded));
        let (r, rest) = self.whnf_no_unfolding_aux_with_cert(unfolded, true, Evidence::Wanted);
        let cert = self.seq(step, rest);
        (r, cert)
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
            return Some(self.admit(x, y, Admit::Cache))
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
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
                            for a in arg_certs {
                                crate::certify::bump_certified();
                                c = self.certifier.app_cong(self.ctx, c, a);
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

    fn try_unfold_proj_app(&mut self, e: ExprPtr<'t>) -> Option<(ExprPtr<'t>, DefEq<'t, 'p>)> {
        if let Proj { .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            let (eprime, cert) = self.whnf_no_unfolding_aux_with_cert(e, false, Evidence::Wanted);
            if eprime != e {
                return Some((eprime, cert))
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
                    Some(c) => self.seq(step, Some(c)),
                })
            } else if let Some(yprime) = self.try_reduce_nat(y) {
                let step = self.admit(y, yprime, Admit::NatRed);
                let rest = self.def_eq(x, yprime);
                return Some(match rest {
                    None => None,
                    // `x ≡ y'` composed with `y' ≡ y`, the reduction reversed.
                    Some(c) => {
                        let back = self.symm_leg(step);
                        self.seq(Some(c), back)
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
        let (mut x_leg, mut y_leg): (DefEq<'t, 'p>, DefEq<'t, 'p>) = (None, None);
        loop {
            if let Some(mid) = self.delta_try_nat(x, y) {
                return FoundEqResult(self.compose_legs(mid, x_leg, y_leg))
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted { x, y, x_leg, y_leg },
                (Some(..), None) =>
                    if let Some((yprime, step)) = self.try_unfold_proj_app(y) {
                        y = yprime;
                        y_leg = self.seq(y_leg, step);
                    } else {
                        let (xprime, step) = self.delta(x);
                        x = xprime;
                        x_leg = self.seq(x_leg, step);
                    },
                (None, Some(..)) =>
                    if let Some((xprime, step)) = self.try_unfold_proj_app(x) {
                        x = xprime;
                        x_leg = self.seq(x_leg, step);
                    } else {
                        let (yprime, step) = self.delta(y);
                        y = yprime;
                        y_leg = self.seq(y_leg, step);
                    },
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(&r_hint) => {
                    let (yprime, step) = self.delta(y);
                    y = yprime;
                    y_leg = self.seq(y_leg, step);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(&l_hint) => {
                    let (xprime, step) = self.delta(x);
                    x = xprime;
                    x_leg = self.seq(x_leg, step);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(mid) = self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint) {
                        return FoundEqResult(self.compose_legs(mid, x_leg, y_leg))
                    } else {
                        let (xprime, x_step) = self.delta(x);
                        let (yprime, y_step) = self.delta(y);
                        x = xprime;
                        y = yprime;
                        x_leg = self.seq(x_leg, x_step);
                        y_leg = self.seq(y_leg, y_step);
                    }
                }
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                return FoundEqResult(self.compose_legs(quick_result, x_leg, y_leg))
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
    pub fn is_proposition(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_sort_zero(infd), infd)
    }

    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_proposition(infd).0, infd)
    }

    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        match self.is_proof(x) {
            (false, _) => None,
            (true, l_type) => match self.is_proof(y) {
                (false, _) => None,
                (true, r_type) =>
                    if self.def_eq(l_type, r_type).is_some() {
                        crate::stepcount::bump(crate::stepcount::Kind::ProofIrrel);
                        self.admit(x, y, Admit::ProofIrrel)
                    } else {
                        None
                    },
            },
        }
    }

    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        self.try_eta_expansion_aux(x, y).or_else(|| self.try_eta_expansion_aux(y, x))
    }

    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DefEq<'t, 'p> {
        if let Lambda { .. } = self.ctx.read_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.read_expr(y_ty) {
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y, v0);
                let new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
                if self.def_eq(x, new_lambda).is_some() {
                    crate::stepcount::bump(crate::stepcount::Kind::Eta);
                    // Eta is a real backend rule, not an admit: `λz. y z ≡ y`.
                    crate::certify::bump_certified();
                    let c = self.certifier.eta(self.ctx, x, y);
                    return Some(c)
                }
                return None
            }
        }
        None
    }
}
