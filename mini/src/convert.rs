//! Export file → mini declarations, and the level pre-pass's schedule.
//!
//! # Interface
//!
//! [`load`] parses one `.ndjson` export with **`checker`'s own parser** —
//! `Config::try_from` is bypassed in favour of deserialising a `Config` from a
//! string, but everything downstream (`to_export_file`, the arena, the
//! `Declar` map) is upstream nanoda's, unmodified. It then walks the arena with
//! the `pub` `TcCtx::read_*` accessors and produces owned de Bruijn
//! [`Declaration`]s, plus the [`Instantiations`] schedule keyed by mini `Name`.
//!
//! Mirroring mini-lean's parser (`MiniKernel/Parser.lean`) exactly matters for
//! acceptance fidelity, so the same things are declined here:
//!
//! * nat literals above 10 (mini-lean's `parseExprNatLit` guard),
//! * unsafe / mutual / nested inductives (`parseInductInfo`),
//! * recursor declarations, which are *not* fed to the kernel: mini generates
//!   its own from the inductive declaration (`parseRecInfo` is a stub).
//!
//! Two things `checker`'s parser does that mini-lean's does not, both
//! harmless: it rejects `mdata` outright (mini-lean unwraps it — no tutorial
//! export contains one, or nanoda would already panic), and it keeps recursor
//! and constructor declarations, which this module uses for the audit of §2 and
//! then drops.
//!
//! **The inductive's own fields.** `parseInductInfo`'s three declines and the
//! parameter count come from `InductiveData::{num_params, all_ind_names,
//! is_nested}`, which `checker` exposes as accessors. Reading them rather than
//! inferring them is load-bearing, not tidiness: the arena's `bad/048` pairs a
//! degenerate `numParams: 0` recursor with a correct `numParams: 2`
//! constructor, so a checker that recovers the count from a neighbouring
//! declaration splits the telescope in the wrong place and **accepts an
//! ill-typed file**. Mini did, for one commit, before the accessors existed.
//!
//! `isUnsafe` is not among them, and does not need to be: `checker`'s parser
//! asserts `!is_unsafe` for every declaration kind, so an unsafe declaration
//! never reaches mini at all — it becomes a decline at the parser panic.

use crate::env::{Declaration, DefKind};
use crate::expr::{self, Expr, Level, Name, E};
use nanoda_lib::env::Declar;
use nanoda_lib::expr::Expr as CExpr;
use nanoda_lib::instantiations::{Inst, Instantiations};
use nanoda_lib::level::Level as CLevel;
use nanoda_lib::name::Name as CName;
use nanoda_lib::util::{Config, ExprPtr, LevelPtr, NamePtr, TcCtx};
use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;

/// What the corpus harness measures at step 1 of MINI-DESIGN.md §12, plus the
/// audit rows §3 and §11 pin.
#[derive(Default, Debug, Clone)]
pub struct Facts {
    /// Export-file declarations, before mini bundles constructors into their
    /// inductive and drops recursors.
    pub declars: usize,
    /// `natLit` nodes seen, and the largest.
    pub nat_lits: usize,
    pub max_nat_lit: u64,
    /// `strLit` nodes seen.
    pub str_lits: usize,
    /// Inductives whose export recursor is not named `T.rec`, or whose level
    /// parameters are not `T`'s own optionally prefixed by one motive
    /// parameter — the §2 entitlement check for reusing the export's schedule
    /// for mini's *generated* recursor.
    pub recursor_shape_mismatches: Vec<String>,
    /// `(declaration, instantiation)` pairs the pre-pass scheduled.
    pub scheduled_pairs: usize,
}

pub struct Loaded {
    pub decls: Vec<Declaration>,
    /// Per declaration name, the ground instantiations the pre-pass demands.
    /// Unused in step (b); the interpretation store of step (c) is keyed on it.
    pub schedule: HashMap<Name, Vec<Inst>>,
    pub facts: Facts,
}

/// A declined export file: mini refuses to look at it, as mini-lean's parser
/// does. Distinct from a *rejection*, which is a type error.
#[derive(Debug)]
pub enum LoadError {
    Declined(String),
    Io(String),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Declined(s) => write!(f, "declined: {s}"),
            LoadError::Io(s) => write!(f, "io: {s}"),
        }
    }
}

type LR<T> = Result<T, LoadError>;

fn declined(s: impl Into<String>) -> LoadError { LoadError::Declined(s.into()) }

/// [`load_inner`], with `checker`'s parser's `assert!`s caught.
///
/// Upstream nanoda signals "this file is not acceptable" by panicking, and its
/// parser does so for things mini-lean handles as ordinary rejections — a
/// duplicate declaration (`bad/tutorial/126`) is `Environment.insertNew`'s job
/// in mini-lean but an `assert!` in `parser.rs`. Mini must not inherit that as
/// a crash, and must not launder it into a verdict it did not reach either, so
/// it becomes a *decline*: mini never saw the file.
pub fn load(path: &Path) -> LR<Loaded> {
    // The panic hook is process-global, so swapping it must be serialised or
    // two concurrent loads can leave the silencing hook installed for good.
    // The lock covers the whole catch window; parsing is not on any hot path.
    static HOOK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let p = path.to_path_buf();
    let guard = HOOK.lock().unwrap_or_else(|e| e.into_inner());
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(move || load_inner(&p));
    std::panic::set_hook(hook);
    drop(guard);
    match r {
        Ok(v) => v,
        Err(_) => Err(declined("checker's parser panicked (assertion in parser.rs)")),
    }
}

fn load_inner(path: &Path) -> LR<Loaded> {
    // `Config` is `Deserialize`; building it from a literal avoids writing a
    // temporary config file just to call `Config::try_from(&Path)`. The flags
    // match `checker/tests/corpus.rs`: mini is testing the type checker, not
    // nanoda's axiom whitelist.
    let cfg_json = format!(
        r#"{{"export_file_path": {},
             "unpermitted_axiom_hard_error": false,
             "unsafe_permit_all_axioms": true,
             "nat_extension": true,
             "string_extension": true,
             "print_axioms": false,
             "print_success_message": false}}"#,
        serde_json::to_string(&path.to_string_lossy().to_string()).unwrap()
    );
    let cfg: Config =
        serde_json::from_str(&cfg_json).map_err(|e| LoadError::Io(format!("config: {e}")))?;
    let (ef, _skipped) = cfg.to_export_file().map_err(|e| LoadError::Io(format!("parse: {e}")))?;

    let insts = Instantiations::compute(&ef);

    ef.with_ctx(|ctx| {
        let mut cv = Cv::new(ctx);
        let mut facts = Facts { declars: ef.declars.len(), ..Facts::default() };

        // Pass 1: index constructors by their inductive (mini bundles them into
        // the inductive declaration), and recursors by the type they eliminate
        // (only for the §2 shape audit — mini generates its own).
        let mut ctors_of: HashMap<NamePtr<'_>, Vec<(u16, NamePtr<'_>, ExprPtr<'_>)>> =
            HashMap::new();
        let mut rec_of: HashMap<NamePtr<'_>, (NamePtr<'_>, Vec<LevelPtr<'_>>)> = HashMap::new();
        for (_, d) in ef.declars.iter() {
            match d {
                Declar::Constructor(c) => {
                    ctors_of.entry(c.inductive_name).or_default().push((
                        c.ctor_idx,
                        c.info.name,
                        c.info.ty,
                    ));
                }
                Declar::Recursor(r) => {
                    for ind in r.all_inductives.iter() {
                        rec_of.insert(
                            *ind,
                            (r.info.name, ctx.read_levels(r.info.uparams).to_vec()),
                        );
                    }
                }
                _ => {}
            }
        }

        // Pass 2: the declaration schedule, in file order.
        let mut decls: Vec<Declaration> = Vec::new();
        let mut schedule: HashMap<Name, Vec<Inst>> = HashMap::new();
        for (name_ptr, d) in ef.declars.iter() {
            let info = d.info();
            let name = cv.name(info.name);
            if let Some(set) = insts.for_name(*name_ptr) {
                let v: Vec<Inst> = set.iter().cloned().collect();
                facts.scheduled_pairs += v.len();
                schedule.insert(name.clone(), v);
            }
            let lparams = cv.uparams(info.uparams)?;
            match d {
                Declar::Axiom { info } => {
                    decls.push(Declaration::Axiom {
                        name,
                        lparams,
                        ty: cv.expr(info.ty, &mut facts)?,
                    });
                }
                Declar::Definition { info, val, .. } => decls.push(Declaration::Def {
                    name,
                    lparams,
                    ty: cv.expr(info.ty, &mut facts)?,
                    value: cv.expr(*val, &mut facts)?,
                    kind: DefKind::Def,
                }),
                Declar::Theorem { info, val } => decls.push(Declaration::Def {
                    name,
                    lparams,
                    ty: cv.expr(info.ty, &mut facts)?,
                    value: cv.expr(*val, &mut facts)?,
                    kind: DefKind::Theorem,
                }),
                Declar::Opaque { info, val } => decls.push(Declaration::Def {
                    name,
                    lparams,
                    ty: cv.expr(info.ty, &mut facts)?,
                    value: cv.expr(*val, &mut facts)?,
                    kind: DefKind::Opaque,
                }),
                Declar::Quot { .. } => {
                    // mini-lean adds all four constants when it sees the
                    // `type` kind, and ignores the other three.
                    if name == Name::simple("Quot") {
                        decls.push(Declaration::Quot);
                    }
                }
                Declar::Inductive(ind) => {
                    // `parseInductInfo`'s declines, in its order. (`isUnsafe`
                    // is absent because `checker`'s parser already asserts it.)
                    if ind.all_ind_names().len() > 1 {
                        return Err(declined(format!("Mutual inductive {name} not supported")))
                    }
                    if ind.is_nested() {
                        return Err(declined(format!("Nested inductive {name} not supported")))
                    }
                    if let Some((rec_name, rec_uparams)) = rec_of.get(name_ptr) {
                        cv.audit_recursor_shape(
                            &name,
                            *rec_name,
                            rec_uparams,
                            info.uparams,
                            &mut facts,
                        );
                    }
                    let num_params = u32::from(ind.num_params());
                    let mut cs = ctors_of.get(name_ptr).cloned().unwrap_or_default();
                    cs.sort_by_key(|(i, _, _)| *i);
                    let mut ctors: Vec<(Name, E)> = Vec::new();
                    for (_, cn, cty) in cs {
                        ctors.push((cv.name(cn), cv.expr(cty, &mut facts)?));
                    }
                    decls.push(Declaration::Inductive {
                        name,
                        lparams,
                        num_params,
                        ty: cv.expr(info.ty, &mut facts)?,
                        ctors,
                    });
                }
                // Constructors arrive inside their inductive; recursors are
                // generated, not read (`parseRecInfo` is a stub in mini-lean).
                Declar::Constructor(_) | Declar::Recursor(_) => {}
            }
        }
        Ok(Loaded { decls, schedule, facts })
    })
}

struct Cv<'a, 't, 'p> {
    ctx: &'a TcCtx<'t, 'p>,
    names: HashMap<NamePtr<'t>, Name>,
    levels: HashMap<LevelPtr<'t>, Level>,
    exprs: HashMap<ExprPtr<'t>, E>,
}

impl<'a, 't, 'p> Cv<'a, 't, 'p> {
    fn new(ctx: &'a TcCtx<'t, 'p>) -> Self {
        Cv { ctx, names: HashMap::new(), levels: HashMap::new(), exprs: HashMap::new() }
    }

    /// MINI-DESIGN.md §2's entitlement check: mini reuses the *export's*
    /// schedule for its *generated* recursor, which is only legitimate if the
    /// two are the same constant. Recorded rather than declined — the point of
    /// step 1 is to measure whether it ever fires.
    fn audit_recursor_shape(
        &mut self,
        ind: &Name,
        rec_name: NamePtr<'t>,
        rec_uparams: &[LevelPtr<'t>],
        ind_uparams: nanoda_lib::util::LevelsPtr<'t>,
        facts: &mut Facts,
    ) {
        let rec = self.name(rec_name);
        let expected = Name::str(ind, "rec");
        if rec != expected {
            facts
                .recursor_shape_mismatches
                .push(format!("{ind}: recursor named {rec}, not {expected}"));
            return
        }
        let ind_ptrs = self.ctx.read_levels(ind_uparams).to_vec();
        let ind_us: Vec<Level> = ind_ptrs.iter().map(|l| self.level(*l)).collect();
        let rec_us: Vec<Level> = rec_uparams.iter().map(|l| self.level(*l)).collect();
        // mini generates `v :: lparams` when the recursor eliminates to a sort,
        // and `lparams` otherwise.
        let ok =
            rec_us == ind_us || (rec_us.len() == ind_us.len() + 1 && rec_us[1..] == ind_us[..]);
        if !ok {
            facts
                .recursor_shape_mismatches
                .push(format!("{ind}: recursor level order {rec_us:?} against {ind_us:?}"));
        }
    }

    fn name(&mut self, p: NamePtr<'t>) -> Name {
        if let Some(n) = self.names.get(&p) {
            return n.clone()
        }
        let n = match self.ctx.read_name(p) {
            CName::Anon => Name::Anon,
            CName::Str(pre, s, _) => {
                let pre = self.name(pre);
                Name::Str(Rc::new(pre), Rc::from(self.ctx.read_string(s).as_ref()))
            }
            CName::Num(pre, i, _) => {
                let pre = self.name(pre);
                Name::Num(Rc::new(pre), i)
            }
        };
        self.names.insert(p, n.clone());
        n
    }

    fn level(&mut self, p: LevelPtr<'t>) -> Level {
        if let Some(l) = self.levels.get(&p) {
            return l.clone()
        }
        let l = match self.ctx.read_level(p) {
            CLevel::Zero => Level::Zero,
            CLevel::Succ(x, _) => Level::Succ(Rc::new(self.level(x))),
            CLevel::Max(x, y, _) => Level::max(self.level(x), self.level(y)),
            CLevel::IMax(x, y, _) => Level::imax(self.level(x), self.level(y)),
            CLevel::Param(n, _) => Level::Param(self.name(n)),
        };
        self.levels.insert(p, l.clone());
        l
    }

    fn uparams(&mut self, p: nanoda_lib::util::LevelsPtr<'t>) -> LR<Vec<Name>> {
        let ls = self.ctx.read_levels(p);
        let mut out = Vec::with_capacity(ls.len());
        for l in ls.iter() {
            match self.level(*l) {
                Level::Param(n) => out.push(n),
                other => {
                    return Err(declined(format!(
                        "universe parameter list contains a non-parameter: {other}"
                    )))
                }
            }
        }
        Ok(out)
    }

    fn expr(&mut self, p: ExprPtr<'t>, facts: &mut Facts) -> LR<E> {
        if let Some(e) = self.exprs.get(&p) {
            return Ok(e.clone())
        }
        let e = match self.ctx.read_expr(p) {
            CExpr::Var { dbj_idx, .. } => expr::bvar(u32::from(dbj_idx)),
            CExpr::Sort { level, .. } => expr::sort(self.level(level)),
            CExpr::Const { name, levels, .. } => {
                let n = self.name(name);
                let ls: Vec<Level> =
                    self.ctx.read_levels(levels).iter().map(|l| self.level(*l)).collect();
                expr::konst(n, ls.into())
            }
            CExpr::App { fun, arg, .. } => {
                expr::app(self.expr(fun, facts)?, self.expr(arg, facts)?)
            }
            CExpr::Pi { binder_type, body, .. } => {
                expr::forall(self.expr(binder_type, facts)?, self.expr(body, facts)?)
            }
            CExpr::Lambda { binder_type, body, .. } => {
                expr::lam(self.expr(binder_type, facts)?, self.expr(body, facts)?)
            }
            CExpr::Let { binder_type, val, body, .. } => Rc::new(Expr::Let {
                ty: self.expr(binder_type, facts)?,
                val: self.expr(val, facts)?,
                body: self.expr(body, facts)?,
            }),
            CExpr::Proj { ty_name, idx, structure, .. } => Rc::new(Expr::Proj {
                ind: self.name(ty_name),
                idx: u32::try_from(idx).map_err(|_| declined("projection index too large"))?,
                s: self.expr(structure, facts)?,
            }),
            CExpr::NatLit { ptr, .. } => {
                // No num-bigint dependency in `mini`: the decimal form is
                // enough, and anything that does not fit `u64` is above 10 and
                // declined regardless.
                let s = self
                    .ctx
                    .read_bignum(ptr)
                    .ok_or_else(|| declined("nat literal not found in the arena"))?
                    .to_string();
                let n: u64 = s.parse().unwrap_or(u64::MAX);
                facts.nat_lits += 1;
                facts.max_nat_lit = facts.max_nat_lit.max(n);
                if n > 10 {
                    return Err(declined(
                        "The mini kernel does not support nat literals larger than 10",
                    ))
                }
                Rc::new(Expr::NatLit(n))
            }
            CExpr::StringLit { ptr, .. } => {
                facts.str_lits += 1;
                Rc::new(Expr::StrLit(Rc::from(self.ctx.read_string(ptr).as_ref())))
            }
            CExpr::Local { .. } => {
                return Err(declined("export file contains a free variable"))
            }
        };
        self.exprs.insert(p, e.clone());
        Ok(e)
    }
}
