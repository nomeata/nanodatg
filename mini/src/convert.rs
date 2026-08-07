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
//! * unsafe / mutual / nested inductives (`parseInductInfo`) — **mutual is now
//!   a gate rather than an unconditional refusal**, see [`LoadOptions`]; the
//!   default is still the decline, so the arena's exit-2 population is
//!   unchanged,
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

use crate::env::{Declaration, DefKind, IndType};
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
    /// Axioms the export declares that are **not** one of Lean's own — see
    /// [`is_standard_axiom`]. Recorded here rather than declined here, because
    /// *where* the decline happens decides whether the negative corpus keeps
    /// its teeth: [`crate::run::check_file_with`] declines only after the
    /// kernel has accepted the file, so `bad/tutorial`'s `044`, `047`, `050`
    /// and `054` — all of which declare a helper axiom before the ill-typed
    /// declaration the fixture is about — go on being **rejected** instead of
    /// quietly becoming declines.
    pub nonstandard_axioms: Vec<String>,
    /// `mutual … end` blocks seen, blocks `mutual_aux::encode` could express,
    /// and recursor rules stated as theorems. Filled by
    /// [`crate::run::check_file_with`] after the kernel pass, not here — the
    /// frontend only knows how many blocks there are.
    pub mutual_blocks: usize,
    pub mutual_encoded: usize,
    pub mutual_rules: usize,
    /// Nested declarations seen, and the ones whose model
    /// [`crate::nested_splice::splice`] built, checked and keyed. Filled at the
    /// same place and for the same reason as the three above.
    pub nested_seen: usize,
    pub nested_models: usize,
}

pub struct Loaded {
    pub decls: Vec<Declaration>,
    /// Per declaration name, the ground instantiations the pre-pass demands.
    /// Unused in step (b); the interpretation store of step (c) is keyed on it.
    pub schedule: HashMap<Name, Vec<Inst>>,
    pub facts: Facts,
    /// **The export's own recursors**, by name, converted and otherwise
    /// untouched.
    ///
    /// Mini *generates* its recursors and feeds the generated ones to the
    /// kernel; these are kept beside them so a test can put the two side by
    /// side. That comparison is the only oracle zone A's recursor builder has
    /// that is independent of zone A: everything else it is checked against —
    /// `check_type` on the generated type, the ι rule firing — is mini
    /// agreeing with itself. It is not consulted by the kernel and must not
    /// become an input to it; `parseRecInfo` is a stub in mini-lean and stays
    /// one here.
    pub export_recs: HashMap<Name, ExportRec>,
}

/// One recursor as the export file declares it. See [`Loaded::export_recs`].
#[derive(Debug, Clone)]
pub struct ExportRec {
    pub lparams: Vec<Name>,
    pub ty: E,
    pub num_params: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub num_indices: u32,
    /// `(constructor, right-hand side)`, with the export's own
    /// `fun params motives minors fields => …` binders still on the RHS —
    /// where [`crate::env::ConstantInfo::Recursor`] stores the open body.
    pub rules: Vec<(Name, E)>,
    /// Whether Lean marks this recursor as K-like. Mini computes its own
    /// (`ConstantInfo::Recursor`'s `k_type`), and the two must agree: a
    /// recursor that fires on the major argument's *type* rather than on its
    /// head constructor is a different reduction, and getting it wrong on a
    /// mutual block would let one member's K-rule fire at another's major.
    pub is_k: bool,
}

/// What the frontend is allowed to take.
///
/// **One field, and it is a contract change waiting to be made.** Mini declines
/// a `mutual … end` block at the parser, exit 2, which is the kernel arena's
/// code for an unsupported feature and a population `MINI-DESIGN.md` §0 says
/// must not move by accident. Zone A can check a mutual block and compute its
/// recursors now (`kernel::add_block`), but zone B cannot interpret one, so a
/// file carrying one would be *accepted* and wholly untranslated. Lifting the
/// decline is therefore deliberate and separate: it is off here, the fixture
/// tests turn it on, and the corpus never sees it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LoadOptions {
    /// Take a `mutual … end` block instead of declining the file.
    pub mutual: bool,
    /// Take a **nested** inductive instead of declining the file.
    ///
    /// A second gate, and separate from `mutual` for a reason that is not
    /// symmetry: a nested declaration is accepted by *specialising* it into a
    /// mutual block, checking that, and **restoring** the result
    /// ([`crate::nested`]). The restoration rewrites the specialised copy of
    /// the container back to the real container, and that rewrite is not a
    /// derivation — `List Tree` and the copy are isomorphic, not equal, and
    /// the round trip is propositional (`mini/tests/nested.rs`). So the
    /// recursor `Tree.rec_1` enters the environment carrying an ι rule on
    /// `List.cons` that nothing on the acceptance axis has checked. Until the
    /// evidence axis discharges it, the corpus must not see this.
    pub nested: bool,
    /// Convert the export's own recursors into [`Loaded::export_recs`].
    ///
    /// **Off by default, and not for tidiness.** Converting them walks every
    /// recursor type and every rule right-hand side, which are the largest
    /// expressions in an export; it would move `Facts`' literal counters, and
    /// a nat literal above ten inside a rule — a shape `Cv::expr` declines —
    /// would turn an accepted file into a declined one from a code path
    /// nothing in the checker reads. The one consumer is a test.
    pub keep_export_recursors: bool,
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

/// **Lean's own axioms**, and nothing else.
///
/// These three are the axioms `lean4export` emits for a file that declares
/// none of its own: `Quot.sound` (the quotient's soundness rule, which the
/// exporter emits as an `axiom` even though `Quot`'s other three constants
/// come through as `quot` entries), `propext`, and `Classical.choice`. Each
/// is *validated* by the set-theoretic model — Carneiro's thesis constructs
/// an interpretation in which each is a theorem — so each is, in the long
/// run, a `derived/` obligation.
///
/// A **user-declared** axiom is a different thing entirely: nothing in the
/// model says the symbol denotes an inhabitant of anything, so no amount of
/// work in `derived/` can discharge it. The interpretation can be given, and
/// mini gives it — a fresh opaque symbol is a conservative signature
/// extension — but the typing `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` is not derivable *in
/// principle*, and a run that stops at the first missing derivation would
/// stop there for ever.
///
/// **No exceptions, including a sort-valued one.** `axiom A : Prop` asserts no
/// inhabitation, so its `⊢ ⟦A⟧ ∈ U₀` *is* derivable — but deriving it is work
/// for a file mini has already taken out of scope, and the only construction
/// that did it (`Interp::opaque_in_sort`, `cc0f898`) paid for it by narrowing
/// the model: `⟦T⟧` for `axiom T : Type` became `0` or `1` rather than an
/// arbitrary small set. Mini declines the whole export by name rather than
/// reasoning about which of its axioms happen to be harmless.
///
/// So mini declines such a file at the frontend, **by name and with a
/// reason**, as `mini-lean`'s parser declines an unsafe declaration. This is
/// the acceptance axis, not the evidence axis: the file is not rejected and
/// no judgement about it is claimed. `mini/tests/tutorial.rs` records the
/// exports this covers.
///
/// # Structurally, not by rendering
///
/// The components are matched the way [`crate::axiom::clause_for`] matches
/// them. A `Name` renders its components dot-separated, and the export format
/// puts no constraint on a component's string — so `axiom «Quot.sound»`, one
/// component containing a dot, renders as `Quot.sound` and a `to_string()`
/// comparison would wave it through as Lean's own. The pin is this module's
/// `a_dotted_component_is_not_a_standard_axiom`.
fn is_standard_axiom(n: &Name) -> bool {
    let Name::Str(pre, s) = n else { return false };
    match &**pre {
        Name::Anon => &**s == "propext",
        Name::Str(root, q) if **root == Name::Anon => {
            matches!((&**q, &**s), ("Quot", "sound") | ("Classical", "choice"))
        }
        _ => false,
    }
}

/// [`load_inner`], with `checker`'s parser's `assert!`s caught.
///
/// Upstream nanoda signals "this file is not acceptable" by panicking, and its
/// parser does so for things mini-lean handles as ordinary rejections — a
/// duplicate declaration (`bad/tutorial/126`) is `Environment.insertNew`'s job
/// in mini-lean but an `assert!` in `parser.rs`. Mini must not inherit that as
/// a crash, and must not launder it into a verdict it did not reach either, so
/// it becomes a *decline*: mini never saw the file.
pub fn load(path: &Path) -> LR<Loaded> { load_with(path, LoadOptions::default()) }

/// [`load`], with the frontend's one gate open or shut.
pub fn load_with(path: &Path, opts: LoadOptions) -> LR<Loaded> {
    // The panic hook is process-global, so swapping it must be serialised or
    // two concurrent loads can leave the silencing hook installed for good.
    // The lock covers the whole catch window; parsing is not on any hot path.
    static HOOK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let p = path.to_path_buf();
    let guard = HOOK.lock().unwrap_or_else(|e| e.into_inner());
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(move || load_inner(&p, opts));
    std::panic::set_hook(hook);
    drop(guard);
    match r {
        Ok(v) => v,
        Err(_) => Err(declined("checker's parser panicked (assertion in parser.rs)")),
    }
}

fn load_inner(path: &Path, opts: LoadOptions) -> LR<Loaded> {
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
        // **A `Vec`, because a mutual block has one recursor per member and
        // every one of them lists every member in `all`.** Keyed by the
        // inductive with the last writer winning, `A` came out pointing at
        // `C.rec` — and the audit below, whose whole job is to say whether the
        // export's recursor for `T` really is `T.rec`, would have reported the
        // block's last recursor for all of them. Non-mutual files put exactly
        // one entry in each vector and are unaffected.
        let mut rec_of: HashMap<NamePtr<'_>, Vec<(NamePtr<'_>, Vec<LevelPtr<'_>>)>> =
            HashMap::new();
        // Every inductive by name, for a `mutual` block: its members are
        // separate `Declar::Inductive` entries and are collected at the first
        // of them.
        let mut ind_of: HashMap<NamePtr<'_>, &Declar<'_>> = HashMap::new();
        for (n, d) in ef.declars.iter() {
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
                        rec_of
                            .entry(*ind)
                            .or_default()
                            .push((r.info.name, ctx.read_levels(r.info.uparams).to_vec()));
                    }
                }
                Declar::Inductive(_) => {
                    ind_of.insert(*n, d);
                }
                _ => {}
            }
        }

        // The export's own recursors, kept beside mini's generated ones for the
        // benefit of a test and of nothing else. See [`Loaded::export_recs`].
        // The scratch `Facts` is why this cannot move a measurement: the
        // literal counters it feeds are thrown away with it.
        let mut export_recs: HashMap<Name, ExportRec> = HashMap::new();
        if opts.keep_export_recursors {
            let mut scratch = Facts::default();
            for (_, d) in ef.declars.iter() {
                let Declar::Recursor(r) = d else { continue };
                let go = |cv: &mut Cv<'_, '_, '_>, scratch: &mut Facts| -> LR<ExportRec> {
                    let mut rules = Vec::with_capacity(r.rec_rules.len());
                    for rule in r.rec_rules.iter() {
                        rules.push((cv.name(rule.ctor_name), cv.expr(rule.val, scratch)?));
                    }
                    Ok(ExportRec {
                        lparams: cv.uparams(r.info.uparams)?,
                        ty: cv.expr(r.info.ty, scratch)?,
                        num_params: u32::from(r.num_params),
                        num_motives: u32::from(r.num_motives),
                        num_minors: u32::from(r.num_minors),
                        num_indices: u32::from(r.num_indices),
                        rules,
                        is_k: r.is_k,
                    })
                };
                // A recursor mini cannot convert is simply absent from the
                // table; the consumer asserts on the ones it finds and names
                // the ones it does not.
                if let Ok(er) = go(&mut cv, &mut scratch) {
                    export_recs.insert(cv.name(r.info.name), er);
                }
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
                    if !is_standard_axiom(&name) {
                        facts.nonstandard_axioms.push(name.to_string());
                    }
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
                    let all = ind.all_ind_names();
                    if all.len() > 1 && !opts.mutual {
                        return Err(declined(format!("Mutual inductive {name} not supported")))
                    }
                    if ind.is_nested() && !opts.nested {
                        return Err(declined(format!("Nested inductive {name} not supported")))
                    }
                    if let Some(recs) = rec_of.get(name_ptr) {
                        cv.audit_recursor_shape(&name, recs, info.uparams, &mut facts);
                    }
                    let num_params = u32::from(ind.num_params());
                    if all.len() > 1 {
                        // **The whole block is one declaration, emitted at its
                        // first member and skipped at the rest.** `all` is the
                        // export's own list and is in the block's declaration
                        // order, which is the order the shared motive and minor
                        // telescopes are built in — recovering it from the
                        // order the members happen to appear in the file would
                        // be the same list today and an assumption tomorrow.
                        if all.first() != Some(name_ptr) {
                            continue
                        }
                        let mut types: Vec<IndType> = Vec::with_capacity(all.len());
                        for m in all {
                            let Some(md) = ind_of.get(m).copied() else {
                                return Err(declined(format!(
                                    "mutual block of {name} names a member the export does not declare"
                                )))
                            };
                            let Declar::Inductive(mi) = md else {
                                return Err(declined(format!(
                                    "mutual block of {name} names a non-inductive member"
                                )))
                            };
                            // The kernel checks parameter *types* against the
                            // first member; the count is what splits every
                            // telescope below and is read here, per member, for
                            // the reason `bad/048` exists.
                            if mi.num_params() != ind.num_params() {
                                return Err(declined(format!(
                                    "mutual block of {name} has members with different parameter counts"
                                )))
                            }
                            let minfo = md.info();
                            let mn = cv.name(minfo.name);
                            types.push(cv.ind_member(mn, *m, minfo.ty, &ctors_of, &mut facts)?);
                        }
                        decls.push(Declaration::Mutual { lparams, num_params, types });
                    } else {
                        let t =
                            cv.ind_member(name, *name_ptr, info.ty, &ctors_of, &mut facts)?;
                        decls.push(Declaration::Inductive {
                            name: t.name,
                            lparams,
                            num_params,
                            ty: t.ty,
                            ctors: t.ctors,
                        });
                    }
                }
                // Constructors arrive inside their inductive; recursors are
                // generated, not read (`parseRecInfo` is a stub in mini-lean).
                Declar::Constructor(_) | Declar::Recursor(_) => {}
            }
        }
        Ok(Loaded { decls, schedule, facts, export_recs })
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

    /// One inductive member: its type and its constructors, in `ctor_idx`
    /// order. The same code for a single declaration and for a member of a
    /// `mutual … end` block — the only difference between them is how many
    /// times it is called.
    fn ind_member(
        &mut self,
        name: Name,
        ptr: NamePtr<'t>,
        ty: ExprPtr<'t>,
        ctors_of: &HashMap<NamePtr<'t>, Vec<(u16, NamePtr<'t>, ExprPtr<'t>)>>,
        facts: &mut Facts,
    ) -> LR<IndType> {
        let mut cs = ctors_of.get(&ptr).cloned().unwrap_or_default();
        cs.sort_by_key(|(i, _, _)| *i);
        let mut ctors: Vec<(Name, E)> = Vec::new();
        for (_, cn, cty) in cs {
            ctors.push((self.name(cn), self.expr(cty, facts)?));
        }
        Ok(IndType { name, ty: self.expr(ty, facts)?, ctors })
    }

    /// MINI-DESIGN.md §2's entitlement check: mini reuses the *export's*
    /// schedule for its *generated* recursor, which is only legitimate if the
    /// two are the same constant. Recorded rather than declined — the point of
    /// step 1 is to measure whether it ever fires.
    fn audit_recursor_shape(
        &mut self,
        ind: &Name,
        recs: &[(NamePtr<'t>, Vec<LevelPtr<'t>>)],
        ind_uparams: nanoda_lib::util::LevelsPtr<'t>,
        facts: &mut Facts,
    ) {
        let expected = Name::str(ind, "rec");
        // **The recursor for *this* member.** A single declaration's list has
        // one entry and this picks it; a mutual block's has one per member and
        // this picks `T.rec`, falling back to the first so that a block whose
        // recursor really is misnamed still reports rather than silently
        // finding nothing to audit.
        let Some((rec_name, rec_uparams)) =
            recs.iter().find(|(n, _)| self.name(*n) == expected).or_else(|| recs.first())
        else {
            return
        };
        let (rec_name, rec_uparams) = (*rec_name, rec_uparams.clone());
        let rec = self.name(rec_name);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// **The whitelist is three names, matched component by component.**
    ///
    /// Both directions are pinned, because each has a way of going wrong:
    /// Lean's three must be recognised (or every export declines and the
    /// corpus empties), and a *user* axiom must not be able to render itself
    /// into the whitelist. `Name.str(anon, "Quot.sound")` is a name Lean can
    /// declare (`axiom «Quot.sound»`) and the export format can carry, and it
    /// renders exactly as the real one — a `to_string()` comparison accepts
    /// it, which is the mutation this test kills.
    #[test]
    fn a_dotted_component_is_not_a_standard_axiom() {
        for n in [
            Name::simple("propext"),
            Name::str(&Name::simple("Quot"), "sound"),
            Name::str(&Name::simple("Classical"), "choice"),
        ] {
            assert!(is_standard_axiom(&n), "Lean's own axiom is not recognised: {n}");
        }
        for n in [
            Name::simple("Quot.sound"),
            Name::simple("Classical.choice"),
            Name::str(&Name::simple("My"), "propext"),
            Name::str(&Name::str(&Name::simple("A"), "Quot"), "sound"),
            Name::Num(Rc::new(Name::simple("propext")), 0),
            Name::Anon,
        ] {
            assert!(
                !is_standard_axiom(&n),
                "a user-declared axiom passed as one of Lean's own: {n:?}"
            );
        }
    }
}
