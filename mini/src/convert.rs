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
use crate::expr::{self, Level, Name, E, NameView, LevelView};
use nanoda_lib::env::Declar;
use nanoda_lib::expr::Expr as CExpr;
use nanoda_lib::instantiations::{Inst, Instantiations};
use nanoda_lib::util::{Config, ExprPtr, LevelPtr, NamePtr};
use std::collections::HashMap;
use std::path::Path;

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
    // **There is no `nonstandard_axioms` list here, and its absence is the
    // point.** The frontend used to record one and
    // [`crate::run::check_file_with`] used to decline on its first entry. The
    // decline now asks [`crate::unused_axiom::classify`] instead, because the
    // question is no longer "is there one" but "does anything refer to it",
    // and that is a property of the whole declaration list rather than of a
    // declaration as it goes past. Leaving the list behind would have left two
    // answers to one question, computed in two places, with only one of them
    // read.
    //
    /// `mutual … end` blocks seen, blocks `mutual_aux::encode` could express,
    /// and recursor rules stated as theorems. Filled by
    /// [`crate::run::check_file_with`] after the kernel pass, not here — the
    /// frontend only knows how many blocks there are.
    pub mutual_blocks: usize,
    pub mutual_encoded: usize,
    pub mutual_rules: usize,
    /// Nested declarations seen, and the ones whose model
    /// [`crate::nested_splice::recognise`] found in the export and keyed. Filled at the
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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LoadOptions {
    /// **Run the export through the `modelgen` filter first** —
    /// [`crate::modelgen`], which says where the binary is looked for, why the
    /// pass streams rather than writing a temporary file, and why every failure
    /// is a named decline rather than a silent skip.
    ///
    /// [`crate::modelgen::Filter::Off`] here and **on** in `mini`'s command
    /// line, and the asymmetry is deliberate: the library entry point is what
    /// the test suites call, and they read committed fixtures that are already
    /// filtered, so a suite that ran the pass would acquire a dependency on a
    /// Lean toolchain for no change in what it reads.
    pub modelgen: crate::modelgen::Filter,
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
/// **One narrowing, and it is not an exception to the paragraph above.** An
/// axiom this predicate rejects and **nothing in the file refers to** is
/// *ignored* rather than declined: it creates no obligation for any pair,
/// because every consequence of an axiom reaches the ledger through a
/// reference to it. [`crate::unused_axiom`] is the whole of that rule, the
/// argument for it, and what "refers to" is checked to cover. A **used**
/// non-standard axiom declines here exactly as it always has.
///
/// # Structurally, not by rendering
///
/// The components are matched the way [`crate::axiom::clause_for`] matches
/// them. A `Name` renders its components dot-separated, and the export format
/// puts no constraint on a component's string — so `axiom «Quot.sound»`, one
/// component containing a dot, renders as `Quot.sound` and a `to_string()`
/// comparison would wave it through as Lean's own. The pin is this module's
/// `a_dotted_component_is_not_a_standard_axiom`.
pub fn is_standard_axiom(n: &Name) -> bool {
    let NameView::Str(pre, s) = n.view() else { return false };
    match pre.view() {
        NameView::Anon => &*s == "propext",
        NameView::Str(root, q) if root.is_anon() => {
            matches!((&*q, &*s), ("Quot", "sound") | ("Classical", "choice"))
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
    // **The `modelgen` pass, and a failure here is a decline that names it.**
    // `crate::modelgen`'s header says why: falling back to the unfiltered input
    // would report a toolchain problem as the declaration's.
    let (ef, _skipped) = match &opts.modelgen {
        crate::modelgen::Filter::Off => {
            cfg.to_export_file().map_err(|e| LoadError::Io(format!("parse: {e}")))?
        }
        crate::modelgen::Filter::Run(exe) => {
            let (bytes, report) =
                crate::modelgen::filter(exe, path).map_err(|e| declined(format!("modelgen: {e}")))?;
            // **The child's report, written through.** It is on the child's
            // stderr precisely so that it can be, and it carries the only
            // statement of *why* a declaration has no model — `nested model
            // without funext` rather than mini's own `no nested model in the
            // export`, which says where the lookup stopped and not why.
            if !report.is_empty() {
                eprintln!("{report}");
            }
            cfg.to_export_file_from(std::io::Cursor::new(bytes))
                .map_err(|e| LoadError::Io(format!("parse (after modelgen): {e}")))?
        }
    };

    // **One context, and it is `crate::arena`'s.** This used to be
    // `ef.with_ctx(|ctx| …)`, which mints a *second* `LeanDag` and `TcCtx`
    // scoped to the closure. That was harmless while mini converted every
    // pointer into an owned tree on the way out, and is not harmless now: a
    // `NamePtr` read from one context and a `NamePtr` built in another are
    // incomparable integers, so the two must be the same context. Installing
    // the export file *is* opening it — see `crate::arena`.
    let ef = crate::arena::install_export_file(ef);
    let insts = Instantiations::compute(ef);

    {
        let mut cv = Cv::new();
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
                            .push((r.info.name, crate::arena::read_levels(r.info.uparams).to_vec()));
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
                let go = |cv: &mut Cv, scratch: &mut Facts| -> LR<ExportRec> {
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
                schedule.insert(name, v);
            }
            let lparams = cv.uparams(info.uparams)?;
            match d {
                Declar::Axiom { info } => {
                    // Nothing is recorded about a non-standard axiom here:
                    // whether it takes the file out of scope depends on what
                    // the *rest* of the file refers to, and this loop has seen
                    // only the prefix. [`crate::unused_axiom`] asks that
                    // question of the finished list, and `Facts`' fields say
                    // why the list this one used to keep is gone.
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
                    // **`--nested` opens the mutual gate too**, and that is a
                    // consequence of the model arriving in the file rather
                    // than a softening of the contract. `modelgen` splices
                    // `T._model.0 … T._model.{n−1}` — a `mutual … end` block —
                    // in front of every nested inductive it models
                    // (`MODELGEN.md` §1), so a filtered export with a nested
                    // declaration *always* has a mutual block in it. A nested
                    // gate that did not open the mutual one could therefore
                    // never take a nested declaration at all: every one of
                    // `mini/tests/fixtures/nested_*.ndjson` declines at this
                    // line before reaching the next.
                    //
                    // `--mutual` on its own is unchanged, and so is the corpus:
                    // no `good/tutorial` export declares either shape, and the
                    // exit-2 population MINI-DESIGN.md §0 pins is read off that
                    // corpus.
                    if all.len() > 1 && !(opts.mutual || opts.nested) {
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
    }
}

/// The export file's items, in mini's normal form.
///
/// **One table left of three.** `names` and `levels` are gone: mini's `Name`
/// and `Level` *are* `checker`'s pointers, so there is nothing to convert and
/// nothing to memoise. `exprs` survives because [`Cv::expr`] is not the
/// identity — it erases binder metadata — and without a memo it would walk a
/// hash-consed DAG as a tree.
struct Cv {
    exprs: HashMap<ExprPtr<'static>, E>,
}

impl Cv {
    fn new() -> Self { Cv { exprs: HashMap::new() } }

    /// One inductive member: its type and its constructors, in `ctor_idx`
    /// order. The same code for a single declaration and for a member of a
    /// `mutual … end` block — the only difference between them is how many
    /// times it is called.
    fn ind_member(
        &mut self,
        name: Name,
        ptr: NamePtr<'static>,
        ty: ExprPtr<'static>,
        ctors_of: &HashMap<NamePtr<'static>, Vec<(u16, NamePtr<'static>, ExprPtr<'static>)>>,
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
        recs: &[(NamePtr<'static>, Vec<LevelPtr<'static>>)],
        ind_uparams: nanoda_lib::util::LevelsPtr<'static>,
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
        let ind_ptrs = crate::arena::read_levels(ind_uparams).to_vec();
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

    /// **The identity.** Mini's `Name` is `checker`'s `NamePtr`, so there is
    /// no conversion left — this is a wrap, kept as a method only so that the
    /// call sites do not all have to change in the same commit.
    fn name(&mut self, p: NamePtr<'static>) -> Name { Name(p) }

    /// **The identity**, as [`Cv::name`] is.
    ///
    /// This used to rebuild the level node by node. It cannot do anything now:
    /// mini's `Level` *is* `checker`'s `LevelPtr`, and a level carries no
    /// binder metadata, so rebuilding would hash-cons its way back to the
    /// pointer it started from — a walk with no output. Dropping it takes the
    /// memo that cached the walk with it.
    fn level(&mut self, p: LevelPtr<'static>) -> Level { Level(p) }

    fn uparams(&mut self, p: nanoda_lib::util::LevelsPtr<'static>) -> LR<Vec<Name>> {
        let ls = crate::arena::read_levels(p);
        let mut out = Vec::with_capacity(ls.len());
        for l in ls.iter() {
            let lvl = self.level(*l);
            match lvl.view() {
                LevelView::Param(n) => out.push(n),
                _ => {
                    return Err(declined(format!(
                        "universe parameter list contains a non-parameter: {lvl}"
                    )))
                }
            }
        }
        Ok(out)
    }

    /// **The export's expression, in mini's normal form.**
    ///
    /// Not a conversion any more — the representations are the same — but not
    /// the identity either, and the difference is the whole correctness
    /// argument of the migration. Rebuilding every node through
    /// `crate::expr`'s constructors is what *erases the binder metadata*:
    /// `checker` hash-conses `binder_name`, `binder_style` and `nondep` into
    /// the node, mini has always dropped binder names on purpose
    /// (`crate::expr`'s header), and a parsed `∀ x : A, B` must come out as
    /// the same pointer as a generated `∀ _ : A, B` or mini's whole-expression
    /// comparisons start distinguishing spellings. `crate::arena::erase_binders`
    /// states that normal form on its own and four tests there pin it; this is
    /// the same form, realised inline because the walk has to happen anyway —
    /// it counts literals, enforces mini-lean's `natLit > 10` decline, bounds
    /// the projection index and refuses a free variable.
    ///
    /// So the memo stays: without it this is a *tree* walk over a DAG.
    fn expr(&mut self, p: ExprPtr<'static>, facts: &mut Facts) -> LR<E> {
        if let Some(e) = self.exprs.get(&p) {
            return Ok(*e)
        }
        let e = match crate::arena::read_expr(p) {
            CExpr::Var { .. } => E(p),
            // `Const` and `Sort` carry no binders, so both are already in
            // normal form and the pointer passes straight through.
            CExpr::Const { .. } | CExpr::Sort { .. } => E(p),
            CExpr::App { fun, arg, .. } => {
                expr::app(self.expr(fun, facts)?, self.expr(arg, facts)?)
            }
            CExpr::Pi { binder_type, body, .. } => {
                expr::forall(self.expr(binder_type, facts)?, self.expr(body, facts)?)
            }
            CExpr::Lambda { binder_type, body, .. } => {
                expr::lam(self.expr(binder_type, facts)?, self.expr(body, facts)?)
            }
            CExpr::Let { binder_type, val, body, .. } => crate::expr::let_(
                self.expr(binder_type, facts)?,
                self.expr(val, facts)?,
                self.expr(body, facts)?,
            ),
            CExpr::Proj { ty_name, idx, structure, .. } => crate::expr::proj(
                self.name(ty_name),
                u32::try_from(idx).map_err(|_| declined("projection index too large"))?,
                self.expr(structure, facts)?,
            ),
            CExpr::NatLit { ptr, .. } => {
                // The decimal form is enough: mini's literals are `u64` and
                // anything that does not fit is above 10 and declined anyway.
                let s = crate::arena::read_nat_lit_decimal(ptr)
                    .ok_or_else(|| declined("nat literal not found in the arena"))?;
                let n = literal_value(&s)?;
                facts.nat_lits += 1;
                facts.max_nat_lit = facts.max_nat_lit.max(n);
                if n > 10 {
                    return Err(declined(
                        "The mini kernel does not support nat literals larger than 10",
                    ))
                }
                E(p)
            }
            CExpr::StringLit { .. } => {
                facts.str_lits += 1;
                E(p)
            }
            CExpr::Local { .. } => {
                return Err(declined("export file contains a free variable"))
            }
        };
        self.exprs.insert(p, e);
        Ok(e)
    }
}

/// A nat literal's value, as a `u64`, or a **decline that names the overflow**.
///
/// `mini`'s [`Expr::NatLit`](crate::expr::Expr::NatLit) is a `u64` and the
/// arena's is arbitrary precision, so the conversion is partial and the
/// partiality is not hypothetical: `init-prelude` declares `UInt64.size` as
/// `18446744073709551616` = 2⁶⁴, which is the **first value past the type** —
/// and `.parse().unwrap_or(u64::MAX)`, the spelling this replaces, turned it
/// into `2⁶⁴ − 1`.
///
/// That was harmless only because every value above ten is declined two lines
/// below, so the wrong number was never used for anything but the
/// `facts maxNatLit` column — where it was already visibly wrong, reporting
/// `18446744073709551615` for a file whose largest literal is
/// `18446744073709551616`. The moment the `> 10` guard is lifted for the
/// binary literal clause the clamp becomes silent value corruption at exactly
/// the value the whole exercise is named after, so it is closed here, ahead of
/// that change and independently of it.
///
/// The decline is its own reason and not the `> 10` one, because the two are
/// different facts about the export and a single message would make the
/// measurement above unreadable a second time.
fn literal_value(s: &str) -> LR<u64> {
    s.parse().map_err(|_| {
        declined(format!("nat literal {s} does not fit in the 64 bits mini's Expr::NatLit has"))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **2⁶⁴ is a decline, not `2⁶⁴ − 1`.** The boundary is pinned from both
    /// sides — `u64::MAX` is the largest value that fits and must survive
    /// intact — because a clamp passes any test that only looks at the value
    /// *below* the boundary, and because the two neighbours differ by one and
    /// the wrong answer is exactly the smaller of them.
    #[test]
    fn a_literal_past_sixty_four_bits_declines_rather_than_clamping() {
        assert_eq!(literal_value("0").ok(), Some(0));
        assert_eq!(literal_value("11").ok(), Some(11));
        assert_eq!(literal_value("18446744073709551615").ok(), Some(u64::MAX));
        // 2⁶⁴ — `UInt64.size` in `init-prelude`, and the first value past the type.
        assert!(
            literal_value("18446744073709551616").is_err(),
            "2⁶⁴ was accepted, which can only be by clamping it to 2⁶⁴ − 1"
        );
        // …and the reason says which fact about the export it is.
        let e = format!("{:?}", literal_value("18446744073709551616").unwrap_err());
        assert!(e.contains("64 bits"), "the decline does not name the overflow: {e}");
    }

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
            Name::num(&Name::simple("propext"), 0),
            Name::anon(),
        ] {
            assert!(
                !is_standard_axiom(&n),
                "a user-declared axiom passed as one of Lean's own: {n:?}"
            );
        }
    }
}
