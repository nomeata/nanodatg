//! One export file, one verdict.
//!
//! # Interface
//!
//! [`check_file`] is what both `mini/src/main.rs` and `mini/tests/tutorial.rs`
//! call. It reproduces `Main.lean`'s `runKernel` in its strict (non-`--liberal`)
//! mode: declarations in file order, the first rejection ends the run.
//!
//! The three outcomes are kept apart because MINI-DESIGN.md §0's two axes
//! demand it: [`Verdict::Accepted`] and [`Verdict::Rejected`] are the
//! *acceptance* axis, which must agree with mini-lean and with nanoda, and
//! [`Verdict::Declined`] is mini refusing to look — the **arena decline**,
//! mini-lean's `exit 2`, for a *file* carrying a feature mini does not support.
//! Gaps are a further column on an accepted file, never a verdict.
//!
//! **The arena decline is the only thing in this file called a decline.** A
//! declaration mini could not translate inside a file it *accepted* is an
//! `untranslated` record on the certification axis
//! ([`crate::ledger::Untranslated`], exit 4) and must never move a file into
//! [`Verdict::Declined`]: that set is the arena's contract. `zoneb`'s header
//! separates the senses.
//!
//! **A decline has two causes now, and they arrive at different moments.**
//! The parser's — a shape mini-lean's parser also refuses — happens in
//! [`convert::load`], before anything is checked. The other is a
//! *user-declared axiom*, which takes the file out of scope because its
//! inhabitation is not derivable in principle; that one happens **after** the
//! kernel has accepted the file, and the comment at the site says why the
//! order is load-bearing.
//!
//! **The second cause needs the axiom to be *used*.** A non-standard axiom
//! nothing in the file refers to is ignored — kernel-checked like any other
//! declaration, then dropped before the interpretation pass, so it is not
//! translated and schedules no pair — and named in
//! [`crate::ledger::Ledger::ignored_axioms`] so the skip is visible.
//! [`crate::unused_axiom`] is the rule, the argument that it is a narrowing
//! rather than a reversal, and the enumeration of what "refers to" covers.
//!
//! [`Options::block`] adds the blocking mode of MINI-DESIGN.md §0.6. It is not
//! a verdict either: a blocked file was *accepted*, and the report says which
//! `(declaration, σ)` the evidence axis stopped at.

use crate::census::Census;
use crate::ledger::Ledger;
use crate::convert::{self, Facts};
use crate::env::Environment;
use crate::kernel;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Accepted { declars: usize },
    Rejected { name: String, msg: String },
    Declined { reason: String },
}

impl Verdict {
    pub fn is_accepted(&self) -> bool { matches!(self, Verdict::Accepted { .. }) }

    /// The one-word column the corpus tables use.
    pub fn tag(&self) -> &'static str {
        match self {
            Verdict::Accepted { .. } => "accept",
            Verdict::Rejected { .. } => "reject",
            Verdict::Declined { .. } => "decline",
        }
    }
}

/// How much mini is asked to do with the file.
///
/// Not `Copy` since [`Options::dump`] carries a filter; it is moved into the
/// worker thread once per file, which is the only place it travels.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Options {
    /// **Stop at the first blocker.** The interpretation pass ends at the
    /// first `(declaration, σ)` whose obligation it cannot discharge, and
    /// [`Outcome::blocker`] carries the report. Off, the pass runs to the end
    /// and the ledger counts every gap, as it always has.
    pub block: bool,
    /// **Dump the stored context** after the pass — [`crate::dump`]. Not a
    /// verdict and not a mode: the same run happens, and the store is read at
    /// the end. `None` is off; `Some(filter)` narrows it.
    pub dump: Option<crate::dump::Filter>,
    /// **Take a `mutual … end` block** instead of declining the file at the
    /// parser. Off by default: the mutual decline is part of the arena's exit-2
    /// contract and `crate::convert::LoadOptions` says why lifting it is a
    /// separate, deliberate step. A file taken this way is *accepted* and its
    /// whole block is untranslated — exit 4, not exit 0.
    pub mutual: bool,
    /// **Take a nested inductive** instead of declining the file at the
    /// parser. A second gate, off by default, and separate from `mutual` for
    /// the reason [`crate::convert::LoadOptions::nested`] gives: a nested
    /// declaration is accepted by specialising it into a mutual block and
    /// *restoring* the result, and the restoration is a rewrite along an
    /// isomorphism the acceptance axis does not check.
    pub nested: bool,
    /// **Run the export through the `modelgen` filter before parsing it** —
    /// [`crate::modelgen`]. `Off` here and on in `mini`'s command line; the
    /// module header says why the two differ and what happens on a machine
    /// with no Lean toolchain.
    pub modelgen: crate::modelgen::Filter,
    /// **Take the de-scheduled route** — [`crate::poly_run`], `LEVELPOLY.md`
    /// §5.3 step 1. One interpretation per *declaration* at its own universe
    /// parameters, instead of one per `(declaration, σ)`.
    ///
    /// **It replaces the scheduled pass rather than joining it**, and
    /// [`crate::poly_run`]'s header carries the argument: the two mint into one
    /// [`crate::interp::Interp`] and `level_poly` declares symbols off the
    /// shared `Env`, so a run that did both would renumber the second pass's
    /// symbols and the byte-identical scheduled rows this branch lands against
    /// would stop being reproducible. Off by default, so the default route is
    /// the route it has always been.
    ///
    /// The acceptance axis is untouched: the file is kernel-checked exactly as
    /// before and the [`Verdict`] is the same one. Only the interpretation pass
    /// differs, and [`Outcome::poly`] is where its report goes.
    pub poly: bool,
}

pub struct Outcome {
    pub verdict: Verdict,
    pub facts: Facts,
    /// Which §6.2 clauses this file's declarations spend their nodes on —
    /// how the remaining threading work is sized.
    pub census: Census,
    /// One row per inductive with an exported recursor: the computed
    /// eliminator class against the recursor's own. See
    /// [`crate::zoneb::elim_audit`].
    pub elim_audit: Vec<String>,
    /// What `⟦·⟧` actually reached, per `(declaration, σ)`, attributed by
    /// cause. `None` when the file was declined or rejected: a gap ledger for
    /// a file mini did not accept would mix the two axes.
    ///
    /// **Also `None` under [`Options::poly`]**, where the scheduled pass did
    /// not run at all and [`Outcome::poly`] is the report instead. The two are
    /// exclusive by construction and never both `Some`.
    pub ledger: Option<Ledger>,
    /// The **de-scheduled** pass's report — [`crate::poly_run`] — when
    /// [`Options::poly`] asked for one, and `None` otherwise.
    pub poly: Option<crate::poly_run::PolyLedger>,
    /// The stored-context dump, when [`Options::dump`] asked for one.
    ///
    /// A `String`, and rendered inside the worker, for the reason
    /// [`crate::blocker::Blocker`] is: the `Interp` is `Rc`-backed and does not
    /// cross the thread join, so the only place it can be read is where it
    /// lives.
    pub dump: Option<String>,
}

impl Outcome {
    /// The first blocker, when the run was asked to stop at one.
    pub fn blocker(&self) -> Option<&crate::blocker::Blocker> {
        self.ledger.as_ref()?.first_blocker.as_ref()
    }

    /// **The certification axis** — what this run left underived, as a verdict
    /// rather than a row. See [`crate::ledger::Uncertified`].
    ///
    /// Clean when there is no ledger, and that is not a papering-over: a
    /// rejected or declined file was never interpreted, so it owes nothing on
    /// this axis. The verdict about the *file* is the one that stands, and
    /// [`Verdict`] carries it.
    pub fn uncertified(&self) -> crate::ledger::Uncertified {
        self.ledger.as_ref().map(crate::ledger::Ledger::uncertified).unwrap_or_default()
    }

    /// **The certification axis's other half** — what this run recorded a
    /// refusal to translate. See [`crate::ledger::Untranslated`].
    ///
    /// Clean when there is no ledger, for the same reason as above and with the
    /// same force: a file mini declined at the frontend was never translated at
    /// all, and reporting *that* as untranslated debt would collapse the two
    /// senses of the word the whole design keeps apart.
    pub fn untranslated(&self) -> crate::ledger::Untranslated {
        self.ledger.as_ref().map(|l| l.untranslated.clone()).unwrap_or_default()
    }

    /// **Nothing owed on the certification axis** — both halves. The condition
    /// for exit 0 on an accepted file.
    ///
    /// **On the de-scheduled route the poly ledger is the axis**, and it is
    /// conjoined rather than substituted. `uncertified` and `untranslated` both
    /// read [`Outcome::ledger`], which is `None` under [`Options::poly`] — so
    /// without this conjunct `mini --poly` would exit 0 on every file by virtue
    /// of having run no scheduled pass, which is `DECISIONS.md`'s "SKIP is not
    /// PASS" with an exit code as the vehicle. [`crate::poly_run::PolyLedger::is_clean`]
    /// is what the de-scheduled route owes, and it is false today by a wide
    /// margin; when the route works it becomes true, and *that* is the verdict
    /// this strand was asked for.
    pub fn fully_certified(&self) -> bool {
        self.uncertified().is_clean()
            && self.untranslated().is_clean()
            && self.poly.as_ref().is_none_or(crate::poly_run::PolyLedger::is_clean)
    }
}

pub fn check_file(path: &Path) -> Outcome { check_file_with(path, Options::default()) }

pub fn check_file_with(path: &Path, opts: Options) -> Outcome {
    check_file_with_interp(path, opts, crate::interp::Interp::new()).0
}

/// [`check_file_with`] over a **caller-supplied** [`crate::interp::Interp`],
/// handed back beside the [`Outcome`] so the caller keeps the signature the
/// run grew. This is the mini half of the shared-environment seam
/// (ENV-UNIFY.md §3.3): a driver that builds one
/// [`nanoda_lib::tg::EnvCore`], hands `Interp::over(core)` here and installs
/// the same core with `nanoda_lib::tg::install_shared_core`, has both
/// engines minting into one kernel `Env` — their skeleton variables one
/// series, their W-type machine one machine. Behaviour is
/// [`check_file_with`]'s exactly; the only difference is who built the
/// `Interp` and who gets to keep it.
pub fn check_file_with_interp(
    path: &Path,
    opts: Options,
    ip: crate::interp::Interp,
) -> (Outcome, crate::interp::Interp) {
    let mut loaded = match convert::load_with(
        path,
        convert::LoadOptions {
            mutual: opts.mutual,
            nested: opts.nested,
            modelgen: opts.modelgen.clone(),
            ..Default::default()
        },
    ) {
        Ok(l) => l,
        Err(e) => {
            return (
                Outcome {
                    verdict: Verdict::Declined { reason: e.to_string() },
                    facts: Facts::default(),
                    census: Census::default(),
                    elim_audit: Vec::new(),
                    ledger: None,
                    poly: None,
                    dump: None,
                },
                ip,
            )
        }
    };
    let census = Census::of(&loaded.decls);
    let mut facts = loaded.facts.clone();
    // **Which of the file's non-standard axioms anything in the file refers
    // to** — over the *whole* file, which is why it is computed here and not
    // as the declarations stream past: an axiom unused at the point of
    // declaration may be used four hundred declarations later.
    // [`crate::unused_axiom`] states what "refers to" covers and why an unused
    // one may be ignored.
    let axioms = crate::unused_axiom::classify(&loaded.decls, |n| !convert::is_standard_axiom(n));
    let mut env = Environment::empty();
    let mut accepted = 0usize;
    for decl in &loaded.decls {
        if let Err(msg) = kernel::add(&mut env, decl) {
            // **A budget refusal is a decline.** See
            // [`crate::kernel::BUDGET_DECLINE`]: `reject` says the file is
            // ill-typed and `decline` says mini does not handle it, and
            // running out of recursion budget is the second. Classified here
            // because this is the one place a kernel-pass error becomes a
            // verdict.
            if msg.starts_with(crate::kernel::BUDGET_DECLINE) {
                return (
                    Outcome {
                        verdict: Verdict::Declined {
                            reason: format!("{} while checking {}", msg, decl.name()),
                        },
                        facts: loaded.facts,
                        census,
                        elim_audit: Vec::new(),
                        ledger: None,
                        poly: None,
                        dump: None,
                    },
                    ip,
                )
            }
            return (
                Outcome {
                    verdict: Verdict::Rejected { name: decl.name().to_string(), msg },
                    facts: loaded.facts,
                    census,
                    elim_audit: Vec::new(),
                    ledger: None,
                    poly: None,
                    dump: None,
                },
                ip,
            )
        }
        accepted += 1;
    }
    // **A user-declared axiom something in the file uses takes the file out of
    // scope.** Its inhabitation is not derivable in principle, so a run that
    // stops at the first missing derivation would stop there for ever;
    // `convert::is_standard_axiom` is where the line is drawn and why.
    //
    // *After* the kernel pass, not before, and the position is load-bearing:
    // four `bad/tutorial` fixtures declare a helper axiom ahead of the
    // ill-typed declaration they are about, and declining at the parser would
    // have turned four rejections into declines — a weaker claim, made
    // silently, on the axis that is supposed to be exact.
    if let Some(n) = axioms.used.first() {
        return (
            Outcome {
                verdict: Verdict::Declined { reason: format!("non-standard axiom: {n}") },
                facts: loaded.facts,
                census,
                elim_audit: Vec::new(),
                ledger: None,
                poly: None,
                dump: None,
            },
            ip,
        )
    }
    // **An unused one is ignored**, and the drop happens here — after the
    // kernel, before the interpretation pass — so that both halves are true at
    // once: its *type* is still checked, so a file declaring `axiom bad : (fun
    // x => x)` goes on being rejected exactly as mini-lean rejects it, and
    // nothing downstream ever sees the declaration, so it is not translated and
    // schedules no pair. `crate::unused_axiom` is the rule and the argument.
    //
    // The list is carried to [`Ledger::ignored_axioms`] below rather than
    // discarded: `#64`'s lesson is that a declaration with no scheduled pair is
    // invisible, and this one has none by construction.
    let ignored_axioms: Vec<String> = axioms.unused.iter().map(|n| n.to_string()).collect();
    if !axioms.unused.is_empty() {
        let drop: std::collections::HashSet<crate::expr::Name> =
            axioms.unused.iter().copied().collect();
        loaded.decls.retain(
            |d| !matches!(d, crate::env::Declaration::Axiom { name, .. } if drop.contains(name)),
        );
    }
    // The interpretation pass runs only on a file mini accepted: MINI-DESIGN
    // §0's two axes, kept apart.
    crate::blocker::arm(opts.block);
    let mut ip = ip;
    // Names for the dump have to be switched on *before* the pass, because the
    // registry is written as each constant is stored. Not by arming: arming
    // also stops at the first blocker, which would dump one pair.
    ip.set_labels_on(opts.dump.is_some());
    // **Step 6 of the mutual arc, and it is a substitution rather than an
    // install.** Every `mutual … end` block mini can encode is replaced, right
    // here, by an enumeration, one indexed inductive and a list of ordinary
    // definitions and theorems over it — under the block's *own* names. The
    // pass below then interprets those, and `⟦T.{σ}⟧`, `⟦T.ctor.{σ}⟧`,
    // `⟦T.rec.{σ}⟧` and the rule theorems land in the store at exactly the keys
    // every later use site reads. There is nothing to copy afterwards.
    //
    // A block the encoder declines stays as it was and `fill_declaration`
    // records its reason. `mini/src/mutual_aux.rs` is the whole of it, and that
    // module never names a `Term` or a `Thm`.
    //
    // **Step 3 of the nested arc runs first, and it is a *recognition* rather
    // than a substitution or an insertion.** A nested declaration's primitives
    // stay exactly where they are — the file's own theorems are checked by the ι
    // rules they carry — and its *model* is already in the file, put there by
    // the `modelgen` filter (`MODELGEN.md` §1), so all that is built here is the
    // side table saying which model constant carries `⟦T⟧`, `⟦T.ctorᵢ⟧` and
    // `⟦T.rec_k⟧`, and the σ those constants have to be interpreted at.
    // `mini/src/nested_splice.rs` says why the table cannot be a name rule.
    //
    // Before `expand` and not after: the model contains a `mutual … end` block
    // of its own, and the σ this pass propagates onto its members have to be in
    // the schedule `expand` reads.
    let sp = crate::nested_splice::recognise(&env, &loaded.decls, &loaded.schedule);
    facts.nested_models = sp.modelled;
    facts.nested_seen = sp.seen;
    // The tables go on the apparatus, which means building it — so only when
    // there is something to put there. A file with no nested declaration must
    // not acquire an apparatus it would otherwise never have had.
    if !sp.nested.is_empty() {
        if let Some(app) = ip.ind_apparatus() {
            app.model_of = sp.model_of;
            app.model_iota = sp.model_iota;
            app.nested = sp.nested;
        }
    }
    let ex = crate::mutual_aux::expand(&env, &loaded.decls, &sp.schedule);
    facts.mutual_blocks = ex.blocks;
    facts.mutual_encoded = ex.encoded;
    facts.mutual_rules = ex.rules;
    // **The de-scheduled route takes the whole pass or none of it** —
    // `LEVELPOLY.md` §5.3 step 1, and [`crate::poly_run`]'s header is the
    // argument for the exclusivity. The same `ex.decls` in the same order, so
    // the two reports name the same population; only the inner σ loop is gone,
    // which is the entire point.
    //
    // `elim_audit` and `dump` do not run beside it, and that is not an
    // oversight: both are instruments of the *scheduled* store —
    // `dump::render` is handed `ex.schedule` and `elim_audit` reads
    // interpretations keyed at ground σ — so pointing them at a pass that
    // filled neither would print emptiness as though it were a finding.
    if opts.poly {
        let led = crate::poly_run::run(&ex.env, &ex.decls, &mut ip);
        crate::blocker::arm(false);
        return (
            Outcome {
                verdict: Verdict::Accepted { declars: accepted },
                facts,
                census,
                elim_audit: Vec::new(),
                ledger: None,
                poly: Some(led),
                dump: None,
            },
            ip,
        )
    }
    let mut led = Ledger::run(&ex.env, &ex.decls, &ex.schedule, &mut ip);
    crate::blocker::arm(false);
    // **After the pass, not before**, and the order is a consequence of
    // [`crate::ledger::Ledger::run`] filling the store from the schedule.
    // `elim_audit` infers the types of a declaration's constructor fields, so
    // it *reads* the interpretation store; running it first made it a second,
    // unscheduled entry point into zone B, and the constants it pulled in were
    // built before the declaration walk had reached the declarations that own
    // them. Two exports showed it: `Bool` at `071`/`072` and `True` at `090`
    // were interpreted by the audit rather than by their own declaration. It
    // reads and does not mint now, which is what an oracle should do.
    let elim_audit = crate::zoneb::elim_audit(&env, &mut ip, &loaded.decls);
    let dump = opts
        .dump
        .as_ref()
        .map(|f| crate::dump::render(&mut ip, &ex.decls, &ex.schedule, f));
    // The same reason as the path below: `Ledger::run` is a function of the
    // declarations it was handed, and the ignored ones are precisely the ones
    // it was *not* handed. Recording them on the ledger is what keeps the skip
    // visible; the ledger never inferred it.
    led.ignored_axioms = ignored_axioms;
    // `Ledger::run` never learns the path; filling it here keeps the ledger a
    // function of the declarations alone.
    if let Some(b) = led.first_blocker.as_mut() {
        b.export = path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    }
    (
        Outcome {
            verdict: Verdict::Accepted { declars: accepted },
            facts,
            census,
            elim_audit,
            ledger: Some(led),
            poly: None,
            dump,
        },
        ip,
    )
}

/// `check_file` on a thread with a large stack. `whnf` and `inferType` are
/// mutually recursive over the term structure with no depth limit, exactly as
/// in mini-lean, and `checker` does the same thing for the same reason.
pub fn check_file_deep(path: &Path) -> Outcome {
    check_file_deep_with(path, Options::default())
}

pub fn check_file_deep_with(path: &Path, opts: Options) -> Outcome {
    const STACK_SIZE: usize = 256 * 1024 * 1024;
    let p = path.to_path_buf();
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || check_file_with(&p, opts))
        .expect("spawn")
        .join()
        .expect("mini panicked")
}
