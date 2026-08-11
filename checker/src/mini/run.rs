//! One export file, one verdict.
//!
//! # Interface
//!
//! [`check_file`] is the library entry point used by the checker binary and
//! its former-mini regression tests. It reproduces `Main.lean`'s `runKernel`
//! in its strict (non-`--liberal`)
//! mode: declarations in file order, the first rejection ends the run.
//!
//! **The pipeline is: parse, schedule, then one per-declaration loop.** In the
//! default checker, each declaration is dispatched exactly once: inductive
//! constructions to the former mini implementation, all other declarations
//! to nanoda. `--naive` selects the historical mini-only policy, including its
//! unused-axiom filtering. There is no whole-file acceptance pass and no
//! whole-file interpretation pass.
//! [`crate::mini::decl_pass`] is the loop body and carries the argument for each of
//! the orderings that had to be answered to fuse them, and
//! [`Outcome::prefix`] is what the fusion buys: on a mid-file stop, everything
//! before the stop is certified.
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
//! ([`crate::mini::ledger::Untranslated`], exit 4) and must never move a file into
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
//! **In `--naive`, the second cause needs the axiom to be *used*.** A
//! non-standard axiom nothing in the file refers to is ignored, so it is not
//! translated and schedules no pair, and is named in
//! [`crate::mini::ledger::Ledger::ignored_axioms`] so the skip is visible.
//! [`crate::mini::unused_axiom`] is the rule, the argument that it is a narrowing
//! rather than a reversal, and the enumeration of what "refers to" covers.
//! The default checker does not apply this mini-only filter: every axiom is an
//! ordinary declaration and is dispatched to nanoda.
//!
//! [`Options::block`] adds the blocking mode of MINI-DESIGN.md §0.6. It is not
//! a verdict either: a blocked file was *accepted*, and the report says which
//! `(declaration, σ)` the evidence axis stopped at.

use crate::mini::census::Census;
use crate::mini::ledger::Ledger;
use crate::mini::convert::{self, Facts};
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
    /// **Dump the stored context** after the pass — [`crate::mini::dump`]. Not a
    /// verdict and not a mode: the same run happens, and the store is read at
    /// the end. `None` is off; `Some(filter)` narrows it.
    pub dump: Option<crate::mini::dump::Filter>,
    /// **Take a `mutual … end` block** instead of declining the file at the
    /// parser. Off by default: the mutual decline is part of the arena's exit-2
    /// contract and `crate::mini::convert::LoadOptions` says why lifting it is a
    /// separate, deliberate step. A file taken this way is *accepted* and its
    /// whole block is untranslated — exit 4, not exit 0.
    pub mutual: bool,
    /// **Take a nested inductive** instead of declining the file at the
    /// parser. A second gate, off by default, and separate from `mutual` for
    /// the reason [`crate::mini::convert::LoadOptions::nested`] gives: a nested
    /// declaration is accepted by specialising it into a mutual block and
    /// *restoring* the result, and the restoration is a rewrite along an
    /// isomorphism the acceptance axis does not check.
    pub nested: bool,
    /// **Run the export through the `modelgen` filter before parsing it** —
    /// [`crate::mini::modelgen`]. `Off` here and on in `mini`'s command line; the
    /// module header says why the two differ and what happens on a machine
    /// with no Lean toolchain.
    pub modelgen: crate::mini::modelgen::Filter,
    /// **Route each declaration group to one engine** (ENV-UNIFY.md §5
    /// track D, [`crate::mini::route`]): `None` is the historical mini-only run;
    /// `Some(mode)` replaces the evidence pass with the interleaved routed
    /// driver, both engines over this run's one core. A routed run installs
    /// the core as the checker's per-thread signature, so it owns its thread:
    /// one routed file per thread, which [`check_file_deep_with`] provides.
    pub route: Option<crate::mini::route::Mode>,
}

pub struct Outcome {
    pub verdict: Verdict,
    pub facts: Facts,
    /// Which §6.2 clauses this file's declarations spend their nodes on —
    /// how the remaining threading work is sized.
    pub census: Census,
    /// One row per inductive with an exported recursor: the computed
    /// eliminator class against the recursor's own. See
    /// [`crate::mini::zoneb::elim_audit`].
    pub elim_audit: Vec<String>,
    /// What `⟦·⟧` actually reached, per `(declaration, σ)`, attributed by
    /// cause. `None` when the file was declined or rejected: a gap ledger for
    /// a file mini did not accept would mix the two axes.
    pub ledger: Option<Ledger>,
    /// **How far the evidence pass got before the run stopped** — see
    /// [`crate::mini::decl_pass::Prefix`].
    ///
    /// Present on *every* outcome, including a rejected one, and that is the
    /// whole point: the pipeline is one per-declaration loop now, so a file
    /// that stops at declaration `k` has certified everything before `k`. It is
    /// three counters and not a ledger, so a rejected file still owes nothing
    /// on the certification axis and [`Outcome::uncertified`] still answers
    /// clean for it.
    pub prefix: crate::mini::decl_pass::Prefix,
    /// The stored-context dump, when [`Options::dump`] asked for one.
    ///
    /// A `String`, and rendered inside the worker, for the reason
    /// [`crate::mini::blocker::Blocker`] is: the `Interp` is `Rc`-backed and does not
    /// cross the thread join, so the only place it can be read is where it
    /// lives.
    pub dump: Option<String>,
    /// The routing ledger, when [`Options::route`] asked for a routed run:
    /// who got what, any export anchors left unclaimed, and the shared stores'
    /// evidence reports. `None` on an unrouted run and on a file that was
    /// declined or rejected before the evidence pass.
    pub route: Option<crate::mini::route::RouteReport>,
}

impl Outcome {
    /// The first blocker, when the run was asked to stop at one.
    pub fn blocker(&self) -> Option<&crate::mini::blocker::Blocker> {
        self.ledger.as_ref()?.first_blocker.as_ref()
    }

    /// **The certification axis** — what this run left underived, as a verdict
    /// rather than a row. See [`crate::mini::ledger::Uncertified`].
    ///
    /// Clean when there is no ledger, and that is not a papering-over: a
    /// rejected or declined file was never interpreted, so it owes nothing on
    /// this axis. The verdict about the *file* is the one that stands, and
    /// [`Verdict`] carries it.
    pub fn uncertified(&self) -> crate::mini::ledger::Uncertified {
        self.ledger.as_ref().map(crate::mini::ledger::Ledger::uncertified).unwrap_or_default()
    }

    /// **The certification axis's other half** — what this run recorded a
    /// refusal to translate. See [`crate::mini::ledger::Untranslated`].
    ///
    /// Clean when there is no ledger, for the same reason as above and with the
    /// same force: a file mini declined at the frontend was never translated at
    /// all, and reporting *that* as untranslated debt would collapse the two
    /// senses of the word the whole design keeps apart.
    pub fn untranslated(&self) -> crate::mini::ledger::Untranslated {
        self.ledger.as_ref().map(|l| l.untranslated.clone()).unwrap_or_default()
    }

    /// **Nothing owed on the certification axis** — both halves. The condition
    /// for exit 0 on an accepted file.
    pub fn fully_certified(&self) -> bool {
        self.uncertified().is_clean() && self.untranslated().is_clean()
    }
}

pub fn check_file(path: &Path) -> Outcome { check_file_with(path, Options::default()) }

pub fn check_file_with(path: &Path, opts: Options) -> Outcome {
    check_file_with_interp(path, opts, crate::mini::interp::Interp::new()).0
}

/// [`check_file_with`] over a **caller-supplied** [`crate::mini::interp::Interp`],
/// handed back beside the [`Outcome`] so the caller keeps the signature the
/// run grew. This is the mini half of the shared-environment seam
/// (ENV-UNIFY.md §3.3): a driver that builds one
/// [`crate::tg::EnvCore`], hands `Interp::over(core)` here and installs
/// the same core with `crate::tg::install_shared_core`, has both
/// engines minting into one kernel `Env` — their skeleton variables one
/// series, their W-type machine one machine. Behaviour is
/// [`check_file_with`]'s exactly; the only difference is who built the
/// `Interp` and who gets to keep it.
pub fn check_file_with_interp(
    path: &Path,
    opts: Options,
    ip: crate::mini::interp::Interp,
) -> (Outcome, crate::mini::interp::Interp) {
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
                    prefix: crate::mini::decl_pass::Prefix::default(),
                    dump: None,
                    route: None,
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
    // [`crate::mini::unused_axiom`] states what "refers to" covers and why an unused
    // one may be ignored. It reads the declaration list and no environment, so
    // it belongs ahead of the loop.
    let axioms = crate::mini::unused_axiom::classify(&loaded.decls, |n| !convert::is_standard_axiom(n));
    // **An unused one is ignored**, and the drop happens *before* the loop, so
    // the declaration is never added and never interpreted.
    //
    // It used to be dropped after the kernel pass so that its *type* was still
    // checked, and a file declaring `axiom bad : (fun x => x)` and referring to
    // it nowhere was rejected for it. **The owner waived that property
    // explicitly** — "yes, it will not complain about the type of a dropped
    // axiom; that's not a concern" — and it is the one behaviour this
    // restructure gives up.
    //
    // The list is carried to [`Ledger::ignored_axioms`] below rather than
    // discarded: `#64`'s lesson is that a declaration with no scheduled pair is
    // invisible, and this one has none by construction.
    let naive = opts.route.is_none();
    let ignored_axioms: Vec<String> = if naive {
        axioms.unused.iter().map(|n| n.to_string()).collect()
    } else {
        Vec::new()
    };
    // `--naive` preserves mini's historical unused-axiom policy. The unified
    // checker dispatches every axiom to nanoda like every other ordinary
    // declaration; dropping one here would mean the one declaration loop never
    // made a decision for it.
    if naive && !axioms.unused.is_empty() {
        let drop: std::collections::HashSet<crate::mini::expr::Name> =
            axioms.unused.iter().copied().collect();
        loaded.decls.retain(
            |d| !matches!(d, crate::mini::env::Declaration::Axiom { name, .. } if drop.contains(name)),
        );
    }
    // **A user-declared axiom something in the file *uses* takes the file out
    // of scope.** Its inhabitation is not derivable in principle, so a run that
    // stops at the first missing derivation would stop there for ever;
    // `convert::is_standard_axiom` is where the line is drawn and why.
    //
    // That decline is issued *after* the loop, and the position is
    // load-bearing: four `bad/tutorial` fixtures (044, 047, 050, 054) declare a
    // helper axiom ahead of the ill-typed declaration they are about, and
    // declining first would turn four rejections into declines — a weaker
    // claim, made silently, on the axis that is supposed to be exact. So the
    // file is checked to the end and *then* declined; the evidence half is
    // switched off for it, which is what it always was on this path.
    let declining = naive && !axioms.used.is_empty();
    crate::mini::blocker::arm(opts.block);
    let mut ip = ip;
    // Names for the dump have to be switched on *before* the pass, because the
    // registry is written as each constant is stored. Not by arming: arming
    // also stops at the first blocker, which would dump one pair.
    ip.set_labels_on(opts.dump.is_some());
    // **The routing seam** (ENV-UNIFY.md §5 track D), chosen once and then
    // stepped once per declaration. Unrouted, each step is the walk it has
    // always been. Routed, `crate::mini::route`'s interleaved driver takes it: same
    // declarations, same schedule, same `Interp` — each group walked by the
    // engine the policy picks, the checker driven over the same core in the
    // same walk. One loop, a policy choice inside it.
    let mut driver = crate::mini::route::Driver::new(
        &mut ip,
        opts.route,
        loaded.checker_schedule.clone(),
    );
    let mut pass = crate::mini::decl_pass::Pass::new(&loaded.decls, &loaded.schedule, !declining);
    let mut stopped: Option<Verdict> = None;
    for decl in &loaded.decls {
        match pass.step(decl, &mut ip, &mut driver) {
            crate::mini::decl_pass::Step::Continue => {}
            crate::mini::decl_pass::Step::Rejected { name, msg } => {
                stopped = Some(Verdict::Rejected { name, msg });
                break
            }
            crate::mini::decl_pass::Step::Declined { reason } => {
                stopped = Some(Verdict::Declined { reason });
                break
            }
        }
    }
    if stopped.is_none() {
        pass.end(&mut ip, &mut driver);
    }
    crate::mini::blocker::arm(false);
    let prefix = pass.prefix();
    facts.nested_models = pass.nested_models;
    facts.nested_seen = pass.nested_seen;
    facts.mutual_blocks = pass.mutual_blocks();
    facts.mutual_encoded = pass.mutual_encoded();
    facts.mutual_rules = pass.mutual_rules();
    // **The stop wins over the used-axiom decline**, and the loop ran to the
    // declaration that caused it. The certified prefix is on the outcome; the
    // ledger is not, for MINI-DESIGN.md §0's reason.
    let stopped = stopped.or_else(|| {
        declining.then(|| Verdict::Declined {
            reason: format!("non-standard axiom: {}", axioms.used[0]),
        })
    });
    if let Some(verdict) = stopped {
        // No route report either, and for the ledger's reason: its dispatch
        // counts and end-of-run store observations describe a completed pass
        // over a file the selected checker accepted.
        drop(driver);
        return (
            Outcome {
                verdict,
                facts,
                census,
                elim_audit: Vec::new(),
                ledger: None,
                prefix,
                dump: None,
                route: None,
            },
            ip,
        )
    }
    let (blocked, accepted) = (pass.blocked, pass.accepted);
    let route_report = driver.finish(&mut ip, &mut pass.led, blocked);
    // `env` is the accepted syntactic environment and not the evidence pass's, which is the
    // distinction `elim_audit` needs: it is an oracle over the file's own
    // inductives, and an encoded block's members are definitions in the other
    // one.
    let crate::mini::decl_pass::Pass { env, xdecls, schedule, mut led, .. } = pass;
    // **After the loop, not inside it**, and the order is a consequence of the
    // evidence walk filling the store from the schedule.
    // `elim_audit` infers the types of a declaration's constructor fields, so
    // it *reads* the interpretation store; running it first made it a second,
    // unscheduled entry point into zone B, and the constants it pulled in were
    // built before the declaration walk had reached the declarations that own
    // them. Two exports showed it: `Bool` at `071`/`072` and `True` at `090`
    // were interpreted by the audit rather than by their own declaration. It
    // reads and does not mint now, which is what an oracle should do.
    let elim_audit = crate::mini::zoneb::elim_audit(&env, &mut ip, &loaded.decls);
    let dump = opts.dump.as_ref().map(|f| crate::mini::dump::render(&mut ip, &xdecls, &schedule, f));
    // The same reason as the path below: the walk is a function of the
    // declarations it was handed, and the ignored ones are precisely the ones
    // it was *not* handed. Recording them on the ledger is what keeps the skip
    // visible; the ledger never inferred it.
    led.ignored_axioms = ignored_axioms;
    // The walk never learns the path; filling it here keeps the ledger a
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
            prefix,
            dump,
            route: route_report,
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
