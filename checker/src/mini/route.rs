//! Track D — per-declaration routing between the two engines
//! (ENV-UNIFY.md §5 track D): the policy function, the narrow engine seam,
//! and the interleaved driver.
//!
//! # Interface
//!
//! ```text
//! Mode::Split                                 the production policy
//! Mode::pick(&Declaration) -> Pick            the policy function
//! trait GroupEngine                           one group in, a report out
//! Driver::{accept, evidence}                  the per-group driver, called
//!                                             from decl_pass::Pass
//! ```
//!
//! # The policy
//!
//! [`Mode::Split`] is the owner's split (ENV-UNIFY.md §3.6): the inductive
//! constructions — inductives, mutual blocks, and the quotient family — go
//! to mini, whose certificate-producing constructions live there
//! (`quot_classes.rs`, the `IndApparatus`); axioms, definitions, and theorems
//! go to nanoda, whose cached dispatch is the
//! measured escape from the matcher wall (MATCHER-WALL.md: mini at 121–302×
//! the reference on three matcher closures, with its own type checker at
//! 1.58% of the run — the cost is evidence, and the checker's evidence path
//! is the cheap one on the def population). The historical whole-file mini
//! checker is a separate `Driver::Plain` selected by `--naive`; it never adds
//! another pass to the split run.
//!
//! # The routing unit is the group, on both sides
//!
//! Mini's [`Declaration`] already is the group — constructors ride inside
//! `Inductive`, recursors are generated, `Quot` is one declaration. The
//! checker's export entries are finer, and
//! `crate::routed::RoutedChecker` buckets them by **route anchor**
//! (constructors and recursors follow their inductive, the quotient family
//! follows `Quot`), so one routing decision covers one group on either side.
//!
//! # One decision means no fallback
//!
//! Mini *declines* — budget bounds, unsupported shapes — and records the
//! refusal ([`crate::mini::ledger::Untranslated`]). The checker *gaps* — its
//! certificates carry counted incompletenesses (`tg::global_report`). The
//! two never net and never trigger a second engine. A mini decline remains
//! untranslated certification debt. A missing checker anchor is an invariant
//! failure. At end, unclaimed export anchors are reported but not checked by a
//! repair sweep.
//!
//! # What routing governs in this stage, exactly
//!
//! The dispatch owns both acceptance and evidence. Mini checks inductive
//! constructions; nanoda checks all ordinary declarations and emits their TG
//! evidence in the same call. A nanoda-accepted declaration is copied without
//! re-checking into mini's syntactic environment solely so later mini-owned
//! inductives can refer to it. On inductives, one known asymmetry is recorded
//! rather than hidden (ENV-UNIFY.md §3.8,
//! `checker/src/routed.rs` header): the export's recursor entries of a
//! mini-routed inductive are covered by mini's load-time shape comparison,
//! not the checker's full mint-and-compare.

use std::collections::HashMap;

use crate::mini::env::{DefKind, Declaration, Environment};
use crate::mini::expr::Name;
use crate::mini::interp::Interp;
use crate::mini::ledger::Ledger;

/// The production routing policy. The historical mini-only checker is
/// represented by [`Driver::Plain`], not by a second routing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The owner's split: constructions to mini; axioms, definitions,
    /// theorems, and opaque definitions to nanoda.
    Split,
}

/// Which engine a group goes to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pick {
    Mini,
    Checker,
}

/// The group kinds the policy distinguishes. A [`Declaration::Mutual`] block
/// is an inductive construction; the `DefKind`s are told apart because a
/// future policy may want to split them (an `opaque` has no defining
/// equation to certify), not because today's does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Inductive,
    Quotient,
    Definition,
    Theorem,
    Opaque,
    Axiom,
}

impl DeclKind {
    pub fn of(d: &Declaration) -> DeclKind {
        match d {
            Declaration::Inductive { .. } | Declaration::Mutual { .. } => DeclKind::Inductive,
            Declaration::Quot => DeclKind::Quotient,
            Declaration::Axiom { .. } => DeclKind::Axiom,
            Declaration::Def { kind: DefKind::Def, .. } => DeclKind::Definition,
            Declaration::Def { kind: DefKind::Theorem, .. } => DeclKind::Theorem,
            Declaration::Def { kind: DefKind::Opaque, .. } => DeclKind::Opaque,
        }
    }
}

impl Mode {
    /// **The policy function**: one declaration group in, one engine out.
    /// Everything the driver routes goes through here — there is no second
    /// place a routing decision is made.
    pub fn pick(self, d: &Declaration) -> Pick {
        match self {
            Mode::Split => match DeclKind::of(d) {
                DeclKind::Inductive | DeclKind::Quotient => Pick::Mini,
                DeclKind::Definition
                | DeclKind::Theorem
                | DeclKind::Opaque
                | DeclKind::Axiom => Pick::Checker,
            },
        }
    }
}

/// What nanoda reports after accepting and producing evidence for one group.
/// The evidence itself lands in the shared constant store on
/// [`crate::tg::EnvCore`]; this value distinguishes a type error from a broken
/// route-anchor invariant.
#[derive(Debug, Default)]
pub struct GroupReport {
    /// `no-export-group` when the declaration loop has no matching export
    /// anchor. Empty means nanoda took the group; *taken* still admits counted
    /// TG gaps, which remain on nanoda's evidence ledger.
    pub declined: Vec<String>,
    /// A type-check rejection. This is distinct from an evidence decline: the
    /// declaration did not enter either syntactic environment.
    pub rejected: Option<String>,
}

/// **The narrow engine seam**: a declaration group in; what landed in the
/// shared store, and the gap/decline ledger, out. Nothing about dispatch,
/// `whnf` or `def_eq` crosses this trait — each engine keeps its own, which
/// is what keeps the two independently refutable and the differential oracle
/// meaningful (the risk ENV-UNIFY.md §3.3 names is exactly a wider trait
/// dragging both onto one reduction strategy).
pub trait GroupEngine {
    fn check_group(&mut self, d: &Declaration) -> GroupReport;
}

/// The checker as a [`GroupEngine`]: the export's entries for the group's
/// names, each checked at every scheduled instantiation.
struct CheckerEngine<'x, 'p> {
    rc: crate::routed::RoutedChecker<'x, 'p>,
}

/// Every name a group covers on the checker side — one for everything except
/// a `mutual` block, whose members are separate export anchors.
fn group_names(d: &Declaration) -> Vec<Name> {
    match d {
        Declaration::Mutual { types, .. } => types.iter().map(|t| t.name).collect(),
        _ => vec![d.name()],
    }
}

impl GroupEngine for CheckerEngine<'_, '_> {
    fn check_group(&mut self, d: &Declaration) -> GroupReport {
        let mut missing = Vec::new();
        for n in group_names(d) {
            let result = crate::panic_capture::catch_silent(|| self.rc.check_anchor(&n.to_string()));
            match result {
                Ok(Some(_)) => {}
                Ok(None) => missing.push(n.to_string()),
                Err(payload) => {
                    let msg = crate::panic_capture::message(payload.as_ref());
                    return GroupReport {
                        declined: Vec::new(),
                        rejected: Some(msg),
                    }
                }
            }
        }
        GroupReport {
            declined: missing.into_iter().map(|n| format!("no-export-group:{n}")).collect(),
            rejected: None,
        }
    }
}

/// The routed run's own ledger: who got what, which export anchors the single
/// loop did not claim, and what the shared evidence stores observed.
#[derive(Debug)]
pub struct RouteReport {
    pub mode: Mode,
    /// Groups the policy sent to each engine.
    pub to_mini: usize,
    pub to_checker: usize,
    /// Export anchors no declaration-loop dispatch claimed. Observed only;
    /// never repaired by a post-loop validation pass.
    pub unclaimed: Vec<String>,
    /// The shared constant store's crossing report at end of run — the
    /// measurement ENV-UNIFY.md B4 exists to produce, under routing.
    pub cross: String,
    /// The checker's global evidence report (`tg::global_report`), the gap
    /// column of the checker's half.
    pub tg: String,
    /// The shared lambda mint's report at end of run — how many `lam` symbols
    /// exist, who minted each, and how many lookups one engine answered from
    /// the other's mint. The measurement that distinguishes the one-lambda
    /// merge from a rename.
    pub lam: String,
    /// The shared dependent-product mint's report, the same measurement for
    /// `Π`. Separate from [`RouteReport::lam`] because the two merges have
    /// very different residues and averaging them would hide that: λ's
    /// one-sided shapes are genuine divergence, Π's were the same skeleton
    /// under two symbols.
    pub pi: String,
}

impl RouteReport {
    fn new(mode: Mode) -> RouteReport {
        RouteReport {
            mode,
            to_mini: 0,
            to_checker: 0,
            unclaimed: Vec::new(),
            cross: String::new(),
            tg: String::new(),
            lam: String::new(),
            pi: String::new(),
        }
    }

    /// The one-line row the measurement runs scrape, shaped like the
    /// ledger's rows (`k=v`, tab-separated).
    pub fn row(&self) -> String {
        let mut s = format!(
            "route\tmode={:?}\ttoMini={}\ttoChecker={}\tunclaimed={}",
            self.mode,
            self.to_mini,
            self.to_checker,
            self.unclaimed.len(),
        );
        for n in &self.unclaimed {
            s.push_str(&format!("\tunclaimed:{n}"));
        }
        s
    }
}

/// The trait is the seam: both engines are driven through it and only
/// through it.
fn via(e: &mut dyn GroupEngine, d: &Declaration) -> GroupReport { e.check_group(d) }

/// **The evidence pass, one declaration at a time** —
/// [`crate::mini::decl_pass::Pass`]'s other half.
///
/// [`Driver::Plain`] is the historical mini-only walk, [`Driver::Routed`] the
/// interleaved routed one. They are the *same loop* with a policy choice
/// inside: `run.rs` builds one of these before the per-declaration loop and
/// calls [`Driver::accept`] and then [`Driver::evidence`] once per declaration
/// either way. There is no second driver beside the first.
///
/// Interleaving, not two passes, is what makes crossings observable in both
/// directions: a checker-routed definition can adopt the inductive
/// interpretation mini published two declarations earlier, and a mini-routed
/// construction can adopt a def entry the checker published — within one
/// walk of one file.
pub(crate) enum Driver {
    Plain,
    Routed(Box<Routed>),
}

/// [`Driver::Routed`]'s state: the checker engine and dispatch report.
pub(crate) struct Routed {
    mode: Mode,
    chk: Option<CheckerEngine<'static, 'static>>,
    report: RouteReport,
}

impl Driver {
    /// Build the driver the run's options ask for, before the loop.
    ///
    /// A routed run installs the caller's core as the checker's per-thread
    /// core, so it must run on a thread where no `TgBackend` has been built
    /// yet (one routed file per thread; `run.rs`'s deep-thread wrapper and
    /// the tests both give it that).
    pub(crate) fn new(
        ip: &mut Interp,
        mode: Option<Mode>,
        schedule: std::sync::Arc<crate::instantiations::Instantiations>,
    ) -> Driver {
        // The armed-blocker labels, before any walk — [`Ledger::run`]'s first
        // statement, and the routed driver's, hoisted to the one place both
        // paths now start from.
        Ledger::arm_labels(ip);
        let Some(mode) = mode else { return Driver::Plain };
        let report = RouteReport::new(mode);
        // **One parse** (the comprehensive-merge's first stage): the checker is
        // driven over the very `ExportFile` mini's load installed as this
        // thread's arena — one file, one arena, one `NameKey` identity. This is
        // not only economy: under the `modelgen` filter the export mini checked
        // exists only in memory, so the re-parse this replaced would have handed
        // the two engines two genuinely different files. An absent installation
        // is retained as `None` and reported as a routing invariant failure when
        // the loop first dispatches an ordinary declaration.
        let ef = crate::mini::arena::installed_export_file();
        crate::tg::install_shared_core(ip.core().clone());
        let chk = ef.map(|ef| CheckerEngine {
            rc: crate::routed::RoutedChecker::new(ef, schedule),
        });
        Driver::Routed(Box::new(Routed { mode, chk, report }))
    }

    /// Type-check one declaration group through exactly one engine and install
    /// the accepted syntax in mini's environment for later inductive groups.
    /// The returned pick is the same dispatch decision the evidence phase uses;
    /// there is no second policy lookup.
    pub(crate) fn accept(
        &mut self,
        env: &mut Environment,
        d: &Declaration,
    ) -> Result<Pick, String> {
        match self {
            Driver::Plain => {
                crate::mini::kernel::add(env, d)?;
                Ok(Pick::Mini)
            }
            Driver::Routed(r) => r.accept(env, d),
        }
    }

    /// Produce evidence for the decision already returned by [`Self::accept`].
    /// Nanoda produced TG evidence while it accepted a checker-routed group, so
    /// that arm is intentionally empty; running it again would be a second pass.
    pub(crate) fn evidence(
        &mut self,
        pick: Pick,
        env: &Environment,
        schedule: &HashMap<Name, Vec<Vec<u32>>>,
        ip: &mut Interp,
        led: &mut Ledger,
        d: &Declaration,
    ) -> bool {
        match pick {
            Pick::Mini => led.walk_decl(env, d, schedule, ip),
            Pick::Checker => false,
        }
    }

    /// The end of the walk. `blocked` is the armed blocker's flag: a blocked
    /// run's counters are partial by design and [`Ledger::finish`] is not
    /// called, exactly as [`Ledger::run`]'s early return left them.
    pub(crate) fn finish(
        self,
        ip: &mut Interp,
        led: &mut Ledger,
        blocked: bool,
    ) -> Option<RouteReport> {
        match self {
            Driver::Plain => {
                if !blocked {
                    led.finish(ip);
                }
                None
            }
            Driver::Routed(r) => Some(r.finish(ip, led, blocked)),
        }
    }
}

impl Routed {
    fn accept(
        &mut self,
        env: &mut Environment,
        d: &Declaration,
    ) -> Result<Pick, String> {
        let pick = self.mode.pick(d);
        match pick {
            Pick::Mini => {
                self.report.to_mini += 1;
                crate::mini::kernel::add(env, d)?;
                if let Some(c) = self.chk.as_mut() {
                    for n in group_names(d) {
                        c.rc.claim_anchor(&n.to_string());
                    }
                }
            }
            Pick::Checker => {
                self.report.to_checker += 1;
                let c = self
                    .chk
                    .as_mut()
                    .ok_or_else(|| {
                        "routing invariant: the shared export file is not installed".to_string()
                    })?;
                let rep = via(c, d);
                if let Some(msg) = rep.rejected {
                    return Err(msg)
                }
                if !rep.declined.is_empty() {
                    return Err(format!(
                        "routing invariant: nanoda has no export group for {} ({})",
                        d.name(),
                        rep.declined.join(", ")
                    ))
                }
                crate::mini::kernel::install_checked_noninductive(env, d)
                    .map_err(|e| format!("routing invariant: {e}"))?;
            }
        }
        Ok(pick)
    }

    fn finish(mut self, ip: &mut Interp, led: &mut Ledger, blocked: bool) -> RouteReport {
        if !blocked {
            led.finish(ip);
        }
        // Observe missed dispatches even when mini's evidence blocker fired,
        // but never repair them with a second checker sweep: one group gets
        // one validation in the main loop.
        if let Some(c) = self.chk.as_mut() {
            self.report.unclaimed = c.rc.unclaimed();
        }
        self.report.cross = ip.core().consts().borrow().report();
        self.report.lam = ip.core().lams().borrow().report();
        self.report.pi = ip.core().pis().borrow().report();
        self.report.tg = crate::tg::global_report();
        self.report
    }
}
