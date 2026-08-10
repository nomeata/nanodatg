//! Track D — per-declaration routing between the two engines
//! (ENV-UNIFY.md §5 track D): the policy function, the narrow engine seam,
//! and the interleaved driver.
//!
//! # Interface
//!
//! ```text
//! Mode::{Split, ForceMini, ForceChecker}      the flag
//! Mode::pick(&Declaration) -> Pick            the policy function
//! trait GroupEngine                           one group in, a report out
//! run_routed(...)                             the driver, called from
//!                                             run::check_file_with_interp
//!                                             when Options::route is set
//! ```
//!
//! # The policy
//!
//! [`Mode::Split`] is the owner's split (ENV-UNIFY.md §3.6): the inductive
//! constructions — inductives, mutual blocks, the quotient family — and
//! axioms go to mini, whose certificate-producing constructions live there
//! (`quot_classes.rs`, the `IndApparatus`, the axiom inhabitation clauses);
//! definitions and theorems go to the checker, whose cached dispatch is the
//! measured escape from the matcher wall (MATCHER-WALL.md: mini at 121–302×
//! the reference on three matcher closures, with its own type checker at
//! 1.58% of the run — the cost is evidence, and the checker's evidence path
//! is the cheap one on the def population). [`Mode::ForceMini`] and
//! [`Mode::ForceChecker`] force one engine for everything, so the historical
//! single-engine runs stay reachable and the two stay comparable — and with
//! one `Env` under both, comparable as *objects*: the differential oracle.
//!
//! # The routing unit is the group, on both sides
//!
//! Mini's [`Declaration`] already is the group — constructors ride inside
//! `Inductive`, recursors are generated, `Quot` is one declaration. The
//! checker's export entries are finer, and
//! `nanoda_lib::routed::RoutedChecker` buckets them by **route anchor**
//! (constructors and recursors follow their inductive, the quotient family
//! follows `Quot`), so one routing decision covers one group on either side.
//!
//! # The asymmetry: mini declines, the checker gaps
//!
//! Mini *declines* — budget bounds, unsupported shapes — and records the
//! refusal ([`crate::ledger::Untranslated`]). The checker *gaps* — its
//! certificates carry counted incompletenesses (`tg::global_report`). The
//! two never net: a mini decline on a routed group **falls back to the
//! checker as a counted, named event** ([`RouteReport::fallbacks_to_checker`]),
//! and a checker-routed name the export never saw (an encoder-generated
//! declaration) falls back to mini the same way
//! ([`RouteReport::fallbacks_to_mini`]). Groups no decision ever covered are
//! swept, checked and *named* ([`RouteReport::strays`]) — nothing is ever
//! silently unvalidated, and nothing silently swallowed.
//!
//! # What routing governs in this stage, exactly
//!
//! The **evidence axis**: who interprets a group's constants, derives its
//! certificates and publishes them into the shared store — and, for
//! checker-routed groups, the checker's own acceptance check. Mini's zone A
//! still checks the whole file first (`kernel::add`, measured at 1.58% of a
//! mini run), because mini's `Environment` is grown by checking and the
//! shared *syntactic* store that would let one engine's check stand for the
//! other's is track A, not landed. So under [`Mode::Split`] acceptance is
//! dual on defs (mini's kernel and the checker both check them; the checker's
//! panic is the routed run's rejection) and mini-only on inductives — where
//! one known asymmetry is recorded rather than hidden (ENV-UNIFY.md §3.8,
//! `checker/src/routed.rs` header): the export's recursor entries of a
//! mini-routed inductive are covered by mini's load-time shape comparison,
//! not the checker's full mint-and-compare.

use std::collections::{HashMap, HashSet};

use crate::env::{DefKind, Declaration, Environment};
use crate::expr::Name;
use crate::interp::Interp;
use crate::ledger::{Ledger, Untranslated};

/// The routing flag: the policy split, or one engine forced for everything.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The owner's split: constructions to mini, defs and theorems to the
    /// checker.
    Split,
    /// Everything to mini — the historical `mini` run, reachable for
    /// comparison (and the degraded mode when the checker cannot parse).
    ForceMini,
    /// Everything to the checker — the historical `nanoda` run over the
    /// shared core, reachable for comparison.
    ForceChecker,
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
            Mode::ForceMini => Pick::Mini,
            Mode::ForceChecker => Pick::Checker,
            Mode::Split => match DeclKind::of(d) {
                DeclKind::Inductive | DeclKind::Quotient | DeclKind::Axiom => Pick::Mini,
                DeclKind::Definition | DeclKind::Theorem | DeclKind::Opaque => Pick::Checker,
            },
        }
    }
}

/// What one engine reports for one group. The interpretations and the
/// certificates themselves land in the shared constant store on the
/// [`nanoda_lib::tg::EnvCore`] — the return value is the **ledger**, in the
/// type from the start, because the counts are the measurement this whole
/// seam exists to produce.
#[derive(Debug, Default)]
pub struct GroupReport {
    /// Units of checking done: `(declaration, σ)` pairs walked (mini) or
    /// scheduled declaration-instantiation checks run (checker).
    pub checked: usize,
    /// The engine refused (part of) the group, by reason — mini's decline
    /// vocabulary ([`crate::ledger::Ledger::key`]), or `no-export-group` from
    /// the checker for a name the export never saw. Empty means the group
    /// was taken; *taken* still admits counted gaps, which stay on each
    /// engine's own gap ledger and are never folded into this field.
    pub declined: Vec<String>,
    /// The armed blocker stopped the run (mini only) — the driver must walk
    /// nothing further, like [`Ledger::run`]'s early return.
    pub blocked: bool,
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

/// Mini as a [`GroupEngine`]: the ledger walk, one declaration at a time.
struct MiniEngine<'a> {
    env: &'a Environment,
    schedule: &'a HashMap<Name, Vec<Vec<u32>>>,
    ip: &'a mut Interp,
    led: &'a mut Ledger,
}

/// The decline delta between two [`Untranslated`] snapshots, by reason.
fn decline_delta(before: &Untranslated, after: &Untranslated) -> Vec<String> {
    let grew = after.declarations + after.constructors + after.eliminators
        > before.declarations + before.constructors + before.eliminators;
    if !grew {
        return Vec::new()
    }
    let mut out = Vec::new();
    for (k, v) in &after.by_reason {
        let d = v.saturating_sub(before.by_reason.get(k).copied().unwrap_or(0));
        if d > 0 {
            out.push(if d == 1 { k.clone() } else { format!("{k}×{d}") });
        }
    }
    if out.is_empty() {
        // The tables grew but no reason did — impossible by construction of
        // `by_reason`; name it rather than report a silent decline.
        out.push("unattributed-decline".to_string());
    }
    out
}

impl GroupEngine for MiniEngine<'_> {
    fn check_group(&mut self, d: &Declaration) -> GroupReport {
        // A decline is possible only for the construction kinds: the refusal
        // tables are the inductive apparatus's ([`Untranslated::of`]). A def
        // that cannot be interpreted is a *gap* on the pair, counted by the
        // walk itself, and must not be re-reported here as a decline.
        let watch = matches!(
            d,
            Declaration::Quot | Declaration::Inductive { .. } | Declaration::Mutual { .. }
        );
        let before = watch.then(|| Untranslated::of(self.ip));
        let pairs_before = self.led.pairs;
        let blocked = self.led.walk_decl(self.env, d, self.schedule, self.ip);
        let declined = match before {
            Some(b) => decline_delta(&b, &Untranslated::of(self.ip)),
            None => Vec::new(),
        };
        GroupReport { checked: self.led.pairs - pairs_before, declined, blocked }
    }
}

/// The checker as a [`GroupEngine`]: the export's entries for the group's
/// names, each checked at every scheduled instantiation.
struct CheckerEngine<'x, 'p> {
    rc: nanoda_lib::routed::RoutedChecker<'x, 'p>,
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
        let mut checked = 0usize;
        let mut any = false;
        for n in group_names(d) {
            if let Some(k) = self.rc.check_anchor(&n.to_string()) {
                checked += k;
                any = true;
            }
        }
        GroupReport {
            checked,
            declined: if any { Vec::new() } else { vec!["no-export-group".to_string()] },
            blocked: false,
        }
    }
}

/// The routed run's own ledger: who got what, what fell back and why, what
/// was swept. In the return type from the start — every row here is a count
/// that would otherwise have to be reconstructed from two engines' logs.
#[derive(Debug)]
pub struct RouteReport {
    pub mode: Mode,
    /// Groups the policy sent to each engine (fallbacks are counted where
    /// they were *first* sent; the fallback vectors say where they landed).
    pub to_mini: usize,
    pub to_checker: usize,
    /// Mini declined the group (name, reasons); the checker took it. The
    /// counted event that keeps a decline from hiding a regression.
    pub fallbacks_to_checker: Vec<(String, String)>,
    /// Mini declined and the checker had no export group either — the group
    /// stands declined, exactly as visible as it was in a mini-only run.
    pub declines_unfallen: Vec<(String, String)>,
    /// The checker had no export-side group for a routed name (an
    /// encoder-generated declaration only mini's parse knows); mini took it.
    pub fallbacks_to_mini: Vec<String>,
    /// Export groups no mini declaration names — checked by the checker so
    /// nothing goes unvalidated, and named here.
    pub strays: Vec<String>,
    /// The checker could not parse the export; everything ran on mini.
    pub checker_error: Option<String>,
    /// The shared constant store's crossing report at end of run — the
    /// measurement ENV-UNIFY.md B4 exists to produce, under routing.
    pub cross: String,
    /// The checker's global evidence report (`tg::global_report`), the gap
    /// column of the checker's half.
    pub tg: String,
}

impl RouteReport {
    fn new(mode: Mode) -> RouteReport {
        RouteReport {
            mode,
            to_mini: 0,
            to_checker: 0,
            fallbacks_to_checker: Vec::new(),
            declines_unfallen: Vec::new(),
            fallbacks_to_mini: Vec::new(),
            strays: Vec::new(),
            checker_error: None,
            cross: String::new(),
            tg: String::new(),
        }
    }

    /// The one-line row the measurement runs scrape, shaped like the
    /// ledger's rows (`k=v`, tab-separated).
    pub fn row(&self) -> String {
        let mut s = format!(
            "route\tmode={:?}\ttoMini={}\ttoChecker={}\tfallbacksToChecker={}\t\
             declinesUnfallen={}\tfallbacksToMini={}\tstrays={}\tcheckerError={}",
            self.mode,
            self.to_mini,
            self.to_checker,
            self.fallbacks_to_checker.len(),
            self.declines_unfallen.len(),
            self.fallbacks_to_mini.len(),
            self.strays.len(),
            self.checker_error.is_some(),
        );
        for (n, why) in &self.fallbacks_to_checker {
            s.push_str(&format!("\tfellBack:{n}={why}"));
        }
        for (n, why) in &self.declines_unfallen {
            s.push_str(&format!("\tunfallen:{n}={why}"));
        }
        for n in &self.fallbacks_to_mini {
            s.push_str(&format!("\tfellBackToMini:{n}"));
        }
        for n in &self.strays {
            s.push_str(&format!("\tstray:{n}"));
        }
        s
    }
}

/// The trait is the seam: both engines are driven through it and only
/// through it.
fn via(e: &mut dyn GroupEngine, d: &Declaration) -> GroupReport { e.check_group(d) }

/// **The interleaved driver** — [`crate::run::check_file_with_interp`]'s
/// evidence pass when `Options::route` is set, replacing the single
/// [`Ledger::run`] call. Declarations in file order, each group handed to
/// the engine the policy picks, both engines over the caller's one
/// [`nanoda_lib::tg::EnvCore`] — which this function installs as the
/// checker's per-thread core, so it must run on a thread where no
/// `TgBackend` has been built yet (one routed file per thread; `run.rs`'s
/// deep-thread wrapper and the tests both give it that).
///
/// Interleaving, not two passes, is what makes crossings observable in both
/// directions: a checker-routed definition can adopt the inductive
/// interpretation mini published two declarations earlier, and a mini-routed
/// construction can adopt a def entry the checker published — within one
/// walk of one file.
pub(crate) fn run_routed(
    path: &std::path::Path,
    env: &Environment,
    decls: &[Declaration],
    schedule: &HashMap<Name, Vec<Vec<u32>>>,
    ip: &mut Interp,
    mode: Mode,
) -> (Ledger, RouteReport) {
    let mut led = Ledger::default();
    let mut report = RouteReport::new(mode);
    Ledger::arm_labels(ip);

    // The checker over the same export, same thread, same core. A parse
    // failure is not a crash: the run degrades to mini for everything, and
    // the report says so.
    let parsed = nanoda_lib::routed::routed_config(path).to_export_file();
    let ef = match parsed {
        Ok((ef, _skipped_axioms)) => Some(ef),
        Err(e) => {
            report.checker_error = Some(e.to_string());
            None
        }
    };
    nanoda_lib::tg::install_shared_core(ip.core().clone());
    let mut chk = ef.as_ref().map(|ef| CheckerEngine { rc: nanoda_lib::routed::RoutedChecker::new(ef) });

    let mut blocked = false;
    {
        let mut mini_eng = MiniEngine { env, schedule, ip: &mut *ip, led: &mut led };
        for d in decls {
            let pick = if chk.is_none() { Pick::Mini } else { mode.pick(d) };
            match pick {
                Pick::Mini => {
                    report.to_mini += 1;
                    let rep = via(&mut mini_eng, d);
                    if rep.blocked {
                        blocked = true;
                        break
                    }
                    if !rep.declined.is_empty() {
                        // The counted fallback: mini refused, the checker
                        // takes the group — never silently.
                        let name = d.name().to_string();
                        let why = rep.declined.join(", ");
                        let taken = chk
                            .as_mut()
                            .is_some_and(|c| !via(c, d).declined.contains(&"no-export-group".to_string()));
                        if taken {
                            report.fallbacks_to_checker.push((name, why));
                        } else {
                            report.declines_unfallen.push((name, why));
                        }
                    }
                }
                Pick::Checker => {
                    report.to_checker += 1;
                    let c = chk.as_mut().expect("pick() returns Checker only when the checker parsed");
                    let rep = via(c, d);
                    if !rep.declined.is_empty() {
                        // No export-side group for this name: an
                        // encoder-generated declaration. Mini owns it.
                        report.fallbacks_to_mini.push(d.name().to_string());
                        let mrep = via(&mut mini_eng, d);
                        if mrep.blocked {
                            blocked = true;
                            break
                        }
                    }
                }
            }
        }
    }
    if !blocked {
        led.finish(ip);
        // The stray sweep: export groups no mini declaration names. `known`
        // is every name a group covers, so a routed-to-mini group is not a
        // stray merely because the checker never saw a claim for it.
        if let Some(c) = chk.as_mut() {
            let known: HashSet<String> =
                decls.iter().flat_map(group_names).map(|n| n.to_string()).collect();
            report.strays = c.rc.check_strays(&known);
        }
    }
    report.cross = ip.core().consts().borrow().report();
    report.tg = nanoda_lib::tg::global_report();
    (led, report)
}
