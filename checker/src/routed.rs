//! Track D — the checker's half of the per-declaration routing seam
//! (ENV-UNIFY.md §5 track D).
//!
//! # Interface
//!
//! ```text
//! routed_config(export)                 -> Config      the routed run's config
//! ef.routed_schedule()                  -> Arc<Instantiations>
//! ef.check_declar_scheduled(d, &sched)                 one declaration, every σ
//! RoutedChecker::new(&ef)               -> RoutedChecker
//! rc.check_anchor(name)                 -> Option<usize>
//! rc.check_strays(&known)               -> Vec<String>
//! ```
//!
//! The routed driver lives in `mini` (`mini/src/route.rs`), because `mini`
//! already depends on this crate and not the other way around. What the
//! driver needs from this side is exactly three things, and this module is
//! all of them: the `Config` a routed run drives the checker with, the
//! per-declaration analogue of [`ExportFile::check_all_declars`], and the
//! **route-anchor grouping** — which export entries stand or fall with which
//! declaration name.
//!
//! # The group is the routing unit, and the anchor names it
//!
//! Routing is per *declaration group*, not per export line (ENV-UNIFY.md
//! §3.7): an inductive's constructors and recursors are separate `Declar`
//! entries whose validation is the inductive's own check, so routing the
//! inductive to one engine and its recursor to the other would leave the
//! recursor's ι rules validated by nobody. Every `Declar` therefore has a
//! **route anchor** — the name whose routing decision governs it:
//!
//! * a `Constructor` follows its `inductive_name`;
//! * a `Recursor` follows the first of its `all_inductives` — for an
//!   ordinary recursor that is its own inductive, and for a nested
//!   inductive's auxiliary recursors it is the outer type of the nest, which
//!   under a *kind*-based policy routes the same way (both are inductives);
//! * the four `Quot` entries all follow the name `Quot`, which is also the
//!   name `mini`'s single `Declaration::Quot` reports;
//! * everything else anchors to itself.
//!
//! # What a skipped group means, and who still vouches for it
//!
//! A group routed to `mini` is **not checked here at all** — that is the
//! point of routing, not an oversight. Its entries stay visible in the
//! parse-time-complete `DeclarMap`, so later checker work can mention them;
//! mini's kernel is what accepted them. One known asymmetry rides along,
//! recorded rather than hidden (ENV-UNIFY.md §3.8): the checker validates an
//! export's recursor entries by mint-and-compare inside
//! `check_inductive_declar`, and mini generates its own recursors without
//! comparing them to the export's — so on a mini-routed inductive the export
//! rules the checker later ι-reduces with are covered by `mini`'s load-time
//! shape comparison (`Facts::recursor_shape_mismatches`) and not by the full
//! mint-and-compare. Promoting that comparison is track A3, not this seam.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::env::Declar;
use crate::instantiations::Instantiations;
use crate::util::{Config, ExportFile};

/// The `Config` a routed run drives the checker with — the same shape the
/// cross-engine seam test (`mini/tests/envshare_tg.rs`) has always used:
/// every axiom admitted (mini's frontend has already declined the files whose
/// *used* axioms are out of scope, see `mini::run`), both literal extensions
/// on (the corpus uses them), no success banner. Built directly rather than
/// through a JSON file because a routed run has no user-facing config of its
/// own; the export path is the only variable.
pub fn routed_config(export: &std::path::Path) -> Config {
    Config {
        export_file_path: Some(export.to_path_buf()),
        use_stdin: false,
        permitted_axioms: None,
        unpermitted_axiom_hard_error: false,
        // The routed evidence axis is single-threaded by construction — the
        // shared `EnvCore` is `!Send` (ENV-UNIFY.md §3.4 item 4).
        num_threads: 0,
        nat_extension: true,
        string_extension: true,
        pp_declars: None,
        unknown_pp_declar_hard_error: true,
        pp_options: Default::default(),
        pp_output_path: None,
        pp_to_stdout: false,
        print_success_message: false,
        print_axioms: false,
        unsafe_permit_all_axioms: true,
    }
}

impl<'p> ExportFile<'p> {
    /// The instantiation schedule, computed and **published** once — the
    /// first half of what [`ExportFile::check_all_declars`] does before any
    /// checking, exposed so a driver that interleaves engines can do the same
    /// and then check one declaration at a time. Publishing before any check
    /// is load-bearing for the same reason it is there: the backend reports
    /// interpreted instantiations against the published schedule.
    pub fn routed_schedule(&self) -> Arc<Instantiations> {
        crate::instantiations::publish(Instantiations::compute(self))
    }

    /// Check `d` at every instantiation the schedule requires of it — the
    /// per-declaration step of `check_all_declars`, exposed for the routed
    /// driver. Mirrors `tc.rs`'s private `check_declar_all`, including its
    /// reason for checking `Inductive` and `Quot` once at their own
    /// parameters: neither has anywhere to put a σ. Returns how many
    /// `(declaration, σ)` checks ran.
    pub fn check_declar_scheduled(&self, d: &Declar<'p>, schedule: &Instantiations) -> usize {
        if matches!(d, Declar::Inductive(..) | Declar::Quot { .. }) {
            self.check_declar_at(d, &[]);
            return 1
        }
        match schedule.for_name(d.info().name) {
            // The schedule's default seeding gives every declaration of the
            // file at least one instantiation, so this is the empty-schedule
            // case only.
            None => {
                self.check_declar_at(d, &[]);
                1
            }
            Some(insts) => {
                for sigma in insts.iter() {
                    self.check_declar_at(d, sigma)
                }
                insts.len()
            }
        }
    }

    /// The route anchor of `d`, rendered in the joint spelling (`pre.s`,
    /// `pre.3` — the same format `mini`'s `Name` displays as and the shared
    /// store's alias guard compares, see `TgBackend::spell`).
    pub fn route_anchor(&self, d: &Declar<'p>) -> String {
        let n = match d {
            Declar::Quot { .. } => return "Quot".to_string(),
            Declar::Constructor(c) => c.inductive_name,
            Declar::Recursor(r) => match r.all_inductives.first() {
                Some(n) => *n,
                None => d.info().name,
            },
            _ => d.info().name,
        };
        self.with_ctx(|ctx| {
            fn go<'t, 'p>(
                ctx: &crate::util::TcCtx<'t, 'p>,
                n: crate::util::NamePtr<'t>,
                out: &mut String,
            ) {
                match ctx.read_name(n) {
                    crate::name::Name::Anon => out.push_str("[anonymous]"),
                    crate::name::Name::Str(pre, s, _) => {
                        if !matches!(ctx.read_name(pre), crate::name::Name::Anon) {
                            go(ctx, pre, out);
                            out.push('.');
                        }
                        out.push_str(ctx.read_string(s).as_ref());
                    }
                    crate::name::Name::Num(pre, i, _) => {
                        if !matches!(ctx.read_name(pre), crate::name::Name::Anon) {
                            go(ctx, pre, out);
                            out.push('.');
                        }
                        out.push_str(&i.to_string());
                    }
                }
            }
            let mut s = String::new();
            go(ctx, n, &mut s);
            s
        })
    }
}

/// The checker's side of a routed run: the export's declarations bucketed by
/// route anchor, the published schedule, and the claim ledger that makes
/// "nothing was silently left unchecked" a checkable statement rather than a
/// hope.
pub struct RoutedChecker<'x, 'p> {
    ef: &'x ExportFile<'p>,
    schedule: Arc<Instantiations>,
    /// Route anchor → indices into `ef.declars`, file order within a group.
    groups: HashMap<String, Vec<usize>>,
    /// Anchors in first-appearance file order, for the stray sweep.
    order: Vec<String>,
    claimed: HashSet<String>,
}

impl<'x, 'p> RoutedChecker<'x, 'p> {
    pub fn new(ef: &'x ExportFile<'p>) -> Self {
        let schedule = ef.routed_schedule();
        let mut groups: HashMap<String, Vec<usize>> = HashMap::new();
        let mut order = Vec::new();
        for (i, d) in ef.declars.values().enumerate() {
            let a = ef.route_anchor(d);
            let e = groups.entry(a.clone()).or_default();
            if e.is_empty() {
                order.push(a);
            }
            e.push(i);
        }
        RoutedChecker { ef, schedule, groups, order, claimed: HashSet::new() }
    }

    /// Check every export entry anchored to `anchor`, in file order, at every
    /// scheduled instantiation, and mark the group claimed. `None` when no
    /// export entry anchors to that name — a driver-side declaration the
    /// export never saw (an encoder-generated one, say), which the caller
    /// must route back to the engine that owns it, counted.
    pub fn check_anchor(&mut self, anchor: &str) -> Option<usize> {
        let idxs = self.groups.get(anchor)?;
        let mut n = 0;
        for &i in idxs {
            let (_, d) = self.ef.declars.get_index(i).expect("a grouped index is in range");
            n += self.ef.check_declar_scheduled(d, &self.schedule);
        }
        self.claimed.insert(anchor.to_string());
        Some(n)
    }

    /// Mark `anchor` claimed without checking — the driver routed the group
    /// to the other engine, which is a claim of coverage, not a gap.
    pub fn claim_anchor(&mut self, anchor: &str) {
        if self.groups.contains_key(anchor) {
            self.claimed.insert(anchor.to_string());
        }
    }

    /// **The stray sweep.** Every anchor neither claimed nor present in
    /// `known` (the driver's own declaration names) is a group no routing
    /// decision ever covered — it is *checked here*, so nothing is silently
    /// unvalidated, and *returned by name*, so the driver can count it.
    pub fn check_strays(&mut self, known: &HashSet<String>) -> Vec<String> {
        let anchors: Vec<String> = self
            .order
            .iter()
            .filter(|a| !self.claimed.contains(*a) && !known.contains(*a))
            .cloned()
            .collect();
        for a in &anchors {
            self.check_anchor(a);
        }
        anchors
    }
}
