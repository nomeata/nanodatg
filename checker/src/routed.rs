//! Track D — the checker's half of the per-declaration routing seam
//! (ENV-UNIFY.md §5 track D).
//!
//! # Interface
//!
//! ```text
//! ef.check_declar_scheduled(d, &sched)                 one declaration, every σ
//! RoutedChecker::new(&ef, schedule)     -> RoutedChecker
//! rc.check_anchor(name)                 -> Option<usize>
//! rc.unclaimed()                        -> Vec<String>
//! ```
//!
//! The routed driver lives in [`crate::mini::route`]. **The `ExportFile` is
//! the caller's, and it is the one the former mini loader parsed and installed
//! as its arena** (`mini::arena::installed_export_file`) — one
//! parse, one arena, one `NameKey` identity across both engines; this module
//! does not construct a `Config` or read the file, and must not grow the
//! ability to, because a second parse is what made "the same declaration"
//! two objects. What the driver needs from this side is exactly two things,
//! and this module is both of them: the per-declaration analogue of
//! [`ExportFile::check_all_declars`], and the **route-anchor grouping** —
//! which export entries stand or fall with which declaration name.
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
use crate::util::ExportFile;

impl<'p> ExportFile<'p> {
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

impl<'p> ExportFile<'p> {
    /// Interpret `d`'s declared type — and, for a definition-like
    /// declaration, its value — at `sigma`, through the checker's dispatch,
    /// discarding the terms: what remains is what the dispatch *minted* into
    /// the thread's `Shared` skeleton-site tables. The paired-subterm
    /// measurement seam (`mini/tests/route_tg.rs::
    /// paired_subterm_lam_divergence`): with one parse the `ExprPtr`s here
    /// are the very pointers mini's declarations hold, so driving both
    /// dispatches over them separates genuine skeleton disagreement from
    /// surface asymmetry — the confound the whole-run sweep cannot remove.
    /// Behind the `tg` feature because only the TG backend has an
    /// interpretation to measure.
    pub fn interp_declar_exprs_at(&self, d: &Declar<'p>, sigma: &[u32]) {
        let info = *d.info();
        self.with_tc_and_declar(info, sigma, |tc| {
            let _ = tc.certifier.interp(tc.ctx, info.ty);
            if let Declar::Definition { val, .. }
            | Declar::Theorem { val, .. }
            | Declar::Opaque { val, .. } = d
            {
                let _ = tc.certifier.interp(tc.ctx, *val);
            }
        });
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
    /// Anchors in first-appearance file order, for the coverage observation.
    order: Vec<String>,
    claimed: HashSet<String>,
}

impl<'x, 'p> RoutedChecker<'x, 'p> {
    pub fn new(ef: &'x ExportFile<'p>, schedule: Arc<Instantiations>) -> Self {
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
    /// export entry anchors to that name. That is a routing invariant failure:
    /// the caller must report it, never repair it by dispatching elsewhere.
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

    /// Anchors no declaration-loop dispatch claimed. This is an observation,
    /// not a post-loop validation sweep: the unified checker must never repair
    /// missed dispatch by running a second type-check pass.
    pub fn unclaimed(&self) -> Vec<String> {
        self.order
            .iter()
            .filter(|a| !self.claimed.contains(*a))
            .cloned()
            .collect()
    }
}
