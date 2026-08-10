//! **The de-scheduled pass** — one interpretation per *declaration*, at that
//! declaration's own universe parameters, driven over a whole file.
//!
//! # Interface
//!
//! ```text
//! poly_run::run(&Environment, &[Declaration], &mut Interp) -> PolyLedger
//! ```
//!
//! [`crate::run::Options::poly`] is the switch, `mini --poly` the command line,
//! and [`PolyLedger::rows`] the report. `LEVELPOLY.md` §5.3 step 1's second
//! half: *"a caller that drives `Checker::poly` over a whole file"*. Until this
//! module existed the de-scheduled route had no caller in anger, and every
//! claim about it was a claim about unit tests.
//!
//! # What it does, in one paragraph
//!
//! For each `axiom` / `def` / `theorem`, in file order, it builds a
//! [`crate::kernel::Checker::poly`] over the declaration's `lparams` and infers
//! the declaration's type and value **unsubstituted** — no σ, no
//! `ground::subst_ground`, no schedule. `Nat.add.{}` and `List.map.{u,v}` are
//! each one pass, not one pass per ground instantiation. The certificates come
//! back under `{u⃗ ∈ ω}` and are closed together at declaration exit by
//! [`crate::kernel::Checker::discharge_levels`].
//!
//! # The counterpart, not the replacement
//!
//! This is [`crate::ledger::Ledger::run`]'s de-scheduled twin and the two are
//! **mutually exclusive within a run**, which is a decision rather than a
//! limitation. They mint into one [`Interp`]: the scheduled pass fills the
//! store at ground keys and this one would fill it at parametric ones, and
//! `derived::levels::apparatus::level_poly` declares symbols off the shared
//! `Env`, so a run that did both would renumber every symbol the second pass's
//! declarations mint. The branch's whole measurement discipline is that the
//! scheduled route's rows are **byte-identical**; a route that perturbs them by
//! existing would end that. So `--poly` runs *instead*, and the scheduled rows
//! stay reproducible because nothing about the default path changed.
//!
//! # Where the apparatus is built, and why it is here
//!
//! At route entry, before the first declaration — the hazard
//! [`crate::kernel::Checker::poly`]'s header describes, one level up.
//! `Checker::poly` forces it too and [`Interp::levels`] is idempotent, so the
//! extra call buys exactly one thing: the numbering stops depending on
//! **whether the file has a declaration this route accepts at all**. A file of
//! nothing but inductives would otherwise build no apparatus and number its
//! symbols differently from a file with one `def` in front, and the poly rows
//! of the two would not be comparable.
//!
//! # What is *not* here yet, stated so a zero row is readable
//!
//! * **Nothing is stored.** `⟦c.{u⃗}⟧` is not minted and the interpretation
//!   store is not filled, so every *reference* to a constant this pass has
//!   already walked past still finds nothing. That is §5.3 step 5's business —
//!   the store's key has to be the generic point — and it is why
//!   `polyblocked` is expected to be dominated by constant references — and
//!   measured, it is: 84 of the 138 residual `Gap::SymbolicLevel` over the
//!   tutorial corpus are `const_evidence`'s. That is **not** wholly an
//!   artifact of the absent store, though: `const_evidence` reads the level
//!   vector as `Vec<u32>` and would miss at a parametric level whatever the
//!   store contained. See the header of [`PolyLedger::sites`].
//! * **Zone B is not on this route.** `inductive`, `mutual` and `Quot` are
//!   counted in [`PolyLedger::zone_b`] and skipped. Their clauses are
//!   `zoneb.rs`'s 23 `Gap::SymbolicLevel` sites and are a later clause group.
//!
//! Both are counted rather than silently passed over, because a pass that
//! reports `declars=N` while having attempted a third of them is the shape of
//! report this project has been burned by.

use std::collections::BTreeMap;

use crate::env::{Declaration, Environment};
use crate::ev::Gap;
use crate::interp::Interp;
use crate::kernel::{Checker, Typing};
use crate::ledger::Ledger;

/// What the de-scheduled pass reached, per declaration.
///
/// Deliberately **not** [`crate::ledger::Ledger`]. That one counts
/// `(declaration, σ)` pairs and half its columns — `pairs`, `fullyInterpreted`,
/// the σ-keyed store columns — have no meaning without a schedule; reusing it
/// would have produced a report whose column headings lie about what was
/// counted. The two share `Ledger::key` and nothing else, and sharing *that* is
/// deliberate: one vocabulary for a gap, so the two routes' rows can be read
/// against each other.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PolyLedger {
    /// `axiom` / `def` / `theorem` declarations this route attempted.
    pub declarations: usize,
    /// `inductive` / `mutual` / `Quot`, counted and skipped — see the module
    /// header. Not a gap: this route has not been pointed at zone B yet.
    pub zone_b: usize,
    /// Declarations whose `⟦ty⟧` was produced.
    pub types_ok: usize,
    /// Declarations whose `⊢ ⟦ty⟧ ∈ ⟦Sort ℓ⟧` was derived **and closed**.
    pub type_ev_ok: usize,
    /// Declarations with a value at all.
    pub values_attempted: usize,
    /// Declarations whose `⟦val⟧` was produced.
    pub values_ok: usize,
    /// Declarations whose `⊢ ⟦val⟧ ∈ ⟦valTy⟧` was derived **and closed**.
    pub value_ev_ok: usize,
    /// **Certificates that reached declaration exit still carrying a
    /// hypothesis**, after [`Checker::discharge_levels`].
    ///
    /// The de-scheduled route's counterpart of
    /// [`crate::ledger::Ledger::unsealed`], and it must be **zero**. A nonzero
    /// count is an escaped assumption: `discharge_levels` closes exactly the
    /// `uᵢ ∈ ω` it opened, so anything left is a hypothesis some clause raised
    /// and did not discharge, and it would be `Sealed`-refused the moment step
    /// 5 gave this route a store to write to. Counting it here means the
    /// defect is found by the pass rather than by the funnel.
    pub open: usize,
    /// The apparatus built at route entry. `false` means nothing ran.
    pub apparatus: bool,
    /// Why `⟦ty⟧` or `⟦val⟧` was absent, by first blocking cause, in
    /// [`Ledger::key`]'s vocabulary.
    ///
    /// **This histogram is the point of the module.** `LEVELPOLY.md` §5.3
    /// step 1 lists the remaining §6.2 clauses by *`Gap::SymbolicLevel` site
    /// count* — `zoneb.rs` at 23, `kernel.rs` at 21 — and a site count is not a
    /// work estimate; the branch has already had three sizings corrected for
    /// exactly that reason. This is what the clauses cost when a real file is
    /// run through them.
    pub blocked: BTreeMap<String, usize>,
    /// Why a certificate was absent where the interpretation was present — the
    /// evidence axis, kept in its own histogram for MINI-DESIGN.md §0's reason.
    pub ev_blocked: BTreeMap<String, usize>,
    /// **Where the reported gap was minted**, `file:line`, when
    /// `MINI_POLY_SITES` asked — empty otherwise.
    ///
    /// # The row [`PolyLedger::blocked`] cannot produce
    ///
    /// [`Gap::SymbolicLevel`] carries no payload, so every one of them keys to
    /// the single string `symbolic-level`, and on the first run of this route
    /// that one bucket was **90% of every blocked interpretation**. That number
    /// sizes the remaining work and says nothing about *which* work: under a
    /// [`Checker::poly`] thread the two sites that can still mint it are
    /// `pi_evidence`, which wants `as_numeral(l1)`/`as_numeral(l2)` and is
    /// **derivation** (`derived::levels::{pi_rules, ite0, leq}`), and
    /// `const_evidence`, which wants the whole level vector as numerals and is
    /// **the store's key** (§5.3 step 5). Those are different jobs with
    /// different owners, and a bucket that merges them is `MINI-DESIGN.md`
    /// §0.4's "keyed on a name instead of a cause" in the one place the branch
    /// most needs the cause.
    ///
    /// The trail [`crate::blocker`] already keeps is exactly the missing
    /// information, and its oldest entry is the origin rather than a
    /// forwarding — the eviction bug its `TRAIL_CAP` header records is the
    /// reason that is true. So this arms the blocker, clears per declaration,
    /// and files the **first** mint whose variant matches the reason that was
    /// actually reported.
    ///
    /// Off by default and off in every gate: arming puts a thread-local write
    /// on `Ev::missing`, which is the failure branch of `whnf`.
    pub sites: BTreeMap<String, usize>,
}

impl PolyLedger {
    /// Nothing owed: every declaration this route attempted interpreted and
    /// certified, both halves, with nothing left open.
    ///
    /// **`zone_b` is *not* excused.** A file whose inductives this route cannot
    /// reach owes them; counting the route clean on the strength of having
    /// skipped them is the "SKIP is not PASS" defect with a ledger column as
    /// the vehicle.
    pub fn is_clean(&self) -> bool {
        self.apparatus
            && self.zone_b == 0
            && self.open == 0
            && self.types_ok == self.declarations
            && self.type_ev_ok == self.declarations
            && self.values_ok == self.values_attempted
            && self.value_ev_ok == self.values_attempted
    }

    /// The report, one `key=value` per tab — `mini --poly --verbose`'s rows and
    /// the poly gate's baseline.
    ///
    /// Three lines, so the interpretation axis and the evidence axis do not
    /// share a histogram (MINI-DESIGN.md §0), plus a fourth only when
    /// `MINI_POLY_SITES` asked for one.
    pub fn rows(&self) -> Vec<String> {
        let mut head = format!(
            "polyledger\tdeclars={}\tzoneB={}\ttypesOk={}\ttypeEv={}\tvaluesOk={}/{}\tvalueEv={}\topen={}",
            self.declarations,
            self.zone_b,
            self.types_ok,
            self.type_ev_ok,
            self.values_ok,
            self.values_attempted,
            self.value_ev_ok,
            self.open,
        );
        // Named on the row and not merely implied by a zero, because "the
        // apparatus did not build" and "the file had no declarations" produce
        // the same counters and are entirely different results.
        head.push_str(if self.apparatus { "\tapparatus=built" } else { "\tapparatus=none" });
        let hist = |tag: &str, m: &BTreeMap<String, usize>| {
            let mut s = tag.to_string();
            for (k, v) in m {
                s.push_str(&format!("\t{k}={v}"));
            }
            s
        };
        let mut rows =
            vec![head, hist("polyblocked", &self.blocked), hist("polyev", &self.ev_blocked)];
        // Only when it was asked for: a bare `polysites` row on every run would
        // read as "no site was recorded" rather than "nobody asked".
        if !self.sites.is_empty() {
            rows.push(hist("polysites", &self.sites));
        }
        rows
    }

    fn note(m: &mut BTreeMap<String, usize>, g: Option<&Gap>) {
        *m.entry(Ledger::key(g)).or_insert(0) += 1;
    }

    /// File the origin of `g` from the current [`crate::blocker`] trail — the
    /// **oldest** mint of the same variant, which is the site that gave up
    /// rather than one that forwarded its reason.
    fn note_site(&mut self, g: Option<&Gap>) {
        let Some(g) = g else { return };
        let want = crate::blocker::variant_name(g);
        let Some(m) = crate::blocker::trail().into_iter().find(|m| {
            crate::blocker::variant_name(&m.gap) == want
        }) else {
            return
        };
        *self.sites.entry(format!("{}:{}", m.file, m.line)).or_insert(0) += 1;
    }
}

/// Run the de-scheduled interpretation over a whole file.
///
/// Declarations in file order — mini-lean's order, and the same order
/// [`Ledger::run`] uses, so the two reports name the same declarations in the
/// same sequence. There is no inner loop: **that is the whole point.**
pub fn run(env: &Environment, decls: &[Declaration], ip: &mut Interp) -> PolyLedger {
    // The build point, pinned at route entry — before the first declaration,
    // and in the initialiser so nothing can slip in front of it. See the module
    // header for why *when* this runs decides every later symbol's number.
    let mut led = PolyLedger { apparatus: ip.levels().is_some(), ..Default::default() };
    if !led.apparatus {
        return led
    }
    // The site census — [`PolyLedger::sites`]. Armed here rather than by the
    // caller, and disarmed on the way out, so an env variable cannot leave the
    // blocker on for whatever runs next in the process.
    let sites = std::env::var_os("MINI_POLY_SITES").is_some();
    let was_armed = crate::blocker::is_armed();
    if sites {
        crate::blocker::arm(true);
    }
    for d in decls {
        if sites {
            crate::blocker::enter_pair();
        }
        let (lparams, ty, val) = match d {
            Declaration::Axiom { lparams, ty, .. } => (lparams, ty, None),
            Declaration::Def { lparams, ty, value, .. } => (lparams, ty, Some(value)),
            Declaration::Quot | Declaration::Inductive { .. } | Declaration::Mutual { .. } => {
                led.zone_b += 1;
                continue
            }
        };
        led.declarations += 1;
        let Some(mut c) = Checker::poly(env, ip, lparams) else {
            // `Interp::levels` answered above, so it answers here: a `None`
            // would mean the apparatus stopped building mid-file, which is
            // not a thing that can happen and is not silently tolerated.
            unreachable!("the apparatus built at route entry")
        };
        // One traversal per half, both results, and the reason for a missing
        // one is the `Typing`'s own `ev` — `Ledger::run`'s discipline, kept.
        let ty_t = c.infer_type(ty);
        let val_t = val.map(|v| c.infer_type(v));

        // **Closed together, in one call, before anything is read back.**
        // The two conclusions stand over the same `uᵢ`, so they are discharged
        // against the same assumptions in one pass; `Checker::discharge_levels`
        // says why the singular form could not do this.
        let raw: Vec<_> = [ty_t.as_ref().ok(), val_t.as_ref().and_then(|t| t.as_ref().ok())]
            .iter()
            .map(|t| t.and_then(|t: &Typing| t.ev.thm().cloned()))
            .collect();
        let present: Vec<_> = raw.iter().flatten().cloned().collect();
        let mut closed = c.discharge_levels(&present).into_iter();
        drop(c);
        // Back into the two slots the theorems came from, so a missing type
        // certificate does not shift the value's into its place.
        //
        // **`if r.is_some()` and not `r.as_ref().and(closed.next())`**, which
        // is what this was and is wrong: `Option::and` evaluates its argument
        // eagerly, so an absent type certificate still consumed the iterator's
        // next element — the value's — and both slots came back `None`. It
        // reported itself as `polyev inference-error`, a reason no clause can
        // mint here, which is the only thing that gave it away. See
        // [`tests::a_missing_type_certificate_does_not_eat_the_values`].
        let closed: Vec<Option<kernel::Thm>> = raw
            .iter()
            .map(|r| if r.is_some() { closed.next() } else { None })
            .collect();

        let ty_ok = ty_t.as_ref().is_ok_and(|t| t.tm.is_some());
        if ty_ok {
            led.types_ok += 1;
        } else {
            let g = ty_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
            PolyLedger::note(&mut led.blocked, g.as_ref());
            if sites {
                led.note_site(g.as_ref());
            }
        }
        match &closed[0] {
            Some(t) if t.hyps().is_empty() => led.type_ev_ok += 1,
            Some(_) => led.open += 1,
            None => {
                let g = ty_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
                PolyLedger::note(&mut led.ev_blocked, g.as_ref());
            }
        }

        let Some(val_t) = val_t else { continue };
        led.values_attempted += 1;
        if val_t.as_ref().is_ok_and(|t| t.tm.is_some()) {
            led.values_ok += 1;
        } else {
            let g = val_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
            PolyLedger::note(&mut led.blocked, g.as_ref());
            if sites {
                led.note_site(g.as_ref());
            }
        }
        match &closed[1] {
            Some(t) if t.hyps().is_empty() => led.value_ev_ok += 1,
            Some(_) => led.open += 1,
            None => {
                let g = val_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
                PolyLedger::note(&mut led.ev_blocked, g.as_ref());
            }
        }
    }
    if sites {
        crate::blocker::arm(was_armed);
    }
    led
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::DefKind;
    use crate::expr::{E, Level, Name, forall, sort};

    fn n(s: &str) -> Name { Name::simple(s) }

    /// A `def` whose type is `Sort u` and whose value is `Sort v`, at whatever
    /// parameters are asked for.
    fn def(name: &str, us: &[&str], ty: E, value: E) -> Declaration {
        Declaration::Def {
            name: n(name),
            lparams: us.iter().map(|s| n(s)).collect(),
            ty,
            value,
            kind: DefKind::Def,
        }
    }

    /// **The route runs, and it runs at a variable rung.**
    ///
    /// `def d.{u} : Sort (u+1) := Sort u` is the smallest declaration that has
    /// a level parameter in *both* halves and needs no constant, so it is the
    /// one thing this route can certify end to end today. Both certificates
    /// come back closed, which is the property the singular `discharge_levels`
    /// could not have produced.
    #[test]
    fn a_polymorphic_declaration_is_certified_at_its_own_parameter() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let d = def("d", &["u"], sort(u.succ()), sort(u));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert!(led.apparatus, "the apparatus builds at route entry");
        assert_eq!(led.declarations, 1);
        assert_eq!(led.types_ok, 1, "⟦Sort (u+1)⟧ at a variable rung: {:?}", led.blocked);
        assert_eq!(led.values_ok, 1, "⟦Sort u⟧ at a variable rung: {:?}", led.blocked);
        // **Both halves, and this is the assertion that needed the batch
        // discharge.** Under the singular form the second theorem came back
        // with `u ∈ ω` still on it and `open` would be 1.
        assert_eq!(led.type_ev_ok, 1, "the type's certificate: {:?}", led.ev_blocked);
        assert_eq!(led.value_ev_ok, 1, "the value's certificate: {:?}", led.ev_blocked);
        assert_eq!(led.open, 0, "nothing escaped its discharge");
        assert!(led.is_clean(), "{:?}", led.rows());
    }

    /// **Three parameters, and the one the declaration mentions is the one
    /// assumed.** Two would pass under a constructor that bound them all to one
    /// variable; the strand's own rule.
    ///
    /// Run twice over one `Interp` as well, because the apparatus is built at
    /// route entry and [`Interp::levels`] is idempotent: a second file through
    /// the same `Interp` must produce the same counters and must not rebuild.
    #[test]
    fn the_route_is_idempotent_in_the_apparatus_and_picks_the_right_parameter() {
        let env = Environment::empty();
        let v = Level::param(n("v"));
        let d = def("d", &["u", "v", "w"], sort(v.succ()), sort(v));
        let mut ip = Interp::new();
        assert!(ip.levels_built().is_none(), "nothing built before the route runs");
        let first = run(&env, std::slice::from_ref(&d), &mut ip);
        let built = ip.levels_built().cloned().expect("built by the route");
        let again = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(first, again, "a second pass over one Interp must report the same");
        assert!(
            std::rc::Rc::ptr_eq(&built, ip.levels_built().expect("still built")),
            "the apparatus was rebuilt, which renumbers every later symbol"
        );
        assert!(first.is_clean(), "{:?}", first.rows());
    }

    /// **Zone B is counted, not passed over.** An inductive is neither a
    /// success nor a gap on this route; it is work the route has not been
    /// pointed at, and `is_clean` must refuse it all the same.
    ///
    /// # …and it is the only witness the pinned build point has
    ///
    /// The apparatus is forced at route entry rather than left to
    /// `Checker::poly`'s own idempotent force, because `level_poly` declares
    /// symbols off the shared `Env` and *when* it runs decides the numbering of
    /// every symbol minted after it. **Measured, that pin is invisible in the
    /// corpus rows**: removing it and rerunning all 91 tutorial exports
    /// produces byte-identical `polyledger` / `polyblocked` / `polyev` lines,
    /// because every one of those exports has at least one `def` or `axiom`,
    /// so `Checker::poly` builds the apparatus at the first declaration either
    /// way, and the ledger counts declarations and reasons rather than terms.
    ///
    /// A file of **nothing but** zone B is the cell where the two differ, and
    /// the tutorial corpus does not contain one. So the assertion below is not
    /// belt-and-braces on a covered property — it is the *whole* coverage the
    /// pin has, and without it the mutation that deletes the pin is green.
    /// Recorded here rather than dropped, per the branch's own rule.
    #[test]
    fn an_inductive_is_counted_as_zone_b_and_keeps_the_run_unclean() {
        let env = Environment::empty();
        let d = Declaration::Inductive {
            name: n("T"),
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero()),
            ctors: Vec::new(),
        };
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!((led.declarations, led.zone_b), (0, 1));
        assert!(!led.is_clean(), "a skipped inductive is owed, not excused");
        assert!(led.rows()[0].contains("zoneB=1"), "{:?}", led.rows());
        // The pin. Nothing on this file ever constructs a `Checker::poly`, so
        // an apparatus built here was built by the route and by nothing else.
        assert!(led.apparatus, "the apparatus is built at route entry, not at the first def");
        assert!(ip.levels_built().is_some(), "…and it really is on the Interp");
    }

    /// **A monomorphic declaration on this route is the scheduled one.** With
    /// no `lparams` there is no ω-variable, `Checker::poly`'s thread is
    /// `Checker::threaded`'s, and `⟦Sort 0⟧` is the ground rung — so the two
    /// routes agree on the population where they overlap, which is what makes
    /// the poly row readable against the scheduled one at all.
    #[test]
    fn a_monomorphic_declaration_takes_the_ground_rung_on_this_route() {
        let env = Environment::empty();
        let d = def("d", &[], sort(Level::zero().succ()), sort(Level::zero()));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert!(led.is_clean(), "{:?}", led.rows());
        // The value is `⟦Sort 0⟧` and it is `U₀`, not `srt(0̄)`.
        let mut c = Checker::poly(&env, &mut ip, &[]).expect("poly");
        let t = c.infer_type(&sort(Level::zero())).expect("infer");
        drop(c);
        assert_eq!(t.tm, Some(ip.sort(0)), "a monomorphic Sort 0 must stay the ground rung");
    }

    /// **The `Π` clause at a variable rung, end to end through the route.**
    ///
    /// `def d.{u} : Sort (u+1) := Sort u → Sort u` — the value is a `Π` whose
    /// *both* levels are the declaration's own parameter, so neither the
    /// scheduled `l2 == 0` split nor `as_numeral` can reach it. Before the
    /// clause landed this was `polyblocked symbolic-level`; now it interprets
    /// to `ite0(û, cndd(⟦Sort u⟧), dprod(⟦Sort u⟧))` and certifies.
    ///
    /// The type is `Sort (u+1)` rather than the `Π`'s real type because this
    /// route infers the two halves independently and does not check them
    /// against each other — see `run`.
    #[test]
    fn a_pi_at_a_variable_rung_interprets_and_certifies() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let arrow = forall(sort(u), sort(u));
        let d = def("d", &["u"], sort(u.succ()), arrow);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(led.values_ok, 1, "⟦Π x:Sort u. Sort u⟧: {:?}", led.rows());
        assert_eq!(led.value_ev_ok, 1, "…and its typing: {:?}", led.rows());
        assert_eq!(led.open, 0, "the Π clause discharged everything it opened");
        assert!(
            !led.blocked.contains_key("symbolic-level"),
            "the Π clause still wants a numeral: {:?}",
            led.blocked
        );
    }

    /// **The mixed case, which is the one the bridge exists for.**
    ///
    /// `Sort 0 → Sort u` has one numeral level and one parameter, so the
    /// domain's membership arrives spelled `⟦A⟧ ∈ U₀` while `pi_imax_dep`
    /// states its premise over `srt(0̄)`. `Interp::mem_at_srt` is what
    /// reconciles them, and this is the shape that exercises it — a test with
    /// two parameters and no numeral would pass with the bridge deleted.
    ///
    /// Both orders, because the domain's premise and the fibre's are
    /// reconciled by two *different* calls and a bridge applied to only one of
    /// them would pass whichever test used it.
    #[test]
    fn a_pi_mixing_a_numeral_level_with_a_parameter_bridges_both_ways() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let z = Level::zero();
        for (i, body) in [forall(sort(z), sort(u)), forall(sort(u), sort(z))].into_iter().enumerate()
        {
            let d = def("d", &["u"], sort(u.succ()), body);
            let mut ip = Interp::new();
            let led = run(&env, std::slice::from_ref(&d), &mut ip);
            assert_eq!(led.values_ok, 1, "case {i} did not interpret: {:?}", led.rows());
            assert_eq!(led.open, 0, "case {i} left an assumption open");
            // The certificate is the point; `mem_at_srt` returning `None` shows
            // up here and nowhere else.
            assert_eq!(led.value_ev_ok, 1, "case {i} lost its certificate: {:?}", led.rows());
        }
    }

    /// **A nonzero numeral codomain needs no `ite0` collapse, measured.**
    ///
    /// `Checker::pi_evidence_poly`'s header predicted this case would be
    /// declined: `imax ℓ k` for nonzero `k` was expected to arrive already
    /// normalised by Lean to `max ℓ k`, mismatching the rule's
    /// `srt(ite0(k̄, ∅, ℓ̂ ∪ k̄))` and waiting on `Ite0::when_nonzero`. It is
    /// **not** normalised — `Level::imax(u, 1)` is `imax(u,(0+1))`, mini's
    /// smart constructor keeps the node — so `sort_of` spells the target
    /// exactly as the rule concludes it and the clause certifies.
    ///
    /// Kept as a test rather than deleted with the prediction, because it is
    /// the only thing standing between that paragraph and rotting back: if a
    /// future `Level::imax` *does* start collapsing, this goes red at the
    /// clause rather than silently at the next tranche's measurement.
    ///
    /// `k = 0` is included and is a different case — `imax ℓ 0` is `0`, the
    /// `Prop` clause — so the loop covers both sides of `ite0`'s split.
    #[test]
    fn a_pi_over_a_nonzero_numeral_codomain_needs_no_ite0_collapse() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        for k in 0..3u32 {
            let l2 = crate::ground::numeral(k);
            let d = def("d", &["u"], sort(u.succ()), forall(sort(u), sort(l2)));
            let mut ip = Interp::new();
            let led = run(&env, std::slice::from_ref(&d), &mut ip);
            assert_eq!(led.values_ok, 1, "Sort u → Sort {k} did not interpret: {:?}", led.rows());
            assert_eq!(led.value_ev_ok, 1, "Sort u → Sort {k} uncertified: {:?}", led.rows());
            assert_eq!(led.open, 0, "Sort u → Sort {k} left an assumption open");
        }
    }

    /// **The type's slot and the value's slot are the slots they came from.**
    ///
    /// A declaration whose type has no certificate and whose value does is not
    /// a corner case: it is what `015_levelParams` did when this was written.
    /// The two theorems are closed in one batch, so putting them back takes an
    /// index, and getting that wrong reported the **value's** certificate as
    /// absent under the reason `inference-error` — a key no clause on this
    /// route can mint, which is the only reason it was visible at all.
    ///
    /// # The fixture may not assert that something stays broken
    ///
    /// This first used `Sort u → Sort u` as the uninterpretable type, because
    /// the `Π` clause wanted a numeral. **The `Π` clause then landed one
    /// tranche later and this test went red on the cure** — it was asserting
    /// `typesOk == 0` about the very clause whose purpose was to make it 1.
    /// That is the branch's own rule, and this is the second time it has
    /// caught something.
    ///
    /// A string literal is the replacement, and the choice is the point:
    /// `Gap::StrLit` is not *waiting* on anything. Mini declines string
    /// literals as a matter of interpretation **scope**, not of unfinished
    /// threading (MINI-DESIGN.md §0's two axes), so no clause conversion can
    /// cure it and this fixture cannot go red on progress a second time.
    ///
    /// **The axis is what makes it safe, not the distance.** Re-founding this
    /// on the next dark thing — a constant at a parametric level, 109 sites
    /// today — would have failed again at the very next slice. `DECISIONS.md`
    /// 2026-08-10 is the rule: when a stays-broken fixture is cured, cross to
    /// the *other* axis rather than moving further along the same one.
    ///
    /// The pair is not well-typed and does not need to be — this route infers
    /// the two halves independently and checks neither against the other.
    #[test]
    fn a_missing_type_certificate_does_not_eat_the_values() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let d = def("d", &["u"], crate::expr::str_lit("not a type"), sort(u));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(led.types_ok, 0, "a string literal interprets to nothing: {:?}", led.rows());
        assert_eq!(led.type_ev_ok, 0);
        assert_eq!(
            led.blocked.get("strLit"),
            Some(&1),
            "…and the reason is scope, not threading: {:?}",
            led.blocked
        );
        assert_eq!(led.values_ok, 1, "⟦Sort u⟧ interprets: {:?}", led.rows());
        // The assertion the misalignment failed, and the reason it minted.
        assert_eq!(led.value_ev_ok, 1, "the value's certificate went to the type's slot");
        assert_eq!(led.open, 0);
        assert!(
            !led.ev_blocked.contains_key("inference-error"),
            "`inference-error` is unmintable on this route: {:?}",
            led.ev_blocked
        );
    }

    /// The row is wire-safe in the same sense `Ledger`'s is: one `key=value`
    /// per tab, and the harness splits on the first `=`.
    #[test]
    fn every_poly_row_is_wire_safe() {
        let mut led = PolyLedger { apparatus: true, ..Default::default() };
        led.blocked.insert("no-interp(Nat)".to_string(), 3);
        led.ev_blocked.insert("symbolic-level".to_string(), 1);
        for row in led.rows() {
            let mut it = row.split('\t');
            assert!(it.next().is_some_and(|t| !t.contains('=')), "the tag is bare: {row}");
            for cell in it {
                assert!(cell.contains('='), "every cell is key=value: {cell:?} in {row}");
                assert!(!cell.contains(' '), "no spaces around the separator: {cell:?}");
            }
        }
    }
}

