//! **Abort on the first blocker** — the hard stop that replaces the statistic.
//!
//! # Interface
//!
//! ```text
//! blocker::arm(true)                    // switch the whole run into blocking mode
//! blocker::is_armed() -> bool
//! blocker::enter_pair()                 // start a (declaration, σ); clears the trail
//! blocker::record(&Gap, Location)       // one gap minted, with its source site
//! Blocker { .. }                        // the report, `Display`-able
//! ```
//!
//! # Why this exists
//!
//! [`crate::ledger`] measures: it records every missing derivation as a
//! [`Gap`], attributes it by [`Cause`](crate::ev::Cause), and sums the columns.
//! That is the right instrument for *sizing* the work and the wrong one for
//! *ordering* it — a table of 83 residual pairs says nothing about which one to
//! do next, and a run that files a gap and carries on will file eighty-two more
//! behind it, some of which exist only because the first one does.
//!
//! Armed, mini stops at the **first** `(declaration, σ)` whose obligation it
//! cannot discharge and reports it in full. The vocabulary is unchanged: the
//! reason is the same [`Gap`] the ledger would have counted, spelled with the
//! same [`crate::ledger::Ledger::key`] string, so a blocker and a ledger row
//! name the same thing and can be cross-read.
//!
//! # What the report contains, and where each part comes from
//!
//! * **the pair** — export file, declaration name, and σ spelled as
//!   `u := 0, v := 1` against the declaration's own level parameters;
//! * **the obligation** — which of the four things a pair owes was missing
//!   ([`Obligation`]), stated at the Lean level with mini's own `Expr`
//!   printer, which is exact;
//! * **what was in hand** — the interpretations and evidence that *did* exist,
//!   with kernel terms rendered through [`crate::interp::Interp::parts_of`] and
//!   the label registry;
//! * **the site that gave up** — the source location of every [`Ev::missing`]
//!   mint in this pair carrying that gap, with the source line itself;
//! * **the construction sites of the gap variant** — a grep of `mini/src` for
//!   the variant (and, when the variant carries a `&'static str` detail, for
//!   that literal, which pins one line exactly).
//!
//! # The one imprecision, stated rather than hidden
//!
//! Several modules mint their gaps through a per-function closure
//! (`let gap = |g: Gap| Typing { .., ev: Ev::missing(g) }` in `zoneb`,
//! `recursor`, `class_s`, `direct`, `rec_dep`). `#[track_caller]` reports the *closure
//! body's* line for those, not the line that chose the gap — the closure is the
//! caller. Those variants all carry a name or a `&'static str` detail, and the
//! variant grep is what pins them; the trail still identifies the function.
//! Making the trail exact there means turning those five closures into macros,
//! which is a mechanical change and is deliberately not bundled with this one.
//!
//! A *function* has the same problem and does not need a macro to fix it:
//! [`crate::conv::Conv::gap`] is one line every `whnf` step routes through, and
//! it carried the whole trail until it was given `#[track_caller]` of its own.
//! On one `mutual_aux_encoding` pair it accounted for twenty of some thirty
//! mints, all reading `pub fn gap(to: E, g: Gap) -> Conv`.
//!
//! # Two things that are *not* mints, and had to be taught so
//!
//! **Propagating a reason the caller chose.** `whnf_conv`'s `acc` starts as a
//! gap when the caller handed in no endpoint, and the gap it starts as is the
//! caller's own `why` — already chosen, and already recorded wherever it came
//! from an `Ev`. It is built with `Ev::Gap` directly for that reason.
//!
//! **Deciding "no".** A predicate that answers *no* has not given up.
//! `Checker::is_prop_or_unit_ev` used to return `(bool, Ev)` and fill the `Ev`
//! on its negative branches with an `Ev::missing` no caller reads; it returns
//! `Option<Ev>` now, so there is no slot. Both are the same rule as
//! [`record`]'s "re-wrapping is not minting", one step further out.

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::panic::Location;

use crate::ev::{Cause, Gap};
use crate::expr::{Name, E};
use crate::interp::Interp;

/// How many gap mints to keep per pair. The cap is there so that a
/// pathological declaration cannot grow the trail without bound.
///
/// **It was 64, and 64 was an instrument defect rather than a number that did
/// not matter.** The trail evicts from the *front*, and the front is where the
/// origin is: mints arrive innermost-first, so a pair that mints more than the
/// cap loses precisely the site that gave up and keeps the forwardings above
/// it. `Nat.add` mints exactly 64 — the trail was full — and the report named
/// `app_evidence`/`lam_evidence`, which is what three seats then read as the
/// answer. A blocked pair is one pair on one armed run; four thousand `Mint`s
/// is under 200 kB and the eviction is now a real overflow rather than a
/// routine one.
const TRAIL_CAP: usize = 4096;

/// One gap, minted at one place.
#[derive(Debug, Clone)]
pub struct Mint {
    pub gap: Gap,
    pub file: &'static str,
    pub line: u32,
}

thread_local! {
    /// The fast path. Read on every [`Ev::missing`](crate::ev::Ev::missing),
    /// which is on the failure branch of `whnf` and is taken millions of times
    /// per corpus run, so it must be one thread-local `bool` read and nothing
    /// else.
    static ARMED: Cell<bool> = const { Cell::new(false) };
    static TRAIL: RefCell<VecDeque<Mint>> = const { RefCell::new(VecDeque::new()) };
    /// Nesting depth of [`Quiet`] scopes. Non-zero means the walk currently
    /// running was never asked for a certificate, so nothing it gives up on is
    /// evidence about the pair.
    static QUIET: Cell<usize> = const { Cell::new(0) };
}

/// Switch blocking mode on or off for this thread.
pub fn arm(on: bool) {
    ARMED.with(|a| a.set(on));
    TRAIL.with(|t| t.borrow_mut().clear());
    QUIET.with(|q| q.set(0));
}

pub fn is_armed() -> bool { ARMED.with(Cell::get) }

/// **A walk nobody asked a certificate of files nothing** — [`record`]'s third
/// exclusion, and the one that was missing.
///
/// The two already stated — *propagating a reason the caller chose* and
/// *deciding "no"* — are about a single call. This is the same rule over a
/// whole subtree. `Checker::is_def_eq` and `Checker::whnf` hand in **no**
/// endpoints: their callers want a `bool` and an expression, the `Ev` they
/// produce is dropped at the frame above, and every `Ev::missing` inside them
/// is scaffolding by construction. There is no way to tell those mints apart at
/// the mint site — `def_eq_struct`'s `Const` arm is one line whether the
/// conversion was asked for or not — so the *entry* to the subtree marks it.
///
/// **What it was costing.** `nested_model`'s `iotaNode` pair, the residual this
/// was built to find, filed **4 108** mints: 2 675 at `def_eq_struct`'s `Const`
/// arm, 918 at `delta_evidence`'s first line, 181 at the `refl` closure, 144 at
/// `beta_evidence`. Every one of them is a decision-only call. `TRAIL_CAP` is
/// 4 096, so the pair *overflowed* and evicted from the front — which is where
/// the origin is, exactly the failure mode the cap's own note records against
/// its previous value of 64. Two seats read the 2 675 and the 918 as the
/// residual and scoped work off them; they are the acceptance walk.
///
/// Held as an RAII guard rather than a pair of calls because every site that
/// opens one returns through `?`.
///
/// # What the tests kill, measured
///
/// Three mutations, against
/// `kernel::tests::a_conversion_nobody_asked_for_files_nothing`:
///
/// ```text
/// KILLED   never open the scope in `def_eq_ev`
/// KILLED   never open the scope in `whnf_conv`
/// KILLED   never close it — `Drop` does nothing
/// ```
///
/// The second needs its own observation and has one: `is_def_eq` enters through
/// `def_eq_ev`, which quietens the whole subtree, so the two sites are
/// indistinguishable from there — and `whnf` has callers that never pass
/// through `def_eq_ev` at all (`is_prop`, the recursor arm's major,
/// `proj_data`'s subject). The third is asserted on [`is_quiet`] directly
/// rather than on a later empty trail, because a leak makes *every* subsequent
/// trail empty and so looks exactly like the property holding.
pub struct Quiet(());

impl Quiet {
    /// Open a quiet scope. Cheap enough for the hot path — one thread-local
    /// increment — but callers gate it on [`is_armed`] anyway, because unarmed
    /// there is no trail for it to protect.
    ///
    /// **Not `Default`.** Constructing this has an effect that lasts until the
    /// value is dropped, and `Quiet::default()` reads like a value rather than
    /// like a scope being entered.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        QUIET.with(|q| q.set(q.get() + 1));
        Quiet(())
    }
}

impl Drop for Quiet {
    fn drop(&mut self) { QUIET.with(|q| q.set(q.get().saturating_sub(1))); }
}

/// Is a [`Quiet`] scope open?
pub fn is_quiet() -> bool { QUIET.with(Cell::get) != 0 }

/// Should a mint be filed at all? Armed, and not inside a walk nobody asked a
/// certificate of.
fn filing() -> bool { is_armed() && !is_quiet() }

/// Begin a `(declaration, σ)`. The trail is per pair: a gap minted while
/// checking an earlier declaration is not evidence about this one.
pub fn enter_pair() { TRAIL.with(|t| t.borrow_mut().clear()); }

/// Record one gap mint. A no-op unarmed, checked here as well as at the call
/// site: the trail must never grow on an ordinary run, and one guard that
/// cannot be forgotten is worth more than one that is fast.
pub fn record(gap: &Gap, at: &'static Location<'static>) {
    if !filing() {
        return
    }
    TRAIL.with(|t| {
        let mut t = t.borrow_mut();
        if t.len() == TRAIL_CAP {
            t.pop_front();
        }
        t.push_back(Mint { gap: gap.clone(), file: at.file(), line: at.line() });
    });
}

/// Record one gap minted into an **`Err`** rather than into an
/// [`Ev`](crate::ev::Ev), and hand it back.
///
/// [`Ev::missing`](crate::ev::Ev::missing) is the only mint the trail used to
/// see, and a route that declines by `Err(Gap)` — `proj_data::typing`,
/// `proj_prop::typing`, `whnf_conv`'s callees — was invisible in it. The gap
/// still reached the report, because some caller downstream turned it into an
/// `Ev`, so the trail named the *forwarding* site and looked like an answer.
/// Two seats read `app_evidence`/`lam_evidence` off a `Nat.add` trail as the
/// place that gave up; neither is.
///
/// Use it through [`crate::gap!`], never bare: this takes `file`/`line` as
/// arguments instead of using `#[track_caller]` precisely because these routes
/// mint through a per-function `miss` closure, and `#[track_caller]` would
/// report the closure body — `blocker`'s own "one imprecision", which the macro
/// removes rather than documents.
pub fn record_line(gap: &Gap, file: &'static str, line: u32) {
    if !filing() {
        return
    }
    TRAIL.with(|t| {
        let mut t = t.borrow_mut();
        if t.len() == TRAIL_CAP {
            t.pop_front();
        }
        t.push_back(Mint { gap: gap.clone(), file, line });
    });
}

/// The mints recorded for the current pair, oldest first.
pub fn trail() -> Vec<Mint> { TRAIL.with(|t| t.borrow().iter().cloned().collect()) }

/// **Which of the four things a `(declaration, σ)` owes** was the one missing.
///
/// The order is the dependency order the ledger already runs them in, so the
/// first one that fails is the first one to fix. The type's *own* typing
/// (`⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`) is deliberately **not** in this list: it is
/// reported under "in hand" when it is missing, but it does not stop the run,
/// because a pair's deliverable is the constant's typing and stopping on a
/// sub-obligation that nothing downstream consumed would be stopping on
/// something that is not in anyone's way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Obligation {
    /// `infer_type` returned `Err` on a file mini accepted. Not a gap at all —
    /// the two axes have crossed, and that is a bug in mini.
    Inference,
    /// `⟦ty[σ]⟧`.
    TypeInterp,
    /// `⟦val[σ]⟧`.
    ValueInterp,
    /// `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` — the pair's deliverable.
    ConstTyping,
    /// `Sealed::new` refused a theorem at the store funnel: a hypothesis
    /// escaped its scope. Invariant I2 says this cannot happen on a correctly
    /// threaded run, so it is a threading bug surfaced where it should be.
    Unsealed,
}

impl Obligation {
    pub fn what(self) -> &'static str {
        match self {
            Obligation::Inference => "inference on an accepted declaration",
            Obligation::TypeInterp => "the type's interpretation, ⟦ty[σ]⟧",
            Obligation::ValueInterp => "the value's interpretation, ⟦val[σ]⟧",
            Obligation::ConstTyping => "the constant's typing, ⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧",
            Obligation::Unsealed => "a sealed theorem at the store funnel",
        }
    }
}

/// Everything Ursula needs to hand the next step to Tara.
///
/// **Every field is a `String` or a `Copy`**, and the report is rendered at
/// construction rather than at `Display` time. That is not tidiness: mini
/// checks each file on a 256 MB-stack worker thread, so an `Outcome` has to be
/// `Send`, and `Gap`, `Name` and `Expr` are all `Rc`-backed. Rendering inside
/// the worker — where the `Interp`, the gap and the trail are all still in
/// hand — is what lets the report cross the join.
#[derive(Debug, Clone)]
pub struct Blocker {
    /// The export file, filled in by [`crate::run`] once it knows it.
    pub export: String,
    /// The declaration, and σ against its own level parameters.
    pub decl: String,
    pub sigma: Vec<u32>,
    /// Which of the pair's obligations was the one missing.
    pub obligation: Obligation,
    /// The reason, spelled exactly as the ledger's `waiting:` column spells
    /// it — `proj(And)`, `recursor(Empty: no constructors)`. `inference-error`
    /// for [`Obligation::Inference`], which has no gap by construction.
    pub key: String,
    /// The axis, `None` for an inference error.
    pub cause: Option<Cause>,
    /// The whole report, ready to print.
    pub report: String,
}

impl std::fmt::Display for Blocker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The first line is the machine-readable one, in the same
        // tab-separated shape as the `ledger`/`evidence`/`convs` rows the
        // corpus tables already scrape.
        writeln!(f, "BLOCKED\t{}\t{}\t{}", self.export, self.decl, self.key)?;
        writeln!(f)?;
        writeln!(f, "  export       {}", self.export)?;
        f.write_str(&self.report)
    }
}

/// What the report is built from — the pair, and everything mini had in hand
/// when it gave up. [`crate::ledger`] fills this in; nothing else does.
pub struct Draft<'a> {
    pub decl: &'a Name,
    pub lparams: &'a [Name],
    pub sigma: &'a [u32],
    /// The declaration's type and value **at σ**, as Lean-level expressions.
    /// This is where the wanted obligation is stated exactly.
    pub ty: &'a E,
    pub val: Option<&'a E>,
    pub obligation: Obligation,
    pub gap: Option<Gap>,
    /// One line each, already rendered against the `Interp`.
    pub in_hand: Vec<String>,
}

impl Draft<'_> {
    /// `u := 0, v := 1`, or `—` at no level parameters.
    fn sigma_str(&self) -> String {
        if self.sigma.is_empty() {
            return "—".to_string()
        }
        self.sigma
            .iter()
            .enumerate()
            .map(|(i, n)| match self.lparams.get(i) {
                Some(p) => format!("{p} := {n}"),
                None => format!("?{i} := {n}"),
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Render. The trail is read here, so this must be called while the pair
    /// that produced it is still the current one.
    pub fn finish(self) -> Blocker {
        use std::fmt::Write;
        let key = crate::ledger::Ledger::key(self.gap.as_ref());
        let cause = self.gap.as_ref().map(Gap::cause);
        let trail = trail();
        let mut f = String::new();
        let _ = writeln!(f, "  declaration  {}", self.decl);
        let _ = writeln!(f, "  σ            {}", self.sigma_str());
        let _ = writeln!(f, "  obligation   {}", self.obligation.what());
        match cause {
            Some(c) => {
                let _ = writeln!(f, "  gap          {key}   [{c:?}]");
            }
            None => {
                let _ = writeln!(f, "  gap          — (inference error, not a gap)");
            }
        }

        let _ = writeln!(f, "\n  wanted");
        let _ = writeln!(f, "    c    {}", self.decl);
        let _ = writeln!(f, "    ty   {}", self.ty);
        if let Some(v) = self.val {
            let _ = writeln!(f, "    val  {v}");
        }
        let _ = match self.obligation {
            Obligation::ConstTyping | Obligation::Unsealed => {
                writeln!(f, "    ⊢ ⟦{}.{{σ}}⟧ ∈ ⟦{}⟧", self.decl, self.ty)
            }
            Obligation::TypeInterp => writeln!(f, "    ⟦{}⟧", self.ty),
            Obligation::ValueInterp => {
                writeln!(f, "    ⟦{}⟧", self.val.map(|v| v.to_string()).unwrap_or_default())
            }
            Obligation::Inference => Ok(()),
        };

        let _ = writeln!(f, "\n  in hand");
        if self.in_hand.is_empty() {
            let _ = writeln!(f, "    (nothing)");
        }
        for h in &self.in_hand {
            let _ = writeln!(f, "    {h}");
        }

        let own: Vec<&Mint> = match &self.gap {
            Some(g) => trail.iter().filter(|m| m.gap == *g).collect(),
            None => Vec::new(),
        };
        let _ = writeln!(f, "\n  gave up at");
        if own.is_empty() {
            let _ = writeln!(f, "    (no `Ev::missing` mint of this gap in this pair — it was either");
            let _ = writeln!(f, "     read back from the interpretation store, or built directly as a");
            let _ = writeln!(f, "     `Result` error; the construction sites below are where to look)");
        }
        for m in &own {
            let _ = writeln!(f, "    {}:{}", m.file, m.line);
            if let Some(src) = source_line(m.file, m.line) {
                let _ = writeln!(f, "      {}", src.trim());
            }
        }

        if let Some(g) = &self.gap {
            let sites = variant_sites(g);
            if !sites.is_empty() {
                let _ = writeln!(f, "\n  {} is constructed at", variant_name(g));
                for (file, line, src) in &sites {
                    let _ = writeln!(f, "    {file}:{line}");
                    let _ = writeln!(f, "      {}", src.trim());
                }
            }
        }

        // Rolled up by site: the acceptance-only calls mint `no-endpoint` at
        // the same three lines hundreds of times, and a flat listing would
        // bury everything above it. The count is kept because "once" and
        // "fifty times" say different things about what the pair was doing.
        let mut others: Vec<(String, &'static str, u32, usize)> = Vec::new();
        for m in trail.iter().filter(|m| Some(&m.gap) != self.gap.as_ref()) {
            let k = crate::ledger::Ledger::key(Some(&m.gap));
            match others.iter_mut().find(|o| o.0 == k && o.1 == m.file && o.2 == m.line) {
                Some(o) => o.3 += 1,
                None => others.push((k, m.file, m.line, 1)),
            }
        }
        if !others.is_empty() {
            let _ = writeln!(f, "\n  other gaps minted while checking this pair, by site");
            for (k, file, line, n) in &others {
                let times = if *n == 1 { String::new() } else { format!("   ×{n}") };
                let _ = writeln!(f, "    {k:<34} {file}:{line}{times}");
            }
        }

        Blocker {
            export: String::new(),
            decl: self.decl.to_string(),
            sigma: self.sigma.to_vec(),
            obligation: self.obligation,
            key,
            cause,
            report: f,
        }
    }
}

// ─────────────────────────────────────────────────────── source lookup ──

/// The workspace root, from this crate's manifest directory.
fn root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf()
}

/// The text of `file:line`, if it can be found. `Location::file()` is relative
/// to the workspace root under a cargo workspace build; both that and a
/// crate-relative reading are tried, so the report degrades to "no source
/// line" rather than to a wrong one.
pub fn source_line(file: &str, line: u32) -> Option<String> {
    let root = root();
    for cand in [root.join(file), root.join("mini").join(file), std::path::PathBuf::from(file)] {
        if let Ok(s) = std::fs::read_to_string(&cand) {
            return s.lines().nth(line.saturating_sub(1) as usize).map(str::to_string)
        }
    }
    None
}

/// `Gap::IndexedFamily`, as written in the source.
pub fn variant_name(g: &Gap) -> &'static str {
    match g {
        Gap::Axiom(_) => "Gap::Axiom",
        Gap::NoInterpretation(..) => "Gap::NoInterpretation",
        Gap::Quotient(..) => "Gap::Quotient",
        Gap::StructProj(_) => "Gap::StructProj",
        Gap::StructEta(_) => "Gap::StructEta",
        Gap::UnitLike(_) => "Gap::UnitLike",
        Gap::FunEta => "Gap::FunEta",
        Gap::IndexedFamily(..) => "Gap::IndexedFamily",
        Gap::PropInductive(_) => "Gap::PropInductive",
        Gap::IndUniverseHeight(..) => "Gap::IndUniverseHeight",
        Gap::IndFibreValue(_) => "Gap::IndFibreValue",
        Gap::IndSummand(_) => "Gap::IndSummand",
        Gap::IndSpec(..) => "Gap::IndSpec",
        Gap::IndApparatus => "Gap::IndApparatus",
        Gap::FunTypedRecArg(_) => "Gap::FunTypedRecArg",
        Gap::Recursor(..) => "Gap::Recursor",
        Gap::IndexedCtor(..) => "Gap::IndexedCtor",
        Gap::TruncCtor(..) => "Gap::TruncCtor",
        Gap::Iota(_) => "Gap::Iota",
        Gap::StuckRecursor(_) => "Gap::StuckRecursor",
        Gap::Skeleton => "Gap::Skeleton",
        Gap::Classifier => "Gap::Classifier",
        Gap::BinderCongruence(_) => "Gap::BinderCongruence",
        Gap::SortTowerHeight => "Gap::SortTowerHeight",
        Gap::ConvCompose(_) => "Gap::ConvCompose",
        Gap::NoDefiningEquation(_) => "Gap::NoDefiningEquation",
        Gap::NoEndpoint => "Gap::NoEndpoint",
        Gap::NotDecomposable => "Gap::NotDecomposable",
        Gap::EndpointDrift => "Gap::EndpointDrift",
        Gap::StrLit => "Gap::StrLit",
        Gap::SymbolicLevel => "Gap::SymbolicLevel",
    }
}

/// The `&'static str` detail a variant carries, when it carries one. Grepping
/// for the literal pins **one** line, which is what makes the detailed
/// variants — `Recursor`, `IndSpec`, `ConvCompose` — exactly locatable even
/// though they are minted through a closure.
fn detail(g: &Gap) -> Option<&'static str> {
    match g {
        Gap::Recursor(_, w, _) | Gap::IndSpec(_, w) | Gap::ConvCompose(w) => Some(w),
        _ => None,
    }
}

/// Every line of `mini/src` that constructs this gap. A grep, not an index:
/// the trail's `#[track_caller]` site is authoritative when it exists, and
/// this is what covers the closure-minted variants.
pub fn variant_sites(g: &Gap) -> Vec<(String, u32, String)> {
    let needle: String = match detail(g) {
        Some(d) => format!("\"{d}\""),
        None => variant_name(g).to_string(),
    };
    let dir = root().join("mini/src");
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(&dir) else { return out };
    let mut files: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    files.sort();
    for p in files {
        if p.extension().map(|x| x != "rs").unwrap_or(true) {
            continue
        }
        // `ev.rs` declares the variants and `blocker.rs` only names them;
        // listing those would bury the construction sites. `ledger.rs` stays
        // in — it mints `Gap::Axiom` and `Gap::Classifier` itself — with its
        // `Ledger::key` match arms filtered out below.
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        if matches!(name.as_str(), "ev.rs" | "blocker.rs") {
            continue
        }
        let Ok(src) = std::fs::read_to_string(&p) else { continue };
        // Only the crate's own code: a `#[cfg(test)]` fixture that names a gap
        // is not a place mini gave up.
        let lines: Vec<&str> = src.lines().collect();
        let end = lines.iter().position(|l| l.trim() == "#[cfg(test)]").unwrap_or(lines.len());
        for (i, line) in lines[..end].iter().enumerate() {
            let t = line.trim_start();
            if t.starts_with("//") || !line.contains(&needle) {
                continue
            }
            // A match arm that *reads* a gap — `Ledger::key`, `Gap::cause` —
            // is not a construction.
            if t.starts_with("Some(Gap::") || t.starts_with("| Gap::") || line.contains("=> Cause::")
            {
                continue
            }
            out.push((format!("mini/src/{name}"), i as u32 + 1, line.to_string()));
        }
    }
    // `Gap::NoInterpretation` is minted in a dozen places and listing all of
    // them buries the trail above it; the trail is the authoritative site.
    out.truncate(12);
    out
}

// ────────────────────────────────────────────────────── term rendering ──

/// The applicative structure of a kernel term, and the best name mini has for
/// each symbol in it.
///
/// Two sources, in order: the label registry mini fills for the terms it can
/// name, then [`Interp::parts_of`], which reads the spine off the term itself.
/// An unlabelled symbol prints as `f<id>`, and a term with no spine at all — a
/// bare variable — as `⟨·⟩`: honest, and the reason the *wanted* obligation
/// above is stated at the Lean level, where it is exact.
pub fn show_term(ip: &Interp, t: &kernel::Term, depth: usize) -> String {
    if let Some(l) = ip.label_of(t) {
        return l.to_string()
    }
    if depth == 0 {
        return "…".to_string()
    }
    match ip.parts_of(t) {
        Some((f, args)) => {
            let name = ip.sym_label(f).map(str::to_string).unwrap_or_else(|| format!("f{}", f.id()));
            if args.is_empty() {
                return name
            }
            let inner: Vec<String> = args.iter().map(|a| show_term(ip, a, depth - 1)).collect();
            format!("{name}({})", inner.join(", "))
        }
        None => "⟨·⟩".to_string(),
    }
}

/// A kernel formula in the same spirit: the connectives are public
/// (`as_mem`/`as_eq`/`as_imp`/`is_forall`), the terms are not.
pub fn show_formula(ip: &Interp, phi: &kernel::Formula) -> String {
    if let Some((a, b)) = phi.as_mem() {
        return format!("{} ∈ {}", show_term(ip, &a, 3), show_term(ip, &b, 3))
    }
    if let Some((a, b)) = phi.as_eq() {
        return format!("{} = {}", show_term(ip, &a, 3), show_term(ip, &b, 3))
    }
    if let Some((a, b)) = phi.as_imp() {
        return format!("({}) → ({})", show_formula(ip, &a), show_formula(ip, &b))
    }
    if phi.is_forall() {
        return "∀ …".to_string()
    }
    "⊥".to_string()
}

/// `⊢ φ`, or `h₁, … ⊢ φ` when the theorem still carries hypotheses.
pub fn show_thm(ip: &Interp, t: &kernel::Thm) -> String {
    let concl = show_formula(ip, t.concl());
    match t.hyps().len() {
        0 => format!("⊢ {concl}"),
        n => format!("[{n} hyp] ⊢ {concl}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Arming is per thread and the trail is per pair — a mint recorded for
    /// one pair must not be attributed to the next. Three mints, so the
    /// ordering and the clear are both pinned rather than only the count.
    #[test]
    fn the_trail_is_armed_ordered_and_cleared_per_pair() {
        arm(false);
        record(&Gap::FunEta, Location::caller());
        assert!(trail().is_empty(), "unarmed, nothing is recorded");

        arm(true);
        enter_pair();
        for g in [Gap::FunEta, Gap::StrLit, Gap::Skeleton] {
            record(&g, Location::caller());
        }
        let t = trail();
        assert_eq!(t.len(), 3);
        assert_eq!(t[0].gap, Gap::FunEta);
        assert_eq!(t[1].gap, Gap::StrLit);
        assert_eq!(t[2].gap, Gap::Skeleton, "the trail is oldest-first");

        enter_pair();
        assert!(trail().is_empty(), "a new pair starts with an empty trail");
        arm(false);
    }

    /// The variant grep must find the real construction sites, and the
    /// detail-carrying variants must resolve to the *one* line that mints
    /// them. Both halves matter: the first is what covers the closure-minted
    /// gaps, the second is what makes them exact.
    ///
    /// # The `IndexedFamily` half moved, and the move is the finding
    ///
    /// **Prior revision (through `9bb19c9`): this asserted `mini/src/zoneb.rs`.**
    /// It was right then and is false now: `zoneb::build`'s indexed branch used
    /// to *be* the decline, and it no longer mints `Gap::IndexedFamily` at all.
    /// Both classes the branch declines for have a route — [`crate::class_s_ix`]
    /// and [`crate::class_p_ix`] — so every indexed decline is now raised inside
    /// the route that tried, at the step that did not fit, rather than by a
    /// declaration-level guard that could only report the class. The assertion
    /// is rewritten to the route modules rather than relaxed to "any file",
    /// because the property under test is that the grep finds a *real* site.
    #[test]
    fn the_variant_grep_finds_construction_sites() {
        let sites = variant_sites(&Gap::IndexedFamily(Name::simple("RBTree"), ""));
        assert!(
            sites.iter().any(|(f, _, _)| f == "mini/src/class_s_ix.rs")
                && sites.iter().any(|(f, _, _)| f == "mini/src/class_p_ix.rs"),
            "Gap::IndexedFamily is minted by the two indexed routes; got {sites:?}"
        );
        let one = variant_sites(&Gap::IndSpec(Name::simple("T"), "nested occurrence"));
        assert_eq!(one.len(), 1, "the detail literal must pin exactly one line: {one:?}");
        assert_eq!(one[0].0, "mini/src/zoneb.rs");
    }

    /// A gap's source line is read back from the tree, not guessed. Reading
    /// the wrong file would print a plausible-looking wrong line, which is
    /// worse than none, so the content is checked.
    #[test]
    fn a_source_line_is_read_from_the_tree() {
        let sites = variant_sites(&Gap::IndSpec(Name::simple("T"), "nested occurrence"));
        let (file, line, text) = &sites[0];
        let read = source_line(file, *line).expect("the file is in the tree");
        assert_eq!(&read, text);
        assert!(read.contains("nested occurrence"));
    }
}
