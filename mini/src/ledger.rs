//! **The gap ledger**: what mini can and cannot interpret, per
//! `(declaration, σ)` on the real corpus, attributed by cause.
//!
//! # Interface
//!
//! ```text
//! Ledger::run(&[Declaration], &schedule) -> Ledger
//! ```
//!
//! # What this measures, and what it does not
//!
//! It runs the §6.2 dispatch over every declaration at every ground
//! instantiation the pre-pass scheduled, and records for each whether `⟦ty⟧`
//! and `⟦val⟧` were produced — and when they were not, the **first clause that
//! blocked**, not merely that something did. `mini/src/census.rs` counts
//! *nodes*; this counts *declarations*, which is the granularity that matters,
//! because one un-interpreted node at a declaration's root blocks all of it.
//!
//! It measures **both** of MINI-DESIGN.md §0's axes, kept apart:
//!
//! * *interpretation* — was `⟦ty⟧` / `⟦val⟧` produced at all;
//! * *evidence* — was `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` produced, and when not, **what
//!   kind of work** it is waiting on ([`Cause`]).
//!
//! The second axis is the one nanoda cannot produce today, because its ledger
//! mixes threading debt with library debt. Here they are separate columns, and
//! §0.4's rule is what keeps them separate: a gap's reason propagates from the
//! sub-result that caused it, never from the failing clause's own label. A
//! previous run filed 104 pairs as `pi-typing-unthreaded` when the cause was an
//! uninterpreted inductive several levels down; that is *scope*, not
//! *threading*, and the two must not trade places.
//!
//! # Measuring is not ordering
//!
//! A table of residual pairs sizes the work and says nothing about which one
//! to do next, and a run that files a gap and carries on files every gap that
//! exists only *because* of that one behind it. [`crate::blocker`] is the
//! other mode: armed, [`Ledger::run`] stops at the first `(declaration, σ)`
//! that owes something and reports it. Same traversal, same order, same `Gap`
//! vocabulary — the only difference is that it does not continue.
//!
//! # Nothing here searches
//!
//! Worth stating in those words, because it is the claim task #29 is built on.
//! Every constant's interpretation is read from the store by
//! `(name, ground levels)`; every `bvar`'s is read from the scope stack by
//! index; every clause is decided by `is_prop`/`is_prop_ev` or by a ground
//! level numeral (`body_clause` at the application, `is_prop_ev` at the λ, `l2`
//! at the `Π` — `term_clause` has no caller here), which is inference either
//! way. **No function in this path looks for a fact
//! it was not handed or cannot compute forward.** There is no fallback, no
//! retry, and no goal-directed matching anywhere in it.

use std::collections::BTreeMap;

use crate::env::{Declaration, DefKind, Environment};
use crate::ev::Gap;
use crate::expr::Name;
use crate::ground;
use crate::interp::{ConstInterp, Interp};
use crate::kernel::{Checker, Typing};

/// The interpretation and, when it is absent, the named reason.
fn split(t: crate::kernel::R<Typing>) -> (Option<kernel::Term>, Option<Gap>) {
    match t {
        Ok(t) => {
            let g = if t.tm.is_none() { t.ev.gap().cloned().or(Some(Gap::Classifier)) } else { None };
            (t.tm, g)
        }
        // Inference failed outright, which on an accepted file it should not.
        Err(_) => (None, None),
    }
}

/// What one `(declaration, σ)` produced, as the blocker report needs to read
/// it back. A view, borrowed from the loop body: bundling it is what keeps
/// [`PairView::blocker`] from being a twelve-argument function called twice.
struct PairView<'a> {
    name: &'a Name,
    lparams: &'a [Name],
    sigma: &'a [u32],
    /// The type and value **at σ** — what was actually interpreted.
    ty: &'a crate::expr::E,
    val: Option<&'a crate::expr::E>,
    ty_tm: Option<&'a kernel::Term>,
    /// Why `⟦ty[σ]⟧` / `⟦val[σ]⟧` is absent, when it is.
    ty_why: Option<&'a Gap>,
    val_why: Option<&'a Gap>,
    /// `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`.
    ty_ev: Option<&'a crate::ev::Ev>,
    val_tm: Option<&'a kernel::Term>,
    /// `⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧`, after the retarget.
    val_mem: Option<&'a crate::ev::Ev>,
    /// `⟦c.{σ}⟧`, once minted.
    c_term: Option<&'a kernel::Term>,
}

impl PairView<'_> {
    /// `⟦x⟧ = …`, or the named reason it is absent.
    fn line(ip: &Interp, what: &str, tm: Option<&kernel::Term>, why: Option<&Gap>) -> String {
        match tm {
            Some(t) => format!("{what}  =  {}", crate::blocker::show_term(ip, t, 3)),
            None => format!("{what}  —  absent ({})", Ledger::key(why)),
        }
    }

    /// The same for a piece of evidence.
    fn ev_line(ip: &Interp, what: &str, ev: Option<&crate::ev::Ev>) -> String {
        match ev {
            Some(crate::ev::Ev::Proved(t)) => {
                format!("{what}  =  {}", crate::blocker::show_thm(ip, t))
            }
            Some(crate::ev::Ev::Gap(g)) => format!("{what}  —  absent ({})", Ledger::key(Some(g))),
            None => format!("{what}  —  not attempted"),
        }
    }

    fn blocker(
        &self,
        ip: &Interp,
        (obligation, gap): (crate::blocker::Obligation, Option<Gap>),
    ) -> crate::blocker::Blocker {
        let mut in_hand = vec![
            Self::line(ip, "⟦ty[σ]⟧              ", self.ty_tm, self.ty_why),
            Self::ev_line(ip, "⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧ ", self.ty_ev),
        ];
        if self.val.is_some() {
            in_hand.push(Self::line(ip, "⟦val[σ]⟧             ", self.val_tm, self.val_why));
            in_hand.push(Self::ev_line(ip, "⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧ ", self.val_mem));
        }
        if let Some(t) = self.c_term {
            in_hand.push(Self::line(ip, "⟦c.{σ}⟧              ", Some(t), None));
        }
        crate::blocker::Draft {
            decl: self.name,
            lparams: self.lparams,
            sigma: self.sigma,
            ty: self.ty,
            val: self.val,
            obligation,
            gap,
            in_hand,
        }
        .finish()
    }
}

/// **What this run left uncertified** — the certification axis of
/// MINI-DESIGN.md §0, reduced to a verdict.
///
/// # What is in the set, and why exactly these
///
/// The project's claim is *every definitional-equality conclusion carries a
/// certificate*, and a run is **certified** when nothing it was asked for is
/// owed. The counters below are the obligations mini opens; a run is
/// uncertified iff one of them is nonzero.
///
/// **This is half of the axis.** The other half is [`Untranslated`], and it has
/// to be a second set rather than a fifth counter here for the reason its
/// header gives: a declaration that opens *no obligation* cannot be a shortfall
/// against `pairs`. The verdict and the exit code read both.
///
/// * [`Uncertified::const_typings`] — `pairs − constEv`. The headline
///   obligation: for each `(declaration, σ)`, `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`. Every
///   `waiting:` row and every interpretation gap ends here, because a pair
///   whose type or value did not interpret gets `typing: Err(…)` at the store
///   funnel. It is the *sum* of [`Ledger::missing`], which is why that map is
///   not counted separately.
/// * [`Uncertified::type_typings`] — `pairs − typeEv`. The other obligation the
///   ledger opens per pair, `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`. **In the set on evidence,
///   not on symmetry**, and the evidence is
///   `mini/tests/fixtures/beyond_the_tower.ndjson`: `constEv = 2`,
///   `typeEv = 1` — `Type 30 → Type 30`'s own sort is above
///   [`crate::interp::CUMUL_HEIGHT`], so the constant typing derives and the
///   type's does not. A definition watching only the line above would call that
///   run clean. (The two also move apart the other way, which is what
///   [`Ledger::type_ev_only_gap`] pinned at 0 says on the corpus.)
/// * [`Uncertified::conversions`] — [`crate::interp::ConvStats::gapped`]. A
///   conversion that reached its reduct with no certificate is the claim's own
///   sentence, negated. Nothing above it need be missing for this to be
///   nonzero: a gapped conversion inside a `def` whose typing came from
///   elsewhere leaves `constEv` untouched.
/// * [`Uncertified::unsealed`] — [`Ledger::unsealed`]. Zero on a correctly
///   threaded run *by I2*, so a nonzero count is a bug, and it is reported on
///   its own line rather than folded into `const_typings` (which it also moves)
///   because "a hypothesis escaped" and "no derivation exists" are different
///   findings with different fixes.
///
/// # One entry per *obligation*, not one per reason — and why that matters
///
/// The set above is closed under new gap kinds, and deliberately so. It does
/// not enumerate reasons; it enumerates the four things the ledger *asks for*.
/// A new [`Gap`] variant, a new refusal site in `kernel.rs`, a clause that
/// starts declining where it used to guess — none of them needs an entry here,
/// because every one of them reaches a caller as an absent `Ev`, and an absent
/// `Ev` on this path lands in a pair's `typing` (moving `const_typings`), in
/// its type's own typing (`type_typings`), or in a `Conv` (`conversions`).
/// That is not a hope: [`tests::every_reason_lands_in_a_counter_in_the_set`]
/// runs the ledger over declarations with unrelated gap kinds and asserts the
/// `missing` map sums to `const_typings` exactly.
///
/// The alternative — a counter per reason, ORed together — is what would have
/// to be revisited every time a zero-valued row is added, and this project's
/// record is that such a set silently stops being exhaustive.
///
/// **The closure has a boundary, and it is the pair.** Every sentence above is
/// about an absent `Ev` *on a `(declaration, σ)`'s path*. A declaration for
/// which the ledger schedules no pair — every `Declaration::Inductive`, every
/// `Declaration::Quot` — reaches none of these counters however loudly it
/// refuses, and no amount of closure under gap kinds fixes that. That is
/// [`Untranslated`]'s territory, discovered at `113_reduceCtorParamRefl`, which
/// read `accept … pairs=2 constEv=2 gapped=0` and exit 0 while carrying an
/// inductive mini had not translated.
///
/// # What is deliberately excluded
///
/// * `sealed < proved` and `movedSealed < moved`. **Nonzero on a legitimately
///   clean run** — 11 568 618 of 11 578 061 conversions seal on the tutorial
///   corpus, and the rest carry kernel hypotheses, which is what §0.3 measured
///   the ratio *for*. Certification is "a certificate exists", not "a
///   certificate is shareable".
/// * [`Ledger::type_ev_only_gap`] and [`Ledger::type_ev_masked`]. Both are
///   strict subsets of `pairs − typeEv` (each requires `ty_ev` unproved), so
///   including them would double-count. They stay on the `evidence` row as
///   instruments: they say *which* underived type typing it is, which is a
///   different question from whether one exists.
/// * [`Ledger::missing`], [`Ledger::blocked`] and
///   [`crate::interp::ConvStats::gapped_by`]. Attributions of counts already in
///   the set — `missing` sums to `const_typings`, `gapped_by` to
///   `conversions` — so they name causes rather than adding obligations.
/// * [`Ledger::first_blocker`]. `--block` is a development mode with an exit
///   code of its own; a blocked run's counters are partial by design and must
///   not be read as a census.
///
/// # The one place `const_typings` can over-report
///
/// [`Ledger::run`]'s store-hit path (`ip.get_const(&key).is_some()`) increments
/// `pairs` and `continue`s without touching `const_ev_ok`, so a repeated
/// `(name, σ)` would read as uncertified. It fires **zero** times on the
/// tutorial corpus — `constEv = pairs = 218` is that measurement — and the
/// schedule dedupes σ per name, so it is defensive. The direction is the safe
/// one: a repeat would raise a false alarm, never hide an owed derivation.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Uncertified {
    /// Pairs owing `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`.
    pub const_typings: usize,
    /// Pairs owing `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`.
    pub type_typings: usize,
    /// Conversions that reached their reduct with no certificate.
    pub conversions: usize,
    /// `Sealed::new` refusals at the store funnel — a threading bug, by I2.
    pub unsealed: usize,
}

impl Uncertified {
    /// Nothing owed. The condition for exit 0 on an accepted file.
    pub fn is_clean(&self) -> bool { *self == Uncertified::default() }

    /// The verdict line's fourth column, or `None` when there is nothing to
    /// say. A clean run's verdict must read exactly as it always has.
    pub fn column(&self) -> Option<String> {
        let parts: Vec<String> = [
            (self.const_typings, "const typing"),
            (self.type_typings, "type typing"),
            (self.conversions, "conversion"),
            (self.unsealed, "sealing refusal"),
        ]
        .into_iter()
        .filter(|(n, _)| *n > 0)
        .map(|(n, what)| format!("{n} {what}{}", if n == 1 { "" } else { "s" }))
        .collect();
        (!parts.is_empty()).then(|| format!("uncertified: {}", parts.join(", ")))
    }
}

/// **What this run did not translate at all** — the certification axis's
/// second half, and a *different kind of thing* from [`Uncertified`].
///
/// # Why this is its own axis and not a fifth `Uncertified` counter
///
/// [`Uncertified`] counts **obligations the ledger opened and did not
/// discharge**, and that is precisely what makes it closed under new [`Gap`]
/// kinds: every refusal anywhere reaches a caller as an absent `Ev`, and an
/// absent `Ev` on that path lands in one of its four counters.
///
/// A declaration that opens **no obligation at all** is outside that closure,
/// and it is not a corner case: `Declaration::Inductive` and `Declaration::Quot`
/// carry no interpretable expression pair, so [`Ledger::run`] schedules **zero**
/// pairs for them. `113_reduceCtorParamRefl` is the witness — one inductive,
/// `σ=[]`, no translation, and `pairs − constEv = 0` because there is no pair to
/// be short of. Folding this count into `Uncertified`'s sum would have bought
/// the number at the cost of the property: the sum would no longer be *the
/// obligations*, and the next reader deciding whether a new counter belongs
/// would have no rule to apply. So the two are separate structs, separate
/// columns, and one exit code.
///
/// **They may overlap, and that is not double-counting**, because they are
/// never added. An untranslated declaration that *is* used by a scheduled pair
/// shows up here **and** as that pair's `const_typings`; the two say different
/// true things — "this declaration has no translation" and "this pair's typing
/// is owed" — and a reader who saw only the second would not know how far the
/// hole extends.
///
/// # What is in the set
///
/// Exactly the three tables `zoneb` records a reason in, read off the `Interp`
/// at the end of the pass by [`Untranslated::of`]:
///
/// * [`Untranslated::declarations`] —
///   [`crate::interp::IndApparatus::untranslated`], by `(T, σ_T)`. A whole
///   declaration with no translation.
/// * [`Untranslated::constructors`] —
///   [`crate::interp::IndApparatus::ctor_untranslated`]. One constructor of an
///   indexed family, where the type former itself stood.
/// * [`Untranslated::eliminators`] —
///   [`crate::interp::IndApparatus::rec_untranslated`]. `⟦T.rec⟧` waiting on a
///   `derived/` construction. In the set even though a *use* of the recursor
///   also moves `const_typings`, for the reason above: `fill_declaration`
///   attempts the eliminator once, at the declaration, and an inductive whose
///   recursor no scheduled pair happens to mention would otherwise be silent in
///   exactly the way `113` is.
///
/// # The invariant, in the terms chosen here
///
/// > **No run reports clean while the tool knowingly did not translate
/// > something.** `Uncertified` covers everything the ledger *asked* for;
/// > `Untranslated` covers everything mini *recorded a refusal for*. A run
/// > exits 0 only when both are clean, and a recorded refusal that reached
/// > neither would be debt the verdict cannot see.
///
/// The two halves are guarded from opposite sides.
/// [`tests::every_reason_lands_in_a_counter_in_the_set`] holds the first: a new
/// `Gap` kind needs no entry here. [`tests::a_recorded_refusal_reaches_the_verdict`]
/// holds the second: each of the three tables, populated alone, makes the run
/// unclean and names itself. A **fourth** recorded-refusal table would need an
/// entry, and [`Untranslated::of`] is the one place to add it — which is why it
/// is a constructor over the whole `IndApparatus` rather than three call sites.
///
/// # This is not the arena's `decline`
///
/// [`crate::run::Verdict::Declined`] is exit **2**, a verdict about a *file*
/// carrying a feature mini does not support, and its population is the arena's
/// contract (`031`, `032`, mutual inductives). Nothing here may move a file into
/// it: an untranslated declaration sits in a file mini **accepted**. `zoneb`'s
/// header separates the three senses of the word.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Untranslated {
    /// Declarations with no translation.
    pub declarations: usize,
    /// Constructors of a translated family with no translation.
    pub constructors: usize,
    /// Eliminators waiting on a `derived/` construction.
    pub eliminators: usize,
    /// The same population, attributed by [`Ledger::key`] — an attribution of
    /// the counts above, as `missing` is of `const_typings`, so it is *not*
    /// itself part of [`Untranslated::is_clean`].
    pub by_reason: BTreeMap<String, usize>,
}

impl Untranslated {
    /// Read the three recorded-refusal tables off the interpretation machine.
    ///
    /// **The one place a fourth table would be added.** It runs at the end of
    /// [`Ledger::run`], where `ip` is still alive — the `Interp` is `Rc`-backed
    /// and does not cross the worker thread's join, so a count taken later
    /// cannot exist.
    pub fn of(ip: &Interp) -> Untranslated {
        let mut u = Untranslated::default();
        let Some(app) = ip.ind_opt() else { return u };
        for (table, n) in [
            (&app.untranslated, &mut u.declarations),
            (&app.ctor_untranslated, &mut u.constructors),
            (&app.rec_untranslated, &mut u.eliminators),
        ] {
            *n = table.len();
            for g in table.values() {
                *u.by_reason.entry(Ledger::key(Some(g))).or_default() += 1;
            }
        }
        u
    }

    /// Nothing was refused. Half of the condition for exit 0 on an accepted
    /// file; [`Uncertified::is_clean`] is the other half.
    pub fn is_clean(&self) -> bool {
        self.declarations == 0 && self.constructors == 0 && self.eliminators == 0
    }

    /// The verdict line's column, or `None` when there is nothing to say. A
    /// fully-translated run's verdict must read exactly as it always has.
    pub fn column(&self) -> Option<String> {
        let parts: Vec<String> = [
            (self.declarations, "declaration"),
            (self.constructors, "constructor"),
            (self.eliminators, "eliminator"),
        ]
        .into_iter()
        .filter(|(n, _)| *n > 0)
        .map(|(n, what)| format!("{n} {what}{}", if n == 1 { "" } else { "s" }))
        .collect();
        (!parts.is_empty()).then(|| format!("untranslated: {}", parts.join(", ")))
    }

    /// The verbose row, with one `key=count` per reason so the *why* is in the
    /// default `--verbose` output rather than only under `--dump-theorems`.
    pub fn row(&self) -> String {
        let mut s = format!(
            "untranslated\tdeclarations={}\tconstructors={}\teliminators={}",
            self.declarations, self.constructors, self.eliminators
        );
        for (k, v) in &self.by_reason {
            s.push_str(&format!("\tnotrans:{k}={v}"));
        }
        s
    }
}

/// One row per reason, so the residue is readable by cause.
#[derive(Debug, Default, Clone)]
pub struct Ledger {
    /// `(declaration, σ)` pairs attempted.
    pub pairs: usize,
    /// Pairs whose **type** interpreted.
    pub types_ok: usize,
    /// Pairs with a value (`def`/`theorem`/`opaque`) whose value interpreted.
    pub values_ok: usize,
    /// Pairs with a value at all.
    pub values_attempted: usize,
    /// Why an interpretation stopped, by first blocking cause.
    pub blocked: BTreeMap<String, usize>,
    /// Declarations whose *every* scheduled instantiation interpreted.
    pub fully_interpreted: usize,
    pub declarations: usize,
    // ── the evidence axis ────────────────────────────────────────────────
    /// Pairs whose type's own typing `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` was derived.
    pub type_ev_ok: usize,
    /// Pairs whose constant typing `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` was derived.
    pub const_ev_ok: usize,
    /// Why a constant typing was missing, by propagated reason.
    pub missing: BTreeMap<String, usize>,
    /// The same, rolled up to the axis it belongs to.
    pub by_cause: BTreeMap<&'static str, usize>,
    /// `Sealed::new` refusals at the store funnel. **Zero on a correctly
    /// threaded run**, by I2: at top level no scopes are open. A nonzero
    /// count is a threading bug surfaced where it should surface, and it is
    /// mini's analogue of nanoda's escaped-assumption ledger.
    pub unsealed: usize,
    /// Pairs whose **constant** typing was derived while the *type's own*
    /// typing `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` was not.
    ///
    /// Counted because it decides whether the type's typing belongs in
    /// [`crate::blocker::Obligation`]: if it is always zero, the two
    /// obligations are ordered and stopping on either is the same stop; if it
    /// is not, the type's typing is a sub-obligation nothing downstream
    /// consumed, and stopping on it would stop on something that is in no
    /// one's way. It is zero on the tutorial corpus, and the blocker
    /// deliberately does not stop on it.
    pub type_ev_only_gap: usize,
    /// Pairs whose type **interpreted** while its own typing
    /// `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` did not.
    ///
    /// # Why this needs a counter of its own, and what it costs not to have one
    ///
    /// The reason such a pair carries is **masked**: `⟦ty[σ]⟧` exists, so the
    /// blocker walks past `Obligation::TypeInterp` to the value's, and the
    /// pair's `waiting:` row names whatever stopped the *value*. Nothing was
    /// stepped over — [`Ledger::type_ev_only_gap`] pinned at zero is the
    /// statement that no constant typing outran its type's — but the row
    /// underneath the label is a different row, and this project's record is
    /// four for four that a masked reason is a different **size** than its
    /// label says.
    ///
    /// It is **0** on the tutorial corpus, and the one occupant it ever had is
    /// what this counter was built to find. *(This paragraph read "It is **1**
    /// … and the occupant is `117_accRecType`'s `accRecType` at `σ = [1,1]`";
    /// the row closed at `Acc.intro`'s typing.)* That row was waiting on
    /// `ind-spec(Acc: acc: Acc.intro's step hypothesis is not transported to
    /// preds_in)` — the *constructor's* typing, under a `waiting:` row labelled
    /// for the *eliminator* — so `Acc.intro` was a prerequisite for the pair
    /// rather than an optional extra, which is not what the label said, and
    /// building it moved `typeEv` by exactly one and moved nothing else.
    ///
    /// **A zero here is `MINI-DESIGN.md` §0.5's "read a zero row twice"**: it
    /// now means *no pair has a masked reason*, and it will mean *nothing has
    /// reached one* the moment a new clause lands. The instrument below is what
    /// tells the two apart, and it costs one build.
    ///
    /// # How to read the reason back
    ///
    /// The count is the ratchet; the reason is one throwaway away, and this is
    /// the whole of it, in a detached worktree, never committed:
    ///
    /// ```text
    /// } else if ty_tm.is_some() {
    ///     eprintln!("TYEV\t{name}\tsigma={sigma:?}\treason={}",
    ///         Ledger::key(ty_ev.as_ref().and_then(|e| e.gap())));
    /// }
    /// ```
    ///
    /// It is written down rather than left to be reinvented because the gap is
    /// already in `ty_ev` and is simply not reported — the value is one line,
    /// and rediscovering that it is one line is what costs.
    pub type_ev_masked: usize,
    /// The §0.3 conversion census, summed over the file.
    pub convs: crate::interp::ConvStats,
    /// The frame-local `infer_type` memo's hit rate, process-wide.
    pub frame_cache: crate::census::FrameCache,
    /// **Constant occurrences that had to build their own interpretation** —
    /// [`crate::interp::Interp::lazy_fills`], read off at the end of the run.
    ///
    /// A zero-firings ratchet, and the measurement that says the store is
    /// filled from the schedule rather than from what a use site happened to
    /// reach. It is reported rather than only asserted because `0` here is the
    /// claim that [`fill_declaration`] covered the file, and a claim is worth
    /// printing.
    pub lazy_fills: usize,
    /// **What the boundary recorded a refusal for** — see [`Untranslated`].
    ///
    /// On the certification axis and not the interpretation one: an entry here
    /// is something mini knowingly did not translate, in a file it accepted,
    /// and it reaches the verdict line and the exit code on its own.
    pub untranslated: Untranslated,
    /// **The first blocker**, when the run was armed. `Some` means the run
    /// stopped here and the counters above are partial by design.
    pub first_blocker: Option<crate::blocker::Blocker>,
}

impl Ledger {
    /// The row key for a gap — `waiting:proj(And)`'s `proj(And)`.
    ///
    /// `pub` because [`crate::blocker`] names a blocker with the *same* string
    /// the ledger would have counted it under. One vocabulary, two
    /// instruments: a blocker and a `waiting:` row that disagreed about what
    /// to call the same absence would be worse than either alone.
    pub fn key(g: Option<&Gap>) -> String {
        match g {
            Some(Gap::StructProj(n)) => format!("proj({n})"),
            Some(Gap::NoInterpretation(n, _)) => format!("no-interp({n})"),
            // **The level is in the key**, because the quotient row is two
            // clauses and every `Quot`-bearing declaration is scheduled at
            // both: a key without it cannot tell a half-closed row from an
            // untouched one. See [`Gap::Quotient`].
            //
            // **`u:1` and not `u = 1`** — the wire format is `key=value` and
            // the harness splits on the first `=`; see
            // [`tests::a_reason_key_is_wire_safe`], which exists because this
            // key was first spelled the other way.
            // **The primitive is in the key beside the level.** The `u ≥ 1`
            // half is four clauses; formation landed and this row did not
            // move, which is the same unmeasurability the level was added for.
            Some(Gap::Quotient(u, p)) => format!("quot-classes({}, u:{u})", p.name()),
            Some(Gap::Axiom(n)) => format!("axiom({n})"),
            Some(Gap::Iota(n)) => format!("iota({n})"),
            Some(Gap::StuckRecursor(n)) => format!("stuck-recursor({n})"),
            Some(Gap::UnitLike(n)) => format!("unit-like({n})"),
            Some(Gap::StructEta(n)) => format!("struct-eta({n})"),
            Some(Gap::PropInductive(n)) => format!("prop-inductive({n})"),
            Some(Gap::IndexedFamily(n, w)) => format!("indexed-family({n}: {w})"),
            Some(Gap::Recursor(n, w, _)) => format!("recursor({n}: {w})"),
            Some(Gap::IndexedCtor(n, w, _)) => format!("ctor({n}: {w})"),
            Some(Gap::TruncCtor(n, w)) => format!("ctor({n}: {w})"),
            Some(Gap::IndSummand(n)) => format!("ind-summand({n})"),
            Some(Gap::IndUniverseHeight(n, h)) => format!("ind-universe({n}>U{h})"),
            Some(Gap::IndFibreValue(n)) => format!("ind-fibre-value({n})"),
            Some(Gap::IndSpec(n, w)) => format!("ind-spec({n}: {w})"),
            Some(Gap::FunTypedRecArg(n)) => format!("fun-typed-rec-arg({n})"),
            Some(Gap::StrLit) => "strLit".to_string(),
            Some(Gap::SymbolicLevel) => "symbolic-level".to_string(),
            Some(Gap::Skeleton) => "skeleton".to_string(),
            Some(Gap::Classifier) => "classifier".to_string(),
            Some(Gap::NoEndpoint) => "no-endpoint".to_string(),
            Some(Gap::NotDecomposable) => "not-decomposable".to_string(),
            Some(Gap::BinderCongruence(r)) => format!("binder-congruence({})", r.tag()),
            Some(Gap::ConvCompose(w)) => format!("conv-compose({w})"),
            Some(Gap::EndpointDrift) => "endpoint-drift".to_string(),
            Some(Gap::FunEta) => "fun-eta".to_string(),
            Some(Gap::SortTowerHeight) => "sort-tower-height".to_string(),
            Some(other) => format!("{other:?}"),
            None => "inference-error".to_string(),
        }
    }

    fn note(&mut self, g: Option<&Gap>) { *self.blocked.entry(Self::key(g)).or_insert(0) += 1; }

    /// Record a missing constant typing, **by the axis it is waiting on**.
    fn note_missing(&mut self, g: Option<&Gap>) {
        *self.missing.entry(Self::key(g)).or_insert(0) += 1;
        let c = match g.map(Gap::cause) {
            Some(crate::ev::Cause::Scope) => "interpretation-scope",
            Some(crate::ev::Cause::Library) => "library-gap",
            Some(crate::ev::Cause::Threading) => "threading-incompleteness",
            Some(crate::ev::Cause::Bug) => "mini-bug",
            None => "inference-error",
        };
        *self.by_cause.entry(c).or_insert(0) += 1;
    }

    /// Run the interpretation over the whole file.
    ///
    /// Declarations in file order, σ inner — mini-lean's order for the first
    /// and MINI-DESIGN.md §3's for the second. A constant is minted **before**
    /// its type is interpreted, because a recursive declaration's own type may
    /// mention it, and a later declaration certainly will.
    ///
    /// # Armed, this stops
    ///
    /// When [`crate::blocker::is_armed`], the **first** `(declaration, σ)`
    /// that owes something it cannot produce ends the run:
    /// [`Ledger::first_blocker`] is set and the counters above are partial by
    /// design. Nothing else changes — the same obligations are attempted in
    /// the same order and are reported with the same [`Gap`] vocabulary — so a
    /// blocker is always a row the unarmed ledger would also have counted.
    pub fn run(
        env: &Environment,
        decls: &[Declaration],
        schedule: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
        ip: &mut Interp,
    ) -> Ledger {
        let mut led = Ledger::default();
        if crate::blocker::is_armed() {
            // The terms a report is most likely to have to name, named once.
            for n in 0..=crate::interp::CUMUL_HEIGHT as u32 {
                let s = ip.sort(n);
                ip.set_label(&s, format!("⟦Sort {n}⟧"));
            }
            let pt = ip.point();
            ip.set_label(&pt, "•");
        }
        // **The conversion census, while the run is still alive.** `conv_row`
        // prints once, at the end, which is exactly when a run that exhausts
        // memory has nothing to print: an aborted experiment yielded pass/fail
        // where it should have yielded a number. Gated, because on the corpus
        // this is one line per declaration and the census is not what most runs
        // are for.
        let trace = std::env::var_os("MINI_CONV_TRACE").is_some();
        for (done, d) in decls.iter().enumerate() {
            if trace {
                eprintln!(
                    "convtrace\t{done}\t{}\tproved={}\tsealed={}\tgapped={}",
                    d.name(),
                    ip.convs.proved,
                    ip.convs.sealed,
                    ip.convs.gapped
                );
            }
            let (name, lparams, ty, val) = match d {
                Declaration::Axiom { name, lparams, ty } => (name, lparams, ty, None),
                Declaration::Def { name, lparams, ty, value, .. } => {
                    (name, lparams, ty, Some(value))
                }
                // `Quot`'s four constants are built by the kernel and an
                // inductive's are built by §9 zone B, so neither has a
                // converted type or value for the walk below to interpret.
                // They are not skipped: [`fill_declaration`] puts every
                // constant they own into the store, at the instantiations the
                // schedule already predicted.
                Declaration::Quot
                | Declaration::Inductive { .. }
                | Declaration::Mutual { .. } => {
                    led.declarations += 1;
                    fill_declaration(env, ip, schedule, d);
                    continue
                }
            };
            led.declarations += 1;
            let sigmas: &[Vec<u32>] = schedule.get(name).map(|v| v.as_slice()).unwrap_or(&[]);
            let sigmas: Vec<Vec<u32>> =
                if sigmas.is_empty() { vec![vec![0; lparams.len()]] } else { sigmas.to_vec() };
            let mut all_ok = true;
            for sigma in &sigmas {
                led.pairs += 1;
                crate::blocker::enter_pair();
                // The obligation this pair could not discharge, at the finest
                // granularity, in dependency order — first one wins.
                let mut obl: Option<(crate::blocker::Obligation, Option<Gap>)> = None;
                let ty_g = ground::subst_ground(ty, lparams, sigma);
                let val_g = val.map(|v| ground::subst_ground(v, lparams, sigma));

                let mut c = Checker::threaded(env, ip);
                // `⟦ty⟧` is `infer_type(ty).tm`: one traversal, both results,
                // and the reason for a missing one is the `Typing`'s own `ev`.
                let ty_t = c.infer_type(&ty_g);
                let ty_ev = ty_t.as_ref().ok().map(|t| t.ev.clone());
                let ty_err = ty_t.is_err();
                let (ty_tm, ty_blocked) = split(ty_t);
                // **The `def`/`theorem` pipeline of §8.** The value's own
                // typing is transported along the conversion the acceptance
                // gate produces, and then along the constant's defining
                // equation: `⊢ ⟦val⟧ ∈ ⟦valTy⟧` ↦ `⊢ ⟦val⟧ ∈ ⟦ty⟧` ↦
                // `⊢ ⟦c⟧ ∈ ⟦ty⟧`. Nothing is re-derived and nothing is
                // discarded; the `Conv` this consumes is the reason
                // `assert_def_eq` returns one.
                let mut val_mem: Option<crate::ev::Ev> = None;
                let (val_tm, val_blocked) = match &val_g {
                    Some(v) => {
                        let tv = c.infer_type(v);
                        if let (Ok(tv), Some(want)) = (&tv, ty_tm.clone()) {
                            val_mem = Some(c.retarget_to(tv, &ty_g, want));
                        }
                        split(tv)
                    }
                    None => (None, None),
                };
                drop(c);

                if ty_tm.is_some() {
                    led.types_ok += 1;
                } else {
                    all_ok = false;
                    led.note(ty_blocked.as_ref());
                }
                if ty_ev.as_ref().is_some_and(|e| e.is_proved()) {
                    led.type_ev_ok += 1;
                } else if ty_tm.is_some() {
                    // The type interpreted and its own typing did not, so this
                    // pair's `waiting:` row is about something else. See
                    // [`Ledger::type_ev_masked`] for why that is counted rather
                    // than left to be noticed.
                    led.type_ev_masked += 1;
                }
                if val_g.is_some() {
                    led.values_attempted += 1;
                    if val_tm.is_some() {
                        led.values_ok += 1;
                    } else {
                        all_ok = false;
                        led.note(val_blocked.as_ref());
                    }
                }

                // The interpretation obligations, in dependency order. The
                // type's *own* typing is not among them — see
                // `Ledger::type_ev_only_gap`.
                if ty_err {
                    obl = Some((crate::blocker::Obligation::Inference, None));
                } else if ty_tm.is_none() {
                    obl = Some((crate::blocker::Obligation::TypeInterp, ty_blocked.clone()));
                } else if val_g.is_some() && val_tm.is_none() {
                    obl = Some((crate::blocker::Obligation::ValueInterp, val_blocked.clone()));
                }
                // The pair, as the report reads it back. `c_term` is filled in
                // once `⟦c.{σ}⟧` exists; the store-hit path below reports
                // before it does.
                let mut pv = PairView {
                    name,
                    lparams,
                    sigma,
                    ty: &ty_g,
                    val: val_g.as_ref(),
                    ty_tm: ty_tm.as_ref(),
                    ty_why: ty_blocked.as_ref(),
                    val_why: val_blocked.as_ref(),
                    ty_ev: ty_ev.as_ref(),
                    val_tm: val_tm.as_ref(),
                    val_mem: val_mem.as_ref(),
                    c_term: None,
                };

                // Mint `⟦c.{σ}⟧`. A transparent definition whose value
                // interpreted gets an **abbreviation**, whose defining axiom is
                // also delta reduction's certificate; everything else gets an
                // opaque symbol, which is a signature extension and asserts
                // nothing about inhabitation — hence the `Gap` on its typing.
                let key = (*name, sigma.clone());
                if ip.get_const(&key).is_some() {
                    if let (true, Some(o)) = (crate::blocker::is_armed(), obl) {
                        led.first_blocker = Some(pv.blocker(ip, o));
                        return led
                    }
                    continue
                }
                let transparent = matches!(
                    d,
                    Declaration::Def { kind: DefKind::Def | DefKind::Theorem, .. }
                );
                // §0.4: a missing typing carries the reason of the sub-result
                // that stopped it, never the failing clause's own label.
                //
                // Two rounds of getting this wrong are on the record. Using
                // `Gap::Axiom` as the *fallback* filed 57 theorems as
                // assumptions. Then it fired **unconditionally** on an axiom,
                // ahead of the `ty_blocked` check — and that is the same
                // mistake one step in, because a declaration being an axiom
                // says nothing about *why* its typing is missing when its type
                // did not even interpret.
                //
                // `123_quotSoundType` decides it inside one file.
                // `quotSoundType`'s value is literally `Quot.sound.{u}` — the
                // same constant under a second name, at the same type. One
                // copy was filed `no-interp(Quot)` and the other
                // `axiom(Quot.sound)`: the same obligation, on two different
                // axes, in the same file. The interpretation one is right, and
                // an axiom only reaches `Gap::Axiom` once its type interprets
                // and the missing thing really is the inhabitation.
                //
                // **The interpretation's third insertion point.** An axiom's
                // inhabitation is the one obligation with no constant
                // occurrence to hang off, so `zoneb::ensure` and
                // `crate::direct` structurally cannot see it; the declaration
                // walk is the only thing that ever asks. Attempted here, and
                // only once the type has interpreted, so that a clause can
                // never stand in front of the reason above. See
                // [`crate::axiom`].
                let axiom_ev: Option<Result<crate::ev::Sealed, Gap>> = match (d, &ty_tm) {
                    (Declaration::Axiom { .. }, Some(want)) => crate::axiom::clause_for(name)
                        .map(|cl| {
                            let mut c = Checker::threaded(env, ip);
                            crate::axiom::inhabit(&mut c, cl, name, sigma, want)
                                .and_then(|t| crate::ev::Sealed::new(t).map_err(|_| Gap::Skeleton))
                        }),
                    _ => None,
                };
                let no_val = match d {
                    // An axiom has no value, so `val_blocked` is `None` here by
                    // construction; the type is the only sub-result there is.
                    // A clause that was tried and declined reports **its** own
                    // reason: `Gap::Axiom` means "nothing here can inhabit it",
                    // and a clause that got as far as a nest knows better.
                    Declaration::Axiom { .. } => ty_blocked
                        .clone()
                        .or_else(|| axiom_ev.as_ref().and_then(|r| r.as_ref().err().cloned()))
                        .unwrap_or(Gap::Axiom(*name)),
                    _ => val_blocked
                        .clone()
                        .or_else(|| ty_blocked.clone())
                        .unwrap_or(Gap::Classifier),
                };
                let mut escaped = false;
                let entry = match val_tm.clone() {
                    // The value interpreted, so `⟦c.{σ}⟧` is an
                    // **abbreviation** for it — a conservative definitional
                    // extension whose axiom is also delta reduction's
                    // certificate. `opaque` gets the abbreviation and hence the
                    // typing, but not the equation: opacity is a *checker*
                    // policy, not a fact about the model.
                    Some(v) => match ip.abbrev(&v) {
                        Some((t, ax)) => {
                            // `⊢ ⟦c⟧ ∈ ⟦ty⟧`, from `⊢ ⟦val⟧ ∈ ⟦ty⟧` carried
                            // back along `⊢ ⟦c⟧ = ⟦val⟧`.
                            let typing = match val_mem.clone() {
                                Some(crate::ev::Ev::Proved(m)) => {
                                    match ip.retarget_subject(&m, &ax) {
                                        Some(t) => match crate::ev::Sealed::new(t) {
                                            Ok(s) => Ok(s),
                                            Err(_) => {
                                                led.unsealed += 1;
                                                escaped = true;
                                                Err(Gap::Skeleton)
                                            }
                                        },
                                        None => Err(Gap::ConvCompose("store-retarget")),
                                    }
                                }
                                Some(crate::ev::Ev::Gap(g)) => Err(g),
                                None => Err(no_val.clone()),
                            };
                            ConstInterp {
                                term: t,
                                typing,
                                defeq: if transparent {
                                    crate::ev::Sealed::new(ax).ok()
                                } else {
                                    None
                                },
                            }
                        }
                        None => ConstInterp {
                            term: ip.opaque(),
                            typing: Err(Gap::Skeleton),
                            defeq: None,
                        },
                    },
                    // **An inhabited axiom denotes `•`, not an opaque symbol.**
                    // A clause at insertion point 3 produced `⊢ • ∈ ⟦ty[σ]⟧`,
                    // so the term it is about is the one that goes in the
                    // store; handing back the opaque symbol beside the theorem
                    // would put a membership and a denotation in the store that
                    // are not about the same thing.
                    None if matches!(axiom_ev, Some(Ok(_))) => ConstInterp {
                        term: ip.point(),
                        typing: axiom_ev.clone().expect("matched Some(Ok)"),
                        defeq: None,
                    },
                    // A fresh opaque symbol is a pure signature extension: it
                    // is conservative on its own, but that it *denotes an
                    // inhabitant* of anything is exactly what is not derivable.
                    //
                    // **A sort-valued axiom is not a special case here**, and
                    // `cc0f898` was reverted for saying it was: `⟦A⟧ ∈ Uₙ` is
                    // derivable, but the export that declares `axiom A : Prop`
                    // is declined at the frontend before this walk runs
                    // (`crate::run::check_file_with`), so a sort-valued axiom
                    // reaches this arm only from an in-memory fixture. From a
                    // *file*, the axioms that get here are Lean's own without a
                    // clause in `crate::axiom` — `propext`, `Classical.choice`.
                    None => ConstInterp {
                        term: ip.opaque(),
                        typing: Err(no_val.clone()),
                        defeq: None,
                    },
                };
                match &entry.typing {
                    Ok(_) => {
                        led.const_ev_ok += 1;
                        // The measurement that decides whether the type's own
                        // typing belongs among the blocking obligations.
                        if ty_ev.as_ref().is_some_and(|e| !e.is_proved()) {
                            led.type_ev_only_gap += 1;
                        }
                    }
                    Err(g) => {
                        led.note_missing(Some(g));
                        if obl.is_none() {
                            let o = if escaped {
                                crate::blocker::Obligation::Unsealed
                            } else {
                                crate::blocker::Obligation::ConstTyping
                            };
                            obl = Some((o, Some(g.clone())));
                        }
                    }
                }
                if let (true, Some(o)) = (crate::blocker::is_armed(), obl) {
                    pv.c_term = Some(&entry.term);
                    led.first_blocker = Some(pv.blocker(ip, o));
                    ip.put_const(key, entry);
                    // Partial, like every counter on this path — but taken, so
                    // the verdict line a blocked run prints before the report
                    // is not a *false* "everything translated".
                    led.untranslated = Untranslated::of(ip);
                    return led
                }
                ip.put_const(key, entry);
            }
            if all_ok {
                led.fully_interpreted += 1;
            }
        }
        led.convs = ip.convs.clone();
        // Read on the worker thread, which is the only one that ran a
        // `Checker`; the counter is thread-local and does not cross the join.
        led.frame_cache = crate::census::frame_cache();
        led.lazy_fills = ip.lazy_fills;
        // **The certification axis's second half**, read off where `ip` is: an
        // absence that opened no obligation is invisible in every counter
        // above, and `113_reduceCtorParamRefl` is the file that proves it.
        led.untranslated = Untranslated::of(ip);
        led
    }

    /// **What this run left uncertified** — see [`Uncertified`] for which
    /// counters are in the set and which are deliberately not.
    pub fn uncertified(&self) -> Uncertified {
        Uncertified {
            const_typings: self.pairs.saturating_sub(self.const_ev_ok),
            type_typings: self.pairs.saturating_sub(self.type_ev_ok),
            conversions: self.convs.gapped,
            unsealed: self.unsealed,
        }
    }

    /// The row format the corpus tables scrape.
    pub fn row(&self) -> String {
        let mut s = format!(
            "ledger\tdeclars={}\tpairs={}\ttypesOk={}\tvaluesOk={}/{}\tfullyInterpreted={}",
            self.declarations,
            self.pairs,
            self.types_ok,
            self.values_ok,
            self.values_attempted,
            self.fully_interpreted
        );
        for (k, v) in &self.blocked {
            s.push_str(&format!("\t{k}={v}"));
        }
        s
    }

    /// The evidence axis, as its own row: what was derived, and what the rest
    /// is waiting on.
    pub fn evidence_row(&self) -> String {
        let mut s = format!(
            "evidence\tpairs={}\ttypeEv={}\tconstEv={}\tunsealed={}\ttypeEvOnlyGap={}\
             \ttypeEvMasked={}\tlazyFills={}",
            self.pairs,
            self.type_ev_ok,
            self.const_ev_ok,
            self.unsealed,
            self.type_ev_only_gap,
            self.type_ev_masked,
            self.lazy_fills
        );
        for (k, v) in &self.by_cause {
            s.push_str(&format!("\t{k}={v}"));
        }
        for (k, v) in &self.missing {
            s.push_str(&format!("\twaiting:{k}={v}"));
        }
        s
    }

    /// The §0.3 conversion census: how many conversions are hypothesis-free.
    /// The frame-local memo's own row — separate from `conv_row`, whose key
    /// set is asserted exhaustively by `tutorial_conversion_split`.
    pub fn frame_row(&self) -> String {
        let f = self.frame_cache;
        let n = f.hits + f.misses;
        format!(
            "framecache\thits={}\tmisses={}\tcalls={n}\thitRate={:.1}%",
            f.hits,
            f.misses,
            100.0 * f.hits as f64 / n.max(1) as f64
        )
    }

    pub fn conv_row(&self) -> String {
        format!(
            "convs\tproved={}\tsealed={}\tgapped={}\tmoved={}\tmovedSealed={}{}",
            self.convs.proved,
            self.convs.sealed,
            self.convs.gapped,
            self.convs.moved,
            self.convs.moved_sealed,
            // …then one column per reason, `convGap:<the ledger's own key>`, so
            // a conversion-level census and a declaration-level one can be read
            // against each other rather than only side by side.
            self.convs
                .gapped_by
                .iter()
                .map(|(k, n)| format!("\tconvGap:{k}={n}"))
                .collect::<String>()
        )
    }
}

/// **Fill the store for a declaration whose constants have no converted
/// expressions** — an inductive's, or `Quot`'s four primitives.
///
/// The walk above interprets a `def`/`theorem`/`axiom` by *reading its type
/// and value*, and mints `⟦c.{σ}⟧` once per scheduled `σ`. An inductive has
/// neither: its constants are built by [`crate::zoneb`] out of the
/// declaration, and `Quot`'s are §6.2 clauses. So they are filled here, from
/// the **same schedule** the walk above is driven by, at the moment the
/// declaration is reached.
///
/// # Why the schedule and not the use sites
///
/// `checker::instantiations` already computed, by a worklist fixpoint over the
/// export file, every `(declaration, σ)` this run will ask for — including an
/// inductive's, and including the constructor types' own edges, which are
/// attributed to the inductive's node precisely because *this* checker
/// interprets them whenever the inductive is interpreted. Filling on a store
/// miss instead makes the store's population a function of what is
/// *reachable*: an inductive declared and never used at a ground level was
/// never asked whether it is interpretable at all, so a decline it owes was
/// never recorded. Reading the schedule makes it a function of the file.
///
/// Each name is filled at **its own** schedule entry, not at the inductive's:
/// a recursor's instantiation carries the motive's level in front of the
/// declaration's, and `zoneb::ensure` is keyed on the constant's own list.
///
/// Errors are dropped on purpose. A decline is *recorded* by `ensure` — under
/// the declaration's key in `IndApparatus::declined`, or the constructor's in
/// `ctor_declined` — and the consumer that needs it is the constant occurrence
/// that reports it, which reads the same tables. Nothing here counts, because
/// an inductive is not a `(declaration, σ)` pair of the ledger.
pub(crate) fn fill_declaration(
    env: &Environment,
    ip: &mut Interp,
    schedule: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
    d: &Declaration,
) {
    let names: Vec<Name> = match d {
        Declaration::Inductive { name, ctors, .. } => {
            // The type former, then its constructors, then the recursor mini
            // generates for it (`kernel::add`'s `Name::str(ind, "rec")` — the
            // export's recursor declaration is audited, never read).
            //
            // **The recursor half is load-bearing and the constructor half is
            // not**, measured the same way: dropping `T.rec` leaves the miss
            // path firing on 25 of the corpus's 91 exports, and dropping the
            // constructors leaves it firing on none. `zoneb::ensure(T, σ)`
            // stores every `⟦T.ctorᵢ.{σ}⟧` alongside `⟦T.{σ}⟧`, and a
            // constructor's own schedule entry cannot outrun the declaration's,
            // because its type mentions the declaration at the declaration's
            // own parameters — so demanding `(T.ctorᵢ, σ)` demands `(T, σ)`.
            // The loop is kept because that containment is a property of the
            // *export file's* well-formedness rather than of this module, and
            // a second `ensure` at a key already in the store is one hash
            // lookup.
            //
            // **A nested declaration owns more than one recursor**, and the
            // list is the splice's rather than this one: `Tree.rec_1`
            // eliminates `List Tree` and is not `Name::str(name, "rec")` under
            // any spelling. Reached lazily it would still be built, at the cost
            // of a `lazyFills` this project pins at zero and of a reason
            // reported from the miss path rather than from the declaration.
            // `ind_opt`, not `ind_apparatus`: the read must not *build* the
            // apparatus. `crate::run` fills the table, which needs the
            // apparatus, so a file with a nested declaration has one by now and
            // a file without one is unchanged — including in the dump, which
            // reports an apparatus that exists.
            if let Some(r) = ip.ind_opt().and_then(|a| a.nested.get(name)) {
                r.constants.clone()
            } else {
                let mut v = Vec::with_capacity(ctors.len() + 2);
                v.push(*name);
                v.extend(ctors.iter().map(|(n, _)| *n));
                v.push(Name::str(name, "rec"));
                v
            }
        }
        // `add_quot` mints all four when it sees the `Quot` declaration, and
        // `convert::load` pushes exactly one [`Declaration::Quot`] for it, so
        // this arm names all four itself. **The order is `add_quot`'s**, and it
        // is load-bearing: `Quot.mk`'s type mentions `Quot`, and `Quot.ind`'s
        // mentions `Quot.mk`, so filling `ind` first leaves `mk`'s
        // interpretation to be found rather than already built. Measured — with
        // the order reversed, the miss path fires on `Quot.mk` at every one of
        // the corpus's six `Quot` exports.
        Declaration::Quot => {
            let q = Name::simple("Quot");
            vec![q, Name::str(&q, "mk"), Name::str(&q, "lift"), Name::str(&q, "ind")]
        }
        Declaration::Axiom { .. } | Declaration::Def { .. } => return,
        // **A mutual block does not go to zone B, and the absence is recorded
        // rather than left to be discovered.**
        //
        // `zoneb::ensure` resolves a name to its declaration through the
        // *environment*, where a block's members are indistinguishable from
        // single inductives — so calling it here would not decline, it would
        // silently translate `Exp` as if `Stm` did not exist. The block is
        // written into `untranslated`/`ctor_untranslated`/`rec_untranslated`
        // directly, at the keys zone B's three-table miss path already reads,
        // so an occurrence of a member reports `ind-spec(Exp: mutual)` and not
        // a bare `no-interp`. This is what makes the arc's next step visible:
        // when the aux encoding lands, these entries stop being written and
        // the fixtures' `waiting:` rows name what is left.
        Declaration::Mutual { types, .. } => {
            // **The reason names the shape, not the feature.** A block reaches
            // here only when `mutual_aux::expand` left it alone, and the
            // encoder knows exactly why it did; asking it again costs one
            // environment clone per declined block and turns
            // `ind-spec(T0: mutual)` into `ind-spec(T0: mutual with indices)`,
            // which is the difference between "not supported" and a named
            // increment. `NotABlock` cannot arise — this *is* a block — and its
            // label is the generic word, so the fallback reads correctly too.
            let why = crate::mutual_aux::encode(env, d)
                .err()
                .unwrap_or(crate::mutual_aux::Reason::NotABlock)
                .label();
            for t in types {
                let g = crate::ev::Gap::IndSpec(t.name, why);
                let mut keys: Vec<(Name, bool)> = vec![(t.name, false)];
                keys.extend(t.ctors.iter().map(|(n, _)| (*n, false)));
                keys.push((Name::str(&t.name, "rec"), true));
                for (n, is_rec) in keys {
                    let Some(sigmas) = schedule.get(&n) else { continue };
                    for sigma in sigmas {
                        let mut c = Checker::threaded(env, ip);
                        let Some(app) = c.interp().and_then(|i| i.ind_apparatus()) else { continue };
                        let key = (n, sigma.clone());
                        if is_rec {
                            app.rec_untranslated.insert(key, g.clone());
                        } else if n == t.name {
                            app.untranslated.insert(key, g.clone());
                        } else {
                            app.ctor_untranslated.insert(key, g.clone());
                        }
                    }
                }
            }
            return
        }
    };
    for n in &names {
        let Some(sigmas) = schedule.get(n) else { continue };
        for sigma in sigmas {
            let mut c = Checker::threaded(env, ip);
            let _ = crate::zoneb::ensure(&mut c, n, sigma);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{app, bvar, forall, konst, lam, sort, Level, E};

    /// **Every reason key must survive the wire format**, which is
    /// tab-separated `key=value` on the `evidence` row and is split on the
    /// *first* `=`. A key containing `=` or a tab parses as a truncated name
    /// with a non-numeric value, and the corpus harness panics **in its
    /// parser** — not in an assertion, so the failure names a line of
    /// `tutorial.rs` and not the key that caused it.
    ///
    /// *(Written after a `Quot` reason key was first spelled
    /// `quot-classes(u = 1)` and did exactly that: `tutorial_evidence_ledger`
    /// panicked at its own `split_once('=').expect("k=v")`, naming a line of
    /// the harness and not the key that caused it. The clause that key belonged
    /// to is not in the tree; this is. Nothing enforced the format — the keys
    /// are built by `format!` in one `match` arm each, and every existing one
    /// **happened** to be safe, which is the shape this project has a rule
    /// about.)*
    ///
    /// Exhaustive over the variants that interpolate caller-supplied data,
    /// since those are the ones a future key can go wrong in.
    #[test]
    fn a_reason_key_is_wire_safe() {
        let n = Name::simple("T");
        let gaps = [
            Gap::NoInterpretation(n, vec![0, 1]),
            Gap::Quotient(0, crate::quot::Prim::Quot),
            Gap::Quotient(1, crate::quot::Prim::Mk),
            Gap::Axiom(n),
            Gap::StructProj(n),
            Gap::StructEta(n),
            Gap::UnitLike(n),
            Gap::IndSpec(n, "a reason with spaces"),
            Gap::Recursor(n, "a reason with spaces", crate::ev::Cause::Threading),
        ];
        for g in &gaps {
            let k = Ledger::key(Some(g));
            assert!(!k.contains('='), "reason key {k:?} contains '=' and breaks `key=value`");
            assert!(!k.contains('\t'), "reason key {k:?} contains a tab and breaks the row");
            assert!(!k.is_empty(), "an empty reason key is not a reason");
        }
        assert!(!Ledger::key(None).contains('='));
    }

    /// **Which counters make a run uncertified**, asserted rather than
    /// narrated — this is the definition of the tool's central claim, and
    /// `Uncertified`'s header is prose that a mutation cannot refute.
    ///
    /// Two directions, and both are load-bearing:
    ///
    /// * every counter *in* the set makes an otherwise-clean ledger dirty, one
    ///   at a time, so none of them can be dropped without a failure here;
    /// * every counter deliberately *outside* it leaves a clean ledger clean,
    ///   so none of them can be added without a failure here either. The second
    ///   half is the one that matters: `sealed < proved` is nonzero on 9 443 of
    ///   the tutorial corpus's conversions, and a definition that included it
    ///   would report the fully-closed corpus as uncertified.
    #[test]
    fn uncertified_is_exactly_these_four_counters() {
        // A clean ledger with *work in it* — a set of counters that reported
        // "all fine" on an empty run would prove nothing.
        let clean = Ledger {
            pairs: 3,
            types_ok: 3,
            values_ok: 2,
            values_attempted: 2,
            fully_interpreted: 3,
            declarations: 3,
            type_ev_ok: 3,
            const_ev_ok: 3,
            convs: crate::interp::ConvStats {
                proved: 100,
                // **Deliberately below `proved`.** A conversion that carries
                // kernel hypotheses is certified; it is merely not shareable.
                sealed: 60,
                gapped: 0,
                moved: 40,
                moved_sealed: 10,
                gapped_by: Default::default(),
            },
            ..Ledger::default()
        };
        assert!(clean.uncertified().is_clean(), "{:?}", clean.uncertified());
        assert_eq!(clean.uncertified().column(), None, "a clean run says nothing");

        // ── in the set ───────────────────────────────────────────────────
        let mut l = clean.clone();
        l.const_ev_ok = 1;
        assert_eq!(l.uncertified().const_typings, 2);
        assert!(!l.uncertified().is_clean(), "an underived ⊢ ⟦c.{{σ}}⟧ ∈ ⟦ty[σ]⟧ is debt");

        let mut l = clean.clone();
        l.type_ev_ok = 2;
        assert_eq!(l.uncertified().type_typings, 1);
        // **The half a `constEv`-only definition would have missed.**
        // `mini/tests/fixtures/beyond_the_tower.ndjson` is the real witness:
        // `constEv = 2`, `typeEv = 1`, and the arrow's own sort is genuinely
        // owed.
        assert!(!l.uncertified().is_clean(), "an underived ⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧ is debt");

        let mut l = clean.clone();
        l.convs.gapped = 7;
        assert_eq!(l.uncertified().conversions, 7);
        assert!(!l.uncertified().is_clean(), "an uncertified conversion is the claim, negated");

        let mut l = clean.clone();
        l.unsealed = 1;
        assert_eq!(l.uncertified().unsealed, 1);
        assert!(!l.uncertified().is_clean(), "a sealing refusal is a threading bug");

        // ── deliberately outside it ──────────────────────────────────────
        // `sealed`/`movedSealed` below their totals is what §0.3 measured the
        // ratio *for*; the blocked/missing maps and `gappedBy` are
        // attributions of counts already in the set; `typeEvOnlyGap` and
        // `typeEvMasked` are strict subsets of `pairs − typeEv`, so counting
        // them would double-count — and `fullyInterpreted` is the
        // interpretation axis, not this one.
        for (what, mutate) in [
            ("sealed < proved", (|l: &mut Ledger| l.convs.sealed = 0) as fn(&mut Ledger)),
            ("movedSealed < moved", |l: &mut Ledger| l.convs.moved_sealed = 0),
            ("gappedBy", |l: &mut Ledger| {
                l.convs.gapped_by.insert("proj(And)".into(), 3);
            }),
            ("blocked", |l: &mut Ledger| {
                l.blocked.insert("strLit".into(), 3);
            }),
            ("missing", |l: &mut Ledger| {
                l.missing.insert("axiom(p)".into(), 3);
            }),
            ("by_cause", |l: &mut Ledger| {
                l.by_cause.insert("library-gap", 3);
            }),
            ("fullyInterpreted", |l: &mut Ledger| l.fully_interpreted = 0),
        ] {
            let mut l = clean.clone();
            mutate(&mut l);
            assert!(
                l.uncertified().is_clean(),
                "{what} must not make a run uncertified — it is nonzero on a legitimately \
                 clean run, or it double-counts something already in the set"
            );
        }
    }

    /// **A new [`Ledger`] field cannot join without being classified** — the
    /// guard is the exhaustive pattern below, which has no `..`, so adding a
    /// field to `Ledger` stops compiling here until someone says which side of
    /// [`Uncertified`] it falls on.
    ///
    /// The invariant in [`every_reason_lands_in_a_counter_in_the_set`] covers
    /// new *reasons*: a `Gap` variant, a new refusal site, a clause that starts
    /// declining — all of them arrive as an absent `Ev` and land in a counter
    /// already in the set. It does **not** cover a new *obligation*, because a
    /// new counter on `Ledger` is by definition something nothing yet routes
    /// through the existing ones. That is the case this exists for, and the
    /// audit at `03e7c42` is why it is worth having: it enumerated four
    /// load-bearing sites in `infer`/`whnf`/`def_eq` where a decision that
    /// changes what `⟦·⟧` *is* has no certificate behind it, none of which
    /// fires today, and counters for them are the next thing to arrive here.
    ///
    /// This is a *type*, not an assertion: it costs a build failure with a
    /// pointer to this comment, which is the cheapest possible way to force
    /// the question and the only one that cannot be forgotten.
    #[test]
    fn a_new_ledger_field_must_be_classified() {
        let Ledger {
            // ── in the set ───────────────────────────────────────────────
            pairs: _,
            const_ev_ok: _,
            type_ev_ok: _,
            unsealed: _,
            convs: crate::interp::ConvStats {
                gapped: _,
                // …and out of it: a certificate that carries hypotheses is
                // still a certificate.
                proved: _,
                sealed: _,
                moved: _,
                moved_sealed: _,
                // An attribution of `gapped`.
                gapped_by: _,
            },
            // ── the interpretation axis, which is not this one ───────────
            types_ok: _,
            values_ok: _,
            values_attempted: _,
            fully_interpreted: _,
            declarations: _,
            // ── attributions of counts already in the set ────────────────
            blocked: _,
            missing: _,
            by_cause: _,
            // ── strict subsets of `pairs − typeEv`; instruments, not debt ─
            type_ev_only_gap: _,
            type_ev_masked: _,
            // ── not debt either, and for a different reason: a lazy fill
            // produces the same interpretation the eager one would have. It
            // says *where* the store was filled, not whether it was — a
            // structural claim about `fill_declaration` covering the file,
            // pinned at zero in `mini/tests/tutorial.rs`.
            lazy_fills: _,
            // ── the *other* half of the certification axis ───────────────
            // Not in `Uncertified` and not outside the verdict either: a
            // recorded refusal is debt that opens no obligation, so it has a
            // set, a column and a share of exit 4 of its own. See
            // [`Untranslated`], whose own three counters are destructured
            // here for the same reason `convs` is.
            untranslated: Untranslated {
                declarations: _,
                constructors: _,
                eliminators: _,
                // An attribution of the three above.
                by_reason: _,
            },
            // ── `--block`'s own output; partial by design ────────────────
            first_blocker: _,
            // ── an instrument, and not on either axis ────────────────────
            // The frame-local `infer_type` memo's hit rate. It says how much
            // of the walk was re-derivation, not what was or was not proved,
            // so it is neither debt nor interpretation and has a row of its
            // own (`frame_row`) rather than a column in the verdict.
            frame_cache: _,
        } = Ledger::default();
    }

    /// **Every reason lands in a counter that is in the set**, so a `Gap`
    /// variant added later needs no entry in [`Uncertified`].
    ///
    /// This is the invariant that makes the set closed rather than a list to
    /// be maintained: the `waiting:` rows are an *attribution* of
    /// `pairs − constEv`, so their total is that number and cannot exceed it.
    /// A refusal site that produced a row without moving the counter would be
    /// debt the verdict cannot see, and this is where that shows up.
    ///
    /// Two unrelated gap kinds, on two declarations, so the sum is a sum and
    /// not a coincidence of one.
    #[test]
    fn every_reason_lands_in_a_counter_in_the_set() {
        let env = Environment::empty();
        let decls = vec![
            // `Gap::StrLit` — a clause with no construction behind it.
            Declaration::Axiom {
                name: Name::simple("uninterpretable"),
                lparams: vec![],
                ty: crate::expr::str_lit("s"),
            },
            // `Gap::Axiom` — a statement that interprets and an inhabitation
            // nothing here can produce. **An assumed inhabitant, not a sort.**
            // `axiom c : Sort n` owes only `⟦c⟧ ∈ Uₙ`, which is derivable —
            // mini declines the file rather than deriving it — so a
            // sort-valued axiom is an example of a *policy*, and this gap is
            // about what is underivable in principle.
            Declaration::Axiom {
                name: Name::simple("uninhabited"),
                lparams: vec![],
                ty: forall(sort(Level::zero()), sort(Level::zero())),
            },
            // And one that owes nothing, so the equality below is not `0 = 0`
            // nor `n = n` over a uniformly broken file.
            Declaration::Def {
                name: Name::simple("fine"),
                lparams: vec![],
                ty: sort(Level::zero().succ()),
                value: sort(Level::zero()),
                kind: DefKind::Def,
            },
        ];
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &decls, &Default::default(), &mut ip);
        let u = led.uncertified();
        assert_eq!(led.missing.len(), 2, "two distinct reasons: {:?}", led.missing);
        assert_eq!(u.const_typings, 2, "one pair discharges, two do not");
        assert_eq!(
            led.missing.values().sum::<usize>(),
            u.const_typings,
            "a `waiting:` row appeared that moves no counter in the set — the verdict cannot \
             see it, and `Uncertified` is no longer closed under new gap kinds: {:?}",
            led.missing
        );
    }

    /// **Every recorded refusal reaches the verdict**, one table at a time.
    ///
    /// The other half of the invariant in [`Untranslated`]'s header, and the
    /// half [`every_reason_lands_in_a_counter_in_the_set`] cannot cover: a
    /// `Gap` that never reaches a `(declaration, σ)` moves no counter there,
    /// however loudly it was recorded. `113_reduceCtorParamRefl` is the file
    /// that was reading `accept … constEv = pairs` and exit 0 with an
    /// inductive it had not translated.
    ///
    /// Populated on a real [`Interp`] rather than by building an
    /// `Untranslated` literal, because the failure mode being guarded is
    /// exactly a table [`Untranslated::of`] does not read: a literal would
    /// agree with itself. Each of the three, alone, must make the run unclean
    /// **and name itself**.
    #[test]
    fn a_recorded_refusal_reaches_the_verdict() {
        fn key(s: &str) -> (Name, Vec<u32>) { (Name::simple(s), vec![0u32]) }
        // Every table empty: clean, and silent.
        let ip = Interp::new();
        let none = Untranslated::of(&ip);
        assert!(none.is_clean(), "an untouched run owes nothing here: {none:?}");
        assert_eq!(none.column(), None, "a fully-translated run says nothing");

        for (what, fill, want) in [
            (
                "declaration",
                (|a: &mut crate::interp::IndApparatus| {
                    a.untranslated.insert(key("T"), Gap::StrLit);
                }) as fn(&mut crate::interp::IndApparatus),
                "untranslated: 1 declaration",
            ),
            ("constructor", |a| {
                a.ctor_untranslated.insert(key("T.mk"), Gap::StrLit);
            }, "untranslated: 1 constructor"),
            ("eliminator", |a| {
                a.rec_untranslated.insert(key("T.rec"), Gap::StrLit);
            }, "untranslated: 1 eliminator"),
        ] {
            let mut ip = Interp::new();
            fill(ip.ind_apparatus().expect("the apparatus builds"));
            let u = Untranslated::of(&ip);
            assert!(
                !u.is_clean(),
                "an untranslated {what} left the run clean — `Untranslated::of` does not read \
                 its table, so the verdict cannot see it: {u:?}"
            );
            assert_eq!(u.column().as_deref(), Some(want), "the column must name the {what}");
            assert_eq!(
                u.by_reason.get("strLit").copied(),
                Some(1),
                "the reason must be attributed under the ledger's own key: {u:?}"
            );
        }

        // ── deliberately outside `is_clean` ──────────────────────────────
        // `by_reason` is an attribution of the three counts, as `missing` is of
        // `const_typings`. A run whose reasons were somehow populated with all
        // three counts at zero has nothing to report, and treating the map as
        // debt would make `is_clean` depend on a map used only for display.
        let mut u = Untranslated::default();
        u.by_reason.insert("proj(And)".into(), 3);
        assert!(u.is_clean(), "an attribution is not debt: {u:?}");
        assert_eq!(u.column(), None, "and it must not put a column on a clean verdict");
    }

    /// The verdict line's fourth column: only the nonzero counters, named, and
    /// singular when there is one of them. `main.rs` prints this verbatim, and
    /// a reader who cannot tell a partially-certified run from a clean one is
    /// the whole defect this task is about.
    #[test]
    fn the_uncertified_column_names_what_is_owed() {
        let u = Uncertified { const_typings: 2, type_typings: 1, conversions: 0, unsealed: 3 };
        assert_eq!(
            u.column().as_deref(),
            Some("uncertified: 2 const typings, 1 type typing, 3 sealing refusals")
        );
        assert_eq!(
            Uncertified { conversions: 12, ..Default::default() }.column().as_deref(),
            Some("uncertified: 12 conversions")
        );
        // The wire format again: the column sits in a tab-separated row, and a
        // tab in it would make the verdict line parse as five columns. See
        // [`a_reason_key_is_wire_safe`], which exists for the same reason.
        assert!(!u.column().unwrap().contains('\t'));
    }

    /// A file mini can interpret **completely**: two definitions over sorts
    /// and arrows only. Every pair must interpret, and the blocked map must be
    /// empty — a ledger that reported "all fine" on an empty run would prove
    /// nothing, so the counts are checked too.
    ///
    /// **`A` is a definition, and it was an `axiom` until the sort-valued
    /// axiom's typing was withdrawn.** `def id : A → A` takes `kernel.rs`'s
    /// `l2 = 0` clause at the `Π`, and that clause requires the codomain's own
    /// `⟦A⟧ ∈ U₀` to be *in hand* — an `axiom A : Prop` has none, because mini
    /// declines any export that declares an axiom of its own rather than
    /// deriving one. So the fixture as written described a file mini refuses
    /// to look at; `A := ∀ p : Prop, p` is a proposition mini can interpret,
    /// and the property under test — a whole file with nothing outstanding —
    /// is the one it was always about.
    #[test]
    fn an_inductive_free_file_interprets_completely() {
        let mut env = Environment::empty();
        let prop = sort(Level::zero());
        let a = Name::simple("A");
        let a_def = Declaration::Def {
            name: a,
            lparams: vec![],
            ty: prop,
            // `∀ p : Prop, p` — a closed proposition, no axiom needed.
            value: forall(prop, crate::expr::bvar(0)),
            kind: DefKind::Def,
        };
        crate::kernel::add(&mut env, &a_def).unwrap();
        let id_ty = forall(konst(a, Vec::new().into()), konst(a, Vec::new().into()));
        let id = Declaration::Def {
            name: Name::simple("id"),
            lparams: vec![],
            ty: id_ty,
            value: crate::expr::lam(konst(a, Vec::new().into()), crate::expr::bvar(0)),
            kind: DefKind::Def,
        };
        crate::kernel::add(&mut env, &id).unwrap();

        let decls = vec![a_def, id];
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &decls, &Default::default(), &mut ip);
        assert_eq!(led.pairs, 2);
        assert_eq!(led.types_ok, 2, "both types must interpret");
        assert_eq!(led.values_ok, 2);
        assert_eq!(led.values_attempted, 2);
        assert!(led.blocked.is_empty(), "unexpected gaps: {:?}", led.blocked);
        assert_eq!(led.fully_interpreted, 2);
    }

    /// A clause mini cannot interpret blocks, and the ledger says **which**
    /// one rather than only that something did. The reason comes from the
    /// `Typing`'s own `ev`, so attribution cannot drift from the gap.
    ///
    /// **The uninterpretable stand-in is a string literal, and it used to be a
    /// nat literal.** `Expr::NatLit` was the convenient "clause mini has no
    /// interpretation for" fixture in three tests here; it now interprets —
    /// `⟦natLit n⟧ = ⟦Nat.succ^n Nat.zero⟧`, through the ordinary inductive
    /// route — so all three had stopped exercising what they are about and
    /// said so by failing. `Expr::StrLit` is the replacement and is a *better*
    /// one for the purpose: `Gap::StrLit` is a clause with no construction
    /// behind it at all, where the nat literal's absence was always one
    /// clause away.
    ///
    /// The general lesson, and it is why this is written here rather than in a
    /// commit: **a fixture chosen for being unsupported has a shelf life**, and
    /// the only thing that keeps it honest is that it fails loudly when the
    /// support arrives. These three did.
    #[test]
    fn an_uninterpretable_clause_is_attributed_by_name() {
        let env = Environment::empty();
        let d = Declaration::Axiom {
            name: Name::simple("p"),
            lparams: vec![],
            ty: crate::expr::str_lit("s"),
        };
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &[d], &Default::default(), &mut ip);
        assert_eq!(led.types_ok, 0);
        assert_eq!(led.blocked.get("strLit"), Some(&1), "got {:?}", led.blocked);
    }

    /// **An axiom whose type did not interpret is blamed on the type, not on
    /// being an axiom.**
    ///
    /// §0.4 at the one place that used to violate it. `Gap::Axiom` fired
    /// unconditionally on an axiom, ahead of the `ty_blocked` check, so
    /// "we assumed something" was reported where "we could not interpret the
    /// statement" was true — and `123_quotSoundType` filed the *same*
    /// obligation on two axes because of it, once as `Quot.sound` and once as
    /// the definition `quotSoundType` whose value is that very constant.
    ///
    /// Both directions are pinned, because a fix that simply stopped emitting
    /// `Gap::Axiom` would pass a one-sided test while losing the category.
    #[test]
    fn an_axioms_typing_is_blamed_on_its_type_when_its_type_did_not_interpret() {
        let env = Environment::empty();
        let blocked = Declaration::Axiom {
            name: Name::simple("blocked"),
            lparams: vec![],
            ty: crate::expr::str_lit("s"),
        };
        // `Prop → Prop`, not `Prop`: a **sort-valued** axiom's `⟦c⟧ ∈ Uₙ` is
        // derivable and mini declines the file instead, so it is an example of
        // a policy rather than of an outstanding inhabitation. This one is an
        // assumed *inhabitant*, which is underivable in principle.
        let plain = Declaration::Axiom {
            name: Name::simple("plain"),
            lparams: vec![],
            ty: forall(sort(Level::zero()), sort(Level::zero())),
        };

        let mut ip = Interp::new();
        let led = Ledger::run(&env, &[blocked, plain], &Default::default(), &mut ip);
        assert_eq!(led.pairs, 2);
        assert_eq!(
            led.missing.get("strLit"),
            Some(&1),
            "an axiom with an uninterpretable type is blocked on the type: {:?}",
            led.missing
        );
        assert_eq!(
            led.missing.get("axiom(plain)"),
            Some(&1),
            "an axiom whose type *did* interpret still owes its inhabitation: {:?}",
            led.missing
        );
        // And the axis: what is left of `Gap::Axiom` is Lean's own three, each
        // validated by the model, so it is a construction rather than a
        // postulate. `Cause::Assumption` has no occupant and is gone.
        assert_eq!(led.by_cause.get("interpretation-scope"), Some(&1));
        assert_eq!(led.by_cause.get("library-gap"), Some(&1));
        assert!(!led.by_cause.contains_key("model-assumption"));
    }

    /// `Eq` and `add_quot`'s four, which is everything the `Quot.lift` ι redex
    /// below needs in an environment. Nothing else is declared: every other
    /// name in that declaration is a **λ binder**, and that is not incidental —
    /// a binder's interpretation is its scope's own assumption, so the redex
    /// reaches the ι site with `cur_tm` in hand, where the same shape written
    /// over axioms would gap on `Gap::Axiom` two steps earlier and never get
    /// there.
    fn quot_env() -> Environment {
        let (e, refl) = (Name::simple("Eq"), Name::str(&Name::simple("Eq"), "refl"));
        let u = Level::param(Name::simple("u"));
        let us: std::rc::Rc<[Level]> = vec![u].into();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e,
                lparams: vec![Name::simple("u")],
                num_params: 2,
                // `Eq : ∀ (α : Sort u) (a : α), α → Prop`
                ty: forall(sort(u), forall(bvar(0), forall(bvar(1), sort(Level::zero())))),
                // `Eq.refl : ∀ (α : Sort u) (a : α), Eq α a a`
                ctors: vec![(
                    refl,
                    forall(
                        sort(u),
                        forall(bvar(0), app(app(app(konst(e, us), bvar(1)), bvar(0)), bvar(0))),
                    ),
                )],
            },
        )
        .expect("Eq is accepted");
        crate::kernel::add_quot(&mut env).expect("Quot is accepted");
        env
    }

    /// **A `Quot.lift` ι that declined reports *what* `quot_iota` refused, not
    /// `iota(Quot.lift)`** — §0.4 at the four `.ok()`s that used to feed one
    /// `Gap::Iota` mint.
    ///
    /// The declaration is `vendor/arena-tests/good/undecidability/`
    /// `alg-conv-trans-quot-right`'s `right`, transcribed: `rfl` at a
    /// `Quot.lift.{0,1}` redex over `Quot.mk.{0}`, whose type forces the ι
    /// conversion. `u = 0` is `crate::quot`'s identity clause rather than
    /// `quot_iota`'s, so `quot_iota::fire` declines with a named step — and the
    /// arm above it threw that away and minted `Gap::Iota` regardless, so the
    /// published ι census measured the arm's own label instead of the route's.
    /// Measured on that file before and after: `waiting:iota(Quot.lift)=1`
    /// became `waiting:recursor(Quot.lift: quotient iota: the redex's arity or
    /// its levels disagree)=1`.
    ///
    /// **The totals do not move and that is the point.** Both labels are
    /// `Cause::Threading` and both sink the same one const typing, so no
    /// counter can tell them apart; what was wrong was the attribution, and
    /// only the key can see it. Hence the second assertion, which is the one a
    /// regression would trip.
    #[test]
    fn a_declined_quotient_iota_reports_the_step_that_refused_it() {
        let env = quot_env();
        let one: std::rc::Rc<[Level]> = vec![Level::zero().succ()].into();
        let zero_one: std::rc::Rc<[Level]> = vec![Level::zero(), Level::zero().succ()].into();
        let zero: std::rc::Rc<[Level]> = vec![Level::zero()].into();
        let eq = |b: E, x: E, y: E| app(app(app(konst(Name::simple("Eq"), one.clone()), b), x), y);
        // `Quot.lift.{0,1} α r β f h (Quot.mk.{0} α r a)`, under the six
        // binders: `a=#0 h=#1 f=#2 β=#3 r=#4 α=#5`.
        let redex = || {
            let mk = app(
                app(app(konst(Name::str(&Name::simple("Quot"), "mk"), zero.clone()), bvar(5)), bvar(4)),
                bvar(0),
            );
            let lift = konst(Name::str(&Name::simple("Quot"), "lift"), zero_one.clone());
            app(
                app(app(app(app(app(lift, bvar(5)), bvar(4)), bvar(3)), bvar(2)), bvar(1)),
                mk,
            )
        };
        // `h : ∀ (a b : α), r a b → Eq.{1} β (f a) (f b)`, under four binders.
        let h_ty = forall(
            bvar(3),
            forall(
                bvar(4),
                forall(
                    app(app(bvar(4), bvar(1)), bvar(0)),
                    eq(bvar(4), app(bvar(3), bvar(2)), app(bvar(3), bvar(1))),
                ),
            ),
        );
        let telescope = |cod: E| {
            forall(
                sort(Level::zero()),
                forall(
                    forall(bvar(0), forall(bvar(1), sort(Level::zero()))),
                    forall(
                        sort(Level::zero().succ()),
                        forall(forall(bvar(2), bvar(1)), forall(h_ty, forall(bvar(4), cod))),
                    ),
                ),
            )
        };
        let lams = |body: E| {
            lam(
                sort(Level::zero()),
                lam(
                    forall(bvar(0), forall(bvar(1), sort(Level::zero()))),
                    lam(
                        sort(Level::zero().succ()),
                        lam(forall(bvar(2), bvar(1)), lam(h_ty, lam(bvar(4), body))),
                    ),
                ),
            )
        };
        let d = Declaration::Def {
            name: Name::simple("right"),
            lparams: vec![],
            ty: telescope(eq(bvar(3), redex(), app(bvar(2), bvar(0)))),
            value: lams(app(
                app(konst(Name::str(&Name::simple("Eq"), "refl"), one), bvar(3)),
                redex(),
            )),
            kind: DefKind::Def,
        };

        let mut ip = Interp::new();
        let led = Ledger::run(&env, &[d], &Default::default(), &mut ip);
        assert_eq!(led.pairs, 1);
        assert_eq!(led.uncertified().const_typings, 1, "the ι is owed: {:?}", led.missing);
        assert_eq!(
            led.missing.get(
                "recursor(Quot.lift: quotient iota: the redex's arity or its levels disagree)"
            ),
            Some(&1),
            "the route's own reason must be what is published: {:?}",
            led.missing
        );
        assert!(
            !led.missing.contains_key("iota(Quot.lift)"),
            "the arm's own label may not stand in for the route's: {:?}",
            led.missing
        );
    }

    /// **Armed, the run stops — and stops at the *first* pair that owes
    /// something.**
    ///
    /// Three declarations, so the stop is a position and not an accident: the
    /// first discharges, the second and third do not. Unarmed the ledger
    /// counts both absences and reaches the end; armed it reports the second
    /// and never attempts the third. The same `Gap` names it either way, which
    /// is the property that lets a blocker and a `waiting:` row be
    /// cross-read.
    #[test]
    fn armed_the_run_stops_at_the_first_pair_it_cannot_discharge() {
        let env = Environment::empty();
        let nat = || crate::expr::str_lit("s");
        let decls = vec![
            Declaration::Def {
                name: Name::simple("fine"),
                lparams: vec![],
                ty: sort(Level::zero().succ()),
                value: sort(Level::zero()),
                kind: DefKind::Def,
            },
            Declaration::Axiom { name: Name::simple("second"), lparams: vec![], ty: nat() },
            Declaration::Axiom { name: Name::simple("third"), lparams: vec![], ty: nat() },
        ];

        let mut ip = Interp::new();
        let led = Ledger::run(&env, &decls, &Default::default(), &mut ip);
        assert_eq!(led.pairs, 3, "unarmed, every pair is attempted");
        assert_eq!(led.blocked.get("strLit"), Some(&2), "got {:?}", led.blocked);
        assert_eq!(led.const_ev_ok, 1, "the first declaration's typing must derive");
        assert!(led.first_blocker.is_none(), "unarmed, nothing blocks");

        crate::blocker::arm(true);
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &decls, &Default::default(), &mut ip);
        crate::blocker::arm(false);
        assert_eq!(led.pairs, 2, "the third pair must never be attempted");
        assert_eq!(led.const_ev_ok, 1, "the first pair is still discharged");
        let b = led.first_blocker.expect("armed, the second pair must block");
        assert_eq!(b.decl, "second");
        assert_eq!(b.key, "strLit", "the blocker uses the ledger's own vocabulary");
        assert_eq!(b.obligation, crate::blocker::Obligation::TypeInterp);
        assert_eq!(b.cause, Some(crate::ev::Cause::Scope));
        assert!(b.report.contains("⟦ty[σ]⟧"), "the report says what was wanted:\n{}", b.report);
    }
}
