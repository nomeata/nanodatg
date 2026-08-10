//! The shared cross-engine constant store (ENV-UNIFY.md §3.4 items 3, 5, 6 —
//! tracks B3/B4): one table of `⟦c.{σ}⟧` carriers and their certificates,
//! written and read by both engines over one [`crate::tg::EnvCore`].
//!
//! # Interface
//!
//! ```text
//! ConstKey = (NameKey, Vec<LevelKey>)      the one joint key (B3)
//! store.publish(&key, sp, eng, term, typing, defeq)
//! store.get(&key, sp, reader)              -> Vec<ConstEntry>
//! store.note_adopted / note_declined       the crossing ledger
//! store.report()                           -> String, for measurements
//! ```
//!
//! # The key, defined once
//!
//! * `NameKey` is the export file's own index for the name
//!   ([`crate::instantiations::name_key`]) — the only per-run-stable identity
//!   either engine has. A name interned in a per-declaration arena has none,
//!   and such constants simply never cross.
//! * [`LevelKey::Ground`] is a universe level that evaluates to a numeral
//!   under the instantiation — `mini` runs at ground levels only, and the
//!   checker's σ pre-pass makes ground the common case, so this is the arm on
//!   which the two engines' keys are *equal values*. [`LevelKey::Sym`] keeps
//!   the checker's historical spelling (the interpreted level term) for the
//!   levels that are not ground — the eliminator universe while an inductive
//!   block is checked, above all — which by construction only the checker
//!   produces, so nothing is lost and nothing collides.
//!
//! # Adopt-and-check, and what the store itself guarantees
//!
//! Nothing read from here is trusted. The store enforces exactly two facts,
//! both checked at `publish` so that no reader has to hope for them:
//!
//! * **Entry coherence** — every certificate in an entry is *about the
//!   entry's own carrier*: a typing's subject and a defining equation's
//!   left-hand side must be the entry's `term`, or the slot is refused and
//!   counted. A reader that adopts `entry.term` therefore knows the attached
//!   theorems speak of that term and not of something the writer mislabelled.
//! * **Spelling** — each entry records the constant's name as the writer
//!   spells it, and both `publish` and `get` refuse (and count) a caller
//!   whose spelling disagrees. The `NameKey` half of the key is an arena
//!   index. On a **routed** run the two engines read one `ExportFile` — the
//!   one `mini`'s load installed (`mini::arena::installed_export_file`), so
//!   the index is one identity and this guard is a tripwire against a second
//!   parse creeping back in. The *sequential* seam tests
//!   (`mini/tests/envshare_tg.rs`) still parse twice, and there the guard
//!   carries its original weight: two deterministic parses agreeing is an
//!   assumption, and the spelling check turns it into a measured refusal
//!   (`alias`) instead of a silent mislabelling.
//!
//! Everything *semantic* — "is this defining equation about the body **I**
//! just interpreted", "is this typing literally the membership **I** am
//! claiming" — stays with the reader, at the same single-exit guards the
//! checker's per-thread stores already use. A statement mismatch there is a
//! counted decline, never an adopted theorem.
//!
//! # One carrier per key is a goal the store measures, not a fiction it asserts
//!
//! The identity doctrine (`mini/src/interp.rs`, `IndApparatus::decls`) wants
//! one carrier per key per composition domain. Until B5 aligns the two
//! dispatches' skeleton normal forms, the engines can genuinely interpret one
//! constant to two different terms; pretending otherwise by keeping only the
//! first writer's carrier would silently strip the second engine of its own
//! per-thread sharing (measured at about a thousand re-mints per constant on
//! `init-prelude` when the checker lost exactly that store). So: **at most
//! one entry per key per engine; entries merge the moment their carriers are
//! equal terms; keys where the two engines' carriers differ are counted**
//! (`divergent`) — that count is the B5 work list, and `converged` plus the
//! adoption ledger are the crossing measurement B4 exists to produce.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use kernel::Term;

use crate::sealed::Sealed;

/// The export file's per-run-stable index for a name — see
/// [`crate::instantiations::NameKey`].
pub type NameKey = u32;

/// One universe level as it appears in a joint constant key.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum LevelKey {
    /// The level evaluates to this numeral under the instantiation. The arm
    /// both engines produce, and so the arm on which their keys agree.
    Ground(u32),
    /// Not ground; the checker's interpreted level term. `mini` never
    /// produces this arm (its zone-B walk is ground-only by construction).
    Sym(Term),
}

/// **The one joint key** (ENV-UNIFY.md §3.4 item 3): a constant at one
/// instantiation, as both engines name it.
pub type ConstKey = (NameKey, Vec<LevelKey>);

/// Which engine wrote a carrier or a certificate. A label for the crossing
/// ledger — never a licence: readers guard statements, not provenance.
///
/// # Why a `by` is stored at all
///
/// The question was asked directly — *"why do you even store a `by` in the
/// environment? once both engines mint the same terms, a certificate is a
/// certificate"* — and the first half is right: **nothing decides whether to
/// believe a theorem by looking here.** Every consumer matches the
/// statement. So the tag is only worth its place if some reader needs to
/// know *who wrote it* for a reason that is not belief.
///
/// One does, and it is the only one left. `CrossStats::adopted`,
/// `declined`, `converged` and `divergent` are each *defined* as "the other
/// engine wrote it": a certificate that crossed, a crossing that gapped, two
/// engines that agreed on a carrier, two that did not. There is no way to
/// state any of those without a writer, and they are the measurement the
/// whole two-engine merge is steered by. That is the answer: the tag is the
/// **ledger's**, and the environment is where the ledger keeps it because the
/// entry is what the ledger is about.
///
/// The census behind that, each entry mutated and its green column measured
/// over the 91 tutorial exports:
///
/// | reader | reads | class | mutation |
/// |--------|-------|-------|----------|
/// | [`ConstStore::publish`] — `converged`, `divergent`, [`ConstStore::census`] | `carrier_by` | ledger | — |
/// | [`ConstStore::publish`] — one carrier per engine, first wins | `carrier_by` | **decision** | red: `one_carrier_per_engine_divergence_and_convergence_counted` |
/// | `tg::const_abbrev`, `tg::has_type_const`, `tg::ty_const` — `note_adopted`/`note_declined` | `typing.1`, `defeq.1` | ledger | — |
/// | `mini::kernel::adopt_shared` — `note_adopted` | `typing.1` | ledger | — |
/// | `tg::ty_const` — which of two typings to try | `typing.1` | **decision** | **removed** |
/// | `mini::kernel::adopt_shared` — adopt only a *foreign* typing | `typing.1` | **decision** | no test red, no number moves |
///
/// **One decision was removed.** `ty_const` picked between two stored
/// typings by writer (own slot first). Dropping that preference outright
/// moves the corpus report — `checkerSlots` 71 → 60,
/// `declinedByCheckerTyping` 481 → 503 — so it was load-bearing, and *no
/// test caught it*. Replacing it with the rule the header already claimed —
/// pick the slot whose conclusion is the statement wanted, whoever wrote it
/// — reproduces the baseline to the field. Statement first, provenance
/// never, and now that is true of every decision in `tg.rs`.
///
/// **One decision stays, and it is worth naming.**
/// `mini::kernel::adopt_shared` adopts only a typing this engine did *not*
/// write. Engine-blind, the corpus report is unchanged to the field, because
/// `adopt_shared` runs only where mini's own table has no entry and the store
/// therefore holds no mini entry either — the filter never fires. It stays
/// because if that invariant ever breaks, an engine-blind read would adopt
/// its own certificate back and `note_adopted` would count a self-read as a
/// crossing: the filter guards the *measurement*, not the belief, which is
/// the same reason the tag exists at all.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Engine {
    Mini,
    Checker,
}

/// Which certificate slot of an entry a crossing event is about.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Slot {
    Typing,
    Defeq,
}

/// What the store holds for one `(key, carrier)`: the carrier term and the
/// certificates that are **about it** (enforced at [`ConstStore::publish`]).
#[derive(Clone, Debug)]
pub struct ConstEntry {
    /// The constant's name as the writer spells it — the alias guard.
    pub spelling: Rc<str>,
    /// `⟦c.{σ}⟧`, this writer's carrier.
    pub term: Term,
    /// Who minted the carrier. Read by [`ConstStore::publish`]'s
    /// one-carrier-per-engine rule and by the `converged`/`divergent`
    /// counters; see [`Engine`] for why a writer is stored at all.
    pub carrier_by: Engine,
    /// `⊢ term ∈ ⟦ty[σ]⟧`, and who derived it. **The writer is the ledger's,
    /// not a licence** — no consumer decides whether to believe this theorem
    /// by reading it, and since the `ty_const` slot pick became
    /// statement-first, no consumer decides anything by reading it. See
    /// [`Engine`].
    pub typing: Option<(Sealed, Engine)>,
    /// `⊢ term = ⟦val[σ]⟧` — the defining equation — and who derived it. Same
    /// rule as [`ConstEntry::typing`].
    pub defeq: Option<(Sealed, Engine)>,
}

/// The crossing ledger. Key-level sets rather than event counters, so a read
/// that re-adopts the same entry every declaration counts once.
#[derive(Default, Debug)]
pub struct CrossStats {
    /// `(key, slot, reader)` where the reader's statement guard **passed** on
    /// a slot the other engine wrote — a certificate that crossed.
    pub adopted: HashSet<(ConstKey, Slot, Engine)>,
    /// `(key, slot, reader)` where a cross-written slot existed but the
    /// reader's guard refused it — a crossing that still gaps (B5's residue).
    pub declined: HashSet<(ConstKey, Slot, Engine)>,
    /// Keys where the two engines hold **different carriers** — the forbidden
    /// two-carriers state, counted instead of hidden.
    pub divergent: HashSet<ConstKey>,
    /// Keys where a publish merged one engine's certificate onto the *other*
    /// engine's carrier — the carriers are one term there.
    pub converged: HashSet<ConstKey>,
    /// Spelling disagreements at `publish` or `get` — a `NameKey` that means
    /// different names to the two sides. Must stay 0 while both engines parse
    /// the same export; nonzero is an arena-drift alarm, and the access is
    /// refused.
    pub alias: u64,
    /// Slots refused at `publish` because their statement was not about the
    /// entry's own term. A writer bug surfaced at the funnel, not a reader
    /// hazard.
    pub incoherent: u64,
}

/// The store: one table over the joint key, hanging off the shared
/// [`crate::tg::EnvCore`] so both engines reach the same cell.
#[derive(Default)]
pub struct ConstStore {
    entries: HashMap<ConstKey, Vec<ConstEntry>>,
    pub stats: CrossStats,
}

impl ConstStore {
    /// Offer `(term, typing?, defeq?)` for `key` as `eng`'s interpretation.
    ///
    /// Rules, in order — each refusal counted, none silent:
    /// * a spelling that disagrees with the key's existing entries is an
    ///   `alias`: refused outright;
    /// * a certificate not about `term` is `incoherent`: that slot is dropped;
    /// * if an entry with **the same carrier term** exists, slots merge into
    ///   it (first certificate per slot wins), and a cross-engine merge marks
    ///   the key `converged`;
    /// * else, one entry per engine: `eng`'s first carrier for the key wins
    ///   (the historical `or_insert`), later different carriers from the same
    ///   engine are dropped — the caller has already counted its own drift;
    /// * a key now holding two engines' distinct carriers is `divergent`.
    pub fn publish(
        &mut self,
        key: &ConstKey,
        spelling: &str,
        eng: Engine,
        term: Term,
        typing: Option<Sealed>,
        defeq: Option<Sealed>,
    ) {
        let list = self.entries.entry(key.clone()).or_default();
        if list.iter().any(|e| &*e.spelling != spelling) {
            self.stats.alias += 1;
            return
        }
        // Coherence: a certificate must be about the carrier it rides with.
        let typing = typing.filter(|s| {
            let ok = s.concl().as_mem().is_some_and(|(subj, _)| subj == term);
            if !ok {
                self.stats.incoherent += 1;
            }
            ok
        });
        let defeq = defeq.filter(|s| {
            let ok = s.concl().as_eq().is_some_and(|(lhs, _)| lhs == term);
            if !ok {
                self.stats.incoherent += 1;
            }
            ok
        });
        if let Some(e) = list.iter_mut().find(|e| e.term == term) {
            if e.carrier_by != eng {
                self.stats.converged.insert(key.clone());
            }
            if e.typing.is_none() {
                e.typing = typing.map(|s| (s, eng));
            }
            if e.defeq.is_none() {
                e.defeq = defeq.map(|s| (s, eng));
            }
            return
        }
        if list.iter().any(|e| e.carrier_by == eng) {
            // This engine already named a carrier for the key; the first one
            // stands (`or_insert`), exactly as the per-thread stores always
            // behaved. The caller counts its own drift.
            return
        }
        list.push(ConstEntry {
            spelling: Rc::from(spelling),
            term,
            carrier_by: eng,
            typing: typing.map(|s| (s, eng)),
            defeq: defeq.map(|s| (s, eng)),
        });
        if list.iter().any(|e| e.carrier_by != list[0].carrier_by) {
            self.stats.divergent.insert(key.clone());
        }
    }

    /// Every entry under `key` whose spelling agrees with the reader's —
    /// disagreement is counted (`alias`) and the entry withheld. Clones: the
    /// caller guards statements against its own objects at its leisure,
    /// without holding the store's cell open.
    ///
    /// **It does not take the reader's engine, and that is the answer to
    /// "why is a `by` stored at all?" in miniature.** It used to, as
    /// `_reader: Engine` — a parameter every caller passed and this function
    /// ignored — which made the store look provenance-aware on the read path
    /// when nothing on that path has ever consulted a writer. A read is
    /// decided by spelling and, at the caller, by statement. See the type
    /// header for where the writer *is* read.
    pub fn get(&mut self, key: &ConstKey, spelling: &str) -> Vec<ConstEntry> {
        let Some(list) = self.entries.get(key) else { return Vec::new() };
        let (hit, miss): (Vec<_>, Vec<_>) =
            list.iter().partition(|e| &*e.spelling == spelling);
        self.stats.alias += miss.len() as u64;
        hit.into_iter().cloned().collect()
    }

    /// The reader's statement guard passed on a slot the other engine wrote.
    pub fn note_adopted(&mut self, key: &ConstKey, slot: Slot, reader: Engine) {
        self.stats.adopted.insert((key.clone(), slot, reader));
    }

    /// A cross-written slot existed but the reader's guard refused it.
    pub fn note_declined(&mut self, key: &ConstKey, slot: Slot, reader: Engine) {
        self.stats.declined.insert((key.clone(), slot, reader));
    }

    /// Entries and certificate slots per writer: `(mini entries, checker
    /// entries, mini-written slots, checker-written slots)`.
    pub fn census(&self) -> (usize, usize, usize, usize) {
        let (mut em, mut ec, mut sm, mut sc) = (0, 0, 0, 0);
        for list in self.entries.values() {
            for e in list {
                match e.carrier_by {
                    Engine::Mini => em += 1,
                    Engine::Checker => ec += 1,
                }
                for eng in
                    e.typing.iter().map(|(_, g)| *g).chain(e.defeq.iter().map(|(_, g)| *g))
                {
                    match eng {
                        Engine::Mini => sm += 1,
                        Engine::Checker => sc += 1,
                    }
                }
            }
        }
        (em, ec, sm, sc)
    }

    /// The crossing measurement, one line per row, `k=v` tab-separated like
    /// the ledger's `convs` row so the same scrapers can read it.
    pub fn report(&self) -> String {
        let (em, ec, sm, sc) = self.census();
        let count = |r: Engine, s: Slot, set: &HashSet<(ConstKey, Slot, Engine)>| {
            set.iter().filter(|(_, sl, rd)| *sl == s && *rd == r).count()
        };
        format!(
            "cross\tminiEntries={em}\tcheckerEntries={ec}\tminiSlots={sm}\tcheckerSlots={sc}\t\
             adoptedByCheckerTyping={}\tadoptedByCheckerDefeq={}\tadoptedByMiniTyping={}\t\
             adoptedByMiniDefeq={}\tdeclinedByCheckerTyping={}\tdeclinedByCheckerDefeq={}\t\
             declinedByMiniTyping={}\tdeclinedByMiniDefeq={}\tconverged={}\tdivergent={}\t\
             alias={}\tincoherent={}",
            count(Engine::Checker, Slot::Typing, &self.stats.adopted),
            count(Engine::Checker, Slot::Defeq, &self.stats.adopted),
            count(Engine::Mini, Slot::Typing, &self.stats.adopted),
            count(Engine::Mini, Slot::Defeq, &self.stats.adopted),
            count(Engine::Checker, Slot::Typing, &self.stats.declined),
            count(Engine::Checker, Slot::Defeq, &self.stats.declined),
            count(Engine::Mini, Slot::Typing, &self.stats.declined),
            count(Engine::Mini, Slot::Defeq, &self.stats.declined),
            self.stats.converged.len(),
            self.stats.divergent.len(),
            self.stats.alias,
            self.stats.incoherent,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::{Env, Term, Thm};

    fn t(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// A real hypothesis-free theorem whose conclusion is `a = a` — the
    /// cheapest coherent "defining equation" for carrier `a`.
    fn refl(a: &Term) -> Sealed {
        Sealed::new(Thm::eq_refl(a.clone())).expect("eq_refl is hypothesis-free")
    }

    fn key(n: u32) -> ConstKey { (n, vec![LevelKey::Ground(0)]) }

    #[test]
    fn coherence_is_enforced_at_publish() {
        let mut env = Env::new();
        let (a, b) = (t(&mut env), t(&mut env));
        let mut st = ConstStore::default();
        // A defeq about `b` offered on `a`'s entry: the slot is dropped and
        // counted; the carrier itself still lands.
        st.publish(&key(1), "c", Engine::Mini, a.clone(), None, Some(refl(&b)));
        assert_eq!(st.stats.incoherent, 1, "an incoherent slot must be counted");
        let got = st.get(&key(1), "c");
        assert_eq!(got.len(), 1);
        assert!(got[0].defeq.is_none(), "an incoherent certificate must not be stored");
        // The coherent one lands.
        st.publish(&key(1), "c", Engine::Mini, a.clone(), None, Some(refl(&a)));
        let got = st.get(&key(1), "c");
        assert!(got[0].defeq.is_some(), "a coherent certificate must merge into the entry");
    }

    #[test]
    fn spelling_disagreement_is_refused_both_ways() {
        let mut env = Env::new();
        let (a, b) = (t(&mut env), t(&mut env));
        let mut st = ConstStore::default();
        st.publish(&key(2), "List.cons", Engine::Mini, a, None, None);
        // Same raw key, different name: the write is refused…
        st.publish(&key(2), "Zzz", Engine::Checker, b, None, None);
        assert_eq!(st.stats.alias, 1, "an aliased publish must be counted");
        assert_eq!(st.get(&key(2), "List.cons").len(), 1);
        // …and so is the read.
        assert!(st.get(&key(2), "Zzz").is_empty());
        assert_eq!(st.stats.alias, 2, "an aliased read must be counted");
    }

    /// Three carriers, not two (the two-atoms rule): mini's first, mini's
    /// second (dropped — first per engine wins), the checker's (kept beside,
    /// key counted divergent). Then the checker republishing *mini's* term
    /// merges instead of stacking, and the key counts converged.
    #[test]
    fn one_carrier_per_engine_divergence_and_convergence_counted() {
        let mut env = Env::new();
        let (a, b, c) = (t(&mut env), t(&mut env), t(&mut env));
        let mut st = ConstStore::default();
        st.publish(&key(3), "c", Engine::Mini, a.clone(), None, None);
        st.publish(&key(3), "c", Engine::Mini, b.clone(), None, Some(refl(&b)));
        let got = st.get(&key(3), "c");
        assert_eq!(got.len(), 1, "an engine's second carrier for one key must be dropped");
        assert_eq!(got[0].term, a, "…and the first must stand");
        st.publish(&key(3), "c", Engine::Checker, c.clone(), None, None);
        assert_eq!(st.get(&key(3), "c").len(), 2);
        assert!(st.stats.divergent.contains(&key(3)), "two carriers must be counted divergent");
        // The checker meets mini's carrier: same term ⇒ merge, not a third row.
        st.publish(&key(3), "c", Engine::Checker, a.clone(), None, Some(refl(&a)));
        let got = st.get(&key(3), "c");
        assert_eq!(got.len(), 2, "a same-term publish must merge, never stack");
        assert!(st.stats.converged.contains(&key(3)), "a cross-engine merge is convergence");
        let m = got.iter().find(|e| e.term == a).expect("mini's entry");
        assert_eq!(m.carrier_by, Engine::Mini, "the carrier's minting engine is remembered");
        assert!(
            matches!(m.defeq, Some((_, Engine::Checker))),
            "the merged slot remembers who derived it"
        );
    }

    /// A typing slot must be a *membership about the carrier*. The genuine
    /// membership comes from the prelude (`⊢ U₀ ∈ U₁`): offered on the wrong
    /// carrier it is dropped and counted, on `U₀` itself it lands.
    #[test]
    fn a_typing_slot_must_be_a_membership_about_the_carrier() {
        let mut env = Env::new();
        let a = t(&mut env);
        let pre = derived::prelude::prelude();
        let u0_in_u1 =
            Sealed::new(pre.u0_in_u1.clone()).expect("the prelude theorem is hypothesis-free");
        let mut st = ConstStore::default();
        // A reflexivity theorem offered as a typing: not a membership at all.
        st.publish(&key(4), "c", Engine::Checker, a.clone(), Some(refl(&a)), None);
        assert_eq!(st.stats.incoherent, 1);
        assert!(st.get(&key(4), "c")[0].typing.is_none());
        // A real membership about a *different* subject: still refused.
        st.publish(&key(4), "c", Engine::Checker, a.clone(), Some(u0_in_u1.clone()), None);
        assert_eq!(st.stats.incoherent, 2);
        // About its own subject: lands.
        st.publish(&key(5), "d", Engine::Checker, pre.u0(), Some(u0_in_u1), None);
        assert!(st.get(&key(5), "d")[0].typing.is_some());
    }

    #[test]
    fn the_ledger_deduplicates_by_key() {
        let mut st = ConstStore::default();
        st.note_adopted(&key(5), Slot::Typing, Engine::Checker);
        st.note_adopted(&key(5), Slot::Typing, Engine::Checker);
        st.note_declined(&key(5), Slot::Defeq, Engine::Mini);
        assert_eq!(st.stats.adopted.len(), 1, "re-adoption of one key counts once");
        assert!(st.report().contains("adoptedByCheckerTyping=1"));
        assert!(st.report().contains("declinedByMiniDefeq=1"));
    }
}
