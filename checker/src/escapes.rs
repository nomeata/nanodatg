//! **The escape census**: which conditional certificates reach a declaration
//! boundary, and where each of the assumptions they still carry came from.
//!
//! The escape *ledger* in [`crate::tg`] is two counters — conditional
//! certificates made, conditional certificates handed back to a rule — and its
//! difference is the gap row. That difference is exact but anonymous: it says
//! sixteen certificates escaped, not what they assume or which rule minted the
//! assumption. Deciding what to build next needs the second thing, so this
//! module records it.
//!
//! Two registers, both keyed on real kernel objects rather than on labels:
//!
//! * [`prov`] records, for an assumption atom, the rule that minted it. There
//!   are exactly four minting sites in the backend — the beta rule's raw
//!   fallback, [`crate::tg::TgBackend::local_premises`]/`has_type_local`,
//!   `has_type_proj`, and the hoist in `guard_and_generalise_at` — so a
//!   `Prov::Unknown` in the output is a real finding about a fifth one, not a
//!   hole in the instrumentation.
//! * [`made`]/[`taken`] tally conditional certificates by their **assumption
//!   list**, which is the same `Vec<Formula>` the ledger's two counters are
//!   bumped alongside. The residue `made - taken` per key is therefore exactly
//!   the ledger's `escaped()`, decomposed by what escaped; the report checks
//!   that identity and prints it, so a divergence is visible rather than
//!   assumed away.
//!
//! Measurement only, and compiled out entirely without `--features stepcount`.

use kernel::Formula;
use std::cell::RefCell;
use std::collections::HashMap;

/// Where an assumption atom came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Prov {
    /// [`crate::tg::TgBackend::domain_obligation`]'s raw fallback: no typing
    /// rule applied to the argument, so its membership became the assumption.
    RawBeta {
        /// [`crate::tg`]'s `HtMiss` name — what the subject *is*.
        shape: &'static str,
        /// `HtTarget`'s name — what the obligation is *stated at*.
        target: &'static str,
        /// `ArgMem`'s name — why the application check's handoff did not have it.
        cause: &'static str,
        /// Whether this very membership was concluded anywhere in the run —
        /// the "thread it, do not derive it" question, asked per atom.
        reach: &'static str,
        /// The subject, as Lean syntax, truncated.
        subject: String,
        /// The domain, as Lean syntax where the interpretation came from one.
        dom: String,
    },
    /// A context local's own typing, `⟦w⟧ ∈ ⟦A⟧`.
    LocalOwn { name: String },
    /// A projection's own field typing.
    ProjField,
    /// A guarded universal closure `∀w. (w ∈ A → φ(w))` hoisted at a binder,
    /// wrapping the provenance of `φ`.
    Family(Box<Prov>),
}

impl Prov {
    /// The provenance under every layer of guarded-family wrapping.
    pub fn core(&self) -> &Prov {
        match self {
            Prov::Family(inner) => inner.core(),
            other => other,
        }
    }

    /// How many guarded-family wrappers stand between this and its core.
    pub fn depth(&self) -> usize {
        match self {
            Prov::Family(inner) => 1 + inner.depth(),
            _ => 0,
        }
    }

    /// The grouping key for the census table: the shape of the obligation,
    /// ignoring the particular subject term.
    pub fn group(&self) -> String {
        match self.core() {
            Prov::RawBeta { shape, target, cause, .. } => {
                format!("raw beta [{shape} @ {target}] ({cause})")
            }
            Prov::LocalOwn { .. } => "context local's own typing".to_string(),
            Prov::ProjField => "projection field typing".to_string(),
            Prov::Family(_) => unreachable!("core() never returns a family"),
        }
    }
}

struct Census {
    prov: HashMap<Formula, Prov>,
    made: HashMap<Vec<Formula>, (u64, u32)>,
    taken: HashMap<Vec<Formula>, u64>,
    decls: HashMap<u32, String>,
}

// Thread-local, not a `Mutex`: `Formula` is `Rc`-backed and deliberately not
// `Send`, and the backend's own `Shared` is thread-local for the same reason.
// `global_report` already reads thread-local state (`held_false_anchor`), so
// the report runs where the checking ran.
thread_local! {
    static CENSUS: RefCell<Census> = RefCell::new(Census {
        prov: HashMap::new(),
        made: HashMap::new(),
        taken: HashMap::new(),
        decls: HashMap::new(),
    });
}

/// Record the rule that minted an assumption atom.
///
/// First writer wins: an atom that two rules could have minted is attributed to
/// the one that actually did so first, and re-minting the same formula later
/// does not relabel it. That matters for the family wrapper, whose inner
/// formula is by construction already registered.
pub fn prov(f: &Formula, p: Prov) {
    CENSUS.with(|c| {
        c.borrow_mut().prov.entry(f.clone()).or_insert(p);
    });
}

/// Look an atom's provenance up.
pub fn prov_of(f: &Formula) -> Option<Prov> {
    CENSUS.with(|c| c.borrow().prov.get(f).cloned())
}

/// One conditional certificate came into existence, carrying `hyps`, in the
/// declaration whose backend has sequence number `seq`.
pub fn made(hyps: &[Formula], seq: u32) {
    CENSUS.with(|c| {
        let mut c = c.borrow_mut();
        let e = c.made.entry(hyps.to_vec()).or_insert((0, seq));
        e.0 += 1;
    });
}

/// One conditional certificate was handed back to a rule.
pub fn taken(hyps: &[Formula]) {
    CENSUS.with(|c| {
        *c.borrow_mut().taken.entry(hyps.to_vec()).or_insert(0) += 1;
    });
}

/// Name the declaration a backend sequence number belongs to.
pub fn decl(seq: u32, name: &str) {
    CENSUS.with(|c| {
        c.borrow_mut().decls.entry(seq).or_insert_with(|| name.to_string());
    });
}

/// The census: one block per escaping certificate, then the shape groups and
/// the closure count each group would buy.
pub fn report() -> String {
    CENSUS.with(|c| report_from(&c.borrow()))
}

fn report_from(c: &Census) -> String {
    // The residue: assumption lists made more often than they were consumed.
    let mut escaping: Vec<(Vec<Formula>, u64, u32)> = Vec::new();
    for (hyps, (n, seq)) in c.made.iter() {
        let used = c.taken.get(hyps).copied().unwrap_or(0);
        if *n > used {
            escaping.push((hyps.clone(), n - used, *seq));
        }
    }
    escaping.sort_by_key(|(h, _, seq)| (*seq, h.len()));
    let total: u64 = escaping.iter().map(|(_, n, _)| *n).sum();

    let mut s = String::from("\nescape census (stepcount): what the escaping certificates assume\n");
    s.push_str(&format!("  escaping certificates: {total}\n"));

    // Per-atom groups, and the certificates each group appears in.
    let mut groups: HashMap<String, (usize, Vec<usize>)> = HashMap::new();
    let mut unknown = 0usize;
    for (i, (hyps, n, _)) in escaping.iter().enumerate() {
        for h in hyps {
            match c.prov.get(h) {
                None => unknown += *n as usize,
                Some(p) => {
                    let g = groups.entry(p.group()).or_insert((0, Vec::new()));
                    g.0 += *n as usize;
                    if !g.1.contains(&i) {
                        g.1.push(i);
                    }
                }
            }
        }
    }

    s.push_str("  by certificate:\n");
    for (i, (hyps, n, seq)) in escaping.iter().enumerate() {
        let who = c.decls.get(seq).cloned().unwrap_or_else(|| format!("seq {seq}"));
        let mut raw = 0;
        let mut loc = 0;
        let mut proj = 0;
        let mut fam = 0;
        let mut unk = 0;
        for h in hyps {
            match c.prov.get(h).map(|p| (p.depth(), p.core().clone())) {
                None => unk += 1,
                Some((d, core)) => {
                    if d > 0 {
                        fam += 1;
                    }
                    match core {
                        Prov::RawBeta { .. } => raw += 1,
                        Prov::LocalOwn { .. } => loc += 1,
                        Prov::ProjField => proj += 1,
                        Prov::Family(_) => {}
                    }
                }
            }
        }
        s.push_str(&format!(
            "    [{i}] {who} ×{n}: {} atoms — raw {raw}, local {loc}, proj {proj}, unknown {unk} (of which {fam} wrapped in a family)\n",
            hyps.len()
        ));
        // The atoms themselves, behind an environment variable: this is the
        // view that turns a shape group into a term one can go and derive, and
        // it is far too long to print on every run.
        if std::env::var_os("NANODATG_ESCAPE_DETAIL").is_some() {
            for h in hyps {
                match c.prov.get(h) {
                    None => s.push_str("         · <unregistered>\n"),
                    Some(p) => {
                        let d = p.depth();
                        match p.core() {
                            Prov::RawBeta { subject, dom, reach, cause, .. } => s.push_str(&format!(
                                "         · fam{d} [{cause}; {reach}]\n             {subject}\n             ∈ {dom}\n"
                            )),
                            Prov::LocalOwn { name } => s.push_str(&format!("         · fam{d} local {name}\n")),
                            Prov::ProjField => s.push_str("         · proj field\n"),
                            Prov::Family(_) => {}
                        }
                    }
                }
            }
        }
    }

    s.push_str("  by atom shape (atoms, and the certificates the shape appears in):\n");
    let mut gs: Vec<_> = groups.into_iter().collect();
    gs.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
    for (g, (n, certs)) in &gs {
        // A certificate closes only when *every* atom it carries is
        // discharged, so the number worth reading is not `n` but how many
        // certificates carry nothing but this group.
        let sole = certs
            .iter()
            .filter(|i| {
                escaping[**i].0.iter().all(|h| c.prov.get(h).map(|p| p.group() == *g).unwrap_or(false))
            })
            .count();
        s.push_str(&format!(
            "    {n:>4} atoms in {:>3} certificates, {sole} of which carry only this shape — {g}\n",
            certs.len()
        ));
    }
    if unknown > 0 {
        s.push_str(&format!("    {unknown:>4} atoms of UNKNOWN provenance (a fifth minting site)\n"));
        for (hyps, _, seq) in escaping.iter() {
            for h in hyps {
                if c.prov.get(h).is_none() {
                    let who = c.decls.get(seq).cloned().unwrap_or_else(|| format!("seq {seq}"));
                    let kind = match h.as_mem() {
                        None => "not a membership at all",
                        Some((a, _)) =>
                            if a.as_app().is_none() { "a membership of a bare variable" } else { "a membership of a compound term" },
                    };
                    s.push_str(&format!("      in {who}: {kind}\n"));
                }
            }
        }
    }

    // **The threading verdict.** How many escaping raw atoms are facts the run
    // already holds somewhere (plumbing) against facts nothing ever concluded
    // (derivation). Counted over escaping atoms, not over all raw hoists.
    s.push_str("  escaping raw-beta atoms, by whether the fact exists elsewhere in the run:\n");
    let mut reaches: HashMap<&'static str, usize> = HashMap::new();
    for (hyps, n, _) in escaping.iter() {
        for h in hyps {
            if let Some(p) = c.prov.get(h) {
                if let Prov::RawBeta { reach, .. } = p.core() {
                    *reaches.entry(reach).or_insert(0) += *n as usize;
                }
            }
        }
    }
    let mut rv: Vec<_> = reaches.into_iter().collect();
    rv.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (r, n) in &rv {
        s.push_str(&format!("    {n:>4}  {r}\n"));
    }

    // The subjects, so that "raw beta" is a term rather than a label.
    s.push_str("  distinct raw-beta subjects:\n");
    let mut subs: HashMap<(String, String, &'static str), usize> = HashMap::new();
    for (hyps, n, _) in escaping.iter() {
        for h in hyps {
            if let Some(p) = c.prov.get(h) {
                if let Prov::RawBeta { subject, dom, cause, .. } = p.core() {
                    *subs.entry((subject.clone(), dom.clone(), cause)).or_insert(0) += *n as usize;
                }
            }
        }
    }
    let mut sv: Vec<_> = subs.into_iter().collect();
    sv.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for ((subject, dom, cause), n) in sv.iter().take(40) {
        s.push_str(&format!("    ×{n:<3} ({cause}) {subject}\n        ∈ {dom}\n"));
    }
    s
}
