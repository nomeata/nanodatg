//! **What mini proved, listed** — every theorem the interpretation stored,
//! grouped, sorted, and with its absences named.
//!
//! # Interface
//!
//! ```text
//! dump::Filter { decl: Option<String>, sigma: Option<Vec<u32>> }
//! dump::render(ip, decls, schedule, &filter) -> String
//! ```
//!
//! `mini --dump-theorems <export>` prints it. `--dump-only <name>` and
//! `--dump-sigma <n,m>` narrow it, because the corpus dump is thousands of
//! lines and a reader almost always wants one declaration.
//!
//! # Why this is rendered inside the run
//!
//! For the reason [`crate::blocker::Blocker`] is: [`Interp`] is `Rc`-backed and
//! [`crate::run::Outcome`] has to cross a thread join, so the *only* place the
//! store can be read is inside the worker that owns it. The dump is therefore a
//! `String` on the `Outcome`, built while the `Interp` is still alive, exactly
//! as the blocker report is.
//!
//! # The three properties this module is built around
//!
//! **1. Deterministic.** Every store here is a `HashMap`, whose iteration order
//! is seeded per process and differs between two runs of the same file. Nothing
//! is ever printed in store order: declarations sort by rendered name and then
//! by σ, and the apparatus sections sort the same way. A dump that reordered
//! between runs would be useless for the diffing that is most of its value, and
//! `mini/tests/dump.rs` asserts byte-equality across two runs.
//!
//! **2. Honest about absence.** MINI-DESIGN.md §0.5's standing lesson — *read a
//! zero row twice* — is that a missing row means either "solved" or "never
//! reached", and a ledger that cannot tell them apart costs planning mistakes.
//! So this dump **enumerates the schedule, not the store**: every
//! `(declaration, σ)` the pre-pass scheduled gets a row, and a pair with no
//! entry in [`Interp::get_const`] is printed as `not reached`, which is a
//! different string from a pair that was reached and whose typing is `Err(gap)`.
//! The same at the apparatus: a declaration in
//! [`IndApparatus::declined`](crate::interp::IndApparatus) prints with its
//! reason, and a lazily-built table that was never asked for prints
//! `not built` rather than being silently skipped.
//!
//! **3. Only the real statement.** Every theorem line is
//! [`kernel::Thm::concl`] of a theorem that is actually in the store — nothing
//! here reconstructs what a theorem "should" say from its name. The one active
//! step is [`peeled`], which strips outermost `∀`s by `mp(ax_inst(…))`; that is
//! *derivation*, not reconstruction, so what is printed remains the conclusion
//! of a theorem mini can produce. Where the renderer cannot see — a `∀` under
//! an implication, a term with no label — it prints `∀ …` or `⟨·⟩` rather than
//! a guess, which is [`crate::blocker::show_term`]'s existing discipline.
//!
//! # What this module does not print, and why
//!
//! * **Sub-theorems consumed into a stored result.** `zoneb`'s `DeclUniv` (the
//!   carrier's `⊢ ∀p⃗. ind(p⃗) ∈ Uₙ`) and `family::IndexedUniverse` are built as
//!   locals and folded into a `ConstInterp::typing`; they are not in any store,
//!   so there is nothing to read back and a printed one would have to be
//!   rebuilt. Property 3 says say so instead, and the universe section does.
//! * **The `LamSite`/`FibreSite`/`CondSite` registries.** They hold defining
//!   axioms for per-shape symbols (`⊢ ∀x. app(t,x) = …`), which are real
//!   theorems, but there is one per *body shape* — thousands on the corpus,
//!   named only by number — and they are machinery rather than statements about
//!   a Lean declaration. Counted in the summary, not listed.
//! * **`Cumul`.** `⊢ Uₘ ⊆ Uₙ` for every `m ≤ n ≤ 8` is built eagerly and is the
//!   same 45 theorems on every run, independent of the file.

use std::collections::HashMap;
use std::fmt::Write as _;

use kernel::{Term, Thm};

use crate::blocker::show_term;
use crate::env::Declaration;
use crate::ev::Gap;
use crate::expr::Name;
use crate::interp::{ConstKey, Interp};
use crate::ledger::Ledger;

/// How many outermost `∀`s [`peeled`] will strip. A recursor typing has one
/// per parameter, one per minor, plus the indices — a dozen is the whole of
/// even `RBTree.rec`, and the cap exists so a malformed theorem cannot spin.
const PEEL_CAP: usize = 16;

/// Narrow the dump. Both empty is the whole file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Filter {
    /// Only this declaration, matched exactly against the rendered name.
    pub decl: Option<String>,
    /// Only this ground instantiation.
    pub sigma: Option<Vec<u32>>,
}

impl Filter {
    fn keeps(&self, name: &str, sigma: &[u32]) -> bool {
        if let Some(d) = &self.decl {
            if d != name {
                return false
            }
        }
        match &self.sigma {
            Some(s) => s == sigma,
            None => true,
        }
    }

    /// A declaration-level test, for the apparatus sections, which are keyed by
    /// the *inductive's* name rather than the pair's.
    fn keeps_decl(&self, name: &str) -> bool {
        self.decl.as_ref().map(|d| d == name).unwrap_or(true)
    }
}

/// `u := 0, v := 1`, or `—`. The same spelling
/// [`crate::blocker::Draft`] uses, so a blocker and a dump name one pair alike.
fn sigma_str(lparams: &[Name], sigma: &[u32]) -> String {
    if sigma.is_empty() {
        return "—".to_string()
    }
    sigma
        .iter()
        .enumerate()
        .map(|(i, n)| match lparams.get(i) {
            Some(p) => format!("{p} := {n}"),
            None => format!("?{i} := {n}"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// The sort key for a `(name, σ)` pair.
///
/// [`Name`] is `Eq + Hash` but **not `Ord`**, so a `ConstKey` cannot be sorted
/// directly; the rendered name is the key, and it is stable because `Display`
/// for a `Name` is a pure function of the name.
fn key_of(k: &ConstKey) -> (String, Vec<u32>) { (k.0.to_string(), k.1.clone()) }

/// Strip the outermost `∀`s of a theorem, **as a derivation**.
///
/// `⊢ ∀x. φ` becomes `⊢ φ[x₀]` by `mp(ax_inst(∀x. φ, x₀), thm)` with `x₀` a
/// variable minted for the purpose and labelled, so the body is printed with
/// named binders instead of collapsing to [`show_formula`]'s `∀ …`. Both steps
/// are kernel inference rules, so the conclusion printed is a real theorem's
/// real conclusion — the alternative, reading under the binder, is not
/// available outside `kernel` (`Formula::instantiate` is `pub(crate)`) and
/// would be reconstruction rather than derivation if it were.
///
/// Returns the binder names peeled and the theorem left underneath. Minting a
/// variable advances the `Env`'s counter and adds a label; neither can change
/// any stored theorem, which is why observing the store this way is safe.
fn peeled(ip: &mut Interp, thm: &Thm) -> (Vec<String>, Thm) {
    let mut cur = thm.clone();
    let mut names = Vec::new();
    while names.len() < PEEL_CAP && cur.concl().is_forall() {
        let v = ip.env.fresh_var();
        let t = Term::var(v);
        let nm = format!("x{}", names.len());
        ip.set_label(&t, nm.clone());
        let Some(step) = Thm::ax_inst(cur.concl().clone(), t) else { break };
        let Some(next) = Thm::mp(&step, &cur) else { break };
        cur = next;
        names.push(nm);
    }
    (names, cur)
}

/// `⊥`, identified by elimination.
///
/// `Formula` is not `PartialEq`, so `False` cannot be compared for; but the
/// language has exactly five formula shapes and four of them have public
/// destructors, so ruling those out *is* the test. This is the same inference
/// [`crate::blocker::show_formula`]'s final fallback makes, named so the
/// connective decoding below can rely on it.
fn is_false(phi: &kernel::Formula) -> bool {
    phi.as_mem().is_none() && phi.as_eq().is_none() && phi.as_imp().is_none() && !phi.is_forall()
}

/// A formula with `¬`, `∧` and `∨` decoded.
///
/// [`crate::blocker::show_formula`] prints the primitives, and the kernel's
/// language *has* only `⊥`, `=`, `∈`, `→` and `∀` — `Formula::and` is
/// `¬(φ → ¬ψ)` and `Formula::or` is `¬φ → ψ`. Printed literally, one
/// constructor membership of `RBTree` is four lines of `(… → (⊥)) → (⊥)`, which
/// is faithful and unreadable. Decoding the three derived connectives back is
/// not a guess about what the theorem says: it inverts a total, injective
/// encoding that `kernel::Formula` documents, and every shape it does not
/// recognise falls through to the primitive spelling.
///
/// Kept here rather than in `blocker` so the blocker report's format, which
/// tests assert on, is not changed by this feature.
fn show_f(ip: &Interp, phi: &kernel::Formula, d: usize) -> String {
    if d == 0 {
        return "…".to_string()
    }
    if let Some((a, b)) = phi.as_mem() {
        return format!("{} ∈ {}", show_term(ip, &a, 4), show_term(ip, &b, 4))
    }
    if let Some((a, b)) = phi.as_eq() {
        return format!("{} = {}", show_term(ip, &a, 4), show_term(ip, &b, 4))
    }
    if let Some((p, q)) = phi.as_imp() {
        if is_false(&q) {
            // `¬p` — and `p` itself may be the `φ → ¬ψ` of a conjunction.
            if let Some((a, r)) = p.as_imp() {
                if let Some((b, f)) = r.as_imp() {
                    if is_false(&f) {
                        return format!("({} ∧ {})", show_f(ip, &a, d - 1), show_f(ip, &b, d - 1))
                    }
                }
            }
            return format!("¬{}", show_f(ip, &p, d - 1))
        }
        // `¬a → q` is `a ∨ q`.
        if let Some((a, f)) = p.as_imp() {
            if is_false(&f) {
                return format!("({} ∨ {})", show_f(ip, &a, d - 1), show_f(ip, &q, d - 1))
            }
        }
        return format!("({} → {})", show_f(ip, &p, d - 1), show_f(ip, &q, d - 1))
    }
    if phi.is_forall() {
        return "∀ …".to_string()
    }
    "⊥".to_string()
}

/// How deep [`show_f`] descends before printing `…`.
const FORMULA_DEPTH: usize = 24;

/// One stored theorem, rendered as `[n hyp] ⊢ ∀x0 x1. body`.
///
/// The hypothesis count is the *original* theorem's: `mp` and `ax_inst`
/// preserve hypotheses, so peeling cannot hide one. A theorem that is still
/// quantified at the cap says so rather than looking closed.
pub fn show(ip: &mut Interp, thm: &Thm) -> String {
    let hyps = match thm.hyps().len() {
        0 => String::new(),
        n => format!("[{n} hyp] "),
    };
    let (names, inner) = peeled(ip, thm);
    let body = show_f(ip, inner.concl(), FORMULA_DEPTH);
    let quant = if names.is_empty() { String::new() } else { format!("∀{}. ", names.join(" ")) };
    let more = if inner.concl().is_forall() { "   (∀ nest deeper than the peel cap)" } else { "" };
    format!("{hyps}⊢ {quant}{body}{more}")
}

// ────────────────────────────────────────────────── collect, then render ──

/// A line of the dump: a real theorem, a term, or a named absence.
///
/// Collected before rendering because rendering needs `&mut Interp` (it mints
/// peel variables) while the stores are borrowed out of the same `Interp`.
/// `Thm` and `Term` are cheap to clone, so the two phases cost nothing.
enum Item {
    Thm(Box<Thm>),
    Term(Term),
    /// Nothing is stored, and this is why. **Never** an empty string: an
    /// unexplained absence is the defect §0.5 is about.
    Absent(String),
}

struct Line {
    label: String,
    item: Item,
}

impl Line {
    fn thm(label: impl Into<String>, t: &Thm) -> Line {
        Line { label: label.into(), item: Item::Thm(Box::new(t.clone())) }
    }

    fn term(label: impl Into<String>, t: &Term) -> Line {
        Line { label: label.into(), item: Item::Term(t.clone()) }
    }

    fn absent(label: impl Into<String>, why: impl Into<String>) -> Line {
        Line { label: label.into(), item: Item::Absent(why.into()) }
    }

    fn opt(label: impl Into<String>, t: Option<&Thm>, why: &str) -> Line {
        match t {
            Some(t) => Line::thm(label, t),
            None => Line::absent(label, why),
        }
    }
}

/// A titled group of lines, with an optional one-line summary.
struct Group {
    title: String,
    note: Option<String>,
    lines: Vec<Line>,
}

fn render_group(ip: &mut Interp, out: &mut String, g: &Group, indent: &str) {
    let _ = writeln!(out, "{indent}{}", g.title);
    if let Some(n) = &g.note {
        let _ = writeln!(out, "{indent}  {n}");
    }
    // The label column is padded to the widest label in *this* group, so a
    // group reads as a table without the whole dump being padded to its widest
    // line anywhere.
    let w = g.lines.iter().map(|l| l.label.chars().count()).max().unwrap_or(0);
    for l in &g.lines {
        let pad = " ".repeat(w - l.label.chars().count());
        let body = match &l.item {
            Item::Thm(t) => show(ip, t),
            Item::Term(t) => show_term(ip, t, 4),
            Item::Absent(why) => format!("({why})"),
        };
        let _ = writeln!(out, "{indent}  {}{pad}  {body}", l.label);
    }
}

// ──────────────────────────────────────────────────────── the constants ──

/// Per declaration and σ, the pair's own deliverables.
///
/// Enumerated from the **schedule**, so a scheduled pair the interpretation
/// never reached is a printed row rather than a silent gap. Property 2.
fn const_groups(ip: &Interp, sched: &Sched, f: &Filter) -> Vec<Group> {
    let mut out = Vec::new();
    let mut names: Vec<&DeclInfo> = sched.order.iter().collect();
    names.sort_by(|a, b| a.shown.cmp(&b.shown));
    for d in names {
        if !f.keeps_decl(&d.shown) {
            continue
        }
        let mut sigmas = d.sigmas.clone();
        sigmas.sort();
        for s in &sigmas {
            if !f.keeps(&d.shown, s) {
                continue
            }
            let key: ConstKey = (d.name.clone(), s.clone());
            let title = format!("{}   σ = {}", d.shown, sigma_str(&d.lparams, s));
            let lines = match ip.get_const(&key) {
                None => vec![Line::absent(
                    "⟦c.{σ}⟧",
                    "not reached — this pair was scheduled and no interpretation was stored \
                     for it; the run stopped earlier, it is not a pair that succeeded silently",
                )],
                Some(c) => {
                    let mut v = vec![Line::term("⟦c.{σ}⟧", &c.term)];
                    match &c.typing {
                        Ok(s) => v.push(Line::thm("typing", s.thm())),
                        Err(g) => v.push(Line::absent(
                            "typing",
                            format!("no ⊢ ⟦c.{{σ}}⟧ ∈ ⟦ty[σ]⟧ — waiting on {}", Ledger::key(Some(g))),
                        )),
                    }
                    match (&c.defeq, d.has_value) {
                        (Some(s), _) => v.push(Line::thm("defeq", s.thm())),
                        (None, true) => v.push(Line::absent(
                            "defeq",
                            "this declaration has a value, so ⊢ ⟦c.{σ}⟧ = ⟦val[σ]⟧ was expected \
                             and is missing",
                        )),
                        (None, false) => v.push(Line::absent(
                            "defeq",
                            "none expected — not a transparent definition",
                        )),
                    }
                    v
                }
            };
            out.push(Group { title, note: None, lines });
        }
    }
    out
}

// ──────────────────────────────────────────────────────── the apparatus ──

/// The zone-B stores: carriers, constructors, recursors and ι rules.
fn apparatus_groups(ip: &Interp, f: &Filter) -> (Vec<Group>, Option<String>) {
    let Some(app) = ip.ind_opt() else {
        return (
            Vec::new(),
            Some(
                "not built — no declaration in this file reached zone B. This is an absence of \
                 attempts, not of results."
                    .to_string(),
            ),
        )
    };
    let mut out = Vec::new();

    // ── the shared, lazily-built apparatus ────────────────────────────────
    let mut shared = Vec::new();
    match app.stored_wrec() {
        Some(w) => {
            shared.push(Line::thm("W ι", &w.iota));
            shared.push(Line::thm("W funspace", &w.funspace));
            shared.push(Line::thm("W value", &w.rc.value));
            shared.push(Line::thm("W comp typed", &w.rc.comp_typed));
        }
        None => shared.push(Line::absent(
            "W recursor",
            if app.wrec_attempted() {
                "build attempted and failed"
            } else {
                "not built — nothing in this file needed the class-(T) eliminator"
            },
        )),
    }
    match app.stored_acc() {
        Some(a) => {
            shared.push(Line::thm("acc subset", &a.acc_subset));
            shared.push(Line::thm("acc induction", &a.acc_induction));
            shared.push(Line::thm("acc intro", &a.acc_intro));
        }
        None => shared.push(Line::absent(
            "acc",
            if app.acc_attempted() {
                "build attempted and failed"
            } else {
                "not built — no class-(S) declaration in this file"
            },
        )),
    }
    match app.stored_trunc() {
        Some(t) => {
            shared.push(Line::thm("‖·‖ intro", &t.intro));
            shared.push(Line::thm("‖·‖ elim", &t.elim));
            shared.push(Line::thm("‖·‖ subset", &t.subset));
        }
        None => shared.push(Line::absent(
            "truncation",
            if app.trunc_attempted() {
                "build attempted and failed"
            } else {
                "not built — no class-(P) declaration in this file"
            },
        )),
    }
    if f.decl.is_none() {
        out.push(Group {
            title: "shared apparatus".to_string(),
            note: Some("built on first use, so an absence here is a statement about the file"
                .to_string()),
            lines: shared,
        });
    }

    // ── non-indexed translated declarations ───────────────────────────────
    let mut decls: Vec<(&ConstKey, _)> = app.decls.iter().collect();
    decls.sort_by_key(|(k, _)| key_of(k));
    for (k, tr) in decls {
        let shown = k.0.to_string();
        if !f.keeps(&shown, &k.1) {
            continue
        }
        let ind = &tr.ind;
        let mut lines = vec![
            Line::term("carrier", &ind.carrier),
            Line::thm("carrier ax", &ind.ty_ax),
            Line::thm("closed", &ind.closed),
        ];
        for c in &ind.ctors {
            lines.push(Line::thm(format!("ctor {} mem", c.index), &c.mem));
            lines.push(Line::opt(
                format!("ctor {} inj", c.index),
                c.inj.as_ref(),
                "none — a nullary constructor has no injectivity statement",
            ));
        }
        lines.push(Line::absent(
            "universe",
            "⊢ ∀p⃗. ind(p⃗) ∈ Uₙ is built as a local in zoneb::DeclUniv and folded into the \
             constant's typing; it is in no store, so it cannot be read back",
        ));
        // The eliminator, which is keyed by the declaration and built once.
        match app.deprecs.get(k) {
            Some(dr) => {
                lines.push(Line::thm("rec typing", &dr.dr.typing));
                lines.push(Line::thm("rec step typed", &dr.gr.step_typed));
                for (i, t) in dr.dr.iota.iter().enumerate() {
                    lines.push(Line::thm(format!("ι {i}"), t));
                }
                for (i, t) in dr.gr.iota.iter().enumerate() {
                    lines.push(Line::thm(format!("gen ι {i}"), t));
                }
            }
            None => lines.push(Line::absent(
                "recursor",
                if app.deprec_failed.contains(k) {
                    "build attempted and failed".to_string()
                } else {
                    "not built — this declaration's eliminator was never asked for".to_string()
                },
            )),
        }
        out.push(Group {
            title: format!("inductive {shown}   σ = {:?}", k.1),
            note: Some(format!("{} constructor(s), non-indexed", ind.ctors.len())),
            lines,
        });
    }

    // ── indexed families ──────────────────────────────────────────────────
    let mut ixs: Vec<(&ConstKey, _)> = app.indexed.iter().collect();
    ixs.sort_by_key(|(k, _)| key_of(k));
    for (k, it) in ixs {
        let shown = k.0.to_string();
        if !f.keeps(&shown, &k.1) {
            continue
        }
        let ii = &it.ii;
        let mut lines = vec![
            Line::thm("carrier ax", &ii.carrier.ty_ax),
            Line::thm("subset W", &ii.carrier.subset_w),
            Line::thm("intro", &ii.carrier.intro),
            Line::thm("good funspace", &ii.good.funspace),
            Line::thm("good W ι", &ii.good.wrec_iota),
        ];
        for (i, t) in ii.good.iota.iter().enumerate() {
            lines.push(Line::thm(format!("good ι {i}"), t));
        }
        for (i, c) in ii.carrier.ctors.iter().enumerate() {
            lines.push(Line::thm(format!("ctor {i} mem"), &c.mem));
            lines.push(Line::thm(format!("ctor {i} inv"), &c.inv));
        }
        match app.stored_prop_rec(k) {
            Some(r) => lines.push(Line::thm("Prop-motive rec", &r.rec)),
            None => lines.push(Line::absent(
                "Prop-motive rec",
                if app.prop_rec_attempted(k) {
                    "build attempted and failed"
                } else {
                    "not built — never asked for"
                },
            )),
        }
        match app.stored_dep_rec_ix(k) {
            Some(r) => {
                lines.push(Line::thm("value-motive rec", &r.typing));
                // Not an oversight: `IndexedDepRecursor` has no `iota` field.
                lines.push(Line::absent(
                    "value-motive ι",
                    "not stored — derived/…/family/dep_rec.rs §\"What is not here\" says the \
                     indexed ι at a value motive is neither built nor tested; the GenRecursor ι \
                     above is expected to be all of it, unchecked",
                ));
            }
            None => lines.push(Line::absent(
                "value-motive rec",
                if app.dep_rec_ix_attempted(k) {
                    "build attempted and failed"
                } else {
                    "not built — never asked for"
                },
            )),
        }
        out.push(Group {
            title: format!("indexed {shown}   σ = {:?}", k.1),
            note: Some(format!("{} constructor(s), indexed family", ii.carrier.ctors.len())),
            lines,
        });
    }

    // ── class-(S) propositional declarations ──────────────────────────────
    let mut props: Vec<(&ConstKey, _)> = app.props.iter().collect();
    props.sort_by_key(|(k, _)| key_of(k));
    for (k, cs) in props {
        let shown = k.0.to_string();
        if !f.keeps(&shown, &k.1) {
            continue
        }
        let mut lines = vec![
            Line::thm("carrier ∈ U₀", &cs.in_u0),
            Line::thm("φ axiom", &cs.lc.phi_ax),
            Line::thm("χ", &cs.lp.chi),
            Line::thm("subsingleton", &cs.lp.subsingleton),
            Line::thm("elim", &cs.lp.elim),
        ];
        for (i, t) in cs.lc.intro.iter().enumerate() {
            lines.push(Line::thm(format!("intro {i}"), t));
        }
        match app.stored_prop_fields(k) {
            Some(pf) => {
                for (i, t) in pf.steps.iter().enumerate() {
                    lines.push(Line::thm(format!("field step {i}"), t));
                }
                lines.push(Line::opt("inhabited", pf.inhabited.as_ref(), "none — no fields"));
                lines.push(Line::opt("guard", pf.guard.as_ref(), "none — no guard needed"));
            }
            None => lines.push(Line::absent(
                "field ladder",
                if app.prop_fields_attempted(k) {
                    "build attempted and failed"
                } else {
                    "not built — never asked for"
                },
            )),
        }
        lines.push(Line::absent(
            "ι",
            "none — the class-(S) route eliminates through LePropRecursor, which is not \
             retained in the apparatus",
        ));
        out.push(Group {
            title: format!("class-(S) {shown}   σ = {:?}", k.1),
            note: None,
            lines,
        });
    }

    (out, None)
}

/// Names for the terms `derived/` built, so the apparatus does not print as
/// `⟨·⟩`.
///
/// [`crate::blocker::show_term`] can name a term two ways: the label registry,
/// and [`Interp::parts_of`], which only knows terms mini built through
/// `Interp::mk`. A carrier, a `W`, an index space and a constructor term are
/// all built *inside* `derived/`, so neither applies and every one of them
/// prints `⟨·⟩`. They are recoverable here because the apparatus stores the
/// terms themselves; labelling is retroactive, since the registry is keyed by
/// the term.
///
/// Collected rather than applied in place: the stores are borrowed out of the
/// `Interp` that `set_label` needs mutably.
fn apparatus_labels(ip: &Interp) -> Vec<(Term, String)> {
    let mut out = Vec::new();
    let Some(app) = ip.ind_opt() else { return out };
    let mut decls: Vec<(&ConstKey, _)> = app.decls.iter().collect();
    decls.sort_by_key(|(k, _)| key_of(k));
    for (k, tr) in decls {
        let n = k.0.to_string();
        out.push((tr.ind.carrier.clone(), format!("⟦{n}⟧")));
        out.push((tr.ind.wty.clone(), "W".to_string()));
        for c in &tr.ind.ctors {
            out.push((c.term.clone(), format!("{n}.ctor{}", c.index)));
            out.push((c.tag.clone(), format!("{n}.tag{}", c.index)));
        }
    }
    let mut ixs: Vec<(&ConstKey, _)> = app.indexed.iter().collect();
    ixs.sort_by_key(|(k, _)| key_of(k));
    for (k, it) in ixs {
        let n = k.0.to_string();
        out.push((it.ii.carrier.carrier.clone(), format!("⟦{n}⟧")));
        out.push((it.ii.ix.idx.clone(), format!("Idx({n})")));
        out.push((it.ii.ix.target.clone(), format!("𝒫(Idx({n}))")));
        out.push((it.base.wty.clone(), "W".to_string()));
        for c in &it.base.ctors {
            out.push((c.term.clone(), format!("{n}.ctor{}", c.index)));
            out.push((c.tag.clone(), format!("{n}.tag{}", c.index)));
        }
    }
    out
}

/// Declarations and constructors the boundary declined, with the reason.
///
/// Its own section because a decline is the one absence that is *recorded*
/// rather than inferred, and §0.5's lesson is that those must be legible.
fn declined_group(ip: &Interp, f: &Filter) -> Group {
    let mut lines = Vec::new();
    if let Some(app) = ip.ind_opt() {
        let mut ds: Vec<(&ConstKey, &Gap)> = app.declined.iter().collect();
        ds.sort_by_key(|(k, _)| key_of(k));
        for (k, g) in ds {
            let shown = k.0.to_string();
            if f.keeps(&shown, &k.1) {
                lines.push(Line::absent(
                    format!("{shown} σ={:?}", k.1),
                    format!("declined: {}", Ledger::key(Some(g))),
                ));
            }
        }
        let mut cs: Vec<(&ConstKey, &Gap)> = app.ctor_declined.iter().collect();
        cs.sort_by_key(|(k, _)| key_of(k));
        for (k, g) in cs {
            let shown = k.0.to_string();
            if f.keeps(&shown, &k.1) {
                lines.push(Line::absent(
                    format!("{shown} σ={:?}", k.1),
                    format!("constructor declined: {}", Ledger::key(Some(g))),
                ));
            }
        }
    }
    let note = if lines.is_empty() {
        Some("nothing was declined in this file".to_string())
    } else {
        Some("a decline is recorded once and not retried; the reason is the ledger's own key"
            .to_string())
    };
    Group { title: "declined".to_string(), note, lines }
}

// ─────────────────────────────────────────────────────────── the schedule ──

struct DeclInfo {
    name: Name,
    shown: String,
    lparams: Vec<Name>,
    sigmas: Vec<Vec<u32>>,
    has_value: bool,
}

struct Sched {
    order: Vec<DeclInfo>,
}

/// The pairs the interpretation pass owes, **exactly as
/// [`crate::ledger::Ledger::run`] enumerates them**.
///
/// Mirrored rather than recomputed on purpose: `Quot` and `Inductive` are
/// skipped there (they carry no interpretable expression pair), and a
/// declaration the pre-pass gave no σ still gets the all-zero one. A dump whose
/// pair population disagreed with the ledger's would make the two instruments
/// uncomparable, which is the mistake `Ledger::key` exists to avoid one level
/// down.
fn schedule_of(decls: &[Declaration], sched: &HashMap<Name, Vec<Vec<u32>>>) -> Sched {
    let mut order = Vec::new();
    for d in decls {
        let (name, lparams, has_value) = match d {
            Declaration::Axiom { name, lparams, .. } => (name, lparams, false),
            Declaration::Def { name, lparams, .. } => (name, lparams, true),
            Declaration::Quot | Declaration::Inductive { .. } => continue,
        };
        let sigmas = match sched.get(name) {
            Some(v) if !v.is_empty() => v.clone(),
            _ => vec![vec![0; lparams.len()]],
        };
        order.push(DeclInfo {
            shown: name.to_string(),
            lparams: lparams.clone(),
            sigmas,
            has_value,
            name: name.clone(),
        });
    }
    order.sort_by(|a, b| a.shown.cmp(&b.shown));
    Sched { order }
}

/// Constants in the store that no scheduled pair covers — the type formers,
/// constructors and recursors zone B mints while interpreting *another*
/// declaration.
///
/// Listed separately because they are real stored theorems that the pair
/// enumeration above structurally cannot reach: `Ledger::run` skips
/// `Declaration::Inductive`, so `⟦List.{0}⟧` is in the store with nothing in
/// the schedule pointing at it. Leaving them out would be the §0.5 defect in
/// its other direction — a silence that looks like nothing was proved.
fn extra_consts(ip: &Interp, sched: &Sched, f: &Filter) -> Vec<Group> {
    let mut covered: Vec<ConstKey> = Vec::new();
    for d in &sched.order {
        for s in &d.sigmas {
            covered.push((d.name.clone(), s.clone()));
        }
    }
    let mut keys = ip.const_keys();
    keys.retain(|k| !covered.contains(k));
    keys.sort_by_key(key_of);
    let mut out = Vec::new();
    for k in &keys {
        let shown = k.0.to_string();
        if !f.keeps(&shown, &k.1) {
            continue
        }
        let Some(c) = ip.get_const(k) else { continue };
        let mut lines = vec![Line::term("⟦c.{σ}⟧", &c.term)];
        match &c.typing {
            Ok(s) => lines.push(Line::thm("typing", s.thm())),
            Err(g) => lines.push(Line::absent(
                "typing",
                format!("no typing — waiting on {}", Ledger::key(Some(g))),
            )),
        }
        if let Some(s) = &c.defeq {
            lines.push(Line::thm("defeq", s.thm()));
        }
        out.push(Group {
            title: format!("{shown}   σ = {:?}", k.1),
            note: None,
            lines,
        });
    }
    out
}

// ────────────────────────────────────────────────────────────── the dump ──

/// Render the whole stored context.
///
/// `decls` and `schedule` are what [`crate::ledger::Ledger::run`] was driven
/// from; they are the authority on which pairs *should* exist, which is what
/// makes a missing one reportable rather than invisible.
pub fn render(
    ip: &mut Interp,
    decls: &[Declaration],
    schedule: &HashMap<Name, Vec<Vec<u32>>>,
    filter: &Filter,
) -> String {
    let sched = schedule_of(decls, schedule);
    let pairs: usize = sched.order.iter().map(|d| d.sigmas.len()).sum();

    // Phase 1 — collect, with the stores borrowed immutably.
    let cgs = const_groups(ip, &sched, filter);
    let xgs = extra_consts(ip, &sched, filter);
    let (ags, app_note) = apparatus_groups(ip, filter);
    let dg = declined_group(ip, filter);
    let stored = ip.const_count();
    let sites = ip.site_count();
    let names = apparatus_labels(ip);
    for (t, n) in &names {
        ip.set_label(t, n.clone());
    }

    // The terms a dump is most likely to have to name, named once. This works
    // *retroactively* — `labels` is keyed by the term, and `Interp::sort`
    // returns the tower's own term rather than a fresh one — so seeding here
    // names the sorts already sitting inside theorems the pass stored.
    for n in 0..=crate::interp::CUMUL_HEIGHT as u32 {
        let s = ip.sort(n);
        ip.set_label(&s, format!("⟦Sort {n}⟧"));
    }
    let pt = ip.point();
    ip.set_label(&pt, "•");

    // Phase 2 — render, which mints peel variables and so needs `&mut`.
    let mut out = String::new();
    let _ = writeln!(
        out,
        "THEOREMS\t{pairs} pairs\t{stored} stored\t{} groups",
        cgs.len() + xgs.len() + ags.len()
    );
    if filter != &Filter::default() {
        let _ = writeln!(
            out,
            "  filter       decl={:?} sigma={:?}",
            filter.decl.as_deref().unwrap_or("*"),
            filter.sigma
        );
    }
    let _ = writeln!(out, "  scheduled    {pairs} (declaration, σ) pairs over {} declarations", sched.order.len());
    let _ = writeln!(out, "  stored       {stored} constant interpretations");
    let _ = writeln!(out, "  binder sites {sites} lam/fibre/cond symbols with defining axioms (not listed)");

    let _ = writeln!(out, "\n── constants ─────────────────────────────────────────────");
    if cgs.is_empty() {
        let _ = writeln!(out, "  (no scheduled pair matched)");
    }
    for g in &cgs {
        let _ = writeln!(out);
        render_group(ip, &mut out, g, "  ");
    }

    let _ = writeln!(out, "\n── also stored (no scheduled pair) ───────────────────────");
    if xgs.is_empty() {
        let _ = writeln!(out, "  (none — every stored constant belongs to a scheduled pair)");
    }
    for g in &xgs {
        let _ = writeln!(out);
        render_group(ip, &mut out, g, "  ");
    }

    let _ = writeln!(out, "\n── inductive apparatus ───────────────────────────────────");
    if let Some(n) = &app_note {
        let _ = writeln!(out, "  ({n})");
    }
    if ags.is_empty() && app_note.is_none() {
        let _ = writeln!(out, "  (nothing matched the filter)");
    }
    for g in &ags {
        let _ = writeln!(out);
        render_group(ip, &mut out, g, "  ");
    }

    let _ = writeln!(out, "\n── declines ──────────────────────────────────────────────");
    render_group(ip, &mut out, &dg, "  ");
    out
}
