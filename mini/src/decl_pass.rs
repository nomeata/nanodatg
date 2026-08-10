//! **One declaration: checked, certified, and added to the environment.**
//!
//! # Interface
//!
//! ```text
//! Pass::new(&loaded, evidence)        parse-only state, before anything is checked
//! Pass::step(d, ip, driver) -> Step   accept `d`, then certify it
//! Pass::end(ip, driver)               the end-of-file append point
//! ```
//!
//! [`crate::run::check_file_with_interp`] is the one caller, and the pipeline it
//! runs is this module's shape: **parse, schedule, drop the unused axioms, then
//! one loop over the declarations.** There is no whole-file acceptance pass and
//! no whole-file interpretation pass; there is one pass, and each declaration
//! goes through zone A's kernel and the evidence walk before the next one is
//! looked at.
//!
//! # What that buys, and it is the only thing that changed
//!
//! The acceptance loop used to run to completion before the evidence pass
//! started, and it **stops at the first rejection** — so a file with one bad
//! declaration produced no certificate for any of the others. Measured on
//! `good/init-prelude.ndjson`: one ill-typed declaration two hundred-odd
//! declarations into a file of 2059, and the certified prefix was **zero**.
//! Fused, everything before the stop is certified and [`Prefix`] carries the
//! count.
//!
//! **Nothing else about the two axes moved.** A rejected or declined file still
//! gets `Outcome::ledger = None` — MINI-DESIGN.md §0's axis separation, and the
//! reason [`Prefix`] is a field of its own rather than a ledger attached to a
//! verdict that would then be reporting gap counts for a file mini did not
//! accept. The verdicts, their tags and the exit codes are what they were.
//!
//! # The three orderings this had to answer, and what each turned out to be
//!
//! 1. **The unused-axiom drop is parse-only.** [`crate::unused_axiom::classify`]
//!    takes a declaration list and no environment, so it moves ahead of the
//!    loop and a dropped axiom is simply never added — no kernel check, no
//!    interpretation. That loses one property: the *type* of an unused
//!    non-standard axiom is no longer checked, so a file declaring
//!    `axiom bad : (fun x => x)` and referring to it nowhere is no longer
//!    rejected for it. **The owner waived it explicitly.** It is still named on
//!    the verdict line and in `Ledger::ignored_axioms`, which is what `#64`'s
//!    lesson asks for.
//!
//!    The *used*-axiom decline has a different ordering property and it is
//!    **kept**: it must lose to any rejection, because four `bad/tutorial`
//!    fixtures (044, 047, 050, 054) declare a helper axiom ahead of the
//!    ill-typed declaration they are about, and declining first would turn four
//!    rejections into declines. So the decline is issued only when the loop ends
//!    unrejected — and the evidence half is switched **off** for such a file, so
//!    it costs exactly what it cost before: a kernel pass and no interpretation.
//!
//! 2. **A nested declaration's model is already before it.** The previous
//!    reading of this — that `modelgen` inserts the model *behind* the
//!    declaration, so recognition needs a completed environment — is wrong in
//!    both directions. `modelgen/Modelgen/Driver.lean` emits it before ("the
//!    model … generated **before** the declaration is added … nothing in the
//!    model mentions `T`"), and `crate::nested_splice`'s own `settled` check has
//!    always *required* that: a model at or after its declaration is
//!    `Missing::Later`. So recognition is a per-declaration step
//!    ([`crate::nested_splice::Recogniser`]) and there is no deferral queue.
//!
//! 3. **A block's encoding is a per-declaration step; its rule theorems are
//!    not.** [`crate::mutual_aux::encode`] reads each member's recursor, which
//!    `kernel::add` of that very block minted. Its rule theorems mention `Eq`,
//!    which the exporter routinely declares *after* the block — so their
//!    construction moves to the end-of-file append point where they were
//!    already being *emitted*. [`crate::mutual_aux::Expander`] is the split.
//!
//! The fourth pass over the whole file, `crate::zoneb::elim_audit`, stays a
//! sweep and stays where it was: it is an **oracle**, not a stage. It reads the
//! finished interpretation store and mints nothing (`run.rs` says what happened
//! when it did), so it has no per-declaration position to occupy — and running
//! it early is the defect its comment records.
//!
//! # The two environments
//!
//! [`Pass::env`] is **zone A's**: the file's declarations as `kernel::add`
//! accepted them, each `Tᵢ` of a `mutual … end` block a real inductive.
//! [`Pass::xenv`] is the **evidence pass's**: the same, with each encoded
//! block's constants replaced by the encoding's definitions. Before the fusion
//! the second was one `env.clone()` with the encodings written over it; there is
//! no finished environment to clone now, so it is grown alongside the first by
//! copying across exactly the names each accepted declaration
//! [`introduced`](self::introduced).
//!
//! The two are equal until a block is encoded, and `debug_assert!`s below check
//! it declaration by declaration on every debug run — which is every `cargo
//! test`, over the whole corpus. That is what makes [`introduced`] a checked
//! claim rather than a list somebody kept up to date.

use std::collections::HashMap;

use crate::env::{Declaration, Environment};
use crate::expr::Name;
use crate::interp::Interp;
use crate::ledger::Ledger;
use crate::route::Driver;

/// What one declaration did to the run.
pub enum Step {
    /// Accepted, and — unless the evidence half is off or the armed blocker
    /// has already fired — certified. Keep going.
    Continue,
    /// Zone A rejected it: the file is ill-typed here. Everything before it has
    /// been certified, and [`Pass::prefix`] says how much.
    Rejected { name: String, msg: String },
    /// Zone A refused to look. Today the only cause is
    /// [`crate::kernel::BUDGET_DECLINE`] — `reject` says the file is ill-typed
    /// and `decline` says mini does not handle it, and running out of recursion
    /// budget is the second.
    Declined { reason: String },
}

/// **The certified prefix** — what the evidence pass got through before the run
/// stopped.
///
/// A field of the outcome and not a ledger, deliberately: a ledger on a
/// rejected file would be reporting the certification axis about a file that
/// failed on the acceptance axis, which is the mixing MINI-DESIGN.md §0 exists
/// to prevent. These three numbers say *how far it got* and claim nothing about
/// what the file owes.
///
/// On an accepted file they agree with the ledger's own counters, and
/// `mini/tests/tutorial.rs` pins that they do.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Prefix {
    /// Declarations the evidence pass walked.
    pub declarations: usize,
    /// `(declaration, σ)` pairs it opened.
    pub pairs: usize,
    /// Pairs it produced a constant typing for — **the certificates**.
    pub const_ev_ok: usize,
}

impl Prefix {
    /// The one-line row `mini --verbose` prints. Printed on every verdict,
    /// because the whole point of the number is the verdict it used to be
    /// missing from.
    pub fn row(&self) -> String {
        format!(
            "prefix\tdeclarations={}\tpairs={}\tcertified={}",
            self.declarations, self.pairs, self.const_ev_ok
        )
    }
}

/// The state the per-declaration loop carries between declarations.
pub struct Pass {
    /// **Zone A's environment.** Grown by `kernel::add`, one declaration at a
    /// time; this is what the acceptance verdict is about.
    pub env: Environment,
    /// **The evidence pass's environment.** See the module header.
    pub xenv: Environment,
    /// The declaration list the evidence pass walks — the file's, with each
    /// encoded block replaced in place and the rule theorems appended at the
    /// end. `crate::dump` and the census read it.
    pub xdecls: Vec<Declaration>,
    /// The ledger the evidence half accumulates. Handed to the outcome **only**
    /// on an accepted file.
    pub led: Ledger,
    /// Declarations `kernel::add` accepted — the verdict line's count.
    pub accepted: usize,
    /// The armed blocker fired: the evidence half is over, the acceptance half
    /// goes on so that the count above and the verdict stay what they were.
    pub blocked: bool,
    /// The run's schedule: the pre-pass's, plus what the nested keying and the
    /// block encodings demand as the loop reaches them.
    pub schedule: HashMap<Name, Vec<Vec<u32>>>,
    /// Is the evidence half running at all? Off for a file that is going to
    /// decline on a used non-standard axiom — see the header's ordering (1).
    evidence: bool,
    nested: crate::nested_splice::Recogniser,
    expander: crate::mutual_aux::Expander,
    pub nested_seen: usize,
    pub nested_models: usize,
}

impl Pass {
    pub fn new(
        decls: &[Declaration],
        schedule: &HashMap<Name, Vec<Vec<u32>>>,
        evidence: bool,
    ) -> Pass {
        // **Normalised once, before anything reads it.** The whole-file passes
        // sorted and deduplicated the *entire* schedule at their end, including
        // the pre-pass's own untouched entries, and the walk then read a sorted
        // one. A per-declaration walk reads it as it goes, so the normalisation
        // has to be done up front and then maintained at every write
        // (`nested_splice::add_sigmas`).
        let mut schedule = schedule.clone();
        for v in schedule.values_mut() {
            v.sort();
            v.dedup();
        }
        Pass {
            env: Environment::empty(),
            xenv: Environment::empty(),
            xdecls: Vec::with_capacity(decls.len()),
            led: Ledger::default(),
            accepted: 0,
            blocked: false,
            nested: crate::nested_splice::Recogniser::new(decls, &schedule),
            schedule,
            evidence,
            expander: crate::mutual_aux::Expander::new(),
            nested_seen: 0,
            nested_models: 0,
        }
    }

    /// **The loop body.** Accept `d`, then certify it.
    pub(crate) fn step(&mut self, d: &Declaration, ip: &mut Interp, driver: &mut Driver) -> Step {
        if let Err(msg) = crate::kernel::add(&mut self.env, d) {
            // **A budget refusal is a decline.** See
            // [`crate::kernel::BUDGET_DECLINE`]. Classified here because this
            // is the one place a kernel-pass error becomes a verdict.
            if msg.starts_with(crate::kernel::BUDGET_DECLINE) {
                return Step::Declined { reason: format!("{} while checking {}", msg, d.name()) }
            }
            return Step::Rejected { name: d.name().to_string(), msg }
        }
        self.accepted += 1;
        if !self.evidence {
            return Step::Continue
        }
        // Zone A's constants, copied across to the evidence pass's environment
        // before anything writes an encoding over them.
        for n in introduced(&self.env, d) {
            if let Some(v) = self.env.consts.get(&n) {
                self.xenv.consts.insert(n, v.clone());
            }
            if let Some(o) = self.env.owners.get(&n) {
                self.xenv.owners.insert(n, *o);
            }
        }
        debug_assert!(
            self.expander.encoded > 0 || self.xenv.consts.len() == self.env.consts.len(),
            "the evidence pass's environment drifted from zone A's at {} — \
             `introduced` is missing a name `kernel::add` inserted",
            d.name()
        );

        // **Step 3 of the nested arc, and it is a *recognition* rather than a
        // substitution or an insertion.** A nested declaration's primitives
        // stay exactly where they are — the file's own theorems are checked by
        // the ι rules they carry — and its *model* is already in the file, put
        // there by the `modelgen` filter (`MODELGEN.md` §1), so all that is
        // built here is the side table saying which model constant carries
        // `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧`, and the σ those constants have to
        // be interpreted at. `mini/src/nested_splice.rs` says why the table
        // cannot be a name rule.
        //
        // Before the expansion and not after: the model contains a
        // `mutual … end` block of its own, and the σ this propagates onto its
        // members have to be in the schedule the expansion reads.
        let i = self.file_index();
        {
            let Pass { env, nested, schedule, .. } = &mut *self;
            nested.observe(env, i, d);
            nested.step(env, i, d, schedule);
        }
        self.install_nested_tables(ip);

        // **Step 6 of the mutual arc, and it is a substitution rather than an
        // install.** Every `mutual … end` block mini can encode is replaced,
        // right here, by an enumeration, one indexed inductive and a list of
        // ordinary definitions over it — under the block's *own* names. The
        // walk below then interprets those, and `⟦T.{σ}⟧`, `⟦T.ctor.{σ}⟧` and
        // `⟦T.rec.{σ}⟧` land in the store at exactly the keys every later use
        // site reads. There is nothing to copy afterwards.
        //
        // A block the encoder declines stays as it was and `fill_declaration`
        // records its reason. `mini/src/mutual_aux.rs` is the whole of it, and
        // that module never names a `Term` or a `Thm`.
        let from = self.xdecls.len();
        {
            let Pass { env, xenv, expander, xdecls, schedule, .. } = &mut *self;
            let new = expander.step(env, xenv, schedule, d);
            xdecls.extend_from_slice(new);
        }
        self.walk(from, ip, driver);
        Step::Continue
    }

    /// **The end-of-file append point.** Every encoded block's recursor rules,
    /// stated now that the file's `Eq` is in scope, and walked like any other
    /// declaration.
    ///
    /// Reached only when the loop ended without a rejection: a rule theorem for
    /// a block in a file mini did not accept is a statement about a file that
    /// does not typecheck.
    pub(crate) fn end(&mut self, ip: &mut Interp, driver: &mut Driver) {
        if !self.evidence {
            return
        }
        let from = self.xdecls.len();
        {
            let Pass { env, xenv, expander, xdecls, schedule, .. } = &mut *self;
            let new = expander.append_rules(env, xenv, schedule);
            xdecls.extend_from_slice(new);
        }
        self.walk(from, ip, driver);
    }

    /// The evidence walk over `xdecls[from..]`, unless the armed blocker has
    /// already stopped it.
    fn walk(&mut self, from: usize, ip: &mut Interp, driver: &mut Driver) {
        let Pass { xdecls, xenv, schedule, led, blocked, .. } = self;
        for d in &xdecls[from..] {
            if *blocked {
                return
            }
            if driver.step(xenv, schedule, ip, led, d) {
                *blocked = true;
            }
        }
    }

    /// The position the [`crate::nested_splice::Recogniser`] sees this
    /// declaration at.
    ///
    /// **The file's own index, not `xdecls`'s.** `settled` compares a model
    /// constant's position against the modelled declaration's, and both are
    /// positions in the *file*; an expansion that replaced one earlier block by
    /// eleven declarations would otherwise push every later declaration past
    /// its own model. It is the count of declarations accepted so far minus
    /// one, which is the file index because `accepted` counts file
    /// declarations.
    fn file_index(&self) -> usize { self.accepted - 1 }

    /// Put the nested keying on the interpretation apparatus.
    ///
    /// The tables go on the apparatus, which means **building** it — so only
    /// when there is something to put there. A file with no nested declaration
    /// must not acquire an apparatus it would otherwise never have had.
    fn install_nested_tables(&mut self, ip: &mut Interp) {
        if !self.nested.any() {
            return
        }
        let Some(app) = ip.ind_apparatus() else { return };
        // Written before the declaration is walked, which is what
        // `ledger::fill_declaration` needs: it reads `nested[T]` to learn which
        // constants `T`'s model is responsible for, at `T`'s own position.
        self.nested.publish(app);
        self.nested_seen = self.nested.seen;
        self.nested_models = self.nested.modelled;
    }

    /// The certified prefix, at whatever point the run stopped.
    pub fn prefix(&self) -> Prefix {
        Prefix {
            declarations: self.led.declarations,
            pairs: self.led.pairs,
            const_ev_ok: self.led.const_ev_ok,
        }
    }

    pub fn mutual_blocks(&self) -> usize { self.expander.blocks }
    pub fn mutual_encoded(&self) -> usize { self.expander.encoded }
    pub fn mutual_rules(&self) -> usize { self.expander.rules }
}

/// **Every name `kernel::add(env, d)` brought into `env`.**
///
/// The declaration's own names — the constant, or an inductive's type formers
/// and constructors, or `Quot`'s four — and then everything `env` now says one
/// of those owns.
///
/// The second half is **read off `env.owners` rather than predicted**, for
/// `nested_splice::export_recs`'s reason: a nested declaration owns `T.rec_1`
/// and `T.rec_2` as well as `T.rec`, and how many recursors it owns is the
/// specialisation's answer, not the declaration's. The scan is once per
/// inductive — an axiom or a definition owns nothing — and it is checked on
/// every debug run by [`Pass::step`]'s `debug_assert!`.
fn introduced(env: &Environment, d: &Declaration) -> Vec<Name> {
    let mut out: Vec<Name> = match d {
        Declaration::Axiom { name, .. } => return vec![*name],
        Declaration::Def { name, .. } => return vec![*name],
        Declaration::Quot => {
            let q = Name::simple("Quot");
            vec![q, Name::str(&q, "mk"), Name::str(&q, "lift"), Name::str(&q, "ind")]
        }
        Declaration::Inductive { name, ctors, .. } => {
            let mut v = vec![*name];
            v.extend(ctors.iter().map(|(c, _)| *c));
            v
        }
        Declaration::Mutual { types, .. } => {
            let mut v = Vec::new();
            for t in types {
                v.push(t.name);
                v.extend(t.ctors.iter().map(|(c, _)| *c));
            }
            v
        }
    };
    let owners: std::collections::HashSet<Name> = out.iter().copied().collect();
    out.extend(env.owners.iter().filter(|(_, o)| owners.contains(o)).map(|(n, _)| *n));
    out
}
