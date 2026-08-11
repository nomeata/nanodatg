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
//! [`crate::mini::run::check_file_with_interp`] is the one caller, and the pipeline it
//! runs is this module's shape: **parse, schedule, then one loop over the
//! declarations.** The historical `--naive` policy filters unused axioms before
//! entering the loop; the default policy dispatches every declaration. There
//! is no whole-file acceptance pass and no whole-file interpretation pass.
//! Each declaration is accepted by its selected engine and its evidence is
//! produced before the next declaration is looked at.
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
//! 1. **The unused-axiom drop is parse-only.** [`crate::mini::unused_axiom::classify`]
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
//!    model mentions `T`"), and `crate::mini::nested_splice`'s own `settled` check has
//!    always *required* that: a model at or after its declaration is
//!    `Missing::Later`. So recognition is a per-declaration step
//!    ([`crate::mini::nested_splice::Recogniser`]) and there is no deferral queue.
//!
//! 3. **A block's encoding is a per-declaration step; its rule theorems are
//!    not.** [`crate::mini::mutual_aux::encode`] reads each member's recursor, which
//!    `kernel::add` of that very block minted. Its rule theorems mention `Eq`,
//!    which the exporter routinely declares *after* the block — so their
//!    construction moves to the end-of-file append point where they were
//!    already being *emitted*. [`crate::mini::mutual_aux::Expander`] is the split.
//!
//! The fourth pass over the whole file, `crate::mini::zoneb::elim_audit`, **stays a
//! sweep, and not because it has to.** It was moved into the loop — run on each
//! inductive right after that declaration's own walk — and the `elim` rows over
//! all 154 arena files came out **identical, zero lines of diff**. So its
//! comment's claim that it "reads and does not mint" is now measured rather
//! than asserted, and the position is free.
//!
//! It is left outside the loop anyway, because it is an **oracle and not a
//! stage**: it produces a `--verbose` report, no certificate and no verdict,
//! and the loop is the place where a declaration is accepted and certified.
//! Putting a reader of the finished store inside the walk is the shape the
//! defect its own comment records had.
//!
//! # The two environments
//!
//! [`Pass::env`] is the selected checker's syntactic environment: mini-owned
//! declarations after `kernel::add`, and nanoda-owned declarations copied in
//! without a second check, each `Tᵢ` of a `mutual … end` block a real
//! inductive.
//! [`Pass::xenv`] is the **evidence pass's**: the same, with each encoded
//! block's constants replaced by the encoding's definitions. Before the fusion
//! the second was one `env.clone()` with the encodings written over it; there is
//! no finished environment to clone now, so it is grown alongside the first by
//! copying across exactly the names each accepted declaration
//! [`introduced`](self::introduced).
//!
//! The two hold the same names, plus exactly what the encodings added, and a
//! `debug_assert_eq!` in [`Pass::step`] checks that declaration by declaration
//! on every debug run — which is every `cargo test`, over the whole corpus and
//! every fixture. It is stated against a counter rather than switched off once
//! a block appears, so it is live on the ten mutual fixtures too. That is what
//! makes [`introduced`] a checked claim rather than a list somebody kept up to
//! date; `introduced_is_what_the_kernel_inserted` is the same claim against an
//! oracle read off the environment.

use std::collections::HashMap;

use crate::mini::env::{Declaration, Environment};
use crate::mini::expr::Name;
use crate::mini::interp::Interp;
use crate::mini::ledger::Ledger;
use crate::mini::route::{Driver, Pick};

/// What one declaration did to the run.
pub enum Step {
    /// Accepted, and — unless the evidence half is off or the armed blocker
    /// has already fired — certified. Keep going.
    Continue,
    /// Zone A rejected it: the file is ill-typed here. Everything before it has
    /// been certified, and [`Pass::prefix`] says how much.
    Rejected { name: String, msg: String },
    /// Zone A refused to look. Today the only cause is
    /// [`crate::mini::kernel::BUDGET_DECLINE`] — `reject` says the file is ill-typed
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
    /// **The accepted syntactic environment.** Grown by the engine selected
    /// for each declaration; this is what later mini-owned constructions see.
    pub env: Environment,
    /// **The evidence pass's environment.** See the module header.
    pub xenv: Environment,
    /// The declaration list the evidence pass walks — the file's, with each
    /// encoded block replaced in place and the rule theorems appended at the
    /// end. `crate::mini::dump` and the census read it.
    pub xdecls: Vec<Declaration>,
    /// The ledger the evidence half accumulates. Handed to the outcome **only**
    /// on an accepted file.
    pub led: Ledger,
    /// Declarations the selected engine accepted — the verdict line's count.
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
    nested: crate::mini::nested_splice::Recogniser,
    expander: crate::mini::mutual_aux::Expander,
    /// Names an encoding put in [`Pass::xenv`] that are not in [`Pass::env`] —
    /// the bookkeeping the environment invariant in [`Pass::step`] is stated
    /// against.
    xenv_extra: usize,
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
        //
        // **Measured: this loop changes nothing today.** Instrumented over the
        // arena's 154 files, not one pre-pass entry is out of order or carries
        // a duplicate — `checker::instantiations` already emits them normalised.
        // It is here to *establish* the precondition the walk has always been
        // read under rather than to fix a violation of it; the half that is
        // load-bearing is `add_sigmas`, which keeps it true of the entries the
        // nested keying and the block encodings add.
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
            nested: crate::mini::nested_splice::Recogniser::new(decls, &schedule),
            schedule,
            evidence,
            expander: crate::mini::mutual_aux::Expander::new(),
            xenv_extra: 0,
            nested_seen: 0,
            nested_models: 0,
        }
    }

    /// **The loop body.** Accept `d`, then certify it.
    pub(crate) fn step(&mut self, d: &Declaration, ip: &mut Interp, driver: &mut Driver) -> Step {
        let pick = match driver.accept(&mut self.env, d) {
            Ok(pick) => pick,
            Err(msg) => {
            // **A budget refusal is a decline.** See
            // [`crate::mini::kernel::BUDGET_DECLINE`]. Classified here because this
            // is the one place a kernel-pass error becomes a verdict.
                if msg.starts_with(crate::mini::kernel::BUDGET_DECLINE) {
                    return Step::Declined {
                        reason: format!("{} while checking {}", msg, d.name()),
                    }
                }
                if msg.starts_with("routing invariant:") {
                    return Step::Declined { reason: msg }
                }
                return Step::Rejected { name: d.name().to_string(), msg }
            }
        };
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
        // **The two environments hold the same names, plus what the encodings
        // added.** Exact and O(1), so it runs on every declaration of every
        // debug build — which is every `cargo test`, over the whole corpus and
        // every fixture. A name [`introduced`] forgets would otherwise surface
        // as an unresolved constant somewhere downstream, attributed to
        // whatever gap the walk reached first.
        debug_assert_eq!(
            self.xenv.consts.len(),
            self.env.consts.len() + self.xenv_extra,
            "the evidence pass's environment drifted from acceptance at {} — \
             `introduced` is missing an installed name",
            d.name()
        );

        // **Step 3 of the nested arc, and it is a *recognition* rather than a
        // substitution or an insertion.** A nested declaration's primitives
        // stay exactly where they are — the file's own theorems are checked by
        // the ι rules they carry — and its *model* is already in the file, put
        // there by the `modelgen` filter (`MODELGEN.md` §1), so all that is
        // built here is the side table saying which model constant carries
        // `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧`, and the σ those constants have to
        // be interpreted at. `crate::mini::nested_splice` says why the table
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
        // records its reason. `crate::mini::mutual_aux` is the whole of it, and
        // that module never names a `Term` or a `Thm`.
        let from = self.xdecls.len();
        {
            let Pass { env, xenv, expander, xdecls, schedule, xenv_extra, .. } = &mut *self;
            let before = xenv.consts.len();
            let new = expander.step(env, xenv, schedule, d);
            xdecls.extend_from_slice(new);
            // What the encoding put in the evidence pass's environment over and
            // above the block's own names — `Tag`, `Aux`, the packed motive and
            // their constructors and recursors. Counted so the invariant above
            // stays exact once a block has been encoded, rather than switching
            // itself off there.
            *xenv_extra += xenv.consts.len() - before;
        }
        self.walk(from, ip, driver, pick);
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
        self.walk(from, ip, driver, Pick::Mini);
    }

    /// The evidence walk over `xdecls[from..]`, unless the armed blocker has
    /// already stopped it.
    fn walk(&mut self, from: usize, ip: &mut Interp, driver: &mut Driver, pick: Pick) {
        let Pass { xdecls, xenv, schedule, led, blocked, .. } = self;
        for d in &xdecls[from..] {
            if *blocked {
                return
            }
            if driver.evidence(pick, xenv, schedule, ip, led, d) {
                *blocked = true;
            }
        }
    }

    /// The position the [`crate::mini::nested_splice::Recogniser`] sees this
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
    ///
    /// **Written here rather than by `nested_splice`**, and that is the
    /// module's black box (`ci/check-mutual-blackbox.sh`): a module that
    /// produces a table of `(Name, σ) -> Name` syntax for the evidence layer to
    /// consume may not name `crate::mini::interp` to hand it over. So it exposes the
    /// tables and this does the handing.
    ///
    /// Copied after every recognised declaration rather than once at the end,
    /// because `ledger::fill_declaration` reads `nested[T]` at `T`'s **own**
    /// position to learn which constants `T`'s model is responsible for. A
    /// nested declaration's entries never change after it has been keyed, so
    /// re-copying is idempotent on everything already there.
    fn install_nested_tables(&mut self, ip: &mut Interp) {
        if !self.nested.any() {
            return
        }
        let Some(app) = ip.ind_apparatus() else { return };
        app.model_of = self.nested.model_of.clone();
        app.model_iota = self.nested.model_iota.clone();
        app.nested = self.nested.nested.clone();
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

/// **Every name accepting `d` brought into `env`.**
///
/// Two sources and they are genuinely different:
///
/// * the names nothing owns — a definition's or an axiom's own, an inductive's
///   type formers, and `Quot`'s four, which `kernel::add_quot` mints and files
///   under **no owner** at all;
/// * everything `env` now attributes to one of those, read off `env.owners`.
///
/// The second half covers an inductive's constructors and its recursors, and it
/// is read rather than predicted for `nested_splice::export_recs`'s reason: a
/// nested declaration owns `T.rec_1` and `T.rec_2` as well as `T.rec`, and how
/// many recursors it owns is the specialisation's answer and not the
/// declaration's. **So the constructors are not listed here either**, and that
/// is deliberate: an explicit list of them was, and a mutation that deleted it
/// left every test green, because `add_block` files each constructor under its
/// type former and the scan below picks them all up. A branch that cannot fail
/// is worse than no branch.
///
/// The scan runs once per inductive — an axiom or a definition owns nothing —
/// and the whole function is checked on every debug run by [`Pass::step`]'s
/// `debug_assert_eq!` and directly by
/// [`tests::introduced_is_what_the_kernel_inserted`].
fn introduced(env: &Environment, d: &Declaration) -> Vec<Name> {
    let mut out: Vec<Name> = match d {
        Declaration::Axiom { name, .. } | Declaration::Def { name, .. } => return vec![*name],
        // **`add_quot` files no owners**, so its family is named here and
        // nowhere else. Deleting this arm is a mutation the unit test catches.
        Declaration::Quot => {
            let q = Name::simple("Quot");
            vec![q, Name::str(&q, "mk"), Name::str(&q, "lift"), Name::str(&q, "ind")]
        }
        Declaration::Inductive { name, .. } => vec![*name],
        Declaration::Mutual { types, .. } => types.iter().map(|t| t.name).collect(),
    };
    let owners: std::collections::HashSet<Name> = out.iter().copied().collect();
    out.extend(env.owners.iter().filter(|(_, o)| owners.contains(o)).map(|(n, _)| *n));
    out
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::mini::env::{DefKind, IndType};
    use crate::mini::expr::{forall, konst, sort, Level};

    /// The names `kernel::add` really inserted, read off the environment rather
    /// than predicted — the oracle [`introduced`] is compared against.
    fn really_added(before: &Environment, after: &Environment) -> Vec<Name> {
        let mut v: Vec<Name> =
            after.consts.keys().filter(|n| !before.consts.contains_key(n)).copied().collect();
        v.sort_by_key(|n| n.to_string());
        v
    }

    fn sorted(mut v: Vec<Name>) -> Vec<Name> {
        v.sort_by_key(|n| n.to_string());
        v.dedup();
        v
    }

    /// **[`introduced`] is exactly what `kernel::add` inserts**, for every
    /// declaration kind.
    ///
    /// The evidence pass's environment is grown by copying these names across
    /// from zone A's, so a name this function forgets is a constant the
    /// interpretation walk cannot resolve — which surfaces as a gap somewhere
    /// downstream rather than as a failure here. Hence the oracle: the set is
    /// *measured* off the environment, not asserted against a list.
    ///
    /// **Three constructors, and that is the point of the inductive case.** A
    /// declaration with one constructor cannot tell "copy the constructors"
    /// from "copy the first constructor", and two cannot tell either from an
    /// off-by-one; three separate all of them. `Colour.rec` and the owner index
    /// come along for free, which is the half that has to be read off
    /// `env.owners` rather than predicted.
    #[test]
    fn introduced_is_what_the_kernel_inserted() {
        let mut env = Environment::empty();

        // `axiom P : Prop`
        let p = Name::simple("P");
        let d = Declaration::Axiom { name: p, lparams: vec![], ty: sort(Level::zero()) };
        let before = env.clone();
        crate::mini::kernel::add(&mut env, &d).expect("axiom");
        assert_eq!(sorted(introduced(&env, &d)), really_added(&before, &env), "axiom");

        // `def idP : Prop → Prop := fun x => x`
        let arrow = forall(sort(Level::zero()), sort(Level::zero()));
        let d = Declaration::Def {
            name: Name::simple("idP"),
            lparams: vec![],
            ty: arrow,
            value: crate::mini::expr::lam(sort(Level::zero()), crate::mini::expr::bvar(0)),
            kind: DefKind::Def,
        };
        let before = env.clone();
        crate::mini::kernel::add(&mut env, &d).expect("def");
        assert_eq!(sorted(introduced(&env, &d)), really_added(&before, &env), "def");

        // `inductive Colour : Type | red | green | blue` — three atoms.
        let c = Name::simple("Colour");
        let ty = sort(Level::zero().succ());
        let d = Declaration::Inductive {
            name: c,
            lparams: vec![],
            num_params: 0,
            ty,
            ctors: ["red", "green", "blue"]
                .iter()
                .map(|s| (Name::str(&c, s), konst(c, vec![].into())))
                .collect(),
        };
        let before = env.clone();
        crate::mini::kernel::add(&mut env, &d).expect("inductive");
        let got = sorted(introduced(&env, &d));
        assert_eq!(got, really_added(&before, &env), "inductive");
        // …and it is not vacuous: five names, the recursor among them.
        assert_eq!(got.len(), 5, "type former, three constructors and the recursor: {got:?}");
        assert!(got.contains(&Name::str(&c, "rec")), "the recursor is owned, not named: {got:?}");

        // A `mutual … end` block of two, each with its own constructors.
        let (a, b) = (Name::simple("Ping"), Name::simple("Pong"));
        let d = Declaration::Mutual {
            lparams: vec![],
            num_params: 0,
            types: vec![
                IndType {
                    name: a,
                    ty: sort(Level::zero().succ()),
                    ctors: vec![
                        (Name::str(&a, "stop"), konst(a, vec![].into())),
                        (Name::str(&a, "go"), forall(konst(b, vec![].into()), konst(a, vec![].into()))),
                    ],
                },
                IndType {
                    name: b,
                    ty: sort(Level::zero().succ()),
                    ctors: vec![(
                        Name::str(&b, "back"),
                        forall(konst(a, vec![].into()), konst(b, vec![].into())),
                    )],
                },
            ],
        };
        let before = env.clone();
        crate::mini::kernel::add(&mut env, &d).expect("block");
        let got = sorted(introduced(&env, &d));
        assert_eq!(got, really_added(&before, &env), "mutual block");
        // Two type formers, three constructors, two recursors.
        assert_eq!(got.len(), 7, "{got:?}");

        // `Quot`, whose four constants the kernel mints itself.
        let before = env.clone();
        crate::mini::kernel::add(&mut env, &Declaration::Quot).expect("quot");
        assert_eq!(
            sorted(introduced(&env, &Declaration::Quot)),
            really_added(&before, &env),
            "quot"
        );
    }
}
