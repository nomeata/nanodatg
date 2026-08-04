//! One export file, one verdict.
//!
//! # Interface
//!
//! [`check_file`] is what both `mini/src/main.rs` and `mini/tests/tutorial.rs`
//! call. It reproduces `Main.lean`'s `runKernel` in its strict (non-`--liberal`)
//! mode: declarations in file order, the first rejection ends the run.
//!
//! The three outcomes are kept apart because MINI-DESIGN.md §0's two axes
//! demand it: [`Verdict::Accepted`] and [`Verdict::Rejected`] are the
//! *acceptance* axis, which must agree with mini-lean and with nanoda, and
//! [`Verdict::Declined`] is mini refusing to look — mini-lean's `exit 2`.
//! Gaps are a fourth column on an accepted file, never a verdict.
//!
//! **A decline has two causes now, and they arrive at different moments.**
//! The parser's — a shape mini-lean's parser also refuses — happens in
//! [`convert::load`], before anything is checked. The other is a
//! *user-declared axiom*, which takes the file out of scope because its
//! inhabitation is not derivable in principle; that one happens **after** the
//! kernel has accepted the file, and the comment at the site says why the
//! order is load-bearing.
//!
//! [`Options::block`] adds the blocking mode of MINI-DESIGN.md §0.6. It is not
//! a verdict either: a blocked file was *accepted*, and the report says which
//! `(declaration, σ)` the evidence axis stopped at.

use crate::census::Census;
use crate::ledger::Ledger;
use crate::convert::{self, Facts};
use crate::env::Environment;
use crate::kernel;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Accepted { declars: usize },
    Rejected { name: String, msg: String },
    Declined { reason: String },
}

impl Verdict {
    pub fn is_accepted(&self) -> bool { matches!(self, Verdict::Accepted { .. }) }

    /// The one-word column the corpus tables use.
    pub fn tag(&self) -> &'static str {
        match self {
            Verdict::Accepted { .. } => "accept",
            Verdict::Rejected { .. } => "reject",
            Verdict::Declined { .. } => "decline",
        }
    }
}

/// How much mini is asked to do with the file.
///
/// Not `Copy` since [`Options::dump`] carries a filter; it is moved into the
/// worker thread once per file, which is the only place it travels.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Options {
    /// **Stop at the first blocker.** The interpretation pass ends at the
    /// first `(declaration, σ)` whose obligation it cannot discharge, and
    /// [`Outcome::blocker`] carries the report. Off, the pass runs to the end
    /// and the ledger counts every gap, as it always has.
    pub block: bool,
    /// **Dump the stored context** after the pass — [`crate::dump`]. Not a
    /// verdict and not a mode: the same run happens, and the store is read at
    /// the end. `None` is off; `Some(filter)` narrows it.
    pub dump: Option<crate::dump::Filter>,
}

pub struct Outcome {
    pub verdict: Verdict,
    pub facts: Facts,
    /// Which §6.2 clauses this file's declarations spend their nodes on —
    /// how the remaining threading work is sized.
    pub census: Census,
    /// One row per inductive with an exported recursor: the computed
    /// eliminator class against the recursor's own. See
    /// [`crate::zoneb::elim_audit`].
    pub elim_audit: Vec<String>,
    /// What `⟦·⟧` actually reached, per `(declaration, σ)`, attributed by
    /// cause. `None` when the file was declined or rejected: a gap ledger for
    /// a file mini did not accept would mix the two axes.
    pub ledger: Option<Ledger>,
    /// The stored-context dump, when [`Options::dump`] asked for one.
    ///
    /// A `String`, and rendered inside the worker, for the reason
    /// [`crate::blocker::Blocker`] is: the `Interp` is `Rc`-backed and does not
    /// cross the thread join, so the only place it can be read is where it
    /// lives.
    pub dump: Option<String>,
}

impl Outcome {
    /// The first blocker, when the run was asked to stop at one.
    pub fn blocker(&self) -> Option<&crate::blocker::Blocker> {
        self.ledger.as_ref()?.first_blocker.as_ref()
    }

    /// **The certification axis** — what this run left underived, as a verdict
    /// rather than a row. See [`crate::ledger::Uncertified`].
    ///
    /// Clean when there is no ledger, and that is not a papering-over: a
    /// rejected or declined file was never interpreted, so it owes nothing on
    /// this axis. The verdict about the *file* is the one that stands, and
    /// [`Verdict`] carries it.
    pub fn uncertified(&self) -> crate::ledger::Uncertified {
        self.ledger.as_ref().map(crate::ledger::Ledger::uncertified).unwrap_or_default()
    }
}

pub fn check_file(path: &Path) -> Outcome { check_file_with(path, Options::default()) }

pub fn check_file_with(path: &Path, opts: Options) -> Outcome {
    let loaded = match convert::load(path) {
        Ok(l) => l,
        Err(e) => {
            return Outcome {
                verdict: Verdict::Declined { reason: e.to_string() },
                facts: Facts::default(),
                census: Census::default(),
                elim_audit: Vec::new(),
                ledger: None,
                dump: None,
            }
        }
    };
    let census = Census::of(&loaded.decls);
    let mut env = Environment::empty();
    let mut accepted = 0usize;
    for decl in &loaded.decls {
        if let Err(msg) = kernel::add(&mut env, decl) {
            return Outcome {
                verdict: Verdict::Rejected { name: decl.name().to_string(), msg },
                facts: loaded.facts,
                census,
                elim_audit: Vec::new(),
                ledger: None,
                dump: None,
            }
        }
        accepted += 1;
    }
    // **A user-declared axiom takes the file out of scope.** Its inhabitation
    // is not derivable in principle, so a run that stops at the first missing
    // derivation would stop there for ever; `convert::is_standard_axiom` is
    // where the line is drawn and why.
    //
    // *After* the kernel pass, not before, and the position is load-bearing:
    // four `bad/tutorial` fixtures declare a helper axiom ahead of the
    // ill-typed declaration they are about, and declining at the parser would
    // have turned four rejections into declines — a weaker claim, made
    // silently, on the axis that is supposed to be exact.
    if let Some(n) = loaded.facts.nonstandard_axioms.first() {
        return Outcome {
            verdict: Verdict::Declined { reason: format!("non-standard axiom: {n}") },
            facts: loaded.facts,
            census,
            elim_audit: Vec::new(),
            ledger: None,
            dump: None,
        }
    }
    // The interpretation pass runs only on a file mini accepted: MINI-DESIGN
    // §0's two axes, kept apart.
    crate::blocker::arm(opts.block);
    let mut ip = crate::interp::Interp::new();
    // Names for the dump have to be switched on *before* the pass, because the
    // registry is written as each constant is stored. Not by arming: arming
    // also stops at the first blocker, which would dump one pair.
    ip.set_labels_on(opts.dump.is_some());
    let elim_audit = crate::zoneb::elim_audit(&env, &mut ip, &loaded.decls);
    let mut led = Ledger::run(&env, &loaded.decls, &loaded.schedule, &mut ip);
    crate::blocker::arm(false);
    let dump = opts
        .dump
        .as_ref()
        .map(|f| crate::dump::render(&mut ip, &loaded.decls, &loaded.schedule, f));
    // `Ledger::run` never learns the path; filling it here keeps the ledger a
    // function of the declarations alone.
    if let Some(b) = led.first_blocker.as_mut() {
        b.export = path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    }
    Outcome {
        verdict: Verdict::Accepted { declars: accepted },
        facts: loaded.facts,
        census,
        elim_audit,
        ledger: Some(led),
        dump,
    }
}

/// `check_file` on a thread with a large stack. `whnf` and `inferType` are
/// mutually recursive over the term structure with no depth limit, exactly as
/// in mini-lean, and `checker` does the same thing for the same reason.
pub fn check_file_deep(path: &Path) -> Outcome {
    check_file_deep_with(path, Options::default())
}

pub fn check_file_deep_with(path: &Path, opts: Options) -> Outcome {
    const STACK_SIZE: usize = 256 * 1024 * 1024;
    let p = path.to_path_buf();
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || check_file_with(&p, opts))
        .expect("spawn")
        .join()
        .expect("mini panicked")
}
