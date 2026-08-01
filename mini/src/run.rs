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
//! [`Verdict::Declined`] is the parser refusing to look — mini-lean's `exit 2`.
//! Gaps, when step (c) lands, are a fourth column on an accepted file, never a
//! verdict.

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

pub struct Outcome {
    pub verdict: Verdict,
    pub facts: Facts,
}

pub fn check_file(path: &Path) -> Outcome {
    let loaded = match convert::load(path) {
        Ok(l) => l,
        Err(e) => {
            return Outcome {
                verdict: Verdict::Declined { reason: e.to_string() },
                facts: Facts::default(),
            }
        }
    };
    let mut env = Environment::empty();
    let mut accepted = 0usize;
    for decl in &loaded.decls {
        if let Err(msg) = kernel::add(&mut env, decl) {
            return Outcome {
                verdict: Verdict::Rejected { name: decl.name().to_string(), msg },
                facts: loaded.facts,
            }
        }
        accepted += 1;
    }
    Outcome { verdict: Verdict::Accepted { declars: accepted }, facts: loaded.facts }
}

/// `check_file` on a thread with a large stack. `whnf` and `inferType` are
/// mutually recursive over the term structure with no depth limit, exactly as
/// in mini-lean, and `checker` does the same thing for the same reason.
pub fn check_file_deep(path: &Path) -> Outcome {
    const STACK_SIZE: usize = 256 * 1024 * 1024;
    let p = path.to_path_buf();
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || check_file(&p))
        .expect("spawn")
        .join()
        .expect("mini panicked")
}
