//! Why a derivation stopped: [`DerErr`], and the [`DResult`] it travels in.
//!
//! # Interface
//!
//! ```text
//! type DResult<T> = Result<T, DerErr>
//!
//! decline!("reason")                      -> DerErr    // the contract working
//! DerErr::assembly(site, prim, operands)  -> DerErr    // a bug, always
//!
//! e.is_decline() / e.is_assembly()        -> bool
//! e.site() -> Site                        // file:line that produced it
//! e.reason() -> &str                      // the short label
//! format!("{e}")                          // one line, plus operands if any
//! ```
//!
//! # The two variants, and why the distinction is the point
//!
//! `derived/` used to return `Option<T>`, and a `None` said nothing: a
//! deliberate refusal and a mis-assembled derivation were the same value, and
//! both arrived at the caller stripped of the sub-result that actually stopped
//! them. Two failures live in this crate and they want opposite reactions:
//!
//! * **[`DerErr::Declined`]** — *the contract working*. `bnd_carrier` refusing
//!   a recursive carrier, a fail-closed guard at a function-typed field, a
//!   lookup that legitimately has no answer. These happen constantly on a
//!   normal corpus run. They are not bugs, they must not panic, and they must
//!   not read like bugs in a log.
//! * **[`DerErr::Assembly`]** — *a bug, always*. A kernel primitive was handed
//!   data it cannot accept: [`kernel::Thm::mp`] on a mismatched antecedent,
//!   an instantiation of something that is not a `∀`, a generalisation over a
//!   variable that is free in a hypothesis. The derivation that produced the
//!   operands is wrong. An `Assembly` reaching a corpus run is a finding.
//!
//! An `Assembly` therefore carries the **operands** — the actual formulas and
//! theorems the primitive rejected — because "`mp` failed" without them is the
//! `None` this module exists to replace. A `Declined` deliberately carries no
//! operands: it is on the hot path, and its site plus its one-line reason is
//! the whole story.
//!
//! # Rendering
//!
//! `kernel`'s `TermData` is `pub(crate)`, so this crate cannot walk a term and
//! has no way to pretty-print one. Operands render with `{:?}`, which is
//! complete and ugly. A consumer that has a symbol table — `mini::blocker`'s
//! `show_formula` does — should render [`DerErr::operands`] itself.
//!
//! # `?` composes; the first reason wins
//!
//! `DResult` is an ordinary `Result`, so `?` propagates a `DerErr` unchanged
//! through every intermediate frame. That is §0.4's rule — *a result carries
//! the reason of the sub-result that stopped it* — obtained from the type
//! rather than from a discipline. Nothing re-labels an error on the way out;
//! if a caller wants to say more, it declines with its own reason instead of
//! overwriting the one it was given.

use core::fmt;
use kernel::{Formula, FreeVar, Term, Thm};

/// A source position inside this crate: the `file!()`/`line!()` of the thing
/// that refused.
///
/// Not [`core::panic::Location`], which has no public constructor, so the
/// `decline!` macro could not build one. [`Site::caller`] converts from a
/// `Location` for the `#[track_caller]` shims in [`crate::prim`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Site {
    file: &'static str,
    line: u32,
}

impl Site {
    /// The site of a literal `file!()`/`line!()` pair. Used by `decline!`.
    pub const fn new(file: &'static str, line: u32) -> Site { Site { file, line } }

    /// The *caller's* site. Only meaningful inside a `#[track_caller]` function.
    #[track_caller]
    pub fn caller() -> Site {
        let l = core::panic::Location::caller();
        Site { file: l.file(), line: l.line() }
    }

    pub fn file(self) -> &'static str { self.file }
    pub fn line(self) -> u32 { self.line }
}

impl fmt::Display for Site {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.file, self.line)
    }
}

/// One argument a kernel primitive rejected, under the name the primitive's
/// own signature gives it.
#[derive(Clone, Debug)]
pub struct Operand {
    /// The parameter name — `imp`, `arg`, `phi`, `x`, …
    pub label: &'static str,
    pub value: Shown,
}

/// A value an [`Operand`] can hold. One variant per kernel type that appears in
/// a primitive's signature.
#[derive(Clone, Debug)]
pub enum Shown {
    Formula(Formula),
    Term(Term),
    Thm(Thm),
    Var(FreeVar),
}

impl Operand {
    pub fn formula(label: &'static str, x: &Formula) -> Operand {
        Operand { label, value: Shown::Formula(x.clone()) }
    }
    pub fn term(label: &'static str, x: &Term) -> Operand {
        Operand { label, value: Shown::Term(x.clone()) }
    }
    pub fn thm(label: &'static str, x: &Thm) -> Operand {
        Operand { label, value: Shown::Thm(x.clone()) }
    }
    pub fn var(label: &'static str, x: FreeVar) -> Operand {
        Operand { label, value: Shown::Var(x) }
    }
}

/// The operands of a rejected primitive call.
///
/// Boxed inside [`DerErr`] so that the *decline* path — the common one — stays
/// a 40-byte value with no allocation.
#[derive(Clone, Debug)]
pub struct Assembly {
    pub site: Site,
    /// The primitive that refused, spelled as it appears in `kernel` —
    /// `"Thm::mp"`, `"Formula::as_imp"`, ….
    pub primitive: &'static str,
    pub operands: Vec<Operand>,
}

/// Why a derivation stopped.
#[derive(Clone, Debug)]
pub enum DerErr {
    /// The contract working: a construction refused input it does not handle.
    /// `reason` is a short static label, and the site pins which refusal it was.
    Declined { site: Site, reason: &'static str },
    /// A kernel primitive was handed data it cannot accept. Always a bug in the
    /// derivation that built the operands.
    Assembly(Box<Assembly>),
}

/// The result type of everything in `derived/` that can fail.
pub type DResult<T> = Result<T, DerErr>;

impl DerErr {
    /// A refusal. Prefer the [`decline!`](crate::decline) macro, which fills in
    /// the site.
    pub fn declined(site: Site, reason: &'static str) -> DerErr {
        DerErr::Declined { site, reason }
    }

    /// A primitive rejected its operands.
    pub fn assembly(site: Site, primitive: &'static str, operands: Vec<Operand>) -> DerErr {
        DerErr::Assembly(Box::new(Assembly { site, primitive, operands }))
    }

    /// True for the contract working — a decline is normal traffic.
    pub fn is_decline(&self) -> bool { matches!(self, DerErr::Declined { .. }) }

    /// True for a bug. An `Assembly` on a corpus run is a finding, not noise.
    pub fn is_assembly(&self) -> bool { matches!(self, DerErr::Assembly(_)) }

    /// Where the failure was produced.
    pub fn site(&self) -> Site {
        match self {
            DerErr::Declined { site, .. } => *site,
            DerErr::Assembly(a) => a.site,
        }
    }

    /// The short label: a decline's reason, or the primitive that refused.
    pub fn reason(&self) -> &'static str {
        match self {
            DerErr::Declined { reason, .. } => reason,
            DerErr::Assembly(a) => a.primitive,
        }
    }

    /// The rejected operands — empty for a decline.
    pub fn operands(&self) -> &[Operand] {
        match self {
            DerErr::Declined { .. } => &[],
            DerErr::Assembly(a) => &a.operands,
        }
    }
}

impl fmt::Display for DerErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DerErr::Declined { site, reason } => write!(f, "{site}: declined: {reason}"),
            DerErr::Assembly(a) => {
                write!(f, "{}: {} was passed bad data", a.site, a.primitive)?;
                for op in &a.operands {
                    match &op.value {
                        Shown::Formula(x) => write!(f, "\n    {} = {x:?}", op.label)?,
                        Shown::Term(x) => write!(f, "\n    {} = {x:?}", op.label)?,
                        Shown::Thm(x) => write!(f, "\n    {} = {x:?}", op.label)?,
                        Shown::Var(x) => write!(f, "\n    {} = {x:?}", op.label)?,
                    }
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for DerErr {}

/// Refuse, naming the reason and the site.
///
/// ```ignore
/// if i >= hs.len() {
///     return Err(decline!("projection index past the end of the conjunction"))
/// }
/// ```
///
/// The reason must be a string literal: it is a *label*, not a message, and
/// keeping it static is what makes the set of refusals in this crate a finite,
/// greppable list rather than a pile of formatted strings.
#[macro_export]
macro_rules! decline {
    ($reason:literal) => {
        $crate::err::DerErr::declined($crate::err::Site::new(file!(), line!()), $reason)
    };
}
