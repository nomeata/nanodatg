//! Why a derivation stopped: [`DerErr`], and the [`DResult`] it travels in.
//!
//! # Interface
//!
//! ```text
//! type DResult<T> = Result<T, DerErr>
//!
//! decline!("reason")                      -> DerErr    // the contract working
//! decline_at_caller!("reason")            -> DerErr    // …sited at the caller
//! assembly!("what", operands…)            -> DerErr    // a bug, always
//! DerErr::assembly(site, prim, operands)  -> DerErr    // what the macro builds
//! imported("crate::foo::bar", opt)        -> DResult<T> // an unmigrated `Option`
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
//!   The verdict is not only [`crate::prim`]'s. Most refusals in this crate are
//!   the code checking its **own** work — a theorem it just built not having
//!   the conclusion it intended, a formula it just decomposed not being the
//!   connective it named — and those are wrong in exactly the same way. The
//!   [`assembly!`](crate::assembly) macro is how a guard says so, and its
//!   header carries the rule for telling the two variants apart at a guard.
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
//!
//! # Folds, and where the blame lands
//!
//! A **combinator that loops collapses many call sites into one.**
//! `rules::inst_all` has ~2 000 callers in this crate and `rules::eq_trans` is
//! reached from every equational chain there is; a refusal sited at the
//! combinator's own line names the toolkit, which the reader already knew, and
//! not the call that was wrong. That is issue #99, and it is a
//! correctness-of-diagnosis defect rather than a cosmetic one: `nat`'s
//! `Chain::done` reported `rules.rs:108` — `eq_trans`'s guard — for *every*
//! chain in the module, and it cost a seat a build cycle.
//!
//! **`#[track_caller]` is the whole mechanism, and it chains.** This was
//! measured, because the opposite was believed for a while and it is the fact
//! the design turns on:
//!
//! ```text
//! shim direct                    -> the shim's caller
//! through 1 annotated frame      -> that frame's caller
//! through 2 annotated frames     -> the outermost annotated frame's caller
//! through an unannotated frame   -> the call site inside that frame
//! ```
//!
//! So blame travels out through *consecutively annotated* frames and stops at
//! the first one without the attribute. That makes the attribute the **knob**:
//! annotate the toolkit and leave the constructions plain, and a refusal lands
//! on the line of the construction that composed the call — which is the line
//! a reader wants — rather than on the toolkit's line or on `mini`'s.
//!
//! Two rules follow, and both are needed; the first without the second leaves
//! #99 exactly as it was.
//!
//! * **Annotate a function that is a thin composition over its arguments** —
//!   `syl`, `eq_trans`, `inst_all`, `hyp_mp`, `conj_proj`. For these "which
//!   internal line" is never the question. **Do not** annotate a construction
//!   with a derivation of its own — `define_by_membership`, `opair_fst`,
//!   `union_singleton` — where which internal step failed *is* the question.
//! * **An annotated function's own guards must be sited at the caller too.**
//!   [`decline!`] expands to `file!()`/`line!()` and cannot do that, so an
//!   annotated function uses [`decline_at_caller!`] instead. This is the half
//!   #99 actually needs: `rules.rs:108` is a `decline!`, not a shim failure,
//!   and no amount of annotation moves it on its own.
//!
//! ## Shape versus fit
//!
//! A fold also has to choose a *verdict*, and the choice is forced by what the
//! guard is comparing:
//!
//! * a refusal about **one argument's shape** — `syl` handed something that is
//!   not an implication — stays [`DerErr::Assembly`]. The operand *is* the
//!   diagnosis and a reason could add nothing to it.
//! * a refusal about **two arguments not fitting each other** — `ts` longer
//!   than `thm`'s quantifier prefix, `eqs` not the symbol's arity, two
//!   implications that do not compose — is a [`DerErr::Declined`]. Both
//!   operands look correct in isolation, so the reason is the whole content.
//!
//! Most of the toolkit already had this shape: destructure with `imp_parts`
//! (assembly on shape), then compare (decline on fit). [`crate::rules::inst_all`]
//! was the exception, because there the shape check and the fit check are the
//! *same* kernel call — and that is why `universe::least_universe_pairing`
//! handed the wrong theorem used to report `Thm::ax_inst was passed bad data`
//! while the very same mistake one quantifier later reported the function's own
//! documented precondition. The verdict must not depend on how far wrong the
//! caller was.
//!
//! ## What this replaces
//!
//! Two heavier designs were considered and are **not** needed. A site-taking
//! variant of each `prim` shim is unnecessary because the attribute already
//! carries the site. A `DerErr` carrying a link index is unnecessary *and*
//! would have broken the rule above this section: what identifies a failed link
//! is the argument, the argument is the caller's, and the caller's line is what
//! the attribute delivers. A combinator that still wants to name the link — the
//! shape `nat`'s `Chain` needs — should take a `&'static str` label per link
//! and pass it as the decline's reason, which stays inside the "reason is a
//! static label" rule and needs nothing here.

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
    /// **What refused.** A kernel primitive spelled as it appears in `kernel`
    /// — `"Thm::mp"`, `"Formula::as_imp"` — when [`crate::prim`] produced this;
    /// otherwise the name of the check inside `derived/` that found its own
    /// work mis-assembled (see the [`assembly!`](crate::assembly) macro), or
    /// the path of an unmigrated construction (see [`imported`]).
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

/// Adapt a construction from the part of `derived/` that still returns
/// `Option`.
///
/// The migration to [`DResult`] runs module by module, so a migrated module
/// keeps calling unmigrated ones. A `None` from one of those means *the
/// construction this caller is built on refused*, and its reason was thrown
/// away at the boundary — so it is reported as a [`DerErr::Assembly`] naming
/// that construction, with no operands, which is the honest amount of
/// information available.
///
/// It is deliberately **not** a decline. None of these refuse as part of a
/// contract that this crate's own callers are expected to trip, and one
/// arriving on a corpus run is a finding: it says which unmigrated
/// construction to migrate next.
///
/// `#[track_caller]` puts the *call site* in the report, so the site names the
/// line that asked rather than this line.
///
/// `crate::nat::glue::imported` is the same function, written before this one
/// existed and confined to `nat/`; it will be replaced by this when `nat/` is
/// next touched.
#[track_caller]
pub fn imported<T>(from: &'static str, r: Option<T>) -> DResult<T> {
    match r {
        Some(t) => Ok(t),
        None => Err(DerErr::assembly(Site::caller(), from, Vec::new())),
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

/// Refuse, naming the reason and siting it at the **caller**.
///
/// [`decline!`] with one difference: the site is [`Site::caller`] rather than
/// `file!()`/`line!()`. It is for the guards of a `#[track_caller]` function —
/// see *Folds, and where the blame lands* in this module's header. In a
/// looping combinator this is the half that fixes the diagnosis: annotating
/// `rules::eq_trans` moves its *shim* failures to the caller but leaves its own
/// guard reporting `rules.rs:108` for every chain in the crate, which is issue
/// #99 verbatim.
///
/// **Only use it in a function carrying `#[track_caller]`.** In a plain
/// function `Site::caller()` resolves to this macro's own line, so it degrades
/// to [`decline!`] with extra ceremony rather than to something wrong — but the
/// reader would be misled about where the reason is meant to land.
///
/// **And not inside a closure.** A closure does not carry the attribute, so
/// `foo().map_err(|_| decline_at_caller!("…"))` sites the decline at the
/// closure and silently undoes the whole thing. Write the `match` out.
#[macro_export]
macro_rules! decline_at_caller {
    ($reason:literal) => {
        $crate::err::DerErr::declined($crate::err::Site::caller(), $reason)
    };
}

/// Report a derivation that mis-assembled its **own** work, naming the check
/// and the values that failed it.
///
/// ```ignore
/// if *step.concl() != want {
///     return Err(assembly!(
///         "universe_union_closed: the surjection step",
///         Operand::thm("step", &step),
///         Operand::formula("want", &want),
///     ))
/// }
/// ```
///
/// This is the [`DerErr::Assembly`] counterpart of [`decline!`], for the checks
/// that [`crate::prim`] cannot express. A `prim::` shim covers the case where a
/// *kernel* primitive rejects its operands; a great many refusals in this crate
/// are instead the code comparing a theorem it just built, or a formula it just
/// decomposed, against the shape it intended — and those are bugs in exactly
/// the same way, so they must not read as declines.
///
/// # Which of the two a guard wants
///
/// The discriminant is **where the checked value came from**:
///
/// * the value traces back to a **parameter** — a caller-supplied theorem,
///   symbol, index or formula — so the guard is enforcing this function's
///   documented precondition. That is [`decline!`]: the contract working.
/// * the value was built **entirely from what this function derived itself**,
///   so a mismatch means the derivation above it is wrong. That is this macro.
///
/// A guard on a value that is a *function of* a parameter (a caller's theorem
/// instantiated at our own terms, say) is a decline: what it detects is the
/// caller having handed over the wrong theorem.
///
/// "Parameter" means a parameter of a **public** entry. A private helper's
/// caller is the module itself, so a guard on one of its arguments is the
/// module checking its own work and takes this macro — which is also why a
/// module's private readers can be `Assembly` throughout.
#[macro_export]
macro_rules! assembly {
    ($what:literal $(, $op:expr)* $(,)?) => {
        $crate::err::DerErr::assembly(
            $crate::err::Site::new(file!(), line!()),
            $what,
            vec![$($op),*],
        )
    };
}
