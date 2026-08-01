//! Memoised weak-head reducts, and the evidence that justifies them.
//!
//! # Interface
//!
//! * [`Rule`] — which rule a reduction step applied. One variant per backend
//!   method `whnf` can reach, plus [`Rule::Admitted`] for the ones the backend
//!   has no method for.
//! * [`Trace`] / [`TracePtr`] — a reduction, as the steps it took together with
//!   its two endpoints and a slot for its certificate. `None` is the empty
//!   reduction, i.e. "no step was taken".
//! * [`one`], [`then`] — a one-step reduction, and two reductions in sequence.
//! * [`Reduct`] — the value type of the two reduct memos in
//!   [`crate::util::TcCache`]: the answer and the trace that produced it.
//!
//! # Why the memo stores the evidence and not only the answer
//!
//! `whnf` is called both for its answer and for its evidence, and the answer is
//! memoised the first time. When the memo held only an `ExprPtr`, a call that
//! wanted evidence and found a reduct left behind by a call that did not had
//! nothing to hand back, and the reduction had to be admitted (`Admit::Whnf`)
//! or — worse for performance — *re-run*. Re-running a memoised computation on
//! a cache hit gives back exactly the work the memo exists to avoid, so the
//! evidence lives in the memo's value type instead: memoise a result, memoise
//! why.
//!
//! # Why a trace rather than the certificate itself
//!
//! Because the two are not the same cost. Recording a step is a few words and
//! no backend call; building a certificate interprets both endpoints into
//! first-order terms and derives a real theorem. Most `whnf` calls come from
//! type inference, which wants the reduct and nothing else, and asking the
//! backend there would both waste that work and tally gaps in the coverage
//! report against reduction steps that no definitional-equality conclusion
//! rests on — the report would then measure something other than what it says.
//!
//! So the reduction always records what it did, at trace prices, and the first
//! caller that actually wants a certificate turns the trace into one **without
//! redoing the reduction**. The certificate is then written into [`Trace::cert`]
//! — the trace *is* the memo's value, so this is the memoised result carrying
//! its own justification — and every later hit clones it. Each reduct is
//! reduced once and derived at most once.
//!
//! A trace is also strictly more faithful than a re-run. It is *the* chain of
//! steps that produced the memoised reduct, so the certificate it yields is
//! about that reduct by construction — there is no "the re-run landed somewhere
//! else" case to fall back from. (The two reduct memos are keyed by input
//! alone, and `whnf_no_unfolding`'s cheap-projection variant does not reduce as
//! far as its ordinary one, so a re-run genuinely could land elsewhere.)
//!
//! # Sharing, and why it is load-bearing
//!
//! A reduction that takes `n` steps memoises an entry for each of its suffixes,
//! so a flat list of steps per entry would be quadratic. A [`Trace`] is an
//! `Rc`-shared tree instead: [`then`] is O(1), and the sub-reduction hanging off
//! a memo hit is *the same node* the hit came from.
//!
//! That identity is what keeps a certificate for a long reduction from being
//! rebuilt step by step every time it is asked for. Building it out of the
//! sub-reduction's own certificate composes one `trans`; flattening the same
//! reduction and folding over the steps composes `n`, and — because each `trans`
//! over an admitted premise is itself a reported gap — turns one gap into `n`.
//! Measured on `init-prelude`, flattening cost 971 extra
//! `trans over an admitted premise` gaps. The tree is not an optimisation.

use crate::certify::Admit;
use crate::util::ExprPtr;
use std::cell::RefCell;
use std::rc::Rc;

/// Which rule a reduction step applied.
///
/// The rules are named, not pre-applied: the backend is asked only when a
/// certificate is actually wanted, and asking it is [`crate::tc`]'s job because
/// that is where the certifier lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rule {
    /// One or more beta contractions of a lambda spine, taken together.
    Beta,
    /// Zeta: a `let` body instantiated with its value.
    Zeta,
    /// Delta: a defined constant unfolded, applied to the same spine.
    Delta,
    /// A `Sort` whose level simplified to a different one.
    Sort,
    /// Iota: a recursor applied to a constructor application.
    Iota,
    /// A projection of a constructor application, reduced to the field.
    ///
    /// A rule rather than [`Rule::Admitted`] since it acquired a backend method
    /// ([`crate::certify::Certifier::proj_red`]). The distinction the enum draws
    /// is "there is somewhere to ask" versus "there is not"; a step whose gap is
    /// reported *by the rule that was asked* belongs on this side of it.
    ProjRed,
    /// A step the backend has no rule for, tagged with the reason.
    Admitted(Admit),
}

/// One reduction `from ⟶* to`: how it was done, and its certificate once
/// something has asked for one.
///
/// Both endpoints are recorded because every backend rule concludes about two
/// *named* terms and checks its result against them. A trace that knew only
/// where it started could not be handed to one, and a certificate recovered
/// from a cache has to be checked against the equation the caller is asking
/// about — which is what having `from` and `to` on the node makes possible.
#[derive(Debug)]
pub(crate) struct Trace<'t, C> {
    pub(crate) from: ExprPtr<'t>,
    pub(crate) to: ExprPtr<'t>,
    pub(crate) node: Node<'t, C>,
    /// The certificate for `from ≡ to`. Filled in by
    /// `TypeChecker::certify_reduct` when this trace is a memo entry's own
    /// reduction, so that the entry answers the next caller from store rather
    /// than by deriving again.
    pub(crate) cert: RefCell<Option<C>>,
}

/// How a [`Trace`] was put together.
#[derive(Debug)]
pub(crate) enum Node<'t, C> {
    /// A single rule application, between the trace's two endpoints.
    One(Rule),
    /// Two reductions in sequence. The left one's `to` is the right one's
    /// `from`; [`then`] is the only constructor and establishes that.
    Seq(Rc<Trace<'t, C>>, Rc<Trace<'t, C>>),
}

/// A reduction, where `None` means the empty one.
///
/// `None` is the identity for [`then`], and it is deliberately the same
/// convention the certificates themselves use: "no step was taken", so the
/// reduct is the input and reflexivity applies. It never means "not reducible"
/// — a reduction is always justified.
pub(crate) type TracePtr<'t, C> = Option<Rc<Trace<'t, C>>>;

/// The one-step reduction `from ⟶ to` by `rule`.
pub(crate) fn one<'t, C>(rule: Rule, from: ExprPtr<'t>, to: ExprPtr<'t>) -> TracePtr<'t, C> {
    Some(Rc::new(Trace { from, to, node: Node::One(rule), cert: RefCell::new(None) }))
}

/// Two reductions in sequence, in O(1) and without copying either.
///
/// The endpoints of the result are the outer two, so a composite always knows
/// what it is a reduction *of*. Nothing here checks that the two meet in the
/// middle; `TypeChecker::trace_cert` does, before it builds anything.
pub(crate) fn then<'t, C>(a: TracePtr<'t, C>, b: TracePtr<'t, C>) -> TracePtr<'t, C> {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(x), Some(y)) => {
            let (from, to) = (x.from, y.to);
            Some(Rc::new(Trace { from, to, node: Node::Seq(x, y), cert: RefCell::new(None) }))
        }
    }
}

/// A memoised weak-head reduct together with the reduction that produced it.
///
/// There is no separate certificate field: the certificate belongs to the
/// reduction, and lives in [`Trace::cert`] at its root. Keeping it there rather
/// than beside it is what makes the two impossible to get out of step — the
/// failure mode a parallel `(input, reduct) -> certificate` table had.
#[derive(Debug)]
pub(crate) struct Reduct<'t, C> {
    pub(crate) reduct: ExprPtr<'t>,
    pub(crate) trace: TracePtr<'t, C>,
}
