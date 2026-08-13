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
//! redoing the reduction**. An unconditional certificate is then written into
//! [`Trace::cert`] — the trace *is* the memo's value, so this is the memoised
//! result carrying its own justification — and every later hit clones it. A
//! conditional certificate is deliberately re-derived: a copy parked in a
//! declaration-wide memo crosses no binder and can never discharge its
//! antecedents. The reduction itself is still performed exactly once.
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
    /// A reduction **inside an application spine**: either the head is the
    /// inner reduction with every argument unchanged, or the two endpoints
    /// have the same head and differ at the positions the inner reduction is
    /// about. The certificate is a fold of `app_cong` with reflexivity
    /// everywhere else.
    ///
    /// This exists for one reason. `reduce_rec` weak-head-normalises the major
    /// premise *inside itself* and then reports a single `Iota` step from the
    /// **unreduced** redex, so the backend's ι rule is handed a major premise
    /// that is not a constructor and can only decline — 486 gaps on
    /// `init-prelude`, and 3 066 with the sub-tree they feed. Splitting that
    /// into a congruence leg and an ι leg needs a node that can carry "the same
    /// spine, one argument reduced", and `Seq`/`One` cannot: a `One` is a whole-
    /// term rewrite and a `Seq` composes two of those.
    ///
    /// Nothing is checked here; [`crate::tc::TypeChecker::trace_cert`] verifies
    /// that the endpoints really are one spine differing only at the inner
    /// reduction's own endpoints before it builds anything.
    Cong(Rc<Trace<'t, C>>),
    /// A projection computation whose subject had to reduce before the
    /// constructor became visible. The inner trace is exactly that subject
    /// reduction; the outer node remains the single projection step from the
    /// original redex to its field.
    ///
    /// Keeping the trace here (rather than asking `proj_red` to normalise the
    /// subject again) preserves the memo's "reduce once, certify on demand"
    /// contract. [`crate::tc::TypeChecker::trace_cert`] checks that `sub.from`
    /// really is the redex's subject before handing its certificate to the
    /// backend.
    ProjRed(Rc<Trace<'t, C>>),
}

/// A reduction, where `None` means the empty one.
///
/// `None` is the identity for [`then`], and it is deliberately the same
/// convention the certificates themselves use: "no step was taken", so the
/// reduct is the input and reflexivity applies. It never means "not reducible"
/// — a reduction is always justified.
pub(crate) type TracePtr<'t, C> = Option<Rc<Trace<'t, C>>>;

/// A replayable structural equality recipe.
///
/// Unlike a certificate, this contains no theorem and therefore imports no
/// assumptions when retained in a declaration-wide cache. Reduction nodes hold
/// certificate-free copies of their traces, and replay certifies a fresh copy,
/// so even the trace's memo slot cannot park a conditional theorem here. Every
/// node names its exact endpoints; replay checks those names and the
/// corresponding expression shapes before asking a backend rule.
#[derive(Debug)]
pub(crate) enum EqRecipe<'t, C> {
    Refl(ExprPtr<'t>),
    /// Replay an already-recorded reduction, in its original direction or by
    /// symmetry. The trace itself always reads `trace.from ⟶ trace.to`.
    Reduction {
        from: ExprPtr<'t>,
        to: ExprPtr<'t>,
        trace: Rc<Trace<'t, C>>,
        reversed: bool,
    },
    App {
        from: ExprPtr<'t>,
        to: ExprPtr<'t>,
        fun: Rc<EqRecipe<'t, C>>,
        arg: Rc<EqRecipe<'t, C>>,
    },
    Seq {
        from: ExprPtr<'t>,
        middle: ExprPtr<'t>,
        to: ExprPtr<'t>,
        left: Rc<EqRecipe<'t, C>>,
        right: Rc<EqRecipe<'t, C>>,
    },
}

/// Copy a reduction trace as recipe structure, discarding every cached
/// certificate in the tree.
///
/// A [`Trace`] normally memoises its certificate in place. That is correct for
/// a reduct memo, whose certificate lives only as long as the declaration that
/// produced it, but not for a declaration-wide equality recipe: a conditional
/// certificate would carry the original call's local assumptions into a later
/// call. Recipes therefore retain these clean copies and certify another clean
/// copy on each replay.
pub(crate) fn recipe_trace<'t, C>(trace: &Rc<Trace<'t, C>>) -> Rc<Trace<'t, C>> {
    let node = match &trace.node {
        Node::One(rule) => Node::One(*rule),
        Node::Seq(left, right) => Node::Seq(recipe_trace(left), recipe_trace(right)),
        Node::Cong(sub) => Node::Cong(recipe_trace(sub)),
        Node::ProjRed(sub) => Node::ProjRed(recipe_trace(sub)),
    };
    Rc::new(Trace {
        from: trace.from,
        to: trace.to,
        node,
        cert: RefCell::new(None),
    })
}

/// The one-step reduction `from ⟶ to` by `rule`.
pub(crate) fn one<'t, C>(rule: Rule, from: ExprPtr<'t>, to: ExprPtr<'t>) -> TracePtr<'t, C> {
    Some(Rc::new(Trace { from, to, node: Node::One(rule), cert: RefCell::new(None) }))
}

/// Simulate the numeral bridge's link 2 having landed. Measurement only.
#[cfg(feature = "stepcount")]
fn nat_ruled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("NANODA_NAT_RULED").is_some())
}

/// Whether every step of a reduction is one of the four rules that essentially
/// always certify — `Beta`, `Zeta`, `Delta`, `Sort`.
///
/// A syntactic walk of the recorded trace: no backend call, no interpretation,
/// so it may be asked on the reduction hot path. It exists so a caller can
/// decide *whether to say more* about a reduction before anyone has paid to
/// certify it. See `TypeChecker::reduce_rec`.
pub(crate) fn fully_ruled<'t, C>(t: &TracePtr<'t, C>) -> bool {
    match t {
        None => true,
        Some(t) => match &t.node {
            // `Iota` and `ProjRed` are *asked*, which is the distinction this
            // enum draws — but being asked is not being answered, and both gap
            // on this corpus far more often than not. A caller uses this to
            // decide whether to expose a reduction to certification that was
            // never exposed before, so the bar is "will almost certainly
            // certify", not "has somewhere to ask".
            Node::One(Rule::Beta | Rule::Zeta | Rule::Delta | Rule::Sort) => true,
            // `NANODA_NAT_RULED` promotes the numeral admission to a rule
            // *for this test only*, which is exactly what the numeral bridge's
            // link 2 will do for real. It is how the caller downstream can be
            // shown to fire rather than being dead code waiting for a landing
            // that has not happened. Measurement only, and gated twice.
            #[cfg(feature = "stepcount")]
            Node::One(Rule::Admitted(Admit::NatRed)) if nat_ruled() => true,
            Node::One(_) => false,
            Node::Seq(l, r) => {
                fully_ruled(&Some(l.clone())) && fully_ruled(&Some(r.clone()))
            }
            Node::Cong(sub) => fully_ruled(&Some(sub.clone())),
            Node::ProjRed(sub) => fully_ruled(&Some(sub.clone())),
        },
    }
}

/// The reduction `from ⟶* to` that `sub` performs inside an application spine.
///
/// `None` when `sub` is empty, which is the right answer: an inner reduction
/// that took no step leaves the spine alone.
pub(crate) fn cong<'t, C>(
    from: ExprPtr<'t>,
    to: ExprPtr<'t>,
    sub: TracePtr<'t, C>,
) -> TracePtr<'t, C> {
    let sub = sub?;
    Some(Rc::new(Trace { from, to, node: Node::Cong(sub), cert: RefCell::new(None) }))
}

/// A projection reduction carrying the reduction of its subject.
///
/// `subject` must be non-empty: an already-direct constructor projection is
/// represented by the ordinary `One(Rule::ProjRed)` node.
pub(crate) fn proj_red<'t, C>(
    from: ExprPtr<'t>,
    to: ExprPtr<'t>,
    subject: TracePtr<'t, C>,
) -> TracePtr<'t, C> {
    let subject = subject?;
    Some(Rc::new(Trace {
        from,
        to,
        node: Node::ProjRed(subject),
        cert: RefCell::new(None),
    }))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::DagMarker;

    fn expr(n: usize) -> ExprPtr<'static> { ExprPtr::from(DagMarker::ExportFile, n) }

    fn fill(trace: &Rc<Trace<'static, u8>>) {
        trace.cert.replace(Some(7));
        match &trace.node {
            Node::One(_) => {}
            Node::Seq(left, right) => {
                fill(left);
                fill(right);
            }
            Node::Cong(sub) | Node::ProjRed(sub) => fill(sub),
        }
    }

    fn assert_empty(trace: &Rc<Trace<'static, u8>>) {
        assert!(trace.cert.borrow().is_none());
        match &trace.node {
            Node::One(_) => {}
            Node::Seq(left, right) => {
                assert_empty(left);
                assert_empty(right);
            }
            Node::Cong(sub) | Node::ProjRed(sub) => assert_empty(sub),
        }
    }

    #[test]
    fn recipe_trace_recursively_discards_certificates() {
        let inner = one(Rule::Delta, expr(1), expr(2));
        let congr = cong(expr(3), expr(4), inner);
        let subject = one(Rule::Iota, expr(5), expr(6));
        let projection = proj_red(expr(7), expr(8), subject);
        let original = then(congr, projection).expect("two non-empty traces compose");
        fill(&original);

        let clean = recipe_trace(&original);
        assert_eq!((clean.from, clean.to), (original.from, original.to));
        assert_empty(&clean);
        assert_eq!(*original.cert.borrow(), Some(7), "copying must not mutate the source memo");
    }
}
