//! The accessibility apparatus, assembled once.
//!
//! # Interface
//!
//! [`Acc::new`] builds every symbol and derives every theorem from the axioms
//! up; [`Acc::with_apply`] does the same over a caller-supplied
//! [`crate::funcs::Apply`], so that a client already holding one gets an `acc`
//! whose ordered pairs are *the same* ordered pairs. The fields are A0–A2 plus
//! the two positive non-vacuity witnesses, so a caller reads them off the
//! struct and never calls the functions in the sibling files directly. A3
//! ([`crate::acc::acc_rect`]) and the negative witnesses are methods — see
//! below.
//!
//! # What it is built over, and what it is not
//!
//! An `Acc` needs exactly two things: a pairing operation, because the relation
//! `R` is a set of Kuratowski pairs, and an empty set, because
//! [`crate::funcs::separation_full`] consumes one. It needs **no function
//! space, no application, no universe and no bound** — contrast
//! [`crate::wtype::Wtype`], which carries a whole [`crate::sums::Sums`] and
//! whose central theorems are conditional on `closed(A,B,u)`.
//!
//! So the field list here is [`crate::funcs::Sets`] plus `∅`, not an `Apply`.
//! [`Acc::with_apply`] exists because most clients *will* have an `Apply` (the
//! recursor `rec_acc` and the §5.3 translation both need application), and
//! building a second pairing operation would mint a second `⟨·,·⟩` under which
//! none of these theorems compose.
//!
//! # Why `no_loops`, `no_two_cycle` and `rect` are methods, not fields
//!
//! All three mint a fresh symbol per call — [`crate::acc::acc_rect`] carves
//! `{z ∈ acc : φ(z)}` out with a Separation — so making every `Acc` carry one
//! would put a definitional extension into the struct that most callers never
//! use. This is the same split [`crate::wtype::Wtype::inversion`] makes.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::err::DResult;
use crate::funcs::{Apply, Sets};
use crate::{assembly, decline};

use super::condition::{acc_subset, acc_symbol, preds_in, step_closed};
use super::induction::acc_induction;
use super::intro::acc_intro;
use super::witness::{acc_empty_relation, acc_minimal, acc_no_loops, acc_no_two_cycle};

/// The `acc` symbol together with everything derived about it.
///
/// Built over a **single** [`Sets`], so that every `⟨y,x⟩` mentioned by a
/// relation comes from one definitional extension and the theorems compose.
/// Building two would mint two unrelated pairing operations and nothing here
/// would fit.
#[derive(Clone)]
pub struct Acc {
    /// Pairing and union; only `up` is used.
    pub sets: Sets,
    /// `∅`, with no members; see [`crate::empty::empty`].
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)`.
    pub empty_ax: Thm,
    /// The symbol `acc`.
    pub acc: FnSym,
    /// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) ↔ (z ∈ A ∧ ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C)))`.
    pub acc_ax: Thm,
    /// **A0**: `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → z ∈ A)`.
    pub acc_subset: Thm,
    /// **A2**: `⊢ ∀A ∀R ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → ∀z. (z ∈ acc(A,R) → z ∈ C))`.
    pub acc_induction: Thm,
    /// **A1**: `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc(A,R))))
    /// → x ∈ acc(A,R))` — unconditional; see [`crate::acc::acc_intro`].
    pub acc_intro: Thm,
    /// **Non-vacuity, positive**:
    /// `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. ¬(⟨y,x⟩ ∈ R)) → x ∈ acc(A,R))` — every
    /// `R`-minimal point of `A` is accessible. See [`crate::acc::acc_minimal`].
    pub minimal: Thm,
    /// **Non-vacuity, positive and closed**: `⊢ ∀A. acc(A,∅) = A`. See
    /// [`crate::acc::acc_empty_relation`]; it is built unconditionally so that a
    /// development whose `acc` came out empty would fail to construct at all.
    pub empty_relation: Thm,
}

impl Acc {
    /// Introduce every symbol and derive every theorem, from the axioms up.
    ///
    /// Mints a fresh [`Sets`] and a fresh `∅`. When the pairing has to be
    /// *shared*, use [`Acc::with_apply`] or [`Acc::over`].
    pub fn new_checked(env: &mut Env) -> DResult<Acc> {
        let sets = Sets::new(env);
        let (empty, empty_ax) = crate::empty::empty(env);
        Acc::over_checked(env, sets, empty, empty_ax)
    }

    /// The same, sharing the pairing and the empty set of an existing
    /// [`Apply`].
    ///
    /// This is the normal way to build one: `⟨y,x⟩` then denotes the same term
    /// here as it does in every other construction over that `Apply`, which is
    /// what makes an `acc` usable as a carrier alongside `Σ`, `+` and `W`.
    pub fn with_apply_checked(env: &mut Env, ap: &Apply) -> DResult<Acc> {
        Acc::over_checked(env, ap.sets.clone(), ap.empty, ap.empty_ax.clone())
    }

    /// The same, over caller-supplied pairing and empty set.
    ///
    /// `empty_ax` must **establish** `∀z. ¬(z ∈ e)` for the term
    /// `e := empty()` — right conclusion *and* no hypotheses; otherwise this
    /// returns `None` rather than building something that does not mean what it
    /// says.
    ///
    /// The hypothesis half is not redundant. `empty_ax` is stored verbatim as
    /// the [`Acc::empty_ax`] field, which [`crate::acc::acc_rect`] hands to
    /// [`crate::funcs::separation_full`] on every call; today a `Γ`-carrying one
    /// would be caught downstream at [`kernel::thm::define`], but only by
    /// accident, and the field's own doc says `⊢`.
    pub fn over_checked(env: &mut Env, sets: Sets, empty: FnSym, empty_ax: Thm) -> DResult<Acc> {
        // Insist the axiom really is about the symbol we were handed, and that
        // it is not conditional on anything.
        let probe = env.fresh_var();
        let inst = crate::rules::inst_all(&empty_ax, &[Term::var(probe)])?;
        if !crate::establishes(
            &inst,
            &Formula::not(Formula::mem(Term::var(probe), Term::apply(empty, vec![]))),
        ) {
            return Err(decline!("the empty-set axiom does not state that the empty set has no members"))
        }

        let up = sets.up;
        let (acc, acc_ax) = acc_symbol(env, up, &empty_ax)?;
        let sub = acc_subset(env, up, acc, &acc_ax)?;
        let ind = acc_induction(env, up, acc, &acc_ax)?;
        let intro = acc_intro(env, up, acc, &acc_ax, &ind)?;
        let minimal = acc_minimal(env, up, acc, &intro)?;
        let empty_relation = acc_empty_relation(env, up, empty, &empty_ax, acc, &sub, &minimal)?;

        let out = Acc {
            sets,
            empty,
            empty_ax,
            acc,
            acc_ax,
            acc_subset: sub,
            acc_induction: ind,
            acc_intro: intro,
            minimal,
            empty_relation,
        };
        // Every field above is documented `⊢ φ`, so none may carry a `Γ`. The
        // seven are derived here from an `empty_ax` already checked
        // unconditional, so this cannot fire today; it is the guard that keeps
        // the struct's own promise true if one of the derivations later starts
        // consuming something else.
        if !out.all_unconditional() {
            return Err(assembly!("Acc: a field of the assembled apparatus carries hypotheses"))
        }
        Ok(out)
    }

    /// The hypothesis half of the house rule for **every theorem this struct
    /// carries**: none of the seven is conditional on anything.
    ///
    /// All seven fields are documented `⊢ φ`, and every one of them is `pub`, so
    /// a caller can replace any of them after construction with a
    /// [`kernel::Thm::assume`] of the same conclusion. Anything that consumes an
    /// `Acc` it did not itself build owes this check — see
    /// [`crate::all_unconditional`] for why the conclusions are *not* rechecked
    /// here: they are this struct's own business, pinned by [`Acc::over`], while
    /// the hypothesis leg is checked nowhere else and would ride into a result
    /// labelled `⊢ …` through the first [`kernel::Thm::mp`].
    ///
    /// It is all seven and not the four that the recursion happens to consume
    /// today: `empty_ax`'s safety is an accident of
    /// [`kernel::thm::define`] refusing a hypothetical witness, `minimal` is
    /// simply unconsumed downstream at the moment, and neither is a property a
    /// future edit should have to rediscover.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(&[
            &self.empty_ax,
            &self.acc_ax,
            &self.acc_subset,
            &self.acc_induction,
            &self.acc_intro,
            &self.minimal,
            &self.empty_relation,
        ])
    }

    /// The term `acc(A,R)`.
    pub fn of(&self, a: Term, r: Term) -> Term { Term::apply(self.acc, vec![a, r]) }

    /// The term `⟨y,x⟩` — the edge of the relation, pointing from `y` to `x`.
    pub fn edge(&self, y: Term, x: Term) -> Term { crate::opair(self.sets.up, y, x) }

    /// The term `∅`.
    pub fn empty_term(&self) -> Term { Term::apply(self.empty, vec![]) }

    /// `step_closed(A,R,C)`, as a formula.
    pub fn step_closed_at(&self, env: &mut Env, a: &Term, r: &Term, c: &Term) -> Formula {
        step_closed(env, self.sets.up, a, r, c)
    }

    /// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ C))`, as a formula.
    pub fn preds_in_at(
        &self,
        env: &mut Env,
        a: &Term,
        r: &Term,
        c: &Term,
        x: &Term,
    ) -> Formula {
        preds_in(env, self.sets.up, a, r, c, x)
    }

    /// **Non-vacuity, negative**, derived on demand — see
    /// [`crate::acc::acc_no_loops`].
    ///
    /// Not a field: it is [`crate::acc::acc_rect`] at a particular `φ`, and
    /// `acc_rect` mints a fresh symbol per call.
    pub fn no_loops(&self, env: &mut Env) -> DResult<Thm> { acc_no_loops(env, self) }

    /// **Non-vacuity, negative and irreflexive**, derived on demand — see
    /// [`crate::acc::acc_no_two_cycle`].
    ///
    /// Not a field, for the same reason as [`Acc::no_loops`].
    pub fn no_two_cycle(&self, env: &mut Env) -> DResult<Thm> { acc_no_two_cycle(env, self) }
}

impl Acc {
    /// `Option`-shaped adaptor over [`Acc::new_checked`].
    ///
    /// `mini/` builds the apparatus from `Option`-returning functions and `?`
    /// cannot cross from `Result` to `Option`; this seat may not edit `mini/`.
    /// Same **migration seam** the crate root keeps for [`crate::rules`] — the
    /// reason is discarded here, and code inside `derived/` should call the
    /// `_checked` form, which keeps it. See `DERR-HANDOFF.md` §10.
    pub fn new(env: &mut Env) -> Option<Acc> { Acc::new_checked(env).ok() }

    /// `Option`-shaped adaptor over [`Acc::with_apply_checked`], for `mini/`.
    /// See [`Acc::new`].
    pub fn with_apply(env: &mut Env, ap: &Apply) -> Option<Acc> {
        Acc::with_apply_checked(env, ap).ok()
    }

    /// `Option`-shaped adaptor over [`Acc::over_checked`], for `mini/`.
    /// See [`Acc::new`].
    pub fn over(env: &mut Env, sets: Sets, empty: FnSym, empty_ax: Thm) -> Option<Acc> {
        Acc::over_checked(env, sets, empty, empty_ax).ok()
    }
}
