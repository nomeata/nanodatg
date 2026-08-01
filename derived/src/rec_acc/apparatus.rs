//! The accessibility recursor, assembled once.
//!
//! # Interface
//!
//! [`RecAcc::new`] builds every symbol and derives every theorem from the axioms
//! up; [`RecAcc::over`] does the same over a caller-supplied [`Base`], which is
//! itself built over a caller-supplied [`crate::sums::Sums`] and
//! [`crate::acc::Acc`]. **Use `over`.** A `RecAcc` built beside, rather than
//! over, a client's apparatus mints a second `⟨·,·⟩`, a second `app` and a
//! second `acc`, and then not one theorem here mentions the client's terms.
//!
//! The fields are the whole contract; the functions in the sibling files are
//! not meant to be called directly.
//!
//! # Every theorem, in one place
//!
//! Writing `accrec` for `accrec(A,R,T,e)` and `ST` for
//! [`super::extend::step_typed`]:
//!
//! ```text
//! ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att ↔ (g ∈ 𝒫(prod(acc(A,R),T)) ∧ (sv(g) ∧ rec_cond(g))))
//! ⊢ ∀A ∀R ∀T ∀e. ∅ ∈ Att                                     [empty_attempt]
//! ⊢ ∀A ∀R ∀T ∀e ∀z. (z ∈ acc(A,R) → agree_formula(z))            [agreement]
//! ⊢ ∀A ∀R ∀T ∀e. accrec = ⋃ Att                                 [rec_symbol]
//! ⊢ ∀A ∀R ∀T ∀e. accrec ⊆ prod(acc(A,R),T)                 [rec_subset_prod]
//! ⊢ ∀A ∀R ∀T ∀e. sv(accrec)                              [rec_single_valued]
//! ⊢ ∀A ∀R ∀T ∀e. accrec ∈ Att                               [rec_is_attempt]
//! ⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) → app(accrec,x) = step)  [iota_on_domain]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))      [totality]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → accrec ∈ fs(acc(A,R),T))               [rec_funspace]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(accrec,x) = step))     [iota]
//! ```
//!
//! where `step` is `app(app(app(e,x),•), ih(accrec,A,R,x))`. Everything above
//! `totality` is **unconditional**; `ST` is the only hypothesis in the module,
//! and there is no analogue of `wrec`'s `closed(A,B,u)`.

use kernel::{Env, Env as E, FnSym, Term, Thm};

use crate::acc::Acc;
use crate::sums::Sums;

use super::agree::agreement;
use super::attempt::{att_of, attempts, empty_attempt};
use super::base::Base;
use super::extend::step_typed;
use super::package::{pack_app, pack_iota, pack_of};
use super::is_attempt::{iota_on_domain, rec_is_attempt, rec_rec_cond, Syms, UnionFacts};
use super::total::{iota, rec_funspace, totality, Machinery};
use super::union::{
    attempt_indom_rec, attempt_subset_rec, rec_members, rec_of, rec_single_valued,
    rec_subset_prod, rec_symbol, rec_value,
};

/// The accessibility recursor and everything derived about it.
#[derive(Clone)]
pub struct RecAcc {
    /// The shared apparatus: `Sums`, `Acc`, the conditional value and `ih`.
    pub base: Base,
    /// The symbol `Att(A,R,T,e)`.
    pub att: FnSym,
    /// Its characteristic theorem.
    pub att_ax: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. ∅ ∈ Att(A,R,T,e)`.
    pub empty_attempt: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀z. (z ∈ acc(A,R) → agree_formula(z))`.
    pub agreement: Thm,
    /// The symbol `accrec(A,R,T,e)`.
    pub rec: FnSym,
    /// `⊢ ∀A ∀R ∀T ∀e. accrec(A,R,T,e) = ⋃ Att(A,R,T,e)`.
    pub rec_def: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀p. (p ∈ accrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))`.
    pub rec_members: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ accrec)`.
    pub attempt_subset: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. accrec ⊆ prod(acc(A,R),T)`.
    pub rec_subset_prod: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. sv(accrec)` — **unconditional**.
    pub rec_single_valued: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(accrec,x) = app(g,x)))`.
    pub rec_value: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(accrec,x)))`.
    pub attempt_indom: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. rec_cond(A,R,e,accrec)`.
    pub rec_rec_cond: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. accrec ∈ Att`.
    pub rec_is_attempt: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) → app(accrec,x) = step)` — ι, guarded.
    pub iota_on_domain: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))`.
    pub totality: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → accrec ∈ fs(acc(A,R),T))`.
    pub rec_funspace: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(accrec,x) = step))` — **ι**.
    pub iota: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e ∀x. (x ∈ acc(A,R) → app(app(pack,x),•) = app(accrec,x))`
    /// — the thesis's outer packaging, applied to a point and its proof.
    pub pack_app: Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(app(pack,x),•) = step))`
    /// — **ι at the thesis's spelling** (thesis.txt:2129).
    pub pack_iota: Thm,
}

impl RecAcc {
    /// Build everything from the axioms up. For tests; a client with an
    /// apparatus of its own wants [`RecAcc::over`].
    pub fn new(env: &mut Env) -> Option<RecAcc> {
        let s = Sums::new(env)?;
        let ac = Acc::with_apply(env, &s.ap)?;
        let base = Base::over(env, s, ac)?;
        RecAcc::over(env, base)
    }

    /// Build over a caller-supplied [`Base`].
    pub fn over(env: &mut E, base: Base) -> Option<RecAcc> {
        let bin = crate::sums::mem_bin_union_iff(env, &base.s.ap.sets)?;

        let (att, att_ax) = attempts(env, &base)?;
        let empty = empty_attempt(env, &base, att, &att_ax)?;
        let ag = agreement(env, &base, att, &att_ax)?;

        let (rec, rec_def) = rec_symbol(env, &base, att)?;
        let members = rec_members(env, &base, att, rec, &rec_def)?;
        let attempt_subset = attempt_subset_rec(env, att, &members)?;
        let subset_prod = rec_subset_prod(env, &base, att, &att_ax, rec, &members)?;
        let sv = rec_single_valued(env, &base, att, &att_ax, rec, &members, &ag)?;
        let value = rec_value(env, &base, att, &att_ax, rec, &attempt_subset, &sv)?;
        let indom = attempt_indom_rec(env, &base, att, rec, &attempt_subset)?;

        let facts = UnionFacts {
            subset_prod: &subset_prod,
            single_valued: &sv,
            value: &value,
            indom: &indom,
            members: &members,
        };
        let rc = rec_rec_cond(env, &base, att, &att_ax, rec, &facts)?;
        let syms = Syms { att, att_ax: &att_ax, rec };
        let is_att = rec_is_attempt(env, &base, syms, &facts, &rc)?;
        let iota_dom = iota_on_domain(env, &base, rec, &rc)?;

        let m = Machinery {
            att,
            att_ax: &att_ax,
            rec,
            facts: &facts,
            iota_dom: &iota_dom,
            rec_rc: &rc,
            bin: &bin,
        };
        let total = totality(env, &base, &m)?;
        let fsp = rec_funspace(env, &base, rec, &facts, &total)?;
        let io = iota(env, &base, rec, &total, &iota_dom)?;
        let pa = pack_app(env, &base, rec)?;
        let pi = pack_iota(env, &base, rec, &pa, &io)?;

        Some(RecAcc {
            base,
            att,
            att_ax,
            empty_attempt: empty,
            agreement: ag,
            rec,
            rec_def,
            rec_members: members,
            attempt_subset,
            rec_subset_prod: subset_prod,
            rec_single_valued: sv,
            rec_value: value,
            attempt_indom: indom,
            rec_rec_cond: rc,
            rec_is_attempt: is_att,
            iota_on_domain: iota_dom,
            totality: total,
            rec_funspace: fsp,
            iota: io,
            pack_app: pa,
            pack_iota: pi,
        })
    }

    /// The term `accrec(A,R,T,e)`.
    pub fn of(&self, a: Term, r: Term, t: Term, e: Term) -> Term { rec_of(self.rec, a, r, t, e) }

    /// The term `pack(A,R,T,e)` — the thesis's `rec_acc(A,R,e)` at target `T`.
    pub fn pack(&self, a: &Term, r: &Term, t: &Term, e: &Term) -> Term {
        pack_of(&self.base, self.rec, a, r, t, e)
    }

    /// The term `Att(A,R,T,e)`.
    pub fn att_of(&self, a: Term, r: Term, t: Term, e: Term) -> Term {
        att_of(self.att, a, r, t, e)
    }

    /// `step_typed(A,R,T,e)`, as a formula — the one hypothesis anything in this
    /// module carries.
    pub fn step_typed(
        &self,
        env: &mut Env,
        a: &Term,
        r: &Term,
        t: &Term,
        e: &Term,
    ) -> kernel::Formula {
        step_typed(env, &self.base, a, r, t, e)
    }
}
