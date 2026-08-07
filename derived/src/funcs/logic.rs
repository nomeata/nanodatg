//! Propositional odds and ends.
//!
//! # Interface
//!
//! ```text
//! ⊢ l → (l ∨ r)                                                    [or_intro_left]
//! ⊢ r → (l ∨ r)                                                    [or_intro_right]
//! from ⊢ φ → χ and ⊢ ¬φ → χ                    infer ⊢ χ           [cases]
//! from ⊢ H → (A → (B → C)) and ⊢ H → (A → B)   infer ⊢ H → (A → C) [hyp_mp2]
//! from ⊢ H → (a → b) and ⊢ H → (b → c)         infer ⊢ H → (a → c) [hyp_syl]
//! ```
//!
//! Disjunction is `¬a → b`, so introducing a disjunct is not a projection but a
//! small derivation, and a case analysis with no ambient hypothesis needs its
//! own combinator — [`cases`] is Clavius' law rather than an appeal to excluded
//! middle. The two `hyp_` combinators are the `⊢ H → φ` idiom's replacements for
//! modus ponens and syllogism, there being no deduction theorem. All five are
//! used constantly throughout the crate.
//!
//! # How this fails
//!
//! The five entries here split three ways.
//!
//! [`or_intro_left`] and [`or_intro_right`] are **infallible**: they build a
//! theorem out of two formulas and nothing can be wrong with the input.
//!
//! [`cases`] and [`hyp_mp2`] return [`crate::err::DResult`], and each is a
//! combinator over the two theorems it is handed and nothing else — three or
//! four steps, no derivation of its own — so both carry `#[track_caller]` and
//! both site their guards at the caller with [`crate::decline_at_caller`]. With
//! these two reached from all over the crate, the site worth reporting is the
//! line that composed the call, never the line inside. Each **declines** when
//! its *first* premise is not the implication its signature spells out. That
//! read is the contract check and not merely a shape check: below it
//! [`crate::rules::syl`] and [`crate::rules::hyp_mp`] decline when the second
//! premise does not fit the first, so leaving the read an `Assembly` would make
//! the verdict depend on how far wrong the caller was — see *Shape versus fit*
//! in [`crate::err`]. The second premise is left to those two, which report its
//! shape with the offending formula attached.
//!
//! [`hyp_syl`] is deliberately still `Option`-shaped. It is a three-line adaptor
//! over [`crate::rules::hyp_syl`], where the derivation and its reason now live,
//! and it is kept for the ~200 call sites that have not moved to `DResult`; it
//! is a migration seam rather than a design.

use kernel::{Formula, Thm};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{com12, contrapos, hyp_mp, imp_mono_r, syl};
use crate::{a1i, clavius, decline_at_caller, ex_falso};

/// `⊢ l → (l ∨ r)`.
///
/// `l ∨ r` is `¬l → r`, so from `l` the antecedent is absurd and ex falso
/// supplies `r`.
pub fn or_intro_left(l: Formula, r: Formula) -> Thm {
    let mono = imp_mono_r(&ex_falso(r), l).expect("or_intro_left: monotonicity applies");
    com12(&mono).expect("or_intro_left: com12 applies")
}

/// `⊢ r → (l ∨ r)`. Weakening, since `l ∨ r` is `¬l → r`.
pub fn or_intro_right(l: Formula, r: Formula) -> Thm { Thm::ax_k(r, Formula::not(l)) }

/// Case analysis with no ambient hypothesis: from `⊢ φ → χ` and `⊢ ¬φ → χ`
/// infer `⊢ χ`.
///
/// Three steps over the two theorems it is handed and no derivation of its own,
/// so it is `#[track_caller]`: the site worth reporting is the line that
/// composed the call. **Declines** when the positive case is not an
/// implication — that read *is* the contract check, because the syllogism below
/// it declines when `neg`'s antecedent is not the negation of `pos`'s, and the
/// two mistakes must not get different verdicts. A `neg` of the wrong shape
/// altogether is reported by [`crate::rules::syl`], with the formula attached.
#[track_caller]
pub fn cases(pos: &Thm, neg: &Thm) -> DResult<Thm> {
    let (_, chi) = match pos.concl().imp_parts() {
        Ok(parts) => parts,
        Err(_) => {
            return Err(decline_at_caller!(
                "the positive case does not prove an implication, so there is no condition to split on"
            ))
        }
    };
    let nc_chi = syl(&contrapos(pos)?, neg)?; // ¬χ → ¬φ → χ
    prim::mp(&clavius(chi), &nc_chi)
}

/// Modus ponens two implications deep: from `⊢ H → (A → (B → C))` and
/// `⊢ H → (A → B)` infer `⊢ H → (A → C)`.
///
/// Four steps over the two theorems it is handed and no derivation of its own,
/// so it is `#[track_caller]`. **Declines** when the implication premise is not
/// three implications deep: that read is the contract check, [`hyp_mp`] below it
/// declining when the argument premise does not fit it.
#[track_caller]
pub fn hyp_mp2(h_imp: &Thm, h_arg: &Thm) -> DResult<Thm> {
    let (h, rest) = match h_imp.concl().imp_parts() {
        Ok(parts) => parts,
        Err(_) => {
            return Err(decline_at_caller!("the implication premise is not of the shape H → (A → (B → C))"))
        }
    };
    let (a, bc) = match rest.imp_parts() {
        Ok(parts) => parts,
        Err(_) => {
            return Err(decline_at_caller!("the implication premise is not of the shape H → (A → (B → C))"))
        }
    };
    let (b, c) = match bc.imp_parts() {
        Ok(parts) => parts,
        Err(_) => {
            return Err(decline_at_caller!("the implication premise is not of the shape H → (A → (B → C))"))
        }
    };
    let s = a1i(&Thm::ax_s(a, b, c), h);
    hyp_mp(&hyp_mp(&s, h_imp)?, h_arg)
}

/// Chain two implications under a hypothesis: from `⊢ H → (a → b)` and
/// `⊢ H → (b → c)` infer `⊢ H → (a → c)`.
///
/// `Option`-shaped adaptor over [`crate::rules::hyp_syl`], which is where the
/// derivation now lives — this module and `crate::separation` had two copies of
/// it, differing only in whether the two hypotheses were compared here or left
/// to [`hyp_mp`] one frame on. The reason is discarded here; see
/// [`crate::rules`].
pub fn hyp_syl(h_ab: &Thm, h_bc: &Thm) -> Option<Thm> {
    crate::rules::hyp_syl(h_ab, h_bc).ok()
}
