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

use kernel::{Formula, Thm};

use crate::{a1i, clavius, com12, contrapos, ex_falso, hyp_mp, imp_mono_r, syl, syl_imp};

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
pub fn cases(pos: &Thm, neg: &Thm) -> Option<Thm> {
    let (_, chi) = pos.concl().as_imp()?;
    let nc_chi = syl(&contrapos(pos)?, neg)?; // ¬χ → ¬φ → χ
    Thm::mp(&clavius(chi), &nc_chi)
}

/// Modus ponens two implications deep: from `⊢ H → (A → (B → C))` and
/// `⊢ H → (A → B)` infer `⊢ H → (A → C)`.
pub fn hyp_mp2(h_imp: &Thm, h_arg: &Thm) -> Option<Thm> {
    let (h, rest) = h_imp.concl().as_imp()?;
    let (a, bc) = rest.as_imp()?;
    let (b, c) = bc.as_imp()?;
    let s = a1i(&Thm::ax_s(a, b, c), h);
    hyp_mp(&hyp_mp(&s, h_imp)?, h_arg)
}

/// Chain two implications under a hypothesis: from `⊢ H → (a → b)` and
/// `⊢ H → (b → c)` infer `⊢ H → (a → c)`.
pub fn hyp_syl(h_ab: &Thm, h_bc: &Thm) -> Option<Thm> {
    let (h, ab) = h_ab.concl().as_imp()?;
    let (a, b) = ab.as_imp()?;
    let (_, bc) = h_bc.concl().as_imp()?;
    let (_, c) = bc.as_imp()?;
    let bridge = a1i(&syl_imp(a, b, c), h);
    hyp_mp(&hyp_mp(&bridge, h_ab)?, h_bc)
}
