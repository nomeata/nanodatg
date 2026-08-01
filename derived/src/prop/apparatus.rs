//! The apparatus, and the proof that `Prop` is not trivial.
//!
//! # Interface
//!
//! [`Props::new`] builds every symbol and theorem the interpretations of `Eq`
//! and `And` need; the fields are the theorems. `eq_nontrivial` is the
//! non-vacuity witness.
//!
//! It does **not** build `U₀ = {0, 1}` itself, despite what this header used to
//! claim: nothing here mentions the set of truth values, only subsets of `1`.
//! `U₀` as a term, `⊢ [φ] ∈ U₀`, and the anchor `⊢ ∀x. ¬(x ∈ ⟦False⟧)` are
//! [`crate::anchor::falsity`].
//!
//! # Why the non-vacuity check is the point of this file
//!
//! Everything about the conditional singleton would still be true if `0 = 1` —
//! `U₀` would be a one-element set, every proposition would be the same set, and
//! "proof irrelevance" would be a statement with no content. `eq_nontrivial`
//! rules that out: the two truth values are **different sets**, so `U₀` really
//! has two elements and `⟦φ⟧ = 1` genuinely says something.
//!
//! # Scope
//!
//! Only the **typing** of `Eq.refl` and `And.intro` is built here — enough for
//! the tutorial tests, in which every computing recursor states its result as an
//! equation. The recursors of `Eq` and `And` themselves, indexed families in
//! general, and subsingleton elimination are all out of scope.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};
use crate::funcs::hyp_syl;
use crate::sums::Sums;
use crate::{a1i, and_left, and_right, contrapos, gen_all, inst_all};

use super::cond::{cond_elim, cond_intro, cond_subset_unit, cond_subsingleton, conditional_singleton};

/// The interpretations of Lean's `Eq` and `And`, and the unit apparatus they
/// stand on.
///
/// Built once: the `Sums` inside is *the* source of `1` and `•` for both
/// symbols, so their theorems compose. Building two would mint two unrelated
/// unit sets and nothing here would fit together.
pub struct Props {
    /// The unit type, the sums, and everything under them.
    pub sums: Sums,
    /// `eq_set(a,b) = [a = b]`.
    pub eq: FnSym,
    /// `⊢ ∀a ∀b ∀z. (z ∈ eq_set(a,b) ↔ (z ∈ 1 ∧ a = b))`.
    pub eq_ax: Thm,
    /// `⊢ ∀a. • ∈ eq_set(a,a)` — the typing of `Eq.refl`.
    pub eq_refl: Thm,
    /// `⊢ ∀a ∀b. (• ∈ eq_set(a,b) → a = b)` — soundness.
    pub eq_sound: Thm,
    /// `⊢ ∀a ∀b ∀z. (z ∈ eq_set(a,b) → z ∈ 1)`, i.e. `eq_set(a,b) ⊆ 1`.
    pub eq_subset: Thm,
    /// `⊢ ∀a ∀b ∀x ∀y. ((x ∈ eq_set(a,b) ∧ y ∈ eq_set(a,b)) → x = y)`.
    pub eq_irrel: Thm,
    /// `⊢ ∀a ∀b. (¬(a = b) → ¬(eq_set(a,a) = eq_set(a,b)))` — **non-vacuity**.
    pub eq_distinct: Thm,
    /// `and_set(p,q) = [• ∈ p ∧ • ∈ q]`.
    pub and: FnSym,
    /// `⊢ ∀p ∀q ∀z. (z ∈ and_set(p,q) ↔ (z ∈ 1 ∧ (• ∈ p ∧ • ∈ q)))`.
    pub and_ax: Thm,
    /// `⊢ ∀p ∀q. ((• ∈ p ∧ • ∈ q) → • ∈ and_set(p,q))` — `And.intro`'s typing.
    pub and_intro: Thm,
    /// `⊢ ∀p ∀q. (• ∈ and_set(p,q) → • ∈ p)`.
    pub and_proj_l: Thm,
    /// `⊢ ∀p ∀q. (• ∈ and_set(p,q) → • ∈ q)`.
    pub and_proj_r: Thm,
    /// `⊢ ∀p ∀q ∀z. (z ∈ and_set(p,q) → z ∈ 1)`, i.e. `and_set(p,q) ⊆ 1`.
    pub and_subset: Thm,
    /// `⊢ ∀p ∀q ∀x ∀y. ((x ∈ and_set(p,q) ∧ y ∈ and_set(p,q)) → x = y)`.
    pub and_irrel: Thm,
}

impl Props {
    /// Introduce both symbols and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Props> {
        let sums = Sums::new(env)?;

        // ── Eq ───────────────────────────────────────────────────────────────
        let (a, b) = (env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(a), Term::var(b));
        let eq_phi = Formula::eq(ta.clone(), tb.clone());
        let (eq, eq_ax) = conditional_singleton(env, &sums, &[a, b], &eq_phi)?;

        let eq_of = |x: Term, y: Term| Term::apply(eq, vec![x, y]);
        let chi_ab = inst_all(&eq_ax, &[ta.clone(), tb.clone()])?;
        let c_ab = eq_of(ta.clone(), tb.clone());

        let eq_sound = gen_all(&[a, b], &cond_elim(&sums, &eq_phi, &c_ab, &chi_ab)?);
        let eq_subset = gen_all(&[a, b], &cond_subset_unit(env, &sums, &eq_phi, &c_ab, &chi_ab)?);
        let eq_irrel = gen_all(&[a, b], &cond_subsingleton(env, &sums, &eq_phi, &c_ab, &chi_ab)?);

        // Reflexivity: the same lemma at `b := a`, where the condition is a
        // theorem rather than a hypothesis.
        let refl_phi = Formula::eq(ta.clone(), ta.clone());
        let chi_aa = inst_all(&eq_ax, &[ta.clone(), ta.clone()])?;
        let c_aa = eq_of(ta.clone(), ta.clone());
        let intro_aa = cond_intro(&sums, &refl_phi, &c_aa, &chi_aa)?;
        let eq_refl = Thm::gen(a, &Thm::mp(&intro_aa, &Thm::eq_refl(ta.clone()))?);

        let eq_distinct = eq_nontrivial(env, &sums, eq, &eq_ax, a, b)?;

        // ── And ──────────────────────────────────────────────────────────────
        let (p, q) = (env.fresh_var(), env.fresh_var());
        let (tp, tq) = (Term::var(p), Term::var(q));
        let pt = sums.point();
        let (mem_p, mem_q) =
            (Formula::mem(pt.clone(), tp.clone()), Formula::mem(pt.clone(), tq.clone()));
        let and_phi = Formula::and(mem_p.clone(), mem_q.clone());
        let (and, and_ax) = conditional_singleton(env, &sums, &[p, q], &and_phi)?;

        let chi_pq = inst_all(&and_ax, &[tp.clone(), tq.clone()])?;
        let c_pq = Term::apply(and, vec![tp.clone(), tq.clone()]);

        let and_intro = gen_all(&[p, q], &cond_intro(&sums, &and_phi, &c_pq, &chi_pq)?);
        let elim = cond_elim(&sums, &and_phi, &c_pq, &chi_pq)?;
        let and_proj_l = gen_all(&[p, q], &crate::syl(&elim, &and_left(mem_p.clone(), mem_q.clone()))?);
        let and_proj_r = gen_all(&[p, q], &crate::syl(&elim, &and_right(mem_p, mem_q))?);
        let and_subset = gen_all(&[p, q], &cond_subset_unit(env, &sums, &and_phi, &c_pq, &chi_pq)?);
        let and_irrel = gen_all(&[p, q], &cond_subsingleton(env, &sums, &and_phi, &c_pq, &chi_pq)?);

        Some(Props {
            sums,
            eq,
            eq_ax,
            eq_refl,
            eq_sound,
            eq_subset,
            eq_irrel,
            eq_distinct,
            and,
            and_ax,
            and_intro,
            and_proj_l,
            and_proj_r,
            and_subset,
            and_irrel,
        })
    }

    /// The term `eq_set(a, b)`, the denotation of `Eq a b`.
    pub fn eq_of(&self, a: Term, b: Term) -> Term { Term::apply(self.eq, vec![a, b]) }

    /// The term `and_set(p, q)`, the denotation of `And p q`.
    pub fn and_of(&self, p: Term, q: Term) -> Term { Term::apply(self.and, vec![p, q]) }
}

/// `⊢ ∀a ∀b. (¬(a = b) → ¬(eq_set(a,a) = eq_set(a,b)))` — **the non-vacuity
/// lemma**.
///
/// Every other theorem in this module would still hold if `[·]` were constant.
/// This one would not: `•` inhabits `eq_set(a,a)`, and if `a ≠ b` then nothing
/// inhabits `eq_set(a,b)`, so Leibniz refutes the equation between them.
/// Discharged at two provably distinct sets — [`crate::sums::tags_distinct`]
/// supplies `∅` and `1` — it shows the interpretation separates a true equation
/// from a false one.
fn eq_nontrivial(
    env: &mut Env,
    s: &Sums,
    eq: FnSym,
    eq_ax: &Thm,
    a: FreeVar,
    b: FreeVar,
) -> Option<Thm> {
    let (ta, tb) = (Term::var(a), Term::var(b));
    let pt = s.point();
    let (c_aa, c_ab) = (Term::apply(eq, vec![ta.clone(), ta.clone()]), Term::apply(eq, vec![ta.clone(), tb.clone()]));

    // `⊢ • ∈ eq_set(a,a)`.
    let refl_phi = Formula::eq(ta.clone(), ta.clone());
    let chi_aa = inst_all(eq_ax, &[ta.clone(), ta.clone()])?;
    let pt_in_aa = Thm::mp(&cond_intro(s, &refl_phi, &c_aa, &chi_aa)?, &Thm::eq_refl(ta.clone()))?;

    // `⊢ ¬(a = b) → ¬(• ∈ eq_set(a,b))`, from soundness.
    let chi_ab = inst_all(eq_ax, &[ta.clone(), tb.clone()])?;
    let sound = cond_elim(s, &Formula::eq(ta.clone(), tb.clone()), &c_ab, &chi_ab)?;
    let h = Formula::not(Formula::eq(ta, tb));
    let h_not_mem = contrapos(&sound)?;

    // `⊢ eq_set(a,a) = eq_set(a,b) → • ∈ eq_set(a,b)`, by Leibniz.
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(c_aa.clone(), c_ab.clone(), w, Formula::mem(pt.clone(), Term::var(w)));
    let e_mem = crate::mpd_const(&carry, &pt_in_aa)?;

    let out = hyp_syl(&a1i(&e_mem, h.clone()), &h_not_mem)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::not(Formula::eq(c_aa, c_ab))),
        "eq_nontrivial: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}
