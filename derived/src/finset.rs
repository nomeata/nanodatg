//! **The finite set `{a₀, …, a_{m-1}}`**, as a right-nested chain of binary
//! unions of singletons, with its `m` memberships and its inclusion rule.
//!
//! # Why it is wanted
//!
//! Twice in the translation of an inductive declaration, and for the same
//! reason both times: a **codomain has to be produced before anything can be
//! typed**, and the cheapest set containing `m` given elements is the chain
//!
//! ```text
//! fin(a₀ … a_{m-1}) := {a₀} ∪ ({a₁} ∪ (… ∪ ∅))
//! ```
//!
//! [`crate::fibre`] already builds exactly this term by hand for the fibre
//! family's codomain (`{finord(m₀)} ∪ …`), and [`crate::recarg`] needs it again
//! for a constructor's recursive-argument function: that function is a
//! [`crate::isum::Dispatch`], and `Dispatch::new` demands **unconditional**
//! branch typings, which are only available if the codomain is a set the
//! branches are in *by construction* rather than by hypothesis. Taking the
//! codomain to be `fin(r⃗)` and then widening with
//! [`Wtype::fs_mono`](crate::wtype::Wtype::fs_mono) is what turns
//! `r_j ∈ carrier` from a premise of the dispatcher into a premise of the
//! *inclusion*, where it belongs.
//!
//! # Interface
//!
//! [`FinSet::new`] derives the one lemma the chain is walked with; the term is
//! [`FinSet::of`], and the two exports are
//!
//! ```text
//! ⊢ aᵢ ∈ fin(a⃗)                                                 [FinSet::mem]
//! ⊢ (a₀ ∈ T ∧ (… ∧ a_{m-1} ∈ T)) → fin(a⃗) ⊆ T                   [FinSet::subset]
//! ```
//!
//! both at caller-supplied terms, which may be open. [`FinSet::subset`] is
//! defined only for `m ≥ 1`; at `m = 0` the chain is `∅`, the statement has no
//! antecedent, and the caller wanting `∅ ⊆ T` has
//! [`crate::wtype::empty_is_a_function`]'s neighbourhood instead — see
//! [`crate::recarg`], which special-cases `m = 0` for exactly this reason and
//! does not need the inclusion at all.
//!
//! # Non-vacuity
//!
//! [`FinSet::mem`] alone would hold of `fin(a⃗) := V`; [`FinSet::subset`] alone
//! would hold of `fin(a⃗) := ∅`. Together they pin the chain between the two:
//! it contains every `aᵢ` and nothing that is not forced. `tests/finset.rs`
//! cashes that by deriving `fin(a,b) ⊆ T` and `a ∈ fin(a,b)` at fresh `a`, `b`,
//! and checking the chain is not `∅` — `a ∈ fin(a,b)` with `¬(a ∈ ∅)` is a
//! contradiction, so the two exports cannot both be about the empty set.
//!
//! # Nothing here is an axiom
//!
//! `m` pairings and `m` unions, with membership read off
//! [`crate::sums::mem_bin_union_iff`] and
//! [`Apply::mem_sing`](crate::funcs::Apply::mem_sing). No new symbol.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{or_intro_left, or_intro_right};
use crate::funspace::bin_union;
use crate::sums::{mem_bin_union_iff, Sums};
use crate::{
    a1i, com12, conj_of, conj_proj, ex_falso, eq_symm_imp, hyp_or_elim, iff_mp, iff_mpr, inst_all,
    singleton, syl,
};

/// The chain `{a₀} ∪ ({a₁} ∪ (… ∪ ∅))`, together with the one lemma every walk
/// along it uses.
///
/// Held as a struct only so that [`crate::sums::mem_bin_union_iff`] is derived
/// once rather than once per element.
pub struct FinSet {
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
    pub bin: Thm,
}

impl FinSet {
    /// Derive the union-membership lemma the chain is walked with.
    pub fn new(env: &mut Env, s: &Sums) -> Option<FinSet> {
        Some(FinSet { bin: mem_bin_union_iff(env, &s.ap.sets)? })
    }

    /// The term `{a₀} ∪ ({a₁} ∪ (… ∪ ∅))`; the empty list gives `∅`.
    pub fn of(s: &Sums, elems: &[Term]) -> Term {
        elems.iter().rev().fold(s.zero(), |acc, v| {
            bin_union(&s.ap.sets, singleton(s.ap.sets.up, v.clone()), acc)
        })
    }

    /// `⊢ aᵢ ∈ fin(a⃗)` — the `i`-th element is in the chain.
    ///
    /// One [`Apply::mem_sing`](crate::funcs::Apply::mem_sing) for `aᵢ ∈ {aᵢ}`,
    /// then `i` right-injections and one left-injection climbing out of the
    /// nested unions. Returns `None` if `i` is out of range.
    pub fn mem(&self, s: &Sums, elems: &[Term], i: usize) -> Option<Thm> {
        if i >= elems.len() {
            return None
        }
        let ap = &s.ap;
        let target = FinSet::of(s, elems);
        let sing = singleton(ap.sets.up, elems[i].clone());
        let rest = FinSet::of(s, &elems[i + 1..]);

        let in_sing = Thm::mp(
            &iff_mpr(&inst_all(&ap.mem_sing, &[elems[i].clone(), elems[i].clone()])?)?,
            &Thm::eq_refl(elems[i].clone()),
        )?;
        let mut th = Thm::mp(
            &iff_mpr(&inst_all(&self.bin, &[sing.clone(), rest.clone(), elems[i].clone()])?)?,
            &Thm::mp(
                &or_intro_left(
                    Formula::mem(elems[i].clone(), sing),
                    Formula::mem(elems[i].clone(), rest),
                ),
                &in_sing,
            )?,
        )?;
        for j in (0..i).rev() {
            let sj = singleton(ap.sets.up, elems[j].clone());
            let rj = FinSet::of(s, &elems[j + 1..]);
            th = Thm::mp(
                &iff_mpr(&inst_all(&self.bin, &[sj.clone(), rj.clone(), elems[i].clone()])?)?,
                &Thm::mp(
                    &or_intro_right(
                        Formula::mem(elems[i].clone(), sj),
                        Formula::mem(elems[i].clone(), rj),
                    ),
                    &th,
                )?,
            )?;
        }
        debug_assert_eq!(
            *th.concl(),
            Formula::mem(elems[i].clone(), target),
            "finset: mem has the wrong shape"
        );
        Some(th)
    }

    /// `⊢ (a₀ ∈ T ∧ (… ∧ a_{m-1} ∈ T)) → fin(a⃗) ⊆ T`, for `m ≥ 1`.
    ///
    /// Induction on the chain, carried out with the *element* hypothesis
    /// outermost so that no currying is needed: at each link
    /// [`crate::sums::mem_bin_union_iff`] splits `z ∈ {aⱼ} ∪ rest` into a
    /// disjunction, the left branch turns `z = aⱼ` into `z ∈ T` by Leibniz off
    /// the `j`-th conjunct, and the right branch is the tail. The base is
    /// `¬(z ∈ ∅)`.
    pub fn subset(&self, env: &mut Env, s: &Sums, elems: &[Term], t: &Term) -> Option<Thm> {
        let m = elems.len();
        if m == 0 {
            return None
        }
        let ap = &s.ap;
        let atoms: Vec<Formula> =
            elems.iter().map(|a| Formula::mem(a.clone(), t.clone())).collect();
        let h = conj_of(&atoms)?;

        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let z_in_t = Formula::mem(tz.clone(), t.clone());
        let goal = Formula::imp(h.clone(), z_in_t.clone());

        // ── the base: nothing is in `∅` ─────────────────────────────────────
        let mut cur = syl(
            &inst_all(&ap.empty_ax, std::slice::from_ref(&tz))?,
            &ex_falso(goal.clone()),
        )?;

        for j in (0..m).rev() {
            let sj = singleton(ap.sets.up, elems[j].clone());
            let rest = FinSet::of(s, &elems[j + 1..]);
            let here = FinSet::of(s, &elems[j..]);
            let in_sj = Formula::mem(tz.clone(), sj.clone());

            // `⊢ z ∈ {aⱼ} → (aⱼ ∈ T → z ∈ T)`, then the `j`-th conjunct.
            let hole = env.fresh_var();
            let to_val = syl(
                &syl(
                    &iff_mp(&inst_all(&ap.mem_sing, &[elems[j].clone(), tz.clone()])?)?,
                    &eq_symm_imp(env, tz.clone(), elems[j].clone()),
                )?,
                &Thm::eq_leibniz(
                    elems[j].clone(),
                    tz.clone(),
                    hole,
                    Formula::mem(Term::var(hole), t.clone()),
                ),
            )?;
            let left = com12(&syl(&conj_proj(&atoms, j)?, &com12(&to_val)?)?)?;
            debug_assert_eq!(
                *left.concl(),
                Formula::imp(in_sj.clone(), goal.clone()),
                "finset: the singleton branch has the wrong shape"
            );

            let disj = iff_mp(&inst_all(&self.bin, &[sj, rest, tz.clone()])?)?;
            let here_mem = Formula::mem(tz.clone(), here);
            cur = hyp_or_elim(
                &disj,
                &a1i(&left, here_mem.clone()),
                &a1i(&cur, here_mem.clone()),
            )?;
        }

        // `⊢ z ∈ fin → (H → z ∈ T)` becomes `⊢ H → ∀z. (z ∈ fin → z ∈ T)`.
        let swapped = com12(&cur)?;
        let out = Thm::mp(&Thm::ax_dist(zv, h.clone(), swapped.concl().as_imp()?.1)?, &Thm::gen(zv, &swapped))?;
        debug_assert_eq!(
            *out.concl(),
            Formula::imp(h, kernel::thm::subset(env, FinSet::of(s, elems), t.clone())),
            "finset: subset has the wrong shape"
        );
        Some(out)
    }
}
