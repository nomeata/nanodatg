//! Adjoining one element to a set.
//!
//! # Interface
//!
//! `adjoin(s,e)` is the *term* `s ∪ {e}` — a composition of existing symbols, so
//! no definitional extension and no proof obligation — and
//!
//! ```text
//! ⊢ ∀s ∀e ∀z. (z ∈ s ∪ {e} ↔ (z ∈ s ∨ z = e))          [mem_adjoin]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why it is worth a file
//!
//! The approximation argument extends a graph by exactly one pair, and every one
//! of the five conjuncts of [`crate::recursion::Approx`] then has to be
//! re-established for the extension. Each of those re-establishments starts by
//! splitting a membership in `h ∪ {⟨a,v⟩}` into "was already there" and "is the
//! new pair", so the split is worth having once in the shape both directions
//! want, rather than composing
//! [`crate::sums::mem_bin_union_iff`] with the singleton lemma at every use.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{or_intro_left, or_intro_right, Sets};
use crate::funspace::mem_bin_union;
use crate::sums::mem_bin_union_iff;
use crate::{
    a1i, and_intro, gen_all, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all,
    singleton, syl,
};

/// The term `s ∪ {e}`.
pub fn adjoin(sets: &Sets, s: Term, e: Term) -> Term {
    crate::funspace::bin_union(sets, s, singleton(sets.up, e))
}

/// `⊢ ∀s ∀e ∀z. (z ∈ s ∪ {e} ↔ (z ∈ s ∨ z = e))`.
///
/// [`crate::sums::mem_bin_union_iff`] splits the union and `mem_sing` — which
/// must be `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)` — turns the right disjunct into an
/// equation; the two directions are assembled separately because the disjunction
/// has to be taken apart in one and put together in the other.
pub fn mem_adjoin(env: &mut Env, sets: &Sets, mem_sing: &Thm) -> Option<Thm> {
    let (s, e, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, te, tz) = (Term::var(s), Term::var(e), Term::var(z));
    let sing = singleton(sets.up, te.clone());
    let un = adjoin(sets, ts.clone(), te.clone());

    let mem_un = Formula::mem(tz.clone(), un.clone());
    let mem_s = Formula::mem(tz.clone(), ts.clone());
    let mem_sg = Formula::mem(tz.clone(), sing.clone());
    let eq_ze = Formula::eq(tz.clone(), te.clone());
    let goal = Formula::or(mem_s.clone(), eq_ze.clone());

    let bin = inst_all(&mem_bin_union_iff(env, sets)?, &[ts.clone(), sing.clone(), tz.clone()])?;
    let sng = inst_all(mem_sing, &[te.clone(), tz.clone()])?;
    debug_assert_eq!(
        *sng.concl(),
        Formula::iff(mem_sg.clone(), eq_ze.clone()),
        "mem_adjoin: the singleton lemma has an unexpected shape"
    );

    // ── forward ──────────────────────────────────────────────────────────────
    let fwd_disj = iff_mp(&bin)?;
    let left = a1i(&or_intro_left(mem_s.clone(), eq_ze.clone()), mem_un.clone());
    let right = a1i(
        &syl(&iff_mp(&sng)?, &or_intro_right(mem_s.clone(), eq_ze.clone()))?,
        mem_un.clone(),
    );
    let fwd = hyp_or_elim(&fwd_disj, &left, &right)?;

    // ── backward ─────────────────────────────────────────────────────────────
    let (into_left, into_right) = mem_bin_union(env, sets)?;
    let in_s = inst_all(&into_left, &[ts.clone(), sing.clone(), tz.clone()])?;
    let in_sing = inst_all(&into_right, &[ts.clone(), sing.clone(), tz.clone()])?;
    let bwd_left = a1i(&in_s, goal.clone());
    let bwd_right = a1i(&syl(&iff_mpr(&sng)?, &in_sing)?, goal.clone());
    let bwd = hyp_or_elim(&imp_refl(goal.clone()), &bwd_left, &bwd_right)?;

    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(*out.concl(), Formula::iff(mem_un, goal), "mem_adjoin: unexpected shape");
    Some(gen_all(&[s, e, z], &out))
}
