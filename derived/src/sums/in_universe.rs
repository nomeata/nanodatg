//! Closure of a universe under the binary sum: `(a + b) ∈ U(c)`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))        [sum_in_universe]
//! ```
//!
//! One function, [`sum_in_universe`]. It carries **no hypothesis about
//! `U(c)`** — in particular not `is_universe(U(c))`, whose inaccessibility
//! clause is still open ([`crate::universe::inaccessibility_reduction`]) — and
//! no side condition on the summands. Callers need none of the derivation
//! below.
//!
//! # What it is made of
//!
//! `a + b` is `({∅} × a) ∪ ({1} × b)` ([`super::Sums::sum_def`]), so unfolding
//! the definition leaves four closure steps and nothing else:
//!
//! | step | supplied by |
//! |---|---|
//! | `∅ ∈ U(c)` | the `empty_in` argument, e.g. [`crate::tower::Tower::empty_in`] |
//! | `{∅} ∈ U(c)` and `{1} ∈ U(c)` | [`crate::universe::least_universe_pairing`] at `{x} = {x,x}` |
//! | `({∅} × a) ∈ U(c)`, `({1} × b) ∈ U(c)` | [`crate::funspace::product_in_universe`] |
//! | the union of those two | [`crate::universe::least_universe_bin_union`] |
//!
//! Everything is already proved; the file is the composition. Every argument is
//! rebuilt at our own terms and compared before use, so a stack that does not
//! fit together — a pairing lemma for a different universe operator, a product
//! lemma for a different `prod` — is refused rather than silently described as
//! a theorem about sums.
//!
//! # Why `∅ ∈ U(c)` is an argument rather than a step
//!
//! It is the one ingredient that is not a *closure* property, so it does not
//! follow from the three lemmas above: it needs `c ∈ U(c)` and `C₂`, which live
//! on [`crate::funspace::Space`] rather than on anything this module has. Any
//! caller that can supply `pairing`, `product` and `bin_union` for the same
//! `U(·)` already holds it — [`crate::tower::Tower`] stores all four as fields
//! — so it is taken as input rather than pulling a whole `Space` in.
//!
//! The tags are the reason it is needed at all: `{∅}` and `{1}` are sets that
//! occur in `a + b` but in neither summand, so their membership has to come
//! from somewhere, and it bottoms out at `∅`. (`{∅}` *is* the unit type `1`,
//! and `{1}` is its singleton, so the pairing lemma is used twice in a row on
//! the same chain.)
//!
//! # Where it is used
//!
//! `⟦List α⟧ ∈ ⟦Type 0⟧` needs it first of three things
//! (MEASUREMENTS.md:1524–1529), and more generally every §5.2 carrier is a
//! W-type over a **tag sum**, so a universe-membership proof for a compiled
//! inductive pays this toll once per declaration shape. Nothing consumes it in
//! the tree yet; the `tg.rs` clause that would is separate, later work.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::bin_union;
use crate::{a1i, and_intro, and_left, and_right, eq_symm, gen_all, hyp_and, hyp_mp, inst_all, singleton, syl};

use super::sum::Sums;

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))` — **`U(c)` is closed
/// under binary sums**.
///
/// `lu` is the universe operator, and the four theorems are its closure
/// properties, all of which must be about *that* operator and about `s`'s
/// pairing and product:
///
/// ```text
/// empty_in    ⊢ ∀c. ∅ ∈ U(c)
/// pairing     ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))
/// product     ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))
/// bin_union   ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))
/// ```
///
/// Each is instantiated at the terms this derivation needs and checked against
/// the shape rebuilt here; a mismatch returns `None`.
pub fn sum_in_universe(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    empty_in: &Thm,
    pairing: &Thm,
    product: &Thm,
    bin_union_closed: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let up = s.ap.sets.up;

    // The two tags' singletons: `{∅}`, which is the unit type `1`, and `{1}`.
    let zero = s.zero();
    let tag_l = s.unit();
    let tag_r = singleton(up, tag_l.clone());
    debug_assert_eq!(tag_l, singleton(up, zero.clone()), "the left tag is not {{∅}}");

    // ── `∅ ∈ U(c)`, and the two singletons above it ─────────────────────────
    let z_in = inst_all(empty_in, std::slice::from_ref(&tc))?;
    if *z_in.concl() != Formula::mem(zero.clone(), w.clone()) {
        return None
    }
    let sing_in = |x: &Term, x_in: &Thm| -> Option<Thm> {
        let at = inst_all(pairing, &[tc.clone(), x.clone(), x.clone()])?;
        let mem_x = Formula::mem(x.clone(), w.clone());
        let want = Formula::imp(
            Formula::and(mem_x.clone(), mem_x),
            Formula::mem(singleton(up, x.clone()), w.clone()),
        );
        if *at.concl() != want {
            return None
        }
        Thm::mp(&at, &and_intro(x_in, x_in))
    };
    let l_in = sing_in(&zero, &z_in)?;
    let r_in = sing_in(&tag_l, &l_in)?;

    // ── Under `H := (a ∈ U(c) ∧ b ∈ U(c))` ──────────────────────────────────
    let (ma, mb) = (Formula::mem(ta.clone(), w.clone()), Formula::mem(tb.clone(), w.clone()));
    let h = Formula::and(ma.clone(), mb.clone());

    let factor = |tag: &Term, tag_in: &Thm, x: &Term, h_x: &Thm| -> Option<Thm> {
        let at = inst_all(product, &[tc.clone(), tag.clone(), x.clone()])?;
        let want = Formula::imp(
            Formula::and(Formula::mem(tag.clone(), w.clone()), Formula::mem(x.clone(), w.clone())),
            Formula::mem(s.prod.of(tag.clone(), x.clone()), w.clone()),
        );
        if *at.concl() != want {
            return None
        }
        hyp_mp(&a1i(&at, h.clone()), &hyp_and(&a1i(tag_in, h.clone()), h_x)?)
    };
    let h_left = factor(&tag_l, &l_in, &ta, &and_left(ma.clone(), mb.clone()))?;
    let h_right = factor(&tag_r, &r_in, &tb, &and_right(ma, mb))?;

    // ── The union of the two tagged copies is the body of `a + b` ───────────
    let (pl, pr) = (s.prod.of(tag_l, ta.clone()), s.prod.of(tag_r, tb.clone()));
    let body = s.sum_term(ta.clone(), tb.clone());
    debug_assert_eq!(
        body,
        bin_union(&s.ap.sets, pl.clone(), pr.clone()),
        "the sum's body is not the union of its two tagged copies"
    );
    let bu = inst_all(bin_union_closed, &[tc.clone(), pl.clone(), pr.clone()])?;
    let want = Formula::imp(
        Formula::and(Formula::mem(pl, w.clone()), Formula::mem(pr, w.clone())),
        Formula::mem(body.clone(), w.clone()),
    );
    if *bu.concl() != want {
        return None
    }
    let h_body = hyp_mp(&a1i(&bu, h.clone()), &hyp_and(&h_left, &h_right)?)?;

    // ── Fold the body back up into the symbol ───────────────────────────────
    let sum_t = s.sum_of(ta.clone(), tb.clone());
    let def_at = inst_all(&s.sum_def, &[ta, tb])?;
    if *def_at.concl() != Formula::eq(sum_t.clone(), body.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let leib =
        Thm::eq_leibniz(body, sum_t.clone(), hole, Formula::mem(Term::var(hole), w.clone()));
    let out = syl(&h_body, &Thm::mp(&leib, &eq_symm(env, &def_at)?)?)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(sum_t, w)),
        "sum_in_universe: unexpected shape"
    );
    Some(gen_all(&[cv, av, bv], &out))
}
