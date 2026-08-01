//! **The recursion's own induction hypothesis is in `ih_bound`.**
//!
//! # Interface
//!
//! Writing `accrec` for `accrec(A,R,T,e)` and `ST` for [`super::step_typed`]:
//!
//! ```text
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) →
//!       ih(accrec,A,R,x) ∈ ih_bound(A,T)))                    [ih_in_bound]
//! ```
//!
//! # Why this was missing, and what wants it
//!
//! [`super::ih::ih_typed`] is stated over an *arbitrary* `g` and so is guarded
//! by [`super::preds_typed`] — "`g`'s values on the `R`-predecessors of `x`
//! land in `T`". Inside the recursion that guard is discharged from the
//! induction hypothesis ([`super::extend`] does exactly that at the one new
//! point), so `rec_acc` never needed it at the *top level*, for `accrec`
//! itself, and did not derive it.
//!
//! A consumer does. `rec_acc`'s ι rule computes `app(accrec,x)` to
//! `step(e,x,ih(accrec,A,R,x))`, and a caller who wants that step to *be*
//! something — Lean's minor premise applied to the constructor's fields, say —
//! has to hold an equation about `step(e,x,c)`. That equation cannot be
//! unguarded in `c`: a set-level `e` is a function with a set domain, so it can
//! only be specified on a set of arguments, and [`super::ih_bound`] is the set
//! `rec_acc` already chose for the purpose. Instantiating such an equation at
//! `c := ih(accrec,A,R,x)` is exactly this theorem.
//!
//! # `∅ ∈ T` is not needed, because **A4** is available
//!
//! The obvious derivation runs `preds_typed` off
//! [`super::rec_funspace`] — but that types `accrec` on `acc(A,R)`, while
//! `preds_typed` quantifies over predecessors in `A`. Closing that gap by
//! assuming `∅ ∈ T` (so that the off-domain value is typed) would put a second
//! hypothesis on every downstream theorem, and `T` is frequently a set with no
//! reason to contain `∅` — a skeleton `W`, for one.
//!
//! [`crate::acc::acc_pred_closed`] removes the need: an `A`-predecessor of an
//! **accessible** point is itself accessible, so the quantifier never leaves
//! `acc(A,R)` and `ST` alone suffices. That lemma was derived for this;
//! `INDEXED-DESIGN.md` §6.1's route to the §5.3 recursor is its only consumer
//! so far.
//!
//! The value is read off `accrec`'s *graph* rather than off
//! [`super::rec_funspace`]: [`super::totality`] gives `indom(accrec,y)`, and
//! then [`super::rec_subset_prod`] and [`super::rec_single_valued`] — both
//! **unconditional** — turn one member of the graph into `app(accrec,y) ∈ T`.
//! So `ST` is spent exactly once, on totality, which is what it was introduced
//! for.

use kernel::{Env, Formula, Term, Thm};

use crate::acc::acc_pred_closed;
use crate::wrec::hyp_eq_symm;
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};

use super::apparatus::RecAcc;
use super::shared::{gen_under, hyp_leibniz};

/// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → ih(accrec,A,R,x) ∈ ih_bound(A,T)))`.
///
/// Mints one fresh symbol, for the subset [`crate::acc::acc_rect`] runs **A4**'s
/// induction at.
///
/// Refuses a [`RecAcc`] carrying a hypothetical theorem: the statement above is
/// advertised with `ST` as its *only* antecedent and nothing in `hyps()`, and
/// five of the struct's fields are spent through [`Thm::mp`] and [`syl`], both
/// of which union the premises' `Γ`s.
pub fn ih_in_bound(env: &mut Env, ra: &RecAcc) -> Option<Thm> {
    if !ra.all_unconditional() {
        return None
    }
    let b = &ra.base;
    let (av, rv, tv, ev) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (xv, yv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tt, te) = (Term::var(av), Term::var(rv), Term::var(tv), Term::var(ev));
    let (tx, ty, tw) = (Term::var(xv), Term::var(yv), Term::var(wv));

    let acc_t = b.acc_of(&ta, &tr);
    let f = ra.of(ta.clone(), tr.clone(), tt.clone(), te.clone());
    let st = ra.step_typed(env, &ta, &tr, &tt, &te);
    let x_acc = Formula::mem(tx.clone(), acc_t.clone());

    // The four instances of `RecAcc`'s own theorems, once.
    let args = [ta.clone(), tr.clone(), tt.clone(), te.clone()];
    let tot = inst_all(&ra.totality, &args)?;
    let sub_prod = inst_all(&ra.rec_subset_prod, &args)?;
    let sv = inst_all(&ra.rec_single_valued, &args)?;
    let pc = acc_pred_closed(env, &b.ac)?;

    // ── H := ST ∧ x ∈ acc(A,R) ──────────────────────────────────────────────
    let h = Formula::and(st.clone(), x_acc.clone());
    let h_st = and_left(st.clone(), x_acc.clone());
    let h_xacc = and_right(st.clone(), x_acc.clone());

    // ── H₂ := (H ∧ y ∈ A) ∧ ⟨y,x⟩ ∈ R — left-nested, so `uncurry` unpacks it ─
    let y_in_a = Formula::mem(ty.clone(), ta.clone());
    let edge = Formula::mem(b.edge(&ty, &tx), tr.clone());
    let h1 = Formula::and(h.clone(), y_in_a.clone());
    let h2 = Formula::and(h1.clone(), edge.clone());
    let h2_h1 = and_left(h1.clone(), edge.clone());
    let h2_edge = and_right(h1.clone(), edge.clone());
    let h2_h = syl(&h2_h1, &and_left(h.clone(), y_in_a.clone()))?;
    let h2_ya = syl(&h2_h1, &and_right(h.clone(), y_in_a.clone()))?;
    let h2_st = syl(&h2_h, &h_st)?;
    let h2_xacc = syl(&h2_h, &h_xacc)?;

    // ── A4: the predecessor is itself accessible ────────────────────────────
    let pc_at = inst_all(&pc, &[ta.clone(), tr.clone(), ty.clone(), tx.clone()])?;
    let h2_guard = hyp_and(&h2_ya, &h2_edge)?;
    let h2_yacc = hyp_mp(&syl(&h2_xacc, &pc_at)?, &h2_guard)?;

    // ── totality: `y` is in `accrec`'s domain ───────────────────────────────
    let h2_all = syl(&h2_st, &tot)?;
    let (_, all_body) = h2_all.concl().as_imp()?;
    let at_y = Thm::ax_inst(all_body, ty.clone())?;
    let h2_indom = hyp_mp(&syl(&h2_all, &at_y)?, &h2_yacc)?;

    // ── H₃ := H₂ ∧ ⟨y,w⟩ ∈ accrec — one member of the graph ──────────────────
    let pair_yw = Formula::mem(b.s.ap.sets.pair(ty.clone(), tw.clone()), f.clone());
    let h3 = Formula::and(h2.clone(), pair_yw.clone());
    let h3_pair = and_right(h2.clone(), pair_yw.clone());

    // `app(accrec,y) = w`, by single-valuedness.
    let graph_at = inst_all(&b.app_of_graph, &[f.clone(), ty.clone(), tw.clone()])?;
    let h3_sv = a1i(&sv, h3.clone());
    let h3_eq = syl(&hyp_and(&h3_sv, &h3_pair)?, &graph_at)?;

    // `w ∈ T`, because the graph is inside `acc(A,R) × T`.
    let in_prod = inst_all(&sub_prod, &[b.s.ap.sets.pair(ty.clone(), tw.clone())])?;
    let h3_in_prod = syl(&h3_pair, &in_prod)?;
    let split = iff_mp(&inst_all(
        &b.s.pair_in_prod,
        &[acc_t.clone(), tt.clone(), ty.clone(), tw.clone()],
    )?)?;
    let h3_pair_split = syl(&h3_in_prod, &split)?;
    let h3_wt = syl(
        &h3_pair_split,
        &and_right(
            Formula::mem(ty.clone(), acc_t.clone()),
            Formula::mem(tw.clone(), tt.clone()),
        ),
    )?;

    // Transport `w ∈ T` back along `app(accrec,y) = w`.
    let back = hyp_eq_symm(env, &h3_eq)?;
    let tt_c = tt.clone();
    let carry = hyp_leibniz(env, &back, move |hole| Formula::mem(hole, tt_c.clone()))?;
    let h3_val = hyp_mp(&carry, &h3_wt)?;

    // ── discharge the witness, then close over `y` ──────────────────────────
    let h2_val = crate::wrec::hyp_exists_elim(wv, &h3_val, &h2_indom)?;
    let per_y = uncurry(&uncurry(&h2_val)?)?;
    let h_preds = gen_under(yv, &per_y)?;

    // ── and that is exactly `ih_typed`'s guard ──────────────────────────────
    let typed = inst_all(
        &b.ih_typed,
        &[f.clone(), ta.clone(), tr.clone(), tt.clone(), tx.clone()],
    )?;
    let (guard, want) = typed.concl().as_imp()?;
    if h_preds.concl().as_imp()?.1 != guard {
        return None
    }
    let h_bound = syl(&h_preds, &typed)?;

    let per_x = uncurry(&h_bound)?;
    let out = gen_under(xv, &per_x)?;
    if out.concl() != &Formula::imp(st, Formula::forall(xv, Formula::imp(x_acc, want))) {
        return None
    }
    Some(gen_all(&[av, rv, tv, ev], &out))
}
