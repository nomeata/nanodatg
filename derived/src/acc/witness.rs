//! Non-vacuity, in **both** polarities.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. ¬(⟨y,x⟩ ∈ R)) → x ∈ acc(A,R))       [acc_minimal]
//! ⊢ ∀A. acc(A,∅) = A                                     [acc_empty_relation]
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ¬(⟨z,z⟩ ∈ R))                    [acc_no_loops]
//! ⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) →
//!       ∀w. ¬(w ∈ A ∧ (⟨z,w⟩ ∈ R ∧ ⟨w,z⟩ ∈ R)))            [acc_no_two_cycle]
//! ```
//!
//! # Why both polarities are needed
//!
//! Every theorem in [`crate::acc`] is trivially true when `acc(A,R)` is empty,
//! so without a witness the module proves nothing at all. [`acc_minimal`] and
//! [`acc_empty_relation`] are that witness: at `R := ∅` the accessible set is
//! the whole of `A`.
//!
//! But there is a second, opposite way this development could have said
//! nothing. `acc(A,R) ⊆ A` is one of its theorems, so if `acc(A,R)` were
//! *always* `A` then [`crate::acc::acc_induction`] and
//! [`crate::acc::acc_rect`] would be true and useless, and the guard `x ∈ A` in
//! [`crate::acc::step_closed`] would be doing the damage described in that
//! module's header. [`acc_no_loops`] rules that out: **no `R`-reflexive point
//! is accessible**, so for any `A` containing a point `x` with `⟨x,x⟩ ∈ R` the
//! inclusion `acc(A,R) ⊆ A` is strict. `tests/acc.rs` exhibits such an `A` and
//! `R` concretely. [`acc_no_two_cycle`] strengthens that: even an *irreflexive*
//! `R` can leave points inaccessible, so the exclusion is about well-foundedness
//! and not about loops at a point.
//!
//! [`acc_no_loops`] is also the first real use of [`crate::acc::acc_rect`], and
//! the cheapest available check that the scheme's induction hypothesis is
//! strong enough: the proof instantiates it at `y := x`, which is possible only
//! because the hypothesis ranges over all `R`-predecessors rather than over
//! some structurally smaller notion.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::err::{DResult, Operand};
use crate::prim::{self, Shape};
use crate::rules::{com12, hyp_and, hyp_mp, imp_mono_r, inst_all, syl, uncurry};
use crate::{a1i, and_intro, and_left, and_right, assembly, decline, ex_falso, gen_all, imp_refl, opair};

use super::apparatus::Acc;
use super::rect::{acc_rect, Params};
use super::shared::hyp_inst_mp;

/// `⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. ¬(⟨y,x⟩ ∈ R)) → x ∈ acc(A,R))` — every
/// `R`-minimal point of `A` is accessible.
///
/// [`crate::acc::acc_intro`] with its induction hypothesis discharged
/// vacuously: if nothing bears `R` to `x` then "every `R`-predecessor of `x` in
/// `A` is accessible" holds by [`crate::ex_falso`], and the rule applies.
///
/// This is the base case of accessibility, and it is where members of `acc`
/// come from at all.
///
/// **The whole consequent comes from `acc_intro`**, so `acc_intro` is checked
/// twice over. It must be unconditional, or the `Γ` behind "every minimal point
/// is accessible" would be invisible; and the final shape is compared in
/// *release* as well as debug, because the consequent `x ∈ acc(A,R)` is the
/// claim this function's name makes — it is read off the caller's theorem by
/// [`syl`] and nothing else forces it. A `debug_assert` alone leaves the
/// release measurement path (`scripts/arena.sh`, `stepcount`,
/// `cargo build --release`) relabelling an arbitrary
/// `∀A ∀R ∀x. ((x ∈ A ∧ preds) → C(A,R,x))` as this witness.
pub fn acc_minimal(env: &mut Env, up: FnSym, acc: FnSym, acc_intro: &Thm) -> DResult<Thm> {
    if !acc_intro.hyps().is_empty() {
        return Err(decline!("the introduction rule carries hypotheses, so it does not establish what its header claims"))
    }
    let (av, rv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx) = (Term::var(av), Term::var(rv), Term::var(xv));
    let acc_t = Term::apply(acc, vec![ta.clone(), tr.clone()]);

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let mem_ya = Formula::mem(ty.clone(), ta.clone());
    let mem_pair = Formula::mem(opair(up, ty.clone(), tx.clone()), tr.clone());
    let mem_yacc = Formula::mem(ty.clone(), acc_t.clone());

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let nopred = Formula::forall(yv, Formula::not(mem_pair.clone()));
    let h = Formula::and(mem_xa.clone(), nopred.clone());
    let h_xa = and_left(mem_xa.clone(), nopred.clone());
    let h_np = and_right(mem_xa, nopred);

    // `H → (⟨y,x⟩ ∈ R → y ∈ acc)`, the implication holding because its
    // antecedent is refutable.
    let np_at_y = prim::ax_inst(h_np.concl().imp_parts()?.1, ty.clone())?;
    let h_ny = syl(&h_np, &np_at_y)?;
    let h_yacc = syl(&h_ny, &imp_mono_r(&ex_falso(mem_yacc.clone()), mem_pair.clone())?)?;

    // Weaken to `H → (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc))` and generalise.
    let tail = Formula::imp(mem_pair, mem_yacc);
    let weaken = com12(&a1i(&imp_refl(tail.clone()), mem_ya.clone()))?;
    let inner = Formula::imp(mem_ya, tail);
    let h_preds = prim::mp(
        &prim::ax_dist(yv, h.clone(), inner)?,
        &Thm::gen(yv, &syl(&h_yacc, &weaken)?),
    )?;

    let intro_at = inst_all(acc_intro, &[ta, tr, tx.clone()])?;
    let out = syl(&hyp_and(&h_xa, &h_preds)?, &intro_at)?;
    // Release, not `debug_assert`: this pins the *claim*. See the header.
    if *out.concl() != Formula::imp(h, Formula::mem(tx, acc_t)) {
        return Err(decline!("the introduction rule is not the one acc_intro states, so the witness would be a relabelling"))
    }
    Ok(gen_all(&[av, rv, xv], &out))
}

/// `⊢ ∀A. acc(A,∅) = A` — the accessible part of the empty relation is
/// everything.
///
/// The two inclusions are [`crate::acc::acc_subset`] and [`acc_minimal`] at
/// `R := ∅`, whose side condition `∀y. ¬(⟨y,x⟩ ∈ ∅)` is the empty set's own
/// axiom. Extensionality turns them into an equation.
///
/// This is the sharpest available statement that the module is not vacuous:
/// `acc` is not merely inhabited at some contrived instance, it is *all of `A`*
/// for every `A`, at a relation that always exists.
///
/// All three premises must be **unconditional**. The two inclusions are pinned
/// below, and the final equation is forced by [`Thm::ax_extensionality`], so the
/// conclusion cannot be relabelled — but nothing in the kernel stops a `Γ` from
/// riding through the [`syl`] chain, and this theorem is the one a caller reads
/// as "the development did not come out empty". A conditional one would say
/// nothing of the kind.
pub fn acc_empty_relation(
    env: &mut Env,
    up: FnSym,
    empty: FnSym,
    empty_ax: &Thm,
    acc: FnSym,
    acc_subset: &Thm,
    minimal: &Thm,
) -> DResult<Thm> {
    if !crate::all_unconditional(&[empty_ax, acc_subset, minimal]) {
        return Err(decline!("the empty-set axiom, the subset lemma or the minimality witness carries hypotheses"))
    }
    let (av, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tx, ty) = (Term::var(av), Term::var(xv), Term::var(yv));
    let e = Term::apply(empty, vec![]);
    let acc_e = Term::apply(acc, vec![ta.clone(), e.clone()]);
    let mem_xa = Formula::mem(tx.clone(), ta.clone());

    let fwd = inst_all(acc_subset, &[ta.clone(), e.clone(), tx.clone()])?;
    if *fwd.concl() != Formula::imp(Formula::mem(tx.clone(), acc_e.clone()), mem_xa.clone()) {
        return Err(decline!("the subset lemma does not put a member of acc in the carrier"))
    }

    // `∀y. ¬(⟨y,x⟩ ∈ ∅)`, straight from the empty set's axiom.
    let nopred = Thm::gen(yv, &inst_all(empty_ax, &[opair(up, ty, tx.clone())])?);
    let min_at = inst_all(minimal, &[ta.clone(), e, tx.clone()])?;
    let bwd = syl(
        &hyp_and(&imp_refl(mem_xa.clone()), &a1i(&nopred, mem_xa.clone()))?,
        &min_at,
    )?;
    if *bwd.concl() != Formula::imp(mem_xa, Formula::mem(tx, acc_e.clone())) {
        return Err(decline!("the minimality witness does not put a member of the carrier in acc over the empty relation"))
    }

    let same = Thm::gen(xv, &and_intro(&fwd, &bwd));
    let ext_at = inst_all(&Thm::ax_extensionality(env), &[acc_e.clone(), ta.clone()])?;
    let out = prim::mp(&ext_at, &same)?;
    debug_assert_eq!(*out.concl(), Formula::eq(acc_e, ta), "acc_empty_relation: unexpected shape");
    Ok(gen_all(&[av], &out))
}

/// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ¬(⟨z,z⟩ ∈ R))` — **no accessible point is
/// `R`-reflexive**.
///
/// Equivalently, by contraposition: a point `x` with `⟨x,x⟩ ∈ R` is never in
/// `acc(A,R)`, however large `A` is. This is [`crate::acc::acc_rect`] at
///
/// ```text
/// φ(z) := ¬(⟨z,z⟩ ∈ R)
/// ```
///
/// and the minor premise is a two-line argument with no equality reasoning in
/// it: given `x ∈ A` and `⟨x,x⟩ ∈ R`, the induction hypothesis applies **at
/// `y := x`**, since `x` is then one of its own `R`-predecessors, and yields
/// `¬(⟨x,x⟩ ∈ R)` — a contradiction.
///
/// Mints one fresh symbol, for the subset `acc_rect` runs the induction at.
///
/// Takes no theorem of its own: everything it spends comes out of `ac`, and
/// [`acc_rect`] refuses an [`Acc`] carrying a hypothetical theorem before a
/// single step is taken — see [`Acc::all_unconditional`]. The two shape checks
/// below (and the corresponding one in [`acc_no_two_cycle`]) compare the
/// rebuilt minor premise with the scheme's own antecedent, so the theorem fired
/// is the theorem read.
pub fn acc_no_loops(env: &mut Env, ac: &Acc) -> DResult<Thm> {
    let (av, rv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz) = (Term::var(av), Term::var(rv), Term::var(zv));
    let acc_t = ac.of(ta.clone(), tr.clone());

    let phi = Formula::not(Formula::mem(ac.edge(tz.clone(), tz), tr.clone()));
    let rect = acc_rect(env, ac, &[av, rv], Params { a: av, r: rv }, zv, &phi)?;

    // Read the minor premise off the scheme rather than rebuilding it.
    let (ih, _) = rect.concl().imp_parts()?;
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let (_, body) = prim::ax_inst(ih.clone(), tx.clone())?.concl().imp_parts()?;
    let (mem_xa, rest) = body.imp_parts()?;
    let (ihyp, phi_x) = rest.imp_parts()?;
    let (mem_rxx, _) = phi_x.imp_parts()?;

    // Under `N := (x ∈ A ∧ ihyp) ∧ ⟨x,x⟩ ∈ R`, derive `⊥`.
    let front = Formula::and(mem_xa.clone(), ihyp.clone());
    let n_front = and_left(front.clone(), mem_rxx.clone());
    let n_xa = syl(&n_front, &and_left(mem_xa.clone(), ihyp.clone()))?;
    let n_ih = syl(&n_front, &and_right(mem_xa, ihyp.clone()))?;
    let n_rxx = and_right(front, mem_rxx);

    let ihyp_at_x = prim::ax_inst(ihyp, tx)?;
    let n_conj = hyp_mp(&hyp_mp(&syl(&n_ih, &ihyp_at_x)?, &n_xa)?, &n_rxx)?;
    let n_phix = syl(&n_conj, &and_right(Formula::mem(Term::var(xv), acc_t), phi_x))?;
    let n_false = hyp_mp(&n_phix, &n_rxx)?;

    let minor = Thm::gen(xv, &uncurry(&uncurry(&n_false)?)?);
    if *minor.concl() != ih {
        return Err(assembly!("acc_no_loops: the assembled minor premise is not the induction hypothesis", Operand::thm("minor", &minor)))
    }
    let out = prim::mp(&rect, &minor)?;
    Ok(gen_all(&[av, rv], &out))
}

/// `⊢ ∀A ∀R ∀z. (z ∈ acc(A,R) → ∀w. ¬(w ∈ A ∧ (⟨z,w⟩ ∈ R ∧ ⟨w,z⟩ ∈ R)))` —
/// **no accessible point sits on a 2-cycle through `A`**.
///
/// The strengthening of [`acc_no_loops`] that shows its content is not an
/// artefact of reflexivity: a relation can be irreflexive and still have
/// nothing accessible on it. [`crate::acc::acc_rect`] at
///
/// ```text
/// φ(z) := ∀w. ¬(w ∈ A ∧ (⟨z,w⟩ ∈ R ∧ ⟨w,z⟩ ∈ R))
/// ```
///
/// Given `u ∈ A` on a cycle with some `p`, the induction hypothesis applies at
/// `y := p` — legitimate because `⟨p,u⟩ ∈ R` and, crucially, `p ∈ A` is part of
/// the cycle being assumed. It yields `φ(p)`, which instantiated at `w := u`
/// denies the very same cycle.
///
/// **Why this is not folded into [`acc_no_loops`].** `acc_no_loops` is the case
/// `w := z` of this theorem, modulo [`crate::acc::acc_subset`] to supply
/// `z ∈ A`, so one could be derived from the other. They are kept separate
/// because they instantiate [`crate::acc::acc_rect`] at
/// structurally different `φ` — atomic there, quantified here — and the
/// quantified case is the one that exercises `separation_full` and
/// `define_by_membership` on a condition with a bound variable of its own.
/// Two independent instances check the scheme; one instance plus a corollary
/// would not.
///
/// **The `w ∈ A` conjunct cannot be dropped, and not merely because the proof
/// would break.** The unguarded statement is *false*. Take `A := {a}` and
/// `R := {⟨a,b⟩, ⟨b,a⟩}` with `b ∉ A`. Then `preds_in(A,R,C,a)` quantifies only
/// over `y ∈ A`, i.e. over `y = a`, and `⟨a,a⟩ ∉ R`, so it holds vacuously and
/// [`crate::acc::acc_intro`] puts `a` into `acc(A,R)` — yet `a` lies on a
/// 2-cycle with `b`. `acc(A,R)` is accessibility *relative to `A`*, and says
/// nothing about `R`-edges leaving it.
pub fn acc_no_two_cycle(env: &mut Env, ac: &Acc) -> DResult<Thm> {
    let (av, rv, zv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tz, tw) = (Term::var(av), Term::var(rv), Term::var(zv), Term::var(wv));
    let acc_t = ac.of(ta.clone(), tr.clone());

    // `b ∈ A ∧ (⟨a,b⟩ ∈ R ∧ ⟨b,a⟩ ∈ R)` — "`a` and `b` lie on a 2-cycle in `A`".
    let cycle = |a: &Term, b: &Term| {
        Formula::and(
            Formula::mem(b.clone(), ta.clone()),
            Formula::and(
                Formula::mem(ac.edge(a.clone(), b.clone()), tr.clone()),
                Formula::mem(ac.edge(b.clone(), a.clone()), tr.clone()),
            ),
        )
    };
    let phi = Formula::forall(wv, Formula::not(cycle(&tz, &tw)));
    let rect = acc_rect(env, ac, &[av, rv], Params { a: av, r: rv }, zv, &phi)?;

    // Read the minor premise off the scheme rather than rebuilding it.
    let (ih, _) = rect.concl().imp_parts()?;
    let (uv, pv) = (env.fresh_var(), env.fresh_var());
    let (tu, tp) = (Term::var(uv), Term::var(pv));
    let (_, body) = prim::ax_inst(ih.clone(), tu.clone())?.concl().imp_parts()?;
    let (mem_ua, rest) = body.imp_parts()?;
    let (ihyp, phi_u) = rest.imp_parts()?;

    // Under `N := (u ∈ A ∧ ihyp) ∧ cycle(u,p)`, derive `⊥`.
    let cyc_up = cycle(&tu, &tp);
    let front = Formula::and(mem_ua.clone(), ihyp.clone());
    let n_front = and_left(front.clone(), cyc_up.clone());
    let n_ua = syl(&n_front, &and_left(mem_ua.clone(), ihyp.clone()))?;
    let n_ih = syl(&n_front, &and_right(mem_ua, ihyp.clone()))?;
    let n_cyc = and_right(front.clone(), cyc_up.clone());

    let e_up = Formula::mem(ac.edge(tu.clone(), tp.clone()), tr.clone());
    let e_pu = Formula::mem(ac.edge(tp.clone(), tu.clone()), tr.clone());
    let edges = Formula::and(e_up.clone(), e_pu.clone());
    let mem_pa = Formula::mem(tp.clone(), ta);
    let n_pa = syl(&n_cyc, &and_left(mem_pa.clone(), edges.clone()))?;
    let n_edges = syl(&n_cyc, &and_right(mem_pa, edges))?;
    let n_up = syl(&n_edges, &and_left(e_up.clone(), e_pu.clone()))?;
    let n_pu = syl(&n_edges, &and_right(e_up, e_pu))?;

    // The induction hypothesis at `p`, whose `φ(p)` denies the cycle at `w := u`.
    let n_both = hyp_mp(&hyp_mp(&syl(&n_ih, &prim::ax_inst(ihyp, tp.clone())?)?, &n_pa)?, &n_pu)?;
    let n_phi_p = syl(
        &n_both,
        &and_right(Formula::mem(tp, acc_t), phi.subst(zv, &Term::var(pv))),
    )?;
    let n_false =
        hyp_inst_mp(&n_phi_p, &tu, &hyp_and(&n_ua, &hyp_and(&n_pu, &n_up)?)?)?;

    let all_p = prim::mp(
        &prim::ax_dist(pv, front.clone(), Formula::not(cyc_up))?,
        &Thm::gen(pv, &uncurry(&n_false)?),
    )?;
    if *all_p.concl() != Formula::imp(front, phi_u) {
        return Err(assembly!("acc_no_two_cycle: the distributed step does not conclude the cycle is refuted", Operand::thm("all_p", &all_p)))
    }
    let minor = Thm::gen(uv, &uncurry(&all_p)?);
    if *minor.concl() != ih {
        return Err(assembly!("acc_no_two_cycle: the assembled minor premise is not the induction hypothesis", Operand::thm("minor", &minor)))
    }
    Ok(gen_all(&[av, rv], &prim::mp(&rect, &minor)?))
}
