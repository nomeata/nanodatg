//! **Each field type of a class-(P) structure is inhabited by the point** —
//! [`super::le_prop_fields`]'s statement with the major premise swapped.
//!
//! # What this closes
//!
//! `⟦projⱼ x⟧` is `•` for a projection out of a proposition, so a checker's
//! obligation is `⊢ • ∈ βⱼ(p⃗, •⃗<ⱼ)` — and that does **not** follow from
//! `βⱼ ⊆ 1`, which is satisfied by the empty set. Inhabitation is extra
//! information and it comes from the major premise.
//!
//! For a class-(S) structure that premise is [`LeProp::elim`](super::le_prop),
//! whose conclusion ψ *is* a disjunction of field existentials, and
//! [`super::le_prop_fields`] collapses it. A class-(P) structure has no `A_φ`
//! and no ψ: its carrier is `‖ind(p⃗)‖` and all the major premise gives is
//! [`TruncCarrier::elim`], `⊢ • ∈ ‖ind(p⃗)‖ → ∃w. w ∈ ind(p⃗)` — *some* element
//! exists, with nothing said about its shape. Recovering the fields from that
//! is this file, and it is one step longer than its sibling.
//!
//! # The missing ψ is one induction, and that is the whole difference
//!
//! [`TruncFields::elim_psi`] is the class-(P) analogue of
//! [`LeProp::elim`](super::le_prop):
//!
//! ```text
//! ψ := ∃y₀ … ∃y_{k-1}. ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)
//!
//! ⊢ ∀p⃗. ( • ∈ ‖ind(p⃗)‖ → ψ )                       [TruncFields::elim_psi]
//! ```
//!
//! and it is [`decl_rect`] at that ψ, which is **constant in the induction
//! variable**. So the induction step is `∀y⃗. (⋀ⱼ yⱼ ∈ βⱼ → ψ)` — one
//! existential introduction per field and nothing else — and the two ends are
//! [`TruncCarrier::elim`] and [`Inductive::ty_ax`], exactly as
//! [`super::trunc_rec`]'s are and for the same reason: the truncation threw the
//! member away, so anything about it has to go back to the thing truncated.
//!
//! Calling that "the carrier's inversion" is right in spirit and wrong in
//! name. There is no inversion theorem for a non-indexed carrier; structural
//! induction at a constant `φ` *is* the inversion, and saying so is worth the
//! one [`crate::wtype::w_rect`] Separation it costs — the only one in this file,
//! and the only thing [`super::le_prop_fields`] does not pay.
//!
//! Once ψ is in hand the collapse is its sibling's, verbatim in structure: each
//! `yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)` with `βⱼ ⊆ 1` gives `yⱼ = •`, and the equations already
//! produced rewrite the *next* field type's argument list, leftmost first.
//!
//! # Interface
//!
//! With `p⃗` the declaration's own parameter variables and `•⃗<ⱼ` for `j` copies
//! of the point:
//!
//! ```text
//! Pⱼ  :=  βⱼ(p⃗, •⃗<ⱼ) ⊆ 1                             [TruncFields::subsets]
//! Hⱼ  :=  • ∈ βⱼ(p⃗, •⃗<ⱼ)                         [TruncFields::memberships]
//!
//! ⊢ ∀p⃗. ( • ∈ ‖ind(p⃗)‖ → ψ )                        [TruncFields::elim_psi]
//! ⊢ ∀p⃗. ( • ∈ ‖ind(p⃗)‖ → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)) )     [steps[j]]
//! ⊢ ∀p⃗. ( • ∈ ‖ind(p⃗)‖ → ((P₀ ∧ … ∧ P_{k-1}) → (H₀ ∧ … ∧ H_{k-1})) )
//!                                                   [TruncFields::inhabited]
//! ```
//!
//! All unconditional; `steps` is empty and the other two are `None` exactly at
//! `k = 0`, where `P⃗` and `H⃗` are the empty conjunction this kernel cannot
//! spell. [`TruncFields::is_present`] is the one-line test on the spec.
//! `steps[k-1]` *is* `inhabited`.
//!
//! **The ladder is not decoration here — it is what the corpus needs.**
//! [`super::le_prop_fields`]'s header argues for it from a hypothetical
//! dependent field type; on this side the argument is `086_projProp3`, below.
//!
//! There is no `guard` field. Its sibling has one because
//! [`super::le_prop_rec::LePropRecursor`]'s antecedent is `P⃗ ++ H⃗` conjunct for
//! conjunct; class (P)'s recursor
//! ([`super::trunc_rec::TruncRecursor`]) has no antecedent of that shape, so a
//! `guard` here would be an export with no consumer.
//!
//! # Scope: every index, and the boundary is not this theorem's
//!
//! **The theorem covers every field index**, `j = 0 … k-1`, each conditionally
//! on `P₀ … Pⱼ` and nothing else. It has **no guard for a non-`Prop` field**,
//! and that is deliberate rather than an omission — `Pⱼ` *is* the condition, and
//! a field whose type is not a subset of `1` makes its own hypothesis
//! undischargeable without anything here having to notice.
//!
//! A guard would also be **wrong**, which is the part worth writing down.
//! `PropStructure` (`084`–`089`) has six fields:
//!
//! | j | field | type | projection |
//! |---:|---|---|---|
//! | 0 | `aProof` | `PUnit` at `Sort 0` | `084`, **good** |
//! | 1 | `someData` | `PUnit` at `Sort 1` | `085`, bad |
//! | 2 | `aSecondProof` | `PUnit` at `Sort 0` | `086`, **good** |
//! | 3 | `someMoreData` | `PUnit` at `Sort 1` | `087`, `088`, bad |
//! | 4 | `aProofAboutData` | `Eq PUnit _ _` | `088`, bad |
//! | 5 | `aFinalProof` | `PUnit` at `Sort 0` | `089`, bad |
//!
//! — read off the exports, not inferred: `084` and `086` are the two in
//! `good/tutorial/`, the other four are in `bad/tutorial/`, and `infer_proj`
//! refuses the data fields (`kernel.rs:1985`) and anything whose type depends on
//! one (`:1973`). **`086` is legal and projects index 2, so it needs `P₀ ∧ P₁ ∧
//! P₂` — and `P₁` is the *data* field's.** It is discharegable: `PUnit` at
//! `Sort 1` interprets to a singleton, so `⟦PUnit.{1}⟧ ⊆ 1` is simply true. A
//! `derived/`-side guard reading "every field is a `Prop`" would refuse a
//! declaration the checker accepts.
//!
//! So `⊆ 1` is *strictly weaker* than "is a `Prop`", it is exactly what the
//! derivation consumes, and the numbering gap `085`/`087`/`088`/`089` is
//! `infer_proj`'s boundary and not this theorem's. Every index here is
//! set-theoretically fine, including the four the checker rejects; what makes
//! those projections meaningless is a fact about `Sort`s, which this layer does
//! not see and should not restate.
//!
//! # What is refused, and by what
//!
//! The same three [`super::le_prop_fields`] refuses — indices, a constructor
//! count other than one, and a recursive field — and no structure Lean will
//! project out of is any of them. With two constructors the statement would be
//! **false**: `• ∈ ‖ind(p⃗)‖` says only that *some* constructor's fields are
//! inhabited, which pins nothing about constructor 0's.
//!
//! **None of the three has a guard**, and that is a result rather than an
//! oversight. Guards for all three were written, and a mutation run deleting
//! each in turn failed no test; each is subsumed by a statement comparison that
//! is there for its own reasons and is the stronger check. An indexed or
//! foreign truncation fails the shape check on [`TruncCarrier::elim`], whose
//! conclusion is compared against `∃w. w ∈ ind(p⃗)` rebuilt from `ind`; two
//! constructors fail `parts.len() != 1`; a recursive field fails the
//! `establishes` against `rect_parts`, because `rect_step₀` then carries
//! `tⱼ ∈ W` and `ψ(tⱼ)` atoms the existential fold does not produce. All three
//! refusals are tested — see `derived/tests/family_trunc_fields.rs` — so they
//! are behaviour and not merely code that is never reached.
//!
//! **A warning for the next reader with a mutation script.** Deleting any *one*
//! of those three comparisons also fails no test, and that is not evidence that
//! it is dead. Instrumenting the three bad inputs shows each is the **first**
//! refuser for exactly one of them — `parts.len()` for two constructors,
//! `establishes(&step, &parts[0])` for a recursive field, `tc.elim`'s shape for
//! an indexed or foreign truncation — and the survivors plus the downstream
//! `Thm::mp` against `decl_rect`'s antecedent catch whichever one is removed.
//! The net is deep because the construction refuses rather than lies. What made
//! the four deleted guards different is that they were a *second* layer doing
//! the same job one step earlier, by provenance rather than by statement.
//!
//! [`TruncFields::is_present`] is a different thing and stays: it is a question
//! about the *spec*, answered before any theorem is built, and a consumer reads
//! it rather than pattern-matching on an `Option` it might mistake for a
//! failure.
//!
//! # Nothing here is an axiom
//!
//! One [`decl_rect`] — one Separation — and then no symbol, no second
//! Separation: `k` uses of [`crate::sums::unit_eta`], one Leibniz per
//! dependency, and the existential fold.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{carry_under, hyp_conj, hyp_ex_branch, rewrite_under};
use crate::inductive::rect::{decl_rect, rect_parts};
use crate::inductive::DeclSpec;
use crate::{
    and_left, and_right, conj_of, conj_proj, curry, exists_intro_imp, gen_all, hyp_mp, imp_refl,
    inst_all, syl, uncurry,
};

use super::trunc::TruncCarrier;

/// A class-(P) structure's fields, shown inhabited by the point.
pub struct TruncFields {
    /// `Pⱼ = βⱼ(p⃗, •⃗<ⱼ) ⊆ 1`, one per field in declared order — spelled here
    /// so a consumer discharges the *same* formulas the theorems carry rather
    /// than rebuilding a `subset` with its own fresh binder.
    pub subsets: Vec<Formula>,
    /// `Hⱼ = • ∈ βⱼ(p⃗, •⃗<ⱼ)`, one per field in declared order.
    pub memberships: Vec<Formula>,
    /// `⊢ ∀p⃗. (• ∈ ‖ind(p⃗)‖ → ψ)` — the class-(P) analogue of
    /// [`LeProp::elim`](super::le_prop::LeProp::elim), and the only thing in
    /// this file that costs a Separation. `None` exactly at `k = 0`, where ψ's
    /// matrix is the empty conjunction.
    pub elim_psi: Option<Thm>,
    /// **The ladder.** `steps[j]` is
    /// `⊢ ∀p⃗. (• ∈ ‖ind(p⃗)‖ → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)))` — the `j`-th
    /// prefix, needing the `Pᵢ` for `i ≤ j` and **no others**. Empty at `k = 0`,
    /// and `steps[k-1]` is [`TruncFields::inhabited`] on the nose.
    ///
    /// This is the field `086_projProp3` consumes: it projects index 2, so it
    /// needs `steps[2]`, and the bundle would demand `P₃ … P₅` it has no reason
    /// to hold.
    pub steps: Vec<Thm>,
    /// `⊢ ∀p⃗. (• ∈ ‖ind(p⃗)‖ → (⋀ⱼ Pⱼ → ⋀ⱼ Hⱼ))`. `None` exactly at `k = 0`.
    pub inhabited: Option<Thm>,
}

impl TruncFields {
    /// Derive the field inhabitations from the truncated major premise.
    ///
    /// `tc` must be [`TruncCarrier::over_declaration`] at this `ind` — checked
    /// on its `base`, and on the *statement* of the one theorem this spends.
    ///
    /// `None` on an indexed `tc`, on a declaration without exactly one
    /// constructor, on one whose constructor has a recursive field, on a
    /// foreign apparatus, and on any internal shape check. At `k = 0` it
    /// returns a value whose three theorems are `None`; see the header.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        tc: &TruncCarrier,
    ) -> Option<TruncFields> {
        // **Four guards were written here and deleted**, because a mutation run
        // removed each in turn and failed nothing: `tc.xvs.is_empty()`,
        // `tc.base == ind.carrier`, `ctors.len() == 1` and `c.recs == 0`. Every
        // one is subsumed by a *statement* comparison further down, which is
        // the better check anyway — it pins what a theorem says rather than
        // where it came from:
        //
        // * an indexed or foreign `tc` fails the shape check on `tc.elim`,
        //   whose conclusion is compared against `∃w. w ∈ ind(p⃗)` rebuilt here;
        // * two constructors fail `parts.len() != 1`, which is the honest
        //   statement of what this derivation handles — one induction step;
        // * a recursive field fails `establishes(&step, &parts[0])`, because
        //   `rect_step₀` then carries `tⱼ ∈ W` and `ψ(tⱼ)` atoms the existential
        //   fold does not produce.
        //
        // The one kept is the apparatus identity, which nothing below re-checks.
        if !ind.is_over(mach) || ind.spec.ctors.is_empty() {
            return None
        }
        let c = &ind.spec.ctors[0];
        if !crate::all_unconditional(&[&tc.elim, &ind.ty_ax]) {
            return None
        }
        let s = mach.wt.sums.clone();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let (point, unit) = (s.point(), s.unit());
        let k = c.args.len();
        let pts = vec![point.clone(); k];

        let subsets: Vec<Formula> = (0..k)
            .map(|j| {
                let b = beta(&ind.spec, &ps, &pts, j).expect("j is in range");
                kernel::thm::subset(env, b, unit.clone())
            })
            .collect();
        let memberships = typings(&ind.spec, &ps, &pts);

        let (p_conj, chi) = match (conj_of(&subsets), conj_of(&memberships)) {
            (Some(p), Some(h)) => (p, h),
            // `k = 0`: nothing to be inhabited, and the empty conjunction is
            // not a formula this kernel has.
            _ => {
                return Some(TruncFields {
                    subsets,
                    memberships,
                    elim_psi: None,
                    steps: Vec::new(),
                    inhabited: None,
                })
            }
        };

        // ── ψ, and the induction that produces it ───────────────────────────
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let body_atoms = typings(&ind.spec, &ps, &ys);
        let body = conj_of(&body_atoms)?;
        // Plain folding is capture-free here, and the reason is worth naming
        // because the sibling construction in `le.rs` was not: every occurrence
        // of `yⱼ` is *under* the binder being introduced — the subject of its
        // own typing atom — so there is no fixed term outside the quantifier
        // mentioning it. `le.rs`'s index tuple was exactly that fixed term.
        let psi = yvs.iter().rev().fold(body.clone(), |acc, v| Formula::exists(*v, acc));

        let zv = env.fresh_var();
        let parts = rect_parts(env, mach, ind, zv, &psi)?;
        if parts.len() != 1 {
            return None
        }
        // `rect_step₀(ψ)` at a non-recursive constructor is
        // `∀y⃗. (⋀ⱼ yⱼ ∈ βⱼ → ψ)`: ψ is constant in `z`, so the conclusion
        // `ψ(ctor₀(y⃗))` is ψ, and the antecedent is the field typings alone.
        let mut step = imp_refl(body.clone());
        for pos in (0..k).rev() {
            let inner = yvs[pos + 1..].iter().rev().fold(body.clone(), |a, v| Formula::exists(*v, a));
            step = syl(&step, &exists_intro_imp(yvs[pos], inner, ys[pos].clone())?)?;
        }
        let step = gen_all(&yvs, &step);
        if !crate::establishes(&step, &parts[0]) {
            return None
        }
        let all_w = Thm::mp(&decl_rect(env, mach, ind, zv, &psi)?, &step)?;

        // ── the two ends: `elim`, then the witness discharged into `W` ──────
        let mem_h = Formula::mem(point.clone(), tc.carrier.clone());
        let elim = inst_all(&tc.elim, &ps)?;
        let wv = env.fresh_var();
        let tw = Term::var(wv);
        let ex_of = |a: Term| Formula::exists(wv, Formula::mem(Term::var(wv), a));
        if *elim.concl() != Formula::imp(mem_h.clone(), ex_of(ind.carrier.clone())) {
            return None
        }
        let to_w = inst_all(&ind.ty_ax, &ps)?;
        let h_ex = carry_under(env, &to_w, ex_of, &elim)?;

        let mem_w = Formula::mem(tw.clone(), ind.wty.clone());
        let k3 = Formula::and(mem_h.clone(), mem_w.clone());
        let at_w = syl(
            &and_right(mem_h.clone(), mem_w),
            &inst_all(&all_w, std::slice::from_ref(&tw))?,
        )?;
        if *at_w.concl() != Formula::imp(k3, psi.clone()) {
            return None
        }
        let elim_psi = hyp_mp(&hyp_ex_branch(wv, &at_w, &mem_h, &psi)?, &h_ex)?;
        if !crate::establishes(&elim_psi, &Formula::imp(mem_h.clone(), psi.clone())) {
            return None
        }

        // ── the prefix ladder, one independent pass each ────────────────────
        let cx = Fold {
            spec: &ind.spec,
            elim: &elim_psi,
            mem_h: &mem_h,

            unit_eta: &s.unit_eta,
            ps: &ps,
            pts: &pts,
            ys: &ys,
            yvs: &yvs,
            body: &body,
            body_atoms: &body_atoms,
            subsets: &subsets,
            memberships: &memberships,
        };
        let steps: Vec<Thm> = (0..k)
            .map(|j| Some(gen_all(&ind.params, &inhabited_upto(env, &cx, j)?)))
            .collect::<Option<_>>()?;

        let inhabited = inhabited_upto(env, &cx, k - 1)?;
        if !crate::establishes(&inhabited, &Formula::imp(mem_h, Formula::imp(p_conj, chi))) {
            return None
        }

        let out = TruncFields {
            subsets,
            memberships,
            elim_psi: Some(gen_all(&ind.params, &elim_psi)),
            steps,
            inhabited: Some(gen_all(&ind.params, &inhabited)),
        };
        out.all_unconditional().then_some(out)
    }

    /// Whether the theorems above exist — `Some(k > 0)`, where `k` is the
    /// single constructor's field count. `None` when `spec` is not one this
    /// construction is about.
    ///
    /// A question about the *spec*, decided before any theorem is built, for
    /// the reason [`super::LeCarrier::intro_is_conditional`] is.
    pub fn is_present(spec: &DeclSpec) -> Option<bool> {
        if spec.ctors.len() != 1 || spec.ctors[0].recs != 0 {
            return None
        }
        Some(!spec.ctors[0].args.is_empty())
    }

    /// Whether every theorem here rests on nothing. Checked on the way out.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(
            &self
                .elim_psi
                .iter()
                .chain(self.inhabited.iter())
                .chain(self.steps.iter())
                .collect::<Vec<_>>(),
        )
    }
}

/// Everything [`inhabited_upto`] reads, gathered once. Private.
struct Fold<'a> {
    spec: &'a DeclSpec,
    /// [`TruncFields::elim_psi`] at the working variables, `⊢ • ∈ ‖ind(p⃗)‖ → ψ`.
    elim: &'a Thm,
    mem_h: &'a Formula,
    unit_eta: &'a Thm,
    ps: &'a [Term],
    /// `k` copies of the point.
    pts: &'a [Term],
    /// ψ's witness variables, as terms and as variables.
    ys: &'a [Term],
    yvs: &'a [FreeVar],
    /// ψ's matrix, and its conjuncts.
    body: &'a Formula,
    body_atoms: &'a [Formula],
    subsets: &'a [Formula],
    memberships: &'a [Formula],
}

/// **`⊢ • ∈ ‖ind(p⃗)‖ → ((P₀ ∧ … ∧ P_upto) → (H₀ ∧ … ∧ H_upto))`** — the fold,
/// run as far as `upto` and no further.
///
/// A function of the prefix length for the reason
/// [`super::le_prop_fields`]'s is: the statement at `upto` has a strictly
/// weaker hypothesis than the statement at `k-1`, so it is not a projection out
/// of it. The passes share nothing, which is what makes `steps[k-1] ==
/// inhabited` a fact about the derivation rather than a promise.
fn inhabited_upto(env: &mut Env, cx: &Fold<'_>, upto: usize) -> Option<Thm> {
    let m = upto + 1;
    let p_conj = conj_of(cx.subsets.get(..m)?)?;
    let chi = conj_of(cx.memberships.get(..m)?)?;
    let ctx = Formula::and(cx.mem_h.clone(), p_conj.clone());
    let h_psi = syl(&and_left(cx.mem_h.clone(), p_conj.clone()), cx.elim)?;

    // ── under the context *and* one witness assignment ──────────────────────
    let ctxb = Formula::and(ctx.clone(), cx.body.clone());
    let to_ctx = and_left(ctx.clone(), cx.body.clone());
    let to_body = and_right(ctx.clone(), cx.body.clone());
    let to_p = syl(&to_ctx, &and_right(cx.mem_h.clone(), p_conj.clone()))?;

    let mut eqs: Vec<Thm> = Vec::with_capacity(m); // `⊢ ctxb → yᵢ = •`
    let mut mems: Vec<Thm> = Vec::with_capacity(m); // `⊢ ctxb → Hⱼ`
    for j in 0..m {
        // `⊢ ctxb → yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)`, then the earlier fields erased from the
        // *type*, leftmost first. Every `eqs[i]` read here has `i < j ≤ upto`,
        // which is the ordering contract as a loop bound.
        let mut mem = syl(&to_body, &conj_proj(cx.body_atoms, j)?)?;
        debug_assert_eq!(eqs.len(), j);
        for (i, eq) in eqs.iter().enumerate() {
            let (sym, yj) = (cx.spec.ctors[0].args[j], cx.ys[j].clone());
            let head: Vec<Term> = cx.ps.iter().chain(cx.pts[..i].iter()).cloned().collect();
            let tail: Vec<Term> = cx.ys[i + 1..j].to_vec();
            mem = rewrite_under(
                env,
                eq,
                move |t| {
                    let mut a = head.clone();
                    a.push(t);
                    a.extend(tail.iter().cloned());
                    Formula::mem(yj.clone(), Term::apply(sym, a))
                },
                &mem,
            )?;
        }
        let beta_j = beta(cx.spec, cx.ps, cx.pts, j)?;
        if *mem.concl()
            != Formula::imp(ctxb.clone(), Formula::mem(cx.ys[j].clone(), beta_j.clone()))
        {
            return None
        }

        // `Pⱼ` at the witness: `yⱼ ∈ βⱼ(p⃗,•⃗<ⱼ) ⊆ 1`, hence `yⱼ = •`.
        let p_j = syl(&to_p, &conj_proj(cx.subsets.get(..m)?, j)?)?;
        let (_, all) = p_j.concl().as_imp()?;
        let at_y = syl(&p_j, &Thm::ax_inst(all, cx.ys[j].clone())?)?;
        let eq_j = syl(&hyp_mp(&at_y, &mem)?, &inst_all(cx.unit_eta, &cx.ys[j..=j])?)?;
        // …and the same membership, at the point.
        let mem_j = rewrite_under(env, &eq_j, move |t| Formula::mem(t, beta_j.clone()), &mem)?;
        eqs.push(eq_j);
        mems.push(mem_j);
    }
    let under_witness = hyp_conj(&mems)?;
    if *under_witness.concl() != Formula::imp(ctxb, chi.clone()) {
        return None
    }

    // ── discharge the witnesses, innermost binder first ─────────────────────
    //
    // `ctx` and `chi` are free of `y⃗` — both speak only about `‖ind(p⃗)‖` and
    // the field types at the *point* — which is `hyp_ex_branch`'s side
    // condition. Unlike the class-(S) sibling there is no disjunction to
    // eliminate afterwards: ψ is one existential, because a structure has one
    // constructor and this file refuses any other.
    let mut acc = under_witness;
    let mut branch = None;
    for v in cx.yvs.iter().rev() {
        let br = hyp_ex_branch(*v, &acc, &ctx, &chi)?;
        acc = curry(&br)?;
        branch = Some(br);
    }
    let under_ctx = hyp_mp(&branch?, &h_psi)?;

    let out = uncurry(&under_ctx)?;
    crate::establishes(&out, &Formula::imp(cx.mem_h.clone(), Formula::imp(p_conj, chi)))
        .then_some(out)
}

/// `βⱼ(p⃗, x⃗<ⱼ)` — the `j`-th field's type at a caller-chosen prefix.
fn beta(spec: &DeclSpec, ps: &[Term], xs: &[Term], j: usize) -> Option<Term> {
    let mut a = ps.to_vec();
    a.extend(xs.get(..j)?.iter().cloned());
    Some(Term::apply(*spec.ctors.first()?.args.get(j)?, a))
}

/// `xⱼ ∈ βⱼ(p⃗, x⃗<ⱼ)`, one per field — the single constructor's field typings
/// at a caller-chosen argument list.
fn typings(spec: &DeclSpec, ps: &[Term], xs: &[Term]) -> Vec<Formula> {
    (0..xs.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(xs[..j].iter().cloned());
            Formula::mem(xs[j].clone(), Term::apply(spec.ctors[0].args[j], a))
        })
        .collect()
}
