//! **Each `Prop` field of a class-(T) structure is inhabited by the point** —
//! the third and smallest of the three field-inhabitation theorems.
//!
//! # The family, and what distinguishes this member
//!
//! Three constructions state the same conclusion and differ only in **which
//! carrier supplies the major premise**. `SCOPING.md` §9 records that they read
//! as one problem for as long as they did precisely because of that:
//!
//! | class | major premise | where |
//! |---|---|---|
//! | (S) | `• ∈ A_φ(p⃗)`, and [`LeProp::elim`] hands back ψ | [`super::family::le_prop_fields`] |
//! | (P) | `• ∈ ‖ind(p⃗)‖`, and `TruncCarrier::elim` hands back an existential | [`super::family::trunc_fields`] |
//! | **(T)** | **`z ∈ ind(p⃗)`** — plain membership in the §5.2 carrier | **here** |
//!
//! `PProd.{u,v}` and `PSigma.{u,v}` have a resultant sort containing a literal
//! `1`, so they are `provably_nonzero` at every σ and `PProd.{0,0}` is
//! `Prop → Prop → Type 0`: a class-**(T)** carrier whose *fields* are `Prop`s.
//! There is no `A_φ` and no truncation, so neither sibling's premise exists, and
//! the projection is still `•` because the projection's **type** is a `Prop` —
//! which is equally true of a `Prop` field in a `Type`-resultant structure.
//!
//! # Interface
//!
//! With `p⃗` the declaration's own parameter variables and `•⃗<ⱼ` for `j` copies
//! of the point:
//!
//! ```text
//! Pⱼ  :=  βⱼ(p⃗, •⃗<ⱼ) ⊆ 1                              [DeclFields::subsets]
//! Hⱼ  :=  • ∈ βⱼ(p⃗, •⃗<ⱼ)                          [DeclFields::memberships]
//!
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)) )     [steps[j]]
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → ((P₀ ∧ … ∧ P_{k-1}) → (H₀ ∧ … ∧ H_{k-1})) )
//!                                                    [DeclFields::inhabited]
//! ```
//!
//! All unconditional; `steps` is empty and `inhabited` is `None` exactly at
//! `k = 0`, and `steps[k-1]` *is* `inhabited`.
//! [`DeclFields::is_present`] is the one-line test on the spec.
//!
//! **The major premise quantifies `z`.** Its two siblings state theirs at the
//! point, because for them the carrier's only possible inhabitant *is* the
//! point. Here it is not: a class-(T) carrier holds W-elements, and the
//! projection's subject is whatever the checker has. Nothing in the conclusion
//! mentions `z`, which is the whole reason the derivation below is the short
//! one.
//!
//! # φ constant in `z`, and the ladder for one Separation
//!
//! [`decl_rect`] at
//!
//! ```text
//! φ(z) := ⋀_{j<k} ( (P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ) )
//! ```
//!
//! — **constant in the induction variable**, which is legal here and is what
//! removes the existential fold both siblings need. The sole induction step is
//! `∀y⃗. (⋀ⱼ yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ) → φ)`, and its `y⃗` are `rect_step`'s own binders
//! rather than an existential's witnesses, so there is no `hyp_ex_branch`
//! anywhere in this file and no disjunction elimination either.
//!
//! Conjoining the whole ladder into one `φ` is what buys the rest:
//! [`super::family::trunc_fields`] pays one Separation for ψ and then `k`
//! existential eliminations, and a rung-at-a-time version of this file would pay
//! `k` Separations. **One `w_rect` Separation covers every rung**, because the
//! prefixes are conjuncts of a single constant `φ` and `conj_proj` reads them
//! back afterwards. That is the whole of why this is the smallest of the three.
//!
//! The collapse inside the step is its siblings' verbatim: `yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)`
//! with `βⱼ ⊆ 1` gives `yⱼ = •` by [`crate::sums::unit_eta`], and the equations
//! already produced rewrite the *next* field type's argument list, leftmost
//! first — `k(k-1)/2` Leibniz steps, which is the cost
//! [`super::family::le_prop_fields`]'s header already names.
//!
//! # The ordering contract
//!
//! `Hⱼ` needs `P₀ … Pⱼ` and no others, and `steps[j]` says so. It is not an
//! accident of the corpus: `PSigma`'s second field type is `β fst`, so `P₁`
//! is only available once `H₀` is, and a consumer projecting `snd` climbs
//!
//! ```text
//! P₀ ⟹ H₀ ⟹ (its own typing gives) P₁ ⟹ H₁
//! ```
//!
//! With only the bundle that is a cycle. `PProd` does not need it — its two
//! field types are its two parameters — so one of the two corpus declarations
//! on this row exercises the ladder and one does not.
//!
//! # Scope: correct at every σ, usable at some — and that is the design
//!
//! **The theorem holds at every σ**, and nothing here is restricted to a level.
//! `Pⱼ` is a *hypothesis*, so [`decl_rect`] at `φ(z) := (⋀P → ⋀H)` goes through
//! whatever the field types are. What varies with σ is only whether a consumer
//! can **discharge** `Pⱼ`: at `PProd.{1,1}` the fields are data and `⟦α⟧ ∈ U₁`
//! does not give `⟦α⟧ ⊆ 1`.
//!
//! That is worth stating as a consequence rather than a caveat, because it is
//! the same property that made the design right one row earlier.
//! [`super::family::trunc_fields`]'s header records why `Pⱼ` is *quantified*
//! rather than decided: `086_projProp3` is legal, projects index 2, and so needs
//! `P₁` — the **data** field `someData : PUnit.{1}`'s — which discharges,
//! because `PUnit.{1}` interprets to a singleton. `⊆ 1` is strictly weaker than
//! "is a `Prop`", so a field-is-a-`Prop` guard would have refused a declaration
//! the checker accepts. **Quantifying rather than deciding is exactly what lets
//! one σ-generic statement be usable at only some σ.** A guard would have made
//! the theorem smaller *and* wrong.
//!
//! So the honest count is by *obligation*, not by key. Of the eight waiting
//! pairs over `080`/`081`, four (`σ = 0,0`) owe only this certificate and four
//! (`σ = 1,1`) owe a **term** and belong with `Prod` on `SCOPING.md` §9's row 3.
//! **This closes four.** (Measured by Vera at `9ede611`; `SCOPING` §9 said eight
//! and `MINI-HANDOFF` §11 said four, and both were honest — eight is the count
//! by key. Stamp the commit beside any corpus figure quoted here, or the next
//! landing makes it stale without making it wrong.)
//!
//! **What splits by σ is the field's sort *expression*, not projection in
//! general** — Vera's table, and the thing to cite rather than "at low σ":
//!
//! | field's sort | example | splits? |
//! |---|---|---|
//! | `Sort 0`, a numeral | `And.left` | no — a proof at every σ |
//! | `Sort (u+1)`, a successor | `Prod.fst` | no — data at every σ |
//! | **`Sort u`, a bare parameter** | `PProd.fst`, `PSigma.fst` | **yes** |
//!
//! Only a bare parameter can be zero at one σ and nonzero at another, which is
//! why this row is the first on the project where the σ question answers
//! "different".
//!
//! # What is refused, and by what
//!
//! A constructor count other than one, and a recursive field. With two
//! constructors the statement is **false**: membership says only that *some*
//! constructor's fields are inhabited, which pins nothing about constructor 0's.
//!
//! **Indices are not a refusal here**, unlike in both siblings: this takes an
//! [`Inductive`], which is the non-indexed carrier, so there is no indexed input
//! to refuse. One fewer claim to witness.
//!
//! Neither refusal has a guard of its own. Both are already refused by a
//! *statement* comparison that is there for the derivation's own sake — two
//! constructors by `parts.len() != 1`, a recursive field by the `establishes`
//! against [`rect_parts`], because `rect_step₀` then carries `tⱼ ∈ W` and
//! `φ(tⱼ)` atoms the step this file builds does not produce. Both are tested.
//!
//! Which check catches which input was **instrumented, not inferred** (two
//! constructors → `parts.len()`; a recursive field → the `establishes`) — see
//! [`super::family::trunc_fields`]'s header for why that distinction earns its
//! sentence: deleting either comparison alone also fails no test, because the
//! survivor plus the downstream `Thm::mp` against [`decl_rect`]'s antecedent
//! catches whatever the other would have. An over-determined net where each
//! check owns one input is not the same thing as a redundant layer, and only
//! measuring which fires *first* tells them apart.
//!
//! # Nothing here is an axiom
//!
//! One [`decl_rect`] — one Separation, for the whole ladder — and then no
//! symbol and no second Separation: `k` uses of [`crate::sums::unit_eta`] and
//! one Leibniz per dependency.
//!
//! [`LeProp::elim`]: super::family::le_prop::LeProp::elim

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{
    and_left, and_right, conj_of, conj_proj, eq_symm, gen_all, hyp_mp, inst_all, syl, uncurry,
};

use super::carrier::Inductive;
use super::machine::Machine;
use super::rec_shared::{hyp_conj, rewrite_under};
use super::rect::{decl_rect, rect_parts};
use super::spec::DeclSpec;

/// A class-(T) structure's `Prop` fields, shown inhabited by the point.
pub struct DeclFields {
    /// `Pⱼ = βⱼ(p⃗, •⃗<ⱼ) ⊆ 1`, one per field in declared order — spelled here
    /// so a consumer discharges the *same* formulas the theorems carry rather
    /// than rebuilding a `subset` with its own fresh binder.
    pub subsets: Vec<Formula>,
    /// `Hⱼ = • ∈ βⱼ(p⃗, •⃗<ⱼ)`, one per field in declared order.
    pub memberships: Vec<Formula>,
    /// The major-premise variable `z`, bound by the second `∀` of every theorem
    /// below. Exported so a consumer can rebuild the statement it instantiates.
    pub major: FreeVar,
    /// **The ladder.** `steps[j]` is
    /// `⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)))` — the `j`-th
    /// prefix, needing the `Pᵢ` for `i ≤ j` and **no others**. Empty at
    /// `k = 0`, and `steps[k-1]` is [`DeclFields::inhabited`] on the nose.
    ///
    /// `PSigma.snd` is what consumes it: its field type depends on `fst`, so
    /// `P₁` is available only once `H₀` is.
    pub steps: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → (⋀ⱼ Pⱼ → ⋀ⱼ Hⱼ))`. `None` exactly at `k = 0`.
    pub inhabited: Option<Thm>,
}

impl DeclFields {
    /// Derive the field inhabitations from plain carrier membership.
    ///
    /// `None` for a declaration without exactly one constructor, for one whose
    /// constructor has a recursive field, for a foreign apparatus, and on any
    /// internal shape check. At `k = 0` it returns a value whose theorems are
    /// `None`; see the header.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call — for the
    /// whole ladder, not per rung — so build this once per declaration and
    /// cache it with the result.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
    ) -> Option<DeclFields> {
        // The apparatus identity is the only guard: it is what nothing below
        // re-checks. Every other refusal this file makes is a statement
        // comparison, and the header says which catches which.
        if !ind.is_over(mach) || ind.spec.ctors.is_empty() {
            return None
        }
        if !crate::all_unconditional(&[&ind.ty_ax]) {
            return None
        }
        let s = mach.wt.sums.clone();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let (point, unit) = (s.point(), s.unit());
        let k = ind.spec.ctors[0].args.len();
        let pts = vec![point.clone(); k];
        let zv2 = env.fresh_var();

        let subsets: Vec<Formula> = (0..k)
            .map(|j| {
                let b = beta(&ind.spec, &ps, &pts, j).expect("j is in range");
                kernel::thm::subset(env, b, unit.clone())
            })
            .collect();
        let memberships = typings(&ind.spec, &ps, &pts);

        if conj_of(&subsets).is_none() {
            // `k = 0`: nothing to be inhabited, and the empty conjunction is
            // not a formula this kernel has.
            return Some(DeclFields {
                subsets,
                memberships,
                major: zv2,
                steps: Vec::new(),
                inhabited: None,
            })
        }

        // ── φ: the whole ladder, conjoined, and constant in `z` ─────────────
        let phis: Vec<Formula> = (0..k)
            .map(|j| {
                Some(Formula::imp(
                    conj_of(subsets.get(..=j)?)?,
                    conj_of(memberships.get(..=j)?)?,
                ))
            })
            .collect::<Option<_>>()?;
        let phi = conj_of(&phis)?;

        // ── the single induction step ───────────────────────────────────────
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let body_atoms = typings(&ind.spec, &ps, &ys);
        let body = conj_of(&body_atoms)?;

        let zv = env.fresh_var();
        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != 1 {
            return None
        }
        let cx = Fold {
            spec: &ind.spec,
            unit_eta: &s.unit_eta,
            ps: &ps,
            pts: &pts,
            ys: &ys,
            body: &body,
            body_atoms: &body_atoms,
            subsets: &subsets,
            memberships: &memberships,
        };
        let rungs: Vec<Thm> = (0..k).map(|j| rung(env, &cx, j)).collect::<Option<_>>()?;
        let step = gen_all(&yvs, &hyp_conj(&rungs)?);
        if !crate::establishes(&step, &parts[0]) {
            return None
        }

        // `⊢ ∀z. (z ∈ W → φ)`, then the carrier's own name for `W`.
        let all_w = Thm::mp(&decl_rect(env, mach, ind, zv, &phi)?, &step)?;
        let tz2 = Term::var(zv2);
        let at_z = inst_all(&all_w, std::slice::from_ref(&tz2))?;
        let to_w = inst_all(&ind.ty_ax, &ps)?;
        if *to_w.concl() != Formula::eq(ind.carrier.clone(), ind.wty.clone()) {
            return None
        }
        let hole = env.fresh_var();
        let at_ind = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    ind.wty.clone(),
                    ind.carrier.clone(),
                    hole,
                    Formula::imp(
                        Formula::mem(tz2.clone(), Term::var(hole)),
                        phi.clone(),
                    ),
                ),
                &eq_symm(env, &to_w)?,
            )?,
            &at_z,
        )?;

        // ── the rungs, read back off the conjunction ────────────────────────
        let mut quant = ind.params.clone();
        quant.push(zv2);
        let mem_z = Formula::mem(tz2, ind.carrier.clone());
        let steps: Vec<Thm> = (0..k)
            .map(|j| {
                let at = syl(&at_ind, &conj_proj(&phis, j)?)?;
                crate::establishes(&at, &Formula::imp(mem_z.clone(), phis[j].clone()))
                    .then(|| gen_all(&quant, &at))
            })
            .collect::<Option<_>>()?;

        let out = DeclFields {
            subsets,
            memberships,
            major: zv2,
            inhabited: Some(steps[k - 1].clone()),
            steps,
        };
        out.all_unconditional().then_some(out)
    }

    /// Whether the theorems above exist — `Some(k > 0)`, where `k` is the
    /// single constructor's field count. `None` when `spec` is not one this
    /// construction is about.
    ///
    /// A question about the *spec*, decided before any theorem is built, for
    /// the reason
    /// [`LeCarrier::intro_is_conditional`](super::family::LeCarrier::intro_is_conditional)
    /// is: a consumer reads which shape it has rather than pattern-matching on
    /// an `Option` it might mistake for a failure.
    pub fn is_present(spec: &DeclSpec) -> Option<bool> {
        if spec.ctors.len() != 1 || spec.ctors[0].recs != 0 {
            return None
        }
        Some(!spec.ctors[0].args.is_empty())
    }

    /// Whether every theorem here rests on nothing. Checked on the way out.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(
            &self.inhabited.iter().chain(self.steps.iter()).collect::<Vec<_>>(),
        )
    }
}

/// Everything [`rung`] reads, gathered once. Private.
struct Fold<'a> {
    spec: &'a DeclSpec,
    unit_eta: &'a Thm,
    ps: &'a [Term],
    /// `k` copies of the point.
    pts: &'a [Term],
    /// The induction step's own field variables.
    ys: &'a [Term],
    /// The step's antecedent, and its conjuncts.
    body: &'a Formula,
    body_atoms: &'a [Formula],
    subsets: &'a [Formula],
    memberships: &'a [Formula],
}

/// **`⊢ body → ((P₀ ∧ … ∧ P_upto) → (H₀ ∧ … ∧ H_upto))`** — one rung, inside
/// the induction step and under the step's own field typings.
///
/// A function of the prefix length rather than one accumulating pass, for the
/// reason both siblings give: the statement at `upto` has a strictly weaker
/// hypothesis than the statement at `k-1`, so it is not a projection out of it.
/// The passes share nothing, which is what makes `steps[k-1] == inhabited` a
/// fact about the derivation rather than a promise.
fn rung(env: &mut Env, cx: &Fold<'_>, upto: usize) -> Option<Thm> {
    let m = upto + 1;
    let p_conj = conj_of(cx.subsets.get(..m)?)?;
    let chi = conj_of(cx.memberships.get(..m)?)?;
    let ctx = Formula::and(cx.body.clone(), p_conj.clone());
    let to_body = and_left(cx.body.clone(), p_conj.clone());
    let to_p = and_right(cx.body.clone(), p_conj.clone());

    let mut eqs: Vec<Thm> = Vec::with_capacity(m); // `⊢ ctx → yᵢ = •`
    let mut mems: Vec<Thm> = Vec::with_capacity(m); // `⊢ ctx → Hⱼ`
    for j in 0..m {
        // `⊢ ctx → yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)`, then the earlier fields erased from the
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
            != Formula::imp(ctx.clone(), Formula::mem(cx.ys[j].clone(), beta_j.clone()))
        {
            return None
        }

        // `Pⱼ` at the field variable: `yⱼ ∈ βⱼ(p⃗,•⃗<ⱼ) ⊆ 1`, hence `yⱼ = •`.
        let p_j = syl(&to_p, &conj_proj(cx.subsets.get(..m)?, j)?)?;
        let (_, all) = p_j.concl().as_imp()?;
        let at_y = syl(&p_j, &Thm::ax_inst(all, cx.ys[j].clone())?)?;
        let eq_j = syl(&hyp_mp(&at_y, &mem)?, &inst_all(cx.unit_eta, &cx.ys[j..=j])?)?;
        // …and the same membership, at the point.
        let mem_j = rewrite_under(env, &eq_j, move |t| Formula::mem(t, beta_j.clone()), &mem)?;
        eqs.push(eq_j);
        mems.push(mem_j);
    }
    let under = hyp_conj(&mems)?;
    if *under.concl() != Formula::imp(ctx, chi.clone()) {
        return None
    }
    let out = uncurry(&under)?;
    crate::establishes(&out, &Formula::imp(cx.body.clone(), Formula::imp(p_conj, chi)))
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
