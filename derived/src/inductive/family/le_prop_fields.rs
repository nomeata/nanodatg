//! **Each field type of a class-(S) constructor is inhabited by the point** —
//! read out of the *major premise*, which is the only place the information
//! exists.
//!
//! # What this closes
//!
//! [`super::le_prop_rec::LePropRecursor::rec_typed`] is
//! `⊢ ∀m ∀T. (minor(m, •⃗) ∈ T → rec(m) ∈ fs(1, T))`. A consumer elaborating a
//! class-(S) eliminator meets it at `T := app(C, •)`, so its premise is
//! `app(app(m,•),•) ∈ app(C,•)`, and the application rules that produce such a
//! membership (`Interp::{cond_app, dprod_app, fs_app}` in `mini`) each demand a
//! membership **for the argument**. The obligation therefore lands on
//!
//! ```text
//! ⊢ • ∈ βⱼ(p⃗, •⃗<ⱼ)          for every field j
//! ```
//!
//! and that does **not** follow from `βⱼ ⊆ 1`, which is all the parameter
//! typing gives: `βⱼ ⊆ 1` is satisfied by the *empty* set. Inhabitation is
//! extra information, and it comes from the major premise:
//! [`LeProp::elim`] is `⊢ • ∈ A_φ(p⃗) → ψ` with
//!
//! ```text
//! ψ = ∃y₀ … ∃y_{k-1}. ( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)  ∧  • = • )
//! ```
//!
//! — "the constructor's fields *can* all be inhabited". The witnesses `y⃗` are
//! not `•⃗`, and the types they inhabit are `βⱼ` at `y⃗<ⱼ` rather than at `•⃗<ⱼ`,
//! so neither half of the wanted statement is present verbatim. Both are
//! recovered by the same collapse, run left to right:
//!
//! ```text
//! y₀ ∈ β₀(p⃗)      and β₀(p⃗) ⊆ 1        ⟹  y₀ = •,  so • ∈ β₀(p⃗)
//! y₁ ∈ β₁(p⃗,y₀) = β₁(p⃗,•)  and ⊆ 1     ⟹  y₁ = •,  so • ∈ β₁(p⃗,•)
//! …
//! ```
//!
//! Each step needs the *previous* equations to have already rewritten the field
//! type's argument list, which is why this is a fold and not `k` independent
//! lemmas — and why `Pⱼ` is stated at `•⃗<ⱼ` (the form the consumer holds) and
//! not at `y⃗<ⱼ` (the form the witnesses come in).
//!
//! # Why it is here and not in the checker
//!
//! ψ is a disjunction of existentials and `derived` hands it back unopened;
//! `mini` has no existential elimination at all, and the two combinators that
//! do it (`crate::inductive::rec_shared`'s `hyp_ex_branch` and
//! `hyp_disj_elim`) are `pub(crate)` and stay that way. Assembling this in a
//! consumer would put a disjunction-of-existentials elimination there, which is
//! type theory modelled in set theory and so belongs in `derived` by the
//! boundary rule.
//!
//! # Interface
//!
//! With `p⃗` the declaration's own parameter variables, `•⃗<ⱼ` for `j` copies of
//! the point, and
//!
//! ```text
//! Pⱼ  :=  βⱼ(p⃗, •⃗<ⱼ) ⊆ 1              [LePropFields::subsets]
//! Hⱼ  :=  • ∈ βⱼ(p⃗, •⃗<ⱼ)              [LePropFields::memberships]
//! G   :=  P₀ ∧ … ∧ P_{k-1} ∧ H₀ ∧ … ∧ H_{k-1}
//! ```
//!
//! ```text
//! ⊢ ∀p⃗. (• ∈ A_φ(p⃗) → ((P₀ ∧ … ∧ P_{k-1}) → (H₀ ∧ … ∧ H_{k-1})))  [inhabited]
//! ⊢ ∀p⃗. (• ∈ A_φ(p⃗) → ((P₀ ∧ … ∧ P_{k-1}) → G))                   [guard]
//! ```
//!
//! Both are **unconditional** and both are `None` exactly when `k = 0`.
//!
//! `G` is [`super::le_prop_rec::LePropRecursor`]'s own antecedent at `y⃗ := •⃗`,
//! conjunct for conjunct and in the same order, so [`LePropFields::guard`] is
//! literally what discharges
//! [`super::le_prop_rec::LePropRecursor::iota_at_point`] once its `∀y⃗` has been
//! instantiated at the point. That is the whole reason the redundant-looking
//! `P⃗ → … ∧ P⃗ ∧ …` shape is exported beside [`LePropFields::inhabited`]: the
//! consumer would otherwise have to know `G`'s conjunct order to reassemble it.
//!
//! # `k = 0` is not a special case here, and needs no wiring
//!
//! At `k = 0` there is no field, so there is nothing to be inhabited: `P⃗`, `H⃗`
//! and `G` are all the empty conjunction, which this kernel cannot spell (there
//! is no `⊤`). Both theorems are therefore `None`, and
//! [`LePropFields::is_present`] is the one-line test on the *spec*.
//!
//! This subsumes the sub-case a consumer would otherwise have had to wire by
//! hand, because at `k = 0`
//! [`super::le_prop_rec::LePropRecursor::iota_at_point`] carries **no
//! antecedent at all** — `LePropRecursor`'s header records the same
//! `intro_is_conditional(spec, 0)` test deciding it. So the consumer's `match`
//! on "is there a guard to discharge" is the `match` it already writes for ι's
//! two shapes, and the two `None`s coincide by construction rather than by
//! agreement. Nothing extra exists at `k = 0`, and nothing extra is needed.
//!
//! # What is refused, and why the guards are the consumer's
//!
//! Indices, a constructor count other than one, and a recursive field — the
//! same three [`super::le_prop_rec::LePropRecursor::build`] refuses, for the
//! reasons its header gives. With two constructors the statement is *false*:
//! ψ is then a genuine disjunction and membership in `A_φ` says only that
//! **some** constructor's fields are inhabited, which pins nothing about
//! constructor 0's. The derivation below is written as an `n`-branch
//! elimination anyway (one branch, at `n = 1`) so that the shape is honest
//! about what would have to change.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced and no Separation is performed. One
//! [`LeProp::elim`], `k` uses of [`crate::sums::unit_eta`], one Leibniz per
//! dependency (`k(k-1)/2` of them, and that count is the whole cost), and the
//! existential fold. ψ is **rebuilt** from the spec and compared against
//! [`LeProp::psi`] before anything else happens, so a [`LeProp`] describing a
//! different declaration is refused rather than silently spoken for.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{hyp_conj, hyp_disj_elim, hyp_ex_branch, rewrite_under};
use crate::{and_left, and_right, conj_of, conj_proj, curry, gen_all, hyp_mp, inst_all, syl, uncurry};

use super::le::LeSpec;
use super::le_prop::LeProp;
use super::le_rec::typings;

/// The class-(S) constructor's fields, shown inhabited by the point.
pub struct LePropFields {
    /// `Pⱼ = βⱼ(p⃗, •⃗<ⱼ) ⊆ 1`, one per field in declared order — the
    /// propositionality hypotheses, spelled here so a consumer discharges them
    /// against the *same* formulas the theorems below carry rather than
    /// rebuilding a `subset` with its own fresh binder.
    pub subsets: Vec<Formula>,
    /// `Hⱼ = • ∈ βⱼ(p⃗, •⃗<ⱼ)`, one per field in declared order — the conclusion,
    /// conjunct by conjunct.
    pub memberships: Vec<Formula>,
    /// `⊢ ∀p⃗. (• ∈ A_φ(p⃗) → (⋀ⱼ Pⱼ → ⋀ⱼ Hⱼ))`. `None` exactly at `k = 0`.
    pub inhabited: Option<Thm>,
    /// `⊢ ∀p⃗. (• ∈ A_φ(p⃗) → (⋀ⱼ Pⱼ → G))`, with
    /// `G = conj_of(subsets ++ memberships)` —
    /// [`super::le_prop_rec::LePropRecursor`]'s antecedent at `y⃗ := •⃗`.
    /// `None` exactly at `k = 0`.
    pub guard: Option<Thm>,
}

impl LePropFields {
    /// Derive the field inhabitations from the major premise.
    ///
    /// `lp` must be the conditional-singleton reading of `spec` at `params` —
    /// checked by rebuilding ψ from the spec and comparing it against
    /// [`LeProp::psi`], which pins the field symbols, their order and the
    /// parameter variables all at once.
    ///
    /// `None` on a spec that is not
    /// [`well_formed`](super::spec::IndexedDeclSpec::well_formed), on an
    /// **indexed** one, on one without exactly one constructor, on one whose
    /// constructor has a recursive field, on a parameter-count mismatch, on a
    /// hypothetical [`LeProp`], or when ψ does not match. At `k = 0` it returns
    /// a value whose two theorems are `None`; see the header.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        spec: &LeSpec,
        lp: &LeProp,
        params: &[FreeVar],
    ) -> Option<LePropFields> {
        if !spec.well_formed()
            || spec.num_indices() != 0
            || spec.len() != 1
            || params.len() != spec.params()
        {
            return None
        }
        let c = &spec.base.ctors[0];
        if c.recs != 0 || c.order.len() != c.args.len() {
            return None
        }
        if !lp.all_unconditional() {
            return None
        }
        let s = mach.wt.sums.clone();
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let (point, unit) = (s.point(), s.unit());
        let k = c.args.len();
        let pts = vec![point.clone(); k];

        // ── ψ, rebuilt ─────────────────────────────────────────────────────
        //
        // `LeCarrier` built the disjunct with fresh field variables of its own
        // and closed them; the binders are de Bruijn, so a second pass with
        // *different* fresh variables produces the identical formula. That is
        // what makes this a check rather than a hope, and it is the only route:
        // `Formula` cannot be taken apart under a quantifier.
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let mut body_atoms = typings(spec, &ps, 0, &ys);
        // The index equation `q = tup(e⃗₀)` at `ni = 0`, with `q` at the point:
        // `tup()` is `•`, so this is `• = •`. `LeProp`'s header says why it is
        // a conjunct and not an oversight.
        body_atoms.push(Formula::eq(point.clone(), point.clone()));
        // `body` is never `None`: the index equation is always a conjunct, which
        // is the whole reason `LeProp`'s header keeps `• = •` standing.
        let body = conj_of(&body_atoms)?;
        let psi = yvs.iter().rev().fold(body.clone(), |acc, v| Formula::exists(*v, acc));
        if psi != lp.psi {
            return None
        }

        let (subsets, memberships) = atoms(env, spec, &ps, &pts, &unit);
        let (p_conj, chi) = match (conj_of(&subsets), conj_of(&memberships)) {
            (Some(p), Some(h)) => (p, h),
            // `k = 0`: `P⃗`, `H⃗` and `G` are all the empty conjunction, which
            // this kernel cannot spell. The ψ check above has already run, so
            // this is "nothing to prove" and not "input not recognised".
            _ => {
                return Some(LePropFields {
                    subsets,
                    memberships,
                    inhabited: None,
                    guard: None,
                })
            }
        };

        // ── The ambient context: the major premise and the `Pⱼ` ────────────
        let mem_a = Formula::mem(point.clone(), lp.set.clone());
        let ctx = Formula::and(mem_a.clone(), p_conj.clone());
        let h_psi = syl(&and_left(mem_a.clone(), p_conj.clone()), &lp.elim)?;

        // ── Under the context *and* one witness assignment ─────────────────
        let ctxb = Formula::and(ctx.clone(), body.clone());
        let to_ctx = and_left(ctx.clone(), body.clone());
        let to_body = and_right(ctx.clone(), body.clone());
        let to_p = syl(&to_ctx, &and_right(mem_a.clone(), p_conj.clone()))?;

        let mut eqs: Vec<Thm> = Vec::with_capacity(k); // `⊢ ctxb → yᵢ = •`
        let mut mems: Vec<Thm> = Vec::with_capacity(k); // `⊢ ctxb → Hⱼ`
        for j in 0..k {
            // `⊢ ctxb → yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)`, then the earlier fields erased from
            // the *type*, one position at a time and leftmost first.
            let mut mem = syl(&to_body, &conj_proj(&body_atoms, j)?)?;
            for i in 0..j {
                let (sym, yj) = (c.args[j], ys[j].clone());
                let head: Vec<Term> = ps.iter().chain(pts[..i].iter()).cloned().collect();
                let tail: Vec<Term> = ys[i + 1..j].to_vec();
                mem = rewrite_under(
                    env,
                    &eqs[i],
                    move |t| {
                        let mut a = head.clone();
                        a.push(t);
                        a.extend(tail.iter().cloned());
                        Formula::mem(yj.clone(), Term::apply(sym, a))
                    },
                    &mem,
                )?;
            }
            let beta_j = beta(spec, &ps, &pts, j)?;
            if *mem.concl() != Formula::imp(ctxb.clone(), Formula::mem(ys[j].clone(), beta_j.clone()))
            {
                return None
            }

            // `Pⱼ` at the witness: `yⱼ ∈ βⱼ(p⃗,•⃗<ⱼ) ⊆ 1`, hence `yⱼ = •`.
            let p_j = syl(&to_p, &conj_proj(&subsets, j)?)?;
            let (_, all) = p_j.concl().as_imp()?;
            let at_y = syl(&p_j, &Thm::ax_inst(all, ys[j].clone())?)?;
            let eq_j = syl(&hyp_mp(&at_y, &mem)?, &inst_all(&s.unit_eta, &ys[j..=j])?)?;
            // …and the same membership, at the point.
            let mem_j = rewrite_under(env, &eq_j, move |t| Formula::mem(t, beta_j.clone()), &mem)?;
            eqs.push(eq_j);
            mems.push(mem_j);
        }
        let under_witness = hyp_conj(&mems)?;
        if *under_witness.concl() != Formula::imp(ctxb, chi.clone()) {
            return None
        }

        // ── Discharge the witnesses, innermost binder first ────────────────
        //
        // `ctx` and `chi` are free of `y⃗` — `ctx` speaks about `A_φ(p⃗)` and the
        // field types at the *point*, `chi` likewise — which is exactly
        // `hyp_ex_branch`'s side condition.
        let mut acc = under_witness;
        let mut branch = None;
        for v in yvs.iter().rev() {
            let br = hyp_ex_branch(*v, &acc, &ctx, &chi)?;
            acc = curry(&br)?;
            branch = Some(br);
        }
        // One disjunct, because one constructor. The fold is the general one so
        // that a second constructor would fail at the *statement*, not here.
        let under_ctx = hyp_disj_elim(&h_psi, &ctx, &[branch?])?;

        let want = Formula::imp(mem_a.clone(), Formula::imp(p_conj.clone(), chi.clone()));
        let inhabited = uncurry(&under_ctx)?;
        if !crate::establishes(&inhabited, &want) {
            return None
        }

        // ── The same, re-packaged as `LePropRecursor`'s antecedent ─────────
        let mut g_atoms = subsets.clone();
        g_atoms.extend(memberships.iter().cloned());
        let g = conj_of(&g_atoms)?;
        let ctx_p = and_right(mem_a.clone(), p_conj.clone());
        let mut parts: Vec<Thm> = (0..k)
            .map(|j| syl(&ctx_p, &conj_proj(&subsets, j)?))
            .collect::<Option<_>>()?;
        for j in 0..k {
            parts.push(syl(&under_ctx, &conj_proj(&memberships, j)?)?);
        }
        let guard = uncurry(&hyp_conj(&parts)?)?;
        if !crate::establishes(&guard, &Formula::imp(mem_a, Formula::imp(p_conj, g))) {
            return None
        }

        let out = LePropFields {
            subsets,
            memberships,
            inhabited: Some(gen_all(params, &inhabited)),
            guard: Some(gen_all(params, &guard)),
        };
        out.all_unconditional().then_some(out)
    }

    /// Whether the two theorems above exist — `Some(k > 0)`, where `k` is the
    /// single constructor's field count. `None` when `spec` is not one this
    /// construction is about (indices, or a constructor count other than one).
    ///
    /// A question about the *spec*, decided before any theorem is built, for the
    /// reason [`super::LeCarrier::intro_is_conditional`] is: a consumer reads
    /// which shape it has rather than pattern-matching on an `Option` it might
    /// mistake for a failure.
    pub fn is_present(spec: &LeSpec) -> Option<bool> {
        if spec.num_indices() != 0 || spec.len() != 1 {
            return None
        }
        Some(!spec.base.ctors[0].args.is_empty())
    }

    /// Whether every theorem here rests on nothing. Checked on the way out.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(
            &self.inhabited.iter().chain(self.guard.iter()).collect::<Vec<_>>(),
        )
    }
}

/// `βⱼ(p⃗, x⃗<ⱼ)` — the `j`-th field's type at a caller-chosen prefix.
fn beta(spec: &LeSpec, ps: &[Term], xs: &[Term], j: usize) -> Option<Term> {
    let mut a = ps.to_vec();
    a.extend(xs.get(..j)?.iter().cloned());
    Some(Term::apply(*spec.base.ctors.first()?.args.get(j)?, a))
}

/// The `Pⱼ` and the `Hⱼ`, both at `•⃗`.
///
/// `Hⱼ` goes through [`typings`] — the *same* function
/// [`super::le::LeCarrier`] built φ's matrix with and
/// [`super::le_prop_rec::LePropRecursor`] built `G` with — so the three agree
/// by construction rather than by three transcriptions of one formula.
fn atoms(
    env: &mut Env,
    spec: &LeSpec,
    ps: &[Term],
    pts: &[Term],
    unit: &Term,
) -> (Vec<Formula>, Vec<Formula>) {
    let subsets = (0..pts.len())
        .map(|j| {
            let b = beta(spec, ps, pts, j).expect("j is in range and the ctor exists");
            kernel::thm::subset(env, b, unit.clone())
        })
        .collect();
    (subsets, typings(spec, ps, 0, pts))
}
