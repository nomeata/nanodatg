//! **The iterated dependent Σ** — a constructor's non-recursive arguments,
//! packed into one set by `k` nested [`DSum`]s bottoming out at `1`.
//!
//! # What the thesis asks for
//!
//! §5.2 builds a constructor's contribution to the tag set by recursion on the
//! constructor's *type*, one rule per argument. The two that matter for a
//! non-recursive telescope are the base case and the `∀y : β` case
//! (`thesis.txt:1793–1797`):
//!
//! ```text
//! Γ; t : ∀x :: α. U_ℓ ⊢ t e ctor ⇒ 1_ℓ;  p. 0_ℓ;  pgx. x = e
//!
//! Γ; t : ∀x :: α. U_ℓ ⊢ ∀y : β. τ ctor ⇒ Σy' : β. A[y'/y];
//!                                        p'. B[π₁p'/y][π₂p'/p];  …
//! ```
//!
//! Reading them from the inside out, a constructor `∀y₀:β₀. ∀y₁:β₁. … ∀y_{k-1}:β_{k-1}. t e`
//! contributes
//!
//! ```text
//! Σy₀ : β₀. Σy₁ : β₁(y₀). … Σy_{k-1} : β_{k-1}(y₀,…,y_{k-2}). 1
//! ```
//!
//! — genuinely **dependent**, because each `βᵢ` is elaborated in the context
//! extended by the earlier `yⱼ`. This file builds that nest, from the innermost
//! `1` outwards, and derives the two rules a translation needs: pack `k` typed
//! arguments into one element, and read the `i`-th argument back out with its
//! type, which is where the thesis's `[π₁p'/y][π₂p'/p]` substitution lands.
//!
//! # What the components are
//!
//! With `q` an element of the telescope,
//!
//! ```text
//! tailᵢ(q) := π₂ⁱ(q)          compᵢ(q) := π₁(π₂ⁱ(q))
//! ```
//!
//! so `compᵢ(q)` is the `i`-th argument. Substituting `compⱼ(q)` for `yⱼ`
//! *is* the thesis's iterated substitution: `π₁p'` for the argument in scope,
//! `π₂p'` for the rest of the tuple. It is expressible as a term only because
//! each `βᵢ` is a function **symbol** rather than a term with a free variable —
//! see [`super::dsum`]'s header for why the kernel forces that.
//!
//! # Interface
//!
//! [`Telescope::new`] takes `np` outer parameters (the inductive's own
//! parameters, fixed throughout the declaration) and the `k` argument-type
//! symbols `β₀ … β_{k-1}`, where `βᵢ` has arity `np + i`. Writing `T(p⃗)` for
//! the packed type, `Hᵢ` for `yᵢ ∈ βᵢ(p⃗, y₀ … y_{i-1})` and
//! `tuple = ⟨y₀, ⟨y₁, … ⟨y_{k-1}, •⟩ … ⟩⟩`:
//!
//! ```text
//! ⊢ ∀p⃗ ∀y₀ … ∀y_{k-1}. ((H₀ ∧ (H₁ ∧ (… ∧ H_{k-1}))) → tuple ∈ T(p⃗))     [Telescope::intro]
//! ⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → compᵢ(q) ∈ βᵢ(p⃗, comp₀ q, …, comp_{i-1} q))     [Telescope::proj_mem[i]]
//! ⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → ⟨comp₀ q, ⟨…, ⟨comp_{k-1} q, •⟩…⟩⟩ = q)          [Telescope::eta]
//! ```
//!
//! At `k = 0` the conjunction is empty and [`Telescope::intro`] degenerates to
//! `⊢ ∀p⃗. • ∈ T(p⃗)` — a nullary constructor, whose tag component is the point
//! of `1`, exactly as the thesis's base case `t e ctor ⇒ 1_ℓ` says. Nothing
//! else changes; `k = 0` is not a special case anywhere below.
//!
//! # Non-vacuity: `eta` is what makes the packing faithful
//!
//! [`Telescope::intro`] alone would be satisfied by a one-element `T(p⃗)` that
//! forgets its arguments. [`Telescope::eta`] rules that out: every element is
//! recovered from its own components, so the packing is injective and
//! `compᵢ ∘ pack = yᵢ` follows from [`crate::proj::Proj::fst`] and
//! [`snd`](crate::proj::Proj::snd) alone. `tests/sigma.rs` cashes this at a
//! genuinely dependent two-argument telescope.
//!
//! # Nothing here is an axiom
//!
//! `k` uses of [`super::dsum`] — each one Replacement and one Separation — plus
//! one [`crate::define_abbrev`] naming the innermost `1`. No new axiom.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::proj::Proj;
use crate::recursion::hyp::hyp_eq_trans;
use crate::sums::Sums;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, imp_refl, inst_all, syl};

use super::dsum::{dsum, DSum};
use super::shared::{hyp_congr, hyp_eq_symm, hyp_transport};

/// The iterated dependent sum over a telescope of argument types.
pub struct Telescope {
    /// The `np` outer parameter variables — the inductive's own parameters.
    pub outer: Vec<FreeVar>,
    /// The `k` telescope variables `y₀ … y_{k-1}`.
    pub ys: Vec<FreeVar>,
    /// The argument-type symbols, `βᵢ` of arity `np + i`.
    pub betas: Vec<FnSym>,
    /// `C₀ … C_k`, the level symbols; `Cᵢ` has arity `np + i` and `C_k = 1`.
    pub levels: Vec<FnSym>,
    /// The `k` dependent sums, outermost first: `sums[i].sigma == levels[i]`.
    pub sums: Vec<DSum>,
    /// `⊢ ∀p⃗ ∀y⃗. C_k(p⃗,y⃗) = 1` — the innermost level.
    pub base_ax: Thm,
    /// `T(p⃗) = C₀(p⃗)`, at the quantified outer parameters.
    pub ty: Term,
    /// `⊢ ∀p⃗ ∀y⃗. ((H₀ ∧ (… ∧ H_{k-1})) → tuple(y⃗) ∈ T(p⃗))`, and at `k = 0`
    /// the hypothesis-free `⊢ ∀p⃗. • ∈ T(p⃗)`.
    pub intro: Thm,
    /// For each `i < k`:
    /// `⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → compᵢ(q) ∈ βᵢ(p⃗, comp₀ q, …, comp_{i-1} q))`.
    pub proj_mem: Vec<Thm>,
    /// For each `i ≤ k`: `⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → tailᵢ(q) ∈ Cᵢ(p⃗, comp₀ q, …))`.
    pub tail_mem: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → ⟨comp₀ q, ⟨…, ⟨comp_{k-1} q, •⟩…⟩⟩ = q)`.
    pub eta: Thm,
}

impl Telescope {
    /// The term `tailᵢ(q) = π₂ⁱ(q)`.
    pub fn tail_of(ap: &crate::funcs::Apply, proj: &Proj, i: usize, q: Term) -> Term {
        (0..i).fold(q, |t, _| proj.snd_of(ap, t))
    }

    /// The term `compᵢ(q) = π₁(π₂ⁱ(q))` — the `i`-th packed argument.
    pub fn comp_of(ap: &crate::funcs::Apply, proj: &Proj, i: usize, q: Term) -> Term {
        proj.fst_of(ap, Telescope::tail_of(ap, proj, i, q))
    }

    /// The packed tuple `⟨y₀, ⟨y₁, … ⟨y_{k-1}, •⟩ … ⟩⟩`.
    pub fn tuple_of(s: &Sums, args: &[Term]) -> Term {
        args.iter()
            .rev()
            .fold(s.point(), |acc, y| s.ap.sets.pair(y.clone(), acc))
    }

    /// The term `T(p⃗)` at caller-supplied outer parameters.
    pub fn ty_of(&self, args: Vec<Term>) -> Term { Term::apply(self.levels[0], args) }

    /// Build the nest and derive the introduction rule, the `k` projections and
    /// the η rule.
    ///
    /// `betas[i]` must have arity `np + i`; `pparts` must be
    /// [`super::product_parts`] over the same product and projections. Returns
    /// `None` if either fails.
    pub fn new(
        env: &mut Env,
        s: &Sums,
        proj: &Proj,
        pparts: &Thm,
        np: usize,
        betas: &[FnSym],
    ) -> Option<Telescope> {
        let k = betas.len();
        for (i, b) in betas.iter().enumerate() {
            if b.arity() as usize != np + i {
                return None
            }
        }
        let ap = &s.ap;
        let outer: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
        let ys: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ps: Vec<Term> = outer.iter().map(|v| Term::var(*v)).collect();
        let tys: Vec<Term> = ys.iter().map(|v| Term::var(*v)).collect();

        // ── The innermost level `C_k(p⃗,y⃗) = 1`, then `k` dependent sums ────
        let mut all_vars = outer.clone();
        all_vars.extend(ys.iter().copied());
        let (base, base_ax) = crate::define_abbrev(env, &all_vars, &s.unit())?;

        let mut levels = vec![base];
        let mut sums: Vec<DSum> = Vec::with_capacity(k);
        for i in (0..k).rev() {
            let inner = *levels.last()?;
            let d = dsum(env, s, proj, pparts, betas[i], inner)?;
            levels.push(d.sigma);
            sums.push(d);
        }
        levels.reverse();
        sums.reverse();
        debug_assert_eq!(levels.len(), k + 1);
        let ty = Term::apply(levels[0], ps.clone());

        // Arguments of level `i` when the telescope variables are `y⃗`.
        let level_args = |i: usize| -> Vec<Term> {
            let mut a = ps.clone();
            a.extend(tys[..i].iter().cloned());
            a
        };

        // ── The introduction rule ───────────────────────────────────────────
        let hyps: Vec<Formula> = (0..k)
            .map(|i| Formula::mem(tys[i].clone(), Term::apply(betas[i], level_args(i))))
            .collect();
        let conj = |from: usize| -> Option<Formula> {
            if from >= k {
                return None
            }
            Some(
                hyps[from..]
                    .iter()
                    .rev()
                    .cloned()
                    .reduce(|acc, h| Formula::and(h, acc))
                    .expect("non-empty"),
            )
        };

        // `⊢ • ∈ C_k(p⃗,y⃗)`, from `⊢ • ∈ 1` backwards along the defining equation.
        let base_at = inst_all(&base_ax, &{
            let mut a = ps.clone();
            a.extend(tys.iter().cloned());
            a
        })?;
        let unit_in_base = {
            let hole = env.fresh_var();
            let back = Thm::mp(
                &Thm::eq_leibniz(
                    s.unit(),
                    Term::apply(base, level_args(k)),
                    hole,
                    Formula::mem(s.point(), Term::var(hole)),
                ),
                &crate::eq_symm(env, &base_at)?,
            )?;
            Thm::mp(&back, &s.unit_mem)?
        };

        let intro = if k == 0 {
            gen_all(&outer, &unit_in_base)
        } else {
            let h = conj(0)?;
            let mut cur = a1i(&unit_in_base, h.clone());
            for i in (0..k).rev() {
                // Project the `i`-th conjunct out of the right-nested `H`.
                let mut hi = imp_refl(h.clone());
                for (j, hj) in hyps.iter().enumerate().take(i) {
                    hi = syl(&hi, &and_right(hj.clone(), conj(j + 1)?))?;
                }
                if i + 1 < k {
                    hi = syl(&hi, &and_left(hyps[i].clone(), conj(i + 1)?))?;
                }
                let rule = inst_all(&sums[i].intro, &{
                    let mut a = level_args(i);
                    a.push(tys[i].clone());
                    a.push(Telescope::tuple_of(s, &tys[i + 1..]));
                    a
                })?;
                cur = hyp_mp(&a1i(&rule, h.clone()), &hyp_and(&hi, &cur)?)?;
            }
            debug_assert_eq!(
                *cur.concl(),
                Formula::imp(h, Formula::mem(Telescope::tuple_of(s, &tys), ty.clone())),
                "telescope: intro has the wrong shape"
            );
            gen_all(&all_vars, &cur)
        };

        // ── The projections, walking down the `π₂` spine ────────────────────
        let qv = env.fresh_var();
        let tq = Term::var(qv);
        let comp_args = |i: usize| -> Vec<Term> {
            let mut a = ps.clone();
            a.extend((0..i).map(|j| Telescope::comp_of(ap, proj, j, tq.clone())));
            a
        };
        let mut elim_quant = outer.clone();
        elim_quant.push(qv);

        let mut tails = vec![imp_refl(Formula::mem(tq.clone(), ty.clone()))];
        let mut proj_mem = Vec::with_capacity(k);
        for i in 0..k {
            let at = |th: &Thm| -> Option<Thm> {
                let mut a = comp_args(i);
                a.push(Telescope::tail_of(ap, proj, i, tq.clone()));
                inst_all(th, &a)
            };
            proj_mem.push(syl(&tails[i], &at(&sums[i].fst_mem)?)?);
            let next = syl(&tails[i], &at(&sums[i].snd_mem)?)?;
            tails.push(next);
        }

        // ── η: rebuild `q` from its components ──────────────────────────────
        let eta = {
            // `tail_k q ∈ C_k(…)` becomes `tail_k q ∈ 1`, hence `= •`.
            let base_here = inst_all(&base_ax, &comp_args(k))?;
            let tk = Telescope::tail_of(ap, proj, k, tq.clone());
            let in_unit = {
                let h_eq = a1i(&base_here, Formula::mem(tq.clone(), ty.clone()));
                let tk2 = tk.clone();
                hyp_transport(env, &h_eq, &tails[k], move |t| Formula::mem(tk2.clone(), t))?
            };
            let is_point = syl(&in_unit, &inst_all(&s.unit_eta, std::slice::from_ref(&tk))?)?;
            let mut cur = hyp_eq_symm(env, &is_point)?;
            for i in (0..k).rev() {
                let ci = Telescope::comp_of(ap, proj, i, tq.clone());
                let lifted = {
                    let ci2 = ci.clone();
                    hyp_congr(env, &cur, move |t| ap.sets.pair(ci2.clone(), t))?
                };
                let step = {
                    let mut a = comp_args(i);
                    a.push(Telescope::tail_of(ap, proj, i, tq.clone()));
                    syl(&tails[i], &inst_all(&sums[i].eta, &a)?)?
                };
                cur = hyp_eq_trans(env, &lifted, &step)?;
            }
            debug_assert_eq!(
                *cur.concl(),
                Formula::imp(
                    Formula::mem(tq.clone(), ty.clone()),
                    Formula::eq(
                        Telescope::tuple_of(
                            s,
                            &(0..k)
                                .map(|i| Telescope::comp_of(ap, proj, i, tq.clone()))
                                .collect::<Vec<_>>()
                        ),
                        tq.clone(),
                    ),
                ),
                "telescope: eta has the wrong shape"
            );
            gen_all(&elim_quant, &cur)
        };

        let tail_mem = tails
            .into_iter()
            .map(|t| gen_all(&elim_quant, &t))
            .collect();
        let proj_mem = proj_mem
            .into_iter()
            .map(|t| gen_all(&elim_quant, &t))
            .collect();

        Some(Telescope {
            outer,
            ys,
            betas: betas.to_vec(),
            levels,
            sums,
            base_ax,
            ty,
            intro,
            proj_mem,
            tail_mem,
            eta,
        })
    }
}
