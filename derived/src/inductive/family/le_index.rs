//! **Class (S) at an index** — the carrier `⟦T p⃗ x⃗⟧ = [tup(x⃗) ∈ acc(A_φ,R)]`,
//! minted as a symbol of arity `np + ni`.
//!
//! # What this closes
//!
//! [`super::le::LeCarrier`] stops at a *set*: `A_φ(p⃗)`, `R(p⃗)` and the term
//! `acc(A_φ(p⃗), R(p⃗))`. What a consumer needs at an index is not that set but a
//! **proposition** — the truth value "`tup(x⃗)` is accessible" — because
//! `T p⃗ x⃗ : Prop` and `⟦Prop⟧ = U₀`. `thesis.txt:1886` writes the carrier
//!
//! ```text
//! ⟦µt : ∀x::α. U_ℓ. (c:β)⟧ = λx::α. ulift_ℓ (acc^ϕ_r (x))
//! ```
//!
//! and `:2057` and `:2162` write the bracket that turns it into a truth value:
//! `[p] = {x ∈ {•} | p}`, and `[x ∈ acc(A,R)]` outright, inside `rec_acc`'s own
//! definition. Before this file that set existed in this repository **only as
//! prose** — six headers describe it and nothing built it.
//!
//! # Why this is a module beside [`super::le_prop`] and not a relaxed guard
//!
//! [`super::le_prop`] mints **nothing**. Its whole content is that at `ni = 0`
//! the *already existing* `A_φ` **is** a conditional singleton, because
//! `Idx(p⃗) = 1`; its own header says the symbol `A_φ` is not re-introduced.
//! Every step of it spends [`super::index::IndexSpace::point`], which is `Some`
//! only when the telescope has no `β`s, so at `ni ≥ 1` it returns `None` by
//! construction — and a version that did not would be **false**, since at
//! `ni ≥ 1` `A_φ` is a subset of a genuine `Σ` nest and is not the carrier.
//!
//! At `ni ≥ 1` there is therefore a set to *introduce*: one
//! [`crate::prop::conditional_singleton`] over `p⃗ ++ x⃗`, at the condition
//! `tup(x⃗) ∈ acc(A_φ(p⃗), R(p⃗))`. That is a new symbol `χ` of arity `np + ni`,
//! and the seam this file sits on is the one
//! [`super::trunc::TruncCarrier::over_family`] already established for class
//! (P): **`derived` mints the symbol and exports the characteristic theorem;
//! a consumer calls [`crate::tower::Tower::cond_in_u0`] and the rest of
//! [`crate::prop`] where it needs the typing.** [`LeIndexCarrier::chi_at`] is
//! what makes that reachable at index terms other than this module's own
//! variables, and it is the interface a checker actually consumes.
//!
//! # `ulift_ℓ` is nothing here, as it is nothing anywhere
//!
//! `thesis.txt:2106` and `:2284`: `⟦ulift_n^n α⟧ = ⟦α⟧`, and `ulift`'s
//! soundness clause is `ᾱ ∈ Uₙ ⊆ Uₙ′` — a cumulativity raise, not a set
//! operation. So the `ulift_ℓ` in `:1886` needs nothing new at `ni ≥ 1`:
//! [`LeIndexCarrier::in_u0`] gives `χ ∈ U₀` and a raise to any higher rung is
//! [`crate::cumul`]'s, already spent by whoever asks for it.
//!
//! # The `acc^ϕ_r` collapse is [`super::le`]'s argument, and is cited not
//! re-derived
//!
//! Carneiro builds `acc^ϕ_r x := ∃h : ϕ x. acc_{r'}(x,h)` over the subtype
//! `{x : α | ϕ x}` with a projected relation (`:1832–1845`). [`super::le`]'s
//! header gives the reason both wrappers evaporate at the set level — the two
//! corrections that landed with [`crate::acc`], `step_closed`'s `x ∈ A` guard
//! and the absence of any `R ⊆ A × A` assumption — so that `acc^ϕ_r` *is*
//! `acc(A_φ, R)` with `R` unrestricted. This file rests on that argument and
//! does not restate it: `acc` enters here only as the term
//! [`super::le::LeCarrier::acc_set`] hands over, pinned against `ac` on the way
//! in.
//!
//! # [`LeIndexCarrier::ctor_intro`] is the **degenerate** case only
//!
//! With a non-recursive declaration `R` is provably empty,
//! [`super::le::LeCarrier::degenerate`] is `⊢ ∀p⃗. acc(A_φ,R) = A_φ`, and the
//! constructor rule is three theorems composed: [`super::le::LeCarrier::intro`]
//! lands `tup(e⃗ᵢ) ∈ A_φ`, `degenerate` carries it to `acc`, and
//! [`crate::prop::cond_intro`] turns it into `• ∈ χ(p⃗, e⃗ᵢ)`.
//!
//! With a **recursive** constructor there is no such composition and this file
//! **declines**, by returning `None` for the whole vector rather than an empty
//! one. What would be needed is [`crate::acc::Acc`]'s `acc_intro`, whose
//! premise is a *universally quantified* accessibility
//! `∀y. (y ∈ A_φ → (⟨y, tup(e⃗ᵢ)⟩ ∈ R → y ∈ acc))`, while a Lean constructor
//! supplies `mᵢ` **specific** accessible children plus an inversion of
//! [`super::le::LeCarrier::rel_ax`] saying they are the only predecessors of
//! `tup(e⃗ᵢ)`. That is [`super::le_rec`]-shaped work, it has **no witness
//! anywhere** — [`super::le`]'s census finds no recursive class-(S)
//! declaration in this repository, tutorials or prelude — and writing something
//! that looked general would be writing the inversion without the census that
//! justifies its shape.
//!
//! # Interface
//!
//! With `p⃗` the declaration's parameter variables, `x⃗` the `ni` index
//! variables [`LeIndexCarrier::xvs`] holds, `X := tup(x⃗)` and
//! `acc := acc(A_φ(p⃗), R(p⃗))`:
//!
//! ```text
//! χ, of arity np + ni                                     [LeIndexCarrier::sym]
//! χ(p⃗,x⃗)                                              [LeIndexCarrier::carrier]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ χ(p⃗,x⃗) ↔ (z ∈ 1 ∧ X ∈ acc))              [LeIndexCarrier::chi]
//! ⊢ ∀z. (z ∈ χ(p⃗,x⃗) ↔ (z ∈ 1 ∧ X ∈ acc))        [LeIndexCarrier::chi_at_params]
//! ⊢ ∀p⃗∀x⃗. χ(p⃗,x⃗) ∈ U₀                                  [LeIndexCarrier::in_u0]
//! ⊢ ∀p⃗∀x⃗. (X ∈ acc → • ∈ χ(p⃗,x⃗))                       [LeIndexCarrier::intro]
//! ⊢ ∀p⃗∀x⃗. (• ∈ χ(p⃗,x⃗) → X ∈ acc)                        [LeIndexCarrier::elim]
//! ⊢ ∀p⃗∀x⃗∀z. (z ∈ χ(p⃗,x⃗) → z = •)                  [LeIndexCarrier::only_point]
//! ⊢ ∀p⃗∀x⃗∀u∀v. ((u ∈ χ(p⃗,x⃗) ∧ v ∈ χ(p⃗,x⃗)) → u = v)      [LeIndexCarrier::irrel]
//!
//! per constructor, and only when the declaration is non-recursive:
//! ⊢ ∀p⃗∀y⃗ᵢ. ((Hᵢ ∧ Eᵢ) → • ∈ χ(p⃗, e⃗ᵢ(p⃗,y⃗ᵢ)))                  [LeIndexCtor::mem]
//!
//! χ(p⃗′,x⃗′) at other terms                             [LeIndexCarrier::at]
//! ⊢ ∀z. (z ∈ χ(p⃗′,x⃗′) ↔ (z ∈ 1 ∧ tup(x⃗′) ∈ acc′))  [LeIndexCarrier::chi_at]
//! ```
//!
//! `Hᵢ ∧ Eᵢ` is [`super::le::LeCarrier::intro`]'s own antecedent, **read off**
//! it rather than rebuilt, so the two cannot drift; at `ni ≥ 1` it is never
//! empty, so [`super::le::LeCarrier::intro_is_conditional`] is `true` at every
//! constructor and this file has no second shape to carry.
//!
//! [`LeIndexCarrier::in_u0`] is **unconditional**: `χ ⊆ 1` whatever `acc` is,
//! so there is no `H`, no size argument and no parameter typing — exactly as
//! [`super::le_prop`]'s and [`super::trunc::TruncCarrier::in_u0`]'s are, and
//! for the same reason.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::prop::conditional_singleton`] — a Separation over `1`, and
//! Separation is unconditional — and then the [`crate::prop`] lemmas at it. The
//! constructor rules add one [`crate::eq_symm`] and one [`Thm::eq_leibniz`]
//! each. Every exported theorem is pinned with [`crate::establishes`] against
//! the formula this header advertises, and the bundle is checked
//! [`crate::all_unconditional`] on the way out.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::acc::Acc;
use crate::inductive::machine::Machine;
use crate::prop::{
    cond_elim, cond_intro, cond_subset_unit, cond_subsingleton, conditional_singleton,
};
use crate::tower::Tower;
use crate::{eq_symm, gen_all, inst_all, syl};

use super::le::{LeCarrier, LeSpec};
use super::spec::IndexedDeclSpec;

/// One constructor's introduction rule for the class-(S) carrier at an index.
///
/// Present only in the degenerate case; see the module header for what the
/// recursive case would need and why it is declined rather than approximated.
pub struct LeIndexCtor {
    /// Its position in the declaration.
    pub index: usize,
    /// The `kᵢ` plain-field variables [`LeIndexCtor::mem`] quantifies after the
    /// parameters. Fresh here: [`super::le::LeCarrier`] does not export its
    /// own, and its `intro` is universally closed, so it is instantiated at
    /// these.
    pub yvs: Vec<FreeVar>,
    /// `Hᵢ ∧ Eᵢ` — the antecedent, read off
    /// [`super::le::LeCarrier::intro`]`[i]` at those variables.
    pub ante: Formula,
    /// `e⃗ᵢ(p⃗, y⃗ᵢ)` — the result index vector this rule is stated at.
    pub result: Vec<Term>,
    /// `χ(p⃗, e⃗ᵢ(p⃗,y⃗ᵢ))`.
    pub at: Term,
    /// `⊢ ∀p⃗ ∀y⃗ᵢ. ((Hᵢ ∧ Eᵢ) → • ∈ χ(p⃗, e⃗ᵢ(p⃗,y⃗ᵢ)))`.
    pub mem: Thm,
}

/// A subsingleton family's carrier **at an index**: the conditional singleton
/// `[tup(x⃗) ∈ acc(A_φ,R)]`.
pub struct LeIndexCarrier {
    /// The `ni ≥ 1` index variables everything is stated at.
    pub xvs: Vec<FreeVar>,
    /// `χ`, of arity `np + ni`.
    pub sym: FnSym,
    /// `χ(p⃗, x⃗)`.
    pub carrier: Term,
    /// `acc(A_φ(p⃗), R(p⃗))` — repeated from
    /// [`super::le::LeCarrier::acc_set`] so a caller compares the term the
    /// theorems below are about rather than assuming it.
    pub acc: Term,
    /// `X := tup(x⃗)`, the index tuple `χ`'s condition is about.
    pub tuple: Term,
    /// `X ∈ acc` — the condition itself, which is what
    /// [`crate::prop`]'s lemmas take as their `φ`.
    pub cond: Formula,
    /// `⊢ ∀p⃗ ∀x⃗ ∀z. (z ∈ χ(p⃗,x⃗) ↔ (z ∈ 1 ∧ X ∈ acc))`.
    pub chi: Thm,
    /// [`LeIndexCarrier::chi`] at the declaration's own parameter and index
    /// variables — the form [`crate::prop`]'s lemmas take.
    pub chi_at_params: Thm,
    /// `⊢ ∀p⃗ ∀x⃗. χ(p⃗,x⃗) ∈ U₀`, with **no antecedent**.
    pub in_u0: Thm,
    /// `⊢ ∀p⃗ ∀x⃗. (X ∈ acc → • ∈ χ(p⃗,x⃗))`.
    pub intro: Thm,
    /// `⊢ ∀p⃗ ∀x⃗. (• ∈ χ(p⃗,x⃗) → X ∈ acc)` — soundness: the carrier is not
    /// inhabited at an index the accessibility does not reach.
    pub elim: Thm,
    /// `⊢ ∀p⃗ ∀x⃗ ∀z. (z ∈ χ(p⃗,x⃗) → z = •)`.
    pub only_point: Thm,
    /// `⊢ ∀p⃗ ∀x⃗ ∀u ∀v. ((u ∈ χ(p⃗,x⃗) ∧ v ∈ χ(p⃗,x⃗)) → u = v)` — proof
    /// irrelevance, and it holds whatever the condition is.
    pub irrel: Thm,
    /// One rule per constructor, in declaration order — **`None` when the
    /// declaration is recursive**, which is the decline the header names. An
    /// empty `Vec` means a declaration with no constructors, which is a
    /// different thing.
    pub ctor_intro: Option<Vec<LeIndexCtor>>,
    /// The parameter variables everything above is stated at.
    params: Vec<FreeVar>,
}

impl LeIndexCarrier {
    /// Mint the class-(S) carrier at an index.
    ///
    /// `lc` must be [`super::le::LeCarrier::build`] at `spec` and `params`, and
    /// `ac` the [`Acc`] it was built with — both are pinned rather than
    /// assumed, so a carrier from another [`Machine`] or at other parameters is
    /// refused instead of silently described. `tow` supplies `U₀`; it must be
    /// over the same [`crate::sums::Sums`] as `mach`, or the `1` this speaks
    /// about is not the one `cond_in_u0` does and the shape check below fails.
    ///
    /// **`spec` must have at least one index.** At `ni = 0` there is nothing to
    /// mint: `Idx(p⃗) = 1`, `A_φ` is *already* a conditional singleton, and
    /// [`super::le_prop`] says so without a second Separation. This returns
    /// `None` there rather than introducing a symbol that would duplicate one.
    ///
    /// The [`super::index::IndexSpace`] is **not** an argument. Nothing here
    /// speaks about `Idx(p⃗)`: the condition is a membership in `acc`, and the
    /// tuple is [`IndexedDeclSpec::tup`]'s, which is a function of the `Sums`
    /// alone. `ni` is read off the spec and `lc` is pinned against `params`
    /// directly.
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        tow: &Tower,
        ac: &Acc,
        spec: &LeSpec,
        lc: &LeCarrier,
        params: &[FreeVar],
    ) -> Option<LeIndexCarrier> {
        let ni = spec.num_indices();
        if !spec.well_formed()
            || ni == 0
            || params.len() != spec.params()
            || lc.phi_disjuncts.len() != spec.len()
            || lc.intro.len() != spec.len()
        {
            return None
        }
        // One pairing, one unit set, one `U₀`.
        if ac.sets.up != mach.wt.sums.ap.sets.up || tow.sums.ap.sets.up != mach.wt.sums.ap.sets.up {
            return None
        }
        let s = &mach.wt.sums;
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();

        // `lc` is this declaration's carrier, at *these* parameters.
        if lc.a_phi != Term::apply(lc.phi, ps.clone())
            || lc.r != Term::apply(lc.rel, ps.clone())
            || lc.acc_set != ac.of(lc.a_phi.clone(), lc.r.clone())
        {
            return None
        }
        let acc = lc.acc_set.clone();

        // ── the symbol: one conditional singleton over `p⃗ ++ x⃗` ────────────
        let xvs: Vec<FreeVar> = (0..ni).map(|_| env.fresh_var()).collect();
        let xs: Vec<Term> = xvs.iter().map(|v| Term::var(*v)).collect();
        let tuple = IndexedDeclSpec::tup(s, &xs);
        let cond = Formula::mem(tuple.clone(), acc.clone());

        let mut quant: Vec<FreeVar> = params.to_vec();
        quant.extend(xvs.iter().copied());
        let (sym, chi) = conditional_singleton(env, s, &quant, &cond)?;

        let mut qs = ps.clone();
        qs.extend(xs.iter().cloned());
        let carrier = Term::apply(sym, qs.clone());
        let chi_at_params = inst_all(&chi, &qs)?;

        // ── the wanted shapes, spelled out once and pinned individually ─────
        let (one, pt) = (s.unit(), s.point());
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let guard = |t: &Term| {
            Formula::iff(
                Formula::mem(t.clone(), carrier.clone()),
                Formula::and(Formula::mem(t.clone(), one.clone()), cond.clone()),
            )
        };
        if !crate::establishes(&chi_at_params, &Formula::forall(zv, guard(&tz))) {
            return None
        }
        if !crate::establishes(&chi, &forall_all(&quant, Formula::forall(zv, guard(&tz)))) {
            return None
        }

        // ── the `prop` lemmas, at this set and this condition ───────────────
        let in_u0 = gen_all(&quant, &tow.cond_in_u0(env, &cond, &carrier, &chi_at_params)?);
        let intro = gen_all(&quant, &cond_intro(s, &cond, &carrier, &chi_at_params)?);
        let elim = gen_all(&quant, &cond_elim(s, &cond, &carrier, &chi_at_params)?);
        let irrel = gen_all(&quant, &cond_subsingleton(env, s, &cond, &carrier, &chi_at_params)?);

        // `z ∈ χ → z ∈ 1 → z = •` — the shape that makes a class-(S) ι
        // reflexivity, and the one `cond` does not state directly.
        let subset = cond_subset_unit(env, s, &cond, &carrier, &chi_at_params)?;
        let only_point = gen_all(
            &quant,
            &Thm::gen(
                zv,
                &syl(
                    &inst_all(&subset, std::slice::from_ref(&tz))?,
                    &inst_all(&s.unit_eta, std::slice::from_ref(&tz))?,
                )?,
            ),
        );

        let mem_pt = Formula::mem(pt.clone(), carrier.clone());
        let (uv, vv) = (env.fresh_var(), env.fresh_var());
        let (tu, tv) = (Term::var(uv), Term::var(vv));
        let want = [
            (&in_u0, forall_all(&quant, Formula::mem(carrier.clone(), tow.u0()))),
            (&intro, forall_all(&quant, Formula::imp(cond.clone(), mem_pt.clone()))),
            (&elim, forall_all(&quant, Formula::imp(mem_pt, cond.clone()))),
            (
                &only_point,
                forall_all(
                    &quant,
                    Formula::forall(
                        zv,
                        Formula::imp(
                            Formula::mem(tz.clone(), carrier.clone()),
                            Formula::eq(tz.clone(), pt.clone()),
                        ),
                    ),
                ),
            ),
            (
                &irrel,
                forall_all(
                    &quant,
                    forall_all(
                        &[uv, vv],
                        Formula::imp(
                            Formula::and(
                                Formula::mem(tu.clone(), carrier.clone()),
                                Formula::mem(tv.clone(), carrier.clone()),
                            ),
                            Formula::eq(tu, tv),
                        ),
                    ),
                ),
            ),
        ];
        if !want.iter().all(|(t, w)| crate::establishes(t, w)) {
            return None
        }

        // ── the constructor rules, degenerate case only ─────────────────────
        let ctor_intro = match &lc.degenerate {
            None => None,
            Some(deg) => {
                let deg_at = inst_all(deg, &ps)?;
                if !crate::establishes(&deg_at, &Formula::eq(acc.clone(), lc.a_phi.clone())) {
                    return None
                }
                // `⊢ A_φ(p⃗) = acc`, the direction the rule needs.
                let back = eq_symm(env, &deg_at)?;
                let mut out = Vec::with_capacity(spec.len());
                for i in 0..spec.len() {
                    out.push(ctor_rule(env, mach, spec, lc, &chi, sym, &back, &ps, params, i)?);
                }
                Some(out)
            }
        };

        let outp = LeIndexCarrier {
            xvs,
            sym,
            carrier,
            acc,
            tuple,
            cond,
            chi,
            chi_at_params,
            in_u0,
            intro,
            elim,
            only_point,
            irrel,
            ctor_intro,
            params: params.to_vec(),
        };
        outp.all_unconditional().then_some(outp)
    }

    /// `χ(p⃗′, x⃗′)` — the carrier at other parameter and index **terms**.
    ///
    /// The one spelling of "this symbol applied to its arguments", so a
    /// consumer with concrete Lean index expressions in hand does not have to
    /// know that the parameters come first. `None` on a length mismatch.
    pub fn at(&self, ps: &[Term], xs: &[Term]) -> Option<Term> {
        if ps.len() != self.params.len() || xs.len() != self.xvs.len() {
            return None
        }
        let mut args = ps.to_vec();
        args.extend(xs.iter().cloned());
        Some(Term::apply(self.sym, args))
    }

    /// `⊢ ∀z. (z ∈ χ(p⃗′,x⃗′) ↔ (z ∈ 1 ∧ tup(x⃗′) ∈ acc(A_φ(p⃗′), R(p⃗′))))` —
    /// [`LeIndexCarrier::chi`] at other terms.
    ///
    /// **This is the interface, not [`LeIndexCarrier::chi_at_params`].** A
    /// consumer holds Lean index expressions, not this module's fresh
    /// variables, and every lemma in [`crate::prop`] plus
    /// [`crate::tower::Tower::cond_in_u0`] takes exactly this theorem — so
    /// without it the whole of `prop` would be reachable only at `x⃗`.
    pub fn chi_at(&self, ps: &[Term], xs: &[Term]) -> Option<Thm> {
        if ps.len() != self.params.len() || xs.len() != self.xvs.len() {
            return None
        }
        let mut args = ps.to_vec();
        args.extend(xs.iter().cloned());
        inst_all(&self.chi, &args)
    }

    /// The condition `tup(x⃗′) ∈ acc(A_φ(p⃗′), R(p⃗′))` that
    /// [`LeIndexCarrier::chi_at`]'s theorem is about, at the same terms.
    ///
    /// Rebuilt from `self.cond` by substitution rather than re-derived, so a
    /// caller cannot pass [`crate::prop`] a `φ` that differs from the one the
    /// characteristic theorem carries.
    pub fn cond_at(&self, ps: &[Term], xs: &[Term]) -> Option<Formula> {
        if ps.len() != self.params.len() || xs.len() != self.xvs.len() {
            return None
        }
        let mut out = self.cond.clone();
        for (v, t) in self.params.iter().zip(ps).chain(self.xvs.iter().zip(xs)) {
            out = out.subst(*v, t);
        }
        Some(out)
    }

    /// Whether every theorem here rests on nothing. Checked on the way out.
    pub fn all_unconditional(&self) -> bool {
        let mut ts: Vec<&Thm> = vec![
            &self.chi,
            &self.chi_at_params,
            &self.in_u0,
            &self.intro,
            &self.elim,
            &self.only_point,
            &self.irrel,
        ];
        if let Some(cs) = &self.ctor_intro {
            ts.extend(cs.iter().map(|c| &c.mem));
        }
        crate::all_unconditional(&ts)
    }
}

/// `∀v⃗. φ` — the formula-level counterpart of [`gen_all`], for the
/// [`crate::establishes`] pins above.
fn forall_all(vs: &[FreeVar], phi: Formula) -> Formula {
    vs.iter().rev().fold(phi, |acc, v| Formula::forall(*v, acc))
}

/// One constructor's rule: [`LeCarrier::intro`], the degenerate collapse, and
/// [`cond_intro`] at the carrier's instance.
#[allow(clippy::too_many_arguments)]
fn ctor_rule(
    env: &mut Env,
    mach: &Machine,
    spec: &LeSpec,
    lc: &LeCarrier,
    chi: &Thm,
    sym: FnSym,
    back: &Thm,
    ps: &[Term],
    params: &[FreeVar],
    i: usize,
) -> Option<LeIndexCtor> {
    let s = &mach.wt.sums;
    let yvs: Vec<FreeVar> = (0..spec.base.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();

    // `⊢ (Hᵢ ∧ Eᵢ) → tup(e⃗ᵢ) ∈ A_φ(p⃗)`, at *these* variables. At `ni ≥ 1` the
    // antecedent is never empty, so the `as_imp` cannot be the shape
    // `LeCarrier::intro_is_conditional` warns about. A hypothesis on it rides
    // into `mem` and is caught by the `establishes` below — there is no second,
    // earlier check, because an unreachable one is worse than none.
    let mut args = ps.to_vec();
    args.extend(ys.iter().cloned());
    let at = inst_all(&lc.intro[i], &args)?;
    let (ante, concl) = at.concl().as_imp()?;
    let result = spec.result_vec(i, ps, &ys)?;
    let tup_res = IndexedDeclSpec::tup(s, &result);
    if concl != Formula::mem(tup_res.clone(), lc.a_phi.clone()) {
        return None
    }

    // `⊢ tup(e⃗ᵢ) ∈ A_φ → tup(e⃗ᵢ) ∈ acc`, out of `⊢ A_φ = acc`.
    let hole = env.fresh_var();
    let carry = Thm::mp(
        &Thm::eq_leibniz(
            lc.a_phi.clone(),
            lc.acc_set.clone(),
            hole,
            Formula::mem(tup_res.clone(), Term::var(hole)),
        ),
        back,
    )?;

    // `⊢ tup(e⃗ᵢ) ∈ acc → • ∈ χ(p⃗, e⃗ᵢ)`, at the carrier's own instance.
    let mut ia = ps.to_vec();
    ia.extend(result.iter().cloned());
    let at_res = Term::apply(sym, ia.clone());
    let cond_i = Formula::mem(tup_res, lc.acc_set.clone());
    let chi_i = inst_all(chi, &ia)?;
    let body = syl(&syl(&at, &carry)?, &cond_intro(s, &cond_i, &at_res, &chi_i)?)?;

    let mut quant = params.to_vec();
    quant.extend(yvs.iter().copied());
    let mem = gen_all(&quant, &body);
    let want = forall_all(
        &quant,
        Formula::imp(ante.clone(), Formula::mem(s.point(), at_res.clone())),
    );
    if !crate::establishes(&mem, &want) {
        return None
    }
    Some(LeIndexCtor { index: i, yvs, ante, result, at: at_res, mem })
}
