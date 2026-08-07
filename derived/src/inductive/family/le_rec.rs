//! **Class (S)'s recursor** — §5.4 for a subsingleton eliminator, as `rec_acc`
//! at `(A_φ, R)`.
//!
//! # What is thesis and what is invention
//!
//! §5.3 (`thesis.txt:1822–1889`) translates the *type*; §5.4 says of the
//! introduction rules, the recursor and ι only that they "are more or less
//! uniquely determined by the translated type" and leaves them as future work.
//! So the carrier in [`super::le`] is Carneiro's and everything here is ours,
//! on the precedent `RECURSOR-DESIGN.md` set for the non-indexed case.
//!
//! The one thing §5.3 *does* say about the recursor is `:1856–1858`: every
//! non-propositional non-recursive argument must appear in the result index,
//! which yields a variable–variable equality, "and this variable can be
//! eliminated — however, due to potential dependencies on earlier arguments, we
//! will delay this elimination to the recursor". That delayed elimination is
//! **not** here, and deliberately: it is the map from an index tuple back to
//! the constructor's fields, it needs per-declaration data
//! ([`IndexedDeclSpec`] records no field↔index-slot correspondence), and at the
//! set level it is what the *step* `e` is built out of. This module states the
//! contract that step must meet and derives ι from it; see "the step is an
//! adapter" below.
//!
//! # Interface
//!
//! Write `A_φ`, `R` for [`super::LeCarrier`]'s two Separations,
//! `F := accrec(A_φ, R, T, e)`, `IH := ih(F, A_φ, R, tup(e⃗ᵢ))`,
//! `ST := step_typed(A_φ, R, T, e)`, and
//!
//! ```text
//! antᵢ         :=  Hᵢ ∧ Eᵢ            the plain-field and result-index typings
//! slotⱼ(c)     :=  app(app(c, tup(d⃗ᵢⱼ)), •)
//! minorᵢ(m,v⃗)  :=  m applied curried to the fields in DECLARED order
//!                  (a plain field as itself, a recursive field as `•`),
//!                  then to v₀ … v_{mᵢ−1}
//! ```
//!
//! Eliding a leading `∀p⃗ ∀T ∀e ∀y⃗` from every line:
//!
//! ```text
//! ⊢ ((antᵢ ∧ tup(d⃗ᵢⱼ) ∈ A_φ) → ⟨tup(d⃗ᵢⱼ), tup(e⃗ᵢ)⟩ ∈ R(p⃗))      [rel_intro[i][j]]
//! ⊢ ((antᵢ ∧ tup(d⃗ᵢⱼ) ∈ A_φ) → slotⱼ(IH) = app(F, tup(d⃗ᵢⱼ)))   [ih_slot[i][j]]
//! ⊢ (ST → (tup(e⃗ᵢ) ∈ acc(A_φ,R) →
//!       app(F, tup(e⃗ᵢ)) = step(e, tup(e⃗ᵢ), IH)))                     [iota[i]]
//! ⊢ ∀m. ((ST ∧ minor_eq(i)) →
//!       ((antᵢ ∧ tup(e⃗ᵢ) ∈ acc(A_φ,R) ∧ ⋀ⱼ tup(d⃗ᵢⱼ) ∈ acc(A_φ,R)) →
//!        app(F, tup(e⃗ᵢ)) = minorᵢ(m, [app(F, tup(d⃗ᵢⱼ))]ⱼ)))    [minor_iota[i]]
//! ```
//!
//! with the step's contract, [`minor_eq`], being
//!
//! ```text
//! ∀y⃗ ∀c. ((antᵢ ∧ c ∈ ih_bound(A_φ,T) ∧ ⋀ⱼ slotⱼ(c) ∈ T) →
//!           step(e, tup(e⃗ᵢ), c) = minorᵢ(m, [slotⱼ(c)]ⱼ))
//! ```
//!
//! [`rel_intro`](LeRecursor::rel_intro) and [`ih_slot`](LeRecursor::ih_slot) are
//! **unconditional**; `iota` carries `ST`, which is `rec_acc`'s only hypothesis
//! and this module adds none of its own; `minor_iota` carries `ST` and
//! `minor_eq`, both spelled inside the conclusion.
//!
//! # `rel_intro` is the whole content
//!
//! `iota[i]` is [`crate::rec_acc::RecAcc::iota`] instantiated, and says nothing
//! a caller could not get from `rec_acc` directly. What is new is `rel_intro`
//! and, through it, `ih_slot`: **the `j`-th recursive value really is reachable
//! from the induction hypothesis.** `ih(g,A,R,x)` is a set of rows indexed by
//! `y ∈ A`, and `ih_app` reads a row off only when `y ∈ A ∧ ⟨y,x⟩ ∈ R`. So a
//! §5.3 declaration's ι rule fires exactly when the edge from the child's index
//! to the result index is in `R` — which is what `rel_intro` derives, by
//! injecting into the disjunct of ρ that the `LE ctor` recursion emitted for
//! that recursive argument ([`super::LeCarrier::rel_disjuncts`]). Without it,
//! every theorem below would be a true statement about an opaque set.
//!
//! # The step is an adapter, and the minor is curried
//!
//! [`crate::rec_acc`]'s header records why *its* step is applied curried,
//! `e(x)(•)(i)`: `acc` has one introduction rule, so `e` **is** Lean's minor
//! premise and Carneiro's spelling is the one a backend produces. **That
//! argument does not transfer, and the conclusion is that there are two
//! objects here, not one.**
//!
//! `rec_acc`'s `e` is addressed by the *index tuple* and takes the whole
//! induction-hypothesis row as one set. A §5.3 declaration's Lean minor is
//! addressed by the constructor's *fields* and takes the `mᵢ` induction
//! hypotheses separately. Those are different arities over different data, and
//! no spelling convention reconciles them: what sits between is the delayed
//! elimination of `:1856–1858`, the map index-tuple ↦ fields. So:
//!
//! * `e` keeps `rec_acc`'s **curried 3-slot** shape, because that is what
//!   `accrec` consumes and it is not ours to change;
//! * `m` is **curried in Lean's own order** — the constructor's fields in
//!   declared order (a [`Slot::Rec`] contributing `•`, since a class-(S)
//!   recursive field is a proof and every proof interprets to the point), then
//!   one induction hypothesis per recursive field. That is `minorᵢ`, and it is
//!   the spine the recursor nest already produces for the non-indexed case;
//! * [`minor_eq`] is the equation relating them, and it is a **hypothesis**.
//!
//! Making it a hypothesis rather than constructing `e` is a real scope limit
//! and is stated as one. It is the same shape as `rec_acc`'s own `step_typed`
//! and as the general recursor's pointwise `HYP`: the derived layer says what
//! the step must satisfy, the wiring builds a step and discharges it.
//!
//! # Why `minor_eq`'s guard cannot be dropped
//!
//! `c` is guarded by `c ∈ ih_bound(A_φ,T)` because a set-level `e` is a
//! function with a **set** domain — it cannot be specified at every `c` — and
//! `slotⱼ(c) ∈ T` because the minor is likewise a set-level function and can
//! only be applied inside its own domain. Both are discharged at the ι site and
//! neither survives into `minor_iota`'s conclusion:
//! [`crate::rec_acc::Bounded::in_bound`] gives `IH ∈ ih_bound(A_φ,T)` and
//! [`crate::rec_acc::Bounded::value_typed`] gives `app(F,tup(d⃗ᵢⱼ)) ∈ T`, which
//! [`ih_slot`](LeRecursor::ih_slot) transports onto `slotⱼ(IH)`. Both of those
//! needed **A4** ([`crate::acc::acc_pred_closed`]), which is why this
//! construction grew two lemmas outside `family/`.
//!
//! # Scope: what this is for, and what the corpus actually asks
//!
//! The task that produced this file expected the demand to be on
//! `init-prelude`. **It is not.** Decoding every export in the repository
//! (`vendor/arena-tests`, `checker/tests/fixtures`, the 91 tutorial files) for
//! declarations with `numIndices > 0`, and classifying each by
//! `INDEXED-DESIGN.md` §2.1's trichotomy — class (S) iff the recursor carries a
//! motive level the declaration does not — gives, for class (S):
//!
//! | declaration | recursive? | where |
//! |---|---|---|
//! | `Eq` | no | 28 tutorial files, `init-prelude` |
//! | `HEq` | no | `init-prelude` |
//! | `SortElimProp` | no | `071` |
//! | `T` (`nested-unused-param`) | no | that fixture |
//! | `Acc` | **yes**, and *reflexive* | `096`, `117`, `118` |
//!
//! and `init-prelude`'s other two indexed declarations, `Nat.le` and
//! `Nat.le.below`, are class **(P)** — two constructors, so not
//! large-eliminating — and take the truncation clause, not §5.3.
//!
//! Every non-`Acc` witness is therefore the **degenerate** case that
//! [`super::LeCarrier::degenerate`] already closes without a recursor at all,
//! and `Acc`'s recursive argument is function-typed, which
//! [`IndexedDeclSpec`] cannot represent (`recs` is a `usize`, and `d⃗ᵢⱼ` cannot
//! depend on a `γ` binder) and which `INDEXED-DESIGN.md` §2.2 routes to the
//! **direct** clause `⟦Acc.rec⟧ = rec_acc::pack` anyway. So the general
//! recursive class-(S) recursor still has **no corpus witness**, on
//! `init-prelude` as much as on the tutorials.
//!
//! What it does buy: `minor_iota` covers `mᵢ = 0` uniformly — with no recursive
//! argument the conjunctions are empty, `minor_eq` degenerates to "the step is
//! the minor at the fields", and the theorem is the degenerate case's ι rule.
//! That is the shape `Eq`, `HEq` and `071` need.
//!
//! # Non-vacuity
//!
//! `derived/tests/family_le_rec.rs` fires `minor_iota` **closed**, on a
//! two-constructor family over a two-point index whose edge relation is the
//! single edge `⟨tup(ff), tup(tt)⟩`, and pins
//!
//! ```text
//! ⊢ ¬(app(F, tup(tt)) = app(F, tup(ff)))
//! ```
//!
//! by a diagonal argument on the minor, with `ST` and `minor_eq` both
//! discharged from an explicitly constructed `e`. A recursor that computed to a
//! constant would fail that, and it is the reason the witness has two
//! constructors: with one, a finite index set cannot carry both a base point
//! and a genuine recursive step (see the test's header).

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::machine::Machine;
use crate::inductive::spec::Slot;
use crate::rec_acc::{Base, Bounded, RecAcc};
use crate::sums::Sums;
use crate::wrec::{hyp_eq_symm, hyp_eq_trans};
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conj_sub, disj_inject, exists_intro_imp,
    gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

use super::index::IndexSpace;
use super::le::{LeCarrier, LeSpec};
use super::spec::IndexedDeclSpec;

/// Class (S)'s recursor: `rec_acc` at `(A_φ, R)`, plus what makes its ι rule
/// fire at a constructor.
pub struct LeRecursor {
    /// `⊢ ∀p⃗ ∀y⃗. ((antᵢ ∧ tup(d⃗ᵢⱼ) ∈ A_φ) → ⟨tup(d⃗ᵢⱼ), tup(e⃗ᵢ)⟩ ∈ R(p⃗))`,
    /// per constructor and recursive argument. **Unconditional.**
    pub rel_intro: Vec<Vec<Thm>>,
    /// `⊢ ∀p⃗ ∀T ∀e ∀y⃗. ((antᵢ ∧ tup(d⃗ᵢⱼ) ∈ A_φ) →
    /// `app(app(IH, tup(d⃗ᵢⱼ)), •) = app(F, tup(d⃗ᵢⱼ)))`. **Unconditional.**
    pub ih_slot: Vec<Vec<Thm>>,
    /// `⊢ ∀p⃗ ∀T ∀e ∀y⃗. (ST → (tup(e⃗ᵢ) ∈ acc(A_φ,R) →
    /// `app(F, tup(e⃗ᵢ)) = step(e, tup(e⃗ᵢ), IH)))`.
    pub iota: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀T ∀e ∀m ∀y⃗. ((ST ∧ minor_eq(i)) → (K → app(F, tup(e⃗ᵢ)) = minorᵢ))`
    /// — **the §5.3 ι rule**, with `K` the Lean-shaped antecedent of the header.
    pub minor_iota: Vec<Thm>,
    /// Per constructor, [`minor_eq`]'s formula at the **free** variables
    /// [`LeRecursor::target`], [`LeRecursor::step`] and [`LeRecursor::minor`] —
    /// kept so a caller pins the *same* contract it is being handed the ι rule
    /// for, rather than a look-alike. Use [`LeRecursor::minor_eq_at`] to read it
    /// at concrete arguments.
    pub minor_eq: Vec<Formula>,
    /// The variable `minor_iota` quantifies `T` with, and `minor_eq` is stated
    /// over.
    pub target: FreeVar,
    /// The same for the step `e`.
    pub step: FreeVar,
    /// The same for the minor premise `m`.
    pub minor: FreeVar,
}

impl LeRecursor {
    /// Build every rule above.
    ///
    /// `ra` must be the [`RecAcc`] over the *same* [`crate::acc::Acc`] and
    /// pairing that `le` was built with — checked, because a look-alike `acc`
    /// would make every theorem here speak of a different carrier — and `bd`
    /// must be [`Bounded::build`] over that same `ra`.
    ///
    /// Returns `None` on a spec that is not
    /// [`well_formed`](IndexedDeclSpec::well_formed), on a non-indexed or
    /// constructor-less one, on an apparatus mismatch, on a hypothetical input,
    /// or when any shape check fails.
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ra: &RecAcc,
        bd: &Bounded,
        spec: &LeSpec,
        ix: &IndexSpace,
        le: &LeCarrier,
        params: &[FreeVar],
    ) -> Option<LeRecursor> {
        if !spec.well_formed() || spec.indices.is_empty() || spec.is_empty() {
            return None
        }
        if params.len() != spec.params() {
            return None
        }
        if !ra.all_unconditional() || !bd.all_unconditional() {
            return None
        }
        // The house rule at the boundary: `le`'s fields are `pub`.
        if !crate::all_unconditional(&[&le.phi_ax, &le.rel_ax]) {
            return None
        }
        // One apparatus, one `acc`, one pairing.
        let s = mach.wt.sums.clone();
        if ra.base.s.ap.sets.up != s.ap.sets.up {
            return None
        }
        if le.acc_set != ra.base.acc_of(&le.a_phi, &le.r) {
            return None
        }

        let b = &ra.base;
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let ni = spec.num_indices();
        let n = spec.len();

        let (tv, ev, mv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tt, te, tm) = (Term::var(tv), Term::var(ev), Term::var(mv));
        let f = ra.of(le.a_phi.clone(), le.r.clone(), tt.clone(), te.clone());
        let st = ra.step_typed(env, &le.a_phi, &le.r, &tt, &te);
        let acc_args = [le.a_phi.clone(), le.r.clone(), tt.clone(), te.clone()];
        let iota_all = inst_all(&ra.iota, &acc_args)?;
        let in_bound_all = inst_all(&bd.in_bound, &acc_args)?;
        let value_typed_all = inst_all(&bd.value_typed, &acc_args)?;

        let mut rel_intro = Vec::with_capacity(n);
        let mut ih_slot = Vec::with_capacity(n);
        let mut iota = Vec::with_capacity(n);
        let mut minor_iota = Vec::with_capacity(n);
        let mut minor_eq_out = Vec::with_capacity(n);

        for i in 0..n {
            let c = &spec.base.ctors[i];
            let yvs: Vec<FreeVar> = (0..c.args.len()).map(|_| env.fresh_var()).collect();
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let plain = typings(spec, &ps, i, &ys);
            let res = spec.result_vec(i, &ps, &ys)?;
            let tup_res = IndexedDeclSpec::tup(&s, &res);
            let ih_t = b.ih_at(&f, &le.a_phi, &le.r, &tup_res);

            // antᵢ = the plain-field typings, then the `ni` result-index ones.
            let mut ant_atoms = plain.clone();
            for k in 0..ni {
                ant_atoms.push(Formula::mem(res[k].clone(), spec.index_type_at(k, &ps, &res)?));
            }
            let np_plain = plain.len();

            // `tup(e⃗ᵢ) ∈ Idx(p⃗)`, from the index typings alone.
            let mut ia = ps.clone();
            ia.extend(res.iter().cloned());
            let ant_res_idx = syl(
                &conj_sub(&ant_atoms, np_plain, ant_atoms.len())?,
                &inst_all(ix.intro(), &ia)?,
            )?;

            // ── per recursive argument: the edge, and the ih slot ────────────
            let mut rel_bodies = Vec::with_capacity(c.recs);
            let mut slot_bodies = Vec::with_capacity(c.recs);
            let mut children = Vec::with_capacity(c.recs);
            for j in 0..c.recs {
                let child = spec.rec_index_vec(i, j, &ps, &ys)?;
                let tup_child = IndexedDeclSpec::tup(&s, &child);
                let edge_t = b.edge(&tup_child, &tup_res);

                let mut k_atoms = ant_atoms.clone();
                k_atoms.push(Formula::mem(tup_child.clone(), le.a_phi.clone()));
                let k = conj_of(&k_atoms)?;
                let k_ant = conj_sub(&k_atoms, 0, ant_atoms.len())?;
                let k_child_phi = conj_proj(&k_atoms, ant_atoms.len())?;

                // `tup(d⃗ᵢⱼ) ∈ Idx(p⃗)`: a Separation is a subset.
                let mut pa = ps.clone();
                pa.push(tup_child.clone());
                let phi_at = inst_all(&le.phi_ax, &pa)?;
                let (_, phi_rhs) = split_iff(phi_at.concl())?;
                let (in_idx, phi_matrix) = split_and(&phi_rhs)?;
                let k_child_idx = syl(
                    &syl(&k_child_phi, &iff_mp(&phi_at)?)?,
                    &and_left(in_idx, phi_matrix),
                )?;
                let k_res_idx = syl(&k_ant, &ant_res_idx)?;

                // `⟨tup(d⃗ᵢⱼ), tup(e⃗ᵢ)⟩ ∈ Idx × Idx`.
                let into_prod = iff_mpr(&inst_all(
                    &s.pair_in_prod,
                    &[ix.idx.clone(), ix.idx.clone(), tup_child.clone(), tup_res.clone()],
                )?)?;
                let k_in_sq = syl(&hyp_and(&k_child_idx, &k_res_idx)?, &into_prod)?;

                // ρ's own disjunct for this recursive argument, at the fields.
                let k_rho = inject_disjunct(
                    spec, le, &s, i, j, &ps, &yvs, &ys, &k, &k_atoms, np_plain, &edge_t,
                )?;

                let mut ra_args = ps.clone();
                ra_args.push(edge_t.clone());
                let into_r = iff_mpr(&inst_all(&le.rel_ax, &ra_args)?)?;
                let edge_in_r = syl(&hyp_and(&k_in_sq, &k_rho)?, &into_r)?;
                if *edge_in_r.concl()
                    != Formula::imp(k.clone(), Formula::mem(edge_t.clone(), le.r.clone()))
                {
                    return None
                }

                // The ih slot, by `ih_app` at the child's index.
                let slot_t = slot_at(&s, &ih_t, &tup_child);
                let app_at = inst_all(
                    &b.ih_app,
                    &[
                        f.clone(),
                        le.a_phi.clone(),
                        le.r.clone(),
                        tup_res.clone(),
                        tup_child.clone(),
                    ],
                )?;
                let slot = syl(&hyp_and(&k_child_phi, &edge_in_r)?, &app_at)?;
                if *slot.concl() != Formula::imp(k, Formula::eq(slot_t, b.app(&f, &tup_child))) {
                    return None
                }

                children.push(tup_child);
                rel_bodies.push(edge_in_r);
                slot_bodies.push(slot);
            }

            // ── ι, by `rec_acc`'s own ────────────────────────────────────────
            let (_, iota_body) = iota_all.concl().as_imp()?;
            let iota_i = syl(&iota_all, &Thm::ax_inst(iota_body, tup_res.clone())?)?;

            // ── the Lean-shaped ι ────────────────────────────────────────────
            let me = minor_eq(
                env, &s, b, spec, i, &yvs, &ys, &ant_atoms, &tup_res, &children, &le.a_phi, &tt,
                &te, &tm,
            )?;
            let mi = compose_minor(
                env,
                &s,
                ra,
                spec,
                i,
                &ys,
                &ant_atoms,
                &tup_res,
                &ih_t,
                &children,
                &f,
                le,
                &st,
                &me,
                &tm,
                &tt,
                &iota_i,
                &in_bound_all,
                &value_typed_all,
                &slot_bodies,
            )?;

            let mut quant_y: Vec<FreeVar> = params.to_vec();
            quant_y.extend(yvs.iter().copied());
            let mut quant_te = params.to_vec();
            quant_te.extend([tv, ev]);
            quant_te.extend(yvs.iter().copied());
            let mut quant_tem = params.to_vec();
            quant_tem.extend([tv, ev, mv]);
            quant_tem.extend(yvs.iter().copied());

            rel_intro.push(rel_bodies.iter().map(|t| gen_all(&quant_y, t)).collect());
            ih_slot.push(slot_bodies.iter().map(|t| gen_all(&quant_te, t)).collect());
            iota.push(gen_all(&quant_te, &iota_i));
            minor_iota.push(gen_all(&quant_tem, &mi));
            minor_eq_out.push(me);
        }

        let out = LeRecursor {
            rel_intro,
            ih_slot,
            iota,
            minor_iota,
            minor_eq: minor_eq_out,
            target: tv,
            step: ev,
            minor: mv,
        };
        if !out.all_unconditional() {
            return None
        }
        Some(out)
    }

    /// [`LeRecursor::minor_eq`] at a concrete target, step and minor — the
    /// **second** antecedent of `minor_iota[i]` once that has been instantiated
    /// at the same three, and so the formula a caller has to discharge.
    pub fn minor_eq_at(&self, i: usize, t: &Term, e: &Term, m: &Term) -> Option<Formula> {
        let f = self.minor_eq.get(i)?;
        Some(f.subst(self.target, t).subst(self.step, e).subst(self.minor, m))
    }

    /// The hypothesis half of the house rule for every theorem this carries.
    ///
    /// `rel_intro` and `ih_slot` are advertised **unconditional**; `iota` and
    /// `minor_iota` carry their antecedents *inside* the conclusion, so a
    /// sequent hypothesis would falsify those labels too. See
    /// [`crate::all_unconditional`].
    pub fn all_unconditional(&self) -> bool {
        let mut ts: Vec<&Thm> = Vec::new();
        ts.extend(self.rel_intro.iter().flatten());
        ts.extend(self.ih_slot.iter().flatten());
        ts.extend(self.iota.iter());
        ts.extend(self.minor_iota.iter());
        crate::all_unconditional(&ts)
    }
}

/// `minorᵢ(m, v⃗)` — Lean's minor premise applied **curried**, to the
/// constructor's fields in declared order and then to one induction hypothesis
/// per recursive field.
///
/// A [`Slot::Plain`] contributes the field itself; a [`Slot::Rec`] contributes
/// `•`, because a class-(S) recursive field is a *proof* — the carrier is
/// `[tup(x⃗) ∈ acc(A_φ,R)]`, a conditional singleton — and every proof
/// interprets to the point.
pub fn minor_app(
    s: &Sums,
    spec: &LeSpec,
    i: usize,
    m: &Term,
    ys: &[Term],
    vs: &[Term],
) -> Option<Term> {
    let c = spec.base.ctors.get(i)?;
    if ys.len() != c.args.len() || vs.len() != c.recs {
        return None
    }
    let mut t = m.clone();
    let mut next = 0;
    for sl in &c.order {
        match sl {
            Slot::Plain => {
                t = s.ap.apply(t, ys.get(next)?.clone());
                next += 1;
            }
            Slot::Rec => t = s.ap.apply(t, s.point()),
        }
    }
    for v in vs {
        t = s.ap.apply(t, v.clone());
    }
    Some(t)
}

/// `slotⱼ(c) = app(app(c, tup(d⃗ᵢⱼ)), •)` — the `j`-th induction hypothesis, as
/// the step sees it: the row of `c` at the child's index, applied to the proof
/// that it *is* a predecessor.
pub fn slot_at(s: &Sums, c: &Term, child: &Term) -> Term {
    s.ap.apply(s.ap.apply(c.clone(), child.clone()), s.point())
}

/// **The contract the step `e` owes the recursor**, at one constructor:
///
/// ```text
/// ∀y⃗ ∀c. ((antᵢ ∧ c ∈ ih_bound(A_φ,T) ∧ ⋀ⱼ slotⱼ(c) ∈ T) →
///           step(e, tup(e⃗ᵢ), c) = minorᵢ(m, [slotⱼ(c)]ⱼ))
/// ```
///
/// Exposed so the wiring can build a step *against* the formula it will have to
/// discharge, rather than against a transcription of it. Every binder is closed
/// by [`Formula::forall`], so two calls with different fresh variables produce
/// the **same** formula.
#[allow(clippy::too_many_arguments)]
pub fn minor_eq(
    env: &mut Env,
    s: &Sums,
    b: &Base,
    spec: &LeSpec,
    i: usize,
    yvs: &[FreeVar],
    ys: &[Term],
    ant_atoms: &[Formula],
    tup_res: &Term,
    children: &[Term],
    a_phi: &Term,
    tt: &Term,
    te: &Term,
    tm: &Term,
) -> Option<Formula> {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let slots: Vec<Term> = children.iter().map(|d| slot_at(s, &tc, d)).collect();

    let mut guard = ant_atoms.to_vec();
    guard.push(Formula::mem(tc.clone(), crate::rec_acc::ih_bound(s, a_phi, tt)));
    for v in &slots {
        guard.push(Formula::mem(v.clone(), tt.clone()));
    }
    let body = Formula::imp(
        conj_of(&guard)?,
        Formula::eq(b.step_at(te, tup_res, &tc), minor_app(s, spec, i, tm, ys, &slots)?),
    );
    let closed = Formula::forall(cv, body);
    Some(yvs.iter().rev().fold(closed, |acc, v| Formula::forall(*v, acc)))
}

/// One constructor's plain-argument typings `yⱼ ∈ βⱼ(p⃗, y₀ … y_{j−1})`.
pub(super) fn typings(spec: &LeSpec, ps: &[Term], i: usize, ys: &[Term]) -> Vec<Formula> {
    (0..ys.len())
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(spec.base.ctors[i].args[j], a))
        })
        .collect()
}

/// `⊢ H → atomᵢ` folded into `⊢ H → conj_of(atoms)`, matching [`conj_of`]'s
/// right nesting.
fn fold_conj(thms: &[Thm]) -> Option<Thm> {
    let mut acc = thms.last()?.clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = hyp_and(t, &acc)?;
    }
    Some(acc)
}

/// `φ ∧ ψ` taken apart. `Formula::and` is `¬(φ → ¬ψ)` and has no projection, so
/// this is the two `as_imp`s that undo it. Taking a formula apart produces no
/// `Thm`, so a bug here can only cause a rejection.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// The two sides of `φ ↔ ψ`, read off `(φ → ψ) ∧ (ψ → φ)`.
fn split_iff(f: &Formula) -> Option<(Formula, Formula)> {
    split_and(f)?.0.as_imp()
}

/// From `⊢ H → x = y` infer `⊢ H → (φ(x) → φ(y))`, the context given as a
/// closure over a hole.
fn hyp_leib<F: Fn(Term) -> Formula>(env: &mut Env, h_eq: &Thm, ctx: F) -> Option<Thm> {
    let (k, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    hyp_mp(&a1i(&leib, k), h_eq)
}

/// `⊢ K → ρ(⟨tup(d⃗ᵢⱼ), tup(e⃗ᵢ)⟩)` — inject into the disjunct of the relation's
/// matrix that the `LE ctor` recursion emitted for this recursive argument,
/// witnessed by the constructor's own fields.
///
/// Mirrors [`LeCarrier`]'s introduction rule one level down: there the
/// base-case equality `q = tup(e⃗ᵢ)` is closed by reflexivity, here the edge
/// equality is.
#[allow(clippy::too_many_arguments)]
fn inject_disjunct(
    spec: &LeSpec,
    le: &LeCarrier,
    s: &Sums,
    i: usize,
    j: usize,
    ps: &[Term],
    yvs: &[FreeVar],
    ys: &[Term],
    k: &Formula,
    k_atoms: &[Formula],
    np_plain: usize,
    edge_t: &Term,
) -> Option<Thm> {
    let subject = le.rel_subject;
    let at_edge: Vec<Formula> =
        le.rel_disjuncts.iter().map(|d| d.subst(subject, edge_t)).collect();
    let slot = LeCarrier::rel_slot(spec, i, j)?;

    // The witness body at `y⃗ := y⃗`: the typings, then `edge = edge`.
    let plain = typings(spec, ps, i, ys);
    let mut wit_atoms = plain.clone();
    wit_atoms.push(Formula::eq(edge_t.clone(), edge_t.clone()));
    let wit_body = conj_of(&wit_atoms)?;
    let mut parts: Vec<Thm> =
        (0..np_plain).map(|a| conj_proj(k_atoms, a)).collect::<Option<_>>()?;
    parts.push(a1i(&Thm::eq_refl(edge_t.clone()), k.clone()));
    let h_body = fold_conj(&parts)?;
    if *h_body.concl() != Formula::imp(k.clone(), wit_body) {
        return None
    }

    // Existentially close one field at a time, innermost first.
    let subj_t = Term::var(subject);
    let mut h_disj = h_body;
    for (pos, v) in yvs.iter().enumerate().rev() {
        let mut inner = plain.clone();
        inner.push(Formula::eq(
            subj_t.clone(),
            crate::opair(
                s.ap.sets.up,
                IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, ps, ys)?),
                IndexedDeclSpec::tup(s, &spec.result_vec(i, ps, ys)?),
            ),
        ));
        let body = yvs[pos + 1..]
            .iter()
            .rev()
            .fold(conj_of(&inner)?, |acc, w| Formula::exists(*w, acc));
        let body = body.subst(subject, edge_t);
        h_disj = syl(&h_disj, &exists_intro_imp(*v, body, ys[pos].clone())?)?;
    }
    syl(&h_disj, &disj_inject(&at_edge, slot)?)
}

/// `⊢ (ST ∧ minor_eq) → (K → app(F, tup(e⃗ᵢ)) = minorᵢ(m, [app(F,tup(d⃗ᵢⱼ))]))`
/// — the composition described in the module header.
#[allow(clippy::too_many_arguments)]
fn compose_minor(
    env: &mut Env,
    s: &Sums,
    ra: &RecAcc,
    spec: &LeSpec,
    i: usize,
    ys: &[Term],
    ant_atoms: &[Formula],
    tup_res: &Term,
    ih_t: &Term,
    children: &[Term],
    f: &Term,
    le: &LeCarrier,
    st: &Formula,
    me: &Formula,
    tm: &Term,
    tt: &Term,
    iota_i: &Thm,
    in_bound_all: &Thm,
    value_typed_all: &Thm,
    slot_bodies: &[Thm],
) -> Option<Thm> {
    let b = &ra.base;
    let acc_t = le.acc_set.clone();

    // K := antᵢ ∧ tup(e⃗ᵢ) ∈ acc(A_φ,R) ∧ ⋀ⱼ tup(d⃗ᵢⱼ) ∈ acc(A_φ,R)
    let mut kp_atoms = ant_atoms.to_vec();
    kp_atoms.push(Formula::mem(tup_res.clone(), acc_t.clone()));
    for d in children {
        kp_atoms.push(Formula::mem(d.clone(), acc_t.clone()));
    }
    let kp = conj_of(&kp_atoms)?;
    let h = Formula::and(st.clone(), me.clone());
    let n_h = and_left(h.clone(), kp.clone());
    let n_k = and_right(h.clone(), kp.clone());
    let n_st = syl(&n_h, &and_left(st.clone(), me.clone()))?;
    let n_me = syl(&n_h, &and_right(st.clone(), me.clone()))?;
    let proj = |idx: usize| -> Option<Thm> { syl(&n_k, &conj_proj(&kp_atoms, idx)?) };

    let n_res_acc = proj(ant_atoms.len())?;
    let mut n_child_acc = Vec::with_capacity(children.len());
    for j in 0..children.len() {
        n_child_acc.push(proj(ant_atoms.len() + 1 + j)?);
    }

    // ι at this constructor's result index.
    let n_iota = hyp_mp(&syl(&n_st, iota_i)?, &n_res_acc)?;

    // `IH ∈ ih_bound(A_φ,T)`.
    let (_, ib_body) = in_bound_all.concl().as_imp()?;
    let n_ib_all = syl(&n_st, in_bound_all)?;
    let n_ihb = hyp_mp(
        &syl(&n_ib_all, &Thm::ax_inst(ib_body, tup_res.clone())?)?,
        &n_res_acc,
    )?;

    // Per recursive argument: the slot's value, and that it is in `T`.
    let (_, vt_body) = value_typed_all.concl().as_imp()?;
    let n_vt_all = syl(&n_st, value_typed_all)?;
    let mut n_slot_eq = Vec::with_capacity(children.len());
    let mut n_slot_typed = Vec::with_capacity(children.len());
    for j in 0..children.len() {
        let n_child_phi = syl(
            &n_child_acc[j],
            &inst_all(&b.ac.acc_subset, &[le.a_phi.clone(), le.r.clone(), children[j].clone()])?,
        )?;
        let mut parts: Vec<Thm> =
            (0..ant_atoms.len()).map(proj).collect::<Option<_>>()?;
        parts.push(n_child_phi);
        let eq = syl(&fold_conj(&parts)?, &slot_bodies[j])?;

        let n_val = hyp_mp(
            &syl(&n_vt_all, &Thm::ax_inst(vt_body.clone(), children[j].clone())?)?,
            &n_child_acc[j],
        )?;
        let back = hyp_eq_symm(env, &eq)?;
        let tt_c = tt.clone();
        let carry = hyp_leib(env, &back, move |hole| Formula::mem(hole, tt_c.clone()))?;
        n_slot_typed.push(hyp_mp(&carry, &n_val)?);
        n_slot_eq.push(eq);
    }

    // `minor_eq` at `y⃗ := y⃗` and `c := IH`, guard discharged.
    let mut cur = n_me;
    for y in ys {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, y.clone())?)?;
    }
    let (_, body) = cur.concl().as_imp()?;
    let n_me_at = syl(&cur, &Thm::ax_inst(body, ih_t.clone())?)?;
    let mut parts: Vec<Thm> = (0..ant_atoms.len()).map(proj).collect::<Option<_>>()?;
    parts.push(n_ihb);
    parts.extend(n_slot_typed.iter().cloned());
    let n_step = hyp_mp(&n_me_at, &fold_conj(&parts)?)?;

    // Chain, then replace each slot by the recursive value it computes to.
    let mut out = hyp_eq_trans(env, &n_iota, &n_step)?;
    let mut vals: Vec<Term> = children.iter().map(|d| slot_at(s, ih_t, d)).collect();
    let lhs = b.app(f, tup_res);
    for j in 0..children.len() {
        let ctx_vals = vals.clone();
        let (sp, ss, ysv, tmv, lh) =
            (spec.clone(), s.clone(), ys.to_vec(), tm.clone(), lhs.clone());
        let carry = hyp_leib(env, &n_slot_eq[j], move |hole| {
            let mut vv = ctx_vals.clone();
            vv[j] = hole;
            Formula::eq(
                lh.clone(),
                minor_app(&ss, &sp, i, &tmv, &ysv, &vv).expect("the minor's spine"),
            )
        })?;
        out = hyp_mp(&carry, &out)?;
        vals[j] = b.app(f, &children[j]);
    }

    let want = Formula::eq(lhs, minor_app(s, spec, i, tm, ys, &vals)?);
    if out.concl().as_imp()?.1 != want {
        return None
    }
    uncurry(&out)
}
