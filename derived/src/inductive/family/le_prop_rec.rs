//! **Class (S)'s ι rule at `ni = 0`** — the recursor of a non-indexed
//! subsingleton eliminator, which is *not* [`super::le_rec`]'s and is not
//! `rec_acc` at all.
//!
//! # Interface
//!
//! One constructor, `k` fields, none recursive. Write `A_φ(p⃗)` for
//! [`super::LeCarrier::a_phi`] (the same set [`LeProp`] reads as a conditional
//! singleton), `βⱼ(p⃗, y⃗<ⱼ)` for the `j`-th field's type,
//! `minor(m, y⃗)` for [`super::le_rec::minor_app`] at constructor 0, `•⃗` for `k`
//! copies of the point, and
//!
//! ```text
//! Pⱼ  :=  βⱼ(p⃗, y⃗<ⱼ) ⊆ 1          the field is a PROPOSITION      (§5.3)
//! Hⱼ  :=  yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)         the field inhabits its type
//! G   :=  P₀ ∧ … ∧ P_{k-1} ∧ H₀ ∧ … ∧ H_{k-1}      (absent when k = 0)
//! rec(m) := {⟨•, minor(m, •⃗)⟩}                      [le_prop_rec::rec_term]
//! ```
//!
//! Then, eliding a leading `∀p⃗ ∀m ∀y⃗`:
//!
//! ```text
//! ⊢ ∀p⃗ ∀z. (z ∈ A_φ(p⃗) → z = •)                            [carrier_point]
//! ⊢ (G → minor(m, y⃗) = minor(m, •⃗))                        [erase]   (k ≥ 1)
//! ⊢ ([G →] app(rec(m), •) = minor(m, y⃗))                    [iota_at_point]
//! ⊢ ∀z. ((G ∧ z ∈ A_φ(p⃗)) → app(rec(m), z) = minor(m, y⃗))   [iota]
//! ⊢ ∀m ∀T. (minor(m, •⃗) ∈ T → rec(m) ∈ fs(1, T))            [rec_typed]
//! ```
//!
//! All five are **unconditional**; every hypothesis is spelled inside the
//! conclusion. `erase` is `None` exactly when `k = 0`, where `G` is empty and
//! `minor(m, •⃗)` *is* `m` — see "the empty antecedent" below.
//!
//! The `Hⱼ` occupy positions `k .. 2k` of `G`'s conjunct list, contiguously and
//! in order, so a consumer holding [`super::LeCarrier::intro`]`[0]` — whose
//! antecedent at `ni = 0` is exactly `conj_of(H₀ … H_{k-1})` — recovers it with
//! one [`crate::conj_sub`] rather than rebuilding it. The `Pⱼ` are the new
//! obligation and are grouped in front for that reason.
//!
//! # Does `ni = 0` collapse [`super::le_rec`]'s two objects into one?
//!
//! **No — it degenerates them apart, and that is why this file exists rather
//! than a relaxed guard in [`super::le_rec`].**
//!
//! [`super::le_rec`]'s header records that `rec_acc`'s step `e` is addressed by
//! the *index tuple* while a §5.3 minor `m` is addressed by the constructor's
//! *fields*, and that the map index-tuple ↦ fields is §5.3's delayed
//! elimination. At `ni = 0` the index tuple is `tup(•) = •` — a single closed
//! term, the **same** one for every constructor and every field assignment. So:
//!
//! * `e` is addressed by *nothing*. `step(e, tup(e⃗₀), c)` is
//!   `app(app(app(e,•),•),c)`, which cannot mention `y⃗`;
//! * `minor(m, y⃗)` still varies with `y⃗`.
//!
//! [`super::le_rec::minor_eq`] is `∀y⃗ ∀c. (… → step(e, tup(e⃗ᵢ), c) = minorᵢ(…))`
//! with the `∀y⃗` on the outside, so at `ni = 0` it is satisfiable **only** when
//! the minor is constant in its fields on the antecedent's domain. The gap is
//! wider at `ni = 0` than at `ni ≥ 1`, not narrower: there, `e⃗ᵢ(p⃗,y⃗)` genuinely
//! depends on `y⃗` and the map is at least conceivable.
//!
//! What closes it is §5.3's own side condition (`thesis.txt:1866–1870`): every
//! non-propositional non-recursive argument must appear in the result index. At
//! `ni = 0` there are no result indices, so **every** field is propositional —
//! `βⱼ ⊆ 1`, hence `yⱼ = •` — and the minor *is* constant in its fields. That is
//! [`LePropRecursor::erase`], and it is the delayed elimination at `ni = 0`:
//! the map `• ↦ y⃗` does not exist, and it does not have to, because nothing
//! downstream can tell `y⃗` from `•⃗`.
//!
//! `IndexedDeclSpec` records no "this field is a proposition" flag, so `Pⱼ` is a
//! **hypothesis** spelled in the conclusion, exactly as
//! [`super::le_rec::minor_eq`] is. A caller holding `βⱼ ∈ U₀` discharges it in
//! one step from [`crate::tower::Tower::u0_subsingleton`]-style irrelevance; a
//! caller that cannot is telling us the declaration is not §5.3's.
//!
//! # Why there is no `acc`, and why a recursive field is refused
//!
//! At `ni = 0` a recursive field's *child* index tuple is `tup(d⃗₀ⱼ) = •` as
//! well — the same term as the constructor's own result index. So the edge
//! [`super::le_rec::LeRecursor::rel_intro`] would derive is `⟨•,•⟩ ∈ R`, a self
//! loop, and `acc(A_φ,R)` is then empty: every ι rule `rec_acc` could offer is
//! guarded by `tup(e⃗ᵢ) ∈ acc(A_φ,R)` and would be vacuously true. `rec_acc` has
//! nothing to contribute at `ni = 0` in either direction — with no recursive
//! field `R` is empty and [`super::LeCarrier::degenerate`] collapses
//! `acc(A_φ,R)` to `A_φ` without unfolding anything. [`LePropRecursor::build`]
//! therefore refuses `recs > 0` rather than producing vacuous theorems, and
//! takes neither a [`crate::rec_acc::RecAcc`] nor a [`crate::rec_acc::Bounded`].
//!
//! The recursor is consequently not a fixpoint but a **one-point function**:
//! `A_φ ⊆ 1`, so the only argument it can ever be applied to is `•`, and
//! [`crate::point_fun::PointFun`] already proves the three clauses such a graph
//! needs. `rec_typed` lands in `fs(1,T)` and not in `fs(A_φ,T)`: `A_φ` is `1`
//! only when ψ holds ([`LeProp::true_`]), and a consumer that has ψ has the
//! equation to retarget with.
//!
//! # More than one constructor is refused
//!
//! Also `recs`-free: at `ni = 0` every constructor's result index is `•`, so
//! two constructors are indistinguishable in the carrier and no ι rule can
//! choose between their minors. That is Lean's own condition for large
//! elimination of a `Prop` (at most one constructor), read off the set model
//! rather than assumed, and [`LePropRecursor::build`] enforces it. A
//! **constructor-less** declaration (`False`, `Empty`) is refused too and needs
//! nothing: ψ is `⊥`, so [`LeProp::false_`] gives `⊢ A_φ(p⃗) = 0` and the
//! elimination is ex falso.
//!
//! # The empty antecedent
//!
//! At `k = 0` (`PUnit.unit`, `True.intro`) `G` has no conjuncts, and this kernel
//! has no `⊤` to weaken it to — the same situation
//! [`super::LeCarrier::intro_is_conditional`] reports for the introduction rule,
//! and the answer here is the same predicate: `intro_is_conditional(spec, 0)` is
//! `Some(k > 0)` at `ni = 0`, and it decides whether `erase` exists and whether
//! `iota_at_point` carries an antecedent. [`LePropRecursor::iota`] is **not**
//! affected: its antecedent always contains `z ∈ A_φ(p⃗)`, so it is conditional
//! at every `k`.
//!
//! # Non-vacuity
//!
//! `derived/tests/family_le_prop_rec.rs` fires `iota` at a two-field
//! declaration (`And`-shaped) with both fields' types *closed and inhabited*,
//! discharges `G` outright, and lands on `app(rec(m), •) = app(app(m,•),•)` at a
//! minor `m` that is a genuine two-argument graph — so the recursor computes to
//! the minor's value and not to a constant chosen in advance. It also pins
//! `erase` at three *distinct* field assignments and the `k = 0` shape beside
//! the `k = 2` one.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::inductive::machine::Machine;
use crate::inductive::spec::Slot;
use crate::point_fun::PointFun;
use crate::sums::Sums;
use crate::wrec::hyp_eq_trans;
use crate::{
    a1i, conj_of, conj_proj, conj_sub, gen_all, hyp_mp, inst_all, syl,
};

use super::index::IndexSpace;
use super::le::{LeCarrier, LeSpec};
use super::le_prop::LeProp;
use super::le_rec::{minor_app, typings};

/// Class (S)'s recursor at `ni = 0`: a one-point function, and the field
/// erasure that makes its ι rule Lean-shaped.
pub struct LePropRecursor {
    /// `⊢ ∀p⃗ ∀z. (z ∈ A_φ(p⃗) → z = •)` — the carrier is inside `1`, so the
    /// only major premise the recursor can ever meet is the point.
    pub carrier_point: Thm,
    /// `⊢ ∀p⃗ ∀m ∀y⃗. (G → minor(m, y⃗) = minor(m, •⃗))` — §5.3's delayed
    /// elimination at `ni = 0`. `None` exactly when the constructor has no
    /// fields, where the statement would be `⊢ m = m`.
    pub erase: Option<Thm>,
    /// `⊢ ∀p⃗ ∀m ∀y⃗. ([G →] app(rec(m), •) = minor(m, y⃗))` — ι at the major
    /// premise Lean's constructor actually denotes.
    pub iota_at_point: Thm,
    /// `⊢ ∀p⃗ ∀m ∀y⃗ ∀z. ((G ∧ z ∈ A_φ(p⃗)) → app(rec(m), z) = minor(m, y⃗))` —
    /// ι at *any* member of the carrier, which is the form a consumer whose
    /// `⟦t⟧` is not syntactically `•` needs.
    pub iota: Thm,
    /// `⊢ ∀m ∀T. (minor(m, •⃗) ∈ T → rec(m) ∈ fs(1, T))`.
    pub rec_typed: Thm,
    /// The variable the statements above quantify the minor premise `m` with.
    pub minor: FreeVar,
    /// The same for the target `T` of [`LePropRecursor::rec_typed`].
    pub target: FreeVar,
    /// The `k` variables `y⃗` are quantified with, outermost first — kept so a
    /// consumer instantiating `iota` at concrete fields knows the order.
    pub fields: Vec<FreeVar>,
}

/// `rec(m) = {⟨•, minor(m, •⃗)⟩}` — the recursor at a caller's own minor.
///
/// A free function rather than a method: the theorems above are stated at a
/// bound `m`, so a caller instantiates them and rebuilds the term here with the
/// *same* code, instead of comparing against a stored copy at a variable it
/// does not have.
///
/// `None` on a spec with no constructors, or one whose single constructor has a
/// recursive field — the two cases [`LePropRecursor::build`] refuses.
pub fn rec_term(s: &Sums, spec: &LeSpec, m: &Term) -> Option<Term> {
    let c = spec.base.ctors.first()?;
    if c.recs != 0 {
        return None
    }
    let pts = vec![s.point(); c.args.len()];
    Some(PointFun::of(s, s.point(), minor_app(s, spec, 0, m, &pts, &[])?))
}

impl LePropRecursor {
    /// Build every rule above.
    ///
    /// `ix`, `lc` and `lp` must be the index space, carrier and conditional
    /// singleton of `spec` at `params`, and `pf` a [`PointFun`] over the same
    /// [`Sums`] — all checked, because a look-alike would make every equation
    /// below speak about a different set.
    ///
    /// Returns `None` on a spec that is not
    /// [`well_formed`](super::spec::IndexedDeclSpec::well_formed), on an
    /// **indexed** one (that is [`super::le_rec`]'s), on one without exactly one
    /// constructor, on one whose constructor has a recursive field, on a
    /// parameter-count mismatch, on a hypothetical input, or when any shape
    /// check fails.
    #[allow(clippy::too_many_arguments)]
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        pf: &PointFun,
        spec: &LeSpec,
        ix: &IndexSpace,
        lc: &LeCarrier,
        lp: &LeProp,
        params: &[FreeVar],
    ) -> Option<LePropRecursor> {
        if !spec.well_formed()
            || spec.num_indices() != 0
            || ix.num_indices() != 0
            || spec.len() != 1
            || params.len() != spec.params()
        {
            return None
        }
        let c = &spec.base.ctors[0];
        if c.recs != 0 || c.order.len() != c.args.len() {
            return None
        }
        // Nothing hypothetical rides into a conclusion this file labels `⊢`.
        if !crate::all_unconditional(&[
            &lp.chi_at_params,
            &lc.phi_ax,
            &pf.app,
            &pf.in_fs,
        ]) {
            return None
        }
        let s = mach.wt.sums.clone();
        // `lp` really describes `lc`'s carrier, and `pf` really is over `s`.
        if lp.set != lc.a_phi {
            return None
        }
        let (pa, pb) = (env.fresh_var(), env.fresh_var());
        let want_app = Formula::forall(
            pa,
            Formula::forall(
                pb,
                Formula::eq(
                    s.ap.apply(PointFun::of(&s, Term::var(pa), Term::var(pb)), Term::var(pa)),
                    Term::var(pb),
                ),
            ),
        );
        if *pf.app.concl() != want_app {
            return None
        }

        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let a_phi = lc.a_phi.clone();
        let unit = s.unit();
        let point = s.point();
        let k = c.args.len();

        let carrier_point = carrier_point(env, &s, lp, params)?;

        // ── `G`, and the field-by-field `⊢ G → yⱼ = •` ──────────────────────
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let hs = typings(spec, &ps, 0, &ys);
        let mut atoms: Vec<Formula> = (0..k)
            .map(|j| {
                let mut a = ps.clone();
                a.extend(ys[..j].iter().cloned());
                kernel::thm::subset(env, Term::apply(c.args[j], a), unit.clone())
            })
            .collect();
        atoms.extend(hs.iter().cloned());
        let g = conj_of(&atoms);

        let (mv, tv) = (env.fresh_var(), env.fresh_var());
        let tm = Term::var(mv);
        let pts = vec![point.clone(); k];
        let minor_y = minor_app(&s, spec, 0, &tm, &ys, &[])?;
        let minor_pt = minor_app(&s, spec, 0, &tm, &pts, &[])?;
        let rec = rec_term(&s, spec, &tm)?;

        let erase = match &g {
            None => None,
            Some(gf) => {
                let mut acc = a1i(&Thm::eq_refl(tm.clone()), gf.clone());
                for (j, sl) in c.order.iter().enumerate() {
                    if *sl != Slot::Plain {
                        return None
                    }
                    let at_y = mem_is_point(&s, &atoms, j, k, &ys[j])?;
                    acc = app_cong(env, gf, &s, &acc, &at_y)?;
                }
                if *acc.concl() != Formula::imp(gf.clone(), Formula::eq(minor_y.clone(), minor_pt.clone()))
                {
                    return None
                }
                Some(acc)
            }
        };

        // ── ι at the point ─────────────────────────────────────────────────
        //
        // `app(rec(m), •) = minor(m, •⃗)` is `point_app`; `erase` turns the
        // right-hand side into the minor at the *fields*, which is what Lean's
        // ι rule says.
        let at_pt = inst_all(&pf.app, &[point.clone(), minor_pt.clone()])?;
        let iota_at_point = match (&g, &erase) {
            (None, _) => at_pt.clone(),
            (Some(gf), Some(e)) => {
                let back = crate::eq_symm_imp(env, minor_y.clone(), minor_pt.clone());
                hyp_eq_trans(env, &a1i(&at_pt, gf.clone()), &syl(e, &back)?)?
            }
            (Some(_), None) => return None,
        };
        let want_pt_body =
            Formula::eq(s.ap.apply(rec.clone(), point.clone()), minor_y.clone());
        if *iota_at_point.concl() != wrap(&g, want_pt_body.clone()) {
            return None
        }

        // ── ι at any member of the carrier ─────────────────────────────────
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let mut atoms2 = atoms.clone();
        atoms2.push(Formula::mem(tz.clone(), a_phi.clone()));
        let g2 = conj_of(&atoms2)?; // never empty: `z ∈ A_φ(p⃗)` is always there

        let z_pt = syl(
            &conj_proj(&atoms2, atoms.len())?,
            &inst_all(&carrier_point, &ps)?.pipe_inst(&tz)?,
        )?;
        let moved = cong(env, &g2, &z_pt, |t| s.ap.apply(rec.clone(), t))?;
        let lifted = match &g {
            None => a1i(&iota_at_point, g2.clone()),
            Some(_) => syl(&conj_sub(&atoms2, 0, atoms.len())?, &iota_at_point)?,
        };
        let iota_body = hyp_eq_trans(env, &moved, &lifted)?;
        let want_iota = Formula::imp(
            g2,
            Formula::eq(s.ap.apply(rec.clone(), tz.clone()), minor_y.clone()),
        );
        if *iota_body.concl() != want_iota {
            return None
        }

        // ── Typing ─────────────────────────────────────────────────────────
        let rec_typed_body =
            inst_all(&pf.in_fs, &[point.clone(), minor_pt.clone(), Term::var(tv)])?;

        // ── Generalise ─────────────────────────────────────────────────────
        let mut quant: Vec<FreeVar> = params.to_vec();
        quant.push(mv);
        quant.extend(yvs.iter().copied());
        let mut quant_z = quant.clone();
        quant_z.push(zv);
        let mut quant_t: Vec<FreeVar> = params.to_vec();
        quant_t.push(mv);
        quant_t.push(tv);

        Some(LePropRecursor {
            carrier_point,
            erase: erase.as_ref().map(|e| gen_all(&quant, e)),
            iota_at_point: gen_all(&quant, &iota_at_point),
            iota: gen_all(&quant_z, &iota_body),
            rec_typed: gen_all(&quant_t, &rec_typed_body),
            minor: mv,
            target: tv,
            fields: yvs,
        })
    }

    /// Every theorem above rests on nothing.
    pub fn all_unconditional(&self) -> bool {
        let mut v = vec![&self.carrier_point, &self.iota_at_point, &self.iota, &self.rec_typed];
        if let Some(e) = &self.erase {
            v.push(e);
        }
        crate::all_unconditional(&v)
    }
}

/// `⊢ ∀p⃗ ∀z. (z ∈ A_φ(p⃗) → z = •)`.
///
/// [`crate::prop::cond_subset_unit`] already turns [`LeProp::chi_at_params`]
/// into `A_φ(p⃗) ⊆ 1` — including the shape check on χ, so a `LeProp` whose
/// fields have drifted from its own header is refused there rather than
/// described here — and [`crate::sums::unit_eta`] is the second half. Two
/// lines, and the only place this file touches `LeProp`.
fn carrier_point(
    env: &mut Env,
    s: &Sums,
    lp: &LeProp,
    params: &[FreeVar],
) -> Option<Thm> {
    let sub = crate::prop::cond_subset_unit(env, s, &lp.psi, &lp.set, &lp.chi_at_params)?;
    if !crate::all_unconditional(&[&sub]) {
        return None
    }
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let at = inst_all(&sub, std::slice::from_ref(&tz))?;
    let out = syl(&at, &inst_all(&s.unit_eta, std::slice::from_ref(&tz))?)?;
    let want = Formula::imp(
        Formula::mem(tz.clone(), lp.set.clone()),
        Formula::eq(tz, s.point()),
    );
    if *out.concl() != want {
        return None
    }
    let mut quant = params.to_vec();
    quant.push(zv);
    Some(gen_all(&quant, &out))
}

/// `⊢ G → yⱼ = •`, from `Pⱼ` (`βⱼ ⊆ 1`) and `Hⱼ` (`yⱼ ∈ βⱼ`).
///
/// `atoms` is `G`'s conjunct list with the `k` subset clauses first and the `k`
/// typings after, so `Pⱼ` is at `j` and `Hⱼ` at `k + j`.
fn mem_is_point(
    s: &Sums,
    atoms: &[Formula],
    j: usize,
    k: usize,
    y: &Term,
) -> Option<Thm> {
    let p_j = conj_proj(atoms, j)?; // ⊢ G → ∀x. (x ∈ βⱼ → x ∈ 1)
    let h_j = conj_proj(atoms, k + j)?; // ⊢ G → yⱼ ∈ βⱼ
    let (_, all) = p_j.concl().as_imp()?;
    let at_y = syl(&p_j, &Thm::ax_inst(all, y.clone())?)?; // ⊢ G → (yⱼ ∈ βⱼ → yⱼ ∈ 1)
    let in_unit = hyp_mp(&at_y, &h_j)?;
    let eta = inst_all(&s.unit_eta, std::slice::from_ref(y))?;
    syl(&in_unit, &eta)
}

/// From `⊢ G → p = q` infer `⊢ G → C[p] = C[q]`, for a term context `C`.
///
/// Leibniz at `φ(x) := (C[p] = C[x])`, whose `φ[p]` is reflexivity. The guard
/// is threaded with one [`syl`] and one [`hyp_mp`]; there is no deduction
/// theorem to open it with.
fn cong(
    env: &mut Env,
    g: &Formula,
    pq: &Thm,
    mk: impl Fn(Term) -> Term,
) -> Option<Thm> {
    let (_, eq) = pq.concl().as_imp()?;
    let (p, q) = eq.as_eq()?;
    let lhs = mk(p.clone());
    let h = env.fresh_var();
    let phi = Formula::eq(lhs.clone(), mk(Term::var(h)));
    let under = syl(pq, &Thm::eq_leibniz(p, q, h, phi))?;
    hyp_mp(&under, &a1i(&Thm::eq_refl(lhs), g.clone()))
}

/// From `⊢ G → f = f'` and `⊢ G → a = a'` infer `⊢ G → app(f,a) = app(f',a')`.
///
/// The one step of the curried spine [`minor_app`] builds, run under `G`.
fn app_cong(
    env: &mut Env,
    g: &Formula,
    s: &Sums,
    fe: &Thm,
    xe: &Thm,
) -> Option<Thm> {
    let (_, feq) = fe.concl().as_imp()?;
    let (_, xeq) = xe.concl().as_imp()?;
    let (_, f2) = feq.as_eq()?;
    let (x1, _) = xeq.as_eq()?;
    let left = cong(env, g, fe, |t| s.ap.apply(t, x1.clone()))?;
    let right = cong(env, g, xe, |t| s.ap.apply(f2.clone(), t))?;
    hyp_eq_trans(env, &left, &right)
}

/// `[G →] φ`, matching [`conj_of`]'s absent-antecedent case.
fn wrap(g: &Option<Formula>, phi: Formula) -> Formula {
    match g {
        Some(h) => Formula::imp(h.clone(), phi),
        None => phi,
    }
}

/// Instantiate one leading `∀`, as an extension trait so the ι derivation reads
/// left to right.
trait PipeInst {
    fn pipe_inst(&self, t: &Term) -> Option<Thm>;
}

impl PipeInst for Thm {
    fn pipe_inst(&self, t: &Term) -> Option<Thm> { inst_all(self, std::slice::from_ref(t)) }
}
