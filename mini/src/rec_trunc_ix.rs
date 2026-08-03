//! **The class-(P) eliminator at an index** — `⟦T.rec.{σ}⟧` for a family
//! [`crate::class_p_ix`] translated.
//!
//! # Interface
//!
//! ```text
//! rec_trunc_ix::ensure(checker, T, σ_T, T.rec, σ_rec, ClassPIx)
//! ```
//!
//! Called from [`crate::recursor::ensure`]'s class-(P)-at-an-index arm and from
//! nowhere else. On success `⟦T.rec.{σ_rec}⟧ = •` and its typing are in the
//! store under the recursor's own instantiation.
//!
//! # The obligation, and why it is `rec_ix_prop`'s with one set changed
//!
//! A class-(P) recursor has **no extra level parameter** — that is what class
//! (P) *means* — so its motive is `Sort 0` at every σ and there is no §6.2
//! split to make: the eliminator is always a proof, `⟦T.rec⟧ = •`, and
//! [`crate::rec_ix_dep`]'s value clause has no counterpart here. What is owed
//! is [`IndexedTruncRecursor`]:
//!
//! ```text
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. ( t ∈ ‖ind(p⃗,x⃗)‖ → • ∈ app(m, x⃗, t) ) )
//! ```
//!
//! which is [`IndexedPropRecursor`](derived::inductive::family::IndexedPropRecursor)'s
//! statement with `ind(p⃗,x⃗)` replaced by its truncation. So the nest is the
//! same `np + 1 + n + ni + 1` deep, the minors are [`crate::minor_ix`]'s at
//! [`Clause::trunc`], and the only step of the firing that differs is the major
//! premise: the scope holds `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧` and `⟦T p⃗ x⃗⟧` is now the
//! truncation, so the β down the type former's nest is followed by
//! [`ClassPIx::abbrev`], one Leibniz further than the class-(T) route needs.
//!
//! # The δ-redex is not this module's, and measuring said which pair it is
//!
//! `SortElimProp2.mk`'s second result index is `id.{1} Bool b1`, so
//! `sortElimProp2Rec`'s **declared** minor is `motive b2 b1 (mk b b1 b2)` while
//! `SortElimProp2.rec`'s own is `motive b2 (id.{1} Bool b1) (mk b b1 b2)`. It
//! is natural to expect the two spellings to meet inside the minor walk, one
//! argument of one motive spine apart, and to need a bridge here. **They do
//! not, and this module builds none.**
//!
//! This route reads the Lean minor off `SortElimProp2.rec`'s *own* exported
//! type ([`ConstantInfo::Recursor`]'s `ty`, via `local_type`), which is the
//! spelling with `id.{1} Bool b1` in it — the same expression
//! [`crate::zoneb::spec_of`] read off the constructor's codomain and abbreviated
//! as `eᵢ₁`. So the walk's conclusion and `IndexedTruncRecursor::minors` are at
//! the same term and there is nothing to convert.
//!
//! The two spellings do meet, one pair over: `sortElimProp2Rec := SortElimProp2.rec`
//! asks `⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧` at the **alias's** declared type, and *that* is
//! where `⟦rec's own type⟧` has to convert to `⟦the alias's type⟧`. It is
//! discharged by `assert_def_eq` with no help from any carrier, exactly as
//! `kernel::tests::a_delta_redex_in_an_argument_converts_under_a_binder`
//! measured it — δ+β on `id`, unconditional in both directions. Wren's
//! measurement was right and the placement of it in `SCOPING.md` §7 ("the
//! pair's last obligation") is the accurate one; the reading that put it in the
//! minor is this header's own first draft, corrected by a run.
//!
//! # Nothing here searches
//!
//! The rule comes from a memo keyed on the declaration
//! ([`IndApparatus::indexed_trunc_recursor`](crate::interp::IndApparatus)); the
//! index expressions come from the checker's own telescope and are inferred;
//! every equation is a defining axiom this declaration's translation kept. Each
//! finished minor is compared against
//! [`IndexedTruncRecursor::minors`] rebuilt at mini's own terms, and the
//! bottom's membership against `⟦C x⃗ t⟧` inferred from the recursor's declared
//! codomain.

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use derived::inductive::family::{motive_app, IndexedTruncRecursor};

use crate::class_p_ix::ClassPIx;
use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::Name;
use crate::interp::Interp;
use crate::kernel::{Checker, Typing, R};
use crate::minor_ix::{self, At, Clause, Fam, Site};
use crate::rec_dep::subst_f;

const ARITY: &str = "class (P) eliminator at an index: arity";
const DISAGREE: &str =
    "class (P) eliminator at an index: the recursor and the carrier disagree";
const MINOR: &str =
    "class (P) eliminator at an index: a minor premise does not transport";
const CARRIER: &str = "class (P) eliminator at an index: the carrier at the index binders";
const CODOMAIN: &str =
    "class (P) eliminator at an index: the codomain is not the motive at x⃗ and t";
/// **The walk produced a premise and it is not the rule's.** A different
/// failure from [`MINOR`], which is the walk not getting there at all, and
/// worth its own row: this one means every bridge fitted and the *statement*
/// still differs, which is the shape a wrong atom order produces.
const SHAPE: &str =
    "class (P) eliminator at an index: a minor premise is not the rule's statement";

/// **`IndexedTruncRecursor::over_family` declined this declaration** — the one
/// `Cause::Library` exit of this module.
pub const RULE: &str =
    "class (P) eliminator at an index: IndexedTruncRecursor::over_family declined";

/// Make `⟦T.rec.{σ_rec}⟧` available for an indexed class-(P) declaration.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    cp: Rc<ClassPIx>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w, Cause::Threading);
    let ctors = match c.environment().get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) => ctors.clone(),
        _ => return Err(Gap::NoInterpretation(ind_name.clone(), ind_inst.to_vec())),
    };
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    };
    let (np, n, ni) = (*num_params as usize, *num_minors as usize, *num_indices as usize);
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    }
    // **No §6.2 split.** A class-(P) recursor's motive is `Sort 0` — the
    // absence of the extra level parameter is what put the declaration on this
    // route in the first place — so `rec_inst` is the declaration's own and
    // there is no value clause to choose between.
    let rec_ty = crate::ground::subst_ground(ty, lparams, rec_inst);
    if cp.np() != np || cp.ni() != ni || cp.walk.spec.len() != n || ctors.len() != n {
        return Err(bad(DISAGREE))
    }
    let depth = np + 1 + n + ni + 1;
    let codomain = crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad(ARITY))?;

    let site = Site {
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        rec: rec_name.clone(),
        rec_inst: rec_inst.to_vec(),
        ctors,
        np,
        n,
        ni,
        depth,
        codomain,
        fam: Fam::ClassP(cp),
        minor_gap: MINOR,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// The bottom of `⟦T.rec⟧`'s nest: `⊢ • ∈ ⟦C x⃗ t⟧`.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let Some(cp) = site.fam.class_p().cloned() else { return gap(bad(DISAGREE)) };

    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((tms, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    // **Not read for class (P), and kept empty rather than faked.** A class-(P)
    // constructor's interpretation is `•`, so `minor_ix`'s conclusion step has
    // no constructor spine to β down and never indexes this.
    let ctor_formers = Vec::new();

    let Some(vars) = c.scope_vars(site.depth) else { return gap(Gap::NoEndpoint) };
    let (np, n, ni, depth) = (site.np, site.n, site.ni, site.depth);
    let at = At {
        ps: tms[..np].to_vec(),
        param_mems: mems[..np].to_vec(),
        c_tm: tms[np].clone(),
        s_tms: tms[np + 1..np + 1 + n].to_vec(),
        s_mems: mems[np + 1..np + 1 + n].to_vec(),
        xs: tms[np + 1 + n..depth - 1].to_vec(),
        x_mems: mems[np + 1 + n..depth - 1].to_vec(),
        t_tm: tms[depth - 1].clone(),
        t_mem: mems[depth - 1].clone(),
        former,
        ctor_formers,
        goal,
        vars,
        all: tms.clone(),
    };
    if at.xs.len() != ni {
        return gap(bad(DISAGREE))
    }

    // The rule, once per declaration — one `w_rect` Separation per build.
    let tr = {
        let key = (site.ind.clone(), site.inst.clone());
        let (base, fam, tc) = (cp.base.clone(), cp.ii.clone(), cp.tc.clone());
        let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
        let Some((kenv, app, _)) = ip.ind_parts() else { return gap(Gap::IndApparatus) };
        let Some(trunc) = app.trunc(kenv) else { return gap(Gap::IndApparatus) };
        match app.indexed_trunc_recursor(kenv, &key, &trunc, &base, &fam, &tc) {
            Some(r) => r,
            None => return gap(Gap::Recursor(site.ind.clone(), RULE, Cause::Library)),
        }
    };
    if tr.minors.len() != n || tr.xvs.len() != ni {
        return gap(bad(DISAGREE))
    }

    let mut minors = Vec::with_capacity(n);
    for i in 0..n {
        let Some(cs) = cp.walk.spec.base.ctors.get(i) else { return gap(bad(DISAGREE)) };
        // `nvars` is the **plain** field count: a recursive field of a
        // `Prop`-valued family is a proof, so `MINORᵢ` does not quantify it.
        let clause =
            Clause { nvars: cs.args.len(), proof: true, motive: tr.motive, trunc: true };
        let (src, mvars) = match (tr.minor_atoms.get(i), tr.minor_vars.get(i)) {
            (Some(a), Some(v)) => (a.clone(), v.clone()),
            _ => return gap(bad(DISAGREE)),
        };
        match minor_ix::transport(c, site, &at, i, &src, &mvars, clause) {
            Ok(t) => {
                if *t.thm.concl() != subst_f(&tr.minors[i], &t.sub) {
                    return gap(bad(SHAPE))
                }
                minors.push(t.thm)
            }
            Err(g) => return gap(g),
        }
    }

    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match fire(ip, site, &cp, &tr, &at, &minors) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// The rule at `(⟦p⃗⟧, ⟦C⟧)`, discharged by the minors and fired at the index
/// binders and the major premise.
fn fire(
    ip: &mut Interp,
    site: &Site,
    cp: &Rc<ClassPIx>,
    tr: &IndexedTruncRecursor,
    at: &At,
    minors: &[Thm],
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let s = ip.prelude.tower.sums.clone();
    let point = ip.point();

    // `⟦C x⃗ t⟧` is the motive's own curried spine — checked, because a recursor
    // concluding at some *fixed* index is a well-typed `Π` and is exactly what a
    // wiring that ignored the major premise would satisfy.
    if at.goal != motive_app(&s, &at.c_tm, &at.xs, &at.t_tm) {
        return Err(bad(CODOMAIN))
    }

    let mut args = at.ps.clone();
    args.push(at.c_tm.clone());
    let rule = derived::inst_all(&tr.rec, &args).ok_or_else(|| bad(DISAGREE))?;
    let all = minors
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("class (P) eliminator at an index: a declaration with no constructors"))?;
    let over = Thm::mp(&rule, &all).ok_or_else(|| bad(MINOR))?;

    let mut ia = at.xs.clone();
    ia.push(at.t_tm.clone());
    let at_t = derived::inst_all(&over, &ia).ok_or_else(|| bad(CARRIER))?;

    // The scope holds `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧`; the rule speaks of `‖ind(p⃗,⟦x⃗⟧)‖`. One
    // β down the type former's nest and one abbreviation — the class-(T) route
    // stops after the β, and this extra Leibniz is the whole of the difference,
    // because `⟦T p⃗ x⃗⟧` is the truncation and not the base. The `x⃗` need no
    // symbol move at all: they are `∀`-bound in the rule, so they are
    // instantiated at the interpretations directly.
    let mut sa = at.ps.clone();
    sa.extend(at.xs.iter().cloned());
    let mut sm = at.param_mems.clone();
    sm.extend(at.x_mems.iter().cloned());
    let (_, beta) = ip.beta_spine(&at.former, &sa, &sm).ok_or_else(|| bad(CARRIER))?;
    let held = at.t_mem.concl().as_mem().ok_or_else(|| bad(CARRIER))?.1;
    if beta.concl().as_eq().ok_or_else(|| bad(CARRIER))?.0 != held {
        return Err(bad(CARRIER))
    }
    let ax_at = derived::inst_all(&cp.abbrev, &sa).ok_or_else(|| bad(CARRIER))?;
    let to_trunc = derived::eq_trans(&mut ip.env, &beta, &ax_at).ok_or_else(|| bad(CARRIER))?;
    let t_in = ip.retarget_set(&at.t_mem, &to_trunc).ok_or_else(|| bad(CARRIER))?;
    let mem = Thm::mp(&at_t, &t_in).ok_or_else(|| bad(CARRIER))?;
    if *mem.concl() != Formula::mem(point.clone(), at.goal.clone()) {
        return Err(bad("class (P) eliminator at an index: the rule did not land in the codomain"))
    }
    Ok((point, mem))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class_p_ix::tests::{cell_env, cells};
    use crate::expr::{konst, Level};
    use crate::interp::Interp;
    use crate::kernel::Checker;

    /// **The same four corners of `(kᵢ, mᵢ)`, at the eliminator** —
    /// `crate::class_p_ix::tests::cells`, which is where the argument for the
    /// walk is. One family of declarations across three layers, so a cell
    /// cannot be covered at the carrier and silently absent at the rule.
    ///
    /// # What only `Pc` and `Pd` can say
    ///
    /// `072_sortElimProp2Rec` has `recs = 0`, so the corpus exercises
    /// `Clause::trunc`'s **easy** half and nothing else: every level is a bound
    /// plain field, the bound levels are trivially a prefix, and no induction
    /// hypothesis is fired. `Pc` and `Pd` are the only witnesses in the
    /// repository for the other half —
    ///
    /// * a `Slot::Rec` level whose atom is `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖` and whose binder
    ///   the rule does **not** quantify, so the bound levels stop being a
    ///   prefix and `Clause::binds` is load-bearing;
    /// * an induction hypothesis at `•`, which needs proof irrelevance on the
    ///   recursive binder — the one equation `minor_ix` builds from a typing it
    ///   kept at an earlier level rather than from a defining axiom.
    ///
    /// `Nat.le`, `Nat.le.below` and `List.Mem` would witness both from a real
    /// file, and are in the prelude and `grind-ring-5` rather than the
    /// tutorials. A passing corpus run is not evidence for this half.
    ///
    /// Three assertions per cell, each ruling out a different vacuous pass: the
    /// typing is **unconditional**, so no minor's hypothesis escaped its binder;
    /// it is about `•`, which is what a class-(P) eliminator denotes; and its
    /// set is `⟦the recursor's declared type⟧` *inferred*, so a derivation that
    /// landed in the motive at some other index fails.
    #[test]
    fn the_class_p_indexed_eliminator_is_interpreted_at_every_field_shape() {
        let no: std::rc::Rc<[Level]> = Vec::new().into();
        for (name, np, ty, ctors) in cells() {
            let n = Name::simple(name);
            let (env, _) = cell_env(name, np, ty, &ctors);
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            c.infer_type(&konst(n.clone(), no.clone())).expect("infer ⟦T⟧");
            let rec = Name::str(&n, "rec");
            let got = c
                .infer_type(&konst(rec.clone(), no.clone()))
                .unwrap_or_else(|e| panic!("{name}: infer ⟦{rec}⟧: {e}"));
            let m = got
                .ev
                .thm()
                .unwrap_or_else(|| panic!("{name}: ⟦{rec}⟧ has no typing: {:?}", got.ev))
                .clone();
            assert!(m.hyps().is_empty(), "{name}: a stored typing is unconditional");
            let point = c.interp().expect("threaded").point();
            assert_eq!(got.tm, Some(point.clone()), "{name}: a class-(P) eliminator is a proof");
            let (subj, set) = m.concl().as_mem().expect("a membership");
            assert_eq!(subj, point, "{name}: the typing is about the term the store holds");
            let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
            assert_eq!(set, want, "{name}: …and about the recursor's own declared type");
        }
    }
}
