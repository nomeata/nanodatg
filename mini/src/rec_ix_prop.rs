//! **The indexed class-(T) eliminator at a `Prop`-valued motive** —
//! `⟦T.rec.{0,σ}⟧` for a family [`crate::zoneb::build_indexed`] translated
//! (`INDEXED-DESIGN.md` §5.3 and §8's D7, MINI-DESIGN.md §9).
//!
//! # Interface
//!
//! ```text
//! rec_ix_prop::ensure(checker, T, σ_T, T.rec, σ_rec, np, n, ni, rec ty)
//! ```
//!
//! Called from [`crate::rec_dep::ensure`]'s `num_indices != 0` branch and from
//! nowhere else, on a recursor whose motive binder lands in `Sort 0`. On
//! success `⟦T.rec.{σ_rec}⟧ = •` and its typing are in the store under the
//! recursor's own instantiation.
//!
//! # The obligation
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : Π x⃗ (t : T p⃗ x⃗). Sort 0) (S⃗ : minors) x⃗ (t : T p⃗ x⃗). C x⃗ t⟧
//! ```
//!
//! `C x⃗ t : Sort 0`, so by §6.2's proof column the eliminator **is** a proof:
//! there is no `grec`, no target set and no `T`-policy, and §5.1's value
//! recursor does not apply. What is owed is that the motive is inhabited at
//! every inhabitant of the carrier, and that is
//! [`IndexedPropRecursor`](derived::inductive::family::IndexedPropRecursor):
//!
//! ```text
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → • ∈ app(m, x⃗, t) ) )
//! ```
//!
//! So the nest is `np + 1 + n + ni + 1` deep,
//! [`Checker::lam_nest`](crate::kernel::Checker::lam_nest) walks it, and the
//! whole of this module is **transporting Lean's minor premises into
//! `MINORᵢ`'s shape** — plus three lines at the bottom to fire the rule at the
//! index binders and the major premise.
//!
//! # The minor premises are `crate::minor_ix`'s
//!
//! Transporting Lean's minor into `MINORᵢ`'s shape is the bulk of the work and
//! it is **not here**: `IDEPᵢ`'s antecedent is the same `minor_atoms_at` this
//! rule's is, at a bound `vⱼ` instead of at `•`, so the value clause
//! ([`crate::rec_ix_dep`]) transports it with the same walk. That walk, the
//! three set-swaps it performs and the close-time domain rewrite it needs are
//! [`crate::minor_ix`], and its header is where the design lives. What is left
//! here is [`Clause`]'s `Prop` half — the induction hypotheses are *atoms* of
//! `Aᵢ` rather than binders, so the rule quantifies `k + m` and the walk
//! instantiates the last `m` levels at `•`, and the conclusion's subject is
//! moved onto `•` by proof irrelevance.
//!
//! # Nothing here searches
//!
//! The rule comes from a memo keyed on the declaration
//! ([`IndApparatus::indexed_prop_recursor`](crate::interp::IndApparatus)); the
//! index expressions come from the checker's own telescope and are inferred;
//! every equation is a defining axiom this declaration's translation kept.
//! Each finished minor is compared against
//! [`IndexedPropRecursor::minors`](derived::inductive::family::IndexedPropRecursor)
//! rebuilt at mini's own terms, and the bottom's membership against `⟦C x⃗ t⟧`
//! inferred from the recursor's declared codomain. A recursor of some other
//! shape cannot make those comparisons succeed.

use kernel::{Formula, Term, Thm};

use derived::inductive::family::{motive_app, IndexedPropRecursor};

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::interp::Interp;
use crate::kernel::{Checker, Typing, R};
use crate::minor_ix::{self, At, Clause, Site};
use crate::rec_dep::subst_f;

const ARITY: &str = "indexed Prop recursor: arity";
const DISAGREE: &str = "indexed Prop recursor: the recursor and the carrier disagree";
const MINOR: &str = "indexed Prop recursor: a minor premise does not transport";
const CARRIER: &str = "indexed Prop recursor: the carrier at the index binders";
const CODOMAIN: &str = "indexed Prop recursor: the codomain is not the motive at x⃗ and t";
const SORTS: &str = "indexed Prop recursor: the motive's sort and its codomain disagree";

/// **`IndexedPropRecursor::over_family` declined this declaration** — the one
/// `Cause::Library` exit of this module.
pub const RULE: &str = "indexed Prop recursor: IndexedPropRecursor::over_family declined";

/// Make `⟦T.rec.{σ_rec}⟧` available for an indexed class-(T) declaration whose
/// motive lands in `Sort 0`, or say what the wiring could not transport.
///
/// The counts and the ground recursor type are the caller's — `rec_dep` has
/// just read them off the same `ConstantInfo` to decide §6.2's split, and a
/// second read here would be a second chance to disagree about which clause
/// this is.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    np: usize,
    n: usize,
    ni: usize,
    rec_ty: &E,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let ctors = match c.environment().get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) => ctors.clone(),
        _ => return Err(Gap::NoInterpretation(*ind_name, ind_inst.to_vec())),
    };
    let depth = np + 1 + n + ni + 1;
    let codomain = crate::zoneb::peel(rec_ty, depth).ok_or_else(|| bad(ARITY))?;

    let key = (*ind_name, ind_inst.to_vec());
    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.indexed
            .get(&key)
            .cloned()
            .ok_or_else(|| bad("indexed Prop recursor: the family is not translated"))?
    };
    if tr.ii.spec.len() != n
        || tr.ii.spec.params() != np
        || tr.ii.spec.num_indices() != ni
        || ctors.len() != n
        || tr.base.params.len() != np
    {
        return Err(bad(DISAGREE))
    }

    let site = Site {
        ind: *ind_name,
        inst: ind_inst.to_vec(),
        rec: *rec_name,
        rec_inst: rec_inst.to_vec(),
        ctors,
        np,
        n,
        ni,
        depth,
        codomain,
        fam: minor_ix::Fam::ClassT(tr),
        minor_gap: MINOR,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// The bottom of `⟦T.rec⟧`'s nest: `⊢ • ∈ ⟦C x⃗ t⟧`.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: `rec_dep` read it off
    // the motive's declared sort to get here, and this is the codomain the nest
    // actually reached.
    match c.is_prop(&site.codomain) {
        Ok(true) => (),
        Ok(false) => return gap(bad(SORTS)),
        Err(_) => return gap(Gap::Classifier),
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((tms, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let mut ctor_formers = Vec::with_capacity(site.n);
    for name in &site.ctors {
        match c.stored_term(name, &site.inst) {
            Some(t) => ctor_formers.push(t),
            None => return gap(Gap::NoEndpoint),
        }
    }

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

    // The rule, once per declaration — one `w_rect` Separation per build, so a
    // second one would carve a second carrier no equation relates to the first.
    let pr = {
        let key = (site.ind, site.inst.clone());
        let (base, fam) = (site.fam.class_t().expect("class (T)").base.clone(), &site.fam.class_t().expect("class (T)").ii);
        let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
        let Some((mut kenv, app, _)) = ip.ind_parts() else { return gap(Gap::IndApparatus) };
        let kenv = &mut *kenv;
        match app.indexed_prop_recursor(kenv, &key, &base, fam) {
            Some(r) => r,
            None => return gap(Gap::Recursor(site.ind, RULE, Cause::Library)),
        }
    };
    if pr.minors.len() != n || pr.xvs.len() != ni {
        return gap(bad(DISAGREE))
    }

    let mut minors = Vec::with_capacity(n);
    for i in 0..n {
        let Some(cs) = site.fam.class_t().expect("class (T)").ii.spec.base.ctors.get(i) else { return gap(bad(DISAGREE)) };
        let clause = Clause {
            nvars: cs.args.len() + cs.recs,
            proof: true,
            motive: pr.motive,
            trunc: false,
        };
        let (src, mvars) = match (pr.minor_atoms.get(i), pr.minor_vars.get(i)) {
            (Some(a), Some(v)) => (a.clone(), v.clone()),
            _ => return gap(bad(DISAGREE)),
        };
        match minor_ix::transport(c, site, &at, i, &src, &mvars, clause) {
            // **Compared against what `derived` states**, rebuilt at these very
            // terms. That is what pins the quantifier prefix, the atom order
            // and the conclusion's spine; nothing the walk did is asserted that
            // is not checked here.
            Ok(t) => {
                if *t.thm.concl() != subst_f(&pr.minors[i], &t.sub) {
                    return gap(bad(MINOR))
                }
                minors.push(t.thm)
            }
            Err(g) => return gap(g),
        }
    }

    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match fire(ip, site, &pr, &at, &minors) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// The rule at `(⟦p⃗⟧, ⟦C⟧)`, discharged by the minors and fired at the index
/// binders and the major premise.
fn fire(
    ip: &mut Interp,
    site: &Site,
    pr: &IndexedPropRecursor,
    at: &At,
    minors: &[Thm],
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let s = ip.prelude.tower.sums.clone();
    let point = ip.point();

    // `⟦C x⃗ t⟧` is the motive's own curried spine — checked, because a recursor
    // concluding at some *fixed* index or constructor is a well-typed `Π` and is
    // exactly what a wiring that ignored the major premise would satisfy.
    if at.goal != motive_app(&s, &at.c_tm, &at.xs, &at.t_tm) {
        return Err(bad(CODOMAIN))
    }

    let mut args = at.ps.clone();
    args.push(at.c_tm.clone());
    let rule = derived::inst_all(&pr.rec, &args).ok_or_else(|| bad(DISAGREE))?;
    let all = minors
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("indexed Prop recursor: a declaration with no constructors"))?;
    let over = Thm::mp(&rule, &all).ok_or_else(|| bad(MINOR))?;

    let mut ia = at.xs.clone();
    ia.push(at.t_tm.clone());
    let at_t = derived::inst_all(&over, &ia).ok_or_else(|| bad(CARRIER))?;

    // The scope holds `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧`, the applied spine; the rule speaks of
    // `ind(p⃗,⟦x⃗⟧)`. One β down the type former's nest, and the drift check is
    // that the equation's left-hand side is the set the scope actually holds.
    let mut sa = at.ps.clone();
    sa.extend(at.xs.iter().cloned());
    let mut sm = at.param_mems.clone();
    sm.extend(at.x_mems.iter().cloned());
    let (_, beta) = ip.beta_spine(&at.former, &sa, &sm).ok_or_else(|| bad(CARRIER))?;
    let held = at.t_mem.concl().as_mem().ok_or_else(|| bad(CARRIER))?.1;
    if beta.concl().as_eq().ok_or_else(|| bad(CARRIER))?.0 != held {
        return Err(bad(CARRIER))
    }
    let t_in = ip.retarget_set(&at.t_mem, &beta).ok_or_else(|| bad(CARRIER))?;
    let mem = Thm::mp(&at_t, &t_in).ok_or_else(|| bad(CARRIER))?;
    if *mem.concl() != Formula::mem(point.clone(), at.goal.clone()) {
        return Err(bad("indexed Prop recursor: the proof clause did not land in the codomain"))
    }
    Ok((point, mem))
}



#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no_levels() -> Rc<[Level]> { Vec::new().into() }
    fn ty1() -> E { sort(Level::zero().succ()) }

    /// ```text
    /// inductive B : Type    | b0 | b1
    /// inductive T (α : Type) : B → B → Type
    ///   | c0 : T α b0 b0                                    0 plain, 0 rec
    ///   | c1 : ∀ (x : B), T α x b0 → T α b1 x                1 plain, 1 rec
    ///   | c2 : ∀ (x y : B), T α x y → T α y x → T α b0 b1    2 plain, 2 rec
    /// ```
    ///
    /// **`c2` is why this family and not `RBTree`, and the reason is not the
    /// one it is natural to give.** Its two recursive arguments sit at `(x,y)`
    /// and `(y,x)` and its result at `(b0,b1)`, so the induction hypothesis at
    /// level `k + m + j` must be paired with recursive *slot* `j` and with slot
    /// `j`'s own `d⃗ᵢⱼ`, and a build that paired them the other way proves a
    /// statement `IndexedPropRecursor::minors` does not contain.
    ///
    /// The natural reason — "`RBTree.red`'s children are both at `(Color.b,n)`
    /// and cannot tell the two apart" — was checked and is **half false**, in a
    /// way that matters for every later test at this seam. Blindness is a
    /// property of a *spelling*, not of a declaration. At `derived`'s spelling
    /// no constructor is blind at all: `d⃗ᵢ₀` and `d⃗ᵢ₁` are different `FnSym`s,
    /// of different arities whenever a plain field separates the two `Slot::Rec`
    /// positions. It is only **after unfolding** — this module's spelling, the
    /// one the code manipulates — that `red`'s two children land on the same
    /// `(⟦Color.b⟧, ⟦n⟧)`. And `RBTree.black`'s do *not*: they stay apart at
    /// `c₁`/`c₂`, so `RBTree` as a declaration does catch a pure index swap here
    /// — measured, by mutating this module and running `068`.
    ///
    /// What `c2` supplies that no corpus constructor does is that its two child
    /// vectors are each other's **reverse** after unfolding. That is the pin,
    /// and it is why this family stays even though `RBTree` happens to catch the
    /// mutations that were tried.
    ///
    /// `c0` is here for the opposite reason: at `k + 2m = 0` no application
    /// rule fires, the minor is a proof *variable* rather than `•`, and the
    /// proof-irrelevance step is the only thing that reaches the conclusion.
    /// It is also the case that passes under every wrong binder arithmetic, so
    /// it certifies nothing on its own and is asserted alongside the other two.
    pub(crate) fn indexed_env() -> (Environment, Name, Name) {
        let b = nm("B");
        let bt = konst(b, no_levels());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: b,
                lparams: vec![],
                num_params: 0,
                ty: ty1(),
                ctors: vec![
                    (Name::str(&b, "b0"), bt),
                    (Name::str(&b, "b1"), bt),
                ],
            },
        )
        .expect("B is accepted");
        let b0 = konst(Name::str(&b, "b0"), no_levels());
        let b1 = konst(Name::str(&b, "b1"), no_levels());
        let t = nm("T");
        let tap = |a: E, i: E, j: E| app(app(app(konst(t, no_levels()), a), i), j);
        let ty = forall(ty1(), forall(bt, forall(bt, ty1())));
        let ctors = vec![
            (Name::str(&t, "c0"), forall(ty1(), tap(bvar(0), b0, b0))),
            (
                Name::str(&t, "c1"),
                forall(
                    ty1(),
                    forall(
                        bt,
                        forall(tap(bvar(1), bvar(0), b0), tap(bvar(2), b1, bvar(1))),
                    ),
                ),
            ),
            (
                Name::str(&t, "c2"),
                forall(
                    ty1(),
                    forall(
                        bt,
                        forall(
                            bt,
                            forall(
                                tap(bvar(2), bvar(1), bvar(0)),
                                forall(tap(bvar(3), bvar(1), bvar(2)), tap(bvar(4), b0, b1)),
                            ),
                        ),
                    ),
                ),
            ),
        ];
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t,
                lparams: vec![],
                num_params: 1,
                ty,
                ctors,
            },
        )
        .expect("T is accepted");
        let rec = Name::str(&t, "rec");
        (env, t, rec)
    }

    /// **`⟦T.rec.{0}⟧` is interpreted with its typing**, at an indexed family
    /// whose motive is `Prop`-valued.
    ///
    /// Three assertions, and each rules out a different way of passing
    /// vacuously. The typing must be **unconditional** — a hypothesis that
    /// escaped a minor's binder would be caught by
    /// [`crate::ev::Sealed`](crate::ev::Sealed) at the store funnel, but this
    /// says so where the reason is legible. It must be about `•`, which is
    /// §6.2's proof column and the whole reason this clause is not
    /// `crate::rec_dep`'s. And the set must be `⟦the recursor's declared
    /// type⟧`, *inferred* rather than synthesised, so a derivation that landed
    /// in the motive at some other index — the one thing an indexed eliminator
    /// can get wrong that a non-indexed one cannot — fails the third.
    #[test]
    fn the_prop_motive_indexed_eliminator_is_interpreted_with_its_typing() {
        let (env, t, rec) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(t, no_levels())).expect("infer ⟦T⟧");
        let at: Rc<[Level]> = vec![Level::zero()].into();
        let got = c.infer_type(&konst(rec, at)).expect("infer ⟦T.rec.{0}⟧");
        let m = got
            .ev
            .thm()
            .unwrap_or_else(|| panic!("⟦{rec}.{{0}}⟧ has no typing: {:?}", got.ev))
            .clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        let point = c.interp().expect("threaded").point();
        assert_eq!(got.tm, Some(point.clone()), "a Prop-valued motive makes the eliminator a proof");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, point, "the typing must be about the term the store holds");
        let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…and about the recursor's own declared type");
    }

    /// **§6.2's split routes the two clauses apart, and the routing is the
    /// assertion.**
    ///
    /// `T.rec.{0}` and `T.rec.{1}` are the same declaration at two motive
    /// sorts, and they are two different constructions —
    /// [`IndexedPropRecursor`] here, `IndexedDepRecursor` in
    /// [`crate::rec_ix_dep`]. Both derive, so "it did not decline" says
    /// nothing; what says something is that they produce **different
    /// interpretations**: a `Prop` motive makes the eliminator a proof, which
    /// denotes `•`, and a value motive makes it a λ-nest that comes apart
    /// again. A `rec_dep` branch that sent both to one clause would give the
    /// same term twice and fail here.
    #[test]
    fn the_two_motive_sorts_are_two_constructions_and_two_terms() {
        let (env, t, rec) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(t, no_levels())).expect("infer ⟦T⟧");
        let point = c.interp().expect("threaded").point();

        let at0: Rc<[Level]> = vec![Level::zero()].into();
        let p = c.infer_type(&konst(rec, at0)).expect("infer ⟦T.rec.{0}⟧");
        assert_eq!(p.tm, Some(point.clone()), "a Prop-valued motive gives a proof");

        let at1: Rc<[Level]> = vec![Level::zero().succ()].into();
        let v = c.infer_type(&konst(rec, at1)).expect("infer ⟦T.rec.{1}⟧");
        let vt = v.tm.clone().expect("the value clause interprets");
        assert_ne!(vt, point, "a value-valued motive is not a proof");
        assert!(
            c.interp().expect("threaded").as_lam(&vt).is_some(),
            "…and its interpretation is a λ-nest, not an opaque symbol"
        );
    }
}
