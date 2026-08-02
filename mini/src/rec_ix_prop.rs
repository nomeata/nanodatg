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
//! # The minor walk opens *checker* binders, and that is the whole design
//!
//! [`crate::rec_dep::minor_at`] walks a minor's Π-interpretation with a private
//! [`Scopes`](crate::scope::Scopes) and never touches the Lean type. That
//! cannot work here, and the reason is one atom:
//!
//! ```text
//! rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))         the atom `minor_atoms` states
//! rⱼ ∈ ⟦T p⃗ d⃗⟧                   the domain the binder was opened at
//! ```
//!
//! The two sets differ by one β down the type former's own λ-nest, and β
//! consumes **one membership per level** — `⟦dₖ⟧ ∈ ⟦Iₖ⟧`, per index of the
//! recursive argument. Nothing hands those over: `d⃗ᵢⱼ`'s defining axioms give
//! the *terms* and not the memberships, and the recursive argument's index
//! expressions live inside the minor's Lean type, where no interpretation walk
//! can infer anything. This is where the estimate for this row ("`spine_eq` +
//! `index_congr`, verbatim from `crate::ctor_ix`") did not survive contact:
//! both helpers do reuse verbatim, and their `xs: &[(Term, Thm)]` argument had
//! no source.
//!
//! So the walk opens the minor's Lean binders on the **checker's own**
//! telescope, with [`Checker::push_interpreted`](crate::kernel::Checker::push_interpreted)
//! at the domain the Π-interpretation already recorded. Everything
//! [`crate::ctor_ix`] does at the bottom of a constructor's nest is then
//! available one level up and unchanged: [`crate::zoneb::ind_spine`] reads the
//! index expressions off the binder's type and [`crate::ctor_ix::infer_indices`]
//! *infers* them, which is the only place `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists.
//!
//! # The domain swap happens at each binder's close, not afterwards
//!
//! `minor_at`'s conversion of the interleaved `∀w. (w ∈ D → …)` family into the
//! prenex `∀f⃗. (⋀A → …)` needs, per level, an implication `⋀A → (w ∈ D)` — and
//! `rec_dep` builds it from an **unconditional** equation between the two sets.
//! Here the equation is a β step and carries the very hypotheses the scopes
//! introduced, so a `Γ`-carrying implication would survive to the final
//! `gen_all_checked` and be refused there: the bound variable is free in a
//! remaining hypothesis, which is exactly the discipline I2 exists to enforce.
//!
//! [`domain_swap`] moves the equation to where its `Γ` is still legal. Each
//! scope discharges to `∀w. (w ∈ ⟦D⟧ → φ)` and is *then* rewritten, by one
//! Leibniz, into `∀w. (w ∈ D_derived → φ)` — innermost first, while every outer
//! scope is still open, so the hypotheses the equation carries (which mention
//! only strictly earlier binders) are discharged by the closes above it. What
//! comes out has no `Γ` beyond the recursor nest's own, the antecedents are
//! `minor_atoms` on the nose, and the prenexing loop is `conj_proj` with no
//! retargeting left to do.
//!
//! It is the same move `zoneb`'s summand-leg close makes for the same reason,
//! at the same shape.
//!
//! # `minor_vars` is Lean-positional, so level `l` answers atom `l`
//!
//! D7 quantifies `MINORᵢ` in the constructor's **declared** field order and
//! states `Aᵢ`'s atoms in that order, then the `mᵢ` induction hypotheses. A
//! minor's Π-interpretation unfolds in exactly that order. So there is no
//! permutation here at all — no `order_index`, no mask read — and the `Slot`
//! mask is consulted only to decide *which kind* of equation level `l` needs.
//! That is what moving the permutation inside `over_family` bought, and it is
//! the difference between this file and [`crate::rec_dep`]'s equivalent loop.
//!
//! # Three moves between a set the interpretation names and one `derived` names
//!
//! | level | `minor_atoms` | the binder's domain | the equation |
//! |---|---|---|---|
//! | `Slot::Plain` | `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` | `⟦βⱼ⟧` | `field_abbrev`, instantiated |
//! | `Slot::Rec` | `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` | `⟦T p⃗ d⃗⟧` | `index_congr`, then β |
//! | IH | `• ∈ app(m,d⃗ᵢⱼ,rⱼ)` | `⟦C d⃗ rⱼ⟧` | `motive_congr_of` |
//!
//! and the conclusion travels the same way — `⟦C e⃗ᵢ (T.ctorᵢ p⃗ y⃗ r⃗)⟧` onto
//! `app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))`, which is *two* positions of one spine moving at
//! once and is why [`motive_congr`](derived::inductive::family::motive_congr)
//! covers the subject as well: the constructor term sits inside an **argument**
//! of the membership, so a subject retarget cannot reach it.
//!
//! # The conclusion's equation carries `Γ`, and `motive_congr_of` takes it
//!
//! The subject equation is a β down the *constructor's* λ-nest, so it arrives
//! as `Γ ⊢ ⟦T.ctorᵢ p⃗ y⃗ r⃗⟧ = ctorᵢ(y⃗,r⃗)` carrying that nest's scope
//! assumptions. `motive_congr_of` refused a hypothesis-carrying input when this
//! module was written, and its documented escape — `a1i` the scheme, `hyp_and`
//! the conjunction — addresses an *implication antecedent*, which a sequent
//! hypothesis is not. This file carried a local copy of the fold for exactly
//! one call while that stood.
//!
//! **It is gone.** `motive_congr_of` now accepts the caller's `Γ` and its
//! result carries exactly the union of the inputs' hypotheses and nothing else,
//! checked in `prop_rec.rs` rather than argued here. Both this module's uses —
//! the induction hypotheses and the conclusion — go through the one entry
//! point, which is the whole reason the fold lives on the side that defines the
//! spine.
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

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::{motive_app, motive_congr_of, IndexedPropRecursor};
use derived::inductive::Slot;

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Expr, Name, E};
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};
use crate::rec_dep::{gen_all_checked, hyp_inst, subst_f};
use crate::scope::Closed;
use crate::zoneb::IndexedTranslation;

const ARITY: &str = "indexed Prop recursor: arity";
const DISAGREE: &str = "indexed Prop recursor: the recursor and the carrier disagree";
const MINOR: &str = "indexed Prop recursor: a minor premise does not transport";
const CARRIER: &str = "indexed Prop recursor: the carrier at the index binders";
const CODOMAIN: &str = "indexed Prop recursor: the codomain is not the motive at x⃗ and t";
const SORTS: &str = "indexed Prop recursor: the motive's sort and its codomain disagree";
const SCOPES: &str = "indexed Prop recursor: a minor's binder did not close";

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
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w, Cause::Threading);
    let ctors = match c.environment().get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) => ctors.clone(),
        _ => return Err(Gap::NoInterpretation(ind_name.clone(), ind_inst.to_vec())),
    };
    let depth = np + 1 + n + ni + 1;
    let codomain = crate::zoneb::peel(rec_ty, depth).ok_or_else(|| bad(ARITY))?;

    let key = (ind_name.clone(), ind_inst.to_vec());
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
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        ctors,
        np,
        n,
        ni,
        depth,
        codomain,
        tr,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// Which eliminator is being built, and everything read before a binder opens.
struct Site {
    ind: Name,
    inst: Vec<u32>,
    /// The constructors' names, in declaration order.
    ctors: Vec<Name>,
    np: usize,
    n: usize,
    ni: usize,
    /// `np + 1 + n + ni + 1` — parameters, motive, minors, indices, major.
    depth: usize,
    codomain: E,
    tr: Rc<IndexedTranslation>,
}

/// What the nest's own scopes hold at the bottom, plus the store reads.
struct At {
    /// `⟦p⃗⟧`.
    ps: Vec<Term>,
    /// Their scope typings.
    param_mems: Vec<Thm>,
    /// `⟦C⟧`.
    c_tm: Term,
    /// `⟦S⃗⟧`'s scope typings — the minors, which is all this needs of them.
    s_mems: Vec<Thm>,
    /// `⟦x⃗⟧`, the index binders, with their typings.
    xs: Vec<Term>,
    x_mems: Vec<Thm>,
    /// `⟦t⟧` and `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧`.
    t_tm: Term,
    t_mem: Thm,
    /// `⟦T⟧` and each `⟦T.ctorᵢ⟧`, as the store holds them.
    former: Term,
    ctor_formers: Vec<Term>,
    /// `⟦C x⃗ t⟧`, the set the bottom's membership must be about.
    goal: Term,
}

/// The bottom of `⟦T.rec⟧`'s nest: `⊢ • ∈ ⟦C x⃗ t⟧`.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);

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

    let (np, n, ni, depth) = (site.np, site.n, site.ni, site.depth);
    let at = At {
        ps: tms[..np].to_vec(),
        param_mems: mems[..np].to_vec(),
        c_tm: tms[np].clone(),
        s_mems: mems[np + 1..np + 1 + n].to_vec(),
        xs: tms[np + 1 + n..depth - 1].to_vec(),
        x_mems: mems[np + 1 + n..depth - 1].to_vec(),
        t_tm: tms[depth - 1].clone(),
        t_mem: mems[depth - 1].clone(),
        former,
        ctor_formers,
        goal,
    };
    if at.xs.len() != ni {
        return gap(bad(DISAGREE))
    }

    // The rule, once per declaration — one `w_rect` Separation per build, so a
    // second one would carve a second carrier no equation relates to the first.
    let pr = {
        let key = (site.ind.clone(), site.inst.clone());
        let (base, fam) = (site.tr.base.clone(), &site.tr.ii);
        let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
        let Some((kenv, app, _)) = ip.ind_parts() else { return gap(Gap::IndApparatus) };
        match app.indexed_prop_recursor(kenv, &key, &base, fam) {
            Some(r) => r,
            None => return gap(Gap::Recursor(site.ind.clone(), RULE, Cause::Library)),
        }
    };
    if pr.minors.len() != n || pr.xvs.len() != ni {
        return gap(bad(DISAGREE))
    }

    let mut minors = Vec::with_capacity(n);
    for i in 0..n {
        match minor_at(c, site, &pr, &at, i) {
            Ok(t) => minors.push(t),
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
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
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

// ─────────────────────────────────────────────────────────────────────────────
// One minor premise, transported
// ─────────────────────────────────────────────────────────────────────────────

/// What the walk leaves behind at the bottom of one minor's telescope.
struct Walked {
    /// The `k + 2m` binder terms, in Lean order.
    ws: Vec<Term>,
    /// Their kernel variables.
    wvs: Vec<FreeVar>,
    /// Per level, `⊢ Dᵈᵉʳⁱᵛᵉᵈ = ⟦D⟧` — the equation [`domain_swap`] closes with.
    eqs: Vec<Thm>,
    /// `Γ ⊢ • ∈ app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))`, at `derived`'s spelling.
    concl: Thm,
    /// `minor_atoms[i]` at this call's own terms.
    atoms: Vec<Formula>,
    /// The substitution the caller compares `minors[i]` under.
    sub: Vec<(FreeVar, Term)>,
}

/// `⊢ MINORᵢ(⟦C⟧)` at mini's own terms, from the minor binder's scope typing.
fn minor_at(
    c: &mut Checker<'_, '_>,
    site: &Site,
    pr: &IndexedPropRecursor,
    at: &At,
    i: usize,
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let cs = site.tr.ii.spec.base.ctors.get(i).ok_or_else(|| bad(DISAGREE))?.clone();
    let (k, m) = (cs.args.len(), cs.recs);
    let nlev = k + 2 * m;
    if pr.minor_atoms.get(i).map(Vec::len) != Some(nlev)
        || pr.minor_vars.get(i).map(Vec::len) != Some(k + m)
    {
        return Err(bad(DISAGREE))
    }

    // The minor's Lean type, read **before** any of its own binders is open, so
    // that `local_type` does the de Bruijn shift and this module does none.
    let idx = u32::try_from(site.depth - 1 - (site.np + 1 + i)).map_err(|_| bad(DISAGREE))?;
    let mty = c.local_type(idx).map_err(|_| bad(MINOR))?;

    // The walk leaves `nlev` checker binders open whether it succeeds or not,
    // and they must come off the telescope either way.
    let mut opened = 0usize;
    let walked = walk(c, site, pr, at, i, &cs, &mty, &mut opened);
    let mut closed: Vec<Closed> = Vec::with_capacity(opened);
    for _ in 0..opened {
        match c.close_one() {
            Some(cl) => closed.push(cl),
            None => return Err(bad(SCOPES)),
        }
    }
    let w = walked?;
    if closed.len() != nlev {
        return Err(bad(SCOPES))
    }

    // ── discharge, innermost first, swapping each domain as it closes ───────
    let mut chain = w.concl;
    for (l, cl) in closed.iter().enumerate() {
        let level = nlev - 1 - l;
        let Some(ip) = c.interp() else { return Err(Gap::SymbolicLevel) };
        chain = domain_swap(ip, cl, &w.eqs[level], &chain).ok_or_else(|| bad(MINOR))?;
    }

    // ── prenex: re-instantiate and discharge each atom from the conjunction ──
    //
    // Level `l` answers atom `l`: `minor_vars` is Lean-positional, so there is
    // no permutation here. The induction-hypothesis levels are instantiated at
    // `•`, which is what makes their antecedent `minor_atoms`' own `• ∈ …`.
    let point = {
        let Some(ip) = c.interp() else { return Err(Gap::SymbolicLevel) };
        ip.point()
    };
    let hyp = derived::conj_of(&w.atoms);
    let mut cur = match &hyp {
        None => chain,
        Some(h) => derived::a1i(&chain, h.clone()),
    };
    for l in 0..nlev {
        let arg = if l < k + m { w.ws[l].clone() } else { point.clone() };
        cur = hyp_inst(&cur, &arg).ok_or_else(|| bad(MINOR))?;
        let ante = cur
            .concl()
            .as_imp()
            .and_then(|(_, r)| r.as_imp())
            .map(|(a, _)| a)
            .ok_or_else(|| bad(MINOR))?;
        if ante != w.atoms[l] {
            return Err(bad(MINOR))
        }
        let step = derived::conj_proj(&w.atoms, l).ok_or_else(|| bad(MINOR))?;
        cur = derived::hyp_mp(&cur, &step).ok_or_else(|| bad(MINOR))?;
    }
    let out = gen_all_checked(&w.wvs[..k + m], &cur).ok_or_else(|| bad(MINOR))?;

    // **Compared against what `derived` states**, rebuilt at these very terms.
    // That is what pins the quantifier prefix, the atom order and the
    // conclusion's spine; nothing above is asserted that is not checked here.
    if *out.concl() != subst_f(&pr.minors[i], &w.sub) {
        return Err(bad(MINOR))
    }
    Ok(out)
}

/// Open every binder of one minor's Lean telescope, applying the minor as it
/// goes, and stop at the conclusion.
#[allow(clippy::too_many_arguments)]
fn walk(
    c: &mut Checker<'_, '_>,
    site: &Site,
    pr: &IndexedPropRecursor,
    at: &At,
    i: usize,
    cs: &derived::inductive::CtorSpec,
    mty: &E,
    opened: &mut usize,
) -> Result<Walked, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let (np, ni) = (site.np, site.ni);
    let (k, m) = (cs.args.len(), cs.recs);
    let nlev = k + 2 * m;
    let mvars = &pr.minor_vars[i];
    let src = &pr.minor_atoms[i];

    let mut sub: Vec<(FreeVar, Term)> = site
        .tr
        .base
        .params
        .iter()
        .copied()
        .zip(at.ps.iter().cloned())
        .collect();
    sub.push((pr.motive, at.c_tm.clone()));

    let mut ws: Vec<Term> = Vec::with_capacity(nlev);
    let mut wvs: Vec<FreeVar> = Vec::with_capacity(nlev);
    let mut wmems: Vec<Thm> = Vec::with_capacity(nlev);
    let mut eqs: Vec<Thm> = Vec::with_capacity(nlev);
    // `⟦d⃗ᵢⱼ⟧` with their typings, per recursive slot, as the walk infers them.
    let mut childs: Vec<Vec<(Term, Thm)>> = Vec::with_capacity(m);
    let mut ys: Vec<Term> = Vec::with_capacity(k);

    let mut f_mem = at.s_mems[i].clone();
    let mut cur = mty.clone();
    let (mut plains, mut recs) = (0usize, 0usize);
    for l in 0..nlev {
        let Expr::Forall { ty: dom_e, body } = &*cur.clone() else { return Err(bad(MINOR)) };
        let (dom_e, body) = (dom_e.clone(), body.clone());

        // The set the interpretation opened this binder at, and the one
        // `minor_atoms` states the level's atom in. `derived`'s set mentions
        // only *earlier* fields, so the partial substitution is complete for it.
        let f_set = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?.1;
        let shape = {
            let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
            ip.as_pi(&f_set).ok_or_else(|| bad(MINOR))?
        };
        let idom = shape.dom();
        let ddom = subst_f(&src[l], &sub).as_mem().ok_or_else(|| bad(MINOR))?.1;

        // The equation between the two, by the level's kind.
        let eq = if l < k + m {
            match cs.order[l] {
                Slot::Plain => {
                    let mut a = at.ps.clone();
                    a.extend(ys.iter().cloned());
                    let ax = site
                        .tr
                        .field_abbrev
                        .get(i)
                        .and_then(|r| r.get(plains))
                        .ok_or_else(|| bad(MINOR))?;
                    derived::inst_all(ax, &a).ok_or_else(|| bad(MINOR))?
                }
                Slot::Rec => {
                    // The recursive argument's index expressions come off its
                    // own binder type and are **inferred** here — the only
                    // place `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists. `d` is the field depth the
                    // parameters are pinned at: the whole context is
                    // `site.depth + l` deep and the parameters are its outermost.
                    let d = site.depth + l - np;
                    let ds_e = crate::zoneb::ind_spine(&site.ind, &dom_e, np, ni, d)
                        .ok_or_else(|| bad(MINOR))?;
                    let ds = crate::ctor_ix::infer_indices(c, &ds_e).ok_or_else(|| bad(MINOR))?;
                    let before = site
                        .tr
                        .ii
                        .spec
                        .plains_before(i, recs)
                        .ok_or_else(|| bad(MINOR))?;
                    let mut a = at.ps.clone();
                    a.extend(ys.get(..before).ok_or_else(|| bad(MINOR))?.iter().cloned());
                    let axs = site
                        .tr
                        .ax
                        .ctors
                        .get(i)
                        .and_then(|cx| cx.rec_args.get(recs))
                        .ok_or_else(|| bad(MINOR))?;
                    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
                    let cong =
                        crate::ctor_ix::index_congr(ip, site.tr.ii.carrier.ty, &at.ps, &ds, axs, &a)
                            .ok_or_else(|| bad(MINOR))?;
                    let mut sa = at.ps.clone();
                    sa.extend(ds.iter().map(|(t, _)| t.clone()));
                    let mut sm = at.param_mems.clone();
                    sm.extend(ds.iter().map(|(_, t)| t.clone()));
                    let (_, beta) =
                        ip.beta_spine(&at.former, &sa, &sm).ok_or_else(|| bad(MINOR))?;
                    // The drift check: the spine β-reduces from the very set
                    // this binder was opened at.
                    if beta.concl().as_eq().ok_or_else(|| bad(MINOR))?.0 != idom {
                        return Err(bad(MINOR))
                    }
                    let back = derived::eq_symm(&mut ip.env, &beta).ok_or_else(|| bad(MINOR))?;
                    childs.push(ds);
                    derived::eq_trans(&mut ip.env, &cong, &back).ok_or_else(|| bad(MINOR))?
                }
            }
        } else {
            // An induction hypothesis: the motive's spine at the child's own
            // indices, and only the indices move.
            let j = l - (k + m);
            let ds = childs.get(j).ok_or_else(|| bad(MINOR))?.clone();
            let before = site.tr.ii.spec.plains_before(i, j).ok_or_else(|| bad(MINOR))?;
            let mut a = at.ps.clone();
            a.extend(ys.get(..before).ok_or_else(|| bad(MINOR))?.iter().cloned());
            let axs = site
                .tr
                .ax
                .ctors
                .get(i)
                .and_then(|cx| cx.rec_args.get(j))
                .ok_or_else(|| bad(MINOR))?;
            if axs.len() != ni || ds.len() != ni {
                return Err(bad(MINOR))
            }
            let child = child_term(cs, &ws, j).ok_or_else(|| bad(MINOR))?;
            let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
            let s = ip.prelude.tower.sums.clone();
            let mut ceqs: Vec<Thm> = Vec::with_capacity(ni + 1);
            for (q, ax) in axs.iter().enumerate() {
                let step = derived::inst_all(ax, &a).ok_or_else(|| bad(MINOR))?;
                if step.concl().as_eq().ok_or_else(|| bad(MINOR))?.1 != ds[q].0 {
                    return Err(bad(MINOR))
                }
                ceqs.push(step);
            }
            ceqs.push(Thm::eq_refl(child));
            motive_congr_of(&mut ip.env, &s, &at.c_tm, &ceqs).ok_or_else(|| bad(MINOR))?
        };
        if eq.concl().as_eq() != Some((ddom, idom.clone())) {
            return Err(bad(MINOR))
        }
        eqs.push(eq);

        // Open the binder on the checker's own telescope, at the domain the
        // interpretation recorded, so that inference under it is Lean's.
        c.push_interpreted(dom_e, idom);
        *opened += 1;
        let (wt, wm) = c.binder(0).ok_or_else(|| bad(MINOR))?;
        let wv = c.scope_vars(1).and_then(|v| v.first().copied()).ok_or_else(|| bad(MINOR))?;

        let f_tm = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?.0;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let out = match &shape {
            PiShape::Fs { dom, cod } => ip.fs_app(dom, cod, &f_tm, &wt, &f_mem, &wm),
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &wt, &f_mem, &wm),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &wt, &wm),
        }
        .ok_or_else(|| bad(MINOR))?;
        f_mem = out;

        if l < k + m {
            sub.push((mvars[l], wt.clone()));
            match cs.order[l] {
                Slot::Plain => {
                    ys.push(wt.clone());
                    plains += 1
                }
                Slot::Rec => recs += 1,
            }
        }
        ws.push(wt);
        wvs.push(wv);
        wmems.push(wm);
        cur = body;
    }
    if plains != k || recs != m {
        return Err(bad(DISAGREE))
    }

    // ── the conclusion ──────────────────────────────────────────────────────
    //
    // A field-free constructor's minor is a proof *variable*: no application
    // rule fired, so the subject is still the minor binder's own scope variable
    // and §6.2 gives it `•` by proof irrelevance. Where a rule did fire it is
    // `cond_app`, whose subject is `•` already, and this step is skipped.
    let concl_ev = c.infer_type(&cur).map_err(|_| Gap::Classifier)?;
    let point = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        ip.point()
    };
    let (subj, cset) = f_mem.concl().as_mem().ok_or_else(|| bad(MINOR))?;
    if subj != point {
        let ty_mem = concl_ev.ev.thm().cloned().ok_or_else(|| bad(MINOR))?;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        if *ty_mem.concl() != Formula::mem(cset.clone(), ip.sort(0)) {
            return Err(bad(SORTS))
        }
        let pt = ip.point_of_proof(&ty_mem, &f_mem).ok_or_else(|| bad(MINOR))?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(|| bad(MINOR))?;
        f_mem = ip.retarget_subject(&f_mem, &back).ok_or_else(|| bad(MINOR))?;
    }

    // `⟦C e⃗ᵢ (T.ctorᵢ p⃗ y⃗ r⃗)⟧` onto `app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗))`: `ni`
    // index equations and the subject, all in one spine.
    let fields: Vec<Term> = ws[..k + m].to_vec();
    let mut e_args = at.ps.clone();
    e_args.extend(ys.iter().cloned());
    let e_axs = site.tr.ax.ctors.get(i).map(|cx| &cx.result).ok_or_else(|| bad(MINOR))?;
    if e_axs.len() != ni {
        return Err(bad(DISAGREE))
    }
    let mut sp_args = at.ps.clone();
    sp_args.extend(fields.iter().cloned());
    let mut sp_mems = at.param_mems.clone();
    sp_mems.extend(wmems[..k + m].iter().cloned());

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let mut ceqs: Vec<Thm> = Vec::with_capacity(ni + 1);
    for ax in e_axs {
        let fwd = derived::inst_all(ax, &e_args).ok_or_else(|| bad(MINOR))?;
        ceqs.push(derived::eq_symm(&mut ip.env, &fwd).ok_or_else(|| bad(MINOR))?);
    }
    let (_, cbeta) = ip
        .beta_spine(&at.ctor_formers[i], &sp_args, &sp_mems)
        .ok_or_else(|| bad(MINOR))?;
    let cax = derived::inst_all(&site.tr.ctor_abbrev[i].1, &fields).ok_or_else(|| bad(MINOR))?;
    ceqs.push(derived::eq_trans(&mut ip.env, &cbeta, &cax).ok_or_else(|| bad(MINOR))?);
    let s = ip.prelude.tower.sums.clone();
    let move_eq =
        motive_congr_of(&mut ip.env, &s, &at.c_tm, &ceqs).ok_or_else(|| bad(MINOR))?;
    let concl = ip.retarget_set(&f_mem, &move_eq).ok_or_else(|| bad(MINOR))?;

    let atoms: Vec<Formula> = src.iter().map(|f| subst_f(f, &sub)).collect();
    Ok(Walked { ws, wvs, eqs, concl, atoms, sub })
}

/// The `j`-th recursive field's own binder term, found by counting `Slot::Rec`
/// down the declared mask — the induction hypothesis at level `k + m + j`
/// speaks of *that* binder, not of level `j`.
fn child_term(cs: &derived::inductive::CtorSpec, ws: &[Term], j: usize) -> Option<Term> {
    let mut seen = 0;
    for (q, sl) in cs.order.iter().enumerate() {
        if *sl == Slot::Rec {
            if seen == j {
                return ws.get(q).cloned()
            }
            seen += 1;
        }
    }
    None
}

/// `Γ ⊢ ∀w. (w ∈ Dᵈᵉʳⁱᵛᵉᵈ → φ)` from `Γ ∪ {w ∈ ⟦D⟧} ⊢ φ` and
/// `Γ ⊢ Dᵈᵉʳⁱᵛᵉᵈ = ⟦D⟧`.
///
/// The discharge and the domain rewrite in one step, because the two must
/// happen at the same moment: see the module header. `eq` may carry `Γ` — it
/// is a β step for a recursive field — and that `Γ` mentions only strictly
/// earlier binders, which the closes above this one discharge.
fn domain_swap(ip: &mut Interp, closed: &Closed, eq: &Thm, inner: &Thm) -> Option<Thm> {
    let idom = closed.domain().clone();
    let (ddom, rhs) = eq.concl().as_eq()?;
    if rhs != idom {
        return None
    }
    let w = closed.var();
    let phi = inner.concl().clone();
    let discharged = closed.discharge(inner).ok()?;
    let x = ip.env.fresh_var();
    let at = Formula::forall(w, Formula::imp(Formula::mem(Term::var(w), Term::var(x)), phi));
    let back = derived::eq_symm(&mut ip.env, eq)?;
    let leib = Thm::eq_leibniz(idom, ddom, x, at);
    Thm::mp(&Thm::mp(&leib, &back)?, &discharged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no_levels() -> Rc<[Level]> { Vec::new().into() }
    fn ty1() -> E { sort(Level::Zero.succ()) }

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
    fn indexed_env() -> (Environment, Name, Name) {
        let b = nm("B");
        let bt = konst(b.clone(), no_levels());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: b.clone(),
                lparams: vec![],
                num_params: 0,
                ty: ty1(),
                ctors: vec![
                    (Name::str(&b, "b0"), bt.clone()),
                    (Name::str(&b, "b1"), bt.clone()),
                ],
            },
        )
        .expect("B is accepted");
        let b0 = konst(Name::str(&b, "b0"), no_levels());
        let b1 = konst(Name::str(&b, "b1"), no_levels());
        let t = nm("T");
        let tap = |a: E, i: E, j: E| app(app(app(konst(t.clone(), no_levels()), a), i), j);
        let ty = forall(ty1(), forall(bt.clone(), forall(bt.clone(), ty1())));
        let ctors = vec![
            (Name::str(&t, "c0"), forall(ty1(), tap(bvar(0), b0.clone(), b0.clone()))),
            (
                Name::str(&t, "c1"),
                forall(
                    ty1(),
                    forall(
                        bt.clone(),
                        forall(tap(bvar(1), bvar(0), b0.clone()), tap(bvar(2), b1.clone(), bvar(1))),
                    ),
                ),
            ),
            (
                Name::str(&t, "c2"),
                forall(
                    ty1(),
                    forall(
                        bt.clone(),
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
                name: t.clone(),
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
        let at: Rc<[Level]> = vec![Level::Zero].into();
        let got = c.infer_type(&konst(rec.clone(), at)).expect("infer ⟦T.rec.{0}⟧");
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

    /// **The value clause is still declined, by its own name and on the other
    /// axis.**
    ///
    /// `T.rec.{1}` is the same declaration at a `Type`-valued motive, which is
    /// `INDEXED-DESIGN.md` §5.1/§5.2 and is not this module. Two things are
    /// pinned. §6.2's split is taken on the motive's *declared sort* and routes
    /// the two clauses apart — a `rec_dep` branch that sent both here would
    /// pass the test above and derive something false for this one. And the
    /// cause is **`Library`**: `GenRecursor` types into a target *set* and
    /// `DepRecursor`'s motive is applied to the tree alone, so no target policy
    /// and no mini-side recogniser reaches the fibre `app(m,x⃗,t)`. See
    /// [`crate::rec_dep::INDEXED_VALUE`]. A change that quietly refiles it as
    /// threading is a change that has decided `derived/` owes nothing, and that
    /// has to be argued there rather than here.
    #[test]
    fn the_value_clause_is_a_different_construction_and_says_so() {
        let (env, t, rec) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(t.clone(), no_levels())).expect("infer ⟦T⟧");
        let at: Rc<[Level]> = vec![Level::Zero.succ()].into();
        let got = c.infer_type(&konst(rec, at)).expect("infer");
        assert_eq!(
            got.ev.gap(),
            Some(&Gap::Recursor(t, crate::rec_dep::INDEXED_VALUE, Cause::Library)),
            "a value-valued motive needs a dependent rule over the indexed carrier"
        );
    }
}
