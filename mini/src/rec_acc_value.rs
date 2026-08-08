//! **`Acc.rec` at `u₁ ≥ 1`** — the eliminator as a *value*, `derived::rec_acc`'s
//! `pack`.
//!
//! # Interface
//!
//! ```text
//! rec_acc_value::value_bottom(checker, site) -> Typing
//! ```
//!
//! The `u₁ ≥ 1` arm of [`crate::rec_acc::ensure`]'s nest, and called from
//! nowhere else. `MINI-HANDOFF.md` §23 and §25 item 3 are the sizing; §25's
//! four pieces are, in this file,
//!
//! | # | piece | where |
//! |---|---|---|
//! | 1 | `step_typed(A,R̄,T,ē)` | [`step_typed_at`] |
//! | 2 | the refinement — `app(accrec,z) ∈ app(app(C̄,z),•)` | [`refine`], over [`crate::rec_acc_ih`] |
//! | 3 | the term: `pack`, `pack_app`, the abbreviation | [`build`]'s last third |
//!
//! # Why the refinement is a second induction and not a transport
//!
//! [`derived::rec_acc`] is **non-dependent**: it recurses into a fixed set `T`,
//! and its exports are `accrec ∈ fs(acc(A,R̄),T)` and `app(accrec,y) ∈ T`. There
//! is no analogue of `derived::inductive::DepRecursor::typing`, which is what
//! carries a class-(T) eliminator into `app(C,t)`. Lean's obligation is a
//! **fibre**, `⟦Acc.rec α r C m a t⟧ ∈ app(app(C̄,ā),•)`, so the typing has to be
//! refined from `T` down to the motive — and the only tool for that is another
//! `acc_rect`, at
//!
//! ```text
//! φ(z) := app(accrec(A,R̄,T,ē), z) ∈ app(app(C̄,z),•)
//! ```
//!
//! whose induction hypothesis feeds exactly the fibre condition at the
//! predecessors, which is why it cannot be a direct typing. So "typed into
//! `⟦Sort u₁⟧` and refined afterwards" — §23 item 2's phrase — names two
//! constructions, not a step.
//!
//! # `T` is a rung, and that is a structural fact rather than a measurement
//!
//! `Tower::at(n)` is `Some` exactly for `n ≥ 1`, with `Rung::set == Tower::u(n)`,
//! and [`Interp::sort`] **is** `Tower::u`. So at `u₁ ≥ 1` the recursor's target
//! `T = ⟦Sort u₁⟧` and the rung's own set are the same *term*, not two terms
//! that happen to be equal, and `Rung::empty_mem` and `Rung::transitive` are
//! fields on it. Both are spent, and neither exists at `u₁ = 0` — `U₀` is not a
//! universe — which is the second, independent reason §16's split had to be a
//! split.
//!
//! The equality is nevertheless *checked* rather than assumed
//! ([`RUNG`]): if a future clause reaches here with a `T` that is a genuine
//! carrier, the junk branch below demands `∅ ∈ T` and there is nothing to prove
//! it with, and a decline that names the reason is worth more than a `None` four
//! functions deeper.
//!
//! # `step_typed`'s junk branch, and where the antecedent comes from
//!
//! `ih_bound(A,T) = 𝒫(prod(A, 𝒫(prod(1,T))))` contains `∅` and every
//! non-single-valued junk relation, while the `ih` binder's own interpretation
//! is a `dprod` — only total sections. The quantifier therefore ranges strictly
//! wider than the certificate in hand and **no transport closes the gap**: the
//! discharge has to say something about `ē` applied outside its domain, and that
//! is a classical case split on `i ∈ I(x)`.
//!
//! Off the domain, [`derived::funcs::app_off_domain`] gives `step = ∅` — and its
//! antecedent `¬∃w. ⟨i,w⟩ ∈ app(app(ē,x),•)` comes off the **type**, never off
//! the term: `dprod ⊆ fs(A,·)` and `fs(a,b)`'s own members are subsets of
//! `prod(a,b)`, so a pair at `i` forces `i ∈ I(x)` whatever `ē` is. §23 item 3's
//! first draft looked for a λ-nest to take apart instead; at `117` σ `(1,1)` the
//! minor is a **binder of the recursor's own nest**, so there is no `lam` term
//! and only its typing is in hand. The route off the type is what makes the
//! discharge work at a variable minor.

use kernel::{Formula, Term, Thm};

use derived::acc::{acc_rect, ind_step, Params};
use derived::prop::cond_intro;
use derived::rec_acc::ih_bound;

use crate::acc::AccClause;
use crate::ev::{Cause, Ev, Gap};
use crate::interp::{FibreSite, Interp, PiShape};
use crate::kernel::{Checker, Typing};
use crate::rec_acc::{preds, At, Site, Src, Want};
use crate::rec_acc_ap::RecAccApparatus;
use crate::scope::Scopes;

/// `α, r, C, m, a, t` — the same nest [`crate::rec_acc`] peels.
const DEPTH: usize = 6;

const SORT: &str = "Acc.rec: the motive's sort and its codomain disagree";
const RUNG: &str = "Acc.rec: the recursor's target sort is not a universe rung";
const MAJOR: &str = "Acc.rec: the major premise's accessibility";
const MINOR_FN: &str = "Acc.rec: the minor premise does not apply at x and the accessibility";
const ACCESSIBLE: &str = "Acc.rec: the induction step's point is not accessible";
const IH_SECTION: &str = "Acc.rec: the induction hypothesis is not a section of Lean's";
const IH_APPLY: &str = "Acc.rec: the minor premise does not apply at the induction hypothesis";
const IOTA: &str = "Acc.rec: rec_acc's iota does not instantiate here";
const STEP_SHAPE: &str = "Acc.rec: the induction step is not acc_rect's premise";
const STEP_TYPED: &str = "Acc.rec: step_typed does not discharge here";
const REFINE: &str = "Acc.rec: the fibre refinement's induction step";
const RECT: &str = "Acc.rec: acc_rect does not instantiate here";
const PACK: &str = "Acc.rec: pack's beta rule does not instantiate here";
const TERM: &str = "Acc.rec: naming the eliminator's term";
const CODOMAIN: &str = "Acc.rec: the value clause did not land in the codomain";

/// The bottom of `⟦Acc.rec.{u₁,u}⟧`'s nest at `u₁ ≥ 1`.
pub(crate) fn value_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort (in `ensure`), once from the codomain the nest reached.
    match c.is_prop(&site.codomain) {
        Ok(false) => {}
        Ok(true) => return gap(bad(SORT)),
        Err(_) => return gap(Gap::Classifier),
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(vars) = c.scope_vars(DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(ac) = ip.acc() else { return gap(Gap::IndApparatus) };
    let Some(ra) = ip.rec_acc() else { return gap(Gap::IndApparatus) };
    let at = At { xs, mems, vars, former, goal };
    match build(ip, &ac, &ra, site, &at) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// Everything the two inductions are written with, built once.
///
/// **Nothing here is a nest position**, exactly as in [`crate::rec_dep`]: `a`,
/// `r` and the rest are terms and their memberships are at the domains the
/// interpretation names, which is what a binder's scope assumption is and
/// equally what a use site would produce.
pub(crate) struct Cx<'a> {
    pub(crate) ac: &'a AccClause,
    pub(crate) ra: &'a RecAccApparatus,
    /// `A = ⟦α⟧`, and its scope typing.
    pub(crate) a: Term,
    pub(crate) a_mem: Thm,
    /// `⟦r⟧`, Lean's *curried* relation, and its scope typing.
    pub(crate) r: Term,
    pub(crate) r_mem: Thm,
    /// `R̄ = rel_graph(A,⟦r⟧)` — the set of pairs `acc` reasons about.
    pub(crate) graph: Term,
    /// `acc(A,R̄)`.
    pub(crate) acc_t: Term,
    /// `⟦C⟧` and its scope typing.
    pub(crate) cm: Term,
    pub(crate) c_mem: Thm,
    /// `⟦m⟧`, Lean's minor premise, and its scope typing.
    pub(crate) em: Term,
    pub(crate) m_mem: Thm,
    /// `T = ⟦Sort u₁⟧`, which is `Rung::set`.
    pub(crate) t: Term,
    /// `⊢ ∅ ∈ T` and `⊢ ∀y. (y ∈ T → ∀z. (z ∈ y → z ∈ T))`.
    pub(crate) empty_mem: Thm,
    pub(crate) transitive: Thm,
    /// `accrec(A,R̄,T,⟦m⟧)`.
    pub(crate) accrec: Term,
}

/// The bottom's term and its typing, or the transport that did not fit.
fn build(
    ip: &mut Interp,
    ac: &AccClause,
    ra: &RecAccApparatus,
    site: &Site,
    at: &At,
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let point = ip.point();
    let (a, r, cm) = (at.xs[0].clone(), at.xs[1].clone(), at.xs[2].clone());
    let (em, aa, tt) = (at.xs[3].clone(), at.xs[4].clone(), at.xs[5].clone());
    let graph = Term::apply(ac.graph, vec![a.clone(), r.clone()]);
    let acc_t = ac.sets.of(a.clone(), graph.clone());

    // `T` is the recursor's **target sort**, not the motive's value — the
    // distinction §23 item 2 turns on, and `118`'s `λ a h. Bool` is the export
    // that would have refuted it.
    let t = ip.sort(site.u1);
    let rung = ip.prelude.tower.at(site.u1 as usize).ok_or_else(|| bad(RUNG))?;
    if rung.set != t {
        return Err(bad(RUNG))
    }
    let accrec = ra.ra.of(a.clone(), graph.clone(), t.clone(), em.clone());
    let cx = Cx {
        ac,
        ra,
        a,
        a_mem: at.mems[0].clone(),
        r,
        r_mem: at.mems[1].clone(),
        graph,
        acc_t,
        cm,
        c_mem: at.mems[2].clone(),
        em,
        m_mem: at.mems[3].clone(),
        t,
        empty_mem: rung.empty_mem.clone(),
        transitive: rung.transitive.clone(),
        accrec,
    };

    // ── the major premise: `⟦a⟧ ∈ acc(A,R̄)`, and `⟦t⟧ = •` ──────────────────
    let (a_in_acc, pt_eq_t) = major(ip, &cx, at, &aa).ok_or_else(|| bad(MAJOR))?;

    // ── piece 1, then piece 2 ───────────────────────────────────────────────
    let st = step_typed_at(ip, &cx, at).ok_or_else(|| bad(STEP_TYPED))?;
    let over = refine(ip, &cx, at, &st).map_err(&bad)?;
    let at_a = derived::inst_all(&over, std::slice::from_ref(&aa))
        .and_then(|t| Thm::mp(&t, &a_in_acc))
        .ok_or_else(|| bad(RECT))?;

    // ── piece 3: the thesis's packaging, and the term ───────────────────────
    //
    // `pack_app` reads the value off the outer abstraction: it is an equation,
    // so the typing moves onto `app(app(pack,ā),•)` by rewriting the *subject*.
    let pack = ra.ra.pack(&cx.a, &cx.graph, &cx.t, &cx.em);
    let pa = derived::inst_all(
        &ra.ra.pack_app,
        &[cx.a.clone(), cx.graph.clone(), cx.t.clone(), cx.em.clone()],
    )
    .and_then(|t| derived::inst_all(&t, std::slice::from_ref(&aa)))
    .and_then(|t| Thm::mp(&t, &a_in_acc))
    .ok_or_else(|| bad(PACK))?;
    let at_pt = ip.retarget_subject(&at_a, &pa).ok_or_else(|| bad(PACK))?;

    // `⟦t⟧ = •` moves both sides at once: the subject is `app(app(pack,ā),w)`
    // and the set is `app(app(C̄,ā),w)`, so one Leibniz rewrite at a single hole
    // carries the membership from `•` onto the binder.
    let hole = ip.env.fresh_var();
    let pack_at = ip.app(pack.clone(), aa.clone());
    let c_at = ip.app(cx.cm.clone(), aa.clone());
    let (sub_hole, set_hole) =
        (ip.app(pack_at.clone(), Term::var(hole)), ip.app(c_at.clone(), Term::var(hole)));
    let leib = Thm::eq_leibniz(point, tt.clone(), hole, Formula::mem(sub_hole, set_hole));
    let done = Thm::mp(&leib, &pt_eq_t)
        .and_then(|i| Thm::mp(&i, &at_pt))
        .ok_or_else(|| bad(CODOMAIN))?;

    // ── the term, under a name of mini's own ────────────────────────────────
    //
    // `pack` is assembled inside `derived`, so its applicative structure was
    // never recorded through `Interp::mk` and the λ above this bottom could not
    // skeletonise its body. One abbreviation over the nest's own binders fixes
    // it, exactly as `rec_dep::dep_bottom` does.
    // **`&mut ip.env`, not `Interp::ind_parts`.** `rec_dep::dep_bottom` reaches
    // its `Env` through the inductive apparatus because it is holding one
    // already; here that would make `117_accRecType` — an export that mentions
    // no inductive but `Acc` — build a `Wtype`, a `Bound` and an `IndChain` for
    // one `define_abbrev`, which is the whole expense `crate::acc`'s laziness
    // exists to avoid.
    let raw = ip.app(pack_at, tt);
    let (sym, ax) =
        derived::define_abbrev(&mut ip.env, &at.vars, &raw).ok_or_else(|| bad(TERM))?;
    // **And the name is kept.** `define_abbrev` mints a fresh symbol per call,
    // so this equation is the only way from the symbol a β chain lands on back
    // to `pack` — and the ι rule ([`crate::rec_acc_iota`]) has no other route.
    // Dropping it is `MINI-HANDOFF.md` §2's sixth instance; storing it before
    // that reader existed would have been §26 item 1's from the other side.
    ip.rec_acc_elims.insert(
        (site.rec, site.rec_inst.clone()),
        std::rc::Rc::new(crate::interp::RecAccElim { sym, ax: ax.clone() }),
    );
    let unfold = derived::inst_all(&ax, &at.xs).ok_or_else(|| bad(TERM))?;
    let term = ip.mk(sym, at.xs.clone());
    let out = ip.retarget_subject(&done, &unfold).ok_or_else(|| bad(TERM))?;
    if *out.concl() != Formula::mem(term.clone(), at.goal.clone()) {
        return Err(bad(CODOMAIN))
    }
    Ok((term, out))
}

/// `Γ ⊢ ⟦a⟧ ∈ acc(A,R̄)` and `Γ ⊢ • = ⟦t⟧`, from the major premise's own scope
/// typing.
///
/// Identical to the `u₁ = 0` clause's opening: `t : Acc α r a` is a proof, so
/// `⟦t⟧` is an element of a conditional singleton and therefore equal to `•`,
/// and the singleton's elimination is what puts `⟦a⟧` into the carrier.
pub(crate) fn major(ip: &mut Interp, cx: &Cx<'_>, at: &At, aa: &Term) -> Option<(Thm, Thm)> {
    let sums = ip.prelude.tower.sums.clone();
    let tower = ip.prelude.tower.clone();
    let args = [cx.a.clone(), cx.r.clone(), aa.clone()];
    let mems = [cx.a_mem.clone(), cx.r_mem.clone(), at.mems[4].clone()];
    let (set_a, beta_a) = ip.beta_spine(&at.former, &args, &mems)?;
    let t_in_set = ip.retarget_set(&at.mems[5], &beta_a)?;
    let chi_a = derived::inst_all(&cx.ac.acc_set_ax, &args)?;
    let phi_a = cx.ac.phi(&cx.a, &cx.r, aa);
    let in_u0 = tower.cond_in_u0(&mut ip.env, &phi_a, &set_a, &chi_a)?;
    let t_pt = ip.point_of_proof(&in_u0, &t_in_set)?;
    let pt_eq_t = derived::eq_symm(&mut ip.env, &t_pt)?;
    let pt_in_set = ip.retarget_subject(&t_in_set, &pt_eq_t)?;
    let elim = derived::prop::cond_elim(&sums, &phi_a, &set_a, &chi_a)?;
    let a_in_acc = Thm::mp(&elim, &pt_in_set)?;
    Some((a_in_acc, pt_eq_t))
}

// ─────────────────────────────────────────────────────────────────────────────
// Lean's minor premise, applied at a point and at its accessibility
// ─────────────────────────────────────────────────────────────────────────────

/// `Γ ⊢ app(app(ē,x),•) ∈ ⟦(∀ y (hy : r y x), C y (h y hy)) → C x (…)⟧`, plus
/// the site and domain of that last `Π`.
///
/// The **two** levels both clauses of this file share. Level 1 is
/// [`Interp::dprod_app`] at `x`; level 2 is `dprod_app` at `•`, and its argument
/// obligation is `• ∈ ⟦∀ y, r y x → Acc α r y⟧` — every predecessor of `x` is
/// accessible, which at a *use* site has no induction hypothesis behind it and
/// is **A4** ([`Src::Pred`]).
///
/// The third level is deliberately *not* taken here: [`step_typed_at`] applies
/// it at an arbitrary `i` and [`refine`] at the recursion's own `ih`, and those
/// are the two obligations that differ.
///
/// # The caller's stack, and what happens on a `None`
///
/// `sc` is the caller's own [`Scopes`], and the scope this opens is abandoned —
/// token and all — on every early exit between the open and the close. That is
/// sound because the caller `?`-propagates out of the function that owns the
/// stack, so the stack is dropped rather than closed; and a caller that did not
/// would abort at [`Scopes::close`]'s LIFO assertion rather than derive
/// anything. `mini/src/scope.rs`'s I2 is the argument in full.
fn minor_fn(
    ip: &mut Interp,
    cx: &Cx<'_>,
    at: &At,
    x: &Term,
    x_in_a: &Thm,
    x_in_acc: &Thm,
    sc: &mut Scopes,
) -> Option<(Term, Thm, FibreSite, Term)> {
    let point = ip.point();
    let m_set = cx.m_mem.concl().as_mem()?.1.clone();
    let PiShape::Dep { site: s1, dom: d1 } = ip.as_pi(&m_set)? else { return None };
    if d1 != cx.a {
        return None
    }
    let at_x = ip.dprod_app(&s1, &d1, &cx.em, x, &cx.m_mem, x_in_a)?;

    let (f1, h_set) = {
        let (s, t) = at_x.concl().as_mem()?;
        (s.clone(), t.clone())
    };
    let PiShape::Dep { site: s2, dom: hset } = ip.as_pi(&h_set)? else { return None };
    let h_mem = preds(
        ip,
        cx.ac,
        Want::Accessible,
        &hset,
        at,
        x,
        x_in_a,
        Src::Pred { rule: &cx.ra.pred_closed, x_in_acc },
        sc,
    )?;
    let at_h = ip.dprod_app(&s2, &hset, &f1, &point, &at_x, &h_mem)?;

    let (f2, i_set) = {
        let (s, t) = at_h.concl().as_mem()?;
        (s.clone(), t.clone())
    };
    let PiShape::Dep { site: s3, dom: iset } = ip.as_pi(&i_set)? else { return None };
    Some((f2, at_h, s3, iset))
}

/// `Γ ⊢ x ∈ A` from `Γ ⊢ x ∈ acc(A,R̄)` — **A0**.
pub(crate) fn in_carrier(cx: &Cx<'_>, x: &Term, x_in_acc: &Thm) -> Option<Thm> {
    let a0 = derived::inst_all(
        &cx.ac.sets.acc_subset,
        &[cx.a.clone(), cx.graph.clone(), x.clone()],
    )?;
    Thm::mp(&a0, x_in_acc)
}

/// `Γ ⊢ • ∈ ⟦Acc α r x⟧` from `Γ ⊢ x ∈ acc(A,R̄)`.
///
/// The conditional singleton's introduction, then one [`Interp::beta_spine`]
/// read backwards: `⟦Acc α r x⟧` is a redex over the stored `⟦Acc.{u}⟧` nest,
/// not the `acc_set` the clause denotes with.
pub(crate) fn acc_point(
    ip: &mut Interp,
    cx: &Cx<'_>,
    at: &At,
    x: &Term,
    x_in_a: &Thm,
    x_in_acc: &Thm,
) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();
    let args = [cx.a.clone(), cx.r.clone(), x.clone()];
    let chi = derived::inst_all(&cx.ac.acc_set_ax, &args)?;
    let phi = cx.ac.phi(&cx.a, &cx.r, x);
    let set = ip.mk(cx.ac.acc_set, args.to_vec());
    let intro = cond_intro(&sums, &phi, &set, &chi)?;
    let pt = Thm::mp(&intro, x_in_acc)?;
    let mems = [cx.a_mem.clone(), cx.r_mem.clone(), x_in_a.clone()];
    let (_, beta) = ip.beta_spine(&at.former, &args, &mems)?;
    let back = derived::eq_symm(&mut ip.env, &beta)?;
    ip.retarget_set(&pt, &back)
}

/// `Γ ⊢ app(app(C̄,x),•) ∈ T` — the motive's own fibre, in the target sort.
///
/// `C : ∀ a, Acc α r a → Sort u₁`, so this is [`Interp::dprod_app`] twice: at
/// `x`, and at the accessibility proof, which denotes `•`. It is what
/// `Rung::transitive` then carries the step's value along.
pub(crate) fn motive_fibre(
    ip: &mut Interp,
    cx: &Cx<'_>,
    at: &At,
    x: &Term,
    x_in_a: &Thm,
    x_in_acc: &Thm,
) -> Option<(Term, Thm)> {
    let point = ip.point();
    let c_set = cx.c_mem.concl().as_mem()?.1.clone();
    let PiShape::Dep { site: s1, dom: d1 } = ip.as_pi(&c_set)? else { return None };
    if d1 != cx.a {
        return None
    }
    let at_x = ip.dprod_app(&s1, &d1, &cx.cm, x, &cx.c_mem, x_in_a)?;
    let (c_at, acc_set) = {
        let (s, t) = at_x.concl().as_mem()?;
        (s.clone(), t.clone())
    };
    let PiShape::Dep { site: s2, dom: d2 } = ip.as_pi(&acc_set)? else { return None };
    let pt = acc_point(ip, cx, at, x, x_in_a, x_in_acc)?;
    let out = ip.dprod_app(&s2, &d2, &c_at, &point, &at_x, &pt)?;
    let fibre = ip.app(c_at, point);
    (*out.concl() == Formula::mem(fibre.clone(), cx.t.clone())).then_some((fibre, out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Piece 1 — `step_typed`
// ─────────────────────────────────────────────────────────────────────────────

/// `Γ ⊢ step_typed(A,R̄,T,ē)` — the one hypothesis anything in
/// [`derived::rec_acc`] carries.
///
/// ```text
/// ∀x. (x ∈ acc(A,R̄) → ∀i. (i ∈ ih_bound(A,T) → app(app(app(ē,x),•),i) ∈ T))
/// ```
///
/// Two binders and a classical case split. The result is compared against the
/// formula `derived` builds at these very terms, so what is produced is A3's
/// premise rather than merely something of that shape.
pub(crate) fn step_typed_at(ip: &mut Interp, cx: &Cx<'_>, at: &At) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();

    let mut sc = Scopes::new();
    let tok_x = sc.open(&mut ip.env, cx.acc_t.clone());
    let (x, x_in_acc) = {
        let s = sc.get(0)?;
        (s.term(), s.assumption().clone())
    };
    let x_in_a = in_carrier(cx, &x, &x_in_acc)?;
    let (f, f_mem, s3, iset) = minor_fn(ip, cx, at, &x, &x_in_a, &x_in_acc, &mut sc)?;
    let (_, fibre_mem) = motive_fibre(ip, cx, at, &x, &x_in_a, &x_in_acc)?;

    let tok_i = sc.open(&mut ip.env, ih_bound(&sums, &cx.a, &cx.t));
    let i = {
        let s = sc.get(0)?;
        s.term()
    };
    let step = ip.app(f.clone(), i.clone());
    let goal = Formula::mem(step.clone(), cx.t.clone());
    let phi = Formula::mem(i.clone(), iset.clone());

    // ── `i` is a section of Lean's own `ih` type ────────────────────────────
    let (tok_p, in_dom) = sc.assume(phi.clone());
    let inside = {
        let at_i = ip.dprod_app(&s3, &iset, &f, &i, &f_mem, &in_dom)?;
        // One `Rung::transitive`, off the motive's fibre and into the sort it
        // was declared in. The fibre is *compared*, not assumed: a codomain
        // that depends on the `ih` argument would land somewhere else.
        let trans = derived::inst_all(&cx.transitive, &[at_i.concl().as_mem()?.1.clone()])?;
        let over = Thm::mp(&trans, &fibre_mem)?;
        Thm::mp(&derived::inst_all(&over, std::slice::from_ref(&step))?, &at_i)?
    };
    let left = sc.discharge_assumption(tok_p, &inside);

    // ── or it is junk, and the step is `∅` ──────────────────────────────────
    let (tok_n, off_dom) = sc.assume(Formula::not(phi.clone()));
    let outside = {
        let no_pair = no_pair_at(ip, &s3, &iset, &f, &f_mem, &i, &off_dom)?;
        let eq = derived::inst_all(&cx.ra.app_off_domain, &[f.clone(), i.clone()])
            .and_then(|t| Thm::mp(&t, &no_pair))?;
        ip.retarget_subject(&cx.empty_mem, &eq)?
    };
    let right = sc.discharge_assumption(tok_n, &outside);

    // `Formula::or(φ,ψ)` unfolds to `¬φ → ψ`, so excluded middle at `φ` is
    // `imp_refl(¬φ)` and costs nothing at all.
    let disj = Formula::or(phi.clone(), Formula::not(phi.clone()));
    let em = derived::imp_refl(Formula::not(phi));
    let both = derived::hyp_or_elim(
        &derived::imp_refl(disj.clone()),
        &derived::a1i(&left, disj.clone()),
        &derived::a1i(&right, disj),
    )?;
    let out = Thm::mp(&both, &em)?;
    if *out.concl() != goal {
        return None
    }

    let over_i = sc.close(tok_i).discharge(&out).ok()?;
    let over_x = sc.close(tok_x).discharge(&over_i).ok()?;
    let want = derived::rec_acc::step_typed(
        &mut ip.env,
        &cx.ra.ra.base,
        &cx.a,
        &cx.graph,
        &cx.t,
        &cx.em,
    );
    (*over_x.concl() == want).then_some(over_x)
}

/// `Γ ⊢ ¬∃w. ⟨i,w⟩ ∈ f`, from `Γ ⊢ ¬(i ∈ I)` and `Γ ⊢ f ∈ dprod(q⃗,I)`.
///
/// **Off the type, not off the term.** `dprod(q⃗,I) ⊆ fs(I, ⋃img(q⃗,I))` and a
/// member of `fs(a,b)` is a subset of `prod(a,b)`, so any pair in `f` has its
/// first component in `I` — which is what the case hypothesis denies. Nothing
/// about `f`'s structure is used, which is what makes this work at a minor
/// premise that is a bare scope variable.
fn no_pair_at(
    ip: &mut Interp,
    site: &FibreSite,
    iset: &Term,
    f: &Term,
    f_mem: &Thm,
    i: &Term,
    not_in: &Thm,
) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();
    let base = sums.ap.sets.union_of(site.dp.img_of(&site.holes, iset.clone()));

    let mut args = site.holes.clone();
    args.push(iset.clone());
    let sub = derived::inst_all(&site.dp.dprod_sub, &args)?;
    let in_fs = Thm::mp(&derived::inst_all(&sub, std::slice::from_ref(f))?, f_mem)?;
    let is_fun = Thm::mp(
        &derived::iff_mp(&derived::inst_all(
            &sums.fs.fs_ax,
            &[iset.clone(), base.clone(), f.clone()],
        )?)?,
        &in_fs,
    )?;
    let f_sub = derived::and_elim_left(&is_fun)?;

    let wv = ip.env.fresh_var();
    let w = Term::var(wv);
    let pair = sums.ap.sets.pair(i.clone(), w.clone());
    let to_prod = derived::inst_all(&f_sub, std::slice::from_ref(&pair))?;
    let split = derived::iff_mp(&derived::inst_all(
        &sums.pair_in_prod,
        &[iset.clone(), base.clone(), i.clone(), w.clone()],
    )?)?;
    let to_first = derived::and_left(
        Formula::mem(i.clone(), iset.clone()),
        Formula::mem(w, base),
    );
    let to_false = derived::syl(&derived::syl(&derived::syl(&to_prod, &split)?, &to_first)?, not_in)?;
    let all_w = crate::rec_dep::gen_all_checked(&[wv], &to_false)?;
    derived::exists_elim_imp(wv, &all_w, &Formula::false_())
}

// ─────────────────────────────────────────────────────────────────────────────
// Piece 2 — the fibre refinement
// ─────────────────────────────────────────────────────────────────────────────

/// `Γ ⊢ ∀z. (z ∈ acc(A,R̄) → app(accrec,z) ∈ app(app(C̄,z),•))` — the second
/// `acc_rect`.
///
/// [`derived::rec_acc`]'s own typing lands in `T`; this is what brings it down
/// to Lean's motive. The induction step rewrites `app(accrec,x)` by ι and then
/// applies Lean's minor at `x`, at `•`, and at the recursion's own induction
/// hypothesis — and that last argument's typing is the whole of
/// [`crate::rec_acc_ih`].
fn refine(ip: &mut Interp, cx: &Cx<'_>, at: &At, st: &Thm) -> Result<Thm, &'static str> {
    let point = ip.point();
    // `φ(z) := app(accrec,z) ∈ app(app(C̄,z),•)`.
    let zv = ip.env.fresh_var();
    let phi = {
        let lhs = ip.app(cx.accrec.clone(), Term::var(zv));
        let at_z = ip.app(cx.cm.clone(), Term::var(zv));
        Formula::mem(lhs, ip.app(at_z, point))
    };
    let step = ind_step_at(ip, cx, at, st, zv, &phi)?;

    // `acc_rect` carves `{z ∈ acc(A,R) : φ(z)}` by Separation over `params`, so
    // **every** free variable of `φ` has to be listed — and here `φ` mentions
    // `accrec(A,R̄,T,ē)`, hence all four of `α`, `r`, `C` and `m`. The `u₁ = 0`
    // clause lists only the motive's because its `φ` is `• ∈ app(app(C̄,z),•)`
    // and mentions nothing else; that is the one difference between the two
    // calls, and it is not a difference in the scheme.
    let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
    let params = [av, rv, at.vars[0], at.vars[1], at.vars[2], at.vars[3]];
    let sets = cx.ac.sets.clone();
    let rule = acc_rect(&mut ip.env, &sets, &params, Params { a: av, r: rv }, zv, &phi).ok_or(RECT)?;
    let want = ind_step(
        &mut ip.env,
        &sets,
        &cx.acc_t,
        &cx.a,
        &cx.graph,
        zv,
        &phi,
    );
    if *step.concl() != want {
        return Err(STEP_SHAPE)
    }
    let rule = crate::rec_dep::gen_all_checked(&params[..2], &rule).ok_or(RECT)?;
    let rule = derived::inst_all(&rule, &[cx.a.clone(), cx.graph.clone()]).ok_or(RECT)?;
    Thm::mp(&rule, &step).ok_or(RECT)
}

/// `Γ ⊢ ind_step(φ)` at `φ(z) := app(accrec,z) ∈ app(app(C̄,z),•)`.
fn ind_step_at(
    ip: &mut Interp,
    cx: &Cx<'_>,
    at: &At,
    st: &Thm,
    zv: kernel::FreeVar,
    phi: &Formula,
) -> Result<Thm, &'static str> {
    let up = cx.ac.sets.sets.up;

    let mut sc = Scopes::new();
    let tok_x = sc.open(&mut ip.env, cx.a.clone());
    let (x, x_in_a) = {
        let s = sc.get(0).ok_or(REFINE)?;
        (s.term(), s.assumption().clone())
    };

    // The induction hypothesis, spelled as `derived::acc::ind_step` spells it.
    let yv = ip.env.fresh_var();
    let y = Term::var(yv);
    let ih_formula = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(y.clone(), cx.a.clone()),
            Formula::imp(
                Formula::mem(derived::opair(up, y.clone(), x.clone()), cx.graph.clone()),
                Formula::and(
                    Formula::mem(y, cx.acc_t.clone()),
                    phi.subst(zv, &Term::var(yv)),
                ),
            ),
        ),
    );
    let (tok_ih, ih) = sc.assume(ih_formula);

    // `x` is accessible: A1 from the induction hypothesis's *left* conjunct.
    // The scheme carves `{z ∈ acc : φ(z)}` out of `acc`, not out of `A`, and
    // that conjunct is the whole reason this step is available.
    let x_in_acc = accessible_from_ih(ip, cx, &x, &x_in_a, &ih).ok_or(ACCESSIBLE)?;

    let (f, f_mem, s3, iset) =
        minor_fn(ip, cx, at, &x, &x_in_a, &x_in_acc, &mut sc).ok_or(MINOR_FN)?;
    let ih_mem = crate::rec_acc_ih::ih_in_minor_domain(ip, cx, &x, &x_in_a, &ih, &iset, &mut sc)
        .ok_or(IH_SECTION)?;
    let ih_tm = ih_mem.concl().as_mem().ok_or(IH_APPLY)?.0.clone();
    let at_i = ip.dprod_app(&s3, &iset, &f, &ih_tm, &f_mem, &ih_mem).ok_or(IH_APPLY)?;

    // ι, at the recursion's own induction hypothesis: `app(accrec,x)` **is**
    // the step this walk just typed.
    let iota = derived::inst_all(
        &cx.ra.ra.iota,
        &[cx.a.clone(), cx.graph.clone(), cx.t.clone(), cx.em.clone()],
    )
    .and_then(|t| Thm::mp(&t, st))
    .and_then(|t| derived::inst_all(&t, std::slice::from_ref(&x)))
    .and_then(|t| Thm::mp(&t, &x_in_acc))
    .ok_or(IOTA)?;
    let body = ip.retarget_subject(&at_i, &iota).ok_or(IOTA)?;
    if *body.concl() != phi.subst(zv, &x) {
        return Err(REFINE)
    }

    let discharged = sc.discharge_assumption(tok_ih, &body);
    sc.close(tok_x).discharge(&discharged).map_err(|_| REFINE)
}

/// `Γ ⊢ x ∈ acc(A,R̄)` from `x ∈ A` and the induction hypothesis — **A1**.
///
/// `acc_intro`'s second premise is `∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ → y ∈ acc(A,R̄)))`,
/// which is the induction hypothesis with its right conjunct dropped. No graph
/// bridge is involved: both sides speak of the pair.
fn accessible_from_ih(
    ip: &mut Interp,
    cx: &Cx<'_>,
    x: &Term,
    x_in_a: &Thm,
    ih: &Thm,
) -> Option<Thm> {
    let yv = ip.env.fresh_var();
    let y = Term::var(yv);
    let at_y = derived::inst_all(ih, std::slice::from_ref(&y))?;
    let (y_in_a, rest) = at_y.concl().as_imp()?;
    let (pair, conj) = rest.as_imp()?;
    let (l, r) = split_and(&conj)?;
    // `⊢ (y ∈ acc ∧ φ(y)) → y ∈ acc`, lifted under the two antecedents.
    let drop = derived::imp_mono_r(
        &derived::imp_mono_r(&derived::and_left(l, r), pair)?,
        y_in_a,
    )?;
    let under = Thm::mp(&drop, &at_y)?;
    let preds = crate::rec_dep::gen_all_checked(&[yv], &under)?;
    let a1 = derived::inst_all(
        &cx.ac.sets.acc_intro,
        &[cx.a.clone(), cx.graph.clone(), x.clone()],
    )?;
    Thm::mp(&a1, &derived::and_intro(x_in_a, &preds))
}

/// `φ ∧ ψ` taken apart, as the pair of formulas.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, bot) = f.as_imp()?;
    if bot != Formula::false_() {
        return None
    }
    let (phi, npsi) = inner.as_imp()?;
    let (psi, bot2) = npsi.as_imp()?;
    (bot2 == Formula::false_()).then_some((phi, psi))
}
