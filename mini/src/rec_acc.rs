//! **`Acc.rec`** — the accessibility eliminator, `Acc.rec.{u₁,u}`
//! (thesis.txt:2155–2166, `MINI-HANDOFF.md` §16 item 1 and §23).
//!
//! # Interface
//!
//! ```text
//! rec_acc::ensure(checker, Acc, σ_Acc, Acc.rec, σ_rec) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] on the declaration
//! [`crate::direct::Clause::Acc`] names, and from nowhere else. On success
//! `⟦Acc.rec.{σ_rec}⟧` and its typing are in the store.
//!
//! # Two rules, not one rule at two levels
//!
//! `Acc.rec.{u₁,u}`'s codomain is `C a t : Sort u₁`, so §6.2's own split
//! decides which object the eliminator is, exactly as it does for
//! [`crate::rec_dep`]:
//!
//! | `u₁` | interpretation | what carries the bottom |
//! |---|---|---|
//! | `0` | `•` | [`derived::acc::acc_rect`] at `φ(z) := • ∈ app(app(⟦C⟧,z),•)` |
//! | `≥ 1` | `app(app(pack,·),•)` | `derived::rec_acc::pack` and a discharge of `step_typed` |
//!
//! Only the first is wired here; the second is [`VALUE`]. `u₁` is read off the
//! recursor's **own** motive binder ([`crate::rec_dep::motive_level`]) and not
//! off `σ`, so a recursor whose motive is not a family of sorts is declined
//! rather than mis-routed.
//!
//! # The `u₁ = 0` clause
//!
//! ```text
//! Acc.rec.{0,u} : ∀ (α : Sort u) (r : α → α → Prop)
//!                   (C : ∀ a, Acc α r a → Sort 0)
//!                   (m : ∀ x (h : ∀ y, r y x → Acc α r y),
//!                          (∀ y (hy : r y x), C y (h y hy)) → C x (Acc.intro α r x h))
//!                   (a : α) (t : Acc α r a), C a t
//! ```
//!
//! Every `Π` in it is `Prop`-valued, so the whole nest is conditional
//! singletons and [`Interp::cond_app`] is the only application rule the walk
//! fires. What has to be produced is A3's premise
//!
//! ```text
//! ind_step(φ) = ∀x. (x ∈ A → ((∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ →
//!                     (y ∈ acc(A,R̄) ∧ φ(y))))) → φ(x)))
//! ```
//!
//! at `φ(z) := • ∈ app(app(⟦C⟧,z),•)`, and then [`derived::acc::acc_rect`]
//! carries it to every accessible point. The major premise `t : Acc α r a`
//! delivers `⟦a⟧ ∈ acc(A,R̄)` — one [`Interp::beta_spine`] off the stored
//! `⟦Acc.{u}⟧` nest, then [`derived::prop::cond_elim`] — and `⟦t⟧ = •` by proof
//! irrelevance, which is what moves `φ(⟦a⟧)` onto the declared codomain
//! `app(app(⟦C⟧,⟦a⟧),⟦t⟧)`.
//!
//! # The eliminator wants `pair_in_graph`, and that is the opposite of what §17
//! predicted
//!
//! `MINI-HANDOFF.md` §17 item 3 corrected the two graph bridges' attribution
//! and concluded *"`step_closed` has it in the same position, so the eliminator
//! wants `graph_pair` too"*, leaving
//! [`AccClause::pair_in_graph`](crate::acc::AccClause::pair_in_graph) with no
//! consumer in `mini/` and the `ℓ > 0` quotient clause as its expected first
//! one. Measured here, the eliminator wants **`pair_in_graph`**, twice, and
//! `graph_pair` not at all.
//!
//! The rule §17 states is right and the application of it was not. A bridge is
//! chosen by which side of the implication the consumer stands on — and
//! `preds_in` occurs at *opposite polarities* in the two consumers:
//!
//! ```text
//! acc_intro : (x ∈ A ∧ preds_in(A,R̄,acc,x)) → x ∈ acc(A,R̄)   — preds_in is proved
//! ind_step  : ∀x. (x ∈ A → (preds_in-shaped IH → φ(x)))       — the IH is used
//! ```
//!
//! Proving `∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ → …))` **holds** the pair membership;
//! *using* one **owes** it, and what is in hand instead is Lean's curried
//! `r y x` as `• ∈ app(app(⟦r⟧,y),x)`. `acc_intro` is on the first side and
//! `Acc.rec` is on the second, even though the formula is the same formula. So
//! the discriminator has to be applied to the *occurrence*, not to the theorem
//! it appears in.
//!
//! # Assuming a formula that is not a membership
//!
//! `ind_step`'s induction hypothesis is a `∀`-formula, so it cannot be opened
//! as a binder. [`Scopes::assume`] is the entry point — see `crate::scope`'s
//! header for why it lives there and not here.

use kernel::{Formula, FreeVar, Term, Thm};

use derived::acc::{acc_rect, ind_step, Params};
use derived::prop::{cond_elim, cond_intro};

use crate::acc::AccClause;
use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};
use crate::scope::Scopes;

/// **`Acc.rec` at `u₁ ≥ 1`.** The eliminator is a value, `derived::rec_acc`'s
/// `pack(A,R̄,T,e)`, and `pack_iota` is guarded by `step_typed(A,R,T,e)` — the
/// only hypothesis in that module. `MINI-HANDOFF.md` §23 is the sizing.
pub const VALUE: &str = "acc eliminator: rec_acc::pack is not wired at u:1";

/// `α, r, C, m, a, t` — `num_params + 1 + num_minors + num_indices + 1` at
/// `Acc`'s `(2, 1, 1)`.
const DEPTH: usize = 6;

const SHAPE: &str = "Acc.rec: recursor shape";
const ARITY: &str = "Acc.rec: recursor arity";
const MOTIVE: &str = "Acc.rec: the motive's binder is not a Lean motive";
const SORT: &str = "Acc.rec: the motive's sort and its codomain disagree";
const MAJOR: &str = "Acc.rec: the major premise's accessibility";
const MINOR: &str = "Acc.rec: the minor premise does not transport to ind_step";
const RECT: &str = "Acc.rec: acc_rect does not instantiate here";
const CODOMAIN: &str = "Acc.rec: the proof clause did not land in the codomain";

/// Make `⟦Acc.rec.{σ_rec}⟧` available, or say which of the two rules is owed.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    };
    if (*num_params, *num_minors, *num_indices) != (2, 1, 1) {
        return Err(bad(SHAPE))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    }
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let u1 = crate::rec_dep::motive_level(&rec_ty, 2, 1).ok_or_else(|| bad(MOTIVE))?;
    let codomain = crate::zoneb::peel(&rec_ty, DEPTH).ok_or_else(|| bad(ARITY))?;
    let site = Site {
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        codomain,
        u1,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        Ok(if site.u1 == 0 {
            prop_bottom(c, &site)
        } else {
            crate::rec_acc_value::value_bottom(c, &site)
        })
    };
    let t = c.lam_nest(&rec_ty, DEPTH, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// Which declaration's eliminator is being built, and the codomain read off the
/// recursor's own type.
pub(crate) struct Site {
    pub(crate) ind: Name,
    pub(crate) inst: Vec<u32>,
    pub(crate) codomain: E,
    /// The motive's resultant sort, read off the recursor's own motive binder.
    /// `0` is the proof clause above; everything else is
    /// [`crate::rec_acc_value`].
    pub(crate) u1: u32,
}

/// The bottom of `⟦Acc.rec.{0,u}⟧`'s nest: `•`, and `• ∈ ⟦C a t⟧`.
fn prop_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort (in `ensure`), once from the codomain the nest reached.
    match c.is_prop(&site.codomain) {
        Ok(true) => {}
        Ok(false) => return gap(bad(SORT)),
        Err(_) => return gap(Gap::Classifier),
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(vars) = c.scope_vars(DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(ac) = ip.acc() else { return gap(Gap::IndApparatus) };
    let point = ip.point();
    let at = At { xs, mems, vars, former, goal };
    match build(ip, &ac, site, &at) {
        Ok(thm) => Typing { ty, tm: Some(point), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// What the nest's scopes hold at the bottom, plus the one store read.
pub(crate) struct At {
    /// `⟦α⟧, ⟦r⟧, ⟦C⟧, ⟦m⟧, ⟦a⟧, ⟦t⟧`, outermost first.
    pub(crate) xs: Vec<Term>,
    /// Their scope typings, in the same order.
    pub(crate) mems: Vec<Thm>,
    /// Their kernel variables; the motive's is read by `acc_rect`, which wants
    /// it because `φ` mentions `⟦C⟧`, and all six by the `u₁ ≥ 1` clause's
    /// `define_abbrev`.
    pub(crate) vars: Vec<FreeVar>,
    /// The stored `⟦Acc.{u}⟧` nest.
    pub(crate) former: Term,
    /// `⟦C a t⟧`, the set the bottom's membership must be about.
    pub(crate) goal: Term,
}

/// `Γ ⊢ • ∈ ⟦C a t⟧`.
fn build(ip: &mut Interp, ac: &AccClause, site: &Site, at: &At) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let sums = ip.prelude.tower.sums.clone();
    let tower = ip.prelude.tower.clone();
    let point = ip.point();
    let (a, r, cm) = (at.xs[0].clone(), at.xs[1].clone(), at.xs[2].clone());
    let (aa, tt) = (at.xs[4].clone(), at.xs[5].clone());
    let (a_mem, r_mem) = (at.mems[0].clone(), at.mems[1].clone());
    let (m_mem, aa_mem, tt_mem) = (at.mems[3].clone(), at.mems[4].clone(), at.mems[5].clone());
    // `R̄ = rel_graph(A,⟦r⟧)`: `acc` reasons about a set of pairs and Lean's `r`
    // is curried. See [`crate::acc`].
    let graph = Term::apply(ac.graph, vec![a.clone(), r.clone()]);

    // `φ(z) := • ∈ app(app(⟦C⟧,z),•)` — the motive at `z` and at the proof of
    // `Acc α r z`, which is `•` because `Acc α r z` is a `Prop`.
    let zv = ip.env.fresh_var();
    let phi = {
        let at_z = ip.app(cm.clone(), Term::var(zv));
        Formula::mem(point.clone(), ip.app(at_z, point.clone()))
    };

    // ── the major premise: `⟦a⟧ ∈ acc(A,R̄)`, and `⟦t⟧ = •` ─────────────────
    let args_a = [a.clone(), r.clone(), aa.clone()];
    let (set_a, beta_a) = ip
        .beta_spine(&at.former, &args_a, &[a_mem.clone(), r_mem.clone(), aa_mem])
        .ok_or_else(|| bad(MAJOR))?;
    let t_in_set = ip.retarget_set(&tt_mem, &beta_a).ok_or_else(|| bad(MAJOR))?;
    let chi_a = derived::inst_all(&ac.acc_set_ax, &args_a).ok_or_else(|| bad(MAJOR))?;
    let phi_a = ac.phi(&a, &r, &aa);
    let in_u0 = tower
        .cond_in_u0(&mut ip.env, &phi_a, &set_a, &chi_a)
        .ok_or_else(|| bad(MAJOR))?;
    // `⟦t⟧ = •`: the proof binder ranges over a conditional singleton, so §6.2's
    // proof irrelevance applies to it exactly as it does inside `cond_app`.
    let t_pt = ip.point_of_proof(&in_u0, &t_in_set).ok_or_else(|| bad(MAJOR))?;
    let pt_eq_t = derived::eq_symm(&mut ip.env, &t_pt).ok_or_else(|| bad(MAJOR))?;
    let pt_in_set = ip.retarget_subject(&t_in_set, &pt_eq_t).ok_or_else(|| bad(MAJOR))?;
    let elim = cond_elim(&sums, &phi_a, &set_a, &chi_a).ok_or_else(|| bad(MAJOR))?;
    let a_in_acc = Thm::mp(&elim, &pt_in_set).ok_or_else(|| bad(MAJOR))?;

    // ── A3's premise, from Lean's own minor ─────────────────────────────────
    let step = ind_step_at(ip, ac, at, &graph, &m_mem, zv, &phi).ok_or_else(|| bad(MINOR))?;

    // ── A3, at the variables `derived` states it over ───────────────────────
    //
    // `acc_rect` mints `{z ∈ acc(A,R) : φ(z)}` over `params`, so the motive's
    // own variable has to be one of them; `A` and `R` are then generalised and
    // instantiated at this nest's terms, which is `decl_rect`'s shape in
    // [`crate::rec_dep`] one declaration along.
    let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
    let params = [av, rv, at.vars[2]];
    let sets = ac.sets.clone();
    let rule = acc_rect(&mut ip.env, &sets, &params, Params { a: av, r: rv }, zv, &phi)
        .ok_or_else(|| bad(RECT))?;
    // The premise `derived` rebuilds at these very terms — so what `ind_step_at`
    // produced is compared against A3's own statement and not merely used.
    let want = ind_step(&mut ip.env, &sets, &sets.of(a.clone(), graph.clone()), &a, &graph, zv, &phi);
    if *step.concl() != want {
        return Err(bad(MINOR))
    }
    let rule = crate::rec_dep::gen_all_checked(&params[..2], &rule).ok_or_else(|| bad(RECT))?;
    let rule = derived::inst_all(&rule, &[a, graph]).ok_or_else(|| bad(RECT))?;
    let over = Thm::mp(&rule, &step).ok_or_else(|| bad(RECT))?;
    let at_a = derived::inst_all(&over, std::slice::from_ref(&aa)).ok_or_else(|| bad(RECT))?;
    let out = Thm::mp(&at_a, &a_in_acc).ok_or_else(|| bad(RECT))?;

    // ── `φ(⟦a⟧)` is the codomain with `•` where `⟦t⟧` stands ────────────────
    let hole = ip.env.fresh_var();
    let c_at_a = ip.app(cm, aa);
    let at_hole = ip.app(c_at_a, Term::var(hole));
    let leib =
        Thm::eq_leibniz(point.clone(), tt, hole, Formula::mem(point.clone(), at_hole));
    let done = Thm::mp(&leib, &pt_eq_t)
        .and_then(|i| Thm::mp(&i, &out))
        .ok_or_else(|| bad(CODOMAIN))?;
    if *done.concl() != Formula::mem(point, at.goal.clone()) {
        return Err(bad(CODOMAIN))
    }
    Ok(done)
}

/// `⊢ ∀x. (x ∈ A → (IH(x) → φ(x)))` — A3's premise, from the minor binder's own
/// scope typing.
///
/// The walk is [`crate::rec_dep::minor_at`]'s in shape and differs in what the
/// levels are: Lean's minor takes `x`, then a *proof* of `∀y, r y x → Acc α r y`
/// and a *proof* of `∀y hy, C y (h y hy)`, and neither of those is a binder this
/// derivation can open — they are conditional singletons that have to be shown
/// **inhabited**, from the induction hypothesis, by [`preds`].
fn ind_step_at(
    ip: &mut Interp,
    ac: &AccClause,
    at: &At,
    graph: &Term,
    m_mem: &Thm,
    zv: FreeVar,
    phi: &Formula,
) -> Option<Thm> {
    let point = ip.point();
    let up = ac.sets.sets.up;
    let a = at.xs[0].clone();
    let acc_t = ac.sets.of(a.clone(), graph.clone());

    let mut scopes = Scopes::new();
    let tok_x = scopes.open(&mut ip.env, a.clone());
    let (x, x_mem) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };

    // The induction hypothesis, spelled as `derived::acc::ind_step` spells it.
    let yv = ip.env.fresh_var();
    let y = Term::var(yv);
    let ih_formula = Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(y.clone(), a.clone()),
            Formula::imp(
                Formula::mem(derived::opair(up, y.clone(), x.clone()), graph.clone()),
                Formula::and(Formula::mem(y, acc_t), phi.subst(zv, &Term::var(yv))),
            ),
        ),
    );
    let (tok_ih, ih) = scopes.assume(ih_formula);

    // ── Lean's minor, applied at `x` and then at the two proofs ─────────────
    let m_set = m_mem.concl().as_mem()?.1;
    let (s1, d1) = prop_pi(ip, &m_set)?;
    if d1 != a {
        return None
    }
    let at_x = ip.cond_app(&s1, &a, m_mem, &x, &x_mem)?;

    let h_set = at_x.concl().as_mem()?.1;
    let (s2, hset) = prop_pi(ip, &h_set)?;
    let h_mem = preds(ip, ac, Want::Accessible, &hset, at, &x, &x_mem, Src::Ih(&ih), &mut scopes)?;
    let at_h = ip.cond_app(&s2, &hset, &at_x, &point, &h_mem)?;

    let i_set = at_h.concl().as_mem()?.1;
    let (s3, iset) = prop_pi(ip, &i_set)?;
    let i_mem = preds(ip, ac, Want::Motive, &iset, at, &x, &x_mem, Src::Ih(&ih), &mut scopes)?;
    let at_i = ip.cond_app(&s3, &iset, &at_h, &point, &i_mem)?;

    // `⟦C x (Acc.intro α r x h)⟧` is `app(app(⟦C⟧,x),•)`, because the
    // constructor applied at a `Prop` denotes `•` — §6.2's application clause,
    // and the check that says so rather than assuming it.
    if *at_i.concl() != phi.subst(zv, &x) {
        return None
    }

    let body = scopes.discharge_assumption(tok_ih, &at_i);
    let closed = scopes.close(tok_x);
    closed.discharge(&body).ok()
}

/// Where `y ∈ acc(A,R̄)` comes from at a predecessor `y` of `x`.
///
/// The two sources are the two positions this walk is run from, and they are
/// **not** interchangeable: an induction has a hypothesis and a use site has
/// only A4.
#[derive(Clone, Copy)]
pub(crate) enum Src<'a> {
    /// `ind_step`'s induction hypothesis,
    /// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ → (y ∈ acc(A,R̄) ∧ φ(y))))` — the only source
    /// that also carries [`Want::Motive`]'s right conjunct.
    Ih(&'a Thm),
    /// **A4** ([`derived::acc::acc_pred_closed`]) at an `x` already known
    /// accessible: a predecessor of an accessible point is accessible. Carries
    /// nothing about the motive, so [`Want::Motive`] declines against it rather
    /// than producing a theorem about the wrong formula.
    Pred { rule: &'a Thm, x_in_acc: &'a Thm },
}

/// Which of the two conditional singletons Lean's minor asks for.
#[derive(Clone, Copy)]
pub(crate) enum Want {
    /// `∀ y, r y x → Acc α r y` — every predecessor is accessible.
    Accessible,
    /// `∀ y (hy : r y x), C y (h y hy)` — the motive holds at every
    /// predecessor.
    Motive,
}

/// `Γ ⊢ • ∈ set`, where `set` is one of Lean's two predecessor hypotheses.
///
/// Both are `⟦∀ y:α, r y x → …⟧`: two conditional-singleton levels over the
/// same two domains, differing only in the body. The `y` level is a binder and
/// the `r y x` level is a proof binder whose variable is moved onto `•` by
/// proof irrelevance — which is what puts the induction hypothesis's own
/// antecedent, Lean's curried `r y x`, in hand.
///
/// **The caller's own [`Scopes`] is threaded rather than a fresh one opened.**
/// Every theorem here carries the `x` binder's hypothesis and the assumed
/// induction hypothesis as well as its own two, and the LIFO order of the four
/// is what makes `gen_checked` succeed at each close: `y` and the proof binder
/// are discharged before the induction hypothesis, which is discharged before
/// `x`. A second stack would lose that ordering silently.
#[allow(clippy::too_many_arguments)]
pub(crate) fn preds(
    ip: &mut Interp,
    ac: &AccClause,
    want: Want,
    set: &Term,
    at: &At,
    x: &Term,
    x_mem: &Thm,
    src: Src<'_>,
    sc: &mut Scopes,
) -> Option<Thm> {
    let point = ip.point();
    let sums = ip.prelude.tower.sums.clone();
    let (a, r) = (at.xs[0].clone(), at.xs[1].clone());
    let (a_mem, r_mem) = (at.mems[0].clone(), at.mems[1].clone());

    let (l1, d1) = prop_pi(ip, set)?;
    if d1 != a {
        return None
    }
    let tok_y = sc.open(&mut ip.env, a.clone());
    let (yv, y, y_mem) = {
        let s = sc.get(0)?;
        (s.var(), s.term(), s.assumption().clone())
    };

    // `⟦r y x → …⟧`, this level's body at `y`.
    let (skel, holes) = (l1.skel.clone(), l1.holes.clone());
    let inner = ip.rebuild(&skel, &holes, &y);
    let (l2, rel) = prop_pi(ip, &inner)?;

    let tok_w = sc.open(&mut ip.env, rel.clone());
    let (wv, w_mem) = {
        let s = sc.get(0)?;
        (s.var(), s.assumption().clone())
    };

    // `• ∈ ⟦r y x⟧` — the proof variable, moved onto `•`. Its type has to be
    // placed in `⟦Prop⟧` first, which is `⟦r⟧`'s own dependent product applied
    // twice and is the only place this clause reads `⟦r⟧`'s typing.
    let rel_in_u0 = rel_typing(ip, &r, &r_mem, &y, &y_mem, x, x_mem, &rel)?;
    let w_pt = ip.point_of_proof(&rel_in_u0, &w_mem)?;
    let pt_eq_w = derived::eq_symm(&mut ip.env, &w_pt)?;
    let pt_in_rel = ip.retarget_subject(&w_mem, &pt_eq_w)?;

    // `⟨y,x⟩ ∈ R̄` — hold Lean's curried `r`, owe the pair. See the header.
    let pig = derived::inst_all(
        &ac.pair_in_graph,
        &[a.clone(), r.clone(), y.clone(), x.clone()],
    )?;
    let pair = Thm::mp(&pig, &derived::and_intro(&y_mem, &derived::and_intro(x_mem, &pt_in_rel)))?;

    // …which is what the induction hypothesis, or A4, is waiting for.
    let (y_in_acc, motive) = match src {
        Src::Ih(ih) => {
            let at_y = derived::inst_all(ih, std::slice::from_ref(&y))?;
            let conj = Thm::mp(&Thm::mp(&at_y, &y_mem)?, &pair)?;
            (derived::and_elim_left(&conj)?, Some(derived::and_elim_right(&conj)?))
        }
        Src::Pred { rule, x_in_acc } => {
            let graph = Term::apply(ac.graph, vec![a.clone(), r.clone()]);
            let a4 = derived::inst_all(rule, &[a.clone(), graph, y.clone(), x.clone()])?;
            let over = Thm::mp(&a4, x_in_acc)?;
            (Thm::mp(&over, &derived::and_intro(&y_mem, &pair))?, None)
        }
    };

    let body = match want {
        Want::Motive => motive?,
        Want::Accessible => {
            let args = [a.clone(), r.clone(), y.clone()];
            let chi_y = derived::inst_all(&ac.acc_set_ax, &args)?;
            let phi_y = ac.phi(&a, &r, &y);
            let set_y = ip.mk(ac.acc_set, args.to_vec());
            let intro = cond_intro(&sums, &phi_y, &set_y, &chi_y)?;
            let pt = Thm::mp(&intro, &y_in_acc)?;
            // `⟦Acc α r y⟧` is a redex over the stored nest, not the
            // conditional singleton the clause denotes with — one `beta_spine`,
            // read backwards.
            let (_, beta) =
                ip.beta_spine(&at.former, &args, &[a_mem, r_mem, y_mem.clone()])?;
            let back = derived::eq_symm(&mut ip.env, &beta)?;
            ip.retarget_set(&pt, &back)?
        }
    };

    // Up the two levels, each closed by the `Prop` clause's own λ rule.
    let body = ip.to_cond_fibre(&l2, wv, &body)?;
    let closed_w = sc.close(tok_w);
    let fam_w = closed_w.discharge(&body).ok()?;
    let level = ip.cond_lam_typing(&l2, rel, &fam_w)?;
    let level = ip.to_cond_fibre(&l1, yv, &level)?;
    let closed_y = sc.close(tok_y);
    let fam_y = closed_y.discharge(&level).ok()?;
    let out = ip.cond_lam_typing(&l1, a, &fam_y)?;
    (*out.concl() == Formula::mem(point, set.clone())).then_some(out)
}

/// `⟦Π⟧` taken apart, insisting on §6.2's `Prop` clause.
pub(crate) fn prop_pi(ip: &Interp, t: &Term) -> Option<(crate::interp::CondSite, Term)> {
    match ip.as_pi(t)? {
        PiShape::Prop { site, dom } => Some((site, dom)),
        PiShape::Dep { .. } => None,
    }
}

/// `Γ ⊢ ⟦r y x⟧ ∈ ⟦Prop⟧`, from `⟦r⟧`'s own scope typing.
///
/// `r : α → α → Prop` is `Sort 1`-valued, so both of its levels are §6.2's
/// dependent product at a constant fibre and the rule is [`Interp::dprod_app`]
/// twice. The result is compared against the domain the interpretation named,
/// so a `r` of some other shape is a decline rather than a wrong typing.
#[allow(clippy::too_many_arguments)]
pub(crate) fn rel_typing(
    ip: &mut Interp,
    r: &Term,
    r_mem: &Thm,
    y: &Term,
    y_mem: &Thm,
    x: &Term,
    x_mem: &Thm,
    rel: &Term,
) -> Option<Thm> {
    let r_set = r_mem.concl().as_mem()?.1;
    let (s1, d1) = match ip.as_pi(&r_set)? {
        PiShape::Dep { site, dom } => (site, dom),
        PiShape::Prop { .. } => return None,
    };
    let at_y = ip.dprod_app(&s1, &d1, r, y, r_mem, y_mem)?;
    let (ry, ry_set) = {
        let (s, t) = at_y.concl().as_mem()?;
        (s.clone(), t.clone())
    };
    let (s2, d2) = match ip.as_pi(&ry_set)? {
        PiShape::Dep { site, dom } => (site, dom),
        PiShape::Prop { .. } => return None,
    };
    let out = ip.dprod_app(&s2, &d2, &ry, x, &at_y, x_mem)?;
    (*out.concl() == Formula::mem(rel.clone(), ip.sort(0))).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{konst, Level};
    use crate::interp::Interp;
    use std::rc::Rc;

    fn level(n: u32) -> Level {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = l.succ();
        }
        l
    }

    /// **`⟦Acc.rec.{0,u}⟧` is interpreted with its typing.**
    ///
    /// The declaration is `crate::direct`'s own synthetic `Acc` — the one the
    /// exports declare — and `Acc.rec` is **generated** by
    /// [`crate::kernel::add`] exactly as it is on the corpus, so this reads the
    /// same recursor type `117_accRecType` does rather than an imitation.
    ///
    /// Non-vacuity: a `Prop`-valued motive makes the whole eliminator a proof,
    /// so the term is `•` — asserting a λ-nest here would pin the wrong clause —
    /// and the typing has to be about that term and about the recursor's own
    /// Lean type, not merely about something.
    #[test]
    fn the_prop_motive_eliminator_is_interpreted_with_its_typing() {
        let (env, _, _) = crate::direct::tests::acc_env(false);
        let rec = Name::str(&Name::simple("Acc"), "rec");
        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(0), level(0)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer ⟦Acc.rec⟧");
        let tm = t.tm.clone().unwrap_or_else(|| panic!("no interpretation: {:?}", t.ev));
        let m = t.ev.thm().unwrap_or_else(|| panic!("no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        assert_eq!(
            Some(&tm),
            c.interp().map(|ip| ip.point()).as_ref(),
            "a Prop-valued motive makes Acc.rec a proof, which denotes •"
        );
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about ⟦Acc.rec⟧ itself");
        let want = c.infer_type(&t.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…in ⟦∀ α r C m a t. C a t⟧");
    }

    /// **`⟦Acc.rec.{1,u}⟧` is interpreted with its typing** — the other half of
    /// the row, and a *value* rather than a proof.
    ///
    /// The corner walk this test is one cell of: the differing input against
    /// the test above is the motive's own sort, one build, two cells. It was a
    /// **frontier** test asserting [`VALUE`] until `crate::rec_acc_value`
    /// landed, and the property it pins is the one that flipped: at `u₁ ≥ 1`
    /// the eliminator is `derived::rec_acc`'s `pack` applied to the point and
    /// its accessibility proof, so the term is emphatically *not* `•` — which
    /// is what an assertion about "something" would not have caught.
    #[test]
    fn the_value_motive_eliminator_is_interpreted_with_its_typing() {
        let (env, _, _) = crate::direct::tests::acc_env(false);
        let rec = Name::str(&Name::simple("Acc"), "rec");
        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1), level(0)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer ⟦Acc.rec⟧");
        let tm = t.tm.clone().unwrap_or_else(|| panic!("no interpretation: {:?}", t.ev));
        let m = t.ev.thm().unwrap_or_else(|| panic!("no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        assert_ne!(
            Some(&tm),
            c.interp().map(|ip| ip.point()).as_ref(),
            "a value-motive eliminator is a function, not a proof"
        );
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about ⟦Acc.rec⟧ itself");
        let want = c.infer_type(&t.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…in ⟦∀ α r C m a t. C a t⟧");
    }

    /// **The name is not the evidence, at the eliminator.** The same synthetic
    /// declaration with the step hypothesis stated about `r x y` is the
    /// accessibility predicate of the *converse* relation. Its recursor's type
    /// is a well-formed six-binder `Π` of the right arity at the right sorts, so
    /// neither the shape check nor the codomain comparison can see it; what
    /// refuses is the transport, where `pair_in_graph` is handed
    /// `• ∈ app(app(⟦r⟧,x),y)` and owes `⟨y,x⟩ ∈ R̄`.
    #[test]
    fn a_declaration_named_acc_with_the_relation_reversed_has_no_eliminator() {
        let (env, a, _) = crate::direct::tests::acc_env(true);
        let rec = Name::str(&Name::simple("Acc"), "rec");
        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(0), level(0)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer ⟦Acc.rec⟧");
        assert_eq!(
            t.ev.gap(),
            Some(&Gap::Recursor(a, MINOR, Cause::Threading)),
            "the reversed relation must be declined by the minor's transport"
        );
    }
}
