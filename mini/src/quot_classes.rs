//! **`Quot`'s interpretation clause at `u ≥ 1`** — the equivalence-class
//! reading (`QUOT-MODEL.md` §5's second clause).
//!
//! # Interface
//!
//! ```text
//! quot_classes::QuotClause::build(env, prelude) -> Option<QuotClause>
//! qc.carrier(ip, a, r)                          -> Term      ⟦Quot α r⟧
//! qc.formation(ip, u, a, r, a_mem)              -> Option<Thm>
//! quot_classes::mk_at(qc, ip, former, …)        -> Option<(Term, Thm)>
//! quot_classes::ind_at(qc, ip, former, mk_former, …) -> Option<Thm>
//! quot_classes::lift_at(qc, ip, former, eq_former, …) -> Option<(Term, Thm)>
//! Interp::quotient()                            -> Option<Rc<QuotClause>>
//! ```
//!
//! The clauses are dispatched from [`crate::quot::build`], which owns the
//! `u = 0` / `u ≥ 1` split. What lives here is the **apparatus** — the symbols
//! and theorems the bottoms consume — and the two clauses built so far.
//!
//! # The clauses
//!
//! ```text
//! ⟦Quot α r⟧          = quot(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧))
//! ⟦Quot.mk α r a⟧     = class(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧), ⟦a⟧)
//! ⟦Quot.ind α r β h q⟧ = •      (at every u; the *typing* is what changes)
//! ⟦Quot.lift α r β f h⟧ = lift(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧), ⟦f⟧)
//! ```
//!
//! — Carneiro §6.2, `⟦α/R⟧ = ⟦α⟧/∼`, with the same correction the thesis's
//! notation hides that [`crate::acc`] records one construction along:
//! **`quot` takes a set of pairs and `⟦r⟧` is curried.** Every theorem in
//! [`derived::quot`] reads `⟨x,y⟩ ∈ R`, while Lean's `r : α → α → Prop`
//! interprets as `⟦r⟧ ∈ fs(A, fs(A, U₀))`.
//! [`derived::quot::rel_graph_symbol`] is the bridge, and this is its **second**
//! consumer.
//!
//! **No symbol of mini's own.** `Acc`'s clause needed one because its
//! denotation is a `Prop` and had to be a conditional singleton over a formula;
//! here the denotation is a genuine set and `quot`/`rel_graph` are already
//! arity-2 symbols of `derived`'s. The composite is built through
//! [`Interp::mk`] at both nodes, which is what makes it decomposable again — an
//! unrecorded node is the defect [`Interp::rebuild`]'s doc is about.
//!
//! # Why the apparatus is lazy, and why there are two `rel_graph`s
//!
//! [`derived::quot::Quotient::over`] derives the equivalence closure, the
//! classes, `lift`'s graph, `ker` and the four non-vacuity witnesses from the
//! axioms up. An export that mentions no quotient must not pay for it, so it is
//! built on **its own** first use and cached on the `Interp` — the same
//! lazy-with-a-failure-flag shape [`Interp::direct`], [`Interp::acc`] and
//! `ind_apparatus` all have, and for the same identity reason: `⟦Quot.{1}⟧` and
//! `⟦Quot.{2}⟧` must name one `quot`, or their definitional equality would need
//! a theorem where reflexivity should do.
//!
//! `Quotient::over` mints its **own** `rel_graph`, and [`crate::acc`] has
//! already minted one. That is a re-minted symbol, which this project's standing
//! rule (`MINI-HANDOFF.md` §2) calls a defect *whenever two routes have to agree
//! about it* — and these two do not. `⟦Acc α r x⟧` is a conditional singleton
//! over `acc(A, rel_graph_acc(A,r))` and `⟦Quot α r⟧` is
//! `quot(A, rel_graph_quot(A,r))`; they are different sets, no theorem crosses
//! between them, and nothing anywhere compares an accessibility carrier with a
//! quotient. What the two **must** share is the pairing — `⟨x,y⟩` has to be one
//! term or the two graphs' members would be unrelated statements — and they do,
//! because both are built over `prelude.tower.sums`. That is asserted rather
//! than argued: `the_two_graphs_share_one_pairing`.
//!
//! The alternative — one `rel_graph` lifted onto the `Interp` and handed to
//! both — is the right move if a third consumer ever appears. It is not worth
//! it for two that never compare notes, and it would cost an `Acc`-only export
//! the whole `Quotient`, which is exactly what the laziness is for.
//!
//! # What is here and what is not
//!
//! **All four**, with two exceptions inside the family. `Quot.lift` at
//! `v = 0` is a different clause (`QUOT-MODEL.md` §6 finding 2) and declines;
//! and `Quot.lift`'s **computation rule** is not here at all — it is
//! `whnf`'s, over `lift_beta`, and `124_quotLiftReduction` names it as
//! `iota(Quot.lift)` on the threading axis. `Quot.sound`'s inhabitation is
//! `MINI-HANDOFF.md` §14's point 3 and lives in [`crate::axiom`] — where at
//! `u ≥ 1` it is **not** reflexivity, because `⟦mk a⟧` and `⟦mk b⟧` are two
//! different classes rather than two `•`s, and the rule it wants is
//! [`derived::quot::q_sound`]. The apparatus carries what the three owe —
//! `q_sound`, `lift_beta`, `lift_in_funspace`, `compat_closure`,
//! `pair_in_graph` — because they must all speak of **one** `quot`, and minting
//! at each site would give three.
//!
//! **`pair_in_graph` is the bridge with no consumer yet**, and this module is
//! where it acquires one: `q_sound` wants `⟨ā,b̄⟩ ∈ R̄` while Lean's `h` arrives
//! as `• ∈ app(app(r̄,ā),b̄)`, which is *owing* the pair rather than holding it.
//! That is the prediction `mini/src/acc.rs`'s field doc makes, and `Quot.sound`
//! at `u ≥ 1` is where it gets tested.

use std::rc::Rc;

use kernel::{Env, Formula, Term, Thm};

use derived::prelude::Prelude;
use derived::quot::{quot_in_universe, Quotient};

use crate::interp::{Interp, PiShape};
use crate::scope::Scopes;

/// The `Quot` clause's symbols and the theorems its bottoms consume.
///
/// Built over **the prelude's own** [`derived::sums::Sums`], so that the
/// `⟨x,y⟩` this module's `rel_graph` speaks of is the ordered pair every other
/// construction uses and its `𝒫` is the one the tower's rungs are closed under.
pub struct QuotClause {
    /// Every symbol and theorem of [`derived::quot`], over one definitional
    /// extension.
    pub q: Quotient,
    /// `⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))` — **formation**, at every
    /// rung `c ≥ 1`.
    ///
    /// Built here rather than carried by [`Quotient`] because it needs the
    /// tower's two `∀c` closure statements, which are not quotient apparatus.
    pub in_universe: Thm,
}

impl QuotClause {
    /// Introduce the quotient apparatus and derive the formation theorem.
    ///
    /// Returns `None` rather than half a clause if either declines —
    /// `Quotient::over` refuses a conditional [`derived::sums::Sums`], and
    /// `quot_in_universe` refuses a `pow`/`sub` pair that is not this tower's.
    pub fn build(env: &mut Env, prelude: &Prelude) -> Option<QuotClause> {
        let q = Quotient::over(env, prelude.tower.sums.clone())?;
        let in_universe = quot_in_universe(
            env,
            &q.sums,
            q.class,
            q.quot,
            &q.quot_ax,
            prelude.u_sym,
            &prelude.tower.pow,
            &prelude.tower.sub,
        )?;
        Some(QuotClause { q, in_universe })
    }

    /// `rel_graph(A, r)` — Lean's curried `r` as the set of pairs `quot` wants.
    pub fn graph(&self, ip: &mut Interp, a: &Term, r: &Term) -> Term {
        ip.mk(self.q.rel_graph, vec![a.clone(), r.clone()])
    }

    /// `⟦Quot α r⟧ = quot(A, rel_graph(A,r))`, recorded at both nodes.
    pub fn carrier(&self, ip: &mut Interp, a: &Term, r: &Term) -> Term {
        let g = self.graph(ip, a, r);
        ip.mk(self.q.quot, vec![a.clone(), g])
    }

    /// **`Γ ⊢ ⟦Quot α r⟧ ∈ ⟦Sort u⟧`** at `u ≥ 1`, from `Γ ⊢ ⟦α⟧ ∈ ⟦Sort u⟧`.
    ///
    /// One instantiation of [`QuotClause::in_universe`] and one modus ponens.
    /// The rung is what makes `u ≥ 1` load-bearing rather than decorative:
    /// `⟦Sort u⟧` is `U(seed)` for a *seed term the tower names*, and
    /// `in_universe` is stated at `U(c)` for a variable `c` — so the two meet
    /// exactly when there is a rung, which is `u ≥ 1`. At `u = 0` there is no
    /// rung (`Tower::at(0) = None`) and the statement is not merely unavailable
    /// but false: `quot(1,R) = {1} ∉ U₀`, `QUOT-MODEL.md` §1.2's countermodel.
    ///
    /// The conclusion is compared against the term [`QuotClause::carrier`]
    /// builds, so a caller cannot get a membership about a different set.
    pub fn formation(
        &self,
        ip: &mut Interp,
        u: u32,
        a: &Term,
        r: &Term,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let rung = ip.prelude.tower.at(u as usize)?;
        let carrier = self.carrier(ip, a, r);
        let g = self.graph(ip, a, r);
        if *a_mem.concl() != Formula::mem(a.clone(), rung.set.clone()) {
            return None
        }
        let at = derived::inst_all(&self.in_universe, &[a.clone(), g, rung.seed.clone()])?;
        let out = Thm::mp(&at, a_mem)?;
        (*out.concl() == Formula::mem(carrier, rung.set)).then_some(out)
    }
}

/// **`Γ ⊢ class(A,R̄,ā) ∈ ⟦Quot α r⟧`** — `Quot.mk`'s typing at `u ≥ 1`.
///
/// # The clause
///
/// ```text
/// ⟦Quot.mk α r a⟧ = class(⟦α⟧, rel_graph(⟦α⟧,⟦r⟧), ⟦a⟧)
/// ```
///
/// — Carneiro §6.2's `⟦mk_R x⟧ = [⟦x⟧]∼`. The rule is
/// [`derived::quot::Quotient::mk_mem`], `⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈
/// quot(A,R))`, and its one premise is the `a` binder's own scope typing.
///
/// # The one step that is not the rule
///
/// The declared codomain is `Quot α r`, and §6.2's application clause makes
/// that `app(app(⟦Quot.{u}⟧,A),r̄)` — a **redex over the formation clause's own
/// stored nest**, related to `quot(A,R̄)` by β and not by syntax. So `mk_mem`
/// lands in `quot(A,R̄)` and the codomain is one [`Interp::beta_spine`] away, in
/// the *opposite* direction from the usual: the membership is carried **onto**
/// the spine rather than off it, so the equation is reversed before it is used.
///
/// That is `SCOPING.md` §1's sixth category, and it is the same β step
/// [`crate::quot`]'s `Prim::Mk` needs at `u = 0` for the same reason — where
/// `⟦Quot α r⟧` is a redex onto `⟦α⟧` instead of onto `quot(A,R̄)`. The two
/// clauses disagree about everything except this.
///
/// `None` is a decline: the conclusion is compared against the codomain's own
/// interpretation, so a constant called `Quot.mk` that does not land in its own
/// quotient produces no theorem rather than a wrong one.
pub fn mk_at(
    qc: &QuotClause,
    ip: &mut Interp,
    former: &Term,
    a: &Term,
    a_mem: &Thm,
    r: &Term,
    r_mem: &Thm,
    x: &Term,
    x_mem: &Thm,
    cod_tm: &Term,
) -> Option<(Term, Thm)> {
    let graph = qc.graph(ip, a, r);
    let term = ip.mk(qc.q.class, vec![a.clone(), graph.clone(), x.clone()]);
    let rule = derived::inst_all(&qc.q.mk_mem, &[a.clone(), graph, x.clone()])?;
    let mem = Thm::mp(&rule, x_mem)?;

    // `⊢ ⟦Quot α r⟧ = quot(A,R̄)`, reversed: the membership is in `quot(A,R̄)`
    // and the codomain is the spine.
    let (bot, beta) = ip.beta_spine(former, &[a.clone(), r.clone()], &[a_mem.clone(), r_mem.clone()])?;
    if beta.concl().as_eq()?.0 != *cod_tm {
        return None
    }
    let back = derived::eq_symm(&mut ip.env, &beta)?;
    if *mem.concl() != Formula::mem(term.clone(), bot) {
        return None
    }
    let out = ip.retarget_set(&mem, &back)?;
    (*out.concl() == Formula::mem(term.clone(), cod_tm.clone())).then_some((term, out))
}

/// **`Γ ⊢ • ∈ ⟦β q⟧`** — `Quot.ind`'s typing at `u ≥ 1`.
///
/// # The clause and the obligation
///
/// `⟦Quot.ind α r β h q⟧ = •` at **every** `u`: the motive is hardwired
/// `→ Prop`, so the eliminator is a proof and §6.2 gives it `•` whatever the
/// carrier is. What changes at `u ≥ 1` is the *typing*, and
/// `QUOT-MODEL.md` §6 finding 5 is the one obligation its findings 1–4 do not
/// cover — `Quot.ind` falls between both splits, having no `v` to branch on and
/// a major premise ranging over a genuine `quot(A,R̄)`.
///
/// At `u = 0` (`crate::quot`'s `Prim::Ind`) `⟦Quot α r⟧` **is** `⟦α⟧`, so the
/// major `q` is its own witness and `h` applies at it directly. Here it is not:
/// `h` speaks only of classes, and `q` is an arbitrary member of the quotient.
///
/// # The route, and it is `quot_cases` and nothing cleverer
///
/// ```text
/// q ∈ quot(A,R̄)                              one β step off the formation nest
/// ∃x. (x ∈ A ∧ q = class(A,R̄,x))             quot_cases — no junk
/// •  ∈ app(β̄, class(A,R̄,x))                  h at a fresh x ∈ A, then one β step
/// •  ∈ app(β̄, q)                             Leibniz along the equation
/// ```
///
/// **Two β steps, at two different nests**, and both are `SCOPING.md` §1's
/// sixth category: `⟦Quot α r⟧` is a redex over `⟦Quot.{u}⟧`'s stored nest, and
/// the `⟦Quot.mk α r x⟧` inside `h`'s own fibre is a redex over `⟦Quot.mk.{u}⟧`'s.
/// The second sits under `β̄`'s application, so it needs one `congr_arg` in
/// `app`'s second slot before the membership can move — which is the same
/// second step the note calls free.
///
/// # Why the existential is eliminated by hand
///
/// [`derived::exists_elim`] wants `∀x. (φ(x) → ψ)` with `φ` the existential's
/// own body, and `Closed::discharge` produces `∀x. (x ∈ A → (q = class → ψ))`
/// — the curried form. `inst_self` opens it back at `x`, `curry` conjoins the
/// two antecedents, and `gen_all` closes it again. Three library calls, no
/// formula surgery, and no second `assume`: the scope discipline is what
/// supplies the `x ∈ A` the whole derivation runs under.
#[allow(clippy::too_many_arguments)]
pub fn ind_at(
    qc: &QuotClause,
    ip: &mut Interp,
    former: &Term,
    mk_former: &Term,
    a: &Term,
    a_mem: &Thm,
    r: &Term,
    r_mem: &Thm,
    beta: &Term,
    h_mem: &Thm,
    q: &Term,
    q_mem: &Thm,
    cod_tm: &Term,
) -> Option<Thm> {
    let point = ip.point();
    let app_sym = ip.prelude.ap.app;
    let graph = qc.graph(ip, a, r);
    let psi = Formula::mem(point.clone(), cod_tm.clone());

    // `q ∈ quot(A,R̄)`, then no junk.
    let (_, beta_eq) =
        ip.beta_spine(former, &[a.clone(), r.clone()], &[a_mem.clone(), r_mem.clone()])?;
    let q_in_quot = ip.retarget_set(q_mem, &beta_eq)?;
    let cases = derived::inst_all(&qc.q.quot_cases, &[a.clone(), graph, q.clone()])?;
    let ex = Thm::mp(&cases, &q_in_quot)?;

    // ── at a fresh member of `A` ────────────────────────────────────────────
    let mut scopes = Scopes::new();
    let tok = scopes.open(&mut ip.env, a.clone());
    let (xv, x, x_mem) = {
        let sc = scopes.get(0)?;
        (sc.var(), sc.term(), sc.assumption().clone())
    };

    // `h` at `x`, whose fibre mentions `⟦Quot.mk α r x⟧` — a redex.
    let h_set = h_mem.concl().as_mem()?.1;
    let PiShape::Prop { site, dom } = ip.as_pi(&h_set)? else { return None };
    if dom != *a {
        return None
    }
    let at_x = ip.cond_app(&site, a, h_mem, &x, &x_mem)?;
    let (klass, mk_beta) = ip.beta_spine(
        mk_former,
        &[a.clone(), r.clone(), x.clone()],
        &[a_mem.clone(), r_mem.clone(), x_mem],
    )?;
    // …and the redex reduced *inside* `β̄`'s application.
    let set = at_x.concl().as_mem()?.1;
    let (sym, args) = ip.parts_of(&set)?;
    if sym != app_sym || args.len() != 2 || args[0] != *beta {
        return None
    }
    let move_eq = derived::congr_arg(&mut ip.env, app_sym, &args, 1, &mk_beta)?;
    let at_class = ip.retarget_set(&at_x, &move_eq)?;

    // `q = class(A,R̄,x) → • ∈ app(β̄,q)`, under `x ∈ A`.
    let hole = ip.env.fresh_var();
    let phi_hole = Formula::mem(point, ip.app(beta.clone(), Term::var(hole)));
    let leib = Thm::eq_leibniz(klass.clone(), q.clone(), hole, phi_hole);
    let symm = derived::eq_symm_imp(&mut ip.env, q.clone(), klass);
    let chain = derived::syl(&symm, &leib)?;
    let step = derived::mpd_const(&chain, &at_class)?;

    // ── discharge, re-shape, eliminate ──────────────────────────────────────
    let fam = scopes.close(tok).discharge(&step).ok()?;
    let body = derived::inst_self(xv, &fam)?;
    let all_imp = crate::rec_dep::gen_all_checked(&[xv], &derived::curry(&body)?)?;
    let out = derived::exists_elim(xv, &ex, &all_imp, &psi)?;
    (*out.concl() == psi).then_some(out)
}


/// **`Γ ⊢ lift(A,R̄,f̄) ∈ ⟦Quot α r → β⟧`** — `Quot.lift`'s typing at
/// `u ≥ 1, v ≥ 1`.
///
/// # The clause
///
/// ```text
/// ⟦Quot.lift α r β f h⟧ = lift(⟦α⟧, rel_graph(⟦α⟧,⟦r⟧), ⟦f⟧)
/// ```
///
/// — the nest stops at `f` and its codomain is the **arrow** `Quot α r → β`,
/// for the reason [`crate::quot::Prim::depth`] gives at `u = 0`: a six-deep
/// nest is this one η-expanded and is not the clause.
///
/// # Three pieces, and the middle one is the seam
///
/// 1. **`rcompat` out of Lean's `h`** — [`rcompat_at`], a three-level `cond_app`
///    walk with `graph_pair` at the relation and one β step at `⟦Eq⟧`'s nest.
///    `compat_closure` turns it into the `compat(A,R,f)` both `lift_beta` and
///    `lift_in_funspace` carry.
/// 2. **`fs` against `dprod`**, below.
/// 3. `lift_in_funspace`, and one congruence back onto the codomain's spine.
///
/// # The `fs`/`dprod` seam, and why it is the design rather than a defect
///
/// `lift_in_funspace` is stated over **`fs`**, and *no interpreted `Π` in mini
/// is ever an `fs`*: the `Fs` variant of [`crate::interp::PiShape`] was removed
/// when the `fs` clause retired, and `Interp::fs`/`fs_app`/`fs_typing` have no
/// callers. `fs` was nevertheless **kept in `derived/`**, deliberately, and this
/// is the first place that costs anything: a library theorem stated over `fs`
/// reaches an interpreted `Π` through a bridge rather than by coincidence.
///
/// The bridge is [`derived::ext::dprod_const_fibre_n`] —
/// `⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))` — and it
/// is wanted **twice**: at `⟦α⟧` to put `f̄` into `fs(A,B)`, and at
/// `quot(A,R̄)` to bring `lift` back out into a `dprod`. **Two uses is the
/// honest price of one spelling**, and every future library theorem stated over
/// `fs` will meet the same two.
///
/// Its hypothesis costs nothing here, which is worth stating because it is a
/// *simplification nobody had exercised*: the fibre of `⟦α → β⟧` is constant —
/// `β` is a binder, so the body mentions no `x` — and the fibre symbol's own
/// defining axiom already says `b(h⃗,x) = ⟦β⟧` at every `x`. So the family is
/// [`Interp::symbol_at`] plus `a1i` plus one `gen`, with no scope and no
/// pointwise derivation.
///
/// # `v = 0` is a different clause and is declined
///
/// At `v = 0` the whole of `lift β f h` is a proof, `⟦Quot α r → β⟧` is a
/// conditional singleton rather than a `dprod`, and there is no `f ∈ fs(A,B)`
/// certificate to feed `lift_in_funspace` at all — `QUOT-MODEL.md` §6 finding 2,
/// whose route is per-element through `quot_cases` and is *not* this one.
/// [`Interp::as_pi`] answers `Prop` there and this returns `None`, which is a
/// decline with the caller's reason. The corpus schedules `Quot.lift` at
/// `(0,0)` and `(1,1)` only, so the branch is unreached today and is refused
/// rather than guessed at.
#[allow(clippy::too_many_arguments)]
pub fn lift_at(
    qc: &QuotClause,
    ip: &mut Interp,
    former: &Term,
    eq_former: &Term,
    a: &Term,
    a_mem: &Thm,
    r: &Term,
    r_mem: &Thm,
    b_ty: &Term,
    b_mem: &Thm,
    f: &Term,
    f_mem: &Thm,
    h_mem: &Thm,
    cod_tm: &Term,
) -> Option<(Term, Thm)> {
    let p = ip.prelude.clone();
    let graph = qc.graph(ip, a, r);
    let term = ip.mk(qc.q.lift, vec![a.clone(), graph.clone(), f.clone()]);

    // ── piece 2: the bridge, and `f̄ ∈ fs(A,B)` ──────────────────────────────
    let f_set = f_mem.concl().as_mem()?.1;
    let PiShape::Dep { site, dom } = ip.as_pi(&f_set)? else { return None };
    if dom != *a {
        return None
    }
    let bridge = derived::ext::dprod_const_fibre_n(
        &mut ip.env,
        &p.ap,
        &p.fs,
        site.b,
        site.dp.img,
        &site.dp.img_ax,
        site.dp.dprod,
        &site.dp.dprod_def,
        &p.fs_app_mem,
        &p.fs_retarget,
    )?;
    // The fibre is constant, so its own defining axiom is the whole hypothesis.
    let xv = ip.env.fresh_var();
    let const_eq = ip.symbol_at(site.b, &site.b_ax, &site.holes, &Term::var(xv))?;
    if const_eq.concl().as_eq()?.1 != *b_ty {
        return None
    }
    let quot_t = ip.mk(qc.q.quot, vec![a.clone(), graph.clone()]);
    let at_dom = |ip: &mut Interp, d: &Term| -> Option<Thm> {
        let mut args = site.holes.clone();
        args.push(d.clone());
        args.push(b_ty.clone());
        let rule = derived::inst_all(&bridge, &args)?;
        let fam = crate::rec_dep::gen_all_checked(
            &[xv],
            &derived::a1i(&const_eq, Formula::mem(Term::var(xv), d.clone())),
        )?;
        let _ = ip;
        Thm::mp(&rule, &fam)
    };
    let dp_eq_a = at_dom(ip, a)?;
    let f_in_fs = ip.retarget_set(f_mem, &dp_eq_a)?;

    // ── piece 1: Lean's `h`, as `compat` ────────────────────────────────────
    let rc = rcompat_at(qc, ip, &site, eq_former, a, r, b_ty, b_mem, f, f_mem, h_mem)?;
    let cc = derived::inst_all(
        &qc.q.compat_closure,
        &[a.clone(), graph.clone(), f.clone()],
    )?;
    let compat = Thm::mp(&cc, &rc)?;

    // ── piece 3: the typing rule, and back onto the codomain's spine ────────
    let rule = derived::inst_all(
        &qc.q.lift_in_funspace,
        &[a.clone(), graph.clone(), b_ty.clone(), f.clone()],
    )?;
    let lift_mem = Thm::mp(&rule, &derived::and_intro(&f_in_fs, &compat))?;

    let dp_eq_q = at_dom(ip, &quot_t)?;
    let back = derived::eq_symm(&mut ip.env, &dp_eq_q)?;
    let in_dp = ip.retarget_set(&lift_mem, &back)?;

    // `⟦Quot α r⟧` is a redex over the formation nest, and it sits in the
    // `dprod` symbol's **last** argument — §2.1's domain-slot property, which is
    // what makes this one congruence rather than a rebuild.
    let (_, beta_eq) =
        ip.beta_spine(former, &[a.clone(), r.clone()], &[a_mem.clone(), r_mem.clone()])?;
    let onto = derived::eq_symm(&mut ip.env, &beta_eq)?;
    let mut dargs = site.holes.clone();
    dargs.push(quot_t);
    let last = dargs.len().checked_sub(1)?;
    let move_eq = derived::congr_arg(&mut ip.env, site.dp.dprod, &dargs, last, &onto)?;
    let out = ip.retarget_set(&in_dp, &move_eq)?;
    (*out.concl() == Formula::mem(term.clone(), cod_tm.clone())).then_some((term, out))
}

/// **`Γ ⊢ rcompat(A, R̄, f̄)`** from `Quot.lift`'s `h` binder's own scope typing.
///
/// `rcompat` is `∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R̄)) → app(f̄,x) = app(f̄,y))`
/// and `h` is `∀ a b, r a b → f a = f b`, a three-level conditional singleton.
/// The walk is [`intro_mem`]'s at one more arity, and the three transports are
/// the same three:
///
/// * the **quantifier** — two fresh scopes and two discharges, and the
///   conjoined shape `rcompat` wants is `inst_self` + `curry` at each level,
///   because `Closed::discharge` produces the curried one;
/// * the **curried relation** — `⟨x,y⟩ ∈ R̄` is an *antecedent* here too, so it
///   is [`derived::quot::graph_pair`] composed with `syl`, not `pair_in_graph`;
/// * one **β step**, at a third nest: `⟦Eq β (f a) (f b)⟧` is a redex over
///   `⟦Eq.{v}⟧`'s stored nest, and only after it reduces to `eq_set(f̄x, f̄y)`
///   does `cond_elim` yield the equation. Its two argument typings come from
///   `dprod_app` at the constant fibre.
#[allow(clippy::too_many_arguments)]
fn rcompat_at(
    qc: &QuotClause,
    ip: &mut Interp,
    site: &crate::interp::FibreSite,
    eq_former: &Term,
    a: &Term,
    r: &Term,
    b_ty: &Term,
    b_mem: &Thm,
    f: &Term,
    f_mem: &Thm,
    h_mem: &Thm,
) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();
    let point = ip.point();
    let d = ip.direct()?;

    let mut scopes = Scopes::new();
    let tok_x = scopes.open(&mut ip.env, a.clone());
    let (xv, x, x_mem) = {
        let sc = scopes.get(0)?;
        (sc.var(), sc.term(), sc.assumption().clone())
    };
    let h_set = h_mem.concl().as_mem()?.1;
    let PiShape::Prop { site: s1, dom: d1 } = ip.as_pi(&h_set)? else { return None };
    if d1 != *a {
        return None
    }
    let at_x = ip.cond_app(&s1, a, h_mem, &x, &x_mem)?;

    let tok_y = scopes.open(&mut ip.env, a.clone());
    let (yv, y, y_mem) = {
        let sc = scopes.get(0)?;
        (sc.var(), sc.term(), sc.assumption().clone())
    };
    let set2 = at_x.concl().as_mem()?.1;
    let PiShape::Prop { site: s2, dom: d2 } = ip.as_pi(&set2)? else { return None };
    if d2 != *a {
        return None
    }
    let at_y = ip.cond_app(&s2, a, &at_x, &y, &y_mem)?;

    // The relation's own proof is a scope, as it is in `Acc.intro`: what is held
    // is the pair membership, and `graph_pair` is the direction that owes `r`.
    let set3 = at_y.concl().as_mem()?.1;
    let PiShape::Prop { site: s3, dom: rel } = ip.as_pi(&set3)? else { return None };
    let tok_w = scopes.open(&mut ip.env, rel.clone());
    let (w, w_mem) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let at_w = ip.cond_app(&s3, &rel, &at_y, &w, &w_mem)?;

    // `⟦Eq β (f x) (f y)⟧` is a redex; `eq_set(f̄x, f̄y)` is what `cond_elim` is
    // about. The two argument typings are `f̄`'s own application rule.
    let fx = ip.app(f.clone(), x.clone());
    let fy = ip.app(f.clone(), y.clone());
    let fx_mem = ip.dprod_app(site, a, f, &x, f_mem, &x_mem)?;
    let fy_mem = ip.dprod_app(site, a, f, &y, f_mem, &y_mem)?;
    let (eq_bot, eq_beta) = ip.beta_spine(
        eq_former,
        &[b_ty.clone(), fx.clone(), fy.clone()],
        &[b_mem.clone(), fx_mem, fy_mem],
    )?;
    let at_eq = ip.retarget_set(&at_w, &eq_beta)?;
    let phi = Formula::eq(fx, fy);
    let chi = derived::inst_all(&d.eq_ax, &eq_bot_args(&eq_bot, ip)?)?;
    let elim = derived::prop::cond_elim(&sums, &phi, &eq_bot, &chi)?;
    let the_eq = Thm::mp(&elim, &at_eq)?;

    // ── discharge outwards, conjoining at each level ────────────────────────
    let over_w = scopes.close(tok_w).discharge(&the_eq).ok()?;
    let from_rel = derived::inst_all(&over_w, std::slice::from_ref(&point))?;
    let gp = derived::inst_all(&qc.q.graph_pair, &[a.clone(), r.clone(), x, y])?;
    let step = derived::syl(&gp, &from_rel)?;

    let fam_y = scopes.close(tok_y).discharge(&step).ok()?;
    let body_y = derived::curry(&derived::inst_self(yv, &fam_y)?)?;
    let fam_x = scopes.close(tok_x).discharge(&body_y).ok()?;
    let body_x = derived::curry(&derived::inst_self(xv, &fam_x)?)?;
    crate::rec_dep::gen_all_checked(&[xv, yv], &body_x)
}

/// `eq_set`'s two arguments, read off the term the β chain landed on.
///
/// Rebuilding them from `f̄x`/`f̄y` would be the same terms; reading them back is
/// what refuses a nest whose bottom is some *other* conditional singleton.
fn eq_bot_args(t: &Term, ip: &Interp) -> Option<Vec<Term>> {
    let (_, args) = ip.parts_of(t)?;
    (args.len() == 2).then_some(args)
}

impl Interp {
    /// The `Quot` clause's apparatus at `u ≥ 1`, over **this** `Interp`'s own
    /// pairing and power set, built on first use and then shared.
    ///
    /// Identity, not memoisation: two uses of `Quot` at two `σ` must name one
    /// `quot`, and `Quot.mk`'s and `Quot.lift`'s clauses are further builds over
    /// the carrier the formation clause was stored at.
    pub fn quotient(&mut self) -> Option<Rc<QuotClause>> {
        if self.quotient.is_none() && !self.quotient_failed {
            let p = self.prelude.clone();
            self.quotient = QuotClause::build(&mut self.env, &p).map(Rc::new);
            self.quotient_failed = self.quotient.is_none();
        }
        self.quotient.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The apparatus builds, and the two theorems the formation clause rests on
    /// are **unconditional** — a `Γ`-carrying one would ride into a nest bottom
    /// this module's caller documents as closed.
    #[test]
    fn the_apparatus_builds_and_formation_is_unconditional() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("the Quot apparatus builds over the prelude");
        assert!(q.in_universe.hyps().is_empty(), "formation is unconditional");
        assert!(q.q.quot_ax.hyps().is_empty(), "quot's defining axiom is unconditional");
        assert!(q.q.rel_graph_ax.hyps().is_empty(), "rel_graph's axiom is unconditional");
    }

    /// **One `quot`, not one per call.** Two clause builds at two `σ` must name
    /// the same symbol or their definitional equality would need a theorem; the
    /// cache is what makes that true, so it is what is pinned.
    #[test]
    fn the_apparatus_is_identity_not_a_cache() {
        let mut ip = Interp::new();
        let first = ip.quotient().expect("builds");
        let second = ip.quotient().expect("builds");
        assert_eq!(first.q.quot, second.q.quot, "two uses of Quot must name one quot");
        assert_eq!(first.q.rel_graph, second.q.rel_graph, "…and one rel_graph");
        assert_eq!(first.q.class, second.q.class, "…and one class");
    }

    /// **The two `rel_graph`s share the pairing.** The header argues that
    /// minting a second `rel_graph` beside [`crate::acc`]'s is safe *because*
    /// `⟨x,y⟩` is one term in both; that is a property of two lazily-built
    /// objects and prose does not recompile, so it is asserted.
    #[test]
    fn the_two_graphs_share_one_pairing() {
        let mut ip = Interp::new();
        let (x, y) = (ip.env.fresh_var(), ip.env.fresh_var());
        let mine = ip.quotient().expect("builds").q.sums.ap.sets.clone();
        let theirs = ip.acc().expect("builds").sets.sets.clone();
        assert_eq!(
            mine.pair(Term::var(x), Term::var(y)),
            theirs.pair(Term::var(x), Term::var(y)),
            "the Quot clause's rel_graph and the Acc clause's must speak of one ordered pair"
        );
    }

    /// **Formation, at the rung the interpretation actually uses.** `⟦Sort 1⟧`
    /// is `U(ω)` and not `U(⟦Sort 0⟧)`, so this is the one step where the
    /// tower's seeding could have made a `∀c` theorem fail to instantiate.
    #[test]
    fn formation_lands_in_the_rung_the_interpretation_names() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("builds");
        for u in [1u32, 2] {
            let rung = ip.prelude.tower.at(u as usize).expect("a rung");
            let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
            let (a, r) = (Term::var(av), Term::var(rv));
            // The premise the checker would hold: `⟦α⟧ ∈ ⟦Sort u⟧`.
            let a_mem = crate::scope::test_support::assume(Formula::mem(a.clone(), rung.set.clone()));
            let out = q.formation(&mut ip, u, &a, &r, &a_mem).expect("formation applies");
            let carrier = q.carrier(&mut ip, &a, &r);
            assert_eq!(*out.concl(), Formula::mem(carrier, ip.sort(u)));
        }
    }

    /// **`u = 0` has no rung and the clause must not answer there.** The
    /// identity reading is `crate::quot`'s and the two are refutably different
    /// sets (`QUOT-MODEL.md` §1.2), so a formation theorem at `Sort 0` would be
    /// a wrong one rather than a missing one.
    #[test]
    fn formation_declines_at_sort_zero() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("builds");
        let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
        let (a, r) = (Term::var(av), Term::var(rv));
        let a_mem = crate::scope::test_support::assume(Formula::mem(a.clone(), ip.sort(0)));
        assert!(q.formation(&mut ip, 0, &a, &r, &a_mem).is_none(), "there is no rung 0");
    }
}
