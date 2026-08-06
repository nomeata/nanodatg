//! **`ω` as a type of natural numbers**: zero, the successor, the recursor, and
//! the recursor's two ι rules.
//!
//! # Interface
//!
//! [`Nat::new`] builds one chain of definitional extensions and hands back a
//! [`Nat`]. Writing `0` for `∅`, `succ` for `n ∪ {n}`, `ω` for the least
//! inductive set and `natrec(c,g,n)` for the new symbol:
//!
//! ```text
//! ⊢ 0 ∈ ω                                                     [Nat::zero_mem]
//! ⊢ ∀n. (n ∈ ω → succ(n) ∈ ω)                                 [Nat::succ_mem]
//! ⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))                              [Nat::succ_ne_zero]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ m = succ n → m = n))      [Nat::succ_inj]
//! ⊢ ω ∈ U₁                                                    [Nat::omega_mem]
//!
//! ⊢ ∀c ∀g. natrec(c,g,0) = c                                  [Nat::iota_zero]
//! ⊢ ∀c ∀g ∀n. (n ∈ ω →
//!        natrec(c,g,succ n) = app(app(g,n), natrec(c,g,n)))   [Nat::iota_succ]
//! ```
//!
//! plus induction, which the caller gets as the scheme
//! [`crate::recursion::induction_scheme`] over [`Nat::core`].
//!
//! # This is `ω`, and nothing here knows what `Nat` is
//!
//! The carrier is the *concrete* least inductive set — von Neumann's, `0 := ∅`
//! and `succ n := n ∪ {n}` — built once by [`crate::recursion`] and shared. It
//! is not a parameter and not an abstract structure: an earlier plan for this
//! module took `(N, z, s, r)` as data and quantified everything over it, which
//! buys generality nobody needs and pays for it with a non-vacuity obligation
//! that only a concrete instance can discharge anyway.
//!
//! Nothing here mentions Lean, `Nat`, or any syntax. What a checker does with
//! `ω` — hardcoding it as the interpretation of some declaration — is the
//! checker's business, and no theorem below changes if it does something else.
//!
//! # Why the recursor is built by iteration on a triple
//!
//! [`crate::recursion::recursion`] already gives recursion along `ω`, but its
//! step is a **unary function symbol** `G` fixed when the symbol is minted:
//! `app(f, succ n) = G(app(f,n))`. A recursor in the shape a checker needs has
//! its step supplied as a *set* and lets the step see the index:
//! `natrec(c,g,succ n) = app(app(g,n), natrec(c,g,n))`. Neither the set `g` nor
//! the index `n` can be reached from a fixed unary symbol.
//!
//! The gap closes by moving both into the *state*. Iterate on the triple
//! `⟨g, ⟨n, v⟩⟩` with the one fixed unary symbol
//!
//! ```text
//! nstep(q) := ⟨p1 q, ⟨succ(p1(p2 q)), app(app(p1 q, p1(p2 q)), p2(p2 q))⟩⟩
//! ```
//!
//! which is exactly `⟨g, ⟨n,v⟩⟩ ↦ ⟨g, ⟨succ n, app(app(g,n), v)⟩⟩` when its
//! argument is such a triple ([`Nat::nstep_triple`]), and read the answer back
//! off the last component. One induction — [`Nat::invariant`] — says the state
//! really is that triple at every `n ∈ ω`, and both ι rules fall out of it.
//! That is one induction for the whole recursor, and it is the only thing this
//! file proves that [`crate::recursion`] did not.
//!
//! `π₁`/`π₂` come from [`crate::proj::Proj`] and are wrapped in unary symbols
//! here, because they are otherwise `⋃⋂p` and `app({p}, ⋃⋂p)` — correct, but
//! terms that would multiply the size of every state below.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::point_fun::PointFun;
use crate::proj::Proj;
use crate::recursion::naturals::OmegaCore;
use crate::recursion::peano::Peano;
use crate::recursion::rec::Rec;
use crate::recursion::theorem::recursion;
use crate::tower::{Rung, Tower};
use crate::{define_abbrev, eq_symm, gen_all, inst_all};

use super::glue::{congr1, congr_tmpl, induct, induct_step, Chain};

/// `ω` with zero, the successor, the recursor and its ι rules.
///
/// Built **once** per development: the construction mints symbols, and two
/// copies in one `Env` would speak of two unrelated `ω`s.
pub struct Nat {
    /// Pairing, `∅`, `app`, `ω`, `succ` and the Peano properties.
    pub rec: Rec,
    /// The universe tower, so that `⊢ ω ∈ U₁` is about *this* `ω`.
    pub tower: Tower,
    /// Rung 1, `U₁`.
    pub u1: Rung,
    /// `π₁`/`π₂` as term-formers.
    pub proj: Proj,
    /// `p1(p)`, the first projection as a unary symbol.
    pub p1: FnSym,
    /// `⊢ ∀a ∀b. p1(⟨a,b⟩) = a`.
    pub p1_pair: Thm,
    /// `p2(p)`, the second projection as a unary symbol.
    pub p2: FnSym,
    /// `⊢ ∀a ∀b. p2(⟨a,b⟩) = b`.
    pub p2_pair: Thm,
    /// `nstep(q)`, the fixed unary step the iteration runs on.
    pub nstep: FnSym,
    /// `⊢ ∀q. nstep(q) = ⟨p1 q, ⟨succ(p1(p2 q)), app(app(p1 q, p1(p2 q)), p2(p2 q))⟩⟩`.
    pub nstep_ax: Thm,
    /// `⊢ ∀g ∀n ∀v. nstep(⟨g,⟨n,v⟩⟩) = ⟨g, ⟨succ n, app(app(g,n), v)⟩⟩`.
    pub nstep_triple: Thm,
    /// The iteration symbol `nit(c,g)`.
    pub nit: FnSym,
    /// `⊢ ∀c ∀g. app(nit(c,g), 0) = ⟨g,⟨0,c⟩⟩`.
    pub nit_base: Thm,
    /// `⊢ ∀c ∀g ∀n. (n ∈ ω → app(nit(c,g), succ n) = nstep(app(nit(c,g), n)))`.
    pub nit_step: Thm,
    /// The recursor symbol `natrec(c,g,n)`.
    pub natrec: FnSym,
    /// `⊢ ∀c ∀g ∀n. natrec(c,g,n) = p2(p2(app(nit(c,g), n)))`.
    pub natrec_ax: Thm,
    /// `⊢ ∀c ∀g ∀n. (n ∈ ω → app(nit(c,g), n) = ⟨g, ⟨n, natrec(c,g,n)⟩⟩)` —
    /// the one induction the recursor costs.
    pub invariant: Thm,
    /// `⊢ ∀c ∀g. natrec(c,g,0) = c` — the ι rule at zero.
    pub iota_zero: Thm,
    /// `⊢ ∀c ∀g ∀n. (n ∈ ω → natrec(c,g,succ n) = app(app(g,n), natrec(c,g,n)))`
    /// — the ι rule at a successor.
    pub iota_succ: Thm,
}

impl Nat {
    /// The term `0`, which is `∅`.
    pub fn zero(&self) -> Term { self.rec.zero() }

    /// The term `ω`.
    pub fn omega(&self) -> Term { self.rec.omega() }

    /// The term `succ(t)`.
    pub fn succ_of(&self, t: Term) -> Term { self.rec.succ_of(t) }

    /// The term `⟨a,b⟩`.
    pub fn pair(&self, a: Term, b: Term) -> Term { self.rec.pair(a, b) }

    /// The term `app(f,a)`.
    pub fn apply(&self, f: Term, a: Term) -> Term { self.rec.apply(f, a) }

    /// The term `natrec(c,g,n)`.
    pub fn natrec_of(&self, c: Term, g: Term, n: Term) -> Term {
        Term::apply(self.natrec, vec![c, g, n])
    }

    /// The formula `t ∈ ω`.
    pub fn in_omega(&self, t: Term) -> Formula { Formula::mem(t, self.omega()) }

    /// The shared `ω` apparatus.
    pub fn core(&self) -> &OmegaCore { self.rec.core() }

    /// `⊢ 0 ∈ ω`.
    pub fn zero_mem(&self) -> &Thm { &self.rec.peano.core.zero_mem }

    /// `⊢ ∀n. (n ∈ ω → succ(n) ∈ ω)`.
    pub fn succ_mem(&self) -> &Thm { &self.rec.peano.core.succ_closed }

    /// `⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))`.
    pub fn succ_ne_zero(&self) -> &Thm { &self.rec.peano.succ_ne_zero }

    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ m = succ n → m = n))`.
    pub fn succ_inj(&self) -> &Thm { &self.rec.peano.succ_inj }

    /// `⊢ ω ∈ U₁` — the carrier is a member of the first universe, so a checker
    /// that hardcodes it has something to put in `Sort 1`.
    pub fn omega_mem(&self) -> &Thm { &self.u1.omega_mem }

    /// `⊢ succ(t) ∈ ω` from `⊢ t ∈ ω`.
    pub fn succ_mem_at(&self, t: &Thm) -> Option<Thm> {
        let (x, _) = t.concl().as_mem()?;
        Thm::mp(&inst_all(self.succ_mem(), std::slice::from_ref(&x))?, t)
    }

    /// Build the whole apparatus, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Nat> {
        let tower = Tower::new(env)?;
        let u1 = tower.at(1)?;
        let ap: Apply = tower.sums.ap.clone();
        let app_pair = crate::ext::app_of_pair(env, &ap)?;
        let pf = PointFun::over(env, &tower.sums, &app_pair)?;
        let proj = Proj::new(env, &ap, &pf)?;
        let peano: Peano = tower.peano.clone();
        let app_of_graph = crate::recursion::graph::app_of_graph(env, &ap)?;
        let rec = Rec { ap: ap.clone(), peano, app_of_graph };

        // ── `π₁`/`π₂` as unary symbols ───────────────────────────────────────
        let (p1, p1_pair) = projection_symbol(env, &ap, &proj, true)?;
        let (p2, p2_pair) = projection_symbol(env, &ap, &proj, false)?;

        // ── the fixed unary step ─────────────────────────────────────────────
        let qv = env.fresh_var();
        let tq = Term::var(qv);
        let p1_of = |t: Term| Term::apply(p1, vec![t]);
        let p2_of = |t: Term| Term::apply(p2, vec![t]);
        let body = state_of(
            &ap,
            &rec,
            &p1_of(tq.clone()),
            &p1_of(p2_of(tq.clone())),
            &ap.apply(
                ap.apply(p1_of(tq.clone()), p1_of(p2_of(tq.clone()))),
                p2_of(p2_of(tq.clone())),
            ),
            true,
        );
        let (nstep, nstep_ax) = define_abbrev(env, &[qv], &body)?;
        let nstep_triple =
            step_at_a_triple(env, &rec, p1, &p1_pair, p2, &p2_pair, nstep, &nstep_ax)?;

        // ── the iteration ────────────────────────────────────────────────────
        let (cv, gv) = (env.fresh_var(), env.fresh_var());
        let (tc, tg) = (Term::var(cv), Term::var(gv));
        let seed = ap.sets.pair(tg.clone(), ap.sets.pair(rec.zero(), tc.clone()));
        let it = recursion(env, &rec, nstep, &seed, &[cv, gv])?;
        let nit = it.iter;
        let nit_base = gen_all(&[cv, gv], &it.base);
        let nit_step = gen_all(&[cv, gv], &it.step);

        // ── the recursor ─────────────────────────────────────────────────────
        let nv = env.fresh_var();
        let tn = Term::var(nv);
        let state = ap.apply(Term::apply(nit, vec![tc.clone(), tg.clone()]), tn.clone());
        let rec_body = p2_of(p2_of(state));
        let (natrec, natrec_ax) = define_abbrev(env, &[cv, gv, nv], &rec_body)?;

        let dummy = Thm::eq_refl(tn.clone());
        let mut out = Nat {
            rec,
            tower,
            u1,
            proj,
            p1,
            p1_pair,
            p2,
            p2_pair,
            nstep,
            nstep_ax,
            nstep_triple,
            nit,
            nit_base,
            nit_step,
            natrec,
            natrec_ax,
            invariant: dummy.clone(),
            iota_zero: dummy.clone(),
            iota_succ: dummy,
        };
        out.iota_zero = iota_zero(env, &out, cv, gv)?;
        out.invariant = invariant(env, &out, cv, gv, nv)?;
        out.iota_succ = iota_succ(env, &out, cv, gv, nv)?;
        Some(out)
    }

    /// The state term `⟨g, ⟨n, v⟩⟩`, or `⟨g, ⟨succ n, v⟩⟩` when `bump`.
    fn state(&self, g: &Term, n: &Term, v: &Term, bump: bool) -> Term {
        state_of(&self.rec.ap, &self.rec, g, n, v, bump)
    }
}

/// `⟨g, ⟨n, v⟩⟩`, with the index optionally wrapped in one `succ`.
fn state_of(ap: &Apply, rec: &Rec, g: &Term, n: &Term, v: &Term, bump: bool) -> Term {
    let idx = if bump { rec.succ_of(n.clone()) } else { n.clone() };
    ap.sets.pair(g.clone(), ap.sets.pair(idx, v.clone()))
}

/// `π₁` or `π₂` as a unary symbol, with its computation rule at a pair.
fn projection_symbol(
    env: &mut Env,
    ap: &Apply,
    proj: &Proj,
    first: bool,
) -> Option<(FnSym, Thm)> {
    let pv = env.fresh_var();
    let tp = Term::var(pv);
    let body = if first { proj.fst_of(ap, tp.clone()) } else { proj.snd_of(ap, tp) };
    let (sym, ax) = define_abbrev(env, &[pv], &body)?;

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let pair = ap.sets.pair(ta.clone(), tb.clone());
    let unfold = inst_all(&ax, std::slice::from_ref(&pair))?;
    let computes = inst_all(if first { &proj.fst } else { &proj.snd }, &[ta, tb])?;
    let at_pair = Chain::from(unfold).then(computes).done(env)?;
    Some((sym, gen_all(&[av, bv], &at_pair)))
}

/// `⊢ ∀g ∀n ∀v. nstep(⟨g,⟨n,v⟩⟩) = ⟨g, ⟨succ n, app(app(g,n), v)⟩⟩`.
///
/// Three template rewrites: `nstep` is an abbreviation, and at an argument that
/// really is a triple every `p1`/`p2` in it computes away. The order is
/// innermost-value first, so each rewrite sees the term the previous one left.
fn step_at_a_triple(
    env: &mut Env,
    rec: &Rec,
    p1: FnSym,
    p1_pair: &Thm,
    p2: FnSym,
    p2_pair: &Thm,
    nstep: FnSym,
    nstep_ax: &Thm,
) -> Option<Thm> {
    let ap = &rec.ap;
    let (gv, nv, vv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tn, tv) = (Term::var(gv), Term::var(nv), Term::var(vv));
    let inner = ap.sets.pair(tn.clone(), tv.clone());
    let triple = ap.sets.pair(tg.clone(), inner.clone());

    let p1_of = |t: Term| Term::apply(p1, vec![t]);
    let p2_of = |t: Term| Term::apply(p2, vec![t]);

    // The three components, each with its own `⊢ … = …`.
    let get_g = inst_all(p1_pair, &[tg.clone(), inner.clone()])?;
    let get_rest = inst_all(p2_pair, &[tg.clone(), inner])?;
    let get_n = Chain::from(congr1(env, p1, &get_rest)?)
        .then(inst_all(p1_pair, &[tn.clone(), tv.clone()])?)
        .done(env)?;
    let get_v = Chain::from(congr1(env, p2, &get_rest)?)
        .then(inst_all(p2_pair, &[tn.clone(), tv.clone()])?)
        .done(env)?;

    let q_g = p1_of(triple.clone());
    let q_n = p1_of(p2_of(triple.clone()));

    let hole = env.fresh_var();
    let th = Term::var(hole);
    let mk = |g: &Term, n: &Term, v: &Term| {
        state_of(ap, rec, g, n, &ap.apply(ap.apply(g.clone(), n.clone()), v.clone()), true)
    };

    let mut chain = Chain::from(inst_all(nstep_ax, std::slice::from_ref(&triple))?);
    chain = chain.then(congr_tmpl(env, hole, &mk(&q_g, &q_n, &th), &get_v)?);
    chain = chain.then(congr_tmpl(env, hole, &mk(&q_g, &th, &tv), &get_n)?);
    chain = chain.then(congr_tmpl(env, hole, &mk(&th, &tn, &tv), &get_g)?);

    let want = mk(&tg, &tn, &tv);
    let out = chain.done(env)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(Term::apply(nstep, vec![triple]), want),
        "nstep_triple has the wrong shape"
    );
    Some(gen_all(&[gv, nv, vv], &out))
}

/// From `Γ ⊢ app(nit(c,g), n) = ⟨g, ⟨m, w⟩⟩` infer `Γ ⊢ natrec(c,g,n) = w`.
///
/// The components `g`, `m`, `w` are passed rather than recovered: the kernel
/// exposes no way to take a `Term` apart, and a caller that has just *built*
/// the state has them to hand anyway.
fn value_from_state(
    env: &mut Env,
    nat: &Nat,
    c: &Term,
    g: &Term,
    n: &Term,
    m: &Term,
    w: &Term,
    state: &Thm,
) -> Option<Thm> {
    let unfold = inst_all(&nat.natrec_ax, &[c.clone(), g.clone(), n.clone()])?;
    let once = congr1(env, nat.p2, state)?;
    let outer = congr1(env, nat.p2, &once)?;
    let inner_pair = nat.pair(m.clone(), w.clone());
    let strip1 = inst_all(&nat.p2_pair, &[g.clone(), inner_pair])?;
    let strip2 = inst_all(&nat.p2_pair, &[m.clone(), w.clone()])?;
    Some(
        Chain::from(unfold)
            .then(outer)
            .then(congr1(env, nat.p2, &strip1)?)
            .then(strip2)
            .done(env)?,
    )
}

/// `⊢ ∀c ∀g. natrec(c,g,0) = c`.
fn iota_zero(env: &mut Env, nat: &Nat, cv: FreeVar, gv: FreeVar) -> Option<Thm> {
    let (tc, tg) = (Term::var(cv), Term::var(gv));
    let zero = nat.zero();
    let base = inst_all(&nat.nit_base, &[tc.clone(), tg.clone()])?;
    let out = value_from_state(env, nat, &tc, &tg, &zero, &zero, &tc, &base)?;
    Some(gen_all(&[cv, gv], &out))
}

/// One step of the iteration, computed: from a state theorem at `n`, the state
/// theorem at `succ n` together with the value it carries.
fn advance(
    env: &mut Env,
    nat: &Nat,
    c: &Term,
    g: &Term,
    n: &Term,
    state_at_n: &Thm,
    n_in_omega: &Thm,
) -> Option<(Thm, Term)> {
    let r = nat.natrec_of(c.clone(), g.clone(), n.clone());
    let stepped = Thm::mp(
        &inst_all(&nat.nit_step, &[c.clone(), g.clone(), n.clone()])?,
        n_in_omega,
    )?;
    let folded = congr1(env, nat.nstep, state_at_n)?;
    let triple = inst_all(&nat.nstep_triple, &[g.clone(), n.clone(), r.clone()])?;
    let reached = Chain::from(stepped).then(folded).then(triple).done(env)?;
    let value = nat.apply(nat.apply(g.clone(), n.clone()), r);
    Some((reached, value))
}

/// The state really is the triple:
/// `⊢ ∀c ∀g ∀n. (n ∈ ω → app(nit(c,g), n) = ⟨g, ⟨n, natrec(c,g,n)⟩⟩)`.
fn invariant(env: &mut Env, nat: &Nat, cv: FreeVar, gv: FreeVar, nv: FreeVar) -> Option<Thm> {
    let (tc, tg, tn) = (Term::var(cv), Term::var(gv), Term::var(nv));
    let state_term =
        |n: &Term| nat.apply(Term::apply(nat.nit, vec![tc.clone(), tg.clone()]), n.clone());
    let want = |n: &Term| {
        Formula::eq(
            state_term(n),
            nat.state(&tg, n, &nat.natrec_of(tc.clone(), tg.clone(), n.clone()), false),
        )
    };
    let phi = want(&tn);
    let zero = nat.zero();
    let hole = env.fresh_var();
    let th = Term::var(hole);

    // Base: `app(nit,0) = ⟨g,⟨0,c⟩⟩`, then fold `c` back into `natrec(c,g,0)`.
    let base_eq = inst_all(&nat.nit_base, &[tc.clone(), tg.clone()])?;
    let iz = eq_symm(env, &inst_all(&nat.iota_zero, &[tc.clone(), tg.clone()])?)?;
    let refold = congr_tmpl(env, hole, &nat.state(&tg, &zero, &th, false), &iz)?;
    let base = Chain::from(base_eq).then(refold).done(env)?;
    debug_assert_eq!(*base.concl(), want(&zero), "nat: the induction base has the wrong shape");

    let step = induct_step(nat.core(), nv, &phi, |n_om, ih| {
        let (reached, value) = advance(env, nat, &tc, &tg, &tn, ih, n_om)?;
        let succ_n = nat.succ_of(tn.clone());
        let got =
            value_from_state(env, nat, &tc, &tg, &succ_n, &succ_n, &value, &reached)?;
        let back = eq_symm(env, &got)?;
        let refold = congr_tmpl(env, hole, &nat.state(&tg, &succ_n, &th, false), &back)?;
        let out = Chain::from(reached).then(refold).done(env)?;
        debug_assert_eq!(*out.concl(), want(&succ_n), "nat: the induction step has the wrong shape");
        Some(out)
    })?;

    let out = induct(env, nat.core(), nv, &phi, &base, &step)?;
    Some(gen_all(&[cv, gv], &out))
}

/// `⊢ ∀c ∀g ∀n. (n ∈ ω → natrec(c,g,succ n) = app(app(g,n), natrec(c,g,n)))`.
fn iota_succ(env: &mut Env, nat: &Nat, cv: FreeVar, gv: FreeVar, nv: FreeVar) -> Option<Thm> {
    let (tc, tg, tn) = (Term::var(cv), Term::var(gv), Term::var(nv));
    let n_om = nat.in_omega(tn.clone());
    let assumed = Thm::assume(n_om.clone());
    let state =
        Thm::mp(&inst_all(&nat.invariant, &[tc.clone(), tg.clone(), tn.clone()])?, &assumed)?;
    let (reached, value) = advance(env, nat, &tc, &tg, &tn, &state, &assumed)?;
    let succ_n = nat.succ_of(tn.clone());
    let got = value_from_state(env, nat, &tc, &tg, &succ_n, &succ_n, &value, &reached)?;
    Some(gen_all(&[cv, gv, nv], &Thm::implies_intr(&n_om, &got)))
}
