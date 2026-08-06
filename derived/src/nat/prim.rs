//! **Primitive recursion with a parameter**, as a reusable construction.
//!
//! # Interface
//!
//! [`prim_rec`] takes two term-formers — a base `c(x)` and a step `g(x, a)` —
//! and returns a binary symbol `f` with
//!
//! ```text
//! ⊢ ∀x. f(x, 0) = c(x)                                     [PrimRec::at_zero]
//! ⊢ ∀x ∀n. (n ∈ ω → f(x, succ n) = g(x, f(x,n)))           [PrimRec::at_succ]
//! ```
//!
//! # Why it has to be built rather than taken
//!
//! [`crate::recursion::recursion`] fixes the step as a **unary function
//! symbol** of the ambient extension, chosen when the symbol is minted. A step
//! that mentions a parameter — `a ↦ add(a, x)` for multiplication, `a ↦ mul(a,x)`
//! for exponentiation — is not such a symbol and cannot be made into one:
//! `define_abbrev` would give a *binary* symbol, and there is no way to feed the
//! extra argument through a rule whose step is applied as `G(app(f,n))`.
//!
//! The parameter moves into the **state** instead. Iterate on the pair
//! `⟨x, a⟩` with the one fixed unary symbol `q ↦ ⟨p1 q, g(p1 q, p2 q)⟩`, and
//! read the answer off the second component. One induction —
//! [`PrimRec::invariant`] — says the state really is `⟨x, f(x,n)⟩` at every
//! `n ∈ ω`, and both equations fall out of it.
//!
//! This is the same device [`crate::nat::apparatus`] uses for `natrec`, one
//! nesting level shallower: there the *step itself* is data and has to ride in
//! the state too, so the state is a triple. `natrec` predates this file and is
//! not written in terms of it; the two are independent and the duplication is
//! one `invariant` induction, which is cheaper than a shared abstraction
//! general enough to cover both.
//!
//! # What it does not give
//!
//! Nothing about `f` off `ω`, and no typing: `f(x,n)` is a term for every `x`
//! and `n`, and whether it lands in `ω` is the caller's induction to do — one
//! per operation, because it depends on `c` and `g`.

use kernel::{Env, FnSym, FreeVar, Formula, Term, Thm};

use crate::recursion::theorem::recursion;
use crate::{define_abbrev, eq_symm, gen_all, inst_all};

use super::apparatus::Nat;
use super::glue::{congr1, congr_tmpl, induct, induct_step, Chain};

/// A primitive recursion `f(x,n)` with its two equations.
pub struct PrimRec {
    /// The symbol `f(x,n)`.
    pub sym: FnSym,
    /// `⊢ ∀x ∀n. f(x,n) = p2(app(it(x), n))`.
    pub def: Thm,
    /// `⊢ ∀x. f(x, 0) = c(x)`.
    pub at_zero: Thm,
    /// `⊢ ∀x ∀n. (n ∈ ω → f(x, succ n) = g(x, f(x,n)))`.
    pub at_succ: Thm,
    /// `⊢ ∀x ∀n. (n ∈ ω → app(it(x), n) = ⟨x, f(x,n)⟩)`.
    pub invariant: Thm,
}

impl PrimRec {
    /// The term `f(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.sym, vec![a, b]) }
}

/// Build `f` with `f(x,0) = c(x)` and `f(x, succ n) = g(x, f(x,n))`.
///
/// `c` and `g` are term-formers: `c(x)` may mention `x` and nothing else free,
/// and `g(x,a)` may mention `x` and `a` and nothing else free. A term-former
/// that closes over some other free variable makes the definition unsound and
/// `define_abbrev` refuses it, which surfaces here as `None`.
pub fn prim_rec<C, G>(env: &mut Env, nat: &Nat, c: C, g: G) -> Option<PrimRec>
where
    C: Fn(&Term) -> Term,
    G: Fn(&Term, &Term) -> Term,
{
    let (p1, p2) = (nat.p1, nat.p2);
    let p1_of = |t: Term| Term::apply(p1, vec![t]);
    let p2_of = |t: Term| Term::apply(p2, vec![t]);

    // ── the fixed unary step, and what it does at a genuine pair ─────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let body = nat.pair(p1_of(tq.clone()), g(&p1_of(tq.clone()), &p2_of(tq.clone())));
    let (step, step_ax) = define_abbrev(env, &[qv], &body)?;

    let (pv, av) = (env.fresh_var(), env.fresh_var());
    let (tp, ta) = (Term::var(pv), Term::var(av));
    let pair = nat.pair(tp.clone(), ta.clone());
    let get_p = inst_all(&nat.p1_pair, &[tp.clone(), ta.clone()])?;
    let get_a = inst_all(&nat.p2_pair, &[tp.clone(), ta.clone()])?;
    let hole = env.fresh_var();
    let th = Term::var(hole);
    let q_p = p1_of(pair.clone());
    let step_pair = {
        let unfold = inst_all(&step_ax, std::slice::from_ref(&pair))?;
        let t1 = nat.pair(q_p.clone(), g(&q_p, &th));
        let t2 = nat.pair(th.clone(), g(&th, &ta));
        let out = Chain::from(unfold)
            .then(congr_tmpl(env, hole, &t1, &get_a)?)
            .then(congr_tmpl(env, hole, &t2, &get_p)?)
            .done(env)?;
        debug_assert_eq!(
            *out.concl(),
            Formula::eq(Term::apply(step, vec![pair]), nat.pair(tp.clone(), g(&tp, &ta))),
            "prim_rec: the step at a pair has the wrong shape"
        );
        gen_all(&[pv, av], &out)
    };

    // ── the iteration, and the symbol read off its second component ─────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let seed = nat.pair(tx.clone(), c(&tx));
    let it = recursion(env, &nat.rec, step, &seed, &[xv])?;
    let iter_at = |n: &Term| nat.apply(Term::apply(it.iter, vec![tx.clone()]), n.clone());

    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let (sym, def) = define_abbrev(env, &[xv, nv], &p2_of(iter_at(&tn)))?;
    let f_of = |n: &Term| Term::apply(sym, vec![tx.clone(), n.clone()]);

    // `f(x,0) = p2(⟨x, c(x)⟩) = c(x)`.
    let zero = nat.zero();
    let at_zero = {
        let unfold = inst_all(&def, &[tx.clone(), zero.clone()])?;
        let base = congr1(env, p2, &it.base)?;
        let strip = inst_all(&nat.p2_pair, &[tx.clone(), c(&tx)])?;
        gen_all(&[xv], &Chain::from(unfold).then(base).then(strip).done(env)?)
    };

    // ── the state really is `⟨x, f(x,n)⟩` ────────────────────────────────────
    let want = |n: &Term| Formula::eq(iter_at(n), nat.pair(tx.clone(), f_of(n)));
    let phi = want(&tn);
    let base = {
        let iz = eq_symm(env, &inst_all(&at_zero, std::slice::from_ref(&tx))?)?;
        let refold = congr_tmpl(env, hole, &nat.pair(tx.clone(), th.clone()), &iz)?;
        Chain::from(it.base.clone()).then(refold).done(env)?
    };
    debug_assert_eq!(*base.concl(), want(&zero), "prim_rec: the induction base has the wrong shape");

    let advance = |env: &mut Env, state: &Thm, n_om: &Thm| -> Option<(Thm, Term)> {
        let stepped = Thm::mp(&inst_all(&it.step, std::slice::from_ref(&tn))?, n_om)?;
        let folded = congr1(env, step, state)?;
        let value = g(&tx, &f_of(&tn));
        let at = inst_all(&step_pair, &[tx.clone(), f_of(&tn)])?;
        let reached = Chain::from(stepped).then(folded).then(at).done(env)?;
        Some((reached, value))
    };
    let value_off = |env: &mut Env, n: &Term, w: &Term, state: &Thm| -> Option<Thm> {
        let unfold = inst_all(&def, &[tx.clone(), n.clone()])?;
        let lifted = congr1(env, p2, state)?;
        let strip = inst_all(&nat.p2_pair, &[tx.clone(), w.clone()])?;
        Chain::from(unfold).then(lifted).then(strip).done(env)
    };

    let ind_step = induct_step(nat.core(), nv, &phi, |n_om, ih| {
        let (reached, value) = advance(env, ih, n_om)?;
        let succ_n = nat.succ_of(tn.clone());
        let got = value_off(env, &succ_n, &value, &reached)?;
        let back = eq_symm(env, &got)?;
        let refold = congr_tmpl(env, hole, &nat.pair(tx.clone(), th.clone()), &back)?;
        let out = Chain::from(reached).then(refold).done(env)?;
        debug_assert_eq!(*out.concl(), want(&succ_n), "prim_rec: the step has the wrong shape");
        Some(out)
    })?;
    let all_n = induct(env, nat.core(), nv, &phi, &base, &ind_step)?;
    let invariant = gen_all(&[xv], &all_n);

    // ── the successor equation ───────────────────────────────────────────────
    let n_om = nat.in_omega(tn.clone());
    let assumed = Thm::assume(n_om.clone());
    let state = Thm::mp(&inst_all(&all_n, std::slice::from_ref(&tn))?, &assumed)?;
    let (reached, value) = advance(env, &state, &assumed)?;
    let succ_n = nat.succ_of(tn.clone());
    let got = value_off(env, &succ_n, &value, &reached)?;
    let at_succ = gen_all(&[xv, nv], &Thm::implies_intr(&n_om, &got));

    Some(PrimRec { sym, def, at_zero, at_succ, invariant })
}

/// The variables `prim_rec` quantifies its results over, for a caller that
/// needs to rebuild the exact shape.
pub fn free_pair(env: &mut Env) -> (FreeVar, FreeVar) { (env.fresh_var(), env.fresh_var()) }
