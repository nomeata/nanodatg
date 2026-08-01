//! `⟦·⟧` — the interpretation of mini's `Expr` as a kernel `Term`
//! (MINI-DESIGN.md §7), and the per-`(name, σ)` constant store (§8).
//!
//! # Interface
//!
//! ```text
//! Interp::new()                                  -> Interp
//! ip.sort(n)                                     -> Term          ⟦Sort n⟧
//! ip.sort_typing(n)                              -> Thm           ⊢ ⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧
//! ip.app(f, a)                                   -> Term          ⟦f a⟧, recorded
//! ip.abbrev(&body)                               -> Option<(Term, Thm)>
//! ip.opaque()                                    -> Term
//! ip.get_const(&key) / ip.put_const(key, interp)
//! ip.skeleton(&t, v, &mut holes)                 -> Option<Term>
//! ```
//!
//! **What is reimplemented and what is reused.** `kernel` and `derived` are
//! reused wholesale: everything mini composes with is `Term`/`Thm`-level and
//! knows nothing about Lean syntax. What is written here is only the §6.2
//! *clause dispatch* against mini's own `Expr` — a few hundred lines against a
//! stable original, rather than adopting `ExprPtr`/`TcCtx` and re-importing
//! the arena and the per-declaration re-interning that mini exists to escape.
//! Independent reimplementation also has diagnostic value: where mini and
//! nanoda disagree about a certificate, one of the two dispatches is wrong, and
//! they fail independently.
//!
//! # What state this keeps, and why none of it is a cache
//!
//! The per-skeleton symbol tables and the per-`(name, ground levels)` constant
//! interpretations are **identity**, not memoised recomputation: two
//! occurrences of one lambda body shape must be the *same* symbol, or their
//! definitional equality needs a theorem where reflexivity should do. Mini has
//! no `whnf`/`infer`/`defeq` result memos at all — nanoda's caches, with their
//! hypothesis-import guards, are engineering for a later stage, and mini's role
//! is to show the design correct without them. Everything stored keeps the
//! certificate that produced it beside the result.
//!
//! # Ground levels only
//!
//! Every level reaching this module is a numeral, because the checker runs once
//! per ground instantiation σ (§3). `⟦Sort u⟧` is therefore always exactly one
//! clause, and `PiUndet` — nanoda's "this `Π` is a proposition at `v := 0` and
//! a function space otherwise" — cannot arise. The declaration-shape zone (§9
//! zone A) runs at symbolic levels and simply has no `Interp` at all.

use std::collections::HashMap;
use std::rc::Rc;

use derived::prelude::{fast_forward, prelude, Prelude};
use derived::skeleton::{self, Parts};
use derived::tower::Cumul;
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ev::{Gap, Sealed};
use crate::expr::Name;

/// A constant at one ground instantiation.
pub type ConstKey = (Name, Vec<u32>);

/// What the store holds for `⟦c.{σ}⟧`.
#[derive(Debug, Clone)]
pub struct ConstInterp {
    /// `⟦c.{σ}⟧`.
    pub term: Term,
    /// `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, or why it is missing.
    pub typing: Result<Sealed, Gap>,
    /// For a transparent definition, `⊢ ⟦c.{σ}⟧ = ⟦val[σ]⟧` — the defining
    /// axiom, which is also delta reduction's certificate.
    pub defeq: Option<Sealed>,
}

/// The interpretation's state: one kernel `Env`, the ambient signature, the
/// term registry the skeleton decomposition needs, and the stores.
pub struct Interp {
    pub env: Env,
    pub prelude: Rc<Prelude>,
    /// The applicative structure of every term built through [`Interp::mk`],
    /// which is what makes a term decomposable later. A *hint*, not a
    /// theorem: a wrong entry yields a skeleton that fails to reassemble,
    /// never a bad proof.
    parts: Parts,
    /// The canonical binder slot every skeleton abstracts over.
    x_canon: FreeVar,
    /// The canonical hole variables, by index. They must be the same across
    /// every term this `Interp` decomposes, or two occurrences of one body
    /// shape would produce two unequal skeletons.
    hole_vars: Vec<FreeVar>,
    /// `⊢ Uₘ ⊆ Uₙ` for every `m ≤ n ≤ height`, and the lifting rules over it.
    ///
    /// Built eagerly to [`CUMUL_HEIGHT`]: it is `O(h²)` theorems, `h` is a
    /// small numeral because a closed Lean level evaluates to one before the
    /// interpretation runs, and every `Π` rule needs the two premises raised to
    /// `max(l1, l2)` before it applies.
    cumul: Cumul,
    consts: HashMap<ConstKey, ConstInterp>,
}

/// How far the cumulativity table reaches. A Lean sort above this yields a gap
/// rather than a wrong universe; the tutorial corpus's highest is far below it.
pub const CUMUL_HEIGHT: usize = 8;

impl Default for Interp {
    fn default() -> Self { Interp::new() }
}

impl Interp {
    pub fn new() -> Interp {
        let prelude = prelude();
        let mut env = Env::new();
        // The prelude was proved against a different `Env`. An `Env` is only a
        // pair of counters, so replaying its theorems is sound; all that must
        // be arranged is that this one never re-issues an id the prelude used.
        fast_forward(&mut env, &prelude);
        let x_canon = env.fresh_var();
        let cumul = Cumul::new(&mut env, &prelude.tower, CUMUL_HEIGHT)
            .expect("the cumulativity table is a closed derivation over the prelude's own tower");
        Interp {
            env,
            prelude,
            parts: Parts::new(),
            x_canon,
            hole_vars: Vec::new(),
            cumul,
            consts: HashMap::new(),
        }
    }

    /// `Term::apply`, remembered — the only way to build an applicative term
    /// that may later have to be taken apart.
    pub fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term {
        skeleton::record(&mut self.parts, f, args)
    }

    /// The canonical binder slot.
    pub fn x_canon(&self) -> FreeVar { self.x_canon }

    /// The `i`-th canonical hole variable, allocated on demand.
    pub fn hole_var(&mut self, i: usize) -> FreeVar {
        while self.hole_vars.len() <= i {
            let v = self.env.fresh_var();
            self.hole_vars.push(v);
        }
        self.hole_vars[i]
    }

    /// Split `t` into the part mentioning `v` and its maximal `v`-free
    /// subterms, which are pushed onto `holes` and replaced by canonical hole
    /// variables; `v` itself becomes [`Interp::x_canon`].
    ///
    /// `None` means a subterm mentioning `v` was not built through
    /// [`Interp::mk`] — the interpretation leaked a variable, which must
    /// surface as a gap rather than be papered over.
    pub fn skeleton(&mut self, t: &Term, v: FreeVar, holes: &mut Vec<Term>) -> Option<Term> {
        // Destructured so the `hole_var` callback can borrow `env`/`hole_vars`
        // while `parts` is borrowed mutably beside it.
        let Interp { env, parts, hole_vars, x_canon, .. } = self;
        let mut hv = |i: usize| -> FreeVar {
            while hole_vars.len() <= i {
                let v = env.fresh_var();
                hole_vars.push(v);
            }
            hole_vars[i]
        };
        skeleton::skeleton(parts, *x_canon, &mut hv, t, v, holes)
    }

    // ─────────────────────────────────────────────────── the sort tower ──

    /// `⟦Sort n⟧`. `⟦Sort 0⟧ = U₀ = {0,1}` is `Prop`; `⟦Sort 1⟧ = U(ω)` is
    /// `Type 0`; above that `⟦Sort (n+1)⟧ = U(⟦Sort n⟧)`.
    pub fn sort(&self, n: u32) -> Term { self.prelude.tower.level(n as usize) }

    /// `⊢ ⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧`, the typing of a sort.
    ///
    /// Two cases, and the split is the tower's, not a special case of mini's:
    /// the tower is seeded at `ω` rather than at `U₀`, so `⟦Sort 1⟧` is *not*
    /// `U(⟦Sort 0⟧)` and the generic `⊢ ∀x. x ∈ U(x)` does not carry `n = 0`.
    /// [`Prelude::u0_in_u1`] is the theorem that does.
    pub fn sort_typing(&self, n: u32) -> Option<Thm> {
        if n == 0 {
            return Some(self.prelude.u0_in_u1.clone())
        }
        // `⟦Sort (n+1)⟧ = U(⟦Sort n⟧)` for `n ≥ 1`, so `mem_u` at `⟦Sort n⟧` is
        // exactly the statement wanted.
        let t = self.sort(n);
        let out = derived::inst_all(&self.prelude.mem_u, std::slice::from_ref(&t))?;
        (*out.concl() == Formula::mem(t.clone(), self.sort(n + 1))).then_some(out)
    }

    // ────────────────────────────────────────────────────── application ──

    /// `⟦f a⟧ = app(⟦f⟧, ⟦a⟧)` on the non-proof branch of §6.2.
    pub fn app(&mut self, f: Term, a: Term) -> Term {
        let ap = self.prelude.ap.app;
        self.mk(ap, vec![f, a])
    }

    /// `•`, Carneiro §6.2's interpretation of every *proof*.
    pub fn point(&self) -> Term { self.prelude.point() }

    // ──────────────────────────────────── the non-dependent Π clause ──

    /// `⟦Π (_ : A). B⟧ = fs(⟦A⟧, ⟦B⟧)` when `B` does not mention the binder
    /// and is not a proposition — §6.2's right column at a constant fibre.
    ///
    /// No skeleton and no fibre symbol: the body is closed under the binder, so
    /// the dependent product collapses to the function space and
    /// [`derived::ext::dprod_const_fibre_n`] is not needed to say so — the
    /// interpretation simply *is* `fs`.
    pub fn fs(&mut self, dom: Term, cod: Term) -> Term {
        let fs = self.prelude.fs_sym();
        self.mk(fs, vec![dom, cod])
    }

    /// `⊢ fs(⟦A⟧,⟦B⟧) ∈ ⟦Sort (imax l1 l2)⟧`, from `⊢ ⟦A⟧ ∈ ⟦Sort l1⟧` and
    /// `⊢ ⟦B⟧ ∈ ⟦Sort l2⟧`. Lean's non-dependent `Π` typing rule.
    ///
    /// `imax l1 l2` with `l2 > 0` is `max l1 l2`, so both premises must first
    /// be **raised** to that level — which is what the cumulativity table is
    /// for, and is the step that makes this rule need more than
    /// `Tower::funspace` alone. `l2 = 0` is the `Prop` clause and does not come
    /// here.
    ///
    /// Every intermediate is checked against the statement claimed, so a
    /// mismatched tower or an out-of-range level yields `None` — a gap — and
    /// never a theorem about the wrong universe.
    pub fn fs_typing(&mut self, dom_mem: &Thm, cod_mem: &Thm, l1: u32, l2: u32) -> Option<Thm> {
        if l2 == 0 {
            return None // the `Prop` clause; a different derivation entirely
        }
        let n = l1.max(l2) as usize;
        if n > self.cumul.height {
            return None
        }
        let a = dom_mem.concl().as_mem()?.0.clone();
        let b = cod_mem.concl().as_mem()?.0.clone();
        // Both premises to `U_n`. `raise` re-checks that each really concludes
        // membership in *this* tower's `U_m` before lifting it.
        let a_mem = self.cumul.raise(l1 as usize, n, dom_mem)?;
        let b_mem = self.cumul.raise(l2 as usize, n, cod_mem)?;
        // `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` at the seed
        // of `U_n`, which for `n ≥ 1` is what `Tower::level(n)` is `U(·)` of.
        let seed = self.prelude.tower.seed(n);
        let inst = derived::inst_all(&self.prelude.tower.funspace, &[seed, a.clone(), b.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(&a_mem, &b_mem))?;
        let want = Formula::mem(self.fs(a, b), self.sort(n as u32));
        (*out.concl() == want).then_some(out)
    }

    // ───────────────────────────────────────────────────────── symbols ──

    /// A 0-ary abbreviation: a fresh symbol `c` with `⊢ c = body`.
    ///
    /// A conservative definitional extension. This is how a transparent Lean
    /// definition gets a name of its own, and the returned theorem *is* delta
    /// reduction's certificate for it.
    pub fn abbrev(&mut self, body: &Term) -> Option<(Term, Thm)> {
        let (sym, ax) = derived::define_abbrev(&mut self.env, &[], body)?;
        let t = self.mk(sym, vec![]);
        // The axiom is checked against the statement claimed rather than
        // trusted: a mismatch is a gap, never a described-but-false theorem.
        (*ax.concl() == Formula::eq(t.clone(), body.clone())).then_some((t, ax))
    }

    /// A fresh opaque constant — a pure *signature* extension, with no
    /// defining axiom.
    ///
    /// This is what an axiom, and any constant mini cannot yet interpret, gets.
    /// Extending the signature is conservative on its own; what is *not*
    /// derivable is that the new symbol denotes an inhabitant of anything,
    /// which is why the store's `typing` is a [`Gap`] on this path.
    pub fn opaque(&mut self) -> Term {
        let sym = self.env.declare(0);
        self.mk(sym, vec![])
    }

    // ─────────────────────────────────────────────────── the const store ──

    pub fn get_const(&self, key: &ConstKey) -> Option<&ConstInterp> { self.consts.get(key) }

    pub fn put_const(&mut self, key: ConstKey, c: ConstInterp) { self.consts.insert(key, c); }

    pub fn const_count(&self) -> usize { self.consts.len() }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tower's two typing cases, both pinned against the statement they
    /// are supposed to make. The `n = 0` case is the one a "just use `mem_u`"
    /// implementation gets wrong, because `⟦Sort 1⟧` is `U(ω)` and not
    /// `U(⟦Sort 0⟧)`.
    #[test]
    fn sort_typings_conclude_what_they_claim() {
        let ip = Interp::new();
        for n in 0..4u32 {
            let t = ip.sort_typing(n).unwrap_or_else(|| panic!("no typing for Sort {n}"));
            assert!(t.hyps().is_empty());
            assert_eq!(
                *t.concl(),
                Formula::mem(ip.sort(n), ip.sort(n + 1)),
                "Sort {n}'s typing does not conclude ⟦Sort {n}⟧ ∈ ⟦Sort {}⟧",
                n + 1
            );
        }
        // ⟦Prop⟧ and ⟦Type 0⟧ are distinct, or the tower has collapsed.
        assert_ne!(ip.sort(0), ip.sort(1));
    }

    /// An abbreviation is a definitional extension whose axiom is *the*
    /// equation delta reduction needs.
    #[test]
    fn abbrev_gives_back_its_defining_equation() {
        let mut ip = Interp::new();
        let body = ip.sort(0);
        let (c, ax) = ip.abbrev(&body).expect("abbrev");
        assert!(ax.hyps().is_empty());
        assert_eq!(*ax.concl(), Formula::eq(c.clone(), body.clone()));
        // Distinct calls mint distinct symbols: identity is the store's job,
        // not `abbrev`'s.
        let (c2, _) = ip.abbrev(&body).expect("abbrev");
        assert_ne!(c, c2);
    }

    /// The skeleton decomposition is what makes a lambda body abstractable,
    /// and it only works on terms built through [`Interp::mk`]. Both halves
    /// are pinned: a recorded application decomposes, and the maximal
    /// binder-free subterm comes back as a hole.
    #[test]
    fn skeleton_abstracts_the_binder_and_holes_the_rest() {
        let mut ip = Interp::new();
        let v = ip.env.fresh_var();
        let closed = ip.sort(0);
        // `app(v, ⟦Prop⟧)` — mentions the binder, so it must be recorded.
        let t = ip.app(Term::var(v), closed.clone());
        let mut holes = Vec::new();
        let sk = ip.skeleton(&t, v, &mut holes).expect("skeleton");
        assert_eq!(holes, vec![closed], "the binder-free subterm is the one hole");
        let expect = {
            let x = ip.x_canon();
            let h = ip.hole_var(0);
            ip.app(Term::var(x), Term::var(h))
        };
        assert_eq!(sk, expect, "the skeleton is the term with the binder and hole canonicalised");

        // Two occurrences of one body shape must decompose to the *same*
        // skeleton, or their defeq needs a theorem where reflexivity should do.
        let v2 = ip.env.fresh_var();
        let other = ip.sort(3);
        let t2 = ip.app(Term::var(v2), other.clone());
        let mut holes2 = Vec::new();
        let sk2 = ip.skeleton(&t2, v2, &mut holes2).expect("skeleton");
        assert_eq!(sk, sk2, "one body shape, one skeleton");
        assert_eq!(holes2, vec![other]);
    }

    /// A term that mentions the binder but was never recorded cannot be
    /// decomposed, and that must be visible rather than silently wrong.
    #[test]
    fn skeleton_refuses_an_unrecorded_term() {
        let mut ip = Interp::new();
        let v = ip.env.fresh_var();
        let f = ip.env.declare(1);
        let leaked = Term::apply(f, vec![Term::var(v)]);
        let mut holes = Vec::new();
        assert!(
            ip.skeleton(&leaked, v, &mut holes).is_none(),
            "an unrecorded term mentioning the binder must fail, not be papered over"
        );
    }

    /// **Lean's non-dependent `Π` rule**, end to end and at every level pair
    /// the corpus can present, including the ones needing a cumulativity lift
    /// on one side, on the other, or on neither.
    ///
    /// `⟦Sort l⟧ ∈ ⟦Sort (l+1)⟧` is the premise to hand, so this checks
    /// `fs(⟦Sort l1⟧, ⟦Sort l2⟧) ∈ ⟦Sort (max (l1+1) (l2+1))⟧` — that is, the
    /// function space of two sorts lands where `imax` says it does.
    #[test]
    fn non_dependent_pi_lands_in_the_max_universe() {
        let mut ip = Interp::new();
        for l1 in 0..4u32 {
            for l2 in 0..4u32 {
                let (a, b) = (ip.sort(l1), ip.sort(l2));
                let (ma, mb) = (ip.sort_typing(l1).unwrap(), ip.sort_typing(l2).unwrap());
                // `⟦A⟧ ∈ ⟦Sort (l1+1)⟧` and `⟦B⟧ ∈ ⟦Sort (l2+1)⟧`; the `Π` sits
                // in `Sort (imax (l1+1) (l2+1))`, and `l2+1 > 0` always, so the
                // `imax` is a `max`.
                let n = (l1 + 1).max(l2 + 1);
                let out = ip
                    .fs_typing(&ma, &mb, l1 + 1, l2 + 1)
                    .unwrap_or_else(|| panic!("no Π typing at ({l1},{l2})"));
                assert!(out.hyps().is_empty(), "the Π rule must be unconditional");
                let want = Formula::mem(ip.fs(a, b), ip.sort(n));
                assert_eq!(*out.concl(), want, "wrong universe at ({l1},{l2})");
            }
        }
    }

    /// The `Prop` codomain is a different clause — a conditional singleton, not
    /// a function space — and this rule must refuse it rather than produce a
    /// theorem about the wrong set. Likewise a level past the table.
    #[test]
    fn the_pi_rule_refuses_what_is_not_its_clause() {
        let mut ip = Interp::new();
        let m = ip.sort_typing(1).unwrap();
        assert!(ip.fs_typing(&m, &m, 1, 0).is_none(), "l2 = 0 is the Prop clause");
        assert!(
            ip.fs_typing(&m, &m, 1, CUMUL_HEIGHT as u32 + 1).is_none(),
            "a level past the cumulativity table must gap, not guess"
        );
        // A membership in something that is not this tower's `U_m` is refused
        // by `Cumul::raise` rather than lifted into nonsense.
        let bogus = kernel::Thm::eq_refl(ip.sort(1));
        assert!(ip.fs_typing(&bogus, &m, 1, 2).is_none());
    }

    /// The store is identity, not memoisation: what goes in comes back, with
    /// its certificate.
    #[test]
    fn const_store_round_trips_with_its_certificate() {
        let mut ip = Interp::new();
        let body = ip.sort(1);
        let (c, ax) = ip.abbrev(&body).unwrap();
        let key = (Name::simple("Foo"), vec![0, 1]);
        ip.put_const(
            key.clone(),
            ConstInterp {
                term: c.clone(),
                typing: Err(Gap::Axiom(Name::simple("Foo"))),
                defeq: Some(Sealed::new(ax.clone()).unwrap()),
            },
        );
        let got = ip.get_const(&key).expect("stored");
        assert_eq!(got.term, c);
        assert_eq!(*got.defeq.as_ref().unwrap().thm().concl(), Formula::eq(c, body));
        // A different instantiation is a different key.
        assert!(ip.get_const(&(Name::simple("Foo"), vec![0])).is_none());
    }
}
