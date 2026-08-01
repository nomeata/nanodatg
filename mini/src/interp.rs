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
    /// The graph machinery per lambda body **shape**. Identity, not a cache:
    /// see [`Interp::lam_site`].
    lams: HashMap<Term, LamSite>,
    /// The dependent-product machinery per fibre **shape**.
    fibres: HashMap<Term, FibreSite>,
    /// The conditional-singleton machinery per `Prop`-valued `∀` shape.
    conds: HashMap<Term, CondSite>,
    /// The same three tables keyed the other way, by the symbol each site
    /// *builds* — so that an interpretation handed back can be taken apart
    /// again ([`Interp::as_lam`], [`Interp::as_pi`]).
    ///
    /// This is what lets `whnf` and `assert_def_eq` recover `⟦A⟧` and `⟦B⟧`
    /// from `⟦Π x:A. B⟧` instead of re-interpreting the subterms. Every
    /// interpretation comes from a `Typing` already in hand; taking one apart
    /// is not a second traversal, it is reading the term the traversal built.
    lam_by_sym: HashMap<FnSym, LamSite>,
    fibre_by_sym: HashMap<FnSym, FibreSite>,
    cond_by_sym: HashMap<FnSym, CondSite>,
    /// `⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)`, built on first use.
    prop_sub: Option<Thm>,
    /// The conversion census (MINI-DESIGN.md §0.3).
    pub convs: ConvStats,
}

/// **How many conversions are hypothesis-free** — the measurement §0.3 asked
/// for, taken with [`crate::ev::Sealed::new`] on each `Conv`'s evidence.
///
/// The census named "kernel-hypothesis evidence versus `ExprPtr`-keyed caches"
/// as the one genuine unsettled design decision, and §0.3 reduced it to: *a
/// conversion cache must either key on `Γ` as well as the endpoints, or store
/// `Sealed` entries only.* Which of the two is cheaper is an empirical
/// question about the ratio below, and this is the counter that answers it.
#[derive(Debug, Default, Clone, Copy)]
pub struct ConvStats {
    /// Conversions produced with a certificate.
    pub proved: usize,
    /// …of which `Sealed::new` accepted — no hypotheses, shareable across
    /// declarations.
    pub sealed: usize,
    /// Conversions that reached their reduct with no certificate.
    pub gapped: usize,
}

/// The conditional-singleton machinery for one `Prop`-valued `∀` shape.
#[derive(Clone)]
pub struct CondSite {
    /// The fibre symbol, of arity `k+1`: `b(h⃗, x)`.
    pub b: FnSym,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    pub b_ax: Thm,
    /// The conditional singleton `chi(h⃗, A) = [∀x ∈ A. • ∈ b(h⃗,x)]`.
    pub chi: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀z. (z ∈ chi(h⃗,A) ↔ (z ∈ 1 ∧ φ))`.
    pub chi_ax: Thm,
    /// `φ(h⃗, A) := ∀x. (x ∈ A → • ∈ b(h⃗,x))`, open in `params`.
    pub phi: Formula,
    /// `φ`'s free variables, in `chi`'s argument order: holes, then domain.
    pub params: Vec<FreeVar>,
    /// This *occurrence*'s abstracted binder-free subterms.
    pub holes: Vec<Term>,
    pub k: usize,
}

/// The dependent-product machinery for one fibre shape.
#[derive(Clone)]
pub struct FibreSite {
    /// The fibre symbol, of arity `k+1`: `b(h⃗, x)`.
    pub b: FnSym,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    pub b_ax: Thm,
    /// `img` and `dprod` and everything proved about them.
    pub dp: Rc<derived::ext::DProdN>,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → img(h⃗,A) ∈ U(c))`.
    pub replacement: Thm,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → dprod(h⃗,A) ∈ U(c))` — Lean's `Π` rule.
    pub rule: Thm,
    /// This *occurrence*'s abstracted binder-free subterms.
    pub holes: Vec<Term>,
    pub k: usize,
}

/// The graph machinery for one lambda body shape.
#[derive(Debug, Clone)]
pub struct LamSite {
    /// The body symbol, of arity `k+1`: `t(h⃗, x)`.
    pub t: FnSym,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    pub t_ax: Thm,
    /// The graph symbol, of arity `k+1`: `lam(h⃗, A) = { ⟨x, t(h⃗,x)⟩ : x ∈ A }`.
    pub lam: FnSym,
    /// `derived::funcs::lambda_n`'s characteristic theorem.
    pub lam_ax: Thm,
    /// This *occurrence*'s abstracted binder-free subterms, in traversal
    /// order. Not part of the key: the shape is shared, the holes are not.
    pub holes: Vec<Term>,
    /// `holes.len()` for the occurrence that first built the symbols.
    pub k: usize,
}

/// Which of §6.2's three `Π` clauses an interpretation came from, recovered
/// from the term itself by [`Interp::as_pi`].
///
/// The application rule differs per clause and the three are *different sets*,
/// so this is a decision that has to be read off rather than guessed — which is
/// exactly why the interpretation records its applicative structure.
#[derive(Clone)]
pub enum PiShape {
    /// `fs(⟦A⟧, ⟦B⟧)` — the codomain does not mention the binder.
    Fs { dom: Term, cod: Term },
    /// `dprod(q⃗, ⟦A⟧)` — a genuine dependent product.
    Dep { site: FibreSite, dom: Term },
    /// `chi(h⃗, ⟦A⟧)` — a `Prop`-valued `∀`, a conditional singleton.
    Prop { site: CondSite, dom: Term },
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
            lams: HashMap::new(),
            fibres: HashMap::new(),
            conds: HashMap::new(),
            lam_by_sym: HashMap::new(),
            fibre_by_sym: HashMap::new(),
            cond_by_sym: HashMap::new(),
            prop_sub: None,
            convs: ConvStats::default(),
        }
    }

    /// **Proof irrelevance**: `Γ ⊢ ⟦e⟧ = •` from `Γ ⊢ ⟦T⟧ ∈ U₀` and
    /// `Γ ⊢ ⟦e⟧ ∈ ⟦T⟧`.
    ///
    /// [`derived::anchor::falsity::prop_subsingleton`] states it for every
    /// proposition at once — a member of `{0,1}` is empty or is `1`, and `1`'s
    /// only element is `•` — so nothing about how `T` was built is needed and
    /// there is nothing to look up.
    ///
    /// **This is where §6.5's "addition over mini-lean's control flow" turns
    /// out to be unnecessary**, and the design said it was. §6.5 asked for
    /// `⟦e₂⟧` to be *retargeted into `⟦T₁⟧`* along a conversion of the two
    /// types, which is a strictness delta (§13 risk 2) and an extra recursive
    /// `assert_def_eq` at every proof comparison. It is not needed: each side
    /// reaches `•` from *its own* type independently, and the equation is then
    /// `trans` of one with `symm` of the other. The two types are never
    /// compared.
    pub fn point_of_proof(&mut self, ty_mem: &Thm, e_mem: &Thm) -> Option<Thm> {
        if self.prop_sub.is_none() {
            let p = self.prelude.clone();
            let t = derived::anchor::falsity::prop_subsingleton(&mut self.env, &p.tower.sums)?;
            self.prop_sub = Some(t);
        }
        let rule = self.prop_sub.clone()?;
        let (subj, set) = e_mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        // The two premises must speak of the same `T`, and `T` must be in the
        // tower's own `U₀` — checked, not assumed.
        if *ty_mem.concl() != Formula::mem(set.clone(), self.sort(0)) {
            return None
        }
        let inst = derived::inst_all(&rule, &[set, subj.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(ty_mem, e_mem))?;
        (*out.concl() == Formula::eq(subj, self.point())).then_some(out)
    }

    /// Record one conversion in the §0.3 census.
    pub fn note_conv(&mut self, ev: &crate::ev::Ev) {
        match ev {
            crate::ev::Ev::Proved(t) => {
                self.convs.proved += 1;
                if crate::ev::Sealed::new(t.clone()).is_ok() {
                    self.convs.sealed += 1;
                }
            }
            crate::ev::Ev::Gap(_) => self.convs.gapped += 1,
        }
    }

    /// The applicative structure of a term built through [`Interp::mk`].
    ///
    /// A *hint*, exactly as [`derived::skeleton::Parts`] is: the kernel does
    /// not expose `Term`'s constructors for reading, so structure has to be
    /// recorded on the way in. A wrong entry yields a decomposition that fails
    /// to reassemble, never a bad proof.
    pub fn parts_of(&self, t: &Term) -> Option<(FnSym, Vec<Term>)> { self.parts.get(t).cloned() }

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

    /// From `Γ ⊢ t ∈ Uₘ` infer `Γ ⊢ t ∈ Uₙ`, **keeping `Γ`**.
    ///
    /// [`Cumul::raise`] is the same rule for `Γ = ∅`, and refuses a
    /// hypothesis-carrying premise on purpose: it would otherwise union the
    /// caller's `Γ` into a result its own signature calls `⊢ t ∈ Uₙ`. That
    /// guard is right, and it names this module as the reason it exists —
    /// `mini` is exempt from boundary rule 6 and legitimately holds
    /// `Γ`-carrying theorems, so it is the one caller that can trip it.
    ///
    /// The fix belongs here rather than in `derived`, and it is not a
    /// weakening: the inclusion `⊢ Uₘ ⊆ Uₙ` is itself unconditional, and
    /// [`Thm::mp`] merges hypothesis sets correctly, so `Γ ⊢ t ∈ Uₘ` really
    /// does give `Γ ⊢ t ∈ Uₙ`. What mini must not do — and does not — is
    /// *label* the result unconditional; that is [`crate::ev::Sealed`]'s job at
    /// the store, and `Γ` is carried honestly until a scope discharges it.
    ///
    /// Every `Π` under a binder reaches this with a non-empty `Γ`: the domain's
    /// typing is derived under the enclosing scopes' hypotheses. So the empty
    /// case is the *rare* one here, which is exactly the inversion that makes
    /// mini's context constant-cost.
    fn raise_in_gamma(&self, m: usize, n: usize, mem: &Thm) -> Option<Thm> {
        let (x, _) = mem.concl().as_mem()?;
        let x = x.clone();
        // Same shape check `Cumul::raise` makes: a membership in some *other*
        // set must be refused rather than instantiated into nonsense.
        if *mem.concl() != Formula::mem(x.clone(), self.cumul.level(m)?) {
            return None
        }
        let step = derived::inst_all(self.cumul.lift(m, n)?, std::slice::from_ref(&x))?;
        Thm::mp(&step, mem)
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
    ///
    /// **`Γ` is carried, not required to be empty.** Under a binder the
    /// domain's typing is derived from the enclosing scopes' hypotheses, so the
    /// premises normally have a non-empty `Γ` and the conclusion inherits it.
    /// See [`Interp::raise_in_gamma`].
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
        // Both premises to `U_n`, keeping whatever `Γ` they carry.
        let a_mem = self.raise_in_gamma(l1 as usize, n, dom_mem)?;
        let b_mem = self.raise_in_gamma(l2 as usize, n, cod_mem)?;
        // `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` at the seed
        // of `U_n`, which for `n ≥ 1` is what `Tower::level(n)` is `U(·)` of.
        let seed = self.prelude.tower.seed(n);
        let inst = derived::inst_all(&self.prelude.tower.funspace, &[seed, a.clone(), b.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(&a_mem, &b_mem))?;
        let want = Formula::mem(self.fs(a, b), self.sort(n as u32));
        (*out.concl() == want).then_some(out)
    }

    // ──────────────────────────────────────────────────── the λ clause ──

    /// The graph machinery for one lambda **body shape**, keyed on its
    /// skeleton.
    ///
    /// Keyed, not memoised: two occurrences of one body shape must be the
    /// *same* graph symbol, or their definitional equality needs a theorem
    /// where reflexivity should do. The `holes` differ per occurrence and are
    /// therefore returned rather than stored.
    pub fn lam_site(&mut self, body_tm: &Term, w: FreeVar) -> Option<LamSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_tm, w, &mut holes)?;
        let k = holes.len();
        if let Some(c) = self.lams.get(&skel) {
            return Some(LamSite { holes, ..c.clone() })
        }
        // `t(h⃗, x) = skeleton`, with the holes **first** and the binder
        // **last** — the argument order every `_n` construction assumes.
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (t, t_ax) = derived::define_abbrev(&mut self.env, &xs, &skel)?;
        let p = self.prelude.clone();
        let (lam, lam_ax) = derived::funcs::lambda_n(&mut self.env, &p.ap, t)?;
        let site = LamSite { t, t_ax, lam, lam_ax, holes: Vec::new(), k };
        self.lams.insert(skel, site.clone());
        self.lam_by_sym.insert(lam, site.clone());
        Some(LamSite { holes, ..site })
    }

    /// `⟦λ x:A. b⟧ = lam(h⃗,⟦A⟧)`, taken apart again: the site at *this*
    /// occurrence's holes, and the domain.
    ///
    /// The inverse of [`Interp::lam_term`], and the reason `whnf`'s beta step
    /// needs no second traversal: the redex's own interpretation names the
    /// graph symbol, and the symbol names the site.
    pub fn as_lam(&self, t: &Term) -> Option<(LamSite, Term)> {
        let (f, mut args) = self.parts_of(t)?;
        let site = self.lam_by_sym.get(&f)?;
        if args.len() != site.k + 1 {
            return None
        }
        let dom = args.pop()?;
        Some((LamSite { holes: args, ..site.clone() }, dom))
    }

    /// `⟦Π x:A. B⟧`, taken apart: which of §6.2's three clauses built it, its
    /// domain, and the site that carries the fibre.
    pub fn as_pi(&self, t: &Term) -> Option<PiShape> {
        let (f, mut args) = self.parts_of(t)?;
        if f == self.prelude.fs.fs && args.len() == 2 {
            let cod = args.pop()?;
            let dom = args.pop()?;
            return Some(PiShape::Fs { dom, cod })
        }
        if let Some(site) = self.fibre_by_sym.get(&f) {
            if args.len() != site.k + 1 {
                return None
            }
            let dom = args.pop()?;
            return Some(PiShape::Dep { site: FibreSite { holes: args, ..site.clone() }, dom })
        }
        if let Some(site) = self.cond_by_sym.get(&f) {
            if args.len() != site.k + 1 {
                return None
            }
            let dom = args.pop()?;
            return Some(PiShape::Prop { site: CondSite { holes: args, ..site.clone() }, dom })
        }
        None
    }

    /// `⟦λ x:A. b⟧ = lam(h⃗, ⟦A⟧)` — the graph of the body symbol over the
    /// domain, §6.2's right column.
    pub fn lam_term(&mut self, site: &LamSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.lam, args)
    }

    /// Rewrite `Γ ⊢ ⟦b⟧ ∈ C` into `Γ ⊢ t(h⃗, w) ∈ C`, which is the shape the
    /// lambda typing rules state their premise in.
    ///
    /// One Leibniz step along the body symbol's own defining equation. The
    /// reassembly property is what makes it possible: instantiating the
    /// skeleton back at `(h⃗, w)` gives `⟦b⟧` on the nose, so the two sides of
    /// the equation are the two terms wanted and nothing has to be searched
    /// for.
    pub fn to_body_symbol(&mut self, site: &LamSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let mut args = site.holes.clone();
        args.push(Term::var(w));
        let tw = self.mk(site.t, args.clone());
        let inst = derived::inst_all(&site.t_ax, &args)?;
        // `⊢ t(h⃗,w) = ⟦b⟧`; Leibniz wants it the other way round.
        if *inst.concl() != Formula::eq(tw.clone(), subj.clone()) {
            return None
        }
        let back = derived::eq_symm(&mut self.env, &inst)?;
        let x = self.env.fresh_var();
        let leib =
            Thm::eq_leibniz(subj, tw.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(tw, set)).then_some(out)
    }

    /// `⊢ lam(h⃗,⟦A⟧) ∈ fs(⟦A⟧, C)` from `⊢ ∀x. (x ∈ ⟦A⟧ → t(h⃗,x) ∈ C)`.
    ///
    /// Lean's λ typing rule at a **constant** codomain. `family` is exactly
    /// what [`crate::scope::Closed::discharge`] produces, which is not a
    /// coincidence: the discharge shape and the lemma shape were chosen to be
    /// the same one, so nothing is re-proved against a merged hypothesis set.
    pub fn lam_typing_fs(
        &mut self,
        site: &LamSite,
        dom: Term,
        cod: Term,
        family: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let rule = derived::ext::lam_in_funspace_n(
            &mut self.env,
            &p.ap,
            &p.prod,
            &p.fs,
            site.t,
            site.lam,
            &site.lam_ax,
        )?;
        let mut args = site.holes.clone();
        args.push(dom.clone());
        args.push(cod.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let out = Thm::mp(&inst, family)?;
        let want = Formula::mem(self.lam_term(site, dom.clone()), self.fs(dom, cod));
        (*out.concl() == want).then_some(out)
    }

    // ──────────────────────────────────────── the dependent Π clause ──

    /// The dependent-product machinery for one **fibre shape** — the skeleton
    /// of `⟦B⟧` under the binder — keyed on that skeleton for the same reason
    /// [`Interp::lam_site`] is.
    ///
    /// This is the whole of `pi-dep`'s assembly, and it is assembly rather than
    /// derivation: every piece already exists in `derived`, and what mini
    /// supplies is the fibre symbol and the wiring. `Tower::family` packages
    /// exactly this for a *unary* fibre; a Lean `Π` body is an open expression,
    /// so mini's fibre has arity `k+1` and needs the `_n` route.
    pub fn fibre_site(&mut self, body_ty_tm: &Term, w: FreeVar) -> Option<FibreSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_ty_tm, w, &mut holes)?;
        let k = holes.len();
        if let Some(c) = self.fibres.get(&skel) {
            return Some(FibreSite { holes, ..c.clone() })
        }
        // `b(h⃗, x) = ⟦B⟧`'s skeleton — holes first, binder last.
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (b, b_ax) = derived::define_abbrev(&mut self.env, &xs, &skel)?;

        let p = self.prelude.clone();
        let dp = derived::ext::DProdN::new(&mut self.env, &p.ap, &p.fs, b)?;
        // The one ingredient that mentions `b`, and hence the only one that
        // has to be re-run per fibre rather than taken from the tower.
        let ur = derived::universe::universe_replacement_n(
            &mut self.env,
            &p.tower.space.empty_ax,
            dp.img,
            &dp.img_ax,
            b,
        )?;
        let replacement = derived::universe::least_universe_replacement_n(
            &mut self.env,
            p.tower.space.lu,
            &p.tower.space.lu_ax,
            dp.img,
            b,
            &ur,
        )?;
        let fibre = dp.fibre(&replacement);
        let u = derived::ext::UniverseParts {
            lu: p.tower.space.lu,
            c2: &p.tower.space.c2,
            fs_in_u: &p.tower.funspace_of,
            union: &p.tower.union,
            bin_union: &p.tower.bin_union,
        };
        let general =
            derived::ext::dprod_in_universe_of_n(&mut self.env, &p.ap, &p.fs, &fibre, &u)?;
        let rule =
            derived::ext::dprod_in_universe_pair_n(&mut self.env, &p.ap, &fibre, &u, &general)?;
        // `fibre` borrows `replacement`; the borrow ends here.

        let site =
            FibreSite { b, b_ax, dp: Rc::new(dp), replacement, rule, holes: Vec::new(), k };
        self.fibres.insert(skel, site.clone());
        self.fibre_by_sym.insert(site.dp.dprod, site.clone());
        Some(FibreSite { holes, ..site })
    }

    /// `b(q⃗, x)` — the fibre at a point, **recorded** so that a later skeleton
    /// decomposition can walk into it.
    pub fn fibre_at(&mut self, site: &FibreSite, x: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(x);
        self.mk(site.b, args)
    }

    /// `⟦Π x:A. B⟧ = dprod(h⃗, ⟦A⟧)` — §6.2's right column, dependent case.
    pub fn dprod_term(&mut self, site: &FibreSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.dp.dprod, args)
    }

    /// Rewrite `Γ ⊢ ⟦B⟧ ∈ C` into `Γ ⊢ b(h⃗, w) ∈ C`, the shape the `Π` rule
    /// states its fibre premise in. [`Interp::to_body_symbol`] for the fibre.
    pub fn to_fibre_symbol(&mut self, site: &FibreSite, w: FreeVar, mem: &Thm) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let mut args = site.holes.clone();
        args.push(Term::var(w));
        let bw = self.mk(site.b, args.clone());
        let inst = derived::inst_all(&site.b_ax, &args)?;
        if *inst.concl() != Formula::eq(bw.clone(), subj.clone()) {
            return None
        }
        let back = derived::eq_symm(&mut self.env, &inst)?;
        let x = self.env.fresh_var();
        let leib = Thm::eq_leibniz(subj, bw.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(bw, set)).then_some(out)
    }

    /// From `Γ ⊢ x ∈ A` and `⊢ A = B` infer `Γ ⊢ x ∈ B` — MINI-DESIGN.md
    /// §6.2's `retarget`, one Leibniz step on the membership's **right** side.
    ///
    /// This is what a conversion is *for*: every `assert_def_eq` in the
    /// application and `let` clauses ends by moving a typing along the
    /// equation it just proved. `Γ` is carried.
    pub fn retarget_set(&mut self, mem: &Thm, eq: &Thm) -> Option<Thm> {
        let (subj, a) = mem.concl().as_mem()?;
        let (subj, a) = (subj.clone(), a.clone());
        let (lhs, rhs) = eq.concl().as_eq()?;
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        if lhs != a {
            return None
        }
        let x = self.env.fresh_var();
        let leib =
            Thm::eq_leibniz(lhs, rhs.clone(), x, Formula::mem(subj.clone(), Term::var(x)));
        let out = Thm::mp(&Thm::mp(&leib, eq)?, mem)?;
        (*out.concl() == Formula::mem(subj, rhs)).then_some(out)
    }

    /// `⊢ dprod(h⃗,⟦A⟧) ∈ ⟦Sort n⟧` from `⊢ ⟦A⟧ ∈ ⟦Sort n⟧` and
    /// `⊢ ∀x. (x ∈ ⟦A⟧ → b(h⃗,x) ∈ ⟦Sort n⟧)` — **Lean's dependent `Π` rule**.
    ///
    /// `n` must be `max(l1, l2)`; both premises are the caller's to raise
    /// there, because the fibre premise sits *under* a binder and needs
    /// `Cumul::raise_fibres` rather than `raise`. `Γ` is carried.
    pub fn dprod_typing(
        &mut self,
        site: &FibreSite,
        dom: Term,
        dom_mem: &Thm,
        fibres: &Thm,
        n: u32,
    ) -> Option<Thm> {
        if n == 0 || n as usize > self.cumul.height {
            return None
        }
        let seed = self.prelude.tower.seed(n as usize);
        let mut args = site.holes.clone();
        args.push(seed);
        args.push(dom.clone());
        let inst = derived::inst_all(&site.rule, &args)?;
        let out = Thm::mp(&inst, &derived::and_intro(dom_mem, fibres))?;
        let want = Formula::mem(self.dprod_term(site, dom), self.sort(n));
        (*out.concl() == want).then_some(out)
    }

    /// `⊢ lam(h⃗,⟦A⟧) ∈ dprod(q⃗,⟦A⟧)` from
    /// `⊢ ∀x. (x ∈ ⟦A⟧ → t(h⃗,x) ∈ b(q⃗,x))` — Lean's λ rule at a **dependent**
    /// codomain, and the half of `lam` that `pi-dep` unblocks.
    pub fn lam_typing_dprod(
        &mut self,
        lam: &LamSite,
        fibre: &FibreSite,
        dom: Term,
        family: &Thm,
    ) -> Option<Thm> {
        let p = self.prelude.clone();
        let beta =
            derived::funcs::beta_conditional_n(&mut self.env, &p.ap, lam.t, lam.lam, &lam.lam_ax)?;
        let lam_fs = derived::ext::lam_in_funspace_n(
            &mut self.env,
            &p.ap,
            &p.prod,
            &p.fs,
            lam.t,
            lam.lam,
            &lam.lam_ax,
        )?;
        let rule = derived::ext::lam_in_dprod_n(
            &mut self.env,
            &p.ap,
            &p.fs,
            (lam.t, lam.lam, &beta, &lam_fs),
            (fibre.b, fibre.dp.img, &fibre.dp.img_ax, fibre.dp.dprod, &fibre.dp.dprod_def),
        )?;
        let mut args = lam.holes.clone();
        args.extend(fibre.holes.clone());
        args.push(dom.clone());
        let inst = derived::inst_all(&rule, &args)?;
        let out = Thm::mp(&inst, family)?;
        let want =
            Formula::mem(self.lam_term(lam, dom.clone()), self.dprod_term(fibre, dom));
        (*out.concl() == want).then_some(out)
    }

    // ───────────────────────────────────────────── the Prop Π clause ──

    /// The conditional-singleton machinery for one **`Prop`-valued `∀`** shape.
    ///
    /// §6.2's *other* column for `Π`: a `Prop`-valued `∀x : α. β` interprets to
    /// `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`, a conditional singleton, rather than to a
    /// dependent product. The two are different sets and nothing relates them,
    /// which is why the clause has to be decided (by
    /// [`crate::kernel::Checker::body_clause`]) and not guessed.
    ///
    /// The fibre symbol is built exactly as [`Interp::fibre_site`] builds one —
    /// same skeleton, same holes-first order — but nothing else is: there is no
    /// image, no dependent product and no universe chain, because the whole
    /// thing lands in `U₀` by one lemma.
    pub fn cond_site(&mut self, body_ty_tm: &Term, w: FreeVar) -> Option<CondSite> {
        let mut holes = Vec::new();
        let skel = self.skeleton(body_ty_tm, w, &mut holes)?;
        let k = holes.len();
        if let Some(c) = self.conds.get(&skel) {
            return Some(CondSite { holes, ..c.clone() })
        }
        let mut xs: Vec<FreeVar> = (0..k).map(|i| self.hole_var(i)).collect();
        xs.push(self.x_canon);
        let (b, b_ax) = derived::define_abbrev(&mut self.env, &xs, &skel)?;

        // `φ(h⃗, A) := ∀x. (x ∈ A → • ∈ b(h⃗, x))`, with the binder slot the
        // canonical one, so that one body shape gives one formula.
        let a_var = self.env.fresh_var();
        let mut bargs: Vec<Term> = xs[..k].iter().map(|v| Term::var(*v)).collect();
        bargs.push(Term::var(self.x_canon));
        let bx = self.mk(b, bargs);
        let point = self.prelude.point();
        let phi = Formula::forall(
            self.x_canon,
            Formula::imp(
                Formula::mem(Term::var(self.x_canon), Term::var(a_var)),
                Formula::mem(point, bx),
            ),
        );
        let mut params: Vec<FreeVar> = xs[..k].to_vec();
        params.push(a_var);

        let p = self.prelude.clone();
        let (chi, chi_ax) =
            derived::prop::conditional_singleton(&mut self.env, &p.tower.sums, &params, &phi)?;
        let site = CondSite { b, b_ax, chi, chi_ax, phi, params, holes: Vec::new(), k };
        self.conds.insert(skel, site.clone());
        self.cond_by_sym.insert(chi, site.clone());
        Some(CondSite { holes, ..site })
    }

    /// `b(q⃗, x)` for the `Prop` clause's fibre, recorded.
    pub fn cond_fibre_at(&mut self, site: &CondSite, x: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(x);
        self.mk(site.b, args)
    }

    /// This occurrence's `(⟦∀x:α.β⟧, φ, ⊢ ∀z. (z ∈ χ ↔ (z ∈ 1 ∧ φ)))`.
    ///
    /// The three things every `cond` lemma wants, computed once: the term, the
    /// formula at this occurrence's holes and domain, and the characteristic
    /// theorem instantiated there.
    pub fn cond_parts(&mut self, site: &CondSite, dom: Term) -> Option<(Term, Formula, Thm)> {
        let c = self.cond_term(site, dom.clone());
        let mut args = site.holes.clone();
        args.push(dom);
        let chi_at = derived::inst_all(&site.chi_ax, &args)?;
        let mut phi = site.phi.clone();
        for (v, t) in site.params.iter().zip(args.iter()) {
            phi = phi.subst(*v, t);
        }
        Some((c, phi, chi_at))
    }

    /// `⟦∀x:α. β⟧ = chi(h⃗, ⟦α⟧) = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`.
    pub fn cond_term(&mut self, site: &CondSite, dom: Term) -> Term {
        let mut args = site.holes.clone();
        args.push(dom);
        self.mk(site.chi, args)
    }

    // ────────────────────────────────────────── the application rules ──
    //
    // One per `Π` clause, because the three interpretations are three
    // different sets and nothing relates them. Each takes the two memberships
    // the checker already holds — `Γ ⊢ ⟦f⟧ ∈ ⟦Π x:A. B⟧` from `infer_type(f)`
    // transported along `whnf`, and `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧` from `infer_type(a)`
    // retargeted along the domain conversion — and composes. Nothing is looked
    // for: this is where nanoda's `ty_app`/`app_in_codomain`/`app_in_fibre`
    // reach for `has_type_a`, and mini has both premises in its hands.

    /// `Γ ⊢ app(f,a) ∈ ⟦B⟧` from `Γ ⊢ f ∈ fs(⟦A⟧,⟦B⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    pub fn fs_app(
        &mut self,
        dom: &Term,
        cod: &Term,
        f: &Term,
        a: &Term,
        f_mem: &Thm,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let rule = self.prelude.fs_app_mem.clone();
        let inst =
            derived::inst_all(&rule, &[dom.clone(), cod.clone(), f.clone(), a.clone()])?;
        let out = Thm::mp(&inst, &derived::and_intro(f_mem, a_mem))?;
        let want = Formula::mem(self.app(f.clone(), a.clone()), cod.clone());
        (*out.concl() == want).then_some(out)
    }

    /// `Γ ⊢ app(f,a) ∈ b(q⃗,a)` from `Γ ⊢ f ∈ dprod(q⃗,⟦A⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    ///
    /// The dependent product's defining axiom says its members are exactly the
    /// sections, so the fibre membership is the right conjunct instantiated at
    /// `a`. No new derivation: `DProdN` proved it when the fibre symbol was
    /// introduced.
    pub fn dprod_app(
        &mut self,
        site: &FibreSite,
        dom: &Term,
        f: &Term,
        a: &Term,
        f_mem: &Thm,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let mut args = site.holes.clone();
        args.push(dom.clone());
        args.push(f.clone());
        let at = derived::inst_all(&site.dp.dprod_def, &args)?;
        let cond = Thm::mp(&derived::iff_mp(&at)?, f_mem)?;
        let section = derived::and_elim_right(&cond)?;
        let at_a = derived::inst_all(&section, std::slice::from_ref(a))?;
        let out = Thm::mp(&at_a, a_mem)?;
        let fibre = self.fibre_at(site, a.clone());
        let want = Formula::mem(self.app(f.clone(), a.clone()), fibre);
        (*out.concl() == want).then_some(out)
    }

    /// `Γ ⊢ • ∈ b(h⃗,a)` from `Γ ⊢ • ∈ chi(h⃗,⟦A⟧)` and `Γ ⊢ a ∈ ⟦A⟧`.
    ///
    /// The `Prop` clause's application rule. Both the function and the result
    /// are proofs, so both interpret to `•` and there is no graph to apply;
    /// what the certificate does is move from the conditional singleton's
    /// inhabitation to the fibre's, which is [`derived::prop::cond_elim`]
    /// followed by one instantiation.
    pub fn cond_app(
        &mut self,
        site: &CondSite,
        dom: &Term,
        f_mem: &Thm,
        a: &Term,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom.clone())?;
        let p = self.prelude.clone();
        let elim = derived::prop::cond_elim(&p.tower.sums, &phi, &c, &chi_at)?;
        let all = Thm::mp(&elim, f_mem)?;
        let at_a = derived::inst_all(&all, std::slice::from_ref(a))?;
        let out = Thm::mp(&at_a, a_mem)?;
        let fibre = self.cond_fibre_at(site, a.clone());
        let want = Formula::mem(self.point(), fibre);
        (*out.concl() == want).then_some(out)
    }

    /// `Γ ⊢ • ∈ chi(h⃗,⟦A⟧)` from `⊢ ∀x. (x ∈ ⟦A⟧ → • ∈ b(h⃗,x))` — the `λ`
    /// typing rule on the `Prop` branch.
    pub fn cond_lam_typing(&mut self, site: &CondSite, dom: Term, family: &Thm) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom)?;
        let p = self.prelude.clone();
        let intro = derived::prop::cond_intro(&p.tower.sums, &phi, &c, &chi_at)?;
        let out = Thm::mp(&intro, family)?;
        (*out.concl() == Formula::mem(self.point(), c)).then_some(out)
    }

    /// From `Γ ⊢ x ∈ A` and `⊢ y = x` infer `Γ ⊢ y ∈ A` — [`Interp::retarget_set`]
    /// on the membership's **left** side.
    ///
    /// The declaration pipeline's last step: a definition's constant is an
    /// abbreviation for its value's interpretation, and its typing is the
    /// value's typing carried back along that defining equation.
    pub fn retarget_subject(&mut self, mem: &Thm, eq: &Thm) -> Option<Thm> {
        let (subj, set) = mem.concl().as_mem()?;
        let (subj, set) = (subj.clone(), set.clone());
        let (lhs, rhs) = eq.concl().as_eq()?;
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        if rhs != subj {
            return None
        }
        let x = self.env.fresh_var();
        let leib =
            Thm::eq_leibniz(rhs, lhs.clone(), x, Formula::mem(Term::var(x), set.clone()));
        let back = derived::eq_symm(&mut self.env, eq)?;
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem)?;
        (*out.concl() == Formula::mem(lhs, set)).then_some(out)
    }

    /// `⊢ ⟦∀x:α. β⟧ ∈ ⟦Prop⟧` — the whole typing obligation of the `Prop` `Π`
    /// clause, and it is *unconditional*: every conditional singleton is a
    /// subset of `1`, hence a truth value, hence in `U₀`, whatever the fibre
    /// does. Nothing about `⟦β⟧` is needed, so nothing is assumed about it.
    ///
    /// This is where the two `Π` clauses differ most sharply. The dependent
    /// product needs its domain *and* its fibres placed in a universe first
    /// ([`Interp::dprod_typing`]); this needs neither.
    pub fn cond_typing(&mut self, site: &CondSite, dom: Term) -> Option<Thm> {
        let (c, phi, chi_at) = self.cond_parts(site, dom)?;
        let p = self.prelude.clone();
        let out = p.tower.cond_in_u0(&mut self.env, &phi, &c, &chi_at)?;
        (*out.concl() == Formula::mem(c, self.sort(0))).then_some(out)
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

    /// **The `Π` rule under a binder**, which is the case that actually occurs:
    /// the domain's typing comes from an enclosing scope and carries that
    /// scope's hypothesis. The result must carry it too — and must not be
    /// labelled unconditional, which is what `Cumul::raise`'s `hyps()` guard
    /// exists to prevent and what `Interp::raise_in_gamma` handles instead.
    ///
    /// `Π (_ : α). Prop` for a bound `α : Type 0`.
    #[test]
    fn the_pi_rule_carries_gamma_from_an_enclosing_scope() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let u1 = ip.sort(1);
        let tok = sc.open(&mut ip.env, u1.clone());
        // `Γ ⊢ α ∈ ⟦Type 0⟧` — the scope's own assumption, at zero cost.
        let dom_mem = sc.get(0).unwrap().assumption().clone();
        let alpha = sc.get(0).unwrap().term();
        assert_eq!(dom_mem.hyps().len(), 1);
        // `⊢ ⟦Prop⟧ ∈ ⟦Type 0⟧`, hypothesis-free.
        let cod_mem = ip.sort_typing(0).unwrap();

        let out = ip.fs_typing(&dom_mem, &cod_mem, 1, 1).expect("Π typing under a binder");
        assert_eq!(out.hyps(), dom_mem.hyps(), "Γ must be carried, not dropped");
        let want = Formula::mem(ip.fs(alpha, ip.sort(0)), ip.sort(1));
        assert_eq!(*out.concl(), want);
        // And it is not silently unconditional: sealing it must fail.
        assert!(crate::ev::Sealed::new(out).is_err());
        let _ = sc.close(tok);
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

    /// **`⟦λ (x : Prop). x⟧ ∈ ⟦Prop → Prop⟧`, end to end**, through exactly the
    /// pipeline the checker will use: interpret the domain, open a scope,
    /// interpret the body, decompose it into a skeleton, define the body
    /// symbol, build the graph, rewrite the body's membership along the body
    /// symbol's own defining equation, discharge the scope, and feed the
    /// resulting `∀`-`→` family to the typing rule.
    ///
    /// Nothing is searched for at any step, and the family `discharge`
    /// produces is fed to the lemma unchanged — the two shapes were chosen to
    /// be the same one.
    #[test]
    fn the_identity_lambda_lands_in_the_function_space() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);

        let tok = sc.open(&mut ip.env, dom.clone());
        let w = sc.get(0).unwrap().var();
        // The body is `bvar 0`, so ⟦b⟧ is the scope's own variable and its
        // typing is the scope's stored assumption — no derivation at all.
        let body_tm = Term::var(w);
        let body_mem = sc.get(0).unwrap().assumption().clone();

        let site = ip.lam_site(&body_tm, w).expect("lam site");
        assert_eq!(site.k, 0, "the identity body has no holes");
        let as_sym = ip.to_body_symbol(&site, w, &body_mem).expect("rewrite");
        assert_eq!(as_sym.hyps().len(), 1, "the rewrite must keep Γ, not drop it");

        let closed = sc.close_checked(tok, &as_sym);
        let family = closed.discharge(&as_sym).expect("discharge");
        assert!(family.hyps().is_empty());

        let out = ip.lam_typing_fs(&site, dom.clone(), dom.clone(), &family).expect("λ typing");
        assert!(out.hyps().is_empty(), "the λ rule must be unconditional");
        let want = Formula::mem(ip.lam_term(&site, dom.clone()), ip.fs(dom.clone(), dom));
        assert_eq!(*out.concl(), want);
    }

    /// A body with a **hole**: `λ (x : Prop). app(c, x)` for a closed `c`. The
    /// prefix is what the whole `_n` lemma family exists for, and it must be
    /// threaded in the right order — holes first, domain last.
    #[test]
    fn a_lambda_with_a_prefix_threads_its_holes() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c, _) = ip.abbrev(&ip.sort(1)).expect("abbrev");

        let tok = sc.open(&mut ip.env, dom.clone());
        let w = sc.get(0).unwrap().var();
        let body_tm = ip.app(c.clone(), Term::var(w));
        let site = ip.lam_site(&body_tm, w).expect("lam site");
        assert_eq!(site.k, 1, "`c` is the one hole");
        assert_eq!(site.holes, vec![c], "and it is the abstracted subterm");
        // The graph term carries the prefix, then the domain.
        let lam = ip.lam_term(&site, dom.clone());
        assert_eq!(lam, {
            let mut a = site.holes.clone();
            a.push(dom);
            ip.mk(site.lam, a)
        });
        let _ = sc.close(tok);
    }

    /// **One body shape, one graph symbol.** Two lambdas whose bodies differ
    /// only in the binder-free parts must share the symbol, or their
    /// definitional equality would need a theorem where reflexivity does.
    #[test]
    fn two_occurrences_of_one_shape_share_the_graph() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c1, _) = ip.abbrev(&ip.sort(1)).unwrap();
        let (c2, _) = ip.abbrev(&ip.sort(2)).unwrap();

        let t1 = sc.open(&mut ip.env, dom.clone());
        let w1 = sc.get(0).unwrap().var();
        let b1 = ip.app(c1.clone(), Term::var(w1));
        let s1 = ip.lam_site(&b1, w1).unwrap();
        let _ = sc.close(t1);

        let t2 = sc.open(&mut ip.env, dom);
        let w2 = sc.get(0).unwrap().var();
        let b2 = ip.app(c2.clone(), Term::var(w2));
        let s2 = ip.lam_site(&b2, w2).unwrap();
        let _ = sc.close(t2);

        assert_eq!(s1.lam, s2.lam, "one shape must give one graph symbol");
        assert_eq!(s1.t, s2.t);
        assert_eq!(s1.holes, vec![c1]);
        assert_eq!(s2.holes, vec![c2], "the holes differ; the shape does not");
    }

    /// **`⟦Π (x : Type 0). x⟧ ∈ ⟦Type 1⟧`, end to end.** A genuinely dependent
    /// `Π`: the fibre is the binder itself, so the function space cannot say
    /// it and the dependent product must.
    ///
    /// Pipeline: interpret the domain, open a scope, interpret the body type,
    /// decompose it into a fibre skeleton, define `b(h⃗,x)`, build `DProdN` and
    /// the Π rule over it, rewrite the body type's membership along `b`'s
    /// defining equation, discharge, and apply.
    #[test]
    fn a_dependent_pi_lands_in_the_universe() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        // `Π (x : Type 0). x` — domain `⟦Type 0⟧ = U₁`, body `x : Type 0`.
        let dom = ip.sort(1);
        let dom_mem = ip.sort_typing(1).unwrap(); // ⊢ U₁ ∈ U₂

        let tok = sc.open(&mut ip.env, dom.clone());
        let w = sc.get(0).unwrap().var();
        let body_ty = Term::var(w);
        // `Γ ⊢ x ∈ U₁`, the scope's own assumption; raise it to `U₂`, which is
        // where the `Π` lives (`imax 2 2 = 2`).
        let body_mem = sc.get(0).unwrap().assumption().clone();
        let body_mem = ip.raise_in_gamma(1, 2, &body_mem).expect("lift the fibre");

        let site = ip.fibre_site(&body_ty, w).expect("fibre site");
        assert_eq!(site.k, 0, "the fibre is the binder itself — no holes");
        let as_sym = ip.to_fibre_symbol(&site, w, &body_mem).expect("rewrite");
        let closed = sc.close_checked(tok, &as_sym);
        let fibres = closed.discharge(&as_sym).expect("discharge");
        assert!(fibres.hyps().is_empty());

        let out = ip.dprod_typing(&site, dom.clone(), &dom_mem, &fibres, 2).expect("Π typing");
        assert!(out.hyps().is_empty());
        let want = Formula::mem(ip.dprod_term(&site, dom), ip.sort(2));
        assert_eq!(*out.concl(), want);
    }

    /// **`⟦λ (x : Prop). x⟧ ∈ ⟦Π (x : Prop). Prop⟧`** — the λ rule at a
    /// *dependent* codomain, which is the half of `lam` that `pi-dep`
    /// unblocks. Both the graph and the dependent product are built here and
    /// the membership relates them.
    ///
    /// The fibre is constant in this example, but the code path is not: the
    /// fibre's skeleton has no occurrence of the binder, so `⟦Prop⟧` becomes a
    /// **hole** and `b` has arity 2, which is exactly the prefix threading the
    /// `_n` family exists for. The first attempt at this test used a fibre that
    /// *was* the binder — `Π (x : Type 0). x` — which is not inhabited by the
    /// identity: it would need `x : x`, which Regularity refutes. The rule
    /// refused it, correctly.
    #[test]
    fn the_identity_lambda_lands_in_the_dependent_product() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);

        let tok = sc.open(&mut ip.env, dom.clone());
        let w = sc.get(0).unwrap().var();
        let lam = ip.lam_site(&Term::var(w), w).expect("lam site");
        let fib = ip.fibre_site(&dom.clone(), w).expect("fibre site");
        assert_eq!(fib.k, 1, "the binder-free fibre becomes one hole");
        assert_eq!(fib.holes, vec![dom.clone()]);

        // `Γ ⊢ w ∈ ⟦Prop⟧`, the scope's own assumption, rewritten to
        // `Γ ⊢ t(w) ∈ b(⟦Prop⟧, w)` — subject side then set side.
        let mem = sc.get(0).unwrap().assumption().clone();
        let mem = ip.to_body_symbol(&lam, w, &mem).expect("to t");
        let b_at = derived::inst_all(&fib.b_ax, &[dom.clone(), Term::var(w)]).expect("b at w");
        let back = derived::eq_symm(&mut ip.env, &b_at).expect("symm");
        let mem = ip.retarget_set(&mem, &back).expect("retarget to the fibre");

        let closed = sc.close_checked(tok, &mem);
        let family = closed.discharge(&mem).expect("discharge");
        let out = ip.lam_typing_dprod(&lam, &fib, dom.clone(), &family).expect("λ in dprod");
        assert!(out.hyps().is_empty());
        let want = Formula::mem(ip.lam_term(&lam, dom.clone()), ip.dprod_term(&fib, dom));
        assert_eq!(*out.concl(), want);
    }

    /// **`⟦∀ (x : Prop). x⟧ ∈ ⟦Prop⟧`** — the `Prop` `Π` clause, end to end.
    ///
    /// The fibre here genuinely *is* the binder, so this is the dependent
    /// shape that `a_dependent_pi_lands_in_the_universe` could not use on the
    /// `Type` side (there it would have needed `x : x`). On the `Prop` side it
    /// is fine and is the honest test: the conditional singleton lands in `U₀`
    /// **whatever the fibre does**, so nothing about `⟦β⟧` is assumed.
    #[test]
    fn a_prop_valued_forall_lands_in_prop() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let tok = sc.open(&mut ip.env, dom.clone());
        let w = sc.get(0).unwrap().var();

        let site = ip.cond_site(&Term::var(w), w).expect("cond site");
        assert_eq!(site.k, 0, "the fibre is the binder itself — no holes");
        let out = ip.cond_typing(&site, dom.clone()).expect("Prop Π typing");
        assert!(out.hyps().is_empty(), "the Prop Π rule is unconditional");
        assert_eq!(*out.concl(), Formula::mem(ip.cond_term(&site, dom.clone()), ip.sort(0)));

        // **The two Π clauses are different sets.** A conditional singleton is
        // not a dependent product, which is why the clause has to be decided
        // rather than guessed.
        let fib = ip.fibre_site(&Term::var(w), w).expect("fibre site");
        assert_ne!(ip.cond_term(&site, dom.clone()), ip.dprod_term(&fib, dom));
        let _ = sc.close(tok);
    }

    /// The `Prop` clause with a **prefix**: `∀ (x : Prop). c`, whose fibre is
    /// binder-free and so becomes a hole. Same shape-keying discipline as the
    /// other two sites.
    #[test]
    fn the_prop_clause_threads_a_prefix_and_shares_shapes() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let dom = ip.sort(0);
        let (c1, _) = ip.abbrev(&ip.sort(1)).unwrap();
        let (c2, _) = ip.abbrev(&ip.sort(2)).unwrap();

        let t1 = sc.open(&mut ip.env, dom.clone());
        let w1 = sc.get(0).unwrap().var();
        let s1 = ip.cond_site(&c1.clone(), w1).expect("site");
        let out = ip.cond_typing(&s1, dom.clone()).expect("typing");
        assert_eq!(*out.concl(), Formula::mem(ip.cond_term(&s1, dom.clone()), ip.sort(0)));
        let _ = sc.close(t1);

        let t2 = sc.open(&mut ip.env, dom);
        let w2 = sc.get(0).unwrap().var();
        let s2 = ip.cond_site(&c2.clone(), w2).expect("site");
        let _ = sc.close(t2);

        assert_eq!(s1.k, 1);
        assert_eq!(s1.chi, s2.chi, "one shape, one conditional singleton symbol");
        assert_eq!(s1.holes, vec![c1]);
        assert_eq!(s2.holes, vec![c2]);
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
