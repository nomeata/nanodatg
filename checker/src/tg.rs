//! The Tarski–Grothendieck proof backend: real [`kernel::Thm`] certificates.
//!
//! # What this does and does not claim
//!
//! Every Lean expression is interpreted as a term of the kernel's first-order
//! language, and every definitional-equality certificate is a genuine kernel
//! theorem `⟦a⟧ = ⟦b⟧` — derived from the equality axioms by real inference
//! rules, not asserted.
//!
//! Most of the interpretation is still **pure signature extension**: fresh
//! symbols with *no* axioms (the dependent `pi`, `let`, `proj`, `bvar`, the
//! level formers, …). That is unconditionally conservative, so nothing here
//! enlarges the trusted base or risks consistency. Four parts of the
//! interpretation are now *definitional extensions* instead, which is what
//! makes them mean something:
//!
//! * **`Sort`**. `⟦Sort 0⟧` is a fixed constant and `⟦Sort (u+1)⟧ := U(⟦Sort u⟧)`,
//!   where `U` is the least-Grothendieck-universe operator of
//!   [`derived::universe`]. `⊢ ∀x. x ∈ U(x)` then gives
//!   `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` outright — the one typing fact this backend has.
//!   Levels that are not literal successors keep an opaque `sort` symbol.
//! * **`App`**. `⟦f a⟧ := app(⟦f⟧, ⟦a⟧)`, with `app` the set-theoretic
//!   application of [`derived::funcs`].
//! * **`Lam`**. `⟦λx:A. b⟧` is the *function graph* `{⟨x, t(x)⟩ : x ∈ ⟦A⟧}` of
//!   [`derived::funcs::lambda`]. See "Lambdas" below for how the body is turned
//!   into a function symbol, and why the version used here is `lambda_n`.
//! * **Non-dependent `Pi`**. `⟦A → B⟧ := fs(⟦A⟧, ⟦B⟧)`, the set-theoretic
//!   function space of [`derived::funspace`]. A *dependent* `Π` keeps the
//!   opaque `pi` symbol: the dependent product is not constructed in
//!   `derived/`, and reusing `fs` for it would be asserting facts about a set
//!   nobody built. Non-dependence is decided conservatively from the body's
//!   loose-bvar count, so the worst case is that an arrow is treated as a
//!   dependent product and beta over it reports a gap.
//!
//! With those in place [`derived::funcs::beta_conditional`] applies, and
//! [`Certifier::beta`] is a real derivation rather than an admit — modulo one
//! premise it cannot always discharge, discussed under "What beta still costs".
//!
//! # Lambdas: how the body becomes a function symbol
//!
//! `lambda` wants the body as a *unary* function symbol `t`, but a Lean lambda
//! body is an open expression. Instantiating the binder at a fresh local and
//! interpreting gives a term `bt` containing one distinguished free variable
//! `v`; the obvious move is then `t(v) := bt`. That is wrong as it stands,
//! because a nested lambda's body mentions the *enclosing* binders too, and a
//! defined symbol may not contain free variables that are not among its
//! parameters (it would not be a conservative extension).
//!
//! The fix is to abstract more: `bt` is split into a **skeleton** — the part
//! that actually mentions `v` — and the list of **maximal `v`-free subterms**,
//! which become extra parameters. So
//!
//! ```text
//! ⟦λ y:A. b⟧  :=  lam_C(s₁, …, s_k, ⟦A⟧)
//! ```
//!
//! where `C` is the skeleton, `lam_C` is the graph symbol built once per
//! skeleton, and `s⃗` are the abstracted subterms. This decomposition is
//! canonical *and* stable under substitution — substituting into an `s_i`
//! keeps it `v`-free and leaves `C` alone — which is exactly the property beta
//! needs: `⟦b[a]⟧` really is `⟦b⟧` with the abstracted positions filled in, so
//! the two sides of the beta equation line up syntactically instead of merely
//! morally. Without it, `⟦(λx.λy.x) P⟧` and `⟦λy.P⟧` would be built from
//! unrelated symbols and no chain of steps could connect them.
//!
//! A skeleton's graph is derived **once for the whole run**, not once per
//! declaration: the signature every backend builds terms in is shared per
//! thread (see [`Shared`]), so two occurrences of one body shape in two
//! declarations are the same *term* and hit the same cache. That is what makes
//! the construction affordable for every lambda, with no cut-off on how many
//! subterms a body may abstract.
//!
//! The extra parameters are why `lambda_n`, `beta_conditional_n` and
//! `lam_ext_n` exist: the derived originals take a unary body symbol, and `t`
//! here has arity `k + 1`. They are the derived derivations with the prefix
//! threaded through, and coincide with them at `k = 0`. `lam_ext_n` threads
//! *two* prefixes, of independent lengths, since the two lambdas it relates
//! have unrelated skeletons.
//!
//! # What beta still costs
//!
//! `beta_conditional` is *conditional*: a set-theoretic function has a set
//! domain, so `app(lam(A), a) = t(a)` needs `a ∈ A`. Discharging that is a
//! **typing** obligation — `⟦a⟧ ∈ ⟦A⟧` whenever Lean says `a : A` — and this
//! backend can prove exactly two instances of it (see `domain_premise`):
//!
//! * `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧`, from `⊢ ∀x. x ∈ U(x)`;
//! * `⟦A → A⟧ ∈ ⟦Sort (u+1)⟧` when `⟦A⟧` is `⟦Sort u⟧`, from
//!   [`derived::funspace`]'s `⊢ ∀a. fs(a,a) ∈ U(a)`.
//!
//! The restriction to the diagonal `fs(a,a)` is not a shortcut either: the
//! two-argument form `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` exists,
//! but its antecedent needs closure of `U(x)` under binary unions, which is
//! unproved. That is a limitation of the interpretation rather than of the
//! derivation: nothing here yet says in general what it means for a Lean term to
//! *inhabit* a Lean type.
//!
//! Everywhere else the premise is **carried rather than admitted**. The
//! certificate becomes `⊢ (⟦a⟧ ∈ ⟦A⟧) → ⟦redex⟧ = ⟦reduct⟧` — a complete
//! derivation of a weaker statement, not an assertion — and every rule below
//! merges its premises' assumptions and lifts its reasoning through the
//! conjunction. At a `λ` binder an assumption about *that binder's own variable*
//! is discharged into `lam_ext_n`'s pointwise premise, which is exactly the
//! shape that premise wants.
//!
//! That matters because the obligation used to poison whole subtrees: a beta
//! step that could not discharge it became an admit, and every `trans`, `symm`
//! and congruence above it became "over an admitted premise". Carrying it
//! collapses each of those cascades to a single accounted gap. Measured, over
//! the tutorial corpus: 726 gaps before, 586 after, with the 206
//! `beta: argument not shown to lie in the binder's domain` gaps gone entirely;
//! on `good/init-prelude.ndjson`, 23812 before and 18025 after. `028_peano2`
//! goes from 32 gaps to 8 and `029_peano3` from 59 to 9.
//!
//! # Honesty
//!
//! [`Certifier::beta`], [`Certifier::delta`] and [`Certifier::lam_cong`], the
//! rules that build a chain rather than read one off, check before returning
//! [`TgCert::Proved`] that the theorem they hold is literally `⟦a⟧ = ⟦b⟧` for
//! the `a`, `b` the checker claimed equal; `refl`, `sort` and `const_eq`
//! compare the two interpretations directly.
//!
//! A *conditional* certificate is held in its own variant and never passes for
//! an unconditional one — [`TgCert::thm`] answers `None` for it — and the
//! assumptions it advertises are checked, on construction, to be literally the
//! antecedent of the theorem it carries ([`CondEq::new`]). And a conditional
//! certificate that reaches the checker as an *answer* is not a proof of what
//! the checker claimed, so it is counted and reported as a gap; see the escape
//! ledger next to [`escaped`]. Over the tutorial corpus 128 certificates finish
//! that way, and 2507 on `init-prelude`; those numbers are in the totals above,
//! not excluded from them.
//!
//! [`Certifier::app_cong`] is the exception, and not by choice: it is handed
//! sub-*certificates* rather than terms, so it cannot see what it is supposed
//! to be proving. It does still apply congruence, which is right for `app`.
//!
//! [`Certifier::pi_cong`] is handed both terms and checks. It now also *uses*
//! its premises: the checker compares binder bodies after opening them at a
//! local, so the certificate below a `Π` is about `⟦b[v]⟧` while the claim is
//! about `⟦b⟧` in de Bruijn form, and [`TgBackend::retarget`] closes the gap by
//! generalising `v` and instantiating it at the bound-variable encoding — the
//! step the previous version of this comment described as not taken. What that
//! bought is stated plainly under "What `Π` congruence still costs".
//!
//! # What `Π` congruence still costs
//!
//! Retargeting made every `Π` congruence a real derivation from its premises;
//! it closed no gaps at all. The reason is worth recording, because the two
//! numbers pull in opposite directions.
//!
//! *Before*, on `good/init-prelude.ndjson`: 5084 `pi_cong` conclusions, of which
//! 3746 came from congruence and 1338 from the reflexivity fallback. *After*:
//! 5084 from congruence, 0 from the fallback. But the fallback fires exactly
//! when the two sides interpret to the *same* term, and that is also when
//! congruence is trivial — on that corpus only 57 of the 5084 conclusions relate
//! two genuinely different terms. So the rule is stronger in form and settles
//! the same set of claims.
//!
//! The 4634 gaps it does *not* settle there (219 over the tutorial corpus)
//! divide into three kinds, none of which is a missing congruence:
//!
//! * **2682 are cascades.** A premise below was itself admitted — usually a beta
//!   step whose typing obligation is undischargeable — so there is nothing to
//!   apply congruence *to*. These are named for what is missing.
//! * **1196 are an encoding mismatch.** One side's body mentions the binder and
//!   the other's does not, so one interprets as the opaque `pi` and the other as
//!   `fs`. Relating them needs a theorem identifying a constant-fibre dependent
//!   product with the function space, which `derived/` does not have.
//! * **756 are a de Bruijn shift.** The certificate mentions one local where the
//!   claim has two different `bvar` symbols for the same binder — `⟦A⟧` and
//!   `⟦B⟧` in `fs(⟦A⟧,⟦B⟧)` sit one binder apart, and `inst` does not lower an
//!   out-of-range index. No substitution can send one variable to two terms, so
//!   retargeting refuses. Re-basing the body's indices on the interpretation
//!   side was tried and measured: it moved gaps between these categories and
//!   changed no total, on either corpus.
//!
//! [`derived::ext::dprod_ext`] does not help with any of these. It wants a
//! *unary* fibre symbol, and a Lean `Π` body generally interprets to a term with
//! free variables besides the binder's, which a unary symbol may not contain —
//! the same problem the `lambda_n` machinery solves for lambdas, and
//! solving it here would mean an n-ary re-derivation of the whole `dprod`
//! development. Measured over the corpus, the unary case that needs no such
//! re-derivation arises 11 times on `init-prelude` and once on the tutorials.

use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use crate::expr::Expr;
use crate::level::Level;
use derived::funcs::Apply;
use kernel::{Certifier, Env, FnSym, Formula, FreeVar, Term, Thm};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::rc::Rc;

/// A certificate: a real kernel theorem, a real kernel theorem that still rests
/// on assumptions, or a named gap.
///
/// Making the gap a *variant* rather than a silent success is the point. A
/// backend that could only return `Thm` would have to either refuse (breaking
/// the checker) or forge (defeating the exercise); this way an unproved step is
/// recorded, propagates through the combinators, and can be reported.
///
/// [`TgCert::Conditional`] is a *separate variant* rather than a `hyps` field on
/// `Proved`, and that is deliberate. `Proved` means "this equation is derived,
/// full stop"; every existing consumer of [`TgCert::thm`] keeps exactly that
/// reading, and a rule that has not been taught about assumptions cannot
/// silently treat a conditional derivation as an unconditional one — the
/// compiler makes it say what it does with the new variant. The cardinal rule
/// ("never return `Proved` for a theorem not matched against the claim") is
/// therefore still checkable by reading the `Proved` sites alone.
#[derive(Debug)]
pub enum TgCert {
    /// A genuine derivation of `⟦a⟧ = ⟦b⟧`.
    Proved(Thm),
    /// A genuine derivation of `⊢ (h₁ ∧ … ∧ hₙ) → ⟦a⟧ = ⟦b⟧`, `n ≥ 1`.
    ///
    /// The theorem is complete — nothing here is asserted — but the *claim* the
    /// checker made is the bare equation, so until every `hᵢ` is discharged this
    /// is a step taken on trust. See [`escape_report`]: a conditional
    /// certificate that is never handed back to a rule is counted and reported
    /// as a gap.
    Conditional {
        /// Literally `⊢ conj(hyps) → ⟦a⟧ = ⟦b⟧`; checked on construction.
        thm: Thm,
        /// The assumption atoms, in the order the left-nested conjunction
        /// `conj(R ++ [h]) = conj(R) ∧ h` puts them.
        hyps: Vec<Formula>,
    },
    /// A step that was taken on trust, tagged with why.
    Admitted(&'static str),
}

/// Cloning a conditional certificate creates a *second* obligation, and the
/// escape ledger counts copies, not derivations: a copy that is stored in one of
/// the checker's caches and a copy that is handed back as an answer are both
/// certificates that have to be accounted for. So the `Clone` impl is written
/// out rather than derived, in order to bump the counter.
impl Clone for TgCert {
    fn clone(&self) -> Self {
        match self {
            TgCert::Proved(t) => TgCert::Proved(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_conditional();
                CONDITIONAL_COPIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                TgCert::Conditional { thm: thm.clone(), hyps: hyps.clone() }
            }
            TgCert::Admitted(r) => TgCert::Admitted(r),
        }
    }
}

impl TgCert {
    /// The underlying theorem, if this step was actually proved **outright**.
    ///
    /// A conditional derivation deliberately answers `None` here: its theorem is
    /// not the equation, it is an implication, and a caller that has not been
    /// taught to discharge the antecedent must not be handed it.
    pub fn thm(&self) -> Option<&Thm> {
        match self {
            TgCert::Proved(t) => Some(t),
            TgCert::Conditional { .. } | TgCert::Admitted(_) => None,
        }
    }
    /// Whether this certificate is a complete, unconditional derivation.
    pub fn is_proved(&self) -> bool { matches!(self, TgCert::Proved(_)) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Conditional equations.
//
// The one obligation this backend cannot generally discharge is a *typing*
// one: `beta_conditional_n` needs `⟦a⟧ ∈ ⟦A⟧` for the binder's domain, and
// `domain_premise` knows only two instances of it. Rather than admit the step,
// the premise is recorded as a genuine antecedent and carried: every rule below
// merges its premises' assumption sets and lifts its equality reasoning through
// the conjunction, and at a λ binder the assumption about that binder's own
// variable is discharged into `lam_ext_n`'s pointwise premise.
//
// Nothing here is trusted. A `CondEq` is checked on construction to be exactly
// `⊢ conj(hyps) → (a = b)`, so a rule that mangles the assumption list produces
// `None` — hence a reported gap — rather than a certificate that claims more
// than it proves.
// ─────────────────────────────────────────────────────────────────────────────

/// A derivation of an equation together with the assumptions it rests on:
/// `thm` is literally `⊢ (h₁ ∧ … ∧ hₙ) → a = b`, or `⊢ a = b` when `hyps` is
/// empty.
///
/// The conjunction is **left-nested**, so `conj(R ++ [h]) = conj(R) ∧ h` and
/// [`derived::uncurry`] peels the last assumption off — which is what the
/// discharge at a binder needs.
#[derive(Debug, Clone)]
struct CondEq {
    thm: Thm,
    hyps: Vec<Formula>,
}

impl CondEq {
    /// Check `thm` really is `⊢ conj(hyps) → (a = b)` and package the two.
    ///
    /// This is the only constructor, so no `CondEq` anywhere can misdescribe its
    /// own assumptions.
    fn new(thm: Thm, hyps: Vec<Formula>) -> Option<CondEq> {
        match conj_of(&hyps) {
            None => {
                thm.concl().as_eq()?;
            }
            Some(h) => {
                let (ante, concl) = thm.concl().as_imp()?;
                if ante != h {
                    return None
                }
                concl.as_eq()?;
            }
        }
        Some(CondEq { thm, hyps })
    }

    /// An unconditional derivation.
    fn plain(thm: Thm) -> Option<CondEq> { CondEq::new(thm, Vec::new()) }

    /// `⊢ t = t`.
    fn refl(t: Term) -> CondEq { CondEq { thm: Thm::eq_refl(t), hyps: Vec::new() } }

    /// The equation derived, under the assumptions.
    fn as_eq(&self) -> Option<(Term, Term)> { u_as_eq(&self.thm, conj_of(&self.hyps).as_ref()) }

    /// Whether this derivation is of the equation `l = r`.
    fn proves(&self, l: &Term, r: &Term) -> bool { self.as_eq() == Some((l.clone(), r.clone())) }
}

/// `h₁ ∧ … ∧ hₙ`, left-nested; `None` for the empty list.
fn conj_of(hyps: &[Formula]) -> Option<Formula> {
    let mut it = hyps.iter();
    let first = it.next()?.clone();
    Some(it.fold(first, |acc, h| Formula::and(acc, h.clone())))
}

/// `⊢ conj(hyps) → hyps[i]`, by peeling conjuncts off the left-nested form.
fn conj_proj(hyps: &[Formula], i: usize) -> Option<Thm> {
    let n = hyps.len();
    if i >= n {
        return None
    }
    // `cur : ⊢ conj(hyps) → conj(hyps[..k])`, starting at `k = n` with
    // reflexivity and shedding one conjunct at a time.
    let mut cur = derived::imp_refl(conj_of(hyps)?);
    let mut k = n;
    while k > i + 1 {
        let (prefix, last) = (conj_of(&hyps[..k - 1])?, hyps[k - 1].clone());
        cur = derived::syl(&cur, &derived::and_left(prefix, last))?;
        k -= 1;
    }
    if i == 0 {
        // `conj(hyps[..1])` *is* `hyps[0]`.
        return Some(cur)
    }
    derived::syl(&cur, &derived::and_right(conj_of(&hyps[..i])?, hyps[i].clone()))
}

/// Re-state `⊢ conj(from) → φ` as `⊢ conj(to) → φ`, where every assumption of
/// `from` also occurs in `to`.
///
/// This is what lets two derivations with different assumption sets be combined:
/// both are re-stated under the merged set first. It is also how assumptions get
/// *reordered*, which the discharge at a binder needs — the one being discharged
/// has to be last.
fn reassume(thm: &Thm, from: &[Formula], to: &[Formula]) -> Option<Thm> {
    if from == to {
        return Some(thm.clone())
    }
    let Some(h) = conj_of(to) else {
        // Nothing to assume: only an already-unconditional theorem qualifies.
        return from.is_empty().then(|| thm.clone())
    };
    if from.is_empty() {
        return Some(derived::a1i(thm, h))
    }
    // `⊢ conj(to) → conj(from)`, built conjunct by conjunct in `from`'s order,
    // which reproduces `from`'s own left-nesting.
    let mut acc: Option<Thm> = None;
    for f in from {
        let p = conj_proj(to, to.iter().position(|g| g == f)?)?;
        acc = Some(match acc {
            None => p,
            Some(a) => derived::hyp_and(&a, &p)?,
        });
    }
    derived::syl(&acc?, thm)
}

/// The union of two assumption lists, `a`'s order first.
fn merge_hyps(a: &[Formula], b: &[Formula]) -> Vec<Formula> {
    let mut out = a.to_vec();
    for h in b {
        if !out.contains(h) {
            out.push(h.clone());
        }
    }
    out
}

// The `u_*` family: the equality toolkit of `derived`, repeated "under an
// assumption". `h = None` is the unconditional case and each function then
// coincides with its `derived` original; `h = Some(H)` works inside `⊢ H → …`,
// where `a1i` weakens and `hyp_mp` is modus ponens. Writing them this way means
// every rule below has exactly one code path, so the conditional case cannot
// drift from the unconditional one.

/// `⊢ φ` ↦ `⊢ H → φ`.
fn u_a1i(thm: &Thm, h: Option<&Formula>) -> Thm {
    match h {
        None => thm.clone(),
        Some(h) => derived::a1i(thm, h.clone()),
    }
}

/// From `⊢ H → (φ → ψ)` and `⊢ H → φ` infer `⊢ H → ψ`.
fn u_mp(imp: &Thm, arg: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => Thm::mp(imp, arg),
        Some(_) => derived::hyp_mp(imp, arg),
    }
}

/// The equation `⊢ H → (a = b)` concludes — and `None` unless the antecedent is
/// literally `H`, so a theorem assuming something else cannot be mistaken for
/// one assuming this.
fn u_as_eq(thm: &Thm, h: Option<&Formula>) -> Option<(Term, Term)> {
    match h {
        None => thm.concl().as_eq(),
        Some(h) => {
            let (ante, concl) = thm.concl().as_imp()?;
            (ante == *h).then_some(())?;
            concl.as_eq()
        }
    }
}

/// Transitivity under an assumption. `derived::eq_trans`, threaded.
fn u_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b1) = u_as_eq(ab, h)?;
    let (b2, c) = u_as_eq(bc, h)?;
    if b1 != b2 {
        return None
    }
    let x = env.fresh_var();
    // ⊢ b = c → (a = b → a = c)
    let leib = Thm::eq_leibniz(b1, c, x, Formula::eq(a, Term::var(x)));
    let step = u_mp(&u_a1i(&leib, h), bc, h)?;
    u_mp(&step, ab, h)
}

/// Symmetry under an assumption. `derived::eq_symm`, threaded.
fn u_eq_symm(env: &mut Env, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    let x = env.fresh_var();
    // ⊢ a = b → (a = a → b = a)
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(a), h), h)
}

/// Congruence in one argument, under an assumption. `derived::congr_arg`.
fn u_congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    if args.get(idx) != Some(&a) {
        return None
    }
    let lhs = Term::apply(f, args.to_vec());
    let x = env.fresh_var();
    let mut hole = args.to_vec();
    hole[idx] = Term::var(x);
    let leib = Thm::eq_leibniz(a, b, x, Formula::eq(lhs.clone(), Term::apply(f, hole)));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(lhs), h), h)
}

/// Congruence in every argument, under an assumption. `derived::congr`.
fn u_congr(env: &mut Env, f: FnSym, eqs: &[Thm], h: Option<&Formula>) -> Option<Thm> {
    let mut args: Vec<Term> = Vec::with_capacity(eqs.len());
    for e in eqs {
        args.push(u_as_eq(e, h)?.0);
    }
    if args.len() != f.arity() as usize {
        return None
    }
    let mut acc = u_a1i(&Thm::eq_refl(Term::apply(f, args.clone())), h);
    for (i, e) in eqs.iter().enumerate() {
        let step = u_congr_arg(env, f, &args, i, e, h)?;
        args[i] = u_as_eq(e, h)?.1;
        acc = u_eq_trans(env, &acc, &step, h)?;
    }
    Some(acc)
}

/// How many assumptions a certificate may accumulate before the derivation is
/// abandoned and a gap reported instead.
///
/// A pure cost guard. Every combination re-states both premises under the
/// merged assumption set, which costs one projection per assumption, so an
/// unbounded set would make a long transitivity chain quadratic. Nothing is unsound about a larger bound; a
/// chain that hits it reports `too many undischarged assumptions`, which is
/// visible in the coverage report.
const MAX_HYPS: usize = 12;

// ─────────────────────────────────────────────────────────────────────────────
// The shared prelude.
//
// `Apply::new` and `least_universe` are the same derivation every time — they
// take no input beyond a fresh `Env` — but together they cost ~10ms, and a
// `TgBackend` is created per declaration. Building them once per thread and
// replaying the result is therefore worth it.
//
// Replaying is sound because an `Env` is *only* a pair of counters: it records
// no signature, so a theorem proved against one `Env` is a theorem, full stop.
// All that must be arranged is that a fresh `Env` never re-issues a symbol or
// variable the prelude already used, which `fast_forward` does by burning the
// same number of ids. `FnSym::id`/`FreeVar::id` make the counts observable.
//
// The same argument is what lets [`Shared`] carry one `Env` for every backend
// on the thread, which is why `fast_forward` now runs once per thread rather
// than once per declaration.
// ─────────────────────────────────────────────────────────────────────────────

/// The once-per-thread part of the interpretation's machinery.
struct Prelude {
    /// Set-theoretic application, and everything it is built from.
    ap: Apply,
    /// The least-universe operator `U`.
    u_sym: FnSym,
    /// `⊢ ∀x. x ∈ U(x)`.
    mem_u: Thm,
    /// The function-space operator `fs`, i.e. `fs(a,b) = b^a`.
    fs_sym: FnSym,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    fs_in_u: Thm,
    /// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))`.
    fs_cong: Thm,
    /// How many function symbols and free variables the above consumed.
    n_syms: u32,
    n_vars: u32,
}

thread_local! {
    static PRELUDE: std::cell::RefCell<Option<Rc<Prelude>>> =
        const { std::cell::RefCell::new(None) };
}

fn prelude() -> Rc<Prelude> {
    PRELUDE.with(|slot| {
        if let Some(p) = slot.borrow().as_ref() {
            return p.clone()
        }
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("TG prelude: the application machinery is closed");
        // The whole function-space development, which *includes* the least
        // universe: `U` has to be the same symbol in `⊢ ∀x. x ∈ U(x)` and in
        // `⊢ ∀a. fs(a,a) ∈ U(a)`, or the two facts would be about different
        // operators and the beta path could use only one of them.
        let dev = derived::funspace::Development::new(&mut env).expect("TG prelude: the function-space development");
        let (u_sym, mem_u) = (dev.space.lu, dev.space.mem_lu.clone());
        let (fs_sym, fs_in_u) = (dev.funspace.fs, dev.in_universe.clone());
        let fs_cong = derived::ext::fs_cong(&mut env, &dev.funspace).expect("TG prelude: function-space congruence");
        // One extra of each, purely to read the counters back out.
        let n_syms = env.declare(0).id() + 1;
        let n_vars = env.fresh_var().id() + 1;
        let p = Rc::new(Prelude { ap, u_sym, mem_u, fs_sym, fs_in_u, fs_cong, n_syms, n_vars });
        *slot.borrow_mut() = Some(p.clone());
        p
    })
}

/// Advance a fresh `Env` past every id the prelude used.
fn fast_forward(env: &mut Env, p: &Prelude) {
    for _ in 0..p.n_syms {
        env.declare(0);
    }
    for _ in 0..p.n_vars {
        env.fresh_var();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The n-ary lambda graph.
//
// `derived::funcs::lambda`/`beta_conditional` take a *unary* body symbol. The
// skeleton decomposition described in the module docs produces a body symbol
// with `k` extra parameters, so the two constructions are repeated here in
// parameterised form. They are line-for-line the derived originals with the
// prefix `p⃗` threaded through `t`'s and `lam`'s argument lists; at `k = 0` they
// reduce to exactly the derived versions.
//
// Nothing here is trusted: like everything outside `kernel/`, these can only
// reach a `Thm` through the kernel's primitive rules, so a mistake yields a
// `None` (hence a reported gap) rather than a false theorem. The shapes are
// asserted at the end of each function all the same.
// ─────────────────────────────────────────────────────────────────────────────

/// The graph `lam(p⃗, A) = { ⟨x, t(p⃗, x)⟩ : x ∈ A }`, with
/// `⊢ ∀p⃗ ∀A ∀y. (y ∈ lam(p⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(p⃗,x)⟩))`.
///
/// The `k = 0` case is [`derived::funcs::lambda`].
fn lambda_n(env: &mut Env, ap: &Apply, t: FnSym) -> Option<(FnSym, Thm)> {
    let k = (t.arity() as usize).checked_sub(1)?;
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (t_a, tx) = (Term::var(av), Term::var(x));

    let mut targs = pts.clone();
    targs.push(tx.clone());
    let pair = ap.sets.pair(tx.clone(), Term::apply(t, targs));

    let (y, phi, exu) = derived::exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = derived::inst_all(&repl, std::slice::from_ref(&t_a))?;
    let premise = Thm::gen(x, &derived::a1i(&exu, Formula::mem(tx.clone(), t_a.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, t_a), phi));
    let mut params = ps;
    params.push(av);
    derived::define_by_membership(env, &params, &img, y, &cond)
}

/// `⊢ ∀p⃗ ∀A ∀a. (a ∈ A → app(lam(p⃗,A), a) = t(p⃗,a))` — beta reduction.
///
/// The `k = 0` case is [`derived::funcs::beta_conditional`]; see there for the
/// argument. Only the argument lists of `t` and `lam` differ.
fn beta_conditional_n(env: &mut Env, ap: &Apply, t: FnSym, lam: FnSym, lam_ax: &Thm) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and,
        hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, singleton, syl,
    };

    let k = (t.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, a, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t_a, ta, tx, ty) = (Term::var(av), Term::var(a), Term::var(x), Term::var(y));

    // `t(p⃗, ·)` and `lam(p⃗, ·)`, the only places the extra parameters show up.
    let t_at = |arg: Term| {
        let mut v = pts.clone();
        v.push(arg);
        Term::apply(t, v)
    };
    let lam_t = {
        let mut v = pts.clone();
        v.push(t_a.clone());
        Term::apply(lam, v)
    };
    let lam_inst = |thm: &Thm, extra: &[Term]| {
        let mut v = pts.clone();
        v.extend_from_slice(extra);
        inst_all(thm, &v)
    };

    let val = t_at(ta.clone()); // t(p⃗, a)
    let tx_val = t_at(tx.clone()); // t(p⃗, x)
    let h = Formula::mem(ta.clone(), t_a.clone()); // a ∈ A

    let pair_ay = ap.sets.pair(ta.clone(), ty.clone());
    let pair_aval = ap.sets.pair(ta.clone(), val.clone());
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone());

    // ── ⟨a,t(a)⟩ ∈ lam(A), by taking x := a in the image condition ───────────
    let lam_at_val = lam_inst(lam_ax, &[t_a.clone(), pair_aval.clone()])?;
    let body_val = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_aval.clone(), pair_x.clone()));
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(pair_aval.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(x, body_val, ta.clone())?)?;
    let h_in_lam = syl(&h_ex, &iff_mpr(&lam_at_val)?)?;

    // ── The collection is inhabited, so `coll_ax` applies ────────────────────
    let mem_pair_y = Formula::mem(pair_ay.clone(), lam_t.clone());
    let h_ne = syl(&h_in_lam, &exists_intro_imp(y, mem_pair_y.clone(), val.clone())?)?;
    let coll_here = inst_all(&ap.coll_ax, &[lam_t.clone(), ta.clone()])?;
    let h_coll = syl(&h_ne, &coll_here)?;

    // ── ⟨a,y⟩ ∈ lam(A) ↔ y = t(a) ────────────────────────────────────────────
    let eq_y_val = Formula::eq(ty.clone(), val.clone());
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(w)), lam_t.clone()),
    );
    let bwd = syl(&h_in_lam, &com12(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &carry)?)?)?;

    let lam_at_y = lam_inst(lam_ax, &[t_a.clone(), pair_ay.clone()])?;
    let kf = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let k_eq = and_right(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let inj = inst_all(&ap.pair_inj, &[ta.clone(), ty.clone(), tx.clone(), tx_val.clone()])?;
    let k_conj = syl(&k_eq, &inj)?;
    let (e_ax, e_yt) = (Formula::eq(ta.clone(), tx.clone()), Formula::eq(ty.clone(), tx_val.clone()));
    let k_ax = syl(&k_conj, &and_left(e_ax.clone(), e_yt.clone()))?;
    let k_ytx = syl(&k_conj, &and_right(e_ax, e_yt))?;
    let w2 = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(ta.clone(), tx.clone(), w2, Formula::eq(val.clone(), t_at(Term::var(w2)))),
        &Thm::eq_refl(val.clone()),
    )?;
    let k_txta = syl(&syl(&k_ax, &congr)?, &eq_symm_imp(env, val.clone(), tx_val.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(tx_val.clone(), val.clone(), w3, Formula::eq(ty.clone(), Term::var(w3)));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&carry2, kf), &k_txta)?, &k_ytx)?;
    let fwd = syl(&iff_mp(&lam_at_y)?, &exists_elim_imp(x, &Thm::gen(x, &k_goal), &eq_y_val)?)?;

    // ── coll(lam(A), a) and {t(a)} have the same members ─────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(lam_t.clone(), ta.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let coll_at_y = Formula::forall(y, Formula::iff(mem_yc.clone(), mem_pair_y));
    let h_iff_y = syl(&h_coll, &Thm::ax_inst(coll_at_y, ty.clone())?)?;
    let (h_c_lam, h_lam_c) = (hyp_iff_mp(&h_iff_y)?, hyp_iff_mpr(&h_iff_y)?);
    let h_c_sing = hyp_syl(&hyp_syl(&h_c_lam, &a1i(&fwd, h.clone()))?, &a1i(&iff_mpr(&ms)?, h.clone()))?;
    let h_sing_c = hyp_syl(&hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &bwd)?, &h_lam_c)?;
    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let h_same = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── app(lam(A),a) = ⋃coll = ⋃{t(a)} = t(a) ───────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_term = ap.apply(lam_t.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[lam_t, ta.clone()])?;
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, Formula::eq(app_term, val)) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(a);
    Some(gen_all(&all, &out))
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(p⃗,x) = t'(q⃗,x))) → lam(p⃗,A) = lam'(q⃗,A')))`
/// — lambda graph extensionality, with a parameter prefix on each side.
///
/// The `k = k' = 0` case is [`derived::ext::lam_ext`], and this is that
/// derivation with the two prefixes threaded through the argument lists of
/// `t`/`lam` and `t2`/`lam2`. Nothing else changes: the argument never takes
/// those terms apart, it only quotes them, so the extra parameters ride along
/// untouched. The prefixes need not have the same length — the two lambdas
/// being compared have independent skeletons.
///
/// As everywhere outside `kernel/`, a mistake here can only produce `None`, and
/// hence a reported gap. The final shape is checked regardless.
#[allow(clippy::too_many_arguments)]
fn lam_ext_n(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    t2: FnSym,
    lam2: FnSym,
    lam2_ax: &Thm,
) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp,
        iff_mp, iff_mpr, inst_all, syl, uncurry,
    };

    let k = (t.arity() as usize).checked_sub(1)?;
    let k2 = (t2.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 || lam2.arity() as usize != k2 + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..k2).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, av2, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    /// `f(prefix⃗, arg)`.
    fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
        let mut v = prefix.to_vec();
        v.push(arg);
        Term::apply(f, v)
    }
    /// The instantiation list `prefix⃗, A, y` for a graph's characteristic axiom.
    fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
        let mut v = prefix.to_vec();
        v.push(a.clone());
        v.push(b.clone());
        v
    }

    let lam_t = at(lam, &pts, ta.clone()); // lam(p⃗, A)
    let lam2_t = at(lam2, &qts, ta2.clone()); // lam'(q⃗, A')
    let val1 = at(t, &pts, tx.clone()); // t(p⃗, x)
    let val2 = at(t2, &qts, tx.clone()); // t'(q⃗, x)
    let pair1 = ap.sets.pair(tx.clone(), val1.clone()); // ⟨x, t(p⃗,x)⟩
    let pair2 = ap.sets.pair(tx.clone(), val2.clone()); // ⟨x, t'(q⃗,x)⟩

    // The two hypotheses, and their conjunction `H`.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(Formula::mem(tx.clone(), ta.clone()), Formula::eq(val1.clone(), val2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let eq_y1 = Formula::eq(ty.clone(), pair1.clone());
    let eq_y2 = Formula::eq(ty.clone(), pair2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), lam_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), lam2_t.clone());

    // Both characteristic axioms must have exactly the shape `lambda_n` gives,
    // or the derivation below would be about the wrong sets. Checked, not
    // `debug_assert`ed: this runs in release.
    let lam_at_y = inst_all(lam_ax, &inst2(&pts, &ta, &ty))?;
    if *lam_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let lam2_at_y = inst_all(lam2_ax, &inst2(&qts, &ta2, &ty))?;
    if *lam2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of lam(p⃗,A) is a member of lam'(q⃗,A') ─────────────
    let k_f = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    let k_tt = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k_f.clone()), &k_dom)?, &k_xa)?;
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(
        val1.clone(),
        val2.clone(),
        w2,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w2))),
    );
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k_f), &k_tt)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    let fwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?), &Formula::imp(h.clone(), ex2.clone()))?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&lam2_at_y)?, h.clone()),
    )?;

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_tt = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_tt_symm = syl(&j_tt, &eq_symm_imp(env, val1.clone(), val2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(
        val2.clone(),
        val1.clone(),
        w4,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w4))),
    );
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j), &j_tt_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?), &Formula::imp(h.clone(), ex1.clone()))?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&lam_at_y)?, h.clone()),
    )?;

    // ── Same members, hence equal ───────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(&Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?, &Thm::gen(y, &h_iff))?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[lam_t.clone(), lam2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(lam_t, lam2_t))) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    all.push(av2);
    Some(gen_all(&all, &out))
}

/// The function symbols the interpretation uses that carry *no* axioms.
///
/// All are introduced by signature extension; that is sound but limiting, and
/// it is why the rules over them (`pi_cong`, `zeta`, …) stay in the equational
/// fragment. `sort`, `lam` and `app` are *not* here: those three are now real
/// definitional extensions, held in [`Prelude`] and [`Shared::lam_infos`].
#[derive(Clone, Copy)]
struct Syms {
    /// Sorts whose level is not a literal successor tower.
    sort: FnSym,
    pi: FnSym,
    let_: FnSym,
    proj: FnSym,
    /// Lean's de Bruijn indices. A Lean expression is already de Bruijn and
    /// hash-consed, so alpha-equivalent Lean terms are pointer-equal and map to
    /// syntactically equal kernel terms; a per-index symbol therefore suffices
    /// and no binding structure need be reproduced on the kernel side.
    bvar: FnSym,
    /// Universe levels.
    lzero: FnSym,
    lsucc: FnSym,
    lmax: FnSym,
    limax: FnSym,
    /// Index encodings for `bvar`, `proj` and level/name parameters.
    idx: FnSym,
    /// `⟦Sort 0⟧`, the base of the universe tower.
    sort0: FnSym,
}

/// Everything known about one lambda *skeleton*. Shared by every lambda whose
/// body has that shape.
struct LamInfo {
    /// The head symbol of the interpretation, `lam_C(h⃗, A)`.
    lam: FnSym,
    /// The graph machinery, when it was built; `None` for the inert encoding,
    /// in which case `lam` is an opaque symbol and beta over this lambda
    /// reports a gap. Every skeleton gets a graph now — there is no hole-count
    /// cut-off — so the `None` case is the construction refusing, which it does
    /// not do on any corpus measured.
    graph: Option<Graph>,
}

/// The definitional-extension half of a lambda skeleton.
struct Graph {
    /// The body function `t(h⃗, x)`.
    t: FnSym,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    t_def: Thm,
    /// `⊢ ∀h⃗ ∀A ∀y. (y ∈ lam(h⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(h⃗,x)⟩))`.
    lam_ax: Thm,
}

// ─────────────────────────────────────────────────────────────────────────────
// There is no cut-off on the hole count.
//
// There used to be one — `MAX_HOLES = 8` — because a skeleton's graph cost
// ~130µs to derive and `good/init-prelude.ndjson` reached some 32k distinct
// skeletons, so building them all added ~13s to the run. Sharing the signature
// across the thread's backends (see [`Shared`]) collapsed those 32388 skeletons
// to 2651 — the same shapes, now recognised as the same — and the graph
// construction with them, from 2.3s to 0.66s.
//
// So the cap is gone, and with it the entire `beta: the lambda's graph … was
// not built` category: 1228 gaps on `init-prelude` and 24 over the tutorials
// before, zero now. Measured on `good/init-prelude.ndjson`, with the tutorial
// totals beside it — all with the shared signature, so the first row is *not*
// the old baseline, which was 5.4s for the same 18025 gaps:
//
// | cut-off | prelude gaps | prelude runtime | not built | tutorial gaps |
// |--------:|-------------:|----------------:|----------:|--------------:|
// | 8       | 18025        | 2.7 s           | 1228      | 586           |
// | 16      | 16830        | 3.2 s           | 493       | 567           |
// | 32      | 16301        | 4.0 s           | 205       | 542           |
// | 64      | 16199        | 5.1 s           | 108       | 538           |
// | 128     | 16061        | 6.8 s           | 26        | 538           |
// | none    | 16009        | 8.8 s           | 0         | 538           |
//
// The hole distribution says no finite value could ever have been principled.
// Over `init-prelude`'s 2651 skeletons: 1% need no hole at all, 34% need 1–4,
// 22% need 5–8, 21% need 9–16, 14% need 17–32, 6% need 33–64, and 3% need more
// than 64 — a tail that thins but does not stop, reaching past 128. Every cap
// is a bet on the corpus.
//
// What removing it costs — 8.8s against 2.7s — is *not* graph construction, and
// that is the reason it is no longer guarded. A beta step instantiates a lemma
// whose formula grows with the hole count, one quantifier at a time, so a redex
// over a `k`-hole lambda costs O(k²) inside the kernel's `open`/`close`; a perf
// profile of the uncapped run puts ~40% of its samples in `Term::new`,
// `Term::open` and the allocator beneath them, and `beta_step` accounts for 3.8s
// of the 8.8s against 0.7s for every graph in the run. That is the derivation
// the checker exists to produce, not a mitigation for producing it slowly.
// ─────────────────────────────────────────────────────────────────────────────

/// Where one particular lambda *occurrence* sits: which skeleton it uses, and
/// with what arguments.
struct LamSite {
    /// Key into [`Shared::lam_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

// ─────────────────────────────────────────────────────────────────────────────
// The shared signature.
//
// A `TgBackend` is built per declaration, but the *signature* it builds terms
// in has no reason to be per declaration. A lambda skeleton is a property of
// the body's shape, and the same shapes recur in declaration after
// declaration — but when every backend has its own `Env`, the symbols standing
// for `app`, `proj`, the bound-variable slot and the enclosing lambdas are
// different symbols each time, so two occurrences of one shape produce two
// *different* skeleton terms and the graph is derived twice. Measured on
// `good/init-prelude.ndjson`: 32388 distinct skeleton terms for 1566 distinct
// shapes, a factor of 20 of pure repetition.
//
// Sharing one `Env` across the thread's backends makes those terms literally
// equal, so a shape's graph is derived once for the whole run: 32388 skeletons
// become 2651, and the graph construction drops from 2.3s to 0.66s. Coverage is
// unchanged to the gap — the derivations are the same derivations, and nothing
// about what one declaration can prove depends on another.
//
// Only the *signature* and what is keyed on it moves. `parts`, `consts`,
// `exprs`, `locals` and the rest stay per declaration: they are keyed by Lean
// nodes whose identity is per declaration, and they are not what makes
// skeletons differ — everything in a body that does not mention the binder is
// abstracted into a hole, so a skeleton contains only `app`/`proj`/`Π`
// structure, the canonical variables, and the graph symbols of nested lambdas.
//
// Sharing is sound for the same reason the [`Prelude`] replay is: an `Env` is
// only a pair of counters, so one shared `Env` issues *fewer* colliding names
// than several independent ones, never more.
//
// It does mean those counters now run for the whole check rather than being
// reset per declaration. `init-prelude` ends at 40264 symbols and 463129
// variables for 2059 declarations — about 225 variables each — against a `u32`
// each. A development three orders of magnitude larger would approach the
// variable limit, and the kernel's counters are `checked_add`, so that is a
// panic rather than an aliased variable. The remedy, if it is ever needed, is
// to drop `SHARED` and start a fresh one: nothing outside it depends on it
// persisting, and the only cost of recycling is re-deriving the graphs.
// ─────────────────────────────────────────────────────────────────────────────

/// The per-thread signature, and the derivations keyed on it.
struct Shared {
    /// The kernel signature and variable source, shared by every backend on
    /// this thread so that equal skeletons are equal *terms*.
    env: Env,
    /// The axiom-free interpretation symbols; copied into each backend.
    syms: Syms,
    /// Canonical variables for skeletons, so that two lambdas with the same
    /// body shape produce the *same* key. Reused across skeletons: they are
    /// abstracted away by `define_abbrev` immediately and never escape.
    hole_vars: Vec<FreeVar>,
    x_canon: FreeVar,
    /// Head symbol (and, when built, graph machinery) per distinct skeleton.
    lam_infos: HashMap<Term, Rc<LamInfo>>,
    /// Beta theorems, derived lazily: most lambdas are never a redex head.
    lam_betas: HashMap<Term, Option<Thm>>,
    /// Graph-extensionality theorems, keyed by the *pair* of skeletons being
    /// related. Derived lazily and shared: `lam_ext_n` is a full Extensionality
    /// derivation, and a development compares the same two body shapes over and
    /// over (once per occurrence, and again per `def_eq` call).
    lam_exts: HashMap<(Term, Term), Option<Thm>>,
}

thread_local! {
    static SHARED: std::cell::RefCell<Option<Rc<std::cell::RefCell<Shared>>>> =
        const { std::cell::RefCell::new(None) };
}

/// The thread's shared signature, created on first use.
fn shared(pre: &Prelude) -> Rc<std::cell::RefCell<Shared>> {
    SHARED.with(|slot| {
        if let Some(s) = slot.borrow().as_ref() {
            return s.clone()
        }
        let mut env = Env::new();
        fast_forward(&mut env, pre);
        let syms = Syms {
            sort: env.declare(1),
            pi: env.declare(2),
            let_: env.declare(3),
            proj: env.declare(2),
            bvar: env.declare(1),
            lzero: env.declare(0),
            lsucc: env.declare(1),
            lmax: env.declare(2),
            limax: env.declare(2),
            idx: env.declare(1),
            sort0: env.declare(0),
        };
        let x_canon = env.fresh_var();
        let sh = Rc::new(std::cell::RefCell::new(Shared {
            env,
            syms,
            hole_vars: Vec::new(),
            x_canon,
            lam_infos: HashMap::new(),
            lam_betas: HashMap::new(),
            lam_exts: HashMap::new(),
        }));
        *slot.borrow_mut() = Some(sh.clone());
        sh
    })
}

/// The Tarski–Grothendieck backend.
pub struct TgBackend<'x, 't: 'x, 'p: 't> {
    /// The signature, and everything keyed on it, shared per thread.
    shared: Rc<std::cell::RefCell<Shared>>,
    /// The application machinery and the universe operator, shared per thread.
    pre: Rc<Prelude>,
    /// The checker's declaration environment, used to resolve a constant to its
    /// value so that `⟦c⟧` can be an *explicit definition* rather than an opaque
    /// symbol. This is what makes delta reduction justifiable at all.
    decls: &'x crate::env::Env<'x, 't>,
    /// Defining equations `⊢ ⟦c⟧ = ⟦value⟧`, keyed by the constant's expression
    /// node. Delta certificates are built from these by congruence.
    const_defs: HashMap<ExprPtr<'t>, Thm>,
    /// Defining equations `⊢ ⟦let …⟧ = ⟦body[val/x]⟧`, keyed by the `Let` node.
    /// Zeta reduction is exactly this equation.
    let_defs: HashMap<ExprPtr<'t>, Thm>,
    syms: Syms,
    /// Interpretation cache. Without it, interpreting nested expressions would
    /// be quadratic; with it, each hash-consed Lean node is translated once.
    exprs: HashMap<ExprPtr<'t>, Term>,
    levels: HashMap<LevelPtr<'t>, Term>,
    /// One representative per level-equivalence class, so that levels the
    /// checker considers equal interpret to identical terms.
    level_reps: Vec<LevelPtr<'t>>,
    /// Memoised class lookup.
    level_canon: HashMap<LevelPtr<'t>, LevelPtr<'t>>,
    /// Per-name and per-index constants, allocated on demand.
    consts: HashMap<NamePtr<'t>, FnSym>,
    /// Lean local ids to kernel free variables. Allocated through `Env` rather
    /// than derived from the Lean id: the derived rules mint fresh variables for
    /// Leibniz holes, and a collision between such a hole and a Lean local would
    /// substitute at the wrong occurrences — a genuine soundness bug, not just a
    /// wrong answer.
    locals: HashMap<u64, kernel::FreeVar>,
    params: HashMap<NamePtr<'t>, Term>,
    idxs: HashMap<u64, Term>,

    /// The applicative structure of every term this backend built. The kernel
    /// does not expose `Term`'s constructors for reading, and the skeleton
    /// decomposition has to take terms apart, so the shape is recorded on the
    /// way in.
    parts: HashMap<Term, (FnSym, Vec<Term>)>,
    /// Where each lambda occurrence sits.
    lam_sites: HashMap<ExprPtr<'t>, LamSite>,
    /// A copy of the shared canonical bound-variable slot, so that the common
    /// read-only use needs no borrow.
    x_canon: FreeVar,

    _marker: PhantomData<&'p ()>,
}

impl<'x, 't: 'x, 'p: 't> TgBackend<'x, 't, 'p> {
    /// A backend for one declaration, over the thread's shared signature.
    pub fn new(decls: &'x crate::env::Env<'x, 't>) -> Self {
        let pre = prelude();
        let shared = shared(&pre);
        let (syms, x_canon) = {
            let sh = shared.borrow();
            (sh.syms, sh.x_canon)
        };
        TgBackend {
            shared,
            pre,
            decls,
            const_defs: HashMap::new(),
            let_defs: HashMap::new(),
            syms,
            exprs: HashMap::new(),
            levels: HashMap::new(),
            level_reps: Vec::new(),
            level_canon: HashMap::new(),
            consts: HashMap::new(),
            locals: HashMap::new(),
            params: HashMap::new(),
            idxs: HashMap::new(),
            parts: HashMap::new(),
            lam_sites: HashMap::new(),
            x_canon,
            _marker: PhantomData,
        }
    }

    /// The shared signature, for the duration of one statement.
    ///
    /// Every use is deliberately short-lived: holding this across a call that
    /// itself reaches the shared state would panic on the re-entrant borrow.
    fn env_mut(&self) -> std::cell::RefMut<'_, Env> {
        std::cell::RefMut::map(self.shared.borrow_mut(), |s| &mut s.env)
    }

    /// Build `f(args)` and remember its shape, so that [`Self::skeleton`] can
    /// take it apart again later.
    fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        self.parts.entry(t.clone()).or_insert((f, args));
        t
    }

    /// Accept `eq` as a proof that `redex` and `reduct` are equal, but only
    /// after checking it really is that equation. Every rule that concludes
    /// something about two specific terms goes through this.
    fn check_against(
        &mut self,
        ctx: &mut <Self as Certifier>::Ctx,
        eq: Thm,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        what: &'static str,
    ) -> TgCert {
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *eq.concl() == kernel::Formula::eq(lhs, rhs) {
            self.proved(eq)
        } else if what == "zeta" {
            self.note_admit("zeta: derived equation does not match the reduction")
        } else {
            self.note_admit("derived equation does not match the reduction")
        }
    }

    /// Wrap a derived theorem, tallying it for the coverage report.
    fn proved(&mut self, t: Thm) -> TgCert {
        note_proved();
        TgCert::Proved(t)
    }

    /// Wrap a derivation together with whatever it still assumes.
    ///
    /// The single place a [`TgCert::Conditional`] is built. `CondEq`'s
    /// constructor has already checked that the theorem is literally
    /// `⊢ conj(hyps) → (a = b)`, so the assumptions recorded here are the
    /// theorem's real antecedents and not a label attached to it.
    fn cert(&mut self, c: CondEq) -> TgCert {
        if c.hyps.is_empty() {
            return self.proved(c.thm)
        }
        note_proved();
        note_conditional();
        MAX_ASSUMED.fetch_max(c.hyps.len() as u64, std::sync::atomic::Ordering::Relaxed);
        TgCert::Conditional { thm: c.thm, hyps: c.hyps }
    }

    /// Take a certificate handed to a rule, as a conditional equation.
    ///
    /// Every [`Certifier`] method that receives certificates calls this on each
    /// of them, whatever it then does with them — that is what keeps the escape
    /// ledger exact (see [`escape_report`]): a conditional certificate is
    /// accounted for the moment a rule takes it, so the ones left over are
    /// exactly the copies the checker consumed as an *answer*.
    fn consume(&mut self, c: &TgCert) -> Option<CondEq> {
        match c {
            TgCert::Proved(t) => CondEq::plain(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_consumed();
                CondEq::new(thm.clone(), hyps.clone())
            }
            TgCert::Admitted(_) => None,
        }
    }

    /// Transitivity, merging the two derivations' assumptions.
    fn ceq_trans(&mut self, ab: &CondEq, bc: &CondEq) -> Option<CondEq> {
        let hyps = merge_hyps(&ab.hyps, &bc.hyps);
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let x = reassume(&ab.thm, &ab.hyps, &hyps)?;
        let y = reassume(&bc.thm, &bc.hyps, &hyps)?;
        CondEq::new(u_eq_trans(&mut self.env_mut(), &x, &y, h.as_ref())?, hyps)
    }

    /// Symmetry, keeping the assumptions.
    fn ceq_symm(&mut self, ab: &CondEq) -> Option<CondEq> {
        let h = conj_of(&ab.hyps);
        CondEq::new(u_eq_symm(&mut self.env_mut(), &ab.thm, h.as_ref())?, ab.hyps.clone())
    }

    /// Congruence over `f`, merging every argument's assumptions.
    fn ceq_congr(&mut self, f: FnSym, cs: &[CondEq]) -> Option<CondEq> {
        let mut hyps: Vec<Formula> = Vec::new();
        for c in cs {
            hyps = merge_hyps(&hyps, &c.hyps);
        }
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let mut lifted = Vec::with_capacity(cs.len());
        for c in cs {
            lifted.push(reassume(&c.thm, &c.hyps, &hyps)?);
        }
        CondEq::new(u_congr(&mut self.env_mut(), f, &lifted, h.as_ref())?, hyps)
    }

    fn note_admit(&mut self, reason: &'static str) -> TgCert {
        // Tallied straight into the run totals rather than buffered and merged
        // on `Drop`: a `Drop` impl on the backend would make `TypeChecker`'s
        // borrow of its context live to the end of scope, which breaks callers
        // that legitimately reuse the context afterwards.
        merge_one(reason);
        TgCert::Admitted(reason)
    }

    /// A 0-ary "numeral" term standing for an index. These are opaque tags, not
    /// the primitive `ℕ` of milestone 4.
    fn idx_term(&mut self, i: u64) -> Term {
        if let Some(t) = self.idxs.get(&i) {
            return t.clone()
        }
        // Encoded as `idx` applied to itself i times over a base would be
        // linear in i; instead each distinct index gets its own nullary symbol,
        // which keeps interpretation O(1) per node.
        let s = self.env_mut().declare(0);
        let inner = self.mk(s, vec![]);
        let t = self.mk(self.syms.idx, vec![inner]);
        self.idxs.insert(i, t.clone());
        t
    }

    /// Interpret a universe level.
    ///
    /// The level is *simplified first*. The checker decides level equality with
    /// its own algebra (`eq_antisymm`), under which e.g. `imax 1 1` and `1` are
    /// equal; interpreting them naively would give syntactically different terms
    /// and turn a settled equality into an unprovable one. Normalising to the
    /// checker's canonical form keeps the two views in step, so equal levels map
    /// to identical terms and reflexivity discharges them.
    /// The canonical representative of `l`'s level-equivalence class.
    ///
    /// `simplify` is not a normal form: it settles neither commutativity,
    /// associativity, idempotence nor absorption of `max`, so `max u v` and
    /// `max v u` remain syntactically different while the checker rightly calls
    /// them equal. Rather than reimplement level algebra — `CLAUDE.md` puts
    /// levels in the translator, not the kernel — reuse the checker's own
    /// decision procedure and keep one representative per class.
    ///
    /// The scan is linear in the number of distinct classes, which is bounded by
    /// the development's universe vocabulary (tens, in practice) rather than its
    /// size.
    fn canon_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let l = ctx.simplify(l);
        if let Some(r) = self.level_canon.get(&l) {
            return *r
        }
        for rep in self.level_reps.clone() {
            if ctx.eq_antisymm(l, rep) {
                self.level_canon.insert(l, rep);
                return rep
            }
        }
        self.level_reps.push(l);
        self.level_canon.insert(l, l);
        l
    }

    /// Interpret a level structurally.
    ///
    /// Deliberately does **not** canonicalise: canonicalising here and then
    /// decomposing the representative can hand a sub-level back the whole level
    /// (absorption maps `succ u` to `max u (succ u)`, whose own sub-level is
    /// `succ u`), and the recursion never terminates. Canonicalisation happens
    /// once, at the dispatch point in [`Self::interp_sort`], where the shape
    /// choice actually matters.
    fn interp_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> Term {
        let l = ctx.simplify(l);
        if let Some(t) = self.levels.get(&l) {
            return t.clone()
        }
        let t = match ctx.read_level(l) {
            Level::Zero => self.mk(self.syms.lzero, vec![]),
            Level::Succ(a, _) => {
                let a = self.interp_level(ctx, a);
                self.mk(self.syms.lsucc, vec![a])
            }
            Level::Max(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.lmax, vec![a, b])
            }
            Level::IMax(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.limax, vec![a, b])
            }
            Level::Param(n, _) => {
                if let Some(t) = self.params.get(&n) {
                    t.clone()
                } else {
                    let s = self.env_mut().declare(0);
                    let t = self.mk(s, vec![]);
                    self.params.insert(n, t.clone());
                    t
                }
            }
        };
        self.levels.insert(l, t.clone());
        t
    }

    /// `⟦Sort l⟧`, climbing the universe tower.
    ///
    /// `⟦Sort 0⟧` is a constant and `⟦Sort (l+1)⟧ := U(⟦Sort l⟧)`, so
    /// `⊢ ∀x. x ∈ U(x)` immediately gives `⟦Sort l⟧ ∈ ⟦Sort (l+1)⟧`. Levels
    /// that are neither zero nor a successor (`max`, `imax`, a parameter) fall
    /// back to the opaque `sort` symbol: nothing is known about where they sit,
    /// which is honest, and the encoding stays injective on simplified levels so
    /// the `sort` rule is unaffected.
    fn interp_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>) -> Term {
        // Dispatch on the *canonical representative* of the level, not on its
        // raw shape. Otherwise `Sort (max u u)` takes the opaque branch while
        // the equal `Sort u` takes the universe-tower branch, and two equal
        // levels yield different terms — which is what made idempotence and
        // absorption unprovable.
        let l = self.canon_level(ctx, level);
        match ctx.read_level(l) {
            Level::Zero => self.mk(self.syms.sort0, vec![]),
            Level::Succ(a, _) => {
                let below = self.interp_sort(ctx, a);
                self.mk(self.pre.u_sym, vec![below])
            }
            _ => {
                let lt = self.interp_level(ctx, l);
                self.mk(self.syms.sort, vec![lt])
            }
        }
    }

    fn interp_levels(&mut self, ctx: &mut TcCtx<'t, 'p>, ls: LevelsPtr<'t>) -> Vec<Term> {
        ctx.read_levels(ls).iter().copied().collect::<Vec<_>>().into_iter().map(|l| self.interp_level(ctx, l)).collect()
    }

    /// The `i`-th canonical hole variable, allocating on demand.
    fn hole_var(&mut self, i: usize) -> FreeVar {
        let mut sh = self.shared.borrow_mut();
        while sh.hole_vars.len() <= i {
            let v = sh.env.fresh_var();
            sh.hole_vars.push(v);
        }
        sh.hole_vars[i]
    }

    /// The graph machinery for a skeleton, if that skeleton has been seen.
    fn lam_info(&self, key: &Term) -> Option<Rc<LamInfo>> { self.shared.borrow().lam_infos.get(key).cloned() }

    /// Split `t` into the part that mentions `v` and the maximal `v`-free
    /// subterms, which are pushed onto `holes` and replaced by canonical hole
    /// variables. `v` itself becomes the canonical bound-variable slot.
    ///
    /// Returns `None` if a term mentioning `v` was not built by [`Self::mk`],
    /// which would mean the interpretation had leaked a variable — a bug, and
    /// one that should surface as a gap rather than be papered over.
    fn skeleton(&mut self, t: &Term, v: FreeVar, holes: &mut Vec<Term>) -> Option<Term> {
        if !t.occurs_free(v) {
            let h = self.hole_var(holes.len());
            holes.push(t.clone());
            return Some(Term::var(h))
        }
        if *t == Term::var(v) {
            return Some(Term::var(self.x_canon))
        }
        let (f, args) = self.parts.get(t)?.clone();
        let mut out = Vec::with_capacity(args.len());
        for a in &args {
            out.push(self.skeleton(a, v, holes)?);
        }
        Some(Term::apply(f, out))
    }

    /// The definitional extension behind one skeleton: the body symbol
    /// `t(h⃗,x) := skeleton` and its graph `lam(h⃗,A) = {⟨x,t(h⃗,x)⟩ : x ∈ A}`.
    ///
    /// Derived once per skeleton and then shared by every occurrence of that
    /// shape, in every declaration this thread checks.
    fn build_graph(&mut self, sk: &Term, holes: usize) -> Option<(FnSym, Graph)> {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        ps.push(self.x_canon);
        let (t, t_def) = derived::define_abbrev(&mut self.env_mut(), &ps, sk)?;
        let (lam, lam_ax) = lambda_n(&mut self.env_mut(), &self.pre.clone().ap, t)?;
        Some((lam, Graph { t, t_def, lam_ax }))
    }

    /// Interpret `λ binder:dom. body` as a set-theoretic function graph.
    ///
    /// Returns `None` only if the decomposition itself broke down, which would
    /// be a bug in this module; the caller then falls back to an opaque symbol
    /// so that a bug degrades into a reported gap rather than a wrong answer.
    fn interp_lambda(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        binder_name: NamePtr<'t>,
        binder_style: crate::expr::BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        let dom = self.interp(ctx, binder_type);

        // Open the binder at a fresh local, with a kernel variable reserved for
        // it up front so the interpretation of the body puts that variable in
        // exactly the bound occurrences.
        let local = ctx.mk_unique(binder_name, binder_style, binder_type);
        let key = local_key(ctx, local)?;
        let v = self.env_mut().fresh_var();
        self.locals.insert(key, v);
        let body_open = ctx.inst(body, &[local]);
        let bt = self.interp(ctx, body_open);

        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;

        let info = match self.lam_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = match self.build_graph(&sk, holes.len()) {
                    Some((lam, g)) => Rc::new(LamInfo { lam, graph: Some(g) }),
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // beta. The construction is closed for every skeleton this
                    // module builds, so this is unreachable in practice — and a
                    // reported gap rather than a wrong answer if it ever is not.
                    None => Rc::new(LamInfo { lam: self.env_mut().declare(arity), graph: None }),
                };
                self.shared.borrow_mut().lam_infos.insert(sk.clone(), info.clone());
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.lam, args);
        self.lam_sites.insert(e, LamSite { key: sk, holes, dom });
        Some(term)
    }

    /// Interpret a Lean expression as a kernel term.
    pub fn interp(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Term {
        if let Some(t) = self.exprs.get(&e) {
            return t.clone()
        }
        let t = match ctx.read_expr(e) {
            Expr::Sort { level, .. } => self.interp_sort(ctx, level),
            Expr::Var { dbj_idx, .. } => {
                let i = self.idx_term(dbj_idx as u64);
                self.mk(self.syms.bvar, vec![i])
            }
            Expr::Const { name, levels, .. } => {
                // A constant with a value becomes an **explicit definition**
                // `⟦c⟧ := ⟦value⟧`, monomorphised at these levels. That is
                // conservative for free (`∃!y. y = t` holds for any term), and
                // it is what makes delta reduction justifiable: without a
                // defining equation there is nothing relating the constant to
                // what it unfolds to.
                //
                // Constants without values — axioms, constructors, recursors —
                // stay opaque, which is correct: they do not delta-reduce.
                let decls = self.decls;
                let value = decls.get_declar_val(&name).and_then(|(uparams, val)| {
                    (ctx.read_levels(levels).len() == ctx.read_levels(uparams).len())
                        .then(|| ctx.subst_expr_levels(val, uparams, levels))
                });
                if let Some(val_subst) = value {
                    let body = self.interp(ctx, val_subst);
                    // A definition body with free variables outside the parameter list
                    // cannot be introduced soundly; fall back to an opaque symbol.
                    let Some((sym, axiom)) = derived::define_abbrev(&mut self.env_mut(), &[], &body) else {
                        let s = self.env_mut().declare(0);
                        return Term::apply(s, vec![])
                    };
                    self.const_defs.insert(e, axiom);
                    self.mk(sym, vec![])
                } else {
                    let args = self.interp_levels(ctx, levels);
                    let arity = u32::try_from(args.len()).expect("universe parameter count overflow");
                    let sym = match self.consts.get(&name) {
                        Some(s) if s.arity() == arity => *s,
                        _ => {
                            let s = self.env_mut().declare(arity);
                            self.consts.insert(name, s);
                            s
                        }
                    };
                    self.mk(sym, args)
                }
            }
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.interp(ctx, fun), self.interp(ctx, arg));
                self.mk(self.pre.ap.app, vec![f, a])
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                match self.interp_lambda(ctx, e, binder_name, binder_style, binder_type, body) {
                    Some(t) => t,
                    None => {
                        // Unreachable in principle; see `interp_lambda`. One
                        // opaque symbol per occurrence, which says nothing about
                        // the lambda but is cheap, closed, and makes beta over
                        // it report a gap instead of misbehaving.
                        let d = self.interp(ctx, binder_type);
                        let s = self.env_mut().declare(1);
                        self.mk(s, vec![d])
                    }
                }
            }
            Expr::Pi { binder_type, body, .. } => {
                let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                // A *non-dependent* `Π x:A. B` is the arrow `A → B`, and the
                // arrow is a set: the function space `fs(A,B)` of
                // [`derived::funspace`], with real axioms behind it. A dependent
                // one keeps the opaque `pi` symbol — the dependent product is
                // not constructed in `derived/`, and reusing `fs` for it would
                // be claiming a theorem about a set that was never built.
                //
                // Non-dependence is read off the loose-bvar count: the body of a
                // `Pi` is under one more binder, so `num_loose_bvars(body) == 0`
                // says it mentions no loose de Bruijn index at all, in
                // particular not index 0 — the binder itself. That is
                // conservative rather than exact (a body mentioning an
                // *enclosing* binder but not this one is counted as dependent),
                // which costs coverage and never soundness.
                if ctx.num_loose_bvars(body) == 0 {
                    self.mk(self.pre.fs_sym, vec![d, b])
                } else {
                    self.mk(self.syms.pi, vec![d, b])
                }
            }
            Expr::Let { val, body, .. } => {
                // A `let` denotes its expansion, so introduce it as an
                // **explicit definition** of that expansion — exactly as a
                // constant is introduced as a definition of its value. Zeta is
                // then the defining equation, a real theorem, rather than the
                // interpretation quietly doing the substitution itself (which
                // would leave the kernel certifying nothing about the step).
                //
                // The expansion may mention Lean locals, i.e. kernel free
                // variables, so those become parameters of the symbol; `define`
                // refuses a body with a free variable it does not abstract.
                let expanded = ctx.inst(body, &[val]);
                let t = self.interp(ctx, expanded);
                let mut fvs = Vec::new();
                t.free_vars(&mut fvs);
                let defined = derived::define_abbrev(&mut self.env_mut(), &fvs, &t);
                match defined {
                    Some((sym, axiom)) => {
                        let args: Vec<Term> = fvs.iter().map(|v| Term::var(*v)).collect();
                        // Specialise `⊢ ∀fvs. sym(fvs) = t` down to this instance.
                        if let Some(inst) = derived::inst_all(&axiom, &args) {
                            self.let_defs.insert(e, inst);
                        }
                        self.mk(sym, args)
                    }
                    None => {
                        let s = self.env_mut().declare(0);
                        self.mk(s, vec![])
                    }
                }
            }
            Expr::Local { id, .. } => {
                // Lean locals become kernel *free* variables. This is what makes
                // the eventual certificate a closed statement: generalising over
                // them is `lam_cong`/`pi_cong`'s job, and free variables are
                // exactly what the kernel's `gen` rule can abstract.
                // `FVarId` is either a de Bruijn *level* (used while descending
                // under binders) or a globally unique id; keep the two in
                // separate halves of the key space so they cannot alias.
                let key = match id {
                    crate::expr::FVarId::DbjLevel(n) => n as u64,
                    crate::expr::FVarId::Unique(n) => (n as u64) | (1 << 32),
                };
                let v = match self.locals.get(&key) {
                    Some(v) => *v,
                    None => {
                        let v = self.env_mut().fresh_var();
                        self.locals.insert(key, v);
                        v
                    }
                };
                Term::var(v)
            }
            Expr::Proj { idx, structure, .. } => {
                let i = self.idx_term(idx as u64);
                let s = self.interp(ctx, structure);
                self.mk(self.syms.proj, vec![i, s])
            }
            // Literals get one opaque nullary symbol each. Distinct literals get
            // distinct symbols because the whole match is memoised on the
            // hash-consed `ExprPtr`, so equal literals are the same node.
            // Milestone 4 replaces these with the kernel's primitive `ℕ` and its
            // native bignum rule schemas.
            Expr::NatLit { .. } | Expr::StringLit { .. } => {
                let s = self.env_mut().declare(0);
                self.mk(s, vec![])
            }
        };
        self.exprs.insert(e, t.clone());
        t
    }

    /// Congruence for a binary interpretation symbol, from certificates for the
    /// two sub-positions.
    fn cong2(&mut self, sym: FnSym, a: TgCert, b: TgCert) -> TgCert {
        let (ca, cb) = (self.consume(&a), self.consume(&b));
        let (ta, tb) = match (ca, cb) {
            (Some(x), Some(y)) => (x, y),
            // A gap anywhere below means the whole congruence is a gap; there is
            // nothing to prove congruence *from*.
            _ => return self.note_admit("congruence over an admitted premise"),
        };
        match self.ceq_congr(sym, &[ta, tb]) {
            Some(t) => self.cert(t),
            None => self.note_admit("congruence rule refused"),
        }
    }

    /// `⊢ ⟦a⟧ ∈ dom`, the typing premise `beta_conditional_n` is conditional on,
    /// or `None` when this interpretation does not know that membership.
    ///
    /// Two facts are available, both genuine theorems about the two operators
    /// the interpretation is built from:
    ///
    /// * `⊢ ∀x. x ∈ U(x)` — a sort sits in the next universe up, since
    ///   `⟦Sort (u+1)⟧` *is* `U(⟦Sort u⟧)`;
    /// * `⊢ ∀a. fs(a,a) ∈ U(a)` — the function space `t → t` sits in the least
    ///   universe over `t`, which is what makes `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧`
    ///   available now that a non-dependent `Pi` is interpreted as `fs`.
    ///
    /// Whichever applies, the result is checked to be literally `⟦a⟧ ∈ dom`
    /// before it is returned, so a mistake here yields a gap and not a theorem
    /// about the wrong terms.
    fn domain_premise(&mut self, ta: &Term, dom: &Term) -> Option<Thm> {
        let want = Formula::mem(ta.clone(), dom.clone());
        let out = if *dom == Term::apply(self.pre.u_sym, vec![ta.clone()]) {
            let mem_u = self.pre.mem_u.clone();
            derived::inst_all(&mem_u, std::slice::from_ref(ta))?
        } else {
            // `⟦a⟧` has to be a *diagonal* function space `fs(t,t)`: the
            // two-argument form `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)` carries an
            // antecedent about binary unions that is not dischargeable here.
            let (f, args) = self.parts.get(ta)?.clone();
            if f != self.pre.fs_sym || args.len() != 2 || args[0] != args[1] {
                return None
            }
            let t = args[0].clone();
            if *dom != Term::apply(self.pre.u_sym, vec![t.clone()]) {
                return None
            }
            let fs_in_u = self.pre.fs_in_u.clone();
            derived::inst_all(&fs_in_u, std::slice::from_ref(&t))?
        };
        (*out.concl() == want).then_some(out)
    }

    /// The beta theorem for one lambda skeleton, derived on first use.
    fn beta_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().lam_betas.get(key) {
            return t.clone()
        }
        let info = self.lam_info(key)?;
        let g = info.graph.as_ref()?;
        let (t, lam, lam_ax) = (g.t, info.lam, g.lam_ax.clone());
        let ap = self.pre.clone();
        let thm = beta_conditional_n(&mut self.env_mut(), &ap.ap, t, lam, &lam_ax);
        self.shared.borrow_mut().lam_betas.insert(key.clone(), thm.clone());
        thm
    }

    /// One beta contraction: `⊢ app(⟦λ⟧, ⟦a⟧) = ⟦body[a]⟧`, possibly under the
    /// assumption `⟦a⟧ ∈ dom` when the typing obligation cannot be discharged.
    fn beta_step(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam_expr: ExprPtr<'t>,
        body: ExprPtr<'t>,
        arg: ExprPtr<'t>,
    ) -> Result<(CondEq, ExprPtr<'t>), &'static str> {
        // Interpreting the lambda is what registers its graph symbol.
        let _ = self.interp(ctx, lam_expr);
        let Some(site) = self.lam_sites.get(&lam_expr) else {
            return Err("beta: the lambda has no function-graph interpretation")
        };
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let ta = self.interp(ctx, arg);

        // The domain premise is settled *first*: it is a term comparison plus
        // one instantiation, while the beta lemma below is a derivation, and
        // most redexes fail here.
        //
        // The typing facts this interpretation supplies are `x ∈ U(x)` and
        // `fs(a,a) ∈ U(a)` — see `domain_premise`. When neither applies the step
        // is **not** admitted: the premise is kept as a genuine assumption and
        // the certificate says so, `⊢ (⟦a⟧ ∈ dom) → …`. It then has to be
        // discharged before the certificate reaches a boundary, or it is
        // reported as a gap (see `escape_report`).
        let mem_inst = self.domain_premise(&ta, &dom);
        let hyps = match mem_inst {
            Some(_) => Vec::new(),
            None => vec![Formula::mem(ta.clone(), dom.clone())],
        };
        let Some(beta) = self.beta_thm(&key) else {
            return Err("beta: the lambda's graph, and so its beta lemma, was not built")
        };

        // ⊢ ⟦a⟧ ∈ dom → app(lam(h⃗,dom), ⟦a⟧) = t(h⃗, ⟦a⟧)
        let mut inst = holes.clone();
        inst.push(dom.clone());
        inst.push(ta.clone());
        let Some(conditional) = derived::inst_all(&beta, &inst) else {
            return Err("beta: instantiating the beta lemma failed")
        };

        // With the membership in hand the premise comes off; without it the
        // implication *is* the certificate, its antecedent being the single
        // assumption recorded above.
        let eq_t = match &mem_inst {
            Some(m) => {
                let Some(t) = Thm::mp(&conditional, m) else {
                    return Err("beta: discharging the domain premise failed")
                };
                t
            }
            None => conditional,
        };
        let Some(eq_t) = CondEq::new(eq_t, hyps) else {
            return Err("beta: the beta lemma does not have the assumed shape")
        };

        // Unfold `t(h⃗, ⟦a⟧)` to the skeleton with the argument plugged in, and
        // check that is literally the interpretation of the contracted body.
        let info = self.lam_info(&key).expect("skeleton registered");
        let Some(g) = info.graph.as_ref() else {
            return Err("beta: the lambda's graph was not built")
        };
        let mut inst_t = holes;
        inst_t.push(ta);
        let Some(unfold) = derived::inst_all(&g.t_def, &inst_t) else {
            return Err("beta: instantiating the body definition failed")
        };
        let Some(unfold) = CondEq::plain(unfold) else {
            return Err("beta: the body definition is not an equation")
        };
        let Some(step) = self.ceq_trans(&eq_t, &unfold) else {
            return Err("beta: chaining the body definition failed")
        };

        let next = ctx.inst(body, &[arg]);
        let tnext = self.interp(ctx, next);
        let Some((_, rhs)) = step.as_eq() else {
            return Err("beta: the derived step is not an equation")
        };
        if rhs != tnext {
            return Err("beta: the contracted body does not match its interpretation")
        }
        Ok((step, next))
    }

    /// The whole (possibly multi-argument) beta contraction the checker asked
    /// for, as `⊢ ⟦redex⟧ = ⟦reduct⟧` — or, where a contraction's typing
    /// obligation could not be discharged, under the assumptions it needed.
    fn derive_beta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<CondEq, &'static str> {
        let (fun, args) = ctx.unfold_apps(redex);
        if args.is_empty() {
            return Err("beta: the redex is not an application")
        }
        let mut cur = fun;
        let mut acc = CondEq::refl(self.interp(ctx, fun));
        let app = self.pre.ap.app;

        for arg in args {
            let ta = self.interp(ctx, arg);
            let Some(lifted) = self.ceq_congr(app, &[acc.clone(), CondEq::refl(ta)]) else {
                return Err("beta: congruence over the spine refused")
            };
            acc = lifted;
            // The checker contracts every leading lambda it can and re-applies
            // whatever is left over, so stop peeling at the first non-lambda and
            // let congruence carry the rest.
            if let Expr::Lambda { body, .. } = ctx.read_expr(cur) {
                let (step, next) = self.beta_step(ctx, cur, body, arg)?;
                let Some(chained) = self.ceq_trans(&acc, &step) else {
                    return Err("beta: chaining a contraction failed")
                };
                acc = chained;
                cur = next;
            }
        }

        // Guard. The derivation is worth nothing unless it is a derivation of
        // the equation the checker actually claimed.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if !acc.proves(&lhs, &rhs) {
            return Err("beta: derived equation does not match the reduction")
        }
        Ok(acc)
    }

    /// Graph extensionality relating the two lambda *skeletons*, derived on
    /// first use and shared thereafter.
    fn lam_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().lam_exts.get(&key) {
            return t.clone()
        }
        let ia = self.lam_info(ka)?;
        let ib = self.lam_info(kb)?;
        let thm = match (ia.graph.as_ref(), ib.graph.as_ref()) {
            (Some(ga), Some(gb)) => {
                let ap = self.pre.clone();
                lam_ext_n(&mut self.env_mut(), &ap.ap, ga.t, ia.lam, &ga.lam_ax, gb.t, ib.lam, &gb.lam_ax)
            }
            _ => None,
        };
        self.shared.borrow_mut().lam_exts.insert(key, thm.clone());
        thm
    }

    /// The pointwise premise of [`lam_ext_n`], read off the body certificate.
    ///
    /// The certificate says `⊢ ⟦b⟧ = ⟦b'⟧` with both bodies opened at the
    /// checker's local for this binder — a kernel *free* variable `w`. What the
    /// extensionality lemma wants is `⊢ ∀x. (x ∈ A → t(h⃗,x) = t'(h⃗',x))`.
    ///
    /// The bridge is the two body-symbol definitions: `t(h⃗,w)` unfolds to the
    /// skeleton with `w` in the binder slot, which is exactly the certificate's
    /// left-hand side — *if* `w` is the right variable, which is checked by
    /// comparing the unfolded terms rather than assumed. `w` itself is not
    /// handed to this rule, so it is searched for among the free variables of
    /// the certificate; a body that ignores its binder pins nothing, and then a
    /// fresh variable does (the resulting `∀` is vacuous, which is correct).
    ///
    /// Weakening to the guarded form is `a1i`, and the generalisation is the
    /// kernel's `gen` — which needs no side condition, since a `Thm` carries no
    /// hypotheses. It does need `w` to be absent from `h⃗`, `h⃗'` and `A`, or the
    /// `∀` would capture them; the candidates are filtered on exactly that, and
    /// a slip could only make the `mp` below fail, never produce a false claim.
    ///
    /// # Discharging an assumption
    ///
    /// This is also the one place where a carried assumption goes away. If the
    /// body certificate is conditional and one of its assumptions is literally
    /// `w ∈ A` — the guard of the very `∀` being built — then that assumption is
    /// *not* weakened in, it is **used**: re-stated last, peeled off with
    /// [`derived::uncurry`], generalised, and pushed back through the ∀ with
    /// `Thm::ax_dist`. The kernel checks `ax_dist`'s side condition (`w` not
    /// free in the remaining assumptions), so a mistake is a rejection.
    ///
    /// Returns the premise together with the assumptions that survive it.
    fn pointwise_premise(
        &mut self,
        t_def_a: &Thm,
        t_def_b: &Thm,
        holes_a: &[Term],
        holes_b: &[Term],
        dom_a: &Term,
        body: &CondEq,
    ) -> Option<(Thm, Vec<Formula>)> {
        let (u1, u2) = body.as_eq()?;

        // Variables `w` may be: those the two body interpretations mention, but
        // not any that the parameters or the domain do.
        let mut excluded: Vec<FreeVar> = Vec::new();
        for h in holes_a.iter().chain(holes_b.iter()) {
            h.free_vars(&mut excluded);
        }
        dom_a.free_vars(&mut excluded);
        let mut seen: Vec<FreeVar> = Vec::new();
        u1.free_vars(&mut seen);
        u2.free_vars(&mut seen);
        let mut cands: Vec<FreeVar> = Vec::new();
        for v in seen {
            if !excluded.contains(&v) && !cands.contains(&v) {
                cands.push(v);
            }
        }
        // A body that does not mention its binder leaves `w` free; any variable
        // not already in play will do, and a fresh one certainly is not.
        cands.push(self.env_mut().fresh_var());

        for w in cands {
            let tw = Term::var(w);
            let inst = |holes: &[Term]| {
                let mut v = holes.to_vec();
                v.push(tw.clone());
                v
            };
            let Some(ea) = derived::inst_all(t_def_a, &inst(holes_a)) else { continue };
            let Some(eb) = derived::inst_all(t_def_b, &inst(holes_b)) else { continue };
            // `t(h⃗,w) = ⟦b⟧` and `t'(h⃗',w) = ⟦b'⟧` — the halves that make the
            // certificate applicable at all.
            match (ea.concl().as_eq(), eb.concl().as_eq()) {
                (Some((_, ra)), Some((_, rb))) if ra == u1 && rb == u2 => {}
                _ => continue,
            }
            let Some(eb_symm) = derived::eq_symm(&mut self.env_mut(), &eb) else { continue };
            let (Some(ea), Some(eb_symm)) = (CondEq::plain(ea), CondEq::plain(eb_symm)) else { continue };
            let Some(half) = self.ceq_trans(&ea, body) else { continue };
            let Some(at_w) = self.ceq_trans(&half, &eb_symm) else { continue };
            let Some((l, r)) = at_w.as_eq() else { continue };
            let (eqf, guard) = (Formula::eq(l, r), Formula::mem(tw.clone(), dom_a.clone()));

            // The guarded body `w ∈ A → t(h⃗,w) = t'(h⃗',w)`, under whatever
            // assumptions are left over. Either the guard is one of the
            // certificate's own assumptions — then it is discharged into the
            // implication rather than assumed twice — or it is pure weakening.
            let (rest, guarded) = match at_w.hyps.iter().position(|f| *f == guard) {
                Some(i) => {
                    let mut rest = at_w.hyps.clone();
                    rest.remove(i);
                    let mut last = rest.clone();
                    last.push(guard.clone());
                    let Some(re) = reassume(&at_w.thm, &at_w.hyps, &last) else { continue };
                    if rest.is_empty() {
                        // `conj([guard])` *is* `guard`: already the wanted form.
                        (rest, re)
                    } else {
                        let Some(peeled) = derived::uncurry(&re) else { continue };
                        (rest, peeled)
                    }
                }
                None => {
                    let rest = at_w.hyps.clone();
                    if rest.is_empty() {
                        (rest, derived::a1i(&at_w.thm, guard.clone()))
                    } else {
                        let Some(weak) = derived::syl(&at_w.thm, &Thm::ax_k(eqf.clone(), guard.clone())) else {
                            continue
                        };
                        (rest, weak)
                    }
                }
            };

            let all = Thm::gen(w, &guarded);
            if rest.is_empty() {
                return Some((all, rest))
            }
            // `⊢ ∀w. (conj(rest) → (w ∈ A → …))` becomes
            // `⊢ conj(rest) → ∀w. (w ∈ A → …)`. The kernel refuses if `w` is
            // free in `conj(rest)`, which is exactly the condition under which
            // the move would be wrong.
            let Some(rc) = conj_of(&rest) else { continue };
            let Some(dist) = Thm::ax_dist(w, rc, Formula::imp(guard, eqf)) else { continue };
            let Some(out) = Thm::mp(&dist, &all) else { continue };
            return Some((out, rest))
        }
        None
    }

    /// [`retarget`] against this backend's record of term structure.
    fn retarget(&self, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
        retarget_cond(&self.parts, cert, want_l, want_r)
    }

    /// One premise of `Π` congruence, as `⊢ l = r` under its assumptions.
    ///
    /// Three ways to get there, in order: the certificate already *is* that
    /// equation; it becomes that equation after [`Self::retarget`]; or the two
    /// sides interpret identically and reflexivity proves it outright. The last
    /// is the only one that survives an admitted certificate, and it is a
    /// complete proof rather than a shortcut.
    fn pi_premise(&mut self, c: Option<&CondEq>, l: &Term, r: &Term) -> Option<CondEq> {
        if let Some(t) = c {
            if t.proves(l, r) {
                return Some(t.clone())
            }
            if let Some(rt) = self.retarget(t, l, r) {
                return Some(rt)
            }
        }
        (l == r).then(|| CondEq::refl(l.clone()))
    }

    /// Discharge a lemma's premises with derivations that may carry assumptions.
    ///
    /// `lemma` is `⊢ p₁ → (p₂ → … → concl)` and each `prem` derives one `pᵢ`
    /// under its own assumptions; the result is the conclusion under the union.
    /// This is `Thm::mp`, once per premise, re-stated under the merged
    /// assumption set — the shape both congruences need.
    fn discharge(&mut self, lemma: &Thm, prems: &[CondEq]) -> Option<CondEq> {
        let mut hyps: Vec<Formula> = Vec::new();
        for p in prems {
            hyps = merge_hyps(&hyps, &p.hyps);
        }
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let mut acc = u_a1i(lemma, h.as_ref());
        for p in prems {
            let lifted = reassume(&p.thm, &p.hyps, &hyps)?;
            acc = u_mp(&acc, &lifted, h.as_ref())?;
        }
        CondEq::new(acc, hyps)
    }

    /// `⊢ ⟦Π x:A. b⟧ = ⟦Π x:A'. b'⟧`, by congruence over the head symbol the
    /// two interpretations share.
    fn derive_pi_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        if !matches!((ctx.read_expr(a), ctx.read_expr(b)), (Expr::Pi { .. }, Expr::Pi { .. })) {
            return Err("pi congruence: not applied to two Π types")
        }
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        // Read the two premises' targets straight off the *claim* rather than
        // re-interpreting the two sub-expressions. Those agree today, but this
        // way the premises are by construction about the terms the conclusion
        // will be compared against, so the rule cannot drift from its guard.
        //
        // The head symbol has to agree, and it need not: `⟦Π⟧` is `fs` when
        // the binder is non-dependent and the opaque `pi` otherwise, so two Π
        // types the checker calls equal can interpret with unrelated head
        // symbols. Nothing in the equational fragment relates them, so say so.
        let (Some((fa, aargs)), Some((fb, bargs))) = (self.parts.get(&ta).cloned(), self.parts.get(&tb).cloned())
        else {
            return Err("pi congruence: a Π has no applicative interpretation")
        };
        if fa != fb {
            return Err("pi congruence: dependent and non-dependent Π interpret differently")
        }
        if aargs.len() != 2 || bargs.len() != 2 {
            return Err("pi congruence: a Π interprets to an unexpected arity")
        }
        let (ia, ja) = (aargs[0].clone(), aargs[1].clone());
        let (ib, jb) = (bargs[0].clone(), bargs[1].clone());
        let Some(dom_thm) = self.pi_premise(dom, &ia, &ib) else {
            return Err(if dom.is_none() {
                "pi congruence over an admitted domain premise"
            } else {
                "pi congruence: the domain certificate is not about the binder types"
            })
        };
        let Some(body_thm) = self.pi_premise(body, &ja, &jb) else {
            return Err(if body.is_none() {
                "pi congruence over an admitted body premise"
            } else {
                "pi congruence: the body certificate is not about the binder bodies"
            })
        };
        // For the non-dependent head this is `fs_cong`, the lemma derived for
        // exactly this case, discharged at the four interpreted terms. For the
        // opaque dependent head there is no such lemma to reach for, and plain
        // congruence over the symbol is all the signature supports — the two
        // routes have the same conclusion.
        if fa == self.pre.fs_sym {
            let lemma = self.pre.fs_cong.clone();
            let inst = derived::inst_all(&lemma, &[ia, ib, ja, jb])
                .ok_or("pi congruence: instantiating function-space congruence failed")?;
            self.discharge(&inst, &[dom_thm, body_thm]).ok_or("pi congruence: discharging a premise failed")
        } else {
            self.ceq_congr(fa, &[dom_thm, body_thm]).ok_or("pi congruence: congruence rule refused")
        }
    }

    /// `⊢ ⟦λx:A. b⟧ = ⟦λx:A'. b'⟧`, by graph extensionality.
    fn derive_lam_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        // Interpreting the two lambdas is what registers their graph symbols.
        let _ = self.interp(ctx, a);
        let _ = self.interp(ctx, b);
        let (Some(sa), Some(sb)) = (self.lam_sites.get(&a), self.lam_sites.get(&b)) else {
            return Err("lam congruence: a lambda has no function-graph interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());

        let Some(info_a) = self.lam_info(&key_a) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let Some(info_b) = self.lam_info(&key_b) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let (Some(ga), Some(gb)) = (info_a.graph.as_ref(), info_b.graph.as_ref()) else {
            return Err("lam congruence: the lambda's graph was not built")
        };
        let (t_def_a, t_def_b) = (ga.t_def.clone(), gb.t_def.clone());

        // The domain premise. The certificate the checker handed down is the
        // right one when it proves the two binder types equal; when the types
        // interpret identically, reflexivity does the job instead — which is
        // the only way a gapped domain certificate can still be rescued.
        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err("lam congruence: the domain certificate does not match the binder types"),
        };

        let Some(body_thm) = body else {
            return Err("lam congruence over an admitted premise")
        };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&t_def_a, &t_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("lam congruence: the body certificate is not the graphs' pointwise equation")
        };
        // `pointwise` is `⊢ conj(rest) → ∀x. …`, whose consequent is not an
        // equation — so it cannot be a `CondEq`, and `Self::discharge` (which
        // returns one) does not apply. The two premises are discharged by hand
        // below with the same `reassume`/`u_mp` moves.

        let Some(ext) = self.lam_ext_thm(&key_a, &key_b) else {
            return Err("lam congruence: graph extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("lam congruence: instantiating graph extensionality failed")
        };

        // Both premises are discharged under the union of their assumptions:
        // the domain equation's, and whatever the pointwise premise could not
        // shed at the binder.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        if hyps.len() > MAX_HYPS {
            return Err("lam congruence: too many undischarged assumptions")
        }
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("lam congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("lam congruence: re-stating the pointwise premise failed")
        };
        // This is the step that would fail if the generalisation above had
        // captured a parameter: the premise would not be the lemma's.
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("lam congruence: the result is not the assumed equation")
    }
}

/// The applicative structure of the terms a match may take apart: the shape
/// [`TgBackend::parts`] records on the way in.
type Parts = HashMap<Term, (FnSym, Vec<Term>)>;

/// Match `have` against `want`, reading off which free variables of `have` have
/// to become which subterms of `want`.
///
/// A pure syntactic first-order match, one-sided: only `have`'s free variables
/// are treated as holes, and a variable bound twice to different terms fails.
/// Interior nodes are compared through `parts`, so a term the backend did not
/// build stops the match rather than being taken apart by guesswork.
fn match_term(parts: &Parts, have: &Term, want: &Term, subst: &mut Vec<(FreeVar, Term)>) -> Option<()> {
    if have == want {
        return Some(())
    }
    if let Some((f, hargs)) = parts.get(have) {
        let (g, wargs) = parts.get(want)?;
        if f != g || hargs.len() != wargs.len() {
            return None
        }
        for (h, w) in hargs.iter().zip(wargs.iter()) {
            match_term(parts, h, w, subst)?;
        }
        return Some(())
    }
    // Not an application the backend built, so the only thing it can be and
    // still match is a free variable standing for a whole subterm.
    let mut fvs = Vec::new();
    have.free_vars(&mut fvs);
    if fvs.len() != 1 || *have != Term::var(fvs[0]) {
        return None
    }
    let v = fvs[0];
    match subst.iter().find(|(u, _)| *u == v) {
        Some((_, t)) => (t == want).then_some(()),
        None => {
            subst.push((v, want.clone()));
            Some(())
        }
    }
}

/// Re-aim a certificate from the *opened* form of a binder body at the raw
/// de Bruijn form that `⟦Π⟧` is built over.
///
/// The checker compares binder bodies after instantiating them at locals, so
/// the certificate it hands `pi_cong` is about `⟦B[l⃗]⟧`, with `l⃗` kernel free
/// variables — whereas `⟦Π x:A. B⟧` is `sym(⟦A⟧, ⟦B⟧)` over the *raw* body, in
/// which those positions are `bvar` symbols instead. The two are related by
/// exactly the rule a free variable admits: generalise it, then instantiate at
/// the term wanted in its place. `Thm::gen` needs no side condition here — a
/// `Thm` carries no hypotheses — and `ax_inst` is the kernel's own
/// instantiation, so the result is a genuine theorem about the wanted terms.
///
/// Which term goes in which variable's place is *read off* by matching the
/// certificate against the wanted equation rather than guessed, and the outcome
/// is compared against that equation before it is returned. So the worst a
/// mismatch can do — a shifted de Bruijn index under a nested `Π`, a body the
/// backend did not build, one local that would have to become two different
/// terms — is produce `None`, hence a reported gap.
///
/// A certificate that carries assumptions is re-aimed the same way, except that
/// generalising and re-instantiating rewrites the *assumptions* too — so they
/// are substituted alongside, and `CondEq::new` re-checks that the rewritten
/// list really is the rewritten theorem's antecedent.
fn retarget_cond(parts: &Parts, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
    let (have_l, have_r) = cert.as_eq()?;
    let mut subst: Vec<(FreeVar, Term)> = Vec::new();
    match_term(parts, &have_l, want_l, &mut subst)?;
    match_term(parts, &have_r, want_r, &mut subst)?;
    if subst.is_empty() {
        // Nothing to re-aim, and the caller has already compared the
        // certificate verbatim; going on would only re-derive what it has.
        return None
    }
    let mut cur = cert.thm.clone();
    let mut hyps = cert.hyps.clone();
    for (v, t) in subst {
        cur = derived::inst_all(&Thm::gen(v, &cur), std::slice::from_ref(&t))?;
        hyps = hyps.iter().map(|f| f.subst(v, &t)).collect();
    }
    // The guard. Nothing above is trusted to have produced the right equation,
    // and `CondEq::new` re-checks that the assumptions really are the theorem's
    // antecedent after the rewrite.
    let out = CondEq::new(cur, hyps)?;
    out.proves(want_l, want_r).then_some(out)
}

/// [`retarget_cond`] for a certificate that assumes nothing.
#[cfg(test)]
fn retarget(parts: &Parts, cert: &Thm, want_l: &Term, want_r: &Term) -> Option<Thm> {
    let c = CondEq::plain(cert.clone())?;
    Some(retarget_cond(parts, &c, want_l, want_r)?.thm)
}

/// The `locals` key for a Lean free variable expression.
fn local_key<'t, 'p>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Option<u64> {
    match ctx.read_expr(e) {
        Expr::Local { id: crate::expr::FVarId::DbjLevel(n), .. } => Some(n as u64),
        Expr::Local { id: crate::expr::FVarId::Unique(n), .. } => Some((n as u64) | (1 << 32)),
        _ => None,
    }
}

impl<'x, 't: 'x, 'p: 't> Certifier for TgBackend<'x, 't, 'p> {
    type Term = ExprPtr<'t>;
    type Cert = TgCert;
    type Ctx = TcCtx<'t, 'p>;

    fn refl(&mut self, ctx: &mut Self::Ctx, a: Self::Term) -> TgCert {
        let t = self.interp(ctx, a);
        self.proved(Thm::eq_refl(t))
    }

    fn symm(&mut self, _ctx: &mut Self::Ctx, c: TgCert) -> TgCert {
        match self.consume(&c) {
            Some(t) => match self.ceq_symm(&t) {
                Some(t) => self.cert(t),
                None => self.note_admit("symm refused"),
            },
            None => self.note_admit("symm over an admitted premise"),
        }
    }

    fn trans(&mut self, _ctx: &mut Self::Ctx, ab: TgCert, bc: TgCert) -> TgCert {
        // Both are taken before either is inspected: a premise the rule cannot
        // use is still a premise the rule has *received*, and the escape ledger
        // counts receipt.
        let (x, y) = (self.consume(&ab), self.consume(&bc));
        match (x, y) {
            (Some(x), Some(y)) => match self.ceq_trans(&x, &y) {
                Some(t) => self.cert(t),
                None => self.note_admit("trans refused"),
            },
            _ => self.note_admit("trans over an admitted premise"),
        }
    }

    fn app_cong(&mut self, _ctx: &mut Self::Ctx, f: TgCert, a: TgCert) -> TgCert {
        let s = self.pre.ap.app;
        self.cong2(s, f, a)
    }

    /// Congruence for `λ`, by **graph extensionality**, and guarded.
    ///
    /// `⟦λx:A. b⟧` is a function *graph* `lam_C(s⃗, ⟦A⟧)` whose head symbol
    /// depends on the shape of the body, so this is not congruence over
    /// sub-terms: from `⊢ ⟦A⟧ = ⟦A'⟧` and `⊢ ⟦b⟧ = ⟦b'⟧` one has to conclude
    /// `⊢ lam_C(s⃗,⟦A⟧) = lam_C'(s⃗',⟦A'⟧)` for two *different* symbols. Two
    /// graphs are equal because they have the same members, which is
    /// Extensionality — [`derived::ext::lam_ext`], here in the
    /// parameter-threading form [`lam_ext_n`] the skeleton decomposition needs.
    ///
    /// Its second premise is *pointwise*, `∀x. (x ∈ A → t(x) = t'(x))`, whereas
    /// the certificate this rule is handed compares the bodies at one fixed
    /// local. [`Self::pointwise_premise`] closes that gap: the local is a kernel
    /// free variable, `Thm::gen` abstracts it with no side condition (a `Thm`
    /// carries no hypotheses), and the `x ∈ A` guard is pure weakening. What it
    /// must establish — and does, by unfolding both body definitions and
    /// comparing terms — is that the certificate really is about the graphs'
    /// body symbols at that variable.
    ///
    /// Whatever comes out is checked against `⟦a⟧ = ⟦b⟧` before it counts as a
    /// proof, so every way this can go wrong is a gap rather than a false
    /// theorem.
    ///
    /// # Binder chains
    ///
    /// A binder *chain* is folded up innermost-first, and this used to be where
    /// the rule stopped: `def_eq_binder_aux` handed each frame its lambda in
    /// **un-instantiated** form, so an inner frame's lambda still carried loose
    /// de Bruijn indices for the enclosing binders — interpreted as opaque
    /// `bvar` symbols — while the certificate beneath it was about bodies opened
    /// at real locals. `pointwise_premise` could then never match, and the outer
    /// frame was in turn handed an equation between those un-instantiated inner
    /// lambdas. On a chain of length two or more, nothing derivable here bridged
    /// that.
    ///
    /// `def_eq_binder_aux` now instantiates each `λ` frame at the locals
    /// introduced above it, so the frame's terms *are* the ones its premises
    /// talk about, and the derivation applies at every depth. (`Π` frames are
    /// deliberately left alone: `⟦Π⟧` is built over the raw de Bruijn body, so
    /// `pi_cong` wants the opposite form. See the comment there.)
    ///
    /// The degenerate case remains as a fallback: if the two lambdas interpret
    /// to the *same* graph, reflexivity proves the claim outright, with no
    /// premise needed. That is a complete proof, not a shortcut — and it is
    /// still what closes the chains the derivation cannot reach.
    fn lam_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_lam_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(t),
            Ok(_) => "lam congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        // Both lambdas interpret to the same graph: reflexivity is the claim.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for `Π`, **guarded**.
    ///
    /// `⟦Π x:A. B⟧` is `fs(⟦A⟧,⟦B⟧)` when the binder is non-dependent and
    /// `pi(⟦A⟧,⟦B⟧)` otherwise, both compositional over the *raw* de Bruijn
    /// body. So this is genuine sub-term congruence — `fs_cong` for the first
    /// head, plain congruence for the opaque second — and the only real work is
    /// getting the two premises into the form the claim needs.
    ///
    /// That is [`TgBackend::retarget`]'s job, and it is what used to make this
    /// rule gap. The checker compares binder bodies *opened at locals*, so the
    /// certificate below an innermost `Π` frame is about `⟦B[l⃗]⟧` while the
    /// claim is about `⟦B⟧` with `bvar` symbols in those positions; likewise a
    /// frame below the outermost is handed a domain certificate about the opened
    /// binder type. Generalising the locals and instantiating at the terms the
    /// claim wants closes both, and the substitution is read off by matching
    /// rather than assumed.
    ///
    /// Everything is checked against `⟦a⟧ = ⟦b⟧` before it counts as a proof, so
    /// every way this can go wrong is a gap rather than a false theorem.
    ///
    /// The reflexivity fallback covers the case where both sides interpret
    /// identically — a complete proof of the claim, needing no premise at all,
    /// and on this corpus by far the commonest way a `Π` congruence is settled.
    fn pi_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_pi_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(t),
            Ok(_) => "pi congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    fn beta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        match self.derive_beta(ctx, redex, reduct) {
            Ok(t) => self.cert(t),
            Err(reason) => self.note_admit(reason),
        }
    }

    /// Zeta: `let x := v; b ≡ b[v/x]`.
    ///
    /// Discharged by the `Let`'s defining equation, guarded against the claim in
    /// the same way as `delta` and `beta`.
    fn zeta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        let Some(eq) = self.let_defs.get(&redex).cloned() else {
            let _ = self.interp(ctx, redex);
            match self.let_defs.get(&redex).cloned() {
                Some(eq) => return self.check_against(ctx, eq, redex, reduct, "zeta"),
                None => return self.note_admit("zeta: the let has no defining equation"),
            }
        };
        self.check_against(ctx, eq, redex, reduct, "zeta")
    }

    fn delta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        // `redex` is `c a₁ … aₙ` and `reduct` is `value a₁ … aₙ`. Interpreting
        // the head constant registers its defining equation `⊢ ⟦c⟧ = ⟦value⟧`;
        // folding `app_cong` over the argument spine lifts that to the whole
        // application.
        let (fun, args) = ctx.unfold_apps(redex);
        let _ = self.interp(ctx, fun);
        let Some(head) = self.const_defs.get(&fun).cloned() else {
            return self.note_admit("delta: head constant has no defining equation")
        };
        let mut acc = head;
        for a in args {
            let ta = self.interp(ctx, a);
            let refl = Thm::eq_refl(ta);
            let app = self.pre.ap.app;
            let stepped = derived::congr(&mut self.env_mut(), app, &[acc, refl]);
            match stepped {
                Some(t) => acc = t,
                None => return self.note_admit("delta: congruence over the spine refused"),
            }
        }
        // Guard: the derived equation must really be about the two terms the
        // checker claims are equal. If the interpretation and the reduction have
        // drifted apart, that is a bug — report it rather than pass it off.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *acc.concl() != kernel::Formula::eq(lhs, rhs) {
            return self.note_admit("delta: derived equation does not match the reduction")
        }
        self.proved(acc)
    }

    fn eta(&mut self, _ctx: &mut Self::Ctx, _a: Self::Term, _b: Self::Term) -> TgCert {
        self.note_admit("eta (needs a function-extensionality lemma)")
    }

    fn sort(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> TgCert {
        // The checker only calls this when the two levels are equal under its
        // own level algebra. When that makes the interpretations syntactically
        // identical, reflexivity settles it outright. When it does not — say
        // `max u v` versus `max v u` — proving it needs level axioms the
        // signature does not have, so it is recorded as a gap rather than waved
        // through.
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("sort equality modulo level algebra")
        }
    }

    fn const_eq(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> TgCert {
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("constant equality modulo level algebra")
        }
    }

    fn admit(&mut self, _ctx: &mut Self::Ctx, _a: Self::Term, _b: Self::Term, reason: &'static str) -> TgCert {
        self.note_admit(reason)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reporting.
//
// A `TgBackend` is created per `TypeChecker`, i.e. per declaration, and dropped
// with it, so the per-run totals have to be accumulated somewhere shared. This
// is a report on the checker's own completeness, not part of any derivation.
// ─────────────────────────────────────────────────────────────────────────────

use std::sync::Mutex;

static TOTALS: Mutex<Option<Vec<(&'static str, u64)>>> = Mutex::new(None);
static PROVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// ── The escape ledger ────────────────────────────────────────────────────────
//
// A conditional certificate is a complete derivation of an *implication*, while
// the checker's claim is the bare equation. So carrying one is only honest for
// as long as it stays inside the derivation: the moment a copy is used as an
// answer, an assumption has been taken on trust, and it has to be reported.
//
// The backend cannot see where the checker stops recursing, so the accounting is
// done the other way round, by copies:
//
//   * every conditional certificate *created* — by a rule, or by `Clone`, since
//     a copy is a second certificate that must also be accounted for —
//     increments `CONDITIONAL`;
//   * every conditional certificate *handed back to a rule* increments
//     `CONSUMED`, because the rule has then either folded the assumption into
//     its own result (which is counted in turn), proved the claim without it, or
//     reported a gap instead.
//
// The difference is exactly the number of copies that no rule ever received —
// the ones the checker consumed as a verdict, plus any left in its caches. Those
// are the escapes, and they are reported as gaps. `TgBackend::consume` is the
// single funnel for the second counter, and every `Certifier` method that takes
// a certificate calls it on every argument, whatever it then does.
//
// The direction of the residual error matters and is stated plainly: a copy
// abandoned in a cache is counted as an escape although nothing was concluded
// from it, so this **over**-reports. It cannot under-report, because a copy that
// was never handed to a rule cannot have had its assumption discharged.

/// Conditional certificates brought into existence, copies included.
static CONDITIONAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// How many of those were copies. A copy the checker parked in a cache and never
/// used again is the one thing this ledger over-reports, so the number is kept
/// visible: it bounds the over-report.
static CONDITIONAL_COPIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Conditional certificates handed back to a rule, which accounts for them.
static CONSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// The largest assumption set any one certificate carried.
static MAX_ASSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The gap reported for a certificate that reached a boundary still assuming
/// something. There is exactly one place an assumption is introduced —
/// [`TgBackend::beta_step`], when `domain_premise` cannot show the argument
/// lies in the binder's domain — so this names the assumption it names.
const ESCAPED: &str = "undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary";

/// Record one conditional certificate coming into existence.
pub fn note_conditional() { CONDITIONAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one conditional certificate being handed back to a rule.
fn note_consumed() { CONSUMED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// How many certificates finished conditional. Zero is the only value that lets
/// a file be called fully derived.
pub fn escaped() -> u64 {
    use std::sync::atomic::Ordering::Relaxed;
    CONDITIONAL.load(Relaxed).saturating_sub(CONSUMED.load(Relaxed))
}

/// Record one fully-derived certificate.
pub fn note_proved() { PROVED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one step taken on trust.
pub fn merge_one(reason: &'static str) {
    let mut g = TOTALS.lock().expect("tg totals poisoned");
    let v = g.get_or_insert_with(Vec::new);
    match v.iter_mut().find(|(r, _)| *r == reason) {
        Some((_, m)) => *m += 1,
        None => v.push((reason, 1)),
    }
}

/// Render what the TG kernel actually derived over this run.
pub fn global_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let g = TOTALS.lock().expect("tg totals poisoned");
    let proved = PROVED.load(Relaxed);
    let mut rows: Vec<(&'static str, u64)> = g.clone().unwrap_or_default();
    // An escaped assumption is a gap in exactly the sense the rest of this table
    // measures: a conclusion the checker took that was not derived outright.
    // It is added here rather than tallied through `merge_one` because it is
    // only knowable once the whole run is over.
    let escapes = escaped();
    if escapes > 0 {
        rows.push((ESCAPED, escapes));
    }
    rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    let width = rows.iter().map(|(r, _)| r.len() + 5).chain([24]).max().unwrap_or(24);
    let mut s = String::from("Tarski-Grothendieck kernel: derivation coverage\n");
    s.push_str(&format!("  {:<width$}  {proved:>12}\n", "derived (real kernel Thm)"));
    let total: u64 = rows.iter().map(|(_, n)| *n).sum();
    for (r, n) in &rows {
        s.push_str(&format!("  {:<width$}  {n:>12}\n", format!("gap: {r}")));
    }
    s.push_str(&format!("  {:<width$}  {total:>12}\n", "TOTAL gaps"));
    let made = CONDITIONAL.load(Relaxed);
    if made > 0 {
        s.push_str(&format!(
            "  conditional derivations: {} made ({} of them copies), {} accounted for by a rule, {} escaped (max {} assumptions)\n",
            made,
            CONDITIONAL_COPIES.load(Relaxed),
            CONSUMED.load(Relaxed),
            escapes,
            MAX_ASSUMED.load(Relaxed),
        ));
    }
    if total == 0 && proved > 0 {
        s.push_str("  >> every definitional-equality step was fully derived\n");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh constant, usable to instantiate a quantifier at.
    fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// [`lam_ext_n`] pinned to its *exact* conclusion, at a prefix on one side
    /// only — the asymmetric case, which is what `lam_cong` normally meets and
    /// which `derived::ext::lam_ext` cannot express.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `lam_cong` matches its result against the claim syntactically, so a
    /// lemma that is only *equivalent* to the intended one is useless.
    #[test]
    fn lam_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2); // t(p, x)
        let t2 = env.declare(1); // t'(x)
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let thm = lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_a2) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_a2.clone()]).expect("instantiate");

        let x = env.fresh_var();
        let tx = Term::var(x);
        let pointwise = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), big_a.clone()),
                Formula::eq(Term::apply(t, vec![p.clone(), tx.clone()]), Term::apply(t2, vec![tx])),
            ),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(lam, vec![p, big_a]), Term::apply(lam2, vec![big_a2])),
            ),
        );
        assert_eq!(*inst.concl(), expected, "lam_ext_n has the wrong shape");
    }

    /// A graph symbol whose arity does not match its body symbol's is refused,
    /// rather than yielding a theorem about a malformed term.
    #[test]
    fn lam_ext_n_rejects_mismatched_arities() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let wrong = env.declare(3);
        assert!(lam_ext_n(&mut env, &ap, t, wrong, &lam_ax, t2, lam2, &lam2_ax).is_none());
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, wrong, &lam2_ax).is_none());
        // A nullary body symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(lam_ext_n(&mut env, &ap, nullary, lam, &lam_ax, t2, lam2, &lam2_ax).is_none());
    }

    /// A `parts` map for the terms built here, mirroring [`TgBackend::mk`].
    fn mk_in(parts: &mut Parts, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        parts.insert(t.clone(), (f, args));
        t
    }

    /// [`retarget`] does what `pi_cong` needs: a certificate stated at a local
    /// becomes one stated at the bound-variable encoding, with *exactly* the
    /// wanted conclusion.
    #[test]
    fn retarget_reaims_a_certificate_at_the_de_bruijn_form() {
        let mut env = Env::new();
        let mut parts = Parts::new();
        let (f, bvar) = (env.declare(1), env.declare(1));
        // `bvar(idx₀)`, the interpretation of a loose de Bruijn index, and a
        // second constant to stand for a different one.
        let b0 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);
        let b1 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);

        // A genuinely non-reflexive certificate stated at a local: `⊢ d(v) = f(v)`.
        let v = env.fresh_var();
        let fv = mk_in(&mut parts, f, vec![Term::var(v)]);
        let (d, d_def) = derived::define_abbrev(&mut env, &[v], &fv).expect("define");
        let dv = mk_in(&mut parts, d, vec![Term::var(v)]);
        let cert = derived::inst_all(&d_def, &[Term::var(v)]).expect("instantiate");
        assert_eq!(*cert.concl(), Formula::eq(dv, fv), "the certificate is stated at the local");

        // Re-aimed at the raw form the claim uses, and *exactly* that.
        let (db, fb) = (mk_in(&mut parts, d, vec![b0.clone()]), mk_in(&mut parts, f, vec![b0.clone()]));
        let out = retarget(&parts, &cert, &db, &fb).expect("retarget should re-aim");
        assert_eq!(*out.concl(), Formula::eq(db.clone(), fb));

        // One local cannot become two different terms: the certificate says
        // nothing about `d(bvar₀) = f(bvar₁)` and must not be bent into it.
        let fb1 = mk_in(&mut parts, f, vec![b1.clone()]);
        assert!(retarget(&parts, &cert, &db, &fb1).is_none(), "inconsistent binding must be refused");

        // A head symbol the certificate does not have is refused outright.
        let db1 = mk_in(&mut parts, d, vec![b1]);
        assert!(retarget(&parts, &cert, &db1, &db).is_none(), "mismatched head symbol must be refused");

        // A term the backend never built cannot be taken apart.
        let stranger = Term::apply(f, vec![b0]);
        let mut bare = Parts::new();
        bare.insert(stranger.clone(), (f, vec![]));
        assert!(retarget(&bare, &cert, &stranger, &stranger).is_none(), "unknown structure must be refused");
    }

    /// A membership atom over fresh constants, to stand for an assumption.
    fn atom(env: &mut Env) -> Formula { Formula::mem(constant(env), constant(env)) }

    /// The left-nested conjunction is the one the discharge relies on:
    /// `conj(R ++ [h])` has to be `conj(R) ∧ h`, or `uncurry` peels the wrong
    /// assumption off and the binder discharges something it was not given.
    #[test]
    fn conj_is_left_nested_and_projects() {
        let mut env = Env::new();
        let hs: Vec<Formula> = (0..4).map(|_| atom(&mut env)).collect();
        let whole = conj_of(&hs).expect("non-empty");
        assert_eq!(whole, Formula::and(conj_of(&hs[..3]).expect("non-empty"), hs[3].clone()));
        assert_eq!(conj_of(&hs[..1]), Some(hs[0].clone()), "a single assumption is itself");
        assert_eq!(conj_of(&[]), None);

        for (i, h) in hs.iter().enumerate() {
            let p = conj_proj(&hs, i).expect("projection");
            assert_eq!(*p.concl(), Formula::imp(whole.clone(), h.clone()), "projection {i}");
        }
        assert!(conj_proj(&hs, 4).is_none(), "out of range");
    }

    /// `reassume` really re-states a derivation, and only under a *superset*:
    /// re-stating under assumptions that do not include the ones actually used
    /// would be exactly the way to lose an obligation silently.
    #[test]
    fn reassume_restates_and_reorders() {
        let mut env = Env::new();
        let (h1, h2, h3) = (atom(&mut env), atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let eq = Formula::eq(c.clone(), c.clone());

        // ⊢ (h1 ∧ h2) → c = c
        let from = vec![h1.clone(), h2.clone()];
        let base = derived::a1i(&Thm::eq_refl(c.clone()), conj_of(&from).expect("non-empty"));

        // Reordered and extended.
        let to = vec![h3.clone(), h2.clone(), h1.clone()];
        let out = reassume(&base, &from, &to).expect("re-statement");
        assert_eq!(*out.concl(), Formula::imp(conj_of(&to).expect("non-empty"), eq.clone()));

        // Dropping an assumption that is genuinely used is refused.
        assert!(reassume(&base, &from, &[h1.clone()]).is_none(), "must not shed an assumption");
        assert!(reassume(&base, &from, &[]).is_none(), "must not shed every assumption");
        // An unconditional theorem may of course be weakened.
        let plain = Thm::eq_refl(c);
        let weak = reassume(&plain, &[], std::slice::from_ref(&h1)).expect("weakening");
        assert_eq!(*weak.concl(), Formula::imp(h1, eq));
    }

    /// `CondEq` refuses to describe a theorem it does not have: an assumption
    /// list that is not the theorem's antecedent is rejected outright, which is
    /// what stops a rule from advertising a discharged obligation it never
    /// discharged.
    #[test]
    fn cond_eq_checks_its_own_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let refl = Thm::eq_refl(c.clone());

        assert!(CondEq::new(refl.clone(), vec![]).is_some(), "a bare equation assumes nothing");
        assert!(CondEq::new(refl.clone(), vec![h1.clone()]).is_none(), "an equation is not an implication");

        let under_h1 = derived::a1i(&refl, h1.clone());
        assert!(CondEq::new(under_h1.clone(), vec![h1.clone()]).is_some());
        assert!(CondEq::new(under_h1.clone(), vec![h2.clone()]).is_none(), "the wrong assumption");
        assert!(CondEq::new(under_h1.clone(), vec![]).is_none(), "assumption cannot be dropped");
        assert!(CondEq::new(under_h1, vec![h1, h2]).is_none(), "assumption cannot be invented");

        // The conclusion has to be an equation, whatever the antecedent is.
        let not_eq = derived::imp_refl(Formula::false_());
        assert!(CondEq::new(not_eq, vec![Formula::false_()]).is_none());
    }

    /// Transitivity across two derivations with different assumptions produces
    /// the union, as a real antecedent.
    #[test]
    fn conditional_transitivity_merges_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let b = constant(&mut env);
        // ⊢ h1 → d = b and ⊢ h2 → b = b, from a genuine equation and reflexivity.
        let (d, d_def) = derived::define_abbrev(&mut env, &[], &b).expect("define");
        let ab = derived::inst_all(&d_def, &[]).expect("instantiate"); // ⊢ d = b
        let da = Term::apply(d, vec![]);

        let c1 = CondEq::new(derived::a1i(&ab, h1.clone()), vec![h1.clone()]).expect("conditional");
        let c2 = CondEq::new(derived::a1i(&Thm::eq_refl(b.clone()), h2.clone()), vec![h2.clone()]).expect("cond");

        let hyps = merge_hyps(&c1.hyps, &c2.hyps);
        let h = conj_of(&hyps).expect("non-empty");
        let x = reassume(&c1.thm, &c1.hyps, &hyps).expect("restate");
        let y = reassume(&c2.thm, &c2.hyps, &hyps).expect("restate");
        let out = u_eq_trans(&mut env, &x, &y, Some(&h)).expect("transitivity");
        assert_eq!(*out.concl(), Formula::imp(Formula::and(h1, h2), Formula::eq(da, b)));
    }

    /// A characteristic axiom that is not the one `lambda_n` produces for the
    /// symbol at hand is rejected: the derivation would otherwise be sound but
    /// about the wrong sets, and silently so.
    #[test]
    fn lam_ext_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");
        // The two axioms swapped over: right shape, wrong symbols.
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam2_ax, t2, lam2, &lam_ax).is_none());
    }
}
