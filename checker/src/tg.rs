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
//! symbols with *no* axioms (`pi`, `let`, `proj`, `bvar`, the level formers,
//! …). That is unconditionally conservative, so nothing here enlarges the
//! trusted base or risks consistency. Three parts of the interpretation are
//! now *definitional extensions* instead, which is what makes them mean
//! something:
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
//! The extra parameters are why `lambda_n` and `beta_conditional_n` exist:
//! the derived originals take a unary body symbol, and `t` here has arity
//! `k + 1`. They are the derived derivations with the prefix threaded through,
//! and coincide with them at `k = 0`.
//!
//! # What beta still costs
//!
//! `beta_conditional` is *conditional*: a set-theoretic function has a set
//! domain, so `app(lam(A), a) = t(a)` needs `a ∈ A`. Discharging that is a
//! **typing** obligation — `⟦a⟧ ∈ ⟦A⟧` whenever Lean says `a : A` — and this
//! backend has exactly one instance of it, `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧`. So a
//! beta step closes when every argument is a sort sitting in the next universe
//! up, and is reported as a gap otherwise. That is not a limitation of the
//! derivation but of the interpretation: nothing here yet says what it means
//! for a Lean term to *inhabit* a Lean type.
//!
//! # Honesty
//!
//! [`Certifier::beta`] and [`Certifier::delta`], the two rules that build a
//! chain rather than read one off, check before returning [`TgCert::Proved`]
//! that the theorem they hold is literally `⟦a⟧ = ⟦b⟧` for the `a`, `b` the
//! checker claimed equal; `refl`, `sort` and `const_eq` compare the two
//! interpretations directly.
//!
//! The congruence rules are the exception, and not by choice: they are handed
//! sub-*certificates* rather than terms, so they cannot see what they are
//! supposed to be proving. [`Certifier::lam_cong`] therefore reports a gap
//! rather than produce a theorem it cannot match against the claim.
//! [`Certifier::app_cong`] and [`Certifier::pi_cong`] do still apply
//! congruence, which is right for `app` but inherits a pre-existing looseness
//! for `pi`: the checker compares binder *bodies* after opening them at a
//! local, so what `pi_cong` proves is `pi(⟦A⟧, ⟦b[v]⟧) = pi(⟦A'⟧, ⟦b'[v]⟧)`,
//! whereas `⟦Π x:A. b⟧` keeps the body in de Bruijn form. The two agree after
//! generalising `v` and instantiating it at the bound-variable encoding, but
//! that step is not taken here. It predates this backend's beta work and is
//! left as is.

use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use crate::expr::Expr;
use crate::level::Level;
use derived::funcs::Apply;
use kernel::{Certifier, Env, FnSym, Formula, FreeVar, Term, Thm};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::rc::Rc;

/// A certificate: either a real kernel theorem, or a named gap.
///
/// Making the gap a *variant* rather than a silent success is the point. A
/// backend that could only return `Thm` would have to either refuse (breaking
/// the checker) or forge (defeating the exercise); this way an unproved step is
/// recorded, propagates through the combinators, and can be reported.
#[derive(Debug, Clone)]
pub enum TgCert {
    /// A genuine derivation of `⟦a⟧ = ⟦b⟧`.
    Proved(Thm),
    /// A step that was taken on trust, tagged with why.
    Admitted(&'static str),
}

impl TgCert {
    /// The underlying theorem, if this step was actually proved.
    pub fn thm(&self) -> Option<&Thm> {
        match self {
            TgCert::Proved(t) => Some(t),
            TgCert::Admitted(_) => None,
        }
    }
    /// Whether this certificate is a complete derivation.
    pub fn is_proved(&self) -> bool { matches!(self, TgCert::Proved(_)) }
}

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
// ─────────────────────────────────────────────────────────────────────────────

/// The once-per-thread part of the interpretation's machinery.
struct Prelude {
    /// Set-theoretic application, and everything it is built from.
    ap: Apply,
    /// The least-universe operator `U`.
    u_sym: FnSym,
    /// `⊢ ∀x. x ∈ U(x)`.
    mem_u: Thm,
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
        let (u_sym, u_ax) = derived::universe::least_universe(&mut env).expect("TG prelude: least universe");
        let mem_u = derived::universe::mem_least_universe(&mut env, u_sym, &u_ax)
            .expect("TG prelude: membership in the least universe");
        // One extra of each, purely to read the counters back out.
        let n_syms = env.declare(0).id() + 1;
        let n_vars = env.fresh_var().id() + 1;
        let p = Rc::new(Prelude { ap, u_sym, mem_u, n_syms, n_vars });
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

/// The function symbols the interpretation uses that carry *no* axioms.
///
/// All are introduced by signature extension; that is sound but limiting, and
/// it is why the rules over them (`pi_cong`, `zeta`, …) stay in the equational
/// fragment. `sort`, `lam` and `app` are *not* here: those three are now real
/// definitional extensions, held in [`Prelude`] and [`TgBackend::lam_infos`].
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
    /// The graph machinery, when it was built; `None` for the inert encoding
    /// (see [`MAX_HOLES`]), in which case `lam` is an opaque symbol and beta
    /// over this lambda reports a gap.
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

/// How many abstracted subterms a lambda body may have before the graph
/// construction is skipped.
///
/// Each new skeleton costs a `define_abbrev` plus a [`lambda_n`], and the
/// latter is a full Replacement-and-Extensionality derivation whose size grows
/// with the parameter count — on the order of 130µs, plus another 13µs per
/// hole. `good/init-prelude.ndjson` reaches some 31k distinct skeletons, so
/// paying that unconditionally adds ~13s to a 1.7s run, which is not a
/// reasonable price for a *checker*.
///
/// The cut-off is a pure performance guard, and it is safe by construction: the
/// hole count is a function of the skeleton alone, and the skeleton is stable
/// under substitution, so the choice of encoding cannot differ between the two
/// sides of a reduction — a skipped lambda just makes beta report a gap.
///
/// Nothing measurable is lost at this value: the coverage over that corpus is
/// byte-identical at 2, 4, 8, 16 and no cut-off at all. What limits beta is the
/// domain premise (see the module docs), and the bodies that need a large
/// skeleton are not the ones whose arguments are sorts.
const MAX_HOLES: usize = 8;

/// Where one particular lambda *occurrence* sits: which skeleton it uses, and
/// with what arguments.
struct LamSite {
    /// Key into [`TgBackend::lam_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

/// The Tarski–Grothendieck backend.
pub struct TgBackend<'x, 't: 'x, 'p: 't> {
    /// The kernel signature and variable source.
    env: Env,
    /// The application machinery and the universe operator, shared per thread.
    pre: Rc<Prelude>,
    /// The checker's declaration environment, used to resolve a constant to its
    /// value so that `⟦c⟧` can be an *explicit definition* rather than an opaque
    /// symbol. This is what makes delta reduction justifiable at all.
    decls: &'x crate::env::Env<'x, 't>,
    /// Defining equations `⊢ ⟦c⟧ = ⟦value⟧`, keyed by the constant's expression
    /// node. Delta certificates are built from these by congruence.
    const_defs: HashMap<ExprPtr<'t>, Thm>,
    syms: Syms,
    /// Interpretation cache. Without it, interpreting nested expressions would
    /// be quadratic; with it, each hash-consed Lean node is translated once.
    exprs: HashMap<ExprPtr<'t>, Term>,
    levels: HashMap<LevelPtr<'t>, Term>,
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
    /// Head symbol (and, when built, graph machinery) per distinct skeleton.
    lam_infos: HashMap<Term, Rc<LamInfo>>,
    /// Beta theorems, derived lazily: most lambdas are never a redex head.
    lam_betas: HashMap<Term, Option<Thm>>,
    /// Where each lambda occurrence sits.
    lam_sites: HashMap<ExprPtr<'t>, LamSite>,
    /// Canonical variables for skeletons, so that two lambdas with the same
    /// body shape produce the *same* key. Reused across skeletons: they are
    /// abstracted away by `define_abbrev` immediately and never escape.
    hole_vars: Vec<FreeVar>,
    x_canon: FreeVar,

    _marker: PhantomData<&'p ()>,
}

impl<'x, 't: 'x, 'p: 't> TgBackend<'x, 't, 'p> {
    /// A fresh backend with its own signature.
    pub fn new(decls: &'x crate::env::Env<'x, 't>) -> Self {
        let pre = prelude();
        let mut env = Env::new();
        fast_forward(&mut env, &pre);
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
        TgBackend {
            env,
            pre,
            decls,
            const_defs: HashMap::new(),
            syms,
            exprs: HashMap::new(),
            levels: HashMap::new(),
            consts: HashMap::new(),
            locals: HashMap::new(),
            params: HashMap::new(),
            idxs: HashMap::new(),
            parts: HashMap::new(),
            lam_infos: HashMap::new(),
            lam_betas: HashMap::new(),
            lam_sites: HashMap::new(),
            hole_vars: Vec::new(),
            x_canon,
            _marker: PhantomData,
        }
    }

    /// Build `f(args)` and remember its shape, so that [`Self::skeleton`] can
    /// take it apart again later.
    fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        self.parts.entry(t.clone()).or_insert((f, args));
        t
    }

    /// Wrap a derived theorem, tallying it for the coverage report.
    fn proved(&mut self, t: Thm) -> TgCert {
        note_proved();
        TgCert::Proved(t)
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
        let s = self.env.declare(0);
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
                    let s = self.env.declare(0);
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
        let l = ctx.simplify(level);
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
        while self.hole_vars.len() <= i {
            let v = self.env.fresh_var();
            self.hole_vars.push(v);
        }
        self.hole_vars[i]
    }

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
        let v = self.env.fresh_var();
        self.locals.insert(key, v);
        let body_open = ctx.inst(body, &[local]);
        let bt = self.interp(ctx, body_open);

        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;

        let info = match self.lam_infos.get(&sk) {
            Some(i) => i.clone(),
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = if holes.len() > MAX_HOLES {
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // beta. Costs one signature extension and nothing else.
                    Rc::new(LamInfo { lam: self.env.declare(arity), graph: None })
                } else {
                    let mut ps: Vec<FreeVar> = Vec::with_capacity(holes.len() + 1);
                    for i in 0..holes.len() {
                        ps.push(self.hole_var(i));
                    }
                    ps.push(self.x_canon);
                    let (t, t_def) = derived::define_abbrev(&mut self.env, &ps, &sk)?;
                    let (lam, lam_ax) = lambda_n(&mut self.env, &self.pre.clone().ap, t)?;
                    Rc::new(LamInfo { lam, graph: Some(Graph { t, t_def, lam_ax }) })
                };
                self.lam_infos.insert(sk.clone(), info.clone());
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
                    let Some((sym, axiom)) = derived::define_abbrev(&mut self.env, &[], &body) else {
                        let s = self.env.declare(0);
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
                            let s = self.env.declare(arity);
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
                        let s = self.env.declare(1);
                        self.mk(s, vec![d])
                    }
                }
            }
            Expr::Pi { binder_type, body, .. } => {
                let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                self.mk(self.syms.pi, vec![d, b])
            }
            Expr::Let { binder_type, val, body, .. } => {
                let (ty, v, b) = (self.interp(ctx, binder_type), self.interp(ctx, val), self.interp(ctx, body));
                self.mk(self.syms.let_, vec![ty, v, b])
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
                        let v = self.env.fresh_var();
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
                let s = self.env.declare(0);
                self.mk(s, vec![])
            }
        };
        self.exprs.insert(e, t.clone());
        t
    }

    /// Congruence for a binary interpretation symbol, from certificates for the
    /// two sub-positions.
    fn cong2(&mut self, sym: FnSym, a: TgCert, b: TgCert) -> TgCert {
        let (ta, tb) = match (a.thm().cloned(), b.thm().cloned()) {
            (Some(x), Some(y)) => (x, y),
            // A gap anywhere below means the whole congruence is a gap; there is
            // nothing to prove congruence *from*.
            _ => return self.note_admit("congruence over an admitted premise"),
        };
        match derived::congr(&mut self.env, sym, &[ta, tb]) {
            Some(t) => self.proved(t),
            None => self.note_admit("congruence rule refused"),
        }
    }

    /// The beta theorem for one lambda skeleton, derived on first use.
    fn beta_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.lam_betas.get(key) {
            return t.clone()
        }
        let info = self.lam_infos.get(key)?.clone();
        let g = info.graph.as_ref()?;
        let (t, lam, lam_ax) = (g.t, info.lam, g.lam_ax.clone());
        let ap = self.pre.clone();
        let thm = beta_conditional_n(&mut self.env, &ap.ap, t, lam, &lam_ax);
        self.lam_betas.insert(key.clone(), thm.clone());
        thm
    }

    /// One beta contraction: `⊢ app(⟦λ⟧, ⟦a⟧) = ⟦body[a]⟧`.
    fn beta_step(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam_expr: ExprPtr<'t>,
        body: ExprPtr<'t>,
        arg: ExprPtr<'t>,
    ) -> Result<(Thm, ExprPtr<'t>), &'static str> {
        // Interpreting the lambda is what registers its graph symbol.
        let _ = self.interp(ctx, lam_expr);
        let Some(site) = self.lam_sites.get(&lam_expr) else {
            return Err("beta: the lambda has no function-graph interpretation")
        };
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let ta = self.interp(ctx, arg);

        // The domain premise is checked *first*: it is a term comparison, while
        // the beta lemma below is a derivation, and most redexes fail here.
        //
        // The only typing fact this interpretation supplies is `x ∈ U(x)`, i.e.
        // a sort sits in the next universe up. Anything else is a genuine gap,
        // not a shortcut.
        if dom != Term::apply(self.pre.u_sym, vec![ta.clone()]) {
            return Err("beta: argument not shown to lie in the binder's domain")
        }
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

        let mem = self.pre.mem_u.clone();
        let Some(mem_inst) = derived::inst_all(&mem, std::slice::from_ref(&ta)) else {
            return Err("beta: instantiating x ∈ U(x) failed")
        };
        let Some(eq_t) = Thm::mp(&conditional, &mem_inst) else {
            return Err("beta: discharging the domain premise failed")
        };

        // Unfold `t(h⃗, ⟦a⟧)` to the skeleton with the argument plugged in, and
        // check that is literally the interpretation of the contracted body.
        let info = self.lam_infos.get(&key).expect("skeleton registered").clone();
        let Some(g) = info.graph.as_ref() else {
            return Err("beta: the lambda's graph was not built")
        };
        let mut inst_t = holes;
        inst_t.push(ta);
        let Some(unfold) = derived::inst_all(&g.t_def, &inst_t) else {
            return Err("beta: instantiating the body definition failed")
        };
        let Some(step) = derived::eq_trans(&mut self.env, &eq_t, &unfold) else {
            return Err("beta: chaining the body definition failed")
        };

        let next = ctx.inst(body, &[arg]);
        let tnext = self.interp(ctx, next);
        let Some((_, rhs)) = step.concl().as_eq() else {
            return Err("beta: the derived step is not an equation")
        };
        if rhs != tnext {
            return Err("beta: the contracted body does not match its interpretation")
        }
        Ok((step, next))
    }

    /// The whole (possibly multi-argument) beta contraction the checker asked
    /// for, as `⊢ ⟦redex⟧ = ⟦reduct⟧`.
    fn derive_beta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<Thm, &'static str> {
        let (fun, args) = ctx.unfold_apps(redex);
        if args.is_empty() {
            return Err("beta: the redex is not an application")
        }
        let mut cur = fun;
        let mut acc = Thm::eq_refl(self.interp(ctx, fun));
        let app = self.pre.ap.app;

        for arg in args {
            let ta = self.interp(ctx, arg);
            let Some(lifted) = derived::congr(&mut self.env, app, &[acc.clone(), Thm::eq_refl(ta)]) else {
                return Err("beta: congruence over the spine refused")
            };
            acc = lifted;
            // The checker contracts every leading lambda it can and re-applies
            // whatever is left over, so stop peeling at the first non-lambda and
            // let congruence carry the rest.
            if let Expr::Lambda { body, .. } = ctx.read_expr(cur) {
                let (step, next) = self.beta_step(ctx, cur, body, arg)?;
                let Some(chained) = derived::eq_trans(&mut self.env, &acc, &step) else {
                    return Err("beta: chaining a contraction failed")
                };
                acc = chained;
                cur = next;
            }
        }

        // Guard. The derivation is worth nothing unless it is a derivation of
        // the equation the checker actually claimed.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *acc.concl() != Formula::eq(lhs, rhs) {
            return Err("beta: derived equation does not match the reduction")
        }
        Ok(acc)
    }
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
        match c.thm() {
            Some(t) => match derived::eq_symm(&mut self.env, &t.clone()) {
                Some(t) => self.proved(t),
                None => self.note_admit("symm refused"),
            },
            None => self.note_admit("symm over an admitted premise"),
        }
    }

    fn trans(&mut self, _ctx: &mut Self::Ctx, ab: TgCert, bc: TgCert) -> TgCert {
        match (ab.thm().cloned(), bc.thm().cloned()) {
            (Some(x), Some(y)) => match derived::eq_trans(&mut self.env, &x, &y) {
                Some(t) => self.proved(t),
                None => self.note_admit("trans refused"),
            },
            _ => self.note_admit("trans over an admitted premise"),
        }
    }

    fn app_cong(&mut self, _ctx: &mut Self::Ctx, f: TgCert, a: TgCert) -> TgCert {
        let s = self.pre.ap.app;
        self.cong2(s, f, a)
    }

    /// **A gap, not a rule.**
    ///
    /// `⟦λx:A. b⟧` is now a function *graph* `lam_C(s⃗, ⟦A⟧)` whose head symbol
    /// depends on the shape of the body, so congruence in the two sub-positions
    /// no longer yields the claim: from `⊢ ⟦A⟧ = ⟦A'⟧` and `⊢ ⟦b⟧ = ⟦b'⟧` one
    /// would have to conclude `⊢ lam_C(s⃗,⟦A⟧) = lam_C'(s⃗',⟦A'⟧)` for two
    /// *different* symbols, which needs extensionality of graphs and a
    /// pointwise-equality premise, not congruence.
    ///
    /// The rule is handed sub-certificates rather than the two lambdas, so it
    /// cannot even identify which lambdas it is about, let alone check a result
    /// against them. Reporting the gap is the only honest option; producing the
    /// old `lam(d,b) = lam(d',b')` would be a theorem about a symbol that is no
    /// longer part of the interpretation.
    fn lam_cong(&mut self, _ctx: &mut Self::Ctx, _dom: TgCert, _body: TgCert) -> TgCert {
        self.note_admit("lam congruence (needs graph extensionality)")
    }

    fn pi_cong(&mut self, _ctx: &mut Self::Ctx, dom: TgCert, body: TgCert) -> TgCert {
        let s = self.syms.pi;
        self.cong2(s, dom, body)
    }

    fn beta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        match self.derive_beta(ctx, redex, reduct) {
            Ok(t) => self.proved(t),
            Err(reason) => self.note_admit(reason),
        }
    }

    fn zeta(&mut self, _ctx: &mut Self::Ctx, _redex: Self::Term, _reduct: Self::Term) -> TgCert {
        self.note_admit("zeta (needs let defining axiom)")
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
            match derived::congr(&mut self.env, app, &[acc, refl]) {
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
    let g = TOTALS.lock().expect("tg totals poisoned");
    let proved = PROVED.load(std::sync::atomic::Ordering::Relaxed);
    let mut rows: Vec<(&'static str, u64)> = g.clone().unwrap_or_default();
    rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    let width = rows.iter().map(|(r, _)| r.len() + 5).chain([24]).max().unwrap_or(24);
    let mut s = String::from("Tarski-Grothendieck kernel: derivation coverage\n");
    s.push_str(&format!("  {:<width$}  {proved:>12}\n", "derived (real kernel Thm)"));
    let total: u64 = rows.iter().map(|(_, n)| *n).sum();
    for (r, n) in &rows {
        s.push_str(&format!("  {:<width$}  {n:>12}\n", format!("gap: {r}")));
    }
    s.push_str(&format!("  {:<width$}  {total:>12}\n", "TOTAL gaps"));
    if total == 0 && proved > 0 {
        s.push_str("  >> every definitional-equality step was fully derived\n");
    }
    s
}
