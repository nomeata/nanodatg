//! The Tarski–Grothendieck proof backend: real [`kernel::Thm`] certificates.
//!
//! # What this does and does not claim
//!
//! Every Lean expression is interpreted as a term of the kernel's first-order
//! language, and every definitional-equality certificate is a genuine kernel
//! theorem `⟦a⟧ = ⟦b⟧` — derived from the equality axioms by real inference
//! rules, not asserted.
//!
//! The function symbols used by the interpretation (`sort`, `pi`, `lam`, `app`,
//! …) are introduced by **pure signature extension**: fresh symbols with *no*
//! axioms. That is unconditionally conservative, so nothing here enlarges the
//! trusted base or risks consistency.
//!
//! The price of taking no axioms is that the symbols mean nothing yet, so only
//! the *equational* fragment can be discharged: reflexivity, symmetry,
//! transitivity and congruence hold for any function symbols whatever. Rules
//! that depend on what the symbols denote — beta above all, which needs `lam`
//! and `app` to actually be a function and its application — cannot be proved
//! from nothing and are reported as [`TgCert::Admitted`]. Closing those
//! requires defining axioms introduced by conservative definitional extension,
//! which is the next piece of work.
//!
//! This is exactly the split the project cares about: the checker can now say,
//! per declaration, whether it was accepted on the strength of a complete
//! derivation or whether some step was taken on trust.

use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use crate::expr::Expr;
use crate::level::Level;
use kernel::{Certifier, Env, FnSym, Term, Thm};
use std::collections::HashMap;
use std::marker::PhantomData;

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

/// The function symbols the interpretation uses.
///
/// All are introduced by signature extension with no defining axioms; see the
/// module docs for why that is both sound and limiting.
struct Syms {
    sort: FnSym,
    pi: FnSym,
    lam: FnSym,
    app: FnSym,
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
}

/// The Tarski–Grothendieck backend.
pub struct TgBackend<'t, 'p: 't> {
    env: Env,
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
    /// Count of steps taken on trust, by reason.
    admitted: Vec<(&'static str, u64)>,
    _marker: PhantomData<&'p ()>,
}

impl<'t, 'p: 't> Default for TgBackend<'t, 'p> {
    fn default() -> Self { Self::new() }
}

impl<'t, 'p: 't> TgBackend<'t, 'p> {
    /// A fresh backend with its own signature.
    pub fn new() -> Self {
        let mut env = Env::new();
        let syms = Syms {
            sort: env.declare(1),
            pi: env.declare(2),
            lam: env.declare(2),
            app: env.declare(2),
            let_: env.declare(3),
            proj: env.declare(2),
            bvar: env.declare(1),
            lzero: env.declare(0),
            lsucc: env.declare(1),
            lmax: env.declare(2),
            limax: env.declare(2),
            idx: env.declare(1),
        };
        TgBackend {
            env,
            syms,
            exprs: HashMap::new(),
            levels: HashMap::new(),
            consts: HashMap::new(),
            locals: HashMap::new(),
            params: HashMap::new(),
            idxs: HashMap::new(),
            admitted: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// How many steps were taken on trust, and why.
    pub fn admitted(&self) -> &[(&'static str, u64)] { &self.admitted }

    /// Wrap a derived theorem, tallying it for the coverage report.
    fn proved(&mut self, t: Thm) -> TgCert {
        note_proved();
        TgCert::Proved(t)
    }

    fn note_admit(&mut self, reason: &'static str) -> TgCert {
        match self.admitted.iter_mut().find(|(r, _)| *r == reason) {
            Some((_, n)) => *n += 1,
            None => self.admitted.push((reason, 1)),
        }
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
        let t = Term::apply(self.syms.idx, vec![Term::apply(s, vec![])]);
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
            Level::Zero => Term::apply(self.syms.lzero, vec![]),
            Level::Succ(a, _) => {
                let a = self.interp_level(ctx, a);
                Term::apply(self.syms.lsucc, vec![a])
            }
            Level::Max(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                Term::apply(self.syms.lmax, vec![a, b])
            }
            Level::IMax(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                Term::apply(self.syms.limax, vec![a, b])
            }
            Level::Param(n, _) => {
                if let Some(t) = self.params.get(&n) {
                    t.clone()
                } else {
                    let s = self.env.declare(0);
                    let t = Term::apply(s, vec![]);
                    self.params.insert(n, t.clone());
                    t
                }
            }
        };
        self.levels.insert(l, t.clone());
        t
    }

    fn interp_levels(&mut self, ctx: &mut TcCtx<'t, 'p>, ls: LevelsPtr<'t>) -> Vec<Term> {
        ctx.read_levels(ls).iter().copied().collect::<Vec<_>>().into_iter().map(|l| self.interp_level(ctx, l)).collect()
    }

    /// Interpret a Lean expression as a kernel term.
    pub fn interp(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Term {
        if let Some(t) = self.exprs.get(&e) {
            return t.clone()
        }
        let t = match ctx.read_expr(e) {
            Expr::Sort { level, .. } => {
                let l = self.interp_level(ctx, level);
                Term::apply(self.syms.sort, vec![l])
            }
            Expr::Var { dbj_idx, .. } => {
                let i = self.idx_term(dbj_idx as u64);
                Term::apply(self.syms.bvar, vec![i])
            }
            Expr::Const { name, levels, .. } => {
                let args = self.interp_levels(ctx, levels);
                let arity = u32::try_from(args.len()).expect("universe parameter count overflow");
                // One symbol per constant name, of arity equal to its number of
                // universe parameters, so `c.{u}` and `c.{v}` differ exactly when
                // their levels do.
                let sym = match self.consts.get(&name) {
                    Some(s) if s.arity() == arity => *s,
                    _ => {
                        let s = self.env.declare(arity);
                        self.consts.insert(name, s);
                        s
                    }
                };
                Term::apply(sym, args)
            }
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.interp(ctx, fun), self.interp(ctx, arg));
                Term::apply(self.syms.app, vec![f, a])
            }
            Expr::Lambda { binder_type, body, .. } => {
                let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                Term::apply(self.syms.lam, vec![d, b])
            }
            Expr::Pi { binder_type, body, .. } => {
                let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                Term::apply(self.syms.pi, vec![d, b])
            }
            Expr::Let { binder_type, val, body, .. } => {
                let (ty, v, b) = (self.interp(ctx, binder_type), self.interp(ctx, val), self.interp(ctx, body));
                Term::apply(self.syms.let_, vec![ty, v, b])
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
                Term::apply(self.syms.proj, vec![i, s])
            }
            // Literals get one opaque nullary symbol each. Distinct literals get
            // distinct symbols because the whole match is memoised on the
            // hash-consed `ExprPtr`, so equal literals are the same node.
            // Milestone 4 replaces these with the kernel's primitive `ℕ` and its
            // native bignum rule schemas.
            Expr::NatLit { .. } | Expr::StringLit { .. } => {
                let s = self.env.declare(0);
                Term::apply(s, vec![])
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
        match Thm::congr(&mut self.env, sym, &[ta, tb]) {
            Some(t) => self.proved(t),
            None => self.note_admit("congruence rule refused"),
        }
    }
}

impl<'t, 'p: 't> Drop for TgBackend<'t, 'p> {
    fn drop(&mut self) { merge(&self.admitted); }
}

impl<'t, 'p: 't> Certifier for TgBackend<'t, 'p> {
    type Term = ExprPtr<'t>;
    type Cert = TgCert;
    type Ctx = TcCtx<'t, 'p>;

    fn refl(&mut self, ctx: &mut Self::Ctx, a: Self::Term) -> TgCert {
        let t = self.interp(ctx, a);
        self.proved(Thm::eq_refl(t))
    }

    fn symm(&mut self, _ctx: &mut Self::Ctx, c: TgCert) -> TgCert {
        match c.thm() {
            Some(t) => match Thm::eq_symm(&mut self.env, &t.clone()) {
                Some(t) => self.proved(t),
                None => self.note_admit("symm refused"),
            },
            None => self.note_admit("symm over an admitted premise"),
        }
    }

    fn trans(&mut self, _ctx: &mut Self::Ctx, ab: TgCert, bc: TgCert) -> TgCert {
        match (ab.thm().cloned(), bc.thm().cloned()) {
            (Some(x), Some(y)) => match Thm::eq_trans(&mut self.env, &x, &y) {
                Some(t) => self.proved(t),
                None => self.note_admit("trans refused"),
            },
            _ => self.note_admit("trans over an admitted premise"),
        }
    }

    fn app_cong(&mut self, _ctx: &mut Self::Ctx, f: TgCert, a: TgCert) -> TgCert {
        let s = self.syms.app;
        self.cong2(s, f, a)
    }

    fn lam_cong(&mut self, _ctx: &mut Self::Ctx, dom: TgCert, body: TgCert) -> TgCert {
        let s = self.syms.lam;
        self.cong2(s, dom, body)
    }

    fn pi_cong(&mut self, _ctx: &mut Self::Ctx, dom: TgCert, body: TgCert) -> TgCert {
        let s = self.syms.pi;
        self.cong2(s, dom, body)
    }

    fn beta(&mut self, _ctx: &mut Self::Ctx, _redex: Self::Term, _reduct: Self::Term) -> TgCert {
        // Beta needs `lam` and `app` to denote a function and its application,
        // which requires defining axioms this signature deliberately does not
        // have. See the module docs.
        self.note_admit("beta (needs lam/app defining axioms)")
    }

    fn zeta(&mut self, _ctx: &mut Self::Ctx, _redex: Self::Term, _reduct: Self::Term) -> TgCert {
        self.note_admit("zeta (needs let defining axiom)")
    }

    fn delta(&mut self, _ctx: &mut Self::Ctx, _redex: Self::Term, _reduct: Self::Term) -> TgCert {
        self.note_admit("delta (needs the environment's defining axioms)")
    }

    fn eta(&mut self, _ctx: &mut Self::Ctx, _a: Self::Term, _b: Self::Term) -> TgCert {
        self.note_admit("eta (needs lam/app defining axioms)")
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

/// Merge a finished backend's tallies into the run totals.
pub fn merge(admitted: &[(&'static str, u64)]) {
    let mut g = TOTALS.lock().expect("tg totals poisoned");
    let v = g.get_or_insert_with(Vec::new);
    for (reason, n) in admitted {
        match v.iter_mut().find(|(r, _)| r == reason) {
            Some((_, m)) => *m += n,
            None => v.push((reason, *n)),
        }
    }
}

/// Render what the TG kernel actually derived over this run.
pub fn global_report() -> String {
    let g = TOTALS.lock().expect("tg totals poisoned");
    let proved = PROVED.load(std::sync::atomic::Ordering::Relaxed);
    let mut rows: Vec<(&'static str, u64)> = g.clone().unwrap_or_default();
    rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    let width = rows.iter().map(|(r, _)| r.len()).chain([24]).max().unwrap_or(24);
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
