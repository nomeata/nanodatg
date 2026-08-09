//! Terms and formulas of first-order logic with `∈`.
//!
//! # The capture problem, and how it is designed away
//!
//! Capture-avoiding substitution is the classic soundness hole in an LCF
//! kernel, and free-variable side conditions are where FOL kernel bugs actually
//! live. Rather than implement capture-avoidance and hope the tests find the
//! bugs, this module makes the bad states **unrepresentable**:
//!
//! * The representation is *locally nameless*: bound occurrences are de Bruijn
//!   indices ([`TermData::Bound`]), free occurrences are named
//!   ([`TermData::Free`]). The two are different constructors, so substituting
//!   for a free variable can never accidentally capture — free variables are
//!   not what binders bind.
//! * There is **no public way to build a `Bound`**. The only way to get one is
//!   [`Formula::forall`], which *closes* over a named free variable. So a
//!   dangling index cannot be constructed by a client at all, and every `Term`
//!   handed out is locally closed.
//!
//! What remains is the correctness of `close`/`open` themselves, which is a
//! dozen lines each and is tested adversarially in `tests/substitution.rs`.

use std::rc::Rc;

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};

/// A free variable, identified by an opaque number.
///
/// Distinctness of free variables is decided by this number, so the
/// distinct-variable conditions that plague named representations reduce to
/// integer inequality.
/// A free variable, identified by an opaque number *and the generator that
/// produced it*.
///
/// The brand matters for soundness. Freshness is a per-generator property, but
/// without a brand `FreeVar` identity would be global, so a variable minted by
/// a second generator could alias one an inference rule believed to be fresh —
/// and the rules' freshness assumptions (`ax_replacement`'s `a`/`b`/`y2`,
/// `exists_unique`'s `y2`) are exactly what stop those variables being captured.
/// Branding makes such a collision impossible rather than merely unlikely.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FreeVar {
    brand: u32,
    id: u32,
}

impl FreeVar {
    /// The underlying identifier. Only meaningful alongside the brand.
    pub fn id(self) -> u32 { self.id }
}

/// Source of fresh free variables.
///
/// Freshness matters: reusing a variable that already occurs somewhere would
/// silently identify two different things. The counter only ever increases.
/// Source of fresh free variables.
///
/// **Not public.** The only way to obtain a `FreeVar` is [`crate::Env::fresh_var`],
/// so every variable in circulation belongs to some `Env` and carries its brand.
/// Exposing a constructor here would let a client mint variables that collide
/// with ones the inference rules assume fresh — a demonstrated route to `⊢ ⊥`.
#[derive(Debug)]
pub(crate) struct VarGen {
    brand: u32,
    next: u32,
}

impl VarGen {
    pub(crate) fn new(brand: u32) -> Self { VarGen { brand, next: 0 } }

    /// Produce a variable distinct from every variable produced so far *by this
    /// generator*; the brand distinguishes it from every other generator's.
    pub(crate) fn fresh(&mut self) -> FreeVar {
        let v = FreeVar { brand: self.brand, id: self.next };
        self.next = self.next.checked_add(1).expect("free variable counter overflow");
        v
    }
}

/// The shape of a term.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TermData {
    /// A bound occurrence, as a de Bruijn index counting binders outward.
    /// Constructible only by [`Formula::forall`]; see the module docs.
    Bound(u32),
    /// A free occurrence.
    Free(FreeVar),
    /// A defined function symbol applied to arguments. Function symbols enter
    /// only through conservative definitional extension, so the primitive
    /// signature stays `{∈, =}`.
    App(FnSym, Vec<Term>),
}

/// A defined function symbol: an index into the environment's definition table,
/// together with its arity.
/// A defined function symbol: an index into the environment's signature,
/// together with its arity and the brand of the `Env` that declared it.
///
/// The brand is load-bearing. Two `Env`s each start their counters at zero, so
/// without it symbol `k` from one would compare equal to symbol `k` from
/// another — letting a client hold two *contradictory* defining axioms for what
/// the kernel considers one symbol, which derives `⊢ ⊥`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnSym {
    pub(crate) brand: u32,
    pub(crate) id: u32,
    pub(crate) arity: u32,
}

impl FnSym {
    /// How many arguments this symbol takes.
    pub fn arity(self) -> u32 { self.arity }
    /// The symbol's identifier.
    pub fn id(self) -> u32 { self.id }
}

/// A term of the language.
///
/// Cheap to clone (`Rc`), with a cached hash so that equality — which the
/// inference rules perform constantly — short-circuits on differing hashes
/// instead of walking the structure.
#[derive(Debug, Clone)]
pub struct Term {
    data: Rc<TermData>,
    hash: u64,
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        // Pointer equality first (structure sharing makes this common), then
        // the cached hash, then the structure.
        Rc::ptr_eq(&self.data, &other.data) || (self.hash == other.hash && self.data == other.data)
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.hash) }
}

// The total order: cached hash first, structure as the tie-break. See the note
// on `impl Ord for Formula`, which is the one that is actually load-bearing.
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering { self.hash.cmp(&other.hash).then_with(|| self.data.cmp(&other.data)) }
}

/// A tiny FNV-style mixer. The kernel has no dependencies, so it cannot use a
/// hasher crate; this only needs to spread bits, not resist attack.
fn mix(seed: u64, x: u64) -> u64 {
    let mut h = seed ^ x;
    h = h.wrapping_mul(0x0100_0000_01b3);
    h ^= h >> 29;
    h
}

impl Term {
    fn new(data: TermData) -> Term {
        let hash = match &data {
            TermData::Bound(i) => mix(0x9e37_79b9_7f4a_7c15, *i as u64),
            TermData::Free(v) => mix(mix(0xc2b2_ae3d_27d4_eb4f, v.brand as u64), v.id as u64 | (1 << 32)),
            TermData::App(f, args) => {
                let mut h = mix(mix(0x1656_67b1_9e37_79f9, f.brand as u64), f.id as u64);
                for a in args {
                    h = mix(h, a.hash);
                }
                h
            }
        };
        Term { data: Rc::new(data), hash }
    }

    /// A term consisting of a single free variable.
    pub fn var(v: FreeVar) -> Term { Term::new(TermData::Free(v)) }

    pub(crate) fn bound(i: u32) -> Term { Term::new(TermData::Bound(i)) }

    pub(crate) fn data(&self) -> &TermData { &self.data }

    /// Apply a defined function symbol.
    ///
    /// # Panics
    /// If the number of arguments does not match the symbol's arity. An
    /// arity mismatch is a malformed term, not a false statement, so failing
    /// loudly is right.
    pub fn apply(f: FnSym, args: Vec<Term>) -> Term {
        assert_eq!(args.len(), f.arity as usize, "arity mismatch for function symbol {}", f.id);
        Term::new(TermData::App(f, args))
    }

    /// View this term as an application, if it is one: the symbol at the head
    /// and its arguments, borrowed.
    ///
    /// The counterpart of [`Term::apply`], and the exact analogue of
    /// [`Formula::as_eq`] one level down. **Reading a term is not a trusted
    /// operation** — no amount of inspection lets a client build a
    /// [`crate::Thm`], since the only constructors are the inference rules —
    /// and it does not widen what a client can *build* either:
    ///
    /// * The only representable shape it exposes is [`TermData::App`]; a
    ///   `Bound` index answers `None` here just as a `Free` does, so the
    ///   constructor discipline that makes dangling indices unconstructible is
    ///   untouched.
    /// * The arguments handed back are locally closed whenever the whole term
    ///   is, because `locally_closed` descends into an `App`'s arguments at the
    ///   *same* depth. Every `Term` reachable by a client is locally closed —
    ///   the only binder is `Formula::forall`, and no public accessor opens a
    ///   `Forall` — so this hands back nothing a client could not already hold.
    ///
    /// # Why the kernel owes this
    ///
    /// Without it, a client that must take a term apart has to *remember* how
    /// it built every term it may later decompose, in a side table keyed by the
    /// term. That table was measured at **54 % of the live heap** of an
    /// `init-prelude` run and 80 % of its live `Term` nodes, storing a second
    /// copy of the argument vector the `App` node already holds — and, worse,
    /// its misses were silent: a term the kernel itself had built (by
    /// substitution, or inside a derived rule) was indistinguishable from a
    /// term with no applicative structure, and decomposition of it failed.
    /// See `PRELUDE-COST.md` §3.2 and `derived::skeleton`.
    pub fn as_app(&self) -> Option<(FnSym, &[Term])> {
        match self.data() {
            TermData::App(f, args) => Some((*f, args)),
            _ => None,
        }
    }

    /// Whether `v` occurs free in this term.
    pub fn occurs_free(&self, v: FreeVar) -> bool {
        match self.data() {
            TermData::Bound(_) => false,
            TermData::Free(w) => *w == v,
            TermData::App(_, args) => args.iter().any(|a| a.occurs_free(v)),
        }
    }

    /// Collect the free variables occurring in this term.
    pub fn free_vars(&self, out: &mut Vec<FreeVar>) {
        match self.data() {
            TermData::Bound(_) => {}
            TermData::Free(w) =>
                if !out.contains(w) {
                    out.push(*w)
                },
            TermData::App(_, args) =>
                for a in args {
                    a.free_vars(out)
                },
        }
    }

    /// Replace free variable `v` by `Bound(depth)`, i.e. abstract over `v`.
    fn close(&self, v: FreeVar, depth: u32) -> Term {
        match self.data() {
            TermData::Bound(_) => self.clone(),
            TermData::Free(w) =>
                if *w == v {
                    Term::bound(depth)
                } else {
                    self.clone()
                },
            TermData::App(f, args) => Term::new(TermData::App(*f, args.iter().map(|a| a.close(v, depth)).collect())),
        }
    }

    /// Replace `Bound(depth)` by `t`.
    ///
    /// No index shifting of `t` is needed because every `Term` reachable by a
    /// client is locally closed — it contains no dangling `Bound` — which is
    /// exactly the invariant the constructor discipline maintains. If that
    /// invariant were ever broken, this is the function that would silently
    /// capture, which is why it is private and why the invariant is enforced at
    /// the only place binders are introduced.
    fn open(&self, depth: u32, t: &Term) -> Term {
        match self.data() {
            TermData::Bound(i) =>
                if *i == depth {
                    t.clone()
                } else {
                    self.clone()
                },
            TermData::Free(_) => self.clone(),
            TermData::App(f, args) => Term::new(TermData::App(*f, args.iter().map(|a| a.open(depth, t)).collect())),
        }
    }

    /// Whether the term is locally closed: no `Bound` index escapes.
    pub(crate) fn locally_closed(&self, depth: u32) -> bool {
        match self.data() {
            TermData::Bound(i) => *i < depth,
            TermData::Free(_) => true,
            TermData::App(_, args) => args.iter().all(|a| a.locally_closed(depth)),
        }
    }
}

/// Go one binder deeper, panicking rather than wrapping.
///
/// `close`, `open` and `locally_closed` all descend under `Forall` by
/// incrementing a binder depth, and every one of them is a function where a
/// wrong depth is a *capture*, not a crash: `open` at a wrapped depth replaces
/// the wrong index, and `locally_closed` at a wrapped depth reports a dangling
/// index as locally closed.
///
/// An earlier version of this comment justified the explicit `checked_add` by
/// "plain `depth + 1` wraps silently in a release build — `overflow-checks` is
/// off there". **That premise is false for every build this repository
/// produces**: the workspace `Cargo.toml` sets `overflow-checks = true` under
/// `[profile.release]`, deliberately and with a comment saying why, so `depth +
/// 1` would panic rather than wrap in release exactly as it does in debug.
///
/// The conclusion survives the premise, for two reasons, and the guard stays.
/// **This crate is a library**: a downstream dependent compiling `kernel` gets
/// *its* profiles, and Cargo's default release profile has `overflow-checks`
/// off — the workspace setting protects our builds and no one else's. And a
/// profile is one line in a manifest that nothing checks, removable in the same
/// commit that would need it; the same argument makes `ci/check-boundary.sh`
/// re-grep for `unsafe` that `#![forbid(unsafe_code)]` already forbids. A safety
/// property that holds only because of a build setting is a safety property
/// stated in the wrong file.
///
/// Today the overflow is unreachable, but only *accidentally*: these are
/// recursive, so reaching depth 2³² would need 2³² nested `Forall`s and the
/// stack would go first. That is not a guarantee, it is a side effect of the
/// implementation strategy — an iterative rewrite, or a deeper machine stack,
/// removes it without anyone noticing that a safety property went with it. Same
/// grade of paranoia as the brand-counter latch in `thm.rs`: make the bad state
/// unreachable, do not rely on it being hard to reach.
///
/// # Panics
/// If `depth` is `u32::MAX`. A panic here is a malformed intermediate state,
/// not a false statement, so failing loudly is right — as with the arity check
/// in [`Term::apply`].
fn deeper(depth: u32) -> u32 { depth.checked_add(1).expect("binder depth overflow") }

/// The shape of a formula.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FormulaData {
    /// Absurdity. Negation is `φ → ⊥`.
    False,
    /// `a = b`.
    Eq(Term, Term),
    /// `a ∈ b`.
    Mem(Term, Term),
    /// `φ → ψ`.
    Imp(Formula, Formula),
    /// `∀x. φ`, with `x` the de Bruijn binder introduced here.
    Forall(Formula),
}

/// A formula of the language.
#[derive(Debug, Clone)]
pub struct Formula {
    data: Rc<FormulaData>,
    hash: u64,
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.data, &other.data) || (self.hash == other.hash && self.data == other.data)
    }
}
impl Eq for Formula {}
impl Hash for Formula {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.hash) }
}

/// A **total order on formulas**, used to canonicalise the hypothesis sets a
/// [`crate::Thm`] carries.
///
/// # Why the kernel needs one at all
///
/// `Thm`'s hypothesis set has to compare equal regardless of the order in which
/// the hypotheses arrived, or `Thm::mp`'s premise matching and
/// `Thm::implies_intr`'s membership test become order-dependent. The set is
/// stored as a sorted, duplicate-free `Vec<Formula>`, so sameness of sets is
/// `==` on the vectors — which needs a canonical listing, which needs an order.
///
/// # Why *this* order, and why it is stable
///
/// **Cached structural hash first, full structural comparison as the
/// tie-break.** Both halves are pure functions of the formula's syntax:
///
/// * the hash is computed once in [`Formula::new`] from the constructor and the
///   children's hashes, by a fixed FNV-style mixer with fixed seeds — no
///   randomness, no thread state, no address dependence, so it is the same
///   number in every process and every thread;
/// * the tie-break is the derived lexicographic order on [`FormulaData`], which
///   bottoms out at [`FreeVar`] and [`FnSym`] identifiers — again pure syntax.
///
/// So the order is a *function of the two formulas alone*. This is exactly the
/// property that `derived::hyp::order::rank` cannot have from outside the
/// kernel: unable to see inside a `Forall` or a `Term`, it orders by hash and
/// breaks ties with a thread-local registry of first-registration order, which
/// is stable only within one thread's lifetime. Here there is no registry and
/// nothing to clear.
///
/// The hash goes first purely for speed — it decides almost every comparison in
/// one `u64` compare, which matters because sorting a hypothesis set is on the
/// path of every `mp`. Ordering by hash is not *meaningful*, and it is not
/// meant to be: a canonical listing needs only to be total, deterministic, and
/// consistent with `==`.
///
/// # Consistency with `Eq`, which is what makes `dedup` correct
///
/// `cmp` returns `Equal` exactly when `==` holds. If the structures are equal
/// the hashes are equal (the hash is a function of the structure) and the
/// tie-break returns `Equal`; conversely `Equal` forces the structures equal.
/// That equivalence is what lets a hypothesis set be canonicalised by
/// `sort_unstable` followed by `dedup` — `dedup` only removes *adjacent*
/// duplicates, so it is correct only if sorting brings equal formulas together,
/// and "equal" must mean the same thing to both.
///
/// Note that a hash *collision* between distinct formulas is harmless here: the
/// tie-break still separates them, so the order stays total and `dedup` still
/// removes only genuine duplicates. A collision costs one structural
/// comparison, never a wrong answer.
impl PartialOrd for Formula {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for Formula {
    fn cmp(&self, other: &Self) -> Ordering { self.hash.cmp(&other.hash).then_with(|| self.data.cmp(&other.data)) }
}

impl Formula {
    fn new(data: FormulaData) -> Formula {
        let hash = match &data {
            FormulaData::False => 0x5bf0_3635_1c9e_7a11,
            FormulaData::Eq(a, b) => mix(mix(0x27d4_eb2f_1656_67b1, a.hash), b.hash),
            FormulaData::Mem(a, b) => mix(mix(0x1656_67b1_27d4_eb2f, a.hash), b.hash),
            FormulaData::Imp(a, b) => mix(mix(0xff51_afd7_ed55_8ccd, a.hash), b.hash),
            FormulaData::Forall(b) => mix(0xc4ce_b9fe_1a85_ec53, b.hash),
        };
        Formula { data: Rc::new(data), hash }
    }

    pub(crate) fn data(&self) -> &FormulaData { &self.data }

    /// `⊥`.
    pub fn false_() -> Formula { Formula::new(FormulaData::False) }
    /// `a = b`.
    pub fn eq(a: Term, b: Term) -> Formula { Formula::new(FormulaData::Eq(a, b)) }
    /// `a ∈ b`.
    pub fn mem(a: Term, b: Term) -> Formula { Formula::new(FormulaData::Mem(a, b)) }
    /// `φ → ψ`.
    pub fn imp(a: Formula, b: Formula) -> Formula { Formula::new(FormulaData::Imp(a, b)) }
    /// `¬φ`, i.e. `φ → ⊥`.
    // `not` is the standard name for this connective and reads correctly beside
    // `and`/`or`/`imp`; implementing `std::ops::Not` instead would give `!φ`,
    // which is less clear in formula-building code and cannot be a associated
    // function taking ownership the way the other connectives do.
    #[allow(clippy::should_implement_trait)]
    pub fn not(a: Formula) -> Formula { Formula::imp(a, Formula::false_()) }
    /// `φ ∨ ψ`, i.e. `¬φ → ψ`.
    pub fn or(a: Formula, b: Formula) -> Formula { Formula::imp(Formula::not(a), b) }
    /// `φ ∧ ψ`, i.e. `¬(φ → ¬ψ)`.
    pub fn and(a: Formula, b: Formula) -> Formula { Formula::not(Formula::imp(a, Formula::not(b))) }
    /// `φ ↔ ψ`.
    pub fn iff(a: Formula, b: Formula) -> Formula {
        Formula::and(Formula::imp(a.clone(), b.clone()), Formula::imp(b, a))
    }

    /// `∀v. φ`, abstracting the named variable `v`.
    ///
    /// This is the *only* way a bound variable comes into existence, which is
    /// what makes dangling de Bruijn indices unconstructible from outside the
    /// kernel.
    pub fn forall(v: FreeVar, body: Formula) -> Formula { Formula::new(FormulaData::Forall(body.close(v, 0))) }

    /// `∃v. φ`, i.e. `¬∀v. ¬φ`.
    pub fn exists(v: FreeVar, body: Formula) -> Formula { Formula::not(Formula::forall(v, Formula::not(body))) }

    fn close(&self, v: FreeVar, depth: u32) -> Formula {
        match self.data() {
            FormulaData::False => self.clone(),
            FormulaData::Eq(a, b) => Formula::eq(a.close(v, depth), b.close(v, depth)),
            FormulaData::Mem(a, b) => Formula::mem(a.close(v, depth), b.close(v, depth)),
            FormulaData::Imp(a, b) => Formula::imp(a.close(v, depth), b.close(v, depth)),
            // Under a binder the index to abstract to is one deeper. Checked,
            // not `depth + 1`: see `deeper`.
            FormulaData::Forall(b) => Formula::new(FormulaData::Forall(b.close(v, deeper(depth)))),
        }
    }

    pub(crate) fn open(&self, depth: u32, t: &Term) -> Formula {
        match self.data() {
            FormulaData::False => self.clone(),
            FormulaData::Eq(a, b) => Formula::eq(a.open(depth, t), b.open(depth, t)),
            FormulaData::Mem(a, b) => Formula::mem(a.open(depth, t), b.open(depth, t)),
            FormulaData::Imp(a, b) => Formula::imp(a.open(depth, t), b.open(depth, t)),
            FormulaData::Forall(b) => Formula::new(FormulaData::Forall(b.open(deeper(depth), t))),
        }
    }

    /// Instantiate the outermost `∀` with `t`. Returns `None` if this is not a
    /// universally quantified formula.
    pub(crate) fn instantiate(&self, t: &Term) -> Option<Formula> {
        match self.data() {
            FormulaData::Forall(body) => Some(body.open(0, t)),
            _ => None,
        }
    }

    /// View this formula as an equation, if it is one.
    ///
    /// Reading a formula is not a trusted operation — no amount of inspection
    /// lets a client build a [`crate::Thm`], since the only constructors are the
    /// inference rules. These accessors exist so that *derived* rules can live
    /// outside the kernel, where they belong: they are ordinary code, and
    /// keeping them out keeps the trusted crate down to what must be correct.
    pub fn as_eq(&self) -> Option<(Term, Term)> {
        match self.data() {
            FormulaData::Eq(a, b) => Some((a.clone(), b.clone())),
            _ => None,
        }
    }

    /// View this formula as an implication, if it is one.
    pub fn as_imp(&self) -> Option<(Formula, Formula)> {
        match self.data() {
            FormulaData::Imp(a, b) => Some((a.clone(), b.clone())),
            _ => None,
        }
    }

    /// View this formula as a membership statement, if it is one.
    pub fn as_mem(&self) -> Option<(Term, Term)> {
        match self.data() {
            FormulaData::Mem(a, b) => Some((a.clone(), b.clone())),
            _ => None,
        }
    }

    /// Whether this formula is a universal quantification.
    pub fn is_forall(&self) -> bool { matches!(self.data(), FormulaData::Forall(_)) }

    /// Whether `v` occurs free.
    pub fn occurs_free(&self, v: FreeVar) -> bool {
        match self.data() {
            FormulaData::False => false,
            FormulaData::Eq(a, b) | FormulaData::Mem(a, b) => a.occurs_free(v) || b.occurs_free(v),
            FormulaData::Imp(a, b) => a.occurs_free(v) || b.occurs_free(v),
            FormulaData::Forall(b) => b.occurs_free(v),
        }
    }

    /// Collect free variables.
    pub fn free_vars(&self, out: &mut Vec<FreeVar>) {
        match self.data() {
            FormulaData::False => {}
            FormulaData::Eq(a, b) | FormulaData::Mem(a, b) => {
                a.free_vars(out);
                b.free_vars(out);
            }
            FormulaData::Imp(a, b) => {
                a.free_vars(out);
                b.free_vars(out);
            }
            FormulaData::Forall(b) => b.free_vars(out),
        }
    }

    /// Whether the formula is locally closed at the given binder depth.
    pub(crate) fn locally_closed(&self, depth: u32) -> bool {
        match self.data() {
            FormulaData::False => true,
            FormulaData::Eq(a, b) | FormulaData::Mem(a, b) => a.locally_closed(depth) && b.locally_closed(depth),
            FormulaData::Imp(a, b) => a.locally_closed(depth) && b.locally_closed(depth),
            FormulaData::Forall(b) => b.locally_closed(deeper(depth)),
        }
    }

    /// Substitute term `t` for free variable `v` throughout.
    ///
    /// Safe without side conditions precisely because `v` is free and `t` is
    /// locally closed: there is no binder that could capture either.
    ///
    /// # Panics
    /// If `t` is not locally closed. This check was a `debug_assert!` and is now
    /// a real one; the reasoning is worth recording, because "unreachable today"
    /// argued for either answer.
    ///
    /// It *is* unreachable today: `Bound` is `pub(crate)` and the only public
    /// producers of a `Term` are [`Term::var`] and [`Term::apply`], so no public
    /// path yields a term with a dangling index, and all three in-crate callers
    /// (`eq_leibniz`, `exists_unique_at`, `define`) pass a variable or an
    /// application of variables. But that is an invariant of the API's *shape* —
    /// which constructors happen to be exported — and this function is the one
    /// that silently *captures* if the shape ever changes, since `open` does no
    /// index shifting. The failure would not be a rejection or a crash; it would
    /// be a wrong theorem, produced quietly.
    ///
    /// A `debug_assert!` is exactly the wrong instrument for that. It is absent
    /// from release builds — the only builds that run a real development — so it
    /// guards the configuration that cannot produce the bug and not the one that
    /// can. That is the same shape as this project's fifth soundness bug, where
    /// the guard was `checked_add` on a value the atomic had already wrapped:
    /// present, plausible, and not where the failure was.
    ///
    /// The cost was measured rather than assumed, since this is a hot path.
    /// `init-prelude` (2059 declarations) with the real TG backend, six
    /// interleaved runs of each binary on the same machine: best 9.09 s with the
    /// `debug_assert!`, 9.14 s with the assertion — within run-to-run noise, and
    /// well under the spread from other load. It is cheap for a structural
    /// reason, not by luck: `subst` already walks and *reallocates* the whole of
    /// `self` twice (`close` then `open`), while this is one allocation-free walk
    /// of `t`, which is a variable or a shallow application at every call site.
    ///
    /// Panicking is the right response, as with the arity check in
    /// [`Term::apply`] — which is likewise a real `assert_eq!` on a hot path. A
    /// dangling index is a malformed term, not a false statement, and there is
    /// no sound value to return.
    pub fn subst(&self, v: FreeVar, t: &Term) -> Formula {
        assert!(t.locally_closed(0), "substituting a term with a dangling bound variable");
        // Abstract over `v`, then immediately fill the hole with `t`. Going via
        // the de Bruijn representation is what makes this capture-free: the
        // abstraction step accounts for binder depth, so `t` lands at the right
        // level no matter how deeply `v` occurred.
        self.close(v, 0).open(0, t)
    }

    /// `(self.subst(v, a), self.subst(v, b))`, sharing the abstraction step.
    ///
    /// # Why this exists, and why it is not a second substitution rule
    ///
    /// `subst` is `close` then `open`, and **`close` does not mention the term
    /// being substituted** — it is a function of `self`, `v` and the depth
    /// alone. So the two calls above compute the same `close(v, 0)` twice.
    /// Naming it is a common subexpression and nothing else: this returns the
    /// pair the two `subst` calls return, node for node, and no other pair is
    /// reachable from here. `PERF-REVIEW.md` F3; [`crate::Thm::eq_leibniz`] is
    /// the only caller and it goes from four full-tree rebuilds of `φ` per
    /// Leibniz instance to three.
    ///
    /// The `locally_closed` guard is **not** hoisted along with the `close`,
    /// because it is not about `self` — it is the check that `open` will not
    /// capture, and it is about the term being substituted. Both terms are
    /// checked, once each, exactly as two `subst` calls would check them, and
    /// `&&` checks them in the same left-to-right order. The full argument for
    /// why this assertion is a real `assert!` rather than a `debug_assert!` is
    /// on [`Formula::subst`] and applies here unchanged.
    ///
    /// The extra sharing this produces is invisible to every observer: `a` and
    /// `b`'s results now share their untouched subtrees with each other rather
    /// than with two structurally identical copies. `PartialEq` starts with
    /// `Rc::ptr_eq` and falls back to the structure, `Hash` reads a hash that is
    /// a function of the structure, and `Ord` is the hash then the structure —
    /// so nothing in this crate can tell the two apart, and nothing outside it
    /// can see an `Rc` at all.
    pub(crate) fn subst_pair(&self, v: FreeVar, a: &Term, b: &Term) -> (Formula, Formula) {
        assert!(a.locally_closed(0) && b.locally_closed(0), "substituting a term with a dangling bound variable");
        let closed = self.close(v, 0);
        (closed.open(0, a), closed.open(0, b))
    }
}

#[cfg(test)]
mod depth_tests {
    use super::*;

    /// Descending under a binder must **panic** on overflow, not wrap.
    ///
    /// Reaching depth 2³² through the public API would need 2³² nested
    /// `Forall`s and the stack would go first, so the real exploit is not
    /// runnable — exactly as with the brand counter in `thm.rs`, whose test
    /// pre-loads the counter instead of making 2³² `Env`s. Entering the
    /// recursion at `u32::MAX` is the same trick: it tests the guard rather
    /// than the accident that today keeps the guard from being needed.
    ///
    /// Each of the three is a capture bug if it wraps: `close` would abstract
    /// to the wrong index, `open` would substitute at the wrong index, and
    /// `locally_closed` would certify a dangling index as closed.
    #[test]
    fn binder_depth_overflow_panics() {
        let mut g = VarGen::new(0);
        let (x, y) = (g.fresh(), g.fresh());
        let f = Formula::forall(x, Formula::eq(Term::var(x), Term::var(y)));
        let t = Term::var(y);
        assert!(std::panic::catch_unwind(|| f.locally_closed(u32::MAX)).is_err(), "locally_closed wrapped");
        assert!(std::panic::catch_unwind(|| f.open(u32::MAX, &t)).is_err(), "open wrapped");
        assert!(std::panic::catch_unwind(|| f.close(y, u32::MAX)).is_err(), "close wrapped");
    }
}
