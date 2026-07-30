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

use core::hash::{Hash, Hasher};

/// A free variable, identified by an opaque number.
///
/// Distinctness of free variables is decided by this number, so the
/// distinct-variable conditions that plague named representations reduce to
/// integer inequality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FreeVar(pub(crate) u32);

impl FreeVar {
    /// The underlying identifier.
    pub fn id(self) -> u32 { self.0 }
}

/// Source of fresh free variables.
///
/// Freshness matters: reusing a variable that already occurs somewhere would
/// silently identify two different things. The counter only ever increases.
#[derive(Debug, Default)]
pub struct VarGen {
    next: u32,
}

impl VarGen {
    /// A new generator.
    pub fn new() -> Self { VarGen { next: 0 } }

    /// Produce a variable distinct from every variable produced so far.
    pub fn fresh(&mut self) -> FreeVar {
        let v = FreeVar(self.next);
        self.next = self.next.checked_add(1).expect("free variable counter overflow");
        v
    }
}

/// The shape of a term.
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnSym {
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
            TermData::Free(v) => mix(0xc2b2_ae3d_27d4_eb4f, v.0 as u64 | (1 << 32)),
            TermData::App(f, args) => {
                let mut h = mix(0x1656_67b1_9e37_79f9, f.id as u64);
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

/// The shape of a formula.
#[derive(Debug, Clone, PartialEq, Eq)]
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
            // Under a binder the index to abstract to is one deeper.
            FormulaData::Forall(b) => Formula::new(FormulaData::Forall(b.close(v, depth + 1))),
        }
    }

    pub(crate) fn open(&self, depth: u32, t: &Term) -> Formula {
        match self.data() {
            FormulaData::False => self.clone(),
            FormulaData::Eq(a, b) => Formula::eq(a.open(depth, t), b.open(depth, t)),
            FormulaData::Mem(a, b) => Formula::mem(a.open(depth, t), b.open(depth, t)),
            FormulaData::Imp(a, b) => Formula::imp(a.open(depth, t), b.open(depth, t)),
            FormulaData::Forall(b) => Formula::new(FormulaData::Forall(b.open(depth + 1, t))),
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
            FormulaData::Forall(b) => b.locally_closed(depth + 1),
        }
    }

    /// Substitute term `t` for free variable `v` throughout.
    ///
    /// Safe without side conditions precisely because `v` is free and `t` is
    /// locally closed: there is no binder that could capture either.
    pub fn subst(&self, v: FreeVar, t: &Term) -> Formula {
        debug_assert!(t.locally_closed(0), "substituting a term with a dangling bound variable");
        // Abstract over `v`, then immediately fill the hole with `t`. Going via
        // the de Bruijn representation is what makes this capture-free: the
        // abstraction step accounts for binder depth, so `t` lands at the right
        // level no matter how deeply `v` occurred.
        self.close(v, 0).open(0, t)
    }
}
