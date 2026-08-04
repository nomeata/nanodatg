//! **The shared apparatus** every declaration is translated over: one W-type,
//! one bound, one `rec₊`, one set of projections, built once.
//!
//! # Why it is a struct
//!
//! For the reason [`crate::wtype::Wtype`] and [`crate::bound::Bound`] are: every
//! theorem in this module is about *the* pairing, *the* function space and *the*
//! `W` of one definitional extension. Building the apparatus twice mints a
//! second `upair`, and then `⟨a,f⟩` names two different terms and nothing
//! composes. A process translating a whole Lean file builds one [`Machine`] and
//! calls [`crate::inductive::Inductive::build`] once per declaration.
//!
//! # Interface
//!
//! [`Machine::new`] builds everything from the axioms up; [`Machine::over`]
//! does the same over a caller-supplied [`crate::wtype::Wtype`] and
//! [`crate::bound::Bound`], for a client that already holds them. The two
//! universe facts are carried as fields because the bound obligation
//! (`carrier.rs`) uses each of them twice and re-deriving them per declaration
//! would be the dominant cost.
//!
//! [`Machine::ident`] is how a *result* remembers which apparatus it came from:
//! everything built here is stated over these symbols, so a translated
//! declaration records the identity and refuses a second `Machine` handed to it
//! later. See [`crate::inductive::Inductive::ctor_term`].

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use kernel::{Env, FnSym, Thm};

use crate::bound::Bound;
use crate::finset::FinSet;
use crate::isum::ISumSyms;
use crate::sigma::Telescope;
use crate::point_fun::PointFun;
use crate::proj::Proj;
use crate::ran::Ran;
use crate::sigma::product_parts;
use crate::sigma::Push;
use crate::sums::Cases;
use crate::wtype::Wtype;

/// **Which apparatus** a term or theorem was built over.
///
/// Four symbols, each minted afresh by every [`Machine::over`]: the pairing and
/// the `W` come from the [`Wtype`], `rec₊` from [`Cases::new`] and `⋂` from
/// [`Proj::new`]. Two apparatuses in one `Env` therefore always differ, which
/// is what makes this an identity rather than a heuristic — and all four are
/// fixed when the `Machine` is built, so it never changes under a client's
/// feet the way a lazily-grown cache would.
///
/// A struct built over a machine stores this and compares it before answering a
/// question about a machine it is handed later: `machine.rs`'s own header
/// explains what a second apparatus costs — it mints a second `upair`, and then
/// `⟨a,f⟩` names two different terms — and a *true* theorem about the wrong
/// machine's constructors is exactly the mislabelling that costs a session.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MachineId {
    /// The unordered pair, and with it `⟨·,·⟩`, `sup` and every tuple.
    pub up: FnSym,
    /// The W-type symbol.
    pub w: FnSym,
    /// `rec₊` — [`Cases::new`] mints one per apparatus.
    pub case: FnSym,
    /// `⋂`, and with it `π₁`/`π₂` — [`Proj::new`] mints one per apparatus.
    pub inter: FnSym,
}

/// Everything a declaration is translated over, built once.
pub struct Machine {
    /// The W-type, and with it the pairing, function space and `app`.
    pub wt: Wtype,
    /// The universe bound, and `closed(A,B,U(c))`.
    pub bnd: Bound,
    /// `rec₊`, the binary case function the tag dispatch is nested from.
    pub cases: Cases,
    /// The one-point graph, used for the recursive-argument branches.
    pub pf: PointFun,
    /// `π₁`, `π₂`, for the dependent telescope.
    pub proj: Proj,
    /// `⊢ ∀A ∀B ∀q. (q ∈ A × B → (π₁q ∈ A ∧ (π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)))`.
    pub pparts: Thm,
    /// The finite-set chain, for the fibre codomain and the recursive-argument
    /// function's codomain.
    pub fin: FinSet,
    /// `ran`, the range of a set relation. Only a **function-typed** recursive
    /// argument spends it: its recursive-argument function's codomain is
    /// `⋃ⱼ ran(gⱼ)`, built from the branches because the dispatcher's term
    /// mentions its codomain. A plain declaration mints it and never uses it.
    pub ran: Ran,
    /// `⊢ ∀x. x ∈ U(x)`.
    pub mem_lu: Thm,
    /// `⊢ ∀x. C₁(U(x))` — `U(x)` is transitive. This is what makes the bound
    /// obligation one inference rather than a case analysis on the tag sum.
    pub trans_lu: Thm,
    /// The `n`-ary sum and injection symbols, minted on demand and **cached**
    /// with everything derived about them. Grows across declarations: a second
    /// declaration of the same or smaller arity mints nothing.
    pub syms: ISumSyms,
    /// The dependent telescopes, cached by **`(np, β⃗)`** — the arity *and* the
    /// argument-type symbols, because that is what a telescope is parameterised
    /// by. Two constructors with the same argument types share one `Σ` nest;
    /// two with the same arity and different types do not, which is why this
    /// key is not `n`. Shared by `Rc` rather than rebuilt, so the symbols are
    /// identical and the theorems compose.
    pub telescopes: HashMap<(usize, Vec<FnSym>), Rc<Telescope>>,
    /// [`Machine::fs_ext`]'s memo — derived on first request and **never**
    /// eagerly, so a machine no function-typed declaration is translated over
    /// costs no Extensionality instance for it.
    fs_ext: RefCell<Option<Thm>>,
    /// [`Machine::push`]'s memo, for [`Machine::fs_ext`]'s reason and one more:
    /// `Push::new` mints **two** definitional extensions, so a second build is a
    /// second `push` operator, and `sigma::push_pull_roundtrip` about one of
    /// them says nothing about a minor premise stated with the other.
    ///
    /// It has to live here rather than in a caller because
    /// [`super::motive::dep_minor`] *states* the applied minor at
    /// `push(tⱼ, β₀ⱼ(p⃗))` — see [`Inductive::minor_args`](super::Inductive::minor_args)
    /// — so the operator is part of a declaration's premises, and every consumer
    /// on either side of the crate boundary has to name the same one.
    push: RefCell<Option<Rc<Push>>>,
}

impl Machine {
    /// Build every symbol and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Machine> {
        let wt = Wtype::new(env)?;
        let bnd = Bound::new(env, &wt)?;
        Machine::over(env, wt, bnd)
    }

    /// The same over a caller-supplied W-type and bound, so that the terms
    /// compose with whatever else was proved over them.
    pub fn over(env: &mut Env, wt: Wtype, bnd: Bound) -> Option<Machine> {
        let cases = Cases::new(env, &wt.sums)?;
        let pf = PointFun::over(env, &wt.sums, &wt.app_pair)?;
        let proj = Proj::new(env, &wt.sums.ap, &pf)?;
        let pparts = product_parts(env, &wt.sums.ap, &wt.sums.prod, &proj)?;
        let fin = FinSet::new(env, &wt.sums)?;
        let ran = Ran::new(env, &wt.sums)?;
        let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax)?;
        let trans_lu = crate::universe::least_universe_transitive(env, bnd.lu, &bnd.lu_ax)?;
        Some(Machine {
            wt,
            bnd,
            cases,
            pf,
            proj,
            pparts,
            fin,
            ran,
            mem_lu,
            trans_lu,
            syms: ISumSyms::new(),
            telescopes: HashMap::new(),
            fs_ext: RefCell::new(None),
            push: RefCell::new(None),
        })
    }

    /// **The `push` operator over this apparatus**, derived once —
    /// `push(t,B) = { ⟨b, app(t, ⟨b,•⟩)⟩ : b ∈ B }`.
    ///
    /// Lazy for [`Machine::fs_ext`]'s reason: a corpus with no function-typed
    /// recursive field never asks, and pays neither of the two definitional
    /// extensions. Telescope-*independent* — `⟨b,•⟩` mentions neither the
    /// argument types nor `k` — so one serves every declaration translated over
    /// this apparatus, which is what makes a single slot right rather than a
    /// map keyed by anything.
    pub fn push(&self, env: &mut Env) -> Option<Rc<Push>> {
        if let Some(p) = self.push.borrow().as_ref() {
            return Some(p.clone())
        }
        let out = Rc::new(Push::new(env, &self.wt.sums)?);
        *self.push.borrow_mut() = Some(out.clone());
        Some(out)
    }

    /// `⊢ ∀A ∀S ∀f ∀g. ((f ∈ fs(A,S) ∧ (g ∈ fs(A,S) ∧ pointwise(f,g))) → f = g)`
    /// — **function extensionality**, derived once per apparatus.
    ///
    /// Every consumer of it is a function-typed recursive argument's: the ι
    /// rule's two identifications (`super::iota`), the recursive-argument
    /// function's η rule (`super::rect::recarg_eta`), and the induction
    /// principle that spends it. Each call of [`crate::ext::funspace_ext`]
    /// costs **one Extensionality instance**, and the statement depends on
    /// nothing but this machine's `Wtype`, so deriving it per constructor or
    /// per `φ` made a declaration's axiom count depend on how many times it was
    /// asked. Memoised behind `&self` for the same reason
    /// [`crate::isum::ISumSyms::branch`] is: every term-builder in this module
    /// holds a `&Machine` and minting needs an `&mut Env`.
    ///
    /// **Measured, and now observed.** Two seats recorded this as an efficiency
    /// claim nothing in the crate could see, on the grounds that what it asserts
    /// is an axiom-instance count per declaration and no such ledger exists.
    /// That is true of the *instance* and not of the *event*:
    /// [`crate::ext::funspace_ext`] mints its Extensionality instance and 57
    /// fresh variables in one call, so "the derivation ran again" and "a second
    /// instance was spent" are the same thing, and the first is visible from
    /// outside through `Env`'s monotone variable counter. Deleting the cache hit
    /// now fails
    /// `the_function_extensionality_memo_costs_nothing_the_second_time` in
    /// `derived/tests/inductive.rs`, which pins both halves: the first request
    /// must cost (it is lazy) and the second must cost **zero** (a cache that
    /// re-derived and discarded would leave the axiom count exactly as wrong).
    pub fn fs_ext(&self, env: &mut Env) -> Option<Thm> {
        if let Some(th) = self.fs_ext.borrow().as_ref() {
            return Some(th.clone())
        }
        let s = &self.wt.sums;
        let out = crate::ext::funspace_ext(env, &s.ap, &s.prod, &s.fs, &self.wt.app_pair)?;
        *self.fs_ext.borrow_mut() = Some(out.clone());
        Some(out)
    }

    /// The symbols that identify this apparatus. See [`MachineId`].
    pub fn ident(&self) -> MachineId {
        MachineId {
            up: self.wt.sums.ap.sets.up,
            w: self.wt.w,
            case: self.cases.case,
            inter: self.proj.inter,
        }
    }

    /// The telescope over `betas`, from the cache or freshly built.
    ///
    /// A hit hands back the *same* `Σ` symbols and the *same* intro,
    /// projection and η theorems — never a re-derivation. This matters more
    /// than it looks: `Telescope::new` mints `k + 1` definitional extensions
    /// and derives `2k + 2` theorems, and a corpus declaring the same
    /// constructor shape repeatedly would otherwise pay for all of it each
    /// time.
    pub fn telescope(
        &mut self,
        env: &mut Env,
        np: usize,
        betas: &[FnSym],
    ) -> Option<Rc<Telescope>> {
        let key = (np, betas.to_vec());
        if let Some(t) = self.telescopes.get(&key) {
            return Some(t.clone())
        }
        let built = Rc::new(Telescope::new(env, &self.wt.sums, &self.proj, &self.pparts, np, betas)?);
        self.telescopes.insert(key, built.clone());
        Some(built)
    }
}
