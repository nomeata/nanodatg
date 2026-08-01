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

use std::collections::HashMap;
use std::rc::Rc;

use kernel::{Env, FnSym, Thm};

use crate::bound::Bound;
use crate::finset::FinSet;
use crate::isum::ISumSyms;
use crate::sigma::Telescope;
use crate::point_fun::PointFun;
use crate::proj::Proj;
use crate::sigma::product_parts;
use crate::sums::Cases;
use crate::wtype::Wtype;

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
            mem_lu,
            trans_lu,
            syms: ISumSyms::new(),
            telescopes: HashMap::new(),
        })
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
