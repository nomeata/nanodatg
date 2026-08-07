//! The syntactic environment — port of `MiniKernel/Types.lean`'s
//! `Declaration`, `ConstantInfo` and `Environment`.
//!
//! # Interface
//!
//! * [`Declaration`] is what is sent to the kernel (one per export-file item,
//!   with an inductive type's constructors bundled into it and its recursor
//!   *not* present — mini generates its own).
//! * [`ConstantInfo`] is what the kernel stores. Recursors carry their
//!   generated rules and, for inductive propositions with a single fieldless
//!   constructor, the K-rule's `kType`.
//! * [`Environment`] is a name-keyed store with `insertNew`'s duplicate check.
//!
//! No evidence lives here. The per-ground-instantiation interpretation store
//! it was once going to be wrapped by — `MiniEnv`, from an early draft of
//! MINI-DESIGN.md §8 — **was never built and does not exist**; that role is
//! filled by zone B's const store in [`crate::zoneb`], which is keyed by
//! `(declaration, σ)` and populated eagerly off the instantiation schedule.
//! This module stays evidence-free on purpose: it is zone A, whose job is to
//! accept or reject exactly as Lean's kernel does.

use crate::expr::{Level, Name, E};
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefKind {
    Def,
    Theorem,
    Opaque,
}

/// One member of a `mutual … end` block: its own name, its own type — whose
/// parameter prefix is the block's and whose remaining binders are its own
/// indices — and its own constructors.
///
/// A block's members share their level parameters and their parameter count,
/// which is why those live on [`Declaration::Mutual`] and not here; they do
/// **not** share their indices, and every recursor in the block binds the
/// indices of the member it eliminates only.
#[derive(Clone, Debug)]
pub struct IndType {
    pub name: Name,
    pub ty: E,
    pub ctors: Vec<(Name, E)>,
}

/// A declaration, as sent to `Environment::add`.
#[derive(Clone, Debug)]
pub enum Declaration {
    Axiom { name: Name, lparams: Vec<Name>, ty: E },
    Def { name: Name, lparams: Vec<Name>, ty: E, value: E, kind: DefKind },
    Quot,
    Inductive { name: Name, lparams: Vec<Name>, num_params: u32, ty: E, ctors: Vec<(Name, E)> },
    /// A `mutual … end` block of two or more inductive types, checked and
    /// eliminated as one declaration.
    ///
    /// **A separate variant rather than a list on [`Declaration::Inductive`]**,
    /// even though `kernel::add_inductive` treats the single case as a block of
    /// one internally. The single case is what every existing consumer — the
    /// census, the dump, the interpretation ledger, zone B's boundary — is
    /// written against, and a block of one is the *only* shape any of them can
    /// do anything with. Folding the two together would have made every one of
    /// those a partial function on its own input type; keeping them apart makes
    /// "this declaration is a mutual block" a thing each consumer answers
    /// explicitly, which is what a consumer that has no answer yet should have
    /// to do.
    Mutual { lparams: Vec<Name>, num_params: u32, types: Vec<IndType> },
}

impl Declaration {
    pub fn name(&self) -> Name {
        match self {
            Declaration::Axiom { name, .. } => name.clone(),
            Declaration::Def { name, .. } => name.clone(),
            Declaration::Quot => Name::simple("Quot"),
            Declaration::Inductive { name, .. } => name.clone(),
            // The block's first member. A `mutual` block is one declaration
            // with no name of its own, and the first member is the name the
            // export file's own reporting uses.
            Declaration::Mutual { types, .. } => {
                types.first().map(|t| t.name.clone()).unwrap_or(Name::Anon)
            }
        }
    }
}

/// What the kernel stores per constant.
#[derive(Clone, Debug)]
pub enum ConstantInfo {
    /// An inert opaque definition (axiom, `opaque`, constructor).
    Opaque { lparams: Vec<Name>, ty: E },
    /// An inductive type. The extra data over `Opaque` is what projections need.
    Inductive {
        lparams: Vec<Name>,
        ty: E,
        num_params: u32,
        num_indices: u32,
        ctors: Vec<Name>,
        is_unit: bool,
    },
    /// Any transparent definition (`def`, `theorem`).
    Def { lparams: Vec<Name>, ty: E, value: E },
    /// A recursor.
    ///
    /// Each rule's RHS is an open expression: the body of
    /// `fun params motives minors fields => …`. `k_type`, when present, is the
    /// body of `fun params => …` and says which type the major argument must
    /// have for the K-rule to fire.
    ///
    /// `num_motives` is `1` for every recursor outside a `mutual … end` block
    /// of two or more types, and it used to be an unwritten `1` at every site
    /// that computed a position in the telescope. A mutual block's recursor
    /// binds **one motive per member**, before the minors, so the major
    /// argument sits at `num_params + num_motives + num_minors + num_indices`
    /// and the constant `1` there was a silent assumption about the block size.
    Recursor {
        lparams: Vec<Name>,
        ty: E,
        num_params: u32,
        num_motives: u32,
        num_minors: u32,
        num_indices: u32,
        rules: Vec<(Name, E)>,
        k_type: Option<E>,
    },
}

impl ConstantInfo {
    pub fn lparams(&self) -> &[Name] {
        match self {
            ConstantInfo::Opaque { lparams, .. }
            | ConstantInfo::Inductive { lparams, .. }
            | ConstantInfo::Def { lparams, .. }
            | ConstantInfo::Recursor { lparams, .. } => lparams,
        }
    }

    pub fn ty(&self) -> &E {
        match self {
            ConstantInfo::Opaque { ty, .. }
            | ConstantInfo::Inductive { ty, .. }
            | ConstantInfo::Def { ty, .. }
            | ConstantInfo::Recursor { ty, .. } => ty,
        }
    }

    pub fn value(&self) -> Option<&E> {
        match self {
            ConstantInfo::Def { value, .. } => Some(value),
            _ => None,
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct Environment {
    pub consts: HashMap<Name, ConstantInfo>,
    /// Which inductive declaration a constructor or recursor belongs to.
    ///
    /// An **index**, built when the declaration is added, not a lookup that
    /// scans. MINI-DESIGN.md §0's claim is about the checker never searching
    /// for a fact; `⟦List.cons⟧` has to reach `List`'s declaration data, and it
    /// reaches it by one hash lookup on the name it was asked about.
    pub owners: HashMap<Name, Name>,
}

impl Environment {
    pub fn empty() -> Environment { Environment::default() }

    pub fn get(&self, n: &Name) -> Option<&ConstantInfo> { self.consts.get(n) }

    /// The inductive declaration `n` belongs to, if it is one of its
    /// constructors or its recursor.
    pub fn owner(&self, n: &Name) -> Option<&Name> { self.owners.get(n) }

    /// `Environment.insertNew`.
    pub fn insert_new(&mut self, name: Name, cinfo: ConstantInfo) -> Result<(), String> {
        if self.consts.contains_key(&name) {
            return Err(format!("Duplicate declaration: {name}"))
        }
        self.consts.insert(name, cinfo);
        Ok(())
    }
}

/// `Expr.instantiateLParams`.
pub fn instantiate_lparams(e: &E, lparams: &[Name], levels: &[Level]) -> Result<E, String> {
    if levels.len() != lparams.len() {
        return Err(format!("Expected {} levels, got {}", lparams.len(), levels.len()))
    }
    Ok(crate::expr::subst_level(e, &|n: &Name| match lparams.iter().position(|p| p == n) {
        Some(i) => levels[i].clone(),
        // "should not happen", as the original says.
        None => Level::Param(n.clone()),
    }))
}
