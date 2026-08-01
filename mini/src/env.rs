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
//! No evidence lives here yet; MINI-DESIGN.md §8's `MiniEnv` (the per-ground-
//! instantiation interpretation store) is step (c) and will wrap this.

use crate::expr::{Level, Name, E};
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefKind {
    Def,
    Theorem,
    Opaque,
}

/// A declaration, as sent to `Environment::add`.
#[derive(Clone, Debug)]
pub enum Declaration {
    Axiom { name: Name, lparams: Vec<Name>, ty: E },
    Def { name: Name, lparams: Vec<Name>, ty: E, value: E, kind: DefKind },
    Quot,
    Inductive { name: Name, lparams: Vec<Name>, num_params: u32, ty: E, ctors: Vec<(Name, E)> },
}

impl Declaration {
    pub fn name(&self) -> Name {
        match self {
            Declaration::Axiom { name, .. } => name.clone(),
            Declaration::Def { name, .. } => name.clone(),
            Declaration::Quot => Name::simple("Quot"),
            Declaration::Inductive { name, .. } => name.clone(),
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
    /// `fun params motive minors fields => …`. `k_type`, when present, is the
    /// body of `fun params => …` and says which type the major argument must
    /// have for the K-rule to fire.
    Recursor {
        lparams: Vec<Name>,
        ty: E,
        num_params: u32,
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
}

impl Environment {
    pub fn empty() -> Environment { Environment::default() }

    pub fn get(&self, n: &Name) -> Option<&ConstantInfo> { self.consts.get(n) }

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
