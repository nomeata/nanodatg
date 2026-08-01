//! **mini** — a Rust port of
//! [`lean-mini-kernel`](https://github.com/nomeata/lean-mini-kernel), to be
//! made evidence-passing.
//!
//! Mini exists so that the evidence-threading design is built where there are
//! no caches, no hash-consing and no arena to confound it: a `ReaderT LEnv
//! (Except String)` and nothing else, owned de Bruijn expressions with explicit
//! `shift`/`substs`, a local context that is literally a telescope, whnf as a
//! stack machine with full eager delta, and recursors *generated* from
//! inductive declarations rather than parsed. See `MINI-DESIGN.md`.
//!
//! Status: **step (b)** — the port, unproven. `kernel`/`derived` are declared
//! as dependencies for step (c) and not yet used.
//!
//! Layout, one module per `MINI-DESIGN.md` §1 entry that exists yet:
//!
//! * [`expr`] — `Name`, `Level`, `Expr`, `shift`, `substs`, `subst_level`.
//! * [`env`] — `Declaration`, `ConstantInfo`, `Environment`.
//! * [`kernel`] — the port of `Kernel.lean`'s mutual block and
//!   `Environment.add`.
//! * [`convert`] — export file → mini declarations, and the level pre-pass.
//! * [`run`] — the per-file verdict.

pub mod convert;
pub mod env;
pub mod expr;
pub mod kernel;
pub mod run;
