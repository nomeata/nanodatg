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
//! * [`census`] — which §6.2 clauses the corpus actually spends its nodes on.
//! * [`conv`] — `Γ ⊢ ⟦e⟧ = ⟦e'⟧` and the certificate legs of a reduction.
//! * [`ground`] — the mini side of the pre-pass: levels at a ground σ.
//! * [`ev`] — `Ev`/`Gap`/`Sealed`: evidence, named absences, and the
//!   persistence funnel.
//! * [`scope`] — binder open/close; the only module that names `Thm::assume`.
//! * [`interp`] — `⟦·⟧` against `mini::Expr`, and the per-`(name, σ)` store.
//! * [`ledger`] — what `⟦·⟧` reaches on the corpus, attributed by cause.
//! * [`run`] — the per-file verdict.

pub mod census;
pub mod conv;
pub mod convert;
pub mod env;
pub mod ev;
pub mod expr;
pub mod ground;
pub mod interp;
pub mod kernel;
pub mod ledger;
pub mod run;
pub mod scope;
