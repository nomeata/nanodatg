//! **The level-instantiation pre-pass.**
//!
//! Which universe levels a declaration is going to be *used at* is decided
//! before any checking starts, by a worklist fixpoint over the export file.
//! The rest of the checker then runs once per declaration per instantiation,
//! with the backend told which instantiation it is under. This module computes
//! the schedule; [`crate::util::TcCtx::under_sigma`] is where it takes effect.
//!
//! # Why the interpretation forces this
//!
//! `⟦·⟧` is not well defined on a declaration at *its own* universe
//! parameters. Two independent reasons, both measured:
//!
//! * `TgBackend::interp_sort` sends `max`, `imax` and a bare parameter to an
//!   opaque symbol, while `Sort 0` and `Sort (n+1)` climb the universe tower.
//!   And `subst_expr_levels` substitutes into a constant's *value* before that
//!   value is interpreted, so `⟦c.{0}⟧` and `⟦c.{u}⟧` are definitions of two
//!   different bodies.
//! * Worse, `Level::simplify` never simplifies `IMax(l, r)` when `r` is a
//!   `Param`. So a `Π` whose codomain sits in `Sort (imax u v)` is a
//!   **proposition** when `v := 0` and a **function space** otherwise, and
//!   §6.2 gives those two things *different sets*. Taking either branch is
//!   taking the wrong one on some instantiation, so
//!   [`crate::tg`] takes neither and reports `TyGap::PiUndet`.
//!
//! On `init-prelude` that is 2206 `Π` nodes — 38% of the population — every one
//! of them inside a level-polymorphic declaration.
//!
//! Checking each declaration once *per ground instantiation* removes the
//! problem at the root rather than teaching the interpretation to hedge: at a
//! ground instantiation every level is a numeral, every `imax` simplifies, and
//! exactly one clause of §6.2 applies.
//!
//! # A ground instantiation is a vector of natural numbers
//!
//! Not an arbitrary level: substituting numerals for every parameter and
//! simplifying always yields `succ^n(zero)`. `Max` of two numerals combines to
//! their maximum, and `IMax(l, r)` at a numeral `r` is `0` when `r` is `0` and
//! the maximum otherwise. So an instantiation is a [`Inst`] — `Vec<u32>`, one
//! entry per universe parameter — which is arena-independent, hashable, and
//! cheap to propagate. [`eval`] is the evaluator, and it reproduces
//! `subst_level` followed by `simplify` exactly on ground input.
//!
//! # The fixpoint is not a single sweep
//!
//! Demand propagates: `(d, σ)` being required makes `(c, σ')` required for
//! every constant `c` that `d`'s type, value or recursor rules mention, at the
//! level arguments *evaluated under σ*. A single sweep of the export file
//! undercounts, because a pair discovered late feeds pairs discovered earlier.
//! Measured on `init-prelude`: one sweep finds 856 pairs, the fixpoint 1154 —
//! a 26% undercount.
//!
//! # The default, and why it is a constant rather than a theorem
//!
//! Roughly half of `init-prelude`'s declarations are demanded by nothing at
//! all. Skipping them would mean not checking them, so they are checked at a
//! fixed set of arbitrary instantiations — see [`DEFAULT_LEVELS`].

use crate::env::Declar;
use crate::expr::Expr;
use crate::level::Level;
use crate::util::{
    new_fx_hash_map, new_fx_hash_set, new_fx_index_set, DagMarker, ExportFile, ExprPtr, FxHashMap, FxHashSet,
    FxIndexSet, LevelPtr, NamePtr, TcCtx,
};

/// **The universe levels a never-demanded declaration's parameters are
/// instantiated at.**
///
/// A choice, not a theorem: roughly half of `init-prelude`'s declarations —
/// 1007 of 2059 — are demanded by nothing, and a declaration nothing uses has
/// no instantiation it *ought* to be checked at. The point of checking it at
/// some is only that it is not skipped.
///
/// **It is a list because one entry was a bug.** `Sort 0` is `Prop`, so a
/// single default of `0` puts every otherwise-unused polymorphic declaration
/// under §6.2's `Prop` clauses and a single default of `1` puts them under the
/// `Type` clauses — two different checking problems over the same file, and for
/// a long time they gave different answers, which is a defect in the
/// interpretation rather than a knob to tune. An unused constant should be
/// checked as if it were used at `0` **and** as if it were used at `1`, and
/// both should work.
///
/// Each entry is closed over exactly as a demanded pair is, so this is not a
/// second, unpropagated seeding: `d` at all-zeros pulls in everything `d`
/// mentions at the levels that evaluates to, and likewise at all-ones. A
/// monomorphic declaration has one instantiation whatever the list says — the
/// empty vector — and the [`demand`] set is a set, so it is scheduled once.
///
/// Measured over the tutorial corpus, after the `λ`/application split of §6.2
/// (see [`crate::tg::TgBackend::term_clause`]) and the projection typing rule
/// ([`crate::tg::TgBackend::has_type_proj`]):
///
/// | | tutorial gaps | escapes | zero-gap files | `init-prelude` gaps | pairs |
/// | --- | ---: | ---: | ---: | ---: | ---: |
/// | `[0]` | 179 | 69 | 70 | 10747 | 2414 |
/// | `[1]` | 197 | 68 | 70 | 11114 | 2652 |
/// | `[0, 1]` | 215 | 78 | 69 | 16384 | 3861 |
///
/// The 27-file inductive-free fragment is at zero gaps and zero escapes under
/// **each** of the three, which is what the list is for. The combined row is
/// larger than either single one because it is *more checking*, not worse
/// checking: a defaulted declaration is checked twice, so a file's one gap is
/// reported twice. The `(declaration, instantiation)` pair count is the honest
/// measure of the cost — 2652 → 3861 on `init-prelude`, +46%, for 13.2s → 21.4s
/// of wall clock.
///
/// **`[0]` was the row the two lists disagreed on, and the projection typing
/// rule is what moved it.** It read 186 / 68 before, against `[1]`'s 197 / 68,
/// and the whole of that difference was one file: `081_PSigma.snd`, 8 gaps at
/// `[0]` and 0 at `[1]`, because at `u = v = 0` a `PSigma` field is a
/// proposition and its projection is a proof the interpretation had no typing
/// rule for. Seven of the eight close; the eighth is the escape row and is the
/// missing *interpretation* of `PSigma`, not a missing rule. `[1]` does not
/// move at all, which is the check that the rule is not paying for itself
/// somewhere else.
pub const DEFAULT_LEVELS: &[u32] = &[0, 1];

/// One ground instantiation: a natural number per universe parameter, in the
/// declaration's own parameter order.
pub type Inst = Vec<u32>;

/// The stable per-run identity of an export-file name.
///
/// The same key [`crate::tg::TgBackend`] uses, and for the same reason: the
/// export file's arena is parsed once and never changes, so a name's index in
/// it is stable for the whole run, while a `TcCtx` name's index is reused by
/// the next declaration for something else.
pub type NameKey = u32;

/// The key of `n`, or `None` if `n` lives in a per-declaration arena and so has
/// no identity outside it.
pub(crate) fn name_key(n: NamePtr<'_>) -> Option<NameKey> {
    match n.dag_marker() {
        DagMarker::ExportFile => Some(n.raw()),
        DagMarker::TcCtx => None,
    }
}

/// What the pre-pass found, and what it cost to find it.
#[derive(Default, Clone, Copy, Debug)]
pub struct Stats {
    /// Declarations in the export file.
    pub declars: usize,
    /// Declarations with no universe parameters, which seed the fixpoint.
    pub monomorphic: usize,
    /// `(declaration, instantiation)` pairs after propagating from the seeds.
    pub demand_pairs: usize,
    /// Rounds the first closure took.
    pub demand_rounds: usize,
    /// Declarations no other declaration demands at any instantiation.
    pub defaulted: usize,
    /// `(declaration, instantiation)` pairs in total.
    pub pairs: usize,
    /// Rounds in total.
    pub rounds: usize,
    /// Constant occurrences whose level arguments did not evaluate to numerals
    /// under the instantiation being propagated. Should be zero on a
    /// well-formed export file: `check_declar_info` asserts every parameter a
    /// declaration mentions is one of its own.
    pub nonground_edges: usize,
    /// Seeds added for the literal-expansion constants, which the checker mints
    /// itself and which therefore appear in no expression in the file.
    pub extension_seeds: usize,
    /// Scheduled pairs whose declaration **carries a value** — `def`, `thm`,
    /// `opaque`. The static counterpart of the declaration-typing ledger's
    /// `Dt::Seen`, computed here before any checking, so that a walk which
    /// reaches fewer declarations cannot quietly shrink its own denominator.
    pub value_pairs: usize,
    /// Scheduled pairs whose declaration is an **axiom the goal's sentence
    /// excludes** — an axiom that is not one of Lean's three standard ones.
    ///
    /// Counted from the schedule rather than from the parser's drop list on
    /// purpose: whether a non-standard axiom reaches the schedule at all
    /// depends on `permitted_axioms`, and a goal denominator that moves with a
    /// config flag is not a denominator. Excluding it here makes `population`
    /// the same number under `unsafe_permit_all_axioms` (where `sorryAx` *is*
    /// scheduled, at 2 pairs) and under Lean's three (where it never reaches
    /// the pre-pass).
    pub skipped_pairs: usize,
    /// Scheduled pairs, split over the eight [`Declar`] variants in the order
    /// [`declar_kind`] assigns.
    pub pairs_by_kind: [usize; N_DECLAR_KINDS],
}

/// The [`Declar`] variants, in report order.
pub const N_DECLAR_KINDS: usize = 8;
pub const DECLAR_KINDS: [&str; N_DECLAR_KINDS] =
    ["def", "thm", "opaque", "axiom", "inductive", "ctor", "recursor", "quot"];

/// Which of [`DECLAR_KINDS`] a declaration is.
pub fn declar_kind(d: &Declar<'_>) -> usize {
    match d {
        Declar::Definition { .. } => 0,
        Declar::Theorem { .. } => 1,
        Declar::Opaque { .. } => 2,
        Declar::Axiom { .. } => 3,
        Declar::Inductive(..) => 4,
        Declar::Constructor(..) => 5,
        Declar::Recursor(..) => 6,
        Declar::Quot { .. } => 7,
    }
}

/// Lean's three standard axioms, tested on the name's own structure.
///
/// The same predicate as `mini::convert::is_standard_axiom`; `checker` does not
/// depend on `mini`, and a string round-trip to share one would be a worse
/// coupling than eight lines.
fn is_standard_axiom<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, n: NamePtr<'t>) -> bool {
    use crate::name::Name;
    let Name::Str(pre, s, _) = ctx.read_name(n) else { return false };
    let s = ctx.read_string(s);
    match ctx.read_name(pre) {
        Name::Anon => &*s == "propext",
        Name::Str(root, q, _) if matches!(ctx.read_name(root), Name::Anon) => {
            let q = ctx.read_string(q);
            matches!((q.as_ref(), s.as_ref()), ("Quot", "sound") | ("Classical", "choice"))
        }
        _ => false,
    }
}

/// The schedule: which instantiations each declaration must be checked at.
pub struct Instantiations {
    by_name: FxHashMap<NameKey, FxIndexSet<Inst>>,
    pub stats: Stats,
    /// The declarations behind [`Stats::skipped_pairs`], spelled.
    pub skipped_names: Vec<String>,
}

impl Instantiations {
    /// The instantiations `name` must be checked at. Never empty for a
    /// declaration of the export file: the default seeding guarantees one.
    pub fn for_name(&self, name: NamePtr<'_>) -> Option<&FxIndexSet<Inst>> {
        self.by_name.get(&name_key(name)?)
    }

    /// Whether the pre-pass predicted this pair. The audit in
    /// [`crate::tg`] asks exactly this, and a `false` is the finding that the
    /// pre-pass is incomplete.
    pub fn predicted(&self, key: NameKey, inst: &[u32]) -> bool {
        self.by_name.get(&key).is_some_and(|s| s.contains(inst))
    }
}

/// The published schedule, so that the backend's audit can consult it without
/// being handed one at every call.
///
/// Replaced rather than set once: a process may check more than one export
/// file, and a schedule keyed on *that* file's name indices says nothing about
/// this one — auditing against a stale schedule would manufacture misses. The
/// lock is read on the order of tens of thousands of times per run (once per
/// distinct `Const` node per backend), which is nothing.
static SCHEDULE: std::sync::RwLock<Option<std::sync::Arc<Instantiations>>> = std::sync::RwLock::new(None);

/// Ask the published schedule whether it predicted `(key, inst)`. `None` when
/// no schedule is published — the library's other entry points do not build
/// one, and an audit with nothing to audit against must not report a miss.
pub(crate) fn was_predicted(key: NameKey, inst: &[u32]) -> Option<bool> {
    let g = SCHEDULE.read().ok()?;
    Some(g.as_ref()?.predicted(key, inst))
}

/// The published schedule's statistics, for the report.
pub(crate) fn published_stats() -> Option<Stats> {
    let g = SCHEDULE.read().ok()?;
    Some(g.as_ref()?.stats)
}

/// The names behind [`Stats::skipped_pairs`], so the report can print them
/// rather than a bare count. A skipped population that is not named is a
/// population nobody can check.
pub(crate) fn published_skipped() -> Vec<String> {
    let Ok(g) = SCHEDULE.read() else { return Vec::new() };
    g.as_ref().map(|i| i.skipped_names.clone()).unwrap_or_default()
}

/// A declaration's dotted name, written into `out`.
fn spell_name<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, n: NamePtr<'t>, out: &mut String) {
    use crate::name::Name;
    match ctx.read_name(n) {
        Name::Anon => {}
        Name::Str(pre, s, _) => {
            if !matches!(ctx.read_name(pre), Name::Anon) {
                spell_name(ctx, pre, out);
                out.push('.');
            }
            out.push_str(ctx.read_string(s).as_ref());
        }
        Name::Num(pre, i, _) => {
            if !matches!(ctx.read_name(pre), Name::Anon) {
                spell_name(ctx, pre, out);
                out.push('.');
            }
            out.push_str(&i.to_string());
        }
    }
}

/// Evaluate a **ground** level to the natural number it denotes, or `None` if a
/// parameter outside `env` occurs in it.
///
/// This is `subst_level` followed by `simplify`, read off rather than
/// allocated. The `IMax` clause is the one worth checking against
/// `Level::simplify`: there, an `imax` whose left side simplifies to `0` or `1`
/// returns the right side outright, and otherwise dispatches on the right side
/// being `Zero` (giving `0`) or a `Succ` (giving the maximum). At numerals
/// those three cases collapse to "zero if the right side is zero, else the
/// maximum", which is what this computes.
fn eval<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, l: LevelPtr<'t>, env: &FxHashMap<NamePtr<'t>, u32>) -> Option<u32> {
    match ctx.read_level(l) {
        Level::Zero => Some(0),
        Level::Succ(a, _) => Some(eval(ctx, a, env)? + 1),
        Level::Max(a, b, _) => Some(eval(ctx, a, env)?.max(eval(ctx, b, env)?)),
        Level::IMax(a, b, _) => {
            let rb = eval(ctx, b, env)?;
            if rb == 0 {
                Some(0)
            } else {
                Some(eval(ctx, a, env)?.max(rb))
            }
        }
        Level::Param(n, _) => env.get(&n).copied(),
    }
}

/// [`collect_consts`], for the declaration-frontier dump in `tg.rs`.
#[cfg(feature = "stepcount")]
pub(crate) fn collect_consts_pub<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    seen: &mut FxHashSet<ExprPtr<'t>>,
    out: &mut FxIndexSet<(NamePtr<'t>, crate::util::LevelsPtr<'t>)>,
) {
    collect_consts(ctx, e, seen, out)
}

/// Every `Const` occurrence reachable from `e`, pushed onto `out`.
///
/// Iterative rather than recursive: an export file's expressions are a deep
/// DAG, and this runs on the main thread, which has no enlarged stack.
fn collect_consts<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    e: ExprPtr<'t>,
    seen: &mut FxHashSet<ExprPtr<'t>>,
    out: &mut FxIndexSet<(NamePtr<'t>, crate::util::LevelsPtr<'t>)>,
) {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue
        }
        match ctx.read_expr(e) {
            Expr::Const { name, levels, .. } => {
                out.insert((name, levels));
            }
            Expr::App { fun, arg, .. } => {
                stack.push(fun);
                stack.push(arg);
            }
            Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Expr::Let { binder_type, val, body, .. } => {
                stack.push(binder_type);
                stack.push(val);
                stack.push(body);
            }
            Expr::Proj { structure, .. } => stack.push(structure),
            Expr::Local { binder_type, .. } => stack.push(binder_type),
            Expr::Sort { .. } | Expr::Var { .. } | Expr::NatLit { .. } | Expr::StringLit { .. } => {}
        }
    }
}

/// One declaration, reduced to what the fixpoint needs of it.
struct Node<'t> {
    /// The declaration's universe parameter names, in order.
    uparams: Vec<NamePtr<'t>>,
    /// Every constant it mentions, with the level arguments it mentions it at.
    edges: Vec<(NameKey, Vec<LevelPtr<'t>>)>,
}

/// Names the checker mints itself when it expands a literal, which therefore
/// occur in no expression of the export file.
///
/// `str_lit_to_constructor` builds `List.nil.{0} Char`, `List.cons.{0} Char`,
/// `Char.ofNat` and `String.ofList`; `nat_lit_to_constructor` builds
/// `Nat.zero`/`Nat.succ`; the arithmetic extension names appear in
/// `TypeChecker::reduce_nat_lit`. All of them are used at *ground* levels — the
/// three `List` constants at `{0}` and the rest at no levels at all — so
/// seeding each at all-zeros is exact rather than approximate.
///
/// This list is a claim, and [`crate::tg`]'s unpredicted-instantiation row is
/// what checks it: a name the checker interprets at an instantiation this
/// pre-pass did not predict is counted and reported.
fn extension_seed_names<'p>(ef: &ExportFile<'p>) -> Vec<NamePtr<'p>> {
    let c = &ef.name_cache;
    [
        c.eager_reduce, c.quot, c.quot_mk, c.quot_lift, c.quot_ind, c.nat, c.nat_zero, c.nat_succ, c.nat_add,
        c.nat_sub, c.nat_mul, c.nat_pow, c.nat_mod, c.nat_div, c.nat_beq, c.nat_ble, c.nat_gcd, c.nat_xor,
        c.nat_land, c.nat_lor, c.nat_shr, c.nat_shl, c.string, c.string_of_list, c.bool_false, c.bool_true,
        c.char, c.char_of_nat, c.list, c.list_nil, c.list_cons,
    ]
    .into_iter()
    .flatten()
    .collect()
}

impl Instantiations {
    /// Run the pre-pass over `ef`.
    pub fn compute(ef: &ExportFile<'_>) -> Self { ef.with_ctx(|ctx| compute_in(ctx)) }
}

/// Record that `(key, inst)` is required, queueing it if it is new.
fn demand(
    demanded: &mut FxHashMap<NameKey, FxIndexSet<Inst>>,
    frontier: &mut Vec<(usize, Inst)>,
    key: NameKey,
    idx: usize,
    inst: Inst,
) {
    if demanded.entry(key).or_insert_with(new_fx_index_set).insert(inst.clone()) {
        frontier.push((idx, inst));
    }
}

/// Propagate demand until nothing new appears, returning the number of rounds.
///
/// A *round* is one sweep of the current frontier, so the count says how deep
/// the dependency chain that carries a new instantiation is — and it is the
/// number that shows a single sweep would not have sufficed.
fn close<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    nodes: &[Node<'t>],
    index_of: &FxHashMap<NameKey, usize>,
    demanded: &mut FxHashMap<NameKey, FxIndexSet<Inst>>,
    frontier: &mut Vec<(usize, Inst)>,
    stats: &mut Stats,
) -> usize {
    let mut rounds = 0usize;
    while !frontier.is_empty() {
        rounds += 1;
        let mut next: Vec<(usize, Inst)> = Vec::new();
        for (idx, sigma) in std::mem::take(frontier) {
            let node = &nodes[idx];
            let env: FxHashMap<NamePtr<'t>, u32> =
                node.uparams.iter().copied().zip(sigma.iter().copied()).collect();
            for (key, levels) in node.edges.iter() {
                let Some(&tgt) = index_of.get(key) else { continue };
                let mut inst = Vec::with_capacity(levels.len());
                let mut ground = true;
                for l in levels.iter().copied() {
                    match eval(ctx, l, &env) {
                        Some(n) => inst.push(n),
                        None => {
                            stats.nonground_edges += 1;
                            ground = false;
                            break
                        }
                    }
                }
                // A use at the wrong arity is a malformed file, which
                // `check_declar_info` rejects; do not manufacture a schedule
                // entry for it.
                if !ground || inst.len() != nodes[tgt].uparams.len() {
                    continue
                }
                demand(demanded, &mut next, *key, tgt, inst);
            }
        }
        *frontier = next;
    }
    rounds
}

fn compute_in<'t, 'p: 't>(ctx: &mut TcCtx<'t, 'p>) -> Instantiations {
    let ef = ctx.export_file;
    let mut stats = Stats { declars: ef.declars.len(), ..Stats::default() };

    // ── Pass A: reduce every declaration to its universe parameters and its
    // outgoing constant edges. Independent of any instantiation, so it is done
    // once and the fixpoint below only *evaluates* the level arguments.
    let mut nodes: Vec<Node<'t>> = Vec::with_capacity(ef.declars.len());
    let mut index_of: FxHashMap<NameKey, usize> = new_fx_hash_map();
    for (idx, (name, d)) in ef.declars.iter().enumerate() {
        let info = d.info();
        let uparams: Vec<NamePtr<'t>> = ctx
            .read_levels(info.uparams)
            .iter()
            .copied()
            .map(|l| match ctx.read_level(l) {
                Level::Param(n, _) => n,
                // `check_declar_info` asserts this cannot happen; the pre-pass
                // must not panic on a malformed file, so such a declaration
                // simply gets no parameters and is checked at the empty
                // instantiation, exactly as it is today.
                _ => ctx.anonymous(),
            })
            .collect();
        if uparams.is_empty() {
            stats.monomorphic += 1;
        }

        let mut seen: FxHashSet<ExprPtr<'t>> = new_fx_hash_set();
        let mut consts = new_fx_index_set();
        collect_consts(ctx, info.ty, &mut seen, &mut consts);
        match d {
            Declar::Theorem { val, .. } | Declar::Definition { val, .. } | Declar::Opaque { val, .. } =>
                collect_consts(ctx, *val, &mut seen, &mut consts),
            Declar::Recursor(r) =>
                for rule in r.rec_rules.iter() {
                    collect_consts(ctx, rule.val, &mut seen, &mut consts)
                },
            // **An inductive's edges include its constructors' types.** Not
            // because Lean's elaborator needs them — the `Constructor`
            // declarations are nodes in their own right and carry the same
            // types — but because *this checker* interprets them at the
            // inductive's instantiation. `TgBackend::decl_spec` walks every
            // constructor's field types whenever the **inductive** is
            // interpreted at `ℓ⃗`, so a file that mentions `T.{σ}` without
            // mentioning any `c.{σ}` still makes the backend interpret the
            // constants inside `c`'s fields at `σ`. Without this case those
            // instantiations are ones the schedule never predicted, and the
            // unpredicted-instantiation audit row — the row whose entire
            // purpose is to catch the pre-pass missing something — would go
            // nonzero for a reason that is not a defect.
            //
            // The edges are attributed to the *inductive's* node, which is
            // correct rather than approximate: a constructor's `uparams` are
            // the inductive's own (Lean guarantees it, and
            // `check_declar_info` asserts each parameter a declaration
            // mentions is one of its own), so [`eval`] under the inductive's
            // `σ` is the same evaluation the constructor's node would do.
            Declar::Inductive(i) =>
                for cn in i.all_ctor_names.iter() {
                    let Some(Declar::Constructor(c)) = ef.declars.get(cn) else { continue };
                    collect_consts(ctx, c.info.ty, &mut seen, &mut consts)
                },
            _ => {}
        }
        let edges = consts
            .into_iter()
            .filter_map(|(n, ls)| Some((name_key(n)?, ctx.read_levels(ls).to_vec())))
            .collect();

        if let Some(k) = name_key(*name) {
            index_of.insert(k, idx);
        }
        nodes.push(Node { uparams, edges });
    }

    // ── Pass B: the worklist fixpoint.
    let mut demanded: FxHashMap<NameKey, FxIndexSet<Inst>> = new_fx_hash_map();
    let mut frontier: Vec<(usize, Inst)> = Vec::new();

    // Seed: every monomorphic declaration, at the empty instantiation. Demand
    // then flows outwards from them.
    for (idx, (name, _)) in ef.declars.iter().enumerate() {
        if nodes[idx].uparams.is_empty() {
            if let Some(k) = name_key(*name) {
                demand(&mut demanded, &mut frontier, k, idx, Vec::new());
            }
        }
    }
    // …and the literal-expansion constants, which no expression mentions.
    for n in extension_seed_names(ef) {
        let Some(k) = name_key(n) else { continue };
        let Some(&idx) = index_of.get(&k) else { continue };
        let inst = vec![0u32; nodes[idx].uparams.len()];
        let before = demanded.get(&k).is_some_and(|s| s.contains(&inst));
        demand(&mut demanded, &mut frontier, k, idx, inst);
        if !before {
            stats.extension_seeds += 1;
        }
    }

    stats.demand_rounds = close(ctx, &nodes, &index_of, &mut demanded, &mut frontier, &mut stats);
    stats.demand_pairs = demanded.values().map(|s| s.len()).sum();

    // ── The defaults. A declaration nothing demands is still checked, once per
    // entry of [`DEFAULT_LEVELS`] with that level in every parameter, and
    // re-closing from them is what stops the *bonus* from being a second,
    // unpropagated seeding.
    for (idx, (name, _)) in ef.declars.iter().enumerate() {
        let Some(k) = name_key(*name) else { continue };
        if demanded.get(&k).is_some_and(|s| !s.is_empty()) {
            continue
        }
        stats.defaulted += 1;
        for &l in DEFAULT_LEVELS {
            demand(&mut demanded, &mut frontier, k, idx, vec![l; nodes[idx].uparams.len()]);
        }
    }
    stats.rounds = stats.demand_rounds + close(ctx, &nodes, &index_of, &mut demanded, &mut frontier, &mut stats);
    stats.pairs = demanded.values().map(|s| s.len()).sum();

    // ── The goal's denominator, computed here and only here. `translated`'s
    // whole point is that the population it divides by is fixed before the
    // walk starts, so that narrowing what the walk reaches cannot read as
    // progress. See `MEASUREMENTS.md`, "the four denominators".
    let mut skipped_names: Vec<String> = Vec::new();
    for (k, insts) in demanded.iter() {
        let Some(&idx) = index_of.get(k) else { continue };
        let Some((name, d)) = ef.declars.get_index(idx) else { continue };
        let n = insts.len();
        stats.pairs_by_kind[declar_kind(d)] += n;
        if matches!(d, Declar::Definition { .. } | Declar::Theorem { .. } | Declar::Opaque { .. }) {
            stats.value_pairs += n;
        }
        if matches!(d, Declar::Axiom { .. }) && !is_standard_axiom(ctx, *name) {
            stats.skipped_pairs += n;
            let mut sp = String::new();
            spell_name(ctx, *name, &mut sp);
            skipped_names.push(sp);
        }
    }
    skipped_names.sort();

    Instantiations { by_name: demanded, stats, skipped_names }
}

/// Publish the schedule so the backend's audit can read it, and hand it back
/// for the check itself.
pub(crate) fn publish(i: Instantiations) -> std::sync::Arc<Instantiations> {
    let a = std::sync::Arc::new(i);
    if let Ok(mut g) = SCHEDULE.write() {
        *g = Some(a.clone());
    }
    a
}
