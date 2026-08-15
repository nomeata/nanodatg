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
//! # One edge no expression carries
//!
//! Demand is read off `Const` occurrences, and that finds every dependency a
//! *file* has. It does not find the one an external **model filter** creates: a
//! spliced `T._model` tower is named by no expression, so the graph has no arc
//! into it and it falls to the default. [`model_edges`] adds that arc, before
//! the fixpoint rather than in a second one, and its header is where the
//! measurement and the argument live.
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
///
/// # A default is **uniform**, and that is a statement about coverage
///
/// *The paragraph above is this tree's only measurement of one declaration
/// across σ, and it is about a different axis from the one it keeps being cited
/// for. It compares two whole lists — every parameter `0` against every
/// parameter `1` — on Lean's `PSigma`, and what moved was a **projection typing
/// rule** for a `Prop`-valued field. It says nothing about a σ whose entries
/// differ from one another, and it cannot: [`compute_in`]'s default pass spells
/// every default as `vec![l; nparams]`, one level repeated, so no entry of this
/// list — and no list — can ever produce a mixed instantiation.*
///
/// A mixed σ therefore exists only where some declaration **demands** one, at
/// level arguments that evaluate to different numerals — [`model_edges`]
/// included, which is the one edge here that carries a σ rather than reading
/// one off an expression, and carries a mixed one whenever its subject has one.
/// That is not exotic:
/// `vendor/lean-inductive-models/src/InductiveModels/Simple.lean:26` builds
/// `False`'s role over the model basis as `PSigma'.{0,u} (fun _ : p =>
/// PUnit.{u})`, so every model on that tool's Type route carries one. But until
/// `checker/tests/fixtures/psigma_mixed_sigma.lean` nothing in
/// `vendor/arena-tests` or in `checker/tests/fixtures` demanded one, and
/// **`(0,1)` and `(1,0)` had never been run on anything.** Absent is not
/// passing.
///
/// Measured there, over four demanded σ of two declarations that differ only in
/// their declared resultant sort: the general data carrier takes one `Prop`
/// component and one data component at rung 1 without complaint, and `PSigma'`
/// declines at both mixed σ for the reason it already declines at `(1,1)` —
/// `ind-spec(PSigma': class (P) above Prop)`, a classification made on the
/// declaration's own level expression before σ exists. `MODEL-BASIS.md` §8.6
/// and `mini_designed::
/// psigma_at_mixed_sigma_declines_only_where_the_declared_sort_may_be_prop`
/// carry it; none of it is a property of this constant.
pub const DEFAULT_LEVELS: &[u32] = &[0, 1];

/// **The largest level any scheduled instantiation may name**, and the reason
/// the fixpoint below terminates at all.
///
/// # Why there has to be one
///
/// [`close`] is a worklist over `(declaration, σ)` pairs, and the declarations
/// are finite. σ is not: an edge's level arguments may contain `Succ`, so a
/// **cycle in the mention graph along which some level strictly increases**
/// generates `σ, σ+1, σ+2, …` and the worklist never empties. Nothing else in
/// this module bounds that — the loop runs until the frontier is empty and
/// allocates a new `Inst` per pair — so without this constant the pre-pass's
/// termination is a property of the *input file* rather than of this code.
/// With it the reachable pair set is at most `Σ_d (C+1)^{|uparams(d)|}`, which
/// is finite, so the fixpoint terminates on every input including a malformed
/// or hostile one. That is the whole of the soundness argument, and it does not
/// depend on any property of the export.
///
/// # Why *this* number
///
/// It has to be far above anything a real file demands, and it is. The largest
/// entry of any scheduled σ, measured over all 189 `.ndjson` in
/// `checker/tests/fixtures`, `vendor/arena-tests/good/tutorial` and
/// `modelgen/tests`, is **3**; over `init-prelude` it is **4**. The mini
/// interpretation's cumulative tower is built to
/// [`crate::mini::interp::CUMUL_HEIGHT`] = 8 rungs, so a σ above *that* is one
/// the interpretation could not represent even if it were scheduled. 32 is 8×
/// the largest measured demand and 4× the tower, and it is a number no
/// well-formed export has ever come near.
///
/// # A drop is counted, never silent
///
/// [`Stats::level_cap_drops`] is how many edges this refused. Zero on every
/// input above, so it is also the alarm: a nonzero reading says the schedule is
/// incomplete and names how badly, and [`crate::tg`]'s
/// unpredicted-instantiation row is the independent detector that would see the
/// consequence.
pub const MAX_INSTANTIATION_LEVEL: u32 = 32;

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
    /// Edges added by [`model_edges`] — one per model declaration whose subject
    /// is a declaration of the same file. Zero on every file no model filter
    /// has been over, which is what makes it the number to read when a
    /// modelgen'd file's pair count moves.
    pub model_edges: usize,
    /// Edges [`close`] refused because their instantiation named a level above
    /// [`MAX_INSTANTIATION_LEVEL`]. Zero on every input measured; see that
    /// constant for what a nonzero reading means.
    pub level_cap_drops: usize,
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
    /// The same parameters as *levels*, which is what an edge carries. Kept
    /// beside the names rather than rebuilt because [`model_edges`] needs an
    /// edge whose level arguments are exactly the source's own parameters.
    uparam_levels: Vec<LevelPtr<'t>>,
    /// Every constant it mentions, with the level arguments it mentions it at.
    edges: Vec<(NameKey, Vec<LevelPtr<'t>>)>,
}

/// **The declaration a model declaration models, read off its name** — the
/// prefix strictly above the *last* `_model` component, or `None` for a name
/// that has none.
///
/// `PTree._model` ↦ `PTree`, `PTree.node._model` ↦ `PTree.node`,
/// `PTree.rec._model.iota_0` ↦ `PTree.rec`, `PTree._model._impl.0` ↦ `PTree`.
/// The *last* component rather than the first, so that a model of a model —
/// which nothing emits today — would be attributed to the inner subject rather
/// than to the outer one, and so that `r._model.iota_j` is attributed to `r`
/// rather than being a name with two answers.
///
/// Both producers are covered by one rule and neither is named:
/// `lean-inductive-models` forms every public name as `n._model`
/// (`vendor/lean-inductive-models/src/InductiveModels/Naming.lean:77`) and
/// roots its private bookkeeping at `T._model._impl.*`; `modelgen/`'s legacy
/// tower is `T._model.self` / `T._model.ctor_j` / `T._model.rec_k` /
/// `T._model.iota_k_j` / `T._model.pack_i`, every one of which has `T` above
/// its `_model`.
fn modelled_prefix<'t, 'p: 't>(ctx: &TcCtx<'t, 'p>, n: NamePtr<'t>) -> Option<NamePtr<'t>> {
    use crate::name::Name;
    let mut cur = n;
    loop {
        match ctx.read_name(cur) {
            Name::Anon => return None,
            Name::Str(pre, s, _) => {
                if &*ctx.read_string(s) == "_model" {
                    return (!matches!(ctx.read_name(pre), Name::Anon)).then_some(pre)
                }
                cur = pre;
            }
            Name::Num(pre, _, _) => cur = pre,
        }
    }
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
                // **The termination bound** — see [`MAX_INSTANTIATION_LEVEL`].
                // Checked here rather than at the seeds because a level grows
                // only by traversing an edge, so this is the only place a σ
                // this module did not write itself can appear.
                if inst.iter().any(|&n| n > MAX_INSTANTIATION_LEVEL) {
                    stats.level_cap_drops += 1;
                    continue
                }
                demand(demanded, &mut next, *key, tgt, inst);
            }
        }
        *frontier = next;
    }
    rounds
}

/// **The edge from a modelled declaration to its model**, added to the mention
/// graph before the fixpoint runs. Returns how many edges were added.
///
/// # The defect this closes
///
/// An external filter (`modelgen/`, `lean-inductive-models`) splices a model
/// tower into the export ahead of each declaration it models. The tower's
/// declarations are ordinary declarations of the file — [`compute_in`] sees
/// them, checks them and closes over what *they* mention — but **nothing
/// mentions them**. `T._model` is named by no expression in the file, so it is
/// [`Instantiations::stats`]`.defaulted`, and a defaulted declaration is
/// scheduled at [`DEFAULT_LEVELS`] and nowhere else.
///
/// That is invisible while `DEFAULT_LEVELS` happens to cover the σ in play and
/// wrong as soon as it does not. Measured on
/// `checker/tests/fixtures/tool_poly_nested.ndjson`, where `PTree.{u}` is used
/// at **three** universes:
///
/// ```text
/// PTree                       [[0], [1], [2]]      demanded, by atZero/atOne/atTwo
/// PTree._model                [[0], [1]]           defaulted
/// PTree._model._impl.0        [[0], [1]]           defaulted
/// PTree.node._model           [[0], [1]]           defaulted
/// ```
///
/// `crate::mini::ledger::Ledger::walk_decl` interprets a declaration at the σ
/// the schedule holds for it, in **file order**, and the tower comes before
/// `PTree`. So `⟦PTree._model.{2}⟧` is never built, and
/// `crate::mini::zoneb`'s `model_alias` — which looks the model up at the
/// constant's *own* σ — reports `nested model not interpreted` at one of the
/// three instantiations.
///
/// # Why the fix is an edge and not a second closure
///
/// The obvious reading is that the demand closure has to be **re-taken** once
/// the splicer has propagated σ onto the model constants. It does not, and the
/// reason is the one deletion in `crate::mini::nested_splice`'s history: the
/// model is *in the file*. Every node the closure would need is already in the
/// graph and already carries its own outgoing edges — `T._model`'s value
/// mentions `T._model._impl.0`, which mentions its constructors. The single
/// missing arc is the one no expression can carry, from the modelled
/// declaration to its model, and adding it **before** the existing fixpoint
/// means no fixpoint is taken twice: the cost is one graph edge per model
/// declaration, and it is paid inside the closure that was already running.
///
/// # What the closure costs, measured
///
/// Over all 189 `.ndjson` in `checker/tests/fixtures`,
/// `vendor/arena-tests/good/tutorial` and `modelgen/tests`, plus
/// `init-prelude`, with `demand_rounds` / `rounds` / `pairs` read off
/// [`Stats`]:
///
/// * **180 of 189 files add no edge at all** — a file no model filter has been
///   over has no `_model` name — and every number on them is identical.
/// * **Seven of the nine that do are identical in every number but
///   `model_edges`.** They are `modelgen/`'s legacy fixtures (`nested_iota`,
///   187 edges on `nested_shapes`, …), whose towers are universe-monomorphic:
///   the edge fires, carries the one σ `[]`, and lands where the default
///   already was.
/// * **Two move**, and both are the external tool's:
///   `tool_nested_keying` 3 / 5 / 157 → 4 / 6 / **155**, and
///   `tool_poly_nested` 3 / 6 / 92 → 5 / 7 / 112.
/// * The deepest closure anywhere is `init-prelude`'s 7 / 13, and it is
///   **unmoved** — an unfiltered export has no model names.
///
/// So: **at most one extra round, on two files out of 190**, and +18 pairs in
/// 6378 across the sweep. `tool_nested_keying` going *down* is the shape worth
/// noting: a model that becomes demanded stops being defaulted, so it is
/// scheduled at the one σ it is used at instead of at both of
/// [`DEFAULT_LEVELS`].
///
/// **The added σ do demand more σ, and that is the work being paid for rather
/// than overhead.** `tool_poly_nested`'s demand closure deepens by two rounds
/// because `PTree._model` at `{2}` reaches `List.rec.{3,2}` and `Eq.{3}` — the
/// tower at the third universe genuinely needs them, and before this edge
/// neither was scheduled. What bounds that iteration is
/// [`MAX_INSTANTIATION_LEVEL`], not this edge's shape; see there.
///
/// # This is a name rule, and what that is and is not allowed to decide
///
/// `crate::mini::nested_splice`'s header argues at length that `⟦T⟧ :=
/// ⟦T._model⟧` must **not** be spelled as a name rule, and that argument
/// stands: a file that declares its own `Tree._model` would get its
/// interpretation silently substituted for the model's, and the counters would
/// report a working model. Nothing here touches that. The keying stays where it
/// is, behind that module's statement check, and this pass cannot key anything.
///
/// What a false positive costs here is **scheduling**: a declaration named
/// `Foo._model` that models nothing is checked at `Foo`'s instantiations
/// instead of at [`DEFAULT_LEVELS`]. That is more checking of a declaration
/// that was going to be checked anyway, at instantiations some declaration of
/// the same file genuinely demands. It cannot make a wrong conclusion, only a
/// differently-shaped schedule — which is the same latitude [`DEFAULT_LEVELS`]
/// itself is chosen under.
///
/// # This edge can close a cycle, and that is what the level cap is for
///
/// Every other edge in this graph comes from a `Const` occurrence, and an
/// export file's definitions are acyclic — the cycles that do exist (a
/// recursor's rules naming the recursor, an inductive naming its own
/// constructors) carry the declaration's own parameters and so are the identity
/// on σ. This edge is the identity on σ too, but it points at a subgraph
/// nothing else points into, so `subject → model ⟶ subject` is a cycle the
/// graph did not have before. If some path from a model tower back to its own
/// subject named it at `Succ` of anything, the fixpoint would generate
/// `σ, σ+1, σ+2, …` and never stop.
///
/// Both producers' contracts exclude such a path — a model exists to *replace*
/// its subject, and `nested_splice`'s statement check declines a tower that
/// states something else — but "the producer would not do that" is not a
/// termination argument for code that runs on an untrusted file.
/// [`MAX_INSTANTIATION_LEVEL`] is, and it is why this edge is safe to add
/// without proving anything about the export.
/// `instantiations::tests::a_model_edge_that_closes_an_increasing_cycle_is_bounded`
/// is that cycle, built, and it is the falsifier for the cap: without the cap
/// that fixture does not terminate.
///
/// # The arity guard is [`close`]'s, not a second one
///
/// The edge carries the source's own parameters as its level arguments, so
/// under σ it evaluates to σ. [`close`] already drops an edge whose evaluated
/// arity is not the target's, so a `T._model.rec_k` that binds a motive level
/// `T` does not bind is dropped there rather than mis-scheduled — legacy's
/// recursor tower is exactly that case, and it keeps its default. A model whose
/// parameters are in a different *order* from its subject's would be scheduled
/// at a permuted σ; that would also fail `nested_splice`'s statement check and
/// be declined rather than keyed, so the cost is again scheduling and not a
/// conclusion.
fn model_edges<'t, 'p: 't>(
    ctx: &TcCtx<'t, 'p>,
    ef: &ExportFile<'p>,
    index_of: &FxHashMap<NameKey, usize>,
    nodes: &mut [Node<'t>],
) -> usize {
    let mut added = 0usize;
    for (idx, (name, _)) in ef.declars.iter().enumerate() {
        let Some(k) = name_key(*name) else { continue };
        let Some(pre) = modelled_prefix(ctx, *name) else { continue };
        let Some(pk) = name_key(pre) else { continue };
        let Some(&src) = index_of.get(&pk) else { continue };
        // A declaration cannot be its own model. Unreachable from either
        // producer's naming — `modelName n = n._model` is not the identity —
        // and refusing it costs one comparison.
        if src == idx {
            continue
        }
        let levels = nodes[src].uparam_levels.clone();
        nodes[src].edges.push((k, levels));
        added += 1;
    }
    added
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
        let uparam_levels: Vec<LevelPtr<'t>> = ctx.read_levels(info.uparams).to_vec();
        let uparams: Vec<NamePtr<'t>> = uparam_levels
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
        nodes.push(Node { uparams, uparam_levels, edges });
    }

    // ── Pass A′: the edges no expression carries.
    stats.model_edges = model_edges(ctx, ef, &index_of, &mut nodes);

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// The schedule of a `checker/tests/fixtures` export, spelled.
    ///
    /// The whole pre-pass over a real export in four lines, with no `mini` in
    /// the path: what these tests assert is a property of *this* module, and
    /// routing it through the loader would make a decline in the loader read as
    /// a change here.
    fn schedule(fixture: &str) -> (Stats, BTreeMap<String, Vec<Inst>>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(format!("{fixture}.ndjson"));
        assert!(path.exists(), "{} is missing", path.display());
        let cfg: crate::util::Config = serde_json::from_str(&format!(
            r#"{{"export_file_path": {},
                 "unpermitted_axiom_hard_error": false,
                 "unsafe_permit_all_axioms": true,
                 "nat_extension": true,
                 "string_extension": true,
                 "print_axioms": false,
                 "print_success_message": false}}"#,
            serde_json::to_string(&path.to_string_lossy().to_string()).unwrap()
        ))
        .expect("config");
        let (ef, _) = cfg.to_export_file().expect("parse");
        let insts = Instantiations::compute(&ef);
        // A second context over the same export file. `name_key` is the
        // export's own arena index, which is what both contexts read, so the
        // keys line up — that is the property `name_key`'s header states.
        let table = ef.with_ctx(|ctx| {
            let mut out: BTreeMap<String, Vec<Inst>> = BTreeMap::new();
            for (name, _) in ef.declars.iter() {
                let Some(k) = name_key(*name) else { continue };
                let mut spelled = String::new();
                spell_name(ctx, *name, &mut spelled);
                let mut v: Vec<Inst> =
                    insts.by_name.get(&k).map(|s| s.iter().cloned().collect()).unwrap_or_default();
                v.sort();
                out.insert(spelled, v);
            }
            out
        });
        (insts.stats, table)
    }

    /// **A spliced model tower is scheduled at the σ its subject is used at,
    /// and the third one is what says so.**
    ///
    /// `tool_poly_nested.ndjson` is `lean-inductive-models` (HEAD `5a9a70f`)
    /// over `modelgen/tests/poly_nested_used.lean`, filtered `--nested
    /// --no-simple --no-mutual --no-basic`, so it carries one model family.
    /// `PTree.{u}` is used at **three** universes there, and the producer's own
    /// header says why three: "two copies cannot distinguish a
    /// per-instantiation model from a model emitted once per *something else
    /// that happens to come in pairs*". [`DEFAULT_LEVELS`] is `[0, 1]` — a
    /// pair — so a fixture at two universes passes this test under the very
    /// defect it exists to catch, and every assertion below is on the exact set
    /// `{[0], [1], [2]}`.
    ///
    /// # What it caught
    ///
    /// Before [`model_edges`]: `PTree` at `[[0], [1], [2]]` and the whole
    /// tower — `PTree._model`, `PTree._model._impl.0` and its constructors,
    /// `pack_0`/`unpack_0`/`congrPack_0` — at `[[0], [1]]`, because nothing in
    /// the export mentions a model constant and a declaration nothing mentions
    /// is defaulted. `crate::mini::ledger` walks a declaration at the σ the
    /// schedule holds, so `⟦PTree._model.{2}⟧` was never built and
    /// `crate::mini::zoneb`'s `model_alias` reported `nested model not
    /// interpreted` at one instantiation of three.
    ///
    /// # Falsifiers
    ///
    /// Run, not predicted. Each mutation was applied, built and measured, and
    /// each died at the assertion named:
    ///
    /// | mutation | died at |
    /// | --- | --- |
    /// | the edge is built and counted but never pushed onto the source's edge list | `PTree._model` is `[[0], [1]]` where `[[0], [1], [2]]` was wanted |
    /// | the edge carries all-zeroes instead of the subject's own parameters | the same assertion, same reading — a σ that does not travel is a σ that is not there |
    /// | [`modelled_prefix`] returns the prefix of **every** name, `_model` or not | `PTree._model._impl.unpack_0` is `[[0], [1]]` — its prefix `PTree._model._impl` is not a declaration, so it loses the edge it had — and [`an_export_with_no_model_names_gains_no_edge`] reads 4 edges on `psigma_mixed_sigma` where 0 was wanted |
    ///
    /// **One mutation did *not* die, and the note is here rather than in a
    /// falsifier list that would have claimed it did.** Making
    /// [`modelled_prefix`] take the leftmost `_model` component rather than the
    /// rightmost changes nothing, on this fixture or anywhere in the tree: no
    /// name either producer emits has **two** `_model` components, so the two
    /// readings coincide on every input that exists. The rightmost is still the
    /// right choice — `r._model.iota_j` has to follow `r`, and a model of a
    /// model would have to follow the inner subject — but it is a choice
    /// nothing here can hold down, and saying so is worth more than a fourth
    /// row.
    ///
    /// `PTree.leaf` and `PTree.node` are asserted **unmoved** at `[[0], [1]]`
    /// for the third mutation's sake: they are the ordinary names whose prefix
    /// is a declaration, and a rule that fired on prefixes rather than on
    /// `_model` would move them.
    #[test]
    fn a_spliced_model_is_scheduled_at_the_sigma_its_subject_is_used_at() {
        let (stats, s) = schedule("tool_poly_nested");
        let three = vec![vec![0u32], vec![1], vec![2]];
        assert_eq!(s.get("PTree"), Some(&three), "the subject's own σ moved; the fixture changed");
        for n in [
            "PTree._model",
            "PTree._model._impl.0",
            "PTree._model._impl.1",
            "PTree._model._impl.0.leaf",
            "PTree._model._impl.0.node",
            "PTree._model._impl.pack_0",
            "PTree._model._impl.unpack_0",
            "PTree._model._impl.congrPack_0",
        ] {
            assert_eq!(s.get(n), Some(&three), "{n} is not scheduled at PTree's three σ");
        }
        // The recursor half, at the recursor's own arity — two levels, because
        // `T.rec` binds a motive level `T` does not. `PTree.rec` is defaulted
        // here (nothing in this file eliminates a `PTree`), and the point is
        // that its model follows it *whatever* it is rather than being
        // defaulted independently.
        let rec = s.get("PTree.rec").cloned().expect("PTree.rec");
        assert_eq!(rec.len(), 2, "the fixture's recursor σ changed:\n{rec:?}");
        for n in ["PTree.rec._model", "PTree.rec._model.iota_0", "PTree.rec._model.iota_1"] {
            assert_eq!(s.get(n), Some(&rec), "{n} does not follow PTree.rec");
        }
        // An ordinary name whose prefix is a declaration must be untouched.
        assert_eq!(s.get("PTree.leaf"), Some(&vec![vec![0u32], vec![1]]));
        assert_eq!(s.get("PTree.node"), Some(&vec![vec![0u32], vec![1]]));
        assert_eq!(stats.model_edges, 22, "the tower's size changed");
        assert_eq!(stats.level_cap_drops, 0, "a well-formed file must not reach the level cap");
    }

    /// **A file no model filter has been over is untouched, and this is the
    /// only assertion that can say so.**
    ///
    /// `model_edges` is the number to read: it is the count of edges the rule
    /// added, so zero here is "the rule looked and fired on nothing", which is
    /// a different statement from "the schedule happens to be unchanged".
    #[test]
    fn an_export_with_no_model_names_gains_no_edge() {
        for f in ["psigma_mixed_sigma", "nat_char_equations"] {
            let (stats, _) = schedule(f);
            assert_eq!(stats.model_edges, 0, "{f} gained a model edge");
            assert_eq!(stats.level_cap_drops, 0, "{f} reached the level cap");
        }
    }

    /// **The model edge can close a level-increasing cycle, and
    /// [`MAX_INSTANTIATION_LEVEL`] is what makes the fixpoint terminate
    /// anyway.**
    ///
    /// `model_edge_cycle.ndjson` is hand-written — it has no `.lean` beside it
    /// for the same reason `budget_decline.ndjson` does not, being a shape no
    /// producer emits — and is two declarations:
    ///
    /// ```text
    /// def Foo.{u}        : Sort (u+1) := Sort u
    /// def Foo._model.{u} : Sort (u+2) := Foo.{u+1}
    /// ```
    ///
    /// [`model_edges`] adds `Foo → Foo._model` at `{u}`; the file's own value
    /// gives `Foo._model → Foo` at `{u+1}`. Together they are a cycle on which
    /// the level strictly increases, so the worklist generates `Foo.{0}`,
    /// `Foo.{1}`, `Foo.{2}`, … **without this cap it does not terminate.**
    /// Measured, not predicted: with the cap's condition disabled and the test
    /// binary run under `ulimit -v 4000000`, it dies with `memory allocation of
    /// 4 bytes failed` and dumps core rather than reaching any assertion. That
    /// is the cap's falsifier, and it is an abort rather than a red line.
    ///
    /// Neither edge is a cycle alone: without [`model_edges`] the closure stops
    /// at `Foo` = `[[0], [1], [2]]` — measured — which is the second falsifier
    /// and the one that kills this test on a deleted rule.
    ///
    /// The numbers are exact rather than bounds. Both declarations default to
    /// `[0]` and `[1]`; the cycle then walks `Foo` and `Foo._model` up to and
    /// including [`MAX_INSTANTIATION_LEVEL`], which is 33 σ each, and the one
    /// edge that would have produced `Foo.{33}` is refused and counted. A cap
    /// that was off by one, or that dropped the pair without counting it, moves
    /// one of these three numbers.
    #[test]
    fn a_model_edge_that_closes_an_increasing_cycle_is_bounded() {
        let (stats, s) = schedule("model_edge_cycle");
        let all: Vec<Inst> = (0..=MAX_INSTANTIATION_LEVEL).map(|n| vec![n]).collect();
        assert_eq!(s.get("Foo"), Some(&all), "Foo is not scheduled up to the cap and no further");
        assert_eq!(s.get("Foo._model"), Some(&all));
        assert_eq!(stats.model_edges, 1);
        assert_eq!(stats.level_cap_drops, 1, "the refusal must be counted, not silent");
        assert_eq!(stats.pairs, 2 * (MAX_INSTANTIATION_LEVEL as usize + 1));
    }
}
