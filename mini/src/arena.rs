//! The arena mini's expressions live in: one `checker` [`TcCtx`] per thread.
//!
//! # Interface
//!
//! [`install`] parses an export file and puts the resulting [`ExportFile`] and
//! a fresh [`LeanDag`] behind a thread-local [`TcCtx`]. Everything mini builds
//! after that is an `ExprPtr`/`NamePtr`/`LevelPtr` into it, reached through
//! this module's accessors and constructors — which take and return owned
//! values, never a borrow of the context, for the reason the private `read`
//! gives. This is the seam PIVOT.md §1.1 calls for: one term representation
//! shared with `checker/`, so that the inductive arc can be re-targeted
//! against `TcCtx` accessors rather than bridged at runtime.
//!
//! It is deliberately the *only* module in `mini/` that names `TcCtx`. Steps
//! 2–4 of the migration (`Name`, `Level`, `Expr`) add accessors here and
//! change call sites elsewhere; nothing outside touches the context.
//!
//! **Performance is not the motivation.** The corpus payoff was measured at
//! ~1.5% (the certified run is 45.6% `malloc`/`free` and 35.9%
//! `kernel::term`, and *all* hashing is 1.45%); `PROFILE.md`'s 34% figure is
//! the acceptance-only tower path, not this one. The reason to share a
//! representation is reconciliation, and the instruction count is a
//! regression check rather than a goal.
//!
//! # Three things that are load-bearing, not incidental
//!
//! **1. The lifetime is phantom, so it does not thread.** `ExprPtr<'a>` is
//! `Ptr { raw: u32, ph: PhantomData }` (`checker/src/util.rs`) — a 32-bit
//! index, bit 31 tagging export-dag against `TcCtx`-dag. Nothing borrows
//! anything, so `'static` is free and no signature in `mini/` grows a
//! lifetime parameter. What *is* invasive is that a pointer cannot be read
//! or built without the context, and mini has 772 functions of which ~140
//! see a `Checker` — hence a thread-local rather than an explicit parameter.
//!
//! **2. Binder metadata is pinned to anonymous, and that is a correctness
//! requirement.** `mk_lambda`/`mk_pi`/`mk_let` hash over `binder_name`,
//! `binder_style` and `nondep`, and `alloc_expr` deduplicates on the whole
//! node — so pointer identity is structural identity *including the binder
//! name*. `mini/src/expr.rs`'s header argues that mini drops binder names
//! deliberately and that doing so "cannot change a verdict". If mini kept
//! them, a *generated* `∀ _ : A, B` and a *parsed* `∀ x : A, B` would be
//! different pointers for one expression, and mini's whole-expression
//! comparisons — `acc.rs`, `quot_classes.rs` (seven), `rec_dep.rs`,
//! `zoneb.rs`, `nested_splice.rs` — mix the two sources. So [`pi`], [`lam`]
//! and [`let_`] pin the metadata, and [`erase_binders`] puts every *parsed*
//! expression into the same normal form on the way in. The two must agree,
//! which is what `a_named_binder_and_an_anonymous_one_are_one_pointer` pins.
//!
//! **3. Installing leaks, and the leak is bounded by hash-consing.** A
//! `TcCtx` borrows its `LeanDag` mutably for its whole life, so the two
//! cannot be stored together without a self-reference; [`install`] therefore
//! leaks both. What accumulates is one *deduplicated* dag per installation,
//! and `PROFILE.md` §4 measured 411,015,702 `Expr` constructions against
//! 9,561 distinct expressions on one tower — so the dag holds the 9,561.
//! Mini already allocated the 411 M as `Rc`s; the arena holds four orders of
//! magnitude less.
//!
//! # The rule callers must keep
//!
//! **A pointer must not outlive its installation.** Today nothing carrying an
//! expression escapes `run::check_file_with`: the `Outcome` crosses a thread
//! join, and `Rc<Expr>` is not `Send`, so the compiler enforced it.
//! `ExprPtr` *is* `Send`, so that enforcement is gone and the rule is now a
//! convention. `run::check_file_deep_with` spawns one thread per file, which
//! makes the installation per-file on the path `mini` itself uses.

use nanoda_lib::expr::{BinderStyle, Expr};
use nanoda_lib::level::Level as CLevel;
use nanoda_lib::name::Name as CName;
use nanoda_lib::util::{
    BigUintPtr, Config, ExportFile, ExprPtr, LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
    TcCtx,
};
use std::cell::RefCell;
use std::collections::HashMap;

/// The binder style every expression mini builds carries. See the header:
/// it is in the hash-cons key, so it has to be one value and not a choice.
pub const STYLE: BinderStyle = BinderStyle::Default;

thread_local! {
    static CTX: RefCell<Option<TcCtx<'static, 'static>>> = const { RefCell::new(None) };
}

/// Parse `cfg`'s export file and install it as this thread's arena, replacing
/// any previous installation.
///
/// Returns the leaked [`ExportFile`], because callers need its `declars` and
/// `notations` and the pre-pass needs it too. See the header on why the leak
/// is bounded.
pub fn install(cfg: Config) -> Result<&'static ExportFile<'static>, Box<dyn std::error::Error>> {
    let (ef, _skipped) = cfg.to_export_file()?;
    Ok(install_export_file(ef))
}

/// [`install`], for an [`ExportFile`] already parsed — the `modelgen` path,
/// which parses from a byte buffer rather than from the path in the config.
pub fn install_export_file(ef: ExportFile<'static>) -> &'static ExportFile<'static> {
    let ef: &'static ExportFile<'static> = Box::leak(Box::new(ef));
    let dag: &'static mut LeanDag<'static> = Box::leak(Box::new(LeanDag::new(&ef.config)));
    CTX.with(|c| *c.borrow_mut() = Some(TcCtx::new(ef, dag)));
    ef
}

/// Whether this thread has an arena. False before [`install`], and the reason
/// every accessor below can `expect` rather than return an option.
pub fn is_installed() -> bool { CTX.with(|c| c.borrow().is_some()) }

/// Read through the arena. **Private, and that is the whole safety argument.**
///
/// A `RefCell` borrow that spans caller code is a re-entrancy trap: a `write`
/// nested inside a `read` — or inside another `write` — panics with "already
/// borrowed", and the nesting is easy to write by accident, because arguments
/// to a method called *inside* the closure are evaluated inside it too.
/// `arena::pi(t, arena::bvar(0))` is fine; `write(|c| c.mk_pi(n, S, t,
/// bvar(0)))` is not, and the two read almost the same. The first draft of
/// this module exposed both closures and three of its own tests hit it.
///
/// So no borrow ever spans code outside this module. Every public accessor
/// takes and returns owned values — `Expr<'static>` is `Copy`, so reading one
/// out ends the borrow — and every public constructor takes its arguments
/// already built.
fn read<R>(f: impl FnOnce(&TcCtx<'static, 'static>) -> R) -> R {
    ensure_installed();
    CTX.with(|c| f(c.borrow().as_ref().expect("mini::arena: no export file installed")))
}

/// Allocate through the arena. Private, for the reason [`read`] gives.
fn write<R>(f: impl FnOnce(&mut TcCtx<'static, 'static>) -> R) -> R {
    ensure_installed();
    CTX.with(|c| f(c.borrow_mut().as_mut().expect("mini::arena: no export file installed")))
}

/// **Under `cargo test` only, an absent arena becomes an empty one.**
///
/// Mini's unit tests build declarations by hand — `Name::simple("Nat")`,
/// `konst(…)`, a whole inductive — and none of them has an export file. Before
/// the migration those constructors were `Rc::new`; now they need a context,
/// and requiring 168 tests to install one would be boilerplate proportional to
/// the suite rather than to the change.
///
/// It is safe precisely because it is empty: an auto-installed arena has no
/// declarations, so nothing can *silently find* a name or expression it should
/// have had to parse for — a test that depended on export content would fail,
/// not pass. In a non-test build `cfg!(test)` is `false` and this is dead
/// code, so production still panics on a missing [`install`]. Integration
/// tests go through `run::check_file`, which installs the real thing.
fn ensure_installed() {
    if cfg!(test) && !CTX.with(|c| c.borrow().is_some()) {
        install_empty_arena();
    }
}

/// An arena over a zero-byte export file. `parse_export_file` reads lines
/// until EOF, so an empty input is a valid empty environment.
///
/// `pub` because `mini`'s *integration* tests need it too, for the same reason
/// [`ensure_installed`] gives — and there `cfg!(test)` is false, since they
/// link `mini` as a library.
pub fn install_empty_arena() {
    let cfg: Config = serde_json::from_str(
        r#"{"export_file_path": null,
            "unpermitted_axiom_hard_error": false,
            "unsafe_permit_all_axioms": true,
            "nat_extension": true,
            "string_extension": true,
            "print_axioms": false,
            "print_success_message": false}"#,
    )
    .expect("mini::arena: the empty-arena config does not deserialise");
    let (ef, _) = cfg
        .to_export_file_from(std::io::Cursor::new(Vec::new()))
        .expect("mini::arena: the empty export file does not parse");
    install_export_file(ef);
}

// ────────────────────────────────────────────────────────── accessors ──

/// The node `e` points at. `Expr<'static>` is `Copy`, so this ends the borrow
/// before the caller looks at it — see [`read`].
pub fn read_expr(e: ExprPtr<'static>) -> Expr<'static> { read(|c| c.read_expr(e)) }

/// The node `n` points at. `Name<'static>` is `Copy`; same argument.
pub fn read_name(n: NamePtr<'static>) -> CName<'static> { read(|c| c.read_name(n)) }

/// A component string, copied out. The arena hands back a `&CowStr` borrowed
/// from the context, which must not escape the borrow — see [`read`].
pub fn read_string(s: StringPtr<'static>) -> String {
    read(|c| c.read_string(s).as_ref().to_string())
}

/// The level `l` points at.
pub fn read_level(l: LevelPtr<'static>) -> CLevel<'static> { read(|c| c.read_level(l)) }

/// A universe-parameter list, as an owned vector. The arena stores it as an
/// `Arc<[LevelPtr]>`; cloning the `Arc` would still be a value that outlives
/// the borrow, so this copies the (always short) slice.
pub fn read_levels(ls: LevelsPtr<'static>) -> Vec<LevelPtr<'static>> {
    read(|c| c.read_levels(ls).to_vec())
}

/// A nat literal's value **in decimal**, copied out.
///
/// A string rather than the `BigUint` the arena holds, because mini has no
/// `num-bigint` dependency and wants none: its own literals are `u64` and the
/// parser declines anything above ten, so a value that does not fit is
/// declined regardless of how it is spelled. `None` when the export file was
/// parsed without the nat extension, which mini never does.
pub fn read_nat_lit_decimal(n: BigUintPtr<'static>) -> Option<String> {
    read(|c| c.read_bignum(n).map(|b| b.to_string()))
}

// ─────────────────────────────────────────────────── name constructors ──

/// `Name.anonymous`.
pub fn name_anon() -> NamePtr<'static> { read(|c| c.anonymous()) }

/// `Name.str`. Needs `TcCtx::alloc_string`, which this migration made `pub` —
/// see the citation at its definition.
pub fn name_str(pre: NamePtr<'static>, s: &str) -> NamePtr<'static> {
    let owned = s.to_string();
    write(|c| {
        let sfx = c.alloc_string(std::borrow::Cow::Owned(owned));
        c.str(pre, sfx)
    })
}

/// `Name.num`.
pub fn name_num(pre: NamePtr<'static>, i: u64) -> NamePtr<'static> { write(|c| c.num(pre, i)) }

// ──────────────────────────────────────────────── pinned constructors ──

/// The anonymous name — every binder mini builds is bound to it.
pub fn anon() -> NamePtr<'static> { read(|c| c.anonymous()) }

/// `Expr.app`.
pub fn app(f: ExprPtr<'static>, a: ExprPtr<'static>) -> ExprPtr<'static> {
    write(|c| c.mk_app(f, a))
}

/// `Expr.bvar`, with the width check.
///
/// Mini's de Bruijn indices are `u32` and `checker`'s are `u16`. Measured
/// over every `good/**` and `bad/**` export outside `perf/`, the largest
/// index mini ever constructs is **38**, so the narrowing is safe by three
/// orders of magnitude — but it is a narrowing, and a silent wrap would be a
/// wrong expression rather than a crash. One choke point, one loud failure.
pub fn bvar(i: u32) -> ExprPtr<'static> {
    let i = u16::try_from(i)
        .unwrap_or_else(|_| panic!("de Bruijn index {i} exceeds checker's u16 dbj_idx"));
    write(|c| c.mk_var(i))
}

/// `Expr.lam`, with the binder metadata pinned. See the header, point 2.
pub fn lam(ty: ExprPtr<'static>, body: ExprPtr<'static>) -> ExprPtr<'static> {
    let n = anon();
    write(|c| c.mk_lambda(n, STYLE, ty, body))
}

/// `Expr.forallE`, with the binder metadata pinned.
pub fn pi(ty: ExprPtr<'static>, body: ExprPtr<'static>) -> ExprPtr<'static> {
    let n = anon();
    write(|c| c.mk_pi(n, STYLE, ty, body))
}

/// `Expr.letE`, with the binder name and `nondep` pinned.
///
/// `nondep` is in the hash-cons key too, and mini has no source for it: it is
/// a hint the exporter emits and mini's `Let` carries no such field. `false`
/// is the conservative value — it is what `checker`'s own `mk_let` is given
/// for a `let` whose body does use the bound variable — and, being constant,
/// it cannot split one expression into two pointers.
pub fn let_(
    ty: ExprPtr<'static>,
    val: ExprPtr<'static>,
    body: ExprPtr<'static>,
) -> ExprPtr<'static> {
    let n = anon();
    write(|c| c.mk_let(n, ty, val, body, false))
}

// ─────────────────────────────────────────────────────── the normaliser ──

/// **Every binder in `e` rebound to the anonymous name and the default
/// style, and every `let` marked `nondep: false`.**
///
/// This is the load-time half of the pinning rule: expressions mini *builds*
/// go through [`lam`]/[`pi`]/[`let_`], and expressions mini *reads from the
/// export* go through here, so that the two agree pointer-for-pointer. It is
/// the direct replacement for the binder-dropping that `mini/src/convert.rs`'s
/// `Cv::expr` used to do implicitly by converting into a representation with
/// nowhere to put a name.
///
/// A DAG walk, memoised on the incoming pointer: the export's expressions are
/// hash-consed, so a tree walk would revisit shared subterms.
///
/// `Local` is returned unchanged. Mini declines any export containing one
/// (`convert.rs`), so this is unreachable in practice, and erasing a free
/// variable's binder name would change `FVarId` identity — a thing this
/// function has no business doing.
pub fn erase_binders(e: ExprPtr<'static>) -> ExprPtr<'static> {
    let mut memo = HashMap::new();
    // One borrow for the whole walk: `erase_go` never re-enters the cell.
    write(|c| erase_go(c, e, &mut memo))
}

fn erase_go(
    c: &mut TcCtx<'static, 'static>,
    e: ExprPtr<'static>,
    memo: &mut HashMap<ExprPtr<'static>, ExprPtr<'static>>,
) -> ExprPtr<'static> {
    if let Some(hit) = memo.get(&e) {
        return *hit
    }
    let anon = c.anonymous();
    let node = c.read_expr(e);
    let out = match node {
        // No subexpressions and no binder: already in normal form.
        Expr::Var { .. }
        | Expr::Sort { .. }
        | Expr::Const { .. }
        | Expr::NatLit { .. }
        | Expr::StringLit { .. }
        | Expr::Local { .. } => e,
        Expr::App { fun, arg, .. } => {
            let (fun, arg) = (erase_go(c, fun, memo), erase_go(c, arg, memo));
            c.mk_app(fun, arg)
        }
        Expr::Pi { binder_type, body, .. } => {
            let (t, b) = (erase_go(c, binder_type, memo), erase_go(c, body, memo));
            c.mk_pi(anon, STYLE, t, b)
        }
        Expr::Lambda { binder_type, body, .. } => {
            let (t, b) = (erase_go(c, binder_type, memo), erase_go(c, body, memo));
            c.mk_lambda(anon, STYLE, t, b)
        }
        Expr::Let { binder_type, val, body, .. } => {
            let t = erase_go(c, binder_type, memo);
            let v = erase_go(c, val, memo);
            let b = erase_go(c, body, memo);
            c.mk_let(anon, t, v, b, false)
        }
        Expr::Proj { ty_name, idx, structure, .. } => {
            let s = erase_go(c, structure, memo);
            c.mk_proj(ty_name, idx, s)
        }
    };
    memo.insert(e, out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh empty arena for each test. `ensure_installed` would supply one
    /// lazily, but these tests are *about* the arena, so they say so.
    fn install_empty() { install_empty_arena(); }

    /// **Pointer identity is structural identity.** The property everything
    /// else here rests on: `alloc_expr` checks the export dag and then a
    /// `UniqueIndexSet`, so two separately built copies of one expression are
    /// one pointer. If this ever failed, mini's `==` on expressions would
    /// silently become "was built by the same code path".
    /// `Sort 0`, built through the arena. The tests build every expression by
    /// hand, so they need the two leaves the empty export file already has.
    fn sort0() -> ExprPtr<'static> {
        let zero = read(|c| c.zero());
        write(|c| c.mk_sort(zero))
    }

    /// A one-component name, for the binders these tests want spelled.
    fn name(s: &str) -> NamePtr<'static> {
        let owned = s.to_string();
        write(|c| c.str1_owned(owned))
    }

    #[test]
    fn two_builds_of_one_expression_are_one_pointer() {
        install_empty();
        let (s, i) = (sort0(), bvar(0));
        let a = pi(s, i);
        let (s2, i2) = (sort0(), bvar(0));
        let b = pi(s2, i2);
        assert_eq!(a, b, "two builds of `∀ _ : Sort 0, #0` are not one pointer");
    }

    /// **The hazard, pinned.** A binder built with a real name and the same
    /// binder erased must be one pointer — this is the test that fails if
    /// [`erase_binders`] stops being applied, or if [`pi`] stops pinning.
    ///
    /// Two names, not one: with a single name the test passes under a bug
    /// that erases nothing but happens to compare a node with itself.
    #[test]
    fn a_named_binder_and_an_anonymous_one_are_one_pointer() {
        install_empty();
        let (s, i) = (sort0(), bvar(0));
        let (x, y) = (name("x"), name("y"));
        let named_x = write(|c| c.mk_pi(x, BinderStyle::Implicit, s, i));
        let named_y = write(|c| c.mk_pi(y, BinderStyle::StrictImplicit, s, i));
        assert_ne!(named_x, named_y, "the binder name is not in the hash-cons key after all");
        assert_eq!(
            erase_binders(named_x),
            erase_binders(named_y),
            "two spellings of `∀ _ : Sort 0, #0` survive erasure as two pointers"
        );
        assert_eq!(
            erase_binders(named_x),
            pi(s, i),
            "an erased parsed binder is not the binder mini builds"
        );
    }

    /// Erasure reaches under an application and a `let`, not just the top
    /// node. Three binders at three depths, because a walk that erases only
    /// the outermost passes a one-binder test.
    #[test]
    fn erasure_reaches_every_depth() {
        install_empty();
        let (s, i) = (sort0(), bvar(0));
        let x = name("x");
        let deep = {
            let inner = write(|c| c.mk_lambda(x, BinderStyle::InstanceImplicit, s, i));
            let l = write(|c| c.mk_let(x, s, inner, i, true));
            let outer = write(|c| c.mk_pi(x, BinderStyle::Implicit, s, l));
            app(outer, inner)
        };
        let want = {
            let inner = lam(s, i);
            let l = let_(s, inner, i);
            let outer = pi(s, l);
            app(outer, inner)
        };
        assert_eq!(erase_binders(deep), want, "erasure did not reach every binder");
    }

    /// `nondep` is in the key, and erasure normalises it. Without this the
    /// two `let`s below stay two pointers and every parsed `nondep: true`
    /// `let` is a stranger to the one mini rebuilds.
    #[test]
    fn nondep_is_normalised() {
        install_empty();
        let (s, i) = (sort0(), bvar(0));
        let n = anon();
        let t = write(|c| c.mk_let(n, s, s, i, true));
        let f = write(|c| c.mk_let(n, s, s, i, false));
        assert_ne!(t, f, "`nondep` is not in the hash-cons key after all");
        assert_eq!(erase_binders(t), f, "erasure left `nondep` alone");
    }

    /// The `u16` narrowing fails loudly rather than wrapping. 65,536 would
    /// wrap to 0 — a *different expression*, silently accepted.
    #[test]
    #[should_panic(expected = "exceeds checker's u16")]
    fn a_de_bruijn_index_above_u16_panics() {
        install_empty();
        let _ = bvar(65_536);
    }

    /// …and the largest index that does fit is built, not refused.
    #[test]
    fn the_largest_representable_index_is_fine() {
        install_empty();
        let e = bvar(65_535);
        assert!(matches!(read_expr(e), Expr::Var { dbj_idx: 65_535, .. }));
    }
}
