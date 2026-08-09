//! **B0 prototype (ENV-UNIFY.md §3.5, task #125): do mini's and the checker's
//! dispatches produce the same skeleton key for the same shape?**
//!
//! The measurement: one kernel `Env`, `fast_forward`ed once, one `x_canon`,
//! one canonical hole-variable series — handed first to mini
//! ([`mini::interp::Interp::over`], the `Nat::over` pattern one level up),
//! then, with the same `Env` carried over, to the checker's per-thread
//! `Shared` ([`nanoda_lib::tg::b0_install_shared`]). Both engines then run
//! over the same export in the same thread (so `derived::prelude::prelude()`
//! hands both the *identical* `Prelude`, ambient symbols included), and the
//! skeleton-site tables are compared key by key.
//!
//! Two notions of agreement, kept apart because ENV-UNIFY §3.5 needs them
//! apart:
//!
//! * **raw** — the keys are equal `Term`s. Possible at all only because the
//!   brand, `x_canon`, the hole series and the prelude symbols are shared;
//!   anything engine-local inside a key (a nested site's head symbol) breaks
//!   it even when the shape agrees.
//! * **canonical** — equal after rewriting each engine's *own* site head
//!   symbols to a token derived from that site's own (recursively
//!   canonicalised) key. This is what "same skeleton normal form" means, and
//!   it is what B5's *shared* site tables would make literal: the first
//!   engine to reach an inner shape would allocate the symbol and the second
//!   would find it by key, so canonical agreement today is raw agreement
//!   under one table.
//!
//! A key canonically present on one side only is a **structural** divergence
//! (the §3.5 gap-at-structure case); a key canonically shared but raw-unequal
//! is **nominal** (site-symbol identity only — exactly what one shared table
//! dissolves). The test prints the numbers and asserts only harness sanity:
//! it is a measurement, not a ratchet.
//!
//! Run: `cargo test -p mini --features b0 --test b0_env_unify -- --nocapture`

#![cfg(feature = "b0")]

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use kernel::{FnSym, FreeVar, Term};

#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests")
}

/// Hole variables pre-minted before either engine runs, so both engines'
/// series agree on every index either is likely to reach. Growth past the pool
/// is handed from mini to the checker, so only *checker-side* growth past what
/// mini saw can diverge — and those indexes mini never used.
const POOL: usize = 64;

/// One engine's site tables: (key, minted symbols head-first) per row.
struct Dump {
    lams: Vec<(Term, Vec<FnSym>)>,
    fibres: Vec<(Term, Vec<FnSym>)>,
    conds: Vec<(Term, Vec<FnSym>)>,
    /// Checker only: the neither-clause `Π` sites mini structurally lacks.
    undet: Vec<(Term, FnSym)>,
}

/// Head symbol -> (table tag, that site's own key). The canonicaliser
/// rewrites through this, each engine through its own map.
fn heads(d: &Dump) -> HashMap<FnSym, (char, Term)> {
    let mut m = HashMap::new();
    for (k, s) in &d.lams {
        m.insert(s[0], ('L', k.clone()));
    }
    for (k, s) in &d.fibres {
        m.insert(s[0], ('P', k.clone()));
    }
    for (k, s) in &d.conds {
        m.insert(s[0], ('C', k.clone()));
    }
    for (k, s) in &d.undet {
        m.insert(*s, ('U', k.clone()));
    }
    m
}

/// The canonical rendering of a skeleton key: `X` for `x_canon`, `Hi` for the
/// `i`-th hole, `tag⟨canon(inner key)⟩` for an engine-own site head,
/// `g{id}.{arity}` for anything else (prelude symbols — literally shared, so
/// they agree; engine-local carriers or `Syms` — not shared, so they do not,
/// which is the correct verdict). A leaf that is none of these counts into
/// `unknown` and renders `?` — zero everywhere is a harness invariant worth
/// printing.
fn canon(
    t: &Term,
    x: FreeVar,
    pool: &[FreeVar],
    hd: &HashMap<FnSym, (char, Term)>,
    fs_swap: Option<FnSym>,
    renumber: Option<&mut Vec<HashMap<usize, usize>>>,
    out: &mut String,
    unknown: &mut usize,
) {
    let mut renumber = renumber;
    if *t == Term::var(x) {
        out.push('X');
        return;
    }
    if let Some(i) = pool.iter().position(|h| *t == Term::var(*h)) {
        out.push('H');
        // Modulo hole *numbering*: rename holes by first occurrence in this
        // skeleton's own rendering. The fs(A,B)→dprod₀(B,A) argument swap
        // permutes the traversal order holes are discovered in, so everything
        // downstream of one bridged arrow gets permuted indices; this pass
        // absorbs exactly that, and the delta against the plain bridge pass
        // *is* the permutation class.
        match renumber {
            Some(ctx) => {
                let m = ctx.last_mut().expect("renumber context");
                let n = m.len();
                let r = *m.entry(i).or_insert(n);
                out.push_str(&r.to_string());
            }
            None => out.push_str(&i.to_string()),
        }
        return;
    }
    match t.as_app() {
        None => {
            out.push('?');
            *unknown += 1;
        }
        Some((f, args)) => {
            // The bridge experiment: render this engine's `fs(A,B)` as the
            // other clause's `dprod₀(B,A)`, to measure whether the
            // fs-vs-dprod₀ arrow clause is the whole of the divergence.
            if Some(f) == fs_swap && args.len() == 2 {
                out.push_str("P<H0>(");
                canon(&args[1], x, pool, hd, fs_swap, renumber.as_deref_mut(), out, unknown);
                out.push(',');
                canon(&args[0], x, pool, hd, fs_swap, renumber.as_deref_mut(), out, unknown);
                out.push_str(",)");
                return;
            }
            if let Some((c, key)) = hd.get(&f).cloned() {
                out.push(c);
                out.push('<');
                // An inner site's key has its own hole numbering — a fresh
                // renumbering frame, not the enclosing skeleton's.
                if let Some(ctx) = renumber.as_deref_mut() {
                    ctx.push(HashMap::new());
                    canon(&key, x, pool, hd, fs_swap, Some(ctx), out, unknown);
                    ctx.pop();
                } else {
                    canon(&key, x, pool, hd, fs_swap, None, out, unknown);
                }
                out.push('>');
            } else {
                out.push('g');
                out.push_str(&f.id().to_string());
                out.push('.');
                out.push_str(&f.arity().to_string());
            }
            out.push('(');
            for a in args {
                canon(a, x, pool, hd, fs_swap, renumber.as_deref_mut(), out, unknown);
                out.push(',');
            }
            out.push(')');
        }
    }
}

fn canon_str(
    t: &Term,
    x: FreeVar,
    pool: &[FreeVar],
    hd: &HashMap<FnSym, (char, Term)>,
    fs_swap: Option<FnSym>,
    renumber: bool,
    unknown: &mut usize,
) -> String {
    let mut s = String::new();
    if renumber {
        let mut ctx = vec![HashMap::new()];
        canon(t, x, pool, hd, fs_swap, Some(&mut ctx), &mut s, unknown);
    } else {
        canon(t, x, pool, hd, fs_swap, None, &mut s, unknown);
    }
    s
}

/// Does `t` mention an engine-local symbol that is not a site head — a
/// constant carrier, an apparatus symbol, a `Syms` encoding? Those are the
/// keys only track B4's shared constant store could ever make agree: the
/// symbol is *in* the key, so key agreement presupposes carrier agreement.
fn mentions_local_non_site(
    t: &Term,
    hd: &HashMap<FnSym, (char, Term)>,
    prelude_syms: u32,
) -> bool {
    match t.as_app() {
        None => false,
        Some((f, args)) => {
            (f.id() >= prelude_syms && !hd.contains_key(&f))
                || args.iter().any(|a| mentions_local_non_site(a, hd, prelude_syms))
        }
    }
}

#[derive(Default)]
struct TableStats {
    mini_n: usize,
    ck_n: usize,
    raw: usize,
    canonical: usize,
    nominal: usize,
    mini_only: Vec<String>,
    ck_only: Vec<String>,
    /// Distinct raw keys collapsing to one canonical string, per engine —
    /// nonzero would mean the canonicalisation is too coarse to trust.
    mini_collisions: usize,
    ck_collisions: usize,
    /// Keys mentioning an engine-local non-site symbol (carrier, apparatus,
    /// `Syms`) — matchable only once constants are shared (track B4).
    mini_carrier_keys: usize,
    ck_carrier_keys: usize,
    /// Of the raw-equal keys, how many name the *same* head symbol on both
    /// sides. Expected 0 with two tables — the forbidden two-carriers state,
    /// measured rather than assumed; one shared table takes it to `raw`.
    raw_same_head: usize,
}

#[allow(clippy::too_many_arguments)]
fn compare_table(
    mini: &[(Term, Vec<FnSym>)],
    ck: &[(Term, Vec<FnSym>)],
    mx: FreeVar,
    mpool: &[FreeVar],
    mhd: &HashMap<FnSym, (char, Term)>,
    cx: FreeVar,
    cpool: &[FreeVar],
    chd: &HashMap<FnSym, (char, Term)>,
    ck_fs_swap: Option<FnSym>,
    renumber: bool,
    prelude_syms: u32,
    unknown: &mut usize,
) -> TableStats {
    let mut st = TableStats { mini_n: mini.len(), ck_n: ck.len(), ..Default::default() };
    st.mini_carrier_keys =
        mini.iter().filter(|(k, _)| mentions_local_non_site(k, mhd, prelude_syms)).count();
    st.ck_carrier_keys =
        ck.iter().filter(|(k, _)| mentions_local_non_site(k, chd, prelude_syms)).count();
    let mini_raw: HashSet<&Term> = mini.iter().map(|(k, _)| k).collect();
    let ck_raw: HashSet<&Term> = ck.iter().map(|(k, _)| k).collect();
    st.raw = mini_raw.intersection(&ck_raw).count();
    let ck_heads: HashMap<&Term, FnSym> = ck.iter().map(|(k, s)| (k, s[0])).collect();
    st.raw_same_head = mini
        .iter()
        .filter(|(k, s)| ck_heads.get(k).is_some_and(|h| *h == s[0]))
        .count();

    let mut mini_canon: HashMap<String, usize> = HashMap::new();
    for (k, _) in mini {
        *mini_canon.entry(canon_str(k, mx, mpool, mhd, None, renumber, unknown)).or_insert(0) += 1;
    }
    let mut ck_canon: HashMap<String, usize> = HashMap::new();
    for (k, _) in ck {
        *ck_canon.entry(canon_str(k, cx, cpool, chd, ck_fs_swap, renumber, unknown)).or_insert(0) += 1;
    }
    st.mini_collisions = mini.len() - mini_canon.len();
    st.ck_collisions = ck.len() - ck_canon.len();
    for c in mini_canon.keys() {
        if ck_canon.contains_key(c) {
            st.canonical += 1;
        } else {
            st.mini_only.push(c.clone());
        }
    }
    for c in ck_canon.keys() {
        if !mini_canon.contains_key(c) {
            st.ck_only.push(c.clone());
        }
    }
    // Raw agreement implies canonical agreement (shared vars, and a raw-equal
    // key contains no engine-own head or it would differ), so this subtraction
    // is the nominal count.
    st.nominal = st.canonical.saturating_sub(st.raw);
    st.mini_only.sort();
    st.ck_only.sort();
    st
}

struct ExportResult {
    name: String,
    mini_accepted: bool,
    verdict: String,
    lam: TableStats,
    fibre: TableStats,
    cond: TableStats,
    /// The same three comparisons with the checker's `fs(A,B)` bridged to
    /// `dprod₀(B,A)` — the divergence-class-1 attribution.
    lam_b: TableStats,
    fibre_b: TableStats,
    cond_b: TableStats,
    /// Bridge plus hole renumbering by first occurrence, both engines — the
    /// permutation cascade the bridge's argument swap induces, absorbed.
    lam_r: TableStats,
    fibre_r: TableStats,
    cond_r: TableStats,
    undet_n: usize,
    /// Checker undet keys that canonically match a mini fibre/cond key —
    /// clause-routing divergence rather than shape divergence.
    undet_cross: usize,
    unknown_leaves: usize,
    mini_consts: usize,
    mini_consts_sealed: usize,
}

fn run_one(export: &Path) -> ExportResult {
    let name = export.file_stem().unwrap().to_string_lossy().to_string();

    // ── the shared substrate: one Env, one x_canon, one hole series ──
    let pre = derived::prelude::prelude();
    eprintln!(
        "  [prelude ids: app=g{}.{} fs=g{}.{} dprod-free rendering: engine site heads L/P/C/U]",
        pre.ap.app.id(),
        pre.ap.app.arity(),
        pre.fs_sym().id(),
        pre.fs_sym().arity()
    );
    let mut env = kernel::Env::new();
    derived::prelude::fast_forward(&mut env, &pre);
    let x_canon = env.fresh_var();
    let pool: Vec<FreeVar> = (0..POOL).map(|_| env.fresh_var()).collect();

    // ── engine 1: mini, over the shared Env ──
    let ip = mini::interp::Interp::over(env, x_canon, pool);
    let (out, ip) = mini::run::check_file_with_interp(export, mini::run::Options::default(), ip);
    let mini_accepted = out.verdict.is_accepted();
    let verdict = format!("{:?}", out.verdict);
    let msites = ip.b0_sites();
    let mconsts = ip.b0_consts();
    let (env, x2, mpool) = ip.b0_into_env();
    assert_eq!(x2, x_canon, "x_canon must survive the mini run unchanged");

    let mdump = Dump {
        lams: msites.lams,
        fibres: msites.fibres,
        conds: msites.conds,
        undet: Vec::new(),
    };

    // ── engine 2: the checker's tg backend, over the same Env ──
    nanoda_lib::tg::b0_install_shared(env, x_canon, mpool.clone());
    let cfg_json = format!(
        r#"{{"export_file_path": {},
             "num_threads": 1,
             "unpermitted_axiom_hard_error": false,
             "unsafe_permit_all_axioms": true,
             "nat_extension": true,
             "string_extension": true,
             "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    let cfg: nanoda_lib::util::Config = serde_json::from_str(&cfg_json).unwrap();
    let (export_file, _skipped) = cfg.to_export_file().expect("checker parse");
    export_file.check_all_declars();
    let (cl, cf, cc, cu) = nanoda_lib::tg::b0_sites().expect("checker Shared exists");
    let (cx, cpool) = nanoda_lib::tg::b0_canon_vars().unwrap();
    assert_eq!(cx, x_canon, "x_canon must be the shared one on the checker side too");
    assert_eq!(&cpool[..mpool.len().min(cpool.len())], &mpool[..mpool.len().min(cpool.len())]);
    let cdump = Dump { lams: cl, fibres: cf, conds: cc, undet: cu };

    // ── the comparison ──
    let mhd = heads(&mdump);
    let chd = heads(&cdump);
    let mut unknown = 0usize;
    let fs = pre.fs_sym();
    let lam = compare_table(
        &mdump.lams, &cdump.lams, x_canon, &mpool, &mhd, cx, &cpool, &chd, None, false, pre.n_syms, &mut unknown,
    );
    let fibre = compare_table(
        &mdump.fibres, &cdump.fibres, x_canon, &mpool, &mhd, cx, &cpool, &chd, None, false, pre.n_syms, &mut unknown,
    );
    let cond = compare_table(
        &mdump.conds, &cdump.conds, x_canon, &mpool, &mhd, cx, &cpool, &chd, None, false, pre.n_syms, &mut unknown,
    );
    let lam_b = compare_table(
        &mdump.lams, &cdump.lams, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), false, pre.n_syms, &mut unknown,
    );
    let fibre_b = compare_table(
        &mdump.fibres, &cdump.fibres, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), false, pre.n_syms, &mut unknown,
    );
    let cond_b = compare_table(
        &mdump.conds, &cdump.conds, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), false, pre.n_syms, &mut unknown,
    );
    let lam_r = compare_table(
        &mdump.lams, &cdump.lams, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), true, pre.n_syms, &mut unknown,
    );
    let fibre_r = compare_table(
        &mdump.fibres, &cdump.fibres, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), true, pre.n_syms, &mut unknown,
    );
    let cond_r = compare_table(
        &mdump.conds, &cdump.conds, x_canon, &mpool, &mhd, cx, &cpool, &chd, Some(fs), true, pre.n_syms, &mut unknown,
    );

    // Clause routing: checker `undet` keys that mini put in a real table.
    let mut mini_all: HashSet<String> = HashSet::new();
    for (k, _) in mdump.fibres.iter().chain(mdump.conds.iter()).chain(mdump.lams.iter()) {
        mini_all.insert(canon_str(k, x_canon, &mpool, &mhd, None, true, &mut unknown));
    }
    let undet_cross = cdump
        .undet
        .iter()
        .filter(|(k, _)| mini_all.contains(&canon_str(k, cx, &cpool, &chd, Some(fs), true, &mut unknown)))
        .count();

    ExportResult {
        name,
        mini_accepted,
        verdict,
        lam,
        fibre,
        cond,
        lam_b,
        fibre_b,
        cond_b,
        lam_r,
        fibre_r,
        cond_r,
        undet_n: cdump.undet.len(),
        undet_cross,
        unknown_leaves: unknown,
        mini_consts: mconsts.len(),
        mini_consts_sealed: mconsts.iter().filter(|(_, _, _, ok, _)| *ok).count(),
    }
}

fn print_result(r: &ExportResult) {
    let row = |tag: &str, s: &TableStats| {
        println!(
            "  {tag:<6} mini {:>4}  ck {:>4}  raw= {:>4}  canonical= {:>4}  nominal= {:>4}  mini-only= {:>3}  ck-only= {:>3}  collisions m/c {}/{}",
            s.mini_n,
            s.ck_n,
            s.raw,
            s.canonical,
            s.nominal,
            s.mini_only.len(),
            s.ck_only.len(),
            s.mini_collisions,
            s.ck_collisions,
        );
        if s.raw > 0 {
            println!("        raw-equal keys whose two site heads are one symbol: {} of {}", s.raw_same_head, s.raw);
        }
        if s.mini_carrier_keys + s.ck_carrier_keys > 0 {
            println!(
                "        keys embedding engine-local non-site symbols: mini {} ck {}",
                s.mini_carrier_keys, s.ck_carrier_keys
            );
        }
        for c in s.mini_only.iter().take(6) {
            println!("        mini-only: {}", trunc(c));
        }
        for c in s.ck_only.iter().take(6) {
            println!("        ck-only:   {}", trunc(c));
        }
    };
    println!(
        "b0 {}  (mini accepted: {}, consts {} / sealed typings {}, unknown leaves {})",
        r.name, r.mini_accepted, r.mini_consts, r.mini_consts_sealed, r.unknown_leaves
    );
    row("lam", &r.lam);
    row("fibre", &r.fibre);
    row("cond", &r.cond);
    println!("  — with the checker's fs(A,B) bridged to dprod₀(B,A):");
    row("lam+b", &r.lam_b);
    row("fib+b", &r.fibre_b);
    row("cnd+b", &r.cond_b);
    println!("  — bridge + hole renumbering by first occurrence (both engines):");
    row("lam+r", &r.lam_r);
    row("fib+r", &r.fibre_r);
    row("cnd+r", &r.cond_r);
    println!("  undet  ck {:>4}  of which canonically in a mini table: {}", r.undet_n, r.undet_cross);
}

fn trunc(s: &str) -> String {
    if s.len() > 160 {
        format!("{}…", &s[..160])
    } else {
        s.to_string()
    }
}

/// The measurement, per export, in a fresh thread each (the checker's
/// `Shared` and the `Prelude` are thread-locals: a fresh thread is a fresh
/// signature, which is what makes exports independent).
fn measure(files: &[&str]) {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return;
    }
    let mut totals: HashMap<&'static str, (usize, usize, usize, usize, usize, usize)> =
        HashMap::new();
    for f in files {
        let p = dir.join(f);
        assert!(p.exists(), "missing corpus file {p:?}");
        let r = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || run_one(&p))
            .unwrap()
            .join()
            .expect("b0 worker panicked");
        if !r.mini_accepted {
            println!("b0 {}  SKIPPED: mini verdict {}", r.name, r.verdict);
            continue;
        }
        print_result(&r);
        for (tag, s) in [
            ("lam", &r.lam),
            ("fibre", &r.fibre),
            ("cond", &r.cond),
            ("lam+b", &r.lam_b),
            ("fib+b", &r.fibre_b),
            ("cnd+b", &r.cond_b),
            ("lam+r", &r.lam_r),
            ("fib+r", &r.fibre_r),
            ("cnd+r", &r.cond_r),
        ] {
            let t = totals.entry(tag).or_default();
            t.0 += s.mini_n;
            t.1 += s.ck_n;
            t.2 += s.raw;
            t.3 += s.canonical;
            t.4 += s.mini_only.len();
            t.5 += s.ck_only.len();
        }
    }
    println!("b0 TOTALS (mini_n, ck_n, raw, canonical, mini-only, ck-only)");
    for tag in ["lam", "fibre", "cond", "lam+b", "fib+b", "cnd+b", "lam+r", "fib+r", "cnd+r"] {
        let t = totals[tag];
        println!("  {tag:<6} {:>5} {:>5} {:>5} {:>5} {:>5} {:>5}", t.0, t.1, t.2, t.3, t.4, t.5);
    }
}

/// The inductive-free fragment: both engines discharge these completely, so
/// every site both dispatches build is on the table.
#[test]
fn b0_inductive_free() {
    measure(&[
        "001_basicDef.ndjson",
        "003_arrowType.ndjson",
        "004_dependentType.ndjson",
        "005_constType.ndjson",
        "006_betaReduction.ndjson",
        "007_betaReduction2.ndjson",
        "026_defEqLambda.ndjson",
        "027_peano1.ndjson",
        "028_peano2.ndjson",
        "029_peano3.ndjson",
        "030_letType.ndjson",
        "031_letTypeDep.ndjson",
        "032_letRed.ndjson",
    ]);
}

/// Inductives: mini routes these through zone B's construction tables, the
/// checker through its general path — the crossing surface the owner's split
/// actually needs.
#[test]
fn b0_inductives() {
    measure(&[
        "033_empty.ndjson",
        "034_boolType.ndjson",
        "036_andType.ndjson",
        "041_natDef.ndjson",
    ]);
}
