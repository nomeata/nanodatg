//! `mini <export.ndjson>` — one file, one verdict, in the row format the
//! corpus tables scrape.
//!
//! # The two axes are both in the verdict
//!
//! MINI-DESIGN.md §0 has an *acceptance* axis, which must agree with
//! `Main.lean` and with nanoda, and a *certification* axis — did every
//! obligation get a real theorem. A run that accepted a file while leaving
//! obligations underived is **not** the same event as one that did not, and for
//! a tool whose claim is that every definitional-equality conclusion carries a
//! certificate, silently exiting 0 on the first is the wrong default. So the
//! verdict line grows columns and there is an exit code for it.
//!
//! **The certification axis has two halves, and they are two columns.**
//! `uncertified:` is [`mini::ledger::Uncertified`] — obligations the ledger
//! opened and did not discharge. `untranslated:` is
//! [`mini::ledger::Untranslated`] — declarations, constructors and eliminators
//! mini recorded a refusal to translate. The second exists because the first is
//! closed under new gap kinds only *along a pair's path*, and an inductive
//! schedules no pair: `113_reduceCtorParamRefl` printed
//! `accept 3 declarations` and exited 0 while carrying an untranslated
//! inductive. Both columns share exit `4`.
//!
//! # Exit status
//!
//! | code | meaning | axis |
//! |------|---------|------|
//! | `0` | accepted, everything translated, every obligation certified | both |
//! | `1` | rejected — the file is ill-typed | acceptance |
//! | `2` | **arena decline** — a feature mini does not support; also a usage error | acceptance |
//! | `3` | blocked — `--block` only, see below | neither |
//! | `4` | accepted, and something is uncertified **or untranslated** | certification |
//!
//! **A third column, and it is deliberately not an exit code.**
//! `ignored axioms:` names the non-standard axioms the file declares that
//! *nothing in it refers to* — see [`mini::unused_axiom`]. They are on the line
//! because a declaration with no scheduled pair is otherwise invisible, and off
//! the exit code because they are not debt: nothing rests on them, so there is
//! no claim to be short of.
//!
//! `0`–`2` are `Main.lean`'s and mean exactly what they do there, and `2`'s
//! population is the arena's contract — two corpus exports declaring a
//! non-standard axiom **their own declarations use**, plus mutual inductives at
//! the parser. **A declaration
//! mini could not translate does not go there**; it is a `4`, because the file
//! was genuinely accepted and what is untrue is only the claim that all of it
//! was translated.
//!
//! `3` and `4` are not verdicts *about the file*: a blocked run and an
//! uncertified one both **accepted** it, and `scripts/mini-vs-nanoda.sh` —
//! which compares acceptance and nothing else — passes `--acceptance-only` to
//! say so at the call site.
//!
//! `--block` is the *development* affordance: it stops the interpretation pass
//! at the first `(declaration, σ)` whose obligation mini cannot discharge and
//! prints the report, so one thing can be fixed and re-measured. It is opt-in
//! and keeps exit `3`, and it takes precedence over `4` because a blocked run's
//! counters are partial by design. The default runs to the end and reports the
//! whole picture.
//!
//! `--acceptance-only` restores the pre-certification exit behaviour: `0`/`1`/
//! `2`, and `3` as well if `--block` was also asked for, since that one is
//! explicitly requested. The certification columns are still printed — the flag
//! governs the exit code, not what is on screen.

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, paths): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| a.starts_with("--"));
    let verbose = flags.iter().any(|f| f == "--verbose");
    let block = flags.iter().any(|f| f == "--block");
    // **The mutual gate.** `mini/src/convert.rs`'s `LoadOptions` carries the
    // argument for why this is a flag and not the default; in one line, the
    // exit-2 population is the arena's contract and shrinking it is a change to
    // make on purpose.
    let mutual = flags.iter().any(|f| f == "--mutual");
    // **The nested gate**, and it is a *second* switch rather than the same
    // one: `--mutual` opens a block whose recursor rules the kernel derives,
    // and `--nested` opens a declaration whose `T.rec_1` carries an ι rule on
    // another type's constructors that no acceptance-side check justifies.
    // `mini/src/nested.rs`'s header says which is which.
    let nested = flags.iter().any(|f| f == "--nested");
    // Named for the call site: a run that only cares whether the file was
    // accepted says so, and gets `Main.lean`'s three codes and no fourth.
    let acceptance_only = flags.iter().any(|f| f == "--acceptance-only");
    // `--dump-only`/`--dump-sigma` imply `--dump-theorems`: asking for one
    // declaration's theorems and getting nothing would be a papercut.
    let val = |k: &str| {
        flags.iter().find_map(|f| f.strip_prefix(k).and_then(|r| r.strip_prefix('=')))
    };
    // **The `modelgen` pass is on unless it is turned off** — `mini::modelgen`
    // says why the default is that way round and what the two flags do. A
    // binary that cannot be found is a usage error (exit 2) and not a run with
    // no filter; the module header says why a silent skip would be a
    // misattribution rather than a convenience.
    let modelgen = if flags.iter().any(|f| f == mini::modelgen::NO_FLAG) {
        mini::modelgen::Filter::Off
    } else {
        match mini::modelgen::discover(val(mini::modelgen::PATH_FLAG)) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(2);
            }
        }
    };
    // **The routing flag** (ENV-UNIFY.md §5 track D, `mini::route`):
    // `--route=split` is the owner's split — inductive constructions to mini,
    // defs and theorems to the checker, both over one kernel `Env`;
    // `--route=mini` / `--route=checker` force one engine for everything, so
    // the historical single-engine runs stay reachable and comparable. No
    // flag is the historical mini-only run, untouched.
    let route = match val("--route") {
        None => None,
        Some("split") => Some(mini::route::Mode::Split),
        Some("mini") => Some(mini::route::Mode::ForceMini),
        Some("checker") => Some(mini::route::Mode::ForceChecker),
        Some(other) => {
            eprintln!("--route={other}: expected split, mini or checker");
            std::process::exit(2);
        }
    };
    let only = val("--dump-only").map(str::to_string);
    let sigma = val("--dump-sigma").map(|s| {
        s.split(',').filter(|p| !p.is_empty()).filter_map(|p| p.parse().ok()).collect::<Vec<u32>>()
    });
    let dump = (flags.iter().any(|f| f == "--dump-theorems") || only.is_some() || sigma.is_some())
        .then_some(mini::dump::Filter { decl: only, sigma });
    if paths.len() != 1 {
        eprintln!(
            "usage: mini [--verbose] [--block] [--acceptance-only] [--mutual] [--nested] \
             [--no-modelgen] [--modelgen=<path>] [--route=split|mini|checker] \
             [--dump-theorems] [--dump-only=<decl>] [--dump-sigma=<n,m>] <export.ndjson>"
        );
        std::process::exit(2);
    }
    let path = PathBuf::from(&paths[0]);
    let out = mini::run::check_file_deep_with(
        &path,
        mini::run::Options { block, dump, mutual, nested, modelgen, route },
    );
    let stem = path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    // The certification axis, both halves, computed once: they decide the
    // verdict line's certification columns *and* the exit code, and the two
    // must not be able to disagree.
    let unc = out.uncertified();
    let notrans = out.untranslated();
    match &out.verdict {
        mini::run::Verdict::Accepted { declars } => {
            // A clean run's verdict reads exactly as it always has — a column
            // appears only when there is something to say. `untranslated:`
            // first, because it is the wider statement: it says a piece of the
            // file has no image at all, where `uncertified:` says an image
            // exists and a theorem about it does not.
            // `ignored axioms:` last, and it is the only one of the three that
            // is not debt: it says the file declares a symbol no evidence
            // exists for and that **nothing in the file rests on it**. It is
            // on the line for `#64`'s reason — a declaration with no scheduled
            // pair is otherwise invisible — and off the exit code for the
            // reason `mini::ledger::Ledger::ignored_axioms` gives.
            let ignored = out.ledger.as_ref().and_then(mini::ledger::Ledger::ignored_column);
            let cols: String = [notrans.column(), unc.column(), ignored]
                .into_iter()
                .flatten()
                .map(|c| format!("\t{c}"))
                .collect();
            println!("{stem}\taccept\t{declars} declarations{cols}");
        }
        mini::run::Verdict::Rejected { name, msg } => {
            println!("{stem}\treject\t{name}");
            println!("{msg}");
        }
        mini::run::Verdict::Declined { reason } => {
            println!("{stem}\tdecline\t{reason}");
        }
    }
    if verbose {
        // Machine-readable, one key=value per tab, for `mini/tests/tutorial.rs`.
        let f = &out.facts;
        println!(
            "facts\tdeclars={}\tnatLits={}\tmaxNatLit={}\tstrLits={}\tscheduledPairs={}\trecMismatches={}\tmutualBlocks={}\tmutualEncoded={}\tmutualRules={}",
            f.declars,
            f.nat_lits,
            f.max_nat_lit,
            f.str_lits,
            f.scheduled_pairs,
            f.recursor_shape_mismatches.len(),
            f.mutual_blocks,
            f.mutual_encoded,
            f.mutual_rules
        );
        for m in &f.recursor_shape_mismatches {
            println!("recursor-shape\t{m}");
        }
        // The §6.2 clause census: what the remaining threading work is made of.
        let (done, todo) = out.census.split();
        print!("clauses\tinterpreted={done}\tremaining={todo}");
        for (k, v) in &out.census.counts {
            print!("\t{}={v}", k.name());
        }
        println!();
        for row in &out.elim_audit {
            println!("{row}");
        }
        if let Some(l) = &out.ledger {
            println!("{}", l.row());
            println!("{}", l.evidence_row());
            println!("{}", l.untranslated.row());
            println!("{}", l.conv_row());
            println!("{}", l.frame_row());
        }
    }
    // The routed run's own rows, printed whenever `--route` asked for one:
    // the routing ledger, the shared store's crossing report, and (verbose)
    // the checker's global evidence report.
    if let Some(r) = &out.route {
        println!("{}", r.row());
        println!("{}", r.cross);
        if verbose {
            println!("{}", r.tg);
        }
    }
    // Before the blocker, which exits: a blocked run has a store too, and its
    // contents are exactly what a reader wants when asking why it blocked.
    if let Some(d) = &out.dump {
        print!("{d}");
    }
    if let Some(b) = out.blocker() {
        print!("{b}");
        std::process::exit(3);
    }
    std::process::exit(match out.verdict {
        // 4 is not a verdict about the file — the file was accepted — which is
        // why it does not reuse 1 or 2. In particular an *untranslated*
        // declaration must not become an arena decline: `2` is the arena's
        // contract for an unsupported feature at file level, and a file with
        // one untranslated inductive is still a file mini accepted.
        // `--acceptance-only` opts out of `4` and only `4`.
        mini::run::Verdict::Accepted { .. }
            if !(unc.is_clean() && notrans.is_clean()) && !acceptance_only =>
        {
            4
        }
        mini::run::Verdict::Accepted { .. } => 0,
        mini::run::Verdict::Rejected { .. } => 1,
        mini::run::Verdict::Declined { .. } => 2,
    });
}
