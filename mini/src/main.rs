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
//! verdict line grows a fourth column and there is an exit code for it.
//!
//! # Exit status
//!
//! | code | meaning | axis |
//! |------|---------|------|
//! | `0` | accepted, and every obligation certified | both |
//! | `1` | rejected — the file is ill-typed | acceptance |
//! | `2` | declined — mini refuses to look; also a usage error | acceptance |
//! | `3` | blocked — `--block` only, see below | neither |
//! | `4` | accepted, and something is uncertified | certification |
//!
//! `0`–`2` are `Main.lean`'s and mean exactly what they do there. `3` and `4`
//! are not verdicts *about the file*: a blocked run and an uncertified one both
//! **accepted** it, and `scripts/mini-vs-nanoda.sh` — which compares acceptance
//! and nothing else — passes `--acceptance-only` to say so at the call site.
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
//! explicitly requested. The fourth column is still printed — the flag governs
//! the exit code, not what is on screen.

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, paths): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| a.starts_with("--"));
    let verbose = flags.iter().any(|f| f == "--verbose");
    let block = flags.iter().any(|f| f == "--block");
    // Named for the call site: a run that only cares whether the file was
    // accepted says so, and gets `Main.lean`'s three codes and no fourth.
    let acceptance_only = flags.iter().any(|f| f == "--acceptance-only");
    // `--dump-only`/`--dump-sigma` imply `--dump-theorems`: asking for one
    // declaration's theorems and getting nothing would be a papercut.
    let val = |k: &str| {
        flags.iter().find_map(|f| f.strip_prefix(k).and_then(|r| r.strip_prefix('=')))
    };
    let only = val("--dump-only").map(str::to_string);
    let sigma = val("--dump-sigma").map(|s| {
        s.split(',').filter(|p| !p.is_empty()).filter_map(|p| p.parse().ok()).collect::<Vec<u32>>()
    });
    let dump = (flags.iter().any(|f| f == "--dump-theorems") || only.is_some() || sigma.is_some())
        .then_some(mini::dump::Filter { decl: only, sigma });
    if paths.len() != 1 {
        eprintln!(
            "usage: mini [--verbose] [--block] [--acceptance-only] [--dump-theorems] \
             [--dump-only=<decl>] [--dump-sigma=<n,m>] <export.ndjson>"
        );
        std::process::exit(2);
    }
    let path = PathBuf::from(&paths[0]);
    let out = mini::run::check_file_deep_with(&path, mini::run::Options { block, dump });
    let stem = path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    // The certification axis, computed once: it decides both the verdict line's
    // fourth column and the exit code, and the two must not be able to disagree.
    let unc = out.uncertified();
    match &out.verdict {
        mini::run::Verdict::Accepted { declars } => {
            // A clean run's verdict reads exactly as it always has — the column
            // appears only when there is something to say.
            match unc.column() {
                Some(c) => println!("{stem}\taccept\t{declars} declarations\t{c}"),
                None => println!("{stem}\taccept\t{declars} declarations"),
            }
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
            "facts\tdeclars={}\tnatLits={}\tmaxNatLit={}\tstrLits={}\tscheduledPairs={}\trecMismatches={}",
            f.declars,
            f.nat_lits,
            f.max_nat_lit,
            f.str_lits,
            f.scheduled_pairs,
            f.recursor_shape_mismatches.len()
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
            println!("{}", l.conv_row());
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
        // why it does not reuse 1 or 2. `--acceptance-only` opts out.
        mini::run::Verdict::Accepted { .. } if !unc.is_clean() && !acceptance_only => 4,
        mini::run::Verdict::Accepted { .. } => 0,
        mini::run::Verdict::Rejected { .. } => 1,
        mini::run::Verdict::Declined { .. } => 2,
    });
}
