//! `mini <export.ndjson>` — one file, one verdict, in the row format the
//! corpus tables scrape.
//!
//! Exit status mirrors `Main.lean`: 0 accepted, 1 rejected, 2 declined — plus
//! **3 blocked**, which `Main.lean` has no analogue for because it is not a
//! verdict about the file. `--block` stops the interpretation pass at the first
//! `(declaration, σ)` whose obligation mini cannot discharge and prints the
//! report; the file was still *accepted*, and the acceptance axis is unmoved.

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, paths): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| a.starts_with("--"));
    let verbose = flags.iter().any(|f| f == "--verbose");
    let block = flags.iter().any(|f| f == "--block");
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
            "usage: mini [--verbose] [--block] [--dump-theorems] \
             [--dump-only=<decl>] [--dump-sigma=<n,m>] <export.ndjson>"
        );
        std::process::exit(2);
    }
    let path = PathBuf::from(&paths[0]);
    let out = mini::run::check_file_deep_with(&path, mini::run::Options { block, dump });
    let stem = path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    match &out.verdict {
        mini::run::Verdict::Accepted { declars } => {
            println!("{stem}\taccept\t{declars} declarations");
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
        mini::run::Verdict::Accepted { .. } => 0,
        mini::run::Verdict::Rejected { .. } => 1,
        mini::run::Verdict::Declined { .. } => 2,
    });
}
