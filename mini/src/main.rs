//! `mini <export.ndjson>` — one file, one verdict, in the row format the
//! corpus tables scrape.
//!
//! Exit status mirrors `Main.lean`: 0 accepted, 1 rejected, 2 declined.

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, paths): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| a.starts_with("--"));
    let verbose = flags.iter().any(|f| f == "--verbose");
    if paths.len() != 1 {
        eprintln!("usage: mini [--verbose] <export.ndjson>");
        std::process::exit(2);
    }
    let path = PathBuf::from(&paths[0]);
    let out = mini::run::check_file_deep(&path);
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
    }
    std::process::exit(match out.verdict {
        mini::run::Verdict::Accepted { .. } => 0,
        mini::run::Verdict::Rejected { .. } => 1,
        mini::run::Verdict::Declined { .. } => 2,
    });
}
