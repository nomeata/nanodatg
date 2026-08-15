use nanoda_lib::util::Config;
use std::error::Error;
use std::path::Path;

// ─────────────────────────────────────────────────────────────────────────────
// The allocator, and why it is here rather than anywhere else.
//
// `PERF-REVIEW.md` F1: 47% of `init-prelude`'s cycles were inside glibc malloc.
// The workload is ~1.7 billion small, short-lived, same-sized allocations
// (`Rc<TermData>` boxes and small `Vec<Term>` buffers) freed in near-LIFO order
// against a 369 MB peak — the pattern glibc's free-bin management handles worst
// and a size-class/free-list allocator handles best. Measured on `init-prelude`
// (`--features tg`, same tree, interleaved runs, median of three):
//
//     glibc 2.42          41.92 s
//     jemalloc 5.3.1      33.96 s   (-19%)
//     mimalloc 2.x        30.25 s   (-28%)   ← this one
//
// The review measured tcmalloc best under `LD_PRELOAD` (-30%), but the
// `tcmalloc` crate links a *system* gperftools, which the dev shell does not
// carry, and its `bundled` feature shells out to `autogen.sh`/`autoreconf`.
// mimalloc's crate vendors its C source and needs only the `cc` the shell
// already provides, and it lands on the number tcmalloc's preload promised.
//
// **This is the binary crate, deliberately.** `kernel/` is the trusted base and
// has no dependencies — `ci/check-boundary.sh` rule 2 enforces that. The
// allocator is linked by the *executable*, so the kernel's dependency story is
// untouched: today's glibc malloc is already unaudited foreign code serving
// every `Rc::new` in the kernel, on exactly the same footing. Nothing in the
// soundness argument mentions the allocator, and the corpus verdicts
// (arena 152/0/2, `init-prelude`'s 16341 gaps / 2261 escapes, the tutorial
// reports) are byte-identical with it linked in.
//
// **This is not the only place any more, and it is no longer the one that
// matters.** `src/bin/checker.rs` — the unified checker, which is what every
// integration suite spawns and what the corpus numbers are quoted from — links
// the same allocator, with its own measurement taken on its own binary. Between
// 2026-08-08 and 2026-08-14 it did not, and this paragraph said so; the merge to
// the unified checker left these two lines behind on `nanoda_bin`, so for that
// week the production checker ran on glibc while the older binary got mimalloc.
// Read `src/bin/checker.rs` for the numbers that apply to the checker; the
// figures above are `nanoda_bin`'s own and are what put the lines in the tree.
//
// What is still true is the narrow half: `cargo test` builds the *library*, and
// `nanoda_lib` has no `#[global_allocator]`, so anything running **in process**
// in a test binary is on glibc. Only the two binary targets get mimalloc, and
// they get it independently — a test asserting on allocator behaviour must
// spawn one of them rather than call the library.
// ─────────────────────────────────────────────────────────────────────────────
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), MainError> {
    let mut args = std::env::args();
    let _ = args.next();
    let out = match args.next().as_ref() {
        None => Err(Box::from("This program expects a path to a configuration file.".to_string())),
        Some(p) if p == "-h" || p == "--help" => return Ok(println!("{}", HELP_LONG)),
        Some(p) => use_config(&Path::new(p)),
    }
    .map_err(|e| MainError(e))?;

    if let Some(msg) = out {
        println!("{}", msg);
    }
    Ok(())
}

// Returns an optional success message.
fn use_config(config_path: &Path) -> Result<Option<String>, Box<dyn Error>> {
    let cfg = Config::try_from(config_path)?;
    // Make sure the target pretty printer destination is accessible before doing any real work.
    let mut pp_destination = cfg.get_pp_destination()?;
    let (export_file, skipped_axioms) = cfg.to_export_file()?;
    // Check the environment
    export_file.check_all_declars();
    // Emit the definitional-equality step report, if counting was compiled in
    // (`--features stepcount`). Printed to stderr so it cannot be confused with
    // the checker's verdict on stdout.
    if let Some(report) = nanoda_lib::stepcount::report() {
        eprint!("{}", report);
    }
    if let Some(report) = nanoda_lib::certify::admit_report() {
        eprint!("{}", report);
    }
    if let Some(report) = nanoda_lib::certify::trace_cert_report() {
        eprint!("{}", report);
    }
    eprint!("{}", nanoda_lib::tg::global_report());
    // Pretty print as necessary
    let pp_errs = export_file.pp_selected_declars(pp_destination.as_mut());
    if export_file.config.print_success_message {
        if pp_errs.is_empty() {
            if skipped_axioms.is_empty() {
                Ok(Some(format!("Checked {} declarations with no errors", export_file.declars.len())))
            } else {
                Ok(Some(format!("Checked {} declarations with no errors, skipping exported but unpermitted axioms {:?}",
                export_file.declars.len(), skipped_axioms)))
            }
        } else {
            Ok(Some(format!(
                "Checked {} declarations with no typechecker errors, {} pretty printer errors: {:#?}",
                export_file.declars.len(),
                pp_errs.len(),
                pp_errs
            )))
        }
    } else if skipped_axioms.is_empty() {
        Ok(None)
    } else {
        Ok(Some(format!("Skipped exported but unpermitted axioms {:?}", skipped_axioms)))
    }
}

struct MainError(Box<dyn Error>);

impl std::fmt::Debug for MainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}\n\n{}", self.0, HELP_SHORT) }
}

const HELP_SHORT: &str = "run with `-h` or `--help` for help";
const HELP_LONG: &str = concat!(
    "nanoda_bin",
    " ",
    env!("CARGO_PKG_VERSION"),
    "\n\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n\n",
    "get more help at ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n\n",
    include_str!("../README.md")
);
