//! **The `modelgen` filter, run over the export before mini parses it.**
//!
//! # Interface
//!
//! ```text
//! modelgen::Filter::Off | Filter::Run(path)
//! modelgen::discover(explicit) -> Result<Filter, String>
//! modelgen::filter(exe, input)  -> Result<Vec<u8>, String>
//! ```
//!
//! `modelgen` (`MODELGEN.md`) reads a Lean `.ndjson` export and writes the same
//! export back with the **model of each nested inductive spliced in before the
//! declaration it models**. [`crate::nested_splice`] recognises what it wrote
//! and keys `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧` onto it; with no filter pass
//! there is no model in the file and every nested declaration declines with
//! `no nested model in the export`.
//!
//! So the pass is **on by default** and the user does not have to know it
//! happened. `--no-modelgen` turns it off and `--modelgen=<path>` says where
//! the binary is.
//!
//! # It streams, and the reason that mattered
//!
//! `modelgen IN -o OUT` writes a file, and the obvious implementation is a
//! temporary one. On this machine `/tmp` is a **tmpfs** and writing a
//! multi-megabyte export into it has taken a session down twice, so a temp file
//! is not something to reach for casually. `-o /dev/stdout` is what is used
//! instead: `IO.FS.writeFile "/dev/stdout"` opens the inherited pipe, mini
//! reads the bytes into memory and hands them to the parser through
//! `Config::to_export_file_from`. Nothing is written to disk at all.
//!
//! Two things that costs, both recorded rather than papered over:
//!
//! * **`/dev/stdout` is not portable.** A first-class `-o -` is the right
//!   spelling and is a request on `modelgen`; this is what works against the
//!   binary as it stands, on Linux, which is the only platform this repository
//!   is built on.
//! * **`--quiet` is forced**, because `modelgen`'s report goes to *stdout* by
//!   `IO.println` and would be interleaved with the export. The report says
//!   which declarations were modelled and which were declined and why, which
//!   is exactly what a user would want to see; routing it to stderr is the
//!   other half of the same request. Until then a decline is visible where it
//!   matters anyway — mini's own `nested` counters and `zoneb`'s reason string
//!   name every nested declaration with no model.
//!
//! # Failure is loud, and never a silent skip
//!
//! A missing binary, one that is not executable, a non-zero exit and output
//! that does not parse are all **declines that name the subprocess**, with the
//! child's stderr attached. None of them falls back to the unfiltered input.
//!
//! That is a deliberate refusal of the convenient behaviour. A silent skip
//! would present a toolchain problem — `modelgen` not built — as the
//! *declaration's* problem: the file would be accepted, every nested
//! declaration would decline with `no nested model in the export`, and the
//! counters would report a shape mini cannot model when in fact mini was never
//! shown the model. That is the same misattribution class as keying on a name
//! instead of on a cause, and this project has paid for it once.
//!
//! # Where the binary is looked for
//!
//! In order, first hit wins, and the flag overrides everything:
//!
//! 1. `--modelgen=<path>`, unconditionally — no existence check beyond the one
//!    every other candidate gets, so a wrong path is a named failure rather
//!    than a silent fall-through to the next candidate;
//! 2. `$MINI_MODELGEN`, same rule;
//! 3. `modelgen/.lake/build/bin/modelgen` under the repository the running
//!    binary sits in — `target/{debug,release}/mini` walks up two directories;
//! 4. `modelgen` on `$PATH`.
//!
//! # What happens on a machine with no Lean toolchain
//!
//! Nothing is built and nothing is on `$PATH`, so **every run over a file with
//! a nested inductive declines by name**, saying `modelgen`. A file without one
//! is unaffected in content but still pays the exec.
//!
//! The test suites therefore pass `--no-modelgen` and read **committed,
//! already-filtered fixtures** (`scripts/export-fixture.sh` runs the filter
//! when it regenerates them). That keeps `cargo test` hermetic and independent
//! of `elan`, which is the property the fixture directory has always had — its
//! own header says the `.ndjson` is checked in "so neither `lean` nor the
//! network is needed to run the tests" — while leaving the default user path
//! the invisible one.
//!
//! Filtering is **idempotent**, which is what makes those two facts compatible:
//! `modelgen` scans the whole input for the names its model would take and
//! declines `nested model name taken` when they are there, so a second pass
//! over a filtered file passes it through byte for byte (measured on
//! `nested_keying`). A user who runs mini on a committed fixture with the
//! filter on gets the same bytes the suite reads with it off.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Whether to run the filter, and with which binary.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Filter {
    /// `--no-modelgen`. The export is parsed as it stands.
    #[default]
    Off,
    /// Run this binary over the export first.
    Run(PathBuf),
}

/// The flag as `mini`'s command line spells it.
pub const NO_FLAG: &str = "--no-modelgen";
/// `--modelgen=<path>`.
pub const PATH_FLAG: &str = "--modelgen";
/// The environment variable candidate 2 reads.
pub const ENV_VAR: &str = "MINI_MODELGEN";

/// **Where the filter is**, by the header's four candidates.
///
/// `Err` is "the pass was asked for and there is no binary", with the
/// candidates that were tried — a usage error, and the caller turns it into an
/// exit rather than into a run with no filter.
pub fn discover(explicit: Option<&str>) -> Result<Filter, String> {
    let mut tried: Vec<String> = Vec::new();
    if let Some(p) = explicit {
        return usable(Path::new(p)).map(Filter::Run).ok_or_else(|| {
            format!("{PATH_FLAG}={p}: not an executable file")
        })
    }
    if let Ok(p) = std::env::var(ENV_VAR) {
        return usable(Path::new(&p))
            .map(Filter::Run)
            .ok_or_else(|| format!("${ENV_VAR}={p}: not an executable file"))
    }
    if let Ok(exe) = std::env::current_exe() {
        // `target/<profile>/mini` — two directories up is the workspace root.
        if let Some(root) = exe.parent().and_then(Path::parent).and_then(Path::parent) {
            let c = root.join("modelgen/.lake/build/bin/modelgen");
            if let Some(p) = usable(&c) {
                return Ok(Filter::Run(p))
            }
            tried.push(c.display().to_string());
        }
    }
    for dir in std::env::var("PATH").unwrap_or_default().split(':') {
        if dir.is_empty() {
            continue
        }
        let c = Path::new(dir).join("modelgen");
        if let Some(p) = usable(&c) {
            return Ok(Filter::Run(p))
        }
    }
    tried.push("modelgen on $PATH".to_string());
    Err(format!(
        "modelgen not found (tried {}); build it with `lake build` in modelgen/, \
         point at it with {PATH_FLAG}=<path> or ${ENV_VAR}, or pass {NO_FLAG}",
        tried.join(", ")
    ))
}

/// A candidate that exists and is a file. Executability is left to `exec` to
/// discover: a file that is there and not runnable produces the OS's own
/// message, which says more than "not executable" would.
fn usable(p: &Path) -> Option<PathBuf> {
    p.is_file().then(|| p.to_path_buf())
}

/// **Run the filter over `input` and return the filtered export.**
///
/// `Err` carries the child's own stderr; see the header on why none of these is
/// a fall-back to the unfiltered file.
pub fn filter(exe: &Path, input: &Path) -> Result<Vec<u8>, String> {
    let out = Command::new(exe)
        .arg(input)
        .arg("-o")
        .arg("/dev/stdout")
        .arg("--quiet")
        .output()
        .map_err(|e| format!("{}: {e}", exe.display()))?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        let err = err.trim();
        return Err(format!(
            "{} exited {}{}{}",
            exe.display(),
            out.status.code().map(|c| c.to_string()).unwrap_or_else(|| "on a signal".into()),
            if err.is_empty() { "" } else { ": " },
            err
        ))
    }
    if out.stdout.is_empty() {
        return Err(format!("{} produced no output", exe.display()))
    }
    Ok(out.stdout)
}
