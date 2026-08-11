//! **The `modelgen` filter, run over the export before mini parses it.**
//!
//! # Interface
//!
//! ```text
//! modelgen::Filter::Off | Filter::Run(path)
//! modelgen::discover(explicit) -> Result<Filter, String>
//! modelgen::filter(exe, input)  -> Result<(Vec<u8>, String), String>
//! ```
//!
//! `modelgen` (`MODELGEN.md`) reads a Lean `.ndjson` export and writes the same
//! export back with the **model of each nested inductive spliced in before the
//! declaration it models**. [`crate::mini::nested_splice`] recognises what it wrote
//! and keys `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧` onto it; with no filter pass
//! there is no model in the file and every nested declaration declines with
//! `no nested model in the export`.
//!
//! So the pass is **on by default** and the user does not have to know it
//! happened. `--no-modelgen` turns it off and `--modelgen=<path>` says where
//! the binary is.
//!
//! # It streams, and the two streams are separate
//!
//! `modelgen IN -o OUT` writes a file, and the obvious implementation is a
//! temporary one. On this machine `/tmp` is a **tmpfs** and writing a
//! multi-megabyte export into it has taken a session down twice, so a temp file
//! is not something to reach for casually. **`-o -` is stdout**, first class
//! (`MODELGEN.md` §1.4): mini reads the bytes into memory and hands them to the
//! parser through `Config::to_export_file_from`. Nothing is written to disk at
//! all.
//!
//! **`--quiet` is not passed, and the reason is the point.** `modelgen`'s
//! report — which declarations were modelled, and which were declined *and
//! why* — is on **stderr**, so it does not touch the export and does not have
//! to be silenced to keep it clean. Both were once true the other way round:
//! the report went to stdout by `IO.println`, `--quiet` was mandatory, and mini
//! could say `no nested model in the export` without being able to say why —
//! `nested model without funext`, say. That is naming where a value stopped
//! rather than why, reintroduced at a process boundary, and it is the defect
//! class this project has paid for most. So on success the child's report is
//! written straight through to mini's own stderr.
//!
//! # Failure is loud, and never a silent skip
//!
//! A missing binary, one that is not executable, a non-zero exit and output
//! that does not parse are all **declines that name the subprocess**, with the
//! child's stderr attached. None of them falls back to the unfiltered input.
//!
//! The exit status says *which*, and `MODELGEN.md` §1.4 is the contract mini
//! keys on: **1** is a usage error (mini built the command line, so this is
//! mini's bug), **2** is an input the filter could not read or parse, **3** is
//! the filter's own failure. A decline is **0** with the reason on stderr and
//! the export on stdout, and is deliberately *not* an error here: the file is
//! fine and no model was produced, which `MODELGEN.md` §1.3 says a consumer
//! must not read as a failure.
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
//! filter on gets the same bytes the suite reads with it off — measured over
//! **all 41** of them, not just `nested_keying`, at `-o -`.
//!
//! **One test is exempt and has to be.** `mini/tests/nested.rs`'s
//! `the_filters_report_reaches_the_user_and_says_why_there_is_no_model` execs
//! the real binary, because the report/export split is a property of the
//! process boundary and `--no-modelgen` cannot reach it. It skips when
//! `modelgen/.lake/build/bin/modelgen` is absent, and **says so on stderr**
//! rather than passing quietly — the note on
//! `a_modelgen_that_fails_declines_and_names_it` records a silent skip in this
//! same file that let a real mutation survive.

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

/// **Run the filter over `input` and return the filtered export and its
/// report.**
///
/// The two are the child's two streams, kept apart: the export is stdout
/// (`-o -`) and the report is stderr. The report is returned rather than
/// dropped because it is the only place a *reason* for a missing model exists
/// — see the header — and the caller writes it through.
///
/// `Err` carries the child's own stderr and what its exit status means; see the
/// header on why none of these is a fall-back to the unfiltered file.
pub fn filter(exe: &Path, input: &Path) -> Result<(Vec<u8>, String), String> {
    let out = Command::new(exe)
        .arg(input)
        .arg("-o")
        .arg("-")
        .output()
        .map_err(|e| format!("{}: {e}", exe.display()))?;
    let err = String::from_utf8_lossy(&out.stderr).trim().to_string();
    if !out.status.success() {
        // **The status, and what `MODELGEN.md` §1.4 says it means.** Both: the
        // number is the fact and the gloss is the reading, and a gloss without
        // the number would be unfalsifiable against a filter that is not
        // `modelgen` at all.
        let (code, gloss) = match out.status.code() {
            Some(c) => (
                format!("exited {c}"),
                match c {
                    1 => " (a command line it does not accept — mini built it, so mini's bug)",
                    2 => " (an input it could not read or parse)",
                    3 => " (its own internal error)",
                    _ => "",
                },
            ),
            None => ("died on a signal".to_string(), ""),
        };
        return Err(format!(
            "{} {}{}{}{}",
            exe.display(),
            code,
            gloss,
            if err.is_empty() { "" } else { ": " },
            err
        ))
    }
    if out.stdout.is_empty() {
        return Err(format!("{} produced no output", exe.display()))
    }
    Ok((out.stdout, err))
}
