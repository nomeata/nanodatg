use crate::util::{Config, CowStr, ExportFile, ExprPtr, LevelPtr, TcCtx};
use rand::distributions::Alphanumeric;
use rand::{rngs::ThreadRng, Rng};
use std::error::Error;
use std::path::{Path, PathBuf};

pub(crate) fn test_export_file<A>(
    config_path: Option<&Path>,
    f: impl FnOnce(&ExportFile) -> A,
) -> Result<A, Box<dyn Error>> {
    let (export_file, _) = test_get_export_file(config_path)?;
    Ok(f(&export_file))
}

pub(crate) fn test_get_export_file<'p>(config_path: Option<&Path>) -> Result<(ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let config_file = match config_path {
        None => Config {
            export_file_path: Some(PathBuf::from("test_resources/Empty/export")),
            use_stdin: false,
            permitted_axioms: Some(Vec::new()),
            unpermitted_axiom_hard_error: true,
            nat_extension: false,
            string_extension: false,
            pp_declars: None,
            pp_options: crate::pretty_printer::PpOptions::default(),
            unknown_pp_declar_hard_error: true,
            pp_output_path: None,
            pp_to_stdout: false,
            num_threads: 1,
            print_success_message: true,
            print_axioms: true,
            unsafe_permit_all_axioms: false
        },
        Some(config_path) => Config::try_from(config_path)?,
    };
    config_file.to_export_file()
}

#[allow(dead_code)]
pub(crate) fn test_export_file_should_panic<A>(config_path: Option<&Path>, f: impl FnOnce(&ExportFile) -> A) {
    // If there's an IO issue with actually getting the export file, we don't want
    // `should_panic` test to succeed, so we actually want to return success in this case.
    match test_get_export_file(config_path) {
        Err(..) => {}
        Ok((export_file, _)) => {
            f(&export_file);
        }
    }
}

pub(crate) fn test_ctx<'p, A>(path: Option<&Path>, f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
    test_export_file(path, |export_file| export_file.with_ctx(f))
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    #[cfg(test)]
    pub(crate) fn level_n(&mut self, mut l: LevelPtr<'t>, n: u64) -> LevelPtr<'t> {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn mk_succ_app(&mut self, n: usize) -> ExprPtr<'t> {
        let mut out = self.c_nat_zero().unwrap();
        let succ = self.c_nat_succ().unwrap();
        for _ in 0..n {
            out = self.mk_app(succ, out);
        }
        out
    }

    #[cfg(test)]
    pub(crate) fn param_quick(&mut self, s: &'static str) -> LevelPtr<'t> {
        let n = self.str1(&s);
        self.param(n)
    }
}

#[test]
fn check_empty() -> Result<(), Box<dyn Error>> {
    test_export_file(None, |export| {
        for declar in export.declars.values() {
            export.check_declar(declar);
        }
    })
}

#[test]
#[should_panic(expected = "infer_proj prop")]
fn check_proj_from_prop() {
    test_export_file_should_panic(
        Some(Path::new("test_resources/ProjFromProp/config.json")),
        |export| {
            for declar in export.declars.values() {
                export.check_declar(declar);
            }
        },
    )
}

pub(crate) fn rand_string<'t>(rng: &mut ThreadRng, size: usize) -> CowStr<'t> {
    let rand_string: String = rng.sample_iter(&Alphanumeric).take(size).map(char::from).collect();
    CowStr::Owned(rand_string)
}

/// Hash-consing is injective on literals: two allocations of equal content are
/// the same pointer and hash alike.
///
/// **This test ran 20 000 iterations of `None == None`.** It used
/// `test_export_file(None, …)`, whose inline `Config` sets `nat_extension:
/// false` and `string_extension: false`, and both `mk_string_lit_quick` and
/// `mk_nat_lit_quick` open with `if !…extension { return None }`
/// (`util.rs:687`, `:696`). There is no `unwrap`, so `l` and `r` were `None`
/// for every one of the 20 000 rounds and every assertion compared two `None`s.
/// No mutation to hash-consing, `Ptr::get_hash` or literal allocation could
/// have failed it.
///
/// Two changes, and the second is the one that keeps it fixed:
///
/// * it runs against `test_resources/EmptyLits/config.json` — the same empty
///   export, with both extensions on — so the constructors actually allocate;
/// * **`is_some()` is asserted first.** A test whose subject can silently
///   become unrepresentable must say so at the point it would go vacuous,
///   which is `ci/skip-guard.rs`'s rule ("a check that examined nothing
///   reports success") applied to an assertion rather than to an input. Flip
///   either extension back to `false` and this test now fails instead of
///   passing in 20 000 vacuous rounds.
///
/// See TEST-INVENTORY.md §6.
#[test]
fn hash_test0() -> Result<(), Box<dyn Error>> {
    use crate::hash64;
    use num_bigint::RandBigInt;
    use rand::thread_rng;
    test_export_file(Some(Path::new("test_resources/EmptyLits/config.json")), |export| {
        let mut rng = thread_rng();
        export.with_ctx(|ctx| {
            for size in 0..100 {
                for _ in 0..100 {
                    let s = rand_string(&mut rng, size);
                    let (l, r) = (ctx.mk_string_lit_quick(s.clone()), ctx.mk_string_lit_quick(s));
                    assert!(
                        l.is_some(),
                        "the string extension is off, so every assertion below compares two \
                         `None`s — this test measures nothing in that configuration"
                    );
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
                for _ in 0..100 {
                    let s = rng.gen_biguint(size as u64);
                    let (l, r) = (ctx.mk_nat_lit_quick(s.clone()), ctx.mk_nat_lit_quick(s));
                    assert!(
                        l.is_some(),
                        "the nat extension is off, so every assertion below compares two \
                         `None`s — this test measures nothing in that configuration"
                    );
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
            }
        })
    })
}
