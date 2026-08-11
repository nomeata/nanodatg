//! Catch expected parser/type-checker panics without corrupting stderr.
//!
//! Nanoda's historical rejection API is panic-based. The unified checker
//! catches those panics at a declaration boundary, but the default panic hook
//! runs before `catch_unwind` and would print a false process-crash diagnostic.
//! A single process hook delegates normally except on the catching thread.
//! Suppression is thread-local, so parallel checks do not silence one another.

use std::cell::Cell;
use std::panic::AssertUnwindSafe;
use std::sync::Once;

thread_local! {
    static SILENT: Cell<bool> = const { Cell::new(false) };
}

fn install_hook() {
    static INSTALL: Once = Once::new();
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SILENT.with(Cell::get) {
                previous(info);
            }
        }));
    });
}

pub(crate) fn catch_silent<F: FnOnce() -> R, R>(f: F) -> std::thread::Result<R> {
    install_hook();
    SILENT.with(|silent| {
        let old = silent.replace(true);
        let result = std::panic::catch_unwind(AssertUnwindSafe(f));
        silent.set(old);
        result
    })
}

pub(crate) fn message(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
        .unwrap_or_else(|| "nanoda checker panicked".to_string())
}
