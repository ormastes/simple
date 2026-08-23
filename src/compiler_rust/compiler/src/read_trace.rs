//! Attribution trace for `.spl` source reads (default OFF).
//!
//! `SIMPLE_READ_TRACE=1` prints one `[read] <file>:<line> <path>` line per
//! source read, so a redundant-read count measured with `strace` can be tied to
//! the CALL SITE that issues it. Off-path cost is one relaxed atomic load.
use std::sync::atomic::{AtomicU8, Ordering};

static STATE: AtomicU8 = AtomicU8::new(0);

#[inline(always)]
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        1 => false,
        2 => true,
        _ => {
            let on = std::env::var("SIMPLE_READ_TRACE").is_ok_and(|v| !v.is_empty() && v != "0");
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

/// `read_to_string` with call-site attribution.
pub fn rts<P: AsRef<std::path::Path>>(file: &str, line: u32, path: P) -> std::io::Result<String> {
    if enabled() {
        eprintln!("[read] {}:{} {}", file, line, path.as_ref().display());
    }
    std::fs::read_to_string(path)
}
