//! Attribution trace for `.spl` source reads (default OFF).
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
