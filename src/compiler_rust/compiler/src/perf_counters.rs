//! Level-gated hot-path counters for the AST interpreter (default OFF).
//!
//! Enable with `SIMPLE_PERF_COUNTERS=1`; a one-line-per-counter report is
//! written to stderr (or to `SIMPLE_PERF_COUNTERS_OUT`) at process exit.
//! Off-path cost is a single relaxed atomic load + branch.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering};

const UNKNOWN: u8 = 0;
const OFF: u8 = 1;
const ON: u8 = 2;
static STATE: AtomicU8 = AtomicU8::new(UNKNOWN);
static ATEXIT_REGISTERED: AtomicBool = AtomicBool::new(false);

macro_rules! counters {
    ($($name:ident),* $(,)?) => {
        $(pub static $name: AtomicU64 = AtomicU64::new(0);)*
        fn render_rows() -> Vec<(&'static str, u64)> {
            vec![$((stringify!($name), $name.load(Ordering::Relaxed))),*]
        }
    };
}

counters!(
    // copy_value_type_in_place (argument binding, value-type struct copy)
    VT_CALLS,
    VT_ARRAY_ELEMS_SCANNED,
    VT_ARRAY_CLONES,
    VT_ARRAY_ELEMS_CLONED,
    VT_OBJECT_FIELD_CLONES,
    // identifier-receiver array mutation (arr.push(x) and friends)
    ARR_MUT_CALLS,
    ARR_MUT_COW_CLONES,
    ARR_MUT_COW_ELEMS_CLONED,
    // object-field array mutation (obj.field.push(x) / self.field.push(x))
    SELF_FIELD_ARR_MUT_CALLS,
    SELF_FIELD_ARR_COW_CLONES,
    SELF_FIELD_ARR_COW_ELEMS_CLONED,
);

#[inline(always)]
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        OFF => false,
        ON => true,
        _ => init(),
    }
}

#[cold]
fn init() -> bool {
    let on = std::env::var("SIMPLE_PERF_COUNTERS").is_ok_and(|v| !v.is_empty() && v != "0");
    if on && !ATEXIT_REGISTERED.swap(true, Ordering::Relaxed) {
        unsafe {
            libc::atexit(dump_at_exit);
        }
    }
    STATE.store(if on { ON } else { OFF }, Ordering::Relaxed);
    on
}

/// Force the gate on/off regardless of `SIMPLE_PERF_COUNTERS` (mechanism
/// tests: the gate is latched on first use, so an env var set after another
/// test already ran in the same process would be ignored).
pub fn set_enabled(on: bool) {
    STATE.store(if on { ON } else { OFF }, Ordering::Relaxed);
}

#[inline(always)]
pub fn bump(counter: &AtomicU64, by: u64) {
    if enabled() {
        counter.fetch_add(by, Ordering::Relaxed);
    }
}

extern "C" fn dump_at_exit() {
    let text = render();
    match std::env::var("SIMPLE_PERF_COUNTERS_OUT") {
        Ok(path) if !path.is_empty() => {
            let _ = std::fs::write(path, text);
        }
        _ => eprintln!("{}", text),
    }
}

/// Render the counter report. Public so specs can assert on it.
pub fn render() -> String {
    let mut out = String::from("interp-perf-counters:\n");
    for (name, value) in render_rows() {
        out.push_str(&format!("  {:<28} {:>16}\n", name, value));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_lists_every_counter_and_its_value() {
        VT_ARRAY_ELEMS_CLONED.store(7, Ordering::Relaxed);
        let text = render();
        assert!(text.starts_with("interp-perf-counters:\n"));
        for (name, _) in render_rows() {
            assert!(text.contains(name), "counter {name} missing from report");
        }
        assert!(text.contains("VT_ARRAY_ELEMS_CLONED"));
        assert!(text.contains('7'));
        VT_ARRAY_ELEMS_CLONED.store(0, Ordering::Relaxed);
    }
}
