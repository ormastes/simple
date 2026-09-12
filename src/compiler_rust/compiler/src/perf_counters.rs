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
    // identifier-receiver dict mutation (d.insert(k, v) / d.remove(k) and friends)
    DICT_MUT_CALLS,
    DICT_MUT_COW_CLONES,
    DICT_MUT_COW_ENTRIES_CLONED,
    // object-field array mutation (obj.field.push(x) / self.field.push(x))
    SELF_FIELD_ARR_MUT_CALLS,
    SELF_FIELD_ARR_COW_CLONES,
    SELF_FIELD_ARR_COW_ELEMS_CLONED,
    // filter_functions_from_value: imported-module dict rebuilt vs memo hit
    // steal_owned_global (promotion-time unique ownership of a global collection)
    STEAL_OK,
    STEAL_NO_BINDING,
    STEAL_OUTER_SHARED,
    STEAL_INNER_SHARED,
    STEAL_MISSING,
    STEAL_MISMATCH,
    // park_written_back_arguments (caller handle released across a nested call)
    PARK_ARG_OK,
    PARK_ARG_RESTORED,
    // f(obj.field) write-back: object field-map copy-on-write against a handle
    // the suspended caller frame is about to overwrite (dead alias).
    FIELD_WRITEBACK_CALLS,
    FIELD_WRITEBACK_MAP_CLONES,
    FILTERED_DICT_BUILDS,
    FILTERED_DICT_HITS,
    // import-resolution probe file reads (see module_cache::probe_source_cached)
    PROBE_SOURCE_READS,
    PROBE_SOURCE_HITS,
    // imported-module AST memo (hir::lower::import_loader::parsed_imported_module):
    // parses/hits ATTRIBUTED TO THE HIR LANE, i.e. the fills that lane caused.
    IMPORT_AST_PARSES,
    IMPORT_AST_HITS,
    // cross-lane source+AST cache (module_cache::shared_source). PARSES counts
    // physical files read+parsed once for every lane; HITS counts every lookup
    // served from it. The interpreter counters below split its own consumption:
    // AST_REUSE borrowed the shared parse, PARSES had to parse its own source
    // because host `@cfg` stripping changed the bytes.
    SHARED_SRC_PARSES,
    SHARED_SRC_HITS,
    INTERP_MODULE_AST_REUSE,
    INTERP_MODULE_PARSES,
    // place-receiver mutation (`self.inner.xs.push(x)`, `rows[i].push(x)`,
    // `self.d.insert(k, v)`, `arr[i].inc()`) — the in-place kernel in
    // interpreter_helpers/patterns.rs::try_place_mutation_in_place.
    PLACE_MUT_CALLS,
    PLACE_MUT_COW_CLONES,
    PLACE_MUT_COW_ELEMS_CLONED,
    // numbered-layer-directory memos (module_resolver::resolution)
    NUMBERED_DIR_MISSES,
    NUMBERED_DIR_HITS,
    SEGMENT_WITHIN_NUMBERED_MISSES,
    SEGMENT_WITHIN_NUMBERED_HITS,
    // while-loop iterations executed by an inline-integer fast path instead of
    // the generic AST walk (interpreter_control.rs: the one-arg/two-arg helper
    // matchers and the generalised inline-expression matcher). Bumped once per
    // loop with the iteration count, so it is free in the hot loop.
    //
    // This is also the observable that makes those fast paths diagnosable. A
    // matched loop used to touch no counter at all, so the process emitted NO
    // `interp-perf-counters:` block, and "no block" had to be read as "a fast
    // path ran" -- see the hazard section of
    // doc/08_tracking/bug/interpreter_while_loop_fast_path_shape_cliff_2026-09-12.md.
    // Now a matched loop reports the iterations it accelerated.
    WHILE_INLINE_INT_ITERS,
    // retention bounds on the loader memos (module_cache, bounded_cache).
    // EVICTIONS counts entries dropped to stay under the limit; PINNED_SKIPS
    // counts enforcement passes that could free nothing because every
    // over-limit candidate was still borrowed (the cache then stays OVER its
    // limit rather than freeing a live entry); RETAINED_MAX is a high-water
    // entry count, written with `set_max`, not `bump`.
    PARSED_SOURCE_EVICTIONS,
    PARSED_SOURCE_PINNED_SKIPS,
    PARSED_SOURCE_RETAINED_MAX,
    PROBE_SOURCE_EVICTIONS,
    PROBE_SOURCE_PINNED_SKIPS,
    PROBE_SOURCE_RETAINED_MAX,
    PATH_KEY_EVICTIONS,
    PATH_KEY_PINNED_SKIPS,
    PATH_KEY_RETAINED_MAX,
    FILTERED_DICT_EVICTIONS,
    FILTERED_DICT_PINNED_SKIPS,
    FILTERED_DICT_RETAINED_MAX,
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
        #[cfg(unix)]
        unsafe {
            libc::atexit(dump_at_exit);
            libc::signal(libc::SIGTERM, dump_on_signal as libc::sighandler_t);
            libc::signal(libc::SIGINT, dump_on_signal as libc::sighandler_t);
        }
        // `libc` is a cfg(unix)-only dependency of this crate, so the call
        // above cannot compile on Windows. atexit itself is standard C and the
        // MSVC CRT exports it, so declare it directly rather than dropping the
        // feature: SIMPLE_PERF_COUNTERS is a documented debugging tool
        // (.claude/rules/commands.md) and a silently-inert counter dump would
        // be worse than none.
        #[cfg(not(unix))]
        unsafe {
            extern "C" {
                fn atexit(cb: extern "C" fn()) -> i32;
            }
            atexit(dump_at_exit);
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

/// Attribution trace for the hot counters (default OFF): with
/// `SIMPLE_PERF_COUNTERS_TRACE=<min_len>` each COW clone or value-type scan of an
/// array of at least `min_len` elements logs one stderr line naming the
/// receiver/parameter, so a counter that grows quadratically can be tied to the
/// Simple-level variable that causes it.
pub fn trace_min_len() -> u64 {
    static MIN: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *MIN.get_or_init(|| {
        std::env::var("SIMPLE_PERF_COUNTERS_TRACE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    })
}

pub fn trace_array(site: &str, name: &str, len: usize) {
    if enabled() {
        let min = trace_min_len();
        if min > 0 && len as u64 >= min {
            eprintln!("[perf-trace] {site} name={name} len={len}");
        }
    }
}

#[inline(always)]
pub fn bump(counter: &AtomicU64, by: u64) {
    if enabled() {
        counter.fetch_add(by, Ordering::Relaxed);
    }
}

/// Raise `counter` to `value` if `value` is larger, for high-water marks such
/// as `*_RETAINED_MAX`. Adding these with `bump` would report the sum of every
/// sample, which is meaningless for a maximum.
#[inline(always)]
pub fn set_max(counter: &AtomicU64, value: u64) {
    if enabled() {
        counter.fetch_max(value, Ordering::Relaxed);
    }
}

/// Dump on SIGTERM/SIGINT as well as at exit.
///
/// `atexit` never runs when the process is killed by a signal, and the
/// workloads these counters are most useful on are exactly the ones that get
/// killed by a `timeout` budget. Only installed when `SIMPLE_PERF_COUNTERS`
/// is set, so the default path is unchanged. The handler allocates, which is
/// not async-signal-safe in general; that is acceptable for an opt-in
/// diagnostic whose next action is to terminate the process anyway.
// `libc` is a cfg(unix)-only dependency of this crate, and the only call
// sites (the `libc::signal` installs above) are already `#[cfg(unix)]`.
// Without the same gate here the definition itself is compiled on Windows
// and fails with E0433 `unresolved module or unlinked crate libc`, which
// breaks the Rust seed build for the whole MSVC bootstrap lane.
#[cfg(unix)]
extern "C" fn dump_on_signal(sig: libc::c_int) {
    dump_at_exit();
    unsafe { libc::_exit(128 + sig) };
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

    #[test]
    fn set_max_keeps_the_high_water_not_the_sum() {
        let was = STATE.load(Ordering::Relaxed);
        set_enabled(true);
        let counter = AtomicU64::new(0);
        set_max(&counter, 5);
        set_max(&counter, 3);
        set_max(&counter, 9);
        set_max(&counter, 4);
        assert_eq!(counter.load(Ordering::Relaxed), 9, "a maximum, not 5+3+9+4");
        STATE.store(was, Ordering::Relaxed);
    }
}
