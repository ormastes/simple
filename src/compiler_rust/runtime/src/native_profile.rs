//! Native function-entry profile counters for JIT/`run`-mode parity with the C
//! `src/runtime/runtime_native.c` implementation.
//!
//! The codegen (`codegen/instr/body.rs`, `codegen/llvm/functions.rs`) emits a
//! call to `rt_native_profile_count(name_ptr)` at the entry of every generated
//! Simple function when `SIMPLE_NATIVE_PROFILE_COUNTERS=1` is set at compile
//! time. The corresponding symbol previously existed **only** in the
//! `core-c-bootstrap` C runtime bundle, so the JIT's runtime-symbol provider
//! could not resolve it. Because the JIT registers the `RuntimeFuncSpec` as an
//! import unconditionally, the pre-finalize NULL-jump guard (`codegen/jit.rs`)
//! then rejected the import and **disabled JIT for every program**, not just
//! instrumented ones (bug `jit_globally_disabled_unresolved_rt_native_profile_count_2026-06-19`).
//!
//! Providing real implementations here resolves the symbols (restoring JIT
//! globally) and gives `run`/JIT mode the same counting + TSV dump as
//! native-build. Output is written at process exit (via `libc::atexit`) only
//! when `SIMPLE_NATIVE_PROFILE_OUT` names a file (or `stderr`); with the env
//! unset the functions are effectively a cheap no-op, matching the C behavior.

use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::sync::atomic::{AtomicBool, Ordering};

use lazy_static::lazy_static;
use parking_lot::Mutex;

/// Cap mirrors `RT_NATIVE_PROFILE_MAX` in `runtime_native.c`.
const PROFILE_MAX: usize = 8192;
/// Cap mirrors `RT_NATIVE_PROFILE_EVENT_MAX` in `runtime_native.c`.
const EVENT_MAX: usize = 1024;

struct ProfileState {
    counts: HashMap<String, u64>,
    emitted: u64,
    dropped: u64,
    event_used: usize,
    event_emitted: u64,
    event_dropped: u64,
}

impl ProfileState {
    fn new() -> Self {
        ProfileState {
            counts: HashMap::new(),
            emitted: 0,
            dropped: 0,
            event_used: 0,
            event_emitted: 0,
            event_dropped: 0,
        }
    }
}

lazy_static! {
    static ref PROFILE: Mutex<ProfileState> = Mutex::new(ProfileState::new());
}

static ATEXIT_REGISTERED: AtomicBool = AtomicBool::new(false);
static DUMPED: AtomicBool = AtomicBool::new(false);

/// Read a null-terminated C string name; returns `None` for null/empty/invalid.
unsafe fn read_name(name: *const c_char) -> Option<String> {
    if name.is_null() {
        return None;
    }
    let s = CStr::from_ptr(name).to_str().ok()?;
    if s.is_empty() {
        None
    } else {
        Some(s.to_string())
    }
}

/// Register the atexit dump hook exactly once.
fn ensure_atexit() {
    if ATEXIT_REGISTERED
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
        .is_ok()
    {
        unsafe {
            libc::atexit(dump_at_exit);
        }
    }
}

/// Count one entry of the function named by `name` (a C string pointer).
///
/// # Safety
/// `name` must be null or a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_native_profile_count(name: *const c_char) {
    let Some(n) = read_name(name) else {
        return;
    };
    ensure_atexit();
    let mut st = PROFILE.lock();
    if let Some(slot) = st.counts.get_mut(&n) {
        *slot += 1;
        st.emitted += 1;
    } else if st.counts.len() < PROFILE_MAX {
        st.counts.insert(n, 1);
        st.emitted += 1;
    } else {
        st.dropped += 1;
    }
}

/// Record one event for the function named by `name` (a C string pointer).
///
/// # Safety
/// `name` must be null or a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_native_profile_event(name: *const c_char) {
    if read_name(name).is_none() {
        return;
    }
    ensure_atexit();
    let mut st = PROFILE.lock();
    if st.event_used < EVENT_MAX {
        st.event_used += 1;
        st.event_emitted += 1;
    } else {
        st.event_dropped += 1;
    }
}

extern "C" fn dump_at_exit() {
    dump();
}

/// Emit the TSV report to `SIMPLE_NATIVE_PROFILE_OUT` (path or `stderr`).
/// Matches the `runtime_native.c` format: `count\tfunction` header, rows sorted
/// by descending count (ties broken by name), then two summary comment lines.
fn dump() {
    let out = match std::env::var("SIMPLE_NATIVE_PROFILE_OUT") {
        Ok(v) if !v.is_empty() => v,
        _ => return,
    };
    if DUMPED.swap(true, Ordering::SeqCst) {
        return;
    }
    let st = PROFILE.lock();
    if st.counts.is_empty() {
        return;
    }

    let mut rows: Vec<(&String, u64)> = st.counts.iter().map(|(k, v)| (k, *v)).collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));

    let mut buf = String::new();
    buf.push_str("count\tfunction\n");
    for (name, count) in &rows {
        buf.push_str(&format!("{count}\t{name}\n"));
    }
    buf.push_str(&format!(
        "# profile_summary emitted={} dropped={} capacity={}\n",
        st.emitted, st.dropped, PROFILE_MAX as u64
    ));
    buf.push_str(&format!(
        "# profile_event_summary emitted={} dropped={} capacity={}\n",
        st.event_emitted, st.event_dropped, EVENT_MAX as u64
    ));

    if out == "stderr" {
        eprint!("{buf}");
    } else {
        let _ = std::fs::write(&out, buf);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[test]
    fn count_accumulates_by_name() {
        let mut st = PROFILE.lock();
        *st = ProfileState::new();
        drop(st);

        let a = CString::new("foo").unwrap();
        let b = CString::new("bar").unwrap();
        unsafe {
            rt_native_profile_count(a.as_ptr());
            rt_native_profile_count(a.as_ptr());
            rt_native_profile_count(b.as_ptr());
        }
        let st = PROFILE.lock();
        assert_eq!(st.counts.get("foo"), Some(&2));
        assert_eq!(st.counts.get("bar"), Some(&1));
        assert_eq!(st.emitted, 3);
    }

    #[test]
    fn null_and_empty_names_are_ignored() {
        unsafe {
            rt_native_profile_count(std::ptr::null());
            let empty = CString::new("").unwrap();
            rt_native_profile_count(empty.as_ptr());
        }
        // No panic, no crash — both are silently dropped.
    }
}
