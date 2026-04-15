//! Stub implementations for `rt_test262_*` SFFI symbols declared in
//! `src/app/ui.chromium/js_audit.spl`.
//!
//! By default all symbols are stubs (sentinel values, no JS engine linked).
//! Enable the `test262-real` Cargo feature to replace `rt_test262_eval` with a
//! real QuickJS evaluation via the `rquickjs` crate.  All other symbols remain
//! stubs until a corpus loader lands.
//!
//! Sentinel convention (matches the rest of `src/runtime/hosted/`):
//!   - handle / count returns  → `-1`  (invalid / not-found)
//!   - bool returns            → `false`
//!   - text (ptr) returns      → pointer to a static empty C string

use std::os::raw::c_char;

/// Static empty C string used as the sentinel `text` return value.
static EMPTY: &[u8] = b"\0";

// ---------------------------------------------------------------------------
// rt_test262_eval — real implementation (feature = "test262-real")
// ---------------------------------------------------------------------------

#[cfg(feature = "test262-real")]
/// Evaluate a JS `source` snippet via QuickJS.
/// Returns 0 on success, -1 on any error (null pointer, eval exception, etc.).
#[no_mangle]
pub unsafe extern "C" fn rt_test262_eval(
    _backend: *const c_char,
    source: *const c_char,
) -> i64 {
    use rquickjs::{Context, Runtime};
    use std::ffi::CStr;

    if source.is_null() {
        return -1;
    }
    let src = match CStr::from_ptr(source).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };
    let rt = match Runtime::new() {
        Ok(r) => r,
        Err(_) => return -1,
    };
    let ctx = match Context::full(&rt) {
        Ok(c) => c,
        Err(_) => return -1,
    };
    ctx.with(|ctx| {
        match ctx.eval::<(), _>(src) {
            Ok(_) => 0i64,
            Err(_) => -1i64,
        }
    })
}

// ---------------------------------------------------------------------------
// rt_test262_eval — stub (default, no feature)
// ---------------------------------------------------------------------------

#[cfg(not(feature = "test262-real"))]
/// Evaluate a JS `source` snippet against a named `backend`.
/// Stub: always returns -1 (eval not available).
#[no_mangle]
pub unsafe extern "C" fn rt_test262_eval(
    _backend: *const c_char,
    _source: *const c_char,
) -> i64 {
    -1
}

/// Load a test262 corpus subset by name.
/// Stub: always returns -1 (no corpus available).
#[no_mangle]
pub unsafe extern "C" fn rt_test262_load_corpus(_subset: *const c_char) -> i64 {
    -1
}

/// Return the JS source text of case `index` in corpus `handle`.
/// Stub: always returns pointer to empty string.
#[no_mangle]
pub unsafe extern "C" fn rt_test262_case_source(
    _handle: i64,
    _index: i64,
) -> *const c_char {
    EMPTY.as_ptr() as *const c_char
}

/// Return whether case `index` in corpus `handle` is a negative (must-throw) test.
/// Stub: always returns false.
#[no_mangle]
pub unsafe extern "C" fn rt_test262_case_negative(_handle: i64, _index: i64) -> bool {
    false
}

/// Return the number of cases in corpus `handle`.
/// Stub: always returns -1 (invalid handle).
#[no_mangle]
pub unsafe extern "C" fn rt_test262_case_count(_handle: i64) -> i64 {
    -1
}

/// Free a corpus handle previously returned by `rt_test262_load_corpus`.
/// Stub: no-op.
#[no_mangle]
pub unsafe extern "C" fn rt_test262_corpus_free(_handle: i64) {}
