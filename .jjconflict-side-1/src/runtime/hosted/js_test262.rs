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
pub unsafe extern "C" fn rt_test262_eval(_backend: *const c_char, source: *const c_char) -> i64 {
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
    ctx.with(|ctx| match ctx.eval::<(), _>(src) {
        Ok(_) => 0i64,
        Err(_) => -1i64,
    })
}

// ---------------------------------------------------------------------------
// rt_test262_eval — stub (default, no feature)
// ---------------------------------------------------------------------------

#[cfg(not(feature = "test262-real"))]
/// Evaluate a JS `source` snippet against a named `backend`.
/// Stub: always returns -1 (eval not available).
#[no_mangle]
pub unsafe extern "C" fn rt_test262_eval(_backend: *const c_char, _source: *const c_char) -> i64 {
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
pub unsafe extern "C" fn rt_test262_case_source(_handle: i64, _index: i64) -> *const c_char {
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

// ---------------------------------------------------------------------------
// rt_test262_list_cases / rt_test262_case_path
// ---------------------------------------------------------------------------
// Real impl (feature = "test262-real"): walk suite_dir recursively, store
// *.js paths in a thread-local. Stub returns -1 / empty-string sentinels.

#[cfg(feature = "test262-real")]
mod corpus {
    use std::cell::RefCell;
    use std::ffi::CString;
    use std::fs;
    use std::path::Path;

    thread_local! {
        pub static CASE_PATHS: RefCell<Vec<CString>> = RefCell::new(Vec::new());
    }

    pub fn collect_js_files(dir: &Path, out: &mut Vec<CString>) {
        let entries = match fs::read_dir(dir) {
            Ok(e) => e,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().and_then(|n| n.to_str()) == Some("harness") {
                    continue;
                }
                collect_js_files(&path, out);
            } else if path.extension().and_then(|e| e.to_str()) == Some("js") {
                let fname = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                if fname == "_FIXTURE.js" {
                    continue;
                }
                if let Some(s) = path.to_str() {
                    if let Ok(c) = CString::new(s) {
                        out.push(c);
                    }
                }
            }
        }
    }
}

#[cfg(feature = "test262-real")]
#[no_mangle]
pub unsafe extern "C" fn rt_test262_list_cases(suite_dir: *const c_char) -> i64 {
    use std::ffi::CStr;
    use std::path::Path;

    if suite_dir.is_null() {
        return -1;
    }
    let dir = match CStr::from_ptr(suite_dir).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };
    let mut cases = Vec::new();
    corpus::collect_js_files(Path::new(dir), &mut cases);
    let count = cases.len() as i64;
    corpus::CASE_PATHS.with(|c| *c.borrow_mut() = cases);
    count
}

#[cfg(feature = "test262-real")]
#[no_mangle]
pub unsafe extern "C" fn rt_test262_case_path(index: i64) -> *const c_char {
    if index < 0 {
        return EMPTY.as_ptr() as *const c_char;
    }
    corpus::CASE_PATHS.with(|c| {
        let cases = c.borrow();
        match cases.get(index as usize) {
            Some(cs) => cs.as_ptr(),
            None => EMPTY.as_ptr() as *const c_char,
        }
    })
}

/// Stub: enumerate cases in a test262 suite directory.
/// Real impl walks the tree; stub returns -1.
#[cfg(not(feature = "test262-real"))]
#[no_mangle]
pub unsafe extern "C" fn rt_test262_list_cases(_suite_dir: *const c_char) -> i64 {
    -1
}

/// Stub: return the absolute path of case `index`.
/// Real impl reads a thread-local store populated by `rt_test262_list_cases`.
#[cfg(not(feature = "test262-real"))]
#[no_mangle]
pub unsafe extern "C" fn rt_test262_case_path(_index: i64) -> *const c_char {
    EMPTY.as_ptr() as *const c_char
}
