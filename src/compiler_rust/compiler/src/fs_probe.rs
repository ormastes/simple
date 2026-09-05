//! Memoized filesystem existence probes for module resolution.
//!
//! Module resolution probes a large, fixed candidate set per import: the
//! search-root walk up to the workspace boundary, crossed with the stdlib
//! variant roots, the numbered-directory forms, and the legacy
//! `rust/lib/std/src` / `simple/std_lib/src` / `std_lib/src` layouts. Each
//! candidate is a `Path::exists()` / `is_dir()` / `is_file()` call, and the
//! `exists() && is_file()` idiom used throughout costs two `statx` for one
//! question.
//!
//! Measured 2026-08-20 (`strace -c -f`, seed `bin/simple lint` on a one-line
//! file): **905,970 `statx` calls, 194,055 of them ENOENT** — 21.6% of all
//! syscall time — with individual directories such as
//! `src/compiler/00.common` stat'd 2,798 times in one process. The candidate
//! set does not change while a resolution pass runs, so each distinct path is
//! stat'd once and the answer reused.
//!
//! The cache is thread-local and is cleared by
//! `clear_path_resolution_cache()`, so a test run that creates files between
//! passes sees fresh state.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone, Copy)]
pub(crate) struct PathKind {
    pub exists: bool,
    pub is_dir: bool,
    pub is_file: bool,
}

pub(crate) static STAT_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static STAT_MISSES: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static PATH_KIND_CACHE: RefCell<HashMap<PathBuf, PathKind>> = RefCell::new(HashMap::new());
}

pub(crate) fn path_kind(path: &Path) -> PathKind {
    STAT_CALLS.fetch_add(1, Ordering::Relaxed);
    if let Some(kind) = PATH_KIND_CACHE.with(|cache| cache.borrow().get(path).copied()) {
        return kind;
    }
    STAT_MISSES.fetch_add(1, Ordering::Relaxed);
    let kind = match std::fs::metadata(path) {
        Ok(meta) => PathKind {
            exists: true,
            is_dir: meta.is_dir(),
            is_file: meta.is_file(),
        },
        Err(_) => PathKind {
            exists: false,
            is_dir: false,
            is_file: false,
        },
    };
    PATH_KIND_CACHE.with(|cache| {
        cache.borrow_mut().insert(path.to_path_buf(), kind);
    });
    kind
}

pub(crate) fn p_exists(path: &Path) -> bool {
    path_kind(path).exists
}

pub(crate) fn p_is_dir(path: &Path) -> bool {
    path_kind(path).is_dir
}

pub(crate) fn p_is_file(path: &Path) -> bool {
    path_kind(path).is_file
}

/// Drop every memoized probe. Called whenever the resolver caches are cleared.
pub(crate) fn clear_fs_probe_cache() {
    PATH_KIND_CACHE.with(|cache| cache.borrow_mut().clear());
}
