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
//!
//! **Windows: misses are answered from the parent's directory listing.** A
//! `metadata` call that fails costs ~90 us there (vs ~1 us on Linux), and the
//! resolver's candidate set is mostly paths that do not exist. Measured
//! 2026-11-28 on `bin/simple run scripts/tool/riscv64-unknown-elf-tool-wrapper.spl`
//! (79 modules): 5,396 distinct probes, 504 ms of a 1.55 s run. So on Windows
//! a miss first asks for the parent's kind (memoized, recursive): a child of a
//! path that is not a directory is absent with no syscall at all. Otherwise
//! the parent is listed once (`read_dir`, whose entries already carry their
//! file type) and the name looked up there. Every case the listing cannot
//! answer exactly as `metadata` would falls back to `metadata`: a symlink or
//! junction (metadata follows it), a name the listing does not contain but
//! the OS may still match (8.3 short names with `~`, non-ASCII names under
//! NTFS case folding, trailing `.`/space), an ambiguous case-folded name, a
//! path with no file name (`..` tail) or no parent, and an unreadable parent.
//! Listings share the probe cache's lifetime and are dropped with it. This is
//! WIDER staleness than the per-path cache alone: probing one name lists the
//! directory, which freezes every name in it, so a file created there later is
//! invisible until `clear_fs_probe_cache()` even if that exact path was never
//! probed before. Only resolver code calls these probes, and every resolver
//! cache clear drops both maps.
//!
//! Known gap: a directory with per-directory case sensitivity enabled
//! (`fsutil file setCaseSensitiveInfo`, used by WSL) can report a case-variant
//! name as present where `metadata` would say absent.

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

/// Directory listings read to answer probe misses (Windows only).
pub(crate) static DIR_LISTINGS: AtomicU64 = AtomicU64::new(0);
/// Probe misses that cost a real `metadata` call (all of them off Windows).
pub(crate) static METADATA_CALLS: AtomicU64 = AtomicU64::new(0);

const ABSENT: PathKind = PathKind {
    exists: false,
    is_dir: false,
    is_file: false,
};

thread_local! {
    static PATH_KIND_CACHE: RefCell<HashMap<PathBuf, PathKind>> = RefCell::new(HashMap::new());
    /// Parent directory -> ASCII-lowercased entry name -> file type, or `None`
    /// when two entries fold to the same name. A parent `read_dir` could not
    /// open maps to `None` too, so it is never retried.
    static DIR_LISTING_CACHE: RefCell<HashMap<PathBuf, Option<HashMap<String, Option<std::fs::FileType>>>>> =
        RefCell::new(HashMap::new());
}

pub(crate) fn path_kind(path: &Path) -> PathKind {
    STAT_CALLS.fetch_add(1, Ordering::Relaxed);
    if let Some(kind) = PATH_KIND_CACHE.with(|cache| cache.borrow().get(path).copied()) {
        return kind;
    }
    STAT_MISSES.fetch_add(1, Ordering::Relaxed);
    let kind = listing_kind(path).unwrap_or_else(|| metadata_kind(path));
    PATH_KIND_CACHE.with(|cache| {
        cache.borrow_mut().insert(path.to_path_buf(), kind);
    });
    kind
}

fn metadata_kind(path: &Path) -> PathKind {
    METADATA_CALLS.fetch_add(1, Ordering::Relaxed);
    match std::fs::metadata(path) {
        Ok(meta) => PathKind {
            exists: true,
            is_dir: meta.is_dir(),
            is_file: meta.is_file(),
        },
        Err(_) => ABSENT,
    }
}

/// Answer a probe from the parent's listing, or `None` when only `metadata`
/// can answer it exactly (see the module docs). Off Windows a failed `stat` is
/// cheap and the filesystem may be case-sensitive or case-insensitive, so the
/// listing path is not taken there.
#[cfg(not(windows))]
fn listing_kind(_path: &Path) -> Option<PathKind> {
    None
}

#[cfg(windows)]
fn listing_kind(path: &Path) -> Option<PathKind> {
    let name = path.file_name()?.to_str()?;
    if name.is_empty() || name.ends_with('.') || name.ends_with(' ') {
        return None;
    }
    let parent = path.parent()?;
    if parent.as_os_str().is_empty() {
        return None;
    }
    if !path_kind(parent).is_dir {
        return Some(ABSENT);
    }
    let found = DIR_LISTING_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        let listing = cache
            .entry(parent.to_path_buf())
            .or_insert_with(|| read_listing(parent));
        listing
            .as_ref()
            .map(|entries| entries.get(&name.to_ascii_lowercase()).copied())
    })?;
    match found {
        None if name.is_ascii() && !name.contains('~') => Some(ABSENT),
        None => None,
        Some(None) => None,
        Some(Some(ft)) if ft.is_symlink() => None,
        Some(Some(ft)) => Some(PathKind {
            exists: true,
            is_dir: ft.is_dir(),
            is_file: ft.is_file(),
        }),
    }
}

#[cfg(windows)]
fn read_listing(dir: &Path) -> Option<HashMap<String, Option<std::fs::FileType>>> {
    DIR_LISTINGS.fetch_add(1, Ordering::Relaxed);
    let mut entries: HashMap<String, Option<std::fs::FileType>> = HashMap::new();
    for entry in std::fs::read_dir(dir).ok()? {
        let entry = entry.ok()?;
        let ft = entry.file_type().ok();
        let key = entry.file_name().to_string_lossy().to_ascii_lowercase();
        entries.entry(key).and_modify(|slot| *slot = None).or_insert(ft);
    }
    Some(entries)
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
    DIR_LISTING_CACHE.with(|cache| cache.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kind(p: &Path) -> (bool, bool, bool) {
        let k = path_kind(p);
        (k.exists, k.is_dir, k.is_file)
    }

    /// The memoized answer must equal an uncached `metadata` answer for every
    /// probe shape the resolver issues — present file/dir, absent name, child
    /// of an absent dir, child of a FILE, and a case-variant spelling.
    #[test]
    fn probe_answers_match_metadata() {
        clear_fs_probe_cache();
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        std::fs::create_dir(root.join("pkg")).unwrap();
        std::fs::write(root.join("pkg").join("mod.spl"), "").unwrap();
        let probes = [
            root.join("pkg"),
            root.join("pkg").join("mod.spl"),
            root.join("pkg").join("absent.spl"),
            root.join("missing").join("deeper").join("x.spl"),
            root.join("pkg").join("mod.spl").join("child.spl"),
            root.join("PKG").join("MOD.spl"),
        ];
        for p in &probes {
            let want = metadata_kind(p);
            assert_eq!(kind(p), (want.exists, want.is_dir, want.is_file), "{}", p.display());
        }
        clear_fs_probe_cache();
    }

    /// Off-Windows nothing changes: every miss is a real `metadata` call and
    /// no listing is read.
    #[cfg(not(windows))]
    #[test]
    fn non_windows_never_lists() {
        let tmp = tempfile::tempdir().unwrap();
        assert!(listing_kind(&tmp.path().join("a.spl")).is_none());
    }

    /// On Windows absent candidates under a listed directory, and every
    /// candidate under an absent directory, are answered without `metadata`.
    #[cfg(windows)]
    #[test]
    fn windows_answers_absent_candidates_from_listing() {
        clear_fs_probe_cache();
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("real.spl"), "").unwrap();
        for i in 0..20 {
            let k = listing_kind(&tmp.path().join(format!("absent_{i}.spl"))).expect("answered from listing");
            assert!(!k.exists);
            let k = listing_kind(&tmp.path().join("no_dir").join(format!("m{i}.spl"))).expect("absent parent");
            assert!(!k.exists);
        }
        let k = listing_kind(&tmp.path().join("REAL.SPL")).expect("case-folded hit");
        assert!(k.exists && k.is_file);
        // 8.3-style and non-ASCII misses are left to `metadata`.
        assert!(listing_kind(&tmp.path().join("REAL~1.SPL")).is_none());
        assert!(listing_kind(&tmp.path().join("\u{e9}t\u{e9}.spl")).is_none());
        clear_fs_probe_cache();
    }
}
