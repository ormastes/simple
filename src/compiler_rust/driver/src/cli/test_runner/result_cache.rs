//! File-level test result cache for incremental test runs.
//!
//! Skips re-running test files that haven't changed (same mtime+size AND
//! same source-tree stamp — see `source_tree_stamp`; bug
//! simple_test_default_runner_silent_vacuous_pass_2026-09-06 defect 2)
//! since the last successful run. Cache stored in `.simple/test-result-cache-rs.txt`.

use std::collections::HashMap;
use std::fs;
use std::path::{Component, Path, PathBuf};

const CACHE_REL: &str = ".simple/test-result-cache-rs.txt";

/// Env override for the repository root whose `src/` tree the cache stamp covers.
const SOURCE_ROOT_ENV: &str = "SIMPLE_SOURCE_ROOT";
/// Marker file proving a directory is the Simple repository root.
const ROOT_MARKER: &str = "release/version.sdn";

#[derive(Clone)]
pub struct CachedResult {
    pub mtime: u64,
    pub size: u64,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub duration_ms: u64,
    /// Stamp of everything the spec can import plus the runner binary.
    pub stamp: u64,
}

pub struct ResultCache {
    entries: HashMap<String, CachedResult>,
    stamp: u64,
    /// Where this cache is persisted (absolute, under the repo root).
    path: PathBuf,
}

/// Walk up from `start` to the repo root (the directory holding both `src/`
/// and `test/`). `None` means the stamp cannot be trusted, so the cache must
/// miss (fail closed) rather than stamp a cwd-relative, possibly empty tree.
fn find_repo_root(start: &Path) -> Option<PathBuf> {
    let mut cur = Some(start);
    while let Some(dir) = cur {
        if dir.join("src").is_dir() && dir.join("test").is_dir() {
            return Some(dir.to_path_buf());
        }
        cur = dir.parent();
    }
    None
}

impl ResultCache {
    /// `run_key` is every run input that can change a verdict (flags, mode,
    /// backend); it is folded into the stamp together with SIMPLE_* env vars.
    pub fn load(run_key: &str) -> Self {
        let root = resolve_source_root();
        let exe = std::env::current_exe().ok();
        Self::load_at(root.as_deref(), run_key, exe.as_deref())
    }

    fn load_at(root: Option<&Path>, run_key: &str, exe: Option<&Path>) -> Self {
        let path = match root {
            Some(r) => r.join(CACHE_REL),
            None => PathBuf::from(CACHE_REL),
        };
        let stamp = match root {
            Some(r) => run_stamp(r, run_key, &simple_env(), exe),
            None => 0,
        };
        let mut entries: HashMap<String, CachedResult> = HashMap::new();
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                if line.starts_with('#') || line.is_empty() {
                    continue;
                }
                let parts: Vec<&str> = line.splitn(8, '\t').collect();
                if parts.len() >= 6 {
                    if let (Ok(mtime), Ok(size), Ok(passed), Ok(failed), Ok(skipped)) = (
                        parts[1].parse::<u64>(),
                        parts[2].parse::<u64>(),
                        parts[3].parse::<usize>(),
                        parts[4].parse::<usize>(),
                        parts[5].parse::<usize>(),
                    ) {
                        let duration_ms = if parts.len() >= 7 {
                            parts[6].parse::<u64>().unwrap_or(0)
                        } else {
                            0
                        };
                        // Legacy rows (no stamp column) parse as 0 and never match.
                        let stamp = parts.get(7).and_then(|s| s.parse::<u64>().ok()).unwrap_or(0);
                        let key = cache_key(Path::new(parts[0]));
                        let result = CachedResult {
                            mtime,
                            size,
                            passed,
                            failed,
                            skipped,
                            duration_ms,
                            stamp,
                        };
                        match entries.get(&key) {
                            Some(existing)
                                if existing.mtime > result.mtime
                                    || (existing.mtime == result.mtime
                                        && existing.size == result.size
                                        && existing.duration_ms <= result.duration_ms) => {}
                            _ => {
                                entries.insert(key, result);
                            }
                        }
                    }
                }
            }
        }
        ResultCache { entries, stamp, path }
    }

    /// Check if a test file is unchanged. Returns cached result if fresh.
    pub fn check(&self, path: &Path) -> Option<CachedResult> {
        let key = cache_key(path);
        let entry = self.entries.get(&key)?;

        let meta = fs::metadata(path).ok()?;
        let size = meta.len();
        let mtime = meta
            .modified()
            .ok()?
            .duration_since(std::time::UNIX_EPOCH)
            .ok()?
            .as_secs();

        if entry.mtime == mtime && entry.size == size && entry.stamp == self.stamp && self.stamp != 0 {
            Some(entry.clone())
        } else {
            None
        }
    }

    /// Record a test result for caching.
    pub fn record(&mut self, path: &Path, passed: usize, failed: usize, skipped: usize, duration_ms: u64) {
        let key = cache_key(path);
        if let Ok(meta) = fs::metadata(path) {
            let size = meta.len();
            let mtime = meta
                .modified()
                .ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map(|d| d.as_secs())
                .unwrap_or(0);
            self.entries.insert(
                key,
                CachedResult {
                    mtime,
                    size,
                    passed,
                    failed,
                    skipped,
                    duration_ms,
                    stamp: self.stamp,
                },
            );
        }
    }

    /// Save cache to disk atomically: write a uniquely-named temp file in the
    /// same directory, then rename it over the cache. Concurrent runners can
    /// lose each other's rows (last writer wins) but never tear the file.
    pub fn save(&self) {
        if let Some(dir) = self.path.parent() {
            let _ = fs::create_dir_all(dir);
        }
        let mut lines = Vec::with_capacity(self.entries.len() + 1);
        lines.push("# path\tmtime\tsize\tpassed\tfailed\tskipped\tduration_ms\tstamp".to_string());
        for (path, entry) in &self.entries {
            lines.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                path,
                entry.mtime,
                entry.size,
                entry.passed,
                entry.failed,
                entry.skipped,
                entry.duration_ms,
                entry.stamp
            ));
        }
        let tmp = self.path.with_extension(
            format!("txt.tmp.{}.{:?}", std::process::id(), std::thread::current().id())
                .replace(|c: char| !c.is_ascii_alphanumeric() && c != '.', "_"),
        );
        if fs::write(&tmp, lines.join("\n") + "\n").is_err() || fs::rename(&tmp, &self.path).is_err() {
            let _ = fs::remove_file(&tmp);
        }
    }
}

/// Sorted SIMPLE_* environment variables (they select modes/backends).
fn simple_env() -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> = std::env::vars().filter(|(k, _)| k.starts_with("SIMPLE_")).collect();
    v.sort();
    v
}

/// Full stamp for one run: source + test trees under the repo root, the
/// runner exe, the run flags and the SIMPLE_* environment.
fn run_stamp(root: &Path, run_key: &str, env: &[(String, String)], exe: Option<&Path>) -> u64 {
    let base = source_tree_stamp(root, exe);
    if base == 0 {
        return 0;
    }
    let mut h = base;
    let mut mix = |bytes: &[u8]| {
        for b in bytes {
            h ^= *b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    };
    mix(b"run");
    mix(run_key.as_bytes());
    for (k, v) in env {
        mix(k.as_bytes());
        mix(b"=");
        mix(v.as_bytes());
        mix(b"\0");
    }
    if h == 0 {
        1
    } else {
        h
    }
}

/// Conservative stamp of a spec's whole possible import closure.
///
/// A spec's verdict depends on every module it (transitively) imports and on
/// the runner binary, not just the spec file. Resolving the exact closure
/// would need the module resolver, so instead fold (path, mtime, size) of
/// every `.spl`/`.sdn` under `root` plus the runner exe's (mtime, size) into
/// an FNV-1a hash. Any source or runner change therefore invalidates every
/// cached verdict — correct (no stale PASS), merely less incremental.
/// Returns 0 (never matches) if nothing could be stamped.
fn source_tree_stamp(root: &Path, exe: Option<&Path>) -> u64 {
    fn mix(h: &mut u64, bytes: &[u8]) {
        for b in bytes {
            *h ^= *b as u64;
            *h = h.wrapping_mul(0x100000001b3);
        }
    }
    fn meta_pair(m: &fs::Metadata) -> (u64, u64) {
        let mt = m
            .modified()
            .ok()
            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        (mt, m.len())
    }
    let mut files: Vec<(String, u64, u64)> = Vec::new();
    // src/: importable modules + data/scripts; test/: EVERY file (helpers,
    // fixtures, golden data the specs read). Both resolved from the repo root.
    let mut stack = vec![(root.join("src"), false), (root.join("test"), true)];
    while let Some((dir, all_files)) = stack.pop() {
        let Ok(rd) = fs::read_dir(&dir) else { continue };
        for ent in rd.flatten() {
            let p = ent.path();
            let Ok(ft) = ent.file_type() else { continue };
            if ft.is_dir() {
                let name = ent.file_name();
                // Rust seed + vendored trees hold no importable Simple modules.
                if name == "compiler_rust" || name == "vendor" || name == "target" {
                    continue;
                }
                stack.push((p, all_files));
            } else if all_files
                || matches!(
                    p.extension().and_then(|e| e.to_str()),
                    Some("spl") | Some("sdn") | Some("shs")
                )
            {
                if let Ok(m) = ent.metadata() {
                    let (mt, sz) = meta_pair(&m);
                    files.push((p.to_string_lossy().replace('\\', "/"), mt, sz));
                }
            }
        }
    }
    let exe_meta = exe.and_then(|e| fs::metadata(e).ok());
    if files.is_empty() {
        return 0;
    }
    files.sort();
    let mut h: u64 = 0xcbf29ce484222325;
    for (p, mt, sz) in &files {
        mix(&mut h, p.as_bytes());
        mix(&mut h, &mt.to_le_bytes());
        mix(&mut h, &sz.to_le_bytes());
    }
    if let Some(m) = exe_meta {
        let (mt, sz) = meta_pair(&m);
        mix(&mut h, b"exe");
        mix(&mut h, &mt.to_le_bytes());
        mix(&mut h, &sz.to_le_bytes());
    }
    if h == 0 {
        1
    } else {
        h
    }
}

/// Resolve the repository root whose `src/` tree the cache stamp covers.
///
/// The stamp must not depend on the process cwd (OPUS-REVIEW, PR #7949):
/// running the test runner from any directory must still stamp the real
/// source tree, otherwise source edits never invalidate cached verdicts and
/// a stale PASS can be served. Resolution order: `SIMPLE_SOURCE_ROOT` env
/// override (only if it carries the root marker), then walking up from the cwd.
/// Returns `None` when no root is found; callers must treat that as "never
/// serve cached results".
fn resolve_source_root() -> Option<PathBuf> {
    let is_valid_root =
        |dir: &Path| dir.join(ROOT_MARKER).is_file() && dir.join("src").is_dir() && dir.join("test").is_dir();
    if let Ok(override_root) = std::env::var(SOURCE_ROOT_ENV) {
        let dir = PathBuf::from(override_root);
        if is_valid_root(&dir) {
            return Some(dir);
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        return find_repo_root(&cwd);
    }
    None
}

fn cache_key(path: &Path) -> String {
    let normalized = normalize_path(path);
    normalized.to_string_lossy().replace('\\', "/")
}

fn normalize_path(path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else if let Ok(cwd) = std::env::current_dir() {
        cwd.join(path)
    } else {
        return path.to_path_buf();
    };

    let normalized = normalize_lexically(&absolute);
    if let Ok(cwd) = std::env::current_dir() {
        let normalized_cwd = normalize_lexically(&cwd);
        if let Ok(stripped) = normalized.strip_prefix(&normalized_cwd) {
            return stripped.to_path_buf();
        }
    }
    normalized
}

fn normalize_lexically(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            _ => out.push(component.as_os_str()),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{cache_key, find_repo_root, run_stamp, source_tree_stamp, ResultCache, CACHE_REL, SOURCE_ROOT_ENV};
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;

    static CWD_LOCK: Mutex<()> = Mutex::new(());

    fn lock_cwd() -> std::sync::MutexGuard<'static, ()> {
        CWD_LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn fresh_repo(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("rc_{}_{}", tag, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src/lib")).unwrap();
        std::fs::create_dir_all(dir.join("test/fixtures")).unwrap();
        std::fs::write(dir.join("src/lib/dep.spl"), "fn f() -> i64: 1\n").unwrap();
        std::fs::write(dir.join("test/fixtures/golden.txt"), "a\n").unwrap();
        dir
    }

    /// Repro for bug simple_test_default_runner_silent_vacuous_pass_2026-09-06
    /// defect 2: editing an IMPORTED module (spec file untouched) must change
    /// the cache stamp, so a stale PASS is not replayed.
    #[test]
    fn stamp_changes_when_imported_module_changes() {
        let dir = fresh_repo("dep");
        let s1 = source_tree_stamp(&dir, None);
        assert_ne!(s1, 0);
        assert_eq!(s1, source_tree_stamp(&dir, None), "stamp must be deterministic");
        std::fs::write(dir.join("src/lib/dep.spl"), "fn f() -> i64: 22\n").unwrap();
        let s2 = source_tree_stamp(&dir, None);
        assert_ne!(s1, s2, "dependency edit must invalidate cached verdicts");
        std::fs::write(dir.join("src/lib/new.spl"), "\n").unwrap();
        assert_ne!(s2, source_tree_stamp(&dir, None), "new module must invalidate");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn empty_tree_without_exe_never_matches() {
        let dir = std::env::temp_dir().join(format!("rc_stamp_empty_{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        assert_eq!(source_tree_stamp(&dir, None), 0);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// PR #7949 review (1): the stamp was taken over a cwd-relative `src/`.
    /// Outside a repo the cache must miss (stamp 0) even with a runner exe,
    /// and inside one the root is found from any subdirectory.
    #[test]
    fn stamp_is_repo_rooted_and_fails_closed_outside_repo() {
        let dir = fresh_repo("root");
        assert_eq!(
            find_repo_root(&dir.join("test/fixtures")).as_deref(),
            Some(dir.as_path())
        );
        let outside = std::env::temp_dir().join(format!("rc_outside_{}", std::process::id()));
        std::fs::create_dir_all(&outside).unwrap();
        let exe = std::env::current_exe().unwrap();
        // A tree with no src/test must never yield a usable stamp, even with an exe.
        assert_eq!(source_tree_stamp(&outside, Some(&exe)), 0);
        let cache = ResultCache::load_at(None, "k", Some(&exe));
        assert_eq!(cache.stamp, 0, "no repo root => cache must miss");
        let _ = std::fs::remove_dir_all(&dir);
        let _ = std::fs::remove_dir_all(&outside);
    }

    /// PR #7949 review (2): test/** helpers and fixtures must be stamped.
    #[test]
    fn stamp_changes_when_test_fixture_changes() {
        let dir = fresh_repo("fixture");
        let s1 = source_tree_stamp(&dir, None);
        std::fs::write(dir.join("test/fixtures/golden.txt"), "changed\n").unwrap();
        assert_ne!(s1, source_tree_stamp(&dir, None), "test fixture edit must invalidate");
        let s2 = source_tree_stamp(&dir, None);
        std::fs::write(dir.join("test/fixtures/helper.spl"), "\n").unwrap();
        assert_ne!(s2, source_tree_stamp(&dir, None), "new test helper must invalidate");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// PR #7949 review (3): flags/mode/backend and SIMPLE_* env are in the key.
    #[test]
    fn stamp_changes_with_run_flags_and_env() {
        let dir = fresh_repo("flags");
        let a = run_stamp(&dir, "mode=Interpreter", &[], None);
        assert_ne!(a, 0);
        assert_eq!(a, run_stamp(&dir, "mode=Interpreter", &[], None));
        assert_ne!(a, run_stamp(&dir, "mode=Native", &[], None), "mode must be keyed");
        let env = vec![("SIMPLE_BACKEND".to_string(), "llvm".to_string())];
        assert_ne!(a, run_stamp(&dir, "mode=Interpreter", &env, None), "env must be keyed");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// PR #7949 review (4): the save must be atomic (temp + rename). With a
    /// truncate-then-write save a concurrent reader observes a torn/empty file.
    #[test]
    fn save_is_atomic_under_concurrent_readers() {
        let dir = fresh_repo("atomic");
        let mut cache = ResultCache::load_at(Some(&dir), "k", None);
        for i in 0..400 {
            let p = dir.join(format!("test/fixtures/s{i}.spl"));
            std::fs::write(&p, "x\n").unwrap();
            cache.record(&p, 1, 0, 0, 1);
        }
        cache.save();
        let path = dir.join(CACHE_REL);
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let s2 = stop.clone();
        let writer = std::thread::spawn(move || {
            while !s2.load(std::sync::atomic::Ordering::Relaxed) {
                cache.save();
            }
        });
        let mut torn = 0;
        for _ in 0..3000 {
            match std::fs::read_to_string(&path) {
                Ok(s) if s.lines().count() == 401 && s.ends_with('\n') => {}
                Ok(_) => torn += 1,
                Err(_) => torn += 1,
            }
        }
        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        writer.join().unwrap();
        assert_eq!(torn, 0, "reader observed a torn cache file");
        let leftovers = std::fs::read_dir(dir.join(".simple"))
            .unwrap()
            .flatten()
            .filter(|e| e.file_name().to_string_lossy().contains(".tmp."))
            .count();
        assert_eq!(leftovers, 0, "temp files must be renamed into place");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn cache_key_normalizes_repo_absolute_paths_to_relative() {
        let _g = lock_cwd();
        let rel = Path::new("src/compiler_rust/driver/src/cli/test_runner/result_cache.rs");
        let abs = std::env::current_dir().unwrap().join(rel);

        assert_eq!(cache_key(rel), cache_key(&abs));
        assert!(cache_key(rel).contains('/'));
    }

    /// Repro for OPUS-REVIEW on PR #7949: `ResultCache::load` stamped
    /// `Path::new("src")` relative to the cwd, so running from a directory
    /// with no `./src` made the stamp depend only on the runner exe — source
    /// edits never invalidated, and a stale PASS could be served. The stamp
    /// must be computed from a cwd-independent source root.
    #[test]
    fn stamp_invalidates_source_edit_from_foreign_cwd() {
        let _g = lock_cwd();
        let tmp = std::env::temp_dir().join(format!("rc_cwd_{}", std::process::id()));
        let fake_root = tmp.join("repo");
        let foreign = tmp.join("elsewhere");
        std::fs::create_dir_all(fake_root.join("src")).unwrap();
        std::fs::create_dir_all(fake_root.join("test")).unwrap();
        std::fs::create_dir_all(fake_root.join("release")).unwrap();
        std::fs::create_dir_all(&foreign).unwrap();
        std::fs::write(fake_root.join("release/version.sdn"), "version: 0.0.0\n").unwrap();
        std::fs::write(fake_root.join("src/a.spl"), "fn a() -> i64: 1\n").unwrap();
        let had_override = std::env::var_os(SOURCE_ROOT_ENV);
        std::env::set_var(SOURCE_ROOT_ENV, &fake_root);
        let orig = std::env::current_dir().unwrap();
        std::env::set_current_dir(&foreign).unwrap();
        let c1 = ResultCache::load("test");
        assert_ne!(c1.stamp, 0, "stamp must cover the source tree from any cwd");
        std::fs::write(fake_root.join("src/a.spl"), "fn a() -> i64: 2\n").unwrap();
        let c2 = ResultCache::load("test");
        std::env::set_current_dir(&orig).unwrap();
        match had_override {
            Some(v) => std::env::set_var(SOURCE_ROOT_ENV, v),
            None => std::env::remove_var(SOURCE_ROOT_ENV),
        }
        let _ = std::fs::remove_dir_all(&tmp);
        assert_ne!(
            c1.stamp, c2.stamp,
            "source edit must invalidate the stamp even when run from a foreign cwd (stale PASS otherwise)"
        );
    }

    /// The resolved source root must not depend on the process cwd. Uses the
    /// `SIMPLE_SOURCE_ROOT` override so the assertion holds no matter where
    /// the test binary itself lives (it may be outside the repo, e.g. under
    /// a scratch CARGO_TARGET_DIR).
    #[test]
    fn source_root_resolution_is_cwd_independent() {
        let _g = lock_cwd();
        let tmp = std::env::temp_dir().join(format!("rc_root_{}", std::process::id()));
        let fake_root = tmp.join("repo");
        let foreign = tmp.join("elsewhere");
        std::fs::create_dir_all(fake_root.join("src")).unwrap();
        std::fs::create_dir_all(fake_root.join("test")).unwrap();
        std::fs::create_dir_all(fake_root.join("release")).unwrap();
        std::fs::create_dir_all(&foreign).unwrap();
        std::fs::write(fake_root.join("release/version.sdn"), "version: 0.0.0\n").unwrap();
        let had_override = std::env::var_os(SOURCE_ROOT_ENV);
        std::env::set_var(SOURCE_ROOT_ENV, &fake_root);
        let orig = std::env::current_dir().unwrap();
        std::env::set_current_dir(&foreign).unwrap();
        let resolved = super::resolve_source_root();
        std::env::set_current_dir(&orig).unwrap();
        match had_override {
            Some(v) => std::env::set_var(SOURCE_ROOT_ENV, v),
            None => std::env::remove_var(SOURCE_ROOT_ENV),
        }
        let _ = std::fs::remove_dir_all(&tmp);
        assert_eq!(
            resolved.as_deref(),
            Some(fake_root.as_path()),
            "source root must resolve identically from a foreign cwd"
        );
    }

    /// Default resolution (no env override) must still find the real repo
    /// root from the normal test cwd.
    #[test]
    fn source_root_resolution_finds_real_root_without_override() {
        let _g = lock_cwd();
        let had_override = std::env::var_os(SOURCE_ROOT_ENV);
        std::env::remove_var(SOURCE_ROOT_ENV);
        let root = super::resolve_source_root().expect("must resolve the real repo root");
        match had_override {
            Some(v) => std::env::set_var(SOURCE_ROOT_ENV, v),
            None => std::env::remove_var(SOURCE_ROOT_ENV),
        }
        assert!(root.join("src").is_dir(), "resolved root must contain src/");
    }
}
