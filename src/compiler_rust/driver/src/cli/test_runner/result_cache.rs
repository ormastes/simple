//! File-level test result cache for incremental test runs.
//!
//! Skips re-running test files that haven't changed (same mtime+size AND
//! same source-tree stamp — see `source_tree_stamp`; bug
//! simple_test_default_runner_silent_vacuous_pass_2026-09-06 defect 2)
//! since the last successful run. Cache stored in `.simple/test-result-cache-rs.txt`.

use std::collections::HashMap;
use std::fs;
use std::path::{Component, Path, PathBuf};

const CACHE_PATH: &str = ".simple/test-result-cache-rs.txt";

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
}

impl ResultCache {
    pub fn load() -> Self {
        let mut entries: HashMap<String, CachedResult> = HashMap::new();
        if let Ok(content) = fs::read_to_string(CACHE_PATH) {
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
        ResultCache {
            entries,
            stamp: source_tree_stamp(Path::new("src"), std::env::current_exe().ok().as_deref()),
        }
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

    /// Save cache to disk.
    pub fn save(&self) {
        let _ = fs::create_dir_all(".simple");
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
        let _ = fs::write(CACHE_PATH, lines.join("\n") + "\n");
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
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
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
                stack.push(p);
            } else if matches!(p.extension().and_then(|e| e.to_str()), Some("spl") | Some("sdn")) {
                if let Ok(m) = ent.metadata() {
                    let (mt, sz) = meta_pair(&m);
                    files.push((p.to_string_lossy().replace('\\', "/"), mt, sz));
                }
            }
        }
    }
    let exe_meta = exe.and_then(|e| fs::metadata(e).ok());
    if files.is_empty() && exe_meta.is_none() {
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
    use super::{cache_key, source_tree_stamp};
    use std::path::Path;

    /// Repro for bug simple_test_default_runner_silent_vacuous_pass_2026-09-06
    /// defect 2: editing an IMPORTED module (spec file untouched) must change
    /// the cache stamp, so a stale PASS is not replayed.
    #[test]
    fn stamp_changes_when_imported_module_changes() {
        let dir = std::env::temp_dir().join(format!("rc_stamp_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("lib")).unwrap();
        std::fs::write(dir.join("lib/dep.spl"), "fn f() -> i64: 1\n").unwrap();
        let s1 = source_tree_stamp(&dir, None);
        assert_ne!(s1, 0);
        assert_eq!(s1, source_tree_stamp(&dir, None), "stamp must be deterministic");
        std::fs::write(dir.join("lib/dep.spl"), "fn f() -> i64: 22\n").unwrap();
        let s2 = source_tree_stamp(&dir, None);
        assert_ne!(s1, s2, "dependency edit must invalidate cached verdicts");
        std::fs::write(dir.join("lib/new.spl"), "\n").unwrap();
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

    #[test]
    fn cache_key_normalizes_repo_absolute_paths_to_relative() {
        let rel = Path::new("src/compiler_rust/driver/src/cli/test_runner/result_cache.rs");
        let abs = std::env::current_dir().unwrap().join(rel);

        assert_eq!(cache_key(rel), cache_key(&abs));
        assert!(cache_key(rel).contains('/'));
    }
}
