//! File-level test result cache for incremental test runs.
//!
//! Skips re-running test files that haven't changed (same mtime+size)
//! since the last successful run. Cache stored in `.simple/test-result-cache-rs.txt`.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

const CACHE_PATH: &str = ".simple/test-result-cache-rs.txt";

#[derive(Clone)]
pub struct CachedResult {
    pub mtime: u64,
    pub size: u64,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub duration_ms: u64,
}

pub struct ResultCache {
    entries: HashMap<String, CachedResult>,
}

impl ResultCache {
    pub fn load() -> Self {
        let mut entries: HashMap<String, CachedResult> = HashMap::new();
        if let Ok(content) = fs::read_to_string(CACHE_PATH) {
            for line in content.lines() {
                if line.starts_with('#') || line.is_empty() {
                    continue;
                }
                let parts: Vec<&str> = line.splitn(7, '\t').collect();
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
                        let key = cache_key(Path::new(parts[0]));
                        let result = CachedResult {
                            mtime,
                            size,
                            passed,
                            failed,
                            skipped,
                            duration_ms,
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
        ResultCache { entries }
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

        if entry.mtime == mtime && entry.size == size {
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
                },
            );
        }
    }

    /// Save cache to disk.
    pub fn save(&self) {
        let _ = fs::create_dir_all(".simple");
        let mut lines = Vec::with_capacity(self.entries.len() + 1);
        lines.push("# path\tmtime\tsize\tpassed\tfailed\tskipped\tduration_ms".to_string());
        for (path, entry) in &self.entries {
            lines.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                path, entry.mtime, entry.size, entry.passed, entry.failed, entry.skipped, entry.duration_ms
            ));
        }
        let _ = fs::write(CACHE_PATH, lines.join("\n") + "\n");
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

    let canonical = absolute.canonicalize().unwrap_or(absolute);
    if let Ok(cwd) = std::env::current_dir() {
        let canonical_cwd = cwd.canonicalize().unwrap_or(cwd);
        if let Ok(stripped) = canonical.strip_prefix(&canonical_cwd) {
            return stripped.to_path_buf();
        }
    }
    canonical
}

#[cfg(test)]
mod tests {
    use super::cache_key;
    use std::path::Path;

    #[test]
    fn cache_key_normalizes_repo_absolute_paths_to_relative() {
        let rel = Path::new("src/compiler_rust/driver/src/cli/test_runner/result_cache.rs");
        let abs = std::env::current_dir().unwrap().join(rel);

        assert_eq!(cache_key(rel), cache_key(&abs));
        assert!(cache_key(rel).contains('/'));
    }
}
