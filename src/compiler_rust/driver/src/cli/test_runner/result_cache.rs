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
        let mut entries = HashMap::new();
        if let Ok(content) = fs::read_to_string(CACHE_PATH) {
            for line in content.lines() {
                if line.starts_with('#') || line.is_empty() {
                    continue;
                }
                let parts: Vec<&str> = line.splitn(6, '\t').collect();
                if parts.len() == 6 {
                    if let (Ok(mtime), Ok(size), Ok(passed), Ok(failed), Ok(skipped)) = (
                        parts[1].parse::<u64>(),
                        parts[2].parse::<u64>(),
                        parts[3].parse::<usize>(),
                        parts[4].parse::<usize>(),
                        parts[5].parse::<usize>(),
                    ) {
                        entries.insert(
                            parts[0].to_string(),
                            CachedResult { mtime, size, passed, failed, skipped, duration_ms: 0 },
                        );
                    }
                }
            }
        }
        ResultCache { entries }
    }

    /// Check if a test file is unchanged. Returns cached result if fresh.
    pub fn check(&self, path: &Path) -> Option<CachedResult> {
        let key = path.to_string_lossy().to_string();
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
    pub fn record(&mut self, path: &Path, passed: usize, failed: usize, skipped: usize) {
        let key = path.to_string_lossy().to_string();
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
                CachedResult { mtime, size, passed, failed, skipped, duration_ms: 0 },
            );
        }
    }

    /// Save cache to disk.
    pub fn save(&self) {
        let _ = fs::create_dir_all(".simple");
        let mut lines = Vec::with_capacity(self.entries.len() + 1);
        lines.push("# path\tmtime\tsize\tpassed\tfailed\tskipped".to_string());
        for (path, entry) in &self.entries {
            lines.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}",
                path, entry.mtime, entry.size, entry.passed, entry.failed, entry.skipped
            ));
        }
        let _ = fs::write(CACHE_PATH, lines.join("\n") + "\n");
    }
}
