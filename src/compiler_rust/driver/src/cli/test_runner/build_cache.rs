//! Build cache for compiled test artifacts.
//!
//! Provides hash-based caching of compiled test files (SMF and native binaries)
//! to avoid recompilation when source hasn't changed.

use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

use simple_compiler::CompilerPipeline;
use simple_compiler::linker::NativeBinaryOptions;

/// Cache directory for compiled test artifacts
const CACHE_DIR: &str = "target/test_cache";

/// Build cache for test compilation artifacts.
///
/// Uses interior mutability (`RefCell`) for hash and content caches so that
/// methods can populate them through `&self` references without requiring
/// callers to hold `&mut self`.
pub struct BuildCache {
    cache_dir: PathBuf,
    force_rebuild: bool,
    /// Per-path hash cache — avoids re-reading + re-hashing the same file.
    hash_cache: RefCell<HashMap<PathBuf, u64>>,
    /// Per-path content cache — lets compile_test_to_native reuse the bytes
    /// that source_hash already read instead of reading the file a second time.
    content_cache: RefCell<HashMap<PathBuf, Vec<u8>>>,
}

impl BuildCache {
    /// Create a new build cache.
    pub fn new(force_rebuild: bool) -> Self {
        let cache_dir = PathBuf::from(CACHE_DIR);
        if !cache_dir.exists() {
            let _ = fs::create_dir_all(&cache_dir);
        }
        Self {
            cache_dir,
            force_rebuild,
            hash_cache: RefCell::new(HashMap::new()),
            content_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Compute a hash for the source file content (cached).
    ///
    /// The first call for a given path reads the file and stores both the
    /// hash and the raw bytes.  Subsequent calls return the cached hash
    /// without any I/O.
    fn source_hash(&self, path: &Path) -> Option<u64> {
        // Fast path: already computed
        if let Some(&h) = self.hash_cache.borrow().get(path) {
            return Some(h);
        }
        // Slow path: read, hash, cache
        let content = fs::read(path).ok()?;
        let mut hasher = DefaultHasher::new();
        content.hash(&mut hasher);
        path.hash(&mut hasher);
        let hash = hasher.finish();
        self.hash_cache.borrow_mut().insert(path.to_path_buf(), hash);
        self.content_cache.borrow_mut().insert(path.to_path_buf(), content);
        Some(hash)
    }

    /// Get the cached artifact path for a source file with given extension.
    fn artifact_path(&self, source: &Path, ext: &str) -> Option<PathBuf> {
        let hash = self.source_hash(source)?;
        Some(self.cache_dir.join(format!("{:016x}.{}", hash, ext)))
    }

    /// Check if a source file needs to be rebuilt.
    pub fn needs_rebuild(&self, source: &Path, ext: &str) -> bool {
        if self.force_rebuild {
            return true;
        }
        match self.artifact_path(source, ext) {
            Some(artifact) => !artifact.exists(),
            None => true,
        }
    }

    /// Compute the cached SMF artifact path for a source file.
    pub fn smf_artifact_path(&self, source: &Path) -> Result<PathBuf, String> {
        self.artifact_path(source, "smf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))
    }

    /// Compile a test file to SMF format. Returns the path to the SMF artifact.
    pub fn compile_test_to_smf(&self, source: &Path) -> Result<PathBuf, String> {
        let output = self
            .artifact_path(source, "smf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))?;

        if !self.needs_rebuild(source, "smf") {
            return Ok(output);
        }

        let mut pipeline = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler pipeline: {}", e))?;

        // Enable test mode to activate SSpec DSL parsing
        pipeline.set_test_mode(true);

        pipeline
            .compile(source, &output)
            .map_err(|e| format!("Failed to compile {} to SMF: {}", source.display(), e))?;

        Ok(output)
    }

    /// Compile a test file to a native binary (ELF). Returns the path to the binary.
    pub fn compile_test_to_native(&self, source: &Path) -> Result<PathBuf, String> {
        let output = self
            .artifact_path(source, "elf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))?;

        if !self.needs_rebuild(source, "elf") {
            return Ok(output);
        }

        // Reuse file bytes already read by source_hash() when possible,
        // falling back to a fresh read only if the cache was not populated.
        let source_content = {
            let cache = self.content_cache.borrow();
            if let Some(bytes) = cache.get(source) {
                String::from_utf8(bytes.clone()).map_err(|e| format!("Invalid UTF-8 in {}: {}", source.display(), e))?
            } else {
                drop(cache);
                fs::read_to_string(source).map_err(|e| format!("Failed to read {}: {}", source.display(), e))?
            }
        };

        let mut pipeline = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler pipeline: {}", e))?;

        let options = NativeBinaryOptions::new();

        pipeline
            .compile_to_native_binary(&source_content, &output, Some(options))
            .map_err(|e| format!("Failed to compile {} to native binary: {}", source.display(), e))?;

        // Make executable on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(metadata) = fs::metadata(&output) {
                let mut perms = metadata.permissions();
                perms.set_mode(0o755);
                let _ = fs::set_permissions(&output, perms);
            }
        }

        Ok(output)
    }

    /// Clean the cache directory.
    pub fn clean(&self) -> Result<(), String> {
        if self.cache_dir.exists() {
            fs::remove_dir_all(&self.cache_dir).map_err(|e| format!("Failed to clean cache: {}", e))?;
            fs::create_dir_all(&self.cache_dir).map_err(|e| format!("Failed to recreate cache dir: {}", e))?;
        }
        Ok(())
    }

    /// Remove artifacts for a specific source file.
    pub fn invalidate(&self, source: &Path) {
        for ext in &["smf", "elf"] {
            if let Some(path) = self.artifact_path(source, ext) {
                let _ = fs::remove_file(path);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_hash_deterministic() {
        // Two calls with same path should produce same hash
        let path = Path::new("test/fixtures/sample.spl");
        let cache = BuildCache::new(false);
        let h1 = cache.source_hash(path);
        let h2 = cache.source_hash(path);
        // Both None if file doesn't exist, but they should match
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_needs_rebuild_force() {
        let cache = BuildCache::new(true);
        assert!(cache.needs_rebuild(Path::new("nonexistent.spl"), "smf"));
    }
}
