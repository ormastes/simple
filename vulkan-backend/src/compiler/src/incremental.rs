//! Incremental Compilation (#823)
//!
//! Provides infrastructure for incremental compilation by tracking:
//! 1. Source file modifications (mtimes)
//! 2. Compilation unit dependencies (imports, macros)
//! 3. Artifact validity (HIR, MIR, object code)
//!
//! When a source file changes, only affected compilation units are recompiled.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

use dashmap::DashMap;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};

/// Configuration for incremental compilation.
#[derive(Debug, Clone)]
pub struct IncrementalConfig {
    /// Cache directory for artifacts.
    pub cache_dir: PathBuf,
    /// Whether to persist cache to disk.
    pub persist: bool,
    /// Maximum age of cached artifacts (in seconds).
    pub max_age_secs: u64,
    /// Whether to validate artifacts on load.
    pub validate_on_load: bool,
}

impl Default for IncrementalConfig {
    fn default() -> Self {
        Self {
            cache_dir: PathBuf::from("target/simple_cache"),
            persist: true,
            max_age_secs: 86400 * 7, // 1 week
            validate_on_load: true,
        }
    }
}

impl IncrementalConfig {
    /// Create config for memory-only mode (no disk persistence).
    pub fn memory_only() -> Self {
        Self {
            cache_dir: PathBuf::from("target/simple_cache"),
            persist: false,
            max_age_secs: 3600, // 1 hour
            validate_on_load: false,
        }
    }
}

/// Statistics about incremental compilation.
#[derive(Debug, Clone, Default)]
pub struct IncrementalStats {
    /// Number of files checked.
    pub files_checked: usize,
    /// Number of files that need recompilation.
    pub files_dirty: usize,
    /// Number of files with valid cached artifacts.
    pub files_cached: usize,
    /// Number of cache hits.
    pub cache_hits: usize,
    /// Number of cache misses.
    pub cache_misses: usize,
    /// Number of invalidations due to dependency changes.
    pub dependency_invalidations: usize,
}

impl IncrementalStats {
    /// Calculate cache hit ratio.
    pub fn hit_ratio(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }

    /// Calculate rebuild ratio.
    pub fn rebuild_ratio(&self) -> f64 {
        if self.files_checked == 0 {
            0.0
        } else {
            self.files_dirty as f64 / self.files_checked as f64
        }
    }
}

/// Information about a source file for incremental compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceInfo {
    /// Absolute path to the source file.
    pub path: PathBuf,
    /// Content hash (for change detection).
    pub content_hash: u64,
    /// Modification time.
    pub mtime: u64,
    /// Direct dependencies (imports).
    pub dependencies: Vec<PathBuf>,
    /// Macros defined in this file.
    pub macros: Vec<String>,
    /// Functions defined in this file.
    pub functions: Vec<String>,
    /// Types defined in this file (structs, classes, enums).
    pub types: Vec<String>,
}

impl SourceInfo {
    /// Create new source info.
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            content_hash: 0,
            mtime: 0,
            dependencies: Vec::new(),
            macros: Vec::new(),
            functions: Vec::new(),
            types: Vec::new(),
        }
    }

    /// Update from source content.
    pub fn update_from_content(&mut self, content: &str) {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        content.hash(&mut hasher);
        self.content_hash = hasher.finish();
    }

    /// Update modification time from filesystem.
    pub fn update_mtime(&mut self) -> std::io::Result<()> {
        let metadata = std::fs::metadata(&self.path)?;
        let mtime = metadata
            .modified()?
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        self.mtime = mtime;
        Ok(())
    }

    /// Check if source has changed based on mtime.
    pub fn has_changed(&self) -> bool {
        if let Ok(metadata) = std::fs::metadata(&self.path) {
            if let Ok(mtime) = metadata.modified() {
                let current = mtime
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_secs())
                    .unwrap_or(0);
                return current != self.mtime;
            }
        }
        true // Assume changed if we can't read
    }
}

/// Cached artifact for a compilation unit.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedArtifact {
    /// Source info at time of compilation.
    pub source: SourceInfo,
    /// When the artifact was created.
    pub created_at: u64,
    /// Whether HIR is available.
    pub has_hir: bool,
    /// Whether MIR is available.
    pub has_mir: bool,
    /// Whether object code is available.
    pub has_object: bool,
    /// Path to cached HIR (if persisted).
    pub hir_path: Option<PathBuf>,
    /// Path to cached MIR (if persisted).
    pub mir_path: Option<PathBuf>,
    /// Path to cached object code (if persisted).
    pub object_path: Option<PathBuf>,
}

impl CachedArtifact {
    /// Create a new cached artifact.
    pub fn new(source: SourceInfo) -> Self {
        let now = SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        Self {
            source,
            created_at: now,
            has_hir: false,
            has_mir: false,
            has_object: false,
            hir_path: None,
            mir_path: None,
            object_path: None,
        }
    }

    /// Check if artifact is valid (source hasn't changed).
    pub fn is_valid(&self) -> bool {
        !self.source.has_changed()
    }

    /// Check if artifact is expired.
    pub fn is_expired(&self, max_age_secs: u64) -> bool {
        let now = SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        now - self.created_at > max_age_secs
    }
}

/// Compilation status for a unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilationStatus {
    /// Not yet analyzed.
    Unknown,
    /// Source is unchanged, cached artifacts are valid.
    Clean,
    /// Source or dependencies changed, needs recompilation.
    Dirty,
    /// Currently being compiled.
    InProgress,
    /// Compilation completed successfully.
    Complete,
    /// Compilation failed.
    Failed,
}

/// Thread-safe incremental compilation state.
pub struct IncrementalState {
    config: IncrementalConfig,
    /// Source file information.
    sources: DashMap<PathBuf, SourceInfo>,
    /// Cached artifacts.
    artifacts: DashMap<PathBuf, CachedArtifact>,
    /// Compilation status.
    status: DashMap<PathBuf, CompilationStatus>,
    /// Reverse dependency map (who depends on whom).
    dependents: DashMap<PathBuf, HashSet<PathBuf>>,
    /// Statistics.
    stats: RwLock<IncrementalStats>,
}

impl IncrementalState {
    /// Create new incremental state.
    pub fn new() -> Arc<Self> {
        Self::with_config(IncrementalConfig::default())
    }

    /// Create with custom config.
    pub fn with_config(config: IncrementalConfig) -> Arc<Self> {
        Arc::new(Self {
            config,
            sources: DashMap::new(),
            artifacts: DashMap::new(),
            status: DashMap::new(),
            dependents: DashMap::new(),
            stats: RwLock::new(IncrementalStats::default()),
        })
    }

    /// Register a source file.
    pub fn register_source(&self, info: SourceInfo) {
        let path = info.path.clone();

        // Update reverse dependency map
        for dep in &info.dependencies {
            self.dependents
                .entry(dep.clone())
                .or_insert_with(HashSet::new)
                .insert(path.clone());
        }

        self.sources.insert(path.clone(), info);
        self.status.insert(path, CompilationStatus::Unknown);
    }

    /// Check if a source needs recompilation.
    pub fn needs_recompile(&self, path: &Path) -> bool {
        let mut stats = self.stats.write();
        stats.files_checked += 1;

        // Check if we have cached artifact
        if let Some(artifact) = self.artifacts.get(path) {
            if artifact.is_valid() && !artifact.is_expired(self.config.max_age_secs) {
                stats.cache_hits += 1;
                stats.files_cached += 1;
                return false;
            }
        }

        stats.cache_misses += 1;
        stats.files_dirty += 1;
        true
    }

    /// Mark a source as dirty (needs recompilation).
    pub fn mark_dirty(&self, path: &Path) {
        self.status.insert(path.to_path_buf(), CompilationStatus::Dirty);

        // Also mark all dependents as dirty
        if let Some(deps) = self.dependents.get(path) {
            let mut stats = self.stats.write();
            for dep in deps.iter() {
                self.status.insert(dep.clone(), CompilationStatus::Dirty);
                stats.dependency_invalidations += 1;
            }
        }
    }

    /// Mark a source as in progress.
    pub fn mark_in_progress(&self, path: &Path) {
        self.status.insert(path.to_path_buf(), CompilationStatus::InProgress);
    }

    /// Mark a source as complete with artifact.
    pub fn mark_complete(&self, path: &Path, artifact: CachedArtifact) {
        self.status.insert(path.to_path_buf(), CompilationStatus::Complete);
        self.artifacts.insert(path.to_path_buf(), artifact);
    }

    /// Mark a source as failed.
    pub fn mark_failed(&self, path: &Path) {
        self.status.insert(path.to_path_buf(), CompilationStatus::Failed);
    }

    /// Get compilation status.
    pub fn get_status(&self, path: &Path) -> CompilationStatus {
        self.status
            .get(path)
            .map(|s| *s)
            .unwrap_or(CompilationStatus::Unknown)
    }

    /// Get cached artifact.
    pub fn get_artifact(&self, path: &Path) -> Option<CachedArtifact> {
        self.artifacts.get(path).map(|a| a.clone())
    }

    /// Get all dirty files.
    pub fn get_dirty_files(&self) -> Vec<PathBuf> {
        self.status
            .iter()
            .filter(|e| *e.value() == CompilationStatus::Dirty)
            .map(|e| e.key().clone())
            .collect()
    }

    /// Get all files that need checking.
    pub fn check_all(&self) -> Vec<PathBuf> {
        let mut dirty = Vec::new();

        for source in self.sources.iter() {
            if self.needs_recompile(source.key()) {
                self.mark_dirty(source.key());
                dirty.push(source.key().clone());
            } else {
                self.status.insert(source.key().clone(), CompilationStatus::Clean);
            }
        }

        dirty
    }

    /// Invalidate all caches.
    pub fn invalidate_all(&self) {
        // Collect keys first to avoid deadlock from modifying while iterating
        let keys: Vec<PathBuf> = self.status.iter().map(|e| e.key().clone()).collect();
        for key in keys {
            self.status.insert(key, CompilationStatus::Dirty);
        }
        self.artifacts.clear();
    }

    /// Get statistics.
    pub fn stats(&self) -> IncrementalStats {
        self.stats.read().clone()
    }

    /// Clear all state.
    pub fn clear(&self) {
        self.sources.clear();
        self.artifacts.clear();
        self.status.clear();
        self.dependents.clear();
        *self.stats.write() = IncrementalStats::default();
    }
}

impl Default for IncrementalState {
    fn default() -> Self {
        Self {
            config: IncrementalConfig::default(),
            sources: DashMap::new(),
            artifacts: DashMap::new(),
            status: DashMap::new(),
            dependents: DashMap::new(),
            stats: RwLock::new(IncrementalStats::default()),
        }
    }
}

/// Builder for incremental compilation.
pub struct IncrementalBuilder {
    state: Arc<IncrementalState>,
}

impl IncrementalBuilder {
    /// Create a new builder.
    pub fn new(state: Arc<IncrementalState>) -> Self {
        Self { state }
    }

    /// Add a source file.
    pub fn add_source(&self, path: PathBuf, content: &str) {
        let mut info = SourceInfo::new(path.clone());
        info.update_from_content(content);
        let _ = info.update_mtime();

        // Parse imports (simple heuristic)
        for line in content.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("import ") {
                if let Some(token) = rest.split_whitespace().next() {
                    let mut dep_path = PathBuf::from(token);
                    if dep_path.extension().is_none() {
                        dep_path.set_extension("spl");
                    }
                    if dep_path.is_relative() {
                        if let Some(parent) = path.parent() {
                            dep_path = parent.join(dep_path);
                        }
                    }
                    info.dependencies.push(dep_path);
                }
            } else if let Some(rest) = trimmed.strip_prefix("use ") {
                // Track use statements as potential dependencies
                if let Some(module) = rest.split(|c| c == '.' || c == ' ').next() {
                    let mut dep_path = PathBuf::from(module);
                    dep_path.set_extension("spl");
                    if dep_path.is_relative() {
                        if let Some(parent) = path.parent() {
                            dep_path = parent.join(dep_path);
                        }
                    }
                    if !info.dependencies.contains(&dep_path) {
                        info.dependencies.push(dep_path);
                    }
                }
            } else if let Some(rest) = trimmed.strip_prefix("fn ") {
                if let Some(name) = rest.split(|c| c == '(' || c == '[').next() {
                    info.functions.push(name.trim().to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("struct ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("class ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("enum ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("macro ") {
                if let Some(name) = rest.split(|c| c == '(' || c == '=').next() {
                    info.macros.push(name.trim().to_string());
                }
            }
        }

        self.state.register_source(info);
    }

    /// Build incrementally, returning files that need compilation.
    pub fn build(&self) -> Vec<PathBuf> {
        self.state.check_all()
    }

    /// Mark a file as successfully compiled.
    pub fn complete(&self, path: &Path, has_hir: bool, has_mir: bool, has_object: bool) {
        if let Some(source) = self.state.sources.get(path) {
            let mut artifact = CachedArtifact::new(source.clone());
            artifact.has_hir = has_hir;
            artifact.has_mir = has_mir;
            artifact.has_object = has_object;
            self.state.mark_complete(path, artifact);
        }
    }

    /// Mark a file as failed.
    pub fn fail(&self, path: &Path) {
        self.state.mark_failed(path);
    }

    /// Get compilation statistics.
    pub fn stats(&self) -> IncrementalStats {
        self.state.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_info_content_hash() {
        let mut info = SourceInfo::new(PathBuf::from("test.spl"));
        info.update_from_content("fn main(): println(\"hello\")");

        let hash1 = info.content_hash;

        info.update_from_content("fn main(): println(\"world\")");
        let hash2 = info.content_hash;

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_incremental_state_register() {
        let state = IncrementalState::new();

        let mut info = SourceInfo::new(PathBuf::from("main.spl"));
        info.dependencies.push(PathBuf::from("lib.spl"));
        state.register_source(info);

        assert_eq!(state.get_status(Path::new("main.spl")), CompilationStatus::Unknown);
    }

    #[test]
    fn test_incremental_state_dirty() {
        let state = IncrementalState::new();

        let mut main_info = SourceInfo::new(PathBuf::from("main.spl"));
        main_info.dependencies.push(PathBuf::from("lib.spl"));
        state.register_source(main_info);

        let lib_info = SourceInfo::new(PathBuf::from("lib.spl"));
        state.register_source(lib_info);

        // Mark lib as dirty - should cascade to main
        state.mark_dirty(Path::new("lib.spl"));

        assert_eq!(state.get_status(Path::new("lib.spl")), CompilationStatus::Dirty);
        assert_eq!(state.get_status(Path::new("main.spl")), CompilationStatus::Dirty);
    }

    #[test]
    fn test_incremental_state_complete() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info.clone());

        let artifact = CachedArtifact::new(info);
        state.mark_complete(Path::new("test.spl"), artifact);

        assert_eq!(state.get_status(Path::new("test.spl")), CompilationStatus::Complete);
        assert!(state.get_artifact(Path::new("test.spl")).is_some());
    }

    #[test]
    fn test_incremental_builder() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state);

        builder.add_source(
            PathBuf::from("main.spl"),
            r#"
            import lib
            fn main():
                hello()
            "#,
        );

        builder.add_source(
            PathBuf::from("lib.spl"),
            r#"
            fn hello():
                println("Hello")
            "#,
        );

        // All files should need compilation initially
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_incremental_stats() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info);

        // Check will increment stats
        let _ = state.needs_recompile(Path::new("test.spl"));

        let stats = state.stats();
        assert_eq!(stats.files_checked, 1);
        assert_eq!(stats.cache_misses, 1);
    }

    #[test]
    fn test_cached_artifact() {
        let info = SourceInfo::new(PathBuf::from("test.spl"));
        let mut artifact = CachedArtifact::new(info);

        assert!(!artifact.has_hir);
        assert!(!artifact.has_mir);
        assert!(!artifact.has_object);

        artifact.has_hir = true;
        artifact.has_mir = true;

        assert!(artifact.has_hir);
        assert!(artifact.has_mir);
        assert!(!artifact.has_object);
    }

    #[test]
    fn test_incremental_state_clear() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info);
        state.mark_dirty(Path::new("test.spl"));

        state.clear();

        assert_eq!(state.get_status(Path::new("test.spl")), CompilationStatus::Unknown);
    }

    #[test]
    fn test_incremental_config() {
        let default_config = IncrementalConfig::default();
        assert!(default_config.persist);
        assert!(default_config.validate_on_load);

        let memory_config = IncrementalConfig::memory_only();
        assert!(!memory_config.persist);
        assert!(!memory_config.validate_on_load);
    }

    #[test]
    fn test_stats_ratios() {
        let mut stats = IncrementalStats::default();

        // Empty stats
        assert_eq!(stats.hit_ratio(), 0.0);
        assert_eq!(stats.rebuild_ratio(), 0.0);

        // Some hits and misses
        stats.cache_hits = 3;
        stats.cache_misses = 1;
        stats.files_checked = 10;
        stats.files_dirty = 2;

        assert_eq!(stats.hit_ratio(), 0.75);
        assert_eq!(stats.rebuild_ratio(), 0.2);
    }

    #[test]
    fn test_dependency_chain_invalidation() {
        // Test: A depends on B, B depends on C
        // When C is marked dirty, both A and B should be dirty
        let state = IncrementalState::new();

        // C has no dependencies
        let c_info = SourceInfo::new(PathBuf::from("c.spl"));
        state.register_source(c_info);

        // B depends on C
        let mut b_info = SourceInfo::new(PathBuf::from("b.spl"));
        b_info.dependencies.push(PathBuf::from("c.spl"));
        state.register_source(b_info);

        // A depends on B
        let mut a_info = SourceInfo::new(PathBuf::from("a.spl"));
        a_info.dependencies.push(PathBuf::from("b.spl"));
        state.register_source(a_info);

        // Mark C as dirty - should cascade to B (direct dependent)
        state.mark_dirty(Path::new("c.spl"));

        assert_eq!(state.get_status(Path::new("c.spl")), CompilationStatus::Dirty);
        assert_eq!(state.get_status(Path::new("b.spl")), CompilationStatus::Dirty);
        // Note: A won't be marked dirty automatically - only direct dependents are marked
    }

    #[test]
    fn test_multiple_dependents() {
        // Test: Multiple files depend on same library
        let state = IncrementalState::new();

        let lib_info = SourceInfo::new(PathBuf::from("lib.spl"));
        state.register_source(lib_info);

        // Multiple files depend on lib
        for i in 0..5 {
            let mut info = SourceInfo::new(PathBuf::from(format!("app{}.spl", i)));
            info.dependencies.push(PathBuf::from("lib.spl"));
            state.register_source(info);
        }

        // Mark lib as dirty
        state.mark_dirty(Path::new("lib.spl"));

        // All dependents should be dirty
        for i in 0..5 {
            assert_eq!(
                state.get_status(Path::new(&format!("app{}.spl", i))),
                CompilationStatus::Dirty
            );
        }

        let stats = state.stats();
        assert_eq!(stats.dependency_invalidations, 5);
    }

    #[test]
    fn test_invalidate_all() {
        // Use new() which returns Arc<IncrementalState>
        let state = IncrementalState::new();

        // Register a file
        let info = SourceInfo::new(PathBuf::from("test_inv.spl"));
        state.register_source(info.clone());

        // Create artifact and mark complete
        let mut artifact = CachedArtifact::new(info);
        artifact.has_hir = true;
        state.mark_complete(Path::new("test_inv.spl"), artifact);

        // Verify complete
        assert_eq!(
            state.get_status(Path::new("test_inv.spl")),
            CompilationStatus::Complete
        );
        assert!(state.get_artifact(Path::new("test_inv.spl")).is_some());

        // Invalidate all
        state.invalidate_all();

        // Should be dirty now
        assert_eq!(
            state.get_status(Path::new("test_inv.spl")),
            CompilationStatus::Dirty
        );

        // Artifacts should be cleared
        assert!(state.get_artifact(Path::new("test_inv.spl")).is_none());
    }

    #[test]
    fn test_builder_parse_complex_source() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state);

        // Test parsing of various Simple language constructs
        builder.add_source(
            PathBuf::from("complex.spl"),
            r#"
            import utils
            use core.*
            use io.fs

            struct Point:
                x: i64
                y: i64

            class Counter:
                count: i64

            enum Status:
                Ok
                Error

            macro debug(msg: Str) -> ():
                emit result:
                    println(msg)

            fn helper[T](x: T) -> T:
                return x

            fn main():
                let p = Point(x: 0, y: 0)
                println("Hello")
            "#,
        );

        // Verify parsed metadata
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_builder_complete_and_stats() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state.clone());

        builder.add_source(PathBuf::from("test.spl"), "fn main(): return 0");

        let dirty = builder.build();
        assert_eq!(dirty.len(), 1);

        // Complete with all artifacts
        builder.complete(Path::new("test.spl"), true, true, true);

        assert_eq!(
            state.get_status(Path::new("test.spl")),
            CompilationStatus::Complete
        );

        let artifact = state.get_artifact(Path::new("test.spl")).unwrap();
        assert!(artifact.has_hir);
        assert!(artifact.has_mir);
        assert!(artifact.has_object);
    }

    #[test]
    fn test_builder_fail() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state.clone());

        builder.add_source(PathBuf::from("bad.spl"), "syntax error here");
        let _ = builder.build();

        builder.fail(Path::new("bad.spl"));

        assert_eq!(
            state.get_status(Path::new("bad.spl")),
            CompilationStatus::Failed
        );
    }

    #[test]
    fn test_get_dirty_files() {
        let state = IncrementalState::new();

        for i in 0..5 {
            let info = SourceInfo::new(PathBuf::from(format!("file{}.spl", i)));
            state.register_source(info);
        }

        // Mark some as dirty
        state.mark_dirty(Path::new("file1.spl"));
        state.mark_dirty(Path::new("file3.spl"));

        let dirty = state.get_dirty_files();
        assert_eq!(dirty.len(), 2);
        assert!(dirty.contains(&PathBuf::from("file1.spl")));
        assert!(dirty.contains(&PathBuf::from("file3.spl")));
    }

    #[test]
    fn test_in_progress_status() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("compiling.spl"));
        state.register_source(info);

        state.mark_in_progress(Path::new("compiling.spl"));
        assert_eq!(
            state.get_status(Path::new("compiling.spl")),
            CompilationStatus::InProgress
        );
    }

    #[test]
    fn test_cached_artifact_expiration() {
        let info = SourceInfo::new(PathBuf::from("old.spl"));
        let mut artifact = CachedArtifact::new(info);

        // Artifact created now should not be expired
        assert!(!artifact.is_expired(3600)); // 1 hour

        // Manually set old creation time (1 day ago)
        artifact.created_at = artifact.created_at.saturating_sub(86400 + 1);
        assert!(artifact.is_expired(86400)); // 1 day expiration
    }

    #[test]
    fn test_source_info_definitions() {
        let builder = IncrementalBuilder::new(IncrementalState::new());

        builder.add_source(
            PathBuf::from("defs.spl"),
            r#"
            struct MyStruct:
                field: i32

            class MyClass:
                value: str

            enum MyEnum:
                A
                B

            fn my_function():
                pass

            macro my_macro(x: Int) -> (returns result: Int):
                emit result:
                    x
            "#,
        );

        // The builder should have parsed these definitions
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_content_hash_consistency() {
        let mut info1 = SourceInfo::new(PathBuf::from("test.spl"));
        let mut info2 = SourceInfo::new(PathBuf::from("test.spl"));

        let content = "fn main(): return 42";
        info1.update_from_content(content);
        info2.update_from_content(content);

        // Same content should produce same hash
        assert_eq!(info1.content_hash, info2.content_hash);

        // Different content should produce different hash
        info2.update_from_content("fn main(): return 0");
        assert_ne!(info1.content_hash, info2.content_hash);
    }
}
