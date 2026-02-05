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
            cache_dir: PathBuf::from("rust/target/simple_cache"),
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
            cache_dir: PathBuf::from("rust/target/simple_cache"),
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
        self.status.get(path).map(|s| *s).unwrap_or(CompilationStatus::Unknown)
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

include!("incremental_builder.rs");
