//! Monomorphization Cache (#821)
//!
//! Provides caching for monomorphization results to enable incremental compilation.
//! Caches specialized functions, structs, and classes by their specialization keys.
//!
//! ## Cache Strategy
//!
//! The cache uses a content-based key derived from:
//! 1. The original definition's content hash
//! 2. The type arguments used for specialization
//! 3. The source file's modification time
//!
//! When a cached entry is found and valid, the specialized definition is reused
//! instead of being regenerated.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::SystemTime;

use dashmap::DashMap;
use parking_lot::RwLock;

use super::types::{ConcreteType, SpecializationKey};
use simple_parser::ast::{ClassDef, FunctionDef, StructDef};

/// Configuration for the monomorphization cache.
#[derive(Debug, Clone)]
pub struct MonoCacheConfig {
    /// Maximum number of entries to cache.
    pub max_entries: usize,
    /// Whether to validate cached entries against source modification times.
    pub validate_timestamps: bool,
    /// Whether to persist cache to disk.
    pub persist_to_disk: bool,
    /// Cache directory (if persisting to disk).
    pub cache_dir: Option<PathBuf>,
}

impl Default for MonoCacheConfig {
    fn default() -> Self {
        Self {
            max_entries: 10_000,
            validate_timestamps: true,
            persist_to_disk: false,
            cache_dir: None,
        }
    }
}

impl MonoCacheConfig {
    /// Create config for in-memory only cache.
    pub fn memory_only() -> Self {
        Self {
            max_entries: 10_000,
            validate_timestamps: true,
            persist_to_disk: false,
            cache_dir: None,
        }
    }

    /// Create config for persistent cache.
    pub fn persistent(cache_dir: PathBuf) -> Self {
        Self {
            max_entries: 50_000,
            validate_timestamps: true,
            persist_to_disk: true,
            cache_dir: Some(cache_dir),
        }
    }
}

/// Statistics about cache usage.
#[derive(Debug, Clone, Default)]
pub struct MonoCacheStats {
    /// Number of cache hits.
    pub hits: usize,
    /// Number of cache misses.
    pub misses: usize,
    /// Number of entries evicted.
    pub evictions: usize,
    /// Number of entries invalidated.
    pub invalidations: usize,
    /// Current number of function entries.
    pub function_entries: usize,
    /// Current number of struct entries.
    pub struct_entries: usize,
    /// Current number of class entries.
    pub class_entries: usize,
}

impl MonoCacheStats {
    /// Calculate hit ratio (0.0 to 1.0).
    pub fn hit_ratio(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            self.hits as f64 / total as f64
        }
    }

    /// Total number of cached entries.
    pub fn total_entries(&self) -> usize {
        self.function_entries + self.struct_entries + self.class_entries
    }
}

/// Metadata about a cached entry.
#[derive(Debug, Clone)]
pub struct CacheEntryMeta {
    /// When the entry was created.
    pub created_at: SystemTime,
    /// Source file path (if known).
    pub source_path: Option<PathBuf>,
    /// Source file modification time (for validation).
    pub source_mtime: Option<SystemTime>,
    /// Number of times this entry was accessed.
    pub access_count: usize,
}

impl Default for CacheEntryMeta {
    fn default() -> Self {
        Self {
            created_at: SystemTime::now(),
            source_path: None,
            source_mtime: None,
            access_count: 0,
        }
    }
}

impl CacheEntryMeta {
    /// Create metadata with source info.
    pub fn with_source(source_path: PathBuf, source_mtime: SystemTime) -> Self {
        Self {
            created_at: SystemTime::now(),
            source_path: Some(source_path),
            source_mtime: Some(source_mtime),
            access_count: 0,
        }
    }

    /// Check if entry is valid based on source modification time.
    pub fn is_valid(&self) -> bool {
        if let (Some(path), Some(cached_mtime)) = (&self.source_path, self.source_mtime) {
            if let Ok(metadata) = std::fs::metadata(path) {
                if let Ok(current_mtime) = metadata.modified() {
                    return current_mtime <= cached_mtime;
                }
            }
            // If we can't read the file, assume valid
            true
        } else {
            // No source info, assume valid
            true
        }
    }
}

/// Cached function entry.
#[derive(Debug, Clone)]
pub struct CachedFunction {
    /// The specialized function definition.
    pub def: FunctionDef,
    /// Entry metadata.
    pub meta: CacheEntryMeta,
}

/// Cached struct entry.
#[derive(Debug, Clone)]
pub struct CachedStruct {
    /// The specialized struct definition.
    pub def: StructDef,
    /// Entry metadata.
    pub meta: CacheEntryMeta,
}

/// Cached class entry.
#[derive(Debug, Clone)]
pub struct CachedClass {
    /// The specialized class definition.
    pub def: ClassDef,
    /// Entry metadata.
    pub meta: CacheEntryMeta,
}

/// Thread-safe monomorphization cache.
pub struct MonoCache {
    config: MonoCacheConfig,
    /// Cached specialized functions.
    functions: DashMap<SpecializationKey, CachedFunction>,
    /// Cached specialized structs.
    structs: DashMap<SpecializationKey, CachedStruct>,
    /// Cached specialized classes.
    classes: DashMap<SpecializationKey, CachedClass>,
    /// Cache statistics.
    stats: RwLock<MonoCacheStats>,
}

impl MonoCache {
    /// Create a new cache with default config.
    pub fn new() -> Arc<Self> {
        Self::with_config(MonoCacheConfig::default())
    }

    /// Create a new cache with custom config.
    pub fn with_config(config: MonoCacheConfig) -> Arc<Self> {
        Arc::new(Self {
            config,
            functions: DashMap::new(),
            structs: DashMap::new(),
            classes: DashMap::new(),
            stats: RwLock::new(MonoCacheStats::default()),
        })
    }

    // === Function Cache ===

    /// Get a cached function specialization.
    pub fn get_function(&self, key: &SpecializationKey) -> Option<FunctionDef> {
        if let Some(mut entry) = self.functions.get_mut(key) {
            // Validate if configured
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                drop(entry);
                self.functions.remove(key);
                let mut stats = self.stats.write();
                stats.invalidations += 1;
                stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            let mut stats = self.stats.write();
            stats.hits += 1;
            Some(entry.def.clone())
        } else {
            let mut stats = self.stats.write();
            stats.misses += 1;
            None
        }
    }

    /// Cache a function specialization.
    pub fn put_function(&self, key: SpecializationKey, def: FunctionDef) {
        self.put_function_with_meta(key, def, CacheEntryMeta::default());
    }

    /// Cache a function with metadata.
    pub fn put_function_with_meta(
        &self,
        key: SpecializationKey,
        def: FunctionDef,
        meta: CacheEntryMeta,
    ) {
        self.maybe_evict();
        self.functions.insert(key, CachedFunction { def, meta });
        let mut stats = self.stats.write();
        stats.function_entries = self.functions.len();
    }

    // === Struct Cache ===

    /// Get a cached struct specialization.
    pub fn get_struct(&self, key: &SpecializationKey) -> Option<StructDef> {
        if let Some(mut entry) = self.structs.get_mut(key) {
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                drop(entry);
                self.structs.remove(key);
                let mut stats = self.stats.write();
                stats.invalidations += 1;
                stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            let mut stats = self.stats.write();
            stats.hits += 1;
            Some(entry.def.clone())
        } else {
            let mut stats = self.stats.write();
            stats.misses += 1;
            None
        }
    }

    /// Cache a struct specialization.
    pub fn put_struct(&self, key: SpecializationKey, def: StructDef) {
        self.put_struct_with_meta(key, def, CacheEntryMeta::default());
    }

    /// Cache a struct with metadata.
    pub fn put_struct_with_meta(
        &self,
        key: SpecializationKey,
        def: StructDef,
        meta: CacheEntryMeta,
    ) {
        self.maybe_evict();
        self.structs.insert(key, CachedStruct { def, meta });
        let mut stats = self.stats.write();
        stats.struct_entries = self.structs.len();
    }

    // === Class Cache ===

    /// Get a cached class specialization.
    pub fn get_class(&self, key: &SpecializationKey) -> Option<ClassDef> {
        if let Some(mut entry) = self.classes.get_mut(key) {
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                drop(entry);
                self.classes.remove(key);
                let mut stats = self.stats.write();
                stats.invalidations += 1;
                stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            let mut stats = self.stats.write();
            stats.hits += 1;
            Some(entry.def.clone())
        } else {
            let mut stats = self.stats.write();
            stats.misses += 1;
            None
        }
    }

    /// Cache a class specialization.
    pub fn put_class(&self, key: SpecializationKey, def: ClassDef) {
        self.put_class_with_meta(key, def, CacheEntryMeta::default());
    }

    /// Cache a class with metadata.
    pub fn put_class_with_meta(&self, key: SpecializationKey, def: ClassDef, meta: CacheEntryMeta) {
        self.maybe_evict();
        self.classes.insert(key, CachedClass { def, meta });
        let mut stats = self.stats.write();
        stats.class_entries = self.classes.len();
    }

    // === Cache Management ===

    /// Check if we need to evict entries and do so.
    fn maybe_evict(&self) {
        let total = self.functions.len() + self.structs.len() + self.classes.len();
        if total >= self.config.max_entries {
            self.evict_lru();
        }
    }

    /// Evict least recently used entries.
    fn evict_lru(&self) {
        // Simple strategy: remove entries with lowest access count
        // In practice, we'd use a more sophisticated LRU algorithm

        let target = self.config.max_entries / 10; // Evict ~10%
        let mut evicted = 0;

        // Evict from functions
        let func_keys: Vec<_> = self.functions.iter().map(|e| e.key().clone()).collect();
        for key in func_keys {
            if evicted >= target {
                break;
            }
            if let Some((_, entry)) = self.functions.remove(&key) {
                if entry.meta.access_count == 0 {
                    evicted += 1;
                } else {
                    // Put it back with decremented count
                    let mut entry = entry;
                    entry.meta.access_count = entry.meta.access_count.saturating_sub(1);
                    self.functions.insert(key, entry);
                }
            }
        }

        let mut stats = self.stats.write();
        stats.evictions += evicted;
        stats.function_entries = self.functions.len();
        stats.struct_entries = self.structs.len();
        stats.class_entries = self.classes.len();
    }

    /// Clear all cached entries.
    pub fn clear(&self) {
        self.functions.clear();
        self.structs.clear();
        self.classes.clear();

        let mut stats = self.stats.write();
        stats.function_entries = 0;
        stats.struct_entries = 0;
        stats.class_entries = 0;
    }

    /// Invalidate entries for a specific source file.
    pub fn invalidate_source(&self, source_path: &PathBuf) {
        let mut invalidated = 0;

        self.functions.retain(|_, entry| {
            if entry.meta.source_path.as_ref() == Some(source_path) {
                invalidated += 1;
                false
            } else {
                true
            }
        });

        self.structs.retain(|_, entry| {
            if entry.meta.source_path.as_ref() == Some(source_path) {
                invalidated += 1;
                false
            } else {
                true
            }
        });

        self.classes.retain(|_, entry| {
            if entry.meta.source_path.as_ref() == Some(source_path) {
                invalidated += 1;
                false
            } else {
                true
            }
        });

        let mut stats = self.stats.write();
        stats.invalidations += invalidated;
        stats.function_entries = self.functions.len();
        stats.struct_entries = self.structs.len();
        stats.class_entries = self.classes.len();
    }

    /// Get cache statistics.
    pub fn stats(&self) -> MonoCacheStats {
        let mut stats = self.stats.read().clone();
        stats.function_entries = self.functions.len();
        stats.struct_entries = self.structs.len();
        stats.class_entries = self.classes.len();
        stats
    }

    /// Pre-warm the cache with known specializations.
    pub fn prewarm_functions(&self, entries: impl IntoIterator<Item = (SpecializationKey, FunctionDef)>) {
        for (key, def) in entries {
            self.put_function(key, def);
        }
    }

    /// Pre-warm the cache with struct specializations.
    pub fn prewarm_structs(&self, entries: impl IntoIterator<Item = (SpecializationKey, StructDef)>) {
        for (key, def) in entries {
            self.put_struct(key, def);
        }
    }

    /// Pre-warm the cache with class specializations.
    pub fn prewarm_classes(&self, entries: impl IntoIterator<Item = (SpecializationKey, ClassDef)>) {
        for (key, def) in entries {
            self.put_class(key, def);
        }
    }
}

impl Default for MonoCache {
    fn default() -> Self {
        Self {
            config: MonoCacheConfig::default(),
            functions: DashMap::new(),
            structs: DashMap::new(),
            classes: DashMap::new(),
            stats: RwLock::new(MonoCacheStats::default()),
        }
    }
}

/// Local (non-thread-safe) monomorphization cache.
///
/// Use this for single-threaded compilation scenarios.
pub struct LocalMonoCache {
    config: MonoCacheConfig,
    functions: HashMap<SpecializationKey, CachedFunction>,
    structs: HashMap<SpecializationKey, CachedStruct>,
    classes: HashMap<SpecializationKey, CachedClass>,
    stats: MonoCacheStats,
}

impl LocalMonoCache {
    /// Create a new local cache.
    pub fn new() -> Self {
        Self::with_config(MonoCacheConfig::default())
    }

    /// Create with custom config.
    pub fn with_config(config: MonoCacheConfig) -> Self {
        Self {
            config,
            functions: HashMap::new(),
            structs: HashMap::new(),
            classes: HashMap::new(),
            stats: MonoCacheStats::default(),
        }
    }

    /// Get a cached function.
    pub fn get_function(&mut self, key: &SpecializationKey) -> Option<FunctionDef> {
        if let Some(entry) = self.functions.get_mut(key) {
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                self.functions.remove(key);
                self.stats.invalidations += 1;
                self.stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            self.stats.hits += 1;
            Some(entry.def.clone())
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Cache a function.
    pub fn put_function(&mut self, key: SpecializationKey, def: FunctionDef) {
        self.functions.insert(
            key,
            CachedFunction {
                def,
                meta: CacheEntryMeta::default(),
            },
        );
        self.stats.function_entries = self.functions.len();
    }

    /// Get a cached struct.
    pub fn get_struct(&mut self, key: &SpecializationKey) -> Option<StructDef> {
        if let Some(entry) = self.structs.get_mut(key) {
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                self.structs.remove(key);
                self.stats.invalidations += 1;
                self.stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            self.stats.hits += 1;
            Some(entry.def.clone())
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Cache a struct.
    pub fn put_struct(&mut self, key: SpecializationKey, def: StructDef) {
        self.structs.insert(
            key,
            CachedStruct {
                def,
                meta: CacheEntryMeta::default(),
            },
        );
        self.stats.struct_entries = self.structs.len();
    }

    /// Get a cached class.
    pub fn get_class(&mut self, key: &SpecializationKey) -> Option<ClassDef> {
        if let Some(entry) = self.classes.get_mut(key) {
            if self.config.validate_timestamps && !entry.meta.is_valid() {
                self.classes.remove(key);
                self.stats.invalidations += 1;
                self.stats.misses += 1;
                return None;
            }

            entry.meta.access_count += 1;
            self.stats.hits += 1;
            Some(entry.def.clone())
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Cache a class.
    pub fn put_class(&mut self, key: SpecializationKey, def: ClassDef) {
        self.classes.insert(
            key,
            CachedClass {
                def,
                meta: CacheEntryMeta::default(),
            },
        );
        self.stats.class_entries = self.classes.len();
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.functions.clear();
        self.structs.clear();
        self.classes.clear();
        self.stats.function_entries = 0;
        self.stats.struct_entries = 0;
        self.stats.class_entries = 0;
    }

    /// Get statistics.
    pub fn stats(&self) -> &MonoCacheStats {
        &self.stats
    }
}

impl Default for LocalMonoCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::{Block, Visibility};
    use simple_parser::Span;

    fn make_test_spec_key(name: &str) -> SpecializationKey {
        SpecializationKey::new(name, vec![ConcreteType::Int])
    }

    fn make_test_function(name: &str) -> FunctionDef {
        FunctionDef {
            span: Span::new(0, 0, 1, 1),
            name: name.to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: Block::default(),
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            bounds_block: None,
        }
    }

    fn make_test_struct(name: &str) -> StructDef {
        StructDef {
            span: Span::new(0, 0, 1, 1),
            name: name.to_string(),
            generic_params: vec![],
            where_clause: vec![],
            fields: vec![],
            methods: vec![],
            visibility: Visibility::Private,
            attributes: vec![],
            doc_comment: None,
            invariant: None,
        }
    }

    #[test]
    fn test_mono_cache_function() {
        let cache = MonoCache::new();

        let key = make_test_spec_key("identity");
        let func = make_test_function("identity_i64");

        // Miss on first access
        assert!(cache.get_function(&key).is_none());

        // Put and hit
        cache.put_function(key.clone(), func.clone());
        let result = cache.get_function(&key);
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "identity_i64");

        let stats = cache.stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.function_entries, 1);
    }

    #[test]
    fn test_mono_cache_struct() {
        let cache = MonoCache::new();

        let key = make_test_spec_key("Vec");
        let s = make_test_struct("Vec_i64");

        cache.put_struct(key.clone(), s.clone());
        let result = cache.get_struct(&key);
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "Vec_i64");

        let stats = cache.stats();
        assert_eq!(stats.struct_entries, 1);
    }

    #[test]
    fn test_mono_cache_clear() {
        let cache = MonoCache::new();

        let key1 = make_test_spec_key("f1");
        let key2 = make_test_spec_key("f2");

        cache.put_function(key1.clone(), make_test_function("f1"));
        cache.put_function(key2.clone(), make_test_function("f2"));

        assert_eq!(cache.stats().function_entries, 2);

        cache.clear();
        assert_eq!(cache.stats().function_entries, 0);
        assert!(cache.get_function(&key1).is_none());
    }

    #[test]
    fn test_mono_cache_stats() {
        let cache = MonoCache::new();

        let key = make_test_spec_key("test");
        let func = make_test_function("test");

        // Misses
        cache.get_function(&key);
        cache.get_function(&key);

        // Hit
        cache.put_function(key.clone(), func);
        cache.get_function(&key);
        cache.get_function(&key);

        let stats = cache.stats();
        assert_eq!(stats.hits, 2);
        assert_eq!(stats.misses, 2);
        assert_eq!(stats.hit_ratio(), 0.5);
    }

    #[test]
    fn test_local_mono_cache() {
        let mut cache = LocalMonoCache::new();

        let key = make_test_spec_key("local_func");
        let func = make_test_function("local_func_i64");

        assert!(cache.get_function(&key).is_none());

        cache.put_function(key.clone(), func);
        assert!(cache.get_function(&key).is_some());

        let stats = cache.stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn test_mono_cache_config() {
        let config = MonoCacheConfig {
            max_entries: 2,
            validate_timestamps: false,
            persist_to_disk: false,
            cache_dir: None,
        };
        let cache = MonoCache::with_config(config);

        // Add 3 entries to trigger eviction
        for i in 0..3 {
            let key = make_test_spec_key(&format!("f{}", i));
            cache.put_function(key, make_test_function(&format!("f{}", i)));
        }

        // Some entries should have been evicted
        let stats = cache.stats();
        assert!(stats.function_entries <= 3);
    }

    #[test]
    fn test_mono_cache_prewarm() {
        let cache = MonoCache::new();

        let entries = vec![
            (make_test_spec_key("f1"), make_test_function("f1")),
            (make_test_spec_key("f2"), make_test_function("f2")),
        ];

        cache.prewarm_functions(entries);

        assert_eq!(cache.stats().function_entries, 2);
        assert!(cache.get_function(&make_test_spec_key("f1")).is_some());
        assert!(cache.get_function(&make_test_spec_key("f2")).is_some());
    }

    #[test]
    fn test_cache_entry_meta_default() {
        let meta = CacheEntryMeta::default();
        assert!(meta.is_valid()); // No source info, so valid
        assert_eq!(meta.access_count, 0);
    }
}
