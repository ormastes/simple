//! Effect Analysis Cache (#822)
//!
//! Provides caching for effect analysis results to avoid redundant analysis
//! during compilation. Caches:
//! 1. Function effect sets (what effects a function has)
//! 2. Operation effect requirements (what effects an operation requires)
//! 3. Effect violation results (whether a function violates its declared effects)

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use dashmap::DashMap;
use parking_lot::RwLock;

use simple_parser::ast::Effect;

/// Configuration for the effect cache.
#[derive(Debug, Clone)]
pub struct EffectCacheConfig {
    /// Maximum number of function entries to cache.
    pub max_function_entries: usize,
    /// Maximum number of operation entries to cache.
    pub max_operation_entries: usize,
}

impl Default for EffectCacheConfig {
    fn default() -> Self {
        Self {
            max_function_entries: 10_000,
            max_operation_entries: 1_000,
        }
    }
}

/// Statistics about effect cache usage.
#[derive(Debug, Clone, Default)]
pub struct EffectCacheStats {
    /// Number of function cache hits.
    pub function_hits: usize,
    /// Number of function cache misses.
    pub function_misses: usize,
    /// Number of operation cache hits.
    pub operation_hits: usize,
    /// Number of operation cache misses.
    pub operation_misses: usize,
    /// Current number of cached functions.
    pub function_entries: usize,
    /// Current number of cached operations.
    pub operation_entries: usize,
}

impl EffectCacheStats {
    /// Calculate function hit ratio.
    pub fn function_hit_ratio(&self) -> f64 {
        let total = self.function_hits + self.function_misses;
        if total == 0 {
            0.0
        } else {
            self.function_hits as f64 / total as f64
        }
    }

    /// Calculate operation hit ratio.
    pub fn operation_hit_ratio(&self) -> f64 {
        let total = self.operation_hits + self.operation_misses;
        if total == 0 {
            0.0
        } else {
            self.operation_hits as f64 / total as f64
        }
    }
}

/// Cached effect analysis for a function.
#[derive(Debug, Clone)]
pub struct FunctionEffectInfo {
    /// The function's declared effects.
    pub declared_effects: HashSet<Effect>,
    /// Effects derived from the function body analysis.
    pub derived_effects: HashSet<Effect>,
    /// Operations called by this function.
    pub called_operations: HashSet<String>,
    /// Functions called by this function.
    pub called_functions: HashSet<String>,
    /// Whether this function has any effect violations.
    pub has_violations: bool,
    /// Specific violations found (if any).
    pub violations: Vec<String>,
}

impl FunctionEffectInfo {
    /// Create a new function effect info.
    pub fn new(declared: HashSet<Effect>) -> Self {
        Self {
            declared_effects: declared,
            derived_effects: HashSet::new(),
            called_operations: HashSet::new(),
            called_functions: HashSet::new(),
            has_violations: false,
            violations: Vec::new(),
        }
    }

    /// Check if the function is pure (no side effects).
    pub fn is_pure(&self) -> bool {
        self.declared_effects.contains(&Effect::Pure)
    }

    /// Check if the function is async.
    pub fn is_async(&self) -> bool {
        self.declared_effects.contains(&Effect::Async)
    }

    /// Check if the function requires IO.
    pub fn requires_io(&self) -> bool {
        self.declared_effects.contains(&Effect::Io)
            || self.derived_effects.contains(&Effect::Io)
    }

    /// Check if the function requires filesystem access.
    pub fn requires_fs(&self) -> bool {
        self.declared_effects.contains(&Effect::Fs)
            || self.derived_effects.contains(&Effect::Fs)
    }

    /// Check if the function requires network access.
    pub fn requires_net(&self) -> bool {
        self.declared_effects.contains(&Effect::Net)
            || self.derived_effects.contains(&Effect::Net)
    }

    /// Add a derived effect.
    pub fn add_derived_effect(&mut self, effect: Effect) {
        self.derived_effects.insert(effect);
    }

    /// Add a called operation.
    pub fn add_called_operation(&mut self, operation: String) {
        self.called_operations.insert(operation);
    }

    /// Add a called function.
    pub fn add_called_function(&mut self, function: String) {
        self.called_functions.insert(function);
    }

    /// Record a violation.
    pub fn add_violation(&mut self, violation: String) {
        self.has_violations = true;
        self.violations.push(violation);
    }

    /// Get all effective effects (declared + derived).
    pub fn effective_effects(&self) -> HashSet<Effect> {
        self.declared_effects
            .union(&self.derived_effects)
            .cloned()
            .collect()
    }
}

/// Cached operation effect requirements.
#[derive(Debug, Clone)]
pub struct OperationEffectInfo {
    /// Effects required by this operation.
    pub required_effects: HashSet<Effect>,
    /// Whether this operation is blocking.
    pub is_blocking: bool,
    /// Whether this operation has side effects.
    pub has_side_effects: bool,
}

impl OperationEffectInfo {
    /// Create info for a pure operation.
    pub fn pure() -> Self {
        Self {
            required_effects: HashSet::new(),
            is_blocking: false,
            has_side_effects: false,
        }
    }

    /// Create info for an IO operation.
    pub fn io() -> Self {
        let mut effects = HashSet::new();
        effects.insert(Effect::Io);
        Self {
            required_effects: effects,
            is_blocking: false,
            has_side_effects: true,
        }
    }

    /// Create info for a filesystem operation.
    pub fn fs() -> Self {
        let mut effects = HashSet::new();
        effects.insert(Effect::Fs);
        Self {
            required_effects: effects,
            is_blocking: true,
            has_side_effects: true,
        }
    }

    /// Create info for a network operation.
    pub fn net() -> Self {
        let mut effects = HashSet::new();
        effects.insert(Effect::Net);
        Self {
            required_effects: effects,
            is_blocking: true,
            has_side_effects: true,
        }
    }

    /// Create info for a blocking operation.
    pub fn blocking() -> Self {
        Self {
            required_effects: HashSet::new(),
            is_blocking: true,
            has_side_effects: false,
        }
    }
}

/// Thread-safe effect analysis cache.
pub struct EffectCache {
    config: EffectCacheConfig,
    /// Cached function effect information.
    functions: DashMap<String, FunctionEffectInfo>,
    /// Cached operation effect requirements.
    operations: DashMap<String, OperationEffectInfo>,
    /// Cache statistics.
    stats: RwLock<EffectCacheStats>,
}

impl EffectCache {
    /// Create a new effect cache.
    pub fn new() -> Arc<Self> {
        Self::with_config(EffectCacheConfig::default())
    }

    /// Create with custom config.
    pub fn with_config(config: EffectCacheConfig) -> Arc<Self> {
        Arc::new(Self {
            config,
            functions: DashMap::new(),
            operations: DashMap::new(),
            stats: RwLock::new(EffectCacheStats::default()),
        })
    }

    // === Function Cache ===

    /// Get cached function effect info.
    pub fn get_function(&self, name: &str) -> Option<FunctionEffectInfo> {
        if let Some(entry) = self.functions.get(name) {
            let mut stats = self.stats.write();
            stats.function_hits += 1;
            Some(entry.clone())
        } else {
            let mut stats = self.stats.write();
            stats.function_misses += 1;
            None
        }
    }

    /// Cache function effect info.
    pub fn put_function(&self, name: String, info: FunctionEffectInfo) {
        self.maybe_evict_functions();
        self.functions.insert(name, info);
        let mut stats = self.stats.write();
        stats.function_entries = self.functions.len();
    }

    /// Update function effect info in place.
    pub fn update_function<F>(&self, name: &str, updater: F) -> bool
    where
        F: FnOnce(&mut FunctionEffectInfo),
    {
        if let Some(mut entry) = self.functions.get_mut(name) {
            updater(&mut entry);
            true
        } else {
            false
        }
    }

    /// Check if a function has cached info.
    pub fn has_function(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    // === Operation Cache ===

    /// Get cached operation effect requirements.
    pub fn get_operation(&self, name: &str) -> Option<OperationEffectInfo> {
        if let Some(entry) = self.operations.get(name) {
            let mut stats = self.stats.write();
            stats.operation_hits += 1;
            Some(entry.clone())
        } else {
            let mut stats = self.stats.write();
            stats.operation_misses += 1;
            None
        }
    }

    /// Cache operation effect requirements.
    pub fn put_operation(&self, name: String, info: OperationEffectInfo) {
        self.maybe_evict_operations();
        self.operations.insert(name, info);
        let mut stats = self.stats.write();
        stats.operation_entries = self.operations.len();
    }

    /// Check if an operation has cached info.
    pub fn has_operation(&self, name: &str) -> bool {
        self.operations.contains_key(name)
    }

    // === Cache Management ===

    fn maybe_evict_functions(&self) {
        if self.functions.len() >= self.config.max_function_entries {
            // Simple eviction: remove ~10% of entries
            let to_remove = self.config.max_function_entries / 10;
            let keys: Vec<_> = self.functions.iter().take(to_remove).map(|e| e.key().clone()).collect();
            for key in keys {
                self.functions.remove(&key);
            }
        }
    }

    fn maybe_evict_operations(&self) {
        if self.operations.len() >= self.config.max_operation_entries {
            let to_remove = self.config.max_operation_entries / 10;
            let keys: Vec<_> = self.operations.iter().take(to_remove).map(|e| e.key().clone()).collect();
            for key in keys {
                self.operations.remove(&key);
            }
        }
    }

    /// Clear all cached entries.
    pub fn clear(&self) {
        self.functions.clear();
        self.operations.clear();
        let mut stats = self.stats.write();
        stats.function_entries = 0;
        stats.operation_entries = 0;
    }

    /// Invalidate a specific function.
    pub fn invalidate_function(&self, name: &str) {
        self.functions.remove(name);
        let mut stats = self.stats.write();
        stats.function_entries = self.functions.len();
    }

    /// Get cache statistics.
    pub fn stats(&self) -> EffectCacheStats {
        let mut stats = self.stats.read().clone();
        stats.function_entries = self.functions.len();
        stats.operation_entries = self.operations.len();
        stats
    }

    /// Pre-populate with known operation effects.
    pub fn prewarm_operations(&self) {
        // IO operations
        for op in &["print", "println", "eprint", "eprintln", "input", "flush"] {
            self.put_operation(op.to_string(), OperationEffectInfo::io());
        }

        // FS operations
        for op in &[
            "read_file", "write_file", "read_dir", "list_dir", "create_dir",
            "remove_file", "remove_dir", "rename", "copy", "exists",
        ] {
            self.put_operation(op.to_string(), OperationEffectInfo::fs());
        }

        // Net operations
        for op in &[
            "http_get", "http_post", "tcp_connect", "tcp_listen",
            "udp_bind", "udp_send", "dns_lookup",
        ] {
            self.put_operation(op.to_string(), OperationEffectInfo::net());
        }

        // Blocking operations
        for op in &["recv", "join", "sleep"] {
            self.put_operation(op.to_string(), OperationEffectInfo::blocking());
        }
    }
}

impl Default for EffectCache {
    fn default() -> Self {
        Self {
            config: EffectCacheConfig::default(),
            functions: DashMap::new(),
            operations: DashMap::new(),
            stats: RwLock::new(EffectCacheStats::default()),
        }
    }
}

/// Local (non-thread-safe) effect cache.
pub struct LocalEffectCache {
    functions: HashMap<String, FunctionEffectInfo>,
    operations: HashMap<String, OperationEffectInfo>,
    stats: EffectCacheStats,
}

impl LocalEffectCache {
    /// Create a new local cache.
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            operations: HashMap::new(),
            stats: EffectCacheStats::default(),
        }
    }

    /// Get cached function info.
    pub fn get_function(&mut self, name: &str) -> Option<&FunctionEffectInfo> {
        if self.functions.contains_key(name) {
            self.stats.function_hits += 1;
            self.functions.get(name)
        } else {
            self.stats.function_misses += 1;
            None
        }
    }

    /// Cache function info.
    pub fn put_function(&mut self, name: String, info: FunctionEffectInfo) {
        self.functions.insert(name, info);
        self.stats.function_entries = self.functions.len();
    }

    /// Get cached operation info.
    pub fn get_operation(&mut self, name: &str) -> Option<&OperationEffectInfo> {
        if self.operations.contains_key(name) {
            self.stats.operation_hits += 1;
            self.operations.get(name)
        } else {
            self.stats.operation_misses += 1;
            None
        }
    }

    /// Cache operation info.
    pub fn put_operation(&mut self, name: String, info: OperationEffectInfo) {
        self.operations.insert(name, info);
        self.stats.operation_entries = self.operations.len();
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.functions.clear();
        self.operations.clear();
        self.stats.function_entries = 0;
        self.stats.operation_entries = 0;
    }

    /// Get statistics.
    pub fn stats(&self) -> &EffectCacheStats {
        &self.stats
    }
}

impl Default for LocalEffectCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_effect_cache_function() {
        let cache = EffectCache::new();

        // Miss on first access
        assert!(cache.get_function("test_func").is_none());

        // Put and hit
        let mut info = FunctionEffectInfo::new(HashSet::new());
        info.add_called_operation("print".to_string());
        cache.put_function("test_func".to_string(), info);

        let result = cache.get_function("test_func");
        assert!(result.is_some());
        assert!(result.unwrap().called_operations.contains("print"));

        let stats = cache.stats();
        assert_eq!(stats.function_hits, 1);
        assert_eq!(stats.function_misses, 1);
    }

    #[test]
    fn test_effect_cache_operation() {
        let cache = EffectCache::new();

        cache.put_operation("print".to_string(), OperationEffectInfo::io());

        let result = cache.get_operation("print");
        assert!(result.is_some());
        let info = result.unwrap();
        assert!(info.has_side_effects);
        assert!(info.required_effects.contains(&Effect::Io));
    }

    #[test]
    fn test_effect_cache_prewarm() {
        let cache = EffectCache::new();
        cache.prewarm_operations();

        // Should have cached IO operations
        let print_info = cache.get_operation("print");
        assert!(print_info.is_some());
        assert!(print_info.unwrap().required_effects.contains(&Effect::Io));

        // Should have cached FS operations
        let read_info = cache.get_operation("read_file");
        assert!(read_info.is_some());
        assert!(read_info.unwrap().required_effects.contains(&Effect::Fs));

        // Should have cached Net operations
        let http_info = cache.get_operation("http_get");
        assert!(http_info.is_some());
        assert!(http_info.unwrap().required_effects.contains(&Effect::Net));
    }

    #[test]
    fn test_function_effect_info() {
        let mut effects = HashSet::new();
        effects.insert(Effect::Pure);
        let mut info = FunctionEffectInfo::new(effects);

        assert!(info.is_pure());
        assert!(!info.is_async());

        info.add_called_operation("some_op".to_string());
        info.add_called_function("helper".to_string());
        info.add_derived_effect(Effect::Io);

        assert!(info.called_operations.contains("some_op"));
        assert!(info.called_functions.contains("helper"));
        assert!(info.requires_io());
    }

    #[test]
    fn test_function_effect_violations() {
        let mut info = FunctionEffectInfo::new(HashSet::new());

        assert!(!info.has_violations);
        assert!(info.violations.is_empty());

        info.add_violation("blocking operation in async function".to_string());

        assert!(info.has_violations);
        assert_eq!(info.violations.len(), 1);
    }

    #[test]
    fn test_operation_effect_info() {
        let pure = OperationEffectInfo::pure();
        assert!(!pure.is_blocking);
        assert!(!pure.has_side_effects);

        let io = OperationEffectInfo::io();
        assert!(!io.is_blocking);
        assert!(io.has_side_effects);

        let fs = OperationEffectInfo::fs();
        assert!(fs.is_blocking);
        assert!(fs.has_side_effects);

        let blocking = OperationEffectInfo::blocking();
        assert!(blocking.is_blocking);
        assert!(!blocking.has_side_effects);
    }

    #[test]
    fn test_effect_cache_clear() {
        let cache = EffectCache::new();

        cache.put_function("f1".to_string(), FunctionEffectInfo::new(HashSet::new()));
        cache.put_operation("op1".to_string(), OperationEffectInfo::pure());

        assert_eq!(cache.stats().function_entries, 1);
        assert_eq!(cache.stats().operation_entries, 1);

        cache.clear();

        assert_eq!(cache.stats().function_entries, 0);
        assert_eq!(cache.stats().operation_entries, 0);
    }

    #[test]
    fn test_effect_cache_invalidate() {
        let cache = EffectCache::new();

        cache.put_function("f1".to_string(), FunctionEffectInfo::new(HashSet::new()));
        cache.put_function("f2".to_string(), FunctionEffectInfo::new(HashSet::new()));

        assert!(cache.has_function("f1"));
        assert!(cache.has_function("f2"));

        cache.invalidate_function("f1");

        assert!(!cache.has_function("f1"));
        assert!(cache.has_function("f2"));
    }

    #[test]
    fn test_local_effect_cache() {
        let mut cache = LocalEffectCache::new();

        cache.put_function("local_func".to_string(), FunctionEffectInfo::new(HashSet::new()));
        assert!(cache.get_function("local_func").is_some());

        cache.put_operation("local_op".to_string(), OperationEffectInfo::io());
        assert!(cache.get_operation("local_op").is_some());

        let stats = cache.stats();
        assert_eq!(stats.function_hits, 1);
        assert_eq!(stats.operation_hits, 1);
    }

    #[test]
    fn test_effect_cache_stats() {
        let cache = EffectCache::new();

        // Generate some hits and misses
        cache.get_function("miss1");
        cache.get_function("miss2");

        cache.put_function("f1".to_string(), FunctionEffectInfo::new(HashSet::new()));
        cache.get_function("f1");
        cache.get_function("f1");

        let stats = cache.stats();
        assert_eq!(stats.function_misses, 2);
        assert_eq!(stats.function_hits, 2);
        assert_eq!(stats.function_hit_ratio(), 0.5);
    }

    #[test]
    fn test_effect_cache_update() {
        let cache = EffectCache::new();

        cache.put_function("func".to_string(), FunctionEffectInfo::new(HashSet::new()));

        let updated = cache.update_function("func", |info| {
            info.add_violation("test violation".to_string());
        });
        assert!(updated);

        let info = cache.get_function("func").unwrap();
        assert!(info.has_violations);
        assert_eq!(info.violations.len(), 1);

        // Update non-existent function
        let not_updated = cache.update_function("nonexistent", |_| {});
        assert!(!not_updated);
    }
}
