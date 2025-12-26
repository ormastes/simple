//! Parallel Codegen (#810)
//!
//! Provides parallel code generation using rayon for improved compilation performance.
//! Multiple MIR modules can be compiled to object code concurrently.

use parking_lot::RwLock;
use rayon::prelude::*;
use std::sync::Arc;

use crate::mir::MirModule;

use super::common_backend::{BackendError, BackendResult, BackendSettings};
use super::cranelift::Codegen;

/// Configuration for parallel codegen.
#[derive(Debug, Clone)]
pub struct ParallelCodegenConfig {
    /// Minimum number of modules to trigger parallel codegen.
    pub parallel_threshold: usize,
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
    /// Backend settings for compilation.
    pub backend_settings: BackendSettings,
}

impl Default for ParallelCodegenConfig {
    fn default() -> Self {
        Self {
            parallel_threshold: 2,
            num_threads: None,
            backend_settings: BackendSettings::aot(),
        }
    }
}

impl ParallelCodegenConfig {
    /// Create a new config with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the parallel threshold.
    pub fn with_threshold(mut self, threshold: usize) -> Self {
        self.parallel_threshold = threshold;
        self
    }

    /// Set the number of threads.
    pub fn with_threads(mut self, n: usize) -> Self {
        self.num_threads = Some(n);
        self
    }

    /// Set the backend settings.
    pub fn with_settings(mut self, settings: BackendSettings) -> Self {
        self.backend_settings = settings;
        self
    }
}

/// Statistics about parallel codegen.
#[derive(Debug, Clone, Default)]
pub struct CodegenStats {
    /// Number of modules compiled.
    pub modules_compiled: usize,
    /// Number of functions compiled.
    pub functions_compiled: usize,
    /// Number of errors encountered.
    pub errors: usize,
    /// Whether parallel processing was used.
    pub used_parallel: bool,
    /// Total bytes of object code generated.
    pub total_bytes: usize,
}

/// Result of compiling a single module.
#[derive(Debug)]
pub struct CompiledModule {
    /// Name of the module.
    pub name: String,
    /// Object code bytes.
    pub object_code: Vec<u8>,
    /// Number of functions in the module.
    pub function_count: usize,
}

/// Parallel code generator that processes multiple modules concurrently.
pub struct ParallelCodegen {
    config: ParallelCodegenConfig,
    stats: RwLock<CodegenStats>,
}

impl ParallelCodegen {
    /// Create a new parallel codegen.
    pub fn new() -> Self {
        Self {
            config: ParallelCodegenConfig::default(),
            stats: RwLock::new(CodegenStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelCodegenConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(CodegenStats::default()),
        }
    }

    /// Get current statistics.
    pub fn stats(&self) -> CodegenStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = CodegenStats::default();
    }

    /// Compile a single MIR module to object code.
    pub fn compile_module(&self, mir_module: &MirModule) -> BackendResult<CompiledModule> {
        let codegen = Codegen::for_target(self.config.backend_settings.target.clone())?;
        let object_code = codegen.compile_module(mir_module)?;
        let function_count = mir_module.functions.len();

        // Update stats
        {
            let mut stats = self.stats.write();
            stats.modules_compiled += 1;
            stats.functions_compiled += function_count;
            stats.total_bytes += object_code.len();
        }

        Ok(CompiledModule {
            name: mir_module.name.clone().unwrap_or_else(|| "unnamed".to_string()),
            object_code,
            function_count,
        })
    }

    /// Compile multiple MIR modules.
    /// Uses parallel processing if threshold is met.
    pub fn compile_modules(&self, modules: &[MirModule]) -> Vec<BackendResult<CompiledModule>> {
        let use_parallel = modules.len() >= self.config.parallel_threshold;

        {
            let mut stats = self.stats.write();
            stats.used_parallel = use_parallel;
        }

        if use_parallel {
            self.compile_modules_parallel(modules)
        } else {
            self.compile_modules_sequential(modules)
        }
    }

    /// Compile modules sequentially.
    fn compile_modules_sequential(
        &self,
        modules: &[MirModule],
    ) -> Vec<BackendResult<CompiledModule>> {
        modules.iter().map(|m| self.compile_module(m)).collect()
    }

    /// Compile modules in parallel.
    fn compile_modules_parallel(&self, modules: &[MirModule]) -> Vec<BackendResult<CompiledModule>> {
        modules
            .par_iter()
            .map(|m| self.compile_module(m))
            .collect()
    }
}

impl Default for ParallelCodegen {
    fn default() -> Self {
        Self::new()
    }
}

/// Compile multiple MIR modules to object code in parallel.
pub fn compile_modules_parallel(modules: &[MirModule]) -> Vec<BackendResult<CompiledModule>> {
    let codegen = ParallelCodegen::new();
    codegen.compile_modules(modules)
}

/// Compile multiple MIR modules with custom config.
pub fn compile_modules_parallel_with_config(
    modules: &[MirModule],
    config: ParallelCodegenConfig,
) -> Vec<BackendResult<CompiledModule>> {
    let codegen = ParallelCodegen::with_config(config);
    codegen.compile_modules(modules)
}

/// Batch code generator that tracks statistics across multiple batches.
pub struct BatchCodegen {
    config: ParallelCodegenConfig,
    total_stats: RwLock<CodegenStats>,
}

impl BatchCodegen {
    /// Create a new batch codegen.
    pub fn new() -> Self {
        Self {
            config: ParallelCodegenConfig::default(),
            total_stats: RwLock::new(CodegenStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelCodegenConfig) -> Self {
        Self {
            config,
            total_stats: RwLock::new(CodegenStats::default()),
        }
    }

    /// Compile a batch of MIR modules.
    pub fn compile_batch(&self, modules: &[MirModule]) -> Vec<BackendResult<CompiledModule>> {
        let results = compile_modules_parallel_with_config(modules, self.config.clone());

        // Aggregate stats
        let mut total = self.total_stats.write();
        for result in &results {
            match result {
                Ok(compiled) => {
                    total.modules_compiled += 1;
                    total.functions_compiled += compiled.function_count;
                    total.total_bytes += compiled.object_code.len();
                }
                Err(_) => {
                    total.errors += 1;
                }
            }
        }
        total.used_parallel = modules.len() >= self.config.parallel_threshold;

        results
    }

    /// Get total statistics.
    pub fn total_stats(&self) -> CodegenStats {
        self.total_stats.read().clone()
    }

    /// Reset total statistics.
    pub fn reset_stats(&self) {
        *self.total_stats.write() = CodegenStats::default();
    }
}

impl Default for BatchCodegen {
    fn default() -> Self {
        Self::new()
    }
}

/// Thread-safe compiled module cache for incremental compilation.
pub struct CompiledModuleCache {
    cache: Arc<dashmap::DashMap<String, CompiledModule>>,
}

impl CompiledModuleCache {
    /// Create a new cache.
    pub fn new() -> Self {
        Self {
            cache: Arc::new(dashmap::DashMap::new()),
        }
    }

    /// Get a compiled module from the cache.
    pub fn get(&self, name: &str) -> Option<CompiledModule> {
        self.cache.get(name).map(|r| CompiledModule {
            name: r.name.clone(),
            object_code: r.object_code.clone(),
            function_count: r.function_count,
        })
    }

    /// Insert a compiled module into the cache.
    pub fn insert(&self, module: CompiledModule) {
        self.cache.insert(module.name.clone(), module);
    }

    /// Check if a module is in the cache.
    pub fn contains(&self, name: &str) -> bool {
        self.cache.contains_key(name)
    }

    /// Remove a module from the cache.
    pub fn remove(&self, name: &str) -> Option<CompiledModule> {
        self.cache.remove(name).map(|(_, v)| v)
    }

    /// Clear all cached modules.
    pub fn clear(&self) {
        self.cache.clear();
    }

    /// Get the number of cached modules.
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Check if the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

impl Default for CompiledModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for CompiledModuleCache {
    fn clone(&self) -> Self {
        Self {
            cache: Arc::clone(&self.cache),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_codegen_config() {
        let config = ParallelCodegenConfig::new()
            .with_threshold(10)
            .with_threads(4);

        assert_eq!(config.parallel_threshold, 10);
        assert_eq!(config.num_threads, Some(4));
    }

    #[test]
    fn test_codegen_stats() {
        let stats = CodegenStats {
            modules_compiled: 5,
            functions_compiled: 20,
            errors: 0,
            used_parallel: true,
            total_bytes: 10000,
        };
        assert_eq!(stats.modules_compiled, 5);
        assert_eq!(stats.functions_compiled, 20);
        assert!(stats.used_parallel);
    }

    #[test]
    fn test_parallel_codegen() {
        let codegen = ParallelCodegen::new();
        let stats = codegen.stats();
        assert_eq!(stats.modules_compiled, 0);
        assert_eq!(stats.errors, 0);
    }

    #[test]
    fn test_batch_codegen() {
        let batch = BatchCodegen::new();
        let stats = batch.total_stats();
        assert_eq!(stats.modules_compiled, 0);
    }

    #[test]
    fn test_compile_empty_modules() {
        let modules: Vec<MirModule> = vec![];
        let results = compile_modules_parallel(&modules);
        assert!(results.is_empty());
    }

    #[test]
    fn test_compiled_module_cache() {
        let cache = CompiledModuleCache::new();
        assert!(cache.is_empty());

        let module = CompiledModule {
            name: "test".to_string(),
            object_code: vec![1, 2, 3],
            function_count: 5,
        };

        cache.insert(module);
        assert_eq!(cache.len(), 1);
        assert!(cache.contains("test"));

        let retrieved = cache.get("test").unwrap();
        assert_eq!(retrieved.name, "test");
        assert_eq!(retrieved.object_code, vec![1, 2, 3]);
        assert_eq!(retrieved.function_count, 5);
    }

    #[test]
    fn test_compiled_module_cache_clone() {
        let cache1 = CompiledModuleCache::new();
        cache1.insert(CompiledModule {
            name: "shared".to_string(),
            object_code: vec![42],
            function_count: 1,
        });

        let cache2 = cache1.clone();
        assert!(cache2.contains("shared"));

        // Both caches share the same underlying data
        cache2.insert(CompiledModule {
            name: "new".to_string(),
            object_code: vec![],
            function_count: 0,
        });
        assert!(cache1.contains("new"));
    }
}
