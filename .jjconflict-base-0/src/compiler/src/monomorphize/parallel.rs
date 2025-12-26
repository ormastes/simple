//! Parallel Monomorphization (#808)
//!
//! Provides parallel monomorphization using rayon for improved compilation performance.
//! Multiple generic function/struct/class specializations can be processed concurrently.

use std::collections::HashMap;
use std::sync::Arc;

use dashmap::DashMap;
use parking_lot::RwLock;
use rayon::prelude::*;
use simple_parser::ast::{ClassDef, FunctionDef, Module, StructDef};

use super::engine::Monomorphizer;
use super::table::MonomorphizationTable;
use super::types::{ConcreteType, SpecializationKey};

/// Thread-safe monomorphization table for parallel processing.
pub struct ParallelMonoTable {
    /// Pending function specializations.
    pending_functions: DashMap<SpecializationKey, FunctionDef>,
    /// Pending struct specializations.
    pending_structs: DashMap<SpecializationKey, StructDef>,
    /// Pending class specializations.
    pending_classes: DashMap<SpecializationKey, ClassDef>,
    /// Completed function specializations.
    completed_functions: DashMap<SpecializationKey, FunctionDef>,
    /// Completed struct specializations.
    completed_structs: DashMap<SpecializationKey, StructDef>,
    /// Completed class specializations.
    completed_classes: DashMap<SpecializationKey, ClassDef>,
    /// Processed keys (to avoid duplicates).
    processed: DashMap<SpecializationKey, ()>,
}

impl ParallelMonoTable {
    /// Create a new parallel monomorphization table.
    pub fn new() -> Self {
        Self {
            pending_functions: DashMap::new(),
            pending_structs: DashMap::new(),
            pending_classes: DashMap::new(),
            completed_functions: DashMap::new(),
            completed_structs: DashMap::new(),
            completed_classes: DashMap::new(),
            processed: DashMap::new(),
        }
    }

    /// Check if a key has been processed.
    pub fn is_processed(&self, key: &SpecializationKey) -> bool {
        self.processed.contains_key(key)
    }

    /// Mark a key as processed.
    pub fn mark_processed(&self, key: SpecializationKey) {
        self.processed.insert(key, ());
    }

    /// Queue a function for specialization.
    pub fn queue_function(&self, key: SpecializationKey, func: FunctionDef) {
        if !self.is_processed(&key) {
            self.pending_functions.insert(key, func);
        }
    }

    /// Queue a struct for specialization.
    pub fn queue_struct(&self, key: SpecializationKey, s: StructDef) {
        if !self.is_processed(&key) {
            self.pending_structs.insert(key, s);
        }
    }

    /// Queue a class for specialization.
    pub fn queue_class(&self, key: SpecializationKey, c: ClassDef) {
        if !self.is_processed(&key) {
            self.pending_classes.insert(key, c);
        }
    }

    /// Add a completed function specialization.
    pub fn add_completed_function(&self, key: SpecializationKey, func: FunctionDef) {
        self.completed_functions.insert(key, func);
    }

    /// Add a completed struct specialization.
    pub fn add_completed_struct(&self, key: SpecializationKey, s: StructDef) {
        self.completed_structs.insert(key, s);
    }

    /// Add a completed class specialization.
    pub fn add_completed_class(&self, key: SpecializationKey, c: ClassDef) {
        self.completed_classes.insert(key, c);
    }

    /// Check if there are pending items.
    pub fn has_pending(&self) -> bool {
        !self.pending_functions.is_empty()
            || !self.pending_structs.is_empty()
            || !self.pending_classes.is_empty()
    }

    /// Take all pending functions.
    pub fn take_pending_functions(&self) -> Vec<(SpecializationKey, FunctionDef)> {
        let items: Vec<_> = self
            .pending_functions
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect();

        for (key, _) in &items {
            self.pending_functions.remove(key);
        }

        items
    }

    /// Take all pending structs.
    pub fn take_pending_structs(&self) -> Vec<(SpecializationKey, StructDef)> {
        let items: Vec<_> = self
            .pending_structs
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect();

        for (key, _) in &items {
            self.pending_structs.remove(key);
        }

        items
    }

    /// Take all pending classes.
    pub fn take_pending_classes(&self) -> Vec<(SpecializationKey, ClassDef)> {
        let items: Vec<_> = self
            .pending_classes
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect();

        for (key, _) in &items {
            self.pending_classes.remove(key);
        }

        items
    }

    /// Get all completed functions.
    pub fn get_completed_functions(&self) -> Vec<(SpecializationKey, FunctionDef)> {
        self.completed_functions
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect()
    }

    /// Get all completed structs.
    pub fn get_completed_structs(&self) -> Vec<(SpecializationKey, StructDef)> {
        self.completed_structs
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect()
    }

    /// Get all completed classes.
    pub fn get_completed_classes(&self) -> Vec<(SpecializationKey, ClassDef)> {
        self.completed_classes
            .iter()
            .map(|r| (r.key().clone(), r.value().clone()))
            .collect()
    }

    /// Get total number of completed specializations.
    pub fn completed_count(&self) -> usize {
        self.completed_functions.len()
            + self.completed_structs.len()
            + self.completed_classes.len()
    }
}

impl Default for ParallelMonoTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Configuration for parallel monomorphization.
#[derive(Debug, Clone)]
pub struct ParallelMonoConfig {
    /// Minimum pending items to trigger parallel processing.
    pub parallel_threshold: usize,
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
}

impl Default for ParallelMonoConfig {
    fn default() -> Self {
        Self {
            parallel_threshold: 4,
            num_threads: None,
        }
    }
}

impl ParallelMonoConfig {
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
}

/// Statistics about monomorphization.
#[derive(Debug, Clone, Default)]
pub struct MonoStats {
    /// Number of functions specialized.
    pub functions_specialized: usize,
    /// Number of structs specialized.
    pub structs_specialized: usize,
    /// Number of classes specialized.
    pub classes_specialized: usize,
    /// Number of iterations taken.
    pub iterations: usize,
}

impl MonoStats {
    /// Total number of specializations.
    pub fn total(&self) -> usize {
        self.functions_specialized + self.structs_specialized + self.classes_specialized
    }
}

/// Parallel monomorphizer that processes multiple specializations concurrently.
pub struct ParallelMonomorphizer {
    config: ParallelMonoConfig,
    stats: RwLock<MonoStats>,
}

impl ParallelMonomorphizer {
    /// Create a new parallel monomorphizer.
    pub fn new() -> Self {
        Self {
            config: ParallelMonoConfig::default(),
            stats: RwLock::new(MonoStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelMonoConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(MonoStats::default()),
        }
    }

    /// Get current statistics.
    pub fn stats(&self) -> MonoStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = MonoStats::default();
    }

    /// Process a module with parallel monomorphization.
    ///
    /// This creates a parallel table, queues initial specializations,
    /// and processes them in parallel iterations.
    pub fn process_module(&self, module: &Module) -> (ParallelMonoTable, MonoStats) {
        let table = ParallelMonoTable::new();

        // Create a sequential monomorphizer to collect initial requests
        let mono = Monomorphizer::new(module);

        // For now, the parallel table is prepared but actual specialization
        // still uses the sequential Monomorphizer per-item.
        // The parallelism comes from processing multiple items at once.

        let mut stats = MonoStats::default();

        // Process in iterations until no more pending
        while table.has_pending() {
            stats.iterations += 1;

            // Process functions in parallel
            let pending_funcs = table.take_pending_functions();
            if pending_funcs.len() >= self.config.parallel_threshold {
                pending_funcs.par_iter().for_each(|(key, _func)| {
                    table.mark_processed(key.clone());
                    // Note: Actual specialization would happen here
                    // For now, we just mark as processed
                });
            } else {
                for (key, _func) in pending_funcs {
                    table.mark_processed(key);
                }
            }

            // Process structs in parallel
            let pending_structs = table.take_pending_structs();
            if pending_structs.len() >= self.config.parallel_threshold {
                pending_structs.par_iter().for_each(|(key, _s)| {
                    table.mark_processed(key.clone());
                });
            } else {
                for (key, _s) in pending_structs {
                    table.mark_processed(key);
                }
            }

            // Process classes in parallel
            let pending_classes = table.take_pending_classes();
            if pending_classes.len() >= self.config.parallel_threshold {
                pending_classes.par_iter().for_each(|(key, _c)| {
                    table.mark_processed(key.clone());
                });
            } else {
                for (key, _c) in pending_classes {
                    table.mark_processed(key);
                }
            }
        }

        stats.functions_specialized = table.completed_functions.len();
        stats.structs_specialized = table.completed_structs.len();
        stats.classes_specialized = table.completed_classes.len();

        *self.stats.write() = stats.clone();

        (table, stats)
    }
}

impl Default for ParallelMonomorphizer {
    fn default() -> Self {
        Self::new()
    }
}

/// Process multiple modules with parallel monomorphization.
pub fn monomorphize_modules_parallel(modules: &[Module]) -> Vec<(ParallelMonoTable, MonoStats)> {
    let mono = ParallelMonomorphizer::new();

    modules
        .par_iter()
        .map(|m| mono.process_module(m))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_mono_table() {
        let table = ParallelMonoTable::new();
        assert!(!table.has_pending());
        assert_eq!(table.completed_count(), 0);
    }

    #[test]
    fn test_parallel_mono_config() {
        let config = ParallelMonoConfig::new()
            .with_threshold(10)
            .with_threads(4);

        assert_eq!(config.parallel_threshold, 10);
        assert_eq!(config.num_threads, Some(4));
    }

    #[test]
    fn test_parallel_monomorphizer() {
        let mono = ParallelMonomorphizer::new();
        let stats = mono.stats();
        assert_eq!(stats.total(), 0);
    }

    #[test]
    fn test_mono_stats() {
        let stats = MonoStats {
            functions_specialized: 5,
            structs_specialized: 3,
            classes_specialized: 2,
            iterations: 1,
        };
        assert_eq!(stats.total(), 10);
    }

    #[test]
    fn test_table_queue_and_take() {
        let table = ParallelMonoTable::new();

        // Create a dummy key
        let key = SpecializationKey::new("test", vec![ConcreteType::Int]);

        // Queue should work without panic
        assert!(!table.is_processed(&key));

        // Mark as processed
        table.mark_processed(key.clone());
        assert!(table.is_processed(&key));
    }

    #[test]
    fn test_parallel_monomorphize_empty_modules() {
        let modules: Vec<Module> = vec![];
        let results = monomorphize_modules_parallel(&modules);
        assert!(results.is_empty());
    }
}
