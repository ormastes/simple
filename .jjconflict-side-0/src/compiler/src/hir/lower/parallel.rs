//! Parallel HIR Lowering (#807)
//!
//! Provides parallel HIR lowering using rayon for improved compilation performance.
//! Function bodies can be lowered concurrently when enabled.
//!
//! Note: Full parallelization requires refactoring the Lowerer to support
//! shared read-only context. This module provides the infrastructure and
//! a parallel entry point for future optimization.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use parking_lot::RwLock;
use rayon::prelude::*;
use simple_parser::{Module, Node};

use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

/// Configuration for parallel HIR lowering.
#[derive(Debug, Clone)]
pub struct ParallelLowerConfig {
    /// Minimum number of functions to trigger parallel lowering.
    /// Below this threshold, sequential lowering is used.
    pub parallel_threshold: usize,
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
}

impl Default for ParallelLowerConfig {
    fn default() -> Self {
        Self {
            parallel_threshold: 4,
            num_threads: None,
        }
    }
}

impl ParallelLowerConfig {
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

/// Parallel lowerer that can process multiple modules.
pub struct ParallelModuleLowerer {
    config: ParallelLowerConfig,
}

impl ParallelModuleLowerer {
    /// Create a new parallel module lowerer.
    pub fn new() -> Self {
        Self {
            config: ParallelLowerConfig::default(),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelLowerConfig) -> Self {
        Self { config }
    }

    /// Lower multiple modules in parallel.
    ///
    /// Each module is lowered independently using its own Lowerer instance.
    /// This is useful when compiling multiple files that have been parsed.
    pub fn lower_modules(&self, modules: &[Module]) -> Vec<LowerResult<HirModule>> {
        if modules.len() < self.config.parallel_threshold {
            // Sequential lowering for small batches
            modules
                .iter()
                .map(|m| Lowerer::new().lower_module(m))
                .collect()
        } else {
            // Parallel lowering
            modules
                .par_iter()
                .map(|m| Lowerer::new().lower_module(m))
                .collect()
        }
    }

    /// Lower multiple modules in parallel, collecting errors.
    ///
    /// Returns all successful results and a list of errors.
    pub fn lower_modules_with_errors(
        &self,
        modules: &[Module],
    ) -> (Vec<HirModule>, Vec<(usize, LowerError)>) {
        let results = self.lower_modules(modules);

        let mut successes = Vec::new();
        let mut errors = Vec::new();

        for (idx, result) in results.into_iter().enumerate() {
            match result {
                Ok(hir) => successes.push(hir),
                Err(e) => errors.push((idx, e)),
            }
        }

        (successes, errors)
    }
}

impl Default for ParallelModuleLowerer {
    fn default() -> Self {
        Self::new()
    }
}

/// Lower a single module (sequential, standard API).
pub fn lower(module: &Module) -> LowerResult<HirModule> {
    Lowerer::new().lower_module(module)
}

/// Lower multiple modules in parallel.
///
/// This is useful when processing multiple parsed files concurrently.
pub fn lower_modules_parallel(modules: &[Module]) -> Vec<LowerResult<HirModule>> {
    ParallelModuleLowerer::new().lower_modules(modules)
}

/// Lower multiple modules in parallel with custom config.
pub fn lower_modules_parallel_with_config(
    modules: &[Module],
    config: ParallelLowerConfig,
) -> Vec<LowerResult<HirModule>> {
    ParallelModuleLowerer::with_config(config).lower_modules(modules)
}

/// Statistics about parallel lowering.
#[derive(Debug, Clone, Default)]
pub struct LoweringStats {
    /// Number of modules lowered.
    pub modules_lowered: usize,
    /// Number of functions lowered.
    pub functions_lowered: usize,
    /// Number of errors encountered.
    pub errors: usize,
}

/// Parallel batch lowerer that tracks statistics.
pub struct BatchLowerer {
    config: ParallelLowerConfig,
    stats: RwLock<LoweringStats>,
}

impl BatchLowerer {
    /// Create a new batch lowerer.
    pub fn new() -> Self {
        Self {
            config: ParallelLowerConfig::default(),
            stats: RwLock::new(LoweringStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelLowerConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(LoweringStats::default()),
        }
    }

    /// Lower a batch of modules, tracking statistics.
    pub fn lower_batch(&self, modules: &[Module]) -> Vec<LowerResult<HirModule>> {
        let results = if modules.len() < self.config.parallel_threshold {
            modules
                .iter()
                .map(|m| Lowerer::new().lower_module(m))
                .collect::<Vec<_>>()
        } else {
            modules
                .par_iter()
                .map(|m| Lowerer::new().lower_module(m))
                .collect::<Vec<_>>()
        };

        // Update stats
        let mut stats = self.stats.write();
        stats.modules_lowered += modules.len();

        for result in &results {
            match result {
                Ok(hir) => {
                    stats.functions_lowered += hir.functions.len();
                }
                Err(_) => {
                    stats.errors += 1;
                }
            }
        }

        results
    }

    /// Get current statistics.
    pub fn stats(&self) -> LoweringStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = LoweringStats::default();
    }
}

impl Default for BatchLowerer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> Module {
        let mut parser = simple_parser::Parser::new(source);
        parser.parse().unwrap()
    }

    #[test]
    fn test_lower_single() {
        let source = "fn main() -> i64:\n    return 42";
        let module = parse(source);

        let hir = lower(&module).unwrap();
        assert_eq!(hir.functions.len(), 1);
        assert_eq!(hir.functions[0].name, "main");
    }

    #[test]
    fn test_lower_modules_parallel_single() {
        let source = "fn main() -> i64:\n    return 42";
        let modules = vec![parse(source)];

        let results = lower_modules_parallel(&modules);
        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    fn test_lower_modules_parallel_multiple() {
        let modules = vec![
            parse("fn foo() -> i64:\n    return 1"),
            parse("fn bar() -> i64:\n    return 2"),
            parse("fn baz() -> i64:\n    return 3"),
            parse("fn qux() -> i64:\n    return 4"),
            parse("fn main() -> i64:\n    return 0"),
        ];

        let results = lower_modules_parallel(&modules);
        assert_eq!(results.len(), 5);
        assert!(results.iter().all(|r| r.is_ok()));
    }

    #[test]
    fn test_parallel_lower_config() {
        let config = ParallelLowerConfig::new()
            .with_threshold(10)
            .with_threads(2);

        assert_eq!(config.parallel_threshold, 10);
        assert_eq!(config.num_threads, Some(2));
    }

    #[test]
    fn test_batch_lowerer_stats() {
        let modules = vec![
            parse("fn foo() -> i64:\n    return 1"),
            parse("fn bar() -> i64:\n    return 2"),
        ];

        let lowerer = BatchLowerer::new();
        let results = lowerer.lower_batch(&modules);

        assert_eq!(results.len(), 2);

        let stats = lowerer.stats();
        assert_eq!(stats.modules_lowered, 2);
        assert_eq!(stats.functions_lowered, 2);
        assert_eq!(stats.errors, 0);
    }

    #[test]
    fn test_parallel_module_lowerer_with_errors() {
        let lowerer = ParallelModuleLowerer::new();

        // Valid modules
        let modules = vec![
            parse("fn foo() -> i64:\n    return 1"),
            parse("fn bar() -> i64:\n    return 2"),
        ];

        let (successes, errors) = lowerer.lower_modules_with_errors(&modules);
        assert_eq!(successes.len(), 2);
        assert_eq!(errors.len(), 0);
    }

    #[test]
    fn test_sequential_below_threshold() {
        let config = ParallelLowerConfig::new().with_threshold(10);
        let lowerer = ParallelModuleLowerer::with_config(config);

        // Only 2 modules - should use sequential
        let modules = vec![
            parse("fn foo() -> i64:\n    return 1"),
            parse("fn bar() -> i64:\n    return 2"),
        ];

        let results = lowerer.lower_modules(&modules);
        assert_eq!(results.len(), 2);
    }
}
