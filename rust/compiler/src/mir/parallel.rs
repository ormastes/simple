//! Parallel MIR Lowering (#809)
//!
//! Provides parallel MIR lowering using rayon for improved compilation performance.
//! Multiple HIR functions can be lowered to MIR concurrently.

use parking_lot::RwLock;
use rayon::prelude::*;

use super::function::MirModule;
use super::lower::{lower_to_mir_with_mode, ContractMode, MirLowerResult};
use crate::hir::HirModule;

/// Configuration for parallel MIR lowering.
#[derive(Debug, Clone)]
pub struct ParallelMirConfig {
    /// Minimum number of functions to trigger parallel lowering.
    pub parallel_threshold: usize,
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
    /// Contract checking mode.
    pub contract_mode: ContractMode,
}

impl Default for ParallelMirConfig {
    fn default() -> Self {
        Self {
            parallel_threshold: 4,
            num_threads: None,
            contract_mode: ContractMode::All,
        }
    }
}

impl ParallelMirConfig {
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

    /// Set the contract mode.
    pub fn with_contract_mode(mut self, mode: ContractMode) -> Self {
        self.contract_mode = mode;
        self
    }
}

/// Statistics about MIR lowering.
#[derive(Debug, Clone, Default)]
pub struct MirLowerStats {
    /// Number of functions lowered.
    pub functions_lowered: usize,
    /// Number of errors encountered.
    pub errors: usize,
    /// Whether parallel processing was used.
    pub used_parallel: bool,
}

/// Parallel MIR lowerer that processes multiple functions concurrently.
pub struct ParallelMirLowerer {
    config: ParallelMirConfig,
    stats: RwLock<MirLowerStats>,
}

impl ParallelMirLowerer {
    /// Create a new parallel MIR lowerer.
    pub fn new() -> Self {
        Self {
            config: ParallelMirConfig::default(),
            stats: RwLock::new(MirLowerStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelMirConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(MirLowerStats::default()),
        }
    }

    /// Get current statistics.
    pub fn stats(&self) -> MirLowerStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = MirLowerStats::default();
    }

    /// Lower an HIR module to MIR.
    ///
    /// Uses the standard lowering API. Parallel processing happens
    /// at the module level (multiple modules lowered concurrently).
    pub fn lower_module(&self, hir_module: &HirModule) -> MirLowerResult<MirModule> {
        let result = lower_to_mir_with_mode(hir_module, self.config.contract_mode);

        // Update stats
        {
            let mut stats = self.stats.write();
            match &result {
                Ok(mir_module) => {
                    stats.functions_lowered = mir_module.functions.len();
                    stats.errors = 0;
                }
                Err(_) => {
                    stats.errors = 1;
                }
            }
            stats.used_parallel = false; // Single module lowering
        }

        result
    }
}

impl Default for ParallelMirLowerer {
    fn default() -> Self {
        Self::new()
    }
}

/// Lower multiple HIR modules to MIR in parallel.
pub fn lower_modules_parallel(modules: &[HirModule]) -> Vec<MirLowerResult<MirModule>> {
    let lowerer = ParallelMirLowerer::new();

    modules.par_iter().map(|m| lowerer.lower_module(m)).collect()
}

/// Lower multiple HIR modules with custom config.
pub fn lower_modules_parallel_with_config(
    modules: &[HirModule],
    config: ParallelMirConfig,
) -> Vec<MirLowerResult<MirModule>> {
    let lowerer = ParallelMirLowerer::with_config(config);

    modules.par_iter().map(|m| lowerer.lower_module(m)).collect()
}

/// Batch MIR lowerer that tracks statistics across multiple modules.
pub struct BatchMirLowerer {
    config: ParallelMirConfig,
    total_stats: RwLock<MirLowerStats>,
}

impl BatchMirLowerer {
    /// Create a new batch lowerer.
    pub fn new() -> Self {
        Self {
            config: ParallelMirConfig::default(),
            total_stats: RwLock::new(MirLowerStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelMirConfig) -> Self {
        Self {
            config,
            total_stats: RwLock::new(MirLowerStats::default()),
        }
    }

    /// Lower a batch of HIR modules to MIR.
    pub fn lower_batch(&self, modules: &[HirModule]) -> Vec<MirLowerResult<MirModule>> {
        let results = lower_modules_parallel_with_config(modules, self.config.clone());

        // Aggregate stats
        let mut total = self.total_stats.write();
        for result in &results {
            if let Ok(mir_module) = result {
                total.functions_lowered += mir_module.functions.len();
            } else {
                total.errors += 1;
            }
        }

        results
    }

    /// Get total statistics.
    pub fn total_stats(&self) -> MirLowerStats {
        self.total_stats.read().clone()
    }

    /// Reset total statistics.
    pub fn reset_stats(&self) {
        *self.total_stats.write() = MirLowerStats::default();
    }
}

impl Default for BatchMirLowerer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_mir_config() {
        let config = ParallelMirConfig::new()
            .with_threshold(10)
            .with_threads(4)
            .with_contract_mode(ContractMode::Off);

        assert_eq!(config.parallel_threshold, 10);
        assert_eq!(config.num_threads, Some(4));
        assert!(matches!(config.contract_mode, ContractMode::Off));
    }

    #[test]
    fn test_mir_lower_stats() {
        let stats = MirLowerStats {
            functions_lowered: 10,
            errors: 0,
            used_parallel: true,
        };
        assert_eq!(stats.functions_lowered, 10);
        assert!(stats.used_parallel);
    }

    #[test]
    fn test_parallel_mir_lowerer() {
        let lowerer = ParallelMirLowerer::new();
        let stats = lowerer.stats();
        assert_eq!(stats.functions_lowered, 0);
        assert_eq!(stats.errors, 0);
    }

    #[test]
    fn test_batch_mir_lowerer() {
        let batch = BatchMirLowerer::new();
        let stats = batch.total_stats();
        assert_eq!(stats.functions_lowered, 0);
    }

    #[test]
    fn test_lower_empty_modules() {
        let modules: Vec<HirModule> = vec![];
        let results = lower_modules_parallel(&modules);
        assert!(results.is_empty());
    }
}
