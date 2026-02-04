//! Parallel test execution with dynamic thread adjustment.
//!
//! Provides resource-aware parallel test execution that reduces thread count
//! when system CPU or memory usage exceeds configurable thresholds.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Instant;

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

use super::resource_monitor::{ResourceMonitor, available_cores};
use super::execution::run_test_file_safe_mode;
use super::types::{TestFileResult, TestOptions, DebugLevel, debug_log};

/// Configuration for parallel execution.
#[derive(Debug, Clone)]
pub struct ParallelConfig {
    /// Maximum number of threads (0 = auto-detect)
    pub max_threads: usize,
    /// CPU usage percentage threshold to trigger throttling
    pub cpu_threshold: u8,
    /// Memory usage percentage threshold to trigger throttling
    pub memory_threshold: u8,
    /// Number of threads when throttled
    pub throttled_threads: usize,
    /// Seconds between resource checks
    pub check_interval: u64,
    /// Ignore CPU/memory limits (full parallel mode)
    pub full_parallel: bool,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        Self {
            max_threads: 0, // Auto-detect
            cpu_threshold: 70,
            memory_threshold: 70,
            throttled_threads: 1,
            // Reduced from 5s to 1s for faster response to resource changes.
            // With condvar-based interruptible sleep, shorter intervals don't
            // cause stop() to hang.
            check_interval: 1,
            full_parallel: false,
        }
    }
}

impl ParallelConfig {
    /// Create config from TestOptions.
    pub fn from_options(options: &TestOptions) -> Self {
        Self {
            max_threads: options.max_threads,
            cpu_threshold: options.cpu_threshold,
            memory_threshold: options.memory_threshold,
            throttled_threads: options.throttled_threads,
            check_interval: options.cpu_check_interval,
            full_parallel: options.full_parallel,
        }
    }

    /// Get the effective maximum thread count.
    pub fn effective_max_threads(&self) -> usize {
        if self.max_threads == 0 {
            available_cores()
        } else {
            self.max_threads
        }
    }
}

/// Parallel test executor with resource-aware thread management.
pub struct ParallelExecutor {
    config: ParallelConfig,
    resource_monitor: Option<ResourceMonitor>,
    current_threads: Arc<AtomicUsize>,
}

impl ParallelExecutor {
    /// Create a new parallel executor with the given configuration.
    ///
    /// Checks current memory usage at startup - if already above threshold,
    /// starts with throttled thread count instead of max threads.
    pub fn new(config: ParallelConfig) -> Self {
        let max_threads = config.effective_max_threads();
        let resource_monitor = if config.full_parallel {
            None // No monitoring needed in full parallel mode
        } else {
            Some(ResourceMonitor::new(config.check_interval))
        };

        // Check memory at startup - if already high, start throttled
        let initial_threads = if config.full_parallel {
            max_threads
        } else {
            let memory_usage = ResourceMonitor::measure_memory_once();
            if memory_usage >= config.memory_threshold as f32 {
                eprintln!(
                    "Memory already at {:.0}% (>={:.0}%) - starting with {} thread(s)",
                    memory_usage,
                    config.memory_threshold,
                    config.throttled_threads.max(1)
                );
                config.throttled_threads.max(1)
            } else {
                max_threads
            }
        };

        Self {
            config,
            resource_monitor,
            current_threads: Arc::new(AtomicUsize::new(initial_threads)),
        }
    }

    /// Create executor from TestOptions.
    pub fn from_options(options: &TestOptions) -> Self {
        Self::new(ParallelConfig::from_options(options))
    }

    /// Execute test files in parallel with resource-aware thread adjustment.
    ///
    /// Returns results in the same order as input files (stable ordering).
    pub fn execute(&mut self, test_files: &[PathBuf], options: &TestOptions, quiet: bool) -> Vec<TestFileResult> {
        let total_tests = test_files.len();
        if total_tests == 0 {
            return Vec::new();
        }

        // Start resource monitoring
        if let Some(ref mut monitor) = self.resource_monitor {
            monitor.start();
        }

        let initial_threads = self.current_threads.load(Ordering::SeqCst);
        if !quiet {
            println!(
                "Starting parallel execution with {} threads (CPU threshold: {}%, memory threshold: {}%)",
                initial_threads, self.config.cpu_threshold, self.config.memory_threshold
            );
        }

        debug_log!(
            DebugLevel::Basic,
            "Parallel",
            "Starting with {} threads, {} test files",
            initial_threads,
            total_tests
        );

        // Create thread pool with initial thread count
        let pool = ThreadPoolBuilder::new()
            .num_threads(initial_threads)
            .build()
            .expect("Failed to create thread pool");

        // Track progress
        let completed = Arc::new(AtomicUsize::new(0));
        let throttled_count = Arc::new(AtomicUsize::new(0));

        // Execute tests in parallel
        let results: Vec<TestFileResult> = pool.install(|| {
            test_files
                .par_iter()
                .map(|path| {
                    // Check CPU usage before each test (if monitoring enabled)
                    self.maybe_adjust_threads(quiet);

                    let result = run_test_file_safe_mode(path, options);

                    // Update progress
                    let done = completed.fetch_add(1, Ordering::SeqCst) + 1;
                    if !quiet {
                        let threads = self.current_threads.load(Ordering::SeqCst);
                        print_progress(done, total_tests, threads, &result);
                    }

                    debug_log!(
                        DebugLevel::Detailed,
                        "Parallel",
                        "Completed {}/{}: {} (passed={}, failed={})",
                        done,
                        total_tests,
                        path.display(),
                        result.passed,
                        result.failed
                    );

                    result
                })
                .collect()
        });

        // Stop resource monitoring
        if let Some(ref mut monitor) = self.resource_monitor {
            monitor.stop();
        }

        let throttle_events = throttled_count.load(Ordering::SeqCst);
        if !quiet && throttle_events > 0 {
            println!("Throttled {} times due to high resource usage", throttle_events);
        }

        debug_log!(
            DebugLevel::Basic,
            "Parallel",
            "Completed all {} tests, {} throttle events",
            total_tests,
            throttle_events
        );

        results
    }

    /// Check CPU and memory usage and adjust thread count if needed.
    fn maybe_adjust_threads(&self, quiet: bool) {
        if self.config.full_parallel {
            return; // No adjustment in full parallel mode
        }

        if let Some(ref monitor) = self.resource_monitor {
            let cpu_usage = monitor.get_cpu_usage();
            let memory_usage = monitor.get_memory_usage();
            let current = self.current_threads.load(Ordering::SeqCst);

            let cpu_high = monitor.is_cpu_above_threshold(self.config.cpu_threshold);
            let memory_high = monitor.is_memory_above_threshold(self.config.memory_threshold);

            if cpu_high || memory_high {
                // Either resource is high - reduce threads
                let new_threads = self.config.throttled_threads.max(1);
                if current > new_threads {
                    self.current_threads.store(new_threads, Ordering::SeqCst);
                    if !quiet {
                        let reason = match (cpu_high, memory_high) {
                            (true, true) => format!(
                                "CPU at {:.0}% (>{:.0}%) and memory at {:.0}% (>{:.0}%)",
                                cpu_usage, self.config.cpu_threshold, memory_usage, self.config.memory_threshold
                            ),
                            (true, false) => format!("CPU at {:.0}% (>{:.0}%)", cpu_usage, self.config.cpu_threshold),
                            (false, true) => {
                                format!("Memory at {:.0}% (>{:.0}%)", memory_usage, self.config.memory_threshold)
                            }
                            _ => unreachable!(),
                        };
                        eprintln!("{} - reduced to {} thread(s)", reason, new_threads);
                    }
                    debug_log!(
                        DebugLevel::Detailed,
                        "Parallel",
                        "Throttled: CPU={:.0}%, memory={:.0}%, threads {} -> {}",
                        cpu_usage,
                        memory_usage,
                        current,
                        new_threads
                    );
                }
            } else {
                // Check if BOTH resources are below hysteresis threshold to scale up
                let cpu_hysteresis = self.config.cpu_threshold.saturating_sub(10) as f32;
                let memory_hysteresis = self.config.memory_threshold.saturating_sub(10) as f32;
                let cpu_low = cpu_usage < cpu_hysteresis;
                let memory_low = memory_usage < memory_hysteresis;

                if cpu_low && memory_low {
                    // Both resources are low - consider increasing threads
                    let max_threads = self.config.effective_max_threads();
                    if current < max_threads {
                        let new_threads = (current + 1).min(max_threads);
                        self.current_threads.store(new_threads, Ordering::SeqCst);
                        debug_log!(
                            DebugLevel::Trace,
                            "Parallel",
                            "Unthrottled: CPU={:.0}%, memory={:.0}%, threads {} -> {}",
                            cpu_usage,
                            memory_usage,
                            current,
                            new_threads
                        );
                    }
                }
                // If only one is below hysteresis, stay at current thread count
            }
        }
    }

    /// Get the current thread count.
    pub fn current_threads(&self) -> usize {
        self.current_threads.load(Ordering::SeqCst)
    }
}

/// Print progress line for parallel execution.
fn print_progress(done: usize, total: usize, threads: usize, result: &TestFileResult) {
    let status = if result.failed > 0 || result.error.is_some() {
        "\x1b[31mFAIL\x1b[0m"
    } else {
        "\x1b[32mPASS\x1b[0m"
    };

    // Extract just the filename for compact display
    let filename = result.path.file_name().and_then(|n| n.to_str()).unwrap_or("unknown");

    println!(
        "[{}/{}] {} {} ({}ms, {} threads)",
        done, total, status, filename, result.duration_ms, threads
    );
}

/// Execute tests in parallel using the parallel executor.
///
/// This is the main entry point for parallel test execution.
pub fn run_tests_parallel(
    test_files: &[PathBuf],
    options: &TestOptions,
    quiet: bool,
) -> (Vec<TestFileResult>, usize, usize, usize, usize) {
    let mut executor = ParallelExecutor::from_options(options);
    let results = executor.execute(test_files, options, quiet);

    // Aggregate results
    let mut total_passed = 0;
    let mut total_failed = 0;
    let mut total_skipped = 0;
    let mut total_ignored = 0;

    for result in &results {
        total_passed += result.passed;
        total_failed += result.failed;
        total_skipped += result.skipped;
        total_ignored += result.ignored;
    }

    (results, total_passed, total_failed, total_skipped, total_ignored)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_config_default() {
        let config = ParallelConfig::default();
        assert_eq!(config.max_threads, 0);
        assert_eq!(config.cpu_threshold, 70);
        assert_eq!(config.throttled_threads, 1);
        assert_eq!(config.check_interval, 1); // Reduced from 5 to 1 for faster response
        assert!(!config.full_parallel);
    }

    #[test]
    fn test_effective_max_threads() {
        let mut config = ParallelConfig::default();

        // Auto-detect mode
        config.max_threads = 0;
        assert!(config.effective_max_threads() >= 1);

        // Explicit count
        config.max_threads = 4;
        assert_eq!(config.effective_max_threads(), 4);
    }

    #[test]
    fn test_parallel_executor_creation() {
        let config = ParallelConfig::default();
        let executor = ParallelExecutor::new(config);
        assert!(executor.current_threads() >= 1);
    }

    #[test]
    fn test_parallel_executor_full_parallel_no_monitor() {
        let config = ParallelConfig {
            full_parallel: true,
            ..Default::default()
        };
        let executor = ParallelExecutor::new(config);
        assert!(executor.resource_monitor.is_none());
    }

    #[test]
    fn test_parallel_config_memory_threshold() {
        let config = ParallelConfig::default();
        assert_eq!(config.memory_threshold, 70);
    }

    #[test]
    fn test_empty_test_files() {
        let options = TestOptions::default();
        let (results, passed, failed, skipped, ignored) = run_tests_parallel(&[], &options, true);
        assert!(results.is_empty());
        assert_eq!(passed, 0);
        assert_eq!(failed, 0);
        assert_eq!(skipped, 0);
        assert_eq!(ignored, 0);
    }
}
