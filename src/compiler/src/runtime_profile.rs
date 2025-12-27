//! Runtime Hot Path Analysis for 4KB Page Locality (#2040-#2049)
//!
//! This module provides runtime profiling infrastructure for production builds:
//! - Lightweight profiling hooks with minimal overhead
//! - Hot path detection based on actual execution patterns
//! - Feedback loop to update layout configuration
//! - Performance metrics collection and reporting
//!
//! # Design Goals
//!
//! 1. **Low Overhead**: Profiling should add <1% overhead when enabled
//! 2. **Production-Ready**: Can be enabled in production builds
//! 3. **Adaptive**: Layout can be dynamically adjusted based on runtime data
//! 4. **Actionable**: Generates data that can directly improve layout
//!
//! # Usage
//!
//! ```rust
//! use simple_compiler::runtime_profile::{RuntimeProfiler, ProfileConfig};
//!
//! // Create profiler with sampling configuration
//! let mut profiler = RuntimeProfiler::new(ProfileConfig::default());
//!
//! // Enable profiling
//! profiler.start();
//!
//! // ... application runs ...
//!
//! // Stop and collect metrics
//! profiler.stop();
//! let metrics = profiler.collect_metrics();
//!
//! // Generate layout feedback
//! let feedback = profiler.generate_layout_feedback();
//! ```

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use parking_lot::RwLock;

use crate::hir::{LayoutConfig, LayoutPhase};

/// Profiling configuration
#[derive(Debug, Clone)]
pub struct ProfileConfig {
    /// Sampling rate (1 = every call, 10 = every 10th call, etc.)
    pub sample_rate: u32,
    /// Maximum number of functions to track
    pub max_functions: usize,
    /// Whether to track call stacks
    pub track_call_stacks: bool,
    /// Hot threshold (calls per second to be considered "hot")
    pub hot_threshold: f64,
    /// Cold threshold (calls per second to be considered "cold")
    pub cold_threshold: f64,
    /// Minimum samples before making phase recommendations
    pub min_samples: u64,
}

impl Default for ProfileConfig {
    fn default() -> Self {
        Self {
            sample_rate: 100,      // Sample 1 in 100 calls
            max_functions: 10000,  // Track up to 10k functions
            track_call_stacks: false,
            hot_threshold: 100.0,  // 100+ calls/sec = hot
            cold_threshold: 1.0,   // <1 call/sec = cold
            min_samples: 1000,     // Need 1000 samples before recommendations
        }
    }
}

impl ProfileConfig {
    /// Create a high-resolution config (higher overhead, more accurate)
    pub fn high_resolution() -> Self {
        Self {
            sample_rate: 1,
            track_call_stacks: true,
            ..Default::default()
        }
    }

    /// Create a low-overhead config for production
    pub fn low_overhead() -> Self {
        Self {
            sample_rate: 1000,
            track_call_stacks: false,
            max_functions: 1000,
            ..Default::default()
        }
    }
}

/// Per-function runtime statistics
#[derive(Debug, Clone, Default)]
pub struct FunctionStats {
    /// Function name
    pub name: String,
    /// Total number of calls (sampled)
    pub call_count: u64,
    /// Total execution time (sampled, nanoseconds)
    pub total_time_ns: u64,
    /// First call timestamp (relative to profiling start)
    pub first_call_ns: u64,
    /// Last call timestamp
    pub last_call_ns: u64,
    /// Current inferred phase
    pub inferred_phase: LayoutPhase,
    /// Confidence in phase inference (0.0 - 1.0)
    pub confidence: f64,
}

impl FunctionStats {
    /// Create new function stats
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            ..Default::default()
        }
    }

    /// Calculate calls per second
    pub fn calls_per_second(&self, duration_secs: f64) -> f64 {
        if duration_secs <= 0.0 {
            return 0.0;
        }
        self.call_count as f64 / duration_secs
    }

    /// Calculate average call duration in nanoseconds
    pub fn avg_duration_ns(&self) -> u64 {
        if self.call_count == 0 {
            return 0;
        }
        self.total_time_ns / self.call_count
    }
}

/// Runtime performance metrics
#[derive(Debug, Clone, Default)]
pub struct RuntimeMetrics {
    /// Total profiling duration
    pub duration: Duration,
    /// Total function calls observed (sampled)
    pub total_calls: u64,
    /// Number of unique functions observed
    pub unique_functions: usize,
    /// Functions classified as hot (steady phase)
    pub hot_functions: usize,
    /// Functions classified as cold
    pub cold_functions: usize,
    /// Functions called only at startup
    pub startup_functions: usize,
    /// Estimated page fault reduction from optimal layout
    pub estimated_page_savings: usize,
    /// Per-function statistics
    pub function_stats: Vec<FunctionStats>,
}

impl RuntimeMetrics {
    /// Get functions by phase
    pub fn functions_by_phase(&self, phase: LayoutPhase) -> Vec<&FunctionStats> {
        self.function_stats
            .iter()
            .filter(|f| f.inferred_phase == phase)
            .collect()
    }

    /// Get top N hottest functions
    pub fn top_hot_functions(&self, n: usize) -> Vec<&FunctionStats> {
        let duration_secs = self.duration.as_secs_f64();
        let mut sorted: Vec<_> = self.function_stats.iter().collect();
        sorted.sort_by(|a, b| {
            b.calls_per_second(duration_secs)
                .partial_cmp(&a.calls_per_second(duration_secs))
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        sorted.into_iter().take(n).collect()
    }
}

/// Layout feedback from runtime profiling
#[derive(Debug, Clone, Default)]
pub struct LayoutFeedback {
    /// Functions that should be moved to startup phase
    pub promote_to_startup: Vec<String>,
    /// Functions that should be moved to first_frame phase
    pub promote_to_first_frame: Vec<String>,
    /// Functions that should be in steady (hot) phase
    pub promote_to_steady: Vec<String>,
    /// Functions that should be demoted to cold
    pub demote_to_cold: Vec<String>,
    /// Overall confidence in recommendations (0.0 - 1.0)
    pub confidence: f64,
    /// Number of samples this feedback is based on
    pub sample_count: u64,
}

impl LayoutFeedback {
    /// Check if there are any recommendations
    pub fn has_recommendations(&self) -> bool {
        !self.promote_to_startup.is_empty()
            || !self.promote_to_first_frame.is_empty()
            || !self.promote_to_steady.is_empty()
            || !self.demote_to_cold.is_empty()
    }

    /// Apply feedback to a layout config
    pub fn apply_to_config(&self, config: &mut LayoutConfig) {
        // Add to overrides with runtime-inferred phases
        for name in &self.promote_to_startup {
            config.overrides.insert(name.clone(), LayoutPhase::Startup);
        }
        for name in &self.promote_to_first_frame {
            config.overrides.insert(name.clone(), LayoutPhase::FirstFrame);
        }
        for name in &self.promote_to_steady {
            config.overrides.insert(name.clone(), LayoutPhase::Steady);
        }
        for name in &self.demote_to_cold {
            config.overrides.insert(name.clone(), LayoutPhase::Cold);
        }
    }

    /// Generate SDN snippet for the feedback
    pub fn to_sdn(&self) -> String {
        let mut output = String::new();
        output.push_str("# Runtime profiling feedback\n");
        output.push_str(&format!("# Confidence: {:.1}%\n", self.confidence * 100.0));
        output.push_str(&format!("# Based on {} samples\n\n", self.sample_count));

        output.push_str("layout:\n");
        output.push_str("    overrides:\n");

        for name in &self.promote_to_startup {
            output.push_str(&format!("        {}: startup\n", name));
        }
        for name in &self.promote_to_first_frame {
            output.push_str(&format!("        {}: first_frame\n", name));
        }
        for name in &self.promote_to_steady {
            output.push_str(&format!("        {}: steady\n", name));
        }
        for name in &self.demote_to_cold {
            output.push_str(&format!("        {}: cold\n", name));
        }

        output
    }
}

/// Internal function entry for profiling
#[derive(Debug)]
struct ProfileEntry {
    call_count: AtomicU64,
    total_time_ns: AtomicU64,
    first_call_ns: AtomicU64,
    last_call_ns: AtomicU64,
}

impl ProfileEntry {
    fn new() -> Self {
        Self {
            call_count: AtomicU64::new(0),
            total_time_ns: AtomicU64::new(0),
            first_call_ns: AtomicU64::new(0),
            last_call_ns: AtomicU64::new(0),
        }
    }
}

/// Runtime profiler for hot path analysis
pub struct RuntimeProfiler {
    /// Profiling configuration
    config: ProfileConfig,
    /// Whether profiling is currently active
    active: AtomicBool,
    /// Profiling start time
    start_time: RwLock<Option<Instant>>,
    /// Per-function profile data
    entries: RwLock<HashMap<String, Arc<ProfileEntry>>>,
    /// Sample counter for rate limiting
    sample_counter: AtomicU64,
    /// Startup window (nanoseconds from start)
    startup_window_ns: u64,
    /// First frame window (nanoseconds from start)
    first_frame_window_ns: u64,
}

impl RuntimeProfiler {
    /// Create a new runtime profiler
    pub fn new(config: ProfileConfig) -> Self {
        Self {
            config,
            active: AtomicBool::new(false),
            start_time: RwLock::new(None),
            entries: RwLock::new(HashMap::new()),
            sample_counter: AtomicU64::new(0),
            startup_window_ns: 100_000_000,      // 100ms
            first_frame_window_ns: 500_000_000,  // 500ms
        }
    }

    /// Create with default config
    pub fn default_profiler() -> Self {
        Self::new(ProfileConfig::default())
    }

    /// Set the startup window duration
    pub fn set_startup_window(&mut self, duration: Duration) {
        self.startup_window_ns = duration.as_nanos() as u64;
    }

    /// Set the first frame window duration
    pub fn set_first_frame_window(&mut self, duration: Duration) {
        self.first_frame_window_ns = duration.as_nanos() as u64;
    }

    /// Start profiling
    pub fn start(&self) {
        *self.start_time.write() = Some(Instant::now());
        self.active.store(true, Ordering::SeqCst);
    }

    /// Stop profiling
    pub fn stop(&self) {
        self.active.store(false, Ordering::SeqCst);
    }

    /// Check if profiling is active
    pub fn is_active(&self) -> bool {
        self.active.load(Ordering::Relaxed)
    }

    /// Record a function call (called from instrumented code)
    #[inline]
    pub fn record_call(&self, function_name: &str) {
        if !self.is_active() {
            return;
        }

        // Sample rate limiting
        let counter = self.sample_counter.fetch_add(1, Ordering::Relaxed);
        if counter % self.config.sample_rate as u64 != 0 {
            return;
        }

        self.record_call_internal(function_name);
    }

    /// Record a function call with timing
    #[inline]
    pub fn record_call_with_duration(&self, function_name: &str, duration_ns: u64) {
        if !self.is_active() {
            return;
        }

        // Sample rate limiting
        let counter = self.sample_counter.fetch_add(1, Ordering::Relaxed);
        if counter % self.config.sample_rate as u64 != 0 {
            return;
        }

        self.record_call_internal_with_time(function_name, duration_ns);
    }

    fn record_call_internal(&self, function_name: &str) {
        let now_ns = self.elapsed_ns();

        let entries = self.entries.read();
        if let Some(entry) = entries.get(function_name) {
            entry.call_count.fetch_add(1, Ordering::Relaxed);
            entry.last_call_ns.store(now_ns, Ordering::Relaxed);

            // Set first call if not set
            entry.first_call_ns.compare_exchange(
                0,
                now_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ).ok();
            return;
        }
        drop(entries);

        // Need to insert new entry
        if self.entries.read().len() >= self.config.max_functions {
            return; // At capacity
        }

        let entry = Arc::new(ProfileEntry::new());
        entry.call_count.store(1, Ordering::Relaxed);
        entry.first_call_ns.store(now_ns, Ordering::Relaxed);
        entry.last_call_ns.store(now_ns, Ordering::Relaxed);

        self.entries.write().insert(function_name.to_string(), entry);
    }

    fn record_call_internal_with_time(&self, function_name: &str, duration_ns: u64) {
        let now_ns = self.elapsed_ns();

        let entries = self.entries.read();
        if let Some(entry) = entries.get(function_name) {
            entry.call_count.fetch_add(1, Ordering::Relaxed);
            entry.total_time_ns.fetch_add(duration_ns, Ordering::Relaxed);
            entry.last_call_ns.store(now_ns, Ordering::Relaxed);

            entry.first_call_ns.compare_exchange(
                0,
                now_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ).ok();
            return;
        }
        drop(entries);

        if self.entries.read().len() >= self.config.max_functions {
            return;
        }

        let entry = Arc::new(ProfileEntry::new());
        entry.call_count.store(1, Ordering::Relaxed);
        entry.total_time_ns.store(duration_ns, Ordering::Relaxed);
        entry.first_call_ns.store(now_ns, Ordering::Relaxed);
        entry.last_call_ns.store(now_ns, Ordering::Relaxed);

        self.entries.write().insert(function_name.to_string(), entry);
    }

    fn elapsed_ns(&self) -> u64 {
        self.start_time
            .read()
            .map(|t| t.elapsed().as_nanos() as u64)
            .unwrap_or(0)
    }

    /// Collect runtime metrics
    pub fn collect_metrics(&self) -> RuntimeMetrics {
        let duration = self.start_time
            .read()
            .map(|t| t.elapsed())
            .unwrap_or_default();

        let duration_secs = duration.as_secs_f64();
        let entries = self.entries.read();

        let mut stats: Vec<FunctionStats> = entries
            .iter()
            .map(|(name, entry)| {
                let call_count = entry.call_count.load(Ordering::Relaxed);
                let first_call_ns = entry.first_call_ns.load(Ordering::Relaxed);

                let mut stat = FunctionStats {
                    name: name.clone(),
                    call_count,
                    total_time_ns: entry.total_time_ns.load(Ordering::Relaxed),
                    first_call_ns,
                    last_call_ns: entry.last_call_ns.load(Ordering::Relaxed),
                    inferred_phase: LayoutPhase::Steady,
                    confidence: 0.0,
                };

                // Infer phase based on call patterns
                let (phase, confidence) = self.infer_phase(&stat, duration_secs);
                stat.inferred_phase = phase;
                stat.confidence = confidence;

                stat
            })
            .collect();

        // Sort by call count descending
        stats.sort_by(|a, b| b.call_count.cmp(&a.call_count));

        let total_calls = stats.iter().map(|s| s.call_count).sum();
        let hot_functions = stats.iter().filter(|s| s.inferred_phase == LayoutPhase::Steady).count();
        let cold_functions = stats.iter().filter(|s| s.inferred_phase == LayoutPhase::Cold).count();
        let startup_functions = stats.iter().filter(|s| s.inferred_phase == LayoutPhase::Startup).count();

        RuntimeMetrics {
            duration,
            total_calls,
            unique_functions: stats.len(),
            hot_functions,
            cold_functions,
            startup_functions,
            estimated_page_savings: self.estimate_page_savings(&stats),
            function_stats: stats,
        }
    }

    /// Infer layout phase for a function based on its runtime behavior
    fn infer_phase(&self, stat: &FunctionStats, duration_secs: f64) -> (LayoutPhase, f64) {
        let calls_per_sec = stat.calls_per_second(duration_secs);
        let first_call_ns = stat.first_call_ns;

        // Startup: called only at the beginning, rarely afterward
        if first_call_ns < self.startup_window_ns {
            if stat.call_count <= 5 {
                return (LayoutPhase::Startup, 0.9);
            }
            if first_call_ns < self.startup_window_ns / 2 && calls_per_sec < 10.0 {
                return (LayoutPhase::Startup, 0.7);
            }
        }

        // First frame: called early and moderately
        if first_call_ns < self.first_frame_window_ns {
            if stat.call_count <= 20 && calls_per_sec < 50.0 {
                return (LayoutPhase::FirstFrame, 0.8);
            }
        }

        // Hot (Steady): called frequently
        if calls_per_sec >= self.config.hot_threshold {
            return (LayoutPhase::Steady, 0.9);
        }

        // Cold: rarely called
        if calls_per_sec < self.config.cold_threshold {
            return (LayoutPhase::Cold, 0.8);
        }

        // Default to steady with moderate confidence
        (LayoutPhase::Steady, 0.5)
    }

    /// Estimate page savings from optimal layout
    fn estimate_page_savings(&self, stats: &[FunctionStats]) -> usize {
        const PAGE_SIZE: usize = 4096;
        const AVG_FUNC_SIZE: usize = 200; // Assume average function is 200 bytes

        // Count startup functions
        let startup_count = stats.iter()
            .filter(|s| s.inferred_phase == LayoutPhase::Startup)
            .count();

        // Estimate pages for startup code
        let startup_pages = (startup_count * AVG_FUNC_SIZE + PAGE_SIZE - 1) / PAGE_SIZE;

        // Without optimization, startup code is scattered
        // Estimate 2x more pages touched
        startup_pages
    }

    /// Generate layout feedback based on profiling data
    pub fn generate_layout_feedback(&self) -> LayoutFeedback {
        let metrics = self.collect_metrics();

        if metrics.total_calls < self.config.min_samples {
            return LayoutFeedback {
                confidence: 0.0,
                sample_count: metrics.total_calls,
                ..Default::default()
            };
        }

        let mut feedback = LayoutFeedback {
            sample_count: metrics.total_calls,
            confidence: 0.0,
            ..Default::default()
        };

        let mut total_confidence = 0.0;
        let mut count = 0;

        for stat in &metrics.function_stats {
            if stat.confidence < 0.6 {
                continue; // Skip low-confidence inferences
            }

            total_confidence += stat.confidence;
            count += 1;

            match stat.inferred_phase {
                LayoutPhase::Startup => {
                    feedback.promote_to_startup.push(stat.name.clone());
                }
                LayoutPhase::FirstFrame => {
                    feedback.promote_to_first_frame.push(stat.name.clone());
                }
                LayoutPhase::Steady => {
                    feedback.promote_to_steady.push(stat.name.clone());
                }
                LayoutPhase::Cold => {
                    feedback.demote_to_cold.push(stat.name.clone());
                }
            }
        }

        if count > 0 {
            feedback.confidence = total_confidence / count as f64;
        }

        feedback
    }

    /// Clear all profiling data
    pub fn clear(&self) {
        self.entries.write().clear();
        self.sample_counter.store(0, Ordering::Relaxed);
    }

    /// Get the current sample count
    pub fn sample_count(&self) -> u64 {
        self.sample_counter.load(Ordering::Relaxed)
    }
}

impl Default for RuntimeProfiler {
    fn default() -> Self {
        Self::new(ProfileConfig::default())
    }
}

// Global profiler instance for easy access
static GLOBAL_PROFILER: OnceLock<RuntimeProfiler> = OnceLock::new();

/// Get the global runtime profiler
pub fn global_profiler() -> &'static RuntimeProfiler {
    GLOBAL_PROFILER.get_or_init(RuntimeProfiler::default_profiler)
}

/// Start global profiling
pub fn start_profiling() {
    global_profiler().start();
}

/// Stop global profiling
pub fn stop_profiling() {
    global_profiler().stop();
}

/// Record a function call to the global profiler
#[inline]
pub fn record_call(function_name: &str) {
    global_profiler().record_call(function_name);
}

/// Collect metrics from the global profiler
pub fn collect_global_metrics() -> RuntimeMetrics {
    global_profiler().collect_metrics()
}

/// Generate layout feedback from the global profiler
pub fn generate_global_feedback() -> LayoutFeedback {
    global_profiler().generate_layout_feedback()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profiler_basic() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1, // Sample every call
            ..Default::default()
        });

        profiler.start();

        // Record some calls
        for _ in 0..100 {
            profiler.record_call("hot_function");
        }
        for _ in 0..5 {
            profiler.record_call("cold_function");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        assert_eq!(metrics.unique_functions, 2);
        assert!(metrics.total_calls >= 100);
    }

    #[test]
    fn test_phase_inference() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            hot_threshold: 10.0,
            cold_threshold: 0.5,
            ..Default::default()
        });

        profiler.start();

        // Simulate startup function (called once at start)
        profiler.record_call("init");

        // Wait a bit then call hot function many times
        std::thread::sleep(std::time::Duration::from_millis(10));
        for _ in 0..1000 {
            profiler.record_call("render");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();

        // Find the functions
        let init_stat = metrics.function_stats.iter().find(|s| s.name == "init");
        let render_stat = metrics.function_stats.iter().find(|s| s.name == "render");

        assert!(init_stat.is_some());
        assert!(render_stat.is_some());

        // Init should be startup, render should be steady
        assert_eq!(init_stat.unwrap().inferred_phase, LayoutPhase::Startup);
        assert_eq!(render_stat.unwrap().inferred_phase, LayoutPhase::Steady);
    }

    #[test]
    fn test_layout_feedback() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            min_samples: 10,
            ..Default::default()
        });

        profiler.start();

        // Generate enough samples
        profiler.record_call("startup_func");
        for _ in 0..100 {
            profiler.record_call("hot_func");
        }

        profiler.stop();

        let feedback = profiler.generate_layout_feedback();

        assert!(feedback.has_recommendations());
        assert!(feedback.confidence > 0.0);
    }

    #[test]
    fn test_feedback_to_sdn() {
        let feedback = LayoutFeedback {
            promote_to_startup: vec!["init".to_string()],
            promote_to_steady: vec!["render".to_string(), "update".to_string()],
            demote_to_cold: vec!["debug".to_string()],
            confidence: 0.85,
            sample_count: 10000,
            ..Default::default()
        };

        let sdn = feedback.to_sdn();

        assert!(sdn.contains("init: startup"));
        assert!(sdn.contains("render: steady"));
        assert!(sdn.contains("debug: cold"));
        assert!(sdn.contains("85.0%"));
    }

    #[test]
    fn test_sample_rate() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 10, // Sample 1 in 10
            ..Default::default()
        });

        profiler.start();

        for _ in 0..100 {
            profiler.record_call("test_func");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        // Should have roughly 10 samples (100 / 10)
        assert!(metrics.total_calls >= 5 && metrics.total_calls <= 15);
    }

    #[test]
    fn test_metrics_top_hot() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            ..Default::default()
        });

        profiler.start();

        for _ in 0..100 {
            profiler.record_call("very_hot");
        }
        for _ in 0..50 {
            profiler.record_call("somewhat_hot");
        }
        for _ in 0..10 {
            profiler.record_call("lukewarm");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        let top = metrics.top_hot_functions(2);

        assert_eq!(top.len(), 2);
        assert_eq!(top[0].name, "very_hot");
        assert_eq!(top[1].name, "somewhat_hot");
    }
}
