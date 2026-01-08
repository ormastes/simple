//! Runtime profiler implementation

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use parking_lot::RwLock;

use crate::hir::LayoutPhase;

use super::config::ProfileConfig;
use super::stats::{FunctionStats, RuntimeMetrics};
use super::feedback::LayoutFeedback;

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

    // Tests will be added here
}
