//! Function statistics and runtime metrics

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use crate::hir::LayoutPhase;

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
    pub hot_fields: Vec<String>,
    pub cold_fields: Vec<String>,
}
