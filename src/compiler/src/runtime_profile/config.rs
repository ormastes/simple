//! Profiling configuration

use std::time::Duration;

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
pub struct FunctionRuntimeStats {
    pub function_name: String,
    pub call_count: u64,
    pub total_time_ns: u64,
}
