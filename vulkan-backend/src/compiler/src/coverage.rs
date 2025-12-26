//! Code coverage tracking module
//!
//! Provides coverage tracking for the Simple compiler.

use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// Coverage tracker
#[derive(Debug, Clone, Default)]
pub struct CoverageTracker {
    function_calls: HashMap<String, usize>,
}

impl CoverageTracker {
    /// Create a new coverage tracker
    pub fn new() -> Self {
        Self {
            function_calls: HashMap::new(),
        }
    }

    /// Record a function call
    pub fn record_function_call(&mut self, function_name: &str) {
        *self.function_calls.entry(function_name.to_string()).or_insert(0) += 1;
    }

    /// Get function call counts
    pub fn get_function_calls(&self) -> &HashMap<String, usize> {
        &self.function_calls
    }
}

/// Thread-safe coverage tracker
pub type SharedCoverageTracker = Arc<Mutex<CoverageTracker>>;

/// Create a new shared coverage tracker
pub fn create_coverage_tracker() -> SharedCoverageTracker {
    Arc::new(Mutex::new(CoverageTracker::new()))
}

/// Global coverage tracker (optional, for interpreter use)
static GLOBAL_COVERAGE: once_cell::sync::Lazy<Option<SharedCoverageTracker>> =
    once_cell::sync::Lazy::new(|| {
        // Coverage is disabled by default
        None
    });

/// Get the global coverage tracker if enabled
pub fn get_global_coverage() -> Option<SharedCoverageTracker> {
    GLOBAL_COVERAGE.clone()
}
