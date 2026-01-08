//! Layout feedback generation

use crate::hir::{LayoutConfig, LayoutPhase};

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