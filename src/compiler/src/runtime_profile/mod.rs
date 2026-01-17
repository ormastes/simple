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

pub mod config;
pub mod diagram;
pub mod feedback;
pub mod profiler;
pub mod stats;

#[cfg(test)]
mod tests;

// Re-export public API
pub use config::{
    CallType, FunctionRuntimeStats, ProfileConfig, ProfileData, ProfileMetadata, ProfileMode, SequenceEvent,
};
pub use diagram::{
    generate_arch_diagram, generate_arch_from_events, generate_class_diagram, generate_class_from_events,
    generate_sequence_diagram, generate_sequence_from_events, DiagramFormat, DiagramOptions,
};
pub use feedback::LayoutFeedback;
pub use profiler::{
    collect_global_metrics, generate_global_feedback, global_profiler, record_call, start_profiling, stop_profiling,
    RuntimeProfiler,
};
pub use stats::{FunctionStats, RuntimeMetrics};
