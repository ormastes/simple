//! Layout recording for 4KB page locality optimization.
//!
//! This module provides runtime instrumentation to record function execution
//! patterns during test runs. The recorded data is used to guide optimal
//! code placement for cache-efficient startup.
//!
//! # Usage
//!
//! ```rust
//! use simple_compiler::layout_recorder::{start_recording, stop_recording, export_layout_sdn};
//!
//! // Enable recording before test execution
//! start_recording();
//!
//! // Run tests...
//!
//! // Stop and export recorded data
//! stop_recording();
//! let sdn = export_layout_sdn();
//! std::fs::write("layout.sdn", sdn).unwrap();
//! ```
//!
//! # What Gets Recorded
//!
//! - **Call counts**: How many times each function is called
//! - **First call timing**: When each function is first called (startup vs steady)
//! - **Call graph edges**: Which functions call which (for grouping)
//! - **Estimated sizes**: Based on AST/IR complexity metrics

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Instant;

use crate::hir::{LayoutConfig, LayoutPhase, RecordedFunction};

/// Global recording state
static RECORDING_ENABLED: AtomicBool = AtomicBool::new(false);
static RECORDING_START: AtomicU64 = AtomicU64::new(0);

/// Per-function execution record
#[derive(Debug, Clone, Default)]
pub struct FunctionRecord {
    /// Function name (fully qualified)
    pub name: String,
    /// Module path
    pub module: Option<String>,
    /// Number of times called
    pub call_count: u64,
    /// Timestamp of first call (microseconds from recording start)
    pub first_call_us: u64,
    /// Timestamp of last call
    pub last_call_us: u64,
    /// Estimated size in bytes (from IR metrics)
    pub estimated_size: u64,
    /// Functions called by this function
    pub callees: Vec<String>,
    /// Whether this function is on the startup path
    pub is_startup_path: bool,
}

impl FunctionRecord {
    /// Create a new function record
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            module: None,
            call_count: 0,
            first_call_us: 0,
            last_call_us: 0,
            estimated_size: 0,
            callees: Vec::new(),
            is_startup_path: false,
        }
    }

    /// Infer layout phase from call timing
    pub fn inferred_phase(&self, first_frame_threshold_us: u64) -> LayoutPhase {
        if self.call_count == 0 {
            return LayoutPhase::Cold;
        }

        // If first called during startup (before first frame)
        if self.first_call_us < first_frame_threshold_us {
            if self.call_count == 1 {
                // Called once during startup = startup code
                LayoutPhase::Startup
            } else if self.first_call_us < first_frame_threshold_us / 2 {
                // Called early and multiple times = first_frame
                LayoutPhase::FirstFrame
            } else {
                LayoutPhase::Steady
            }
        } else if self.call_count < 10 {
            // Called rarely after startup = cold
            LayoutPhase::Cold
        } else {
            // Called frequently after startup = steady
            LayoutPhase::Steady
        }
    }
}

/// Recording session data
#[derive(Debug, Default, Clone)]
pub struct RecordingSession {
    /// Function records keyed by name
    pub functions: HashMap<String, FunctionRecord>,
    /// Current call stack for tracking call graph
    pub call_stack: Vec<String>,
    /// Recording start time
    pub start_time: Option<Instant>,
    /// First frame marker time (microseconds from start)
    pub first_frame_us: Option<u64>,
    /// Event loop entry time (microseconds from start)
    pub event_loop_us: Option<u64>,
}

impl RecordingSession {
    /// Create a new recording session
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            call_stack: Vec::new(),
            start_time: Some(Instant::now()),
            first_frame_us: None,
            event_loop_us: None,
        }
    }

    /// Record a function call entry
    pub fn record_call(&mut self, name: &str) {
        let now_us = self.elapsed_us();

        let record = self.functions.entry(name.to_string()).or_insert_with(|| {
            let mut r = FunctionRecord::new(name);
            r.first_call_us = now_us;
            r
        });

        record.call_count += 1;
        record.last_call_us = now_us;

        // Track call graph
        if let Some(caller) = self.call_stack.last() {
            if let Some(caller_record) = self.functions.get_mut(caller) {
                if !caller_record.callees.contains(&name.to_string()) {
                    caller_record.callees.push(name.to_string());
                }
            }
        }

        self.call_stack.push(name.to_string());
    }

    /// Record function exit
    pub fn record_return(&mut self) {
        self.call_stack.pop();
    }

    /// Record a layout marker
    pub fn record_marker(&mut self, marker: &str) {
        let now_us = self.elapsed_us();

        match marker {
            "first_frame" | "ui.ready" | "startup.complete" => {
                if self.first_frame_us.is_none() {
                    self.first_frame_us = Some(now_us);
                }
            }
            "event_loop.enter" | "main_loop" => {
                if self.event_loop_us.is_none() {
                    self.event_loop_us = Some(now_us);
                }
            }
            _ => {
                // Custom markers are recorded as function calls
                self.record_call(&format!("marker:{}", marker));
                self.record_return();
            }
        }
    }

    /// Set estimated size for a function
    pub fn set_function_size(&mut self, name: &str, size: u64) {
        if let Some(record) = self.functions.get_mut(name) {
            record.estimated_size = size;
        }
    }

    /// Get elapsed time in microseconds
    fn elapsed_us(&self) -> u64 {
        self.start_time.map(|t| t.elapsed().as_micros() as u64).unwrap_or(0)
    }

    /// Get the first frame threshold for phase inference
    pub fn first_frame_threshold(&self) -> u64 {
        // Use recorded first_frame marker, or default to 100ms
        self.first_frame_us.unwrap_or(100_000)
    }

    /// Export recorded data as RecordedFunction entries
    pub fn to_recorded_functions(&self) -> Vec<RecordedFunction> {
        let threshold = self.first_frame_threshold();

        self.functions
            .values()
            .map(|r| RecordedFunction::new(&r.name, r.inferred_phase(threshold), r.estimated_size, r.call_count))
            .collect()
    }

    /// Export to LayoutConfig
    pub fn to_layout_config(&self) -> LayoutConfig {
        let mut config = LayoutConfig::new();
        config.recorded = self.to_recorded_functions();
        config
    }
}

// Thread-local recording session
thread_local! {
    static RECORDING_SESSION: RefCell<Option<RecordingSession>> = RefCell::new(None);
}

/// Start recording function execution
pub fn start_recording() {
    RECORDING_ENABLED.store(true, Ordering::SeqCst);
    RECORDING_START.store(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64,
        Ordering::SeqCst,
    );

    RECORDING_SESSION.with(|cell| {
        *cell.borrow_mut() = Some(RecordingSession::new());
    });
}

/// Stop recording
pub fn stop_recording() {
    RECORDING_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if recording is enabled
pub fn is_recording() -> bool {
    RECORDING_ENABLED.load(Ordering::Relaxed)
}

/// Record a function call (called from interpreter)
pub fn record_function_call(name: &str) {
    if !is_recording() {
        return;
    }

    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow_mut().as_mut() {
            session.record_call(name);
        }
    });
}

/// Record function return
pub fn record_function_return() {
    if !is_recording() {
        return;
    }

    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow_mut().as_mut() {
            session.record_return();
        }
    });
}

/// Record a layout marker
pub fn record_layout_marker(marker: &str) {
    if !is_recording() {
        return;
    }

    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow_mut().as_mut() {
            session.record_marker(marker);
        }
    });
}

/// Set estimated size for a function
pub fn set_function_size(name: &str, size: u64) {
    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow_mut().as_mut() {
            session.set_function_size(name, size);
        }
    });
}

/// Get the current recording session (for testing)
pub fn get_recording_session() -> Option<RecordingSession> {
    RECORDING_SESSION.with(|cell| cell.borrow().as_ref().cloned())
}

/// Export recorded layout data as SDN string
pub fn export_layout_sdn() -> String {
    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow().as_ref() {
            session.to_layout_config().to_sdn()
        } else {
            LayoutConfig::new().to_sdn()
        }
    })
}

/// Export recorded layout data as LayoutConfig
pub fn export_layout_config() -> LayoutConfig {
    RECORDING_SESSION.with(|cell| {
        if let Some(session) = cell.borrow().as_ref() {
            session.to_layout_config()
        } else {
            LayoutConfig::new()
        }
    })
}

/// Clear recorded data
pub fn clear_recording() {
    RECORDING_SESSION.with(|cell| {
        *cell.borrow_mut() = None;
    });
}

/// Merge recorded data with existing layout config
pub fn merge_with_config(base: &LayoutConfig) -> LayoutConfig {
    let mut merged = base.clone();
    let recorded = export_layout_config();
    merged.merge(&recorded);
    merged
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_record_phase_inference() {
        let mut record = FunctionRecord::new("test_func");

        // Never called = cold
        assert_eq!(record.inferred_phase(100_000), LayoutPhase::Cold);

        // Called once early = startup
        record.call_count = 1;
        record.first_call_us = 1000;
        assert_eq!(record.inferred_phase(100_000), LayoutPhase::Startup);

        // Called multiple times early = first_frame
        record.call_count = 5;
        record.first_call_us = 10_000;
        assert_eq!(record.inferred_phase(100_000), LayoutPhase::FirstFrame);

        // Called frequently after startup = steady
        record.call_count = 100;
        record.first_call_us = 200_000;
        assert_eq!(record.inferred_phase(100_000), LayoutPhase::Steady);

        // Called rarely after startup = cold
        record.call_count = 2;
        record.first_call_us = 200_000;
        assert_eq!(record.inferred_phase(100_000), LayoutPhase::Cold);
    }

    #[test]
    fn test_recording_session() {
        let mut session = RecordingSession::new();

        session.record_call("main");
        session.record_call("init");
        session.record_return();
        session.record_call("run");
        session.record_return();
        session.record_return();

        assert_eq!(session.functions.len(), 3);
        assert_eq!(session.functions["main"].call_count, 1);
        assert_eq!(session.functions["init"].call_count, 1);
        assert_eq!(session.functions["run"].call_count, 1);

        // Check call graph
        let main_callees = &session.functions["main"].callees;
        assert!(main_callees.contains(&"init".to_string()));
        assert!(main_callees.contains(&"run".to_string()));
    }

    #[test]
    fn test_recording_markers() {
        let mut session = RecordingSession::new();

        session.record_marker("first_frame");
        assert!(session.first_frame_us.is_some());

        session.record_marker("event_loop.enter");
        assert!(session.event_loop_us.is_some());
    }

    #[test]
    fn test_global_recording() {
        clear_recording();
        assert!(!is_recording());

        start_recording();
        assert!(is_recording());

        record_function_call("test_func");
        record_function_call("inner_func");
        record_function_return();
        record_function_return();

        stop_recording();
        assert!(!is_recording());

        let config = export_layout_config();
        assert!(!config.recorded.is_empty());

        clear_recording();
    }

    #[test]
    fn test_export_sdn() {
        clear_recording();
        start_recording();

        record_function_call("main");
        record_function_call("parse_args");
        record_function_return();
        record_layout_marker("first_frame");
        record_function_call("event_loop");
        record_function_return();
        record_function_return();

        stop_recording();

        let sdn = export_layout_sdn();
        assert!(sdn.contains("recorded"));
        assert!(sdn.contains("main"));
        assert!(sdn.contains("parse_args"));

        clear_recording();
    }
}
