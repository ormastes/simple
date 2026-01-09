//! Profiling configuration

use std::time::Duration;

/// Profile mode - determines what data is collected
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProfileMode {
    /// Profiling disabled
    Off,
    /// Original profiling - aggregated statistics only (lowest overhead)
    Statistics,
    /// Sequence profiling - ordered call events for diagrams
    Sequence,
    /// Combined - both statistics and sequence data (default)
    #[default]
    Combined,
}

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
    /// Profile mode - statistics, sequence, or combined
    pub mode: ProfileMode,
    /// Maximum sequence events to record (0 = unlimited)
    pub max_sequence_events: usize,
    /// Whether to capture argument values in sequence mode
    pub capture_args: bool,
    /// Whether to capture return values in sequence mode
    pub capture_returns: bool,
    /// Include filter patterns for sequence (comma-separated globs)
    pub sequence_include: Option<String>,
    /// Exclude filter patterns for sequence (comma-separated globs)
    pub sequence_exclude: Option<String>,
}

impl Default for ProfileConfig {
    fn default() -> Self {
        Self {
            sample_rate: 1,       // Record every call (Combined mode default)
            max_functions: 10000, // Track up to 10k functions
            track_call_stacks: true,
            hot_threshold: 100.0,        // 100+ calls/sec = hot
            cold_threshold: 1.0,         // <1 call/sec = cold
            min_samples: 1000,           // Need 1000 samples before recommendations
            mode: ProfileMode::Combined, // Combined is default
            max_sequence_events: 100000, // 100k events max
            capture_args: true,
            capture_returns: true,
            sequence_include: None,
            sequence_exclude: None,
        }
    }
}

impl ProfileConfig {
    /// Create a disabled config (no profiling)
    pub fn off() -> Self {
        Self {
            mode: ProfileMode::Off,
            sample_rate: 0,
            track_call_stacks: false,
            capture_args: false,
            capture_returns: false,
            ..Default::default()
        }
    }

    /// Create a statistics-only config (original profiling)
    pub fn statistics_only() -> Self {
        Self {
            sample_rate: 100, // Sample 1 in 100 for lower overhead
            track_call_stacks: false,
            mode: ProfileMode::Statistics,
            capture_args: false,
            capture_returns: false,
            ..Default::default()
        }
    }

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
            mode: ProfileMode::Statistics,
            capture_args: false,
            capture_returns: false,
            ..Default::default()
        }
    }

    /// Create a sequence profiling config for diagram generation
    pub fn sequence() -> Self {
        Self {
            sample_rate: 1, // Record every call for accurate sequences
            track_call_stacks: true,
            mode: ProfileMode::Sequence,
            capture_args: true,
            capture_returns: true,
            ..Default::default()
        }
    }

    /// Create a combined config (statistics + sequence) - this is the default
    pub fn combined() -> Self {
        Self::default()
    }

    /// Create a sequence config with filtering
    pub fn sequence_filtered(include: Option<String>, exclude: Option<String>) -> Self {
        Self {
            sample_rate: 1,
            track_call_stacks: true,
            mode: ProfileMode::Sequence,
            capture_args: true,
            capture_returns: true,
            sequence_include: include,
            sequence_exclude: exclude,
            ..Default::default()
        }
    }

    /// Check if profiling is enabled
    pub fn is_enabled(&self) -> bool {
        !matches!(self.mode, ProfileMode::Off)
    }

    /// Check if sequence recording is enabled
    pub fn records_sequence(&self) -> bool {
        matches!(self.mode, ProfileMode::Sequence | ProfileMode::Combined)
    }

    /// Check if statistics recording is enabled
    pub fn records_statistics(&self) -> bool {
        matches!(self.mode, ProfileMode::Statistics | ProfileMode::Combined)
    }

    /// Disable profiling
    pub fn disable(&mut self) {
        self.mode = ProfileMode::Off;
    }

    /// Enable combined mode
    pub fn enable(&mut self) {
        self.mode = ProfileMode::Combined;
    }

    /// Set mode
    pub fn with_mode(mut self, mode: ProfileMode) -> Self {
        self.mode = mode;
        self
    }

    /// Set include filter
    pub fn with_include(mut self, pattern: String) -> Self {
        self.sequence_include = Some(pattern);
        self
    }

    /// Set exclude filter
    pub fn with_exclude(mut self, pattern: String) -> Self {
        self.sequence_exclude = Some(pattern);
        self
    }
}

/// Per-function runtime statistics
#[derive(Debug, Clone, Default)]
pub struct FunctionRuntimeStats {
    pub function_name: String,
    pub call_count: u64,
    pub total_time_ns: u64,
}

/// Call type for sequence events
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallType {
    /// Direct function call
    Direct,
    /// Method call on object
    Method,
    /// Foreign function interface call
    Ffi,
    /// Closure/lambda invocation
    Closure,
    /// Constructor call
    Constructor,
}

impl Default for CallType {
    fn default() -> Self {
        CallType::Direct
    }
}

/// A single call event in the sequence
#[derive(Debug, Clone)]
pub struct SequenceEvent {
    /// Sequence number (global ordering)
    pub sequence_num: u64,
    /// Timestamp in nanoseconds from profiling start
    pub timestamp_ns: u64,
    /// Caller function name
    pub caller: String,
    /// Callee function name
    pub callee: String,
    /// Caller's class (if method call)
    pub caller_class: Option<String>,
    /// Callee's class (if method call)
    pub callee_class: Option<String>,
    /// Argument values (if captured)
    pub arguments: Vec<String>,
    /// Return value (if captured, set on return)
    pub return_value: Option<String>,
    /// Type of call
    pub call_type: CallType,
    /// Call stack depth
    pub depth: u32,
    /// True if this is a return event
    pub is_return: bool,
}

impl SequenceEvent {
    /// Create a new call event
    pub fn new_call(
        sequence_num: u64,
        timestamp_ns: u64,
        caller: String,
        callee: String,
        caller_class: Option<String>,
        callee_class: Option<String>,
        arguments: Vec<String>,
        call_type: CallType,
        depth: u32,
    ) -> Self {
        Self {
            sequence_num,
            timestamp_ns,
            caller,
            callee,
            caller_class,
            callee_class,
            arguments,
            return_value: None,
            call_type,
            depth,
            is_return: false,
        }
    }

    /// Create a new return event
    pub fn new_return(
        sequence_num: u64,
        timestamp_ns: u64,
        caller: String,
        callee: String,
        caller_class: Option<String>,
        callee_class: Option<String>,
        return_value: Option<String>,
        depth: u32,
    ) -> Self {
        Self {
            sequence_num,
            timestamp_ns,
            caller,
            callee,
            caller_class,
            callee_class,
            arguments: Vec::new(),
            return_value,
            call_type: CallType::Direct,
            depth,
            is_return: true,
        }
    }

    /// Get caller participant name for diagrams
    pub fn caller_participant(&self) -> &str {
        self.caller_class.as_deref().unwrap_or(&self.caller)
    }

    /// Get callee participant name for diagrams
    pub fn callee_participant(&self) -> &str {
        self.callee_class.as_deref().unwrap_or(&self.callee)
    }
}
