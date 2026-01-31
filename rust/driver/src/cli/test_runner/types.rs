//! Test runner types and data structures.
//!
//! Defines core types used throughout the test runner including
//! test options, results, and output formats.

use std::path::PathBuf;
use std::sync::OnceLock;

/// Debug logging level for test runner
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DebugLevel {
    /// No debug output
    None,
    /// High-level phases only
    Basic,
    /// Per-test information
    Detailed,
    /// Full data flow tracing
    Trace,
}

impl DebugLevel {
    /// Get debug level from environment variable SIMPLE_TEST_DEBUG
    pub fn from_env() -> Self {
        static DEBUG_LEVEL: OnceLock<DebugLevel> = OnceLock::new();
        *DEBUG_LEVEL.get_or_init(|| match std::env::var("SIMPLE_TEST_DEBUG").as_deref() {
            Ok("trace") | Ok("TRACE") => DebugLevel::Trace,
            Ok("detailed") | Ok("DETAILED") => DebugLevel::Detailed,
            Ok("basic") | Ok("BASIC") => DebugLevel::Basic,
            _ => DebugLevel::None,
        })
    }

    /// Check if debug logging is enabled at this level
    pub fn is_enabled(level: DebugLevel) -> bool {
        Self::from_env() >= level
    }
}

/// Debug logging macro - only logs if debug level is enabled
macro_rules! debug_log {
    ($level:expr, $phase:expr, $($arg:tt)*) => {
        if DebugLevel::is_enabled($level) {
            eprintln!("[DEBUG:{}] {}", $phase, format!($($arg)*));
        }
    };
}

// Export the macro for use in other modules
pub(crate) use debug_log;

/// Test execution mode
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TestExecutionMode {
    /// Interpreter mode (current default)
    #[default]
    Interpreter,
    /// SMF loader mode (compile to SMF, load via Settlement)
    Smf,
    /// Native binary mode (compile to ELF, run as subprocess)
    Native,
}

impl TestExecutionMode {
    /// Parse from string (for CLI)
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "interpreter" | "interp" => Some(Self::Interpreter),
            "smf" | "loader" => Some(Self::Smf),
            "native" | "binary" => Some(Self::Native),
            _ => None,
        }
    }

    /// Display name
    pub fn name(&self) -> &'static str {
        match self {
            Self::Interpreter => "interpreter",
            Self::Smf => "smf",
            Self::Native => "native",
        }
    }
}

/// Test level filter
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestLevel {
    All,
    Unit,
    Integration,
    System,
}

/// Output format for test results
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// Default text format with colors
    #[default]
    Text,
    /// JSON format for machine-readable output
    Json,
    /// Nested documentation format (like RSpec)
    Doc,
}

/// Options for the test runner
///
/// Default behavior: Sequential (single-threaded) test execution.
/// Parallel execution requires explicit `--parallel` or `-p` flag.
#[derive(Debug, Clone)]
pub struct TestOptions {
    /// Test path (file or directory)
    pub path: Option<PathBuf>,
    /// Test level filter
    pub level: TestLevel,
    /// Tag filter
    pub tag: Option<String>,
    /// Stop on first failure
    pub fail_fast: bool,
    /// Random seed for shuffle
    pub seed: Option<u64>,
    /// Enable GC logging
    pub gc_log: bool,
    /// Disable GC
    pub gc_off: bool,
    /// Output format
    pub format: OutputFormat,
    /// Watch mode - auto-rerun on file changes
    pub watch: bool,
    /// Run doctests from .spl files in src directory
    pub doctest_src: bool,
    /// Run doctests from .md files in doc directory
    pub doctest_doc: bool,
    /// Run doctests from .md files using README.md hierarchy
    pub doctest_md: bool,
    /// Source directory for doctest discovery (default: "src" or "simple/std_lib")
    pub doctest_src_dir: Option<PathBuf>,
    /// Doc directory for doctest discovery (default: "doc")
    pub doctest_doc_dir: Option<PathBuf>,
    /// Root directory for README.md-based doctest discovery
    pub doctest_md_dir: Option<PathBuf>,
    /// Generate sequence diagrams for tests
    pub seq_diagram: bool,
    /// Generate class diagrams from sequences
    pub class_diagram: bool,
    /// Generate architecture diagrams
    pub arch_diagram: bool,
    /// Generate all diagram types
    pub diagram_all: bool,
    /// Include filter for diagrams (comma-separated patterns)
    pub seq_include: Option<String>,
    /// Exclude filter for diagrams (comma-separated patterns)
    pub seq_exclude: Option<String>,
    /// Output directory for diagrams
    pub diagram_output: Option<PathBuf>,
    /// Capture GUI screenshots for @gui tagged tests
    pub capture_screenshots: bool,
    /// Force refresh all GUI screenshots (recapture even if exists)
    pub refresh_gui_images: bool,
    /// Output directory for GUI screenshots (default: doc/spec/image)
    pub screenshot_output: Option<PathBuf>,
    /// List tests without running them
    pub list: bool,
    /// List ignored tests only
    pub list_ignored: bool,
    /// Run only slow tests (slow_it)
    pub only_slow: bool,
    /// Run only skipped tests (skip tag)
    pub only_skipped: bool,
    /// List features from skipped test files
    pub list_skip_features: bool,
    /// Filter skip features to show only planned (not implemented)
    pub skip_features_planned_only: bool,
    /// Show tags in test output
    pub show_tags: bool,
    /// Test execution mode (interpreter, smf, native)
    pub execution_mode: TestExecutionMode,
    /// Force rebuild of cached test artifacts
    pub force_rebuild: bool,
    /// Keep compiled test artifacts after run
    pub keep_artifacts: bool,
    /// Run each test file in a separate process (safe mode)
    pub safe_mode: bool,
    /// Timeout in seconds for each test file in safe mode (default: 120)
    pub safe_mode_timeout: u64,
    /// Enable parallel test execution (requires safe_mode)
    pub parallel: bool,
    /// Maximum number of threads (0 = auto-detect all cores)
    pub max_threads: usize,
    /// CPU usage percentage threshold to trigger throttling (0-100)
    pub cpu_threshold: u8,
    /// Memory usage percentage threshold to trigger throttling (0-100)
    pub memory_threshold: u8,
    /// Number of threads when throttled
    pub throttled_threads: usize,
    /// Ignore CPU/memory limits (full parallel mode)
    pub full_parallel: bool,
    /// Seconds between resource usage checks
    pub cpu_check_interval: u64,
    /// Enable runtime profiling
    pub profile: bool,
    /// Profile mode (statistics, sequence, combined)
    pub profile_mode: Option<String>,
    /// Include Rust test results in database
    pub rust_tests: bool,
    /// Only track ignored Rust tests (skip running all)
    pub rust_ignored_only: bool,

    // Run management options
    /// List test runs
    pub list_runs: bool,
    /// Cleanup stale runs (mark as crashed)
    pub cleanup_runs: bool,
    /// Prune old runs (delete, keeping only N most recent)
    pub prune_runs: Option<usize>,
    /// Filter runs by status for listing
    pub runs_status_filter: Option<String>,
}

impl Default for TestOptions {
    fn default() -> Self {
        Self {
            path: None,
            level: TestLevel::All,
            tag: None,
            fail_fast: false,
            seed: None,
            gc_log: false,
            gc_off: false,
            format: OutputFormat::Text,
            watch: false,
            doctest_src: false,
            doctest_doc: false,
            doctest_md: false,
            doctest_src_dir: None,
            doctest_doc_dir: None,
            doctest_md_dir: None,
            seq_diagram: false,
            class_diagram: false,
            arch_diagram: false,
            diagram_all: false,
            seq_include: None,
            seq_exclude: None,
            diagram_output: None,
            capture_screenshots: false,
            refresh_gui_images: false,
            screenshot_output: None,
            list: false,
            list_ignored: false,
            only_slow: false,
            only_skipped: false,
            list_skip_features: false,
            skip_features_planned_only: false,
            show_tags: false,
            execution_mode: TestExecutionMode::Interpreter,
            force_rebuild: false,
            keep_artifacts: false,
            safe_mode: false,
            safe_mode_timeout: 120,
            // Default: sequential (single-threaded) execution
            // Parallel requires explicit --parallel or -p flag
            parallel: false,
            max_threads: 0, // Auto-detect (only used when parallel=true)
            cpu_threshold: 70,
            memory_threshold: 70,
            throttled_threads: 1,
            full_parallel: false,
            cpu_check_interval: 5,
            profile: false,
            profile_mode: None,
            rust_tests: false,
            rust_ignored_only: false,

            // Run management
            list_runs: false,
            cleanup_runs: false,
            prune_runs: None,
            runs_status_filter: None,
        }
    }
}

/// Test result for a single file
#[derive(Debug)]
pub struct TestFileResult {
    pub path: PathBuf,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub ignored: usize,
    pub duration_ms: u64,
    pub error: Option<String>,
}

/// Overall test run result
#[derive(Debug)]
pub struct TestRunResult {
    pub files: Vec<TestFileResult>,
    pub total_passed: usize,
    pub total_failed: usize,
    pub total_skipped: usize,
    pub total_ignored: usize,
    pub total_duration_ms: u64,
}

impl TestRunResult {
    pub fn success(&self) -> bool {
        self.total_failed == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_result_success() {
        let result = TestRunResult {
            files: vec![],
            total_passed: 10,
            total_failed: 0,
            total_skipped: 0,
            total_ignored: 0,
            total_duration_ms: 100,
        };
        assert!(result.success());

        let failed_result = TestRunResult {
            files: vec![],
            total_passed: 10,
            total_failed: 1,
            total_skipped: 0,
            total_ignored: 0,
            total_duration_ms: 100,
        };
        assert!(!failed_result.success());
    }

    #[test]
    fn test_options_default() {
        let opts = TestOptions::default();
        assert_eq!(opts.level, TestLevel::All);
        assert_eq!(opts.format, OutputFormat::Text);
        assert!(!opts.fail_fast);
        assert!(!opts.watch);
    }
}
