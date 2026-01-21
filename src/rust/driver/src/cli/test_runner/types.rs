//! Test runner types and data structures.
//!
//! Defines core types used throughout the test runner including
//! test options, results, and output formats.

use std::path::PathBuf;

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
        }
    }
}

/// Test result for a single file
#[derive(Debug)]
pub struct TestFileResult {
    pub path: PathBuf,
    pub passed: usize,
    pub failed: usize,
    pub duration_ms: u64,
    pub error: Option<String>,
}

/// Overall test run result
#[derive(Debug)]
pub struct TestRunResult {
    pub files: Vec<TestFileResult>,
    pub total_passed: usize,
    pub total_failed: usize,
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
            total_duration_ms: 100,
        };
        assert!(result.success());

        let failed_result = TestRunResult {
            files: vec![],
            total_passed: 10,
            total_failed: 1,
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
