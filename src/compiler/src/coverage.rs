//! Coverage tracking for Simple language tests
//!
//! This module provides runtime coverage collection during test execution.
//! Coverage data includes:
//! - Line execution tracking (file → line numbers)
//! - Function call tracking (function name → call count)
//! - FFI call tracking (FFI function → call count)
//!
//! Usage:
//! ```
//! // Enable coverage via environment variable
//! SIMPLE_COVERAGE=1 cargo test simple_stdlib
//!
//! // Output written to SIMPLE_COVERAGE_OUTPUT or default location
//! // target/coverage/simple_coverage.json
//! ```

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// Coverage collector tracks execution during test runs
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoverageCollector {
    /// Maps file paths to sets of executed line numbers
    execution_map: HashMap<PathBuf, HashSet<usize>>,

    /// Maps function names to call counts
    function_calls: HashMap<String, u64>,

    /// Maps FFI function names to call counts
    ffi_calls: HashMap<String, u64>,

    /// Test name (if known)
    test_name: Option<String>,
}

impl CoverageCollector {
    /// Create a new coverage collector
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a collector for a specific test
    pub fn new_for_test(test_name: String) -> Self {
        Self {
            test_name: Some(test_name),
            ..Default::default()
        }
    }

    /// Record execution of a line in a file
    pub fn record_line(&mut self, file: &Path, line: usize) {
        self.execution_map
            .entry(file.to_path_buf())
            .or_insert_with(HashSet::new)
            .insert(line);
    }

    /// Record a function call
    pub fn record_function_call(&mut self, function_name: &str) {
        *self.function_calls.entry(function_name.to_string()).or_insert(0) += 1;
    }

    /// Record an FFI function call
    pub fn record_ffi_call(&mut self, ffi_name: &str) {
        *self.ffi_calls.entry(ffi_name.to_string()).or_insert(0) += 1;
    }

    /// Merge another collector into this one
    pub fn merge(&mut self, other: &CoverageCollector) {
        // Merge execution maps
        for (file, lines) in &other.execution_map {
            self.execution_map
                .entry(file.clone())
                .or_insert_with(HashSet::new)
                .extend(lines);
        }

        // Merge function calls
        for (func, count) in &other.function_calls {
            *self.function_calls.entry(func.clone()).or_insert(0) += count;
        }

        // Merge FFI calls
        for (ffi, count) in &other.ffi_calls {
            *self.ffi_calls.entry(ffi.clone()).or_insert(0) += count;
        }
    }

    /// Save coverage data to JSON file
    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| format!("Failed to serialize coverage: {}", e))?;

        // Create parent directory if needed
        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create directory: {}", e))?;
        }

        fs::write(path.as_ref(), json)
            .map_err(|e| format!("Failed to write coverage file: {}", e))?;

        Ok(())
    }

    /// Load coverage data from JSON file
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Self, String> {
        let json = fs::read_to_string(path.as_ref())
            .map_err(|e| format!("Failed to read coverage file: {}", e))?;

        serde_json::from_str(&json)
            .map_err(|e| format!("Failed to parse coverage file: {}", e))
    }

    /// Get coverage statistics
    pub fn stats(&self) -> CoverageStats {
        let total_lines: usize = self.execution_map.values().map(|s| s.len()).sum();
        let total_files = self.execution_map.len();
        let total_functions = self.function_calls.len();
        let total_ffi_calls = self.ffi_calls.len();

        CoverageStats {
            total_lines,
            total_files,
            total_functions,
            total_ffi_calls,
        }
    }

    /// Get executed lines for a specific file
    pub fn lines_for_file(&self, file: &Path) -> Option<&HashSet<usize>> {
        self.execution_map.get(file)
    }

    /// Check if a line was executed
    pub fn is_line_executed(&self, file: &Path, line: usize) -> bool {
        self.execution_map
            .get(file)
            .map(|lines| lines.contains(&line))
            .unwrap_or(false)
    }

    /// Get function call count
    pub fn function_call_count(&self, function_name: &str) -> u64 {
        self.function_calls.get(function_name).copied().unwrap_or(0)
    }

    /// Get FFI call count
    pub fn ffi_call_count(&self, ffi_name: &str) -> u64 {
        self.ffi_calls.get(ffi_name).copied().unwrap_or(0)
    }
}

/// Coverage statistics summary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageStats {
    pub total_lines: usize,
    pub total_files: usize,
    pub total_functions: usize,
    pub total_ffi_calls: usize,
}

/// Global coverage collector (thread-safe)
static GLOBAL_COVERAGE: Mutex<Option<Arc<Mutex<CoverageCollector>>>> = Mutex::new(None);

/// Initialize global coverage collection (call at test start)
pub fn init_coverage() -> Arc<Mutex<CoverageCollector>> {
    let collector = Arc::new(Mutex::new(CoverageCollector::new()));
    *GLOBAL_COVERAGE.lock().unwrap() = Some(collector.clone());
    collector
}

/// Get the global coverage collector (if initialized)
pub fn get_global_coverage() -> Option<Arc<Mutex<CoverageCollector>>> {
    GLOBAL_COVERAGE.lock().unwrap().clone()
}

/// Check if coverage is enabled via environment variable
pub fn is_coverage_enabled() -> bool {
    std::env::var("SIMPLE_COVERAGE")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false)
}

/// Get coverage output path from environment or default
pub fn get_coverage_output_path() -> PathBuf {
    std::env::var("SIMPLE_COVERAGE_OUTPUT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("target/coverage/simple_coverage.json"))
}

/// Save global coverage to file
pub fn save_global_coverage() -> Result<(), String> {
    if let Some(collector) = get_global_coverage() {
        let collector = collector.lock().unwrap();
        let path = get_coverage_output_path();
        collector.save_to_file(path)?;
    }
    Ok(())
}

/// Coverage validation and checking functions
impl CoverageCollector {
    /// Check if any coverage data was collected
    pub fn has_data(&self) -> bool {
        !self.execution_map.is_empty()
            || !self.function_calls.is_empty()
            || !self.ffi_calls.is_empty()
    }

    /// Validate that minimum coverage was achieved
    pub fn validate_minimum_coverage(
        &self,
        min_lines: usize,
        min_functions: usize,
    ) -> Result<(), String> {
        let stats = self.stats();

        if stats.total_lines < min_lines {
            return Err(format!(
                "Insufficient line coverage: {} < {} required",
                stats.total_lines, min_lines
            ));
        }

        if stats.total_functions < min_functions {
            return Err(format!(
                "Insufficient function coverage: {} < {} required",
                stats.total_functions, min_functions
            ));
        }

        Ok(())
    }

    /// Check if a specific function was called
    pub fn was_function_called(&self, function_name: &str) -> bool {
        self.function_calls.contains_key(function_name)
    }

    /// Check if a specific file was executed
    pub fn was_file_executed(&self, file: &Path) -> bool {
        self.execution_map.contains_key(file)
    }

    /// Get list of all executed files
    pub fn executed_files(&self) -> Vec<PathBuf> {
        self.execution_map.keys().cloned().collect()
    }

    /// Get list of all called functions
    pub fn called_functions(&self) -> Vec<String> {
        self.function_calls.keys().cloned().collect()
    }

    /// Get coverage percentage for a file (if we know total lines)
    pub fn file_coverage_percentage(&self, file: &Path, total_lines: usize) -> f64 {
        if let Some(executed_lines) = self.execution_map.get(file) {
            (executed_lines.len() as f64 / total_lines as f64) * 100.0
        } else {
            0.0
        }
    }

    /// Generate a summary report
    pub fn summary_report(&self) -> String {
        let stats = self.stats();
        let mut report = String::new();

        report.push_str("=== Coverage Summary ===\n");
        report.push_str(&format!("Lines executed: {}\n", stats.total_lines));
        report.push_str(&format!("Files covered: {}\n", stats.total_files));
        report.push_str(&format!("Functions called: {}\n", stats.total_functions));
        report.push_str(&format!("FFI calls: {}\n", stats.total_ffi_calls));

        if !self.function_calls.is_empty() {
            report.push_str("\nTop Functions:\n");
            let mut funcs: Vec<_> = self.function_calls.iter().collect();
            funcs.sort_by(|a, b| b.1.cmp(a.1)); // Sort by call count descending
            for (func, count) in funcs.iter().take(10) {
                report.push_str(&format!("  {} : {} calls\n", func, count));
            }
        }

        if !self.ffi_calls.is_empty() {
            report.push_str("\nFFI Calls:\n");
            for (ffi, count) in &self.ffi_calls {
                report.push_str(&format!("  {} : {} calls\n", ffi, count));
            }
        }

        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coverage_collector_basic() {
        let mut cov = CoverageCollector::new();

        // Record some execution
        cov.record_line(Path::new("test.spl"), 10);
        cov.record_line(Path::new("test.spl"), 11);
        cov.record_line(Path::new("test.spl"), 10); // Duplicate

        cov.record_function_call("main");
        cov.record_function_call("main");

        cov.record_ffi_call("__builtin_array_push");

        // Check stats
        let stats = cov.stats();
        assert_eq!(stats.total_lines, 2); // 10, 11 (deduplicated)
        assert_eq!(stats.total_files, 1);
        assert_eq!(stats.total_functions, 1);
        assert_eq!(stats.total_ffi_calls, 1);

        // Check counts
        assert_eq!(cov.function_call_count("main"), 2);
        assert_eq!(cov.ffi_call_count("__builtin_array_push"), 1);

        // Check line execution
        assert!(cov.is_line_executed(Path::new("test.spl"), 10));
        assert!(cov.is_line_executed(Path::new("test.spl"), 11));
        assert!(!cov.is_line_executed(Path::new("test.spl"), 12));
    }

    #[test]
    fn test_coverage_merge() {
        let mut cov1 = CoverageCollector::new();
        cov1.record_line(Path::new("a.spl"), 1);
        cov1.record_function_call("foo");

        let mut cov2 = CoverageCollector::new();
        cov2.record_line(Path::new("a.spl"), 2);
        cov2.record_function_call("foo");
        cov2.record_function_call("bar");

        cov1.merge(&cov2);

        assert_eq!(cov1.stats().total_lines, 2); // Lines 1, 2
        assert_eq!(cov1.stats().total_functions, 2); // foo, bar
        assert_eq!(cov1.function_call_count("foo"), 2);
        assert_eq!(cov1.function_call_count("bar"), 1);
    }

    #[test]
    fn test_coverage_validation() {
        let mut cov = CoverageCollector::new();

        // Empty coverage
        assert!(!cov.has_data());

        // Add some data
        cov.record_function_call("test_fn");
        assert!(cov.has_data());

        // Check function was called
        assert!(cov.was_function_called("test_fn"));
        assert!(!cov.was_function_called("other_fn"));

        // Validate minimum coverage
        assert!(cov.validate_minimum_coverage(0, 1).is_ok());
        assert!(cov.validate_minimum_coverage(1, 1).is_err()); // Need at least 1 line
        assert!(cov.validate_minimum_coverage(0, 2).is_err()); // Need at least 2 functions
    }

    #[test]
    fn test_coverage_summary_report() {
        let mut cov = CoverageCollector::new();
        cov.record_function_call("main");
        cov.record_function_call("helper");
        cov.record_function_call("main"); // Called twice
        cov.record_ffi_call("__builtin_print");

        let report = cov.summary_report();

        assert!(report.contains("=== Coverage Summary ==="));
        assert!(report.contains("Functions called: 2"));
        assert!(report.contains("FFI calls: 1"));
        assert!(report.contains("main : 2 calls"));
        assert!(report.contains("helper : 1 calls"));
        assert!(report.contains("__builtin_print : 1 calls"));
    }
}
