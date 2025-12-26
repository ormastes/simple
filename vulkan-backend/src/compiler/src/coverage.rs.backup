//! Coverage tracking for Simple language tests
//!
//! This module provides runtime coverage collection during test execution.
//! Coverage data includes:
//! - Line execution tracking (file → line numbers)
//! - Function call tracking (function name → call count)
//! - FFI call tracking (FFI function → call count)
//! - Condition/Decision Coverage (MC/DC)
//! - Path Coverage
//!
//! Usage:
//! ```text
//! // Enable coverage via environment variable
//! SIMPLE_COVERAGE=1 cargo test simple_stdlib
//!
//! // Output written to SIMPLE_COVERAGE_OUTPUT or default location
//! // target/coverage/simple_coverage.json
//!
//! // SDN output format
//! simple --coverage --coverage-output=coverage.sdn main.spl
//! ```

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

// ============================================================================
// Condition/Decision Coverage Types
// ============================================================================

/// Source location for coverage data
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct SourceLoc {
    pub file: PathBuf,
    pub line: u32,
    pub column: u32,
}

impl SourceLoc {
    pub fn new(file: PathBuf, line: u32, column: u32) -> Self {
        Self { file, line, column }
    }
}

/// A single condition within a decision
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Condition {
    pub id: u32,
    pub loc: SourceLoc,
    pub true_count: u64,
    pub false_count: u64,
}

impl Condition {
    pub fn new(id: u32, loc: SourceLoc) -> Self {
        Self {
            id,
            loc,
            true_count: 0,
            false_count: 0,
        }
    }

    pub fn is_covered(&self) -> bool {
        self.true_count > 0 && self.false_count > 0
    }

    pub fn record(&mut self, result: bool) {
        if result {
            self.true_count += 1;
        } else {
            self.false_count += 1;
        }
    }
}

/// A decision (boolean expression with one or more conditions)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Decision {
    pub id: u32,
    pub loc: SourceLoc,
    pub conditions: Vec<Condition>,
    pub true_count: u64,
    pub false_count: u64,
}

impl Decision {
    pub fn new(id: u32, loc: SourceLoc) -> Self {
        Self {
            id,
            loc,
            conditions: Vec::new(),
            true_count: 0,
            false_count: 0,
        }
    }

    pub fn add_condition(&mut self, condition: Condition) {
        self.conditions.push(condition);
    }

    pub fn is_covered(&self) -> bool {
        self.true_count > 0 && self.false_count > 0
    }

    pub fn record(&mut self, result: bool) {
        if result {
            self.true_count += 1;
        } else {
            self.false_count += 1;
        }
    }

    pub fn mc_dc_covered(&self) -> bool {
        if !self.is_covered() {
            return false;
        }
        self.conditions.iter().all(|c| c.is_covered())
    }
}

/// An execution path through a function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionPath {
    pub id: u32,
    pub block_sequence: Vec<u32>,
    pub hit_count: u64,
}

impl ExecutionPath {
    pub fn new(id: u32, blocks: Vec<u32>) -> Self {
        Self {
            id,
            block_sequence: blocks,
            hit_count: 0,
        }
    }

    pub fn is_covered(&self) -> bool {
        self.hit_count > 0
    }

    pub fn record_hit(&mut self) {
        self.hit_count += 1;
    }
}

/// Coverage data for a single function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionCoverage {
    pub name: String,
    pub loc: SourceLoc,
    pub decisions: Vec<Decision>,
    pub paths: Vec<ExecutionPath>,
    pub entry_count: u64,
}

impl FunctionCoverage {
    pub fn new(name: String, loc: SourceLoc) -> Self {
        Self {
            name,
            loc,
            decisions: Vec::new(),
            paths: Vec::new(),
            entry_count: 0,
        }
    }

    pub fn add_decision(&mut self, decision: Decision) {
        self.decisions.push(decision);
    }

    pub fn add_path(&mut self, path: ExecutionPath) {
        self.paths.push(path);
    }

    pub fn decision_coverage_percent(&self) -> f64 {
        if self.decisions.is_empty() {
            return 100.0;
        }
        let covered = self.decisions.iter().filter(|d| d.is_covered()).count();
        (covered as f64) / (self.decisions.len() as f64) * 100.0
    }

    pub fn condition_coverage_percent(&self) -> f64 {
        let total: usize = self.decisions.iter().map(|d| d.conditions.len()).sum();
        if total == 0 {
            return 100.0;
        }
        let covered: usize = self
            .decisions
            .iter()
            .flat_map(|d| &d.conditions)
            .filter(|c| c.is_covered())
            .count();
        (covered as f64) / (total as f64) * 100.0
    }

    pub fn path_coverage_percent(&self) -> f64 {
        if self.paths.is_empty() {
            return 100.0;
        }
        let covered = self.paths.iter().filter(|p| p.is_covered()).count();
        (covered as f64) / (self.paths.len() as f64) * 100.0
    }

    pub fn mc_dc_percent(&self) -> f64 {
        if self.decisions.is_empty() {
            return 100.0;
        }
        let covered = self.decisions.iter().filter(|d| d.mc_dc_covered()).count();
        (covered as f64) / (self.decisions.len() as f64) * 100.0
    }
}

/// Coverage data for a module/file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleCoverage {
    pub file: PathBuf,
    pub functions: Vec<FunctionCoverage>,
}

impl ModuleCoverage {
    pub fn new(file: PathBuf) -> Self {
        Self {
            file,
            functions: Vec::new(),
        }
    }

    pub fn add_function(&mut self, func: FunctionCoverage) {
        self.functions.push(func);
    }

    pub fn total_decisions(&self) -> u32 {
        self.functions.iter().map(|f| f.decisions.len() as u32).sum()
    }

    pub fn covered_decisions(&self) -> u32 {
        self.functions
            .iter()
            .flat_map(|f| &f.decisions)
            .filter(|d| d.is_covered())
            .count() as u32
    }
}

/// Summary statistics for a coverage report
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageSummary {
    pub total_functions: u32,
    pub covered_functions: u32,
    pub total_decisions: u32,
    pub covered_decisions: u32,
    pub total_conditions: u32,
    pub covered_conditions: u32,
    pub total_paths: u32,
    pub covered_paths: u32,
    pub mc_dc_total: u32,
    pub mc_dc_covered: u32,
}

impl CoverageSummary {
    pub fn new() -> Self {
        Self {
            total_functions: 0,
            covered_functions: 0,
            total_decisions: 0,
            covered_decisions: 0,
            total_conditions: 0,
            covered_conditions: 0,
            total_paths: 0,
            covered_paths: 0,
            mc_dc_total: 0,
            mc_dc_covered: 0,
        }
    }

    pub fn decision_percent(&self) -> f64 {
        if self.total_decisions == 0 {
            return 100.0;
        }
        (self.covered_decisions as f64) / (self.total_decisions as f64) * 100.0
    }

    pub fn condition_percent(&self) -> f64 {
        if self.total_conditions == 0 {
            return 100.0;
        }
        (self.covered_conditions as f64) / (self.total_conditions as f64) * 100.0
    }

    pub fn path_percent(&self) -> f64 {
        if self.total_paths == 0 {
            return 100.0;
        }
        (self.covered_paths as f64) / (self.total_paths as f64) * 100.0
    }

    pub fn mc_dc_percent(&self) -> f64 {
        if self.mc_dc_total == 0 {
            return 100.0;
        }
        (self.mc_dc_covered as f64) / (self.mc_dc_total as f64) * 100.0
    }
}

impl Default for CoverageSummary {
    fn default() -> Self {
        Self::new()
    }
}

/// Top-level coverage report with condition/decision and path coverage
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageReport {
    pub version: String,
    pub timestamp: String,
    pub modules: Vec<ModuleCoverage>,
}

impl CoverageReport {
    pub fn new() -> Self {
        Self {
            version: "1.0".to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            modules: Vec::new(),
        }
    }

    pub fn add_module(&mut self, module: ModuleCoverage) {
        self.modules.push(module);
    }

    pub fn summary(&self) -> CoverageSummary {
        let mut s = CoverageSummary::new();
        for m in &self.modules {
            for f in &m.functions {
                s.total_functions += 1;
                if f.entry_count > 0 {
                    s.covered_functions += 1;
                }
                s.total_decisions += f.decisions.len() as u32;
                s.covered_decisions += f.decisions.iter().filter(|d| d.is_covered()).count() as u32;
                s.total_conditions += f
                    .decisions
                    .iter()
                    .map(|d| d.conditions.len() as u32)
                    .sum::<u32>();
                s.covered_conditions += f
                    .decisions
                    .iter()
                    .flat_map(|d| &d.conditions)
                    .filter(|c| c.is_covered())
                    .count() as u32;
                s.total_paths += f.paths.len() as u32;
                s.covered_paths += f.paths.iter().filter(|p| p.is_covered()).count() as u32;
                s.mc_dc_total += f.decisions.len() as u32;
                s.mc_dc_covered += f.decisions.iter().filter(|d| d.mc_dc_covered()).count() as u32;
            }
        }
        s
    }

    /// Write coverage report in SDN format
    pub fn to_sdn(&self) -> String {
        let mut out = String::new();

        writeln!(out, "# Coverage Report").unwrap();
        writeln!(out, "version: {}", self.version).unwrap();
        writeln!(out, "timestamp: {}", self.timestamp).unwrap();
        writeln!(out).unwrap();

        for module in &self.modules {
            writeln!(out, "module:").unwrap();
            writeln!(out, "    file: {}", module.file.display()).unwrap();
            writeln!(out).unwrap();

            // Functions table
            if !module.functions.is_empty() {
                writeln!(
                    out,
                    "    functions |name, entry_count, decision_pct, condition_pct, path_pct, mc_dc_pct|"
                )
                .unwrap();
                for f in &module.functions {
                    writeln!(
                        out,
                        "        {}, {}, {:.1}, {:.1}, {:.1}, {:.1}",
                        f.name,
                        f.entry_count,
                        f.decision_coverage_percent(),
                        f.condition_coverage_percent(),
                        f.path_coverage_percent(),
                        f.mc_dc_percent()
                    )
                    .unwrap();
                }
                writeln!(out).unwrap();
            }

            // Decisions table
            let has_decisions = module.functions.iter().any(|f| !f.decisions.is_empty());
            if has_decisions {
                writeln!(out, "    decisions |func, id, line, true_count, false_count|").unwrap();
                for f in &module.functions {
                    for d in &f.decisions {
                        writeln!(
                            out,
                            "        {}, {}, {}, {}, {}",
                            f.name, d.id, d.loc.line, d.true_count, d.false_count
                        )
                        .unwrap();
                    }
                }
                writeln!(out).unwrap();
            }

            // Conditions table
            let has_conditions = module
                .functions
                .iter()
                .any(|f| f.decisions.iter().any(|d| !d.conditions.is_empty()));
            if has_conditions {
                writeln!(
                    out,
                    "    conditions |func, decision_id, id, line, true_count, false_count|"
                )
                .unwrap();
                for f in &module.functions {
                    for d in &f.decisions {
                        for c in &d.conditions {
                            writeln!(
                                out,
                                "        {}, {}, {}, {}, {}, {}",
                                f.name, d.id, c.id, c.loc.line, c.true_count, c.false_count
                            )
                            .unwrap();
                        }
                    }
                }
                writeln!(out).unwrap();
            }

            // Paths table
            let has_paths = module.functions.iter().any(|f| !f.paths.is_empty());
            if has_paths {
                writeln!(out, "    paths |func, id, blocks, hit_count|").unwrap();
                for f in &module.functions {
                    for p in &f.paths {
                        let blocks: Vec<String> =
                            p.block_sequence.iter().map(|b| b.to_string()).collect();
                        writeln!(
                            out,
                            "        {}, {}, [{}], {}",
                            f.name,
                            p.id,
                            blocks.join(" "),
                            p.hit_count
                        )
                        .unwrap();
                    }
                }
                writeln!(out).unwrap();
            }
        }

        // Summary section
        let summary = self.summary();
        writeln!(out, "summary:").unwrap();
        writeln!(out, "    total_functions: {}", summary.total_functions).unwrap();
        writeln!(out, "    covered_functions: {}", summary.covered_functions).unwrap();
        writeln!(out, "    total_decisions: {}", summary.total_decisions).unwrap();
        writeln!(out, "    covered_decisions: {}", summary.covered_decisions).unwrap();
        writeln!(out, "    total_conditions: {}", summary.total_conditions).unwrap();
        writeln!(out, "    covered_conditions: {}", summary.covered_conditions).unwrap();
        writeln!(out, "    total_paths: {}", summary.total_paths).unwrap();
        writeln!(out, "    covered_paths: {}", summary.covered_paths).unwrap();
        writeln!(out, "    decision_percent: {:.1}", summary.decision_percent()).unwrap();
        writeln!(
            out,
            "    condition_percent: {:.1}",
            summary.condition_percent()
        )
        .unwrap();
        writeln!(out, "    path_percent: {:.1}", summary.path_percent()).unwrap();
        writeln!(out, "    mc_dc_percent: {:.1}", summary.mc_dc_percent()).unwrap();

        out
    }

    /// Save coverage report to SDN file
    pub fn save_to_sdn<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let sdn = self.to_sdn();

        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create directory: {}", e))?;
        }

        let mut file = fs::File::create(path.as_ref())
            .map_err(|e| format!("Failed to create file: {}", e))?;

        file.write_all(sdn.as_bytes())
            .map_err(|e| format!("Failed to write SDN: {}", e))?;

        Ok(())
    }

    /// Save coverage report to JSON file
    pub fn save_to_json<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| format!("Failed to serialize coverage: {}", e))?;

        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create directory: {}", e))?;
        }

        fs::write(path.as_ref(), json)
            .map_err(|e| format!("Failed to write coverage file: {}", e))?;

        Ok(())
    }
}

impl Default for CoverageReport {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Original Coverage Collector (extended)
// ============================================================================

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

    #[test]
    fn test_manual_coverage_collection() {
        // Manually init
        init_coverage();

        // Record some data
        if let Some(cov) = get_global_coverage() {
            let mut cov = cov.lock().unwrap();
            cov.record_function_call("test_fn");
            cov.record_function_call("main");
            cov.record_function_call("main");

            // Check data was recorded
            assert!(cov.has_data());
            assert_eq!(cov.function_call_count("main"), 2);
            assert_eq!(cov.function_call_count("test_fn"), 1);

            // Print summary
            eprintln!("{}", cov.summary_report());
        }
    }

    #[test]
    fn test_coverage_save_to_file() {
        use std::fs;

        // Clean any existing file
        let path = get_coverage_output_path();
        let _ = fs::remove_file(&path);

        // Init and record data
        init_coverage();
        if let Some(cov) = get_global_coverage() {
            let mut cov = cov.lock().unwrap();
            cov.record_function_call("test_func");
            cov.record_function_call("main");

            // Save directly
            match cov.save_to_file(&path) {
                Ok(()) => {
                    eprintln!("✅ Saved to: {}", path.display());

                    // Check file exists
                    assert!(path.exists(), "File should exist after save");

                    let content = fs::read_to_string(&path).unwrap();
                    eprintln!("Content length: {}", content.len());
                    assert!(content.contains("test_func"), "Should contain function name");
                    assert!(content.contains("main"), "Should contain main");

                    // Clean up
                    let _ = fs::remove_file(&path);
                }
                Err(e) => {
                    panic!("Save failed: {}", e);
                }
            }
        }
    }

    // =========================================================================
    // Condition/Decision Coverage Tests
    // =========================================================================

    #[test]
    fn test_condition_coverage() {
        let loc = SourceLoc::new(PathBuf::from("test.spl"), 10, 1);
        let mut cond = Condition::new(1, loc);

        // Initially not covered
        assert!(!cond.is_covered());

        // Record only true
        cond.record(true);
        assert!(!cond.is_covered());
        assert_eq!(cond.true_count, 1);
        assert_eq!(cond.false_count, 0);

        // Record false - now covered
        cond.record(false);
        assert!(cond.is_covered());
        assert_eq!(cond.true_count, 1);
        assert_eq!(cond.false_count, 1);
    }

    #[test]
    fn test_decision_coverage() {
        let loc = SourceLoc::new(PathBuf::from("test.spl"), 10, 1);
        let mut decision = Decision::new(1, loc.clone());

        // Add conditions
        let cond1 = Condition::new(1, loc.clone());
        let cond2 = Condition::new(2, loc);
        decision.add_condition(cond1);
        decision.add_condition(cond2);

        // Initially not covered
        assert!(!decision.is_covered());
        assert!(!decision.mc_dc_covered());

        // Record decision outcomes
        decision.record(true);
        decision.record(false);
        assert!(decision.is_covered());

        // But MC/DC not covered until conditions are covered
        assert!(!decision.mc_dc_covered());
    }

    #[test]
    fn test_execution_path() {
        let mut path = ExecutionPath::new(1, vec![0, 1, 2, 3]);

        assert!(!path.is_covered());
        assert_eq!(path.hit_count, 0);

        path.record_hit();
        assert!(path.is_covered());
        assert_eq!(path.hit_count, 1);

        path.record_hit();
        assert_eq!(path.hit_count, 2);
    }

    #[test]
    fn test_function_coverage_metrics() {
        let loc = SourceLoc::new(PathBuf::from("test.spl"), 1, 1);
        let mut func = FunctionCoverage::new("test_fn".to_string(), loc.clone());

        // No decisions/paths = 100% coverage
        assert_eq!(func.decision_coverage_percent(), 100.0);
        assert_eq!(func.path_coverage_percent(), 100.0);

        // Add a decision
        let mut decision = Decision::new(1, loc.clone());
        decision.record(true);
        decision.record(false);
        func.add_decision(decision);

        assert_eq!(func.decision_coverage_percent(), 100.0);

        // Add an uncovered decision
        let decision2 = Decision::new(2, loc.clone());
        func.add_decision(decision2);
        assert_eq!(func.decision_coverage_percent(), 50.0);

        // Add paths
        let mut path1 = ExecutionPath::new(1, vec![0, 1]);
        path1.record_hit();
        func.add_path(path1);

        let path2 = ExecutionPath::new(2, vec![0, 2]);
        func.add_path(path2);

        assert_eq!(func.path_coverage_percent(), 50.0);
    }

    #[test]
    fn test_coverage_report_sdn_output() {
        let mut report = CoverageReport::new();

        // Create a module with coverage data
        let mut module = ModuleCoverage::new(PathBuf::from("src/main.spl"));

        let loc = SourceLoc::new(PathBuf::from("src/main.spl"), 10, 1);
        let mut func = FunctionCoverage::new("main".to_string(), loc.clone());
        func.entry_count = 5;

        // Add a covered decision with conditions
        let mut decision = Decision::new(1, loc.clone());
        decision.true_count = 3;
        decision.false_count = 2;

        let mut cond1 = Condition::new(1, loc.clone());
        cond1.true_count = 3;
        cond1.false_count = 2;
        decision.add_condition(cond1);

        let mut cond2 = Condition::new(2, loc.clone());
        cond2.true_count = 4;
        cond2.false_count = 1;
        decision.add_condition(cond2);

        func.add_decision(decision);

        // Add paths
        let mut path1 = ExecutionPath::new(1, vec![0, 1, 2]);
        path1.hit_count = 3;
        func.add_path(path1);

        let path2 = ExecutionPath::new(2, vec![0, 1, 3]);
        func.add_path(path2);

        module.add_function(func);
        report.add_module(module);

        // Generate SDN output
        let sdn = report.to_sdn();

        // Verify SDN contains expected content
        assert!(sdn.contains("# Coverage Report"));
        assert!(sdn.contains("version: 1.0"));
        assert!(sdn.contains("file: src/main.spl"));
        assert!(sdn.contains("main"));
        assert!(sdn.contains("functions |name"));
        assert!(sdn.contains("decisions |func"));
        assert!(sdn.contains("conditions |func"));
        assert!(sdn.contains("paths |func"));
        assert!(sdn.contains("summary:"));
        assert!(sdn.contains("total_decisions: 1"));
        assert!(sdn.contains("total_conditions: 2"));
        assert!(sdn.contains("total_paths: 2"));

        eprintln!("SDN Output:\n{}", sdn);
    }

    #[test]
    fn test_coverage_summary() {
        let mut report = CoverageReport::new();

        let mut module = ModuleCoverage::new(PathBuf::from("test.spl"));
        let loc = SourceLoc::new(PathBuf::from("test.spl"), 1, 1);

        // Function 1: fully covered
        let mut func1 = FunctionCoverage::new("covered_fn".to_string(), loc.clone());
        func1.entry_count = 1;
        let mut d1 = Decision::new(1, loc.clone());
        d1.true_count = 1;
        d1.false_count = 1;
        func1.add_decision(d1);
        module.add_function(func1);

        // Function 2: not covered
        let func2 = FunctionCoverage::new("uncovered_fn".to_string(), loc.clone());
        module.add_function(func2);

        report.add_module(module);

        let summary = report.summary();
        assert_eq!(summary.total_functions, 2);
        assert_eq!(summary.covered_functions, 1);
        assert_eq!(summary.total_decisions, 1);
        assert_eq!(summary.covered_decisions, 1);
        assert_eq!(summary.decision_percent(), 100.0);
    }
}
