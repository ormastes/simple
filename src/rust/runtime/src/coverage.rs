//! Runtime coverage counters for Condition/Decision and Path coverage.
//!
//! This module provides thread-safe storage for coverage probes inserted
//! by the MIR instrumentation pass. It supports:
//! - Decision coverage (tracking true/false outcomes of boolean decisions)
//! - Condition coverage (tracking individual conditions within decisions)
//! - Path coverage (tracking execution paths through functions)
//!
//! The data is collected at runtime and can be exported as SDN format.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Global coverage data storage
static COVERAGE_DATA: OnceLock<Mutex<CoverageData>> = OnceLock::new();

/// Coverage data collected at runtime
#[derive(Debug, Default)]
pub struct CoverageData {
    /// Decision coverage: (decision_id, file, line, column) -> (true_count, false_count)
    pub decisions: HashMap<(u32, String, u32, u32), (u64, u64)>,
    /// Condition coverage: (decision_id, condition_id, file, line, column) -> (true_count, false_count)
    pub conditions: HashMap<(u32, u32, String, u32, u32), (u64, u64)>,
    /// Path coverage: (path_id, block_sequence) -> hit_count
    pub paths: HashMap<(u32, Vec<u32>), u64>,
    /// Current path being traced: path_id -> block sequence
    path_traces: HashMap<u32, Vec<u32>>,
}

impl CoverageData {
    /// Create a new empty coverage data store
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a decision probe (true or false outcome)
    pub fn record_decision(&mut self, decision_id: u32, result: bool, file: &str, line: u32, column: u32) {
        let key = (decision_id, file.to_string(), line, column);
        let entry = self.decisions.entry(key).or_insert((0, 0));
        if result {
            entry.0 += 1;
        } else {
            entry.1 += 1;
        }
    }

    /// Record a condition probe (true or false outcome)
    pub fn record_condition(
        &mut self,
        decision_id: u32,
        condition_id: u32,
        result: bool,
        file: &str,
        line: u32,
        column: u32,
    ) {
        let key = (decision_id, condition_id, file.to_string(), line, column);
        let entry = self.conditions.entry(key).or_insert((0, 0));
        if result {
            entry.0 += 1;
        } else {
            entry.1 += 1;
        }
    }

    /// Record a path probe (block entry)
    pub fn record_path_entry(&mut self, path_id: u32, block_id: u32) {
        // Add block to the current path trace
        let trace = self.path_traces.entry(path_id).or_default();
        trace.push(block_id);
    }

    /// Finalize a path trace and record it
    pub fn finalize_path(&mut self, path_id: u32) {
        if let Some(trace) = self.path_traces.remove(&path_id) {
            let key = (path_id, trace);
            *self.paths.entry(key).or_insert(0) += 1;
        }
    }

    /// Clear all coverage data
    pub fn clear(&mut self) {
        self.decisions.clear();
        self.conditions.clear();
        self.paths.clear();
        self.path_traces.clear();
    }

    /// Generate SDN format coverage report
    pub fn to_sdn(&self) -> String {
        let mut output = String::new();
        output.push_str("# Coverage Report\n");
        output.push_str("version: 1.0\n\n");

        // Decision coverage
        if !self.decisions.is_empty() {
            output.push_str("decisions |id, file, line, column, true_count, false_count|\n");
            for ((id, file, line, column), (true_count, false_count)) in &self.decisions {
                output.push_str(&format!(
                    "    {}, {}, {}, {}, {}, {}\n",
                    id, file, line, column, true_count, false_count
                ));
            }
            output.push('\n');
        }

        // Condition coverage
        if !self.conditions.is_empty() {
            output.push_str("conditions |decision_id, condition_id, file, line, column, true_count, false_count|\n");
            for ((decision_id, condition_id, file, line, column), (true_count, false_count)) in &self.conditions {
                output.push_str(&format!(
                    "    {}, {}, {}, {}, {}, {}, {}\n",
                    decision_id, condition_id, file, line, column, true_count, false_count
                ));
            }
            output.push('\n');
        }

        // Path coverage
        if !self.paths.is_empty() {
            output.push_str("paths |path_id, blocks, hit_count|\n");
            for ((path_id, blocks), hit_count) in &self.paths {
                let blocks_str: Vec<String> = blocks.iter().map(|b| b.to_string()).collect();
                output.push_str(&format!("    {}, [{}], {}\n", path_id, blocks_str.join(" "), hit_count));
            }
            output.push('\n');
        }

        // Summary
        let total_decisions = self.decisions.len();
        let covered_decisions = self.decisions.values().filter(|(t, f)| *t > 0 && *f > 0).count();
        let total_conditions = self.conditions.len();
        let covered_conditions = self.conditions.values().filter(|(t, f)| *t > 0 && *f > 0).count();
        let total_paths = self.paths.len();
        let covered_paths = self.paths.values().filter(|&count| *count > 0).count();

        output.push_str("summary:\n");
        output.push_str(&format!("    total_decisions: {}\n", total_decisions));
        output.push_str(&format!("    covered_decisions: {}\n", covered_decisions));
        output.push_str(&format!("    total_conditions: {}\n", total_conditions));
        output.push_str(&format!("    covered_conditions: {}\n", covered_conditions));
        output.push_str(&format!("    total_paths: {}\n", total_paths));
        output.push_str(&format!("    covered_paths: {}\n", covered_paths));

        if total_decisions > 0 {
            output.push_str(&format!(
                "    decision_percent: {:.1}\n",
                (covered_decisions as f64 / total_decisions as f64) * 100.0
            ));
        } else {
            output.push_str("    decision_percent: 100.0\n");
        }

        if total_conditions > 0 {
            output.push_str(&format!(
                "    condition_percent: {:.1}\n",
                (covered_conditions as f64 / total_conditions as f64) * 100.0
            ));
        } else {
            output.push_str("    condition_percent: 100.0\n");
        }

        if total_paths > 0 {
            output.push_str(&format!(
                "    path_percent: {:.1}\n",
                (covered_paths as f64 / total_paths as f64) * 100.0
            ));
        } else {
            output.push_str("    path_percent: 100.0\n");
        }

        output
    }
}

/// Get or initialize the global coverage data
fn get_coverage_data() -> &'static Mutex<CoverageData> {
    COVERAGE_DATA.get_or_init(|| Mutex::new(CoverageData::new()))
}

//==============================================================================
// FFI Functions
//==============================================================================

/// Record a decision probe
///
/// # Safety
/// The file pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_coverage_decision_probe(
    decision_id: u32,
    result: bool,
    file: *const i8,
    line: u32,
    column: u32,
) {
    let file_str = if file.is_null() {
        ""
    } else {
        std::ffi::CStr::from_ptr(file).to_str().unwrap_or("")
    };

    if let Ok(mut data) = get_coverage_data().lock() {
        data.record_decision(decision_id, result, file_str, line, column);
    }
}

/// Record a condition probe
///
/// # Safety
/// The file pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_coverage_condition_probe(
    decision_id: u32,
    condition_id: u32,
    result: bool,
    file: *const i8,
    line: u32,
    column: u32,
) {
    let file_str = if file.is_null() {
        ""
    } else {
        std::ffi::CStr::from_ptr(file).to_str().unwrap_or("")
    };

    if let Ok(mut data) = get_coverage_data().lock() {
        data.record_condition(decision_id, condition_id, result, file_str, line, column);
    }
}

/// Record a path probe (block entry)
#[no_mangle]
pub extern "C" fn rt_coverage_path_probe(path_id: u32, block_id: u32) {
    if let Ok(mut data) = get_coverage_data().lock() {
        data.record_path_entry(path_id, block_id);
    }
}

/// Finalize a path trace
#[no_mangle]
pub extern "C" fn rt_coverage_path_finalize(path_id: u32) {
    if let Ok(mut data) = get_coverage_data().lock() {
        data.finalize_path(path_id);
    }
}

/// Get the coverage data as an SDN string
///
/// # Safety
/// The returned pointer must be freed by the caller using `rt_coverage_free_sdn`.
#[no_mangle]
pub extern "C" fn rt_coverage_dump_sdn() -> *mut i8 {
    let sdn = if let Ok(data) = get_coverage_data().lock() {
        data.to_sdn()
    } else {
        String::new()
    };

    // Convert to C string and leak it (caller must free)
    match std::ffi::CString::new(sdn) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free an SDN string returned by `rt_coverage_dump_sdn`
///
/// # Safety
/// The pointer must have been returned by `rt_coverage_dump_sdn`.
#[no_mangle]
pub unsafe extern "C" fn rt_coverage_free_sdn(ptr: *mut i8) {
    if !ptr.is_null() {
        drop(std::ffi::CString::from_raw(ptr));
    }
}

/// Clear all coverage data
#[no_mangle]
pub extern "C" fn rt_coverage_clear() {
    if let Ok(mut data) = get_coverage_data().lock() {
        data.clear();
    }
}

/// Check if coverage is enabled (always true when linked with this module)
#[no_mangle]
pub extern "C" fn rt_coverage_enabled() -> bool {
    true
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decision_coverage() {
        let mut data = CoverageData::new();

        // Record some decisions
        data.record_decision(1, true, "test.spl", 10, 5);
        data.record_decision(1, true, "test.spl", 10, 5);
        data.record_decision(1, false, "test.spl", 10, 5);

        let key = (1, "test.spl".to_string(), 10, 5);
        assert_eq!(data.decisions.get(&key), Some(&(2, 1)));
    }

    #[test]
    fn test_condition_coverage() {
        let mut data = CoverageData::new();

        // Record some conditions
        data.record_condition(1, 1, true, "test.spl", 10, 5);
        data.record_condition(1, 1, false, "test.spl", 10, 5);
        data.record_condition(1, 2, true, "test.spl", 10, 10);

        let key1 = (1, 1, "test.spl".to_string(), 10, 5);
        let key2 = (1, 2, "test.spl".to_string(), 10, 10);
        assert_eq!(data.conditions.get(&key1), Some(&(1, 1)));
        assert_eq!(data.conditions.get(&key2), Some(&(1, 0)));
    }

    #[test]
    fn test_path_coverage() {
        let mut data = CoverageData::new();

        // Trace a path
        data.record_path_entry(1, 0);
        data.record_path_entry(1, 1);
        data.record_path_entry(1, 2);
        data.finalize_path(1);

        let key = (1, vec![0, 1, 2]);
        assert_eq!(data.paths.get(&key), Some(&1));

        // Trace same path again
        data.record_path_entry(1, 0);
        data.record_path_entry(1, 1);
        data.record_path_entry(1, 2);
        data.finalize_path(1);

        assert_eq!(data.paths.get(&key), Some(&2));
    }

    #[test]
    fn test_sdn_output() {
        let mut data = CoverageData::new();

        data.record_decision(1, true, "test.spl", 10, 5);
        data.record_decision(1, false, "test.spl", 10, 5);

        let sdn = data.to_sdn();
        assert!(sdn.contains("version: 1.0"));
        assert!(sdn.contains("decisions"));
        assert!(sdn.contains("test.spl"));
    }

    #[test]
    fn test_clear() {
        let mut data = CoverageData::new();

        data.record_decision(1, true, "test.spl", 10, 5);
        data.record_condition(1, 1, true, "test.spl", 10, 5);
        data.record_path_entry(1, 0);

        data.clear();

        assert!(data.decisions.is_empty());
        assert!(data.conditions.is_empty());
        assert!(data.paths.is_empty());
        assert!(data.path_traces.is_empty());
    }

    #[test]
    fn test_coverage_percentage() {
        let mut data = CoverageData::new();

        // One covered decision (both true and false)
        data.record_decision(1, true, "test.spl", 10, 5);
        data.record_decision(1, false, "test.spl", 10, 5);

        // One uncovered decision (only true)
        data.record_decision(2, true, "test.spl", 20, 5);

        let sdn = data.to_sdn();
        assert!(sdn.contains("total_decisions: 2"));
        assert!(sdn.contains("covered_decisions: 1"));
        assert!(sdn.contains("decision_percent: 50.0"));
    }
}
