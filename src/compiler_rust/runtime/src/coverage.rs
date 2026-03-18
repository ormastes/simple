//! Runtime coverage counters for Condition/Decision and Path coverage.
//!
//! Performance optimizations (vs original):
//! - AtomicBool gate: coverage disabled by default, zero overhead when off
//! - String interning: file paths stored once, keyed by integer ID
//! - Thread-local buffers: probes batched locally, flushed periodically

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};

/// Global coverage enable flag — false by default.
/// Must be explicitly enabled via `rt_coverage_enable()`.
static COVERAGE_ENABLED: AtomicBool = AtomicBool::new(false);

/// When true, coverage probes also record timestamps for perf tracing.
static COVERAGE_TIMED: AtomicBool = AtomicBool::new(false);

/// Global file path interning table
static FILE_INTERN: OnceLock<Mutex<FileInternTable>> = OnceLock::new();

/// Global coverage data storage
static COVERAGE_DATA: OnceLock<Mutex<CoverageData>> = OnceLock::new();

/// Flush threshold for thread-local buffers
const FLUSH_THRESHOLD: usize = 1024;

//==============================================================================
// File Interning
//==============================================================================

struct FileInternTable {
    names: Vec<String>,
    lookup: HashMap<String, u32>,
}

impl FileInternTable {
    fn new() -> Self {
        Self {
            names: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.lookup.get(name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.names.push(name.to_string());
        self.lookup.insert(name.to_string(), id);
        id
    }

    fn get_name(&self, id: u32) -> &str {
        &self.names[id as usize]
    }

    fn clear(&mut self) {
        self.names.clear();
        self.lookup.clear();
    }
}

fn get_file_intern() -> &'static Mutex<FileInternTable> {
    FILE_INTERN.get_or_init(|| Mutex::new(FileInternTable::new()))
}

/// Intern a file path, using thread-local cache to avoid mutex on hot path.
fn intern_file(name: &str) -> u32 {
    LOCAL_FILE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if let Some(&id) = cache.get(name) {
            return id;
        }
        let id = get_file_intern().lock().unwrap().intern(name);
        cache.insert(name.to_string(), id);
        id
    })
}

//==============================================================================
// Thread-local Probe Buffers
//==============================================================================

struct DecisionProbe {
    decision_id: u32,
    file_id: u32,
    line: u32,
    column: u32,
    result: bool,
    /// Nanoseconds since coverage clock baseline (0 when timed mode is off)
    timestamp_ns: u64,
}

struct ConditionProbe {
    decision_id: u32,
    condition_id: u32,
    file_id: u32,
    line: u32,
    column: u32,
    result: bool,
    /// Nanoseconds since coverage clock baseline (0 when timed mode is off)
    timestamp_ns: u64,
}

/// Clock baseline for timed coverage mode
static COVERAGE_CLOCK_BASE: OnceLock<std::time::Instant> = OnceLock::new();

/// Get or initialize the coverage clock baseline
fn coverage_clock_base() -> &'static std::time::Instant {
    COVERAGE_CLOCK_BASE.get_or_init(std::time::Instant::now)
}

/// Get current timestamp in nanoseconds (0 if timed mode is off)
fn timed_timestamp_ns() -> u64 {
    if COVERAGE_TIMED.load(Ordering::Relaxed) {
        coverage_clock_base().elapsed().as_nanos() as u64
    } else {
        0
    }
}

thread_local! {
    static LOCAL_DECISIONS: RefCell<Vec<DecisionProbe>> = RefCell::new(Vec::with_capacity(FLUSH_THRESHOLD));
    static LOCAL_CONDITIONS: RefCell<Vec<ConditionProbe>> = RefCell::new(Vec::with_capacity(FLUSH_THRESHOLD));
    static LOCAL_FILE_CACHE: RefCell<HashMap<String, u32>> = RefCell::new(HashMap::new());
}

/// Flush decision probes from a mutable Vec to global storage.
fn flush_decisions_to_global(probes: &mut Vec<DecisionProbe>) {
    if probes.is_empty() {
        return;
    }
    let timed = COVERAGE_TIMED.load(Ordering::Relaxed);
    if let Ok(mut data) = get_coverage_data().lock() {
        for probe in probes.drain(..) {
            let key = (probe.decision_id, probe.file_id, probe.line, probe.column);
            let entry = data.decisions.entry(key).or_insert((0, 0));
            if probe.result {
                entry.0 += 1;
            } else {
                entry.1 += 1;
            }
            if timed && probe.timestamp_ns > 0 {
                data.timed_traces.push(TimedTraceEntry {
                    file_id: probe.file_id,
                    line: probe.line,
                    decision_id: probe.decision_id,
                    timestamp_ns: probe.timestamp_ns,
                });
            }
        }
    }
}

/// Flush condition probes from a mutable Vec to global storage.
fn flush_conditions_to_global(probes: &mut Vec<ConditionProbe>) {
    if probes.is_empty() {
        return;
    }
    let timed = COVERAGE_TIMED.load(Ordering::Relaxed);
    if let Ok(mut data) = get_coverage_data().lock() {
        for probe in probes.drain(..) {
            let key = (
                probe.decision_id,
                probe.condition_id,
                probe.file_id,
                probe.line,
                probe.column,
            );
            let entry = data.conditions.entry(key).or_insert((0, 0));
            if probe.result {
                entry.0 += 1;
            } else {
                entry.1 += 1;
            }
            if timed && probe.timestamp_ns > 0 {
                data.timed_traces.push(TimedTraceEntry {
                    file_id: probe.file_id,
                    line: probe.line,
                    decision_id: probe.decision_id,
                    timestamp_ns: probe.timestamp_ns,
                });
            }
        }
    }
}

/// Flush all thread-local buffers to global storage.
fn flush_all_local() {
    LOCAL_DECISIONS.with(|buf| {
        flush_decisions_to_global(&mut buf.borrow_mut());
    });
    LOCAL_CONDITIONS.with(|buf| {
        flush_conditions_to_global(&mut buf.borrow_mut());
    });
}

//==============================================================================
// Coverage Data (Global)
//==============================================================================

/// Timed trace entry for perf_trace section
#[derive(Debug, Clone)]
pub struct TimedTraceEntry {
    pub file_id: u32,
    pub line: u32,
    pub decision_id: u32,
    pub timestamp_ns: u64,
}

/// Coverage data collected at runtime (uses interned file IDs as keys)
#[derive(Debug, Default)]
pub struct CoverageData {
    /// Decision coverage: (decision_id, file_id, line, column) -> (true_count, false_count)
    pub decisions: HashMap<(u32, u32, u32, u32), (u64, u64)>,
    /// Condition coverage: (decision_id, condition_id, file_id, line, column) -> (true_count, false_count)
    pub conditions: HashMap<(u32, u32, u32, u32, u32), (u64, u64)>,
    /// Path coverage: (path_id, block_sequence) -> hit_count
    pub paths: HashMap<(u32, Vec<u32>), u64>,
    /// Current path being traced: path_id -> block sequence
    path_traces: HashMap<u32, Vec<u32>>,
    /// Timed trace entries (only populated when COVERAGE_TIMED is true)
    pub timed_traces: Vec<TimedTraceEntry>,
}

impl CoverageData {
    /// Create a new empty coverage data store
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a path probe (block entry)
    pub fn record_path_entry(&mut self, path_id: u32, block_id: u32) {
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
        self.timed_traces.clear();
    }

    /// Generate SDN format coverage report (resolves file IDs back to names)
    pub fn to_sdn(&self, intern: &FileInternTable) -> String {
        let mut output = String::new();
        output.push_str("# Coverage Report\n");
        output.push_str("version: 1.0\n\n");

        // Decision coverage
        if !self.decisions.is_empty() {
            output.push_str("decisions |id, file, line, column, true_count, false_count|\n");
            for ((id, file_id, line, column), (true_count, false_count)) in &self.decisions {
                let file = intern.get_name(*file_id);
                output.push_str(&format!(
                    "    {}, {}, {}, {}, {}, {}\n",
                    id, file, line, column, true_count, false_count
                ));
            }
            output.push('\n');
        }

        // Condition coverage
        if !self.conditions.is_empty() {
            output.push_str(
                "conditions |decision_id, condition_id, file, line, column, true_count, false_count|\n",
            );
            for ((decision_id, condition_id, file_id, line, column), (true_count, false_count)) in
                &self.conditions
            {
                let file = intern.get_name(*file_id);
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
                output.push_str(&format!(
                    "    {}, [{}], {}\n",
                    path_id,
                    blocks_str.join(" "),
                    hit_count
                ));
            }
            output.push('\n');
        }

        // Summary
        let total_decisions = self.decisions.len();
        let covered_decisions = self
            .decisions
            .values()
            .filter(|(t, f)| *t > 0 && *f > 0)
            .count();
        let total_conditions = self.conditions.len();
        let covered_conditions = self
            .conditions
            .values()
            .filter(|(t, f)| *t > 0 && *f > 0)
            .count();
        let total_paths = self.paths.len();
        let covered_paths = self.paths.values().filter(|&count| *count > 0).count();

        output.push_str("summary:\n");
        output.push_str(&format!("    total_decisions: {}\n", total_decisions));
        output.push_str(&format!("    covered_decisions: {}\n", covered_decisions));
        output.push_str(&format!("    total_conditions: {}\n", total_conditions));
        output.push_str(&format!(
            "    covered_conditions: {}\n",
            covered_conditions
        ));
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

        // Perf trace section (only when timed data exists)
        if !self.timed_traces.is_empty() {
            output.push('\n');
            output.push_str("perf_trace |file, line, decision_id, timestamp_ns, delta_ns|\n");
            let mut prev_ts: u64 = 0;
            for entry in &self.timed_traces {
                let file = intern.get_name(entry.file_id);
                let delta = if prev_ts > 0 {
                    entry.timestamp_ns.saturating_sub(prev_ts)
                } else {
                    0
                };
                output.push_str(&format!(
                    "    {}, {}, {}, {}, {}\n",
                    file, entry.line, entry.decision_id, entry.timestamp_ns, delta
                ));
                prev_ts = entry.timestamp_ns;
            }
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

/// Enable coverage tracking at runtime.
/// Must be called before any probes will be recorded.
#[no_mangle]
pub extern "C" fn rt_coverage_enable() {
    COVERAGE_ENABLED.store(true, Ordering::Release);
}

/// Enable coverage tracking with timestamps for perf tracing.
/// Enables both coverage AND timed mode.
#[no_mangle]
pub extern "C" fn rt_coverage_enable_timed() {
    let _ = coverage_clock_base(); // Initialize clock baseline
    COVERAGE_ENABLED.store(true, Ordering::Release);
    COVERAGE_TIMED.store(true, Ordering::Release);
}

/// Check if coverage is enabled (false by default).
#[no_mangle]
pub extern "C" fn rt_coverage_enabled() -> bool {
    COVERAGE_ENABLED.load(Ordering::Relaxed)
}

/// Record a decision probe
///
/// # Safety
/// The file pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_coverage_decision_probe(
    decision_id: u32,
    result: bool,
    file: *const std::ffi::c_char,
    line: u32,
    column: u32,
) {
    if !COVERAGE_ENABLED.load(Ordering::Relaxed) {
        return;
    }

    let file_str = if file.is_null() {
        ""
    } else {
        std::ffi::CStr::from_ptr(file).to_str().unwrap_or("")
    };

    let file_id = intern_file(file_str);

    let ts = timed_timestamp_ns();

    LOCAL_DECISIONS.with(|buf| {
        let mut buf = buf.borrow_mut();
        buf.push(DecisionProbe {
            decision_id,
            file_id,
            line,
            column,
            result,
            timestamp_ns: ts,
        });
        if buf.len() >= FLUSH_THRESHOLD {
            flush_decisions_to_global(&mut buf);
        }
    });
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
    file: *const std::ffi::c_char,
    line: u32,
    column: u32,
) {
    if !COVERAGE_ENABLED.load(Ordering::Relaxed) {
        return;
    }

    let file_str = if file.is_null() {
        ""
    } else {
        std::ffi::CStr::from_ptr(file).to_str().unwrap_or("")
    };

    let file_id = intern_file(file_str);
    let ts = timed_timestamp_ns();

    LOCAL_CONDITIONS.with(|buf| {
        let mut buf = buf.borrow_mut();
        buf.push(ConditionProbe {
            decision_id,
            condition_id,
            file_id,
            line,
            column,
            result,
            timestamp_ns: ts,
        });
        if buf.len() >= FLUSH_THRESHOLD {
            flush_conditions_to_global(&mut buf);
        }
    });
}

/// Record a path probe (block entry)
#[no_mangle]
pub extern "C" fn rt_coverage_path_probe(path_id: u32, block_id: u32) {
    if !COVERAGE_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    if let Ok(mut data) = get_coverage_data().lock() {
        data.record_path_entry(path_id, block_id);
    }
}

/// Finalize a path trace
#[no_mangle]
pub extern "C" fn rt_coverage_path_finalize(path_id: u32) {
    if !COVERAGE_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    if let Ok(mut data) = get_coverage_data().lock() {
        data.finalize_path(path_id);
    }
}

/// Get the coverage data as an SDN string
///
/// # Safety
/// The returned pointer must be freed by the caller using `rt_coverage_free_sdn`.
#[no_mangle]
pub extern "C" fn rt_coverage_dump_sdn() -> *mut std::ffi::c_char {
    // Flush thread-local buffers first
    flush_all_local();

    let sdn = if let Ok(data) = get_coverage_data().lock() {
        if let Ok(intern) = get_file_intern().lock() {
            data.to_sdn(&intern)
        } else {
            String::new()
        }
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
pub unsafe extern "C" fn rt_coverage_free_sdn(ptr: *mut std::ffi::c_char) {
    if !ptr.is_null() {
        drop(std::ffi::CString::from_raw(ptr));
    }
}

/// Clear all coverage data
#[no_mangle]
pub extern "C" fn rt_coverage_clear() {
    // Clear thread-local buffers
    LOCAL_DECISIONS.with(|buf| buf.borrow_mut().clear());
    LOCAL_CONDITIONS.with(|buf| buf.borrow_mut().clear());
    LOCAL_FILE_CACHE.with(|cache| cache.borrow_mut().clear());

    // Reset timed mode
    COVERAGE_TIMED.store(false, Ordering::Release);

    if let Ok(mut data) = get_coverage_data().lock() {
        data.clear();
    }
    if let Ok(mut intern) = get_file_intern().lock() {
        intern.clear();
    }
}

/// Check if coverage is running in timed mode
pub fn is_coverage_timed() -> bool {
    COVERAGE_TIMED.load(Ordering::Relaxed)
}

/// Check if coverage is enabled (public helper for interpreter_extern)
pub fn is_coverage_enabled() -> bool {
    COVERAGE_ENABLED.load(Ordering::Relaxed)
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_test() {
        COVERAGE_ENABLED.store(true, Ordering::Release);
        rt_coverage_clear();
    }

    #[test]
    fn test_decision_coverage() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
            rt_coverage_decision_probe(1, false, file.as_ptr(), 10, 5);
        }

        flush_all_local();
        let data = get_coverage_data().lock().unwrap();
        let file_id = get_file_intern()
            .lock()
            .unwrap()
            .lookup
            .get("test.spl")
            .copied()
            .unwrap();
        let key = (1, file_id, 10, 5);
        assert_eq!(data.decisions.get(&key), Some(&(2, 1)));
    }

    #[test]
    fn test_condition_coverage() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_coverage_condition_probe(1, 1, true, file.as_ptr(), 10, 5);
            rt_coverage_condition_probe(1, 1, false, file.as_ptr(), 10, 5);
            rt_coverage_condition_probe(1, 2, true, file.as_ptr(), 10, 10);
        }

        flush_all_local();
        let data = get_coverage_data().lock().unwrap();
        let file_id = get_file_intern()
            .lock()
            .unwrap()
            .lookup
            .get("test.spl")
            .copied()
            .unwrap();
        let key1 = (1, 1, file_id, 10, 5);
        let key2 = (1, 2, file_id, 10, 10);
        assert_eq!(data.conditions.get(&key1), Some(&(1, 1)));
        assert_eq!(data.conditions.get(&key2), Some(&(1, 0)));
    }

    #[test]
    fn test_path_coverage() {
        setup_test();

        if let Ok(mut data) = get_coverage_data().lock() {
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
    }

    #[test]
    fn test_sdn_output() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
            rt_coverage_decision_probe(1, false, file.as_ptr(), 10, 5);
        }

        flush_all_local();
        let data = get_coverage_data().lock().unwrap();
        let intern = get_file_intern().lock().unwrap();
        let sdn = data.to_sdn(&intern);
        assert!(sdn.contains("version: 1.0"));
        assert!(sdn.contains("decisions"));
        assert!(sdn.contains("test.spl"));
    }

    #[test]
    fn test_clear() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
            rt_coverage_condition_probe(1, 1, true, file.as_ptr(), 10, 5);
        }

        flush_all_local();
        rt_coverage_clear();

        let data = get_coverage_data().lock().unwrap();
        assert!(data.decisions.is_empty());
        assert!(data.conditions.is_empty());
        assert!(data.paths.is_empty());
    }

    #[test]
    fn test_coverage_disabled_by_default() {
        COVERAGE_ENABLED.store(false, Ordering::Release);
        rt_coverage_clear();

        // These should be no-ops when disabled
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
        }

        flush_all_local();
        let data = get_coverage_data().lock().unwrap();
        assert!(data.decisions.is_empty());

        // Re-enable for other tests
        COVERAGE_ENABLED.store(true, Ordering::Release);
    }

    #[test]
    fn test_coverage_percentage() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            // One covered decision (both true and false)
            rt_coverage_decision_probe(1, true, file.as_ptr(), 10, 5);
            rt_coverage_decision_probe(1, false, file.as_ptr(), 10, 5);
            // One uncovered decision (only true)
            rt_coverage_decision_probe(2, true, file.as_ptr(), 20, 5);
        }

        flush_all_local();
        let data = get_coverage_data().lock().unwrap();
        let intern = get_file_intern().lock().unwrap();
        let sdn = data.to_sdn(&intern);
        assert!(sdn.contains("total_decisions: 2"));
        assert!(sdn.contains("covered_decisions: 1"));
        assert!(sdn.contains("decision_percent: 50.0"));
    }
}
