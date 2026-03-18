//! Runtime performance measurement infrastructure.
//!
//! Mirrors the coverage architecture:
//! - AtomicBool gate: perf disabled by default, zero overhead when off
//! - String interning: file paths stored once, keyed by integer ID
//! - Thread-local buffers: probes batched locally, flushed periodically
//!
//! Provides:
//! - Fast clock primitives (monotonic ns, rdtsc on x86)
//! - Region-based perf probes with enter/exit timestamps

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

/// Global perf enable flag — false by default.
/// Must be explicitly enabled via `rt_perf_enable()`.
static PERF_ENABLED: AtomicBool = AtomicBool::new(false);

/// Global file path interning table (separate from coverage)
static PERF_FILE_INTERN: OnceLock<Mutex<PerfFileInternTable>> = OnceLock::new();

/// Global perf data storage
static PERF_DATA: OnceLock<Mutex<PerfData>> = OnceLock::new();

/// Monotonic clock baseline (captured once at init)
static CLOCK_BASE: OnceLock<Instant> = OnceLock::new();

/// Flush threshold for thread-local buffers
const FLUSH_THRESHOLD: usize = 1024;

//==============================================================================
// File Interning (separate from coverage to avoid coupling)
//==============================================================================

struct PerfFileInternTable {
    names: Vec<String>,
    lookup: HashMap<String, u32>,
}

impl PerfFileInternTable {
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

fn get_perf_file_intern() -> &'static Mutex<PerfFileInternTable> {
    PERF_FILE_INTERN.get_or_init(|| Mutex::new(PerfFileInternTable::new()))
}

/// Intern a file path, using thread-local cache to avoid mutex on hot path.
fn intern_perf_file(name: &str) -> u32 {
    LOCAL_PERF_FILE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if let Some(&id) = cache.get(name) {
            return id;
        }
        let id = get_perf_file_intern().lock().unwrap().intern(name);
        cache.insert(name.to_string(), id);
        id
    })
}

//==============================================================================
// Thread-local Probe Buffers
//==============================================================================

struct PerfProbeEntry {
    region_id: u32,
    file_id: u32,
    line: u32,
    delta_ns: u64,
}

thread_local! {
    static LOCAL_PERF_PROBES: RefCell<Vec<PerfProbeEntry>> = RefCell::new(Vec::with_capacity(FLUSH_THRESHOLD));
    static LOCAL_PERF_FILE_CACHE: RefCell<HashMap<String, u32>> = RefCell::new(HashMap::new());
    /// Stack of (region_id, entry_instant) for nested region tracking
    static LOCAL_REGION_STACK: RefCell<Vec<(u32, Instant)>> = RefCell::new(Vec::with_capacity(32));
}

/// Flush perf probes from thread-local to global storage.
fn flush_perf_probes_to_global(probes: &mut Vec<PerfProbeEntry>) {
    if probes.is_empty() {
        return;
    }
    if let Ok(mut data) = get_perf_data().lock() {
        for probe in probes.drain(..) {
            let key = (probe.region_id, probe.file_id, probe.line);
            let stats = data.regions.entry(key).or_insert(PerfStats {
                count: 0,
                total_ns: 0,
                min_ns: u64::MAX,
                max_ns: 0,
            });
            stats.count += 1;
            stats.total_ns += probe.delta_ns;
            if probe.delta_ns < stats.min_ns {
                stats.min_ns = probe.delta_ns;
            }
            if probe.delta_ns > stats.max_ns {
                stats.max_ns = probe.delta_ns;
            }
        }
    }
}

/// Flush all thread-local buffers to global storage.
fn flush_all_perf_local() {
    LOCAL_PERF_PROBES.with(|buf| {
        flush_perf_probes_to_global(&mut buf.borrow_mut());
    });
}

//==============================================================================
// Perf Data (Global)
//==============================================================================

/// Per-region performance statistics
#[derive(Debug, Clone)]
pub struct PerfStats {
    pub count: u64,
    pub total_ns: u64,
    pub min_ns: u64,
    pub max_ns: u64,
}

/// Global perf data collected at runtime
#[derive(Debug, Default)]
pub struct PerfData {
    /// Region stats: (region_id, file_id, line) -> PerfStats
    pub regions: HashMap<(u32, u32, u32), PerfStats>,
}

impl PerfData {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.regions.clear();
    }

    /// Generate SDN format perf report (resolves file IDs back to names)
    pub fn to_sdn(&self, intern: &PerfFileInternTable) -> String {
        let mut output = String::new();
        output.push_str("# Perf Report\n");
        output.push_str("version: 1.0\n\n");

        if !self.regions.is_empty() {
            output.push_str("regions |region_id, file, line, count, total_ns, min_ns, max_ns, avg_ns|\n");

            // Sort by total_ns descending (hotspots first)
            let mut entries: Vec<_> = self.regions.iter().collect();
            entries.sort_by(|a, b| b.1.total_ns.cmp(&a.1.total_ns));

            for ((region_id, file_id, line), stats) in &entries {
                let file = intern.get_name(*file_id);
                let avg_ns = if stats.count > 0 {
                    stats.total_ns / stats.count
                } else {
                    0
                };
                output.push_str(&format!(
                    "    {}, {}, {}, {}, {}, {}, {}, {}\n",
                    region_id, file, line, stats.count, stats.total_ns, stats.min_ns, stats.max_ns, avg_ns
                ));
            }
            output.push('\n');
        }

        // Summary
        let total_regions = self.regions.len();
        let total_time: u64 = self.regions.values().map(|s| s.total_ns).sum();
        let total_calls: u64 = self.regions.values().map(|s| s.count).sum();

        output.push_str("summary:\n");
        output.push_str(&format!("    total_regions: {}\n", total_regions));
        output.push_str(&format!("    total_calls: {}\n", total_calls));
        output.push_str(&format!("    total_time_ns: {}\n", total_time));

        if total_calls > 0 {
            output.push_str(&format!(
                "    avg_ns_per_call: {}\n",
                total_time / total_calls
            ));
        }

        output
    }
}

/// Get or initialize the global perf data
fn get_perf_data() -> &'static Mutex<PerfData> {
    PERF_DATA.get_or_init(|| Mutex::new(PerfData::new()))
}

/// Get the monotonic clock baseline
fn clock_base() -> &'static Instant {
    CLOCK_BASE.get_or_init(Instant::now)
}

//==============================================================================
// FFI Functions — Clock Primitives
//==============================================================================

/// Get monotonic nanoseconds since an arbitrary baseline (~20ns overhead).
#[no_mangle]
pub extern "C" fn rt_perf_clock_ns() -> i64 {
    clock_base().elapsed().as_nanos() as i64
}

/// Get CPU cycle counter via rdtsc on x86_64 (~5ns overhead).
/// Falls back to clock_ns on other architectures.
#[no_mangle]
pub extern "C" fn rt_perf_rdtsc() -> i64 {
    #[cfg(target_arch = "x86_64")]
    {
        unsafe { core::arch::x86_64::_rdtsc() as i64 }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        rt_perf_clock_ns()
    }
}

/// Convert rdtsc cycles to nanoseconds given CPU frequency in MHz.
#[no_mangle]
pub extern "C" fn rt_perf_cycles_to_ns(cycles: i64, freq_mhz: i64) -> i64 {
    if freq_mhz <= 0 {
        return 0;
    }
    (cycles * 1000) / freq_mhz
}

//==============================================================================
// FFI Functions — Perf Probes
//==============================================================================

/// Enable perf tracking at runtime.
#[no_mangle]
pub extern "C" fn rt_perf_enable() {
    // Initialize clock baseline on first enable
    let _ = clock_base();
    PERF_ENABLED.store(true, Ordering::Release);
}

/// Check if perf is enabled.
#[no_mangle]
pub extern "C" fn rt_perf_enabled() -> bool {
    PERF_ENABLED.load(Ordering::Relaxed)
}

/// Record entry into a performance region.
///
/// # Safety
/// The file pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_perf_region_enter(
    region_id: u32,
    file: *const std::ffi::c_char,
    line: u32,
) {
    if !PERF_ENABLED.load(Ordering::Relaxed) {
        return;
    }

    let _ = file; // file is used at exit time via the region stack
    let _ = line;

    LOCAL_REGION_STACK.with(|stack| {
        stack.borrow_mut().push((region_id, Instant::now()));
    });
}

/// Record exit from a performance region.
/// Computes delta from the matching enter call.
///
/// # Safety
/// The file pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn rt_perf_region_exit(
    region_id: u32,
    file: *const std::ffi::c_char,
    line: u32,
) {
    if !PERF_ENABLED.load(Ordering::Relaxed) {
        return;
    }

    let exit_time = Instant::now();

    let entry_time = LOCAL_REGION_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        // Pop matching region (should be the top)
        if let Some(pos) = stack.iter().rposition(|(id, _)| *id == region_id) {
            Some(stack.remove(pos).1)
        } else {
            None
        }
    });

    if let Some(enter_time) = entry_time {
        let delta_ns = exit_time.duration_since(enter_time).as_nanos() as u64;

        let file_str = if file.is_null() {
            ""
        } else {
            std::ffi::CStr::from_ptr(file).to_str().unwrap_or("")
        };
        let file_id = intern_perf_file(file_str);

        LOCAL_PERF_PROBES.with(|buf| {
            let mut buf = buf.borrow_mut();
            buf.push(PerfProbeEntry {
                region_id,
                file_id,
                line,
                delta_ns,
            });
            if buf.len() >= FLUSH_THRESHOLD {
                flush_perf_probes_to_global(&mut buf);
            }
        });
    }
}

/// Get perf data as an SDN string.
///
/// # Safety
/// The returned pointer must be freed by the caller using `rt_perf_free_sdn`.
#[no_mangle]
pub extern "C" fn rt_perf_dump_sdn() -> *mut std::ffi::c_char {
    flush_all_perf_local();

    let sdn = if let Ok(data) = get_perf_data().lock() {
        if let Ok(intern) = get_perf_file_intern().lock() {
            data.to_sdn(&intern)
        } else {
            String::new()
        }
    } else {
        String::new()
    };

    match std::ffi::CString::new(sdn) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free an SDN string returned by `rt_perf_dump_sdn`.
///
/// # Safety
/// The pointer must have been returned by `rt_perf_dump_sdn`.
#[no_mangle]
pub unsafe extern "C" fn rt_perf_free_sdn(ptr: *mut std::ffi::c_char) {
    if !ptr.is_null() {
        drop(std::ffi::CString::from_raw(ptr));
    }
}

/// Clear all perf data.
#[no_mangle]
pub extern "C" fn rt_perf_clear() {
    LOCAL_PERF_PROBES.with(|buf| buf.borrow_mut().clear());
    LOCAL_PERF_FILE_CACHE.with(|cache| cache.borrow_mut().clear());
    LOCAL_REGION_STACK.with(|stack| stack.borrow_mut().clear());

    if let Ok(mut data) = get_perf_data().lock() {
        data.clear();
    }
    if let Ok(mut intern) = get_perf_file_intern().lock() {
        intern.clear();
    }
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_test() {
        PERF_ENABLED.store(true, Ordering::Release);
        rt_perf_clear();
    }

    #[test]
    fn test_clock_ns_monotonic() {
        let t1 = rt_perf_clock_ns();
        std::thread::sleep(std::time::Duration::from_millis(1));
        let t2 = rt_perf_clock_ns();
        assert!(t2 > t1, "clock should be monotonically increasing");
    }

    #[test]
    fn test_rdtsc_monotonic() {
        let t1 = rt_perf_rdtsc();
        let t2 = rt_perf_rdtsc();
        assert!(t2 >= t1, "rdtsc should be non-decreasing");
    }

    #[test]
    fn test_cycles_to_ns() {
        // 1000 cycles at 1000MHz = 1000ns
        assert_eq!(rt_perf_cycles_to_ns(1000, 1000), 1000);
        // 3000 cycles at 3000MHz = 1000ns
        assert_eq!(rt_perf_cycles_to_ns(3000, 3000), 1000);
        // Edge case: zero freq
        assert_eq!(rt_perf_cycles_to_ns(1000, 0), 0);
    }

    #[test]
    fn test_region_enter_exit() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_perf_region_enter(1, file.as_ptr(), 10);
            std::thread::sleep(std::time::Duration::from_millis(1));
            rt_perf_region_exit(1, file.as_ptr(), 10);
        }

        flush_all_perf_local();
        let data = get_perf_data().lock().unwrap();
        let file_id = get_perf_file_intern()
            .lock()
            .unwrap()
            .lookup
            .get("test.spl")
            .copied()
            .unwrap();
        let key = (1, file_id, 10);
        let stats = data.regions.get(&key).expect("region should exist");
        assert_eq!(stats.count, 1);
        assert!(stats.total_ns > 0, "should have non-zero duration");
    }

    #[test]
    fn test_sdn_output() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_perf_region_enter(1, file.as_ptr(), 10);
            rt_perf_region_exit(1, file.as_ptr(), 10);
        }

        flush_all_perf_local();
        let data = get_perf_data().lock().unwrap();
        let intern = get_perf_file_intern().lock().unwrap();
        let sdn = data.to_sdn(&intern);
        assert!(sdn.contains("version: 1.0"));
        assert!(sdn.contains("regions"));
        assert!(sdn.contains("test.spl"));
    }

    #[test]
    fn test_perf_disabled_by_default() {
        PERF_ENABLED.store(false, Ordering::Release);
        rt_perf_clear();

        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_perf_region_enter(1, file.as_ptr(), 10);
            rt_perf_region_exit(1, file.as_ptr(), 10);
        }

        flush_all_perf_local();
        let data = get_perf_data().lock().unwrap();
        assert!(data.regions.is_empty());

        PERF_ENABLED.store(true, Ordering::Release);
    }

    #[test]
    fn test_clear() {
        setup_test();
        unsafe {
            let file = std::ffi::CString::new("test.spl").unwrap();
            rt_perf_region_enter(1, file.as_ptr(), 10);
            rt_perf_region_exit(1, file.as_ptr(), 10);
        }

        flush_all_perf_local();
        rt_perf_clear();

        let data = get_perf_data().lock().unwrap();
        assert!(data.regions.is_empty());
    }
}
