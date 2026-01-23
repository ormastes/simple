//! Resource usage monitoring for parallel test execution.
//!
//! Provides CPU and memory monitoring to enable dynamic thread adjustment
//! based on system load. Uses /proc/stat and /proc/meminfo on Linux for
//! accurate measurement, with sysinfo crate as fallback.

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Resource usage monitor that runs in a background thread.
///
/// Monitors system CPU and memory usage and provides real-time readings for
/// the parallel test executor to adjust thread counts dynamically.
pub struct ResourceMonitor {
    /// Current CPU usage percentage (0-100), stored as integer
    cpu_usage: Arc<AtomicU32>,
    /// Current memory usage percentage (0-100), stored as integer
    memory_usage: Arc<AtomicU32>,
    /// Flag to signal the monitoring thread to stop
    running: Arc<AtomicBool>,
    /// Handle to the background monitoring thread
    thread_handle: Option<JoinHandle<()>>,
    /// Interval between resource measurements
    check_interval: Duration,
}

impl ResourceMonitor {
    /// Create a new resource monitor with the specified check interval.
    ///
    /// # Arguments
    /// * `check_interval_secs` - Seconds between resource usage measurements
    pub fn new(check_interval_secs: u64) -> Self {
        Self {
            cpu_usage: Arc::new(AtomicU32::new(0)),
            memory_usage: Arc::new(AtomicU32::new(0)),
            running: Arc::new(AtomicBool::new(false)),
            thread_handle: None,
            check_interval: Duration::from_secs(check_interval_secs),
        }
    }

    /// Start the background monitoring thread.
    ///
    /// The thread will continuously measure CPU and memory usage at the configured
    /// interval until `stop()` is called.
    pub fn start(&mut self) {
        if self.running.load(Ordering::SeqCst) {
            return; // Already running
        }

        self.running.store(true, Ordering::SeqCst);
        let cpu_usage = Arc::clone(&self.cpu_usage);
        let memory_usage = Arc::clone(&self.memory_usage);
        let running = Arc::clone(&self.running);
        let interval = self.check_interval;

        self.thread_handle = Some(thread::spawn(move || {
            monitor_loop(cpu_usage, memory_usage, running, interval);
        }));
    }

    /// Stop the background monitoring thread.
    pub fn stop(&mut self) {
        self.running.store(false, Ordering::SeqCst);
        if let Some(handle) = self.thread_handle.take() {
            let _ = handle.join();
        }
    }

    /// Get the current CPU usage as a percentage (0.0 - 100.0).
    pub fn get_cpu_usage(&self) -> f32 {
        self.cpu_usage.load(Ordering::SeqCst) as f32
    }

    /// Get the current memory usage as a percentage (0.0 - 100.0).
    pub fn get_memory_usage(&self) -> f32 {
        self.memory_usage.load(Ordering::SeqCst) as f32
    }

    /// Check if CPU usage is above the given threshold percentage.
    ///
    /// # Arguments
    /// * `threshold` - CPU usage percentage threshold (0-100)
    pub fn is_cpu_above_threshold(&self, threshold: u8) -> bool {
        self.get_cpu_usage() >= threshold as f32
    }

    /// Check if memory usage is above the given threshold percentage.
    ///
    /// # Arguments
    /// * `threshold` - Memory usage percentage threshold (0-100)
    pub fn is_memory_above_threshold(&self, threshold: u8) -> bool {
        self.get_memory_usage() >= threshold as f32
    }

    /// Take a single CPU usage measurement.
    ///
    /// This is useful for one-time measurements without starting the background thread.
    pub fn measure_cpu_once() -> f32 {
        measure_cpu_usage()
    }

    /// Take a single memory usage measurement.
    ///
    /// This is useful for one-time measurements without starting the background thread.
    pub fn measure_memory_once() -> f32 {
        measure_memory_usage()
    }
}

impl Drop for ResourceMonitor {
    fn drop(&mut self) {
        self.stop();
    }
}

/// Background monitoring loop
fn monitor_loop(
    cpu_usage: Arc<AtomicU32>,
    memory_usage: Arc<AtomicU32>,
    running: Arc<AtomicBool>,
    interval: Duration,
) {
    while running.load(Ordering::SeqCst) {
        let cpu = measure_cpu_usage();
        let memory = measure_memory_usage();
        cpu_usage.store(cpu as u32, Ordering::SeqCst);
        memory_usage.store(memory as u32, Ordering::SeqCst);
        thread::sleep(interval);
    }
}

/// Measure current CPU usage.
///
/// On Linux, reads from /proc/stat for accurate measurement.
/// Falls back to sysinfo crate on other platforms.
fn measure_cpu_usage() -> f32 {
    #[cfg(target_os = "linux")]
    {
        if let Some(usage) = measure_cpu_from_proc_stat() {
            return usage;
        }
    }

    // Fallback to sysinfo crate
    measure_cpu_from_sysinfo()
}

/// Measure current memory usage.
///
/// On Linux, reads from /proc/meminfo for accurate measurement.
/// Falls back to sysinfo crate on other platforms.
fn measure_memory_usage() -> f32 {
    #[cfg(target_os = "linux")]
    {
        if let Some(usage) = measure_memory_from_proc_meminfo() {
            return usage;
        }
    }

    // Fallback to sysinfo crate
    measure_memory_from_sysinfo()
}

/// Measure CPU usage by reading /proc/stat (Linux-specific).
///
/// Uses the same algorithm as scripts/cpu-aware-test.sh:
/// 1. Read CPU stats
/// 2. Wait briefly (500ms)
/// 3. Read again
/// 4. Calculate usage from the difference
#[cfg(target_os = "linux")]
fn measure_cpu_from_proc_stat() -> Option<f32> {
    // First sample
    let (total1, idle1) = read_proc_stat()?;

    // Wait for measurement interval
    thread::sleep(Duration::from_millis(500));

    // Second sample
    let (total2, idle2) = read_proc_stat()?;

    // Calculate usage
    let total_diff = total2.saturating_sub(total1);
    let idle_diff = idle2.saturating_sub(idle1);

    if total_diff == 0 {
        return Some(0.0);
    }

    let usage = ((total_diff - idle_diff) as f32 / total_diff as f32) * 100.0;
    Some(usage)
}

/// Read CPU stats from /proc/stat.
///
/// Returns (total_time, idle_time) tuple.
#[cfg(target_os = "linux")]
fn read_proc_stat() -> Option<(u64, u64)> {
    use std::fs::File;
    use std::io::{BufRead, BufReader};

    let file = File::open("/proc/stat").ok()?;
    let reader = BufReader::new(file);

    for line in reader.lines() {
        let line = line.ok()?;
        if line.starts_with("cpu ") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 8 {
                return None;
            }

            // cpu user nice system idle iowait irq softirq
            let user: u64 = parts[1].parse().ok()?;
            let nice: u64 = parts[2].parse().ok()?;
            let system: u64 = parts[3].parse().ok()?;
            let idle: u64 = parts[4].parse().ok()?;
            let iowait: u64 = parts.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);
            let irq: u64 = parts.get(6).and_then(|s| s.parse().ok()).unwrap_or(0);
            let softirq: u64 = parts.get(7).and_then(|s| s.parse().ok()).unwrap_or(0);

            let total = user + nice + system + idle + iowait + irq + softirq;
            return Some((total, idle));
        }
    }

    None
}

/// Measure memory usage by reading /proc/meminfo (Linux-specific).
///
/// Calculates memory usage as: (MemTotal - MemAvailable) / MemTotal * 100
#[cfg(target_os = "linux")]
fn measure_memory_from_proc_meminfo() -> Option<f32> {
    use std::fs::File;
    use std::io::{BufRead, BufReader};

    let file = File::open("/proc/meminfo").ok()?;
    let reader = BufReader::new(file);

    let mut mem_total: Option<u64> = None;
    let mut mem_available: Option<u64> = None;

    for line in reader.lines() {
        let line = line.ok()?;

        if line.starts_with("MemTotal:") {
            // MemTotal:       16384000 kB
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 2 {
                mem_total = parts[1].parse().ok();
            }
        } else if line.starts_with("MemAvailable:") {
            // MemAvailable:   8192000 kB
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 2 {
                mem_available = parts[1].parse().ok();
            }
        }

        // Stop once we have both values
        if mem_total.is_some() && mem_available.is_some() {
            break;
        }
    }

    match (mem_total, mem_available) {
        (Some(total), Some(available)) if total > 0 => {
            let used = total.saturating_sub(available);
            Some((used as f32 / total as f32) * 100.0)
        }
        _ => None,
    }
}

/// Measure CPU usage using the sysinfo crate (cross-platform fallback).
fn measure_cpu_from_sysinfo() -> f32 {
    use sysinfo::System;

    let mut sys = System::new();

    // First refresh to initialize
    sys.refresh_cpu_usage();
    thread::sleep(Duration::from_millis(500));

    // Second refresh to get accurate reading
    sys.refresh_cpu_usage();

    // Calculate average across all CPUs
    let cpus = sys.cpus();
    if cpus.is_empty() {
        return 0.0;
    }

    let total_usage: f32 = cpus.iter().map(|cpu| cpu.cpu_usage()).sum();
    total_usage / cpus.len() as f32
}

/// Measure memory usage using the sysinfo crate (cross-platform fallback).
fn measure_memory_from_sysinfo() -> f32 {
    use sysinfo::System;

    let mut sys = System::new();
    sys.refresh_memory();

    let total = sys.total_memory();
    let used = sys.used_memory();

    if total == 0 {
        return 0.0;
    }

    (used as f32 / total as f32) * 100.0
}

/// Get the number of available CPU cores.
pub fn available_cores() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resource_monitor_creation() {
        let monitor = ResourceMonitor::new(5);
        assert_eq!(monitor.get_cpu_usage(), 0.0);
        assert_eq!(monitor.get_memory_usage(), 0.0);
    }

    #[test]
    fn test_available_cores() {
        let cores = available_cores();
        assert!(cores >= 1, "Should have at least 1 core");
    }

    #[test]
    fn test_measure_cpu_once() {
        let usage = ResourceMonitor::measure_cpu_once();
        assert!(usage >= 0.0 && usage <= 100.0, "CPU usage should be 0-100%");
    }

    #[test]
    fn test_measure_memory_once() {
        let usage = ResourceMonitor::measure_memory_once();
        assert!(
            usage >= 0.0 && usage <= 100.0,
            "Memory usage should be 0-100%"
        );
    }

    #[test]
    fn test_is_cpu_above_threshold() {
        let monitor = ResourceMonitor::new(5);
        // Initially 0, so should not be above any positive threshold
        assert!(!monitor.is_cpu_above_threshold(50));
        assert!(monitor.is_cpu_above_threshold(0)); // 0% threshold always triggered
    }

    #[test]
    fn test_is_memory_above_threshold() {
        let monitor = ResourceMonitor::new(5);
        // Initially 0, so should not be above any positive threshold
        assert!(!monitor.is_memory_above_threshold(50));
        assert!(monitor.is_memory_above_threshold(0)); // 0% threshold always triggered
    }
}
