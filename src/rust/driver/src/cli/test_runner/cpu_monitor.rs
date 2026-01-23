//! CPU usage monitoring for parallel test execution.
//!
//! Provides CPU monitoring to enable dynamic thread adjustment based on system load.
//! Uses /proc/stat on Linux for accurate measurement, with sysinfo crate as fallback.

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// CPU usage monitor that runs in a background thread.
///
/// Monitors system CPU usage and provides real-time readings for
/// the parallel test executor to adjust thread counts dynamically.
pub struct CpuMonitor {
    /// Current CPU usage percentage (0-100), stored as integer
    usage: Arc<AtomicU32>,
    /// Flag to signal the monitoring thread to stop
    running: Arc<AtomicBool>,
    /// Handle to the background monitoring thread
    thread_handle: Option<JoinHandle<()>>,
    /// Interval between CPU measurements
    check_interval: Duration,
}

impl CpuMonitor {
    /// Create a new CPU monitor with the specified check interval.
    ///
    /// # Arguments
    /// * `check_interval_secs` - Seconds between CPU usage measurements
    pub fn new(check_interval_secs: u64) -> Self {
        Self {
            usage: Arc::new(AtomicU32::new(0)),
            running: Arc::new(AtomicBool::new(false)),
            thread_handle: None,
            check_interval: Duration::from_secs(check_interval_secs),
        }
    }

    /// Start the background monitoring thread.
    ///
    /// The thread will continuously measure CPU usage at the configured interval
    /// until `stop()` is called.
    pub fn start(&mut self) {
        if self.running.load(Ordering::SeqCst) {
            return; // Already running
        }

        self.running.store(true, Ordering::SeqCst);
        let usage = Arc::clone(&self.usage);
        let running = Arc::clone(&self.running);
        let interval = self.check_interval;

        self.thread_handle = Some(thread::spawn(move || {
            monitor_loop(usage, running, interval);
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
    pub fn get_usage(&self) -> f32 {
        self.usage.load(Ordering::SeqCst) as f32
    }

    /// Check if CPU usage is above the given threshold percentage.
    ///
    /// # Arguments
    /// * `threshold` - CPU usage percentage threshold (0-100)
    pub fn is_above_threshold(&self, threshold: u8) -> bool {
        self.get_usage() >= threshold as f32
    }

    /// Take a single CPU usage measurement.
    ///
    /// This is useful for one-time measurements without starting the background thread.
    pub fn measure_once() -> f32 {
        measure_cpu_usage()
    }
}

impl Drop for CpuMonitor {
    fn drop(&mut self) {
        self.stop();
    }
}

/// Background monitoring loop
fn monitor_loop(usage: Arc<AtomicU32>, running: Arc<AtomicBool>, interval: Duration) {
    while running.load(Ordering::SeqCst) {
        let cpu_usage = measure_cpu_usage();
        usage.store(cpu_usage as u32, Ordering::SeqCst);
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

/// Measure CPU usage by reading /proc/stat (Linux-specific).
///
/// Uses the same algorithm as scripts/cpu-aware-test.sh:
/// 1. Read CPU stats
/// 2. Wait briefly (500ms)
/// 3. Read again
/// 4. Calculate usage from the difference
#[cfg(target_os = "linux")]
fn measure_cpu_from_proc_stat() -> Option<f32> {
    use std::fs::File;
    use std::io::{BufRead, BufReader};

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

/// Get the number of available CPU cores.
pub fn available_cores() -> usize {
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_monitor_creation() {
        let monitor = CpuMonitor::new(5);
        assert_eq!(monitor.get_usage(), 0.0);
    }

    #[test]
    fn test_available_cores() {
        let cores = available_cores();
        assert!(cores >= 1, "Should have at least 1 core");
    }

    #[test]
    fn test_measure_once() {
        let usage = CpuMonitor::measure_once();
        assert!(usage >= 0.0 && usage <= 100.0, "Usage should be 0-100%");
    }

    #[test]
    fn test_is_above_threshold() {
        let monitor = CpuMonitor::new(5);
        // Initially 0, so should not be above any positive threshold
        assert!(!monitor.is_above_threshold(50));
        assert!(monitor.is_above_threshold(0)); // 0% threshold always triggered
    }
}
