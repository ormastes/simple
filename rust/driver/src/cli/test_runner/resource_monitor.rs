//! Resource usage monitoring for parallel test execution.
//!
//! Provides CPU and memory monitoring to enable dynamic thread adjustment
//! based on system load. Uses /proc/stat and /proc/meminfo on Linux for
//! accurate measurement, with sysinfo crate as fallback.

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use parking_lot::{Condvar, Mutex};

/// Resource usage monitor that runs in a background thread.
///
/// Monitors system CPU and memory usage and provides real-time readings for
/// the parallel test executor to adjust thread counts dynamically.
///
/// Uses a Condvar-based interruptible sleep so that `stop()` returns quickly
/// instead of waiting for the full check interval to elapse.
pub struct ResourceMonitor {
    /// Current CPU usage percentage (0-100), stored as integer
    cpu_usage: Arc<AtomicU32>,
    /// Current memory usage percentage (0-100), stored as integer
    memory_usage: Arc<AtomicU32>,
    /// Flag to signal the monitoring thread to stop
    running: Arc<AtomicBool>,
    /// Condvar for interruptible sleep - allows stop() to wake thread immediately
    stop_signal: Arc<(Mutex<bool>, Condvar)>,
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
            stop_signal: Arc::new((Mutex::new(false), Condvar::new())),
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

        // Reset stop signal
        *self.stop_signal.0.lock() = false;

        self.running.store(true, Ordering::SeqCst);
        let cpu_usage = Arc::clone(&self.cpu_usage);
        let memory_usage = Arc::clone(&self.memory_usage);
        let running = Arc::clone(&self.running);
        let stop_signal = Arc::clone(&self.stop_signal);
        let interval = self.check_interval;

        self.thread_handle = Some(thread::spawn(move || {
            monitor_loop(cpu_usage, memory_usage, running, stop_signal, interval);
        }));
    }

    /// Stop the background monitoring thread.
    ///
    /// Uses a Condvar to wake the thread immediately instead of waiting for
    /// the sleep interval to complete. Includes a 2-second timeout as a safety net.
    pub fn stop(&mut self) {
        self.running.store(false, Ordering::SeqCst);

        // Signal the condvar to wake the thread immediately
        {
            let (lock, cvar) = &*self.stop_signal;
            *lock.lock() = true;
            cvar.notify_all();
        }

        if let Some(handle) = self.thread_handle.take() {
            // Try to join with a timeout as safety net
            let start = Instant::now();
            let timeout = Duration::from_secs(2);

            while !handle.is_finished() && start.elapsed() < timeout {
                thread::sleep(Duration::from_millis(10));
            }

            if handle.is_finished() {
                let _ = handle.join();
            }
            // If still running after 2s, abandon the thread (it will terminate on process exit)
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
///
/// Uses a Condvar-based interruptible sleep so that stop() can wake
/// the thread immediately instead of waiting for the full interval.
/// All sleeps (including CPU measurement delay) are interruptible.
fn monitor_loop(
    cpu_usage: Arc<AtomicU32>,
    memory_usage: Arc<AtomicU32>,
    running: Arc<AtomicBool>,
    stop_signal: Arc<(Mutex<bool>, Condvar)>,
    interval: Duration,
) {
    while running.load(Ordering::SeqCst) {
        // Check stop signal before CPU measurement (which has internal delay)
        if check_stop_signal(&stop_signal) {
            break;
        }

        let cpu = measure_cpu_usage_interruptible(&stop_signal);

        // Check stop signal after CPU measurement
        if check_stop_signal(&stop_signal) {
            break;
        }

        let memory = measure_memory_usage();
        cpu_usage.store(cpu as u32, Ordering::SeqCst);
        memory_usage.store(memory as u32, Ordering::SeqCst);

        // Use condvar for interruptible sleep
        let (lock, cvar) = &*stop_signal;
        let mut stopped = lock.lock();
        if *stopped {
            break; // Stop signal received
        }
        // Wait for interval or until signaled to stop
        let _result = cvar.wait_for(&mut stopped, interval);
        if *stopped {
            break; // Stop signal received during wait
        }
    }
}

/// Check if the stop signal has been set
fn check_stop_signal(stop_signal: &Arc<(Mutex<bool>, Condvar)>) -> bool {
    let (lock, _) = &**stop_signal;
    *lock.lock()
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

/// Measure CPU usage with interruptible sleep using condvar.
/// Returns 0.0 if interrupted before measurement completes.
fn measure_cpu_usage_interruptible(stop_signal: &Arc<(Mutex<bool>, Condvar)>) -> f32 {
    #[cfg(target_os = "linux")]
    {
        if let Some(usage) = measure_cpu_from_proc_stat_interruptible(stop_signal) {
            return usage;
        }
    }

    // Fallback to sysinfo crate (interruptible version)
    measure_cpu_from_sysinfo_interruptible(stop_signal)
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

/// Measure CPU usage from /proc/stat with interruptible sleep.
/// Returns None if interrupted or if reading /proc/stat fails.
#[cfg(target_os = "linux")]
fn measure_cpu_from_proc_stat_interruptible(stop_signal: &Arc<(Mutex<bool>, Condvar)>) -> Option<f32> {
    // First sample
    let (total1, idle1) = read_proc_stat()?;

    // Use condvar for interruptible wait
    let (lock, cvar) = &**stop_signal;
    let mut stopped = lock.lock();
    if *stopped {
        return Some(0.0); // Interrupted before measurement
    }
    // Wait for 500ms or until signaled to stop
    let _result = cvar.wait_for(&mut stopped, Duration::from_millis(500));
    if *stopped {
        return Some(0.0); // Interrupted during wait
    }
    drop(stopped);

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

/// Measure CPU usage using sysinfo with interruptible sleep.
/// Returns 0.0 if interrupted before measurement completes.
fn measure_cpu_from_sysinfo_interruptible(stop_signal: &Arc<(Mutex<bool>, Condvar)>) -> f32 {
    use sysinfo::System;

    let mut sys = System::new();

    // First refresh to initialize
    sys.refresh_cpu_usage();

    // Use condvar for interruptible wait
    let (lock, cvar) = &**stop_signal;
    let mut stopped = lock.lock();
    if *stopped {
        return 0.0; // Interrupted before measurement
    }
    // Wait for 500ms or until signaled to stop
    let _result = cvar.wait_for(&mut stopped, Duration::from_millis(500));
    if *stopped {
        return 0.0; // Interrupted during wait
    }
    drop(stopped);

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
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
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
        assert!(usage >= 0.0 && usage <= 100.0, "Memory usage should be 0-100%");
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

    #[test]
    fn test_stop_completes_quickly() {
        // Start a monitor with a long interval (10 seconds)
        // Stop should return within 200ms due to condvar signaling
        let mut monitor = ResourceMonitor::new(10);
        monitor.start();

        // Wait a bit for the thread to start and potentially enter sleep
        thread::sleep(Duration::from_millis(50));

        let start = Instant::now();
        monitor.stop();
        let elapsed = start.elapsed();

        // Stop should complete within 200ms, not the full 10 seconds
        assert!(
            elapsed < Duration::from_millis(200),
            "stop() took {:?}, expected < 200ms (condvar should wake thread immediately)",
            elapsed
        );
    }

    #[test]
    fn test_start_stop_cycle() {
        // Verify rapid start/stop cycles don't hang
        let mut monitor = ResourceMonitor::new(5);

        for _ in 0..3 {
            let start = Instant::now();
            monitor.start();
            thread::sleep(Duration::from_millis(20));
            monitor.stop();
            let elapsed = start.elapsed();

            assert!(
                elapsed < Duration::from_millis(300),
                "start/stop cycle took {:?}, expected < 300ms",
                elapsed
            );
        }
    }

    #[test]
    fn test_stop_from_sleeping() {
        // Start monitor, wait for it to enter sleep, then stop
        let mut monitor = ResourceMonitor::new(5);
        monitor.start();

        // Wait 100ms - thread should be sleeping by now
        thread::sleep(Duration::from_millis(100));

        let start = Instant::now();
        monitor.stop();
        let elapsed = start.elapsed();

        // Even though thread is sleeping, stop should complete quickly
        assert!(
            elapsed < Duration::from_millis(200),
            "stop() from sleeping state took {:?}, expected < 200ms",
            elapsed
        );
    }

    #[test]
    fn test_stop_without_start() {
        // Calling stop on an unstarted monitor should not hang
        let mut monitor = ResourceMonitor::new(5);
        let start = Instant::now();
        monitor.stop();
        let elapsed = start.elapsed();

        assert!(
            elapsed < Duration::from_millis(50),
            "stop() on unstarted monitor took {:?}, expected < 50ms",
            elapsed
        );
    }
}
