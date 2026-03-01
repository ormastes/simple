//! Watchdog thread for wall-clock timeout detection.
//!
//! Spawns a background thread that periodically checks if the execution
//! has exceeded the configured timeout. Zero overhead on the fast path
//! (single atomic load with Relaxed ordering).

use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use simple_common::fault_detection::TIMEOUT_EXCEEDED;

/// Handle to a running watchdog thread.
struct WatchdogHandle {
    stop_flag: Arc<std::sync::atomic::AtomicBool>,
    thread: Option<thread::JoinHandle<()>>,
}

static WATCHDOG: Mutex<Option<WatchdogHandle>> = Mutex::new(None);

/// Memory limit in bytes for the watchdog to monitor.
/// Defaults to 2 GB. Overridable via `SIMPLE_TEST_MEMORY_LIMIT_MB`.
fn memory_limit_bytes() -> u64 {
    std::env::var("SIMPLE_TEST_MEMORY_LIMIT_MB")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(2048)
        * 1024
        * 1024
}

/// Read current RSS from /proc/self/statm (Linux only). Returns 0 on failure.
#[cfg(target_os = "linux")]
fn read_rss_bytes() -> u64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok())
        .map(|pages| pages * 4096)
        .unwrap_or(0)
}

#[cfg(not(target_os = "linux"))]
fn read_rss_bytes() -> u64 {
    0
}

/// Start the watchdog thread with the given timeout in seconds.
/// If a watchdog is already running, it is stopped first.
///
/// The watchdog monitors both wall-clock time AND resident memory.
/// If either limit is exceeded, it sets `TIMEOUT_EXCEEDED` so that
/// `check_timeout!()` in the interpreter will bail out.
pub fn start_watchdog(timeout_secs: u64) {
    stop_watchdog();

    TIMEOUT_EXCEEDED.store(false, Ordering::SeqCst);

    let stop_flag = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let stop_clone = Arc::clone(&stop_flag);
    let deadline = Instant::now() + Duration::from_secs(timeout_secs);
    let mem_limit = memory_limit_bytes();

    let handle = thread::Builder::new()
        .name("simple-watchdog".to_string())
        .spawn(move || {
            while !stop_clone.load(Ordering::Relaxed) {
                if Instant::now() >= deadline {
                    eprintln!("[watchdog] wall-clock timeout ({timeout_secs}s) exceeded");
                    TIMEOUT_EXCEEDED.store(true, Ordering::SeqCst);
                    return;
                }
                // Check memory every 500ms (every 5th iteration).
                let rss = read_rss_bytes();
                if mem_limit > 0 && rss > mem_limit {
                    eprintln!(
                        "[watchdog] RSS {}MB exceeds limit {}MB — triggering timeout",
                        rss / (1024 * 1024),
                        mem_limit / (1024 * 1024),
                    );
                    TIMEOUT_EXCEEDED.store(true, Ordering::SeqCst);
                    return;
                }
                thread::sleep(Duration::from_millis(100));
            }
        })
        .expect("failed to spawn watchdog thread");

    if let Ok(mut guard) = WATCHDOG.lock() {
        *guard = Some(WatchdogHandle {
            stop_flag,
            thread: Some(handle),
        });
    }
}

/// Stop the watchdog thread if running.
pub fn stop_watchdog() {
    if let Ok(mut guard) = WATCHDOG.lock() {
        if let Some(mut wh) = guard.take() {
            wh.stop_flag.store(true, Ordering::SeqCst);
            if let Some(thread) = wh.thread.take() {
                let _ = thread.join();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_common::fault_detection;

    #[test]
    fn test_watchdog_start_stop() {
        fault_detection::reset_timeout();
        assert!(!fault_detection::is_timeout_exceeded());
        // Start with large timeout, stop immediately
        start_watchdog(60);
        assert!(!fault_detection::is_timeout_exceeded());
        stop_watchdog();
        assert!(!fault_detection::is_timeout_exceeded());
    }

    #[test]
    fn test_watchdog_triggers_timeout() {
        fault_detection::reset_timeout();
        // 1-second timeout
        start_watchdog(1);
        // Poll until the watchdog fires, with a generous upper bound
        let deadline = Instant::now() + Duration::from_secs(10);
        while !fault_detection::is_timeout_exceeded() {
            assert!(Instant::now() < deadline, "watchdog did not fire within 10 seconds");
            std::thread::sleep(Duration::from_millis(50));
        }
        assert!(fault_detection::is_timeout_exceeded());
        stop_watchdog();
        fault_detection::reset_timeout();
    }

    #[test]
    fn test_watchdog_does_not_fire_before_deadline() {
        fault_detection::reset_timeout();
        start_watchdog(60);
        std::thread::sleep(Duration::from_millis(200));
        assert!(!fault_detection::is_timeout_exceeded());
        stop_watchdog();
    }

    #[test]
    fn test_watchdog_restart() {
        fault_detection::reset_timeout();
        start_watchdog(60);
        // Restart with new timeout
        start_watchdog(60);
        assert!(!fault_detection::is_timeout_exceeded());
        stop_watchdog();
    }
}
