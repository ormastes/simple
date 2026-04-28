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

/// Optional context (e.g. current spec path) recorded into the crash log
/// when the watchdog fires. Set by the test runner (or any caller) before
/// `start_watchdog` and cleared after `stop_watchdog` to disambiguate which
/// spec each `crash_<PID>.log` entry came from.
static WATCHDOG_CONTEXT: Mutex<Option<String>> = Mutex::new(None);

/// Set or clear the watchdog context label. Pass `Some(path)` before
/// `start_watchdog` to tag the kill, and `None` after `stop_watchdog`
/// to avoid leaking a stale label into a later, unrelated kill.
pub fn set_watchdog_context(ctx: Option<String>) {
    if let Ok(mut g) = WATCHDOG_CONTEXT.lock() {
        *g = ctx;
    }
}

/// Memory limit in bytes for the watchdog to monitor.
/// Defaults to 0 (disabled). Overridable via `SIMPLE_MEMORY_LIMIT_MB`
/// (or legacy `SIMPLE_TEST_MEMORY_LIMIT_MB`).
/// Each binary/wrapper should set its own limit as needed.
pub fn memory_limit_bytes() -> u64 {
    std::env::var("SIMPLE_MEMORY_LIMIT_MB")
        .or_else(|_| std::env::var("SIMPLE_TEST_MEMORY_LIMIT_MB"))
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(0)
        * 1024
        * 1024
}

/// Read current RSS from /proc/self/statm (Linux only). Returns 0 on failure.
#[cfg(target_os = "linux")]
pub fn read_rss_bytes() -> u64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok())
        .map(|pages| pages * 4096)
        .unwrap_or(0)
}

#[cfg(target_os = "macos")]
pub fn read_rss_bytes() -> u64 {
    // Use `ps` to read RSS on macOS (returns KB)
    let pid = std::process::id();
    std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()
        .and_then(|out| String::from_utf8_lossy(&out.stdout).trim().parse::<u64>().ok())
        .map(|kb| kb * 1024)
        .unwrap_or(0)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub fn read_rss_bytes() -> u64 {
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
                    let msg = format!("[watchdog] wall-clock timeout ({}s) exceeded", timeout_secs);
                    eprintln!("{}", msg);
                    write_watchdog_crash_log(&msg);
                    TIMEOUT_EXCEEDED.store(true, Ordering::SeqCst);
                    return;
                }
                // Check memory every iteration (100ms).
                let rss = read_rss_bytes();
                if mem_limit > 0 && rss > mem_limit {
                    let msg = format!(
                        "[watchdog] RSS {}MB exceeds limit {}MB — triggering timeout",
                        rss / (1024 * 1024),
                        mem_limit / (1024 * 1024),
                    );
                    eprintln!("{}", msg);
                    write_watchdog_crash_log(&msg);
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

/// Write watchdog crash info to a log file (best-effort).
fn write_watchdog_crash_log(msg: &str) {
    use std::io::Write;
    let pid = std::process::id();
    let crash_dir = std::env::var("SIMPLE_LOG_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            let local = std::path::PathBuf::from(".simple/logs");
            if local.exists() || std::fs::create_dir_all(&local).is_ok() {
                local
            } else {
                std::env::temp_dir().join("simple_logs")
            }
        });
    let _ = std::fs::create_dir_all(&crash_dir);
    let path = crash_dir.join(format!("crash_{}.log", pid));
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(&path) {
        let _ = writeln!(f, "=== WATCHDOG CRASH ===");
        let _ = writeln!(f, "PID: {}", pid);
        if let Ok(g) = WATCHDOG_CONTEXT.lock() {
            if let Some(s) = g.as_ref() {
                let _ = writeln!(f, "Spec: {}", s);
            }
        }
        let _ = writeln!(f, "OS: {} {}", std::env::consts::OS, std::env::consts::ARCH);
        let _ = writeln!(f, "{}", msg);
        let _ = writeln!(f, "======================\n");
        eprintln!("[watchdog] crash report: {}", path.display());
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

    #[test]
    fn test_watchdog_crash_log_includes_spec_context() {
        use std::time::{SystemTime, UNIX_EPOCH};
        fault_detection::reset_timeout();
        // Route the crash log to a test-private dir so we don't pollute .simple/logs
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let tmp_dir = std::env::temp_dir().join(format!("watchdog_log_test_{}", nanos));
        let _ = std::fs::remove_dir_all(&tmp_dir);
        std::fs::create_dir_all(&tmp_dir).unwrap();
        std::env::set_var("SIMPLE_LOG_DIR", &tmp_dir);

        let spec_path = "/tmp/some/fake_demo_spec.spl";
        set_watchdog_context(Some(spec_path.to_string()));
        start_watchdog(1);
        // Wait until the watchdog fires
        let deadline = Instant::now() + Duration::from_secs(10);
        while !fault_detection::is_timeout_exceeded() {
            assert!(
                Instant::now() < deadline,
                "watchdog did not fire within 10 seconds"
            );
            std::thread::sleep(Duration::from_millis(50));
        }
        stop_watchdog();
        set_watchdog_context(None);
        fault_detection::reset_timeout();

        // Find the crash log and verify it contains the spec path.
        let pid = std::process::id();
        let log_path = tmp_dir.join(format!("crash_{}.log", pid));
        let contents = std::fs::read_to_string(&log_path)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", log_path.display(), e));
        assert!(
            contents.contains(&format!("Spec: {}", spec_path)),
            "crash log missing spec context. Contents:\n{}",
            contents
        );
        std::env::remove_var("SIMPLE_LOG_DIR");
        let _ = std::fs::remove_dir_all(&tmp_dir);
    }
}
