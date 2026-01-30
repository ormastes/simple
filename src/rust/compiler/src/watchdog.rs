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

/// Start the watchdog thread with the given timeout in seconds.
/// If a watchdog is already running, it is stopped first.
pub fn start_watchdog(timeout_secs: u64) {
    stop_watchdog();

    TIMEOUT_EXCEEDED.store(false, Ordering::SeqCst);

    let stop_flag = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let stop_clone = Arc::clone(&stop_flag);
    let deadline = Instant::now() + Duration::from_secs(timeout_secs);

    let handle = thread::Builder::new()
        .name("simple-watchdog".to_string())
        .spawn(move || {
            while !stop_clone.load(Ordering::Relaxed) {
                if Instant::now() >= deadline {
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
