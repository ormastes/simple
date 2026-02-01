// Time FFI functions for build system
// Provides current time, formatting, and duration calculations

use super::RuntimeValue;
use std::os::raw::c_char;
use std::ffi::{CStr, CString};
use std::time::{SystemTime, UNIX_EPOCH};

/// Get current time in milliseconds since UNIX epoch
#[no_mangle]
pub extern "C" fn rt_time_current_ms() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_millis() as i64,
        Err(_) => 0,
    }
}

/// Get current time in seconds since UNIX epoch
#[no_mangle]
pub extern "C" fn rt_time_current_secs() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_secs() as i64,
        Err(_) => 0,
    }
}

/// Format timestamp (milliseconds since epoch) to ISO 8601 string
/// Returns: "2026-02-01T12:34:56Z"
#[no_mangle]
pub extern "C" fn rt_time_format_iso8601(timestamp_ms: i64) -> *mut c_char {
    use chrono::{DateTime, Utc};
    use std::time::Duration;

    let duration = Duration::from_millis(timestamp_ms as u64);
    let datetime = DateTime::<Utc>::from(UNIX_EPOCH + duration);
    let formatted = format!("{}", datetime.format("%Y-%m-%dT%H:%M:%SZ"));

    match CString::new(formatted) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => CString::new("").unwrap().into_raw(),
    }
}

/// Format timestamp to human-readable string
/// Returns: "2026-02-01 12:34:56"
#[no_mangle]
pub extern "C" fn rt_time_format_human(timestamp_ms: i64) -> *mut c_char {
    use chrono::{DateTime, Utc};
    use std::time::Duration;

    let duration = Duration::from_millis(timestamp_ms as u64);
    let datetime = DateTime::<Utc>::from(UNIX_EPOCH + duration);
    let formatted = format!("{}", datetime.format("%Y-%m-%d %H:%M:%S"));

    match CString::new(formatted) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => CString::new("").unwrap().into_raw(),
    }
}

/// Calculate duration between two timestamps in milliseconds
#[no_mangle]
pub extern "C" fn rt_time_duration_ms(start_ms: i64, end_ms: i64) -> i64 {
    end_ms - start_ms
}

/// Sleep for specified milliseconds
#[no_mangle]
pub extern "C" fn rt_time_sleep_ms(duration_ms: i64) {
    if duration_ms > 0 {
        std::thread::sleep(std::time::Duration::from_millis(duration_ms as u64));
    }
}

/// Get monotonic clock time (for precise duration measurements)
/// Returns nanoseconds since an unspecified epoch
#[no_mangle]
pub extern "C" fn rt_time_monotonic_ns() -> i64 {
    use std::time::Instant;
    static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

    let start = START.get_or_init(|| Instant::now());
    start.elapsed().as_nanos() as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_current_time() {
        let ms = rt_time_current_ms();
        assert!(ms > 0, "Current time should be positive");

        let secs = rt_time_current_secs();
        assert!(secs > 0, "Current time in seconds should be positive");

        // Milliseconds should be roughly 1000x seconds
        assert!((ms / 1000 - secs).abs() < 2, "ms and secs should be consistent");
    }

    #[test]
    fn test_duration() {
        let start = rt_time_current_ms();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let end = rt_time_current_ms();

        let duration = rt_time_duration_ms(start, end);
        assert!(duration >= 10, "Duration should be at least 10ms");
        assert!(duration < 100, "Duration should be less than 100ms");
    }

    #[test]
    fn test_monotonic_clock() {
        let t1 = rt_time_monotonic_ns();
        std::thread::sleep(std::time::Duration::from_millis(1));
        let t2 = rt_time_monotonic_ns();

        assert!(t2 > t1, "Monotonic clock should always increase");
    }
}
