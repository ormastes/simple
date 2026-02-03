//! time module
//!
//! Time Operations FFI
//! 
//! Current time, timestamps, and date/time components.

use std::time::{SystemTime, UNIX_EPOCH};
use chrono::prelude::*;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Get current Unix timestamp in microseconds
#[no_mangle]
pub extern "C" fn rt_time_now_unix_micros() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_micros() as i64)
        .unwrap_or(0)
}

/// Get current Unix timestamp in milliseconds
#[no_mangle]
pub extern "C" fn rt_current_time_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

/// Get year from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_year(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.year()
}

/// Get month (1-12) from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_month(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.month() as i32
}

/// Get day (1-31) from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_day(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.day() as i32
}

/// Get hour (0-23) from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_hour(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.hour() as i32
}

/// Get minute (0-59) from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_minute(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.minute() as i32
}

/// Get second (0-59) from Unix microseconds
#[no_mangle]
pub extern "C" fn rt_timestamp_get_second(micros: i64) -> i32 {
    let secs = micros / 1_000_000;
    let dt = chrono::DateTime::from_timestamp(secs, 0).unwrap_or_default();
    dt.second() as i32
}

