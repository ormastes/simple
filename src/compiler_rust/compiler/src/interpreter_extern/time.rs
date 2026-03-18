//! Time-related extern functions
//!
//! Functions for querying system time and durations.

use crate::error::CompileError;
use crate::value::Value;

/// Get current time in seconds since Unix epoch
///
/// Callable from Simple as: `rt_time_now_seconds()`
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * Float representing seconds since Unix epoch (with fractional seconds)
pub fn rt_time_now_seconds(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let time = simple_runtime::value::rt_time_now_seconds();
        Ok(Value::Float(time))
    }
}

/// Get current time as Unix timestamp (integer seconds since epoch)
///
/// Callable from Simple as: `_current_time_unix()`
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * i64 representing seconds since Unix epoch (integer)
pub fn _current_time_unix(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let time = simple_runtime::value::rt_time_now_seconds();
        Ok(Value::Int(time as i64))
    }
}

/// Get current time in milliseconds since Unix epoch
///
/// Callable from Simple as: `rt_current_time_ms()`
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * i64 representing milliseconds since Unix epoch
pub fn rt_current_time_ms(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let time_seconds = simple_runtime::value::rt_time_now_seconds();
        let time_ms = (time_seconds * 1000.0) as i64;
        Ok(Value::Int(time_ms))
    }
}

// ============================================================================
// Progress Timing Functions
// ============================================================================

/// Initialize progress timing - stores current time as start
///
/// Callable from Simple as: `rt_progress_init()`
pub fn rt_progress_init(_args: &[Value]) -> Result<Value, CompileError> {
    simple_runtime::value::ffi::rt_progress_init();
    Ok(Value::Nil)
}

/// Reset progress timing - clears stored start time
///
/// Callable from Simple as: `rt_progress_reset()`
pub fn rt_progress_reset(_args: &[Value]) -> Result<Value, CompileError> {
    simple_runtime::value::ffi::rt_progress_reset();
    Ok(Value::Nil)
}

/// Get elapsed seconds since progress was initialized
///
/// Callable from Simple as: `rt_progress_get_elapsed_seconds()`
///
/// # Returns
/// * Float representing seconds since init (0.0 if never initialized)
pub fn rt_progress_get_elapsed_seconds(_args: &[Value]) -> Result<Value, CompileError> {
    let elapsed = simple_runtime::value::ffi::rt_progress_get_elapsed_seconds();
    Ok(Value::Float(elapsed))
}

// ============================================================================
// DateTime FFI Functions
// ============================================================================

/// Get current Unix timestamp in microseconds since epoch
///
/// Callable from Simple as: `rt_time_now_unix_micros()`
pub fn rt_time_now_unix_micros(_args: &[Value]) -> Result<Value, CompileError> {
    let micros = simple_runtime::value::ffi::rt_time_now_unix_micros();
    Ok(Value::Int(micros))
}

/// Get current monotonic time in nanoseconds
///
/// Callable from Simple as: `rt_time_now_nanos()`
///
/// Uses std::time::Instant for monotonic high-resolution timing.
/// Suitable for benchmarking and performance measurement.
pub fn rt_time_now_nanos(_args: &[Value]) -> Result<Value, CompileError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as i64;
    Ok(Value::Int(nanos))
}

/// Get current monotonic time in microseconds
///
/// Callable from Simple as: `rt_time_now_micros()`
///
/// Uses std::time::Instant for monotonic high-resolution timing.
/// Suitable for profiling and performance measurement.
pub fn rt_time_now_micros(_args: &[Value]) -> Result<Value, CompileError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let micros = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_micros() as i64;
    Ok(Value::Int(micros))
}

/// Extract year from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_year(micros)`
pub fn rt_timestamp_get_year(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_year requires i64 argument")),
    };
    let year = simple_runtime::value::ffi::rt_timestamp_get_year(micros);
    Ok(Value::Int(year as i64))
}

/// Extract month from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_month(micros)`
pub fn rt_timestamp_get_month(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_month requires i64 argument")),
    };
    let month = simple_runtime::value::ffi::rt_timestamp_get_month(micros);
    Ok(Value::Int(month as i64))
}

/// Extract day from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_day(micros)`
pub fn rt_timestamp_get_day(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_day requires i64 argument")),
    };
    let day = simple_runtime::value::ffi::rt_timestamp_get_day(micros);
    Ok(Value::Int(day as i64))
}

/// Extract hour from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_hour(micros)`
pub fn rt_timestamp_get_hour(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_hour requires i64 argument")),
    };
    let hour = simple_runtime::value::ffi::rt_timestamp_get_hour(micros);
    Ok(Value::Int(hour as i64))
}

/// Extract minute from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_minute(micros)`
pub fn rt_timestamp_get_minute(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_minute requires i64 argument")),
    };
    let minute = simple_runtime::value::ffi::rt_timestamp_get_minute(micros);
    Ok(Value::Int(minute as i64))
}

/// Extract second from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_second(micros)`
pub fn rt_timestamp_get_second(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => return Err(CompileError::semantic("rt_timestamp_get_second requires i64 argument")),
    };
    let second = simple_runtime::value::ffi::rt_timestamp_get_second(micros);
    Ok(Value::Int(second as i64))
}

/// Extract microsecond from timestamp (microseconds)
///
/// Callable from Simple as: `rt_timestamp_get_microsecond(micros)`
pub fn rt_timestamp_get_microsecond(args: &[Value]) -> Result<Value, CompileError> {
    let micros = match args.first() {
        Some(Value::Int(m)) => *m,
        _ => {
            return Err(CompileError::semantic(
                "rt_timestamp_get_microsecond requires i64 argument",
            ))
        }
    };
    let microsecond = simple_runtime::value::ffi::rt_timestamp_get_microsecond(micros);
    Ok(Value::Int(microsecond as i64))
}

/// Create timestamp from components
///
/// Callable from Simple as: `rt_timestamp_from_components(year, month, day, hour, minute, second, microsecond)`
pub fn rt_timestamp_from_components(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 7 {
        return Err(CompileError::semantic(
            "rt_timestamp_from_components requires 7 arguments",
        ));
    }

    let year = match &args[0] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("year must be i32")),
    };
    let month = match &args[1] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("month must be i32")),
    };
    let day = match &args[2] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("day must be i32")),
    };
    let hour = match &args[3] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("hour must be i32")),
    };
    let minute = match &args[4] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("minute must be i32")),
    };
    let second = match &args[5] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("second must be i32")),
    };
    let microsecond = match &args[6] {
        Value::Int(v) => *v as i32,
        _ => return Err(CompileError::semantic("microsecond must be i32")),
    };

    let timestamp =
        simple_runtime::value::ffi::rt_timestamp_from_components(year, month, day, hour, minute, second, microsecond);
    Ok(Value::Int(timestamp))
}

/// Add days to timestamp
///
/// Callable from Simple as: `rt_timestamp_add_days(micros, days)`
pub fn rt_timestamp_add_days(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic("rt_timestamp_add_days requires 2 arguments"));
    }

    let micros = match &args[0] {
        Value::Int(v) => *v,
        _ => return Err(CompileError::semantic("micros must be i64")),
    };
    let days = match &args[1] {
        Value::Int(v) => *v,
        _ => return Err(CompileError::semantic("days must be i64")),
    };

    let result = simple_runtime::value::ffi::rt_timestamp_add_days(micros, days);
    Ok(Value::Int(result))
}

/// Calculate difference in days between two timestamps
///
/// Callable from Simple as: `rt_timestamp_diff_days(micros1, micros2)`
pub fn rt_timestamp_diff_days(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic("rt_timestamp_diff_days requires 2 arguments"));
    }

    let micros1 = match &args[0] {
        Value::Int(v) => *v,
        _ => return Err(CompileError::semantic("micros1 must be i64")),
    };
    let micros2 = match &args[1] {
        Value::Int(v) => *v,
        _ => return Err(CompileError::semantic("micros2 must be i64")),
    };

    let result = simple_runtime::value::ffi::rt_timestamp_diff_days(micros1, micros2);
    Ok(Value::Int(result))
}

// ============================================================================
// Monotonic High-Resolution Timing (for benchmarking/profiling)
// ============================================================================

/// Get monotonic time in nanoseconds
///
/// Callable from Simple as: `rt_time_monotonic_ns()`
///
/// Uses std::time::Instant for true monotonic timing, suitable for
/// benchmarking and performance measurement. Values are relative to
/// an arbitrary epoch (process start), so only differences are meaningful.
pub fn rt_time_monotonic_ns(_args: &[Value]) -> Result<Value, CompileError> {
    use std::sync::OnceLock;
    use std::time::Instant;

    static EPOCH: OnceLock<Instant> = OnceLock::new();
    let elapsed = EPOCH.get_or_init(Instant::now).elapsed();
    Ok(Value::Int(elapsed.as_nanos() as i64))
}

/// Get current timestamp as ISO 8601 string
///
/// Callable from Simple as: `rt_timestamp_iso8601()`
///
/// # Returns
/// * String in format "YYYY-MM-DDTHH:MM:SSZ"
pub fn rt_timestamp_iso8601(_args: &[Value]) -> Result<Value, CompileError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let micros = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_micros() as i64;

    let year = simple_runtime::value::ffi::rt_timestamp_get_year(micros);
    let month = simple_runtime::value::ffi::rt_timestamp_get_month(micros);
    let day = simple_runtime::value::ffi::rt_timestamp_get_day(micros);
    let hour = simple_runtime::value::ffi::rt_timestamp_get_hour(micros);
    let minute = simple_runtime::value::ffi::rt_timestamp_get_minute(micros);
    let second = simple_runtime::value::ffi::rt_timestamp_get_second(micros);

    Ok(Value::Str(format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        year, month, day, hour, minute, second
    )))
}

/// Get current time in milliseconds
///
/// Callable from Simple as: `rt_time_ms()`
///
/// Alias for rt_current_time_ms, used by profiler_adapter.spl.
pub fn rt_time_ms(args: &[Value]) -> Result<Value, CompileError> {
    rt_current_time_ms(args)
}

// ============================================================================
// Profiler FFI (interpreter-side stubs)
// ============================================================================

/// Record a profiler call event (no-op in interpreter mode)
///
/// Callable from Simple as: `rt_profiler_record_call(name, file, line)`
///
/// The runtime profiler is for compiled (Cranelift) code. In interpreter
/// mode these are no-ops since the interpreter has its own profiling.
pub fn rt_profiler_record_call(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil)
}

/// Record a profiler return event (no-op in interpreter mode)
///
/// Callable from Simple as: `rt_profiler_record_return(name, file, line)`
pub fn rt_profiler_record_return(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil)
}

/// Check if profiler is active (always false in interpreter mode)
///
/// Callable from Simple as: `rt_profiler_is_active()`
pub fn rt_profiler_is_active(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rt_time_now_seconds() {
        let result = rt_time_now_seconds(&[]).unwrap();
        match result {
            Value::Float(t) => {
                // Time should be reasonable (after year 2020, before year 2100)
                assert!(t > 1_600_000_000.0); // After Sept 2020
                assert!(t < 4_000_000_000.0); // Before year 2100
            }
            _ => panic!("Expected Float value"),
        }
    }

    #[test]
    fn test_rt_time_now_unix_micros() {
        let result = rt_time_now_unix_micros(&[]).unwrap();
        match result {
            Value::Int(m) => {
                // Should be after 2020 in microseconds
                assert!(m > 1_577_836_800_000_000);
            }
            _ => panic!("Expected Int value"),
        }
    }
}
