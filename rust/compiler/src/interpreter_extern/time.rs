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
