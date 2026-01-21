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
}
