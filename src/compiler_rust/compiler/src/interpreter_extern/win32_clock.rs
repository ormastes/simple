//! Fixed Win32 clock ABI. This is not a generic Win32 FFI bridge.
use crate::error::CompileError;
use crate::value::Value;

fn checked_tick_count(args: &[Value], read: impl FnOnce() -> u64) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::semantic("GetTickCount64 requires zero arguments"));
    }
    Ok(Value::UInt { value: read(), width: 64 })
}

#[cfg(windows)]
#[link(name = "kernel32")]
extern "system" {
    fn GetTickCount64() -> u64;
}

/// Preserve ULONGLONG's complete unsigned range and the system calling convention.
pub fn get_tick_count64(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(windows)]
    {
        checked_tick_count(args, || unsafe { GetTickCount64() })
    }
    #[cfg(not(windows))]
    {
        if !args.is_empty() {
            return Err(CompileError::semantic("GetTickCount64 requires zero arguments"));
        }
        Err(CompileError::semantic("GetTickCount64 is only available on Windows"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retains_unsigned_boundaries_without_truncation() {
        for ticks in [0, u32::MAX as u64 + 1, i64::MAX as u64 + 1, u64::MAX] {
            assert_eq!(checked_tick_count(&[], || ticks).unwrap(), Value::UInt { value: ticks, width: 64 });
        }
    }
    #[test]
    fn rejects_arguments_before_os_effect() {
        let result = checked_tick_count(&[Value::Int(0)], || panic!("must not call clock"));
        assert!(result.is_err());
        assert!(get_tick_count64(&[Value::Int(0)]).is_err());
    }
    #[cfg(windows)]
    #[test]
    fn real_clock_is_unsigned_and_nondecreasing() {
        let first = get_tick_count64(&[]).unwrap();
        let second = get_tick_count64(&[]).unwrap();
        match (first, second) {
            (Value::UInt { value: a, width: 64 }, Value::UInt { value: b, width: 64 }) => assert!(b >= a),
            other => panic!("wrong Win32 return representation: {other:?}"),
        }
    }
    #[cfg(not(windows))]
    #[test]
    fn other_hosts_fail_closed() { assert!(get_tick_count64(&[]).is_err()); }
}
