//! Performance measurement FFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call into perf functionality.
//! Delegates to simple_runtime::rt_perf_* functions.

use crate::error::CompileError;
use crate::value::Value;

/// Enable perf tracking at runtime
pub fn rt_perf_enable(_args: &[Value]) -> Result<Value, CompileError> {
    simple_runtime::rt_perf_enable();
    Ok(Value::Nil)
}

/// Check if perf tracking is enabled
pub fn rt_perf_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(simple_runtime::rt_perf_enabled()))
}

/// Get monotonic nanoseconds
pub fn rt_perf_clock_ns(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::rt_perf_clock_ns()))
}

/// Get CPU cycle counter (rdtsc on x86, fallback to clock_ns)
pub fn rt_perf_rdtsc(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_runtime::rt_perf_rdtsc()))
}

/// Convert rdtsc cycles to nanoseconds
/// Args: (cycles: i64, freq_mhz: i64)
pub fn rt_perf_cycles_to_ns(args: &[Value]) -> Result<Value, CompileError> {
    let cycles = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => 0,
    };
    let freq_mhz = match args.get(1) {
        Some(Value::Int(n)) => *n,
        _ => 0,
    };
    Ok(Value::Int(simple_runtime::rt_perf_cycles_to_ns(cycles, freq_mhz)))
}

/// Enter a performance region
/// Args: (region_id: i64, file: text, line: i64)
pub fn rt_perf_region_enter(args: &[Value]) -> Result<Value, CompileError> {
    if !simple_runtime::rt_perf_enabled() {
        return Ok(Value::Nil);
    }
    let region_id = match args.first() {
        Some(Value::Int(n)) => *n as u32,
        _ => 0,
    };
    let file = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => String::new(),
    };
    let line = match args.get(2) {
        Some(Value::Int(n)) => *n as u32,
        _ => 0,
    };
    let file_cstr = std::ffi::CString::new(file)
        .unwrap_or_else(|_| std::ffi::CString::new("<error>").unwrap());
    unsafe {
        simple_runtime::rt_perf_region_enter(region_id, file_cstr.as_ptr(), line);
    }
    Ok(Value::Nil)
}

/// Exit a performance region
/// Args: (region_id: i64, file: text, line: i64)
pub fn rt_perf_region_exit(args: &[Value]) -> Result<Value, CompileError> {
    if !simple_runtime::rt_perf_enabled() {
        return Ok(Value::Nil);
    }
    let region_id = match args.first() {
        Some(Value::Int(n)) => *n as u32,
        _ => 0,
    };
    let file = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => String::new(),
    };
    let line = match args.get(2) {
        Some(Value::Int(n)) => *n as u32,
        _ => 0,
    };
    let file_cstr = std::ffi::CString::new(file)
        .unwrap_or_else(|_| std::ffi::CString::new("<error>").unwrap());
    unsafe {
        simple_runtime::rt_perf_region_exit(region_id, file_cstr.as_ptr(), line);
    }
    Ok(Value::Nil)
}

/// Dump perf data as SDN string
pub fn rt_perf_dump_sdn(_args: &[Value]) -> Result<Value, CompileError> {
    let sdn = unsafe {
        let ptr = simple_runtime::rt_perf_dump_sdn();
        if ptr.is_null() {
            return Ok(Value::Str(String::new()));
        }
        let s = std::ffi::CStr::from_ptr(ptr)
            .to_string_lossy()
            .to_string();
        simple_runtime::rt_perf_free_sdn(ptr);
        s
    };
    Ok(Value::Str(sdn))
}

/// Free SDN string (no-op in interpreter - GC handles memory)
pub fn rt_perf_free_sdn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil)
}

/// Clear all perf data
pub fn rt_perf_clear(_args: &[Value]) -> Result<Value, CompileError> {
    simple_runtime::rt_perf_clear();
    Ok(Value::Nil)
}
