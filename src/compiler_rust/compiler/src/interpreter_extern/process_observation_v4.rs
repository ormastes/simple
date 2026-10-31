//! Interpreter marshalling for the Darwin process observation V4 owner.
//!
//! The owner, its executable snapshot pin and cwd pins are C only
//! (`src/runtime/runtime_process_owned.c`, compiled into the seed runtime by
//! `runtime/build.rs`). This module owns no process authority: it converts
//! interpreter values to runtime values, calls the C entry point, decodes the
//! result, and frees every runtime array it received. Only macOS routes here;
//! every other host keeps the explicit interpreter refusal in `system.rs`.
#![cfg(target_os = "macos")]

use crate::error::CompileError;
use crate::runtime_bridge::runtime_to_value;
use crate::value::Value;
use simple_runtime::value::{
    rt_array_free, rt_array_get, rt_array_len, rt_array_new, rt_array_push, HeapHeader, HeapObjectType,
};
use simple_runtime::RuntimeValue;

unsafe extern "C" {
    fn rt_process_observation_v4_capabilities_value() -> RuntimeValue;
    fn rt_process_observation_v4_pin_cwd_value(path: *const u8, len: u64) -> i64;
    fn rt_process_observation_v4_cwd_digest_value(handle: i64) -> RuntimeValue;
    fn rt_process_observation_v4_close_cwd_value(handle: i64) -> i32;
    fn rt_process_pin_executable_owned_value(path: *const u8, len: u64) -> i64;
    fn rt_process_close_pinned_executable_owned_value(handle: i64) -> i32;
    fn rt_process_pinned_executable_sha256_value(handle: i64) -> RuntimeValue;
    fn rt_process_observation_v4_start_pinned_value(executable: i64, cwd: i64, binding: RuntimeValue) -> RuntimeValue;
    fn rt_process_observation_v4_poll_value(ticket: RuntimeValue, wait_ns: i64) -> RuntimeValue;
    fn rt_process_observation_v4_cancel_value(ticket: RuntimeValue, wait_ns: i64) -> RuntimeValue;
    fn rt_process_observation_v4_collect_value(ticket: RuntimeValue, wait_ns: i64) -> RuntimeValue;
    fn rt_process_observation_v4_ack_collect_value(ticket: RuntimeValue, digest: RuntimeValue) -> RuntimeValue;
}

fn is_array(rv: RuntimeValue) -> bool {
    if !rv.is_heap() {
        return false;
    }
    let ptr = rv.as_heap_ptr();
    // SAFETY: a non-null heap runtime value starts with a HeapHeader.
    !ptr.is_null() && unsafe { (*ptr.cast::<HeapHeader>()).object_type == HeapObjectType::Array }
}

/// Frees an owner result: an array whose elements are integers or arrays of
/// integers (the V4 tuple is four arrays). The C owner builds every result
/// array fresh and never aliases an input (ticket, digest, binding), so each
/// nested array is uniquely owned here.
fn free_owned(rv: RuntimeValue) {
    if !is_array(rv) {
        return;
    }
    let len = rt_array_len(rv);
    for i in 0..len.max(0) {
        let item = rt_array_get(rv, i);
        if is_array(item) {
            free_owned(item);
        }
    }
    rt_array_free(rv);
}

/// Decodes and releases a C result; NULL becomes an explicit error.
fn take(rv: RuntimeValue, symbol: &str) -> Result<Value, CompileError> {
    if rv.is_nil() || rv.to_raw() == 0 {
        return Err(CompileError::runtime(format!(
            "{symbol}: native owner returned no receipt"
        )));
    }
    let value = runtime_to_value(rv);
    free_owned(rv);
    Ok(value)
}

fn int_arg(args: &[Value], index: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be an integer"
        ))),
    }
}

fn text_arg<'a>(args: &'a [Value], symbol: &str) -> Result<&'a str, CompileError> {
    match args.first() {
        Some(Value::Str(text)) => Ok(text.as_str()),
        _ => Err(CompileError::runtime(format!("{symbol}: argument 0 must be text"))),
    }
}

/// Integer elements of an `[i64]` / `[u8]` argument. The interpreter carries
/// `u8` elements as `Value::UInt`; the C owner reads plain runtime integers.
fn int_elements(value: &Value) -> Option<Vec<i64>> {
    match value {
        Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => Some(bytes.iter().map(|b| *b as i64).collect()),
        Value::Array(items) | Value::FrozenArray(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(v) => Some(*v),
                Value::UInt { value, .. } if *value <= i64::MAX as u64 => Some(*value as i64),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Marshals an integer-array argument, calls `f`, and frees the marshalled copy.
fn with_array<T>(
    args: &[Value],
    index: usize,
    symbol: &str,
    f: impl FnOnce(RuntimeValue) -> T,
) -> Result<T, CompileError> {
    let items = args
        .get(index)
        .and_then(int_elements)
        .ok_or_else(|| CompileError::runtime(format!("{symbol}: argument {index} must be an integer array")))?;
    let rv = rt_array_new(items.len() as u64);
    if rv.is_nil() {
        return Err(CompileError::runtime(format!(
            "{symbol}: cannot allocate argument {index}"
        )));
    }
    for item in items {
        if !rt_array_push(rv, RuntimeValue::from_int(item)) {
            free_owned(rv);
            return Err(CompileError::runtime(format!(
                "{symbol}: cannot marshal argument {index}"
            )));
        }
    }
    let out = f(rv);
    free_owned(rv);
    Ok(out)
}

pub fn capabilities(_args: &[Value]) -> Result<Value, CompileError> {
    take(
        unsafe { rt_process_observation_v4_capabilities_value() },
        "rt_process_observation_v4_capabilities_value",
    )
}

pub fn pin_cwd(args: &[Value]) -> Result<Value, CompileError> {
    let path = text_arg(args, "rt_process_observation_v4_pin_cwd_value")?;
    Ok(Value::Int(unsafe {
        rt_process_observation_v4_pin_cwd_value(path.as_ptr(), path.len() as u64)
    }))
}

pub fn cwd_digest(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_process_observation_v4_cwd_digest_value")?;
    take(
        unsafe { rt_process_observation_v4_cwd_digest_value(handle) },
        "rt_process_observation_v4_cwd_digest_value",
    )
}

pub fn close_cwd(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_process_observation_v4_close_cwd_value")?;
    Ok(Value::Int(
        unsafe { rt_process_observation_v4_close_cwd_value(handle) } as i64
    ))
}

pub fn pin_executable(args: &[Value]) -> Result<Value, CompileError> {
    let path = text_arg(args, "rt_process_pin_executable_owned_value")?;
    Ok(Value::Int(unsafe {
        rt_process_pin_executable_owned_value(path.as_ptr(), path.len() as u64)
    }))
}

pub fn close_executable(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_process_close_pinned_executable_owned_value")?;
    Ok(Value::Int(
        unsafe { rt_process_close_pinned_executable_owned_value(handle) } as i64,
    ))
}

pub fn executable_digest(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_process_pinned_executable_sha256_value")?;
    let rv = unsafe { rt_process_pinned_executable_sha256_value(handle) };
    // NULL is the C "no pin / stale pin" answer; the facade expects nil.
    if rv.is_nil() || rv.to_raw() == 0 {
        return Ok(Value::Nil);
    }
    take(rv, "rt_process_pinned_executable_sha256_value")
}

pub fn start_pinned(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_process_observation_v4_start_pinned_value";
    let executable = int_arg(args, 0, NAME)?;
    let cwd = int_arg(args, 1, NAME)?;
    let rv = with_array(args, 2, NAME, |binding| unsafe {
        rt_process_observation_v4_start_pinned_value(executable, cwd, binding)
    })?;
    take(rv, NAME)
}

fn ticket_call(
    args: &[Value],
    name: &str,
    call: unsafe extern "C" fn(RuntimeValue, i64) -> RuntimeValue,
) -> Result<Value, CompileError> {
    let wait_ns = int_arg(args, 1, name)?;
    let rv = with_array(args, 0, name, |ticket| unsafe { call(ticket, wait_ns) })?;
    take(rv, name)
}

pub fn poll(args: &[Value]) -> Result<Value, CompileError> {
    ticket_call(
        args,
        "rt_process_observation_v4_poll_value",
        rt_process_observation_v4_poll_value,
    )
}

pub fn cancel(args: &[Value]) -> Result<Value, CompileError> {
    ticket_call(
        args,
        "rt_process_observation_v4_cancel_value",
        rt_process_observation_v4_cancel_value,
    )
}

pub fn collect(args: &[Value]) -> Result<Value, CompileError> {
    ticket_call(
        args,
        "rt_process_observation_v4_collect_value",
        rt_process_observation_v4_collect_value,
    )
}

pub fn ack_collect(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_process_observation_v4_ack_collect_value";
    let rv = with_array(args, 0, NAME, |ticket| {
        with_array(args, 1, NAME, |digest| unsafe {
            rt_process_observation_v4_ack_collect_value(ticket, digest)
        })
    })??;
    take(rv, NAME)
}
