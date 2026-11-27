//! Interpreter marshalling for the owned-process V3 opaque adapter.
//!
//! The adapter (opaque handle -> private core token) is C only
//! (`src/runtime/runtime_process_owned.c`, compiled into the seed runtime by
//! `runtime/build.rs`): the POSIX owner on Linux/FreeBSD/macOS and the Win32
//! owner on Windows. This module owns no process authority. It converts
//! interpreter values into runtime values, calls the C entry point, decodes
//! the receipt, and frees every runtime value it allocated or received.
//! Hosts without a native owner get the C ENOTSUP receipt, which the Simple
//! facade (`process_ops.spl`) reports as "start rejected: runtime error N".

use crate::error::CompileError;
use crate::runtime_bridge::runtime_to_value;
use crate::value::Value;
use simple_runtime::value::{
    rt_array_free, rt_array_get, rt_array_len, rt_array_new, rt_array_push, rt_string_new, HeapHeader,
    HeapObjectType,
};
use simple_runtime::RuntimeValue;

unsafe extern "C" {
    fn rt_process_owned_v3_start_value(
        command: *const u8,
        command_len: u64,
        args: RuntimeValue,
        input: RuntimeValue,
        timeout_ms: i64,
        term_grace_ms: i64,
        max_output_bytes: i64,
    ) -> RuntimeValue;
    fn rt_process_owned_v3_poll_value(handle: i64, wait_ms: i64, stdout_cap: i64, stderr_cap: i64) -> RuntimeValue;
    fn rt_process_owned_v3_input_value(handle: i64) -> RuntimeValue;
    fn rt_process_owned_v3_cancel_value(handle: i64) -> RuntimeValue;
    fn rt_process_owned_v3_result_value(handle: i64) -> RuntimeValue;
    fn rt_process_owned_v3_collect_value(handle: i64) -> RuntimeValue;
    fn rt_process_owned_v3_release_value(handle: i64) -> bool;
}

fn heap_type(rv: RuntimeValue) -> Option<HeapObjectType> {
    if !rv.is_heap() {
        return None;
    }
    let ptr = rv.as_heap_ptr();
    if ptr.is_null() {
        return None;
    }
    // SAFETY: a non-null heap runtime value starts with a HeapHeader.
    Some(unsafe { (*ptr.cast::<HeapHeader>()).object_type })
}

/// Frees a C receipt: an int array, or the poll tuple of three int arrays.
/// The C adapter builds every result fresh and never aliases an input.
fn free_owned(rv: RuntimeValue) {
    if heap_type(rv) != Some(HeapObjectType::Array) {
        return;
    }
    let len = rt_array_len(rv);
    for i in 0..len.max(0) {
        let item = rt_array_get(rv, i);
        if heap_type(item) == Some(HeapObjectType::Array) {
            free_owned(item);
        }
    }
    rt_array_free(rv);
}

fn take(rv: RuntimeValue, symbol: &str) -> Result<Value, CompileError> {
    if rv.is_nil() || rv.to_raw() == 0 {
        return Err(CompileError::runtime(format!("{symbol}: native owner returned no receipt")));
    }
    let value = runtime_to_value(rv);
    free_owned(rv);
    Ok(value)
}

fn int_arg(args: &[Value], index: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!("{symbol}: argument {index} must be an integer"))),
    }
}

/// Owns marshalled runtime values and frees them on drop (strings included).
struct Marshalled(Vec<RuntimeValue>);

impl Drop for Marshalled {
    fn drop(&mut self) {
        for rv in self.0.drain(..).rev() {
            match heap_type(rv) {
                Some(HeapObjectType::Array) => {
                    let _ = rt_array_free(rv);
                }
                Some(_) => {
                    let _ = simple_runtime::value::rt_string_free(rv);
                }
                None => {}
            }
        }
    }
}

fn byte_elements(value: &Value) -> Option<Vec<i64>> {
    match value {
        Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => Some(bytes.iter().map(|b| *b as i64).collect()),
        Value::Array(items) | Value::FrozenArray(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(v) if (0..=255).contains(v) => Some(*v),
                Value::UInt { value, .. } if *value <= 255 => Some(*value as i64),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

pub fn start(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_process_owned_v3_start_value";
    let command = match args.first() {
        Some(Value::Str(text)) => text.as_str().to_owned(),
        _ => return Err(CompileError::runtime(format!("{NAME}: argument 0 must be text"))),
    };
    let argv: Vec<String> = match args.get(1) {
        Some(Value::Array(items)) | Some(Value::FrozenArray(items)) => items
            .iter()
            .map(|item| match item {
                Value::Str(text) => Ok(text.as_str().to_owned()),
                _ => Err(CompileError::runtime(format!("{NAME}: argument 1 must be [text]"))),
            })
            .collect::<Result<_, _>>()?,
        _ => return Err(CompileError::runtime(format!("{NAME}: argument 1 must be [text]"))),
    };
    let input = args
        .get(2)
        .and_then(byte_elements)
        .ok_or_else(|| CompileError::runtime(format!("{NAME}: argument 2 must be [u8]")))?;
    let timeout_ms = int_arg(args, 3, NAME)?;
    let term_grace_ms = int_arg(args, 4, NAME)?;
    let max_output_bytes = int_arg(args, 5, NAME)?;

    let mut owned = Marshalled(Vec::new());
    let alloc_err = || CompileError::runtime(format!("{NAME}: cannot marshal arguments"));
    let args_rv = rt_array_new(argv.len() as u64);
    if args_rv.is_nil() {
        return Err(alloc_err());
    }
    owned.0.push(args_rv);
    for arg in &argv {
        let s = rt_string_new(arg.as_ptr(), arg.len() as u64);
        if s.is_nil() {
            return Err(alloc_err());
        }
        owned.0.push(s);
        if !rt_array_push(args_rv, s) {
            return Err(alloc_err());
        }
    }
    let input_rv = rt_array_new(input.len() as u64);
    if input_rv.is_nil() {
        return Err(alloc_err());
    }
    owned.0.push(input_rv);
    for byte in input {
        if !rt_array_push(input_rv, RuntimeValue::from_int(byte)) {
            return Err(alloc_err());
        }
    }
    // SAFETY: command bytes stay alive for the call; the C adapter copies
    // every argument and never retains or frees caller-owned values.
    let rv = unsafe {
        rt_process_owned_v3_start_value(
            command.as_ptr(),
            command.len() as u64,
            args_rv,
            input_rv,
            timeout_ms,
            term_grace_ms,
            max_output_bytes,
        )
    };
    let result = take(rv, NAME);
    drop(owned);
    result
}

pub fn poll(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_process_owned_v3_poll_value";
    let handle = int_arg(args, 0, NAME)?;
    let wait_ms = int_arg(args, 1, NAME)?;
    let out_cap = int_arg(args, 2, NAME)?;
    let err_cap = int_arg(args, 3, NAME)?;
    let value = take(unsafe { rt_process_owned_v3_poll_value(handle, wait_ms, out_cap, err_cap) }, NAME)?;
    // The Simple signature is a 3-tuple `([u8], [u8], [i64])`.
    match value {
        Value::Array(items) if items.len() == 3 => Ok(Value::Tuple(items.iter().cloned().collect())),
        other => Ok(other),
    }
}

fn handle_call(args: &[Value], name: &str, call: unsafe extern "C" fn(i64) -> RuntimeValue) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, name)?;
    take(unsafe { call(handle) }, name)
}

pub fn input(args: &[Value]) -> Result<Value, CompileError> {
    handle_call(args, "rt_process_owned_v3_input_value", rt_process_owned_v3_input_value)
}

pub fn cancel(args: &[Value]) -> Result<Value, CompileError> {
    handle_call(args, "rt_process_owned_v3_cancel_value", rt_process_owned_v3_cancel_value)
}

pub fn result(args: &[Value]) -> Result<Value, CompileError> {
    handle_call(args, "rt_process_owned_v3_result_value", rt_process_owned_v3_result_value)
}

pub fn collect(args: &[Value]) -> Result<Value, CompileError> {
    handle_call(args, "rt_process_owned_v3_collect_value", rt_process_owned_v3_collect_value)
}

pub fn release(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_process_owned_v3_release_value")?;
    Ok(Value::Bool(unsafe { rt_process_owned_v3_release_value(handle) }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(value: &Value) -> Vec<i64> {
        match value {
            Value::Array(items) => items
                .iter()
                .map(|v| match v {
                    Value::Int(i) => *i,
                    Value::UInt { value, .. } => *value as i64,
                    other => panic!("non-int receipt word {other:?}"),
                })
                .collect(),
            other => panic!("expected int array, got {other:?}"),
        }
    }

    /// Regression: the interpreter used to refuse every V3 entry, so
    /// `OwnedProcessLease.start` (traceability `--snapshot=git:HEAD`) failed
    /// with "invalid 4-word receipt". A real child must start, stream stdout,
    /// and be collected through the opaque handle.
    #[test]
    fn owned_v3_round_trip_runs_a_real_child() {
        let start_value = start(&[
            Value::text("git"),
            Value::array(vec![Value::text("--version")]),
            Value::array(Vec::<Value>::new()),
            Value::Int(30_000),
            Value::Int(1_000),
            Value::Int(65_536),
        ])
        .expect("start receipt");
        let words = ints(&start_value);
        assert_eq!(words.len(), 4, "start receipt must have 4 words: {words:?}");
        assert_eq!(words[1], 1, "receipt version");
        assert_eq!(words[2], 1, "start must be accepted: {words:?}");
        let handle = words[0];
        assert!(handle > 0);

        let mut stdout = Vec::new();
        for _ in 0..600 {
            let polled = poll(&[Value::Int(handle), Value::Int(50), Value::Int(4096), Value::Int(4096)]).expect("poll");
            let Value::Tuple(parts) = polled else { panic!("poll must return a tuple") };
            stdout.extend(ints(&parts[0]).into_iter().map(|b| b as u8));
            let fields = ints(&parts[2]);
            assert_eq!(fields.len(), 17);
            if fields[2] != 0 && fields[14] == 0 && fields[15] == 0 {
                break;
            }
        }
        let collected = ints(&collect(&[Value::Int(handle)]).expect("collect"));
        assert_eq!(collected.len(), 15);
        assert_eq!(collected[1], 0, "git --version exit code: {collected:?}");
        assert_eq!(collected[7], 1, "child must be reaped");
        assert!(String::from_utf8_lossy(&stdout).contains("git version"));
        // Prevention: a consumed handle is stale, never resurrected.
        let stale = ints(&result(&[Value::Int(handle)]).expect("stale result"));
        assert_ne!(stale[14], 0, "collected handle must be stale");
        assert_eq!(release(&[Value::Int(handle)]).expect("release"), Value::Bool(false));
    }

    #[test]
    fn owned_v3_rejects_forged_handle() {
        let fields = ints(&cancel(&[Value::Int(12345)]).expect("cancel"));
        assert_eq!(fields.len(), 4);
        assert_eq!(fields[1], 0, "forged handle must not be accepted");
        assert_ne!(fields[3], 0);
    }
}
