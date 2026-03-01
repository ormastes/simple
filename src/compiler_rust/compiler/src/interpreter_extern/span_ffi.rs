//! Span interop FFI
//!
//! Provides FFI functions for creating and accessing Span values
//! that bridge between Simple code and the Rust compiler's span types.

use crate::value::Value;
use crate::error::CompileError;

use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    static SPAN_REGISTRY: RefCell<HashMap<i64, simple_parser::token::Span>> = RefCell::new(HashMap::new());
    static NEXT_SPAN_HANDLE: RefCell<i64> = RefCell::new(1);
}

fn next_handle() -> i64 {
    NEXT_SPAN_HANDLE.with(|h| {
        let mut handle = h.borrow_mut();
        let id = *handle;
        *handle += 1;
        id
    })
}

fn get_i64(args: &[Value], idx: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(CompileError::runtime(format!(
            "{}: expected integer argument at index {}",
            name, idx
        ))),
    }
}

/// rt_span_create(start, end, line, column) -> handle
pub fn rt_span_create(args: &[Value]) -> Result<Value, CompileError> {
    let start = get_i64(args, 0, "rt_span_create")? as usize;
    let end = get_i64(args, 1, "rt_span_create")? as usize;
    let line = get_i64(args, 2, "rt_span_create")? as usize;
    let column = get_i64(args, 3, "rt_span_create")? as usize;

    let span = simple_parser::token::Span::new(start, end, line, column);
    let handle = next_handle();

    SPAN_REGISTRY.with(|r| r.borrow_mut().insert(handle, span));
    Ok(Value::Int(handle))
}

/// rt_span_start(handle) -> i64
pub fn rt_span_start(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_i64(args, 0, "rt_span_start")?;
    SPAN_REGISTRY.with(|r| {
        let reg = r.borrow();
        let span = reg
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("rt_span_start: invalid handle {}", handle)))?;
        Ok(Value::Int(span.start as i64))
    })
}

/// rt_span_end(handle) -> i64
pub fn rt_span_end(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_i64(args, 0, "rt_span_end")?;
    SPAN_REGISTRY.with(|r| {
        let reg = r.borrow();
        let span = reg
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("rt_span_end: invalid handle {}", handle)))?;
        Ok(Value::Int(span.end as i64))
    })
}

/// rt_span_line(handle) -> i64
pub fn rt_span_line(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_i64(args, 0, "rt_span_line")?;
    SPAN_REGISTRY.with(|r| {
        let reg = r.borrow();
        let span = reg
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("rt_span_line: invalid handle {}", handle)))?;
        Ok(Value::Int(span.line as i64))
    })
}

/// rt_span_column(handle) -> i64
pub fn rt_span_column(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_i64(args, 0, "rt_span_column")?;
    SPAN_REGISTRY.with(|r| {
        let reg = r.borrow();
        let span = reg
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("rt_span_column: invalid handle {}", handle)))?;
        Ok(Value::Int(span.column as i64))
    })
}

/// Clear the span FFI registry between test runs.
pub fn clear_span_ffi_registry() {
    SPAN_REGISTRY.with(|r| r.borrow_mut().clear());
}

/// rt_span_free(handle)
pub fn rt_span_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_i64(args, 0, "rt_span_free")?;
    SPAN_REGISTRY.with(|r| r.borrow_mut().remove(&handle));
    Ok(Value::Nil)
}
