//! Span interop SFFI
//!
//! Provides SFFI functions for creating and accessing Span values
//! that bridge between Simple code and the Rust compiler's span types.

use crate::value::Value;
use crate::error::CompileError;

use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    static SPAN_REGISTRY: RefCell<HashMap<i64, simple_parser::token::Span>> = RefCell::new(HashMap::new());
    static NEXT_SPAN_HANDLE: RefCell<i64> = const { RefCell::new(1) };
}

fn next_handle() -> Result<i64, CompileError> {
    NEXT_SPAN_HANDLE.with(|h| {
        let mut handle = h.borrow_mut();
        let id = *handle;
        *handle = id
            .checked_add(1)
            .ok_or_else(|| CompileError::runtime("rt_span_create: handle space exhausted"))?;
        Ok(id)
    })
}

#[inline(always)]
fn require_arity(args: &[Value], expected: usize, name: &str) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::runtime(format!("{name}: expected {expected} arguments")));
    }
    Ok(())
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
    require_arity(args, 4, "rt_span_create")?;
    let start = usize::try_from(get_i64(args, 0, "rt_span_create")?)
        .map_err(|_| CompileError::runtime("rt_span_create: start is outside usize range"))?;
    let end = usize::try_from(get_i64(args, 1, "rt_span_create")?)
        .map_err(|_| CompileError::runtime("rt_span_create: end is outside usize range"))?;
    let line = usize::try_from(get_i64(args, 2, "rt_span_create")?)
        .map_err(|_| CompileError::runtime("rt_span_create: line is outside usize range"))?;
    let column = usize::try_from(get_i64(args, 3, "rt_span_create")?)
        .map_err(|_| CompileError::runtime("rt_span_create: column is outside usize range"))?;
    if end < start {
        return Err(CompileError::runtime("rt_span_create: end must not precede start"));
    }

    let span = simple_parser::token::Span::new(start, end, line, column);
    let handle = next_handle()?;

    SPAN_REGISTRY.with(|r| r.borrow_mut().insert(handle, span));
    Ok(Value::Int(handle))
}

/// rt_span_start(handle) -> i64
pub fn rt_span_start(args: &[Value]) -> Result<Value, CompileError> {
    require_arity(args, 1, "rt_span_start")?;
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
    require_arity(args, 1, "rt_span_end")?;
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
    require_arity(args, 1, "rt_span_line")?;
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
    require_arity(args, 1, "rt_span_column")?;
    let handle = get_i64(args, 0, "rt_span_column")?;
    SPAN_REGISTRY.with(|r| {
        let reg = r.borrow();
        let span = reg
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("rt_span_column: invalid handle {}", handle)))?;
        Ok(Value::Int(span.column as i64))
    })
}

/// Clear the span SFFI registry between test runs.
pub fn clear_span_sffi_registry() {
    SPAN_REGISTRY.with(|r| r.borrow_mut().clear());
}

/// rt_span_free(handle)
pub fn rt_span_free(args: &[Value]) -> Result<Value, CompileError> {
    require_arity(args, 1, "rt_span_free")?;
    let handle = get_i64(args, 0, "rt_span_free")?;
    let removed = SPAN_REGISTRY.with(|r| r.borrow_mut().remove(&handle));
    if removed.is_none() {
        return Err(CompileError::runtime(format!(
            "rt_span_free: invalid or already freed handle {handle}"
        )));
    }
    Ok(Value::Nil)
}

#[cfg(test)]
mod contract_tests {
    use super::*;

    #[test]
    fn span_transport_rejects_invalid_ranges_and_double_free() {
        clear_span_sffi_registry();
        assert!(rt_span_create(&[Value::Int(-1), Value::Int(1), Value::Int(1), Value::Int(1),]).is_err());
        assert!(rt_span_create(&[Value::Int(2), Value::Int(1), Value::Int(1), Value::Int(1),]).is_err());
        let handle = rt_span_create(&[Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4)])
            .unwrap()
            .as_int()
            .unwrap();
        assert!(rt_span_start(&[Value::Int(handle), Value::Int(0)]).is_err());
        assert!(rt_span_free(&[Value::Int(handle)]).is_ok());
        assert!(rt_span_free(&[Value::Int(handle)]).is_err());
    }
}
