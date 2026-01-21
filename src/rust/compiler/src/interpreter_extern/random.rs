//! Random number generation extern functions
//!
//! Provides random number generation with global state stored in the runtime.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

// Import runtime FFI random functions
use simple_runtime::value::ffi::random::{
    rt_random_seed, rt_random_getstate, rt_random_setstate,
    rt_random_next, rt_random_randint, rt_random_random, rt_random_uniform,
};

/// rt_random_seed - Set the random seed
pub fn rt_random_seed_fn(args: &[Value]) -> Result<Value, CompileError> {
    let seed = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_seed expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_int()?;
    rt_random_seed(seed);
    Ok(Value::Nil)
}

/// rt_random_getstate - Get current random state
pub fn rt_random_getstate_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_random_getstate()))
}

/// rt_random_setstate - Set random state
pub fn rt_random_setstate_fn(args: &[Value]) -> Result<Value, CompileError> {
    let state = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_setstate expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_int()?;
    rt_random_setstate(state);
    Ok(Value::Nil)
}

/// rt_random_next - Generate next random number
pub fn rt_random_next_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_random_next()))
}

/// rt_random_randint - Generate random integer in range
pub fn rt_random_randint_fn(args: &[Value]) -> Result<Value, CompileError> {
    let min = args.get(0).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_randint expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_int()?;
    let max = args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_randint expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_int()?;
    Ok(Value::Int(rt_random_randint(min, max)))
}

/// rt_random_random - Generate random float [0.0, 1.0)
pub fn rt_random_random_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Float(rt_random_random()))
}

/// rt_random_uniform - Generate random float in range
pub fn rt_random_uniform_fn(args: &[Value]) -> Result<Value, CompileError> {
    let min = args.get(0).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_uniform expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    let max = args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_random_uniform expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_random_uniform(min, max)))
}
