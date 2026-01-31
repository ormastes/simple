//! Layout profiling extern functions
//!
//! Functions for marking execution phases to optimize code layout
//! for 4KB page locality (used with --layout-record flag).

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

/// Record a layout marker for 4KB page locality optimization
///
/// Callable from Simple as: `simple_layout_mark("phase_name")`
///
/// When running with --layout-record, this tracks phase boundaries
/// (startup, first_frame, event_loop) for optimal code placement.
///
/// # Arguments
/// * `args` - Evaluated arguments [marker_name: String|Symbol]
///
/// # Returns
/// * Nil
pub fn simple_layout_mark(args: &[Value]) -> Result<Value, CompileError> {
    let val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("simple_layout_mark expects exactly 1 argument");
        CompileError::semantic_with_context("simple_layout_mark expects 1 argument".to_string(), ctx)
    })?;

    let marker_name = match val {
        Value::Str(s) => s.clone(),
        Value::Symbol(s) => s.clone(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("simple_layout_mark expects a string or symbol argument");
            return Err(CompileError::semantic_with_context(
                "simple_layout_mark expects a string argument".to_string(),
                ctx,
            ));
        }
    };

    // Record the marker if layout recording is enabled
    crate::layout_recorder::record_layout_marker(&marker_name);

    // In debug builds, log the marker for verification
    #[cfg(debug_assertions)]
    {
        tracing::debug!(marker = %marker_name, "layout marker reached");
    }

    Ok(Value::Nil)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_layout_mark_string() {
        let result = simple_layout_mark(&[Value::Str("startup".to_string())]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Value::Nil);
    }

    #[test]
    fn test_simple_layout_mark_symbol() {
        let result = simple_layout_mark(&[Value::Symbol("event_loop".to_string())]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Value::Nil);
    }

    #[test]
    fn test_simple_layout_mark_wrong_type() {
        let result = simple_layout_mark(&[Value::Int(42)]);
        assert!(result.is_err());
    }

    #[test]
    fn test_simple_layout_mark_no_args() {
        let result = simple_layout_mark(&[]);
        assert!(result.is_err());
    }
}
