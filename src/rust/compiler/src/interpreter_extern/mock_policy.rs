//! Mock policy FFI for the Simple interpreter
//!
//! This module provides FFI wrappers for mock policy functions from simple_mock_helper.
//! These allow Simple code to configure and check mock policies at runtime.

use crate::error::CompileError;
use crate::value::Value;

/// Initialize mock policy to allow all mocks (unit test mode).
///
/// Callable from Simple as: `__mock_policy_init_all()`
pub fn mock_policy_init_all(_args: &[Value]) -> Result<Value, CompileError> {
    simple_mock_helper::mock_policy::init_mocks_for_only(&["*"]);
    Ok(Value::Nil)
}

/// Initialize mock policy to HAL-only (integration test mode).
///
/// Callable from Simple as: `__mock_policy_init_hal_only()`
pub fn mock_policy_init_hal_only(_args: &[Value]) -> Result<Value, CompileError> {
    simple_mock_helper::mock_policy::init_mocks_for_only_default();
    Ok(Value::Nil)
}

/// Disable all mocks (system test mode).
///
/// Callable from Simple as: `__mock_policy_disable()`
pub fn mock_policy_disable(_args: &[Value]) -> Result<Value, CompileError> {
    simple_mock_helper::mock_policy::init_mocks_for_system();
    Ok(Value::Nil)
}

/// Initialize mock policy with custom patterns.
///
/// Callable from Simple as: `__mock_policy_init_patterns(patterns)`
/// where `patterns` is an array of strings.
pub fn mock_policy_init_patterns(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "__mock_policy_init_patterns requires 1 argument (array of patterns)",
        ));
    }

    match &args[0] {
        Value::Array(patterns) => {
            // Collect patterns as strings
            let pattern_strings: Vec<String> = patterns
                .iter()
                .filter_map(|v| {
                    if let Value::Str(s) = v {
                        Some(s.clone())
                    } else {
                        None
                    }
                })
                .collect();

            // Convert to 'static refs by leaking (this is fine for test setup)
            let static_patterns: Vec<&'static str> = pattern_strings
                .into_iter()
                .map(|s| Box::leak(s.into_boxed_str()) as &'static str)
                .collect();

            let static_slice: &'static [&'static str] = Box::leak(static_patterns.into_boxed_slice());
            simple_mock_helper::mock_policy::init_mocks_for_only(static_slice);
            Ok(Value::Nil)
        }
        _ => Err(CompileError::runtime(
            "__mock_policy_init_patterns: patterns must be an array of strings",
        )),
    }
}

/// Check if mock usage is allowed from a given module path.
/// Panics if not allowed.
///
/// Callable from Simple as: `__mock_policy_check(module_path)`
pub fn mock_policy_check(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "__mock_policy_check requires 1 argument (module_path)",
        ));
    }

    let module_path = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "__mock_policy_check: module_path must be a string",
            ))
        }
    };

    simple_mock_helper::mock_policy::check_mock_use_from(&module_path);
    Ok(Value::Nil)
}

/// Check if mock usage is allowed from a given module path (non-panicking).
/// Returns "allowed", "disabled", "not_initialized", or "not_allowed".
///
/// Callable from Simple as: `__mock_policy_try_check(module_path)`
pub fn mock_policy_try_check(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "__mock_policy_try_check requires 1 argument (module_path)",
        ));
    }

    let module_path = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "__mock_policy_try_check: module_path must be a string",
            ))
        }
    };

    use simple_mock_helper::mock_policy::{try_check_mock_use_from, MockCheckResult};

    let result = try_check_mock_use_from(&module_path);
    let result_str = match result {
        MockCheckResult::Allowed => "allowed",
        MockCheckResult::MocksDisabled => "disabled",
        MockCheckResult::NotInitialized => "not_initialized",
        MockCheckResult::NotAllowed { .. } => "not_allowed",
    };

    Ok(Value::Str(result_str.to_string()))
}

/// Get the current mock policy mode.
/// Returns "all", "hal_only", "disabled", or "custom".
///
/// Callable from Simple as: `__mock_policy_get_mode()`
pub fn mock_policy_get_mode(_args: &[Value]) -> Result<Value, CompileError> {
    // Check if we can use mocks by trying with a wildcard path
    use simple_mock_helper::mock_policy::{try_check_mock_use_from, MockCheckResult};

    let result = try_check_mock_use_from("*");

    let mode = match result {
        MockCheckResult::NotInitialized => "not_initialized",
        MockCheckResult::MocksDisabled => "disabled",
        MockCheckResult::Allowed => "all", // Wildcard allowed means "all" mode
        MockCheckResult::NotAllowed { .. } => "custom", // Wildcard not allowed means restricted
    };

    Ok(Value::Str(mode.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mock_policy_init_all() {
        let result = mock_policy_init_all(&[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_mock_policy_get_mode() {
        // Initialize to all
        mock_policy_init_all(&[]).unwrap();
        let mode = mock_policy_get_mode(&[]).unwrap();
        assert!(matches!(mode, Value::Str(s) if s == "all"));
    }
}
