//! I18n (Internationalization) extern functions
//!
//! Provides FFI bindings to the i18n system for Simple code.
//! Note: The Rust i18n crate has been removed. These functions now use
//! a simple HashMap-based context and return messages as-is (no localization).

use crate::error::CompileError;
use crate::value::{Env, Value};
use std::collections::HashMap;

/// Simple replacement for MessageContext (previously from simple_i18n crate)
struct MessageContext {
    values: HashMap<String, String>,
}

impl MessageContext {
    fn new() -> Self {
        Self { values: HashMap::new() }
    }

    fn insert(&mut self, key: &str, value: &str) {
        self.values.insert(key.to_string(), value.to_string());
    }
}

/// Create a new empty message context
///
/// Returns an opaque handle (Box pointer as i64) to a MessageContext.
pub fn rt_i18n_context_new(env: &mut Env) -> Result<Value, CompileError> {
    let ctx = Box::new(MessageContext::new());
    let handle = Box::into_raw(ctx) as i64;
    Ok(Value::Int(handle))
}

/// Insert a key-value pair into a message context
///
/// Arguments:
/// - handle: i64 - Opaque pointer to MessageContext
/// - key: String - Context key
/// - value: String - Context value
pub fn rt_i18n_context_insert(
    args: &[Value],
    _env: &mut Env,
) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_i18n_context_insert: expected 3 arguments (handle, key, value)".to_string(),
        ));
    }

    let handle = match &args[0] {
        Value::Int(h) => *h,
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_context_insert: first argument must be an Int (handle)".to_string(),
            ))
        }
    };

    let key = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_context_insert: second argument must be a String (key)".to_string(),
            ))
        }
    };

    let value = match &args[2] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_context_insert: third argument must be a String (value)".to_string(),
            ))
        }
    };

    // Safety: The handle must be a valid MessageContext pointer created by rt_i18n_context_new
    unsafe {
        let ctx = &mut *(handle as *mut MessageContext);
        ctx.insert(&key, &value);
    }

    Ok(Value::Nil)
}

/// Free a message context
///
/// Arguments:
/// - handle: i64 - Opaque pointer to MessageContext
pub fn rt_i18n_context_free(args: &[Value], _env: &mut Env) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_i18n_context_free: expected 1 argument (handle)".to_string(),
        ));
    }

    let handle = match &args[0] {
        Value::Int(h) => *h,
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_context_free: argument must be an Int (handle)".to_string(),
            ))
        }
    };

    // Safety: The handle must be a valid MessageContext pointer
    unsafe {
        let _ = Box::from_raw(handle as *mut MessageContext);
        // MessageContext is dropped here
    }

    Ok(Value::Nil)
}

/// Get a localized message by domain and ID
///
/// Arguments:
/// - domain: String - Message domain (e.g., "parser", "compiler")
/// - id: String - Message ID (e.g., "E0001")
/// - ctx_handle: i64 - Opaque pointer to MessageContext
///
/// Returns the message ID as-is (no localization after i18n crate removal).
pub fn rt_i18n_get_message(
    args: &[Value],
    _env: &mut Env,
) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_i18n_get_message: expected 3 arguments (domain, id, ctx_handle)".to_string(),
        ));
    }

    let domain = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_get_message: first argument must be a String (domain)".to_string(),
            ))
        }
    };

    let id = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_get_message: second argument must be a String (id)".to_string(),
            ))
        }
    };

    // Return the message ID as the message (no i18n lookup)
    Ok(Value::Str(format!("{}.{}", domain, id)))
}

/// Get a localized severity name
///
/// Arguments:
/// - severity: String - Severity level ("error", "warning", "note", "help", "info")
///
/// Returns the severity name as-is (no localization after i18n crate removal).
pub fn rt_i18n_severity_name(args: &[Value], _env: &mut Env) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_i18n_severity_name: expected 1 argument (severity)".to_string(),
        ));
    }

    let severity = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_i18n_severity_name: argument must be a String".to_string(),
            ))
        }
    };

    Ok(Value::Str(severity))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i18n_context_creation() {
        let mut env = Env::new();

        // Create a new context
        let result = rt_i18n_context_new(&mut env);
        assert!(result.is_ok());

        if let Ok(Value::Int(handle)) = result {
            // Insert a key-value pair
            let args = vec![
                Value::Int(handle),
                Value::Str("test".to_string()),
                Value::Str("value".to_string()),
            ];
            let insert_result = rt_i18n_context_insert(&args, &mut env);
            assert!(insert_result.is_ok());

            // Free the context
            let free_args = vec![Value::Int(handle)];
            let free_result = rt_i18n_context_free(&free_args, &mut env);
            assert!(free_result.is_ok());
        }
    }

    #[test]
    fn test_severity_name() {
        let mut env = Env::new();

        let args = vec![Value::Str("error".to_string())];
        let result = rt_i18n_severity_name(&args, &mut env);

        assert!(result.is_ok());
        if let Ok(Value::Str(s)) = result {
            assert_eq!(s, "error");
        }
    }
}
