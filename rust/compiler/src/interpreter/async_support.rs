// Async/await support for futures and promises

use crate::error::CompileError;
use crate::value::Value;

/// Await a value if it's a Future or Promise.
/// For FutureValue: blocks until the future completes and returns the result.
/// For Promise objects: extracts the resolved value if already resolved.
/// For other values: returns as-is.
pub(crate) fn await_value(value: Value) -> Result<Value, CompileError> {
    match value {
        // Handle FutureValue - await the result
        Value::Future(ref future) => match future.await_result() {
            Ok(result) => Ok(result),
            Err(e) => Err(CompileError::Runtime(format!("await failed: {}", e))),
        },
        // Handle Promise objects (Simple-level Promise type)
        Value::Object { ref class, ref fields } if class == "Promise" => {
            // Check the state field
            if let Some(state) = fields.get("state") {
                match state {
                    Value::Enum { variant, payload, .. } => {
                        match variant.as_str() {
                            "Resolved" => {
                                // Extract the value from Resolved(value)
                                if let Some(inner) = payload {
                                    Ok(inner.as_ref().clone())
                                } else {
                                    Ok(Value::Nil)
                                }
                            }
                            "Rejected" => {
                                // Extract error message from Rejected(error)
                                if let Some(inner) = payload {
                                    Err(CompileError::Runtime(format!("Promise rejected: {:?}", inner)))
                                } else {
                                    Err(CompileError::Runtime("Promise rejected".to_string()))
                                }
                            }
                            "Pending" => {
                                // For pending promises, we can't block in the interpreter
                                // Return a pending indicator or error
                                Err(CompileError::Runtime(
                                    "Cannot await pending Promise in synchronous context".to_string(),
                                ))
                            }
                            _ => Ok(value),
                        }
                    }
                    _ => Ok(value),
                }
            } else {
                Ok(value)
            }
        }
        // Non-async values pass through unchanged
        _ => Ok(value),
    }
}
