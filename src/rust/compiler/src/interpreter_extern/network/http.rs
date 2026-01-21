//! HTTP network operations
//!
//! Native HTTP operations for the Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_net).

use crate::error::CompileError;
use crate::value::Value;
use super::super::super::interpreter_native_net::*;

/// Send HTTP request
///
/// Callable from Simple as: `native_http_send(request)`
///
/// # Arguments
/// * `args` - Evaluated arguments [request_data]
///
/// # Returns
/// * HTTP response data
///
/// # Effect
/// * Requires network HTTP effect
pub fn native_http_send(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_http_send")?;
    native_http_send_interp(args)
}
