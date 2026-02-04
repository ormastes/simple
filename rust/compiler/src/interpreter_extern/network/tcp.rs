//! TCP network operations
//!
//! Native TCP socket operations for the Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_net).

use crate::error::CompileError;
use crate::value::Value;
use super::super::super::interpreter_native_net::*;

/// Bind TCP listener to address
///
/// # Effect
/// * Requires network bind effect
pub fn native_tcp_bind(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_bind")?;
    native_tcp_bind_interp(args)
}

/// Accept incoming TCP connection
///
/// # Effect
/// * Requires network accept effect
pub fn native_tcp_accept(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_accept")?;
    native_tcp_accept_interp(args)
}

/// Connect to TCP server
///
/// # Effect
/// * Requires network connect effect
pub fn native_tcp_connect(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_connect")?;
    native_tcp_connect_interp(args)
}

/// Connect to TCP server with timeout
///
/// # Effect
/// * Requires network connect effect
pub fn native_tcp_connect_timeout(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_connect_timeout")?;
    native_tcp_connect_timeout_interp(args)
}

/// Read from TCP stream
///
/// # Effect
/// * Requires network read effect
pub fn native_tcp_read(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_read")?;
    native_tcp_read_interp(args)
}

/// Write to TCP stream
///
/// # Effect
/// * Requires network write effect
pub fn native_tcp_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_write")?;
    native_tcp_write_interp(args)
}

/// Flush TCP stream
///
/// # Effect
/// * Requires network write effect
pub fn native_tcp_flush(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_flush")?;
    native_tcp_flush_interp(args)
}

/// Shutdown TCP connection
///
/// # Effect
/// * Requires network shutdown effect
pub fn native_tcp_shutdown(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_shutdown")?;
    native_tcp_shutdown_interp(args)
}

/// Close TCP connection
///
/// # Effect
/// * Requires network close effect
pub fn native_tcp_close(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_close")?;
    native_tcp_close_interp(args)
}

/// Set TCP_NODELAY option
///
/// No effect check - configuration operation
pub fn native_tcp_set_nodelay(args: &[Value]) -> Result<Value, CompileError> {
    native_tcp_set_nodelay_interp(args)
}

/// Set TCP keepalive
///
/// No effect check - configuration operation
/// Currently a stub (returns Nil)
pub fn native_tcp_set_keepalive(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil) // Stub for now
}

/// Set TCP read timeout
///
/// No effect check - configuration operation
pub fn native_tcp_set_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    native_tcp_set_read_timeout_interp(args)
}

/// Set TCP write timeout
///
/// No effect check - configuration operation
pub fn native_tcp_set_write_timeout(args: &[Value]) -> Result<Value, CompileError> {
    native_tcp_set_write_timeout_interp(args)
}

/// Get TCP_NODELAY option
///
/// No effect check - query operation
pub fn native_tcp_get_nodelay(args: &[Value]) -> Result<Value, CompileError> {
    native_tcp_get_nodelay_interp(args)
}

/// Peek at TCP stream data without consuming
///
/// # Effect
/// * Requires network read effect
pub fn native_tcp_peek(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_tcp_peek")?;
    native_tcp_peek_interp(args)
}

/// Set TCP listener backlog
///
/// No effect check - configuration operation
/// Currently a no-op (backlog set at bind time)
pub fn native_tcp_set_backlog(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil) // No-op, backlog set at bind time
}
