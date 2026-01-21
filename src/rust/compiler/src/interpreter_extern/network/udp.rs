//! UDP network operations
//!
//! Native UDP socket operations for the Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_net).

use crate::error::CompileError;
use crate::value::Value;
use super::super::super::interpreter_native_net::*;

/// Bind UDP socket to address
///
/// # Effect
/// * Requires network bind effect
pub fn native_udp_bind(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_bind")?;
    native_udp_bind_interp(args)
}

/// Connect UDP socket to remote address
///
/// # Effect
/// * Requires network connect effect
pub fn native_udp_connect(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_connect")?;
    native_udp_connect_interp(args)
}

/// Receive data from any address
///
/// # Effect
/// * Requires network read effect
pub fn native_udp_recv_from(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_recv_from")?;
    native_udp_recv_from_interp(args)
}

/// Receive data from connected address
///
/// # Effect
/// * Requires network read effect
pub fn native_udp_recv(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_recv")?;
    native_udp_recv_interp(args)
}

/// Send data to specific address
///
/// # Effect
/// * Requires network write effect
pub fn native_udp_send_to(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_send_to")?;
    native_udp_send_to_interp(args)
}

/// Send data to connected address
///
/// # Effect
/// * Requires network write effect
pub fn native_udp_send(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_send")?;
    native_udp_send_interp(args)
}

/// Peek at data from any address without consuming
///
/// # Effect
/// * Requires network read effect
pub fn native_udp_peek_from(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_peek_from")?;
    native_udp_peek_from_interp(args)
}

/// Peek at data from connected address without consuming
///
/// # Effect
/// * Requires network read effect
pub fn native_udp_peek(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_peek")?;
    native_udp_peek_interp(args)
}

/// Get peer address
///
/// No effect check - query operation
pub fn native_udp_peer_addr(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_peer_addr_interp(args)
}

/// Set broadcast mode
///
/// No effect check - configuration operation
pub fn native_udp_set_broadcast(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_broadcast_interp(args)
}

/// Set multicast loop mode
///
/// No effect check - configuration operation
pub fn native_udp_set_multicast_loop(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_multicast_loop_interp(args)
}

/// Set multicast TTL
///
/// No effect check - configuration operation
pub fn native_udp_set_multicast_ttl(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_multicast_ttl_interp(args)
}

/// Set TTL
///
/// No effect check - configuration operation
pub fn native_udp_set_ttl(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_ttl_interp(args)
}

/// Set read timeout
///
/// No effect check - configuration operation
pub fn native_udp_set_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_read_timeout_interp(args)
}

/// Set write timeout
///
/// No effect check - configuration operation
pub fn native_udp_set_write_timeout(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_set_write_timeout_interp(args)
}

/// Get broadcast mode
///
/// No effect check - query operation
pub fn native_udp_get_broadcast(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_get_broadcast_interp(args)
}

/// Get TTL
///
/// No effect check - query operation
pub fn native_udp_get_ttl(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_get_ttl_interp(args)
}

/// Join IPv4 multicast group
///
/// No effect check - configuration operation
pub fn native_udp_join_multicast_v4(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_join_multicast_v4_interp(args)
}

/// Leave IPv4 multicast group
///
/// No effect check - configuration operation
pub fn native_udp_leave_multicast_v4(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_leave_multicast_v4_interp(args)
}

/// Join IPv6 multicast group
///
/// No effect check - configuration operation
pub fn native_udp_join_multicast_v6(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_join_multicast_v6_interp(args)
}

/// Leave IPv6 multicast group
///
/// No effect check - configuration operation
pub fn native_udp_leave_multicast_v6(args: &[Value]) -> Result<Value, CompileError> {
    native_udp_leave_multicast_v6_interp(args)
}

/// Close UDP socket
///
/// # Effect
/// * Requires network close effect
pub fn native_udp_close(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_udp_close")?;
    native_udp_close_interp(args)
}
