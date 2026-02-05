// Performance metrics for direct monoio runtime
// Feature: monoio-direct

use crate::monoio_runtime::direct::with_registry;
use crate::value::RuntimeValue;

// ============================================================================
// Performance Metrics
// ============================================================================

/// Get performance metrics for the direct runtime.
#[no_mangle]
pub extern "C" fn rt_monoio_direct_stats() -> RuntimeValue {
    // Return resource count for now
    let count = with_registry(|reg| reg.tcp_listener_count() + reg.tcp_stream_count() + reg.udp_socket_count());
    RuntimeValue::from_int(count as i64)
}
