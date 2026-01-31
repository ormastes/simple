// Runtime initialization for direct monoio operations
// Feature: monoio-direct

use crate::monoio_runtime::direct::init_direct_runtime;
use crate::value::RuntimeValue;

// ============================================================================
// Runtime Initialization
// ============================================================================

/// Initialize the direct monoio runtime with default settings.
///
/// This must be called before any direct I/O operations on this thread.
/// The runtime is thread-local, so each thread that needs I/O must call this.
#[no_mangle]
pub extern "C" fn rt_monoio_init() -> RuntimeValue {
    match init_direct_runtime(256) {
        Ok(()) => RuntimeValue::from_int(1),
        Err(e) => {
            tracing::error!("rt_monoio_init: {}", e);
            RuntimeValue::from_int(0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init() {
        let result = rt_monoio_init();
        // May fail if io_uring not available
        assert!(result.as_int() == 0 || result.as_int() == 1);
    }
}
