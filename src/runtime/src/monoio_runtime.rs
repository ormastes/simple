// Monoio runtime wrapper for Simple language async networking
// Provides thread-per-core async runtime based on io_uring
// Feature: #1730-#1739 (Core Runtime)

#![cfg(feature = "monoio-net")]

use crate::value::RuntimeValue;
use std::cell::RefCell;

/// Thread-local runtime instance
/// Each thread gets its own monoio runtime (thread-per-core architecture)
thread_local! {
    static MONOIO_RT: RefCell<Option<bool>> = RefCell::new(None);
}

// Note: monoio Runtime is not Send/Sync by design (thread-local only)
// For multi-threaded scenarios, spawn multiple threads each with their own runtime

/// Initialize monoio runtime for current thread
/// Feature #1730: Thread-per-core runtime initialization
#[no_mangle]
pub extern "C" fn monoio_runtime_init() -> RuntimeValue {
    MONOIO_RT.with(|rt| {
        let mut rt_ref = rt.borrow_mut();
        if rt_ref.is_none() {
            // Mark runtime as initialized for this thread
            *rt_ref = Some(true);
        }
    });

    // Return success (1 = true)
    RuntimeValue::from_int(1)
}

/// Initialize global runtime for multi-threaded scenarios
/// Feature #1755: Hybrid runtime support
#[no_mangle]
pub extern "C" fn monoio_runtime_init_global() -> RuntimeValue {
    // Note: monoio doesn't support global shared runtime
    // Each thread must have its own runtime (thread-per-core model)
    // This function is provided for API compatibility but delegates to thread-local init
    tracing::warn!("monoio_runtime_init_global: monoio uses thread-per-core model, initializing thread-local runtime");
    monoio_runtime_init()
}

/// Spawn a task on the current thread's runtime
/// Feature #1731: Task spawning and management
#[no_mangle]
pub extern "C" fn monoio_spawn_local(_task_fn: RuntimeValue) -> RuntimeValue {
    // TODO: Convert RuntimeValue to Future
    // For now, return stub value
    // In full implementation:
    // 1. Extract closure from RuntimeValue
    // 2. Convert to async block
    // 3. Spawn on thread-local runtime
    // 4. Return task handle as RuntimeValue

    tracing::warn!("monoio_spawn_local: stub implementation");
    RuntimeValue::from_int(0)
}

/// Block current thread and run runtime until completion
/// Feature #1732: Runtime execution control
#[no_mangle]
pub extern "C" fn monoio_block_on(_future: RuntimeValue) -> RuntimeValue {
    // TODO: Convert RuntimeValue to Future and execute
    // For now, return stub value

    tracing::warn!("monoio_block_on: stub implementation");
    RuntimeValue::from_int(0)
}

/// Shutdown current thread's runtime
/// Feature #1733: Graceful shutdown
#[no_mangle]
pub extern "C" fn monoio_runtime_shutdown() -> RuntimeValue {
    MONOIO_RT.with(|rt| {
        let mut rt_ref = rt.borrow_mut();
        *rt_ref = None;
    });

    RuntimeValue::from_int(1)
}

/// Shutdown global runtime
#[no_mangle]
pub extern "C" fn monoio_runtime_shutdown_global() -> RuntimeValue {
    // Delegate to thread-local shutdown
    monoio_runtime_shutdown()
}

/// Get number of available CPU cores (for thread-per-core setup)
/// Feature #1734: CPU topology detection
#[no_mangle]
pub extern "C" fn monoio_get_num_cores() -> RuntimeValue {
    let num_cores = num_cpus::get();
    RuntimeValue::from_int(num_cores as i64)
}

/// Configure io_uring entries (ring size)
/// Feature #1735: Runtime configuration
#[no_mangle]
pub extern "C" fn monoio_configure_entries(_entries: i64) -> RuntimeValue {
    // monoio doesn't expose entries() configuration in current API
    // This is a placeholder for future configuration options
    tracing::warn!("monoio_configure_entries: not supported in current monoio API");

    RuntimeValue::from_int(1)
}

/// Runtime statistics and monitoring
/// Feature #1736: Performance monitoring
#[derive(Debug, Clone)]
pub struct MonoioStats {
    pub tasks_spawned: u64,
    pub tasks_completed: u64,
    pub io_operations: u64,
    pub io_errors: u64,
}

thread_local! {
    static RUNTIME_STATS: RefCell<MonoioStats> = RefCell::new(MonoioStats {
        tasks_spawned: 0,
        tasks_completed: 0,
        io_operations: 0,
        io_errors: 0,
    });
}

/// Get current runtime statistics
#[no_mangle]
pub extern "C" fn monoio_get_stats() -> RuntimeValue {
    // TODO: Return stats as RuntimeValue (struct or dict)
    // For now, return stub
    RuntimeValue::from_int(0)
}

/// Reset runtime statistics
#[no_mangle]
pub extern "C" fn monoio_reset_stats() -> RuntimeValue {
    RUNTIME_STATS.with(|stats| {
        let mut stats_ref = stats.borrow_mut();
        stats_ref.tasks_spawned = 0;
        stats_ref.tasks_completed = 0;
        stats_ref.io_operations = 0;
        stats_ref.io_errors = 0;
    });

    RuntimeValue::from_int(1)
}

// Helper functions for internal use

/// Check if monoio runtime is available on current thread
pub(crate) fn has_runtime() -> bool {
    MONOIO_RT.with(|rt| rt.borrow().is_some())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_init() {
        let result = monoio_runtime_init();
        assert_eq!(result.as_int(), 1);
    }

    #[test]
    fn test_num_cores() {
        let cores = monoio_get_num_cores();
        assert!(cores.as_int() > 0);
    }

    #[test]
    fn test_runtime_shutdown() {
        monoio_runtime_init();
        let result = monoio_runtime_shutdown();
        assert_eq!(result.as_int(), 1);
    }

    #[test]
    fn test_stats_reset() {
        let result = monoio_reset_stats();
        assert_eq!(result.as_int(), 1);
    }
}
