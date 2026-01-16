// Monoio runtime wrapper for Simple language async networking
// Provides thread-per-core async runtime based on io_uring
// Feature: #1730-#1739 (Core Runtime)

#![cfg(feature = "monoio-net")]

use crate::value::RuntimeValue;
use std::cell::RefCell;
use std::rc::Rc;

// Re-export monoio types we need
use monoio::RuntimeBuilder;

/// Thread-local runtime instance
/// Each thread gets its own monoio runtime (thread-per-core architecture)
thread_local! {
    static MONOIO_RT: RefCell<Option<MonoioRuntimeHandle>> = RefCell::new(None);
}

/// Handle to the monoio runtime
/// Stores configuration and allows runtime recreation
#[derive(Clone)]
struct MonoioRuntimeHandle {
    /// io_uring entries (ring size)
    entries: u32,
    /// Whether runtime was successfully created
    initialized: bool,
}

impl Default for MonoioRuntimeHandle {
    fn default() -> Self {
        Self {
            entries: 256, // Default io_uring ring size
            initialized: false,
        }
    }
}

// Note: monoio Runtime is not Send/Sync by design (thread-local only)
// For multi-threaded scenarios, spawn multiple threads each with their own runtime

/// Initialize monoio runtime for current thread
/// Feature #1730: Thread-per-core runtime initialization
#[no_mangle]
pub extern "C" fn monoio_runtime_init() -> RuntimeValue {
    let result = MONOIO_RT.with(|rt| {
        let mut rt_ref = rt.borrow_mut();
        if rt_ref.is_none() {
            // Create new runtime handle with default configuration
            let handle = MonoioRuntimeHandle {
                entries: 256,
                initialized: true,
            };
            *rt_ref = Some(handle);
            true
        } else {
            // Already initialized
            true
        }
    });

    // Return success (1 = true) or error (0 = false)
    RuntimeValue::from_int(if result { 1 } else { 0 })
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
    // Stub implementation - RuntimeValue to Future conversion not yet implemented
    // Full implementation would:
    // 1. Extract closure from RuntimeValue (RuntimeClosure)
    // 2. Create async block that calls the closure
    // 3. Spawn on thread-local monoio runtime using spawn_local()
    // 4. Wrap returned JoinHandle in RuntimeValue
    // Requires FFI bridge between RuntimeValue and async Rust

    tracing::warn!("monoio_spawn_local: stub implementation");
    RuntimeValue::from_int(0)
}

/// Block current thread and run runtime until completion
/// Feature #1732: Runtime execution control
///
/// Note: Since we cannot easily convert RuntimeValue to a Future without
/// the full async infrastructure, this is a helper that executes a closure.
/// The actual async execution happens in the TCP/UDP functions.
#[no_mangle]
pub extern "C" fn monoio_block_on(_future: RuntimeValue) -> RuntimeValue {
    // This function is conceptually for blocking on a future
    // In practice, monoio requires creating a runtime and calling block_on on it
    // For now, we'll have each TCP/UDP operation create its own runtime instance

    tracing::warn!("monoio_block_on: Direct future execution not yet supported");
    tracing::info!("monoio_block_on: Use TCP/UDP functions which internally handle async execution");

    RuntimeValue::from_int(0)
}

/// Internal helper: Execute an async block with monoio runtime
/// This creates a runtime, executes the future, and returns the result
pub(crate) fn execute_async<F, R>(entries: u32, future: F) -> Result<R, std::io::Error>
where
    F: std::future::Future<Output = std::io::Result<R>>,
{
    // Create a new runtime with specified configuration
    let mut rt = RuntimeBuilder::<monoio::FusionDriver>::new()
        .with_entries(entries)
        .build()
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to create runtime: {}", e)))?;

    // Execute the future
    rt.block_on(future)
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
pub extern "C" fn monoio_configure_entries(entries: i64) -> RuntimeValue {
    if entries < 1 || entries > 32768 {
        tracing::error!(
            "monoio_configure_entries: Invalid entries value {}, must be 1-32768",
            entries
        );
        return RuntimeValue::from_int(0);
    }

    let result = MONOIO_RT.with(|rt| {
        let mut rt_ref = rt.borrow_mut();
        match rt_ref.as_mut() {
            Some(handle) => {
                handle.entries = entries as u32;
                true
            }
            None => {
                // Create new handle with specified entries
                let handle = MonoioRuntimeHandle {
                    entries: entries as u32,
                    initialized: false,
                };
                *rt_ref = Some(handle);
                true
            }
        }
    });

    RuntimeValue::from_int(if result { 1 } else { 0 })
}

/// Get configured entries value for current thread
pub(crate) fn get_entries() -> u32 {
    MONOIO_RT.with(|rt| rt.borrow().as_ref().map(|h| h.entries).unwrap_or(256))
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
    // Stub implementation - would return RuntimeStats as RuntimeValue
    // Full implementation would:
    // 1. Get RUNTIME_STATS from thread-local storage
    // 2. Create RuntimeDict or RuntimeObject with stats fields:
    //    {tasks_spawned, tasks_completed, io_operations, io_errors}
    // 3. Return as RuntimeValue
    // Currently returns 0 as placeholder
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

// ============================================================================
// RuntimeValue conversion helpers
// ============================================================================

use crate::value::{rt_string_new, HeapObjectType, RuntimeString};

/// Convert RuntimeValue to String
/// Returns None if the value is not a string
pub(crate) fn runtime_value_to_string(value: RuntimeValue) -> Option<String> {
    if !value.is_heap() {
        return None;
    }

    // Get the heap pointer and check type
    let ptr = value.as_heap_ptr();
    unsafe {
        let header = &*(ptr as *const crate::value::HeapHeader);
        if header.object_type != HeapObjectType::String {
            return None;
        }

        let str_ptr = ptr as *const RuntimeString;
        let s = (*str_ptr).as_str();
        Some(s.to_string())
    }
}

/// Convert String to RuntimeValue
pub(crate) fn string_to_runtime_value(s: &str) -> RuntimeValue {
    if s.is_empty() {
        return unsafe { rt_string_new(std::ptr::null(), 0) };
    }

    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

// ============================================================================
// Buffer Management for Network I/O
// ============================================================================

use crate::value::{HeapHeader, RuntimeArray};

/// Extract bytes from RuntimeValue buffer (RuntimeArray or RuntimeString)
/// Returns None if the value is not a valid buffer
pub(crate) fn extract_buffer_bytes(buffer: RuntimeValue) -> Option<Vec<u8>> {
    if !buffer.is_heap() {
        return None;
    }

    let ptr = buffer.as_heap_ptr();
    unsafe {
        let header = &*(ptr as *const HeapHeader);

        match header.object_type {
            HeapObjectType::String => {
                // Extract from RuntimeString
                let str_ptr = ptr as *const RuntimeString;
                let bytes = (*str_ptr).as_bytes();
                Some(bytes.to_vec())
            }
            HeapObjectType::Array => {
                // Extract from RuntimeArray
                let arr_ptr = ptr as *const RuntimeArray;
                let slice = (*arr_ptr).as_slice();

                // Convert RuntimeValue elements to bytes
                // Assume they are integers 0-255
                let mut bytes = Vec::with_capacity((*arr_ptr).len as usize);
                for i in 0..(*arr_ptr).len as usize {
                    let val = slice[i];
                    if val.is_int() {
                        let byte = val.as_int() as u8;
                        bytes.push(byte);
                    } else {
                        return None; // Invalid array element
                    }
                }
                Some(bytes)
            }
            _ => None,
        }
    }
}

/// Copy bytes into RuntimeValue buffer (RuntimeArray)
/// Returns the number of bytes copied, or -1 on error
pub(crate) fn copy_to_buffer(buffer: RuntimeValue, data: &[u8]) -> i64 {
    if !buffer.is_heap() {
        return -1;
    }

    let ptr = buffer.as_heap_ptr();
    unsafe {
        let header = &*(ptr as *const HeapHeader);

        if header.object_type != HeapObjectType::Array {
            return -1;
        }

        let arr_ptr = ptr as *mut RuntimeArray;
        let capacity = (*arr_ptr).capacity as usize;

        // Determine how many bytes we can copy
        let copy_len = data.len().min(capacity);

        // Get pointer to data area (after the header), using capacity not len
        let data_ptr = (arr_ptr as *mut RuntimeArray).add(1) as *mut RuntimeValue;
        let slice = std::slice::from_raw_parts_mut(data_ptr, capacity);

        // Copy data as RuntimeValue integers
        for i in 0..copy_len {
            slice[i] = RuntimeValue::from_int(data[i] as i64);
        }

        // Update array length
        (*arr_ptr).len = copy_len as u64;

        copy_len as i64
    }
}

/// Create a RuntimeValue byte array from bytes
pub(crate) fn bytes_to_runtime_array(data: &[u8]) -> RuntimeValue {
    use crate::value::rt_array_new;

    let array = rt_array_new(data.len() as u64);
    copy_to_buffer(array, data);
    array
}

// ============================================================================
// Direct I/O Registry (Feature: monoio-direct)
// ============================================================================

#[cfg(feature = "monoio-direct")]
pub mod direct {
    use monoio::net::{TcpListener, TcpStream};
    use monoio::net::udp::UdpSocket;
    use std::cell::RefCell;
    use std::collections::HashMap;

    /// Thread-local I/O resource registry
    ///
    /// Stores active TCP/UDP connections for the current thread.
    /// Each thread has its own registry to avoid synchronization overhead.
    pub struct IoRegistry {
        next_id: i64,
        tcp_listeners: HashMap<i64, TcpListener>,
        tcp_streams: HashMap<i64, TcpStream>,
        udp_sockets: HashMap<i64, UdpSocket>,
    }

    impl IoRegistry {
        /// Create a new empty registry
        pub fn new() -> Self {
            Self {
                next_id: 1,
                tcp_listeners: HashMap::new(),
                tcp_streams: HashMap::new(),
                udp_sockets: HashMap::new(),
            }
        }

        /// Allocate a new unique ID
        pub fn alloc_id(&mut self) -> i64 {
            let id = self.next_id;
            self.next_id += 1;
            id
        }

        /// Add a TCP listener and return its ID
        pub fn add_tcp_listener(&mut self, listener: TcpListener) -> i64 {
            let id = self.alloc_id();
            self.tcp_listeners.insert(id, listener);
            id
        }

        /// Add a TCP stream and return its ID
        pub fn add_tcp_stream(&mut self, stream: TcpStream) -> i64 {
            let id = self.alloc_id();
            self.tcp_streams.insert(id, stream);
            id
        }

        /// Add a UDP socket and return its ID
        pub fn add_udp_socket(&mut self, socket: UdpSocket) -> i64 {
            let id = self.alloc_id();
            self.udp_sockets.insert(id, socket);
            id
        }

        /// Get a mutable reference to a TCP listener
        pub fn get_tcp_listener(&mut self, id: i64) -> Option<&mut TcpListener> {
            self.tcp_listeners.get_mut(&id)
        }

        /// Get a mutable reference to a TCP stream
        pub fn get_tcp_stream(&mut self, id: i64) -> Option<&mut TcpStream> {
            self.tcp_streams.get_mut(&id)
        }

        /// Get a mutable reference to a UDP socket
        pub fn get_udp_socket(&mut self, id: i64) -> Option<&mut UdpSocket> {
            self.udp_sockets.get_mut(&id)
        }

        /// Take ownership of a TCP stream (removes from registry)
        pub fn take_tcp_stream(&mut self, id: i64) -> Option<TcpStream> {
            self.tcp_streams.remove(&id)
        }

        /// Take ownership of a TCP listener (removes from registry)
        pub fn take_tcp_listener(&mut self, id: i64) -> Option<TcpListener> {
            self.tcp_listeners.remove(&id)
        }

        /// Take ownership of a UDP socket (removes from registry)
        pub fn take_udp_socket(&mut self, id: i64) -> Option<UdpSocket> {
            self.udp_sockets.remove(&id)
        }

        /// Remove a TCP listener
        pub fn remove_tcp_listener(&mut self, id: i64) -> bool {
            self.tcp_listeners.remove(&id).is_some()
        }

        /// Remove a TCP stream
        pub fn remove_tcp_stream(&mut self, id: i64) -> bool {
            self.tcp_streams.remove(&id).is_some()
        }

        /// Remove a UDP socket
        pub fn remove_udp_socket(&mut self, id: i64) -> bool {
            self.udp_sockets.remove(&id).is_some()
        }

        /// Get the number of active TCP listeners
        pub fn tcp_listener_count(&self) -> usize {
            self.tcp_listeners.len()
        }

        /// Get the number of active TCP streams
        pub fn tcp_stream_count(&self) -> usize {
            self.tcp_streams.len()
        }

        /// Get the number of active UDP sockets
        pub fn udp_socket_count(&self) -> usize {
            self.udp_sockets.len()
        }

        /// Clear all resources
        pub fn clear(&mut self) {
            self.tcp_listeners.clear();
            self.tcp_streams.clear();
            self.udp_sockets.clear();
        }
    }

    impl Default for IoRegistry {
        fn default() -> Self {
            Self::new()
        }
    }

    thread_local! {
        /// Thread-local io_uring entries configuration
        static DIRECT_ENTRIES: RefCell<u32> = const { RefCell::new(256) };

        /// Thread-local flag indicating if runtime is initialized
        static DIRECT_INITIALIZED: RefCell<bool> = const { RefCell::new(false) };

        /// Thread-local I/O registry
        static IO_REGISTRY: RefCell<IoRegistry> = RefCell::new(IoRegistry::new());
    }

    /// Initialize the direct monoio runtime for the current thread
    pub fn init_direct_runtime(entries: u32) -> Result<(), std::io::Error> {
        DIRECT_ENTRIES.with(|e| {
            *e.borrow_mut() = entries;
        });
        DIRECT_INITIALIZED.with(|init| {
            *init.borrow_mut() = true;
        });
        Ok(())
    }

    /// Check if the direct runtime is initialized for the current thread
    pub fn has_direct_runtime() -> bool {
        DIRECT_INITIALIZED.with(|init| *init.borrow())
    }

    /// Shutdown the direct runtime for the current thread
    pub fn shutdown_direct_runtime() {
        DIRECT_INITIALIZED.with(|init| {
            *init.borrow_mut() = false;
        });
        IO_REGISTRY.with(|reg| {
            reg.borrow_mut().clear();
        });
    }

    /// Get configured entries
    fn get_direct_entries() -> u32 {
        DIRECT_ENTRIES.with(|e| *e.borrow())
    }

    /// Execute an async block by creating a new runtime instance
    ///
    /// Note: This creates a new runtime for each call, which has some overhead
    /// but avoids the complexity of storing the runtime (which is !Send/!Sync).
    /// For high-performance scenarios, consider using the thread-local runtime
    /// pattern where the entire thread runs in the monoio context.
    pub fn block_on<F, R>(future: F) -> Result<R, std::io::Error>
    where
        F: std::future::Future<Output = std::io::Result<R>>,
    {
        let entries = get_direct_entries();

        // Create a new runtime for this call
        let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
            .with_entries(entries)
            .build()
            .map_err(|e| {
                std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!("Failed to create monoio runtime: {}", e),
                )
            })?;

        rt.block_on(future)
    }

    /// Access the I/O registry for the current thread
    pub fn with_registry<F, R>(f: F) -> R
    where
        F: FnOnce(&mut IoRegistry) -> R,
    {
        IO_REGISTRY.with(|reg| f(&mut reg.borrow_mut()))
    }

    /// FFI: Initialize direct runtime
    #[no_mangle]
    pub extern "C" fn rt_monoio_direct_init(entries: i64) -> crate::value::RuntimeValue {
        let entries = if entries < 1 || entries > 32768 {
            256
        } else {
            entries as u32
        };

        match init_direct_runtime(entries) {
            Ok(()) => crate::value::RuntimeValue::from_int(1),
            Err(e) => {
                tracing::error!("rt_monoio_direct_init: {}", e);
                crate::value::RuntimeValue::from_int(0)
            }
        }
    }

    /// FFI: Check if direct runtime is available
    #[no_mangle]
    pub extern "C" fn rt_monoio_direct_available() -> crate::value::RuntimeValue {
        crate::value::RuntimeValue::from_bool(has_direct_runtime())
    }

    /// FFI: Shutdown direct runtime
    #[no_mangle]
    pub extern "C" fn rt_monoio_direct_shutdown() -> crate::value::RuntimeValue {
        shutdown_direct_runtime();
        crate::value::RuntimeValue::from_int(1)
    }

    /// FFI: Get I/O resource counts for debugging
    #[no_mangle]
    pub extern "C" fn rt_monoio_direct_resource_count() -> crate::value::RuntimeValue {
        let count = with_registry(|reg| reg.tcp_listener_count() + reg.tcp_stream_count() + reg.udp_socket_count());
        crate::value::RuntimeValue::from_int(count as i64)
    }
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

#[cfg(all(test, feature = "monoio-direct"))]
mod direct_tests {
    use super::direct::*;

    #[test]
    fn test_io_registry() {
        let mut registry = IoRegistry::new();
        assert_eq!(registry.tcp_stream_count(), 0);

        let id = registry.alloc_id();
        assert_eq!(id, 1);

        let id2 = registry.alloc_id();
        assert_eq!(id2, 2);
    }
}
