//! GPU Backend Abstraction Layer
//!
//! This module provides a trait-based abstraction for different GPU backends,
//! allowing the same code to run on CUDA, ROCm/HIP, Metal, Vulkan, or software.

pub mod software;

#[cfg(feature = "cuda")]
pub mod cuda;

#[cfg(feature = "rocm")]
pub mod rocm;

use crate::device::{Device, DeviceCapabilities, GpuBackend};
use crate::error::GpuResult;

/// Backend-specific device handle.
pub type DeviceHandle = u64;

/// Backend-specific buffer handle.
pub type BufferHandle = u64;

/// Backend-specific kernel handle.
pub type KernelHandle = u64;

/// Backend-specific stream handle.
pub type StreamHandle = u64;

/// Memory copy direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemcpyKind {
    /// Host to device.
    HostToDevice,
    /// Device to host.
    DeviceToHost,
    /// Device to device.
    DeviceToDevice,
    /// Host to host.
    HostToHost,
}

/// Event for synchronization.
#[derive(Debug, Clone)]
pub struct GpuEvent {
    /// Backend-specific event handle.
    pub handle: u64,
    /// Backend type.
    pub backend: GpuBackend,
}

/// GPU backend trait - defines the interface all backends must implement.
pub trait Backend: Send + Sync {
    /// Get the backend type.
    fn backend_type(&self) -> GpuBackend;

    /// Initialize the backend.
    fn init(&mut self) -> GpuResult<()>;

    /// Shutdown the backend.
    fn shutdown(&mut self) -> GpuResult<()>;

    /// Check if the backend is available on this system.
    fn is_available(&self) -> bool;

    // Device management

    /// Get the number of available devices.
    fn device_count(&self) -> GpuResult<usize>;

    /// Get device information.
    fn get_device(&self, index: usize) -> GpuResult<Device>;

    /// Set the current device.
    fn set_device(&mut self, index: usize) -> GpuResult<()>;

    /// Get current device index.
    fn current_device(&self) -> GpuResult<usize>;

    /// Get device capabilities.
    fn get_capabilities(&self, index: usize) -> GpuResult<DeviceCapabilities>;

    // Memory management

    /// Allocate device memory.
    fn alloc(&self, size: usize) -> GpuResult<BufferHandle>;

    /// Free device memory.
    fn free(&self, handle: BufferHandle) -> GpuResult<()>;

    /// Copy memory.
    fn memcpy(
        &self,
        dst: *mut u8,
        src: *const u8,
        size: usize,
        kind: MemcpyKind,
    ) -> GpuResult<()>;

    /// Asynchronous memory copy.
    fn memcpy_async(
        &self,
        dst: *mut u8,
        src: *const u8,
        size: usize,
        kind: MemcpyKind,
        stream: StreamHandle,
    ) -> GpuResult<()>;

    /// Set memory to a value.
    fn memset(&self, dst: BufferHandle, value: u8, size: usize) -> GpuResult<()>;

    // Kernel management

    /// Load a kernel from source.
    fn load_kernel(&self, source: &str, name: &str) -> GpuResult<KernelHandle>;

    /// Load a kernel from PTX/binary.
    fn load_kernel_binary(&self, binary: &[u8], name: &str) -> GpuResult<KernelHandle>;

    /// Unload a kernel.
    fn unload_kernel(&self, handle: KernelHandle) -> GpuResult<()>;

    /// Launch a kernel.
    fn launch_kernel(
        &self,
        kernel: KernelHandle,
        grid_dim: [u32; 3],
        block_dim: [u32; 3],
        shared_mem: usize,
        stream: StreamHandle,
        args: &[*const std::ffi::c_void],
    ) -> GpuResult<()>;

    // Stream management

    /// Create a stream.
    fn create_stream(&self) -> GpuResult<StreamHandle>;

    /// Destroy a stream.
    fn destroy_stream(&self, handle: StreamHandle) -> GpuResult<()>;

    /// Synchronize a stream.
    fn sync_stream(&self, handle: StreamHandle) -> GpuResult<()>;

    /// Synchronize the device (all streams).
    fn sync_device(&self) -> GpuResult<()>;

    // Events

    /// Create an event.
    fn create_event(&self) -> GpuResult<GpuEvent>;

    /// Destroy an event.
    fn destroy_event(&self, event: &GpuEvent) -> GpuResult<()>;

    /// Record an event on a stream.
    fn record_event(&self, event: &GpuEvent, stream: StreamHandle) -> GpuResult<()>;

    /// Wait for an event.
    fn wait_event(&self, event: &GpuEvent) -> GpuResult<()>;

    /// Query if an event is complete.
    fn query_event(&self, event: &GpuEvent) -> GpuResult<bool>;

    /// Get elapsed time between two events in milliseconds.
    fn event_elapsed(&self, start: &GpuEvent, end: &GpuEvent) -> GpuResult<f32>;
}

/// Default stream handle (0 in most backends).
pub const DEFAULT_STREAM: StreamHandle = 0;

/// Get the appropriate backend for the current system.
pub fn get_backend() -> Box<dyn Backend> {
    // Try backends in order of preference
    #[cfg(feature = "cuda")]
    {
        let mut cuda = cuda::CudaBackend::new();
        if cuda.is_available() {
            let _ = cuda.init();
            return Box::new(cuda);
        }
    }

    #[cfg(feature = "rocm")]
    {
        let mut rocm = rocm::RocmBackend::new();
        if rocm.is_available() {
            let _ = rocm.init();
            return Box::new(rocm);
        }
    }

    // Fall back to software
    Box::new(software::SoftwareBackend::new())
}

/// Get a specific backend by type.
pub fn get_backend_by_type(backend: GpuBackend) -> Option<Box<dyn Backend>> {
    match backend {
        GpuBackend::Software => Some(Box::new(software::SoftwareBackend::new())),
        #[cfg(feature = "cuda")]
        GpuBackend::Cuda => {
            let mut cuda = cuda::CudaBackend::new();
            if cuda.is_available() {
                let _ = cuda.init();
                Some(Box::new(cuda))
            } else {
                None
            }
        }
        #[cfg(feature = "rocm")]
        GpuBackend::Rocm => {
            let mut rocm = rocm::RocmBackend::new();
            if rocm.is_available() {
                let _ = rocm.init();
                Some(Box::new(rocm))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_backend() {
        let backend = get_backend();
        // Should at least get software backend
        assert!(backend.is_available() || backend.backend_type() == GpuBackend::Software);
    }

    #[test]
    fn test_memcpy_kind() {
        assert_ne!(MemcpyKind::HostToDevice, MemcpyKind::DeviceToHost);
    }
}
