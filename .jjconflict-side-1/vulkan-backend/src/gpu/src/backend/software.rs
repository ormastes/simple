//! Software Backend Implementation
//!
//! CPU-based fallback when no GPU hardware is available.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

use super::{Backend, BufferHandle, GpuEvent, KernelHandle, MemcpyKind, StreamHandle};
use crate::device::{Device, DeviceCapabilities, GpuBackend};
use crate::error::{GpuError, GpuResult};

static NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);

fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Software backend - CPU-based fallback.
pub struct SoftwareBackend {
    initialized: bool,
    current_device: usize,
    /// Allocated memory regions.
    allocations: Mutex<HashMap<BufferHandle, Vec<u8>>>,
    /// Loaded kernels (stored as source for software execution).
    kernels: Mutex<HashMap<KernelHandle, String>>,
}

impl SoftwareBackend {
    /// Create a new software backend.
    pub fn new() -> Self {
        SoftwareBackend {
            initialized: false,
            current_device: 0,
            allocations: Mutex::new(HashMap::new()),
            kernels: Mutex::new(HashMap::new()),
        }
    }
}

impl Default for SoftwareBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for SoftwareBackend {
    fn backend_type(&self) -> GpuBackend {
        GpuBackend::Software
    }

    fn init(&mut self) -> GpuResult<()> {
        self.initialized = true;
        Ok(())
    }

    fn shutdown(&mut self) -> GpuResult<()> {
        self.initialized = false;
        self.allocations.lock().unwrap().clear();
        self.kernels.lock().unwrap().clear();
        Ok(())
    }

    fn is_available(&self) -> bool {
        true // Software backend is always available
    }

    fn device_count(&self) -> GpuResult<usize> {
        Ok(1) // Single virtual device
    }

    fn get_device(&self, index: usize) -> GpuResult<Device> {
        if index != 0 {
            return Err(GpuError::InvalidDevice(index));
        }
        Ok(Device::software())
    }

    fn set_device(&mut self, index: usize) -> GpuResult<()> {
        if index != 0 {
            return Err(GpuError::InvalidDevice(index));
        }
        self.current_device = index;
        Ok(())
    }

    fn current_device(&self) -> GpuResult<usize> {
        Ok(self.current_device)
    }

    fn get_capabilities(&self, index: usize) -> GpuResult<DeviceCapabilities> {
        if index != 0 {
            return Err(GpuError::InvalidDevice(index));
        }
        Ok(DeviceCapabilities::default())
    }

    fn alloc(&self, size: usize) -> GpuResult<BufferHandle> {
        let handle = next_handle();
        let buffer = vec![0u8; size];
        self.allocations.lock().unwrap().insert(handle, buffer);
        Ok(handle)
    }

    fn free(&self, handle: BufferHandle) -> GpuResult<()> {
        self.allocations
            .lock()
            .unwrap()
            .remove(&handle)
            .ok_or(GpuError::InvalidBuffer)?;
        Ok(())
    }

    fn memcpy(
        &self,
        dst: *mut u8,
        src: *const u8,
        size: usize,
        _kind: MemcpyKind,
    ) -> GpuResult<()> {
        // In software backend, all memory is host memory
        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, size);
        }
        Ok(())
    }

    fn memcpy_async(
        &self,
        dst: *mut u8,
        src: *const u8,
        size: usize,
        kind: MemcpyKind,
        _stream: StreamHandle,
    ) -> GpuResult<()> {
        // Software backend has no async - just do sync copy
        self.memcpy(dst, src, size, kind)
    }

    fn memset(&self, handle: BufferHandle, value: u8, size: usize) -> GpuResult<()> {
        let mut allocs = self.allocations.lock().unwrap();
        let buffer = allocs.get_mut(&handle).ok_or(GpuError::InvalidBuffer)?;

        let len = size.min(buffer.len());
        for byte in buffer.iter_mut().take(len) {
            *byte = value;
        }
        Ok(())
    }

    fn load_kernel(&self, source: &str, name: &str) -> GpuResult<KernelHandle> {
        let handle = next_handle();
        let kernel_name = format!("{}:{}", name, source);
        self.kernels.lock().unwrap().insert(handle, kernel_name);
        Ok(handle)
    }

    fn load_kernel_binary(&self, _binary: &[u8], name: &str) -> GpuResult<KernelHandle> {
        // Software backend doesn't execute binaries - just store the name
        let handle = next_handle();
        self.kernels
            .lock()
            .unwrap()
            .insert(handle, name.to_string());
        Ok(handle)
    }

    fn unload_kernel(&self, handle: KernelHandle) -> GpuResult<()> {
        self.kernels
            .lock()
            .unwrap()
            .remove(&handle)
            .ok_or(GpuError::InvalidKernel)?;
        Ok(())
    }

    fn launch_kernel(
        &self,
        _kernel: KernelHandle,
        _grid_dim: [u32; 3],
        _block_dim: [u32; 3],
        _shared_mem: usize,
        _stream: StreamHandle,
        _args: &[*const std::ffi::c_void],
    ) -> GpuResult<()> {
        // Software kernel execution is handled separately via parallel.rs
        // This is just a stub for the backend interface
        Ok(())
    }

    fn create_stream(&self) -> GpuResult<StreamHandle> {
        // Software backend doesn't have real streams
        Ok(next_handle())
    }

    fn destroy_stream(&self, _handle: StreamHandle) -> GpuResult<()> {
        Ok(())
    }

    fn sync_stream(&self, _handle: StreamHandle) -> GpuResult<()> {
        // No-op - software is always synchronous
        Ok(())
    }

    fn sync_device(&self) -> GpuResult<()> {
        // No-op - software is always synchronous
        Ok(())
    }

    fn create_event(&self) -> GpuResult<GpuEvent> {
        Ok(GpuEvent {
            handle: next_handle(),
            backend: GpuBackend::Software,
        })
    }

    fn destroy_event(&self, _event: &GpuEvent) -> GpuResult<()> {
        Ok(())
    }

    fn record_event(&self, _event: &GpuEvent, _stream: StreamHandle) -> GpuResult<()> {
        Ok(())
    }

    fn wait_event(&self, _event: &GpuEvent) -> GpuResult<()> {
        Ok(())
    }

    fn query_event(&self, _event: &GpuEvent) -> GpuResult<bool> {
        Ok(true) // Software events are always complete
    }

    fn event_elapsed(&self, _start: &GpuEvent, _end: &GpuEvent) -> GpuResult<f32> {
        Ok(0.0) // Software backend doesn't track time
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_backend_init() {
        let mut backend = SoftwareBackend::new();
        assert!(backend.is_available());
        assert!(backend.init().is_ok());
        assert!(backend.shutdown().is_ok());
    }

    #[test]
    fn test_software_backend_alloc() {
        let backend = SoftwareBackend::new();
        let handle = backend.alloc(1024).unwrap();
        assert!(backend.free(handle).is_ok());
    }

    #[test]
    fn test_software_backend_memset() {
        let backend = SoftwareBackend::new();
        let handle = backend.alloc(1024).unwrap();
        assert!(backend.memset(handle, 0xFF, 512).is_ok());
        assert!(backend.free(handle).is_ok());
    }

    #[test]
    fn test_software_backend_kernel() {
        let backend = SoftwareBackend::new();
        let handle = backend.load_kernel("void main() {}", "main").unwrap();
        assert!(backend.unload_kernel(handle).is_ok());
    }

    #[test]
    fn test_software_backend_stream() {
        let backend = SoftwareBackend::new();
        let stream = backend.create_stream().unwrap();
        assert!(backend.sync_stream(stream).is_ok());
        assert!(backend.destroy_stream(stream).is_ok());
    }

    #[test]
    fn test_software_backend_event() {
        let backend = SoftwareBackend::new();
        let event = backend.create_event().unwrap();
        let stream = backend.create_stream().unwrap();

        assert!(backend.record_event(&event, stream).is_ok());
        assert!(backend.query_event(&event).unwrap());
        assert!(backend.wait_event(&event).is_ok());
        assert!(backend.destroy_event(&event).is_ok());
    }
}
