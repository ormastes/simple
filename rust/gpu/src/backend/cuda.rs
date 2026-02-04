//! CUDA Backend Implementation
//!
//! NVIDIA CUDA backend using the CUDA Driver API.

use std::collections::HashMap;
use std::ffi::{c_void, CString};
use std::ptr;
use std::sync::Mutex;

use super::{Backend, BufferHandle, GpuEvent, KernelHandle, MemcpyKind, StreamHandle};
use crate::device::{Device, DeviceCapabilities, GpuBackend};
use crate::error::{GpuError, GpuResult};

// CUDA Driver API types
type CUdevice = i32;
type CUcontext = *mut c_void;
type CUmodule = *mut c_void;
type CUfunction = *mut c_void;
type CUstream = *mut c_void;
type CUevent = *mut c_void;
type CUdeviceptr = u64;
type CUresult = i32;

// CUDA error codes
const CUDA_SUCCESS: CUresult = 0;
const CUDA_ERROR_NOT_INITIALIZED: CUresult = 3;

// CUDA device attributes
const CU_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK: i32 = 1;
const CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_X: i32 = 2;
const CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Y: i32 = 3;
const CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Z: i32 = 4;
const CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_X: i32 = 5;
const CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Y: i32 = 6;
const CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Z: i32 = 7;
const CU_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK: i32 = 8;
const CU_DEVICE_ATTRIBUTE_WARP_SIZE: i32 = 10;

// CUDA memory copy kinds
const CU_MEMCPY_HOST_TO_DEVICE: i32 = 1;
const CU_MEMCPY_DEVICE_TO_HOST: i32 = 2;
const CU_MEMCPY_DEVICE_TO_DEVICE: i32 = 3;

// CUDA Driver API FFI
// Use cfg_attr to conditionally link to different library names per OS
#[cfg_attr(target_os = "linux", link(name = "cuda"))]
#[cfg_attr(target_os = "windows", link(name = "nvcuda"))]
#[cfg_attr(target_os = "macos", link(name = "cuda"))]
extern "C" {
    fn cuInit(flags: u32) -> CUresult;
    fn cuDeviceGetCount(count: *mut i32) -> CUresult;
    fn cuDeviceGet(device: *mut CUdevice, ordinal: i32) -> CUresult;
    fn cuDeviceGetName(name: *mut i8, len: i32, dev: CUdevice) -> CUresult;
    fn cuDeviceGetAttribute(pi: *mut i32, attrib: i32, dev: CUdevice) -> CUresult;
    fn cuDeviceTotalMem_v2(bytes: *mut usize, dev: CUdevice) -> CUresult;
    fn cuCtxCreate_v2(ctx: *mut CUcontext, flags: u32, dev: CUdevice) -> CUresult;
    fn cuCtxDestroy_v2(ctx: CUcontext) -> CUresult;
    fn cuCtxSetCurrent(ctx: CUcontext) -> CUresult;
    fn cuCtxSynchronize() -> CUresult;
    fn cuMemAlloc_v2(dptr: *mut CUdeviceptr, bytesize: usize) -> CUresult;
    fn cuMemFree_v2(dptr: CUdeviceptr) -> CUresult;
    fn cuMemcpyHtoD_v2(dst: CUdeviceptr, src: *const c_void, bytecount: usize) -> CUresult;
    fn cuMemcpyDtoH_v2(dst: *mut c_void, src: CUdeviceptr, bytecount: usize) -> CUresult;
    fn cuMemcpyDtoD_v2(dst: CUdeviceptr, src: CUdeviceptr, bytecount: usize) -> CUresult;
    fn cuMemcpyHtoDAsync_v2(dst: CUdeviceptr, src: *const c_void, bytecount: usize, stream: CUstream) -> CUresult;
    fn cuMemcpyDtoHAsync_v2(dst: *mut c_void, src: CUdeviceptr, bytecount: usize, stream: CUstream) -> CUresult;
    fn cuMemsetD8_v2(dst: CUdeviceptr, value: u8, n: usize) -> CUresult;
    fn cuModuleLoadData(module: *mut CUmodule, image: *const c_void) -> CUresult;
    fn cuModuleUnload(hmod: CUmodule) -> CUresult;
    fn cuModuleGetFunction(hfunc: *mut CUfunction, hmod: CUmodule, name: *const i8) -> CUresult;
    fn cuLaunchKernel(
        f: CUfunction,
        gridDimX: u32,
        gridDimY: u32,
        gridDimZ: u32,
        blockDimX: u32,
        blockDimY: u32,
        blockDimZ: u32,
        sharedMemBytes: u32,
        hStream: CUstream,
        kernelParams: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> CUresult;
    fn cuStreamCreate(phStream: *mut CUstream, flags: u32) -> CUresult;
    fn cuStreamDestroy_v2(hStream: CUstream) -> CUresult;
    fn cuStreamSynchronize(hStream: CUstream) -> CUresult;
    fn cuEventCreate(phEvent: *mut CUevent, flags: u32) -> CUresult;
    fn cuEventDestroy_v2(hEvent: CUevent) -> CUresult;
    fn cuEventRecord(hEvent: CUevent, hStream: CUstream) -> CUresult;
    fn cuEventSynchronize(hEvent: CUevent) -> CUresult;
    fn cuEventQuery(hEvent: CUevent) -> CUresult;
    fn cuEventElapsedTime(pMilliseconds: *mut f32, hStart: CUevent, hEnd: CUevent) -> CUresult;
}

/// Convert CUDA result to GpuResult.
fn cuda_check(result: CUresult) -> GpuResult<()> {
    if result == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(GpuError::BackendError(format!("CUDA error: {}", result)))
    }
}

/// Kernel info stored for launching.
struct KernelInfo {
    module: CUmodule,
    function: CUfunction,
}

/// CUDA backend implementation.
pub struct CudaBackend {
    initialized: bool,
    device_count: i32,
    current_device: usize,
    contexts: Vec<CUcontext>,
    /// Buffer handle to device pointer mapping.
    allocations: Mutex<HashMap<BufferHandle, CUdeviceptr>>,
    /// Kernel handle to kernel info mapping.
    kernels: Mutex<HashMap<KernelHandle, KernelInfo>>,
    /// Stream handle to CUDA stream mapping.
    streams: Mutex<HashMap<StreamHandle, CUstream>>,
    /// Event handle to CUDA event mapping.
    events: Mutex<HashMap<u64, CUevent>>,
    next_handle: std::sync::atomic::AtomicU64,
}

impl CudaBackend {
    /// Create a new CUDA backend.
    pub fn new() -> Self {
        CudaBackend {
            initialized: false,
            device_count: 0,
            current_device: 0,
            contexts: Vec::new(),
            allocations: Mutex::new(HashMap::new()),
            kernels: Mutex::new(HashMap::new()),
            streams: Mutex::new(HashMap::new()),
            events: Mutex::new(HashMap::new()),
            next_handle: std::sync::atomic::AtomicU64::new(1),
        }
    }

    fn next_handle(&self) -> u64 {
        self.next_handle.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    /// Get device attribute.
    fn get_attribute(&self, device: CUdevice, attrib: i32) -> GpuResult<i32> {
        let mut value: i32 = 0;
        unsafe {
            cuda_check(cuDeviceGetAttribute(&mut value, attrib, device))?;
        }
        Ok(value)
    }
}

impl Default for CudaBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for CudaBackend {
    fn backend_type(&self) -> GpuBackend {
        GpuBackend::Cuda
    }

    fn init(&mut self) -> GpuResult<()> {
        if self.initialized {
            return Ok(());
        }

        unsafe {
            // Initialize CUDA
            let result = cuInit(0);
            if result == CUDA_ERROR_NOT_INITIALIZED || result != CUDA_SUCCESS {
                return Err(GpuError::BackendError("Failed to initialize CUDA".to_string()));
            }

            // Get device count
            cuda_check(cuDeviceGetCount(&mut self.device_count))?;

            if self.device_count == 0 {
                return Err(GpuError::NoDeviceFound);
            }

            // Create context for each device
            for i in 0..self.device_count {
                let mut device: CUdevice = 0;
                cuda_check(cuDeviceGet(&mut device, i))?;

                let mut ctx: CUcontext = ptr::null_mut();
                cuda_check(cuCtxCreate_v2(&mut ctx, 0, device))?;
                self.contexts.push(ctx);
            }

            // Set first device as current
            if !self.contexts.is_empty() {
                cuda_check(cuCtxSetCurrent(self.contexts[0]))?;
            }
        }

        self.initialized = true;
        Ok(())
    }

    fn shutdown(&mut self) -> GpuResult<()> {
        if !self.initialized {
            return Ok(());
        }

        // Free all allocations
        {
            let allocs = self.allocations.lock().unwrap();
            for &ptr in allocs.values() {
                unsafe {
                    let _ = cuMemFree_v2(ptr);
                }
            }
        }
        self.allocations.lock().unwrap().clear();

        // Unload all kernels
        {
            let kernels = self.kernels.lock().unwrap();
            for info in kernels.values() {
                unsafe {
                    let _ = cuModuleUnload(info.module);
                }
            }
        }
        self.kernels.lock().unwrap().clear();

        // Destroy all streams
        {
            let streams = self.streams.lock().unwrap();
            for &stream in streams.values() {
                unsafe {
                    let _ = cuStreamDestroy_v2(stream);
                }
            }
        }
        self.streams.lock().unwrap().clear();

        // Destroy all events
        {
            let events = self.events.lock().unwrap();
            for &event in events.values() {
                unsafe {
                    let _ = cuEventDestroy_v2(event);
                }
            }
        }
        self.events.lock().unwrap().clear();

        // Destroy contexts
        for ctx in &self.contexts {
            unsafe {
                let _ = cuCtxDestroy_v2(*ctx);
            }
        }
        self.contexts.clear();

        self.initialized = false;
        Ok(())
    }

    fn is_available(&self) -> bool {
        unsafe {
            let result = cuInit(0);
            if result != CUDA_SUCCESS {
                return false;
            }

            let mut count: i32 = 0;
            if cuDeviceGetCount(&mut count) != CUDA_SUCCESS {
                return false;
            }

            count > 0
        }
    }

    fn device_count(&self) -> GpuResult<usize> {
        Ok(self.device_count as usize)
    }

    fn get_device(&self, index: usize) -> GpuResult<Device> {
        if index >= self.device_count as usize {
            return Err(GpuError::InvalidDevice(index));
        }

        unsafe {
            let mut device: CUdevice = 0;
            cuda_check(cuDeviceGet(&mut device, index as i32))?;

            // Get device name
            let mut name_buf = [0i8; 256];
            cuda_check(cuDeviceGetName(name_buf.as_mut_ptr(), 256, device))?;
            let name = std::ffi::CStr::from_ptr(name_buf.as_ptr())
                .to_string_lossy()
                .into_owned();

            // Get total memory
            let mut total_mem: usize = 0;
            cuda_check(cuDeviceTotalMem_v2(&mut total_mem, device))?;

            // Get capabilities
            let caps = self.get_capabilities(index)?;

            Ok(Device {
                id: index as u32,
                name,
                vendor: "NVIDIA".to_string(),
                backend: GpuBackend::Cuda,
                memory_bytes: total_mem as u64,
                capabilities: caps,
                is_default: index == 0,
            })
        }
    }

    fn set_device(&mut self, index: usize) -> GpuResult<()> {
        if index >= self.contexts.len() {
            return Err(GpuError::InvalidDevice(index));
        }

        unsafe {
            cuda_check(cuCtxSetCurrent(self.contexts[index]))?;
        }
        self.current_device = index;
        Ok(())
    }

    fn current_device(&self) -> GpuResult<usize> {
        Ok(self.current_device)
    }

    fn get_capabilities(&self, index: usize) -> GpuResult<DeviceCapabilities> {
        if index >= self.device_count as usize {
            return Err(GpuError::InvalidDevice(index));
        }

        unsafe {
            let mut device: CUdevice = 0;
            cuda_check(cuDeviceGet(&mut device, index as i32))?;

            Ok(DeviceCapabilities {
                max_work_group_size_x: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_X)? as u32,
                max_work_group_size_y: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Y)? as u32,
                max_work_group_size_z: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Z)? as u32,
                max_work_group_invocations: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK)?
                    as u32,
                max_work_groups_x: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_X)? as u32,
                max_work_groups_y: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Y)? as u32,
                max_work_groups_z: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Z)? as u32,
                shared_memory_size: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK)?
                    as usize,
                supports_f64: true, // Most NVIDIA GPUs support f64
                supports_atomics: true,
                supports_subgroups: true,
                subgroup_size: self.get_attribute(device, CU_DEVICE_ATTRIBUTE_WARP_SIZE)? as u32,
            })
        }
    }

    fn alloc(&self, size: usize) -> GpuResult<BufferHandle> {
        let mut ptr: CUdeviceptr = 0;
        unsafe {
            cuda_check(cuMemAlloc_v2(&mut ptr, size))?;
        }

        let handle = self.next_handle();
        self.allocations.lock().unwrap().insert(handle, ptr);
        Ok(handle)
    }

    fn free(&self, handle: BufferHandle) -> GpuResult<()> {
        let ptr = self
            .allocations
            .lock()
            .unwrap()
            .remove(&handle)
            .ok_or(GpuError::InvalidBuffer)?;

        unsafe {
            cuda_check(cuMemFree_v2(ptr))?;
        }
        Ok(())
    }

    fn memcpy(&self, dst: *mut u8, src: *const u8, size: usize, kind: MemcpyKind) -> GpuResult<()> {
        unsafe {
            match kind {
                MemcpyKind::HostToDevice => {
                    cuda_check(cuMemcpyHtoD_v2(dst as CUdeviceptr, src as *const c_void, size))?;
                }
                MemcpyKind::DeviceToHost => {
                    cuda_check(cuMemcpyDtoH_v2(dst as *mut c_void, src as CUdeviceptr, size))?;
                }
                MemcpyKind::DeviceToDevice => {
                    cuda_check(cuMemcpyDtoD_v2(dst as CUdeviceptr, src as CUdeviceptr, size))?;
                }
                MemcpyKind::HostToHost => {
                    std::ptr::copy_nonoverlapping(src, dst, size);
                }
            }
        }
        Ok(())
    }

    fn memcpy_async(
        &self,
        dst: *mut u8,
        src: *const u8,
        size: usize,
        kind: MemcpyKind,
        stream: StreamHandle,
    ) -> GpuResult<()> {
        let cuda_stream = if stream == 0 {
            ptr::null_mut()
        } else {
            *self
                .streams
                .lock()
                .unwrap()
                .get(&stream)
                .ok_or(GpuError::InvalidStream)?
        };

        unsafe {
            match kind {
                MemcpyKind::HostToDevice => {
                    cuda_check(cuMemcpyHtoDAsync_v2(
                        dst as CUdeviceptr,
                        src as *const c_void,
                        size,
                        cuda_stream,
                    ))?;
                }
                MemcpyKind::DeviceToHost => {
                    cuda_check(cuMemcpyDtoHAsync_v2(
                        dst as *mut c_void,
                        src as CUdeviceptr,
                        size,
                        cuda_stream,
                    ))?;
                }
                _ => {
                    // Fallback to sync for other types
                    return self.memcpy(dst, src, size, kind);
                }
            }
        }
        Ok(())
    }

    fn memset(&self, handle: BufferHandle, value: u8, size: usize) -> GpuResult<()> {
        let ptr = *self
            .allocations
            .lock()
            .unwrap()
            .get(&handle)
            .ok_or(GpuError::InvalidBuffer)?;

        unsafe {
            cuda_check(cuMemsetD8_v2(ptr, value, size))?;
        }
        Ok(())
    }

    fn load_kernel(&self, source: &str, name: &str) -> GpuResult<KernelHandle> {
        // CUDA requires PTX or CUBIN, not source code
        // This would need NVRTC (NVIDIA Runtime Compilation) for source compilation
        Err(GpuError::BackendError(
            "CUDA backend requires PTX/CUBIN binary. Use load_kernel_binary() or compile with NVRTC first.".to_string(),
        ))
    }

    fn load_kernel_binary(&self, binary: &[u8], name: &str) -> GpuResult<KernelHandle> {
        let mut module: CUmodule = ptr::null_mut();
        let mut function: CUfunction = ptr::null_mut();

        unsafe {
            cuda_check(cuModuleLoadData(&mut module, binary.as_ptr() as *const c_void))?;

            let c_name =
                CString::new(name).map_err(|_| GpuError::InvalidArgument("Invalid kernel name".to_string()))?;
            cuda_check(cuModuleGetFunction(&mut function, module, c_name.as_ptr()))?;
        }

        let handle = self.next_handle();
        self.kernels
            .lock()
            .unwrap()
            .insert(handle, KernelInfo { module, function });
        Ok(handle)
    }

    fn unload_kernel(&self, handle: KernelHandle) -> GpuResult<()> {
        let info = self
            .kernels
            .lock()
            .unwrap()
            .remove(&handle)
            .ok_or(GpuError::InvalidKernel)?;

        unsafe {
            cuda_check(cuModuleUnload(info.module))?;
        }
        Ok(())
    }

    fn launch_kernel(
        &self,
        kernel: KernelHandle,
        grid_dim: [u32; 3],
        block_dim: [u32; 3],
        shared_mem: usize,
        stream: StreamHandle,
        args: &[*const c_void],
    ) -> GpuResult<()> {
        let info = self
            .kernels
            .lock()
            .unwrap()
            .get(&kernel)
            .ok_or(GpuError::InvalidKernel)?
            .function;

        let cuda_stream = if stream == 0 {
            ptr::null_mut()
        } else {
            *self
                .streams
                .lock()
                .unwrap()
                .get(&stream)
                .ok_or(GpuError::InvalidStream)?
        };

        unsafe {
            // Convert args to mutable pointers (CUDA API requirement)
            let mut kernel_params: Vec<*mut c_void> = args.iter().map(|&p| p as *mut c_void).collect();

            cuda_check(cuLaunchKernel(
                info,
                grid_dim[0],
                grid_dim[1],
                grid_dim[2],
                block_dim[0],
                block_dim[1],
                block_dim[2],
                shared_mem as u32,
                cuda_stream,
                kernel_params.as_mut_ptr(),
                ptr::null_mut(),
            ))?;
        }
        Ok(())
    }

    fn create_stream(&self) -> GpuResult<StreamHandle> {
        let mut stream: CUstream = ptr::null_mut();
        unsafe {
            cuda_check(cuStreamCreate(&mut stream, 0))?;
        }

        let handle = self.next_handle();
        self.streams.lock().unwrap().insert(handle, stream);
        Ok(handle)
    }

    fn destroy_stream(&self, handle: StreamHandle) -> GpuResult<()> {
        let stream = self
            .streams
            .lock()
            .unwrap()
            .remove(&handle)
            .ok_or(GpuError::InvalidStream)?;

        unsafe {
            cuda_check(cuStreamDestroy_v2(stream))?;
        }
        Ok(())
    }

    fn sync_stream(&self, handle: StreamHandle) -> GpuResult<()> {
        if handle == 0 {
            return self.sync_device();
        }

        let stream = *self
            .streams
            .lock()
            .unwrap()
            .get(&handle)
            .ok_or(GpuError::InvalidStream)?;

        unsafe {
            cuda_check(cuStreamSynchronize(stream))?;
        }
        Ok(())
    }

    fn sync_device(&self) -> GpuResult<()> {
        unsafe {
            cuda_check(cuCtxSynchronize())?;
        }
        Ok(())
    }

    fn create_event(&self) -> GpuResult<GpuEvent> {
        let mut event: CUevent = ptr::null_mut();
        unsafe {
            cuda_check(cuEventCreate(&mut event, 0))?;
        }

        let handle = self.next_handle();
        self.events.lock().unwrap().insert(handle, event);

        Ok(GpuEvent {
            handle,
            backend: GpuBackend::Cuda,
        })
    }

    fn destroy_event(&self, event: &GpuEvent) -> GpuResult<()> {
        let cuda_event = self
            .events
            .lock()
            .unwrap()
            .remove(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            cuda_check(cuEventDestroy_v2(cuda_event))?;
        }
        Ok(())
    }

    fn record_event(&self, event: &GpuEvent, stream: StreamHandle) -> GpuResult<()> {
        let cuda_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        let cuda_stream = if stream == 0 {
            ptr::null_mut()
        } else {
            *self
                .streams
                .lock()
                .unwrap()
                .get(&stream)
                .ok_or(GpuError::InvalidStream)?
        };

        unsafe {
            cuda_check(cuEventRecord(cuda_event, cuda_stream))?;
        }
        Ok(())
    }

    fn wait_event(&self, event: &GpuEvent) -> GpuResult<()> {
        let cuda_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            cuda_check(cuEventSynchronize(cuda_event))?;
        }
        Ok(())
    }

    fn query_event(&self, event: &GpuEvent) -> GpuResult<bool> {
        let cuda_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            let result = cuEventQuery(cuda_event);
            Ok(result == CUDA_SUCCESS)
        }
    }

    fn event_elapsed(&self, start: &GpuEvent, end: &GpuEvent) -> GpuResult<f32> {
        let start_event = *self
            .events
            .lock()
            .unwrap()
            .get(&start.handle)
            .ok_or(GpuError::InvalidEvent)?;

        let end_event = *self
            .events
            .lock()
            .unwrap()
            .get(&end.handle)
            .ok_or(GpuError::InvalidEvent)?;

        let mut elapsed: f32 = 0.0;
        unsafe {
            cuda_check(cuEventElapsedTime(&mut elapsed, start_event, end_event))?;
        }
        Ok(elapsed)
    }
}

impl Drop for CudaBackend {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

// Safety: CudaBackend uses Mutex for all shared state
unsafe impl Send for CudaBackend {}
unsafe impl Sync for CudaBackend {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cuda_backend_creation() {
        let backend = CudaBackend::new();
        assert_eq!(backend.backend_type(), GpuBackend::Cuda);
    }

    // Note: Most CUDA tests require actual CUDA hardware
    // These tests are compile-time checks only
}
