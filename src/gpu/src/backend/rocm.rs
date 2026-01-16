//! ROCm/HIP Backend Implementation
//!
//! AMD ROCm backend using the HIP runtime API.
//! HIP provides a CUDA-like API that works on both AMD and NVIDIA GPUs.

use std::collections::HashMap;
use std::ffi::{c_void, CString};
use std::ptr;
use std::sync::Mutex;

use super::{Backend, BufferHandle, GpuEvent, KernelHandle, MemcpyKind, StreamHandle};
use crate::device::{Device, DeviceCapabilities, GpuBackend};
use crate::error::{GpuError, GpuResult};

// HIP types (mirror CUDA types)
type HipDevice = i32;
type HipModule = *mut c_void;
type HipFunction = *mut c_void;
type HipStream = *mut c_void;
type HipEvent = *mut c_void;
type HipDeviceptr = *mut c_void;
type HipError = i32;

// HIP error codes
const HIP_SUCCESS: HipError = 0;

// HIP device attributes
const HIP_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK: i32 = 1;
const HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_X: i32 = 2;
const HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Y: i32 = 3;
const HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Z: i32 = 4;
const HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_X: i32 = 5;
const HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Y: i32 = 6;
const HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Z: i32 = 7;
const HIP_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK: i32 = 8;
const HIP_DEVICE_ATTRIBUTE_WARP_SIZE: i32 = 10;

// HIP memory copy kinds
const HIP_MEMCPY_HOST_TO_DEVICE: i32 = 1;
const HIP_MEMCPY_DEVICE_TO_HOST: i32 = 2;
const HIP_MEMCPY_DEVICE_TO_DEVICE: i32 = 3;
const HIP_MEMCPY_HOST_TO_HOST: i32 = 4;

// HIP Runtime API FFI
#[link(name = "amdhip64")]
extern "C" {
    fn hipInit(flags: u32) -> HipError;
    fn hipGetDeviceCount(count: *mut i32) -> HipError;
    fn hipSetDevice(deviceId: i32) -> HipError;
    fn hipGetDevice(deviceId: *mut i32) -> HipError;
    fn hipDeviceGetName(name: *mut i8, len: i32, device: HipDevice) -> HipError;
    fn hipDeviceGetAttribute(pi: *mut i32, attrib: i32, deviceId: i32) -> HipError;
    fn hipDeviceTotalMem(bytes: *mut usize, device: HipDevice) -> HipError;
    fn hipDeviceSynchronize() -> HipError;
    fn hipMalloc(ptr: *mut HipDeviceptr, size: usize) -> HipError;
    fn hipFree(ptr: HipDeviceptr) -> HipError;
    fn hipMemcpy(dst: *mut c_void, src: *const c_void, size: usize, kind: i32) -> HipError;
    fn hipMemcpyAsync(dst: *mut c_void, src: *const c_void, size: usize, kind: i32, stream: HipStream) -> HipError;
    fn hipMemset(dst: HipDeviceptr, value: i32, size: usize) -> HipError;
    fn hipModuleLoad(module: *mut HipModule, fname: *const i8) -> HipError;
    fn hipModuleLoadData(module: *mut HipModule, image: *const c_void) -> HipError;
    fn hipModuleUnload(module: HipModule) -> HipError;
    fn hipModuleGetFunction(function: *mut HipFunction, module: HipModule, name: *const i8) -> HipError;
    fn hipModuleLaunchKernel(
        f: HipFunction,
        gridDimX: u32,
        gridDimY: u32,
        gridDimZ: u32,
        blockDimX: u32,
        blockDimY: u32,
        blockDimZ: u32,
        sharedMemBytes: u32,
        stream: HipStream,
        kernelParams: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> HipError;
    fn hipStreamCreate(stream: *mut HipStream) -> HipError;
    fn hipStreamDestroy(stream: HipStream) -> HipError;
    fn hipStreamSynchronize(stream: HipStream) -> HipError;
    fn hipEventCreate(event: *mut HipEvent) -> HipError;
    fn hipEventDestroy(event: HipEvent) -> HipError;
    fn hipEventRecord(event: HipEvent, stream: HipStream) -> HipError;
    fn hipEventSynchronize(event: HipEvent) -> HipError;
    fn hipEventQuery(event: HipEvent) -> HipError;
    fn hipEventElapsedTime(ms: *mut f32, start: HipEvent, stop: HipEvent) -> HipError;
}

/// Convert HIP result to GpuResult.
fn hip_check(result: HipError) -> GpuResult<()> {
    if result == HIP_SUCCESS {
        Ok(())
    } else {
        Err(GpuError::BackendError(format!("HIP/ROCm error: {}", result)))
    }
}

/// Kernel info stored for launching.
struct KernelInfo {
    module: HipModule,
    function: HipFunction,
}

/// ROCm/HIP backend implementation.
pub struct RocmBackend {
    initialized: bool,
    device_count: i32,
    current_device: usize,
    /// Buffer handle to device pointer mapping.
    allocations: Mutex<HashMap<BufferHandle, HipDeviceptr>>,
    /// Kernel handle to kernel info mapping.
    kernels: Mutex<HashMap<KernelHandle, KernelInfo>>,
    /// Stream handle to HIP stream mapping.
    streams: Mutex<HashMap<StreamHandle, HipStream>>,
    /// Event handle to HIP event mapping.
    events: Mutex<HashMap<u64, HipEvent>>,
    next_handle: std::sync::atomic::AtomicU64,
}

impl RocmBackend {
    /// Create a new ROCm/HIP backend.
    pub fn new() -> Self {
        RocmBackend {
            initialized: false,
            device_count: 0,
            current_device: 0,
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
    fn get_attribute(&self, device: HipDevice, attrib: i32) -> GpuResult<i32> {
        let mut value: i32 = 0;
        unsafe {
            hip_check(hipDeviceGetAttribute(&mut value, attrib, device))?;
        }
        Ok(value)
    }
}

impl Default for RocmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for RocmBackend {
    fn backend_type(&self) -> GpuBackend {
        GpuBackend::Rocm
    }

    fn init(&mut self) -> GpuResult<()> {
        if self.initialized {
            return Ok(());
        }

        unsafe {
            // Initialize HIP
            let result = hipInit(0);
            if result != HIP_SUCCESS {
                return Err(GpuError::BackendError("Failed to initialize HIP/ROCm".to_string()));
            }

            // Get device count
            hip_check(hipGetDeviceCount(&mut self.device_count))?;

            if self.device_count == 0 {
                return Err(GpuError::NoDeviceFound);
            }

            // Set first device
            hip_check(hipSetDevice(0))?;
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
                    let _ = hipFree(ptr);
                }
            }
        }
        self.allocations.lock().unwrap().clear();

        // Unload all kernels
        {
            let kernels = self.kernels.lock().unwrap();
            for info in kernels.values() {
                unsafe {
                    let _ = hipModuleUnload(info.module);
                }
            }
        }
        self.kernels.lock().unwrap().clear();

        // Destroy all streams
        {
            let streams = self.streams.lock().unwrap();
            for &stream in streams.values() {
                unsafe {
                    let _ = hipStreamDestroy(stream);
                }
            }
        }
        self.streams.lock().unwrap().clear();

        // Destroy all events
        {
            let events = self.events.lock().unwrap();
            for &event in events.values() {
                unsafe {
                    let _ = hipEventDestroy(event);
                }
            }
        }
        self.events.lock().unwrap().clear();

        self.initialized = false;
        Ok(())
    }

    fn is_available(&self) -> bool {
        unsafe {
            let result = hipInit(0);
            if result != HIP_SUCCESS {
                return false;
            }

            let mut count: i32 = 0;
            if hipGetDeviceCount(&mut count) != HIP_SUCCESS {
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
            let device = index as HipDevice;

            // Get device name
            let mut name_buf = [0i8; 256];
            hip_check(hipDeviceGetName(name_buf.as_mut_ptr(), 256, device))?;
            let name = std::ffi::CStr::from_ptr(name_buf.as_ptr())
                .to_string_lossy()
                .into_owned();

            // Get total memory
            let mut total_mem: usize = 0;
            hip_check(hipDeviceTotalMem(&mut total_mem, device))?;

            // Get capabilities
            let caps = self.get_capabilities(index)?;

            Ok(Device {
                id: index as u32,
                name,
                vendor: "AMD".to_string(),
                backend: GpuBackend::Rocm,
                memory_bytes: total_mem as u64,
                capabilities: caps,
                is_default: index == 0,
            })
        }
    }

    fn set_device(&mut self, index: usize) -> GpuResult<()> {
        if index >= self.device_count as usize {
            return Err(GpuError::InvalidDevice(index));
        }

        unsafe {
            hip_check(hipSetDevice(index as i32))?;
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

        let device = index as HipDevice;

        Ok(DeviceCapabilities {
            max_work_group_size_x: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_X)? as u32,
            max_work_group_size_y: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Y)? as u32,
            max_work_group_size_z: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Z)? as u32,
            max_work_group_invocations: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK)? as u32,
            max_work_groups_x: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_X)? as u32,
            max_work_groups_y: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Y)? as u32,
            max_work_groups_z: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_GRID_DIM_Z)? as u32,
            shared_memory_size: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK)? as usize,
            supports_f64: true, // Most AMD GPUs support f64
            supports_atomics: true,
            supports_subgroups: true,
            subgroup_size: self.get_attribute(device, HIP_DEVICE_ATTRIBUTE_WARP_SIZE)? as u32, // Wavefront size (64 on AMD)
        })
    }

    fn alloc(&self, size: usize) -> GpuResult<BufferHandle> {
        let mut ptr: HipDeviceptr = ptr::null_mut();
        unsafe {
            hip_check(hipMalloc(&mut ptr, size))?;
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
            hip_check(hipFree(ptr))?;
        }
        Ok(())
    }

    fn memcpy(&self, dst: *mut u8, src: *const u8, size: usize, kind: MemcpyKind) -> GpuResult<()> {
        let hip_kind = match kind {
            MemcpyKind::HostToDevice => HIP_MEMCPY_HOST_TO_DEVICE,
            MemcpyKind::DeviceToHost => HIP_MEMCPY_DEVICE_TO_HOST,
            MemcpyKind::DeviceToDevice => HIP_MEMCPY_DEVICE_TO_DEVICE,
            MemcpyKind::HostToHost => HIP_MEMCPY_HOST_TO_HOST,
        };

        unsafe {
            hip_check(hipMemcpy(dst as *mut c_void, src as *const c_void, size, hip_kind))?;
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
        let hip_stream = if stream == 0 {
            ptr::null_mut()
        } else {
            *self
                .streams
                .lock()
                .unwrap()
                .get(&stream)
                .ok_or(GpuError::InvalidStream)?
        };

        let hip_kind = match kind {
            MemcpyKind::HostToDevice => HIP_MEMCPY_HOST_TO_DEVICE,
            MemcpyKind::DeviceToHost => HIP_MEMCPY_DEVICE_TO_HOST,
            MemcpyKind::DeviceToDevice => HIP_MEMCPY_DEVICE_TO_DEVICE,
            MemcpyKind::HostToHost => HIP_MEMCPY_HOST_TO_HOST,
        };

        unsafe {
            hip_check(hipMemcpyAsync(
                dst as *mut c_void,
                src as *const c_void,
                size,
                hip_kind,
                hip_stream,
            ))?;
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
            hip_check(hipMemset(ptr, value as i32, size))?;
        }
        Ok(())
    }

    fn load_kernel(&self, _source: &str, _name: &str) -> GpuResult<KernelHandle> {
        // HIP requires compiled binary (HIP-Clang output)
        Err(GpuError::BackendError(
            "ROCm/HIP backend requires compiled binary. Use load_kernel_binary() or compile with hipcc first."
                .to_string(),
        ))
    }

    fn load_kernel_binary(&self, binary: &[u8], name: &str) -> GpuResult<KernelHandle> {
        let mut module: HipModule = ptr::null_mut();
        let mut function: HipFunction = ptr::null_mut();

        unsafe {
            hip_check(hipModuleLoadData(&mut module, binary.as_ptr() as *const c_void))?;

            let c_name =
                CString::new(name).map_err(|_| GpuError::InvalidArgument("Invalid kernel name".to_string()))?;
            hip_check(hipModuleGetFunction(&mut function, module, c_name.as_ptr()))?;
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
            hip_check(hipModuleUnload(info.module))?;
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

        let hip_stream = if stream == 0 {
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
            let mut kernel_params: Vec<*mut c_void> = args.iter().map(|&p| p as *mut c_void).collect();

            hip_check(hipModuleLaunchKernel(
                info,
                grid_dim[0],
                grid_dim[1],
                grid_dim[2],
                block_dim[0],
                block_dim[1],
                block_dim[2],
                shared_mem as u32,
                hip_stream,
                kernel_params.as_mut_ptr(),
                ptr::null_mut(),
            ))?;
        }
        Ok(())
    }

    fn create_stream(&self) -> GpuResult<StreamHandle> {
        let mut stream: HipStream = ptr::null_mut();
        unsafe {
            hip_check(hipStreamCreate(&mut stream))?;
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
            hip_check(hipStreamDestroy(stream))?;
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
            hip_check(hipStreamSynchronize(stream))?;
        }
        Ok(())
    }

    fn sync_device(&self) -> GpuResult<()> {
        unsafe {
            hip_check(hipDeviceSynchronize())?;
        }
        Ok(())
    }

    fn create_event(&self) -> GpuResult<GpuEvent> {
        let mut event: HipEvent = ptr::null_mut();
        unsafe {
            hip_check(hipEventCreate(&mut event))?;
        }

        let handle = self.next_handle();
        self.events.lock().unwrap().insert(handle, event);

        Ok(GpuEvent {
            handle,
            backend: GpuBackend::Rocm,
        })
    }

    fn destroy_event(&self, event: &GpuEvent) -> GpuResult<()> {
        let hip_event = self
            .events
            .lock()
            .unwrap()
            .remove(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            hip_check(hipEventDestroy(hip_event))?;
        }
        Ok(())
    }

    fn record_event(&self, event: &GpuEvent, stream: StreamHandle) -> GpuResult<()> {
        let hip_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        let hip_stream = if stream == 0 {
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
            hip_check(hipEventRecord(hip_event, hip_stream))?;
        }
        Ok(())
    }

    fn wait_event(&self, event: &GpuEvent) -> GpuResult<()> {
        let hip_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            hip_check(hipEventSynchronize(hip_event))?;
        }
        Ok(())
    }

    fn query_event(&self, event: &GpuEvent) -> GpuResult<bool> {
        let hip_event = *self
            .events
            .lock()
            .unwrap()
            .get(&event.handle)
            .ok_or(GpuError::InvalidEvent)?;

        unsafe {
            let result = hipEventQuery(hip_event);
            Ok(result == HIP_SUCCESS)
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
            hip_check(hipEventElapsedTime(&mut elapsed, start_event, end_event))?;
        }
        Ok(elapsed)
    }
}

impl Drop for RocmBackend {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

// Safety: RocmBackend uses Mutex for all shared state
unsafe impl Send for RocmBackend {}
unsafe impl Sync for RocmBackend {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rocm_backend_creation() {
        let backend = RocmBackend::new();
        assert_eq!(backend.backend_type(), GpuBackend::Rocm);
    }

    // Note: Most ROCm tests require actual AMD hardware
    // These tests are compile-time checks only
}
