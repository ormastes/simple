//! GPU Device Discovery and Information

use crate::error::{GpuError, GpuResult};

/// GPU backend type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GpuBackend {
    /// WebGPU-based backend (cross-platform).
    Wgpu,
    /// NVIDIA CUDA backend.
    Cuda,
    /// Apple Metal backend.
    Metal,
    /// Vulkan compute backend.
    Vulkan,
    /// Software fallback (CPU).
    Software,
}

impl GpuBackend {
    /// Check if this backend is available on the current system.
    pub fn is_available(&self) -> bool {
        match self {
            GpuBackend::Software => true,
            // Other backends would check for actual availability
            _ => false, // Stub - would check actual backend availability
        }
    }
}

/// GPU device capabilities.
#[derive(Debug, Clone)]
pub struct DeviceCapabilities {
    /// Maximum work group size (x dimension).
    pub max_work_group_size_x: u32,
    /// Maximum work group size (y dimension).
    pub max_work_group_size_y: u32,
    /// Maximum work group size (z dimension).
    pub max_work_group_size_z: u32,
    /// Maximum total work group size (x * y * z).
    pub max_work_group_invocations: u32,
    /// Maximum number of work groups (x dimension).
    pub max_work_groups_x: u32,
    /// Maximum number of work groups (y dimension).
    pub max_work_groups_y: u32,
    /// Maximum number of work groups (z dimension).
    pub max_work_groups_z: u32,
    /// Shared memory size in bytes.
    pub shared_memory_size: usize,
    /// Whether the device supports 64-bit floats.
    pub supports_f64: bool,
    /// Whether the device supports atomic operations.
    pub supports_atomics: bool,
    /// Whether the device supports subgroups (warp-level operations).
    pub supports_subgroups: bool,
    /// Subgroup size (warp size on NVIDIA, wavefront on AMD).
    pub subgroup_size: u32,
}

impl Default for DeviceCapabilities {
    fn default() -> Self {
        DeviceCapabilities {
            max_work_group_size_x: 1024,
            max_work_group_size_y: 1024,
            max_work_group_size_z: 64,
            max_work_group_invocations: 1024,
            max_work_groups_x: 65535,
            max_work_groups_y: 65535,
            max_work_groups_z: 65535,
            shared_memory_size: 48 * 1024, // 48 KB
            supports_f64: false,
            supports_atomics: true,
            supports_subgroups: true,
            subgroup_size: 32,
        }
    }
}

/// Represents a GPU device.
#[derive(Debug, Clone)]
pub struct Device {
    /// Device ID.
    pub id: u32,
    /// Device name.
    pub name: String,
    /// Device vendor.
    pub vendor: String,
    /// Backend type.
    pub backend: GpuBackend,
    /// Total device memory in bytes.
    pub memory_bytes: u64,
    /// Device capabilities.
    pub capabilities: DeviceCapabilities,
    /// Whether this is the default device.
    pub is_default: bool,
}

impl Device {
    /// Create a software fallback device.
    pub fn software() -> Self {
        Device {
            id: 0,
            name: "Software Renderer".to_string(),
            vendor: "Simple".to_string(),
            backend: GpuBackend::Software,
            memory_bytes: 0,
            capabilities: DeviceCapabilities::default(),
            is_default: true,
        }
    }

    /// Get device memory in megabytes.
    pub fn memory_mb(&self) -> u64 {
        self.memory_bytes / (1024 * 1024)
    }

    /// Check if device supports 64-bit floats.
    pub fn supports_f64(&self) -> bool {
        self.capabilities.supports_f64
    }

    /// Get shared memory size in bytes.
    pub fn shared_memory_size(&self) -> usize {
        self.capabilities.shared_memory_size
    }

    /// Check if device supports atomic operations.
    pub fn supports_atomics(&self) -> bool {
        self.capabilities.supports_atomics
    }
}

/// Discover available GPU devices.
pub fn devices() -> Vec<Device> {
    // In a real implementation, this would query the actual GPU backends
    // For now, return a software fallback device
    vec![Device::software()]
}

/// Get the default GPU device.
pub fn default_device() -> GpuResult<Device> {
    devices()
        .into_iter()
        .find(|d| d.is_default)
        .ok_or(GpuError::NoDeviceFound)
}

/// Check if any GPU is available.
pub fn gpu_available() -> bool {
    !devices().is_empty()
}

/// Check if a specific backend is available.
pub fn backend_available(backend: GpuBackend) -> bool {
    devices().iter().any(|d| d.backend == backend)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_device() {
        let device = Device::software();
        assert_eq!(device.backend, GpuBackend::Software);
        assert!(device.is_default);
    }

    #[test]
    fn test_devices() {
        let devs = devices();
        assert!(!devs.is_empty());
    }

    #[test]
    fn test_default_device() {
        let device = default_device();
        assert!(device.is_ok());
    }

    #[test]
    fn test_gpu_available() {
        // Software fallback is always available
        assert!(gpu_available());
    }

    #[test]
    fn test_capabilities() {
        let caps = DeviceCapabilities::default();
        assert!(caps.max_work_group_invocations > 0);
        assert!(caps.shared_memory_size > 0);
    }
}
