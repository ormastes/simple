//! GPU Backend Selection and Abstraction
//!
//! Provides a unified interface for selecting and managing different GPU backends:
//! - CPU: Software emulation (always available)
//! - Vulkan: Cross-platform GPU (requires Vulkan drivers)
//! - CUDA: NVIDIA GPU (requires CUDA toolkit)
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────┐
//! │       Simple Language Code           │
//! │  gpu::set_backend(BackendType)       │
//! └──────────────────────────────────────┘
//!              │
//!              ▼
//! ┌──────────────────────────────────────┐
//! │      GpuBackend Abstraction          │
//! │  • detect_available()                │
//! │  • select_backend()                  │
//! │  • get_current()                     │
//! └──────────────────────────────────────┘
//!         │           │           │
//!    ┌────┴────┐ ┌────┴────┐ ┌───┴────┐
//!    ▼         ▼         ▼         ▼
//! ┌─────┐ ┌────────┐ ┌──────┐ ┌──────┐
//! │ CPU │ │ Vulkan │ │ CUDA │ │Auto│
//! └─────┘ └────────┘ └──────┘ └──────┘
//! ```
//!
//! # Usage
//!
//! ```simple
//! import gpu
//!
//! # Auto-select best available backend
//! gpu.set_backend(gpu.Backend.Auto)
//!
//! # Explicitly select Vulkan
//! gpu.set_backend(gpu.Backend.Vulkan)
//!
//! # Check current backend
//! let current = gpu.get_backend()
//! print(f"Using {current} backend")
//!
//! # List available backends
//! let backends = gpu.available_backends()
//! for backend in backends:
//!     print(f"  - {backend}")
//! ```

use parking_lot::RwLock;

/// GPU backend types
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuBackendType {
    /// Software CPU emulation (always available)
    Cpu = 0,
    /// Cross-platform Vulkan GPU backend
    Vulkan = 1,
    /// NVIDIA CUDA GPU backend
    Cuda = 2,
    /// Auto-select best available backend
    Auto = 99,
}

impl GpuBackendType {
    /// Convert from i32 (for FFI)
    pub fn from_i32(value: i32) -> Option<Self> {
        match value {
            0 => Some(GpuBackendType::Cpu),
            1 => Some(GpuBackendType::Vulkan),
            2 => Some(GpuBackendType::Cuda),
            99 => Some(GpuBackendType::Auto),
            _ => None,
        }
    }

    /// Check if this backend is available on the current system
    pub fn is_available(&self) -> bool {
        match self {
            GpuBackendType::Cpu => true, // Always available
            GpuBackendType::Vulkan => {
                #[cfg(feature = "vulkan")]
                {
                    crate::vulkan::is_available()
                }
                #[cfg(not(feature = "vulkan"))]
                {
                    false
                }
            }
            GpuBackendType::Cuda => {
                #[cfg(feature = "cuda")]
                {
                    // Check if CUDA is available by trying to initialize
                    // In a real implementation, this would check CUDA availability
                    false // CUDA support not fully implemented
                }
                #[cfg(not(feature = "cuda"))]
                {
                    false
                }
            }
            GpuBackendType::Auto => true, // Auto always "available" (fallback to CPU)
        }
    }

    /// Get human-readable name
    pub fn name(&self) -> &'static str {
        match self {
            GpuBackendType::Cpu => "CPU",
            GpuBackendType::Vulkan => "Vulkan",
            GpuBackendType::Cuda => "CUDA",
            GpuBackendType::Auto => "Auto",
        }
    }

    /// Get priority for auto-selection (higher = better)
    pub fn priority(&self) -> i32 {
        match self {
            GpuBackendType::Cpu => 0,     // Fallback
            GpuBackendType::Vulkan => 10, // Preferred for graphics
            GpuBackendType::Cuda => 20,   // Best for compute if available
            GpuBackendType::Auto => -1,   // Not a real backend
        }
    }
}

/// Global backend selection state
static SELECTED_BACKEND: RwLock<GpuBackendType> = RwLock::new(GpuBackendType::Cpu);

/// GPU Backend Manager
pub struct GpuBackendManager;

impl GpuBackendManager {
    /// Detect all available backends
    pub fn detect_available() -> Vec<GpuBackendType> {
        let mut backends = Vec::new();

        if GpuBackendType::Cpu.is_available() {
            backends.push(GpuBackendType::Cpu);
        }
        if GpuBackendType::Vulkan.is_available() {
            backends.push(GpuBackendType::Vulkan);
        }
        if GpuBackendType::Cuda.is_available() {
            backends.push(GpuBackendType::Cuda);
        }

        backends
    }

    /// Auto-select the best available backend
    pub fn auto_select() -> GpuBackendType {
        let available = Self::detect_available();

        // Sort by priority (highest first)
        available
            .into_iter()
            .max_by_key(|b| b.priority())
            .unwrap_or(GpuBackendType::Cpu)
    }

    /// Set the current backend
    ///
    /// If backend type is Auto, automatically selects the best available backend.
    /// Returns the actually selected backend.
    pub fn set_backend(backend: GpuBackendType) -> Result<GpuBackendType, String> {
        let selected = match backend {
            GpuBackendType::Auto => Self::auto_select(),
            _ => {
                if !backend.is_available() {
                    return Err(format!(
                        "{} backend is not available on this system",
                        backend.name()
                    ));
                }
                backend
            }
        };

        *SELECTED_BACKEND.write() = selected;
        tracing::info!("GPU backend set to: {:?}", selected);
        Ok(selected)
    }

    /// Get the currently selected backend
    pub fn get_backend() -> GpuBackendType {
        *SELECTED_BACKEND.read()
    }

    /// Check if a specific backend is currently selected
    pub fn is_using(&self, backend: GpuBackendType) -> bool {
        Self::get_backend() == backend
    }

    /// Get backend information as a string
    pub fn get_info() -> String {
        let current = Self::get_backend();
        let available = Self::detect_available();

        format!(
            "Current: {} | Available: {}",
            current.name(),
            available
                .iter()
                .map(|b| b.name())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

// =============================================================================
// FFI Functions for Backend Selection
// =============================================================================

/// Get list of available backends
///
/// Returns count of available backends, writes backend IDs to out_backends array
/// out_backends: Array to write backend IDs (0=CPU, 1=Vulkan, 2=CUDA)
/// max_count: Maximum number of backends to write
///
/// Returns: Number of available backends
#[no_mangle]
pub extern "C" fn rt_gpu_backend_available(out_backends: *mut i32, max_count: u32) -> i32 {
    let available = GpuBackendManager::detect_available();

    if !out_backends.is_null() {
        let count = available.len().min(max_count as usize);
        unsafe {
            for (i, backend) in available.iter().take(count).enumerate() {
                *out_backends.add(i) = *backend as i32;
            }
        }
    }

    available.len() as i32
}

/// Set the GPU backend
///
/// backend: Backend type (0=CPU, 1=Vulkan, 2=CUDA, 99=Auto)
///
/// Returns: Actually selected backend ID on success, negative error code on failure
/// Error codes: -1 = invalid backend ID, -2 = backend not available
#[no_mangle]
pub extern "C" fn rt_gpu_backend_set(backend: i32) -> i32 {
    match GpuBackendType::from_i32(backend) {
        Some(backend_type) => match GpuBackendManager::set_backend(backend_type) {
            Ok(selected) => {
                tracing::info!("Selected GPU backend: {:?}", selected);
                selected as i32
            }
            Err(e) => {
                tracing::error!("Failed to set GPU backend: {}", e);
                -2 // Backend not available
            }
        },
        None => {
            tracing::error!("Invalid GPU backend ID: {}", backend);
            -1 // Invalid backend ID
        }
    }
}

/// Get the currently selected GPU backend
///
/// Returns: Backend ID (0=CPU, 1=Vulkan, 2=CUDA)
#[no_mangle]
pub extern "C" fn rt_gpu_backend_get() -> i32 {
    GpuBackendManager::get_backend() as i32
}

/// Check if a specific backend is available
///
/// backend: Backend type to check (0=CPU, 1=Vulkan, 2=CUDA)
///
/// Returns: 1 if available, 0 if not available, -1 if invalid backend ID
#[no_mangle]
pub extern "C" fn rt_gpu_backend_is_available(backend: i32) -> i32 {
    match GpuBackendType::from_i32(backend) {
        Some(backend_type) => {
            if backend_type.is_available() {
                1
            } else {
                0
            }
        }
        None => -1, // Invalid backend ID
    }
}

/// Get backend name as string
///
/// backend: Backend type (0=CPU, 1=Vulkan, 2=CUDA)
/// out_buffer: Buffer to write name string
/// buffer_len: Length of buffer
///
/// Returns: Length of name string (excluding null terminator), or -1 on error
#[no_mangle]
pub extern "C" fn rt_gpu_backend_name(backend: i32, out_buffer: *mut u8, buffer_len: u32) -> i32 {
    if out_buffer.is_null() || buffer_len == 0 {
        return -1;
    }

    match GpuBackendType::from_i32(backend) {
        Some(backend_type) => {
            let name = backend_type.name();
            let name_bytes = name.as_bytes();
            let copy_len = name_bytes.len().min((buffer_len - 1) as usize);

            unsafe {
                std::ptr::copy_nonoverlapping(name_bytes.as_ptr(), out_buffer, copy_len);
                *out_buffer.add(copy_len) = 0; // Null terminator
            }

            name_bytes.len() as i32
        }
        None => -1,
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backend_type_conversion() {
        assert_eq!(GpuBackendType::from_i32(0), Some(GpuBackendType::Cpu));
        assert_eq!(GpuBackendType::from_i32(1), Some(GpuBackendType::Vulkan));
        assert_eq!(GpuBackendType::from_i32(2), Some(GpuBackendType::Cuda));
        assert_eq!(GpuBackendType::from_i32(99), Some(GpuBackendType::Auto));
        assert_eq!(GpuBackendType::from_i32(100), None);
    }

    #[test]
    fn test_cpu_always_available() {
        assert!(GpuBackendType::Cpu.is_available());
    }

    #[test]
    fn test_detect_available() {
        let backends = GpuBackendManager::detect_available();
        assert!(!backends.is_empty());
        assert!(backends.contains(&GpuBackendType::Cpu));
    }

    #[test]
    fn test_auto_select() {
        let backend = GpuBackendManager::auto_select();
        assert!(backend.is_available());
        assert_ne!(backend, GpuBackendType::Auto);
    }

    #[test]
    fn test_set_get_backend() {
        let result = GpuBackendManager::set_backend(GpuBackendType::Cpu);
        assert!(result.is_ok());
        assert_eq!(GpuBackendManager::get_backend(), GpuBackendType::Cpu);
    }

    #[test]
    fn test_set_backend_auto() {
        let result = GpuBackendManager::set_backend(GpuBackendType::Auto);
        assert!(result.is_ok());
        let selected = result.unwrap();
        assert_ne!(selected, GpuBackendType::Auto);
        assert!(selected.is_available());
    }

    #[test]
    fn test_backend_priority() {
        assert!(GpuBackendType::Cuda.priority() > GpuBackendType::Vulkan.priority());
        assert!(GpuBackendType::Vulkan.priority() > GpuBackendType::Cpu.priority());
    }

    #[test]
    fn test_backend_names() {
        assert_eq!(GpuBackendType::Cpu.name(), "CPU");
        assert_eq!(GpuBackendType::Vulkan.name(), "Vulkan");
        assert_eq!(GpuBackendType::Cuda.name(), "CUDA");
        assert_eq!(GpuBackendType::Auto.name(), "Auto");
    }

    #[test]
    fn test_ffi_backend_available() {
        let mut backends = [0i32; 10];
        let count = rt_gpu_backend_available(backends.as_mut_ptr(), 10);
        assert!(count > 0);
        assert!(count <= 10);
    }

    #[test]
    fn test_ffi_backend_set_get() {
        let result = rt_gpu_backend_set(0); // CPU
        assert!(result >= 0);
        assert_eq!(rt_gpu_backend_get(), 0);
    }

    #[test]
    fn test_ffi_backend_is_available() {
        assert_eq!(rt_gpu_backend_is_available(0), 1); // CPU always available
        assert!(rt_gpu_backend_is_available(100) < 0); // Invalid ID
    }

    #[test]
    fn test_ffi_backend_name() {
        let mut buffer = [0u8; 32];
        let len = rt_gpu_backend_name(0, buffer.as_mut_ptr(), 32);
        assert!(len > 0);

        let name = std::str::from_utf8(&buffer[..len as usize]).unwrap();
        assert_eq!(name, "CPU");
    }

    #[test]
    fn test_ffi_backend_name_null_buffer() {
        let len = rt_gpu_backend_name(0, std::ptr::null_mut(), 32);
        assert_eq!(len, -1);
    }

    #[test]
    fn test_ffi_backend_name_zero_length() {
        let mut buffer = [0u8; 32];
        let len = rt_gpu_backend_name(0, buffer.as_mut_ptr(), 0);
        assert_eq!(len, -1);
    }
}
