//! Swapchain management FFI functions
//!
//! Provides C-compatible FFI for Vulkan swapchain operations including creation,
//! recreation, image acquisition, and presentation.

use super::common::{next_handle, VulkanFfiError, DEVICE_REGISTRY, SWAPCHAIN_REGISTRY, WINDOW_SURFACES};

#[cfg(feature = "vulkan")]
use crate::vulkan::VulkanError;
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::sync::Arc;

/// Create a swapchain for rendering to a surface
///
/// # Arguments
/// * `device_handle` - Handle to the Vulkan device
/// * `surface_handle` - Handle to the window surface
/// * `width` - Swapchain width in pixels
/// * `height` - Swapchain height in pixels
/// * `prefer_hdr` - If non-zero, prefer HDR format
/// * `prefer_no_vsync` - If non-zero, prefer no vertical sync
///
/// # Returns
/// Positive swapchain handle on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_create(
    device_handle: u64,
    surface_handle: u64,
    width: u32,
    height: u32,
    prefer_hdr: i32,
    prefer_no_vsync: i32,
) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let device_registry = DEVICE_REGISTRY.lock();
        let surface_registry = WINDOW_SURFACES.lock();

        if let (Some(device), Some(surface)) = (
            device_registry.get(&device_handle),
            surface_registry.get(&surface_handle),
        ) {
            match crate::vulkan::VulkanSwapchain::new(
                device.clone(),
                surface,
                width,
                height,
                prefer_hdr != 0,
                prefer_no_vsync != 0,
            ) {
                Ok(swapchain_arc) => {
                    let handle = next_handle();
                    // VulkanSwapchain::new returns Arc<Self>, unwrap and re-wrap in Mutex
                    let swapchain = Arc::try_unwrap(swapchain_arc)
                        .unwrap_or_else(|_| panic!("Swapchain Arc should have only one reference"));
                    SWAPCHAIN_REGISTRY
                        .lock()
                        .insert(handle, Arc::new(Mutex::new(swapchain)));
                    tracing::info!("Swapchain created with handle {}", handle);
                    handle as i64
                }
                Err(e) => {
                    tracing::error!("Failed to create swapchain: {:?}", e);
                    VulkanFfiError::from(e) as i64
                }
            }
        } else {
            tracing::error!("Invalid device or surface handle");
            VulkanFfiError::InvalidHandle as i64
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i64
    }
}

/// Recreate swapchain (e.g., on window resize)
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain to recreate
/// * `surface_handle` - Handle to the window surface
/// * `width` - New width in pixels
/// * `height` - New height in pixels
///
/// # Returns
/// 0 (VulkanFfiError::Success) on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_recreate(swapchain_handle: u64, surface_handle: u64, width: u32, height: u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let swapchain_registry = SWAPCHAIN_REGISTRY.lock();
        let surface_registry = WINDOW_SURFACES.lock();

        if let (Some(swapchain_mutex), Some(surface)) = (
            swapchain_registry.get(&swapchain_handle).cloned(),
            surface_registry.get(&surface_handle).cloned(),
        ) {
            drop(swapchain_registry); // Release registry locks
            drop(surface_registry);

            let mut swapchain = swapchain_mutex.lock();
            match swapchain.recreate(&surface, width, height) {
                Ok(()) => {
                    tracing::info!("Swapchain {} recreated to {}x{}", swapchain_handle, width, height);
                    VulkanFfiError::Success as i32
                }
                Err(e) => {
                    tracing::error!("Failed to recreate swapchain {}: {:?}", swapchain_handle, e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Destroy a swapchain and release its resources
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain to destroy
///
/// # Returns
/// 0 (VulkanFfiError::Success) on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_destroy(swapchain_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let mut registry = SWAPCHAIN_REGISTRY.lock();
        if registry.remove(&swapchain_handle).is_some() {
            tracing::info!("Swapchain {} destroyed", swapchain_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid swapchain handle: {}", swapchain_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Acquire the next image from the swapchain for rendering
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain
/// * `timeout_ns` - Timeout in nanoseconds (use u64::MAX for infinite)
/// * `out_suboptimal` - Pointer to i32 output: set to 1 if swapchain is suboptimal, 0 otherwise
///
/// # Returns
/// Non-negative image index on success. If index > 1000, swapchain is suboptimal (should recreate).
/// Negative error code on failure.
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_acquire_next_image(
    swapchain_handle: u64,
    timeout_ns: u64,
    out_suboptimal: *mut i32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_suboptimal.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            match swapchain.acquire_next_image(None, timeout_ns) {
                Ok((index, suboptimal)) => {
                    unsafe {
                        *out_suboptimal = if suboptimal { 1 } else { 0 };
                    }
                    index as i32
                }
                Err(VulkanError::SwapchainOutOfDate) => {
                    tracing::warn!("Swapchain out of date");
                    VulkanFfiError::SurfaceError as i32
                }
                Err(e) => {
                    tracing::error!("Failed to acquire next image: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Present a rendered image to the screen
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain
/// * `image_index` - Index of the image to present
///
/// # Returns
/// - 0 (VulkanFfiError::Success) on successful presentation
/// - 1 if swapchain needs recreation (e.g., due to surface changes)
/// - Negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_present(swapchain_handle: u64, image_index: u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            match swapchain.present(image_index, &[]) {
                Ok(needs_recreation) => {
                    if needs_recreation {
                        tracing::info!("Swapchain needs recreation");
                        1 // Needs recreation
                    } else {
                        VulkanFfiError::Success as i32
                    }
                }
                Err(e) => {
                    tracing::error!("Failed to present: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get the number of images in the swapchain
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain
///
/// # Returns
/// Non-negative image count on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_get_image_count(swapchain_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            swapchain.image_count() as i32
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get the dimensions (width and height) of the swapchain
///
/// # Arguments
/// * `swapchain_handle` - Handle to the swapchain
/// * `out_width` - Pointer to u32 output for width
/// * `out_height` - Pointer to u32 output for height
///
/// # Returns
/// 0 (VulkanFfiError::Success) on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_get_extent(swapchain_handle: u64, out_width: *mut u32, out_height: *mut u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_width.is_null() || out_height.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            unsafe {
                *out_width = swapchain.width();
                *out_height = swapchain.height();
            }
            VulkanFfiError::Success as i32
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}
