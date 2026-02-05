//! Image and sampler FFI functions for Vulkan
//!
//! Provides FFI functions for image and sampler management.

use super::common::VulkanFfiError;

#[cfg(feature = "vulkan")]
use super::common::{next_handle, DEVICE_REGISTRY, IMAGE_REGISTRY, SAMPLER_REGISTRY};
#[cfg(feature = "vulkan")]
use crate::vulkan::image::{AddressMode, FilterMode, ImageUsage, Sampler, VulkanImage};
#[cfg(feature = "vulkan")]
use ash::vk;
#[cfg(feature = "vulkan")]
use ash::vk::Handle;

// =============================================================================
// Image FFI
// =============================================================================

/// Create a 2D image.
///
/// # Parameters
/// - `device`: Device handle
/// - `width`: Image width
/// - `height`: Image height
/// - `format`: Image format (vk::Format as u32)
/// - `usage`: Image usage flags (0 = texture, 1 = storage, 2 = color_attachment)
///
/// # Returns
/// Image handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_image_create_2d(device: u64, width: u32, height: u32, format: u32, usage: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let fmt = vk::Format::from_raw(format as i32);
        let img_usage = match usage {
            0 => ImageUsage::texture(),
            1 => ImageUsage::storage(),
            2 => ImageUsage::color_attachment(),
            3 => ImageUsage::depth_stencil(),
            _ => {
                tracing::error!("Invalid image usage: {}", usage);
                return 0;
            }
        };

        match VulkanImage::new(device_arc, width, height, fmt, img_usage) {
            Ok(image) => {
                let handle = next_handle();
                IMAGE_REGISTRY.lock().insert(handle, image);
                tracing::debug!("Image created: handle={}, {}x{}", handle, width, height);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create image: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, width, height, format, usage);
        0
    }
}

/// Free an image.
///
/// # Parameters
/// - `handle`: Image handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_image_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if IMAGE_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Image freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid image handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

/// Upload data to an image.
///
/// # Parameters
/// - `handle`: Image handle
/// - `data`: Pointer to data
/// - `len`: Data length in bytes
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_image_upload(handle: u64, data: *const u8, len: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() || len == 0 {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = IMAGE_REGISTRY.lock();
        match registry.get(&handle) {
            Some(image) => {
                let data_slice = unsafe { std::slice::from_raw_parts(data, len as usize) };
                match image.upload(data_slice) {
                    Ok(()) => {
                        tracing::debug!("Image data uploaded: handle={}, {} bytes", handle, len);
                        VulkanFfiError::Success as i32
                    }
                    Err(e) => {
                        tracing::error!("Failed to upload image data: {:?}", e);
                        VulkanFfiError::ExecutionFailed as i32
                    }
                }
            }
            None => {
                tracing::error!("Invalid image handle: {}", handle);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (handle, data, len);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Download data from an image.
///
/// # Parameters
/// - `handle`: Image handle
/// - `data`: Pointer to receive data
/// - `len`: Buffer length in bytes
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_image_download(handle: u64, data: *mut u8, len: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() || len == 0 {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = IMAGE_REGISTRY.lock();
        match registry.get(&handle) {
            Some(image) => {
                let data_slice = unsafe { std::slice::from_raw_parts_mut(data, len as usize) };
                match image.download(data_slice) {
                    Ok(()) => {
                        tracing::debug!("Image data downloaded: handle={}, {} bytes", handle, len);
                        VulkanFfiError::Success as i32
                    }
                    Err(e) => {
                        tracing::error!("Failed to download image data: {:?}", e);
                        VulkanFfiError::ExecutionFailed as i32
                    }
                }
            }
            None => {
                tracing::error!("Invalid image handle: {}", handle);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (handle, data, len);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get image view handle for binding to descriptors.
///
/// # Parameters
/// - `handle`: Image handle
///
/// # Returns
/// Image view handle (as u64) on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_image_get_view(handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = IMAGE_REGISTRY.lock();
        match registry.get(&handle) {
            Some(image) => image.view().as_raw(),
            None => {
                tracing::error!("Invalid image handle: {}", handle);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        0
    }
}

// =============================================================================
// Sampler FFI
// =============================================================================

/// Create a sampler.
///
/// # Parameters
/// - `device`: Device handle
/// - `filter`: Filter mode (0 = nearest, 1 = linear)
/// - `address_mode`: Address mode (0 = repeat, 1 = mirrored_repeat, 2 = clamp_to_edge, 3 = clamp_to_border)
///
/// # Returns
/// Sampler handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_sampler_create(device: u64, filter: u32, address_mode: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let filter_mode = match filter {
            0 => FilterMode::Nearest,
            1 => FilterMode::Linear,
            _ => {
                tracing::error!("Invalid filter mode: {}", filter);
                return 0;
            }
        };

        let addr_mode = match address_mode {
            0 => AddressMode::Repeat,
            1 => AddressMode::MirroredRepeat,
            2 => AddressMode::ClampToEdge,
            3 => AddressMode::ClampToBorder,
            _ => {
                tracing::error!("Invalid address mode: {}", address_mode);
                return 0;
            }
        };

        match Sampler::new(device_arc, filter_mode, addr_mode) {
            Ok(sampler) => {
                let handle = next_handle();
                SAMPLER_REGISTRY.lock().insert(handle, sampler);
                tracing::debug!("Sampler created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create sampler: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, filter, address_mode);
        0
    }
}

/// Free a sampler.
///
/// # Parameters
/// - `handle`: Sampler handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_sampler_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if SAMPLER_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Sampler freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid sampler handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_image_create_invalid_device() {
        let result = rt_vk_image_create_2d(0, 256, 256, 37, 0); // VK_FORMAT_R8G8B8A8_UNORM = 37
        assert_eq!(result, 0);
    }

    #[test]
    fn test_image_upload_null_data() {
        let result = rt_vk_image_upload(0, std::ptr::null(), 0);
        assert_eq!(result, VulkanFfiError::InvalidParameter as i32);
    }

    #[test]
    fn test_sampler_create_invalid_device() {
        let result = rt_vk_sampler_create(0, 0, 0);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_sampler_free_invalid_handle() {
        let result = rt_vk_sampler_free(999999);
        assert_eq!(result, VulkanFfiError::InvalidHandle as i32);
    }
}
