//! Descriptor management for Vulkan FFI
//!
//! Provides FFI functions for managing Vulkan descriptor sets, descriptor set layouts,
//! and descriptor pools. These are used to bind buffers and images to compute/graphics pipelines.

#[cfg(feature = "vulkan")]
use crate::vulkan::DescriptorPool;
#[cfg(feature = "vulkan")]
use crate::vulkan::DescriptorSet;
#[cfg(feature = "vulkan")]
use crate::vulkan::DescriptorSetLayout;

use super::common::{
    next_handle, VulkanFfiError, BUFFER_REGISTRY, DESCRIPTOR_LAYOUT_REGISTRY, DESCRIPTOR_POOL_REGISTRY,
    DESCRIPTOR_SET_REGISTRY, DEVICE_REGISTRY,
};

/// Create a descriptor set layout for uniform buffers
///
/// # Arguments
/// * `device_handle` - Handle to a valid VulkanDevice
///
/// # Returns
/// Layout handle on success (positive), 0 on failure
///
/// # Example
/// ```c
/// u64 device = rt_vk_device_create();
/// u64 layout = rt_vk_descriptor_layout_create_uniform(device);
/// // Use layout to allocate descriptor sets...
/// rt_vk_descriptor_layout_free(layout);
/// rt_vk_device_free(device);
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_create_uniform(device_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorSetLayout::new_uniform_buffer(device.clone()) {
                Ok(layout) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_LAYOUT_REGISTRY.lock().insert(handle, layout);
                    tracing::info!("Descriptor layout {} created (uniform buffer)", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor layout: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Create a descriptor set layout for combined image samplers
///
/// # Arguments
/// * `device_handle` - Handle to a valid VulkanDevice
///
/// # Returns
/// Layout handle on success (positive), 0 on failure
///
/// # Example
/// ```c
/// u64 device = rt_vk_device_create();
/// u64 layout = rt_vk_descriptor_layout_create_sampler(device);
/// // Use layout to allocate descriptor sets...
/// rt_vk_descriptor_layout_free(layout);
/// rt_vk_device_free(device);
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_create_sampler(device_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorSetLayout::new_combined_image_sampler(device.clone()) {
                Ok(layout) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_LAYOUT_REGISTRY.lock().insert(handle, layout);
                    tracing::info!("Descriptor layout {} created (image sampler)", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor layout: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor set layout
///
/// # Arguments
/// * `layout_handle` - Handle to a valid descriptor set layout
///
/// # Returns
/// 0 (Success) on success, negative error code on failure
///
/// # Example
/// ```c
/// u64 layout = rt_vk_descriptor_layout_create_uniform(device);
/// // Use layout...
/// int result = rt_vk_descriptor_layout_free(layout);
/// if (result == 0) { /* success */ }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_free(layout_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_LAYOUT_REGISTRY.lock().remove(&layout_handle).is_some() {
            tracing::debug!("Descriptor layout {} freed", layout_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor layout handle: {}", layout_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Create a descriptor pool for allocating descriptor sets
///
/// # Arguments
/// * `device_handle` - Handle to a valid VulkanDevice
/// * `max_sets` - Maximum number of descriptor sets this pool can allocate
///
/// # Returns
/// Pool handle on success (positive), 0 on failure
///
/// # Example
/// ```c
/// u64 device = rt_vk_device_create();
/// u64 pool = rt_vk_descriptor_pool_create(device, 10);
/// // Allocate descriptor sets from this pool...
/// rt_vk_descriptor_pool_free(pool);
/// rt_vk_device_free(device);
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_pool_create(device_handle: u64, max_sets: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorPool::new_for_uniform_buffers(device.clone(), max_sets) {
                Ok(pool) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_POOL_REGISTRY.lock().insert(handle, pool);
                    tracing::info!("Descriptor pool {} created (max_sets={})", handle, max_sets);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor pool: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor pool
///
/// # Arguments
/// * `pool_handle` - Handle to a valid descriptor pool
///
/// # Returns
/// 0 (Success) on success, negative error code on failure
///
/// # Example
/// ```c
/// u64 pool = rt_vk_descriptor_pool_create(device, 10);
/// // Use pool...
/// int result = rt_vk_descriptor_pool_free(pool);
/// if (result == 0) { /* success */ }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_pool_free(pool_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_POOL_REGISTRY.lock().remove(&pool_handle).is_some() {
            tracing::debug!("Descriptor pool {} freed", pool_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor pool handle: {}", pool_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Allocate a descriptor set from a pool
///
/// # Arguments
/// * `device_handle` - Handle to a valid VulkanDevice
/// * `pool_handle` - Handle to a valid descriptor pool
/// * `layout_handle` - Handle to a valid descriptor set layout
///
/// # Returns
/// Descriptor set handle on success (positive), 0 on failure
///
/// # Example
/// ```c
/// u64 device = rt_vk_device_create();
/// u64 layout = rt_vk_descriptor_layout_create_uniform(device);
/// u64 pool = rt_vk_descriptor_pool_create(device, 10);
/// u64 set = rt_vk_descriptor_set_allocate(device, pool, layout);
/// // Use descriptor set...
/// rt_vk_descriptor_set_free(set);
/// rt_vk_descriptor_pool_free(pool);
/// rt_vk_descriptor_layout_free(layout);
/// rt_vk_device_free(device);
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_allocate(device_handle: u64, pool_handle: u64, layout_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_registry = DEVICE_REGISTRY.lock();
        let pool_registry = DESCRIPTOR_POOL_REGISTRY.lock();
        let layout_registry = DESCRIPTOR_LAYOUT_REGISTRY.lock();

        if let (Some(device), Some(pool), Some(layout)) = (
            device_registry.get(&device_handle),
            pool_registry.get(&pool_handle),
            layout_registry.get(&layout_handle),
        ) {
            match DescriptorSet::new(device.clone(), pool, layout) {
                Ok(desc_set) => {
                    drop(device_registry);
                    drop(pool_registry);
                    drop(layout_registry);
                    let handle = next_handle();
                    DESCRIPTOR_SET_REGISTRY.lock().insert(handle, desc_set);
                    tracing::info!("Descriptor set {} allocated", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to allocate descriptor set: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device, pool, or layout handle");
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor set
///
/// # Arguments
/// * `set_handle` - Handle to a valid descriptor set
///
/// # Returns
/// 0 (Success) on success, negative error code on failure
///
/// # Example
/// ```c
/// u64 set = rt_vk_descriptor_set_allocate(device, pool, layout);
/// // Use descriptor set...
/// int result = rt_vk_descriptor_set_free(set);
/// if (result == 0) { /* success */ }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_free(set_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_SET_REGISTRY.lock().remove(&set_handle).is_some() {
            tracing::debug!("Descriptor set {} freed", set_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor set handle: {}", set_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Update a descriptor set with a buffer binding
///
/// # Arguments
/// * `set_handle` - Handle to a valid descriptor set
/// * `binding` - Binding index in the descriptor set layout
/// * `buffer_handle` - Handle to a valid VulkanBuffer
/// * `offset` - Byte offset into the buffer
/// * `range` - Number of bytes to bind (or u64::MAX for entire buffer)
///
/// # Returns
/// 0 (Success) on success, negative error code on failure
///
/// # Example
/// ```c
/// u64 buffer = rt_vk_buffer_alloc(device, 1024);
/// u64 set = rt_vk_descriptor_set_allocate(device, pool, layout);
/// int result = rt_vk_descriptor_set_update_buffer(set, 0, buffer, 0, 1024);
/// if (result == 0) { /* success */ }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_update_buffer(
    set_handle: u64,
    binding: u32,
    buffer_handle: u64,
    offset: u64,
    range: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let set_registry = DESCRIPTOR_SET_REGISTRY.lock();
        let buffer_registry = BUFFER_REGISTRY.lock();

        if let (Some(desc_set), Some(buffer)) = (set_registry.get(&set_handle), buffer_registry.get(&buffer_handle)) {
            match desc_set.update_buffer(binding, buffer.as_ref(), offset, range) {
                Ok(()) => {
                    tracing::debug!(
                        "Descriptor set {} updated with buffer {} at binding {}",
                        set_handle,
                        buffer_handle,
                        binding
                    );
                    VulkanFfiError::Success as i32
                }
                Err(e) => {
                    tracing::error!("Failed to update descriptor set: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            tracing::error!("Invalid descriptor set or buffer handle");
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}
