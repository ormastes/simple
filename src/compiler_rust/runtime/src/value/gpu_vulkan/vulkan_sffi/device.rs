//! Vulkan device management SFFI functions

use super::common::{next_handle, VulkanFfiError, COMMAND_BUFFER_REGISTRY, DEVICE_REGISTRY, WINDOW_SURFACES};

/// Create a Vulkan device
///
/// Returns device handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_create() -> u64 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::VulkanDevice;

        match VulkanDevice::new_default() {
            Ok(device) => {
                let handle = next_handle();
                DEVICE_REGISTRY.lock().insert(handle, device);
                tracing::info!("Vulkan device created with handle {}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create Vulkan device: {:?}", e);
                0
            }
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Create a Vulkan device configured for presentation to an existing window.
///
/// The window must be created first so its surface participates in physical
/// device selection and logical-device queue creation.
#[no_mangle]
pub extern "C" fn rt_vk_device_create_for_window(window_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        use ash::vk;
        use crate::vulkan::{VulkanDevice, VulkanInstance};
        use std::ffi::CStr;

        let surface = match WINDOW_SURFACES.lock().get(&window_handle).cloned() {
            Some(surface) => surface,
            None => {
                tracing::error!("Invalid or unavailable Vulkan window handle: {}", window_handle);
                return 0;
            }
        };
        let instance = match VulkanInstance::get_or_init() {
            Ok(instance) => instance,
            Err(e) => {
                tracing::error!("Failed to initialize Vulkan instance: {:?}", e);
                return 0;
            }
        };
        let devices = match instance.enumerate_devices() {
            Ok(devices) => devices,
            Err(e) => {
                tracing::error!("Failed to enumerate Vulkan devices: {:?}", e);
                return 0;
            }
        };
        let surface_handle = surface.handle();
        let mut candidates: Vec<_> = devices
            .into_iter()
            .filter(|device| {
                device.find_compute_queue_family().is_some()
                    && device.find_graphics_queue_family().is_some()
                    && device.find_present_queue_family(&instance, surface_handle).is_some()
                    && device.features.shader_int64 == vk::TRUE
                    && unsafe {
                        instance
                            .instance()
                            .enumerate_device_extension_properties(device.handle)
                            .map(|extensions| {
                                extensions.iter().any(|extension| {
                                    CStr::from_ptr(extension.extension_name.as_ptr()) == ash::khr::swapchain::NAME
                                })
                            })
                            .unwrap_or(false)
                    }
            })
            .collect();
        candidates.sort_by_key(|device| std::cmp::Reverse(device.compute_score()));

        for physical_device in candidates {
            match VulkanDevice::new_for_surface(physical_device, &surface) {
                Ok(device) => {
                    let handle = next_handle();
                    DEVICE_REGISTRY.lock().insert(handle, device);
                    tracing::info!(
                        "Vulkan presentation device created for window {} with handle {}",
                        window_handle,
                        handle
                    );
                    return handle;
                }
                Err(e) => {
                    tracing::warn!("Skipping Vulkan presentation device after creation failure: {:?}", e);
                }
            }
        }
        tracing::error!(
            "No Vulkan device supports compute, graphics, and presentation for window {}",
            window_handle
        );
        0
    }
    #[cfg(not(feature = "vulkan"))]
    {
        let _ = window_handle;
        0
    }
}

/// Free a Vulkan device
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_free(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let mut devices = DEVICE_REGISTRY.lock();
        let Some(device) = devices.get(&device_handle).cloned() else {
            tracing::error!("Invalid device handle: {}", device_handle);
            return VulkanFfiError::InvalidHandle as i32;
        };
        let commands = COMMAND_BUFFER_REGISTRY.lock();
        if commands
            .values()
            .any(|command| std::sync::Arc::ptr_eq(&command.lock().device, &device))
        {
            tracing::error!(
                "Cannot free Vulkan device {} while command buffers are live",
                device_handle
            );
            return VulkanFfiError::ExecutionFailed as i32;
        }
        if devices.remove(&device_handle).is_some() {
            tracing::debug!("Vulkan device {} freed", device_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Synchronize device (wait for all operations to complete)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_sync(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let device = {
            let registry = DEVICE_REGISTRY.lock();
            registry.get(&device_handle).cloned()
        };
        if let Some(device) = device {
            let registry = COMMAND_BUFFER_REGISTRY.lock();
            let commands = registry.values().cloned().collect::<Vec<_>>();
            let mut states = Vec::new();
            for command in &commands {
                let state = command.lock();
                if std::sync::Arc::ptr_eq(&state.device, &device) {
                    states.push(state);
                }
            }
            match device.wait_hardware_idle() {
                Ok(()) => {
                    for state in &mut states {
                        state.completion_unknown = false;
                    }
                    VulkanFfiError::Success as i32
                }
                Err(e) => VulkanFfiError::from(e) as i32,
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
