#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

use std::os::raw::c_char;

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    empty_cstr, leaked_cstr, vk, VulkanDevice, VulkanInstance, STATE,
};
#[cfg(not(feature = "vulkan"))]
use super::vulkan_graphics_runtime_core::{empty_cstr, leaked_cstr};

// ============================================================================
// Device Enumeration & Selection
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_count() -> i64 {
    let state = STATE.lock();
    state.physical_devices.len() as i64
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_count() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_select_device(id: i64) -> i64 {
    use super::vulkan_graphics_runtime_core::SemaphorePool;
    let mut state = STATE.lock();
    let idx = id as usize;
    let dev_count = state.physical_devices.len();
    if idx >= dev_count {
        state.set_error(format!(
            "Device index {id} out of range (count={dev_count})"
        ));
        return 0;
    }

    let instance = match &state.instance {
        Some(i) => i.clone(),
        None => {
            state.set_error("Instance not initialised".to_string());
            return 0;
        }
    };

    let devices = match instance.enumerate_devices() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(format!("enumerate_devices: {e}"));
            return 0;
        }
    };

    if idx >= devices.len() {
        state.set_error(format!("Device index {id} out of range after re-enumerate"));
        return 0;
    }

    let selected = devices.into_iter().nth(idx).unwrap();

    match VulkanDevice::new(selected) {
        Ok(dev) => {
            state.semaphore_pool = Some(SemaphorePool::new(dev.clone()));
            state.device = Some(dev);
            1
        }
        Err(e) => {
            state.set_error(format!("VulkanDevice::new: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_select_device(_id: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_get_device() -> i64 {
    let state = STATE.lock();
    if state.device.is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_get_device() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_name(id: i64) -> *const c_char {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => leaked_cstr(&pd.name()),
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_name(_id: i64) -> *const c_char {
    empty_cstr()
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_memory(id: i64) -> i64 {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => pd.total_memory() as i64,
        None => 0,
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_memory(_id: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_type(id: i64) -> *const c_char {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => {
            let ty = match pd.properties.device_type {
                vk::PhysicalDeviceType::DISCRETE_GPU => "discrete",
                vk::PhysicalDeviceType::INTEGRATED_GPU => "integrated",
                vk::PhysicalDeviceType::VIRTUAL_GPU => "virtual",
                vk::PhysicalDeviceType::CPU => "cpu",
                _ => "other",
            };
            leaked_cstr(ty)
        }
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_type(_id: i64) -> *const c_char {
    empty_cstr()
}
