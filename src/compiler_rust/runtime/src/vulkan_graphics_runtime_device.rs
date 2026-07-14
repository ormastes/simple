use std::os::raw::c_char;

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{empty_cstr, vk, VulkanDevice, VulkanInstance, STATE};
#[cfg(not(feature = "vulkan"))]
use super::vulkan_graphics_runtime_core::empty_cstr;

fn driver_identity(name: &str, vendor_id: u32, device_id: u32, driver_version: u32, api_version: u32) -> String {
    format!("{name}|vendor={vendor_id:08x}|device={device_id:08x}|driver={driver_version:08x}|api={api_version:08x}")
}

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
        state.set_error(format!("Device index {id} out of range (count={dev_count})"));
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
    if state.device.is_some() {
        1
    } else {
        0
    }
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
    let mut state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx).map(|pd| pd.name()) {
        Some(name) => state.cached_cstr(name),
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_name(_id: i64) -> *const c_char {
    empty_cstr()
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_selected_device_name() -> *const c_char {
    let mut state = STATE.lock();
    let name = state.device.as_ref().map(|device| device.physical_device().name());
    name.map_or_else(empty_cstr, |name| state.cached_cstr(name))
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_selected_device_name() -> *const c_char {
    empty_cstr()
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_driver_identity(id: i64) -> *const c_char {
    let mut state = STATE.lock();
    let identity = state.physical_devices.get(id as usize).map(|pd| {
        driver_identity(
            &pd.name(),
            pd.properties.vendor_id,
            pd.properties.device_id,
            pd.properties.driver_version,
            pd.properties.api_version,
        )
    });
    match identity {
        Some(identity) => state.cached_cstr(identity),
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_driver_identity(_id: i64) -> *const c_char {
    empty_cstr()
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_selected_device_driver_identity() -> *const c_char {
    let mut state = STATE.lock();
    let identity = state.device.as_ref().map(|device| {
        let pd = device.physical_device();
        driver_identity(
            &pd.name(),
            pd.properties.vendor_id,
            pd.properties.device_id,
            pd.properties.driver_version,
            pd.properties.api_version,
        )
    });
    match identity {
        Some(identity) => state.cached_cstr(identity),
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_selected_device_driver_identity() -> *const c_char {
    empty_cstr()
}

#[cfg(test)]
mod tests {
    use super::driver_identity;

    #[test]
    fn driver_identity_is_stable_and_unambiguous() {
        assert_eq!(
            driver_identity("GPU", 0x10de, 0x2684, 0x123, 0x0040_3000),
            "GPU|vendor=000010de|device=00002684|driver=00000123|api=00403000"
        );
    }
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
    let mut state = STATE.lock();
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
            state.cached_cstr(ty.to_string())
        }
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_selected_device_type() -> *const c_char {
    let mut state = STATE.lock();
    let ty = state
        .device
        .as_ref()
        .map(|device| match device.physical_device().properties.device_type {
            vk::PhysicalDeviceType::DISCRETE_GPU => "discrete",
            vk::PhysicalDeviceType::INTEGRATED_GPU => "integrated",
            vk::PhysicalDeviceType::VIRTUAL_GPU => "virtual",
            vk::PhysicalDeviceType::CPU => "cpu",
            _ => "other",
        });
    ty.map_or_else(empty_cstr, |ty| state.cached_cstr(ty.to_string()))
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_selected_device_type() -> *const c_char {
    empty_cstr()
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_type(_id: i64) -> *const c_char {
    empty_cstr()
}
