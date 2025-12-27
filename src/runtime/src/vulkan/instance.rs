//! Vulkan instance and physical device management

use super::error::{VulkanError, VulkanResult};
use ash::vk;
use parking_lot::Mutex;
use std::ffi::{CStr, CString};
use std::sync::Arc;

/// Global Vulkan instance (singleton)
static VULKAN_INSTANCE: Mutex<Option<Arc<VulkanInstance>>> = Mutex::new(None);

/// Vulkan instance wrapper with validation layers
pub struct VulkanInstance {
    entry: ash::Entry,
    instance: ash::Instance,
    #[cfg(feature = "vulkan")]
    surface_loader: ash::khr::surface::Instance,
    #[allow(dead_code)]
    debug_utils: Option<ash::ext::debug_utils::Instance>,
    #[allow(dead_code)]
    debug_messenger: Option<vk::DebugUtilsMessengerEXT>,
}

impl VulkanInstance {
    /// Get or create the global Vulkan instance
    pub fn get_or_init() -> VulkanResult<Arc<VulkanInstance>> {
        let mut guard = VULKAN_INSTANCE.lock();
        if let Some(instance) = guard.as_ref() {
            return Ok(Arc::clone(instance));
        }

        let instance = Self::create()?;
        let arc = Arc::new(instance);
        *guard = Some(Arc::clone(&arc));
        Ok(arc)
    }

    /// Check if Vulkan is available on this system
    pub fn is_available() -> bool {
        unsafe {
            ash::Entry::load().is_ok()
        }
    }

    fn create() -> VulkanResult<Self> {
        // Load Vulkan library
        let entry = unsafe { ash::Entry::load()? };

        // Application info
        let app_name = CString::new("Simple Language").unwrap();
        let engine_name = CString::new("Simple Runtime").unwrap();
        let app_info = vk::ApplicationInfo::default()
            .application_name(&app_name)
            .application_version(vk::make_api_version(0, 1, 0, 0))
            .engine_name(&engine_name)
            .engine_version(vk::make_api_version(0, 1, 0, 0))
            .api_version(vk::API_VERSION_1_1); // Vulkan 1.1

        // Enable validation layers in debug builds
        let layer_names_raw: Vec<CString>;
        let layer_names: Vec<*const i8>;

        #[cfg(debug_assertions)]
        {
            layer_names_raw = vec![
                CString::new("VK_LAYER_KHRONOS_validation").unwrap(),
            ];
            layer_names = layer_names_raw.iter()
                .map(|name| name.as_ptr())
                .collect();
        }

        #[cfg(not(debug_assertions))]
        {
            layer_names_raw = vec![];
            layer_names = vec![];
        }

        // Required extensions
        let mut extension_names_raw = vec![];
        let mut extension_names = vec![];

        // Debug utils extension (debug builds only)
        #[cfg(debug_assertions)]
        {
            extension_names_raw.push(ash::ext::debug_utils::NAME.to_owned());
        }

        // Surface extensions for windowing
        #[cfg(feature = "vulkan")]
        {
            extension_names_raw.push(ash::khr::surface::NAME.to_owned());

            // Platform-specific surface extensions
            #[cfg(target_os = "windows")]
            extension_names_raw.push(ash::khr::win32_surface::NAME.to_owned());

            #[cfg(target_os = "linux")]
            {
                // Prefer Wayland if available, fall back to X11
                if std::env::var("WAYLAND_DISPLAY").is_ok() {
                    extension_names_raw.push(ash::khr::wayland_surface::NAME.to_owned());
                } else {
                    extension_names_raw.push(ash::khr::xlib_surface::NAME.to_owned());
                }
            }

            #[cfg(target_os = "macos")]
            extension_names_raw.push(ash::ext::metal_surface::NAME.to_owned());
        }

        for ext in &extension_names_raw {
            extension_names.push(ext.as_ptr());
        }

        let create_info = vk::InstanceCreateInfo::default()
            .application_info(&app_info)
            .enabled_layer_names(&layer_names)
            .enabled_extension_names(&extension_names);

        let instance = unsafe {
            entry.create_instance(&create_info, None)
                .map_err(|e| VulkanError::InitializationFailed(format!("{:?}", e)))?
        };

        // Setup debug messenger
        #[cfg(debug_assertions)]
        let (debug_utils, debug_messenger) = {
            let debug_utils = ash::ext::debug_utils::Instance::new(&entry, &instance);
            let messenger_info = vk::DebugUtilsMessengerCreateInfoEXT::default()
                .message_severity(
                    vk::DebugUtilsMessageSeverityFlagsEXT::WARNING
                        | vk::DebugUtilsMessageSeverityFlagsEXT::ERROR
                )
                .message_type(
                    vk::DebugUtilsMessageTypeFlagsEXT::GENERAL
                        | vk::DebugUtilsMessageTypeFlagsEXT::VALIDATION
                        | vk::DebugUtilsMessageTypeFlagsEXT::PERFORMANCE
                )
                .pfn_user_callback(Some(debug_callback));

            let messenger = unsafe {
                debug_utils.create_debug_utils_messenger(&messenger_info, None)
                    .map_err(|e| VulkanError::InitializationFailed(format!("Debug messenger: {:?}", e)))?
            };
            (Some(debug_utils), Some(messenger))
        };

        #[cfg(not(debug_assertions))]
        let (debug_utils, debug_messenger) = (None, None);

        // Create surface loader for windowing support
        #[cfg(feature = "vulkan")]
        let surface_loader = ash::khr::surface::Instance::new(&entry, &instance);

        tracing::info!("Vulkan instance created successfully");

        Ok(Self {
            entry,
            instance,
            #[cfg(feature = "vulkan")]
            surface_loader,
            debug_utils,
            debug_messenger,
        })
    }

    /// Enumerate physical devices
    pub fn enumerate_devices(&self) -> VulkanResult<Vec<VulkanPhysicalDevice>> {
        let devices = unsafe {
            self.instance.enumerate_physical_devices()
                .map_err(|e| VulkanError::InitializationFailed(format!("Enumerate devices: {:?}", e)))?
        };

        devices.into_iter()
            .map(|device| VulkanPhysicalDevice::new(&self.instance, device))
            .collect()
    }

    /// Get the Vulkan instance handle
    pub fn instance(&self) -> &ash::Instance {
        &self.instance
    }

    /// Get the Vulkan entry
    pub fn entry(&self) -> &ash::Entry {
        &self.entry
    }

    /// Get the surface loader
    #[cfg(feature = "vulkan")]
    pub fn surface_loader(&self) -> &ash::khr::surface::Instance {
        &self.surface_loader
    }
}

impl Drop for VulkanInstance {
    fn drop(&mut self) {
        unsafe {
            #[cfg(debug_assertions)]
            if let (Some(utils), Some(messenger)) = (&self.debug_utils, self.debug_messenger) {
                utils.destroy_debug_utils_messenger(messenger, None);
            }
            self.instance.destroy_instance(None);
        }
        tracing::info!("Vulkan instance destroyed");
    }
}

/// Debug callback for validation layers
#[cfg(debug_assertions)]
unsafe extern "system" fn debug_callback(
    message_severity: vk::DebugUtilsMessageSeverityFlagsEXT,
    _message_type: vk::DebugUtilsMessageTypeFlagsEXT,
    p_callback_data: *const vk::DebugUtilsMessengerCallbackDataEXT<'_>,
    _p_user_data: *mut std::ffi::c_void,
) -> vk::Bool32 {
    let message = CStr::from_ptr((*p_callback_data).p_message);
    let message_str = message.to_string_lossy();

    match message_severity {
        vk::DebugUtilsMessageSeverityFlagsEXT::ERROR => {
            tracing::error!("Vulkan validation: {}", message_str);
        }
        vk::DebugUtilsMessageSeverityFlagsEXT::WARNING => {
            tracing::warn!("Vulkan validation: {}", message_str);
        }
        vk::DebugUtilsMessageSeverityFlagsEXT::INFO => {
            tracing::info!("Vulkan validation: {}", message_str);
        }
        _ => {
            tracing::debug!("Vulkan validation: {}", message_str);
        }
    }

    vk::FALSE
}

/// Physical device wrapper with capability queries
pub struct VulkanPhysicalDevice {
    pub handle: vk::PhysicalDevice,
    pub properties: vk::PhysicalDeviceProperties,
    pub features: vk::PhysicalDeviceFeatures,
    pub memory_properties: vk::PhysicalDeviceMemoryProperties,
    pub queue_families: Vec<vk::QueueFamilyProperties>,
}

impl VulkanPhysicalDevice {
    fn new(instance: &ash::Instance, device: vk::PhysicalDevice) -> VulkanResult<Self> {
        unsafe {
            let properties = instance.get_physical_device_properties(device);
            let features = instance.get_physical_device_features(device);
            let memory_properties = instance.get_physical_device_memory_properties(device);
            let queue_families = instance.get_physical_device_queue_family_properties(device);

            Ok(Self {
                handle: device,
                properties,
                features,
                memory_properties,
                queue_families,
            })
        }
    }

    /// Get device name
    pub fn name(&self) -> String {
        let name_bytes = &self.properties.device_name;
        let len = name_bytes.iter().position(|&c| c == 0).unwrap_or(name_bytes.len());
        String::from_utf8_lossy(&name_bytes[..len].iter().map(|&c| c as u8).collect::<Vec<_>>()).to_string()
    }

    /// Score device for compute workloads (higher is better)
    pub fn compute_score(&self) -> u32 {
        let mut score = 0;

        // Prefer discrete GPUs
        if self.properties.device_type == vk::PhysicalDeviceType::DISCRETE_GPU {
            score += 1000;
        } else if self.properties.device_type == vk::PhysicalDeviceType::INTEGRATED_GPU {
            score += 100;
        }

        // More memory is better
        let total_memory: u64 = (0..self.memory_properties.memory_heap_count)
            .filter_map(|i| {
                let heap = self.memory_properties.memory_heaps[i as usize];
                if heap.flags.contains(vk::MemoryHeapFlags::DEVICE_LOCAL) {
                    Some(heap.size)
                } else {
                    None
                }
            })
            .sum();
        score += (total_memory / (1024 * 1024 * 1024)) as u32; // GB

        score
    }

    /// Find compute queue family index
    pub fn find_compute_queue_family(&self) -> Option<u32> {
        self.queue_families
            .iter()
            .enumerate()
            .find(|(_, props)| props.queue_flags.contains(vk::QueueFlags::COMPUTE))
            .map(|(idx, _)| idx as u32)
    }

    /// Find transfer queue family index (prefer dedicated)
    pub fn find_transfer_queue_family(&self) -> Option<u32> {
        // Try to find dedicated transfer queue
        let dedicated = self.queue_families
            .iter()
            .enumerate()
            .find(|(_, props)| {
                props.queue_flags.contains(vk::QueueFlags::TRANSFER)
                    && !props.queue_flags.contains(vk::QueueFlags::GRAPHICS)
                    && !props.queue_flags.contains(vk::QueueFlags::COMPUTE)
            })
            .map(|(idx, _)| idx as u32);

        if dedicated.is_some() {
            return dedicated;
        }

        // Fall back to any transfer-capable queue
        self.queue_families
            .iter()
            .enumerate()
            .find(|(_, props)| props.queue_flags.contains(vk::QueueFlags::TRANSFER))
            .map(|(idx, _)| idx as u32)
    }

    /// Find graphics queue family index
    #[cfg(feature = "vulkan")]
    pub fn find_graphics_queue_family(&self) -> Option<u32> {
        self.queue_families
            .iter()
            .enumerate()
            .find(|(_, props)| props.queue_flags.contains(vk::QueueFlags::GRAPHICS))
            .map(|(idx, _)| idx as u32)
    }

    /// Find present queue family index (requires surface support check)
    #[cfg(feature = "vulkan")]
    pub fn find_present_queue_family(
        &self,
        instance: &VulkanInstance,
        surface: vk::SurfaceKHR,
    ) -> Option<u32> {
        let surface_loader = instance.surface_loader();

        self.queue_families
            .iter()
            .enumerate()
            .find(|(idx, _)| {
                unsafe {
                    surface_loader
                        .get_physical_device_surface_support(
                            self.handle,
                            *idx as u32,
                            surface,
                        )
                        .unwrap_or(false)
                }
            })
            .map(|(idx, _)| idx as u32)
    }

    /// Get total device memory in bytes
    pub fn total_memory(&self) -> u64 {
        (0..self.memory_properties.memory_heap_count)
            .filter_map(|i| {
                let heap = self.memory_properties.memory_heaps[i as usize];
                if heap.flags.contains(vk::MemoryHeapFlags::DEVICE_LOCAL) {
                    Some(heap.size)
                } else {
                    None
                }
            })
            .sum()
    }
}
