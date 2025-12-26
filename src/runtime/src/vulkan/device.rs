//! Logical device and queue management

use super::error::{VulkanError, VulkanResult};
use super::instance::{VulkanInstance, VulkanPhysicalDevice};
use ash::vk;
use gpu_allocator::vulkan::{Allocator, AllocatorCreateDesc};
use parking_lot::Mutex;
use std::sync::Arc;

/// Vulkan logical device with queues and allocator
pub struct VulkanDevice {
    instance: Arc<VulkanInstance>,
    physical_device: VulkanPhysicalDevice,
    device: ash::Device,

    // Queue families
    compute_queue_family: u32,
    transfer_queue_family: u32,

    // Queues
    compute_queue: Mutex<vk::Queue>,
    transfer_queue: Mutex<vk::Queue>,

    // Memory allocator
    allocator: Mutex<Allocator>,

    // Pipeline cache
    pipeline_cache: vk::PipelineCache,

    // Command pools (per-thread would be better, but global for now)
    compute_pool: Mutex<vk::CommandPool>,
    transfer_pool: Mutex<vk::CommandPool>,
}

impl VulkanDevice {
    /// Create a logical device from a physical device
    pub fn new(physical_device: VulkanPhysicalDevice) -> VulkanResult<Arc<Self>> {
        let instance = VulkanInstance::get_or_init()?;

        let compute_family = physical_device
            .find_compute_queue_family()
            .ok_or(VulkanError::NoComputeQueue)?;
        let transfer_family = physical_device
            .find_transfer_queue_family()
            .unwrap_or(compute_family);

        tracing::info!(
            "Selected device: {} (compute queue: {}, transfer queue: {})",
            physical_device.name(),
            compute_family,
            transfer_family
        );

        // Queue create infos
        let queue_priorities = [1.0f32];
        let mut queue_create_infos = vec![
            vk::DeviceQueueCreateInfo::default()
                .queue_family_index(compute_family)
                .queue_priorities(&queue_priorities),
        ];

        if transfer_family != compute_family {
            queue_create_infos.push(
                vk::DeviceQueueCreateInfo::default()
                    .queue_family_index(transfer_family)
                    .queue_priorities(&queue_priorities)
            );
        }

        // Required features
        let mut features = vk::PhysicalDeviceFeatures::default();
        features.shader_int64 = vk::TRUE; // For 64-bit atomics

        // Device extensions (none required for basic compute)
        let extension_names = [];

        let create_info = vk::DeviceCreateInfo::default()
            .queue_create_infos(&queue_create_infos)
            .enabled_features(&features)
            .enabled_extension_names(&extension_names);

        let device = unsafe {
            instance.instance().create_device(physical_device.handle, &create_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("{:?}", e)))?
        };

        // Get queues
        let compute_queue = unsafe { device.get_device_queue(compute_family, 0) };
        let transfer_queue = unsafe { device.get_device_queue(transfer_family, 0) };

        // Create allocator
        let allocator = Allocator::new(&AllocatorCreateDesc {
            instance: instance.instance().clone(),
            device: device.clone(),
            physical_device: physical_device.handle,
            debug_settings: Default::default(),
            buffer_device_address: false,
            allocation_sizes: Default::default(),
        })
        .map_err(|e| VulkanError::AllocationFailed(format!("{:?}", e)))?;

        // Create pipeline cache
        let cache_info = vk::PipelineCacheCreateInfo::default();
        let pipeline_cache = unsafe {
            device.create_pipeline_cache(&cache_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Pipeline cache: {:?}", e)))?
        };

        // Create command pools
        let compute_pool_info = vk::CommandPoolCreateInfo::default()
            .queue_family_index(compute_family)
            .flags(vk::CommandPoolCreateFlags::RESET_COMMAND_BUFFER);
        let compute_pool = unsafe {
            device.create_command_pool(&compute_pool_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Compute pool: {:?}", e)))?
        };

        let transfer_pool_info = vk::CommandPoolCreateInfo::default()
            .queue_family_index(transfer_family)
            .flags(vk::CommandPoolCreateFlags::TRANSIENT);
        let transfer_pool = unsafe {
            device.create_command_pool(&transfer_pool_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Transfer pool: {:?}", e)))?
        };

        tracing::info!("Vulkan device created successfully");

        Ok(Arc::new(Self {
            instance,
            physical_device,
            device,
            compute_queue_family: compute_family,
            transfer_queue_family: transfer_family,
            compute_queue: Mutex::new(compute_queue),
            transfer_queue: Mutex::new(transfer_queue),
            allocator: Mutex::new(allocator),
            pipeline_cache,
            compute_pool: Mutex::new(compute_pool),
            transfer_pool: Mutex::new(transfer_pool),
        }))
    }

    /// Select best device automatically
    pub fn new_default() -> VulkanResult<Arc<Self>> {
        let instance = VulkanInstance::get_or_init()?;
        let devices = instance.enumerate_devices()?;

        if devices.is_empty() {
            return Err(VulkanError::NoDeviceFound);
        }

        let best = devices
            .into_iter()
            .max_by_key(|d| d.compute_score())
            .ok_or(VulkanError::NoDeviceFound)?;

        tracing::info!("Auto-selected device: {} (score: {})", best.name(), best.compute_score());

        Self::new(best)
    }

    /// Get device handle
    pub fn handle(&self) -> &ash::Device {
        &self.device
    }

    /// Get physical device
    pub fn physical_device(&self) -> &VulkanPhysicalDevice {
        &self.physical_device
    }

    /// Get allocator (requires lock)
    pub fn allocator(&self) -> &Mutex<Allocator> {
        &self.allocator
    }

    /// Get pipeline cache
    pub fn pipeline_cache(&self) -> vk::PipelineCache {
        self.pipeline_cache
    }

    /// Get compute queue family index
    pub fn compute_queue_family(&self) -> u32 {
        self.compute_queue_family
    }

    /// Get transfer queue family index
    pub fn transfer_queue_family(&self) -> u32 {
        self.transfer_queue_family
    }

    /// Wait for device to be idle
    pub fn wait_idle(&self) -> VulkanResult<()> {
        unsafe {
            self.device.device_wait_idle()
                .map_err(|e| VulkanError::SyncError(format!("{:?}", e)))?;
        }
        Ok(())
    }

    /// Begin a transfer command buffer
    pub fn begin_transfer_command(&self) -> VulkanResult<vk::CommandBuffer> {
        let pool = self.transfer_pool.lock();

        let alloc_info = vk::CommandBufferAllocateInfo::default()
            .command_pool(*pool)
            .level(vk::CommandBufferLevel::PRIMARY)
            .command_buffer_count(1);

        let cmd = unsafe {
            self.device.allocate_command_buffers(&alloc_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Allocate: {:?}", e)))?
                [0]
        };

        let begin_info = vk::CommandBufferBeginInfo::default()
            .flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT);

        unsafe {
            self.device.begin_command_buffer(cmd, &begin_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Begin: {:?}", e)))?;
        }

        Ok(cmd)
    }

    /// Submit and wait for a transfer command buffer
    pub fn submit_transfer_command(&self, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        unsafe {
            self.device.end_command_buffer(cmd)
                .map_err(|e| VulkanError::CommandBufferError(format!("End: {:?}", e)))?;
        }

        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default()
            .command_buffers(&cmd_buffers);

        let queue = self.transfer_queue.lock();

        unsafe {
            self.device.queue_submit(*queue, &[submit_info], vk::Fence::null())
                .map_err(|e| VulkanError::CommandBufferError(format!("Submit: {:?}", e)))?;

            self.device.queue_wait_idle(*queue)
                .map_err(|e| VulkanError::SyncError(format!("{:?}", e)))?;
        }

        // Free command buffer
        let pool = self.transfer_pool.lock();
        unsafe {
            self.device.free_command_buffers(*pool, &[cmd]);
        }

        Ok(())
    }

    /// Begin a compute command buffer
    pub fn begin_compute_command(&self) -> VulkanResult<vk::CommandBuffer> {
        let pool = self.compute_pool.lock();

        let alloc_info = vk::CommandBufferAllocateInfo::default()
            .command_pool(*pool)
            .level(vk::CommandBufferLevel::PRIMARY)
            .command_buffer_count(1);

        let cmd = unsafe {
            self.device.allocate_command_buffers(&alloc_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Allocate: {:?}", e)))?
                [0]
        };

        let begin_info = vk::CommandBufferBeginInfo::default()
            .flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT);

        unsafe {
            self.device.begin_command_buffer(cmd, &begin_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Begin: {:?}", e)))?;
        }

        Ok(cmd)
    }

    /// Submit and wait for a compute command buffer
    pub fn submit_compute_command(&self, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        unsafe {
            self.device.end_command_buffer(cmd)
                .map_err(|e| VulkanError::CommandBufferError(format!("End: {:?}", e)))?;
        }

        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default()
            .command_buffers(&cmd_buffers);

        let queue = self.compute_queue.lock();

        unsafe {
            self.device.queue_submit(*queue, &[submit_info], vk::Fence::null())
                .map_err(|e| VulkanError::CommandBufferError(format!("Submit: {:?}", e)))?;

            self.device.queue_wait_idle(*queue)
                .map_err(|e| VulkanError::SyncError(format!("{:?}", e)))?;
        }

        // Free command buffer
        let pool = self.compute_pool.lock();
        unsafe {
            self.device.free_command_buffers(*pool, &[cmd]);
        }

        Ok(())
    }
}

impl Drop for VulkanDevice {
    fn drop(&mut self) {
        unsafe {
            let _ = self.device.device_wait_idle();

            self.device.destroy_command_pool(*self.transfer_pool.lock(), None);
            self.device.destroy_command_pool(*self.compute_pool.lock(), None);
            self.device.destroy_pipeline_cache(self.pipeline_cache, None);

            // Allocator drop happens automatically

            self.device.destroy_device(None);
        }
        tracing::info!("Vulkan device destroyed");
    }
}
