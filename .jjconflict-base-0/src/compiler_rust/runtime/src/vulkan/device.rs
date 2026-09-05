//! Logical device and queue management

use super::buffer::VulkanBuffer;
use super::error::{VulkanError, VulkanResult};
use super::instance::{VulkanInstance, VulkanPhysicalDevice};
use super::pipeline::ComputePipeline;
use super::sync::Fence;
#[cfg(feature = "vulkan")]
use super::surface::Surface;
use ash::vk;
use gpu_allocator::vulkan::{Allocation, Allocator, AllocatorCreateDesc};
use parking_lot::Mutex;
use std::mem::ManuallyDrop;
use std::sync::{Arc, Weak};

pub(super) struct DeviceLifetime {
    _instance: Arc<VulkanInstance>,
    device: ash::Device,
    allocator: Mutex<ManuallyDrop<Allocator>>,
    transfer_gate: Mutex<RecoveryGate<TransferOwner>>,
}

impl DeviceLifetime {
    pub(super) fn handle(&self) -> &ash::Device {
        &self.device
    }

    pub(super) fn allocator(&self) -> &Mutex<ManuallyDrop<Allocator>> {
        &self.allocator
    }

    fn transfer_completion_unknown(&self) -> bool {
        self.transfer_gate.lock().is_blocked()
    }

    pub(super) fn admit_or_release_resource(&self, owner: TransferOwner) {
        let mut gate = self.transfer_gate.lock();
        let owner = match gate.retain_if_closed(owner) {
            Ok(()) => return,
            Err(owner) => owner,
        };
        if let Err(poison) = self.release_resource_owner(owner) {
            gate.poison(poison);
        }
    }

    fn release_resource_owner(&self, owner: TransferOwner) -> Result<(), TransferOwner> {
        let allocation = unsafe {
            match owner {
                TransferOwner::Buffer { buffer, allocation } => {
                    self.handle().destroy_buffer(buffer, None);
                    allocation
                }
                TransferOwner::Image {
                    image,
                    view,
                    allocation,
                } => {
                    self.handle().destroy_image_view(view, None);
                    self.handle().destroy_image(image, None);
                    allocation
                }
                TransferOwner::PoisonedAllocation => {
                    return Err(TransferOwner::PoisonedAllocation);
                }
                owner @ TransferOwner::Submission { .. } => return Err(owner),
            }
        };
        if let Some(allocation) = allocation {
            if let Err(error) = self.allocator().lock().free(allocation) {
                tracing::error!("Vulkan allocation cleanup is irrecoverable; poisoning transfer gate: {error:?}");
                return Err(TransferOwner::PoisonedAllocation);
            }
        }
        Ok(())
    }
}

impl Drop for DeviceLifetime {
    fn drop(&mut self) {
        let transfer_gate = self.transfer_gate.get_mut();
        if transfer_gate.is_blocked() {
            tracing::error!("Leaking poisoned Vulkan lifetime with unreleased transfer owners");
            transfer_gate.leak_all();
            std::mem::forget(Arc::clone(&self._instance));
            return;
        }
        unsafe {
            ManuallyDrop::drop(&mut *self.allocator.lock());
            self.device.destroy_device(None);
        }
        tracing::info!("Vulkan device destroyed");
    }
}

struct RecoveryQueue<T> {
    owners: Vec<T>,
}

impl<T> Default for RecoveryQueue<T> {
    fn default() -> Self {
        Self { owners: Vec::new() }
    }
}

impl<T> RecoveryQueue<T> {
    fn is_blocked(&self) -> bool {
        !self.owners.is_empty()
    }

    fn push(&mut self, owner: T) {
        self.owners.push(owner);
    }

    fn take_if_ready(&mut self, ready: impl FnMut(&T) -> bool) -> Option<Vec<T>> {
        if self.owners.iter().all(ready) {
            Some(std::mem::take(&mut self.owners))
        } else {
            None
        }
    }

    fn leak_all(&mut self) {
        for owner in std::mem::take(&mut self.owners) {
            std::mem::forget(owner);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RecoveryPhase {
    Open,
    Blocked,
    Recovering,
    Poisoned,
}

struct RecoveryGate<T> {
    phase: RecoveryPhase,
    owners: Vec<T>,
}

impl<T> Default for RecoveryGate<T> {
    fn default() -> Self {
        Self {
            phase: RecoveryPhase::Open,
            owners: Vec::new(),
        }
    }
}

impl<T> RecoveryGate<T> {
    fn is_blocked(&self) -> bool {
        self.phase != RecoveryPhase::Open
    }

    fn admit_unknown(&mut self, owner: T) {
        self.owners.push(owner);
        if self.phase == RecoveryPhase::Open {
            self.phase = RecoveryPhase::Blocked;
        }
    }

    fn retain_if_closed(&mut self, owner: T) -> Result<(), T> {
        if self.is_blocked() {
            self.owners.push(owner);
            Ok(())
        } else {
            Err(owner)
        }
    }

    fn begin_recovery(&mut self) -> Option<Vec<T>> {
        if self.phase == RecoveryPhase::Poisoned {
            return None;
        }
        self.phase = RecoveryPhase::Recovering;
        Some(std::mem::take(&mut self.owners))
    }

    fn take_recovery_batch(&mut self) -> Option<Vec<T>> {
        if self.phase != RecoveryPhase::Recovering {
            return None;
        }
        if self.owners.is_empty() {
            self.phase = RecoveryPhase::Open;
            None
        } else {
            Some(std::mem::take(&mut self.owners))
        }
    }

    fn poison(&mut self, owner: T) {
        self.owners.push(owner);
        self.phase = RecoveryPhase::Poisoned;
    }

    fn leak_all(&mut self) {
        for owner in std::mem::take(&mut self.owners) {
            std::mem::forget(owner);
        }
    }
}

/// Vulkan logical device with queues and allocator
pub struct VulkanDevice {
    lifetime: Arc<DeviceLifetime>,
    physical_device: VulkanPhysicalDevice,

    // Queue families
    compute_queue_family: u32,
    transfer_queue_family: u32,
    #[cfg(feature = "vulkan")]
    graphics_queue_family: Option<u32>,
    #[cfg(feature = "vulkan")]
    present_queue_family: Option<u32>,
    #[cfg(feature = "vulkan")]
    present_surface: Option<Weak<Surface>>,

    // Queues
    compute_queue: Arc<Mutex<vk::Queue>>,
    #[cfg(feature = "vulkan")]
    graphics_queue: Option<Arc<Mutex<vk::Queue>>>,
    #[cfg(feature = "vulkan")]
    present_queue: Option<Arc<Mutex<vk::Queue>>>,

    // Pipeline cache
    pipeline_cache: vk::PipelineCache,

    // Command pools (per-thread would be better, but global for now)
    compute_pool: Mutex<vk::CommandPool>,
    transfer_pool: Mutex<vk::CommandPool>,
    #[cfg(feature = "vulkan")]
    graphics_pool: Option<Mutex<vk::CommandPool>>,

    // Swapchain loader (for presentation)
    #[cfg(feature = "vulkan")]
    swapchain_loader: Option<ash::khr::swapchain::Device>,

    direct_compute_gate: Mutex<()>,
    direct_compute_quarantine: Mutex<RecoveryQueue<DirectComputeSubmission>>,
}

struct DirectComputeSubmission {
    pipeline: Arc<ComputePipeline>,
    fence: Fence,
    command_buffer: vk::CommandBuffer,
    buffers: Vec<Arc<VulkanBuffer>>,
}

pub(super) enum TransferOwner {
    Submission {
        fence: vk::Fence,
        command_buffer: vk::CommandBuffer,
    },
    Buffer {
        buffer: vk::Buffer,
        allocation: Option<Allocation>,
    },
    Image {
        image: vk::Image,
        view: vk::ImageView,
        allocation: Option<Allocation>,
    },
    // gpu-allocator consumes Allocation on error; this marker keeps the gate closed and lifetime leaked.
    PoisonedAllocation,
}

pub enum FencedSubmitError {
    NotSubmitted(VulkanError),
    CompletionUnknown(VulkanError),
}

struct VulkanDeviceBuildGuard {
    device: Option<ash::Device>,
    allocator: Option<Allocator>,
    pipeline_cache: Option<vk::PipelineCache>,
    compute_pool: Option<vk::CommandPool>,
    transfer_pool: Option<vk::CommandPool>,
    #[cfg(feature = "vulkan")]
    graphics_pool: Option<vk::CommandPool>,
}

impl VulkanDeviceBuildGuard {
    fn new(device: ash::Device) -> Self {
        Self {
            device: Some(device),
            allocator: None,
            pipeline_cache: None,
            compute_pool: None,
            transfer_pool: None,
            #[cfg(feature = "vulkan")]
            graphics_pool: None,
        }
    }

    fn handle(&self) -> &ash::Device {
        self.device.as_ref().expect("Vulkan build guard is armed")
    }

    fn finish(mut self) -> (ash::Device, Allocator) {
        self.pipeline_cache = None;
        self.compute_pool = None;
        self.transfer_pool = None;
        #[cfg(feature = "vulkan")]
        {
            self.graphics_pool = None;
        }
        let allocator = self.allocator.take().expect("Vulkan allocator was initialized");
        let device = self.device.take().expect("Vulkan device was initialized");
        (device, allocator)
    }
}

impl Drop for VulkanDeviceBuildGuard {
    fn drop(&mut self) {
        let Some(device) = self.device.as_ref() else {
            return;
        };
        unsafe {
            #[cfg(feature = "vulkan")]
            if let Some(pool) = self.graphics_pool.take() {
                device.destroy_command_pool(pool, None);
            }
            if let Some(pool) = self.transfer_pool.take() {
                device.destroy_command_pool(pool, None);
            }
            if let Some(pool) = self.compute_pool.take() {
                device.destroy_command_pool(pool, None);
            }
            if let Some(cache) = self.pipeline_cache.take() {
                device.destroy_pipeline_cache(cache, None);
            }
        }
        drop(self.allocator.take());
        if let Some(device) = self.device.take() {
            unsafe {
                device.destroy_device(None);
            }
        }
    }
}

pub(crate) fn submit_definitely_not_accepted(error: vk::Result) -> bool {
    matches!(
        error,
        vk::Result::ERROR_OUT_OF_HOST_MEMORY | vk::Result::ERROR_OUT_OF_DEVICE_MEMORY
    )
}

fn resource_queue_families(compute: u32, transfer: u32, graphics: Option<u32>) -> Vec<u32> {
    let mut families = vec![compute];
    if transfer != compute {
        families.push(transfer);
    }
    if let Some(graphics) = graphics {
        if !families.contains(&graphics) {
            families.push(graphics);
        }
    }
    families
}

impl VulkanDevice {
    pub fn max_push_constant_size(&self) -> u32 {
        self.physical_device.properties.limits.max_push_constants_size
    }

    /// Create a logical device from a physical device
    pub fn new(physical_device: VulkanPhysicalDevice) -> VulkanResult<Arc<Self>> {
        #[cfg(feature = "vulkan")]
        {
            Self::new_internal(physical_device, None)
        }
        #[cfg(not(feature = "vulkan"))]
        {
            Self::new_internal(physical_device)
        }
    }

    /// Create a logical device with presentation support for `surface`.
    ///
    /// The presentation queue family must be selected before `vkCreateDevice`;
    /// a device created by `new_default` cannot be retrofitted later.
    #[cfg(feature = "vulkan")]
    pub fn new_for_surface(physical_device: VulkanPhysicalDevice, surface: &Arc<Surface>) -> VulkanResult<Arc<Self>> {
        Self::new_internal(physical_device, Some((surface.handle(), Arc::downgrade(surface))))
    }

    fn new_internal(
        physical_device: VulkanPhysicalDevice,
        #[cfg(feature = "vulkan")] surface: Option<(vk::SurfaceKHR, Weak<Surface>)>,
    ) -> VulkanResult<Arc<Self>> {
        let instance = VulkanInstance::get_or_init()?;

        let compute_family = physical_device
            .find_compute_queue_family()
            .ok_or(VulkanError::NoComputeQueue)?;
        // ponytail: one queue avoids cross-queue semaphore ownership; restore a
        // dedicated transfer queue only with measured benefit and explicit sync.
        let transfer_family = compute_family;

        // Graphics queue support (optional - may not be needed for compute-only devices)
        #[cfg(feature = "vulkan")]
        let graphics_family = physical_device.find_graphics_queue_family();

        #[cfg(feature = "vulkan")]
        if surface.is_some() && graphics_family.is_none() {
            return Err(VulkanError::SurfaceError(
                "No queue family supports graphics for presentation".to_string(),
            ));
        }

        #[cfg(feature = "vulkan")]
        let present_family = surface.as_ref().map_or(Ok(None), |(surface, _)| {
            physical_device
                .find_present_queue_family(&instance, *surface)
                .map(Some)
                .ok_or_else(|| VulkanError::SurfaceError("No queue family supports presentation".to_string()))
        })?;

        #[cfg(feature = "vulkan")]
        tracing::info!(
            "Selected device: {} (compute: {}, transfer: {}, graphics: {:?}, present: {:?})",
            physical_device.name(),
            compute_family,
            transfer_family,
            graphics_family,
            present_family
        );

        #[cfg(not(feature = "vulkan"))]
        tracing::info!(
            "Selected device: {} (compute queue: {}, transfer queue: {})",
            physical_device.name(),
            compute_family,
            transfer_family
        );

        // Queue create infos - collect unique queue families
        let queue_priorities = [1.0f32];
        let mut unique_families = std::collections::HashSet::new();
        unique_families.insert(compute_family);
        unique_families.insert(transfer_family);

        #[cfg(feature = "vulkan")]
        if let Some(gfx) = graphics_family {
            unique_families.insert(gfx);
        }
        #[cfg(feature = "vulkan")]
        if let Some(present) = present_family {
            unique_families.insert(present);
        }

        let queue_create_infos: Vec<_> = unique_families
            .into_iter()
            .map(|family| {
                vk::DeviceQueueCreateInfo::default()
                    .queue_family_index(family)
                    .queue_priorities(&queue_priorities)
            })
            .collect();

        // Required features
        let mut features = vk::PhysicalDeviceFeatures::default();
        features.shader_int64 = vk::TRUE; // For 64-bit atomics

        // Device extensions
        let mut extension_names_raw = vec![];

        // Add swapchain extension for graphics/presentation
        #[cfg(feature = "vulkan")]
        extension_names_raw.push(ash::khr::swapchain::NAME.as_ptr());

        let extension_names: Vec<*const i8> = extension_names_raw;

        let create_info = vk::DeviceCreateInfo::default()
            .queue_create_infos(&queue_create_infos)
            .enabled_features(&features)
            .enabled_extension_names(&extension_names);

        let device = unsafe {
            instance
                .instance()
                .create_device(physical_device.handle, &create_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("{:?}", e)))?
        };
        let mut build = VulkanDeviceBuildGuard::new(device);
        let device = build.handle().clone();

        // Get queues
        let compute_queue = unsafe { device.get_device_queue(compute_family, 0) };
        #[cfg(feature = "vulkan")]
        let graphics_queue = graphics_family.map(|family| unsafe { device.get_device_queue(family, 0) });

        #[cfg(feature = "vulkan")]
        let present_queue = present_family.map(|family| unsafe { device.get_device_queue(family, 0) });
        let compute_queue_lock = Arc::new(Mutex::new(compute_queue));
        #[cfg(feature = "vulkan")]
        let graphics_queue_lock = graphics_queue.map(|queue| {
            if queue == compute_queue {
                Arc::clone(&compute_queue_lock)
            } else {
                Arc::new(Mutex::new(queue))
            }
        });
        #[cfg(feature = "vulkan")]
        let present_queue_lock = present_queue.map(|queue| {
            if queue == compute_queue {
                Arc::clone(&compute_queue_lock)
            } else if graphics_queue == Some(queue) {
                Arc::clone(
                    graphics_queue_lock
                        .as_ref()
                        .expect("graphics queue handle must have a lock"),
                )
            } else {
                Arc::new(Mutex::new(queue))
            }
        });
        #[cfg(feature = "vulkan")]
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
        build.allocator = Some(allocator);

        // Create pipeline cache
        let cache_info = vk::PipelineCacheCreateInfo::default();
        let pipeline_cache = unsafe {
            device
                .create_pipeline_cache(&cache_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Pipeline cache: {:?}", e)))?
        };
        build.pipeline_cache = Some(pipeline_cache);

        // Create command pools
        let compute_pool_info = vk::CommandPoolCreateInfo::default()
            .queue_family_index(compute_family)
            .flags(vk::CommandPoolCreateFlags::RESET_COMMAND_BUFFER);
        let compute_pool = unsafe {
            device
                .create_command_pool(&compute_pool_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Compute pool: {:?}", e)))?
        };
        build.compute_pool = Some(compute_pool);

        let transfer_pool_info = vk::CommandPoolCreateInfo::default()
            .queue_family_index(transfer_family)
            .flags(vk::CommandPoolCreateFlags::TRANSIENT);
        let transfer_pool = unsafe {
            device
                .create_command_pool(&transfer_pool_info, None)
                .map_err(|e| VulkanError::DeviceCreationFailed(format!("Transfer pool: {:?}", e)))?
        };
        build.transfer_pool = Some(transfer_pool);

        // Create graphics command pool if graphics queue exists
        #[cfg(feature = "vulkan")]
        let graphics_pool = if let Some(gfx_family) = graphics_family {
            let graphics_pool_info = vk::CommandPoolCreateInfo::default()
                .queue_family_index(gfx_family)
                .flags(vk::CommandPoolCreateFlags::RESET_COMMAND_BUFFER);
            let pool = unsafe {
                device
                    .create_command_pool(&graphics_pool_info, None)
                    .map_err(|e| VulkanError::DeviceCreationFailed(format!("Graphics pool: {:?}", e)))?
            };
            build.graphics_pool = Some(pool);
            Some(pool)
        } else {
            None
        };

        // Create swapchain loader
        #[cfg(feature = "vulkan")]
        let swapchain_loader = Some(ash::khr::swapchain::Device::new(instance.instance(), &device));

        let (device, allocator) = build.finish();
        let lifetime = Arc::new(DeviceLifetime {
            _instance: Arc::clone(&instance),
            device,
            allocator: Mutex::new(ManuallyDrop::new(allocator)),
            transfer_gate: Mutex::new(RecoveryGate::default()),
        });

        tracing::info!("Vulkan device created successfully");

        Ok(Arc::new(Self {
            lifetime,
            physical_device,
            compute_queue_family: compute_family,
            transfer_queue_family: transfer_family,
            #[cfg(feature = "vulkan")]
            graphics_queue_family: graphics_family,
            #[cfg(feature = "vulkan")]
            present_queue_family: present_family,
            #[cfg(feature = "vulkan")]
            present_surface: surface.map(|(_, owner)| owner),
            compute_queue: compute_queue_lock,
            #[cfg(feature = "vulkan")]
            graphics_queue: graphics_queue_lock,
            #[cfg(feature = "vulkan")]
            present_queue: present_queue_lock,
            pipeline_cache,
            compute_pool: Mutex::new(compute_pool),
            transfer_pool: Mutex::new(transfer_pool),
            #[cfg(feature = "vulkan")]
            graphics_pool: graphics_pool.map(Mutex::new),
            #[cfg(feature = "vulkan")]
            swapchain_loader,
            direct_compute_gate: Mutex::new(()),
            direct_compute_quarantine: Mutex::new(RecoveryQueue::default()),
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

        tracing::info!(
            "Auto-selected device: {} (score: {})",
            best.name(),
            best.compute_score()
        );

        Self::new(best)
    }

    /// Get device handle
    pub fn handle(&self) -> &ash::Device {
        self.lifetime.handle()
    }

    pub(super) fn lifetime(&self) -> Arc<DeviceLifetime> {
        Arc::clone(&self.lifetime)
    }

    /// Get physical device
    pub fn physical_device(&self) -> &VulkanPhysicalDevice {
        &self.physical_device
    }

    /// Get allocator (requires lock)
    pub fn allocator(&self) -> &Mutex<ManuallyDrop<Allocator>> {
        self.lifetime.allocator()
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

    /// Queue families which may access device-local buffers and images.
    pub fn resource_queue_families(&self) -> Vec<u32> {
        #[cfg(feature = "vulkan")]
        let graphics = self.graphics_queue_family;
        #[cfg(not(feature = "vulkan"))]
        let graphics = None;
        resource_queue_families(self.compute_queue_family, self.transfer_queue_family, graphics)
    }

    /// Get graphics queue family index (if available)
    #[cfg(feature = "vulkan")]
    pub fn graphics_queue_family(&self) -> Option<u32> {
        self.graphics_queue_family
    }

    /// Get present queue family index (if available)
    #[cfg(feature = "vulkan")]
    pub fn present_queue_family(&self) -> Option<u32> {
        self.present_queue_family
    }

    /// Check that this presentation device was created for this exact surface.
    #[cfg(feature = "vulkan")]
    pub fn supports_surface(&self, surface: &Arc<Surface>) -> bool {
        self.present_surface
            .as_ref()
            .and_then(Weak::upgrade)
            .is_some_and(|owner| Arc::ptr_eq(&owner, surface))
    }

    /// Get graphics queue (if available, requires lock)
    #[cfg(feature = "vulkan")]
    pub fn graphics_queue(&self) -> Option<&Mutex<vk::Queue>> {
        self.graphics_queue.as_deref()
    }

    /// Get present queue (if available, requires lock)
    #[cfg(feature = "vulkan")]
    pub fn present_queue(&self) -> Option<&Mutex<vk::Queue>> {
        self.present_queue.as_deref()
    }

    /// Get swapchain loader
    #[cfg(feature = "vulkan")]
    pub fn swapchain_loader(&self) -> Option<&ash::khr::swapchain::Device> {
        self.swapchain_loader.as_ref()
    }

    /// Wait for device to be idle
    pub fn wait_idle(&self) -> VulkanResult<()> {
        let _direct_compute = self.direct_compute_gate.lock();
        let mut transfer_gate = self.lifetime.transfer_gate.lock();
        if transfer_gate.phase == RecoveryPhase::Poisoned {
            return Err(VulkanError::SyncError(
                "transfer cleanup is irrecoverably poisoned".to_string(),
            ));
        }
        self.wait_hardware_idle()?;
        let direct_submissions = self
            .direct_compute_quarantine
            .lock()
            .take_if_ready(|submission| submission.pipeline.recover_after_device_idle())
            .ok_or_else(|| VulkanError::SyncError("direct compute descriptor recovery failed".to_string()))?;
        let transfer_owners = transfer_gate
            .begin_recovery()
            .ok_or_else(|| VulkanError::SyncError("transfer cleanup is irrecoverably poisoned".to_string()))?;
        drop(transfer_gate);

        for submission in direct_submissions {
            self.free_compute_command(submission.command_buffer);
            drop(submission.buffers);
            drop(submission.fence);
            drop(submission.pipeline);
        }
        if !self.finish_transfer_recovery(transfer_owners) {
            return Err(VulkanError::SyncError(
                "transfer cleanup failed; device remains quarantined".to_string(),
            ));
        }
        Ok(())
    }

    pub(crate) fn wait_hardware_idle(&self) -> VulkanResult<()> {
        let _compute_queue = self.compute_queue.lock();
        #[cfg(feature = "vulkan")]
        let graphics_queue = self
            .graphics_queue
            .as_ref()
            .filter(|queue| !Arc::ptr_eq(queue, &self.compute_queue));
        #[cfg(feature = "vulkan")]
        let _graphics_queue = graphics_queue.map(|queue| queue.lock());
        #[cfg(feature = "vulkan")]
        let _present_queue = self
            .present_queue
            .as_ref()
            .filter(|queue| {
                !Arc::ptr_eq(queue, &self.compute_queue)
                    && graphics_queue.is_none_or(|graphics| !Arc::ptr_eq(queue, graphics))
            })
            .map(|queue| queue.lock());
        unsafe {
            self.handle()
                .device_wait_idle()
                .map_err(|e| VulkanError::SyncError(format!("{:?}", e)))?;
        }
        Ok(())
    }

    pub fn direct_compute_completion_unknown(&self) -> bool {
        self.direct_compute_quarantine.lock().is_blocked()
    }

    pub(super) fn direct_compute_gate(&self) -> &Mutex<()> {
        &self.direct_compute_gate
    }

    pub fn ensure_direct_compute_available(&self) -> VulkanResult<()> {
        if self.direct_compute_completion_unknown() {
            Err(VulkanError::SyncError(
                "direct compute completion is unknown".to_string(),
            ))
        } else {
            Ok(())
        }
    }

    pub fn ensure_buffer_io_available(&self) -> VulkanResult<()> {
        self.ensure_direct_compute_available()?;
        self.ensure_transfer_available()
    }

    pub fn quarantine_direct_compute_submission(
        self: &Arc<Self>,
        pipeline: Arc<ComputePipeline>,
        fence: Fence,
        command_buffer: vk::CommandBuffer,
        buffers: Vec<Arc<VulkanBuffer>>,
    ) {
        self.direct_compute_quarantine.lock().push(DirectComputeSubmission {
            pipeline,
            fence,
            command_buffer,
            buffers,
        });
    }

    fn destroy_transfer_owner(&self, owner: TransferOwner) -> Result<(), TransferOwner> {
        match owner {
            TransferOwner::Submission { fence, command_buffer } => {
                unsafe {
                    self.handle().destroy_fence(fence, None);
                    self.handle()
                        .free_command_buffers(*self.transfer_pool.lock(), &[command_buffer]);
                }
                Ok(())
            }
            owner => self.lifetime.release_resource_owner(owner),
        }
    }

    fn finish_transfer_recovery(&self, mut owners: Vec<TransferOwner>) -> bool {
        loop {
            let mut pending = owners.into_iter();
            while let Some(owner) = pending.next() {
                if let Err(failed) = self.destroy_transfer_owner(owner) {
                    let mut gate = self.lifetime.transfer_gate.lock();
                    gate.poison(failed);
                    gate.owners.extend(pending);
                    return false;
                }
            }
            let mut gate = self.lifetime.transfer_gate.lock();
            match gate.take_recovery_batch() {
                Some(next) => owners = next,
                None => return gate.phase == RecoveryPhase::Open,
            }
        }
    }

    /// Begin a transfer command buffer
    pub fn begin_transfer_command(&self) -> VulkanResult<vk::CommandBuffer> {
        self.ensure_transfer_available()?;
        let pool = self.transfer_pool.lock();

        let alloc_info = vk::CommandBufferAllocateInfo::default()
            .command_pool(*pool)
            .level(vk::CommandBufferLevel::PRIMARY)
            .command_buffer_count(1);

        let cmd = unsafe {
            self.handle()
                .allocate_command_buffers(&alloc_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Allocate: {:?}", e)))?[0]
        };

        let begin_info = vk::CommandBufferBeginInfo::default().flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT);

        if let Err(e) = unsafe { self.handle().begin_command_buffer(cmd, &begin_info) } {
            unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
            return Err(VulkanError::CommandBufferError(format!("Begin: {:?}", e)));
        }

        Ok(cmd)
    }

    /// Submit and wait for a transfer command buffer
    pub fn submit_transfer_command(self: &Arc<Self>, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        let mut transfer_gate = self.lifetime.transfer_gate.lock();
        if transfer_gate.is_blocked() {
            unsafe {
                self.handle().free_command_buffers(*self.transfer_pool.lock(), &[cmd]);
            }
            return Err(VulkanError::SyncError(
                "transfer queue completion is unknown".to_string(),
            ));
        }
        if let Err(e) = unsafe { self.handle().end_command_buffer(cmd) } {
            unsafe { self.handle().free_command_buffers(*self.transfer_pool.lock(), &[cmd]) };
            return Err(VulkanError::CommandBufferError(format!("End: {:?}", e)));
        }

        let fence = match Fence::new(Arc::clone(self), false) {
            Ok(fence) => fence,
            Err(error) => {
                unsafe { self.handle().free_command_buffers(*self.transfer_pool.lock(), &[cmd]) };
                return Err(error);
            }
        };
        match self.submit_transfer_command_with_fence(cmd, fence, &mut transfer_gate) {
            Ok(()) => Ok(()),
            Err(FencedSubmitError::NotSubmitted(error)) => Err(error),
            Err(FencedSubmitError::CompletionUnknown(error)) => Err(error),
        }
    }

    fn submit_transfer_command_with_fence(
        &self,
        cmd: vk::CommandBuffer,
        fence: Fence,
        transfer_gate: &mut RecoveryGate<TransferOwner>,
    ) -> Result<(), FencedSubmitError> {
        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);
        let queue = self.compute_queue.lock();
        if let Err(e) = unsafe { self.handle().queue_submit(*queue, &[submit_info], fence.handle()) } {
            if submit_definitely_not_accepted(e) {
                unsafe { self.handle().free_command_buffers(*self.transfer_pool.lock(), &[cmd]) };
                return Err(FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError(
                    format!("Submit transfer: {:?}", e),
                )));
            }
            transfer_gate.admit_unknown(TransferOwner::Submission {
                fence: fence.into_raw(),
                command_buffer: cmd,
            });
            return Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError(
                format!("Submit transfer: {:?}", e),
            )));
        }
        if let Err(error) = fence.wait(u64::MAX) {
            transfer_gate.admit_unknown(TransferOwner::Submission {
                fence: fence.into_raw(),
                command_buffer: cmd,
            });
            return Err(FencedSubmitError::CompletionUnknown(error));
        }
        unsafe { self.handle().free_command_buffers(*self.transfer_pool.lock(), &[cmd]) };
        Ok(())
    }

    pub fn transfer_completion_unknown(&self) -> bool {
        self.lifetime.transfer_completion_unknown()
    }

    pub fn ensure_transfer_available(&self) -> VulkanResult<()> {
        if self.transfer_completion_unknown() {
            Err(VulkanError::SyncError(
                "transfer queue completion is unknown".to_string(),
            ))
        } else {
            Ok(())
        }
    }

    /// Begin a compute command buffer
    pub fn begin_compute_command(&self) -> VulkanResult<vk::CommandBuffer> {
        let pool = self.compute_pool.lock();

        let alloc_info = vk::CommandBufferAllocateInfo::default()
            .command_pool(*pool)
            .level(vk::CommandBufferLevel::PRIMARY)
            .command_buffer_count(1);

        let cmd = unsafe {
            self.handle()
                .allocate_command_buffers(&alloc_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Allocate: {:?}", e)))?[0]
        };

        let begin_info = vk::CommandBufferBeginInfo::default().flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT);

        if let Err(e) = unsafe { self.handle().begin_command_buffer(cmd, &begin_info) } {
            unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
            return Err(VulkanError::CommandBufferError(format!("Begin: {:?}", e)));
        }

        Ok(cmd)
    }

    /// Begin a graphics command buffer from the graphics-family pool.
    #[cfg(feature = "vulkan")]
    pub fn begin_graphics_command(&self) -> VulkanResult<vk::CommandBuffer> {
        let pool = self
            .graphics_pool
            .as_ref()
            .ok_or_else(|| VulkanError::CommandBufferError("graphics queue unavailable".into()))?
            .lock();
        let alloc_info = vk::CommandBufferAllocateInfo::default()
            .command_pool(*pool)
            .level(vk::CommandBufferLevel::PRIMARY)
            .command_buffer_count(1);
        let cmd = unsafe {
            self.handle()
                .allocate_command_buffers(&alloc_info)
                .map_err(|e| VulkanError::CommandBufferError(format!("Allocate graphics: {:?}", e)))?[0]
        };
        let begin_info = vk::CommandBufferBeginInfo::default().flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT);
        if let Err(e) = unsafe { self.handle().begin_command_buffer(cmd, &begin_info) } {
            unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
            return Err(VulkanError::CommandBufferError(format!("Begin graphics: {:?}", e)));
        }
        Ok(cmd)
    }

    pub fn end_compute_command(&self, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        unsafe {
            self.handle()
                .end_command_buffer(cmd)
                .map_err(|e| VulkanError::CommandBufferError(format!("End: {:?}", e)))
        }
    }

    /// Submit and wait for a compute command buffer.
    pub fn submit_compute_command(&self, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);
        let queue = self.compute_queue.lock();

        unsafe {
            if let Err(e) = self.handle().queue_submit(*queue, &[submit_info], vk::Fence::null()) {
                drop(queue);
                self.handle().free_command_buffers(*self.compute_pool.lock(), &[cmd]);
                return Err(VulkanError::CommandBufferError(format!("Submit: {:?}", e)));
            }
            self.handle()
                .queue_wait_idle(*queue)
                .map_err(|e| VulkanError::SyncError(format!("{:?}", e)))?;
            self.handle().free_command_buffers(*self.compute_pool.lock(), &[cmd]);
        }
        Ok(())
    }

    /// Submit a compute command buffer with a real fence and wait for completion.
    ///
    /// The command buffer is freed exactly once after a successful infinite wait.
    /// If submission or its wait fails, it is intentionally left allocated because
    /// the driver may have accepted the command before reporting the error.
    pub fn submit_compute_command_with_fence(
        &self,
        cmd: vk::CommandBuffer,
        fence: &Fence,
    ) -> Result<(), FencedSubmitError> {
        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);
        let queue = self.compute_queue.lock();
        let submit_result = unsafe { self.handle().queue_submit(*queue, &[submit_info], fence.handle()) };
        if let Err(e) = submit_result {
            if submit_definitely_not_accepted(e) {
                let pool = self.compute_pool.lock();
                unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
                return Err(FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError(
                    format!("Submit: {:?}", e),
                )));
            }
            return Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError(
                format!("Submit: {:?}", e),
            )));
        }
        drop(queue);

        if let Err(e) = fence.wait(u64::MAX) {
            return Err(FencedSubmitError::CompletionUnknown(e));
        }

        let pool = self.compute_pool.lock();
        unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
        Ok(())
    }

    /// Submit a compute command buffer with a real fence WITHOUT waiting for
    /// completion. Returns as soon as `vkQueueSubmit` accepts the work, so
    /// the caller receives a pending (not-yet-signaled) fence and owns all
    /// waiting/timeout policy via a separate `Fence::wait` call.
    ///
    /// The command buffer is intentionally NOT freed here (freeing while the
    /// GPU may still be executing it is undefined behaviour) — the caller is
    /// responsible for keeping the associated resources alive until the
    /// fence is known to be signaled (e.g. by quarantining them the same way
    /// `FencedSubmitError::CompletionUnknown` is already handled by callers
    /// of `submit_compute_command_with_fence`).
    ///
    /// Added to close the gap documented in doc/08_tracking/bug/
    /// vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md:
    /// previously every compute submit path blocked on `fence.wait(u64::MAX)`
    /// internally, so a host-side fence timeout could never fire.
    pub fn submit_compute_command_no_wait(
        &self,
        cmd: vk::CommandBuffer,
        fence: &Fence,
    ) -> Result<(), FencedSubmitError> {
        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);
        let queue = self.compute_queue.lock();
        let submit_result = unsafe { self.handle().queue_submit(*queue, &[submit_info], fence.handle()) };
        if let Err(e) = submit_result {
            if submit_definitely_not_accepted(e) {
                let pool = self.compute_pool.lock();
                unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
                return Err(FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError(
                    format!("Submit: {:?}", e),
                )));
            }
            return Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError(
                format!("Submit: {:?}", e),
            )));
        }
        // Deliberately no `fence.wait(...)` here — that is the entire point
        // of this non-blocking variant. The caller waits separately, with
        // its own timeout, via `rt_vulkan_wait_fence`.
        Ok(())
    }

    #[cfg(feature = "vulkan")]
    pub fn submit_graphics_command_with_fence(
        &self,
        cmd: vk::CommandBuffer,
        fence: &Fence,
    ) -> Result<(), FencedSubmitError> {
        let queue = self.graphics_queue.as_ref().ok_or_else(|| {
            FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError("graphics queue unavailable".into()))
        })?;
        let pool = self.graphics_pool.as_ref().ok_or_else(|| {
            FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError("graphics pool unavailable".into()))
        })?;
        let cmd_buffers = [cmd];
        let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);
        let queue = queue.lock();
        if let Err(e) = unsafe { self.handle().queue_submit(*queue, &[submit_info], fence.handle()) } {
            if submit_definitely_not_accepted(e) {
                unsafe { self.handle().free_command_buffers(*pool.lock(), &[cmd]) };
                return Err(FencedSubmitError::NotSubmitted(VulkanError::CommandBufferError(
                    format!("Submit graphics: {:?}", e),
                )));
            }
            return Err(FencedSubmitError::CompletionUnknown(VulkanError::CommandBufferError(
                format!("Submit graphics: {:?}", e),
            )));
        }
        drop(queue);
        if let Err(e) = fence.wait(u64::MAX) {
            return Err(FencedSubmitError::CompletionUnknown(e));
        }
        unsafe { self.handle().free_command_buffers(*pool.lock(), &[cmd]) };
        Ok(())
    }

    pub fn free_compute_command(&self, cmd: vk::CommandBuffer) {
        let pool = self.compute_pool.lock();
        unsafe { self.handle().free_command_buffers(*pool, &[cmd]) };
    }

    #[cfg(feature = "vulkan")]
    pub fn free_graphics_command(&self, cmd: vk::CommandBuffer) -> VulkanResult<()> {
        let pool = self
            .graphics_pool
            .as_ref()
            .ok_or_else(|| VulkanError::CommandBufferError("graphics pool unavailable".into()))?;
        unsafe { self.handle().free_command_buffers(*pool.lock(), &[cmd]) };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{resource_queue_families, submit_definitely_not_accepted, RecoveryGate, RecoveryPhase, RecoveryQueue};
    use ash::vk;
    use parking_lot::Mutex;
    use std::sync::mpsc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    #[derive(Debug)]
    struct Owner {
        id: usize,
        drops: Arc<AtomicUsize>,
    }

    impl Drop for Owner {
        fn drop(&mut self) {
            self.drops.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn owner(id: usize, drops: &Arc<AtomicUsize>) -> Owner {
        Owner {
            id,
            drops: Arc::clone(drops),
        }
    }

    #[test]
    fn resource_queue_families_are_deduplicated() {
        assert_eq!(resource_queue_families(2, 2, Some(2)), vec![2]);
        assert_eq!(resource_queue_families(2, 5, Some(7)), vec![2, 5, 7]);
    }

    #[test]
    fn submit_oom_is_definitely_not_accepted() {
        assert!(submit_definitely_not_accepted(vk::Result::ERROR_OUT_OF_HOST_MEMORY));
        assert!(submit_definitely_not_accepted(vk::Result::ERROR_OUT_OF_DEVICE_MEMORY));
        assert!(!submit_definitely_not_accepted(vk::Result::ERROR_DEVICE_LOST));
        assert!(!submit_definitely_not_accepted(vk::Result::ERROR_UNKNOWN));
    }

    #[test]
    fn failed_readiness_preserves_every_direct_owner() {
        let drops = Arc::new(AtomicUsize::new(0));
        let mut queue = RecoveryQueue::default();
        queue.push(owner(1, &drops));
        queue.push(owner(2, &drops));

        assert!(queue.take_if_ready(|owner| owner.id != 2).is_none());
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        assert!(queue.is_blocked());

        drop(queue.take_if_ready(|_| true).unwrap());
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        assert!(!queue.is_blocked());
    }

    #[test]
    fn successful_recovery_reopens_gate_for_later_admission() {
        let drops = Arc::new(AtomicUsize::new(0));
        let mut gate = RecoveryGate::default();
        gate.admit_unknown(owner(1, &drops));
        assert_eq!(gate.phase, RecoveryPhase::Blocked);
        drop(gate.begin_recovery().unwrap());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert!(gate.take_recovery_batch().is_none());
        assert_eq!(gate.phase, RecoveryPhase::Open);

        gate.admit_unknown(owner(2, &drops));
        drop(gate.begin_recovery().unwrap());
        assert!(gate.take_recovery_batch().is_none());
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        assert_eq!(gate.phase, RecoveryPhase::Open);
    }

    #[test]
    fn failed_release_poison_preserves_all_owned_entries() {
        let drops = Arc::new(AtomicUsize::new(0));
        let mut gate = RecoveryGate::default();
        gate.admit_unknown(owner(1, &drops));
        gate.admit_unknown(owner(2, &drops));
        let mut drained = gate.begin_recovery().unwrap().into_iter();

        gate.poison(drained.next().unwrap());
        gate.owners.extend(drained);

        assert_eq!(gate.phase, RecoveryPhase::Poisoned);
        assert_eq!(gate.owners.len(), 2);
        assert!(gate.begin_recovery().is_none());
        assert_eq!(drops.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn blocked_lifetime_gate_never_enters_normal_device_destruction() {
        let source = include_str!("device.rs");
        let lifetime_drop = source
            .split("impl Drop for DeviceLifetime")
            .nth(1)
            .unwrap()
            .split("struct RecoveryQueue")
            .next()
            .unwrap();
        let blocked = lifetime_drop.find("if transfer_gate.is_blocked()").unwrap();
        let leaked_instance = lifetime_drop
            .find("std::mem::forget(Arc::clone(&self._instance))")
            .unwrap();
        let early_return = lifetime_drop[leaked_instance..].find("return;").unwrap() + leaked_instance;
        let destroy = lifetime_drop.find("self.device.destroy_device(None)").unwrap();
        assert!(blocked < leaked_instance && leaked_instance < early_return && early_return < destroy);
    }

    #[test]
    fn stale_idle_admission_waits_for_the_shared_recovery_lock() {
        let drops = Arc::new(AtomicUsize::new(0));
        let gate = Arc::new(Mutex::new(RecoveryGate::default()));
        let mut recovery = gate.lock();
        recovery.phase = RecoveryPhase::Recovering;
        let (started_tx, started_rx) = mpsc::channel();
        let (admitted_tx, admitted_rx) = mpsc::channel();
        let worker_gate = Arc::clone(&gate);
        let worker_drops = Arc::clone(&drops);
        let worker = std::thread::spawn(move || {
            started_tx.send(()).unwrap();
            worker_gate.lock().retain_if_closed(owner(1, &worker_drops)).unwrap();
            admitted_tx.send(()).unwrap();
        });

        started_rx.recv().unwrap();
        assert!(admitted_rx.recv_timeout(Duration::from_millis(50)).is_err());
        drop(recovery);
        admitted_rx.recv_timeout(Duration::from_secs(1)).unwrap();
        worker.join().unwrap();
        assert_eq!(gate.lock().owners.len(), 1);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn quarantined_graph_has_no_strong_path_to_vulkan_device() {
        let device = include_str!("device.rs");
        let pipeline = include_str!("pipeline.rs");
        let buffer = include_str!("buffer.rs");
        let sync = include_str!("sync.rs");
        let transfer_owner = device
            .split("pub(super) enum TransferOwner")
            .nth(1)
            .unwrap()
            .split("pub enum FencedSubmitError")
            .next()
            .unwrap();

        assert!(!transfer_owner.contains("Arc<"));
        assert!(pipeline.contains("device: Weak<VulkanDevice>"));
        assert!(pipeline.contains("lifetime: Arc<DeviceLifetime>"));
        assert!(buffer.contains("device: Weak<VulkanDevice>"));
        assert!(buffer.contains("lifetime: Arc<DeviceLifetime>"));
        assert!(sync.contains("pub struct Fence {\n    lifetime: Arc<DeviceLifetime>"));
    }

    #[test]
    fn build_guard_owns_partial_children_before_device_lifetime() {
        let source = include_str!("device.rs");
        let guard = source
            .find("let mut build = VulkanDeviceBuildGuard::new(device);")
            .unwrap();
        let pools = source.find("build.transfer_pool = Some(transfer_pool);").unwrap();
        let finish = source.find("let (device, allocator) = build.finish();").unwrap();
        let lifetime = source.find("let lifetime = Arc::new(DeviceLifetime").unwrap();
        assert!(guard < pools && pools < finish && finish < lifetime);
    }
}

impl Drop for VulkanDevice {
    fn drop(&mut self) {
        if let Err(error) = self.wait_idle() {
            tracing::error!("Leaking Vulkan device after failed idle recovery: {error}");
            self.direct_compute_quarantine.get_mut().leak_all();
            std::mem::forget(Arc::clone(&self.lifetime));
            return;
        }
        unsafe {
            // Destroy command pools
            self.handle().destroy_command_pool(*self.transfer_pool.lock(), None);
            self.handle().destroy_command_pool(*self.compute_pool.lock(), None);

            // Destroy graphics pool if it exists
            #[cfg(feature = "vulkan")]
            if let Some(ref pool) = self.graphics_pool {
                self.handle().destroy_command_pool(*pool.lock(), None);
            }

            self.handle().destroy_pipeline_cache(self.pipeline_cache, None);
        }
    }
}
