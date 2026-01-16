//! Vulkan buffer management

use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use gpu_allocator::vulkan::{Allocation, AllocationCreateDesc, AllocationScheme};
use gpu_allocator::MemoryLocation;
use std::sync::Arc;

/// Buffer usage flags
#[derive(Debug, Clone, Copy)]
pub struct BufferUsage {
    pub storage: bool, // Storage buffer (compute shaders)
    pub uniform: bool, // Uniform buffer
    pub transfer_src: bool,
    pub transfer_dst: bool,
}

impl BufferUsage {
    /// Storage buffer for compute shaders (most common)
    pub fn storage() -> Self {
        Self {
            storage: true,
            uniform: false,
            transfer_src: true,
            transfer_dst: true,
        }
    }

    /// Uniform buffer for read-only data
    pub fn uniform() -> Self {
        Self {
            storage: false,
            uniform: true,
            transfer_src: false,
            transfer_dst: true,
        }
    }

    /// Convert to Vulkan buffer usage flags
    fn to_vk_usage(&self) -> vk::BufferUsageFlags {
        let mut flags = vk::BufferUsageFlags::empty();
        if self.storage {
            flags |= vk::BufferUsageFlags::STORAGE_BUFFER;
        }
        if self.uniform {
            flags |= vk::BufferUsageFlags::UNIFORM_BUFFER;
        }
        if self.transfer_src {
            flags |= vk::BufferUsageFlags::TRANSFER_SRC;
        }
        if self.transfer_dst {
            flags |= vk::BufferUsageFlags::TRANSFER_DST;
        }
        flags
    }
}

/// Vulkan buffer (device-local)
pub struct VulkanBuffer {
    device: Arc<VulkanDevice>,
    buffer: vk::Buffer,
    allocation: Option<Allocation>,
    size: u64,
    usage: BufferUsage,
}

impl VulkanBuffer {
    /// Create a new device-local buffer
    pub fn new(device: Arc<VulkanDevice>, size: u64, usage: BufferUsage) -> VulkanResult<Self> {
        let buffer_info = vk::BufferCreateInfo::default()
            .size(size)
            .usage(usage.to_vk_usage())
            .sharing_mode(vk::SharingMode::EXCLUSIVE);

        let buffer = unsafe {
            device
                .handle()
                .create_buffer(&buffer_info, None)
                .map_err(|e| VulkanError::BufferError(format!("Create: {:?}", e)))?
        };

        let requirements = unsafe { device.handle().get_buffer_memory_requirements(buffer) };

        let allocation = device.allocator().lock().allocate(&AllocationCreateDesc {
            name: "device_buffer",
            requirements,
            location: MemoryLocation::GpuOnly,
            linear: true,
            allocation_scheme: AllocationScheme::GpuAllocatorManaged,
        })?;

        unsafe {
            device
                .handle()
                .bind_buffer_memory(buffer, allocation.memory(), allocation.offset())
                .map_err(|e| VulkanError::BufferError(format!("Bind: {:?}", e)))?;
        }

        Ok(Self {
            device,
            buffer,
            allocation: Some(allocation),
            size,
            usage,
        })
    }

    /// Get buffer handle
    pub fn handle(&self) -> vk::Buffer {
        self.buffer
    }

    /// Get size in bytes
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Upload data to this buffer (creates staging buffer internally)
    pub fn upload(&self, data: &[u8]) -> VulkanResult<()> {
        if data.len() > self.size as usize {
            return Err(VulkanError::BufferTooSmall);
        }

        // Create staging buffer
        let staging = StagingBuffer::new(self.device.clone(), data.len() as u64)?;
        staging.write(data)?;

        // Copy from staging to device buffer
        self.copy_from_staging(&staging, data.len() as u64)?;

        Ok(())
    }

    /// Download data from this buffer
    pub fn download(&self, size: u64) -> VulkanResult<Vec<u8>> {
        let staging = StagingBuffer::new(self.device.clone(), size)?;
        self.copy_to_staging(&staging, size)?;
        staging.read(size as usize)
    }

    fn copy_from_staging(&self, staging: &StagingBuffer, size: u64) -> VulkanResult<()> {
        let cmd = self.device.begin_transfer_command()?;

        let region = vk::BufferCopy::default().size(size);

        unsafe {
            self.device
                .handle()
                .cmd_copy_buffer(cmd, staging.handle(), self.buffer, &[region]);
        }

        self.device.submit_transfer_command(cmd)?;
        Ok(())
    }

    fn copy_to_staging(&self, staging: &StagingBuffer, size: u64) -> VulkanResult<()> {
        let cmd = self.device.begin_transfer_command()?;

        let region = vk::BufferCopy::default().size(size);

        unsafe {
            self.device
                .handle()
                .cmd_copy_buffer(cmd, self.buffer, staging.handle(), &[region]);
        }

        self.device.submit_transfer_command(cmd)?;
        Ok(())
    }
}

impl Drop for VulkanBuffer {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_buffer(self.buffer, None);
        }
        if let Some(allocation) = self.allocation.take() {
            self.device
                .allocator()
                .lock()
                .free(allocation)
                .unwrap_or_else(|e| tracing::error!("Failed to free buffer allocation: {:?}", e));
        }
    }
}

/// Staging buffer (host-visible) for CPU-GPU transfers
pub struct StagingBuffer {
    device: Arc<VulkanDevice>,
    buffer: vk::Buffer,
    allocation: Option<Allocation>,
    size: u64,
}

impl StagingBuffer {
    pub fn new(device: Arc<VulkanDevice>, size: u64) -> VulkanResult<Self> {
        let buffer_info = vk::BufferCreateInfo::default()
            .size(size)
            .usage(vk::BufferUsageFlags::TRANSFER_SRC | vk::BufferUsageFlags::TRANSFER_DST)
            .sharing_mode(vk::SharingMode::EXCLUSIVE);

        let buffer = unsafe {
            device
                .handle()
                .create_buffer(&buffer_info, None)
                .map_err(|e| VulkanError::BufferError(format!("Create staging: {:?}", e)))?
        };

        let requirements = unsafe { device.handle().get_buffer_memory_requirements(buffer) };

        let allocation = device.allocator().lock().allocate(&AllocationCreateDesc {
            name: "staging_buffer",
            requirements,
            location: MemoryLocation::CpuToGpu,
            linear: true,
            allocation_scheme: AllocationScheme::GpuAllocatorManaged,
        })?;

        unsafe {
            device
                .handle()
                .bind_buffer_memory(buffer, allocation.memory(), allocation.offset())
                .map_err(|e| VulkanError::BufferError(format!("Bind staging: {:?}", e)))?;
        }

        Ok(Self {
            device,
            buffer,
            allocation: Some(allocation),
            size,
        })
    }

    pub fn handle(&self) -> vk::Buffer {
        self.buffer
    }

    /// Write data to staging buffer
    pub fn write(&self, data: &[u8]) -> VulkanResult<()> {
        if let Some(allocation) = &self.allocation {
            if let Some(ptr) = allocation.mapped_ptr() {
                unsafe {
                    std::ptr::copy_nonoverlapping(data.as_ptr(), ptr.as_ptr() as *mut u8, data.len());
                }
                Ok(())
            } else {
                Err(VulkanError::NotMapped)
            }
        } else {
            Err(VulkanError::NotMapped)
        }
    }

    /// Read data from staging buffer
    pub fn read(&self, size: usize) -> VulkanResult<Vec<u8>> {
        if let Some(allocation) = &self.allocation {
            if let Some(ptr) = allocation.mapped_ptr() {
                let mut data = vec![0u8; size];
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr.as_ptr() as *const u8, data.as_mut_ptr(), size);
                }
                Ok(data)
            } else {
                Err(VulkanError::NotMapped)
            }
        } else {
            Err(VulkanError::NotMapped)
        }
    }
}

impl Drop for StagingBuffer {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_buffer(self.buffer, None);
        }
        if let Some(allocation) = self.allocation.take() {
            self.device
                .allocator()
                .lock()
                .free(allocation)
                .unwrap_or_else(|e| tracing::error!("Failed to free staging allocation: {:?}", e));
        }
    }
}
