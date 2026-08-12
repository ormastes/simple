//! Vulkan buffer management

use super::device::{DeviceLifetime, TransferOwner, VulkanDevice};
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use gpu_allocator::vulkan::{Allocation, AllocationCreateDesc, AllocationScheme};
use gpu_allocator::MemoryLocation;
use std::sync::{Arc, Weak};

const MAX_STRIDED_TRANSFER_ROWS: u64 = 16_384;

/// Buffer usage flags
#[derive(Debug, Clone, Copy)]
pub struct BufferUsage {
    pub storage: bool, // Storage buffer (compute shaders)
    pub uniform: bool, // Uniform buffer
    pub vertex: bool,
    pub index: bool,
    pub transfer_src: bool,
    pub transfer_dst: bool,
}

impl BufferUsage {
    /// Storage buffer for compute shaders (most common)
    pub fn storage() -> Self {
        Self {
            storage: true,
            uniform: false,
            vertex: false,
            index: false,
            transfer_src: true,
            transfer_dst: true,
        }
    }

    /// Uniform buffer for read-only data
    pub fn uniform() -> Self {
        Self {
            storage: false,
            uniform: true,
            vertex: false,
            index: false,
            transfer_src: false,
            transfer_dst: true,
        }
    }

    /// Convert to Vulkan buffer usage flags
    fn to_vk_usage(&self) -> vk::BufferUsageFlags {
        let mut flags = vk::BufferUsageFlags::empty();
        if self.storage {
            // Storage buffers are device-local and upload/download always use
            // staging copies, so both transfer directions are mandatory.
            flags |= vk::BufferUsageFlags::STORAGE_BUFFER
                | vk::BufferUsageFlags::TRANSFER_SRC
                | vk::BufferUsageFlags::TRANSFER_DST;
        }
        if self.uniform {
            flags |= vk::BufferUsageFlags::UNIFORM_BUFFER;
        }
        if self.vertex {
            flags |= vk::BufferUsageFlags::VERTEX_BUFFER;
        }
        if self.index {
            flags |= vk::BufferUsageFlags::INDEX_BUFFER;
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

fn checked_upload_end(buffer_size: u64, data_len: usize, offset: u64) -> VulkanResult<u64> {
    let data_len = u64::try_from(data_len).map_err(|_| VulkanError::BufferTooSmall)?;
    let end = offset.checked_add(data_len).ok_or(VulkanError::BufferTooSmall)?;
    if end > buffer_size {
        return Err(VulkanError::BufferTooSmall);
    }
    Ok(end)
}

fn checked_download_end(buffer_size: u64, offset: u64, size: u64) -> VulkanResult<u64> {
    let end = offset.checked_add(size).ok_or(VulkanError::BufferTooSmall)?;
    if end > buffer_size {
        return Err(VulkanError::BufferTooSmall);
    }
    Ok(end)
}

fn checked_strided_download(
    buffer_size: u64,
    src_offset: u64,
    row_bytes: u64,
    row_count: u64,
    src_stride: u64,
) -> VulkanResult<(u64, u64)> {
    if row_count == 0 || row_bytes == 0 {
        checked_download_end(buffer_size, src_offset, 0)?;
        return Ok((0, src_offset));
    }
    if row_count > MAX_STRIDED_TRANSFER_ROWS {
        return Err(VulkanError::BufferTooSmall);
    }
    if src_stride < row_bytes {
        return Err(VulkanError::BufferTooSmall);
    }
    let packed_size = row_bytes.checked_mul(row_count).ok_or(VulkanError::BufferTooSmall)?;
    let last_offset = src_stride
        .checked_mul(row_count - 1)
        .and_then(|delta| src_offset.checked_add(delta))
        .ok_or(VulkanError::BufferTooSmall)?;
    let end = checked_download_end(buffer_size, last_offset, row_bytes)?;
    Ok((packed_size, end))
}

fn checked_region_download(buffer_size: u64, regions: &[(u64, u64, u64, u64)]) -> VulkanResult<(u64, u64)> {
    if regions.len() > 256 {
        return Err(VulkanError::BufferTooSmall);
    }
    let mut packed_size = 0u64;
    let mut total_rows = 0u64;
    for &(src_offset, row_bytes, row_count, src_stride) in regions {
        let (region_size, _) = checked_strided_download(buffer_size, src_offset, row_bytes, row_count, src_stride)?;
        packed_size = packed_size
            .checked_add(region_size)
            .ok_or(VulkanError::BufferTooSmall)?;
        total_rows = total_rows.checked_add(row_count).ok_or(VulkanError::BufferTooSmall)?;
        if total_rows > MAX_STRIDED_TRANSFER_ROWS {
            return Err(VulkanError::BufferTooSmall);
        }
    }
    Ok((packed_size, total_rows))
}

fn download_barrier_masks(
    usage: BufferUsage,
) -> (
    vk::PipelineStageFlags,
    vk::AccessFlags,
    vk::PipelineStageFlags,
    vk::AccessFlags,
) {
    let mut src_stage = vk::PipelineStageFlags::empty();
    let mut src_access = vk::AccessFlags::empty();
    if usage.storage {
        src_stage |= vk::PipelineStageFlags::COMPUTE_SHADER;
        src_access |= vk::AccessFlags::SHADER_WRITE;
    }
    if usage.transfer_dst {
        src_stage |= vk::PipelineStageFlags::TRANSFER;
        src_access |= vk::AccessFlags::TRANSFER_WRITE;
    }
    if src_stage.is_empty() {
        src_stage = vk::PipelineStageFlags::ALL_COMMANDS;
        src_access = vk::AccessFlags::MEMORY_WRITE;
    }
    (
        src_stage,
        src_access,
        vk::PipelineStageFlags::TRANSFER,
        vk::AccessFlags::TRANSFER_READ,
    )
}

#[cfg(test)]
mod tests {
    use super::{
        checked_download_end, checked_region_download, checked_strided_download, checked_upload_end,
        download_barrier_masks, BufferUsage,
    };
    use ash::vk;

    #[test]
    fn storage_usage_includes_staging_transfer_directions() {
        let flags = BufferUsage {
            storage: true,
            uniform: false,
            vertex: false,
            index: false,
            transfer_src: false,
            transfer_dst: false,
        }
        .to_vk_usage();

        assert!(flags.contains(vk::BufferUsageFlags::STORAGE_BUFFER));
        assert!(flags.contains(vk::BufferUsageFlags::TRANSFER_SRC));
        assert!(flags.contains(vk::BufferUsageFlags::TRANSFER_DST));
    }

    #[test]
    fn upload_range_accepts_offsets_and_rejects_overflow() {
        assert_eq!(checked_upload_end(16, 6, 5).unwrap(), 11);
        assert_eq!(checked_upload_end(16, 0, 16).unwrap(), 16);
        assert!(checked_upload_end(16, 2, 15).is_err());
        assert!(checked_upload_end(16, 1, u64::MAX).is_err());
    }

    #[test]
    fn download_range_accepts_offsets_and_rejects_overflow() {
        assert_eq!(checked_download_end(16, 5, 6).unwrap(), 11);
        assert_eq!(checked_download_end(16, 16, 0).unwrap(), 16);
        assert!(checked_download_end(16, 15, 2).is_err());
        assert!(checked_download_end(16, u64::MAX, 1).is_err());
    }

    #[test]
    fn region_download_sums_packed_bytes_and_rejects_bad_members() {
        let regions = [(4, 4, 2, 16), (40, 8, 3, 12)];
        assert_eq!(checked_region_download(80, &regions).unwrap(), (32, 5));
        assert!(checked_region_download(64, &[(60, 8, 1, 8)]).is_err());
        assert!(checked_region_download(64, &[(0, 8, 2, 4)]).is_err());
        assert!(checked_region_download(1, &[(0, 1, 16_385, 1)]).is_err());
        assert!(checked_region_download(64, &vec![(0, 1, 1, 1); 257]).is_err());
    }

    #[test]
    fn strided_download_layout_is_bounded_and_packed() {
        assert_eq!(checked_strided_download(64, 5, 4, 3, 8).unwrap(), (12, 25));
        assert_eq!(checked_strided_download(64, 64, 0, 0, 0).unwrap(), (0, 64));
        assert!(checked_strided_download(64, 5, 5, 2, 4).is_err());
        assert!(checked_strided_download(16, 12, 4, 2, 4).is_err());
        assert!(checked_strided_download(20_000, 0, 1, 20_000, 1).is_err());
        assert!(checked_strided_download(u64::MAX, 0, u64::MAX, 2, u64::MAX).is_err());
    }

    #[test]
    fn storage_download_barrier_makes_compute_writes_visible_to_transfer() {
        let (src_stage, src_access, dst_stage, dst_access) = download_barrier_masks(BufferUsage::storage());

        assert!(src_stage.contains(vk::PipelineStageFlags::COMPUTE_SHADER));
        assert!(src_stage.contains(vk::PipelineStageFlags::TRANSFER));
        assert!(src_access.contains(vk::AccessFlags::SHADER_WRITE));
        assert!(src_access.contains(vk::AccessFlags::TRANSFER_WRITE));
        assert_eq!(dst_stage, vk::PipelineStageFlags::TRANSFER);
        assert_eq!(dst_access, vk::AccessFlags::TRANSFER_READ);
    }
}

/// Vulkan buffer (device-local)
pub struct VulkanBuffer {
    device: Weak<VulkanDevice>,
    lifetime: Arc<DeviceLifetime>,
    buffer: vk::Buffer,
    allocation: Option<Allocation>,
    size: u64,
    usage: BufferUsage,
}

impl VulkanBuffer {
    /// Create a new device-local buffer
    pub fn new(device: Arc<VulkanDevice>, size: u64, usage: BufferUsage) -> VulkanResult<Self> {
        let queue_families = device.resource_queue_families();
        let mut buffer_info = vk::BufferCreateInfo::default()
            .size(size)
            .usage(usage.to_vk_usage())
            .sharing_mode(vk::SharingMode::EXCLUSIVE);
        if queue_families.len() > 1 {
            buffer_info = buffer_info
                .sharing_mode(vk::SharingMode::CONCURRENT)
                .queue_family_indices(&queue_families);
        }

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
            device: Arc::downgrade(&device),
            lifetime: device.lifetime(),
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

    fn device(&self) -> VulkanResult<Arc<VulkanDevice>> {
        self.device
            .upgrade()
            .ok_or_else(|| VulkanError::SyncError("Vulkan device owner has been released".to_string()))
    }

    /// Upload data to this buffer (creates staging buffer internally)
    pub fn upload(&self, data: &[u8]) -> VulkanResult<()> {
        self.upload_at(data, 0)
    }

    /// Upload data at a byte offset (creates staging buffer internally).
    pub fn upload_at(&self, data: &[u8], offset: u64) -> VulkanResult<()> {
        checked_upload_end(self.size, data.len(), offset)?;
        let device = self.device()?;
        let _direct_compute = device.direct_compute_gate().lock();
        device.ensure_buffer_io_available()?;
        if data.is_empty() {
            return Ok(());
        }
        // Create staging buffer
        let staging = StagingBuffer::new(Arc::clone(&device), data.len() as u64)?;
        staging.write(data)?;

        // Copy from staging to device buffer
        self.copy_from_staging(&device, &staging, data.len() as u64, offset)?;

        Ok(())
    }

    /// Download data from this buffer
    pub fn download(&self, size: u64) -> VulkanResult<Vec<u8>> {
        self.download_range(0, size)
    }

    /// Download an exact byte range from this buffer.
    pub fn download_range(&self, offset: u64, size: u64) -> VulkanResult<Vec<u8>> {
        checked_download_end(self.size, offset, size)?;
        if size == 0 {
            return Ok(Vec::new());
        }
        let device = self.device()?;
        let _direct_compute = device.direct_compute_gate().lock();
        device.ensure_buffer_io_available()?;
        let staging = StagingBuffer::new(Arc::clone(&device), size)?;
        self.copy_to_staging(&device, &staging, offset, size)?;
        staging.read(size as usize)
    }

    /// Download rows into one tightly packed host result using one transfer.
    pub fn download_strided(
        &self,
        src_offset: u64,
        row_bytes: u64,
        row_count: u64,
        src_stride: u64,
    ) -> VulkanResult<Vec<u8>> {
        let (packed_size, _) = checked_strided_download(self.size, src_offset, row_bytes, row_count, src_stride)?;
        if packed_size == 0 {
            return Ok(Vec::new());
        }
        let device = self.device()?;
        let _direct_compute = device.direct_compute_gate().lock();
        device.ensure_buffer_io_available()?;
        let staging = StagingBuffer::new(Arc::clone(&device), packed_size)?;
        self.copy_rows_to_staging(&device, &staging, src_offset, row_bytes, row_count, src_stride)?;
        staging.read(packed_size as usize)
    }

    /// Download multiple disjoint row regions through one staging buffer and
    /// one transfer submission. Each tuple is
    /// (source offset, row bytes, row count, source stride).
    pub fn download_regions(&self, regions: &[(u64, u64, u64, u64)]) -> VulkanResult<Vec<u8>> {
        let (packed_size, _) = checked_region_download(self.size, regions)?;
        if packed_size == 0 {
            return Ok(Vec::new());
        }
        let device = self.device()?;
        let _direct_compute = device.direct_compute_gate().lock();
        device.ensure_buffer_io_available()?;
        let staging = StagingBuffer::new(Arc::clone(&device), packed_size)?;
        self.copy_regions_to_staging(&device, &staging, regions)?;
        staging.read(packed_size as usize)
    }

    fn copy_from_staging(
        &self,
        device: &Arc<VulkanDevice>,
        staging: &StagingBuffer,
        size: u64,
        dst_offset: u64,
    ) -> VulkanResult<()> {
        let cmd = device.begin_transfer_command()?;

        let region = vk::BufferCopy::default().dst_offset(dst_offset).size(size);

        unsafe {
            device
                .handle()
                .cmd_copy_buffer(cmd, staging.handle(), self.buffer, &[region]);

            let mut dst_stage = vk::PipelineStageFlags::empty();
            let mut dst_access = vk::AccessFlags::empty();
            if self.usage.vertex || self.usage.index {
                dst_stage |= vk::PipelineStageFlags::VERTEX_INPUT;
                dst_access |= vk::AccessFlags::VERTEX_ATTRIBUTE_READ | vk::AccessFlags::INDEX_READ;
            }
            if self.usage.uniform || self.usage.storage {
                dst_stage |= vk::PipelineStageFlags::VERTEX_SHADER
                    | vk::PipelineStageFlags::FRAGMENT_SHADER
                    | vk::PipelineStageFlags::COMPUTE_SHADER;
                dst_access |=
                    vk::AccessFlags::UNIFORM_READ | vk::AccessFlags::SHADER_READ | vk::AccessFlags::SHADER_WRITE;
            }
            if dst_stage.is_empty() {
                dst_stage = vk::PipelineStageFlags::ALL_COMMANDS;
                dst_access = vk::AccessFlags::MEMORY_READ;
            }
            let barrier = vk::BufferMemoryBarrier::default()
                .src_access_mask(vk::AccessFlags::TRANSFER_WRITE)
                .dst_access_mask(dst_access)
                .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .buffer(self.buffer)
                .offset(dst_offset)
                .size(size);
            device.handle().cmd_pipeline_barrier(
                cmd,
                vk::PipelineStageFlags::TRANSFER,
                dst_stage,
                vk::DependencyFlags::empty(),
                &[],
                &[barrier],
                &[],
            );
        }

        device.submit_transfer_command(cmd)?;
        Ok(())
    }

    fn copy_to_staging(
        &self,
        device: &Arc<VulkanDevice>,
        staging: &StagingBuffer,
        src_offset: u64,
        size: u64,
    ) -> VulkanResult<()> {
        let cmd = device.begin_transfer_command()?;

        let region = vk::BufferCopy::default().src_offset(src_offset).size(size);
        let (src_stage, src_access, dst_stage, dst_access) = download_barrier_masks(self.usage);

        unsafe {
            let barrier = vk::BufferMemoryBarrier::default()
                .src_access_mask(src_access)
                .dst_access_mask(dst_access)
                .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .buffer(self.buffer)
                .offset(src_offset)
                .size(size);
            device.handle().cmd_pipeline_barrier(
                cmd,
                src_stage,
                dst_stage,
                vk::DependencyFlags::empty(),
                &[],
                &[barrier],
                &[],
            );
            device
                .handle()
                .cmd_copy_buffer(cmd, self.buffer, staging.handle(), &[region]);
        }

        device.submit_transfer_command(cmd)?;
        Ok(())
    }

    fn copy_rows_to_staging(
        &self,
        device: &Arc<VulkanDevice>,
        staging: &StagingBuffer,
        src_offset: u64,
        row_bytes: u64,
        row_count: u64,
        src_stride: u64,
    ) -> VulkanResult<()> {
        let cmd = device.begin_transfer_command()?;
        let regions: Vec<vk::BufferCopy> = (0..row_count)
            .map(|row| {
                vk::BufferCopy::default()
                    .src_offset(src_offset + row * src_stride)
                    .dst_offset(row * row_bytes)
                    .size(row_bytes)
            })
            .collect();
        let (src_stage, src_access, dst_stage, dst_access) = download_barrier_masks(self.usage);
        let span_size = (row_count - 1) * src_stride + row_bytes;
        unsafe {
            let barrier = vk::BufferMemoryBarrier::default()
                .src_access_mask(src_access)
                .dst_access_mask(dst_access)
                .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .buffer(self.buffer)
                .offset(src_offset)
                .size(span_size);
            device.handle().cmd_pipeline_barrier(
                cmd,
                src_stage,
                dst_stage,
                vk::DependencyFlags::empty(),
                &[],
                &[barrier],
                &[],
            );
            device
                .handle()
                .cmd_copy_buffer(cmd, self.buffer, staging.handle(), &regions);
        }
        device.submit_transfer_command(cmd)?;
        Ok(())
    }

    fn copy_regions_to_staging(
        &self,
        device: &Arc<VulkanDevice>,
        staging: &StagingBuffer,
        inputs: &[(u64, u64, u64, u64)],
    ) -> VulkanResult<()> {
        let cmd = device.begin_transfer_command()?;
        let mut regions = Vec::new();
        let mut dst_offset = 0u64;
        for &(src_offset, row_bytes, row_count, src_stride) in inputs {
            for row in 0..row_count {
                regions.push(
                    vk::BufferCopy::default()
                        .src_offset(src_offset + row * src_stride)
                        .dst_offset(dst_offset)
                        .size(row_bytes),
                );
                dst_offset += row_bytes;
            }
        }
        let (src_stage, src_access, dst_stage, dst_access) = download_barrier_masks(self.usage);
        unsafe {
            let barrier = vk::BufferMemoryBarrier::default()
                .src_access_mask(src_access)
                .dst_access_mask(dst_access)
                .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .buffer(self.buffer)
                .offset(0)
                .size(self.size);
            device.handle().cmd_pipeline_barrier(
                cmd,
                src_stage,
                dst_stage,
                vk::DependencyFlags::empty(),
                &[],
                &[barrier],
                &[],
            );
            device
                .handle()
                .cmd_copy_buffer(cmd, self.buffer, staging.handle(), &regions);
        }
        device.submit_transfer_command(cmd)?;
        Ok(())
    }
}

impl Drop for VulkanBuffer {
    fn drop(&mut self) {
        let owner = TransferOwner::Buffer {
            buffer: self.buffer,
            allocation: self.allocation.take(),
        };
        self.lifetime.admit_or_release_resource(owner);
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
        let owner = TransferOwner::Buffer {
            buffer: self.buffer,
            allocation: self.allocation.take(),
        };
        self.device.lifetime().admit_or_release_resource(owner);
    }
}
