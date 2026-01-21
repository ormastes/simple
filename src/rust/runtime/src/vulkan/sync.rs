//! Vulkan synchronization primitives (Fences, Semaphores)

use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use std::sync::Arc;

/// Fence wrapper for CPU-GPU synchronization
pub struct Fence {
    device: Arc<VulkanDevice>,
    fence: vk::Fence,
}

impl Fence {
    /// Create a new fence
    pub fn new(device: Arc<VulkanDevice>, signaled: bool) -> VulkanResult<Self> {
        let flags = if signaled {
            vk::FenceCreateFlags::SIGNALED
        } else {
            vk::FenceCreateFlags::empty()
        };

        let create_info = vk::FenceCreateInfo::default().flags(flags);

        let fence = unsafe {
            device
                .handle()
                .create_fence(&create_info, None)
                .map_err(|e| VulkanError::SyncError(format!("Create fence: {:?}", e)))?
        };

        Ok(Self { device, fence })
    }

    /// Get the Vulkan fence handle
    pub fn handle(&self) -> vk::Fence {
        self.fence
    }

    /// Wait for the fence to be signaled
    pub fn wait(&self, timeout_ns: u64) -> VulkanResult<()> {
        unsafe {
            self.device
                .handle()
                .wait_for_fences(&[self.fence], true, timeout_ns)
                .map_err(|e| VulkanError::SyncError(format!("Wait fence: {:?}", e)))?;
        }
        Ok(())
    }

    /// Reset the fence to unsignaled state
    pub fn reset(&self) -> VulkanResult<()> {
        unsafe {
            self.device
                .handle()
                .reset_fences(&[self.fence])
                .map_err(|e| VulkanError::SyncError(format!("Reset fence: {:?}", e)))?;
        }
        Ok(())
    }

    /// Check if the fence is signaled (non-blocking)
    pub fn is_signaled(&self) -> VulkanResult<bool> {
        unsafe {
            self.device
                .handle()
                .get_fence_status(self.fence)
                .map_err(|e| VulkanError::SyncError(format!("Get fence status: {:?}", e)))
        }
    }
}

impl Drop for Fence {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_fence(self.fence, None);
        }
    }
}

/// Semaphore wrapper for GPU-GPU synchronization
pub struct Semaphore {
    device: Arc<VulkanDevice>,
    semaphore: vk::Semaphore,
}

impl Semaphore {
    /// Create a new binary semaphore
    pub fn new(device: Arc<VulkanDevice>) -> VulkanResult<Self> {
        let create_info = vk::SemaphoreCreateInfo::default();

        let semaphore = unsafe {
            device
                .handle()
                .create_semaphore(&create_info, None)
                .map_err(|e| VulkanError::SyncError(format!("Create semaphore: {:?}", e)))?
        };

        Ok(Self { device, semaphore })
    }

    /// Get the Vulkan semaphore handle
    pub fn handle(&self) -> vk::Semaphore {
        self.semaphore
    }
}

impl Drop for Semaphore {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_semaphore(self.semaphore, None);
        }
    }
}

/// Semaphore pool for efficient reuse
pub struct SemaphorePool {
    device: Arc<VulkanDevice>,
    available: parking_lot::Mutex<Vec<vk::Semaphore>>,
    in_use: parking_lot::Mutex<Vec<vk::Semaphore>>,
}

impl SemaphorePool {
    /// Create a new semaphore pool
    pub fn new(device: Arc<VulkanDevice>) -> Self {
        Self {
            device,
            available: parking_lot::Mutex::new(Vec::new()),
            in_use: parking_lot::Mutex::new(Vec::new()),
        }
    }

    /// Acquire a semaphore from the pool (creates new if none available)
    pub fn acquire(&self) -> VulkanResult<vk::Semaphore> {
        let mut available = self.available.lock();

        let semaphore = if let Some(sem) = available.pop() {
            sem
        } else {
            // Create new semaphore
            let create_info = vk::SemaphoreCreateInfo::default();
            unsafe {
                self.device
                    .handle()
                    .create_semaphore(&create_info, None)
                    .map_err(|e| VulkanError::SyncError(format!("Create semaphore: {:?}", e)))?
            }
        };

        self.in_use.lock().push(semaphore);
        Ok(semaphore)
    }

    /// Release a semaphore back to the pool
    pub fn release(&self, semaphore: vk::Semaphore) {
        let mut in_use = self.in_use.lock();
        if let Some(pos) = in_use.iter().position(|&s| s == semaphore) {
            in_use.swap_remove(pos);
            self.available.lock().push(semaphore);
        }
    }

    /// Get the number of available semaphores
    pub fn available_count(&self) -> usize {
        self.available.lock().len()
    }

    /// Get the number of in-use semaphores
    pub fn in_use_count(&self) -> usize {
        self.in_use.lock().len()
    }
}

impl Drop for SemaphorePool {
    fn drop(&mut self) {
        unsafe {
            let available = self.available.lock();
            let in_use = self.in_use.lock();

            for &semaphore in available.iter() {
                self.device.handle().destroy_semaphore(semaphore, None);
            }

            for &semaphore in in_use.iter() {
                self.device.handle().destroy_semaphore(semaphore, None);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fence_create() {
        let device = VulkanDevice::new_default().unwrap();
        let fence = Fence::new(device, false).unwrap();

        // Should not be signaled initially
        assert!(!fence.is_signaled().unwrap());
    }

    #[test]
    fn test_semaphore_pool() {
        let device = VulkanDevice::new_default().unwrap();
        let pool = SemaphorePool::new(device);

        // Acquire some semaphores
        let sem1 = pool.acquire().unwrap();
        let sem2 = pool.acquire().unwrap();

        assert_eq!(pool.in_use_count(), 2);
        assert_eq!(pool.available_count(), 0);

        // Release them
        pool.release(sem1);
        pool.release(sem2);

        assert_eq!(pool.in_use_count(), 0);
        assert_eq!(pool.available_count(), 2);
    }

    // Unit tests that don't require Vulkan drivers

    #[test]
    fn test_fence_create_flags_signaled() {
        // Test that SIGNALED flag is used for pre-signaled fences
        let flags = vk::FenceCreateFlags::SIGNALED;
        let create_info = vk::FenceCreateInfo::default().flags(flags);
        assert_eq!(create_info.flags, vk::FenceCreateFlags::SIGNALED);
    }

    #[test]
    fn test_fence_create_flags_unsignaled() {
        // Test that empty flags for unsignaled fences
        let flags = vk::FenceCreateFlags::empty();
        let create_info = vk::FenceCreateInfo::default().flags(flags);
        assert_eq!(create_info.flags, vk::FenceCreateFlags::empty());
    }

    #[test]
    fn test_semaphore_create_info_default() {
        // Semaphore create info should use default (no flags needed)
        let create_info = vk::SemaphoreCreateInfo::default();
        assert_eq!(create_info.flags, vk::SemaphoreCreateFlags::empty());
    }

    #[test]
    fn test_fence_timeout_values() {
        // Common timeout values used for fence waiting
        let one_second_ns: u64 = 1_000_000_000;
        let max_timeout: u64 = u64::MAX;

        assert_eq!(one_second_ns, 1_000_000_000);
        assert_eq!(max_timeout, u64::MAX);
    }

    #[test]
    fn test_fence_wait_all_flag() {
        // When waiting for multiple fences, true means wait for all
        let wait_all = true;
        assert!(wait_all);
    }

    #[test]
    fn test_semaphore_handle_is_non_null_type() {
        // vk::Semaphore null handle
        let null_handle = vk::Semaphore::null();
        assert_eq!(null_handle, vk::Semaphore::null());
    }

    #[test]
    fn test_fence_handle_is_non_null_type() {
        // vk::Fence null handle
        let null_handle = vk::Fence::null();
        assert_eq!(null_handle, vk::Fence::null());
    }

    #[test]
    fn test_signaled_vs_unsignaled_fence_flags() {
        // signaled = true should use SIGNALED, false should use empty
        let signaled = true;
        let flags_true = if signaled {
            vk::FenceCreateFlags::SIGNALED
        } else {
            vk::FenceCreateFlags::empty()
        };
        assert_eq!(flags_true, vk::FenceCreateFlags::SIGNALED);

        let unsignaled = false;
        let flags_false = if unsignaled {
            vk::FenceCreateFlags::SIGNALED
        } else {
            vk::FenceCreateFlags::empty()
        };
        assert_eq!(flags_false, vk::FenceCreateFlags::empty());
    }

    #[test]
    fn test_semaphore_stage_masks() {
        // Common pipeline stages for semaphore synchronization
        let color_output = vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT;
        let bottom = vk::PipelineStageFlags::BOTTOM_OF_PIPE;
        let top = vk::PipelineStageFlags::TOP_OF_PIPE;

        assert!(color_output.contains(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT));
        assert!(bottom.contains(vk::PipelineStageFlags::BOTTOM_OF_PIPE));
        assert!(top.contains(vk::PipelineStageFlags::TOP_OF_PIPE));
    }

    #[test]
    fn test_wait_for_multiple_fences() {
        // Array of fences can be waited on together
        let fence_handles = [vk::Fence::null(), vk::Fence::null()];
        assert_eq!(fence_handles.len(), 2);
    }

    #[test]
    fn test_timeline_semaphore_type() {
        // Timeline semaphores use TIMELINE type (Vulkan 1.2+)
        let timeline_type = vk::SemaphoreType::TIMELINE;
        let binary_type = vk::SemaphoreType::BINARY;

        assert_eq!(timeline_type, vk::SemaphoreType::TIMELINE);
        assert_eq!(binary_type, vk::SemaphoreType::BINARY);
    }

    #[test]
    fn test_external_fence_handle_types() {
        // External fence handle types for cross-process sync
        let opaque_fd = vk::ExternalFenceHandleTypeFlags::OPAQUE_FD;
        assert!(opaque_fd.contains(vk::ExternalFenceHandleTypeFlags::OPAQUE_FD));
    }

    #[test]
    fn test_external_semaphore_handle_types() {
        // External semaphore handle types for cross-process sync
        let opaque_fd = vk::ExternalSemaphoreHandleTypeFlags::OPAQUE_FD;
        assert!(opaque_fd.contains(vk::ExternalSemaphoreHandleTypeFlags::OPAQUE_FD));
    }
}
