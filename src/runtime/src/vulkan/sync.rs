//! Vulkan synchronization primitives (Fences, Semaphores)

use super::error::{VulkanError, VulkanResult};
use super::device::VulkanDevice;
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
            device.handle().create_fence(&create_info, None)
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
            self.device.handle()
                .wait_for_fences(&[self.fence], true, timeout_ns)
                .map_err(|e| VulkanError::SyncError(format!("Wait fence: {:?}", e)))?;
        }
        Ok(())
    }

    /// Reset the fence to unsignaled state
    pub fn reset(&self) -> VulkanResult<()> {
        unsafe {
            self.device.handle()
                .reset_fences(&[self.fence])
                .map_err(|e| VulkanError::SyncError(format!("Reset fence: {:?}", e)))?;
        }
        Ok(())
    }

    /// Check if the fence is signaled (non-blocking)
    pub fn is_signaled(&self) -> VulkanResult<bool> {
        unsafe {
            self.device.handle().get_fence_status(self.fence)
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
            device.handle().create_semaphore(&create_info, None)
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
                self.device.handle().create_semaphore(&create_info, None)
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
    #[ignore] // Requires Vulkan drivers
    fn test_fence_create() {
        let device = VulkanDevice::new_default().unwrap();
        let fence = Fence::new(device, false).unwrap();

        // Should not be signaled initially
        assert!(!fence.is_signaled().unwrap());
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
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
}
