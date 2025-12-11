//! GPU Context and Execution

use crate::buffer::{Buffer, BufferUsage, MappedBuffer};
use crate::device::{default_device, Device};
use crate::error::{GpuError, GpuResult};
use crate::kernel::{CompiledKernel, Kernel};
use std::sync::atomic::{AtomicU64, Ordering};

/// Global buffer ID counter.
static BUFFER_ID: AtomicU64 = AtomicU64::new(1);

/// GPU compute context.
pub struct Context {
    /// The device this context is bound to.
    device: Device,
}

impl Context {
    /// Create a new context for a specific device.
    pub fn new(device: Device) -> GpuResult<Self> {
        Ok(Context { device })
    }

    /// Create a context for the default device.
    pub fn default_context() -> GpuResult<Self> {
        let device = default_device()?;
        Self::new(device)
    }

    /// Get the device this context is bound to.
    pub fn device(&self) -> &Device {
        &self.device
    }

    /// Allocate a buffer on the GPU.
    pub fn alloc<T: Clone + Default>(&self, len: usize) -> GpuResult<Buffer<T>> {
        self.alloc_with_usage(len, BufferUsage::storage())
    }

    /// Allocate a buffer with specific usage flags.
    pub fn alloc_with_usage<T: Clone + Default>(
        &self,
        len: usize,
        usage: BufferUsage,
    ) -> GpuResult<Buffer<T>> {
        let id = BUFFER_ID.fetch_add(1, Ordering::SeqCst);
        Ok(Buffer::new(id, len, usage))
    }

    /// Allocate a buffer and upload data.
    pub fn alloc_upload<T: Clone + Default>(&self, data: &[T]) -> GpuResult<Buffer<T>> {
        let id = BUFFER_ID.fetch_add(1, Ordering::SeqCst);
        Ok(Buffer::with_data(id, data.to_vec(), BufferUsage::storage()))
    }

    /// Map a buffer for CPU access.
    pub fn map<'a, T: Clone + Default>(&self, buffer: &'a mut Buffer<T>) -> GpuResult<MappedBuffer<'a, T>> {
        Ok(MappedBuffer::new(buffer))
    }

    /// Compile a kernel.
    pub fn compile_kernel(&self, kernel: &Kernel) -> GpuResult<CompiledKernel> {
        // In a real implementation, this would compile to SPIR-V or native GPU code
        Ok(CompiledKernel::new(kernel.clone()))
    }

    /// Launch a kernel.
    pub fn launch(
        &self,
        _kernel: &CompiledKernel,
        _global_size: [u32; 3],
        local_size: [u32; 3],
    ) -> GpuResult<()> {
        // Validate work group size
        let total_local = local_size[0] * local_size[1] * local_size[2];
        if total_local > self.device.capabilities.max_work_group_invocations {
            return Err(GpuError::InvalidWorkGroupSize(format!(
                "Work group size {} exceeds maximum {}",
                total_local, self.device.capabilities.max_work_group_invocations
            )));
        }

        // Validate dimensions
        if local_size[0] > self.device.capabilities.max_work_group_size_x
            || local_size[1] > self.device.capabilities.max_work_group_size_y
            || local_size[2] > self.device.capabilities.max_work_group_size_z
        {
            return Err(GpuError::InvalidWorkGroupSize(
                "Work group dimension exceeds maximum".to_string(),
            ));
        }

        // In a real implementation, this would dispatch to the GPU
        // For now, this is a no-op stub
        Ok(())
    }

    /// Launch a kernel with 1D work size.
    pub fn launch_1d(
        &self,
        kernel: &CompiledKernel,
        global_size: u32,
        local_size: u32,
    ) -> GpuResult<()> {
        self.launch(kernel, [global_size, 1, 1], [local_size, 1, 1])
    }

    /// Synchronize - wait for all GPU operations to complete.
    pub fn sync(&self) -> GpuResult<()> {
        // In a real implementation, this would wait for GPU completion
        Ok(())
    }

    /// Execute a simple kernel function on the software fallback.
    ///
    /// This is used for testing and when no GPU is available.
    pub fn execute_software<F>(&self, global_size: u32, f: F) -> GpuResult<()>
    where
        F: Fn(u32) + Sync,
    {
        // Software execution runs the kernel sequentially
        for global_id in 0..global_size {
            f(global_id);
        }
        Ok(())
    }

    /// Execute a kernel function that operates on buffers.
    pub fn execute_on_buffers<T, F>(
        &self,
        input: &Buffer<T>,
        output: &mut Buffer<T>,
        f: F,
    ) -> GpuResult<()>
    where
        T: Clone + Default,
        F: Fn(&T) -> T,
    {
        if input.len() != output.len() {
            return Err(GpuError::InvalidArgument(
                "Input and output buffer sizes must match".to_string(),
            ));
        }

        let input_data = input.data();
        let output_data = output.data_mut();

        for i in 0..input.len() {
            output_data[i] = f(&input_data[i]);
        }

        Ok(())
    }

    /// Execute a binary operation on two buffers.
    pub fn execute_binary<T, F>(
        &self,
        a: &Buffer<T>,
        b: &Buffer<T>,
        output: &mut Buffer<T>,
        f: F,
    ) -> GpuResult<()>
    where
        T: Clone + Default,
        F: Fn(&T, &T) -> T,
    {
        if a.len() != b.len() || a.len() != output.len() {
            return Err(GpuError::InvalidArgument(
                "All buffer sizes must match".to_string(),
            ));
        }

        let a_data = a.data();
        let b_data = b.data();
        let output_data = output.data_mut();

        for i in 0..a.len() {
            output_data[i] = f(&a_data[i], &b_data[i]);
        }

        Ok(())
    }
}

impl Default for Context {
    fn default() -> Self {
        Context::default_context().expect("Failed to create default GPU context")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_creation() {
        let ctx = Context::default_context();
        assert!(ctx.is_ok());
    }

    #[test]
    fn test_buffer_allocation() {
        let ctx = Context::default();
        let buf: Buffer<f32> = ctx.alloc(1024).unwrap();
        assert_eq!(buf.len(), 1024);
    }

    #[test]
    fn test_alloc_upload() {
        let ctx = Context::default();
        let data = vec![1.0f32, 2.0, 3.0, 4.0];
        let buf = ctx.alloc_upload(&data).unwrap();

        assert_eq!(buf.len(), 4);
        assert_eq!(buf.download().unwrap(), data);
    }

    #[test]
    fn test_software_execution() {
        let ctx = Context::default();
        use std::sync::Mutex;
        let results = Mutex::new(vec![0u32; 10]);

        ctx.execute_software(10, |id| {
            results.lock().unwrap()[id as usize] = id * 2;
        })
        .unwrap();

        assert_eq!(*results.lock().unwrap(), vec![0, 2, 4, 6, 8, 10, 12, 14, 16, 18]);
    }

    #[test]
    fn test_execute_on_buffers() {
        let ctx = Context::default();
        let input = ctx.alloc_upload(&[1.0f32, 2.0, 3.0, 4.0]).unwrap();
        let mut output: Buffer<f32> = ctx.alloc(4).unwrap();

        ctx.execute_on_buffers(&input, &mut output, |x| x * 2.0)
            .unwrap();

        assert_eq!(output.download().unwrap(), vec![2.0, 4.0, 6.0, 8.0]);
    }

    #[test]
    fn test_execute_binary() {
        let ctx = Context::default();
        let a = ctx.alloc_upload(&[1.0f32, 2.0, 3.0, 4.0]).unwrap();
        let b = ctx.alloc_upload(&[5.0f32, 6.0, 7.0, 8.0]).unwrap();
        let mut output: Buffer<f32> = ctx.alloc(4).unwrap();

        ctx.execute_binary(&a, &b, &mut output, |x, y| x + y)
            .unwrap();

        assert_eq!(output.download().unwrap(), vec![6.0, 8.0, 10.0, 12.0]);
    }

    #[test]
    fn test_work_group_validation() {
        let ctx = Context::default();
        let kernel = CompiledKernel::new(Kernel::new("test"));

        // Valid work group size
        assert!(ctx.launch(&kernel, [1024, 1, 1], [256, 1, 1]).is_ok());

        // Invalid work group size (too large)
        let result = ctx.launch(&kernel, [1024, 1, 1], [2048, 1, 1]);
        assert!(result.is_err());
    }
}
