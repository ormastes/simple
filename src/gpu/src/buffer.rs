//! GPU Buffer Management

use crate::error::{GpuError, GpuResult};
use std::marker::PhantomData;

/// Buffer usage flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BufferUsage {
    /// Buffer can be read from GPU.
    pub read: bool,
    /// Buffer can be written to by GPU.
    pub write: bool,
    /// Buffer can be used as a copy source.
    pub copy_src: bool,
    /// Buffer can be used as a copy destination.
    pub copy_dst: bool,
    /// Buffer can be mapped to CPU memory.
    pub map: bool,
}

impl BufferUsage {
    /// Storage buffer (read/write from GPU).
    pub fn storage() -> Self {
        BufferUsage {
            read: true,
            write: true,
            copy_src: true,
            copy_dst: true,
            map: false,
        }
    }

    /// Uniform buffer (read-only from GPU).
    pub fn uniform() -> Self {
        BufferUsage {
            read: true,
            write: false,
            copy_src: false,
            copy_dst: true,
            map: false,
        }
    }

    /// Staging buffer (for CPU-GPU transfers).
    pub fn staging() -> Self {
        BufferUsage {
            read: false,
            write: false,
            copy_src: true,
            copy_dst: true,
            map: true,
        }
    }
}

impl Default for BufferUsage {
    fn default() -> Self {
        Self::storage()
    }
}

/// A GPU buffer handle.
#[derive(Debug)]
pub struct Buffer<T> {
    /// Buffer ID.
    id: u64,
    /// Number of elements.
    len: usize,
    /// Usage flags.
    usage: BufferUsage,
    /// Phantom data for type safety.
    _marker: PhantomData<T>,
    /// Buffer data (software implementation).
    data: Vec<T>,
}

impl<T: Clone + Default> Buffer<T> {
    /// Create a new buffer with the given length.
    pub(crate) fn new(id: u64, len: usize, usage: BufferUsage) -> Self {
        Buffer {
            id,
            len,
            usage,
            _marker: PhantomData,
            data: vec![T::default(); len],
        }
    }

    /// Create a new buffer initialized with data.
    pub(crate) fn with_data(id: u64, data: Vec<T>, usage: BufferUsage) -> Self {
        let len = data.len();
        Buffer {
            id,
            len,
            usage,
            _marker: PhantomData,
            data,
        }
    }

    /// Get the buffer ID.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Get the number of elements.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the size in bytes.
    pub fn size_bytes(&self) -> usize {
        self.len * std::mem::size_of::<T>()
    }

    /// Get the usage flags.
    pub fn usage(&self) -> BufferUsage {
        self.usage
    }

    /// Upload data from host to this buffer.
    pub fn upload(&mut self, data: &[T]) -> GpuResult<()> {
        if data.len() != self.len {
            return Err(GpuError::InvalidArgument(format!(
                "Data length {} doesn't match buffer length {}",
                data.len(),
                self.len
            )));
        }
        self.data = data.to_vec();
        Ok(())
    }

    /// Upload data to a portion of this buffer.
    pub fn upload_range(&mut self, data: &[T], offset: usize) -> GpuResult<()> {
        if offset + data.len() > self.len {
            return Err(GpuError::OutOfBounds {
                offset,
                size: data.len(),
                buffer_size: self.len,
            });
        }
        self.data[offset..offset + data.len()].clone_from_slice(data);
        Ok(())
    }

    /// Download data from this buffer to host.
    pub fn download(&self) -> GpuResult<Vec<T>> {
        Ok(self.data.clone())
    }

    /// Download a portion of this buffer to host.
    pub fn download_range(&self, offset: usize, len: usize) -> GpuResult<Vec<T>> {
        if offset + len > self.len {
            return Err(GpuError::OutOfBounds {
                offset,
                size: len,
                buffer_size: self.len,
            });
        }
        Ok(self.data[offset..offset + len].to_vec())
    }

    /// Get a reference to the internal data (for software execution).
    pub(crate) fn data(&self) -> &[T] {
        &self.data
    }

    /// Get a mutable reference to the internal data (for software execution).
    pub(crate) fn data_mut(&mut self) -> &mut [T] {
        &mut self.data
    }

    /// Fill buffer with a value.
    pub fn fill(&mut self, value: T) {
        for item in &mut self.data {
            *item = value.clone();
        }
    }

    /// Copy data from another buffer.
    pub fn copy_from(&mut self, src: &Buffer<T>) -> GpuResult<()> {
        if src.len != self.len {
            return Err(GpuError::InvalidArgument(format!(
                "Source buffer length {} doesn't match destination length {}",
                src.len, self.len
            )));
        }
        self.data = src.data.clone();
        Ok(())
    }
}

/// A mapped buffer region for direct CPU access.
pub struct MappedBuffer<'a, T> {
    buffer: &'a mut Buffer<T>,
}

impl<'a, T: Clone + Default> MappedBuffer<'a, T> {
    pub(crate) fn new(buffer: &'a mut Buffer<T>) -> Self {
        MappedBuffer { buffer }
    }

    /// Get a reference to the mapped data.
    pub fn data(&self) -> &[T] {
        &self.buffer.data
    }

    /// Get a mutable reference to the mapped data.
    pub fn data_mut(&mut self) -> &mut [T] {
        &mut self.buffer.data
    }

    /// Get the length of the mapped data.
    pub fn len(&self) -> usize {
        self.buffer.len
    }

    /// Check if the mapped data is empty.
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }
}

impl<T: Clone + Default> std::ops::Index<usize> for MappedBuffer<'_, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.buffer.data[index]
    }
}

impl<T: Clone + Default> std::ops::IndexMut<usize> for MappedBuffer<'_, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.buffer.data[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_creation() {
        let buf: Buffer<f32> = Buffer::new(1, 1024, BufferUsage::storage());
        assert_eq!(buf.len(), 1024);
        assert_eq!(buf.size_bytes(), 1024 * 4);
    }

    #[test]
    fn test_buffer_upload_download() {
        let mut buf: Buffer<f32> = Buffer::new(1, 4, BufferUsage::storage());
        buf.upload(&[1.0, 2.0, 3.0, 4.0]).unwrap();

        let data = buf.download().unwrap();
        assert_eq!(data, vec![1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_buffer_range() {
        let mut buf: Buffer<f32> = Buffer::new(1, 8, BufferUsage::storage());
        buf.upload_range(&[5.0, 6.0, 7.0], 2).unwrap();

        let data = buf.download_range(2, 3).unwrap();
        assert_eq!(data, vec![5.0, 6.0, 7.0]);
    }

    #[test]
    fn test_buffer_fill() {
        let mut buf: Buffer<i32> = Buffer::new(1, 4, BufferUsage::storage());
        buf.fill(42);

        let data = buf.download().unwrap();
        assert_eq!(data, vec![42, 42, 42, 42]);
    }

    #[test]
    fn test_mapped_buffer() {
        let mut buf: Buffer<f32> = Buffer::new(1, 4, BufferUsage::storage());
        {
            let mut mapped = MappedBuffer::new(&mut buf);
            mapped[0] = 1.0;
            mapped[1] = 2.0;
            mapped[2] = 3.0;
            mapped[3] = 4.0;
        }

        let data = buf.download().unwrap();
        assert_eq!(data, vec![1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_buffer_copy() {
        let src: Buffer<f32> =
            Buffer::with_data(1, vec![1.0, 2.0, 3.0, 4.0], BufferUsage::storage());
        let mut dst: Buffer<f32> = Buffer::new(2, 4, BufferUsage::storage());

        dst.copy_from(&src).unwrap();
        assert_eq!(dst.download().unwrap(), vec![1.0, 2.0, 3.0, 4.0]);
    }
}
