// SimpleBuf: Zero-copy buffer for monoio I/O operations
// Feature: monoio-direct
// Implements monoio's IoBuf and IoBufMut traits for RuntimeArray

#![cfg(feature = "monoio-direct")]

use crate::value::{HeapHeader, HeapObjectType, RuntimeArray, RuntimeValue};
use std::ops::{Deref, DerefMut};

/// SimpleBuf wraps a RuntimeArray for zero-copy I/O with monoio.
///
/// This buffer implements monoio's IoBuf and IoBufMut traits, allowing
/// kernel I/O operations to write directly to Simple's heap memory
/// without intermediate Vec allocations.
///
/// # Safety
///
/// SimpleBuf maintains the following invariants:
/// - The underlying RuntimeArray must remain valid for the lifetime of SimpleBuf
/// - The array is accessed through raw byte pointers for I/O efficiency
/// - Length tracking is separate from the RuntimeArray's len field
///
/// # Zero-Copy Flow
///
/// ```text
/// Traditional:                        Zero-Copy:
/// ┌────────────┐                     ┌────────────┐
/// │ RuntimeArr │                     │ RuntimeArr │
/// └─────┬──────┘                     └─────┬──────┘
///       │ copy                             │ direct ptr
///       ▼                                  ▼
/// ┌────────────┐                     ┌────────────┐
/// │   Vec<u8>  │                     │ io_uring   │
/// └─────┬──────┘                     │  SQE/CQE   │
///       │ copy                       └────────────┘
///       ▼
/// ┌────────────┐
/// │ io_uring   │
/// │  SQE/CQE   │
/// └────────────┘
/// ```
pub struct SimpleBuf {
    /// Pointer to the RuntimeArray's data area (after header)
    data_ptr: *mut u8,
    /// Capacity in bytes
    capacity: usize,
    /// Current read/write position
    pos: usize,
    /// Number of valid bytes (for reads)
    len: usize,
    /// Original RuntimeValue (for lifetime management)
    _owner: RuntimeValue,
}

impl SimpleBuf {
    /// Create a SimpleBuf from a RuntimeArray RuntimeValue.
    ///
    /// # Safety
    ///
    /// The RuntimeValue must be a valid RuntimeArray and must remain
    /// valid for the lifetime of the SimpleBuf.
    pub unsafe fn from_runtime_array(value: RuntimeValue) -> Option<Self> {
        if !value.is_heap() {
            return None;
        }

        let ptr = value.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::Array {
            return None;
        }

        let arr_ptr = ptr as *const RuntimeArray;
        let capacity = (*arr_ptr).capacity as usize;

        // Get pointer to data area (elements are RuntimeValue, 8 bytes each)
        // For byte buffers, we treat the entire capacity as byte storage
        let data_ptr = (arr_ptr as *const RuntimeArray).add(1) as *mut u8;

        Some(Self {
            data_ptr,
            capacity: capacity * 8, // Each RuntimeValue slot is 8 bytes
            pos: 0,
            len: 0,
            _owner: value,
        })
    }

    /// Create a SimpleBuf with a specific byte capacity interpretation.
    ///
    /// Use this when you need exact byte-level control, such as for
    /// network buffers where each element represents one byte.
    pub unsafe fn from_runtime_array_bytes(value: RuntimeValue, byte_capacity: usize) -> Option<Self> {
        if !value.is_heap() {
            return None;
        }

        let ptr = value.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::Array {
            return None;
        }

        let arr_ptr = ptr as *const RuntimeArray;
        let data_ptr = (arr_ptr as *const RuntimeArray).add(1) as *mut u8;

        Some(Self {
            data_ptr,
            capacity: byte_capacity,
            pos: 0,
            len: 0,
            _owner: value,
        })
    }

    /// Create a new SimpleBuf by allocating a RuntimeArray.
    pub fn new(capacity: usize) -> Self {
        let array = crate::value::rt_array_new(capacity as u64);

        unsafe {
            let ptr = array.as_heap_ptr();
            let arr_ptr = ptr as *const RuntimeArray;
            let data_ptr = (arr_ptr as *const RuntimeArray).add(1) as *mut u8;

            Self {
                data_ptr,
                capacity: capacity * 8,
                pos: 0,
                len: 0,
                _owner: array,
            }
        }
    }

    /// Get the current position
    #[inline]
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Set the current position
    #[inline]
    pub fn set_pos(&mut self, pos: usize) {
        self.pos = pos.min(self.capacity);
    }

    /// Get the number of valid bytes
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if the buffer is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Set the number of valid bytes
    #[inline]
    pub fn set_len(&mut self, len: usize) {
        self.len = len.min(self.capacity);
    }

    /// Get the capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Get remaining capacity from current position
    #[inline]
    pub fn remaining(&self) -> usize {
        self.capacity.saturating_sub(self.pos)
    }

    /// Get a slice of the valid data
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.data_ptr, self.len) }
    }

    /// Get a mutable slice of the buffer from current position
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.data_ptr.add(self.pos), self.remaining()) }
    }

    /// Advance the position by n bytes
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.pos = (self.pos + n).min(self.capacity);
    }

    /// Reset position to beginning
    #[inline]
    pub fn reset(&mut self) {
        self.pos = 0;
    }

    /// Clear the buffer (reset position and length)
    #[inline]
    pub fn clear(&mut self) {
        self.pos = 0;
        self.len = 0;
    }

    /// Copy data into the buffer, returning bytes written
    pub fn write_bytes(&mut self, data: &[u8]) -> usize {
        let to_write = data.len().min(self.remaining());
        if to_write > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(data.as_ptr(), self.data_ptr.add(self.pos), to_write);
            }
            self.pos += to_write;
            self.len = self.len.max(self.pos);
        }
        to_write
    }

    /// Read data from the buffer into a slice, returning bytes read
    pub fn read_bytes(&mut self, buf: &mut [u8]) -> usize {
        let available = self.len.saturating_sub(self.pos);
        let to_read = buf.len().min(available);
        if to_read > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(self.data_ptr.add(self.pos), buf.as_mut_ptr(), to_read);
            }
            self.pos += to_read;
        }
        to_read
    }
}

// ============================================================================
// monoio IoBuf trait implementation
// ============================================================================

// Note: These implementations require the monoio crate
// They implement the IoBuf and IoBufMut traits for zero-copy I/O

unsafe impl monoio::buf::IoBuf for SimpleBuf {
    fn read_ptr(&self) -> *const u8 {
        unsafe { self.data_ptr.add(self.pos) }
    }

    fn bytes_init(&self) -> usize {
        self.len.saturating_sub(self.pos)
    }
}

unsafe impl monoio::buf::IoBufMut for SimpleBuf {
    fn write_ptr(&mut self) -> *mut u8 {
        unsafe { self.data_ptr.add(self.pos) }
    }

    fn bytes_total(&mut self) -> usize {
        self.remaining()
    }

    unsafe fn set_init(&mut self, init_len: usize) {
        let new_len = self.pos + init_len;
        self.len = new_len.min(self.capacity);
    }
}

// ============================================================================
// OwnedBuf: A fully owned buffer for monoio I/O
// ============================================================================

/// OwnedBuf is a self-contained buffer for monoio operations.
///
/// Unlike SimpleBuf which wraps a RuntimeArray, OwnedBuf owns its memory
/// and is designed for internal use in the monoio thread where we don't
/// need to pass buffers back to Simple code.
pub struct OwnedBuf {
    data: Vec<u8>,
    pos: usize,
}

impl OwnedBuf {
    /// Create a new OwnedBuf with the given capacity
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0u8; capacity],
            pos: 0,
        }
    }

    /// Get the current position
    #[inline]
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Set the current position
    #[inline]
    pub fn set_pos(&mut self, pos: usize) {
        self.pos = pos.min(self.data.len());
    }

    /// Get the data slice
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.pos]
    }

    /// Get remaining capacity
    #[inline]
    pub fn remaining(&self) -> usize {
        self.data.len().saturating_sub(self.pos)
    }

    /// Advance position
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.pos = (self.pos + n).min(self.data.len());
    }

    /// Clear the buffer
    #[inline]
    pub fn clear(&mut self) {
        self.pos = 0;
    }

    /// Consume the buffer and return the underlying Vec
    pub fn into_vec(self) -> Vec<u8> {
        self.data
    }
}

impl Deref for OwnedBuf {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl DerefMut for OwnedBuf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

unsafe impl monoio::buf::IoBuf for OwnedBuf {
    fn read_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }

    fn bytes_init(&self) -> usize {
        self.pos
    }
}

unsafe impl monoio::buf::IoBufMut for OwnedBuf {
    fn write_ptr(&mut self) -> *mut u8 {
        unsafe { self.data.as_mut_ptr().add(self.pos) }
    }

    fn bytes_total(&mut self) -> usize {
        self.remaining()
    }

    unsafe fn set_init(&mut self, init_len: usize) {
        self.pos = (self.pos + init_len).min(self.data.len());
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Create a SimpleBuf from a RuntimeArray for direct I/O
#[no_mangle]
pub extern "C" fn rt_simplebuf_new(capacity: i64) -> RuntimeValue {
    if capacity <= 0 {
        return RuntimeValue::NIL;
    }

    let buf = SimpleBuf::new(capacity as usize);
    buf._owner
}

/// Copy data from SimpleBuf to RuntimeArray after I/O completion
///
/// This function updates the RuntimeArray's elements with the byte values
/// read by monoio. Each byte becomes a RuntimeValue integer.
#[no_mangle]
pub extern "C" fn rt_simplebuf_sync_to_array(array: RuntimeValue, bytes_read: i64) -> RuntimeValue {
    if !array.is_heap() || bytes_read <= 0 {
        return RuntimeValue::from_int(0);
    }

    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return RuntimeValue::from_int(0);
        }

        let arr_ptr = ptr as *mut RuntimeArray;
        let capacity = (*arr_ptr).capacity as usize;
        let bytes_to_sync = (bytes_read as usize).min(capacity);

        // Get pointer to data area as bytes
        let data_ptr = (arr_ptr as *const RuntimeArray).add(1) as *const u8;

        // Get pointer to elements as RuntimeValue
        let elements_ptr = (arr_ptr as *mut RuntimeArray).add(1) as *mut RuntimeValue;

        // Convert bytes to RuntimeValue integers
        for i in 0..bytes_to_sync {
            let byte_val = *data_ptr.add(i);
            *elements_ptr.add(i) = RuntimeValue::from_int(byte_val as i64);
        }

        // Update array length
        (*arr_ptr).len = bytes_to_sync as u64;

        RuntimeValue::from_int(bytes_to_sync as i64)
    }
}

/// Copy data from RuntimeArray to byte buffer before I/O write
///
/// This function prepares the buffer for monoio write operations by
/// converting RuntimeValue integers to raw bytes.
#[no_mangle]
pub extern "C" fn rt_simplebuf_sync_from_array(array: RuntimeValue, max_len: i64) -> RuntimeValue {
    if !array.is_heap() || max_len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return RuntimeValue::from_int(0);
        }

        let arr_ptr = ptr as *const RuntimeArray;
        let len = ((*arr_ptr).len as usize).min(max_len as usize);

        // Get pointer to elements as RuntimeValue
        let elements_ptr = (arr_ptr as *const RuntimeArray).add(1) as *const RuntimeValue;

        // Get pointer to data area as bytes
        let data_ptr = (arr_ptr as *mut RuntimeArray).add(1) as *mut u8;

        // Convert RuntimeValue integers to bytes
        for i in 0..len {
            let val = *elements_ptr.add(i);
            if val.is_int() {
                *data_ptr.add(i) = val.as_int() as u8;
            } else {
                *data_ptr.add(i) = 0;
            }
        }

        RuntimeValue::from_int(len as i64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplebuf_new() {
        let buf = SimpleBuf::new(1024);
        assert_eq!(buf.capacity(), 1024 * 8);
        assert_eq!(buf.len(), 0);
        assert_eq!(buf.pos(), 0);
    }

    #[test]
    fn test_simplebuf_write_read() {
        let mut buf = SimpleBuf::new(1024);

        let data = b"Hello, World!";
        let written = buf.write_bytes(data);
        assert_eq!(written, data.len());
        assert_eq!(buf.len(), data.len());

        buf.reset();

        let mut read_buf = [0u8; 32];
        let read = buf.read_bytes(&mut read_buf);
        assert_eq!(read, data.len());
        assert_eq!(&read_buf[..read], data);
    }

    #[test]
    fn test_owned_buf() {
        let mut buf = OwnedBuf::new(1024);
        assert_eq!(buf.remaining(), 1024);

        buf.advance(100);
        assert_eq!(buf.pos(), 100);
        assert_eq!(buf.remaining(), 924);

        buf.clear();
        assert_eq!(buf.pos(), 0);
    }
}
