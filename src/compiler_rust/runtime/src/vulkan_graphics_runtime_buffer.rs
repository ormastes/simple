#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, BufferUsage, VulkanBuffer, STATE};
#[cfg(feature = "vulkan")]
use std::sync::Arc;
use crate::value::{byte_array_bytes, byte_array_write, rt_byte_array_new, rt_byte_array_new_len, RuntimeValue};

// A tightly packed 8K ARGB framebuffer is 132,710,400 bytes. Keep the raw ABI
// bounded while allowing one complete 8K seed/upload.
const MAX_RAW_TRANSFER_BYTES: i64 = 256 * 1024 * 1024;

// ============================================================================
// Buffer Management
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_alloc_buffer(size: i64, usage: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    // Decode usage flags from the Simple-side enum encoding:
    //   0x80 = STORAGE_BUFFER, 0x10 = UNIFORM_BUFFER,
    //   0x40 = VERTEX_BUFFER,  0x20 = INDEX_BUFFER,
    //   0x1  = TRANSFER_SRC,   0x2  = TRANSFER_DST
    let buf_usage = BufferUsage {
        storage: (usage & 0x80) != 0,
        uniform: (usage & 0x10) != 0,
        vertex: (usage & 0x40) != 0,
        index: (usage & 0x20) != 0,
        transfer_src: (usage & 0x01) != 0,
        transfer_dst: (usage & 0x02) != 0,
    };

    let buf_usage = if !buf_usage.storage && !buf_usage.uniform && !buf_usage.vertex && !buf_usage.index {
        BufferUsage::storage()
    } else {
        buf_usage
    };

    match VulkanBuffer::new(device, size as u64, buf_usage) {
        Ok(buf) => {
            let h = alloc_handle();
            state.buffers.insert(h, Arc::new(buf));
            h
        }
        Err(e) => {
            state.set_error(format!("alloc_buffer: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_alloc_buffer(_size: i64, _usage: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_free_buffer(handle: i64) -> i64 {
    let mut state = STATE.lock();
    if state.buffers.remove(&handle).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_free_buffer(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_map_memory(_handle: i64) -> i64 {
    // VulkanBuffer uses gpu-allocator staged transfers; explicit map not exposed.
    let state = STATE.lock();
    if state.buffers.contains_key(&_handle) {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_map_memory(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_unmap_memory(_handle: i64) -> i64 {
    let state = STATE.lock();
    if state.buffers.contains_key(&_handle) {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_unmap_memory(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Upload raw bytes from `data_ptr` (host memory) into a Vulkan buffer.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_to_buffer(handle: i64, data: RuntimeValue, offset: i64) -> i64 {
    let Some(data) = byte_array_bytes(data) else {
        return 0;
    };
    copy_to_buffer_bytes(handle, &data, offset)
}

#[cfg(feature = "vulkan")]
fn copy_to_buffer_bytes(handle: i64, data: &[u8], offset: i64) -> i64 {
    let Ok(offset) = u64::try_from(offset) else {
        return 0;
    };
    let mut state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => {
            state.set_error(format!("copy_to_buffer: unknown handle {handle}"));
            return 0;
        }
    };

    match buf.upload_at(data, offset) {
        Ok(()) => 1,
        Err(e) => {
            let err_msg = format!("copy_to_buffer: {e}");
            state.set_error(err_msg.clone());
            tracing::error!("{}", err_msg);
            0
        }
    }
}

/// AOT/raw-array ABI for pure-Simple native executables.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_to_buffer_raw(handle: i64, data_ptr: i64, byte_count: i64, offset: i64) -> i64 {
    if byte_count < 0 || offset < 0 || byte_count > MAX_RAW_TRANSFER_BYTES {
        return 0;
    }
    let Some(end) = offset.checked_add(byte_count) else {
        return 0;
    };
    {
        let state = STATE.lock();
        let Some(buf) = state.buffers.get(&handle) else {
            return 0;
        };
        if end as u64 > buf.size() {
            return 0;
        }
    }
    if byte_count == 0 {
        return copy_to_buffer_bytes(handle, &[], offset);
    }
    if data_ptr <= 0 {
        return 0;
    }
    let data = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, byte_count as usize) };
    copy_to_buffer_bytes(handle, data, offset)
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_to_buffer(_handle: i64, _data: i64, _offset: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_to_buffer_raw(_handle: i64, _data_ptr: i64, _byte_count: i64, _offset: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Download bytes from a Vulkan buffer to `data_ptr` (host memory).
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_buffer(data: RuntimeValue, handle: i64, offset: i64) -> i64 {
    let Some(current) = byte_array_bytes(data) else {
        return 0;
    };
    let len = current.len();
    if offset != 0 {
        return 0;
    }
    let state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => return 0,
    };

    if len > buf.size() as usize {
        return 0;
    }
    match buf.download(len as u64) {
        Ok(bytes) => byte_array_write(data, &bytes) as i64,
        Err(e) => {
            tracing::error!("copy_from_buffer: {e}");
            0
        }
    }
}

/// AOT/raw-array ABI for downloading into core-C-owned byte storage.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_buffer_raw(data_ptr: i64, byte_count: i64, handle: i64, offset: i64) -> i64 {
    if data_ptr <= 0 || byte_count < 0 || offset < 0 || byte_count > MAX_RAW_TRANSFER_BYTES {
        return 0;
    }
    let end = match offset.checked_add(byte_count) {
        Some(end) => end,
        None => return 0,
    };
    let state = STATE.lock();
    let Some(buf) = state.buffers.get(&handle) else {
        return 0;
    };
    if end as u64 > buf.size() {
        return 0;
    }
    let Ok(downloaded) = buf.download_range(offset as u64, byte_count as u64) else {
        return 0;
    };
    unsafe {
        std::ptr::copy_nonoverlapping(downloaded.as_ptr(), data_ptr as *mut u8, downloaded.len());
    }
    1
}

/// Download strided device rows into tightly packed core-C-owned storage.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_buffer_strided_raw(
    data_ptr: i64,
    data_len: i64,
    handle: i64,
    src_offset: i64,
    row_bytes: i64,
    row_count: i64,
    src_stride: i64,
) -> i64 {
    if data_len < 0
        || src_offset < 0
        || row_bytes < 0
        || row_count < 0
        || src_stride < 0
        || (row_count > 0 && row_bytes > 0 && src_stride < row_bytes)
        || data_len > MAX_RAW_TRANSFER_BYTES
        || row_count > 16_384
    {
        return 0;
    }
    let Some(packed_len) = row_bytes.checked_mul(row_count) else {
        return 0;
    };
    if packed_len != data_len || (data_len > 0 && data_ptr <= 0) {
        return 0;
    }
    let state = STATE.lock();
    let Some(buf) = state.buffers.get(&handle) else {
        return 0;
    };
    let Ok(downloaded) = buf.download_strided(src_offset as u64, row_bytes as u64, row_count as u64, src_stride as u64)
    else {
        return 0;
    };
    if downloaded.len() != data_len as usize {
        return 0;
    }
    if !downloaded.is_empty() {
        unsafe {
            std::ptr::copy_nonoverlapping(downloaded.as_ptr(), data_ptr as *mut u8, downloaded.len());
        }
    }
    1
}

/// Download packed disjoint row regions with one Vulkan transfer submission.
/// `regions_ptr` points to little-endian u64 tuples:
/// (source_offset, row_bytes, row_count, source_stride).
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_buffer_regions_raw(
    data_ptr: i64,
    data_len: i64,
    handle: i64,
    regions_ptr: i64,
    regions_len: i64,
) -> i64 {
    const RECORD_BYTES: i64 = 32;
    if data_len <= 0
        || data_len > MAX_RAW_TRANSFER_BYTES
        || data_ptr <= 0
        || regions_ptr <= 0
        || regions_len <= 0
        || regions_len > crate::vulkan::swapchain::MAX_PRESENT_DAMAGE_RECTS as i64 * RECORD_BYTES
        || regions_len % RECORD_BYTES != 0
    {
        return 0;
    }
    let state = STATE.lock();
    let Some(buf) = state.buffers.get(&handle) else {
        return 0;
    };
    let raw = unsafe { std::slice::from_raw_parts(regions_ptr as *const u8, regions_len as usize) };
    let mut regions = Vec::with_capacity((regions_len / RECORD_BYTES) as usize);
    for record in raw.chunks_exact(RECORD_BYTES as usize) {
        let field = |offset: usize| u64::from_le_bytes(record[offset..offset + 8].try_into().unwrap());
        regions.push((field(0), field(8), field(16), field(24)));
    }
    let Ok(downloaded) = buf.download_regions(&regions) else {
        return 0;
    };
    if downloaded.len() != data_len as usize {
        return 0;
    }
    unsafe {
        std::ptr::copy_nonoverlapping(downloaded.as_ptr(), data_ptr as *mut u8, downloaded.len());
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer(_data: i64, _handle: i64, _offset: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer_raw(_data_ptr: i64, _byte_count: i64, _handle: i64, _offset: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer_strided_raw(
    _data_ptr: i64,
    _data_len: i64,
    _handle: i64,
    _src_offset: i64,
    _row_bytes: i64,
    _row_count: i64,
    _src_stride: i64,
) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer_regions_raw(
    _data_ptr: i64,
    _data_len: i64,
    _handle: i64,
    _regions_ptr: i64,
    _regions_len: i64,
) -> i64 {
    0
}

#[cfg(all(test, feature = "vulkan"))]
mod raw_guard_tests {
    use super::rt_vulkan_copy_to_buffer_raw;

    #[test]
    fn vulkan_raw_guard_rejects_unknown_upload_handle_before_pointer_access() {
        assert_eq!(rt_vulkan_copy_to_buffer_raw(0, 1, 4, 0), 0);
    }
}

// ──────────────────────────────────────────────────────────────────────────────

/// Return a new byte array containing a bounded Vulkan buffer range.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_read_buffer_bytes(handle: i64, byte_count: i64, offset: i64) -> RuntimeValue {
    if handle <= 0 || byte_count < 0 || offset < 0 {
        return rt_byte_array_new(0);
    }
    let state = STATE.lock();
    let Some(buf) = state.buffers.get(&handle) else {
        return rt_byte_array_new(0);
    };
    let end = match offset.checked_add(byte_count) {
        Some(end) if end as u64 <= buf.size() => end,
        _ => return rt_byte_array_new(0),
    };
    let Ok(downloaded) = buf.download_range(offset as u64, byte_count as u64) else {
        return rt_byte_array_new(0);
    };
    let result = rt_byte_array_new_len(downloaded.len() as u64);
    if byte_array_write(result, &downloaded) {
        result
    } else {
        rt_byte_array_new(0)
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_read_buffer_bytes(_handle: i64, _byte_count: i64, _offset: i64) -> RuntimeValue {
    rt_byte_array_new(0)
}

// ──────────────────────────────────────────────────────────────────────────────

/// Device-to-device buffer copy via staging download + upload.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_buffer(dst: i64, src: i64, size: i64) -> i64 {
    let state = STATE.lock();
    let src_buf = match state.buffers.get(&src) {
        Some(b) => b,
        None => return 0,
    };
    let copy_size = if size > 0 { size as u64 } else { src_buf.size() };
    let bytes = match src_buf.download(copy_size) {
        Ok(b) => b,
        Err(e) => {
            tracing::error!("copy_buffer download: {e}");
            return 0;
        }
    };

    let dst_buf = match state.buffers.get(&dst) {
        Some(b) => b,
        None => return 0,
    };
    match dst_buf.upload(&bytes) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("copy_buffer upload: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_buffer(_dst: i64, _src: i64, _size: i64) -> i64 {
    0
}

#[cfg(test)]
mod tests {
    use super::{
        rt_vulkan_copy_from_buffer_regions_raw, rt_vulkan_copy_from_buffer_strided_raw, rt_vulkan_copy_to_buffer_raw,
        rt_vulkan_read_buffer_bytes, MAX_RAW_TRANSFER_BYTES,
    };
    use crate::value::{byte_array_bytes, rt_array_len};

    #[test]
    fn read_buffer_bytes_rejects_invalid_ranges_with_empty_bytes() {
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(0, 1, 0)), 0);
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(1, -1, 0)), 0);
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(1, 1, -1)), 0);
    }

    #[test]
    fn raw_transfer_cap_covers_one_8k_argb_frame() {
        assert!(MAX_RAW_TRANSFER_BYTES >= 7_680 * 4_320 * 4);
        assert_eq!(MAX_RAW_TRANSFER_BYTES, 256 * 1024 * 1024);
    }

    #[test]
    fn strided_raw_guard_rejects_invalid_shape_before_pointer_access() {
        assert_eq!(rt_vulkan_copy_from_buffer_strided_raw(0, 8, 0, 0, 4, 3, 8), 0);
        assert_eq!(rt_vulkan_copy_from_buffer_strided_raw(0, 12, 0, 0, 4, 3, 2), 0);
        assert_eq!(rt_vulkan_copy_from_buffer_strided_raw(0, 0, 0, 0, 0, 16_385, 0), 0);
    }

    #[test]
    fn region_raw_guard_rejects_invalid_shape_before_pointer_access() {
        assert_eq!(rt_vulkan_copy_from_buffer_regions_raw(0, 8, 0, 0, 0), 0);
        assert_eq!(rt_vulkan_copy_from_buffer_regions_raw(1, 8, 0, 1, 31), 0);
        assert_eq!(rt_vulkan_copy_from_buffer_regions_raw(1, 8, 0, 1, 32 * 1025), 0);
    }

    #[cfg(feature = "vulkan")]
    #[test]
    #[ignore = "requires a live Vulkan device"]
    fn native_vulkan_upload_honors_nonzero_offset() {
        use super::{rt_vulkan_alloc_buffer, rt_vulkan_free_buffer};
        use super::super::vulkan_graphics_runtime_core::{rt_vulkan_init, rt_vulkan_shutdown};

        struct VulkanShutdown;
        impl Drop for VulkanShutdown {
            fn drop(&mut self) {
                rt_vulkan_shutdown();
            }
        }

        assert_eq!(rt_vulkan_init(), 1);
        let _shutdown = VulkanShutdown;
        let buffer = rt_vulkan_alloc_buffer(16, 0x80);
        assert!(buffer > 0);
        let payload = [0u8, 1, 127, 128, 254, 255];
        assert_eq!(
            rt_vulkan_copy_to_buffer_raw(buffer, payload.as_ptr() as i64, payload.len() as i64, 5),
            1
        );
        assert_eq!(
            byte_array_bytes(rt_vulkan_read_buffer_bytes(buffer, payload.len() as i64, 5)).unwrap(),
            payload
        );
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(buffer, 4, 14)), 0);
        let rows = [10u8, 11, 12, 13, 20, 21, 22, 23, 30, 31, 32, 33];
        assert_eq!(
            rt_vulkan_copy_to_buffer_raw(buffer, rows.as_ptr() as i64, rows.len() as i64, 0),
            1
        );
        let mut packed = [0u8; 6];
        assert_eq!(
            rt_vulkan_copy_from_buffer_strided_raw(packed.as_mut_ptr() as i64, packed.len() as i64, buffer, 1, 2, 3, 4,),
            1
        );
        assert_eq!(packed, [11, 12, 21, 22, 31, 32]);
        let mut descriptors = Vec::new();
        for value in [0u64, 2, 2, 4, 10, 2, 1, 2] {
            descriptors.extend_from_slice(&value.to_le_bytes());
        }
        let mut regions_packed = [0u8; 6];
        assert_eq!(
            rt_vulkan_copy_from_buffer_regions_raw(
                regions_packed.as_mut_ptr() as i64,
                regions_packed.len() as i64,
                buffer,
                descriptors.as_ptr() as i64,
                descriptors.len() as i64,
            ),
            1
        );
        assert_eq!(regions_packed, [10, 11, 20, 21, 32, 33]);
        assert_eq!(rt_vulkan_copy_to_buffer_raw(buffer, 0, 0, 16), 1);
        assert_eq!(rt_vulkan_copy_to_buffer_raw(buffer, 0, 0, 17), 0);
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
    }
}
