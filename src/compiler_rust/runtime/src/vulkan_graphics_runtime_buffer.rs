#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, BufferUsage, VulkanBuffer, STATE};
use crate::value::{byte_array_bytes, byte_array_write, rt_byte_array_new, rt_byte_array_new_len, RuntimeValue};

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
            state.buffers.insert(h, buf);
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
///
/// `data_ptr` is the address of a byte array. `offset` is currently unused.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_to_buffer(handle: i64, data: RuntimeValue, offset: i64) -> i64 {
    let Some(data) = byte_array_bytes(data) else {
        return 0;
    };
    let len = data.len();
    if offset != 0 {
        return 0;
    }
    let mut state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => {
            state.set_error(format!("copy_to_buffer: unknown handle {handle}"));
            return 0;
        }
    };

    if len > buf.size() as usize {
        state.set_error("copy_to_buffer: source exceeds buffer".to_string());
        return 0;
    }
    match buf.upload(&data) {
        Ok(()) => 1,
        Err(e) => {
            let err_msg = format!("copy_to_buffer: {e}");
            tracing::error!("{}", err_msg);
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_to_buffer(_handle: i64, _data: i64, _offset: i64) -> i64 {
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

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer(_data: i64, _handle: i64, _offset: i64) -> i64 {
    0
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
    let Ok(downloaded) = buf.download(end as u64) else {
        return rt_byte_array_new(0);
    };
    let bytes = &downloaded[offset as usize..end as usize];
    let result = rt_byte_array_new_len(bytes.len() as u64);
    if byte_array_write(result, bytes) {
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
    use super::rt_vulkan_read_buffer_bytes;
    use crate::value::rt_array_len;

    #[test]
    fn read_buffer_bytes_rejects_invalid_ranges_with_empty_bytes() {
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(0, 1, 0)), 0);
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(1, -1, 0)), 0);
        assert_eq!(rt_array_len(rt_vulkan_read_buffer_bytes(1, 1, -1)), 0);
    }
}
