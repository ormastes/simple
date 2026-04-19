#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, BufferUsage, VulkanBuffer, STATE};

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
    //   0x1  = TRANSFER_SRC,   0x2  = TRANSFER_DST
    let buf_usage = BufferUsage {
        storage: (usage & 0x80) != 0,
        uniform: (usage & 0x10) != 0,
        transfer_src: (usage & 0x01) != 0,
        transfer_dst: (usage & 0x02) != 0,
    };

    let buf_usage = if !buf_usage.storage && !buf_usage.uniform {
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
    if state.buffers.remove(&handle).is_some() { 1 } else { 0 }
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
    if state.buffers.contains_key(&_handle) { 1 } else { 0 }
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
    if state.buffers.contains_key(&_handle) { 1 } else { 0 }
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
pub extern "C" fn rt_vulkan_copy_to_buffer(handle: i64, data_ptr: i64, offset: i64) -> i64 {
    let mut state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => {
            state.set_error(format!("copy_to_buffer: unknown handle {handle}"));
            return 0;
        }
    };

    if data_ptr == 0 {
        state.set_error("copy_to_buffer: null data pointer".to_string());
        return 0;
    }

    let size = buf.size() as usize;
    let slice = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, size) };

    match buf.upload(slice) {
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
pub extern "C" fn rt_vulkan_copy_from_buffer(data_ptr: i64, handle: i64, offset: i64) -> i64 {
    let state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => return 0,
    };

    if data_ptr == 0 {
        return 0;
    }

    let size = buf.size();
    match buf.download(size) {
        Ok(bytes) => {
            let dst = unsafe { std::slice::from_raw_parts_mut(data_ptr as *mut u8, bytes.len()) };
            dst.copy_from_slice(&bytes);
            1
        }
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
