//! Bounded owner adapter for the shared C collection-capture engine.
use crate::value::collections::{rt_string_data, rt_string_len};
use crate::value::heap::{is_registered_heap_ptr, HeapHeader, HeapObjectType};
use crate::value::{tags, RuntimeValue};

/// Copy a runtime text's C-compatible prefix into a caller-owned buffer.
///
/// # Safety
/// `buffer` must have `max_len + 1` writable bytes. Unregistered addresses
/// retain the capture ABI's trusted caller-owned, NUL-terminated C-string
/// contract; the caller must keep that allocation readable through its NUL.
#[no_mangle]
pub unsafe extern "C" fn spl_collection_capture_text_copy(value: i64, buffer: *mut u8, max_len: usize) -> i64 {
    if buffer.is_null() || max_len > 4096 {
        return 0;
    }
    let raw = value as u64;
    let address = if raw & tags::TAG_MASK == tags::TAG_HEAP {
        raw & !tags::TAG_MASK
    } else {
        raw
    };
    let heap = address as usize as *mut HeapHeader;
    let registered = address >= 4096 && address & tags::TAG_MASK == 0 && is_registered_heap_ptr(heap);
    if registered {
        // Registry membership must precede every heap header access.
        if (*heap).object_type != HeapObjectType::String {
            return 0;
        }
        let text = RuntimeValue::from_heap_ptr(heap);
        let len = rt_string_len(text);
        let data = rt_string_data(text);
        if len < 0 || (len != 0 && data.is_null()) {
            return 0;
        }
        let mut prefix = 0;
        while prefix < len as usize {
            let byte = *data.add(prefix);
            if byte == 0 {
                break;
            }
            if prefix == max_len {
                return 0;
            }
            *buffer.add(prefix) = byte;
            prefix += 1;
        }
        *buffer.add(prefix) = 0;
        return 1;
    }
    if raw < 0x10000 {
        return 0;
    }
    // Read bytewise: a short trusted C allocation need not have max_len bytes.
    let data = raw as usize as *const u8;
    for index in 0..=max_len {
        let byte = *data.add(index);
        if byte == 0 {
            *buffer.add(index) = 0;
            return 1;
        }
        if index == max_len {
            return 0;
        }
        *buffer.add(index) = byte;
    }
    0
}
